(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_rip. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_irt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_pure. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
Local Ltac mem_after_store ::= cbv beta; try rewrite le1_unsigned8; mem_after_store_fast.

Section CANSEC1. Context {rc : runConstT}.
Section PC.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (FMT : Z) (fstr : list byte) (RLOf RHIf : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2320)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis A1 : a1 = Z_to_bv 64 FMT.
  Hypothesis FB : bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]).
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) fstr.
  Notation L := (Z.of_nat (length fstr)).
  Notation NF := (Z.of_nat (length fstr) + 1)%Z.
  (* [comment removed for export] *)
  Hypothesis LAY : rt_layout m.
  Hypothesis SEPF : (FMT + NF <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= FMT)%Z.
  Hypothesis APPF : app_blk FMT (FMT + NF).
  Hypothesis UFMT : unpoisoned m FMT (FMT + NF).
  Hypothesis NFZ : (NF <= 2^40)%Z.
  Hypothesis R1F : (RLOf <= FMT /\ FMT + NF <= RHIf /\ RLOf mod 64 = 0 /\ RHIf mod 64 = 0 /\ 0 <= RLOf /\ RHIf <= KEND)%Z.
  Hypothesis WR1F : wr_at asegs m (shad RLOf) (shad RHIf - shad RLOf).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFM : rng RNG FMT NF.
  Hypothesis RSHF : rng RNG (shad RLOf) (shad RHIf - shad RLOf).

  Notation W := [(bv_unsigned sp + -2320, bv_unsigned sp)]%Z.
  Notation SAVES := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation PAT := 12297829382473034410%Z.

  (* [comment removed for export] *)
  Definition INV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -104) SAVES
    /\ (exists j0, rw_cells asegs mc (bv_unsigned sp + -2240) [CB 8 j0; C8 (Z_to_bv 64 (bv_unsigned sp + -120)); C8 a0])
    /\ stk asegs mc (bv_unsigned sp + -2176) (bv_unsigned sp + -104)
    /\ stk asegs mc lo (bv_unsigned sp + -2240)
    /\ munch W m mc /\ wmono asegs m mc /\ mem_inv asegs mc /\ rt_got mc /\ rt_shbase mc.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2320 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64
     /\ 0 <= FMT /\ FMT + L + 1 + 8 <= 2^47 /\ 0 <= L /\ L + 1 <= 2^40
     /\ (FMT + L + 1 <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= FMT))%Z.
  #[using="m RLOf RHIf ST LO KLO SEPF APPF NFZ"] Lemma BL_ok : BL.
  Proof.
    unfold BL. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R.
    destruct ST as (L0 & _). destruct APPF as [LES AS]. unfold KLOW, KHIGH, KEND in *. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac hide_sec :=
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in FB;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in SEPF; change (?P) with (sf_hide P) in APPF; change (?P) with (sf_hide P) in UFMT;
    change (?P) with (sf_hide P) in R1F; change (?P) with (sf_hide P) in WR1F; change (?P) with (sf_hide P) in LAY.
  Ltac inv_open H := let j0 := fresh "j0" in destruct H as (FRT & (j0 & FRL) & STM & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1).
  Ltac prep IV :=
    inv_open IV;
    let B := fresh "B" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2320) 2320) by (eapply rng_sub'; [exact RSTK| lia]);
    hide_sec.

  (* [comment removed for export] *)
  #[using="lo RLOf RHIf ST LO KLO FB SEPF APPF NFZ"] Lemma fmt_rd : forall mc (i : Z) b, mem_inv asegs mc -> munch W m mc ->
    nth_error (fstr ++ [Z_to_bv 8 0]) (Z.to_nat i) = Some b -> (0 <= i)%Z ->
    ov_read_bytes asegs mc (wa (FMT + i)) 1 = Some [b].
  Proof.
    intros mc i b MIc MUc Hn Hi. pose proof BL_ok as B; unfold BL in B.
    eapply u8ro_read; [| exact Hn | exact Hi | reflexivity].
    eapply bytes_at_transport; [exact FB | exact MUc |]. rewrite length_app; cbn [length disjoint_from]. clear - SEPF B. lia.
  Qed.

  Ltac fmt_read i b Hn :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with MUc : munch _ m mc, MIc : mem_inv _ mc |- _ =>
        let H := fresh "RD" in
        pose proof (fmt_rd mc i b MIc MUc ltac:(rewrite nth_error_app1 by lia; exact Hn) ltac:(lia)) as H
    end end.

  (* [comment removed for export] *)
  Ltac prem :=
    lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- mem_inv _ _ => first [assumption | eassumption | idtac "prem: mem_inv"; fail]
    | |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite !unsigned_lit by lia; prem
    | |- stk _ _ _ _ => first [assumption | eassumption | idtac "prem: stk"; fail]
    | |- find_byte _ _ = _ => first [eassumption | idtac "prem: find_byte"; fail]
    | |- rw_cells _ _ _ _ => first [eassumption | idtac "prem: rw_cells"; fail]
    | |- u8arr _ _ _ _ => first [eassumption | idtac "prem: u8arr"; fail]
    | |- bytes_at _ _ _ _ => first [eassumption | first [apply flags_bytes | apply jzt_bytes | apply ccss_bytes | apply fltcv_bytes | apply dioux_bytes | apply cs_bytes | apply csb_bytes | apply ss_bytes | idtac "prem: bytes_at"; fail]; assumption]
    | |- Forall _ _ => first [exact flags_noz | exact jzt_noz | exact ccss_noz | exact fltcv_noz | exact dioux_noz | exact cs_noz | exact csb_noz | exact ss_noz | assumption | idtac "prem: Forall"; fail]
    | |- _ = Z_to_bv 64 _ => first [reflexivity | idtac "prem: eq"; fail]
    | |- rng _ _ _ => first [ assumption | eapply rng_sub'; [exact RI | cbn; unfold sf_hide in *; lia] | eapply rng_sub'; [exact RSTK | unfold sf_hide in *; lia] | idtac "prem: rng"; fail ]
    | |- ?g => unfold sf_hide in *; first [lia | cbv; discriminate | cbn; lia | idtac "prem: other" g; fail]
    end.

  (* [comment removed for export] *)
  Ltac br CC := let K := fresh "K" in if_cases K; zify_cond K; try (exfalso; clear -K CC; lia); [clear K].

  Notation CONT Q x19v x21v mc dcs :=
    (forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) x19v (Z_to_bv 64 0x15358) x21v y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
             F (Z_to_bv 64 0x473b0) fc None mc (seg_rom asegs))) (only parsing).

  Notation POST := (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition INVF (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -104) SAVES
    /\ (exists j3, rw_cells asegs mc (bv_unsigned sp + -2240) [CB 24 j3])
    /\ (exists dj, rw_cells asegs mc (bv_unsigned sp + -2216) [CB 40 dj])
    /\ stk asegs mc (bv_unsigned sp + -2176) (bv_unsigned sp + -104)
    /\ stk asegs mc lo (bv_unsigned sp + -2240)
    /\ munch W m mc /\ wmono asegs m mc /\ mem_inv asegs mc /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc FMT (FMT + NF) /\ wr_at asegs mc (shad RLOf) (shad RHIf - shad RLOf).

  Definition BNDF : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2320 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64
     /\ 1 <= NF /\ NF <= 2^40
     /\ 0 <= FMT /\ FMT + NF + 8 <= KEND
     /\ 2147450880 <= shad RLOf /\ shad RLOf <= shad FMT /\ shad (FMT + NF - 1) + 1 <= shad RHIf /\ shad RHIf <= KHIGH
     /\ 0 <= Z.shiftr FMT 3 < 2^44 /\ -1 <= Z.shiftr (FMT + NF + -1) 3 < 2^44
     /\ shad RLOf mod 8 = 0 /\ shad RHIf mod 8 = 0
     /\ RLOf <= FMT /\ FMT + NF <= RHIf /\ RLOf mod 64 = 0 /\ RHIf mod 64 = 0)%Z.
  Lemma BNDF_ok : BNDF.
  Proof using APPF KLO LO NFZ R1F ST.
    unfold BNDF. destruct ST as (LOW & _). destruct APPF as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. Z.div_mod_to_equations; (keep_hyps sp lo FMT fstr RLOf RHIf r7 r8 q r q0 r0 q1 r1 q2 r2 q3 r3 q4 r4 q5 r5 q6 r6 q7 q8 LO KLO NFZ R1F AS SPR H H0 H4 H5 H9 H10 H14 H15 H19 H20 H24 H25 H29 H30 H34 H35 H39 H44; lia).
  Qed.
  Ltac acc_facts B ::= pose proof BNDF_ok as B; unfold BNDF, KHIGH, KEND in B.

  Definition BLF : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2320 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64
     /\ 1 <= NF /\ NF <= 2^40 /\ 0 <= FMT /\ FMT + NF + 8 <= 2^47
     /\ 0 <= Z.shiftr FMT 3 < 2^44 /\ -1 <= Z.shiftr (FMT + NF + -1) 3 < 2^44
     /\ 2147450880 <= shad RLOf /\ shad RLOf <= shad FMT /\ shad (FMT + NF - 1) + 1 <= shad RHIf /\ shad RHIf <= 17594333495296)%Z.
  #[using="m ST LO KLO APPF NFZ R1F"] Lemma BLF_ok : BLF. Proof. pose proof BNDF_ok as B. unfold BNDF, KHIGH, KEND in B. unfold BLF. repeat split; lia. Qed.

  Ltac invf_open H := let j3 := fresh "j3" in let dj := fresh "dj" in
    destruct H as (FRT & (j3 & FRL3) & (dj & FRD) & STM & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UF1 & WRF1).
  Ltac fprep IV :=
    pose proof IV as IV0; invf_open IV;
    pose proof BLF_ok as BL0; unfold BLF in BL0;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2320) 2320) by (eapply rng_sub'; [exact RSTK| lia]);
    hide_sec.

  Definition invf_of__stmt : Prop := forall mc j3 dj,
    rw_cells asegs mc (bv_unsigned sp + -104) SAVES ->
    rw_cells asegs mc (bv_unsigned sp + -2240) [CB 24 j3] -> rw_cells asegs mc (bv_unsigned sp + -2216) [CB 40 dj] ->
    stk asegs mc (bv_unsigned sp + -2176) (bv_unsigned sp + -104) -> stk asegs mc lo (bv_unsigned sp + -2240) ->
    munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> INVF mc.
  Section Sz5.
  Variables mc j3 dj : ltac2:(SecDiet.SzSec.tyM 'invf_of__stmt "vvv" @mc).
  #[using="ST LO KLO GOT SHB LAY APPF UFMT NFZ R1F WR1F"] Lemma invf_of__body : ltac2:(SecDiet.SzSec.bodyP 'invf_of__stmt "vvv").
  Proof.
    intros FRT FRL3 FRD STM ST1 MU1 WM1 MI1.
 pose proof BNDF_ok as B. unfold BNDF, KHIGH, KEND in B.
    split; [exact FRT|]. split; [eexists; exact FRL3|]. split; [eexists; exact FRD|]. repeat (split; [assumption|]).
    split. { eapply rw_cells_transport; [exact GOT | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    split. { eapply rw_cells_transport; [exact SHB | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    split. { eapply rw_cells_transport; [exact LAY | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (SS : (shad (FMT + NF - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UFMT | exact MU1 |]. cbn [disjoint_from]. lia. }
    eapply wr_at_transport; eassumption.
  Qed.
  End Sz5.
  #[using="ST LO KLO GOT SHB LAY APPF UFMT NFZ R1F WR1F"] Lemma invf_of : ltac:(let t := eval cbv delta [invf_of__stmt] in invf_of__stmt in exact t).
  Proof. intros mc j3 dj. ltac2:(SecDiet.SzSec.closeP 'invf_of__body "vvv"). Qed.

  (* [comment removed for export] *)
  Definition fregs (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp s1 x10 x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 NF) (Z_to_bv 64 FMT) s4 a2 s6 a0 (Z_to_bv 64 (bv_unsigned sp + -2184)) s9 s10 s11 x28 x29 x30 x31.

  Section FmtCheck.
  Variable Q : machine_state -> Prop.
  (* [comment removed for export] *)
  Hypothesis KF : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31, INVF mc ->
    evtF asegs RNG Q (MS (fregs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31) F (Z_to_bv 64 0x47344) fc None mc (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SLf__stmt : Prop := forall mc (k : nat) (c : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    INVF mc -> (1 <= NF <= 64)%Z -> Z.to_nat (shad (FMT + NF - 1) - c) = k -> (shad FMT <= c < shad (FMT + NF - 1))%Z ->
    evtF asegs RNG Q (MS (fregs x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (FMT + NF + -1) 3)) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                                   x28 x29 x30 x31)
                            F (Z_to_bv 64 0x47c60) fc None mc (seg_rom asegs)).
  Section Sz6.
  Variables mc c x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'SLf__stmt "vkvvvvvvvvvvvvvv" @mc).
  #[using="ST LO KLO APPF NFZ R1F RSTK RSHF KF"] Lemma SLf__body : ltac2:(SecDiet.SzSec.bodyP 'SLf__stmt "vkvvvvvvvvvvvvvv").
  Proof.
    intros k IV N1 Hk Hc.
 unfold fregs. fprep IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (FMT + NF - 1) = 2147450880 + Z.shiftr (FMT + NF + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc FMT (FMT + NF) c UF1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply KF; eassumption.
  Qed.
  End Sz6.
  #[using="ST LO KLO APPF NFZ R1F RSTK RSHF KF"] Lemma SLf : ltac:(let t := eval cbv delta [SLf__stmt] in SLf__stmt in exact t).
  Proof. intros mc k c x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'SLf__body "vkvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition SEf__stmt : Prop := forall mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31, INVF mc -> (1 <= NF <= 64)%Z ->
    evtF asegs RNG Q (MS (fregs x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr FMT 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (FMT + NF + -1) 3))
                                   (Z_to_bv 64 (FMT + NF + -1)) x13 x14 x15 x16 x17 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x47c44) fc None mc (seg_rom asegs)).
  Section Sz7.
  Variables mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'SEf__stmt "vvvvvvvvvvvvvv" @mc).
  #[using="ST LO KLO APPF NFZ R1F RSTK RSHF KF"] Lemma SEf__body : ltac2:(SecDiet.SzSec.bodyP 'SEf__stmt "vvvvvvvvvvvvvv").
  Proof.
    intros IV N1.
 unfold fregs. fprep IV.
    destruct (unpoisoned_check_rd asegs mc FMT (FMT + NF) (FMT + NF + -1) 1 UF1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((FMT + NF + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply KF; eassumption.
    - eapply (SLf mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.
  End Sz7.
  #[using="ST LO KLO APPF NFZ R1F RSTK RSHF KF"] Lemma SEf : ltac:(let t := eval cbv delta [SEf__stmt] in SEf__stmt in exact t).
  Proof. intros mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'SEf__body "vvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition SCf__stmt : Prop := forall mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31, INVF mc ->
    evtF asegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp s1 (Z_to_bv 64 L) x11 x12 x13 x14 x15 x16 x17
                                 s2 (Z_to_bv 64 FMT) s4 a2 s6 a0 (Z_to_bv 64 (bv_unsigned sp + -2184)) s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x472f8) fc None mc (seg_rom asegs)).
  Section Sz8.
  Variables mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'SCf__stmt "vvvvvvvvvvvvvvvv" @mc).
  Lemma SCf__body : ltac2:(SecDiet.SzSec.bodyP 'SCf__stmt "vvvvvvvvvvvvvvvv").
  Proof using APPF GOT KF KLO LAY LO NFZ R1F RI RSHF RSTK SHB ST UFMT WR1F.
    intros IV.
 fprep IV.
    do 3 zstep.
    rewrite zb_lxor_ones by lia. if_cases K0; zify_cond K0. { exfalso. clear -K0 BL0. lia. } clear K0.
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0. lia. } clear K3.
      zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | (keep_hyps sp lo fstr RLOf RHIf LO; lia) | unfold KHIGH; (keep_hyps sp lo FMT fstr RLOf RHIf BL0; lia) | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APPF | zsimp; exact UF1
        | zsimp; pose proof BNDF_ok as B9; unfold BNDF in B9; (keep_hyps fstr RLOf RHIf NFZ; lia)
        | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo fstr RLOf RHIf; lia)] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply KF. eapply invf_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= NF <= 64)%Z) by (clear - K2 BL0; lia).
      do 4 zstep. replace (L + FMT)%Z with (FMT + NF + -1)%Z by lia.
      do 6 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1F.
      destruct (shadow_probe8 asegs mc RLOf RHIf FMT WRF1 ltac:(apply no_image_asan; pose proof BNDF_ok as B9; unfold BNDF in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1F; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLOf RHIf (FMT + NF + -1) WRF1 ltac:(apply no_image_asan; pose proof BNDF_ok as B9; unfold BNDF in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1F; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply SEf; eassumption.
      + eapply KF; eassumption.
  Qed.
  End Sz8.
  #[using="ST LO KLO GOT SHB LAY APPF UFMT NFZ R1F WR1F RI RSTK RSHF KF"] Lemma SCf : ltac:(let t := eval cbv delta [SCf__stmt] in SCf__stmt in exact t).
  Proof. intros mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'SCf__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="lo FMT fstr RLOf RHIf MI ST LO KLO GOT SHB A1 FB NOZ LAY SEPF APPF UFMT NFZ R1F WR1F RI RSTK RFM RSHF KF"] Lemma L_entry_chk :
    evtF asegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x4729c) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as B; unfold BL in B.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2320) 2320) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof FB as FBc. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof ST as ST0.
    hide_sec.
    subst a1.
    carve_frame 104%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2176) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    carve_frame 40%nat ST1. carve_frame 24%nat ST1.
    do 16 zstep. do 6 zstep. zstep.
    call istrlen_spec; [ exact MIc | rewrite unsigned_lit by lia; exact FBc | exact NOZ | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RFM| lia] | ].
    eapply SCf. unfold sf_hide in *. eapply invf_of; eassumption.
  Qed.
  End FmtCheck.

  Ltac norm_stk H tgt :=
    lazymatch type of H with stk _ _ _ ?hi =>
      replace hi with tgt in H by (cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia) end.

  (* [comment removed for export] *)
  Definition L_entry0__stmt : Prop := L = 0%Z -> forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31, INVF mc ->
    evtF asegs RNG POST (MS (fregs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31) F (Z_to_bv 64 0x47344) fc None mc (seg_rom asegs)).
  Section Sz10.
  Variables mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'L_entry0__stmt "hvvvvvvvvvvvvvvvvv" @mc).
  #[using="ST LO KLO FB NOZ SEPF APPF UFMT NFZ R1F RSTK RFM"] Lemma L_entry0__body : ltac2:(SecDiet.SzSec.bodyP 'L_entry0__stmt "hvvvvvvvvvvvvvvvvv").
  Proof.
    intros L0 IV.
 unfold fregs. fprep IV.
    assert (HL : nth_error (fstr ++ [Z_to_bv 8 0]) (Z.to_nat 0) = Some (Z_to_bv 8 0)).
    { destruct fstr; [reflexivity | cbn [length] in L0; lia]. }
    do 3 zs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc' _) => lazymatch goal with MUc : munch _ m mc', MIc : mem_inv _ mc' |- _ =>
      pose proof (fmt_rd mc' 0 (Z_to_bv 8 0) MIc MUc HL ltac:(lia)) as RD; rewrite Z.add_0_r in RD end end.
    zs. cbv beta. rewrite unsigned_lit8 by lia. zs. assert (CC : True) by exact I. br CC.
    (* [comment removed for export] *) clear RD. zs. do 13 zs. zs. zs.
    match goal with H : rw_cells asegs _ (bv_unsigned sp + -2240) _ |- _ => rename H into FRL end.
    pose proof (stk_release _ _ _ _ _ ST1 FRL ltac:(lia)) as SK1. norm_stk SK1 (bv_unsigned sp + -2216)%Z.
    pose proof (stk_release _ _ _ _ _ SK1 FRD ltac:(lia)) as SK2. norm_stk SK2 (bv_unsigned sp + -2176)%Z.
    pose proof (stk_merge _ _ _ _ _ SK2 STM ltac:(lia)) as SK3.
    pose proof (stk_release _ _ _ _ _ SK3 FRT ltac:(lia)) as SK4. norm_stk SK4 (bv_unsigned sp).
    replace (bv_unsigned sp + -2320)%Z with (bv_unsigned sp - 2320)%Z in MU1 by lia.
    finish.
  Qed.
  End Sz10.
  #[using="ST LO KLO FB NOZ SEPF APPF UFMT NFZ R1F RSTK RFM"] Lemma L_entry0 : ltac:(let t := eval cbv delta [L_entry0__stmt] in L_entry0__stmt in exact t).
  Proof. intros L0 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'L_entry0__body "hvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition L_entry1__stmt : Prop := (0 < L)%Z -> forall Q,
    (forall mc dj, INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) [CB 40 dj] ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 FMT) (Z_to_bv 64 0x15358) a2 y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
             F (Z_to_bv 64 0x473b0) fc None mc (seg_rom asegs))) ->
    forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31, INVF mc ->
    evtF asegs RNG Q (MS (fregs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31) F (Z_to_bv 64 0x47344) fc None mc (seg_rom asegs)).
  Section Sz11.
  Variables Q mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'L_entry1__stmt "hvhvvvvvvvvvvvvvvvvv" @Q).
  #[using="ST LO KLO FB NOZ SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_entry1__body : ltac2:(SecDiet.SzSec.bodyP 'L_entry1__stmt "hvhvvvvvvvvvvvvvvvvv").
  Proof.
    intros LP K IV.
 unfold fregs. fprep IV.
    do 3 zs.
    (* [comment removed for export] *)
    destruct (nth_error fstr 0) as [c0|] eqn:E0. 2:{ exfalso. apply nth_error_None in E0. lia. }
    assert (NZ0 : bv_unsigned c0 <> 0%Z) by (eapply (proj1 (Forall_forall _ _) NOZ); eapply nth_error_In; exact E0).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc' _) => lazymatch goal with MUc : munch _ m mc', MIc : mem_inv _ mc' |- _ =>
      pose proof (fmt_rd mc' 0 c0 MIc MUc ltac:(rewrite nth_error_app1 by lia; exact E0) ltac:(lia)) as RD0; rewrite Z.add_0_r in RD0 end end.
    zs. zs. if_cases K4; zify_cond K4. { exfalso. clear - K4 NZ0. pose proof (bv_unsigned_in_range 8 c0). cbn in *. lia. } clear K4 RD0.
    do 17 zs.
    eapply K. 2:{ exact FRD. }
    split; [exact FRT|]. split; [eexists; match goal with H : rw_cells asegs _ (bv_unsigned sp + -2240) _ |- _ => exact H end|].
    unfold sf_hide in *. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz11.
  #[using="ST LO KLO FB NOZ SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_entry1 : ltac:(let t := eval cbv delta [L_entry1__stmt] in L_entry1__stmt in exact t).
  Proof. intros LP Q K mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'L_entry1__body "hvhvvvvvvvvvvvvvvvvv"). Qed.

  Notation dcells1 :=
    ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3)]) (only parsing).

  (* [comment removed for export] *)
  Definition lregs (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 : word) (p aq : word) (y22 y28 y29 y30 y31 : word) :=
    mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
        (Z_to_bv 64 10) p (Z_to_bv 64 0x15358) aq y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
        (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31.

  (* [comment removed for export] *)
  Definition L_head__stmt : Prop := forall Q mc dcs p aq,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    (forall mc', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcells1 ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 p aq y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x473dc) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 p aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x473b0) fc None mc (seg_rom asegs)).
  Section Sz12.
  Variables Q mc dcs p aq : ltac2:(SecDiet.SzSec.tyM 'L_head__stmt "vvvvv" @Q).
  #[using="FMT fstr RLOf RHIf ST LO KLO SEPF APPF NFZ R1F RSTK"] Lemma L_head__body : ltac2:(SecDiet.SzSec.bodyP 'L_head__stmt "vvvvv").
  Proof.
    intros IV DIR SZ K.
 intros. unfold lregs. prep IV.
    destruct (rw_cells_forget _ _ _ _ DIR) as [dj DJ]. rewrite SZ in DJ. clear DIR.
    do 5 zs. do 5 zs.
    destruct (u8arr_of_chunk _ _ _ _ DJ) as (dj2 & DA & DL). cbn in DL. clear DJ.
    call imemset_specZ; [ exact MI1 | exact DA | rewrite DL; reflexivity | lia | lia | lia | cbv; discriminate | ].
    match goal with H : u8arr asegs ?mc _ _ |- _ => rewrite ?unsigned_lit in H by lia;
      apply rw_cells_of_u8arr in H; recell H 0%nat 1%nat (zcells0 : list cell); rename H into DIR end.
    zs.
    eapply K. 2:{ exact DIR. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz12.
  #[using="FMT fstr RLOf RHIf ST LO KLO SEPF APPF NFZ R1F RSTK"] Lemma L_head : ltac:(let t := eval cbv delta [L_head__stmt] in L_head__stmt in exact t).
  Proof. intros Q mc dcs p aq. ltac2:(SecDiet.SzSec.closeP 'L_head__body "vvvvv"). Qed.


  (* [comment removed for export] *)
  Definition fmt_char__stmt : Prop := forall mc (i : Z), mem_inv asegs mc -> munch W m mc -> (0 <= i < L)%Z ->
    exists b, nth_error fstr (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z /\ (0 <= bv_unsigned b < 256)%Z /\
              ov_read_bytes asegs mc (wa (FMT + i)) 1 = Some [b].
  Section Sz13.
  Variables mc i : ltac2:(SecDiet.SzSec.tyM 'fmt_char__stmt "vv" @mc).
  #[using="lo RLOf RHIf ST LO KLO FB NOZ SEPF APPF NFZ R1F"] Lemma fmt_char__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_char__stmt "vv").
  Proof.
    intros MIc MUc Hi.
    destruct (nth_error fstr (Z.to_nat i)) as [b|] eqn:E. 2:{ exfalso. apply nth_error_None in E. lia. }
    exists b. split; [reflexivity|]. split.
    { eapply (proj1 (Forall_forall _ _) NOZ). eapply nth_error_In; exact E. }
    split. { pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
    eapply fmt_rd; [exact MIc | exact MUc | rewrite nth_error_app1 by lia; exact E | lia].
  Qed.
  End Sz13.
  #[using="lo RLOf RHIf ST LO KLO FB NOZ SEPF APPF NFZ R1F"] Lemma fmt_char : ltac:(let t := eval cbv delta [fmt_char__stmt] in fmt_char__stmt in exact t).
  Proof. intros mc i. ltac2:(SecDiet.SzSec.closeP 'fmt_char__body "vv"). Qed.

  (* [comment removed for export] *)
  Definition L_skip__stmt : Prop := forall Q mc (k : nat) (i : Z) aq,
    mem_inv asegs mc -> munch W m mc -> (0 <= i)%Z -> (i + Z.of_nat k <= L)%Z ->
    (forall j b, (Z.to_nat i <= j < Z.to_nat i + k)%nat -> nth_error fstr j = Some b -> bv_unsigned b <> 37%Z) ->
    (forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + (i + Z.of_nat k))) aq y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x473dc) fc None mc (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x473dc) fc None mc (seg_rom asegs)).
  Section Sz14.
  Variables Q mc : ltac2:(SecDiet.SzSec.tyM 'L_skip__stmt "vvk" @Q).
  #[using="lo RLOf RHIf ST LO KLO FB NOZ SEPF APPF NFZ R1F RFM"] Lemma L_skip__body : ltac2:(SecDiet.SzSec.bodyP 'L_skip__stmt "vvk").
  Proof.
    intros k.
 induction k as [|k IH]; intros i aq MIc MUc Hi Hk NP K; intros.
    - specialize (K y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31).
      rewrite Z.add_0_r in K. exact K.
    - pose proof BL_ok as B; unfold BL in B. unfold lregs.
      destruct (fmt_char mc i MIc MUc ltac:(lia)) as (b & Hn & NZ & RB & RD).
      assert (NP0 : bv_unsigned b <> 37%Z) by (eapply NP; [|exact Hn]; lia).
      zs. zs. if_cases K1; zify_cond K1. { exfalso. clear -K1 NP0 RB. lia. }
      zs. if_cases K2; zify_cond K2. { exfalso. clear -K2 NZ RB. lia. }
      zs. zs. zs.
      replace (FMT + i + 1)%Z with (FMT + (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [exact MIc | exact MUc | lia | lia | | ].
      { intros j b' Hj Hb'. eapply NP; [|exact Hb']. lia. }
      intros. replace (i + 1 + Z.of_nat k)%Z with (i + Z.of_nat (S k))%Z by lia. apply K.
  Qed.
  End Sz14.
  #[using="lo RLOf RHIf ST LO KLO FB NOZ SEPF APPF NFZ R1F RFM"] Lemma L_skip : ltac:(let t := eval cbv delta [L_skip__stmt] in L_skip__stmt in exact t).
  Proof. intros Q mc k. ltac2:(SecDiet.SzSec.closeP 'L_skip__body "vvk"). Qed.


  (* [comment removed for export] *)
  Definition dirA_ok (c : Z) : Prop :=
    find_byte c B_FLAGS = None /\ find_byte c B_JZT = None /\ (58 <= c < 256)%Z /\ c <> 108%Z /\ c <> 104%Z.
  (* [comment removed for export] *)
  Definition intconv (c : Z) : Prop := c = 100%Z \/ c = 105%Z \/ c = 117%Z \/ c = 120%Z.
  #[using="fstr RLOf RHIf"] Lemma cfacts : forall c, intconv c ->
    dirA_ok c /\ find_byte c B_CCSS = None /\ find_byte c B_FLTCV = None
    /\ (exists ix, find_byte c B_DIOUX = Some ix) /\ (58 <= c < 256)%Z /\ c <> 109%Z /\ c <> 110%Z.
  Proof. intros c [-> | [-> | [-> | ->]]]; repeat split; try (cbv; reflexivity); try lia; eexists; cbv; reflexivity. Qed.
  (* [comment removed for export] *)
  Definition sconv (c : Z) : Prop := c = 115%Z.
  #[using="fstr RLOf RHIf"] Lemma sfacts : forall c, sconv c ->
    dirA_ok c /\ (58 <= c < 256)%Z /\ c <> 109%Z /\ c <> 110%Z
    /\ find_byte c B_CCSS = Some 2%nat /\ find_byte c B_CS = None /\ find_byte c B_CSB = Some 1%nat /\ find_byte c B_SS = Some 0%nat.
  Proof. intros c ->; repeat split; try (cbv; reflexivity); lia. Qed.

  #[using="Type"] Lemma istrchr_res_none : forall A str c, find_byte c str = None -> istrchr_res A str c = 0%Z.
  Proof. intros A str c H. unfold istrchr_res. rewrite H. reflexivity. Qed.

  Notation dcellsG fw p e lm bc :=
    ([C4 (Z_to_bv 64 fw); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 e);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 lm; C1 (Z_to_bv 8 0); C1 bc; CB 3 (repeat (Z_to_bv 8 0) 3)]) (only parsing).
  Notation dcellsA p bc := (dcellsG 0 p (p + 2) (Z_to_bv 8 0) bc) (only parsing).

  (* [comment removed for export] *)
  Definition L_dirA__stmt : Prop := forall Q mc (i : Z) aq b37 bc,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcells1 ->
    (0 <= i)%Z -> (i + 2 <= L)%Z ->
    nth_error fstr (Z.to_nat i) = Some b37 -> bv_unsigned b37 = 37%Z ->
    nth_error fstr (Z.to_nat (i + 1)) = Some bc -> dirA_ok (bv_unsigned bc) ->
    (forall mc', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) (dcellsA (FMT + i) bc) ->
       forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp (Z_to_bv 64 (FMT + i)) (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x15358) aq (Z_to_bv 64 (FMT + i + 1)) (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                           F (Z_to_bv 64 0x47558) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x473dc) fc None mc (seg_rom asegs)).
  Section Sz18.
  Variables Q mc i aq b37 bc : ltac2:(SecDiet.SzSec.tyM 'L_dirA__stmt "vvvvvv" @Q).
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_dirA__body : ltac2:(SecDiet.SzSec.bodyP 'L_dirA__stmt "vvvvvv").
  Proof.
    intros IV DIR Hi HiL H37 E37 Hc HC K.
 intros. unfold lregs. prep IV.
    destruct HC as (NF1 & NF2 & CR & N108 & N104).
    pose proof (conj CR (conj N108 N104)) as CC.
    fmt_read i b37 H37. zs. clear RD. cbv beta. rewrite E37. zs. br CC.
    (* [comment removed for export] *) zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta.
    zs. br CC.
    (* [comment removed for export] *) zs. br CC.
    zs. zs. zs. br CC.
    (* [comment removed for export] *) zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
    call istrchr_spec; [ eassumption | apply flags_bytes; assumption | exact flags_noz | reflexivity | clear -CC; lia
                       | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    rewrite (istrchr_res_none _ _ _ NF1).
    (* [comment removed for export] *) zs. zs. zs. br CC.
    replace (FMT + (i + 1) + 1 + -1)%Z with (FMT + (i + 1))%Z by lia.
    fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. br CC.
    (* [comment removed for export] *) zs. replace (FMT + (i + 1) + 1 + -1)%Z with (FMT + (i + 1))%Z by lia.
    zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. br CC.
    (* [comment removed for export] *) zs. zs. br CC.
    (* [comment removed for export] *) zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
    call istrchr_spec; [ eassumption | apply jzt_bytes; assumption | exact jzt_noz | reflexivity | clear -CC; lia
                       | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    rewrite (istrchr_res_none _ _ _ NF2).
    (* [comment removed for export] *) fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. br CC.
    (* [comment removed for export] *) zs. zs. br CC. zs. zs. br CC.
    (* [comment removed for export] *) fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
    zs. br CC.
    replace (FMT + (i + 1) + 1)%Z with (FMT + i + 2)%Z by lia. replace (FMT + (i + 1))%Z with (FMT + i + 1)%Z by lia.
    eapply K. 2:{ match goal with H : rw_cells asegs _ (bv_unsigned sp + -2216) _ |- _ => exact H end. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz18.
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_dirA : ltac:(let t := eval cbv delta [L_dirA__stmt] in L_dirA__stmt in exact t).
  Proof. intros Q mc i aq b37 bc. ltac2:(SecDiet.SzSec.closeP 'L_dirA__body "vvvvvv"). Qed.


  (* [comment removed for export] *)
  Definition L_dirB__stmt : Prop := forall Q mc (i : Z) aq bc (fw e : Z),
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) (dcellsG fw (FMT + i) e (Z_to_bv 8 0) bc) ->
    (0 <= i)%Z -> (i + 2 <= L)%Z -> intconv (bv_unsigned bc) ->
    (forall mc' dcs', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcs' -> cells_size dcs' = 40%nat ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 e) (Z_to_bv 64 (bv_unsigned aq + 8)) y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x473a8) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 e) (Z_to_bv 64 0x15358) aq y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x47558) fc None mc (seg_rom asegs)).
  Section Sz19.
  Variables Q mc i aq bc fw e : ltac2:(SecDiet.SzSec.tyM 'L_dirB__stmt "vvvvvvv" @Q).
  #[using="RLOf RHIf ST LO KLO SEPF APPF NFZ R1F RI RSTK"] Lemma L_dirB__body : ltac2:(SecDiet.SzSec.bodyP 'L_dirB__stmt "vvvvvvv").
  Proof.
    intros IV DIR Hi HiL HC K.
 intros. prep IV.
    destruct (cfacts _ HC) as (_ & NF3 & NF4 & (ix & HF) & CR & N109 & N110).
    pose proof (conj CR (conj N109 N110)) as CC.
    recell DIR 2%nat 1%nat [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)].
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC. zs. zs. zs.
    call istrchr_spec. all: prem.
    rewrite (istrchr_res_none _ _ _ NF3).
    (* [comment removed for export] *) zs. cbv beta. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. zs. zs.
    chunk_split DIR 8%nat DIR2. chunk_split DIR2 1%nat DIR3.
    call_sp fgvs_spec. all: prem.
    (* [comment removed for export] *) zs. zs. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC.
    (* [comment removed for export] *) zs. zs. br CC. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs.
    call istrchr_spec. all: prem.
    rewrite (istrchr_res_none _ _ _ NF4).
    zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. br CC. zs. zs. br CC. zs. zs. br CC.
    (* [comment removed for export] *) zs.
    chunk_join DIR DIR2. chunk_join DIR DIR3.
    unfold lregs in K. eapply K. 2:{ exact DIR. } 2:{ reflexivity. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz19.
  #[using="RLOf RHIf ST LO KLO SEPF APPF NFZ R1F RI RSTK"] Lemma L_dirB : ltac:(let t := eval cbv delta [L_dirB__stmt] in L_dirB__stmt in exact t).
  Proof. intros Q mc i aq bc fw e. ltac2:(SecDiet.SzSec.closeP 'L_dirB__body "vvvvvvv"). Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation dcellsZ p bc := (dcellsG 0 p (p + 3) (Z_to_bv 8 122) bc) (only parsing).

  (* [comment removed for export] *)
  Definition L_dirA_z__stmt : Prop := forall Q mc (i : Z) aq b37 bz bc,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcells1 ->
    (0 <= i)%Z -> (i + 3 <= L)%Z ->
    nth_error fstr (Z.to_nat i) = Some b37 -> bv_unsigned b37 = 37%Z ->
    nth_error fstr (Z.to_nat (i + 1)) = Some bz -> bv_unsigned bz = 122%Z ->
    nth_error fstr (Z.to_nat (i + 2)) = Some bc -> (0 < bv_unsigned bc < 256)%Z ->
    (forall mc', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) (dcellsZ (FMT + i) bc) ->
       forall y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 3)) (Z_to_bv 64 0x15358) aq y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                           F (Z_to_bv 64 0x47558) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x473dc) fc None mc (seg_rom asegs)).
  Section Sz20.
  Variables Q mc i aq b37 bz bc : ltac2:(SecDiet.SzSec.tyM 'L_dirA_z__stmt "vvvvvvv" @Q).
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_dirA_z__body : ltac2:(SecDiet.SzSec.bodyP 'L_dirA_z__stmt "vvvvvvv").
  Proof.
    intros IV DIR Hi HiL H37 E37 Hz Ez Hc CR K.
 intros. unfold lregs. prep IV.
    assert (NF1 : find_byte 122 B_FLAGS = None) by (cbv; reflexivity).
    assert (F2 : find_byte 122 B_JZT = Some 1%nat) by (cbv; reflexivity).
    assert (CC : True) by exact I.
    fmt_read i b37 H37. zs. clear RD. cbv beta. rewrite E37. zs. br CC.
    zs. fmt_read (i + 1)%Z bz Hz. zs. clear RD. cbv beta. rewrite Ez.
    zs. br CC.
    zs. br CC.
    zs. zs. zs. br CC.
    zs. fmt_read (i + 1)%Z bz Hz. zs. clear RD. cbv beta. rewrite Ez. zs. zs. zs.
    call istrchr_spec; [ eassumption | apply flags_bytes; assumption | exact flags_noz | reflexivity | lia
                       | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    rewrite (istrchr_res_none _ _ _ NF1).
    zs. zs. zs. br CC.
    replace (FMT + (i + 1) + 1 + -1)%Z with (FMT + (i + 1))%Z by lia.
    fmt_read (i + 1)%Z bz Hz. zs. clear RD. cbv beta. rewrite Ez. zs. zs. br CC.
    zs. replace (FMT + (i + 1) + 1 + -1)%Z with (FMT + (i + 1))%Z by lia.
    zs. fmt_read (i + 1)%Z bz Hz. zs. clear RD. cbv beta. rewrite Ez. zs. zs. br CC.
    zs. zs. br CC.
    zs. fmt_read (i + 1)%Z bz Hz. zs. clear RD. cbv beta. rewrite Ez. zs. zs. zs.
    call istrchr_spec; [ eassumption | apply jzt_bytes; assumption | exact jzt_noz | reflexivity | lia
                       | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    unfold istrchr_res. rewrite F2. rewrite unsigned_lit by (cbn; lia).
    fmt_read (i + 1)%Z bz Hz. zs. clear RD. cbv beta. rewrite Ez. zs. br CC.
    zs. zs.
    replace (FMT + (i + 1) + 1)%Z with (FMT + (i + 2))%Z by lia.
    fmt_read (i + 2)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs. zs. br CR.
    try replace (FMT + (i + 2) + 1)%Z with (FMT + i + 3)%Z by lia.
    eapply K. 2:{ match goal with H : rw_cells asegs _ (bv_unsigned sp + -2216) _ |- _ => exact H end. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz20.
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_dirA_z : ltac:(let t := eval cbv delta [L_dirA_z__stmt] in L_dirA_z__stmt in exact t).
  Proof. intros Q mc i aq b37 bz bc. ltac2:(SecDiet.SzSec.closeP 'L_dirA_z__body "vvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fgvs_z_spec : forall ra' sp' t0' t1' t2' s0' s1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6'
      (F' : bvmap 5 word) fc' (m' : word -> option byte) (lo' : Z) (c : Z) (idx : nat) (LM : Z),
    mem_inv asegs m' -> stk asegs m' lo' (bv_unsigned sp') -> (lo' <= bv_unsigned sp' - 32)%Z ->
    find_byte c B_DIOUX = Some idx -> (0 < c < 256)%Z ->
    rw_cells asegs m' LM [C1 (Z_to_bv 8 122)] -> (bv_unsigned sp' <= LM)%Z -> (LM < 2^64)%Z ->
    rng RNG lo' (bv_unsigned sp' - lo') -> rng_aimg RNG -> rng RNG LM 1 ->
    evtF asegs RNG (fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m'',
                      ms' = MS (mkR ra' sp' gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 8) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
                               F' (ret_pc ra') fc' None m'' (seg_rom asegs)
                      /\ munch [(bv_unsigned sp' - 32, bv_unsigned sp')]%Z m' m'' /\ wmono asegs m' m'' /\ mem_inv asegs m''
                      /\ stk asegs m'' lo' (bv_unsigned sp'))
      (MS (mkR ra' sp' gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 c) (Z_to_bv 64 LM) a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
          F' (Z_to_bv 64 0x4ade0) fc' None m' (seg_rom asegs)).
  Proof.
    clear. intros until LM. intros MI' ST' LO' HF CR LMC SEP LMH RSTK0 RI0 RLM.
    pose proof (munch_refl [(bv_unsigned sp' + -32, bv_unsigned sp')]%Z m') as MU. pose proof (wmono_refl asegs m') as WM.
    assert (LO0 : (0 <= lo')%Z) by (destruct ST' as [? _]; assumption).
    assert (RSTK' : rng RNG (bv_unsigned sp' + -32) 32) by (eapply rng_sub'; [exact RSTK0| lia]).
    carve_frame 32%nat ST'.
    do 11 zstep. zstep.
    call istrchr_spec; [ eassumption | apply dioux_bytes; assumption | exact dioux_noz | reflexivity | exact CR
                       | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI0 | cbn; lia] | ].
    unfold istrchr_res. rewrite HF. rewrite unsigned_lit by (unfold S_DIOUX; lia).
    zstep. if_cases K1; zify_cond K1.
    { exfalso. apply find_byte_Some in HF. destruct HF as [HF _]. cbn in HF.
      change 18446744073709551615%Z with (Z.ones 64) in K1. rewrite Z.land_ones in K1 by lia. rewrite Z.mod_small in K1 by lia. lia. }
    clear K1. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. zstep.
    if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. } clear K2.
    do 5 zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
    do 7 zstep.
    release_frame FR ST' (bv_unsigned sp'). finish.
  Qed.

  (* [comment removed for export] *)
  Definition L_dirB_z__stmt : Prop := forall Q mc (i : Z) aq bc,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) (dcellsZ (FMT + i) bc) ->
    (0 <= i)%Z -> (i + 2 <= L)%Z -> intconv (bv_unsigned bc) ->
    (forall mc' dcs', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcs' -> cells_size dcs' = 40%nat ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i + 3)) (Z_to_bv 64 (bv_unsigned aq + 8)) y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x473a8) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 3)) (Z_to_bv 64 0x15358) aq y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x47558) fc None mc (seg_rom asegs)).
  Section Sz22.
  Variables Q mc i aq bc : ltac2:(SecDiet.SzSec.tyM 'L_dirB_z__stmt "vvvvv" @Q).
  #[using="RLOf RHIf ST LO KLO SEPF APPF NFZ R1F RI RSTK"] Lemma L_dirB_z__body : ltac2:(SecDiet.SzSec.bodyP 'L_dirB_z__stmt "vvvvv").
  Proof.
    intros IV DIR Hi HiL HC K.
 intros. prep IV.
    destruct (cfacts _ HC) as (_ & NF3 & NF4 & (ix & HF) & CR & N109 & N110).
    pose proof (conj CR (conj N109 N110)) as CC.
    recell DIR 2%nat 1%nat [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)].
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC. zs. zs. zs.
    call istrchr_spec. all: prem.
    rewrite (istrchr_res_none _ _ _ NF3).
    (* [comment removed for export] *) zs. cbv beta. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. zs. zs.
    chunk_split DIR 8%nat DIR2. chunk_split DIR2 1%nat DIR3.
    call_sp fgvs_z_spec. all: prem.
    (* [comment removed for export] *) zs. zs. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC.
    (* [comment removed for export] *) zs. zs. br CC. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs.
    call istrchr_spec. all: prem.
    rewrite (istrchr_res_none _ _ _ NF4).
    zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. br CC. zs. zs. br CC.
    (* [comment removed for export] *) zs.
    chunk_join DIR DIR2. chunk_join DIR DIR3.
    unfold lregs in K. eapply K. 2:{ exact DIR. } 2:{ reflexivity. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz22.
  #[using="RLOf RHIf ST LO KLO SEPF APPF NFZ R1F RI RSTK"] Lemma L_dirB_z : ltac:(let t := eval cbv delta [L_dirB_z__stmt] in L_dirB_z__stmt in exact t).
  Proof. intros Q mc i aq bc. ltac2:(SecDiet.SzSec.closeP 'L_dirB_z__body "vvvvv"). Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac if_vm := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota end.
  Ltac zsb := zs; try if_vm.
  Ltac ldb k bb Hb Eb := fmt_read k bb Hb; zs; repeat match goal with R : ov_read_bytes _ _ _ _ = _ |- _ => clear R end; cbv beta; rewrite Eb; try if_vm.
  Ltac a0_vm := let v := getreg 10%Z in lazymatch v with Z_to_bv 64 ?e => let e' := eval vm_compute in e in change e with e' end.

  (* [comment removed for export] *)
  Definition atoll_08__stmt : Prop := forall mc (j : Z) b0 b8 bx ra' sp' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6',
    mem_inv asegs mc -> munch W m mc -> (0 <= j)%Z -> (j + 3 <= L)%Z ->
    nth_error fstr (Z.to_nat j) = Some b0 -> bv_unsigned b0 = 48%Z ->
    nth_error fstr (Z.to_nat (j + 1)) = Some b8 -> bv_unsigned b8 = 56%Z ->
    nth_error fstr (Z.to_nat (j + 2)) = Some bx -> bv_unsigned bx = 120%Z ->
    evtF asegs RNG (fun ms' => exists a1 a2 a3 a4 a5 a6 a7 m',
                      ms' = MS (mkR ra' sp' gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 8) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                               F (ret_pc ra') fc None m' (seg_rom asegs)
                      /\ munch [] mc m' /\ wmono asegs mc m' /\ mem_inv asegs m')
      (MS (mkR ra' sp' gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (FMT + j)) a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
          F (Z_to_bv 64 0x6777c) fc None mc (seg_rom asegs)).
  Section Sz23.
  Variables mc j b0 b8 bx ra' sp' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : ltac2:(SecDiet.SzSec.tyM 'atoll_08__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @mc).
  #[using="lo RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RFM"] Lemma atoll_08__body : ltac2:(SecDiet.SzSec.bodyP 'atoll_08__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros MIc MUc Hj HjL H0 E0 H8 E8 Hx Ex.
    pose proof BL_ok as B; unfold BL in B.
    do 3 zsb. ldb j b0 H0 E0. do 7 zsb. zsb. ldb j b0 H0 E0. do 3 zsb. do 6 zsb.
    (* [comment removed for export] *) do 7 zsb. replace (FMT + j + 1)%Z with (FMT + (j + 1))%Z by lia. ldb (j + 1)%Z b8 H8 E8. do 6 zsb.
    (* [comment removed for export] *) do 7 zsb. replace (FMT + (j + 1) + 1)%Z with (FMT + (j + 2))%Z by lia. ldb (j + 2)%Z bx Hx Ex. do 6 zsb.
    (* [comment removed for export] *) do 4 zsb. do 2 zsb.
    a0_vm. apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MIc].
  Qed.
  End Sz23.
  #[using="lo RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RFM"] Lemma atoll_08 : ltac:(let t := eval cbv delta [atoll_08__stmt] in atoll_08__stmt in exact t).
  Proof. intros mc j b0 b8 bx ra' sp' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6'. ltac2:(SecDiet.SzSec.closeP 'atoll_08__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition atoll_8__stmt : Prop := forall mc (j : Z) b8 bx ra' sp' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6',
    mem_inv asegs mc -> munch W m mc -> (0 <= j)%Z -> (j + 2 <= L)%Z ->
    nth_error fstr (Z.to_nat j) = Some b8 -> bv_unsigned b8 = 56%Z ->
    nth_error fstr (Z.to_nat (j + 1)) = Some bx -> bv_unsigned bx = 120%Z ->
    evtF asegs RNG (fun ms' => exists a1 a2 a3 a4 a5 a6 a7 m',
                      ms' = MS (mkR ra' sp' gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 8) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                               F (ret_pc ra') fc None m' (seg_rom asegs)
                      /\ munch [] mc m' /\ wmono asegs mc m' /\ mem_inv asegs m')
      (MS (mkR ra' sp' gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (FMT + j)) a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
          F (Z_to_bv 64 0x6777c) fc None mc (seg_rom asegs)).
  Section Sz24.
  Variables mc j b8 bx ra' sp' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : ltac2:(SecDiet.SzSec.tyM 'atoll_8__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @mc).
  #[using="lo RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RFM"] Lemma atoll_8__body : ltac2:(SecDiet.SzSec.bodyP 'atoll_8__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros MIc MUc Hj HjL H8 E8 Hx Ex.
    pose proof BL_ok as B; unfold BL in B.
    do 3 zsb. ldb j b8 H8 E8. do 7 zsb. zsb. ldb j b8 H8 E8. do 3 zsb. do 6 zsb.
    (* [comment removed for export] *) do 7 zsb. replace (FMT + j + 1)%Z with (FMT + (j + 1))%Z by lia. ldb (j + 1)%Z bx Hx Ex. do 6 zsb.
    (* [comment removed for export] *) do 4 zsb. do 2 zsb.
    a0_vm. apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MIc].
  Qed.
  End Sz24.
  #[using="lo RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RFM"] Lemma atoll_8 : ltac:(let t := eval cbv delta [atoll_8__stmt] in atoll_8__stmt in exact t).
  Proof. intros mc j b8 bx ra' sp' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6'. ltac2:(SecDiet.SzSec.closeP 'atoll_8__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Notation dcells08 p bc := (dcellsG 8 p (p + 4) (Z_to_bv 8 0) bc) (only parsing).

  (* [comment removed for export] *)
  Definition L_dirA_08__stmt : Prop := forall Q mc (i : Z) aq b37 b0 b8 bx,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcells1 ->
    (0 <= i)%Z -> (i + 4 <= L)%Z ->
    nth_error fstr (Z.to_nat i) = Some b37 -> bv_unsigned b37 = 37%Z ->
    nth_error fstr (Z.to_nat (i + 1)) = Some b0 -> bv_unsigned b0 = 48%Z ->
    nth_error fstr (Z.to_nat (i + 2)) = Some b8 -> bv_unsigned b8 = 56%Z ->
    nth_error fstr (Z.to_nat (i + 3)) = Some bx -> bv_unsigned bx = 120%Z ->
    (forall mc', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) (dcells08 (FMT + i) (Z_to_bv 8 120)) ->
       forall y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 (Z_to_bv 64 120) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 4)) (Z_to_bv 64 0x15358) aq y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                           F (Z_to_bv 64 0x47558) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x473dc) fc None mc (seg_rom asegs)).
  Section Sz25.
  Variables Q mc i aq b37 b0 b8 bx : ltac2:(SecDiet.SzSec.tyM 'L_dirA_08__stmt "vvvvvvvv" @Q).
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_dirA_08__body : ltac2:(SecDiet.SzSec.bodyP 'L_dirA_08__stmt "vvvvvvvv").
  Proof.
    intros IV DIR Hi HiL H37 E37 H0 E0 H8 E8 Hx Ex K.
 intros. unfold lregs. prep IV.
    assert (F0 : find_byte 48 B_FLAGS = Some 5%nat) by (cbv; reflexivity).
    assert (NF8 : find_byte 56 B_FLAGS = None) by (cbv; reflexivity).
    assert (NJx : find_byte 120 B_JZT = None) by (cbv; reflexivity).
    ldb i b37 H37 E37. zsb.
    (* [comment removed for export] *) zsb. ldb (i + 1)%Z b0 H0 E0. zsb. zsb. zsb. zsb. zsb.
    (* [comment removed for export] *) zsb. zsb.
    replace (FMT + i + 1)%Z with (FMT + (i + 1))%Z by lia.
    call (atoll_08 _ (i + 1)%Z b0 b8 bx);
      [ eassumption | eassumption | lia | lia | exact H0 | exact E0 | replace (i + 1 + 1)%Z with (i + 2)%Z by lia; exact H8 | exact E8
      | replace (i + 1 + 2)%Z with (i + 3)%Z by lia; exact Hx | exact Ex | ].
    (* [comment removed for export] *)
    zsb.
    ldb (i + 1)%Z b0 H0 E0. zsb. zsb. zsb.
    ldb (i + 2)%Z b8 H8 E8. zsb. zsb. zsb.
    ldb (i + 3)%Z bx Hx Ex. zsb. zsb. zsb.
    zsb. zsb.
    (* [comment removed for export] *)
    zsb. ldb (i + 1)%Z b0 H0 E0. zsb. zsb. zsb.
    call istrchr_spec; [ eassumption | apply flags_bytes; assumption | exact flags_noz | reflexivity | lia | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    unfold istrchr_res. rewrite F0. rewrite unsigned_lit by (cbn; lia).
    zsb. zsb. zsb.
    ldb (i + 2)%Z b8 H8 E8. zsb. zsb. zsb.
    call istrchr_spec; [ eassumption | apply flags_bytes; assumption | exact flags_noz | reflexivity | lia | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    rewrite (istrchr_res_none _ _ _ NF8).
    zsb. zsb. zsb.
    (* [comment removed for export] *)
    ldb (i + 2)%Z b8 H8 E8. zsb. zsb.
    zsb. zsb.
    ldb (i + 2)%Z b8 H8 E8. zsb. zsb.
    zsb. zsb.
    replace (FMT + (i + 1) + 1)%Z with (FMT + (i + 2))%Z by lia.
    call (atoll_8 _ (i + 2)%Z b8 bx); [ eassumption | eassumption | lia | lia | exact H8 | exact E8 | replace (i + 2 + 1)%Z with (i + 3)%Z by lia; exact Hx | exact Ex | ].
    zsb.
    ldb (i + 2)%Z b8 H8 E8. zsb. zsb. zsb. zsb.
    ldb (i + 3)%Z bx Hx Ex. zsb. zsb. zsb. zsb.
    (* [comment removed for export] *)
    zsb. zsb. zsb.
    ldb (i + 3)%Z bx Hx Ex. zsb. zsb. zsb.
    call istrchr_spec; [ eassumption | apply jzt_bytes; assumption | exact jzt_noz | reflexivity | lia | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    rewrite (istrchr_res_none _ _ _ NJx).
    ldb (i + 3)%Z bx Hx Ex. zsb.
    zsb. zsb. zsb. zsb.
    ldb (i + 3)%Z bx Hx Ex. zsb. zsb. zsb. zsb.
    replace (FMT + (i + 1) + 3)%Z with (FMT + i + 4)%Z in * by lia.
    eapply K. 2:{ match goal with H : rw_cells asegs _ (bv_unsigned sp + -2216) _ |- _ => exact H end. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz25.
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_dirA_08 : ltac:(let t := eval cbv delta [L_dirA_08__stmt] in L_dirA_08__stmt in exact t).
  Proof. intros Q mc i aq b37 b0 b8 bx. ltac2:(SecDiet.SzSec.closeP 'L_dirA_08__body "vvvvvvvv"). Qed.


  (* [comment removed for export] *)
  Definition L_last__stmt : Prop := forall mc aq,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcells1 ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG POST (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + L)) aq y22 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x473dc) fc None mc (seg_rom asegs)).
  Section Sz26.
  Variables mc aq : ltac2:(SecDiet.SzSec.tyM 'L_last__stmt "vv" @mc).
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ RSTK RFM"] Lemma L_last__body : ltac2:(SecDiet.SzSec.bodyP 'L_last__stmt "vv").
  Proof.
    intros IV DIR.
 intros. unfold lregs. prep IV.
    assert (HL : nth_error (fstr ++ [Z_to_bv 8 0]) (Z.to_nat L) = Some (Z_to_bv 8 0)) by (rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia; reflexivity).
    assert (CC : True) by exact I.
    pose proof (fmt_rd mc L (Z_to_bv 8 0) MI1 MU1 HL ltac:(lia)) as RD.
    zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC. zs.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) clear RD. zs. do 13 zs. zs. zs.
    (* [comment removed for export] *)
    pose proof (stk_release _ _ _ _ _ ST1 FRL ltac:(lia)) as SK1. norm_stk SK1 (bv_unsigned sp + -2216)%Z.
    pose proof (stk_release _ _ _ _ _ SK1 DIR ltac:(lia)) as SK2. norm_stk SK2 (bv_unsigned sp + -2176)%Z.
    pose proof (stk_merge _ _ _ _ _ SK2 STM ltac:(lia)) as SK3.
    pose proof (stk_release _ _ _ _ _ SK3 FRT ltac:(lia)) as SK4. norm_stk SK4 (bv_unsigned sp).
    replace (bv_unsigned sp + -2320)%Z with (bv_unsigned sp - 2320)%Z in MU1 by lia.
    finish.
  Qed.
  End Sz26.
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ RSTK RFM"] Lemma L_last : ltac:(let t := eval cbv delta [L_last__stmt] in L_last__stmt in exact t).
  Proof. intros mc aq. ltac2:(SecDiet.SzSec.closeP 'L_last__body "vv"). Qed.



  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition L_next0__stmt : Prop := forall mc dcs aq,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG POST (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + L)) aq y22 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x473a8) fc None mc (seg_rom asegs)).
  Section Sz27.
  Variables mc dcs aq : ltac2:(SecDiet.SzSec.tyM 'L_next0__stmt "vvv" @mc).
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ RSTK RFM"] Lemma L_next0__body : ltac2:(SecDiet.SzSec.bodyP 'L_next0__stmt "vvv").
  Proof.
    intros IV DIR SZ.
 intros. unfold lregs. prep IV.
    assert (HL : nth_error (fstr ++ [Z_to_bv 8 0]) (Z.to_nat L) = Some (Z_to_bv 8 0)) by (rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia; reflexivity).
    assert (CC : True) by exact I.
    pose proof (fmt_rd mc L (Z_to_bv 8 0) MI1 MU1 HL ltac:(lia)) as RD.
    zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) clear RD. zs. do 13 zs. zs. zs.
    pose proof (stk_release _ _ _ _ _ ST1 FRL ltac:(lia)) as SK1. norm_stk SK1 (bv_unsigned sp + -2216)%Z.
    pose proof (stk_release _ _ _ _ _ SK1 DIR ltac:(lia)) as SK2. rewrite SZ in SK2. norm_stk SK2 (bv_unsigned sp + -2176)%Z.
    pose proof (stk_merge _ _ _ _ _ SK2 STM ltac:(lia)) as SK3.
    pose proof (stk_release _ _ _ _ _ SK3 FRT ltac:(lia)) as SK4. norm_stk SK4 (bv_unsigned sp).
    replace (bv_unsigned sp + -2320)%Z with (bv_unsigned sp - 2320)%Z in MU1 by lia.
    finish.
  Qed.
  End Sz27.
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ RSTK RFM"] Lemma L_next0 : ltac:(let t := eval cbv delta [L_next0__stmt] in L_next0__stmt in exact t).
  Proof. intros mc dcs aq. ltac2:(SecDiet.SzSec.closeP 'L_next0__body "vvv"). Qed.

  #[using="RLOf RHIf ST LO KLO FB NOZ SEPF APPF NFZ R1F RSTK RFM"] Lemma L_next1 : forall Q mc (i : Z) aq,
    INV mc -> (0 <= i < L)%Z ->
    (forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x473b0) fc None mc (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x473a8) fc None mc (seg_rom asegs)).
  Proof.
    intros Q mc i aq IV Hi K. intros. unfold lregs. pose proof IV as IV'. prep IV'.
    destruct (fmt_char mc i MI1 MU1 ltac:(lia)) as (b2 & Hb2 & NZ2 & RB2 & RD2).
    zs. cbv beta. zs. assert (CC : True) by exact I. br NZ2.
    unfold lregs in K. eapply K.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Section PCS.
  Variables (AQ Sa : Z) (sstr : list byte) (RLO RHI : Z).
  Hypothesis VAQ : rw_cells asegs m (AQ) [C8 (Z_to_bv 64 Sa)].
  Hypothesis SEPV : (bv_unsigned sp <= AQ /\ AQ + 8 <= 2^64)%Z.
  Hypothesis SSTR : bytes_at asegs m Sa (sstr ++ [Z_to_bv 8 0]).
  Hypothesis SNOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr.
  Notation LS := (Z.of_nat (length sstr)).
  Notation NS := (Z.of_nat (length sstr) + 1)%Z.
  Hypothesis SEPS : (Sa + NS <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= Sa)%Z.
  Hypothesis APPS : app_blk Sa (Sa + NS).
  Hypothesis SPOS : (0 < Sa)%Z.
  Hypothesis USTR : unpoisoned m Sa (Sa + NS).
  Hypothesis NSZ : (NS <= 2^40)%Z.
  Hypothesis R1 : (RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RVA : rng RNG (AQ) 8.
  Hypothesis RS : rng RNG Sa NS.
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition INVS (mc : word -> option byte) : Prop :=
    INV mc /\ rt_layout mc /\ unpoisoned mc Sa (Sa + NS) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO)
    /\ bytes_at asegs mc Sa (sstr ++ [Z_to_bv 8 0]) /\ rw_cells asegs mc (AQ) [C8 (Z_to_bv 64 Sa)].

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2320 /\ KHIGH <= lo /\ 1 <= NS /\ NS <= 2^40
     /\ 0 < Sa /\ Sa + NS + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad Sa /\ shad (Sa + NS - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr Sa 3 < 2^44 /\ 0 <= Z.shiftr (Sa + NS + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0
     /\ bv_unsigned sp <= AQ /\ AQ + 8 <= 2^64)%Z.
  Lemma BND_ok : BND.
  Proof using APPS KLO LO NSZ R1 R1F SEPS SEPV SPOS ST.
    unfold BND. destruct ST as (L0 & _). destruct APPS as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. (keep_hyps sp lo FMT fstr RLOf RHIf r9 r10 AQ Sa sstr RLO RHI r7 r8 q r q0 r0 q1 r1 q2 r2 q3 r3 q4 r4 q5 r5 q6 r6 q7 q8 LO KLO SEPV SPOS NSZ R1 AS H H0 H4 H5 H9 H10 H14 H15 H19 H20 H24 H25 H29 H30 H34 H35 H39 H44; nia).
  Qed.
  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BLS : Prop :=
    (1 <= NS /\ NS <= 2^40 /\ 0 < Sa /\ Sa + NS + 8 <= 2^47
     /\ 0 <= Z.shiftr Sa 3 < 2^44 /\ 0 <= Z.shiftr (Sa + NS + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad Sa /\ shad (Sa + NS - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296
     /\ bv_unsigned sp <= AQ /\ AQ + 8 <= 2^64)%Z.
  #[using="m lo FMT fstr RLOf RHIf ST LO KLO R1F SEPV SEPS APPS SPOS NSZ R1"] Lemma BLS_ok : BLS. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BLS. lia. Qed.

  Definition invs_of__stmt : Prop := forall mc, INV mc -> INVS mc.
  Section Sz31.
  Variables mc : ltac2:(SecDiet.SzSec.tyM 'invs_of__stmt "v" @mc).
  #[using="FMT fstr RLOf RHIf ST LO KLO LAY R1F VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1"] Lemma invs_of__body : ltac2:(SecDiet.SzSec.bodyP 'invs_of__stmt "v").
  Proof.
    intros IV.
 pose proof IV as (FRT & (j0 & FRL) & STM & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1).
    pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    split; [exact IV|].
    split. { eapply rw_cells_transport; [exact LAY | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (SS : (shad (Sa + NS - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact USTR | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    split. { eapply bytes_at_transport; [exact SSTR | exact MU1 |]. rewrite length_app. cbn [length disjoint_from]. lia. }
    eapply rw_cells_transport; [exact VAQ | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia.
  Qed.
  End Sz31.
  #[using="FMT fstr RLOf RHIf ST LO KLO LAY R1F VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1"] Lemma invs_of : ltac:(let t := eval cbv delta [invs_of__stmt] in invs_of__stmt in exact t).
  Proof. intros mc. ltac2:(SecDiet.SzSec.closeP 'invs_of__body "v"). Qed.

  Ltac preps IV :=
    let IVS := fresh "IVS" in pose proof (invs_of _ IV) as IVS;
    destruct IVS as (_ & LAY1 & US1 & WR11 & SSTR1 & VAQ1);
    prep IV;
    let B := fresh "BS" in pose proof BLS_ok as B; unfold BLS in B;
    change (?P) with (sf_hide P) in SEPS; change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in SEPV;
    change (?P) with (sf_hide P) in SSTR; change (?P) with (sf_hide P) in NSZ.

  Ltac unland K :=
    change 18446744073709551615%Z with (Z.ones 64) in K; rewrite ?Z.land_ones in K by lia;
    change (2 ^ 64)%Z with 18446744073709551616%Z in K.

  (* [comment removed for export] *)
  Definition KS (Q : machine_state -> Prop) (i : Z) : Prop :=
    forall mc' dcs', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcs' -> cells_size dcs' = 40%nat ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 (AQ + 8)) y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x473a8) fc None mc' (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition sregs (i : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp (Z_to_bv 64 (-1)) x10 x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x15358) (Z_to_bv 64 (AQ + 8)) x22 x23
        (Z_to_bv 64 (bv_unsigned sp + -2184)) (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) x28 x29 x30 x31.

  (* [comment removed for export] *)
  #[using="fstr RLOf RHIf ST LO KLO SEPF APPF NFZ RSTK sstr RLO RHI"] Lemma LS_X : forall Q i mc dcs, KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31,
    evtF asegs RNG Q (MS (sregs i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x47728) fc None mc (seg_rom asegs)).
  Proof.
    intros Q i mc dcs K IV DIR SZ. intros. unfold sregs. prep IV.
    zs. zs. unfold KS, lregs in K. eapply K; [| exact DIR | exact SZ].
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Definition LS_L__stmt : Prop := forall Q i mc dcs (k : nat) (c : Z), KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    (NS <= 64)%Z -> Z.to_nat (shad (Sa + NS - 1) - c) = k -> (shad Sa <= c < shad (Sa + NS - 1))%Z ->
    forall x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evtF asegs RNG Q (MS (sregs i x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (Sa + NS + -1) 3)) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                              (Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x47838) fc None mc (seg_rom asegs)).
  Section Sz33.
  Variables Q i mc dcs c : ltac2:(SecDiet.SzSec.tyM 'LS_L__stmt "vvvvkv" @Q).
  #[using="fstr RLOf RHIf ST LO KLO LAY SEPF APPF NFZ R1F RSTK RLO RHI VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1 RSH1"] Lemma LS_L__body : ltac2:(SecDiet.SzSec.bodyP 'LS_L__stmt "vvvvkv").
  Proof.
    intros k K IV DIR SZ N1 Hk Hc.
 intros. unfold sregs. pose proof IV as IV0. preps IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (Sa + NS - 1) = 2147450880 + Z.shiftr (Sa + NS + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc Sa (Sa + NS) c US1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LS_X; eassumption.
  Qed.
  End Sz33.
  #[using="fstr RLOf RHIf ST LO KLO LAY SEPF APPF NFZ R1F RSTK RLO RHI VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1 RSH1"] Lemma LS_L : ltac:(let t := eval cbv delta [LS_L__stmt] in LS_L__stmt in exact t).
  Proof. intros Q i mc dcs k c. ltac2:(SecDiet.SzSec.closeP 'LS_L__body "vvvvkv"). Qed.

  (* [comment removed for export] *)
  Definition LS_E__stmt : Prop := forall Q i mc dcs, KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    (NS <= 64)%Z ->
    forall x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evtF asegs RNG Q (MS (sregs i x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr Sa 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (Sa + NS + -1) 3))
                              (Z_to_bv 64 (Sa + NS + -1)) x13 x14 x15 x16 x17 (Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x4781c) fc None mc (seg_rom asegs)).
  Section Sz34.
  Variables Q i mc dcs : ltac2:(SecDiet.SzSec.tyM 'LS_E__stmt "vvvv" @Q).
  #[using="fstr RLOf RHIf ST LO KLO LAY SEPF APPF NFZ R1F RSTK RLO RHI VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1 RSH1"] Lemma LS_E__body : ltac2:(SecDiet.SzSec.bodyP 'LS_E__stmt "vvvv").
  Proof.
    intros K IV DIR SZ N1.
 intros. unfold sregs. pose proof IV as IV0. preps IV.
    destruct (unpoisoned_check_rd asegs mc Sa (Sa + NS) (Sa + NS + -1) 1 US1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((Sa + NS + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LS_X; eassumption.
    - eapply (LS_L Q i mc dcs); [exact K | exact IV0 | exact DIR | exact SZ | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.
  End Sz34.
  #[using="fstr RLOf RHIf ST LO KLO LAY SEPF APPF NFZ R1F RSTK RLO RHI VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1 RSH1"] Lemma LS_E : ltac:(let t := eval cbv delta [LS_E__stmt] in LS_E__stmt in exact t).
  Proof. intros Q i mc dcs. ltac2:(SecDiet.SzSec.closeP 'LS_E__body "vvvv"). Qed.

  (* [comment removed for export] *)
  Definition LS_C__stmt : Prop := forall Q i mc dcs, KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evtF asegs RNG Q (MS (sregs i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x477cc) fc None mc (seg_rom asegs)).
  Section Sz35.
  Variables Q i mc dcs : ltac2:(SecDiet.SzSec.tyM 'LS_C__stmt "vvvv" @Q).
  Lemma LS_C__body : ltac2:(SecDiet.SzSec.bodyP 'LS_C__stmt "vvvv").
  Proof using APPF APPS KLO LAY LO NFZ NSZ R1 R1F RI RSH1 RSTK SEPF SEPS SEPV SPOS SSTR ST USTR VAQ WR1.
    intros K IV DIR SZ.
 intros. unfold sregs. pose proof IV as IV0. preps IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1 BS. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      assert (N1 : (64 < NS)%Z) by (unland K2; clear - K2 BS; Z.div_mod_to_equations; lia).
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BS. lia. }
      zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | (keep_hyps sp lo fstr RLOf RHIf sstr RLO RHI dcs LO; lia) | unfold KHIGH; (keep_hyps sp lo FMT fstr RLOf RHIf sstr RLO RHI dcs B; lia) | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APPS | zsimp; exact US1
        | zsimp; pose proof BND_ok as B9; unfold BND in B9; (keep_hyps sp fstr RLOf RHIf AQ Sa sstr RLO RHI dcs BS; lia)
        | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo fstr RLOf RHIf sstr RLO RHI dcs; lia)] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LS_X; [exact K | | eassumption | exact SZ].
      split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
    - (* [comment removed for export] *)
      assert (N1 : (NS <= 64)%Z) by (unland K2; clear - K2 BS; Z.div_mod_to_equations; lia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 asegs mc RLO RHI Sa WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO RHI (Sa + NS + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. prr [10;11;12;13]%Z. if_cases K5; zify_cond K5.
      + eapply LS_X; eassumption.
      + eapply LS_E; eassumption.
  Qed.
  End Sz35.
  #[using="fstr RLOf RHIf ST LO KLO LAY SEPF APPF NFZ R1F RI RSTK RLO RHI VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1 RSH1"] Lemma LS_C : ltac:(let t := eval cbv delta [LS_C__stmt] in LS_C__stmt in exact t).
  Proof. intros Q i mc dcs. ltac2:(SecDiet.SzSec.closeP 'LS_C__body "vvvv"). Qed.

  (* [comment removed for export] *)
  Definition L_dirS__stmt : Prop := forall Q mc (i : Z) bc,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) (dcellsA (FMT + i) bc) ->
    (0 <= i)%Z -> (i + 2 <= L)%Z -> sconv (bv_unsigned bc) -> KS Q i ->
    forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp (Z_to_bv 64 (FMT + i)) (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x15358) (Z_to_bv 64 AQ) (Z_to_bv 64 (FMT + i + 1)) (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x47558) fc None mc (seg_rom asegs)).
  Section Sz36.
  Variables Q mc i bc : ltac2:(SecDiet.SzSec.tyM 'L_dirS__stmt "vvvv" @Q).
  #[using="RLOf RHIf ST LO KLO LAY SEPF APPF NFZ R1F RI RSTK Sa sstr RLO RHI VAQ SEPV SSTR SNOZ SEPS APPS SPOS USTR NSZ R1 WR1 RVA RS RSH1"] Lemma L_dirS__body : ltac2:(SecDiet.SzSec.bodyP 'L_dirS__stmt "vvvv").
  Proof.
    intros IV DIR Hi HiL HC K.
 intros. pose proof IV as IV0. preps IV.
    destruct (sfacts _ HC) as (_ & CR & N109 & N110 & F3 & F4 & F5 & F6).
    pose proof (conj CR (conj N109 N110)) as CC.
    recell DIR 2%nat 1%nat [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)].
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC. zs. zs. zs.
    call istrchr_spec. all: prem. unfold istrchr_res. rewrite F3. rewrite unsigned_lit by (cbn; lia).
    (* [comment removed for export] *) zs. cbv beta. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. zs. call istrchr_spec. all: prem. rewrite (istrchr_res_none _ _ _ F4).
    (* [comment removed for export] *) zs. zs. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. zs. call istrchr_spec. all: prem. unfold istrchr_res. rewrite F5. rewrite unsigned_lit by (cbn; lia).
    (* [comment removed for export] *) zs. zs. br CC. zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. zs.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. zs. call istrchr_spec. all: prem. unfold istrchr_res. rewrite F6. rewrite unsigned_lit by (cbn; lia).
    (* [comment removed for export] *) zs. br CC. zs.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC.
    (* [comment removed for export] *) zs. zs. br CC. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. br BS.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zs. br CC.
    (* [comment removed for export] *) zs. zs.
    unfold sf_hide in SSTR1.
    call istrlen_spec. all: prem.
    zs.
    cbn [app] in DIR.
    eapply (LS_C Q i); [exact K | | exact DIR | reflexivity].
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz36.
  #[using="RLOf RHIf ST LO KLO LAY SEPF APPF NFZ R1F RI RSTK Sa sstr RLO RHI VAQ SEPV SSTR SNOZ SEPS APPS SPOS USTR NSZ R1 WR1 RVA RS RSH1"] Lemma L_dirS : ltac:(let t := eval cbv delta [L_dirS__stmt] in L_dirS__stmt in exact t).
  Proof. intros Q mc i bc. ltac2:(SecDiet.SzSec.closeP 'L_dirS__body "vvvv"). Qed.
  End PCS.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Inductive pitem : Type :=
  | PLit (l : list byte)                 (* [comment removed for export] *)
  | PInt (bc : byte)                     (* [comment removed for export] *)
  | PZu (bc : byte)                      (* [comment removed for export] *)
  | P08x                                 (* [comment removed for export] *)
  | PStr (Sa : Z) (sstr : list byte).    (* [comment removed for export] *)
  Definition pbytes (it : pitem) : list byte :=
    match it with
    | PLit l => l
    | PInt bc => [Z_to_bv 8 37; bc]
    | PZu bc => [Z_to_bv 8 37; Z_to_bv 8 122; bc]
    | P08x => [Z_to_bv 8 37; Z_to_bv 8 48; Z_to_bv 8 56; Z_to_bv 8 120]
    | PStr _ _ => [Z_to_bv 8 37; Z_to_bv 8 115]
    end.
  Definition pitem_ok (it : pitem) : Prop :=
    match it with
    | PLit l => Forall (fun b : byte => bv_unsigned b <> 37%Z) l
    | PInt bc => intconv (bv_unsigned bc)
    | PZu bc => intconv (bv_unsigned bc)
    | P08x => True
    | PStr _ _ => True
    end.
  Definition prender (its : list pitem) : list byte := concat (map pbytes its).

  (* [comment removed for export] *)
  Definition pstr_ok (AQ Sa : Z) (sstr : list byte) : Prop :=
    rw_cells asegs m AQ [C8 (Z_to_bv 64 Sa)] /\ (bv_unsigned sp <= AQ /\ AQ + 8 <= 2^64)%Z
    /\ bytes_at asegs m Sa (sstr ++ [Z_to_bv 8 0]) /\ Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr
    /\ (Sa + (Z.of_nat (length sstr) + 1) <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= Sa)%Z /\ (0 < Sa)%Z
    /\ sobj RNG m Sa (Sa + (Z.of_nat (length sstr) + 1))
    /\ rng RNG AQ 8 /\ rng RNG Sa (Z.of_nat (length sstr) + 1).
  (* [comment removed for export] *)
  Fixpoint pargs_ok (its : list pitem) (aq : word) : Prop :=
    match its with
    | [] => True
    | PLit _ :: r => pargs_ok r aq
    | PStr Sa sstr :: r => pstr_ok (bv_unsigned aq) Sa sstr /\ pargs_ok r (Z_to_bv 64 (bv_unsigned aq + 8))
    | _ :: r => pargs_ok r (Z_to_bv 64 (bv_unsigned aq + 8))
    end.

  #[using="Type"] Lemma skipn_cons_nth : forall {A} (l : list A) n x r, skipn n l = x :: r -> nth_error l n = Some x /\ skipn (S n) l = r /\ (n < length l)%nat.
  Proof.
    clear. intros A l. induction l as [|a l IH]; intros n x r H; [destruct n; discriminate H|].
    destruct n as [|n]; cbn in H |- *; [injection H as -> ->; repeat split; lia|].
    destruct (IH n x r H) as (H1 & H2 & H3). repeat split; [exact H1 | exact H2 | lia].
  Qed.
  #[using="Type"] Lemma skipn_app_run : forall {A} (l l1 r : list A) n, skipn n l = l1 ++ r -> (n <= length l)%nat ->
    (forall t b, nth_error l1 t = Some b -> nth_error l (n + t) = Some b) /\ skipn (n + length l1) l = r /\ (n + length l1 <= length l)%nat.
  Proof.
    clear. intros A l l1 r n H LE.
    assert (LEN : (n + length l1 <= length l)%nat).
    { pose proof (f_equal (@length A) H) as E. rewrite length_skipn, length_app in E. lia. }
    split; [| split; [| exact LEN]].
    - intros t b Hb. rewrite <- nth_error_skipn, H. rewrite nth_error_app1 by (apply nth_error_Some; rewrite Hb; discriminate). exact Hb.
    - rewrite Nat.add_comm, <- skipn_skipn, H. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
  Qed.
  (* [comment removed for export] *)
  #[using="RLOf RHIf ST LO KLO FB NOZ SEPF APPF NFZ R1F RSTK RFM"] Lemma L_after : forall (i : Z) mc dcs aq,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat -> (0 <= i <= L)%Z ->
    (forall mc', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcells1 ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG POST (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                              F (Z_to_bv 64 0x473dc) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG POST (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x473a8) fc None mc (seg_rom asegs)).
  Proof.
    intros i mc dcs aq IV DIR SZ Hi K. intros.
    destruct (Z.eq_dec i L) as [-> | NE].
    - eapply L_next0; eassumption.
    - eapply (L_next1 POST mc i aq); [exact IV | lia |]. intros.
      eapply (L_head POST mc dcs); [exact IV | exact DIR | exact SZ |]. exact K.
  Qed.
  (* [comment removed for export] *)
  #[using="RLOf RHIf ST LO KLO FB NOZ LAY SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_items : forall its (i : Z) mc aq,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcells1 ->
    (0 <= i <= L)%Z -> skipn (Z.to_nat i) fstr = prender its -> Forall pitem_ok its -> pargs_ok its aq ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG POST (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x473dc) fc None mc (seg_rom asegs)).
  Proof.
    induction its as [|it its IH]; intros i mc aq IV DIR Hi SK OK AOK; intros.
    - (* [comment removed for export] *)
      assert (EI : i = L). { cbn in SK. apply (f_equal (@length byte)) in SK. rewrite length_skipn in SK. cbn in SK. lia. }
      subst i. eapply L_last; eassumption.
    - apply Forall_cons_iff in OK. destruct OK as [OK1 OK].
      unfold prender in SK. cbn [map concat] in SK. fold (prender its) in SK.
      destruct (skipn_app_run _ _ _ _ SK ltac:(lia)) as (NTH & SK' & LEN).
      destruct it as [l | bc | bc | | Sa sstr]; cbn [pbytes pitem_ok pargs_ok length] in *.
      + (* [comment removed for export] *)
        pose proof IV as IV'. destruct IV' as (_ & _ & _ & _ & MUc & _ & MIc & _).
        eapply (L_skip POST mc (length l) i aq); [exact MIc | exact MUc | lia | lia | |].
        { intros j b Hj Hb. destruct (nth_error l (j - Z.to_nat i)) as [b'|] eqn:E.
          2:{ exfalso. apply nth_error_None in E. lia. }
          pose proof (NTH _ _ E) as E2. replace (Z.to_nat i + (j - Z.to_nat i))%nat with j in E2 by lia. rewrite Hb in E2. injection E2 as <-.
          eapply (proj1 (Forall_forall _ _) OK1). eapply nth_error_In. exact E. }
        intros. eapply (IH (i + Z.of_nat (length l))%Z mc aq); [exact IV | exact DIR | lia | | exact OK | exact AOK].
        replace (Z.to_nat (i + Z.of_nat (length l))) with (Z.to_nat i + length l)%nat by lia. exact SK'.
      + (* [comment removed for export] *)
        assert (H37 : nth_error fstr (Z.to_nat i) = Some (Z_to_bv 8 37)) by (rewrite <- (Nat.add_0_r (Z.to_nat i)); apply NTH; reflexivity).
        assert (Hc : nth_error fstr (Z.to_nat (i + 1)) = Some bc) by (replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia; apply NTH; reflexivity).
        eapply (L_dirA POST mc i aq (Z_to_bv 8 37) bc); [exact IV | exact DIR | lia | lia | exact H37 | reflexivity | exact Hc | exact (proj1 (cfacts _ OK1)) |].
        clear mc IV DIR. intros mc IV DIR. intros.
        eapply (L_dirB POST mc i aq bc 0 (FMT + i + 2)); [exact IV | exact DIR | lia | lia | exact OK1 |].
        clear mc IV DIR. intros mc dcs IV DIR SZ. intros.
        replace (FMT + i + 2)%Z with (FMT + (i + 2))%Z by lia.
        eapply (L_after (i + 2)%Z mc dcs); [exact IV | exact DIR | exact SZ | lia |].
        clear mc dcs IV DIR SZ. intros mc IV DIR. intros.
        eapply (IH (i + 2)%Z mc); [exact IV | exact DIR | lia | | exact OK | exact AOK].
        replace (Z.to_nat (i + 2)) with (Z.to_nat i + 2)%nat by lia. exact SK'.
      + (* [comment removed for export] *)
        assert (H37 : nth_error fstr (Z.to_nat i) = Some (Z_to_bv 8 37)) by (rewrite <- (Nat.add_0_r (Z.to_nat i)); apply NTH; reflexivity).
        assert (Hz : nth_error fstr (Z.to_nat (i + 1)) = Some (Z_to_bv 8 122)) by (replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia; apply NTH; reflexivity).
        assert (Hc : nth_error fstr (Z.to_nat (i + 2)) = Some bc) by (replace (Z.to_nat (i + 2)) with (Z.to_nat i + 2)%nat by lia; apply NTH; reflexivity).
        assert (CR : (0 < bv_unsigned bc < 256)%Z) by (destruct (cfacts _ OK1) as (_ & _ & _ & _ & CR & _); lia).
        eapply (L_dirA_z POST mc i aq (Z_to_bv 8 37) (Z_to_bv 8 122) bc); [exact IV | exact DIR | lia | lia | exact H37 | reflexivity | exact Hz | reflexivity | exact Hc | exact CR |].
        clear mc IV DIR. intros mc IV DIR. intros.
        eapply (L_dirB_z POST mc i aq bc); [exact IV | exact DIR | lia | lia | exact OK1 |].
        clear mc IV DIR. intros mc dcs IV DIR SZ. intros.
        replace (FMT + i + 3)%Z with (FMT + (i + 3))%Z by lia.
        eapply (L_after (i + 3)%Z mc dcs); [exact IV | exact DIR | exact SZ | lia |].
        clear mc dcs IV DIR SZ. intros mc IV DIR. intros.
        eapply (IH (i + 3)%Z mc); [exact IV | exact DIR | lia | | exact OK | exact AOK].
        replace (Z.to_nat (i + 3)) with (Z.to_nat i + 3)%nat by lia. exact SK'.
      + (* [comment removed for export] *)
        assert (H37 : nth_error fstr (Z.to_nat i) = Some (Z_to_bv 8 37)) by (rewrite <- (Nat.add_0_r (Z.to_nat i)); apply NTH; reflexivity).
        assert (H0 : nth_error fstr (Z.to_nat (i + 1)) = Some (Z_to_bv 8 48)) by (replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia; apply NTH; reflexivity).
        assert (H8 : nth_error fstr (Z.to_nat (i + 2)) = Some (Z_to_bv 8 56)) by (replace (Z.to_nat (i + 2)) with (Z.to_nat i + 2)%nat by lia; apply NTH; reflexivity).
        assert (Hx : nth_error fstr (Z.to_nat (i + 3)) = Some (Z_to_bv 8 120)) by (replace (Z.to_nat (i + 3)) with (Z.to_nat i + 3)%nat by lia; apply NTH; reflexivity).
        eapply (L_dirA_08 POST mc i aq (Z_to_bv 8 37) (Z_to_bv 8 48) (Z_to_bv 8 56) (Z_to_bv 8 120));
          [exact IV | exact DIR | lia | lia | exact H37 | reflexivity | exact H0 | reflexivity | exact H8 | reflexivity | exact Hx | reflexivity |].
        clear mc IV DIR. intros mc IV DIR. intros.
        eapply (L_dirB POST mc i aq (Z_to_bv 8 120) 8 (FMT + i + 4)); [exact IV | exact DIR | lia | lia | right; right; right; reflexivity |].
        clear mc IV DIR. intros mc dcs IV DIR SZ. intros.
        replace (FMT + i + 4)%Z with (FMT + (i + 4))%Z by lia.
        eapply (L_after (i + 4)%Z mc dcs); [exact IV | exact DIR | exact SZ | lia |].
        clear mc dcs IV DIR SZ. intros mc IV DIR. intros.
        eapply (IH (i + 4)%Z mc); [exact IV | exact DIR | lia | | exact OK | exact AOK].
        replace (Z.to_nat (i + 4)) with (Z.to_nat i + 4)%nat by lia. exact SK'.
      + (* [comment removed for export] *)
        destruct AOK as [PS AOK]. destruct PS as (VAQ & SEPV & SSTR & SNOZ & SEPS & SPOS & (APPS & USTR & NSZ & RLO & RHI & R1 & WR1 & RSH1) & RVA & RS).
        assert (H37 : nth_error fstr (Z.to_nat i) = Some (Z_to_bv 8 37)) by (rewrite <- (Nat.add_0_r (Z.to_nat i)); apply NTH; reflexivity).
        assert (Hc : nth_error fstr (Z.to_nat (i + 1)) = Some (Z_to_bv 8 115)) by (replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia; apply NTH; reflexivity).
        assert (SC : sconv (bv_unsigned (Z_to_bv 8 115))) by reflexivity.
        eapply (L_dirA POST mc i aq (Z_to_bv 8 37) (Z_to_bv 8 115)); [exact IV | exact DIR | lia | lia | exact H37 | reflexivity | exact Hc | exact (proj1 (sfacts _ SC)) |].
        clear mc IV DIR. intros mc IV DIR. intros.
        rewrite <- (Z_to_bv_bv_unsigned aq).
        eapply (L_dirS (bv_unsigned aq) Sa sstr RLO RHI); try eassumption; try lia.
        unfold KS. clear mc IV DIR. intros mc dcs IV DIR SZ. intros.
        replace (FMT + i + 2)%Z with (FMT + (i + 2))%Z by lia.
        eapply (L_after (i + 2)%Z mc dcs); [exact IV | exact DIR | exact SZ | lia |].
        clear mc dcs IV DIR SZ. intros mc IV DIR. intros.
        eapply (IH (i + 2)%Z mc); [exact IV | exact DIR | lia | | exact OK | exact AOK].
        replace (Z.to_nat (i + 2)) with (Z.to_nat i + 2)%nat by lia. exact SK'.
  Qed.

  (* [comment removed for export] *)
  Definition printf_common_items__stmt : Prop := forall its,
    fstr = prender its -> Forall pitem_ok its -> pargs_ok its a2 ->
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x4729c) fc None m (seg_rom asegs)).
  Section Sz41.
  Variables its : ltac2:(SecDiet.SzSec.tyM 'printf_common_items__stmt "v" @its).
  #[using="FMT RLOf RHIf MI ST LO KLO GOT SHB A1 FB NOZ LAY SEPF APPF UFMT NFZ R1F WR1F RI RSTK RFM RSHF"] Lemma printf_common_items__body : ltac2:(SecDiet.SzSec.bodyP 'printf_common_items__stmt "v").
  Proof.
    intros EF OK AOK.
    eapply (L_entry_chk POST). intros mc. intros until x31. intros IVF.
    destruct (Z.eq_dec L 0) as [L0 | LN].
    - eapply L_entry0; eassumption.
    - eapply (L_entry1 ltac:(lia) POST); [| exact IVF].
      clear mc IVF. intros mc dj IV DIR. intros.
      eapply (L_head POST mc [CB 40 dj]); [exact IV | exact DIR | reflexivity |].
      clear mc dj IV DIR. intros mc IV DIR. intros.
      replace (Z_to_bv 64 FMT) with (Z_to_bv 64 (FMT + 0)) by (f_equal; lia).
      eapply (L_items its 0 mc a2); [exact IV | exact DIR | lia | cbn [Z.to_nat skipn]; exact EF | exact OK | exact AOK].
  Qed.
  End Sz41.
  #[using="FMT RLOf RHIf MI ST LO KLO GOT SHB A1 FB NOZ LAY SEPF APPF UFMT NFZ R1F WR1F RI RSTK RFM RSHF"] Theorem printf_common_items : ltac:(let t := eval cbv delta [printf_common_items__stmt] in printf_common_items__stmt in exact t).
  Proof. intros its. ltac2:(SecDiet.SzSec.closeP 'printf_common_items__body "v"). Qed.

End PC.
End CANSEC1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Theorem printf_common_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FMT : Z) (fstr : list byte) (its : list pitem),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2320)%Z -> (KHIGH <= lo)%Z ->
  icptenv m -> a1 = Z_to_bv 64 FMT ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0%Z) fstr ->
  (FMT + (Z.of_nat (length fstr) + 1) <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= FMT)%Z ->
  sobj RNG m FMT (FMT + (Z.of_nat (length fstr) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG FMT (Z.of_nat (length fstr) + 1) ->
  fstr = prender its -> Forall pitem_ok its -> pargs_ok RNG sp m its a2 ->
  evtF asegs RNG (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4729c) fc None m (seg_rom asegs)).
Proof.
  intros until its. intros MI ST LO KLO ENV A1 FB NOZ SEPF (APPF & UFMT & NFZ & RLOf & RHIf & R1F & WR1F & RSHF) RI RSTK RFM EF OK AOK.
  eapply (printf_common_items RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr RLOf RHIf);
    first [ eassumption | exact (ie_got _ ENV) | exact (ie_shb _ ENV) | exact (ie_lay _ ENV) | lia ].
Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_irt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
Local Ltac mem_after_store ::= cbv beta; try rewrite le1_unsigned8; mem_after_store_fast.

Section CANSEC1. Context {rc : runConstT}.
Section PC.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (FMT : Z) (fstr : list byte) (RLOf RHIf : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2320)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis A1 : a1 = Z_to_bv 64 FMT.
  Hypothesis FB : bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]).
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) fstr.
  Notation L := (Z.of_nat (length fstr)).
  Notation NF := (Z.of_nat (length fstr) + 1)%Z.
  (* [comment removed for export] *)
  Hypothesis LAY : rt_layout m.
  Hypothesis SEPF : (FMT + NF <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= FMT)%Z.
  Hypothesis APPF : app_blk FMT (FMT + NF).
  Hypothesis UFMT : unpoisoned m FMT (FMT + NF).
  Hypothesis NFZ : (NF <= 2^40)%Z.
  Hypothesis R1F : (RLOf <= FMT /\ FMT + NF <= RHIf /\ RLOf mod 64 = 0 /\ RHIf mod 64 = 0 /\ 0 <= RLOf /\ RHIf <= KEND)%Z.
  Hypothesis WR1F : wr_at asegs m (shad RLOf) (shad RHIf - shad RLOf).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFM : rng RNG FMT NF.
  Hypothesis RSHF : rng RNG (shad RLOf) (shad RHIf - shad RLOf).

  Notation W := [(bv_unsigned sp + -2320, bv_unsigned sp)]%Z.
  Notation SAVES := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation PAT := 12297829382473034410%Z.

  (* [comment removed for export] *)
  Definition INV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -104) SAVES
    /\ (exists j0, rw_cells asegs mc (bv_unsigned sp + -2240) [CB 8 j0; C8 (Z_to_bv 64 (bv_unsigned sp + -120)); C8 a0])
    /\ stk asegs mc (bv_unsigned sp + -2176) (bv_unsigned sp + -104)
    /\ stk asegs mc lo (bv_unsigned sp + -2240)
    /\ munch W m mc /\ wmono asegs m mc /\ mem_inv asegs mc /\ rt_got mc /\ rt_shbase mc.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2320 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64
     /\ 0 <= FMT /\ FMT + L + 1 + 8 <= 2^47 /\ 0 <= L /\ L + 1 <= 2^40
     /\ (FMT + L + 1 <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= FMT))%Z.
  #[using="m RLOf RHIf ST LO KLO SEPF APPF NFZ"] Lemma BL_ok : BL.
  Proof.
    unfold BL. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R.
    destruct ST as (L0 & _). destruct APPF as [LES AS]. unfold KLOW, KHIGH, KEND in *. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac hide_sec :=
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in FB;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in SEPF; change (?P) with (sf_hide P) in APPF; change (?P) with (sf_hide P) in UFMT;
    change (?P) with (sf_hide P) in R1F; change (?P) with (sf_hide P) in WR1F; change (?P) with (sf_hide P) in LAY.
  Ltac inv_open H := let j0 := fresh "j0" in destruct H as (FRT & (j0 & FRL) & STM & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1).
  Ltac prep IV :=
    inv_open IV;
    let B := fresh "B" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2320) 2320) by (eapply rng_sub'; [exact RSTK| lia]);
    hide_sec.

  (* [comment removed for export] *)
  #[using="lo RLOf RHIf ST LO KLO FB SEPF APPF NFZ"] Lemma fmt_rd : forall mc (i : Z) b, mem_inv asegs mc -> munch W m mc ->
    nth_error (fstr ++ [Z_to_bv 8 0]) (Z.to_nat i) = Some b -> (0 <= i)%Z ->
    ov_read_bytes asegs mc (wa (FMT + i)) 1 = Some [b].
  Proof.
    intros mc i b MIc MUc Hn Hi. pose proof BL_ok as B; unfold BL in B.
    eapply u8ro_read; [| exact Hn | exact Hi | reflexivity].
    eapply bytes_at_transport; [exact FB | exact MUc |]. rewrite length_app; cbn [length disjoint_from]. clear - SEPF B. lia.
  Qed.

  Ltac fmt_read i b Hn :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with MUc : munch _ m mc, MIc : mem_inv _ mc |- _ =>
        let H := fresh "RD" in
        pose proof (fmt_rd mc i b MIc MUc ltac:(rewrite nth_error_app1 by lia; exact Hn) ltac:(lia)) as H
    end end.

  (* [comment removed for export] *)
  Ltac prem :=
    lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- mem_inv _ _ => first [assumption | eassumption | idtac "prem: mem_inv"; fail]
    | |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite !unsigned_lit by lia; prem
    | |- stk _ _ _ _ => first [assumption | eassumption | idtac "prem: stk"; fail]
    | |- find_byte _ _ = _ => first [eassumption | idtac "prem: find_byte"; fail]
    | |- rw_cells _ _ _ _ => first [eassumption | idtac "prem: rw_cells"; fail]
    | |- u8arr _ _ _ _ => first [eassumption | idtac "prem: u8arr"; fail]
    | |- bytes_at _ _ _ _ => first [eassumption | first [apply flags_bytes | apply jzt_bytes | apply ccss_bytes | apply fltcv_bytes | apply dioux_bytes | apply cs_bytes | apply csb_bytes | apply ss_bytes | idtac "prem: bytes_at"; fail]; assumption]
    | |- Forall _ _ => first [exact flags_noz | exact jzt_noz | exact ccss_noz | exact fltcv_noz | exact dioux_noz | exact cs_noz | exact csb_noz | exact ss_noz | assumption | idtac "prem: Forall"; fail]
    | |- _ = Z_to_bv 64 _ => first [reflexivity | idtac "prem: eq"; fail]
    | |- rng _ _ _ => first [ assumption | eapply rng_sub'; [exact RI | cbn; unfold sf_hide in *; lia] | eapply rng_sub'; [exact RSTK | unfold sf_hide in *; lia] | idtac "prem: rng"; fail ]
    | |- ?g => unfold sf_hide in *; first [lia | cbv; discriminate | cbn; lia | idtac "prem: other" g; fail]
    end.

  (* [comment removed for export] *)
  Ltac br CC := let K := fresh "K" in if_cases K; zify_cond K; try (exfalso; clear -K CC; lia); [clear K].

  Notation CONT Q x19v x21v mc dcs :=
    (forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) x19v (Z_to_bv 64 0x15358) x21v y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
             F (Z_to_bv 64 0x47418) fc None mc (seg_rom asegs))) (only parsing).

  Notation POST := (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition INVF (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -104) SAVES
    /\ (exists j3, rw_cells asegs mc (bv_unsigned sp + -2240) [CB 24 j3])
    /\ (exists dj, rw_cells asegs mc (bv_unsigned sp + -2216) [CB 40 dj])
    /\ stk asegs mc (bv_unsigned sp + -2176) (bv_unsigned sp + -104)
    /\ stk asegs mc lo (bv_unsigned sp + -2240)
    /\ munch W m mc /\ wmono asegs m mc /\ mem_inv asegs mc /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc FMT (FMT + NF) /\ wr_at asegs mc (shad RLOf) (shad RHIf - shad RLOf).

  Definition BNDF : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2320 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64
     /\ 1 <= NF /\ NF <= 2^40
     /\ 0 <= FMT /\ FMT + NF + 8 <= KEND
     /\ 2147450880 <= shad RLOf /\ shad RLOf <= shad FMT /\ shad (FMT + NF - 1) + 1 <= shad RHIf /\ shad RHIf <= KHIGH
     /\ 0 <= Z.shiftr FMT 3 < 2^44 /\ -1 <= Z.shiftr (FMT + NF + -1) 3 < 2^44
     /\ shad RLOf mod 8 = 0 /\ shad RHIf mod 8 = 0
     /\ RLOf <= FMT /\ FMT + NF <= RHIf /\ RLOf mod 64 = 0 /\ RHIf mod 64 = 0)%Z.
  #[using="m ST LO KLO APPF NFZ R1F"] Lemma BNDF_ok : BNDF.
  Proof.
    unfold BNDF. destruct ST as (LOW & _). destruct APPF as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. Z.div_mod_to_equations; lia.
  Qed.
  Ltac acc_facts B ::= pose proof BNDF_ok as B; unfold BNDF, KHIGH, KEND in B.

  Definition BLF : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2320 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64
     /\ 1 <= NF /\ NF <= 2^40 /\ 0 <= FMT /\ FMT + NF + 8 <= 2^47
     /\ 0 <= Z.shiftr FMT 3 < 2^44 /\ -1 <= Z.shiftr (FMT + NF + -1) 3 < 2^44
     /\ 2147450880 <= shad RLOf /\ shad RLOf <= shad FMT /\ shad (FMT + NF - 1) + 1 <= shad RHIf /\ shad RHIf <= 17594333495296)%Z.
  #[using="m ST LO KLO APPF NFZ R1F"] Lemma BLF_ok : BLF. Proof. pose proof BNDF_ok as B. unfold BNDF, KHIGH, KEND in B. unfold BLF. repeat split; lia. Qed.

  Ltac invf_open H := let j3 := fresh "j3" in let dj := fresh "dj" in
    destruct H as (FRT & (j3 & FRL3) & (dj & FRD) & STM & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UF1 & WRF1).
  Ltac fprep IV :=
    pose proof IV as IV0; invf_open IV;
    pose proof BLF_ok as BL0; unfold BLF in BL0;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2320) 2320) by (eapply rng_sub'; [exact RSTK| lia]);
    hide_sec.

  Definition invf_of__stmt : Prop := forall mc j3 dj,
    rw_cells asegs mc (bv_unsigned sp + -104) SAVES ->
    rw_cells asegs mc (bv_unsigned sp + -2240) [CB 24 j3] -> rw_cells asegs mc (bv_unsigned sp + -2216) [CB 40 dj] ->
    stk asegs mc (bv_unsigned sp + -2176) (bv_unsigned sp + -104) -> stk asegs mc lo (bv_unsigned sp + -2240) ->
    munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> INVF mc.
  Section Sz5.
  Variables mc j3 dj : ltac2:(SecDiet.SzSec.tyM 'invf_of__stmt "vvv" @mc).
  #[using="ST LO KLO GOT SHB LAY APPF UFMT NFZ R1F WR1F"] Lemma invf_of__body : ltac2:(SecDiet.SzSec.bodyP 'invf_of__stmt "vvv").
  Proof.
    intros FRT FRL3 FRD STM ST1 MU1 WM1 MI1.
 pose proof BNDF_ok as B. unfold BNDF, KHIGH, KEND in B.
    split; [exact FRT|]. split; [eexists; exact FRL3|]. split; [eexists; exact FRD|]. repeat (split; [assumption|]).
    split. { eapply rw_cells_transport; [exact GOT | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    split. { eapply rw_cells_transport; [exact SHB | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    split. { eapply rw_cells_transport; [exact LAY | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (SS : (shad (FMT + NF - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UFMT | exact MU1 |]. cbn [disjoint_from]. lia. }
    eapply wr_at_transport; eassumption.
  Qed.
  End Sz5.
  #[using="ST LO KLO GOT SHB LAY APPF UFMT NFZ R1F WR1F"] Lemma invf_of : ltac:(let t := eval cbv delta [invf_of__stmt] in invf_of__stmt in exact t).
  Proof. intros mc j3 dj. ltac2:(SecDiet.SzSec.closeP 'invf_of__body "vvv"). Qed.

  (* [comment removed for export] *)
  Definition fregs (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp s1 x10 x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 NF) (Z_to_bv 64 FMT) s4 a2 s6 a0 (Z_to_bv 64 (bv_unsigned sp + -2184)) s9 s10 s11 x28 x29 x30 x31.

  Section FmtCheck.
  Variable Q : machine_state -> Prop.
  (* [comment removed for export] *)
  Hypothesis KF : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31, INVF mc ->
    evtF asegs RNG Q (MS (fregs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31) F (Z_to_bv 64 0x473ac) fc None mc (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SLf__stmt : Prop := forall mc (k : nat) (c : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    INVF mc -> (1 <= NF <= 64)%Z -> Z.to_nat (shad (FMT + NF - 1) - c) = k -> (shad FMT <= c < shad (FMT + NF - 1))%Z ->
    evtF asegs RNG Q (MS (fregs x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (FMT + NF + -1) 3)) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                                   x28 x29 x30 x31)
                            F (Z_to_bv 64 0x47cc8) fc None mc (seg_rom asegs)).
  Section Sz6.
  Variables mc c x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'SLf__stmt "vkvvvvvvvvvvvvvv" @mc).
  #[using="ST LO KLO APPF NFZ R1F RSTK RSHF KF"] Lemma SLf__body : ltac2:(SecDiet.SzSec.bodyP 'SLf__stmt "vkvvvvvvvvvvvvvv").
  Proof.
    intros k IV N1 Hk Hc.
 unfold fregs. fprep IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (FMT + NF - 1) = 2147450880 + Z.shiftr (FMT + NF + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc FMT (FMT + NF) c UF1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply KF; eassumption.
  Qed.
  End Sz6.
  #[using="ST LO KLO APPF NFZ R1F RSTK RSHF KF"] Lemma SLf : ltac:(let t := eval cbv delta [SLf__stmt] in SLf__stmt in exact t).
  Proof. intros mc k c x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'SLf__body "vkvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition SEf__stmt : Prop := forall mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31, INVF mc -> (1 <= NF <= 64)%Z ->
    evtF asegs RNG Q (MS (fregs x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr FMT 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (FMT + NF + -1) 3))
                                   (Z_to_bv 64 (FMT + NF + -1)) x13 x14 x15 x16 x17 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x47cac) fc None mc (seg_rom asegs)).
  Section Sz7.
  Variables mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'SEf__stmt "vvvvvvvvvvvvvv" @mc).
  #[using="ST LO KLO APPF NFZ R1F RSTK RSHF KF"] Lemma SEf__body : ltac2:(SecDiet.SzSec.bodyP 'SEf__stmt "vvvvvvvvvvvvvv").
  Proof.
    intros IV N1.
 unfold fregs. fprep IV.
    destruct (unpoisoned_check_rd asegs mc FMT (FMT + NF) (FMT + NF + -1) 1 UF1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((FMT + NF + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply KF; eassumption.
    - eapply (SLf mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.
  End Sz7.
  #[using="ST LO KLO APPF NFZ R1F RSTK RSHF KF"] Lemma SEf : ltac:(let t := eval cbv delta [SEf__stmt] in SEf__stmt in exact t).
  Proof. intros mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'SEf__body "vvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition SCf__stmt : Prop := forall mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31, INVF mc ->
    evtF asegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp s1 (Z_to_bv 64 L) x11 x12 x13 x14 x15 x16 x17
                                 s2 (Z_to_bv 64 FMT) s4 a2 s6 a0 (Z_to_bv 64 (bv_unsigned sp + -2184)) s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x47360) fc None mc (seg_rom asegs)).
  Section Sz8.
  Variables mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'SCf__stmt "vvvvvvvvvvvvvvvv" @mc).
  Lemma SCf__body : ltac2:(SecDiet.SzSec.bodyP 'SCf__stmt "vvvvvvvvvvvvvvvv").
  Proof using APPF GOT KF KLO LAY LO NFZ R1F RI RSHF RSTK SHB ST UFMT WR1F.
    intros IV.
 fprep IV.
    do 3 zstep.
    rewrite zb_lxor_ones by lia. if_cases K0; zify_cond K0. { exfalso. clear -K0 BL0. lia. } clear K0.
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0. lia. } clear K3.
      zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | (keep_hyps sp lo fstr RLOf RHIf LO; lia) | unfold KHIGH; (keep_hyps sp lo FMT fstr RLOf RHIf BL0; lia) | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APPF | zsimp; exact UF1
        | zsimp; pose proof BNDF_ok as B9; unfold BNDF in B9; (keep_hyps fstr RLOf RHIf NFZ; lia)
        | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo fstr RLOf RHIf; lia)] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply KF. eapply invf_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= NF <= 64)%Z) by (clear - K2 BL0; lia).
      do 4 zstep. replace (L + FMT)%Z with (FMT + NF + -1)%Z by lia.
      do 6 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1F.
      destruct (shadow_probe8 asegs mc RLOf RHIf FMT WRF1 ltac:(apply no_image_asan; pose proof BNDF_ok as B9; unfold BNDF in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1F; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLOf RHIf (FMT + NF + -1) WRF1 ltac:(apply no_image_asan; pose proof BNDF_ok as B9; unfold BNDF in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1F; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply SEf; eassumption.
      + eapply KF; eassumption.
  Qed.
  End Sz8.
  #[using="ST LO KLO GOT SHB LAY APPF UFMT NFZ R1F WR1F RI RSTK RSHF KF"] Lemma SCf : ltac:(let t := eval cbv delta [SCf__stmt] in SCf__stmt in exact t).
  Proof. intros mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'SCf__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="lo FMT fstr RLOf RHIf MI ST LO KLO GOT SHB A1 FB NOZ LAY SEPF APPF UFMT NFZ R1F WR1F RI RSTK RFM RSHF KF"] Lemma L_entry_chk :
    evtF asegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x47304) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as B; unfold BL in B.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2320) 2320) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof FB as FBc. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof ST as ST0.
    hide_sec.
    subst a1.
    carve_frame 104%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2176) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    carve_frame 40%nat ST1. carve_frame 24%nat ST1.
    do 16 zstep. do 6 zstep. zstep.
    call istrlen_spec; [ exact MIc | rewrite unsigned_lit by lia; exact FBc | exact NOZ | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RFM| lia] | ].
    eapply SCf. unfold sf_hide in *. eapply invf_of; eassumption.
  Qed.
  End FmtCheck.

  Ltac norm_stk H tgt :=
    lazymatch type of H with stk _ _ _ ?hi =>
      replace hi with tgt in H by (cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia) end.

  (* [comment removed for export] *)
  Definition L_entry0__stmt : Prop := L = 0%Z -> forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31, INVF mc ->
    evtF asegs RNG POST (MS (fregs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31) F (Z_to_bv 64 0x473ac) fc None mc (seg_rom asegs)).
  Section Sz10.
  Variables mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'L_entry0__stmt "hvvvvvvvvvvvvvvvvv" @mc).
  #[using="ST LO KLO FB NOZ SEPF APPF UFMT NFZ R1F RSTK RFM"] Lemma L_entry0__body : ltac2:(SecDiet.SzSec.bodyP 'L_entry0__stmt "hvvvvvvvvvvvvvvvvv").
  Proof.
    intros L0 IV.
 unfold fregs. fprep IV.
    assert (HL : nth_error (fstr ++ [Z_to_bv 8 0]) (Z.to_nat 0) = Some (Z_to_bv 8 0)).
    { destruct fstr; [reflexivity | cbn [length] in L0; lia]. }
    do 3 zs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc' _) => lazymatch goal with MUc : munch _ m mc', MIc : mem_inv _ mc' |- _ =>
      pose proof (fmt_rd mc' 0 (Z_to_bv 8 0) MIc MUc HL ltac:(lia)) as RD; rewrite Z.add_0_r in RD end end.
    zs. cbv beta. rewrite unsigned_lit8 by lia. zs. assert (CC : True) by exact I. br CC.
    (* [comment removed for export] *) clear RD. zs. do 13 zs. zs. zs.
    match goal with H : rw_cells asegs _ (bv_unsigned sp + -2240) _ |- _ => rename H into FRL end.
    pose proof (stk_release _ _ _ _ _ ST1 FRL ltac:(lia)) as SK1. norm_stk SK1 (bv_unsigned sp + -2216)%Z.
    pose proof (stk_release _ _ _ _ _ SK1 FRD ltac:(lia)) as SK2. norm_stk SK2 (bv_unsigned sp + -2176)%Z.
    pose proof (stk_merge _ _ _ _ _ SK2 STM ltac:(lia)) as SK3.
    pose proof (stk_release _ _ _ _ _ SK3 FRT ltac:(lia)) as SK4. norm_stk SK4 (bv_unsigned sp).
    replace (bv_unsigned sp + -2320)%Z with (bv_unsigned sp - 2320)%Z in MU1 by lia.
    finish.
  Qed.
  End Sz10.
  #[using="ST LO KLO FB NOZ SEPF APPF UFMT NFZ R1F RSTK RFM"] Lemma L_entry0 : ltac:(let t := eval cbv delta [L_entry0__stmt] in L_entry0__stmt in exact t).
  Proof. intros L0 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'L_entry0__body "hvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition L_entry1__stmt : Prop := (0 < L)%Z -> forall Q,
    (forall mc dj, INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) [CB 40 dj] ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 FMT) (Z_to_bv 64 0x15358) a2 y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
             F (Z_to_bv 64 0x47418) fc None mc (seg_rom asegs))) ->
    forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31, INVF mc ->
    evtF asegs RNG Q (MS (fregs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31) F (Z_to_bv 64 0x473ac) fc None mc (seg_rom asegs)).
  Section Sz11.
  Variables Q mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : ltac2:(SecDiet.SzSec.tyM 'L_entry1__stmt "hvhvvvvvvvvvvvvvvvvv" @Q).
  #[using="ST LO KLO FB NOZ SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_entry1__body : ltac2:(SecDiet.SzSec.bodyP 'L_entry1__stmt "hvhvvvvvvvvvvvvvvvvv").
  Proof.
    intros LP K IV.
 unfold fregs. fprep IV.
    do 3 zs.
    (* [comment removed for export] *)
    destruct (nth_error fstr 0) as [c0|] eqn:E0. 2:{ exfalso. apply nth_error_None in E0. lia. }
    assert (NZ0 : bv_unsigned c0 <> 0%Z) by (eapply (proj1 (Forall_forall _ _) NOZ); eapply nth_error_In; exact E0).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc' _) => lazymatch goal with MUc : munch _ m mc', MIc : mem_inv _ mc' |- _ =>
      pose proof (fmt_rd mc' 0 c0 MIc MUc ltac:(rewrite nth_error_app1 by lia; exact E0) ltac:(lia)) as RD0; rewrite Z.add_0_r in RD0 end end.
    zs. zs. if_cases K4; zify_cond K4. { exfalso. clear - K4 NZ0. pose proof (bv_unsigned_in_range 8 c0). cbn in *. lia. } clear K4 RD0.
    do 17 zs.
    eapply K. 2:{ exact FRD. }
    split; [exact FRT|]. split; [eexists; match goal with H : rw_cells asegs _ (bv_unsigned sp + -2240) _ |- _ => exact H end|].
    unfold sf_hide in *. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz11.
  #[using="ST LO KLO FB NOZ SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_entry1 : ltac:(let t := eval cbv delta [L_entry1__stmt] in L_entry1__stmt in exact t).
  Proof. intros LP Q K mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31. ltac2:(SecDiet.SzSec.closeP 'L_entry1__body "hvhvvvvvvvvvvvvvvvvv"). Qed.

  Notation dcells1 :=
    ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3)]) (only parsing).

  (* [comment removed for export] *)
  Definition lregs (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 : word) (p aq : word) (y22 y28 y29 y30 y31 : word) :=
    mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
        (Z_to_bv 64 10) p (Z_to_bv 64 0x15358) aq y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
        (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31.

  (* [comment removed for export] *)
  Definition L_head__stmt : Prop := forall Q mc dcs p aq,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    (forall mc', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcells1 ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 p aq y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x47444) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 p aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x47418) fc None mc (seg_rom asegs)).
  Section Sz12.
  Variables Q mc dcs p aq : ltac2:(SecDiet.SzSec.tyM 'L_head__stmt "vvvvv" @Q).
  #[using="FMT fstr RLOf RHIf ST LO KLO SEPF APPF NFZ R1F RSTK"] Lemma L_head__body : ltac2:(SecDiet.SzSec.bodyP 'L_head__stmt "vvvvv").
  Proof.
    intros IV DIR SZ K.
 intros. unfold lregs. prep IV.
    destruct (rw_cells_forget _ _ _ _ DIR) as [dj DJ]. rewrite SZ in DJ. clear DIR.
    do 5 zs. do 5 zs.
    destruct (u8arr_of_chunk _ _ _ _ DJ) as (dj2 & DA & DL). cbn in DL. clear DJ.
    call imemset_specZ; [ exact MI1 | exact DA | rewrite DL; reflexivity | lia | lia | lia | cbv; discriminate | ].
    match goal with H : u8arr asegs ?mc _ _ |- _ => rewrite ?unsigned_lit in H by lia;
      apply rw_cells_of_u8arr in H; recell H 0%nat 1%nat (zcells0 : list cell); rename H into DIR end.
    zs.
    eapply K. 2:{ exact DIR. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz12.
  #[using="FMT fstr RLOf RHIf ST LO KLO SEPF APPF NFZ R1F RSTK"] Lemma L_head : ltac:(let t := eval cbv delta [L_head__stmt] in L_head__stmt in exact t).
  Proof. intros Q mc dcs p aq. ltac2:(SecDiet.SzSec.closeP 'L_head__body "vvvvv"). Qed.


  (* [comment removed for export] *)
  Definition fmt_char__stmt : Prop := forall mc (i : Z), mem_inv asegs mc -> munch W m mc -> (0 <= i < L)%Z ->
    exists b, nth_error fstr (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z /\ (0 <= bv_unsigned b < 256)%Z /\
              ov_read_bytes asegs mc (wa (FMT + i)) 1 = Some [b].
  Section Sz13.
  Variables mc i : ltac2:(SecDiet.SzSec.tyM 'fmt_char__stmt "vv" @mc).
  #[using="lo RLOf RHIf ST LO KLO FB NOZ SEPF APPF NFZ R1F"] Lemma fmt_char__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_char__stmt "vv").
  Proof.
    intros MIc MUc Hi.
    destruct (nth_error fstr (Z.to_nat i)) as [b|] eqn:E. 2:{ exfalso. apply nth_error_None in E. lia. }
    exists b. split; [reflexivity|]. split.
    { eapply (proj1 (Forall_forall _ _) NOZ). eapply nth_error_In; exact E. }
    split. { pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
    eapply fmt_rd; [exact MIc | exact MUc | rewrite nth_error_app1 by lia; exact E | lia].
  Qed.
  End Sz13.
  #[using="lo RLOf RHIf ST LO KLO FB NOZ SEPF APPF NFZ R1F"] Lemma fmt_char : ltac:(let t := eval cbv delta [fmt_char__stmt] in fmt_char__stmt in exact t).
  Proof. intros mc i. ltac2:(SecDiet.SzSec.closeP 'fmt_char__body "vv"). Qed.

  (* [comment removed for export] *)
  Definition L_skip__stmt : Prop := forall Q mc (k : nat) (i : Z) aq,
    mem_inv asegs mc -> munch W m mc -> (0 <= i)%Z -> (i + Z.of_nat k <= L)%Z ->
    (forall j b, (Z.to_nat i <= j < Z.to_nat i + k)%nat -> nth_error fstr j = Some b -> bv_unsigned b <> 37%Z) ->
    (forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + (i + Z.of_nat k))) aq y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x47444) fc None mc (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x47444) fc None mc (seg_rom asegs)).
  Section Sz14.
  Variables Q mc : ltac2:(SecDiet.SzSec.tyM 'L_skip__stmt "vvk" @Q).
  #[using="lo RLOf RHIf ST LO KLO FB NOZ SEPF APPF NFZ R1F RFM"] Lemma L_skip__body : ltac2:(SecDiet.SzSec.bodyP 'L_skip__stmt "vvk").
  Proof.
    intros k.
 induction k as [|k IH]; intros i aq MIc MUc Hi Hk NP K; intros.
    - specialize (K y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31).
      rewrite Z.add_0_r in K. exact K.
    - pose proof BL_ok as B; unfold BL in B. unfold lregs.
      destruct (fmt_char mc i MIc MUc ltac:(lia)) as (b & Hn & NZ & RB & RD).
      assert (NP0 : bv_unsigned b <> 37%Z) by (eapply NP; [|exact Hn]; lia).
      zs. zs. if_cases K1; zify_cond K1. { exfalso. clear -K1 NP0 RB. lia. }
      zs. if_cases K2; zify_cond K2. { exfalso. clear -K2 NZ RB. lia. }
      zs. zs. zs.
      replace (FMT + i + 1)%Z with (FMT + (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [exact MIc | exact MUc | lia | lia | | ].
      { intros j b' Hj Hb'. eapply NP; [|exact Hb']. lia. }
      intros. replace (i + 1 + Z.of_nat k)%Z with (i + Z.of_nat (S k))%Z by lia. apply K.
  Qed.
  End Sz14.
  #[using="lo RLOf RHIf ST LO KLO FB NOZ SEPF APPF NFZ R1F RFM"] Lemma L_skip : ltac:(let t := eval cbv delta [L_skip__stmt] in L_skip__stmt in exact t).
  Proof. intros Q mc k. ltac2:(SecDiet.SzSec.closeP 'L_skip__body "vvk"). Qed.


  (* [comment removed for export] *)
  Definition dirA_ok (c : Z) : Prop :=
    find_byte c B_FLAGS = None /\ find_byte c B_JZT = None /\ (58 <= c < 256)%Z /\ c <> 108%Z /\ c <> 104%Z.
  (* [comment removed for export] *)
  Definition intconv (c : Z) : Prop := c = 100%Z \/ c = 105%Z \/ c = 117%Z \/ c = 120%Z.
  #[using="fstr RLOf RHIf"] Lemma cfacts : forall c, intconv c ->
    dirA_ok c /\ find_byte c B_CCSS = None /\ find_byte c B_FLTCV = None
    /\ (exists ix, find_byte c B_DIOUX = Some ix) /\ (58 <= c < 256)%Z /\ c <> 109%Z /\ c <> 110%Z.
  Proof. intros c [-> | [-> | [-> | ->]]]; repeat split; try (cbv; reflexivity); try lia; eexists; cbv; reflexivity. Qed.
  (* [comment removed for export] *)
  Definition sconv (c : Z) : Prop := c = 115%Z.
  #[using="fstr RLOf RHIf"] Lemma sfacts : forall c, sconv c ->
    dirA_ok c /\ (58 <= c < 256)%Z /\ c <> 109%Z /\ c <> 110%Z
    /\ find_byte c B_CCSS = Some 2%nat /\ find_byte c B_CS = None /\ find_byte c B_CSB = Some 1%nat /\ find_byte c B_SS = Some 0%nat.
  Proof. intros c ->; repeat split; try (cbv; reflexivity); lia. Qed.

  #[using="Type"] Lemma istrchr_res_none : forall A str c, find_byte c str = None -> istrchr_res A str c = 0%Z.
  Proof. intros A str c H. unfold istrchr_res. rewrite H. reflexivity. Qed.

  Notation dcellsG fw p e lm bc :=
    ([C4 (Z_to_bv 64 fw); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 e);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 lm; C1 (Z_to_bv 8 0); C1 bc; CB 3 (repeat (Z_to_bv 8 0) 3)]) (only parsing).
  Notation dcellsA p bc := (dcellsG 0 p (p + 2) (Z_to_bv 8 0) bc) (only parsing).

  (* [comment removed for export] *)
  Definition L_dirA__stmt : Prop := forall Q mc (i : Z) aq b37 bc,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcells1 ->
    (0 <= i)%Z -> (i + 2 <= L)%Z ->
    nth_error fstr (Z.to_nat i) = Some b37 -> bv_unsigned b37 = 37%Z ->
    nth_error fstr (Z.to_nat (i + 1)) = Some bc -> dirA_ok (bv_unsigned bc) ->
    (forall mc', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) (dcellsA (FMT + i) bc) ->
       forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp (Z_to_bv 64 (FMT + i)) (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x15358) aq (Z_to_bv 64 (FMT + i + 1)) (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                           F (Z_to_bv 64 0x475c0) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x47444) fc None mc (seg_rom asegs)).
  Section Sz18.
  Variables Q mc i aq b37 bc : ltac2:(SecDiet.SzSec.tyM 'L_dirA__stmt "vvvvvv" @Q).
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_dirA__body : ltac2:(SecDiet.SzSec.bodyP 'L_dirA__stmt "vvvvvv").
  Proof.
    intros IV DIR Hi HiL H37 E37 Hc HC K.
 intros. unfold lregs. prep IV.
    destruct HC as (NF1 & NF2 & CR & N108 & N104).
    pose proof (conj CR (conj N108 N104)) as CC.
    fmt_read i b37 H37. zs. clear RD. cbv beta. rewrite E37. zs. br CC.
    (* [comment removed for export] *) zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta.
    zs. br CC.
    (* [comment removed for export] *) zs. br CC.
    zs. zs. zs. br CC.
    (* [comment removed for export] *) zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
    call istrchr_spec; [ eassumption | apply flags_bytes; assumption | exact flags_noz | reflexivity | clear -CC; lia
                       | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    rewrite (istrchr_res_none _ _ _ NF1).
    (* [comment removed for export] *) zs. zs. zs. br CC.
    replace (FMT + (i + 1) + 1 + -1)%Z with (FMT + (i + 1))%Z by lia.
    fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. br CC.
    (* [comment removed for export] *) zs. replace (FMT + (i + 1) + 1 + -1)%Z with (FMT + (i + 1))%Z by lia.
    zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. br CC.
    (* [comment removed for export] *) zs. zs. br CC.
    (* [comment removed for export] *) zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
    call istrchr_spec; [ eassumption | apply jzt_bytes; assumption | exact jzt_noz | reflexivity | clear -CC; lia
                       | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    rewrite (istrchr_res_none _ _ _ NF2).
    (* [comment removed for export] *) fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. br CC.
    (* [comment removed for export] *) zs. zs. br CC. zs. zs. br CC.
    (* [comment removed for export] *) fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
    zs. br CC.
    replace (FMT + (i + 1) + 1)%Z with (FMT + i + 2)%Z by lia. replace (FMT + (i + 1))%Z with (FMT + i + 1)%Z by lia.
    eapply K. 2:{ match goal with H : rw_cells asegs _ (bv_unsigned sp + -2216) _ |- _ => exact H end. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz18.
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_dirA : ltac:(let t := eval cbv delta [L_dirA__stmt] in L_dirA__stmt in exact t).
  Proof. intros Q mc i aq b37 bc. ltac2:(SecDiet.SzSec.closeP 'L_dirA__body "vvvvvv"). Qed.


  (* [comment removed for export] *)
  Definition L_dirB__stmt : Prop := forall Q mc (i : Z) aq bc (fw e : Z),
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) (dcellsG fw (FMT + i) e (Z_to_bv 8 0) bc) ->
    (0 <= i)%Z -> (i + 2 <= L)%Z -> intconv (bv_unsigned bc) ->
    (forall mc' dcs', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcs' -> cells_size dcs' = 40%nat ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 e) (Z_to_bv 64 (bv_unsigned aq + 8)) y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x47410) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 e) (Z_to_bv 64 0x15358) aq y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x475c0) fc None mc (seg_rom asegs)).
  Section Sz19.
  Variables Q mc i aq bc fw e : ltac2:(SecDiet.SzSec.tyM 'L_dirB__stmt "vvvvvvv" @Q).
  #[using="RLOf RHIf ST LO KLO SEPF APPF NFZ R1F RI RSTK"] Lemma L_dirB__body : ltac2:(SecDiet.SzSec.bodyP 'L_dirB__stmt "vvvvvvv").
  Proof.
    intros IV DIR Hi HiL HC K.
 intros. prep IV.
    destruct (cfacts _ HC) as (_ & NF3 & NF4 & (ix & HF) & CR & N109 & N110).
    pose proof (conj CR (conj N109 N110)) as CC.
    recell DIR 2%nat 1%nat [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)].
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC. zs. zs. zs.
    call istrchr_spec. all: prem.
    rewrite (istrchr_res_none _ _ _ NF3).
    (* [comment removed for export] *) zs. cbv beta. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. zs. zs.
    chunk_split DIR 8%nat DIR2. chunk_split DIR2 1%nat DIR3.
    call_sp fgvs_spec. all: prem.
    (* [comment removed for export] *) zs. zs. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC.
    (* [comment removed for export] *) zs. zs. br CC. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs.
    call istrchr_spec. all: prem.
    rewrite (istrchr_res_none _ _ _ NF4).
    zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. br CC. zs. zs. br CC. zs. zs. br CC.
    (* [comment removed for export] *) zs.
    chunk_join DIR DIR2. chunk_join DIR DIR3.
    unfold lregs in K. eapply K. 2:{ exact DIR. } 2:{ reflexivity. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz19.
  #[using="RLOf RHIf ST LO KLO SEPF APPF NFZ R1F RI RSTK"] Lemma L_dirB : ltac:(let t := eval cbv delta [L_dirB__stmt] in L_dirB__stmt in exact t).
  Proof. intros Q mc i aq bc fw e. ltac2:(SecDiet.SzSec.closeP 'L_dirB__body "vvvvvvv"). Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation dcellsZ p bc := (dcellsG 0 p (p + 3) (Z_to_bv 8 122) bc) (only parsing).

  (* [comment removed for export] *)
  Definition L_dirA_z__stmt : Prop := forall Q mc (i : Z) aq b37 bz bc,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcells1 ->
    (0 <= i)%Z -> (i + 3 <= L)%Z ->
    nth_error fstr (Z.to_nat i) = Some b37 -> bv_unsigned b37 = 37%Z ->
    nth_error fstr (Z.to_nat (i + 1)) = Some bz -> bv_unsigned bz = 122%Z ->
    nth_error fstr (Z.to_nat (i + 2)) = Some bc -> (0 < bv_unsigned bc < 256)%Z ->
    (forall mc', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) (dcellsZ (FMT + i) bc) ->
       forall y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 3)) (Z_to_bv 64 0x15358) aq y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                           F (Z_to_bv 64 0x475c0) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x47444) fc None mc (seg_rom asegs)).
  Section Sz20.
  Variables Q mc i aq b37 bz bc : ltac2:(SecDiet.SzSec.tyM 'L_dirA_z__stmt "vvvvvvv" @Q).
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_dirA_z__body : ltac2:(SecDiet.SzSec.bodyP 'L_dirA_z__stmt "vvvvvvv").
  Proof.
    intros IV DIR Hi HiL H37 E37 Hz Ez Hc CR K.
 intros. unfold lregs. prep IV.
    assert (NF1 : find_byte 122 B_FLAGS = None) by (cbv; reflexivity).
    assert (F2 : find_byte 122 B_JZT = Some 1%nat) by (cbv; reflexivity).
    assert (CC : True) by exact I.
    fmt_read i b37 H37. zs. clear RD. cbv beta. rewrite E37. zs. br CC.
    zs. fmt_read (i + 1)%Z bz Hz. zs. clear RD. cbv beta. rewrite Ez.
    zs. br CC.
    zs. br CC.
    zs. zs. zs. br CC.
    zs. fmt_read (i + 1)%Z bz Hz. zs. clear RD. cbv beta. rewrite Ez. zs. zs. zs.
    call istrchr_spec; [ eassumption | apply flags_bytes; assumption | exact flags_noz | reflexivity | lia
                       | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    rewrite (istrchr_res_none _ _ _ NF1).
    zs. zs. zs. br CC.
    replace (FMT + (i + 1) + 1 + -1)%Z with (FMT + (i + 1))%Z by lia.
    fmt_read (i + 1)%Z bz Hz. zs. clear RD. cbv beta. rewrite Ez. zs. zs. br CC.
    zs. replace (FMT + (i + 1) + 1 + -1)%Z with (FMT + (i + 1))%Z by lia.
    zs. fmt_read (i + 1)%Z bz Hz. zs. clear RD. cbv beta. rewrite Ez. zs. zs. br CC.
    zs. zs. br CC.
    zs. fmt_read (i + 1)%Z bz Hz. zs. clear RD. cbv beta. rewrite Ez. zs. zs. zs.
    call istrchr_spec; [ eassumption | apply jzt_bytes; assumption | exact jzt_noz | reflexivity | lia
                       | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    unfold istrchr_res. rewrite F2. rewrite unsigned_lit by (cbn; lia).
    fmt_read (i + 1)%Z bz Hz. zs. clear RD. cbv beta. rewrite Ez. zs. br CC.
    zs. zs.
    replace (FMT + (i + 1) + 1)%Z with (FMT + (i + 2))%Z by lia.
    fmt_read (i + 2)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs. zs. br CR.
    try replace (FMT + (i + 2) + 1)%Z with (FMT + i + 3)%Z by lia.
    eapply K. 2:{ match goal with H : rw_cells asegs _ (bv_unsigned sp + -2216) _ |- _ => exact H end. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz20.
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_dirA_z : ltac:(let t := eval cbv delta [L_dirA_z__stmt] in L_dirA_z__stmt in exact t).
  Proof. intros Q mc i aq b37 bz bc. ltac2:(SecDiet.SzSec.closeP 'L_dirA_z__body "vvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fgvs_z_spec : forall ra' sp' t0' t1' t2' s0' s1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6'
      (F' : bvmap 5 word) fc' (m' : word -> option byte) (lo' : Z) (c : Z) (idx : nat) (LM : Z),
    mem_inv asegs m' -> stk asegs m' lo' (bv_unsigned sp') -> (lo' <= bv_unsigned sp' - 32)%Z ->
    find_byte c B_DIOUX = Some idx -> (0 < c < 256)%Z ->
    rw_cells asegs m' LM [C1 (Z_to_bv 8 122)] -> (bv_unsigned sp' <= LM)%Z -> (LM < 2^64)%Z ->
    rng RNG lo' (bv_unsigned sp' - lo') -> rng_aimg RNG -> rng RNG LM 1 ->
    evtF asegs RNG (fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m'',
                      ms' = MS (mkR ra' sp' gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 8) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
                               F' (ret_pc ra') fc' None m'' (seg_rom asegs)
                      /\ munch [(bv_unsigned sp' - 32, bv_unsigned sp')]%Z m' m'' /\ wmono asegs m' m'' /\ mem_inv asegs m''
                      /\ stk asegs m'' lo' (bv_unsigned sp'))
      (MS (mkR ra' sp' gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 c) (Z_to_bv 64 LM) a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
          F' (Z_to_bv 64 0x4ae48) fc' None m' (seg_rom asegs)).
  Proof.
    clear. intros until LM. intros MI' ST' LO' HF CR LMC SEP LMH RSTK0 RI0 RLM.
    pose proof (munch_refl [(bv_unsigned sp' + -32, bv_unsigned sp')]%Z m') as MU. pose proof (wmono_refl asegs m') as WM.
    assert (LO0 : (0 <= lo')%Z) by (destruct ST' as [? _]; assumption).
    assert (RSTK' : rng RNG (bv_unsigned sp' + -32) 32) by (eapply rng_sub'; [exact RSTK0| lia]).
    carve_frame 32%nat ST'.
    do 11 zstep. zstep.
    call istrchr_spec; [ eassumption | apply dioux_bytes; assumption | exact dioux_noz | reflexivity | exact CR
                       | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI0 | cbn; lia] | ].
    unfold istrchr_res. rewrite HF. rewrite unsigned_lit by (unfold S_DIOUX; lia).
    zstep. if_cases K1; zify_cond K1.
    { exfalso. apply find_byte_Some in HF. destruct HF as [HF _]. cbn in HF.
      change 18446744073709551615%Z with (Z.ones 64) in K1. rewrite Z.land_ones in K1 by lia. rewrite Z.mod_small in K1 by lia. lia. }
    clear K1. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. zstep.
    if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. } clear K2.
    do 5 zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
    do 7 zstep.
    release_frame FR ST' (bv_unsigned sp'). finish.
  Qed.

  (* [comment removed for export] *)
  Definition L_dirB_z__stmt : Prop := forall Q mc (i : Z) aq bc,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) (dcellsZ (FMT + i) bc) ->
    (0 <= i)%Z -> (i + 2 <= L)%Z -> intconv (bv_unsigned bc) ->
    (forall mc' dcs', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcs' -> cells_size dcs' = 40%nat ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i + 3)) (Z_to_bv 64 (bv_unsigned aq + 8)) y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x47410) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 3)) (Z_to_bv 64 0x15358) aq y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x475c0) fc None mc (seg_rom asegs)).
  Section Sz22.
  Variables Q mc i aq bc : ltac2:(SecDiet.SzSec.tyM 'L_dirB_z__stmt "vvvvv" @Q).
  #[using="RLOf RHIf ST LO KLO SEPF APPF NFZ R1F RI RSTK"] Lemma L_dirB_z__body : ltac2:(SecDiet.SzSec.bodyP 'L_dirB_z__stmt "vvvvv").
  Proof.
    intros IV DIR Hi HiL HC K.
 intros. prep IV.
    destruct (cfacts _ HC) as (_ & NF3 & NF4 & (ix & HF) & CR & N109 & N110).
    pose proof (conj CR (conj N109 N110)) as CC.
    recell DIR 2%nat 1%nat [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)].
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC. zs. zs. zs.
    call istrchr_spec. all: prem.
    rewrite (istrchr_res_none _ _ _ NF3).
    (* [comment removed for export] *) zs. cbv beta. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. zs. zs.
    chunk_split DIR 8%nat DIR2. chunk_split DIR2 1%nat DIR3.
    call_sp fgvs_z_spec. all: prem.
    (* [comment removed for export] *) zs. zs. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC.
    (* [comment removed for export] *) zs. zs. br CC. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs.
    call istrchr_spec. all: prem.
    rewrite (istrchr_res_none _ _ _ NF4).
    zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. br CC. zs. zs. br CC.
    (* [comment removed for export] *) zs.
    chunk_join DIR DIR2. chunk_join DIR DIR3.
    unfold lregs in K. eapply K. 2:{ exact DIR. } 2:{ reflexivity. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz22.
  #[using="RLOf RHIf ST LO KLO SEPF APPF NFZ R1F RI RSTK"] Lemma L_dirB_z : ltac:(let t := eval cbv delta [L_dirB_z__stmt] in L_dirB_z__stmt in exact t).
  Proof. intros Q mc i aq bc. ltac2:(SecDiet.SzSec.closeP 'L_dirB_z__body "vvvvv"). Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac if_vm := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota end.
  Ltac zsb := zs; try if_vm.
  Ltac ldb k bb Hb Eb := fmt_read k bb Hb; zs; repeat match goal with R : ov_read_bytes _ _ _ _ = _ |- _ => clear R end; cbv beta; rewrite Eb; try if_vm.
  Ltac a0_vm := let v := getreg 10%Z in lazymatch v with Z_to_bv 64 ?e => let e' := eval vm_compute in e in change e with e' end.

  (* [comment removed for export] *)
  Definition atoll_08__stmt : Prop := forall mc (j : Z) b0 b8 bx ra' sp' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6',
    mem_inv asegs mc -> munch W m mc -> (0 <= j)%Z -> (j + 3 <= L)%Z ->
    nth_error fstr (Z.to_nat j) = Some b0 -> bv_unsigned b0 = 48%Z ->
    nth_error fstr (Z.to_nat (j + 1)) = Some b8 -> bv_unsigned b8 = 56%Z ->
    nth_error fstr (Z.to_nat (j + 2)) = Some bx -> bv_unsigned bx = 120%Z ->
    evtF asegs RNG (fun ms' => exists a1 a2 a3 a4 a5 a6 a7 m',
                      ms' = MS (mkR ra' sp' gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 8) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                               F (ret_pc ra') fc None m' (seg_rom asegs)
                      /\ munch [] mc m' /\ wmono asegs mc m' /\ mem_inv asegs m')
      (MS (mkR ra' sp' gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (FMT + j)) a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
          F (Z_to_bv 64 0x677e4) fc None mc (seg_rom asegs)).
  Section Sz23.
  Variables mc j b0 b8 bx ra' sp' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : ltac2:(SecDiet.SzSec.tyM 'atoll_08__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @mc).
  #[using="lo RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RFM"] Lemma atoll_08__body : ltac2:(SecDiet.SzSec.bodyP 'atoll_08__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros MIc MUc Hj HjL H0 E0 H8 E8 Hx Ex.
    pose proof BL_ok as B; unfold BL in B.
    do 3 zsb. ldb j b0 H0 E0. do 7 zsb. zsb. ldb j b0 H0 E0. do 3 zsb. do 6 zsb.
    (* [comment removed for export] *) do 7 zsb. replace (FMT + j + 1)%Z with (FMT + (j + 1))%Z by lia. ldb (j + 1)%Z b8 H8 E8. do 6 zsb.
    (* [comment removed for export] *) do 7 zsb. replace (FMT + (j + 1) + 1)%Z with (FMT + (j + 2))%Z by lia. ldb (j + 2)%Z bx Hx Ex. do 6 zsb.
    (* [comment removed for export] *) do 4 zsb. do 2 zsb.
    a0_vm. apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MIc].
  Qed.
  End Sz23.
  #[using="lo RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RFM"] Lemma atoll_08 : ltac:(let t := eval cbv delta [atoll_08__stmt] in atoll_08__stmt in exact t).
  Proof. intros mc j b0 b8 bx ra' sp' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6'. ltac2:(SecDiet.SzSec.closeP 'atoll_08__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition atoll_8__stmt : Prop := forall mc (j : Z) b8 bx ra' sp' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6',
    mem_inv asegs mc -> munch W m mc -> (0 <= j)%Z -> (j + 2 <= L)%Z ->
    nth_error fstr (Z.to_nat j) = Some b8 -> bv_unsigned b8 = 56%Z ->
    nth_error fstr (Z.to_nat (j + 1)) = Some bx -> bv_unsigned bx = 120%Z ->
    evtF asegs RNG (fun ms' => exists a1 a2 a3 a4 a5 a6 a7 m',
                      ms' = MS (mkR ra' sp' gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 8) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                               F (ret_pc ra') fc None m' (seg_rom asegs)
                      /\ munch [] mc m' /\ wmono asegs mc m' /\ mem_inv asegs m')
      (MS (mkR ra' sp' gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (FMT + j)) a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
          F (Z_to_bv 64 0x677e4) fc None mc (seg_rom asegs)).
  Section Sz24.
  Variables mc j b8 bx ra' sp' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : ltac2:(SecDiet.SzSec.tyM 'atoll_8__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @mc).
  #[using="lo RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RFM"] Lemma atoll_8__body : ltac2:(SecDiet.SzSec.bodyP 'atoll_8__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros MIc MUc Hj HjL H8 E8 Hx Ex.
    pose proof BL_ok as B; unfold BL in B.
    do 3 zsb. ldb j b8 H8 E8. do 7 zsb. zsb. ldb j b8 H8 E8. do 3 zsb. do 6 zsb.
    (* [comment removed for export] *) do 7 zsb. replace (FMT + j + 1)%Z with (FMT + (j + 1))%Z by lia. ldb (j + 1)%Z bx Hx Ex. do 6 zsb.
    (* [comment removed for export] *) do 4 zsb. do 2 zsb.
    a0_vm. apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MIc].
  Qed.
  End Sz24.
  #[using="lo RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RFM"] Lemma atoll_8 : ltac:(let t := eval cbv delta [atoll_8__stmt] in atoll_8__stmt in exact t).
  Proof. intros mc j b8 bx ra' sp' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6'. ltac2:(SecDiet.SzSec.closeP 'atoll_8__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Notation dcells08 p bc := (dcellsG 8 p (p + 4) (Z_to_bv 8 0) bc) (only parsing).

  (* [comment removed for export] *)
  Definition L_dirA_08__stmt : Prop := forall Q mc (i : Z) aq b37 b0 b8 bx,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcells1 ->
    (0 <= i)%Z -> (i + 4 <= L)%Z ->
    nth_error fstr (Z.to_nat i) = Some b37 -> bv_unsigned b37 = 37%Z ->
    nth_error fstr (Z.to_nat (i + 1)) = Some b0 -> bv_unsigned b0 = 48%Z ->
    nth_error fstr (Z.to_nat (i + 2)) = Some b8 -> bv_unsigned b8 = 56%Z ->
    nth_error fstr (Z.to_nat (i + 3)) = Some bx -> bv_unsigned bx = 120%Z ->
    (forall mc', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) (dcells08 (FMT + i) (Z_to_bv 8 120)) ->
       forall y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 (Z_to_bv 64 120) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 4)) (Z_to_bv 64 0x15358) aq y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                           F (Z_to_bv 64 0x475c0) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x47444) fc None mc (seg_rom asegs)).
  Section Sz25.
  Variables Q mc i aq b37 b0 b8 bx : ltac2:(SecDiet.SzSec.tyM 'L_dirA_08__stmt "vvvvvvvv" @Q).
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_dirA_08__body : ltac2:(SecDiet.SzSec.bodyP 'L_dirA_08__stmt "vvvvvvvv").
  Proof.
    intros IV DIR Hi HiL H37 E37 H0 E0 H8 E8 Hx Ex K.
 intros. unfold lregs. prep IV.
    assert (F0 : find_byte 48 B_FLAGS = Some 5%nat) by (cbv; reflexivity).
    assert (NF8 : find_byte 56 B_FLAGS = None) by (cbv; reflexivity).
    assert (NJx : find_byte 120 B_JZT = None) by (cbv; reflexivity).
    ldb i b37 H37 E37. zsb.
    (* [comment removed for export] *) zsb. ldb (i + 1)%Z b0 H0 E0. zsb. zsb. zsb. zsb. zsb.
    (* [comment removed for export] *) zsb. zsb.
    replace (FMT + i + 1)%Z with (FMT + (i + 1))%Z by lia.
    call (atoll_08 _ (i + 1)%Z b0 b8 bx);
      [ eassumption | eassumption | lia | lia | exact H0 | exact E0 | replace (i + 1 + 1)%Z with (i + 2)%Z by lia; exact H8 | exact E8
      | replace (i + 1 + 2)%Z with (i + 3)%Z by lia; exact Hx | exact Ex | ].
    (* [comment removed for export] *)
    zsb.
    ldb (i + 1)%Z b0 H0 E0. zsb. zsb. zsb.
    ldb (i + 2)%Z b8 H8 E8. zsb. zsb. zsb.
    ldb (i + 3)%Z bx Hx Ex. zsb. zsb. zsb.
    zsb. zsb.
    (* [comment removed for export] *)
    zsb. ldb (i + 1)%Z b0 H0 E0. zsb. zsb. zsb.
    call istrchr_spec; [ eassumption | apply flags_bytes; assumption | exact flags_noz | reflexivity | lia | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    unfold istrchr_res. rewrite F0. rewrite unsigned_lit by (cbn; lia).
    zsb. zsb. zsb.
    ldb (i + 2)%Z b8 H8 E8. zsb. zsb. zsb.
    call istrchr_spec; [ eassumption | apply flags_bytes; assumption | exact flags_noz | reflexivity | lia | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    rewrite (istrchr_res_none _ _ _ NF8).
    zsb. zsb. zsb.
    (* [comment removed for export] *)
    ldb (i + 2)%Z b8 H8 E8. zsb. zsb.
    zsb. zsb.
    ldb (i + 2)%Z b8 H8 E8. zsb. zsb.
    zsb. zsb.
    replace (FMT + (i + 1) + 1)%Z with (FMT + (i + 2))%Z by lia.
    call (atoll_8 _ (i + 2)%Z b8 bx); [ eassumption | eassumption | lia | lia | exact H8 | exact E8 | replace (i + 2 + 1)%Z with (i + 3)%Z by lia; exact Hx | exact Ex | ].
    zsb.
    ldb (i + 2)%Z b8 H8 E8. zsb. zsb. zsb. zsb.
    ldb (i + 3)%Z bx Hx Ex. zsb. zsb. zsb. zsb.
    (* [comment removed for export] *)
    zsb. zsb. zsb.
    ldb (i + 3)%Z bx Hx Ex. zsb. zsb. zsb.
    call istrchr_spec; [ eassumption | apply jzt_bytes; assumption | exact jzt_noz | reflexivity | lia | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
    rewrite (istrchr_res_none _ _ _ NJx).
    ldb (i + 3)%Z bx Hx Ex. zsb.
    zsb. zsb. zsb. zsb.
    ldb (i + 3)%Z bx Hx Ex. zsb. zsb. zsb. zsb.
    replace (FMT + (i + 1) + 3)%Z with (FMT + i + 4)%Z in * by lia.
    eapply K. 2:{ match goal with H : rw_cells asegs _ (bv_unsigned sp + -2216) _ |- _ => exact H end. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz25.
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_dirA_08 : ltac:(let t := eval cbv delta [L_dirA_08__stmt] in L_dirA_08__stmt in exact t).
  Proof. intros Q mc i aq b37 b0 b8 bx. ltac2:(SecDiet.SzSec.closeP 'L_dirA_08__body "vvvvvvvv"). Qed.


  (* [comment removed for export] *)
  Definition L_last__stmt : Prop := forall mc aq,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcells1 ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG POST (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + L)) aq y22 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x47444) fc None mc (seg_rom asegs)).
  Section Sz26.
  Variables mc aq : ltac2:(SecDiet.SzSec.tyM 'L_last__stmt "vv" @mc).
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ RSTK RFM"] Lemma L_last__body : ltac2:(SecDiet.SzSec.bodyP 'L_last__stmt "vv").
  Proof.
    intros IV DIR.
 intros. unfold lregs. prep IV.
    assert (HL : nth_error (fstr ++ [Z_to_bv 8 0]) (Z.to_nat L) = Some (Z_to_bv 8 0)) by (rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia; reflexivity).
    assert (CC : True) by exact I.
    pose proof (fmt_rd mc L (Z_to_bv 8 0) MI1 MU1 HL ltac:(lia)) as RD.
    zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC. zs.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) clear RD. zs. do 13 zs. zs. zs.
    (* [comment removed for export] *)
    pose proof (stk_release _ _ _ _ _ ST1 FRL ltac:(lia)) as SK1. norm_stk SK1 (bv_unsigned sp + -2216)%Z.
    pose proof (stk_release _ _ _ _ _ SK1 DIR ltac:(lia)) as SK2. norm_stk SK2 (bv_unsigned sp + -2176)%Z.
    pose proof (stk_merge _ _ _ _ _ SK2 STM ltac:(lia)) as SK3.
    pose proof (stk_release _ _ _ _ _ SK3 FRT ltac:(lia)) as SK4. norm_stk SK4 (bv_unsigned sp).
    replace (bv_unsigned sp + -2320)%Z with (bv_unsigned sp - 2320)%Z in MU1 by lia.
    finish.
  Qed.
  End Sz26.
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ RSTK RFM"] Lemma L_last : ltac:(let t := eval cbv delta [L_last__stmt] in L_last__stmt in exact t).
  Proof. intros mc aq. ltac2:(SecDiet.SzSec.closeP 'L_last__body "vv"). Qed.



  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition L_next0__stmt : Prop := forall mc dcs aq,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG POST (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + L)) aq y22 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x47410) fc None mc (seg_rom asegs)).
  Section Sz27.
  Variables mc dcs aq : ltac2:(SecDiet.SzSec.tyM 'L_next0__stmt "vvv" @mc).
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ RSTK RFM"] Lemma L_next0__body : ltac2:(SecDiet.SzSec.bodyP 'L_next0__stmt "vvv").
  Proof.
    intros IV DIR SZ.
 intros. unfold lregs. prep IV.
    assert (HL : nth_error (fstr ++ [Z_to_bv 8 0]) (Z.to_nat L) = Some (Z_to_bv 8 0)) by (rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia; reflexivity).
    assert (CC : True) by exact I.
    pose proof (fmt_rd mc L (Z_to_bv 8 0) MI1 MU1 HL ltac:(lia)) as RD.
    zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) clear RD. zs. do 13 zs. zs. zs.
    pose proof (stk_release _ _ _ _ _ ST1 FRL ltac:(lia)) as SK1. norm_stk SK1 (bv_unsigned sp + -2216)%Z.
    pose proof (stk_release _ _ _ _ _ SK1 DIR ltac:(lia)) as SK2. rewrite SZ in SK2. norm_stk SK2 (bv_unsigned sp + -2176)%Z.
    pose proof (stk_merge _ _ _ _ _ SK2 STM ltac:(lia)) as SK3.
    pose proof (stk_release _ _ _ _ _ SK3 FRT ltac:(lia)) as SK4. norm_stk SK4 (bv_unsigned sp).
    replace (bv_unsigned sp + -2320)%Z with (bv_unsigned sp - 2320)%Z in MU1 by lia.
    finish.
  Qed.
  End Sz27.
  #[using="RLOf RHIf ST LO KLO FB SEPF APPF NFZ RSTK RFM"] Lemma L_next0 : ltac:(let t := eval cbv delta [L_next0__stmt] in L_next0__stmt in exact t).
  Proof. intros mc dcs aq. ltac2:(SecDiet.SzSec.closeP 'L_next0__body "vvv"). Qed.

  #[using="RLOf RHIf ST LO KLO FB NOZ SEPF APPF NFZ R1F RSTK RFM"] Lemma L_next1 : forall Q mc (i : Z) aq,
    INV mc -> (0 <= i < L)%Z ->
    (forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x47418) fc None mc (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x47410) fc None mc (seg_rom asegs)).
  Proof.
    intros Q mc i aq IV Hi K. intros. unfold lregs. pose proof IV as IV'. prep IV'.
    destruct (fmt_char mc i MI1 MU1 ltac:(lia)) as (b2 & Hb2 & NZ2 & RB2 & RD2).
    zs. cbv beta. zs. assert (CC : True) by exact I. br NZ2.
    unfold lregs in K. eapply K.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Section PCS.
  Variables (AQ Sa : Z) (sstr : list byte) (RLO RHI : Z).
  Hypothesis VAQ : rw_cells asegs m (AQ) [C8 (Z_to_bv 64 Sa)].
  Hypothesis SEPV : (bv_unsigned sp <= AQ /\ AQ + 8 <= 2^64)%Z.
  Hypothesis SSTR : bytes_at asegs m Sa (sstr ++ [Z_to_bv 8 0]).
  Hypothesis SNOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr.
  Notation LS := (Z.of_nat (length sstr)).
  Notation NS := (Z.of_nat (length sstr) + 1)%Z.
  Hypothesis SEPS : (Sa + NS <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= Sa)%Z.
  Hypothesis APPS : app_blk Sa (Sa + NS).
  Hypothesis SPOS : (0 < Sa)%Z.
  Hypothesis USTR : unpoisoned m Sa (Sa + NS).
  Hypothesis NSZ : (NS <= 2^40)%Z.
  Hypothesis R1 : (RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RVA : rng RNG (AQ) 8.
  Hypothesis RS : rng RNG Sa NS.
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition INVS (mc : word -> option byte) : Prop :=
    INV mc /\ rt_layout mc /\ unpoisoned mc Sa (Sa + NS) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO)
    /\ bytes_at asegs mc Sa (sstr ++ [Z_to_bv 8 0]) /\ rw_cells asegs mc (AQ) [C8 (Z_to_bv 64 Sa)].

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2320 /\ KHIGH <= lo /\ 1 <= NS /\ NS <= 2^40
     /\ 0 < Sa /\ Sa + NS + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad Sa /\ shad (Sa + NS - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr Sa 3 < 2^44 /\ 0 <= Z.shiftr (Sa + NS + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0
     /\ bv_unsigned sp <= AQ /\ AQ + 8 <= 2^64)%Z.
  #[using="m FMT fstr RLOf RHIf ST LO KLO R1F SEPV SEPS APPS SPOS NSZ R1"] Lemma BND_ok : BND.
  Proof.
    unfold BND. destruct ST as (L0 & _). destruct APPS as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. nia.
  Qed.
  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BLS : Prop :=
    (1 <= NS /\ NS <= 2^40 /\ 0 < Sa /\ Sa + NS + 8 <= 2^47
     /\ 0 <= Z.shiftr Sa 3 < 2^44 /\ 0 <= Z.shiftr (Sa + NS + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad Sa /\ shad (Sa + NS - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296
     /\ bv_unsigned sp <= AQ /\ AQ + 8 <= 2^64)%Z.
  #[using="m lo FMT fstr RLOf RHIf ST LO KLO R1F SEPV SEPS APPS SPOS NSZ R1"] Lemma BLS_ok : BLS. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BLS. lia. Qed.

  Definition invs_of__stmt : Prop := forall mc, INV mc -> INVS mc.
  Section Sz31.
  Variables mc : ltac2:(SecDiet.SzSec.tyM 'invs_of__stmt "v" @mc).
  #[using="FMT fstr RLOf RHIf ST LO KLO LAY R1F VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1"] Lemma invs_of__body : ltac2:(SecDiet.SzSec.bodyP 'invs_of__stmt "v").
  Proof.
    intros IV.
 pose proof IV as (FRT & (j0 & FRL) & STM & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1).
    pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    split; [exact IV|].
    split. { eapply rw_cells_transport; [exact LAY | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (SS : (shad (Sa + NS - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact USTR | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    split. { eapply bytes_at_transport; [exact SSTR | exact MU1 |]. rewrite length_app. cbn [length disjoint_from]. lia. }
    eapply rw_cells_transport; [exact VAQ | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia.
  Qed.
  End Sz31.
  #[using="FMT fstr RLOf RHIf ST LO KLO LAY R1F VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1"] Lemma invs_of : ltac:(let t := eval cbv delta [invs_of__stmt] in invs_of__stmt in exact t).
  Proof. intros mc. ltac2:(SecDiet.SzSec.closeP 'invs_of__body "v"). Qed.

  Ltac preps IV :=
    let IVS := fresh "IVS" in pose proof (invs_of _ IV) as IVS;
    destruct IVS as (_ & LAY1 & US1 & WR11 & SSTR1 & VAQ1);
    prep IV;
    let B := fresh "BS" in pose proof BLS_ok as B; unfold BLS in B;
    change (?P) with (sf_hide P) in SEPS; change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in SEPV;
    change (?P) with (sf_hide P) in SSTR; change (?P) with (sf_hide P) in NSZ.

  Ltac unland K :=
    change 18446744073709551615%Z with (Z.ones 64) in K; rewrite ?Z.land_ones in K by lia;
    change (2 ^ 64)%Z with 18446744073709551616%Z in K.

  (* [comment removed for export] *)
  Definition KS (Q : machine_state -> Prop) (i : Z) : Prop :=
    forall mc' dcs', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcs' -> cells_size dcs' = 40%nat ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 (AQ + 8)) y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x47410) fc None mc' (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition sregs (i : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp (Z_to_bv 64 (-1)) x10 x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x15358) (Z_to_bv 64 (AQ + 8)) x22 x23
        (Z_to_bv 64 (bv_unsigned sp + -2184)) (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) x28 x29 x30 x31.

  (* [comment removed for export] *)
  #[using="fstr RLOf RHIf ST LO KLO SEPF APPF NFZ RSTK sstr RLO RHI"] Lemma LS_X : forall Q i mc dcs, KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31,
    evtF asegs RNG Q (MS (sregs i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x47790) fc None mc (seg_rom asegs)).
  Proof.
    intros Q i mc dcs K IV DIR SZ. intros. unfold sregs. prep IV.
    zs. zs. unfold KS, lregs in K. eapply K; [| exact DIR | exact SZ].
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Definition LS_L__stmt : Prop := forall Q i mc dcs (k : nat) (c : Z), KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    (NS <= 64)%Z -> Z.to_nat (shad (Sa + NS - 1) - c) = k -> (shad Sa <= c < shad (Sa + NS - 1))%Z ->
    forall x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evtF asegs RNG Q (MS (sregs i x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (Sa + NS + -1) 3)) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                              (Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x478a0) fc None mc (seg_rom asegs)).
  Section Sz33.
  Variables Q i mc dcs c : ltac2:(SecDiet.SzSec.tyM 'LS_L__stmt "vvvvkv" @Q).
  #[using="fstr RLOf RHIf ST LO KLO LAY SEPF APPF NFZ R1F RSTK RLO RHI VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1 RSH1"] Lemma LS_L__body : ltac2:(SecDiet.SzSec.bodyP 'LS_L__stmt "vvvvkv").
  Proof.
    intros k K IV DIR SZ N1 Hk Hc.
 intros. unfold sregs. pose proof IV as IV0. preps IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (Sa + NS - 1) = 2147450880 + Z.shiftr (Sa + NS + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc Sa (Sa + NS) c US1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LS_X; eassumption.
  Qed.
  End Sz33.
  #[using="fstr RLOf RHIf ST LO KLO LAY SEPF APPF NFZ R1F RSTK RLO RHI VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1 RSH1"] Lemma LS_L : ltac:(let t := eval cbv delta [LS_L__stmt] in LS_L__stmt in exact t).
  Proof. intros Q i mc dcs k c. ltac2:(SecDiet.SzSec.closeP 'LS_L__body "vvvvkv"). Qed.

  (* [comment removed for export] *)
  Definition LS_E__stmt : Prop := forall Q i mc dcs, KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    (NS <= 64)%Z ->
    forall x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evtF asegs RNG Q (MS (sregs i x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr Sa 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (Sa + NS + -1) 3))
                              (Z_to_bv 64 (Sa + NS + -1)) x13 x14 x15 x16 x17 (Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x47884) fc None mc (seg_rom asegs)).
  Section Sz34.
  Variables Q i mc dcs : ltac2:(SecDiet.SzSec.tyM 'LS_E__stmt "vvvv" @Q).
  #[using="fstr RLOf RHIf ST LO KLO LAY SEPF APPF NFZ R1F RSTK RLO RHI VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1 RSH1"] Lemma LS_E__body : ltac2:(SecDiet.SzSec.bodyP 'LS_E__stmt "vvvv").
  Proof.
    intros K IV DIR SZ N1.
 intros. unfold sregs. pose proof IV as IV0. preps IV.
    destruct (unpoisoned_check_rd asegs mc Sa (Sa + NS) (Sa + NS + -1) 1 US1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((Sa + NS + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LS_X; eassumption.
    - eapply (LS_L Q i mc dcs); [exact K | exact IV0 | exact DIR | exact SZ | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.
  End Sz34.
  #[using="fstr RLOf RHIf ST LO KLO LAY SEPF APPF NFZ R1F RSTK RLO RHI VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1 RSH1"] Lemma LS_E : ltac:(let t := eval cbv delta [LS_E__stmt] in LS_E__stmt in exact t).
  Proof. intros Q i mc dcs. ltac2:(SecDiet.SzSec.closeP 'LS_E__body "vvvv"). Qed.

  (* [comment removed for export] *)
  Definition LS_C__stmt : Prop := forall Q i mc dcs, KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evtF asegs RNG Q (MS (sregs i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x47834) fc None mc (seg_rom asegs)).
  Section Sz35.
  Variables Q i mc dcs : ltac2:(SecDiet.SzSec.tyM 'LS_C__stmt "vvvv" @Q).
  Lemma LS_C__body : ltac2:(SecDiet.SzSec.bodyP 'LS_C__stmt "vvvv").
  Proof using APPF APPS KLO LAY LO NFZ NSZ R1 R1F RI RSH1 RSTK SEPF SEPS SEPV SPOS SSTR ST USTR VAQ WR1.
    intros K IV DIR SZ.
 intros. unfold sregs. pose proof IV as IV0. preps IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1 BS. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      assert (N1 : (64 < NS)%Z) by (unland K2; clear - K2 BS; Z.div_mod_to_equations; lia).
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BS. lia. }
      zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | (keep_hyps sp lo fstr RLOf RHIf sstr RLO RHI dcs LO; lia) | unfold KHIGH; (keep_hyps sp lo FMT fstr RLOf RHIf sstr RLO RHI dcs B; lia) | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APPS | zsimp; exact US1
        | zsimp; pose proof BND_ok as B9; unfold BND in B9; (keep_hyps sp fstr RLOf RHIf AQ Sa sstr RLO RHI dcs BS; lia)
        | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo fstr RLOf RHIf sstr RLO RHI dcs; lia)] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LS_X; [exact K | | eassumption | exact SZ].
      split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
    - (* [comment removed for export] *)
      assert (N1 : (NS <= 64)%Z) by (unland K2; clear - K2 BS; Z.div_mod_to_equations; lia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 asegs mc RLO RHI Sa WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO RHI (Sa + NS + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. prr [10;11;12;13]%Z. if_cases K5; zify_cond K5.
      + eapply LS_X; eassumption.
      + eapply LS_E; eassumption.
  Qed.
  End Sz35.
  #[using="fstr RLOf RHIf ST LO KLO LAY SEPF APPF NFZ R1F RI RSTK RLO RHI VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1 RSH1"] Lemma LS_C : ltac:(let t := eval cbv delta [LS_C__stmt] in LS_C__stmt in exact t).
  Proof. intros Q i mc dcs. ltac2:(SecDiet.SzSec.closeP 'LS_C__body "vvvv"). Qed.

  (* [comment removed for export] *)
  Definition L_dirS__stmt : Prop := forall Q mc (i : Z) bc,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) (dcellsA (FMT + i) bc) ->
    (0 <= i)%Z -> (i + 2 <= L)%Z -> sconv (bv_unsigned bc) -> KS Q i ->
    forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
    evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp (Z_to_bv 64 (FMT + i)) (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x15358) (Z_to_bv 64 AQ) (Z_to_bv 64 (FMT + i + 1)) (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x475c0) fc None mc (seg_rom asegs)).
  Section Sz36.
  Variables Q mc i bc : ltac2:(SecDiet.SzSec.tyM 'L_dirS__stmt "vvvv" @Q).
  #[using="RLOf RHIf ST LO KLO LAY SEPF APPF NFZ R1F RI RSTK Sa sstr RLO RHI VAQ SEPV SSTR SNOZ SEPS APPS SPOS USTR NSZ R1 WR1 RVA RS RSH1"] Lemma L_dirS__body : ltac2:(SecDiet.SzSec.bodyP 'L_dirS__stmt "vvvv").
  Proof.
    intros IV DIR Hi HiL HC K.
 intros. pose proof IV as IV0. preps IV.
    destruct (sfacts _ HC) as (_ & CR & N109 & N110 & F3 & F4 & F5 & F6).
    pose proof (conj CR (conj N109 N110)) as CC.
    recell DIR 2%nat 1%nat [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)].
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC. zs. zs. zs.
    call istrchr_spec. all: prem. unfold istrchr_res. rewrite F3. rewrite unsigned_lit by (cbn; lia).
    (* [comment removed for export] *) zs. cbv beta. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. zs. call istrchr_spec. all: prem. rewrite (istrchr_res_none _ _ _ F4).
    (* [comment removed for export] *) zs. zs. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. zs. call istrchr_spec. all: prem. unfold istrchr_res. rewrite F5. rewrite unsigned_lit by (cbn; lia).
    (* [comment removed for export] *) zs. zs. br CC. zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    (* [comment removed for export] *) zs. zs.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. zs. call istrchr_spec. all: prem. unfold istrchr_res. rewrite F6. rewrite unsigned_lit by (cbn; lia).
    (* [comment removed for export] *) zs. br CC. zs.
    (* [comment removed for export] *) zs. cbv beta. zs. zs. br CC.
    (* [comment removed for export] *) zs. zs. br CC. zs. br CC.
    (* [comment removed for export] *) zs. zs. zs. br BS.
    (* [comment removed for export] *) zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zs. br CC.
    (* [comment removed for export] *) zs. zs.
    unfold sf_hide in SSTR1.
    call istrlen_spec. all: prem.
    zs.
    cbn [app] in DIR.
    eapply (LS_C Q i); [exact K | | exact DIR | reflexivity].
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz36.
  #[using="RLOf RHIf ST LO KLO LAY SEPF APPF NFZ R1F RI RSTK Sa sstr RLO RHI VAQ SEPV SSTR SNOZ SEPS APPS SPOS USTR NSZ R1 WR1 RVA RS RSH1"] Lemma L_dirS : ltac:(let t := eval cbv delta [L_dirS__stmt] in L_dirS__stmt in exact t).
  Proof. intros Q mc i bc. ltac2:(SecDiet.SzSec.closeP 'L_dirS__body "vvvv"). Qed.
  End PCS.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Inductive pitem : Type :=
  | PLit (l : list byte)                 (* [comment removed for export] *)
  | PInt (bc : byte)                     (* [comment removed for export] *)
  | PZu (bc : byte)                      (* [comment removed for export] *)
  | P08x                                 (* [comment removed for export] *)
  | PStr (Sa : Z) (sstr : list byte).    (* [comment removed for export] *)
  Definition pbytes (it : pitem) : list byte :=
    match it with
    | PLit l => l
    | PInt bc => [Z_to_bv 8 37; bc]
    | PZu bc => [Z_to_bv 8 37; Z_to_bv 8 122; bc]
    | P08x => [Z_to_bv 8 37; Z_to_bv 8 48; Z_to_bv 8 56; Z_to_bv 8 120]
    | PStr _ _ => [Z_to_bv 8 37; Z_to_bv 8 115]
    end.
  Definition pitem_ok (it : pitem) : Prop :=
    match it with
    | PLit l => Forall (fun b : byte => bv_unsigned b <> 37%Z) l
    | PInt bc => intconv (bv_unsigned bc)
    | PZu bc => intconv (bv_unsigned bc)
    | P08x => True
    | PStr _ _ => True
    end.
  Definition prender (its : list pitem) : list byte := concat (map pbytes its).

  (* [comment removed for export] *)
  Definition pstr_ok (AQ Sa : Z) (sstr : list byte) : Prop :=
    rw_cells asegs m AQ [C8 (Z_to_bv 64 Sa)] /\ (bv_unsigned sp <= AQ /\ AQ + 8 <= 2^64)%Z
    /\ bytes_at asegs m Sa (sstr ++ [Z_to_bv 8 0]) /\ Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr
    /\ (Sa + (Z.of_nat (length sstr) + 1) <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= Sa)%Z /\ (0 < Sa)%Z
    /\ sobj RNG m Sa (Sa + (Z.of_nat (length sstr) + 1))
    /\ rng RNG AQ 8 /\ rng RNG Sa (Z.of_nat (length sstr) + 1).
  (* [comment removed for export] *)
  Fixpoint pargs_ok (its : list pitem) (aq : word) : Prop :=
    match its with
    | [] => True
    | PLit _ :: r => pargs_ok r aq
    | PStr Sa sstr :: r => pstr_ok (bv_unsigned aq) Sa sstr /\ pargs_ok r (Z_to_bv 64 (bv_unsigned aq + 8))
    | _ :: r => pargs_ok r (Z_to_bv 64 (bv_unsigned aq + 8))
    end.

  #[using="Type"] Lemma skipn_cons_nth : forall {A} (l : list A) n x r, skipn n l = x :: r -> nth_error l n = Some x /\ skipn (S n) l = r /\ (n < length l)%nat.
  Proof.
    clear. intros A l. induction l as [|a l IH]; intros n x r H; [destruct n; discriminate H|].
    destruct n as [|n]; cbn in H |- *; [injection H as -> ->; repeat split; lia|].
    destruct (IH n x r H) as (H1 & H2 & H3). repeat split; [exact H1 | exact H2 | lia].
  Qed.
  #[using="Type"] Lemma skipn_app_run : forall {A} (l l1 r : list A) n, skipn n l = l1 ++ r -> (n <= length l)%nat ->
    (forall t b, nth_error l1 t = Some b -> nth_error l (n + t) = Some b) /\ skipn (n + length l1) l = r /\ (n + length l1 <= length l)%nat.
  Proof.
    clear. intros A l l1 r n H LE.
    assert (LEN : (n + length l1 <= length l)%nat).
    { pose proof (f_equal (@length A) H) as E. rewrite length_skipn, length_app in E. lia. }
    split; [| split; [| exact LEN]].
    - intros t b Hb. rewrite <- nth_error_skipn, H. rewrite nth_error_app1 by (apply nth_error_Some; rewrite Hb; discriminate). exact Hb.
    - rewrite Nat.add_comm, <- skipn_skipn, H. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
  Qed.
  (* [comment removed for export] *)
  #[using="RLOf RHIf ST LO KLO FB NOZ SEPF APPF NFZ R1F RSTK RFM"] Lemma L_after : forall (i : Z) mc dcs aq,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat -> (0 <= i <= L)%Z ->
    (forall mc', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcells1 ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evtF asegs RNG POST (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                              F (Z_to_bv 64 0x47444) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG POST (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x47410) fc None mc (seg_rom asegs)).
  Proof.
    intros i mc dcs aq IV DIR SZ Hi K. intros.
    destruct (Z.eq_dec i L) as [-> | NE].
    - eapply L_next0; eassumption.
    - eapply (L_next1 POST mc i aq); [exact IV | lia |]. intros.
      eapply (L_head POST mc dcs); [exact IV | exact DIR | exact SZ |]. exact K.
  Qed.
  (* [comment removed for export] *)
  #[using="RLOf RHIf ST LO KLO FB NOZ LAY SEPF APPF NFZ R1F RI RSTK RFM"] Lemma L_items : forall its (i : Z) mc aq,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcells1 ->
    (0 <= i <= L)%Z -> skipn (Z.to_nat i) fstr = prender its -> Forall pitem_ok its -> pargs_ok its aq ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evtF asegs RNG POST (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x47444) fc None mc (seg_rom asegs)).
  Proof.
    induction its as [|it its IH]; intros i mc aq IV DIR Hi SK OK AOK; intros.
    - (* [comment removed for export] *)
      assert (EI : i = L). { cbn in SK. apply (f_equal (@length byte)) in SK. rewrite length_skipn in SK. cbn in SK. lia. }
      subst i. eapply L_last; eassumption.
    - apply Forall_cons_iff in OK. destruct OK as [OK1 OK].
      unfold prender in SK. cbn [map concat] in SK. fold (prender its) in SK.
      destruct (skipn_app_run _ _ _ _ SK ltac:(lia)) as (NTH & SK' & LEN).
      destruct it as [l | bc | bc | | Sa sstr]; cbn [pbytes pitem_ok pargs_ok length] in *.
      + (* [comment removed for export] *)
        pose proof IV as IV'. destruct IV' as (_ & _ & _ & _ & MUc & _ & MIc & _).
        eapply (L_skip POST mc (length l) i aq); [exact MIc | exact MUc | lia | lia | |].
        { intros j b Hj Hb. destruct (nth_error l (j - Z.to_nat i)) as [b'|] eqn:E.
          2:{ exfalso. apply nth_error_None in E. lia. }
          pose proof (NTH _ _ E) as E2. replace (Z.to_nat i + (j - Z.to_nat i))%nat with j in E2 by lia. rewrite Hb in E2. injection E2 as <-.
          eapply (proj1 (Forall_forall _ _) OK1). eapply nth_error_In. exact E. }
        intros. eapply (IH (i + Z.of_nat (length l))%Z mc aq); [exact IV | exact DIR | lia | | exact OK | exact AOK].
        replace (Z.to_nat (i + Z.of_nat (length l))) with (Z.to_nat i + length l)%nat by lia. exact SK'.
      + (* [comment removed for export] *)
        assert (H37 : nth_error fstr (Z.to_nat i) = Some (Z_to_bv 8 37)) by (rewrite <- (Nat.add_0_r (Z.to_nat i)); apply NTH; reflexivity).
        assert (Hc : nth_error fstr (Z.to_nat (i + 1)) = Some bc) by (replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia; apply NTH; reflexivity).
        eapply (L_dirA POST mc i aq (Z_to_bv 8 37) bc); [exact IV | exact DIR | lia | lia | exact H37 | reflexivity | exact Hc | exact (proj1 (cfacts _ OK1)) |].
        clear mc IV DIR. intros mc IV DIR. intros.
        eapply (L_dirB POST mc i aq bc 0 (FMT + i + 2)); [exact IV | exact DIR | lia | lia | exact OK1 |].
        clear mc IV DIR. intros mc dcs IV DIR SZ. intros.
        replace (FMT + i + 2)%Z with (FMT + (i + 2))%Z by lia.
        eapply (L_after (i + 2)%Z mc dcs); [exact IV | exact DIR | exact SZ | lia |].
        clear mc dcs IV DIR SZ. intros mc IV DIR. intros.
        eapply (IH (i + 2)%Z mc); [exact IV | exact DIR | lia | | exact OK | exact AOK].
        replace (Z.to_nat (i + 2)) with (Z.to_nat i + 2)%nat by lia. exact SK'.
      + (* [comment removed for export] *)
        assert (H37 : nth_error fstr (Z.to_nat i) = Some (Z_to_bv 8 37)) by (rewrite <- (Nat.add_0_r (Z.to_nat i)); apply NTH; reflexivity).
        assert (Hz : nth_error fstr (Z.to_nat (i + 1)) = Some (Z_to_bv 8 122)) by (replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia; apply NTH; reflexivity).
        assert (Hc : nth_error fstr (Z.to_nat (i + 2)) = Some bc) by (replace (Z.to_nat (i + 2)) with (Z.to_nat i + 2)%nat by lia; apply NTH; reflexivity).
        assert (CR : (0 < bv_unsigned bc < 256)%Z) by (destruct (cfacts _ OK1) as (_ & _ & _ & _ & CR & _); lia).
        eapply (L_dirA_z POST mc i aq (Z_to_bv 8 37) (Z_to_bv 8 122) bc); [exact IV | exact DIR | lia | lia | exact H37 | reflexivity | exact Hz | reflexivity | exact Hc | exact CR |].
        clear mc IV DIR. intros mc IV DIR. intros.
        eapply (L_dirB_z POST mc i aq bc); [exact IV | exact DIR | lia | lia | exact OK1 |].
        clear mc IV DIR. intros mc dcs IV DIR SZ. intros.
        replace (FMT + i + 3)%Z with (FMT + (i + 3))%Z by lia.
        eapply (L_after (i + 3)%Z mc dcs); [exact IV | exact DIR | exact SZ | lia |].
        clear mc dcs IV DIR SZ. intros mc IV DIR. intros.
        eapply (IH (i + 3)%Z mc); [exact IV | exact DIR | lia | | exact OK | exact AOK].
        replace (Z.to_nat (i + 3)) with (Z.to_nat i + 3)%nat by lia. exact SK'.
      + (* [comment removed for export] *)
        assert (H37 : nth_error fstr (Z.to_nat i) = Some (Z_to_bv 8 37)) by (rewrite <- (Nat.add_0_r (Z.to_nat i)); apply NTH; reflexivity).
        assert (H0 : nth_error fstr (Z.to_nat (i + 1)) = Some (Z_to_bv 8 48)) by (replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia; apply NTH; reflexivity).
        assert (H8 : nth_error fstr (Z.to_nat (i + 2)) = Some (Z_to_bv 8 56)) by (replace (Z.to_nat (i + 2)) with (Z.to_nat i + 2)%nat by lia; apply NTH; reflexivity).
        assert (Hx : nth_error fstr (Z.to_nat (i + 3)) = Some (Z_to_bv 8 120)) by (replace (Z.to_nat (i + 3)) with (Z.to_nat i + 3)%nat by lia; apply NTH; reflexivity).
        eapply (L_dirA_08 POST mc i aq (Z_to_bv 8 37) (Z_to_bv 8 48) (Z_to_bv 8 56) (Z_to_bv 8 120));
          [exact IV | exact DIR | lia | lia | exact H37 | reflexivity | exact H0 | reflexivity | exact H8 | reflexivity | exact Hx | reflexivity |].
        clear mc IV DIR. intros mc IV DIR. intros.
        eapply (L_dirB POST mc i aq (Z_to_bv 8 120) 8 (FMT + i + 4)); [exact IV | exact DIR | lia | lia | right; right; right; reflexivity |].
        clear mc IV DIR. intros mc dcs IV DIR SZ. intros.
        replace (FMT + i + 4)%Z with (FMT + (i + 4))%Z by lia.
        eapply (L_after (i + 4)%Z mc dcs); [exact IV | exact DIR | exact SZ | lia |].
        clear mc dcs IV DIR SZ. intros mc IV DIR. intros.
        eapply (IH (i + 4)%Z mc); [exact IV | exact DIR | lia | | exact OK | exact AOK].
        replace (Z.to_nat (i + 4)) with (Z.to_nat i + 4)%nat by lia. exact SK'.
      + (* [comment removed for export] *)
        destruct AOK as [PS AOK]. destruct PS as (VAQ & SEPV & SSTR & SNOZ & SEPS & SPOS & (APPS & USTR & NSZ & RLO & RHI & R1 & WR1 & RSH1) & RVA & RS).
        assert (H37 : nth_error fstr (Z.to_nat i) = Some (Z_to_bv 8 37)) by (rewrite <- (Nat.add_0_r (Z.to_nat i)); apply NTH; reflexivity).
        assert (Hc : nth_error fstr (Z.to_nat (i + 1)) = Some (Z_to_bv 8 115)) by (replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia; apply NTH; reflexivity).
        assert (SC : sconv (bv_unsigned (Z_to_bv 8 115))) by reflexivity.
        eapply (L_dirA POST mc i aq (Z_to_bv 8 37) (Z_to_bv 8 115)); [exact IV | exact DIR | lia | lia | exact H37 | reflexivity | exact Hc | exact (proj1 (sfacts _ SC)) |].
        clear mc IV DIR. intros mc IV DIR. intros.
        rewrite <- (Z_to_bv_bv_unsigned aq).
        eapply (L_dirS (bv_unsigned aq) Sa sstr RLO RHI); try eassumption; try lia.
        unfold KS. clear mc IV DIR. intros mc dcs IV DIR SZ. intros.
        replace (FMT + i + 2)%Z with (FMT + (i + 2))%Z by lia.
        eapply (L_after (i + 2)%Z mc dcs); [exact IV | exact DIR | exact SZ | lia |].
        clear mc dcs IV DIR SZ. intros mc IV DIR. intros.
        eapply (IH (i + 2)%Z mc); [exact IV | exact DIR | lia | | exact OK | exact AOK].
        replace (Z.to_nat (i + 2)) with (Z.to_nat i + 2)%nat by lia. exact SK'.
  Qed.

  (* [comment removed for export] *)
  Definition printf_common_items__stmt : Prop := forall its,
    fstr = prender its -> Forall pitem_ok its -> pargs_ok its a2 ->
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x47304) fc None m (seg_rom asegs)).
  Section Sz41.
  Variables its : ltac2:(SecDiet.SzSec.tyM 'printf_common_items__stmt "v" @its).
  #[using="FMT RLOf RHIf MI ST LO KLO GOT SHB A1 FB NOZ LAY SEPF APPF UFMT NFZ R1F WR1F RI RSTK RFM RSHF"] Lemma printf_common_items__body : ltac2:(SecDiet.SzSec.bodyP 'printf_common_items__stmt "v").
  Proof.
    intros EF OK AOK.
    eapply (L_entry_chk POST). intros mc. intros until x31. intros IVF.
    destruct (Z.eq_dec L 0) as [L0 | LN].
    - eapply L_entry0; eassumption.
    - eapply (L_entry1 ltac:(lia) POST); [| exact IVF].
      clear mc IVF. intros mc dj IV DIR. intros.
      eapply (L_head POST mc [CB 40 dj]); [exact IV | exact DIR | reflexivity |].
      clear mc dj IV DIR. intros mc IV DIR. intros.
      replace (Z_to_bv 64 FMT) with (Z_to_bv 64 (FMT + 0)) by (f_equal; lia).
      eapply (L_items its 0 mc a2); [exact IV | exact DIR | lia | cbn [Z.to_nat skipn]; exact EF | exact OK | exact AOK].
  Qed.
  End Sz41.
  #[using="FMT RLOf RHIf MI ST LO KLO GOT SHB A1 FB NOZ LAY SEPF APPF UFMT NFZ R1F WR1F RI RSTK RFM RSHF"] Theorem printf_common_items : ltac:(let t := eval cbv delta [printf_common_items__stmt] in printf_common_items__stmt in exact t).
  Proof. intros its. ltac2:(SecDiet.SzSec.closeP 'printf_common_items__body "v"). Qed.

End PC.
End CANSEC1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Theorem printf_common_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FMT : Z) (fstr : list byte) (its : list pitem),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2320)%Z -> (KHIGH <= lo)%Z ->
  icptenv m -> a1 = Z_to_bv 64 FMT ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0%Z) fstr ->
  (FMT + (Z.of_nat (length fstr) + 1) <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= FMT)%Z ->
  sobj RNG m FMT (FMT + (Z.of_nat (length fstr) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG FMT (Z.of_nat (length fstr) + 1) ->
  fstr = prender its -> Forall pitem_ok its -> pargs_ok RNG sp m its a2 ->
  evtF asegs RNG (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x47304) fc None m (seg_rom asegs)).
Proof.
  intros until its. intros MI ST LO KLO ENV A1 FB NOZ SEPF (APPF & UFMT & NFZ & RLOf & RHIf & R1F & WR1F & RSHF) RI RSTK RFM EF OK AOK.
  eapply (printf_common_items RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FMT fstr RLOf RHIf);
    first [ eassumption | exact (ie_got _ ENV) | exact (ie_shb _ ENV) | exact (ie_lay _ ENV) | lia ].
Qed.
End CANSEC2.
End TwB.
