(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import ZdFrame ZdFrameThm.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_libc_iface AZ_seq_iface AZ_kx AZ_copy_iface AZ_memmove.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Ltac kxa_norm ::= unfold shspan in *.

Lemma disjoint_from_above : forall W A n K, Forall (fun iv : Z * Z => K <= fst iv) W -> A + n <= K -> disjoint_from W A n.
Proof.
  induction W as [|[lo' hi'] W IH]; intros A n K HW HA; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [lia|]. eapply IH; eassumption.
Qed.
Lemma art_transport : forall W m m', art m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => 0xd1740 <= fst iv) W -> art m'.
Proof.
  intros W m m' (GOT & RIC & SHB & INI & LAY & REAL) MU WM HW.
  unfold art. repeat split.
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply disjoint_from_above; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply disjoint_from_above; [exact HW| cbn; lia]] ].
Qed.

(* [comment removed for export] *)
Definition ee_ctx (RNG : footprint) (m : amem) (SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 : Z) : Prop :=
  (4096 <= B0) /\ (B1 < 2^47) /\ (B0 <= PFX <= OP) /\ (OP <= OEND <= B1) /\ (B0 < B1) /\
  (0 <= LL < 2^32) /\ (0 <= ML < 2^32) /\ (0 <= OFS < 2^64) /\
  (4096 <= LP <= LLIM) /\ (LLIM + 32 < 2^47) /\
  (apart LP (LLIM + 32 - LP) B0 (B1 - B0) \/ (B0 <= LP /\ LLIM + 32 <= B1)) /\
  (4096 <= SQP /\ SQP + 24 < 2^47) /\ (4096 <= LPP /\ LPP + 8 < 2^47) /\
  (apart SQP 24 B0 (B1 - B0)) /\ (apart LPP 8 B0 (B1 - B0)) /\ (apart SQP 24 LPP 8) /\ (apart LP (LLIM + 32 - LP) LPP 8) /\
  (lo <= SPV - 2464) /\ (4096 <= SPV < 2^47) /\
  (B0 + (B1 - B0) <= lo \/ SPV <= B0) /\ (SQP + 24 <= lo \/ SPV <= SQP) /\ (LPP + 8 <= lo \/ SPV <= LPP) /\ (LP + (LLIM + 32 - LP) <= lo \/ SPV <= LP) /\
  (KHIGH <= lo) /\ (0x10007fff8000 <= SPV - 2464) /\ (rng RNG lo (SPV - lo)) /\ (rng_aimg RNG) /\
  (sclr SQP 24) /\ (sclr LPP 8) /\ (AIMG_HI <= LPP) /\ (SQP mod 8 = 0) /\ (LPP mod 8 = 0) /\
  (rw_cells bsegs m SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)]) /\
  (rw_cells bsegs m LPP [C8 (Z_to_bv 64 LP)]) /\
  (ablk B0 B1) /\ (unpoisoned m B0 B1) /\ (rng RNG B0 (B1 - B0)) /\ (rng RNG (shad B0) (shspan B0 (B1 - B0))) /\ (ahull RNG m B0 (B1 - B0)) /\
  (areg RNG m LP (LLIM + 32 - LP)) /\ (ahull RNG m LP (LLIM + 32 - LP)) /\ (rdbl bsegs m LP (LLIM + 32)) /\
  (aro RNG m SQP 24) /\ (aro RNG m LPP 8) /\ (art m) /\ (aro_client RNG m) /\ DEND = DEND.
Ltac ee_open CTX := pose proof CTX as ee_ctx_copy;
  destruct ee_ctx_copy as (B0L & B1H & PFXR & OPE & B01 & LLR & MLR & OFSR & LPR & LLIMH & LITB & SQPR & LPPR & ASQB & ALPB & ASQLP & ALITLP & LOS & SPV47 &
                           OFFB & OFFSQ & OFFLPP & OFFLIT & KLO & SPHI & RSTK & RI & SCSQ & SCLP & AHL & SQ8 & LP8 & SQ0 & LPC0 &
                           ABB & UB0 & RB & RBS & HB & ARL & HL & RDL & ASQ & ALP & ART0 & AROC & _).

Section EXECEND.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 : Z).
  Hypothesis CTX : ee_ctx RNG m SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1.
  Hypothesis SC2 : zd_safecopy2_stmtA.

  Notation POST := (zd_execend_postA 2464 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP OEND SQP LPP LP LLIM LL ML OFS B0 B1 lo m).
  (* [comment removed for export] *)
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -176)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition FIN (low : list cell) (m1 : amem) : Prop :=
    cells_size low = 72%nat /\
    rw_cells bsegs m1 (SPV + -176) (low ++ SAVED) /\ stk bsegs m1 lo (SPV + -176) /\
    munch [(OP, OEND); (LPP, LPP + 8); (SPV - 2464, SPV)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 B0 B1.
  Ltac open_fin FI := destruct FI as (LOW & FR & STK & MU & WM & MI & REG); cbn [app] in FR.
  Ltac fin_close :=
    lazymatch goal with |- FIN ?low ?m2 =>
      lazymatch goal with
      | FR2 : rw_cells _ m2 (SPV + -176) _, STK2 : stk _ m2 lo _, WM2 : wmono _ m m2, MI2 : mem_inv _ m2, REG2 : stk _ m2 B0 B1 |- _ =>
          refine (conj _ (conj FR2 (conj STK2 (conj _ (conj WM2 (conj MI2 REG2))))));
          [ reflexivity
          | first [ assumption
                  | match goal with MU2 : munch _ m m2 |- _ =>
                      eapply munch_weaken; [|exact MU2]; intros x Hx; unfold outside in *; cbn in Hx |- *; lia end ] ]
      end
    end.

  Lemma ab_app : B1 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= B0.
  Proof. ee_open CTX. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold ablk, AIMG_HI, KLS in ABB. lia. Qed.
  Lemma arl_open : ablk LP (LLIM + 32) /\ unpoisoned m LP (LLIM + 32) /\ rng RNG LP (LLIM + 32 - LP) /\ rng RNG (shad LP) (shspan LP (LLIM + 32 - LP)).
  Proof. ee_open CTX. destruct (ARL ltac:(lia)) as (A & U & Q1 & Q2). replace (LP + (LLIM + 32 - LP)) with (LLIM + 32) in A, U by lia. exact (conj A (conj U (conj Q1 Q2))). Qed.
  Lemma al_app : LLIM + 32 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= LP.
  Proof. ee_open CTX. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. destruct arl_open as (ABL & _). unfold ablk, AIMG_HI, KLS in ABL. lia. Qed.

  Lemma fin_unp : forall low m1, FIN low m1 -> unpoisoned m1 B0 B1.
  Proof. ee_open CTX.
    intros low m1 FI. open_fin FI. pose proof ab_app as BA.
    eapply unpoisoned_munch; [exact UB0 | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold sclr, KLS, ASHOFF, KHIGH in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_unpL : forall low m1, FIN low m1 -> unpoisoned m1 LP (LLIM + 32).
  Proof. ee_open CTX.
    intros low m1 FI. open_fin FI. pose proof ab_app as BA. pose proof al_app as BL. destruct arl_open as (ABL & UL0 & RL & RLS).
    eapply unpoisoned_munch; [exact UL0 | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold sclr, KLS, ASHOFF, KHIGH in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_art : forall low m1, FIN low m1 -> art m1.
  Proof. ee_open CTX.
    intros low m1 FI. open_fin FI. pose proof ab_app as BA.
    eapply art_transport; [exact ART0| exact MU| exact WM|].
    unfold ablk, AIMG_HI, KLS, KHIGH in *. repeat constructor; cbn [fst]; lia.
  Qed.
  Lemma fin_aroc : forall low m1, FIN low m1 -> aro_client RNG m1.
  Proof. ee_open CTX.
    intros low m1 FI. open_fin FI. pose proof ab_app as BA.
    eapply aro_client_transport; [exact AROC| exact MU| exact WM|].
    unfold aappW, sclr, ablk, AIMG_HI, KLS, KLOW, KHIGH, ASHOFF in *.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_nil.
  Qed.
  Lemma fin_sq : forall low m1, FIN low m1 -> rw_cells bsegs m1 SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)].
  Proof. ee_open CTX. intros low m1 FI. open_fin FI. eapply rw_cells_transport; [exact SQ0| exact MU| exact WM|]. unfold apart in *. cbn. lia. Qed.
  Lemma fin_asq : forall low m1, FIN low m1 -> aro RNG m1 SQP 24.
  Proof. ee_open CTX.
    intros low m1 FI. open_fin FI. pose proof ab_app as BA. destruct ASQ as (U & Q1 & Q2). split; [| split; [exact Q1| exact Q2]].
    eapply unpoisoned_munch; [exact U| exact MU|]. unfold apart in *. cbn [disjoint_from]. rewrite !shad_div. unfold sclr, KLS, ASHOFF, KHIGH in *.
    repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_alp : forall low m1, FIN low m1 -> aro RNG m1 LPP 8.
  Proof. ee_open CTX.
    intros low m1 FI. open_fin FI. pose proof ab_app as BA. destruct ALP as (U & Q1 & Q2). split; [| split; [exact Q1| exact Q2]].
    eapply unpoisoned_munch; [exact U| exact MU|]. unfold apart in *. cbn [disjoint_from]. rewrite !shad_div. unfold sclr, KLS, ASHOFF, KHIGH in *.
    repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_rdl : forall low m1, FIN low m1 -> rdbl bsegs m1 LP (LLIM + 32).
  Proof. ee_open CTX.
    intros low m1 FI. open_fin FI. destruct LITB as [AP|[IN1 IN2]].
    - eapply rdbl_transport; [exact RDL| exact MU|]. intros x Hx. left. unfold apart in *. cbn. lia.
    - eapply rdbl_sub; [apply rdbl_of_stk; exact REG| lia| lia].
  Qed.
  Lemma fin_areg : forall low m1, FIN low m1 -> areg RNG m1 B0 (B1 - B0).
  Proof. ee_open CTX.
    intros low m1 FI _. split; [|split; [|split]]; [ replace (B0 + (B1 - B0)) with B1 by lia; exact ABB
      | replace (B0 + (B1 - B0)) with B1 by lia; exact (fin_unp _ _ FI) | exact RB | exact RBS ].
  Qed.
  Lemma fin_aregL : forall low m1, FIN low m1 -> areg RNG m1 LP (LLIM + 32 - LP).
  Proof. ee_open CTX.
    intros low m1 FI _. destruct arl_open as (ABL & UL0 & RL & RLS). split; [|split; [|split]];
      [ replace (LP + (LLIM + 32 - LP)) with (LLIM + 32) by lia; exact ABL
      | replace (LP + (LLIM + 32 - LP)) with (LLIM + 32) by lia; exact (fin_unpL _ _ FI) | exact RL | exact RLS ].
  Qed.
  Lemma fin_ahull : forall low m1 A n, FIN low m1 -> B0 <= A -> 0 <= n -> A + n <= B1 -> ahull RNG m1 A n.
  Proof. ee_open CTX.
    intros low m1 A n FI H1 H2 H3. open_fin FI. destruct HB as (RLO & RHI & C1 & C2 & C3 & C4 & C5 & C6 & W & R).
    exists RLO, RHI. split; [lia|]. split; [lia|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|].
    split; [eapply wr_at_transport; [exact W| exact WM] | exact R].
  Qed.
  Lemma fin_ahullL : forall low m1, FIN low m1 -> ahull RNG m1 LP (LLIM + 32 - LP).
  Proof. ee_open CTX.
    intros low m1 FI. open_fin FI. destruct HL as (RLO & RHI & C1 & C2 & C3 & C4 & C5 & C6 & W & R).
    exists RLO, RHI. split; [lia|]. split; [lia|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|].
    split; [eapply wr_at_transport; [exact W| exact WM] | exact R].
  Qed.
  Lemma fin_astk : astk RNG lo (SPV + -176).
  Proof. ee_open CTX. split; [exact KLO|]. split; [eapply rng_sub; [exact RSTK| lia| lia] | exact RI]. Qed.
  Lemma fin_stk : forall low m1, FIN low m1 -> stk bsegs m1 lo (SPV + -176).  Proof. ee_open CTX. intros low m1 FI; open_fin FI; exact STK. Qed.
  Lemma fin_mi : forall low m1, FIN low m1 -> mem_inv bsegs m1.  Proof. ee_open CTX. intros low m1 FI; open_fin FI; exact MI. Qed.
  Lemma fin_reg : forall low m1, FIN low m1 -> stk bsegs m1 B0 B1.  Proof. ee_open CTX. intros low m1 FI; open_fin FI; exact REG. Qed.
  (* [comment removed for export] *)
  Lemma fin_after_sc : forall low m1 m2 D HI, FIN low m1 -> OP <= D -> HI <= OEND ->
    munch [(D, HI); (SPV + -176 - 2288, SPV + -176)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
    stk bsegs m2 lo (SPV + -176) -> stk bsegs m2 B0 B1 -> FIN low m2.
  Proof. ee_open CTX.
    intros low m1 m2 D HI FI HD HHI MUc WMc MI2 STK2 SD2. pose proof FI as FI0. open_fin FI.
    split; [exact LOW|]. split; [| split; [exact STK2| split; [| split; [| split; [exact MI2| exact SD2]]]]].
    - destruct FI0 as [_ [FR0 _]]. eapply rw_cells_transport; [exact FR0| exact MUc| exact WMc|].
      rewrite cells_size_app, LOW. cbn. lia.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. intros x. cbn. lia.
    - eapply wmono_trans; [exact WM| exact WMc].
  Qed.
  Lemma fin_lpp : forall m1 m2 D HI v, OP <= D -> HI <= OEND -> rw_cells bsegs m1 LPP [C8 v] ->
    munch [(D, HI); (SPV + -176 - 2288, SPV + -176)] m1 m2 -> wmono bsegs m1 m2 -> rw_cells bsegs m2 LPP [C8 v].
  Proof. ee_open CTX. intros m1 m2 D HI v HD HHI H MUc WMc. eapply rw_cells_transport; [exact H| exact MUc| exact WMc|]. unfold apart in *. cbn. lia. Qed.
  Lemma fin_sq2 : forall m1 m2 D HI, OP <= D -> HI <= OEND -> rw_cells bsegs m1 SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)] ->
    munch [(D, HI); (SPV + -176 - 2288, SPV + -176)] m1 m2 -> wmono bsegs m1 m2 ->
    rw_cells bsegs m2 SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)].
  Proof. ee_open CTX. intros m1 m2 D HI HD HHI H MUc WMc. eapply rw_cells_transport; [exact H| exact MUc| exact WMc|]. unfold apart in *. cbn. lia. Qed.

  (* [comment removed for export] *)
  Lemma ee_ret : forall low m1 (R lp' : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 x28 x29 x30 x31,
    FIN low m1 -> rw_cells bsegs m1 LPP [C8 (Z_to_bv 64 lp')] ->
    0 <= R < 2^64 -> (zd_is_error R = true \/ (R = LL + ML /\ OP + R <= OEND /\ lp' = LP + LL /\ LP + LL <= LLIM)) ->
    evtF bsegs RNG POST (ST 0x95410 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 R) xs9 xs10 xs11 x28 x29 x30 x31).
  Proof. ee_open CTX.
    intros until x31. intros FI LPC RR HR. pose proof (fin_sq _ _ FI) as SQ. open_fin FI.
    pose proof (rw_cells_merge bsegs m1 (SPV + -176) [] low SAVED FR) as FRM. cbn [app] in FRM. rewrite LOW in FRM. clear FR.
    kx_autoFLAx [KAApp (SPV - 176) 176] [] 30%nat [KZRange SPV 4096 (2^47); KZWr (SPV - 176) 176] [(SPV - 176, 176)] [(SPV - 176, 176)].
    all: try kx_z. all: try kx_acc RSTK.
    all: kx_mem. all: zstep.
    all: lazymatch goal with FRc : rw_cells _ ?mc (SPV + -176) _, STc : stk _ ?mc lo (SPV + -176) |- _ => release_frame FRc STc SPV end.
    all: apply evtF_done; unfold zd_execend_postA; do 14 eexists; exists m1, R, lp'.
    all: split; [reflexivity|]. all: split; [exact MU|]. all: split; [exact WM|]. all: split; [exact MI|]. all: split; [eassumption|].
    all: split; [exact REG|]. all: split; [exact SQ|]. all: split; [exact LPC|]. all: split; [exact RR| exact HR].
  Qed.

  (* [comment removed for export] *)
  Notation SHP x := (Z_to_bv 64 (0x7fff8000 + x / 8)).
  Notation EC20 := (Z_to_bv 64 18446744073709551596).
  Notation LOWS j := [CB 8 j; C8 (Z_to_bv 64 DEND); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (OEND - 32)); C8 (Z_to_bv 64 (LL + ML));
                      C8 (Z_to_bv 64 OFS); C8 (SHP (SQP + 8)); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 LP)].

  (* [comment removed for export] *)
  Lemma ee_after : forall j0 m1 xra x5 x6 x7 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs10 xs11 x28 x29 x30 x31,
    FIN (LOWS j0) m1 -> rw_cells bsegs m1 LPP [C8 (Z_to_bv 64 LP)] -> OP + LL + ML <= OEND -> LP + LL <= LLIM ->
    evtF bsegs RNG POST (ST 0x9535c m1 xra x5 x6 x7 xs0 (Z_to_bv 64 (SQP + 8)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
      (Z_to_bv 64 LL) (Z_to_bv 64 (OP + LL)) (SHP LPP) xs5 (Z_to_bv 64 LPP) (Z_to_bv 64 (SQP + 16)) EC20 (SHP (SQP + 16))
      xs10 xs11 x28 x29 x30 x31).
  Proof. ee_open CTX.
    intros until x31. intros FI LPC1 HLE HLPL.
    pose proof (fin_sq _ _ FI) as SQ1.
    pose proof (fin_asq _ _ FI) as (USQ & RSQ & RSQS). pose proof (fin_alp _ _ FI) as (ULP & RLP & RLPS).
    pose proof ab_app as BA. pose proof SCLP as SCLP'. unfold sclr, KLS in SCLP'. pose proof ASQLP as ASQLP'. unfold apart in ASQLP'.
    pose proof FI as FI0. open_fin FI.
    kx_autoFLAx [KAApp (SPV - 176) 176; KAApp LPP 8; KAUnp SQP 24; KAUnp LPP 8;
               KAShp (0x7fff8000 + LPP / 8) LPP; KAShp (0x7fff8000 + (SQP + 16) / 8) (SQP + 16); KAShp (0x7fff8000 + (SQP + 8) / 8) (SQP + 8)]
           [0x95410; 0x954b0; 0x953a0] 40%nat
           [KZRange SPV 0x10007fff8000 (2^47); KZRange SQP 4096 (2^47 - 24); KZRange LPP 4096 (2^47 - 8); KZRange LP 4096 (2^47);
            KZRange LL 0 (2^32); KZRange ML 0 (2^32); KZRange OFS 0 (2^64 - 1); KZRange OP 4096 (2^47); KZRange OEND 4096 (2^47);
            KZRange PFX 4096 (2^47); KZRange (OP + LL) 4096 (2^47); KZRange (OP + LL - PFX) 0 (2^47); KZRange (LP + LL) 4096 (2^47);
            KZAlign SQP 8; KZAlign LPP 8; KZWr LPP 8; KZDisj LPP 8 SQP 24; KZDisj LPP 8 (SPV - 176) 176]
           [(SQP, 24); (LPP, 8); (SPV - 176, 176)] [(SQP, 24); (LPP, 8); (SPV - 176, 176)].
    all: try kx_z. all: try kx_acc RSTK.
    all: try lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 611232) _ _ _ _) => exfalso; kx_lia end.   (* [comment removed for export] *)
    all: kx_mem.
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 611344) _ _ ?m2 _) =>
          assert (FI2 : FIN (LOWS j0) m2) by fin_close;
          eapply (ee_ret _ m2 18446744073709551596 (LL + LP));
          [ exact FI2
          | first [ assumption | match goal with H : rw_cells _ m2 LPP [C8 (Z_to_bv 64 ?v)] |- _ => replace (LL + LP) with v by lia; exact H end ]
          | lia | left; reflexivity ]
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 611504) _ _ ?m2 _) =>
          assert (FI2 : FIN (LOWS j0) m2) by fin_close;
          pose proof SC2 as SC; unfold zd_safecopy2_stmtA, APZD_SAFECOPY in SC;
          eapply evtF_cut;
          [ eapply SC with (SPV := SPV + -176) (lo := lo) (OP := OP + LL) (OENDW := OEND - 32) (IP := OP + LL - OFS)
                           (LEN := ML) (OV := 1) (B0 := B0) (B1 := B1) (R0 := B0) (R1 := B1);
            [ exact (fin_reg _ _ FI2) | lia | lia | lia | lia | lia | lia | lia
            | apply rdbl_of_stk; exact (fin_reg _ _ FI2) | lia | lia | lia | left; lia
            | exact (fin_stk _ _ FI2) | lia | lia | unfold off_stack; lia | unfold off_stack; lia
            | lia
            | exact (fin_areg _ _ FI2) | eapply (fin_ahull _ _ B0 (B1 - B0) FI2); lia
            | exact (fin_areg _ _ FI2) | eapply (fin_ahull _ _ B0 (B1 - B0) FI2); lia
            | exact (fin_art _ _ FI2) | exact fin_astk | exact (fin_aroc _ _ FI2) | exact (fin_mi _ _ FI2)
            | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia | reflexivity ]
          | clear SC ]
      end.
    intros ms' PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MUc & WMc & MI3 & STK3 & SD3 & RD3).
    lazymatch goal with FI2 : FIN (LOWS j0) ?m2, SQ2 : rw_cells _ ?m2 SQP _, LP2 : rw_cells _ ?m2 LPP _ |- _ =>
      lazymatch type of MUc with munch [(?D, ?HI); _] _ _ =>
      pose proof (fin_after_sc _ m2 m3 D HI FI2 ltac:(lia) ltac:(lia) MUc WMc MI3 STK3 SD3) as FI3;
      pose proof (fin_sq2 m2 m3 D HI ltac:(lia) ltac:(lia) SQ2 MUc WMc) as SQ3;
      pose proof (fin_lpp m2 m3 D HI _ ltac:(lia) ltac:(lia) LP2 MUc WMc) as LP3
    end end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    pose proof FI3 as FI3c. destruct FI3c as (_ & FR3 & _). cbn [app] in FR3.
    kx_autoFLAx [KAApp (SPV - 176) 176] [0x95410] 4%nat [KZRange SPV 4096 (2^47); KZWr (SPV - 176) 176] [(SPV - 176, 176)] [(SPV - 176, 176)].
    all: try kx_z. all: try kx_acc RSTK.
    all: kx_mem.
    all: eapply (ee_ret _ m3 (LL + ML) (LL + LP)); [ exact FI3 | exact LP3 | lia | right; lia ].
  Qed.

  Lemma ee_cp_app : forall A n, B0 <= A -> 0 <= n -> A + n <= B1 -> app_blk A (A + n).
  Proof. ee_open CTX. intros A n H1 H2 H3. pose proof ab_app. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
         unfold ablk, AIMG_HI, KLS in ABB. unfold app_blk, KLOW, KHIGH, KEND, ASHOFF. lia. Qed.
  Lemma ee_cp_appL : forall A n, LP <= A -> 0 < n -> A + n <= LLIM + 32 -> app_blk A (A + n).
  Proof. ee_open CTX. intros A n H1 H2 H3. pose proof al_app. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
         destruct arl_open as (ABL & _). unfold ablk, AIMG_HI, KLS in ABL. unfold app_blk, KLOW, KHIGH, KEND, ASHOFF. lia. Qed.
  Lemma ee_cp_aro : forall low m1 A n, FIN low m1 -> B0 <= A -> 0 <= n -> A + n <= B1 -> aro RNG m1 A n.
  Proof. ee_open CTX.
    intros low m1 A n FI H1 H2 H3. pose proof (fin_unp _ _ FI) as U. split; [| split].
    - eapply unpoisoned_sub; [exact U| lia| lia].
    - eapply rng_sub; [exact RB| lia| lia].
    - eapply rng_sub; [exact RBS| |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  Qed.
  Lemma ee_cp_aroL : forall low m1 A n, FIN low m1 -> LP <= A -> 0 < n -> A + n <= LLIM + 32 -> aro RNG m1 A n.
  Proof. ee_open CTX.
    intros low m1 A n FI H1 H2 H3. pose proof (fin_unpL _ _ FI) as U. destruct arl_open as (ABL & UL0 & RL & RLS). split; [| split].
    - eapply unpoisoned_sub; [exact U| lia| lia].
    - eapply rng_sub; [exact RL| lia| lia].
    - eapply rng_sub; [exact RLS| |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  Qed.
  Lemma ee_cp_ahullL : forall low m1 A n, FIN low m1 -> LP <= A -> 0 <= n -> A + n <= LLIM + 32 -> ahull RNG m1 A n.
  Proof. ee_open CTX.
    intros low m1 A n FI H1 H2 H3. open_fin FI. destruct HL as (RLO & RHI & C1 & C2 & C3 & C4 & C5 & C6 & W & R).
    exists RLO, RHI. split; [lia|]. split; [lia|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|].
    split; [eapply wr_at_transport; [exact W| exact WM] | exact R].
  Qed.
  Lemma ee_cp_stkD : forall low m1 D n, FIN low m1 -> B0 <= D -> 0 <= n -> D + n <= B1 -> stk bsegs m1 D (D + n).
  Proof. ee_open CTX.
    intros low m1 D n FI H1 H2 H3. open_fin FI.
    destruct (stk_split bsegs m1 B0 D B1 REG ltac:(lia)) as [_ Q2]. destruct (stk_split bsegs m1 D (D + n) B1 Q2 ltac:(lia)) as [Q3 _]. exact Q3.
  Qed.
  Lemma ee_cp_rdblL : forall low m1 A n, FIN low m1 -> LP <= A -> A + n <= LLIM + 32 -> rdbl bsegs m1 A (A + n).
  Proof. ee_open CTX. intros low m1 A n FI H1 H2. eapply rdbl_sub; [exact (fin_rdl _ _ FI)| lia| lia]. Qed.
  Lemma ee_cp_after_call : forall low m1 m2 D n, FIN low m1 -> OP <= D -> 0 <= n -> D + n <= OEND ->
    munch [(SPV + -176 - 2224, SPV + -176); (D, D + n)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
    stk bsegs m2 lo (SPV + -176) -> stk bsegs m2 D (D + n) -> FIN low m2.
  Proof. ee_open CTX.
    intros low m1 m2 D n FI H1 H2 H3 MUc WMc MI2 STK2 SD2. pose proof FI as FI0. open_fin FI.
    split; [exact LOW|]. split; [| split; [exact STK2| split; [| split; [| split; [exact MI2|]]]]].
    - destruct FI0 as [_ [FR0 _]]. eapply rw_cells_transport; [exact FR0| exact MUc| exact WMc|].
      rewrite cells_size_app, LOW. cbn. lia.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. intros x. cbn. lia.
    - eapply wmono_trans; [exact WM| exact WMc].
    - destruct (stk_split bsegs m1 B0 D B1 REG ltac:(lia)) as [Q1 Q2]. destruct (stk_split bsegs m1 D (D + n) B1 Q2 ltac:(lia)) as [_ Q3].
      apply (stk_merge bsegs m2 B0 D B1); [| | lia].
      + eapply stk_transport_disjoint; [exact Q1| exact MUc| exact WMc| cbn; lia].
      + apply (stk_merge bsegs m2 D (D + n) B1); [exact SD2| | lia].
        eapply stk_transport_disjoint; [exact Q3| exact MUc| exact WMc| cbn; lia].
  Qed.
  Lemma ee_cp_lpp : forall m1 m2 D n v, OP <= D -> 0 <= n -> D + n <= OEND -> rw_cells bsegs m1 LPP [C8 v] ->
    munch [(SPV + -176 - 2224, SPV + -176); (D, D + n)] m1 m2 -> wmono bsegs m1 m2 -> rw_cells bsegs m2 LPP [C8 v].
  Proof. ee_open CTX. intros m1 m2 D n v HD HN HHI H MUc WMc. eapply rw_cells_transport; [exact H| exact MUc| exact WMc|]. unfold apart in *. cbn. lia. Qed.

  Ltac ee_callL FI LPC D S FI2 LPC2 :=
    eapply evtF_cut;
    [ eapply (zd_memmoveZ_proofA RNG D S 16 (SPV + -176));
      [ apply (ee_cp_stkD _ _ D 16 FI); lia | apply (ee_cp_rdblL _ _ S 16 FI); lia | lia | exact (fin_stk _ _ FI) | lia | lia | lia | lia
      | apply ee_cp_appL; lia | apply (ee_cp_aroL _ _ S 16 FI); lia | apply (ee_cp_ahullL _ _ S 16 FI); lia
      | apply ee_cp_app; lia | apply (ee_cp_aro _ _ D 16 FI); lia | apply (fin_ahull _ _ D 16 FI); lia
      | exact (fin_art _ _ FI) | exact fin_astk | exact (fin_mi _ _ FI) | reflexivity | reflexivity | reflexivity ]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in let m2 := fresh "m" in
      let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MI2 := fresh "MIc" in let STK2 := fresh "STKc" in let SD2 := fresh "SDc" in
      intros ms' PO;
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MI2 & STK2 & SD2);
      pose proof (ee_cp_after_call _ _ m2 D 16 FI ltac:(lia) ltac:(lia) ltac:(lia) MUc WMc MI2 STK2 SD2) as FI2;
      pose proof (ee_cp_lpp _ m2 D 16 _ ltac:(lia) ltac:(lia) ltac:(lia) LPC MUc WMc) as LPC2;
      clear MUc WMc MI2 STK2 SD2;
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end ].

  Lemma ee_cp_wb : forall (n : nat) j0 m1 (X Y : Z) xra x5 x6 x7 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 x28 x29 x30 x31,
    OP + LL - Y < Z.of_nat n -> LP <= X -> X + (OP + LL - Y) + 31 <= LLIM + 32 -> OP <= Y -> Y < OP + LL -> OP + LL <= OEND - 32 ->
    FIN (LOWS j0) m1 -> rw_cells bsegs m1 LPP [C8 (Z_to_bv 64 LP)] -> OP + LL + ML <= OEND -> LP + LL <= LLIM ->
    evtF bsegs RNG POST (ST 0x95330 m1 xra x5 x6 x7 xs0 (Z_to_bv 64 (SQP + 8)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
      (Z_to_bv 64 LL) (Z_to_bv 64 (OP + LL)) (SHP LPP) xs5 (Z_to_bv 64 LPP) (Z_to_bv 64 (SQP + 16)) EC20 (SHP (SQP + 16))
      (Z_to_bv 64 Y) (Z_to_bv 64 (X + 16)) x28 x29 x30 x31).
  Proof. ee_open CTX.
    induction n as [|n IH]; intros until x31; intros HN HX HXE HOY HYE HEW FI LPC HLE HLPL; [exfalso; lia|].
    pose proof FI as FI1. open_fin FI.
    kx_autoFLAx (@nil kza) (@nil Z) 10%nat [KZRange X 4096 (2^47); KZRange Y 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    ee_callL FI1 LPC Y X FI2 LPC2.
    kx_autoFLAx (@nil kza) (@nil Z) 12%nat [KZRange X 4096 (2^47); KZRange Y 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    ee_callL FI2 LPC2 (Y + 16) (X + 16) FI3 LPC3.
    kx_autoFLAx (@nil kza) [0x95330; 0x9535c] 12%nat [KZRange X 4096 (2^47); KZRange Y 4096 (2^47); KZRange (OP + LL) 0 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x95330) _ _ ?m2 _) =>
             replace (X + 48) with ((X + 32) + 16) by lia;
             apply (IH j0 m2 (X + 32) (Y + 32)); first [assumption | lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9535c) _ _ ?m2 _) =>
             apply (ee_after j0 m2); first [assumption | lia]
         end.
  Qed.
  Lemma ee_cp_wbe : forall j0 m1 xra x5 x6 x7 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs10 x28 x29 x30 x31,
    OP + LL <= OEND - 32 ->
    FIN (LOWS j0) m1 -> rw_cells bsegs m1 LPP [C8 (Z_to_bv 64 LP)] -> OP + LL + ML <= OEND -> LP + LL <= LLIM ->
    evtF bsegs RNG POST (ST 0x9530c m1 xra x5 x6 x7 xs0 (Z_to_bv 64 (SQP + 8)) (Z_to_bv 64 OP) xa1 xa2 xa3 xa4 xa5 xa6 xa7
      (Z_to_bv 64 LL) (Z_to_bv 64 (OP + LL)) (SHP LPP) xs5 (Z_to_bv 64 LPP) (Z_to_bv 64 (SQP + 16)) EC20 (SHP (SQP + 16))
      xs10 (Z_to_bv 64 LP) x28 x29 x30 x31).
  Proof. ee_open CTX.
    intros until x31; intros HEW FI LPC HLE HLPL. pose proof FI as FI1. open_fin FI.
    kx_autoFLAx (@nil kza) (@nil Z) 10%nat [KZRange LP 4096 (2^47); KZRange OP 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    ee_callL FI1 LPC OP LP FI2 LPC2.
    pose proof FI2 as FI2c. destruct FI2c as (_ & FR2 & _). cbn [app] in FR2.
    kx_autoFLAx [KAApp (SPV - 176) 176] [0x95330; 0x9535c] 16%nat
      [KZRange SPV 4096 (2^47); KZWr (SPV - 176) 176;
       KZRange LP 4096 (2^47); KZRange OP 4096 (2^47); KZRange LL 0 (2^32); KZRange (OP + LL) 0 (2^47)]
      [(SPV - 176, 176)] [(SPV - 176, 176)].
    all: try kx_z. all: try kx_acc RSTK.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x95330) _ _ ?m2 _) =>
             replace (LP + 32) with ((LP + 16) + 16) by lia;
             apply (ee_cp_wb (Z.to_nat LL) j0 m2 (LP + 16) (OP + 16)); first [assumption | lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9535c) _ _ ?m2 _) =>
             apply (ee_after j0 m2); first [assumption | lia]
         end.
  Qed.

  Lemma ee_cp_tl : forall (n : nat) j0 m1 (X Y : Z) (w : word) xra x5 x6 x7 xa0 xa3 xa4 xa5 xa6 xa7 xs5 xs10 xs11 x28 x29 x30 x31,
    OP + LL - Y <= Z.of_nat n -> X - Y = LP - OP -> OP <= Y -> Y < OP + LL -> w = Z_to_bv 64 (X - Y) ->
    FIN (LOWS j0) m1 -> rw_cells bsegs m1 LPP [C8 (Z_to_bv 64 LP)] -> OP + LL + ML <= OEND -> LP + LL <= LLIM ->
    evtF bsegs RNG POST (ST 0x952b8 m1 xra x5 x6 x7 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (SQP + 8)) xa0 (Z_to_bv 64 Y) w
      xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 LL) (Z_to_bv 64 (OP + LL)) (SHP LPP) xs5 (Z_to_bv 64 LPP) (Z_to_bv 64 (SQP + 16)) EC20
      (SHP (SQP + 16)) xs10 xs11 x28 x29 x30 x31).
  Proof. ee_open CTX.
    induction n as [|n IH]; intros until x31; intros HN HXY HOY HYE Hw FI LPC HLE HLPL; [exfalso; lia|].
    pose proof (fin_unp _ _ FI) as UB1. pose proof (fin_unpL _ _ FI) as UL1.
    destruct (rdbl_bytes bsegs m1 LP (LLIM + 32) (fin_rdl _ _ FI) ltac:(lia)) as (bs & BL & BA).
    destruct arl_open as (ABL & UL0 & RL & RLS). pose proof ALPB as ALPB'. unfold apart in ALPB'.
    pose proof FI as FI1. open_fin FI. pose proof ab_app as BA'. pose proof al_app as BL'.
    zstep. kx_mkR_fold.
    lazymatch goal with
    | |- context [Z_to_bv 64 (bv_unsigned w + Y)] =>
        replace (Z_to_bv 64 (bv_unsigned w + Y)) with (Z_to_bv 64 X)
          by (rewrite Hw, Z_to_bv_unsigned; apply Z_to_bv_eqm; unfold bv_wrap; cbn [bv_modulus]; rewrite Zplus_mod_idemp_l; f_equal; lia)
    | |- context [Z_to_bv 64 (Y + bv_unsigned w)] =>
        replace (Z_to_bv 64 (Y + bv_unsigned w)) with (Z_to_bv 64 X)
          by (rewrite Hw, Z_to_bv_unsigned; apply Z_to_bv_eqm; unfold bv_wrap; cbn [bv_modulus]; rewrite Zplus_mod_idemp_r; f_equal; lia)
    end.
    kx_autoFLAx [KAUnp X 1; KAUnp Y 1; KAApp Y 1] [0x952b8; 0x9535c] 40%nat
      [KZRange X 4096 (2^47 - 1); KZRange Y 4096 (2^47 - 1); KZRange (OP + LL) 0 (2^47);
       KZRange (OP + LL - Y) 1 (2^47); KZRange (X - LP) 0 (2^47); KZRange (LLIM + 32 - X) 1 (2^47); KZWr Y 1; KZDisj Y 1 LPP 8]
      [(X, 1)] [(X, 1); (Y, 1)].
    all: try kx_z. all: try kx_acc RB. all: try kx_acc RL.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x952b8) _ _ _ _) => idtac
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9535c) _ _ _ _) => idtac
         | |- evtF _ _ _ _ => kx_trap_fast
         | _ => idtac
         end.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x952b8) _ _ ?m2 _) =>
             apply (IH j0 m2 (X + 1) (Y + 1) w); try lia; first [ fin_close | assumption | rewrite Hw; f_equal; lia ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9535c) _ _ ?m2 _) =>
             apply (ee_after j0 m2); [ fin_close | assumption | lia | lia ]
         | |- evtF _ _ _ (MS ?rr _ ?pc _ _ _ _) => idtac "UNEXPPC" pc; fail 0
         | |- ?G => idtac "UNEXPG" G; fail 0
         end.
  Qed.

  Lemma ee_cp_te : forall j0 m1 (Y : Z) xra x5 x6 x7 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs10 xs11 x28 x29 x30 x31,
    Y = Z.max OP (OEND - 32) ->
    FIN (LOWS j0) m1 -> rw_cells bsegs m1 LPP [C8 (Z_to_bv 64 LP)] -> OP + LL + ML <= OEND -> LP + LL <= LLIM ->
    evtF bsegs RNG POST (ST 0x9529c m1 xra x5 x6 x7 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (SQP + 8)) (Z_to_bv 64 OP) (Z_to_bv 64 Y)
      xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 LL) (Z_to_bv 64 (OP + LL)) (SHP LPP) xs5 (Z_to_bv 64 LPP) (Z_to_bv 64 (SQP + 16)) EC20
      (SHP (SQP + 16)) xs10 xs11 x28 x29 x30 x31).
  Proof. ee_open CTX.
    intros until x31; intros HY FI LPC HLE HLPL. pose proof FI as FI1. open_fin FI.
    kx_autoFLAx [KAApp (SPV - 176) 176] [0x952b8; 0x9535c] 12%nat
      [KZRange SPV 4096 (2^47); KZWr (SPV - 176) 176; KZRange LPP 4096 (2^47 - 8); KZAlign LPP 8;
       KZRange OP 4096 (2^47); KZRange Y 4096 (2^47); KZRange (OP + LL) 4096 (2^47); KZRange (OEND - 32) 0 (2^47);
       KZRange LP 4096 (2^47)]
      [(SPV - 176, 176); (LPP, 8)] [(SPV - 176, 176)].
    all: try kx_z. all: try kx_acc RSTK.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9535c) _ _ ?m2 _) =>
             apply (ee_after j0 m2); [ fin_close | assumption | lia | lia ]
         | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?Yc) ?w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x952b8) _ _ ?m2 _) =>
             apply (ee_cp_tl (Z.to_nat (OP + LL - Yc)) j0 m2 (LP + (Yc - OP)) Yc w); try lia; first [ fin_close | assumption | f_equal; lia ]
         | |- evtF _ _ _ (MS ?rr _ ?pc _ _ _ _) => idtac "UNEXPPC" pc; fail 0
         | |- ?G => idtac "UNEXPG" G; fail 0
         end.
  Qed.

  Lemma ee_cp_finc8 : forall low v m1, FIN (C8 v :: low) m1 -> FIN (CB 8 (le8 v) :: low) m1.
  Proof.
    intros low v m1 (LOW & FR & R). split; [exact LOW|]. split; [|exact R].
    eapply rw_cells_recell; [exact FR| |reflexivity].
    destruct FR as [[WF _] _]. cbn [app cells_wf cell_wf] in WF |- *. split; [apply length_le8| exact (proj2 WF)].
  Qed.

  Lemma ee_cp_tw : forall m1 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xs11 x28 x29 x30 x31,
    OP <= OEND - 32 ->
    FIN [C8 (Z_to_bv 64 OP); C8 (Z_to_bv 64 DEND); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (OEND - 32)); C8 (Z_to_bv 64 (LL + ML));
         C8 (Z_to_bv 64 OFS); C8 (SHP (SQP + 8)); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 LP)] m1 ->
    rw_cells bsegs m1 LPP [C8 (Z_to_bv 64 LP)] -> OP + LL + ML <= OEND -> LP + LL <= LLIM ->
    evtF bsegs RNG POST (ST 0x95294 m1 xra x5 x6 x7 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (SQP + 8)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
      (Z_to_bv 64 LL) (Z_to_bv 64 (OP + LL)) (SHP LPP) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LPP) (Z_to_bv 64 (SQP + 16)) EC20
      (SHP (SQP + 16)) xs10 xs11 x28 x29 x30 x31).
  Proof. ee_open CTX.
    intros until x31; intros HOW FI LPC HLE HLPL. pose proof FI as FI1. open_fin FI.
    kx_autoFLAx [KAApp (SPV - 176) 176] [0x9529c] 4%nat [KZRange SPV 4096 (2^47); KZWr (SPV - 176) 176]
      [(SPV - 176, 176)] [(SPV - 176, 176)].
    all: try kx_z. all: try kx_acc RSTK.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?Yc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9529c) _ _ ?m2 _) =>
             apply (ee_cp_te (le8 (Z_to_bv 64 OP)) m2 Yc); [ lia | apply ee_cp_finc8; fin_close | assumption | lia | lia ]
         | |- evtF _ _ _ (MS ?rr _ ?pc _ _ _ _) => idtac "UNEXPPC" pc; fail 0
         | |- ?G => idtac "UNEXPG" G; fail 0
         end.
  Qed.

  Lemma ee_cp_bl : forall (n : nat) j0 m1 (X Y : Z) xra x5 x6 x7 xa4 xa5 xa6 xa7 xs5 xs10 xs11 x28 x29 x30 x31,
    OP + LL - Y <= Z.of_nat n -> LP <= X -> X - LP = Y - OP -> OP <= Y -> Y < OP + LL ->
    FIN (LOWS j0) m1 -> rw_cells bsegs m1 LPP [C8 (Z_to_bv 64 LP)] -> OP + LL + ML <= OEND -> LP + LL <= LLIM ->
    evtF bsegs RNG POST (ST 0x951d4 m1 xra x5 x6 x7 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (SQP + 8)) (Z_to_bv 64 Y) (Z_to_bv 64 Y)
      (Z_to_bv 64 X) (Z_to_bv 64 X) xa4 xa5 xa6 xa7 (Z_to_bv 64 LL) (Z_to_bv 64 (OP + LL)) (SHP LPP) xs5 (Z_to_bv 64 LPP)
      (Z_to_bv 64 (SQP + 16)) EC20 (SHP (SQP + 16)) xs10 xs11 x28 x29 x30 x31).
  Proof. ee_open CTX.
    induction n as [|n IH]; intros until x31; intros HN HX HXY HOY HYE FI LPC HLE HLPL; [exfalso; lia|].
    pose proof (fin_unp _ _ FI) as UB1. pose proof (fin_unpL _ _ FI) as UL1.
    destruct (rdbl_bytes bsegs m1 LP (LLIM + 32) (fin_rdl _ _ FI) ltac:(lia)) as (bs & BL & BA).
    destruct arl_open as (ABL & UL0 & RL & RLS). pose proof ALPB as ALPB'. unfold apart in ALPB'.
    pose proof FI as FI1. open_fin FI. pose proof ab_app as BA'. pose proof al_app as BL'.
    kx_autoFLAx [KAUnp X 1; KAUnp Y 1; KAApp Y 1] [0x951d4; 0x9535c] 40%nat
      [KZRange X 4096 (2^47 - 1); KZRange Y 4096 (2^47 - 1); KZRange (OP + LL) 0 (2^47);
       KZRange (OP + LL - Y) 1 (2^47); KZRange (X - LP) 0 (2^47); KZRange (LLIM + 32 - X) 1 (2^47); KZWr Y 1; KZDisj Y 1 LPP 8]
      [(X, 1)] [(X, 1); (Y, 1)].
    all: try kx_z. all: try kx_acc RB. all: try kx_acc RL.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x951d4) _ _ ?m2 _) =>
             apply (IH j0 m2 (X + 1) (Y + 1)); try lia; first [ fin_close | assumption ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9535c) _ _ ?m2 _) =>
             apply (ee_after j0 m2); [ fin_close | assumption | lia | lia ]
         end.
  Qed.

  Lemma ee_cp_wa : forall (n : nat) m1 (X Y : Z) xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31,
    OEND - 32 - Y < Z.of_nat n -> X - Y = LP - OP -> OP <= Y -> Y < OEND - 32 -> OEND - 32 < OP + LL ->
    FIN [C8 (Z_to_bv 64 OP); C8 (Z_to_bv 64 DEND); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (OEND - 32)); C8 (Z_to_bv 64 (LL + ML));
         C8 (Z_to_bv 64 OFS); C8 (SHP (SQP + 8)); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 LP)] m1 ->
    rw_cells bsegs m1 LPP [C8 (Z_to_bv 64 LP)] -> OP + LL + ML <= OEND -> LP + LL <= LLIM ->
    evtF bsegs RNG POST (ST 0x95268 m1 xra x5 x6 x7 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (SQP + 8)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
      (Z_to_bv 64 LL) (Z_to_bv 64 (OP + LL)) (SHP LPP) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LPP) (Z_to_bv 64 (SQP + 16)) EC20
      (SHP (SQP + 16)) (Z_to_bv 64 Y) (Z_to_bv 64 (X + 16)) x28 x29 x30 x31).
  Proof. ee_open CTX.
    induction n as [|n IH]; intros until x31; intros HN HPAR HOY HYW HWE FI LPC HLE HLPL; [exfalso; lia|].
    pose proof FI as FI1. open_fin FI.
    kx_autoFLAx (@nil kza) (@nil Z) 10%nat [KZRange X 4096 (2^47); KZRange Y 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    ee_callL FI1 LPC Y X FI2 LPC2.
    kx_autoFLAx (@nil kza) (@nil Z) 12%nat [KZRange X 4096 (2^47); KZRange Y 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    ee_callL FI2 LPC2 (Y + 16) (X + 16) FI3 LPC3.
    kx_autoFLAx (@nil kza) [0x95268; 0x95294] 12%nat [KZRange X 4096 (2^47); KZRange Y 4096 (2^47); KZRange (OEND - 32) 0 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x95268) _ _ ?m2 _) =>
             replace (X + 48) with ((X + 32) + 16) by lia;
             apply (IH m2 (X + 32) (Y + 32)); first [assumption | lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x95294) _ _ ?m2 _) =>
             apply (ee_cp_tw m2); first [assumption | lia]
         | |- evtF _ _ _ (MS ?rr _ ?pc _ _ _ _) => idtac "UNEXPPC" pc rr; fail 0
         | |- ?G => idtac "UNEXPG" G; fail 0
         end.
  Qed.
  Lemma ee_cp_wae : forall j0 m1 xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 x28 x29 x30 x31,
    7 < LL -> OEND - 32 < OP + LL -> OP <= OEND - 32 ->
    FIN (LOWS j0) m1 -> rw_cells bsegs m1 LPP [C8 (Z_to_bv 64 LP)] -> OP + LL + ML <= OEND -> LP + LL <= LLIM ->
    evtF bsegs RNG POST (ST 0x95240 m1 xra x5 x6 x7 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (SQP + 8)) (Z_to_bv 64 OP) xa1 xa2 xa3
      xa4 xa5 xa6 xa7 (Z_to_bv 64 LL) (Z_to_bv 64 (OP + LL)) (SHP LPP) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LPP)
      (Z_to_bv 64 (SQP + 16)) EC20 (SHP (SQP + 16)) xs10 (Z_to_bv 64 LP) x28 x29 x30 x31).
  Proof. ee_open CTX.
    intros until x31; intros HL7 HWE HOW FI LPC HLE HLPL. open_fin FI.
    kx_autoFLAx [KAApp (SPV - 176) 176] (@nil Z) 10%nat
      [KZRange SPV 4096 (2^47); KZWr (SPV - 176) 176; KZRange LP 4096 (2^47); KZRange OP 4096 (2^47);
       KZRange (OEND - 32) 0 (2^47); KZRange (OEND - 32 - OP) 0 (2^47); KZDisj (SPV - 176) 176 LPP 8]
      [(SPV - 176, 176)] [(SPV - 176, 176)].
    all: try kx_z. all: try kx_acc RSTK.
    all: kx_mem.
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
        first
          [ assert (FI1 : FIN [C8 (Z_to_bv 64 OP); C8 (Z_to_bv 64 DEND); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (OEND - 32));
                               C8 (Z_to_bv 64 (LL + ML)); C8 (Z_to_bv 64 OFS); C8 (SHP (SQP + 8)); C8 (Z_to_bv 64 PFX);
                               C8 (Z_to_bv 64 LP)] m2) by fin_close
          | match goal with FRc : rw_cells _ m2 (SPV + -176) ?cs |- _ => idtac "FRCELLS" cs end; fail 1 ]
    end.
    ee_callL FI1 LPC OP LP FI2 LPC2.
    pose proof FI2 as FI2c. destruct FI2c as (_ & FR2 & _). cbn [app] in FR2.
    kx_autoFLAx [KAApp (SPV - 176) 176] [0x95268; 0x95294] 16%nat
      [KZRange SPV 4096 (2^47); KZWr (SPV - 176) 176; KZRange LP 4096 (2^47); KZRange OP 4096 (2^47);
       KZRange (OEND - 32) 0 (2^47); KZRange (OEND - 32 - OP) 0 (2^47)]
      [(SPV - 176, 176)] [(SPV - 176, 176)].
    all: try kx_z. all: try kx_acc RSTK.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x95268) _ _ ?m2 _) =>
             replace (LP + 32) with ((LP + 16) + 16) by lia;
             apply (ee_cp_wa (Z.to_nat (OEND - 32 - OP)) m2 (LP + 16) (OP + 16)); first [assumption | lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x95294) _ _ ?m2 _) =>
             apply (ee_cp_tw m2); first [assumption | lia]
         | |- evtF _ _ _ (MS ?rr _ ?pc _ _ _ _) => idtac "UNEXPPC" pc rr; fail 0
         | |- ?G => idtac "UNEXPG" G; fail 0
         end.
  Qed.

  Lemma ee_cp : forall j0 m1 xra x5 x6 x7 xa1 xa3 xa4 xa5 xa6 xa7 xs10 x28 x29 x30 x31,
    FIN (LOWS j0) m1 -> rw_cells bsegs m1 LPP [C8 (Z_to_bv 64 LP)] -> OP + LL + ML <= OEND -> LP + LL <= LLIM ->
    evtF bsegs RNG POST (ST 0x951c0 m1 xra x5 x6 x7 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (SQP + 8)) (Z_to_bv 64 OP) xa1 (Z_to_bv 64 7) xa3 xa4 xa5 xa6 xa7
      (Z_to_bv 64 LL) (Z_to_bv 64 (OP + LL)) (SHP LPP) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LPP) (Z_to_bv 64 (SQP + 16)) EC20
      (SHP (SQP + 16)) xs10 (Z_to_bv 64 LP) x28 x29 x30 x31).
  Proof. ee_open CTX.
    intros until x31. intros FI LPC HLE HLPL.
    pose proof FI as FI1. open_fin FI.
    kx_autoFLAx [KAApp (SPV - 176) 176] [0x9535c; 0x951d4; 0x9530c; 0x9529c; 0x95240] 40%nat
      [KZRange SPV 4096 (2^47); KZRange LL 0 (2^32); KZRange OP 4096 (2^47); KZRange (OEND - 32) 0 (2^47); KZRange (OP + LL) 4096 (2^47);
       KZWr (SPV - 176) 176]
      [(SPV - 176, 176)] [(SPV - 176, 176)].
    all: try kx_z. all: try kx_acc RSTK.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9535c) _ _ ?m2 _) =>
             apply (ee_after j0 m2); [ first [ assumption | fin_close ] | assumption | lia | lia ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x951d4) _ _ ?m2 _) =>
             apply (ee_cp_bl (Z.to_nat LL) j0 m2 LP OP); [ lia | lia | lia | lia | lia | first [ assumption | fin_close ] | assumption | lia | lia ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9530c) _ _ ?m2 _) =>
             apply (ee_cp_wbe j0 m2); [ lia | first [ assumption | fin_close ] | assumption | lia | lia ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9529c) _ _ ?m2 _) =>
             apply (ee_cp_te j0 m2 OP); [ lia | first [ assumption | fin_close ] | assumption | lia | lia ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x95240) _ _ ?m2 _) =>
             apply (ee_cp_wae j0 m2); [ lia | lia | lia | first [ assumption | fin_close ] | assumption | lia | lia ]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma ee_entry : forall t0 t1 t2 t3 t4 t5 t6,
    stk bsegs m lo SPV -> stk bsegs m B0 B1 -> mem_inv bsegs m ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OP) (Z_to_bv 64 OEND) (Z_to_bv 64 SQP) (Z_to_bv 64 LPP)
                                 (Z_to_bv 64 LLIM) (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 DEND) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 APZD_EXECEND) fc None m (seg_rom bsegs)).
  Proof. ee_open CTX.
    intros t0 t1 t2 t3 t4 t5 t6 ST0 REG0 MI0.
    pose proof ART0 as (GOT & RIC & SHB & INI & LAY & REAL). pose proof ab_app as BA. pose proof al_app as BL.
    destruct arl_open as (ABL & UL0 & RL & RLS).
    assert (MU : munch [(OP, OEND); (LPP, LPP + 8); (SPV - 2464, SPV)] m m) by apply munch_refl. assert (WM : wmono bsegs m m) by apply wmono_refl.
    pose proof UB0 as UB1. pose proof UL0 as UL1. pose proof SQ0 as SQ1. pose proof LPC0 as LPC1.
    pose proof ASQ as ASQ1. pose proof ALP as ALP1. destruct ASQ1 as (USQ & RSQ & RSQS). destruct ALP1 as (ULP & RLP & RLPS).
    carve_frame 176%nat ST0.
    unfold APZD_EXECEND.
    kx_autoFLAx [KAApp (SPV - 176) 176; KAUnp SQP 24; KAUnp LPP 8] [0x95410; 0x951c0] 80%nat
      [KZRange SPV 0x10007fff8000 (2^47); KZRange OP 4096 (2^47); KZRange OEND 0 (2^47); KZRange SQP 4096 (2^47 - 24); KZRange LPP 4096 (2^47 - 8);
       KZRange LLIM 0 (2^47); KZRange LP 4096 (2^47); KZRange PFX 0 (2^47); KZRange LL 0 (2^32); KZRange ML 0 (2^32);
       KZAlign SQP 8; KZAlign LPP 8; KZWr (SPV - 176) 176; KZDisj (SPV - 176) 176 SQP 24; KZDisj (SPV - 176) 176 LPP 8]
      [(SPV - 176, 176); (SQP, 24); (LPP, 8)] [(SPV - 176, 176); (SQP, 24); (LPP, 8)].
    all: try kx_cell_lit. all: try kx_acc RI.
    all: kx_mem.
    all: try replace (Z_to_bv 64 ((SQP + 16) mod 2 ^ 64 / 8 + 2147450880)) with (Z_to_bv 64 (0x7fff8000 + (SQP + 16) / 8)) by (f_equal; rewrite Z.mod_small by lia; lia).
    all: try replace (Z_to_bv 64 ((SQP + 8) mod 2 ^ 64 / 8 + 2147450880)) with (Z_to_bv 64 (0x7fff8000 + (SQP + 8) / 8)) by (f_equal; rewrite Z.mod_small by lia; lia).
    all: try replace (Z_to_bv 64 (LPP mod 2 ^ 64 / 8 + 2147450880)) with (Z_to_bv 64 (0x7fff8000 + LPP / 8)) by (f_equal; rewrite Z.mod_small by lia; lia).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 611344) _ _ ?m2 _) =>
          lazymatch goal with FRc : rw_cells _ m2 (SPV + -176) (CB 72 ?j :: _) |- _ =>
            assert (FI2 : FIN [CB 72 j] m2) by fin_close end;
          eapply (ee_ret _ m2 _ LP); [ exact FI2 | assumption | lia | left; reflexivity ]
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 610752) _ _ ?m2 _) =>
          lazymatch goal with FRc : rw_cells _ m2 (SPV + -176) (CB 8 ?j :: _) |- _ =>
            replace (Z_to_bv 64 ((SQP + 8) mod 2 ^ 64 / 8 + 2147450880)) with (SHP (SQP + 8)) in FRc by (f_equal; rewrite Z.mod_small by lia; lia);
            assert (FI2 : FIN (LOWS j) m2) by fin_close;
            eapply (ee_cp j m2); [ exact FI2 | assumption | first [ lia | kx_lia ] | first [ lia | kx_lia ] ] end
      end.
  Qed.
End EXECEND.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem zd_execend_proofA : zd_safecopy2_stmtA -> zd_execend_stmtA.
Proof.
  intros SC2 RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1.
  intros REG B0L B1H PFXR OPE SQC LPC LLR MLR OFSR LPR LLIMH RDL LITB SQPL SQPH LPPL LPPH ASQB ALPB ASQLP ALITLP STK LOS SPR OFFB OFFSQ OFFLPP OFFLIT
         B01 SCSQ SCLP LPPI SQ8 LP8 ARB HB ARL HL ASQ ALP ART AST AROC MI -> -> -> -> -> -> -> ->.
  unfold OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec.ZdDCtx.WILDCOPY_OVERLENGTH in *. unfold off_stack in *.
  pose proof AST as (KLO & RSTK & RI). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  destruct (ARB ltac:(lia)) as (ABB & UB0 & RB & RBS). replace (B0 + (B1 - B0)) with B1 in ABB, UB0 by lia.
  assert (CTX : ee_ctx RNG m SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1).
  { unfold ee_ctx. repeat (lazymatch goal with |- _ /\ _ => split end); first [assumption | reflexivity | lia]. }
  unfold APZD_EXECEND.
  apply (ee_entry RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 CTX SC2);
    [ exact STK | exact REG | exact MI ].
Qed.
End CANSEC1.
(* [comment removed for export] *)
