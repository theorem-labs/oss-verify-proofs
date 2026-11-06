(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import ZdFrame ZdFrameThm.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit MemRange.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_libc_iface AZ_seq_iface AZ_kx AZ_copy_iface AZ_dbs_iface.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
  Forall (fun iv : Z * Z => 0xd5d40 <= fst iv) W -> art m'.
Proof.
  intros W m m' (GOT & RIC & SHB & INI & LAY & REAL) MU WM HW.
  unfold art. repeat split.
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply disjoint_from_above; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply disjoint_from_above; [exact HW| cbn; lia]] ].
Qed.

(* [comment removed for export] *)
Definition es_ctx (RNG : footprint) (m : amem) (SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 : Z) : Prop :=
  (4096 <= B0) /\ (B1 < 2^47) /\ (B0 <= PFX <= OP) /\ (OP <= OEND <= B1) /\ (B0 < B1) /\ (0 <= OENDW) /\ (OENDW + 32 <= OEND) /\
  (0 <= LL < 2^32) /\ (0 <= ML < 2^32) /\ (0 <= OFS < 2^64) /\
  (4096 <= LP <= LLIM) /\ (LLIM < 2^47) /\
  (apart LP (LLIM - LP) B0 (B1 - B0) \/ (B0 <= LP /\ LLIM <= B1)) /\
  (4096 <= SQP /\ SQP + 24 < 2^47) /\ (4096 <= LPP /\ LPP + 8 < 2^47) /\
  (apart SQP 24 B0 (B1 - B0)) /\ (apart LPP 8 B0 (B1 - B0)) /\ (apart SQP 24 LPP 8) /\ (apart LP (LLIM - LP) LPP 8) /\
  (lo <= SPV - 2480) /\ (4096 <= SPV < 2^47) /\
  (B0 + (B1 - B0) <= lo \/ SPV <= B0) /\ (SQP + 24 <= lo \/ SPV <= SQP) /\ (LPP + 8 <= lo \/ SPV <= LPP) /\ (LP + (LLIM - LP) <= lo \/ SPV <= LP) /\
  (KHIGH <= lo) /\ (0x10007fff8000 <= SPV - 2480) /\ (rng RNG lo (SPV - lo)) /\ (rng_aimg RNG) /\
  (sclr SQP 24) /\ (sclr LPP 8) /\ (AIMG_HI <= LPP) /\ (SQP mod 8 = 0) /\ (LPP mod 8 = 0) /\
  (rw_cells bsegs m SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)]) /\
  (rw_cells bsegs m LPP [C8 (Z_to_bv 64 LP)]) /\
  (ablk B0 B1) /\ (unpoisoned m B0 B1) /\ (rng RNG B0 (B1 - B0)) /\ (rng RNG (shad B0) (shspan B0 (B1 - B0))) /\ (ahull RNG m B0 (B1 - B0)) /\
  (areg RNG m LP (LLIM - LP)) /\ (ahull RNG m LP (LLIM - LP)) /\ (rdbl bsegs m LP LLIM) /\
  (aro RNG m SQP 24) /\ (aro RNG m LPP 8) /\ (art m) /\ (aro_client RNG m) /\ DEND = DEND.
Ltac es_open CTX := pose proof CTX as es_ctx_copy;
  destruct es_ctx_copy as (B0L & B1H & PFXR & OPE & B01 & OW0 & OWH & LLR & MLR & OFSR & LPR & LLIMH & LITB & SQPR & LPPR & ASQB & ALPB & ASQLP & ALITLP & LOS & SPV47 &
                           OFFB & OFFSQ & OFFLPP & OFFLIT & KLO & SPHI & RSTK & RI & SCSQ & SCLP & AHL & SQ8 & LP8 & SQ0 & LPC0 &
                           ABB & UB0 & RB & RBS & HB & ARL & HL & RDL & ASQ & ALP & ART0 & AROC & _).

Section EXECSPLIT.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 : Z).
  Hypothesis CTX : es_ctx RNG m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1.
  Hypothesis SC2 : zd_safecopy2_stmtA.
  Hypothesis DBS : zd_dbs_stmtA.

  Notation POST := (zd_execend_postA 2480 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP OEND SQP LPP LP LLIM LL ML OFS B0 B1 lo m).
  (* [comment removed for export] *)
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition FIN (low : list cell) (m1 : amem) : Prop :=
    cells_size low = 24%nat /\
    rw_cells bsegs m1 (SPV + -128) (low ++ SAVED) /\ stk bsegs m1 lo (SPV + -128) /\
    munch [(OP, OEND); (LPP, LPP + 8); (SPV - 2480, SPV)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 B0 B1.
  Ltac open_fin FI := destruct FI as (LOW & FR & STK & MU & WM & MI & REG); cbn [app] in FR.
  Ltac fin_close :=
    lazymatch goal with |- FIN ?low ?m2 =>
      lazymatch goal with
      | FR2 : rw_cells _ m2 (SPV + -128) _, STK2 : stk _ m2 lo _, WM2 : wmono _ m m2, MI2 : mem_inv _ m2, REG2 : stk _ m2 B0 B1 |- _ =>
          refine (conj _ (conj FR2 (conj STK2 (conj _ (conj WM2 (conj MI2 REG2))))));
          [ reflexivity
          | first [ assumption
                  | match goal with MU2 : munch _ m m2 |- _ =>
                      eapply munch_weaken; [|exact MU2]; intros x Hx; unfold outside in *; cbn in Hx |- *; lia end ] ]
      end
    end.

  Lemma ab_app : B1 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= B0.
  Proof. es_open CTX. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold ablk, AIMG_HI, KLS in ABB. lia. Qed.

  Lemma fin_unp : forall low m1, FIN low m1 -> unpoisoned m1 B0 B1.
  Proof. es_open CTX.
    intros low m1 FI. open_fin FI. pose proof ab_app as BA.
    eapply unpoisoned_munch; [exact UB0 | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold sclr, KLS, ASHOFF, KHIGH in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_art : forall low m1, FIN low m1 -> art m1.
  Proof. es_open CTX.
    intros low m1 FI. open_fin FI. pose proof ab_app as BA.
    eapply art_transport; [exact ART0| exact MU| exact WM|].
    unfold ablk, AIMG_HI, KLS, KHIGH in *. repeat constructor; cbn [fst]; lia.
  Qed.
  Lemma fin_aroc : forall low m1, FIN low m1 -> aro_client RNG m1.
  Proof. es_open CTX.
    intros low m1 FI. open_fin FI. pose proof ab_app as BA.
    eapply aro_client_transport; [exact AROC| exact MU| exact WM|].
    unfold aappW, sclr, ablk, AIMG_HI, KLS, KLOW, KHIGH, ASHOFF in *.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_nil.
  Qed.
  Lemma fin_sq : forall low m1, FIN low m1 -> rw_cells bsegs m1 SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)].
  Proof. es_open CTX. intros low m1 FI. open_fin FI. eapply rw_cells_transport; [exact SQ0| exact MU| exact WM|]. unfold apart in *. cbn. lia. Qed.
  Lemma fin_asq : forall low m1, FIN low m1 -> aro RNG m1 SQP 24.
  Proof. es_open CTX.
    intros low m1 FI. open_fin FI. pose proof ab_app as BA. destruct ASQ as (U & Q1 & Q2). split; [| split; [exact Q1| exact Q2]].
    eapply unpoisoned_munch; [exact U| exact MU|]. unfold apart in *. cbn [disjoint_from]. rewrite !shad_div. unfold sclr, KLS, ASHOFF, KHIGH in *.
    repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_alp : forall low m1, FIN low m1 -> aro RNG m1 LPP 8.
  Proof. es_open CTX.
    intros low m1 FI. open_fin FI. pose proof ab_app as BA. destruct ALP as (U & Q1 & Q2). split; [| split; [exact Q1| exact Q2]].
    eapply unpoisoned_munch; [exact U| exact MU|]. unfold apart in *. cbn [disjoint_from]. rewrite !shad_div. unfold sclr, KLS, ASHOFF, KHIGH in *.
    repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_rdl : forall low m1, FIN low m1 -> rdbl bsegs m1 LP LLIM.
  Proof. es_open CTX.
    intros low m1 FI. open_fin FI. destruct LITB as [AP|[IN1 IN2]].
    - eapply rdbl_transport; [exact RDL| exact MU|]. intros x Hx. left. unfold apart in *. cbn. lia.
    - eapply rdbl_sub; [apply rdbl_of_stk; exact REG| lia| lia].
  Qed.
  Lemma fin_areg : forall low m1, FIN low m1 -> areg RNG m1 B0 (B1 - B0).
  Proof. es_open CTX.
    intros low m1 FI _. split; [|split; [|split]]; [ replace (B0 + (B1 - B0)) with B1 by lia; exact ABB
      | replace (B0 + (B1 - B0)) with B1 by lia; exact (fin_unp _ _ FI) | exact RB | exact RBS ].
  Qed.
  (* [comment removed for export] *)
  Lemma fin_aregL : forall low m1, FIN low m1 -> areg RNG m1 LP (LLIM - LP).
  Proof. es_open CTX.
    intros low m1 FI Hn. destruct (ARL Hn) as (ABL & UL0 & RL & RLS). split; [|split; [|split]]; [ exact ABL | | exact RL | exact RLS ].
    open_fin FI. pose proof ab_app as BA.
    assert (BL : LP + (LLIM - LP) + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= LP)
      by (pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR; unfold ablk, AIMG_HI, KLS in ABL; lia).
    pose proof ALITLP as ALITLP'. unfold apart in ALITLP'.
    eapply unpoisoned_munch; [exact UL0 | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold sclr, KLS, ASHOFF, KHIGH in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_ahull : forall low m1 A n, FIN low m1 -> B0 <= A -> 0 <= n -> A + n <= B1 -> ahull RNG m1 A n.
  Proof. es_open CTX.
    intros low m1 A n FI H1 H2 H3. open_fin FI. destruct HB as (RLO & RHI & C1 & C2 & C3 & C4 & C5 & C6 & W & R).
    exists RLO, RHI. split; [lia|]. split; [lia|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|].
    split; [eapply wr_at_transport; [exact W| exact WM] | exact R].
  Qed.
  Lemma fin_ahullL : forall low m1, FIN low m1 -> ahull RNG m1 LP (LLIM - LP).
  Proof. es_open CTX.
    intros low m1 FI. open_fin FI. destruct HL as (RLO & RHI & C1 & C2 & C3 & C4 & C5 & C6 & W & R).
    exists RLO, RHI. split; [lia|]. split; [lia|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|].
    split; [eapply wr_at_transport; [exact W| exact WM] | exact R].
  Qed.
  Lemma fin_astk : astk RNG lo (SPV + -128).
  Proof. es_open CTX. split; [exact KLO|]. split; [eapply rng_sub; [exact RSTK| lia| lia] | exact RI]. Qed.
  Lemma fin_stk : forall low m1, FIN low m1 -> stk bsegs m1 lo (SPV + -128).  Proof. es_open CTX. intros low m1 FI; open_fin FI; exact STK. Qed.
  Lemma fin_mi : forall low m1, FIN low m1 -> mem_inv bsegs m1.  Proof. es_open CTX. intros low m1 FI; open_fin FI; exact MI. Qed.
  Lemma fin_reg : forall low m1, FIN low m1 -> stk bsegs m1 B0 B1.  Proof. es_open CTX. intros low m1 FI; open_fin FI; exact REG. Qed.
  (* [comment removed for export] *)
  Lemma fin_after_sc : forall low m1 m2 D HI K, FIN low m1 -> OP <= D -> HI <= OEND -> 0 <= K <= 2352 ->
    munch [(D, HI); (SPV + -128 - K, SPV + -128)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
    stk bsegs m2 lo (SPV + -128) -> stk bsegs m2 B0 B1 -> FIN low m2.
  Proof. es_open CTX.
    intros low m1 m2 D HI K FI HD HHI HK MUc WMc MI2 STK2 SD2. pose proof FI as FI0. open_fin FI.
    split; [exact LOW|]. split; [| split; [exact STK2| split; [| split; [| split; [exact MI2| exact SD2]]]]].
    - destruct FI0 as [_ [FR0 _]]. eapply rw_cells_transport; [exact FR0| exact MUc| exact WMc|].
      rewrite cells_size_app, LOW. cbn. lia.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. intros x. cbn. lia.
    - eapply wmono_trans; [exact WM| exact WMc].
  Qed.
  Lemma fin_lpp : forall m1 m2 D HI K v, OP <= D -> HI <= OEND -> 0 <= K <= 2352 -> rw_cells bsegs m1 LPP [C8 v] ->
    munch [(D, HI); (SPV + -128 - K, SPV + -128)] m1 m2 -> wmono bsegs m1 m2 -> rw_cells bsegs m2 LPP [C8 v].
  Proof. es_open CTX. intros m1 m2 D HI K v HD HHI HK H MUc WMc. eapply rw_cells_transport; [exact H| exact MUc| exact WMc|]. unfold apart in *. cbn. lia. Qed.
  Lemma fin_sq2 : forall m1 m2 D HI K, OP <= D -> HI <= OEND -> 0 <= K <= 2352 -> rw_cells bsegs m1 SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)] ->
    munch [(D, HI); (SPV + -128 - K, SPV + -128)] m1 m2 -> wmono bsegs m1 m2 ->
    rw_cells bsegs m2 SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)].
  Proof. es_open CTX. intros m1 m2 D HI K HD HHI HK H MUc WMc. eapply rw_cells_transport; [exact H| exact MUc| exact WMc|]. unfold apart in *. cbn. lia. Qed.

  (* [comment removed for export] *)
  Lemma es_ret : forall low m1 (R lp' : Z) xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    FIN low m1 -> rw_cells bsegs m1 LPP [C8 (Z_to_bv 64 lp')] ->
    0 <= R < 2^64 -> (zd_is_error R = true \/ (R = LL + ML /\ OP + R <= OEND /\ lp' = LP + LL /\ LP + LL <= LLIM)) ->
    evtF bsegs RNG POST (ST 0x97710 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 R) xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof. es_open CTX.
    intros until x31. intros FI LPC RR HR. pose proof (fin_sq _ _ FI) as SQ. open_fin FI.
    pose proof (rw_cells_merge bsegs m1 (SPV + -128) [] low SAVED FR) as FRM. cbn [app] in FRM. rewrite LOW in FRM. clear FR.
    kx_autoFLAx [KAApp (SPV - 128) 128] [] 30%nat [KZRange SPV 4096 (2^47); KZWr (SPV - 128) 128] [(SPV - 128, 128)] [(SPV - 128, 128)].
    all: try kx_z. all: try kx_acc RSTK.
    all: kx_mem. all: zstep.
    all: lazymatch goal with FRc : rw_cells _ ?mc (SPV + -128) _, STc : stk _ ?mc lo (SPV + -128) |- _ => release_frame FRc STc SPV end.
    all: apply evtF_done; unfold zd_execend_postA; do 14 eexists; exists m1, R, lp'.
    all: split; [reflexivity|]. all: split; [exact MU|]. all: split; [exact WM|]. all: split; [exact MI|]. all: split; [eassumption|].
    all: split; [exact REG|]. all: split; [exact SQ|]. all: split; [exact LPC|]. all: split; [exact RR| exact HR].
  Qed.

  (* [comment removed for export] *)
  Notation LOWS := [C8 (Z_to_bv 64 DEND); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 OENDW)].
  Notation SHP x := (Z_to_bv 64 (0x7fff8000 + x / 8)).

  (* [comment removed for export] *)
  Lemma es_after : forall SL IL m1 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31,
    FIN LOWS m1 -> rw_cells bsegs m1 LPP [C8 (Z_to_bv 64 LP)] -> OP + LL + ML <= OEND -> LP + LL <= LLIM -> SL = LL + ML -> IL = LP + LL ->
    evtF bsegs RNG POST (ST 0x97664 m1 xra x5 x6 x7 (Z_to_bv 64 (SQP + 8)) (Z_to_bv 64 (SQP + 16)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                             (Z_to_bv 64 LL) (Z_to_bv 64 LPP) (SHP (SQP + 8)) (Z_to_bv 64 SL) (Z_to_bv 64 IL) (Z_to_bv 64 OP)
                             (SHP LPP) (SHP (SQP + 16)) (Z_to_bv 64 OFS) (Z_to_bv 64 PFX) x28 x29 x30 x31).
  Proof. es_open CTX.
    intros until x31. intros FI LPC1 HLE HLPL -> ->.
    pose proof (fin_sq _ _ FI) as SQ1.
    pose proof (fin_asq _ _ FI) as (USQ & RSQ & RSQS). pose proof (fin_alp _ _ FI) as (ULP & RLP & RLPS).
    pose proof ab_app as BA. pose proof SCLP as SCLP'. unfold sclr, KLS in SCLP'. pose proof ASQLP as ASQLP'. unfold apart in ASQLP'.
    pose proof FI as FI0. open_fin FI.
    kx_autoFLAx [KAApp (SPV - 128) 128; KAApp LPP 8; KAUnp SQP 24; KAUnp LPP 8;
               KAShp (0x7fff8000 + LPP / 8) LPP; KAShp (0x7fff8000 + (SQP + 16) / 8) (SQP + 16); KAShp (0x7fff8000 + (SQP + 8) / 8) (SQP + 8)]
           [0x97710; 0x96b74; 0x976a8] 40%nat
           [KZRange SPV 0x10007fff8000 (2^47); KZRange SQP 4096 (2^47 - 24); KZRange LPP 4096 (2^47 - 8); KZRange LP 4096 (2^47);
            KZRange LL 0 (2^32); KZRange ML 0 (2^32); KZRange OFS 0 (2^64 - 1); KZRange OP 4096 (2^47); KZRange OEND 4096 (2^47); KZRange OENDW 0 (2^47);
            KZRange PFX 4096 (2^47); KZRange (OP + LL) 4096 (2^47); KZRange (OP + LL - PFX) 0 (2^47); KZRange (LP + LL) 4096 (2^47);
            KZAlign SQP 8; KZAlign LPP 8; KZWr LPP 8; KZDisj LPP 8 SQP 24; KZDisj LPP 8 (SPV - 128) 128]
           [(SQP, 24); (LPP, 8); (SPV - 128, 128)] [(SQP, 24); (LPP, 8); (SPV - 128, 128)].
    all: try kx_z. all: try kx_acc RSTK.
    all: try lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 620200) _ _ _ _) => exfalso; kx_lia end.   (* [comment removed for export] *)
    all: kx_mem.
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 620304) _ _ ?m2 _) =>
          assert (FI2 : FIN LOWS m2) by fin_close;
          eapply (es_ret _ m2 18446744073709551596 (LP + LL));
          [ exact FI2
          | first [ assumption | match goal with H : rw_cells _ m2 LPP [C8 (Z_to_bv 64 ?v)] |- _ => replace (LP + LL) with v by lia; exact H end ]
          | lia | left; reflexivity ]
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 617332) _ _ ?m2 _) =>
          assert (FI2 : FIN LOWS m2) by fin_close;
          pose proof SC2 as SC; unfold zd_safecopy2_stmtA, APZD_SAFECOPY in SC;
          eapply evtF_cut;
          [ eapply SC with (SPV := SPV + -128) (lo := lo) (OP := OP + LL) (OENDW := OENDW) (IP := OP + LL - OFS)
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
    lazymatch goal with FI2 : FIN LOWS ?m2, SQ2 : rw_cells _ ?m2 SQP _, LP2 : rw_cells _ ?m2 LPP _ |- _ =>
      lazymatch type of MUc with munch [(?D, ?HI); _] _ _ =>
      pose proof (fin_after_sc _ m2 m3 D HI 2320 FI2 ltac:(lia) ltac:(lia) ltac:(lia) MUc WMc MI3 STK3 SD3) as FI3;
      pose proof (fin_sq2 m2 m3 D HI 2320 ltac:(lia) ltac:(lia) ltac:(lia) SQ2 MUc WMc) as SQ3;
      pose proof (fin_lpp m2 m3 D HI 2320 _ ltac:(lia) ltac:(lia) ltac:(lia) LP2 MUc WMc) as LP3
    end end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    zstep.
    eapply (es_ret _ m3 (LL + ML) (LP + LL)); [ exact FI3 | first [ exact LP3 | match type of LP3 with rw_cells _ _ LPP [C8 (Z_to_bv 64 ?v)] =>
                                                                            replace (LP + LL) with v by lia; exact LP3 end ] | lia | right; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma es_entry : forall t0 t1 t2 t4 t5 t6,
    stk bsegs m lo SPV -> stk bsegs m B0 B1 -> mem_inv bsegs m ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OP) (Z_to_bv 64 OEND) (Z_to_bv 64 OENDW) (Z_to_bv 64 SQP) (Z_to_bv 64 LPP)
                                 (Z_to_bv 64 LLIM) (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 DEND) t4 t5 t6)
                            F (Z_to_bv 64 APZD_EXECEND_SPLIT) fc None m (seg_rom bsegs)).
  Proof. es_open CTX.
    intros t0 t1 t2 t4 t5 t6 ST0 REG0 MI0.
    pose proof ART0 as (GOT & RIC & SHB & INI & LAY & REAL). pose proof ab_app as BA.
    assert (MU : munch [(OP, OEND); (LPP, LPP + 8); (SPV - 2480, SPV)] m m) by apply munch_refl. assert (WM : wmono bsegs m m) by apply wmono_refl.
    pose proof UB0 as UB1. pose proof SQ0 as SQ1. pose proof LPC0 as LPC1.
    pose proof ASQ as ASQ1. pose proof ALP as ALP1. destruct ASQ1 as (USQ & RSQ & RSQS). destruct ALP1 as (ULP & RLP & RLPS).
    carve_frame 128%nat ST0.
    unfold APZD_EXECEND_SPLIT.
    kx_autoFLAx [KAApp (SPV - 128) 128; KAUnp SQP 24; KAUnp LPP 8] [0x97710; 0x96540] 80%nat
      [KZRange SPV 0x10007fff8000 (2^47); KZRange OP 4096 (2^47); KZRange OEND 0 (2^47); KZRange OENDW 0 (2^47); KZRange SQP 4096 (2^47 - 24);
       KZRange LPP 4096 (2^47 - 8); KZRange LLIM 0 (2^47); KZRange LP 4096 (2^47); KZRange PFX 0 (2^47);
       KZRange LL 0 (2^32); KZRange ML 0 (2^32); KZRange OFS 0 (2^64 - 1);
       KZAlign SQP 8; KZAlign LPP 8; KZWr (SPV - 128) 128; KZDisj (SPV - 128) 128 SQP 24; KZDisj (SPV - 128) 128 LPP 8]
      [(SPV - 128, 128); (SQP, 24); (LPP, 8)] [(SPV - 128, 128); (SQP, 24); (LPP, 8)].
    all: try kx_cell_lit. all: try kx_acc RI.
    all: try lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 620376) _ _ _ _) => kx_trap_fast end.   (* [comment removed for export] *)
    all: kx_mem.
    all: try replace (Z_to_bv 64 ((SQP + 16) mod 2 ^ 64 / 8 + 2147450880)) with (Z_to_bv 64 (0x7fff8000 + (SQP + 16) / 8)) by (f_equal; rewrite Z.mod_small by lia; lia).
    all: try replace (Z_to_bv 64 ((SQP + 8) mod 2 ^ 64 / 8 + 2147450880)) with (Z_to_bv 64 (0x7fff8000 + (SQP + 8) / 8)) by (f_equal; rewrite Z.mod_small by lia; lia).
    all: try replace (Z_to_bv 64 (LPP mod 2 ^ 64 / 8 + 2147450880)) with (Z_to_bv 64 (0x7fff8000 + LPP / 8)) by (f_equal; rewrite Z.mod_small by lia; lia).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 620304) _ _ ?m2 _) =>
          lazymatch goal with FRc : rw_cells _ m2 (SPV + -128) (CB 24 ?j :: _) |- _ =>
            assert (FI2 : FIN [CB 24 j] m2) by fin_close end;
          eapply (es_ret _ m2 _ LP); [ exact FI2 | assumption | lia | left; reflexivity ]
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 615744) _ _ ?m2 _) =>
          assert (FI2 : FIN LOWS m2) by fin_close;
          pose proof DBS as SC; unfold zd_dbs_stmtA, APZD_DBS in SC;
          eapply evtF_cut;
          [ eapply SC with (SPV := SPV + -128) (lo := lo) (OP := OP) (IP := LP) (LEN := LL) (B0 := B0) (B1 := B1) (R0 := LP) (R1 := LLIM);
            [ exact (fin_reg _ _ FI2) | lia | lia | lia | lia | lia
            | exact (fin_rdl _ _ FI2) | lia | lia | lia | lia | exact LITB
            | exact (fin_stk _ _ FI2) | lia | lia | unfold off_stack; lia | unfold off_stack; lia
            | lia
            | exact (fin_areg _ _ FI2) | eapply (fin_ahull _ _ B0 (B1 - B0) FI2); lia
            | exact (fin_aregL _ _ FI2) | exact (fin_ahullL _ _ FI2)
            | exact (fin_art _ _ FI2) | exact fin_astk | exact (fin_mi _ _ FI2)
            | f_equal; lia | f_equal; lia | f_equal; lia ]
          | clear SC; intros ms' PO;
            destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MUc & WMc & MI3 & STK3 & SD3 & RD3);
            lazymatch goal with LP2 : rw_cells _ m2 LPP _ |- _ =>
              lazymatch type of MUc with munch [(?D, ?HI); _] _ _ =>
              pose proof (fin_after_sc _ m2 m3 D HI 2304 FI2 ltac:(lia) ltac:(lia) ltac:(lia) MUc WMc MI3 STK3 SD3) as FI3;
              pose proof (fin_lpp m2 m3 D HI 2304 _ ltac:(lia) ltac:(lia) ltac:(lia) LP2 MUc WMc) as LP3 end end;
            lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
              replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end;
            eapply (es_after _ _ m3); [ exact FI3 | exact LP3 | lia | lia | lia | lia ] ]
      end.
  Qed.
End EXECSPLIT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem zd_execend_split_proofA : zd_safecopy2_stmtA -> zd_dbs_stmtA -> zd_execend_split_stmtA.
Proof.
  intros SC2 DBS RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1.
  intros REG B0L B1H PFXR OPE OW0 OWH SQC LPC LLR MLR OFSR LPR LLIMH RDL LITB SQPL SQPH LPPL LPPH ASQB ALPB ASQLP ALITLP STK LOS SPR OFFB OFFSQ OFFLPP OFFLIT
         B01 SCSQ SCLP LPPI SQ8 LP8 ARB HB ARL HL ASQ ALP ART AST AROC MI -> -> -> -> -> -> -> -> ->.
  unfold off_stack in *.
  pose proof AST as (KLO & RSTK & RI). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  destruct (ARB ltac:(lia)) as (ABB & UB0 & RB & RBS). replace (B0 + (B1 - B0)) with B1 in ABB, UB0 by lia.
  assert (CTX : es_ctx RNG m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1).
  { unfold es_ctx. repeat (lazymatch goal with |- _ /\ _ => split end); first [assumption | reflexivity | lia]. }
  unfold APZD_EXECEND_SPLIT.
  apply (es_entry RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 CTX SC2 DBS);
    [ exact STK | exact REG | exact MI ].
Qed.
End CANSEC1.
