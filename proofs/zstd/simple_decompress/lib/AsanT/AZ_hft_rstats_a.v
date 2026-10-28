(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require FseNCountRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree StrFun WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_fkit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_hft_rs_iface AZ_libc_iface AZ_kx AZ_hft_rs_defs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
Ltac b2z_norm G :=
  repeat match type of G with
         | context [Z.ltb ?a ?b] =>
             first [ replace (Z.ltb a b) with true in G by (symmetry; apply Z.ltb_lt; lia)
                   | replace (Z.ltb a b) with false in G by (symmetry; apply Z.ltb_ge; lia) ]
         | context [Z.eqb ?a ?b] =>
             first [ replace (Z.eqb a b) with true in G by (symmetry; apply Z.eqb_eq; lia)
                   | replace (Z.eqb a b) with false in G by (symmetry; apply Z.eqb_neq; lia) ]
         end; cbn [Z.b2z] in G.
Ltac lxor_bits G := repeat first [ progress change (Z.lxor 1 0) with 1 in G | progress change (Z.lxor 0 1) with 1 in G
                                 | progress change (Z.lxor 0 0) with 0 in G | progress change (Z.lxor 1 1) with 0 in G ].
Ltac ug_dead G := exfalso; rewrite ?Z.shiftl_mul_pow2 in G by lia; first [ lia | b2z_norm G; lxor_bits G; first [ congruence | lia | apply G; reflexivity ] ].
Ltac ugF TRAP :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if _ then ?a else ?b) _ _ _ _) =>
      let G := fresh "G" in
      lazymatch a with
      | Z_to_bv 64 TRAP => if_cases G; zify_cond G; [ ug_dead G | clear G ]
      | _ => lazymatch b with Z_to_bv 64 TRAP => if_cases G; zify_cond G; [ clear G | ug_dead G ] end
      end
  end.
Ltac zgF TRAP := zstep; try ugF TRAP.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_hide segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_hide segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_hide segs m m' MU WM.

(* [comment removed for export] *)
Ltac u32st RK s x v :=
  lazymatch type of RK with u32arr ?segs ?mx ?Wb (map (Z_to_bv 64) ?l) =>
    let SOK := fresh "SOK" in
    pose proof (u32arr_store_ok segs mx Wb _ s (wa (Wb + 4 * s)) RK ltac:(rewrite length_map; lia) eq_refl) as SOK;
    zstep;
    let S2 := fresh "RK" in
    pose proof (u32arr_write segs mx Wb _ s (Z_to_bv 64 x) RK ltac:(rewrite length_map; lia)) as S2;
    clear RK; store_done;
    apply (u32arr_upd_Z segs _ Wb l (Z.to_nat s) x v) in S2; [| first [ reflexivity | rewrite Z.mod_mod by lia; reflexivity ]];
    rename S2 into RK
  end.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma outside_In : forall W a x y, outside W a -> In (x, y) W -> ~ (x <= a < y).
Proof.
  induction W as [|[u v] W IH]; intros a x y HO HI; [destruct HI|].
  destruct HO as [H1 H2]. destruct HI as [E|HI]; [injection E as -> ->; exact H1| exact (IH a x y H2 HI)].
Qed.

Lemma ainblk_sub : forall LB A n A' n', ainblk LB A n -> A <= A' -> A' + n' <= A + n -> ainblk LB A' n'.
Proof. intros LB A n A' n' (b & Hb & H1 & H2) Ha Hn. exists b. split; [exact Hb| lia]. Qed.

Lemma art_of_aheap : forall AI L RNG st LB m, AHEAP AI L RNG st LB m -> art m.
Proof.
  intros AI L RNG st LB m AH. pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
  destruct RTC as (_ & GOT & RIC & REAL & SHB & _ & INI & LAY & _). unfold art. repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Lemma ffr_pres_appw : forall AI L RNG st LB (m m5 : amem) (W Wr Wa : list (Z * Z)),
  AHEAP AI L RNG st LB m -> ablkLB LB ->
  Forall (fun iv => fst iv <= snd iv /\ ATOP <= fst iv /\ snd iv <= 2^47) Wa ->
  Forall (fun iv => (exists A Bq, ablk A Bq /\ A <= fst iv /\ snd iv <= Bq) /\ fst iv <= snd iv /\ In iv W) Wr ->
  munch (Wr ++ Wa) m m5 -> wmono bsegs m m5 -> ffr_pres W LB m m5.
Proof.
  intros AI L RNG st LB m m5 W Wr Wa AH LBH HWa HWr MU WM.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold ffr_pres. eapply magree_mono; [eapply magree_of_munch; [exact MU | exact WM] |].
  intros a [((cls & FA & fn & Hin & Ha) & OUT)|(a' & (cls & FA & fn & Hin & Ha') & ->)].
  - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hin) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
    rewrite fk_outside_app. split.
    + clear MU. induction HWr as [|[x y] Wr [_ [Hle HI]] HWr IH]; cbn [outside]; [exact I|]. split; [| exact IH].
      exact (outside_In W a x y OUT HI).
    + clear MU. induction HWa as [|[x y] Wa (Hle & Hx & Hy) HWa IH]; cbn [outside]; [exact I|]. split; [| exact IH].
      cbn [fst snd] in Hle, Hx, Hy. clear - Ha B3 Hx ATR. lia.
  - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hin) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
    pose proof (LBH _ Hin) as A3. cbn [ab_addr ab_size] in A3. pose proof (fk_ablk_lits _ _ A3) as A4.
    rewrite fk_outside_app. split.
    + clear MU. induction HWr as [|[x y] Wr [(A & Bq & AB & HA & HB) [Hle _]] HWr IH]; cbn [outside]; [exact I|]. split; [| exact IH].
      cbn [fst snd] in HA, HB, Hle. pose proof (fk_ablk_lits _ _ AB) as ABL. pose proof (ablk_disj_band _ _ AB) as ABD.
      rewrite shad_div. unfold ASHOFF, AIMG_HI, KLS in *. clear - Ha' A4 ABL ABD HA HB Hle ATR B3. Z.div_mod_to_equations. lia.
    + clear MU. induction HWa as [|[x y] Wa (Hle & Hx & Hy) HWa IH]; cbn [outside]; [exact I|]. split; [| exact IH].
      cbn [fst snd] in Hle, Hx, Hy. rewrite shad_div. unfold ASHOFF, AIMG_HI in *. clear - Ha' A4 Hx Hy Hle ATR B3. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma ffr_pres_monoW : forall W W' LB (m m' : amem), ffr_pres W LB m m' -> (forall iv, In iv W -> In iv W') -> ffr_pres W' LB m m'.
Proof.
  intros W W' LB m m' H HI a Ha HP. apply (H a Ha). destruct HP as [[HF HO]|HS]; [left; split; [exact HF|]| right; exact HS].
  clear - HO HI. induction W as [|[x y] W IH]; cbn [outside]; [exact I|]. split; [| apply IH; intros iv Hiv; apply HI; right; exact Hiv].
  exact (outside_In W' a x y HO (HI _ (or_introl eq_refl))).
Qed.

(* [comment removed for export] *)
Lemma ffr_unp_pres : forall AI L RNG st LB W (m m' : amem) X k,
  AHEAP AI L RNG st LB m' -> ffr_pres W LB m m' -> ainblk LB X k -> 0 <= k -> unpoisoned m X (X + k) -> unpoisoned m' X (X + k).
Proof.
  intros AI L RNG st LB W m m' X k AH FP (b & Hb & H1 & H2) Hk U.
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hb) as (N & (BR & B2 & B3 & B4) & RA & RS & SHB & _).
    assert (A8 : A mod 8 = 0) by (clear - B4; Z.div_mod_to_equations; lia).
    pose proof (ablk_lin _ _ BR) as (X1 & X2 & X3 & X4).
    assert (UA : unpoisoned m' A (A + n)) by (apply ablock_unpoisoned; [exact SHB| exact A8| lia| lia| lia]).
    eapply unpoisoned_sub; [exact UA| lia| lia].
  - destruct (Z.eq_dec k 0) as [->|Kp].
    { destruct U as (U0 & U1 & _). split; [lia|]. split; [lia|]. intros G HG. lia. }
    eapply unpoisoned_agree; [exact U|]. intros s Hs. rewrite !shad_div in Hs.
    set (a' := Z.max X (8 * (s - ASHOFF))).
    assert (Ra : X <= a' < X + k).
    { subst a'. unfold ASHOFF in *. destruct (Z.max_spec X (8 * (s - 2147450880))) as [[Hm ->]|[Hm ->]]; Z.div_mod_to_equations; lia. }
    assert (Ea : shad a' = s).
    { subst a'. rewrite shad_div. unfold ASHOFF in *. destruct (Z.max_spec X (8 * (s - 2147450880))) as [[Hm ->]|[Hm ->]]; Z.div_mod_to_equations; lia. }
    rewrite <- Ea. destruct U as (U0 & U1 & _).
    destruct (FP (shad a') ltac:(rewrite shad_div; unfold ASHOFF; clear - Ra U0 U1; Z.div_mod_to_equations; lia)
                 ltac:(right; exists a'; split; [exists c, A, n; split; [exact Hb| lia]| reflexivity])) as [E _].
    exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RS.
  Variables (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem).
  Variables (SPV lo HW RS NBP TLP SRC n WK wksz B bsz : Z).
  Hypothesis HY : rsA_hyps RNG SPV lo HW RS NBP TLP SRC n WK wksz B bsz.
  Hypothesis LBH : ablkLB LB.
  Hypothesis INB : ainblk LB B bsz.
  Hypothesis INNB : ainblk LB NBP 4.
  Hypothesis INTL : ainblk LB TLP 4.
  Notation POST := (huf_rstats_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV HW RS NBP TLP n WK wksz lo m).
  Notation MUNCH := ([(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (WK, WK + wksz); (SPV - 5056, SPV)] ++ fake_area L).
  Notation WL := [(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (WK, WK + wksz)].
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation FRAME := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Lemma rs_cellbands : (NBP + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= NBP) /\ (TLP + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= TLP)
                       /\ 0x625000 <= NBP /\ 0x625000 <= TLP /\ NBP + 4 + 8 <= 2^47 /\ TLP + 4 + 8 <= 2^47.
  Proof.
    destruct (fk_inblk_ablk LB NBP 4 LBH INNB ltac:(lia)) as (A1 & N1 & AB1 & L1 & H1).
    destruct (fk_inblk_ablk LB TLP 4 LBH INTL ltac:(lia)) as (A2 & N2 & AB2 & L2 & H2).
    pose proof (ablk_lin _ _ AB1) as (X1 & _ & _ & X4). pose proof (ablk_disj_band _ _ AB1) as D1.
    pose proof (ablk_lin _ _ AB2) as (Y1 & _ & _ & Y4). pose proof (ablk_disj_band _ _ AB2) as D2.
    unfold AIMG_HI, KLS in *. clear - L1 H1 L2 H2 X1 X4 D1 Y1 Y4 D2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rs_exit_gen : forall m1 r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    munch MUNCH m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (SPV + -64) -> rw_cells bsegs m1 (SPV + -64) FRAME ->
    ffr_pres WL LB m m1 -> AHEAP AI L RNG st LB m1 -> stk bsegs m1 WK (WK + wksz) -> 0 <= r < 2^64 ->
    ((zd_is_error r = false /\ 1 <= r <= n /\ exists hw rank tl nbs,
           u8arr bsegs m1 HW (map (Z_to_bv 8) hw) /\ zlen hw = 256 /\ Forall (fun v => 0 <= v < 256) hw /\
           u32arr bsegs m1 RS (map (Z_to_bv 64) rank) /\
           rw_cells bsegs m1 NBP [C4 (Z_to_bv 64 nbs)] /\ rw_cells bsegs m1 TLP [C4 (Z_to_bv 64 tl)] /\
           huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl /\ 2 <= nbs <= 256)
     \/ (zd_is_error r = true /\ stk bsegs m1 HW (HW + 256) /\ stk bsegs m1 RS (RS + 52) /\ stk bsegs m1 NBP (NBP + 4) /\ stk bsegs m1 TLP (TLP + 4))) ->
    evtF bsegs RNG POST (STF 0xab6b0 m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31; intros MU WM MI STK FR FFR AH WKS RR RES. open_hy HY. hide_all_disj.
    do 8 zstep. zstep.
    apply stk_of_rw_cells in FR. cbn [cells_size csize Nat.add] in FR.
    assert (STK' : stk bsegs m1 lo SPV).
    { apply (stk_merge bsegs m1 lo (SPV + -64) SPV STK); [|lia]. replace SPV with (SPV + -64 + Z.of_nat 64) at 2 by lia. exact FR. }
    zstep. apply evtF_done. unfold huf_rstats_postA.
    do 14 eexists. exists m1, r.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK'|].
    split; [exact FFR|]. split; [exact AH|]. split; [exact WKS|]. split; [exact RR| exact RES].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable mj : amem.
  Hypothesis UBj : unpoisoned mj B (B + bsz).
  Hypothesis UNBj : unpoisoned mj NBP (NBP + 4).
  Hypothesis UTLj : unpoisoned mj TLP (TLP + 4).
  Hypothesis ARTj : art mj.
  Hypothesis AHj : AHEAP AI L RNG st LB mj.
  Hypothesis MU0j : munch MUNCH m mj.
  Hypothesis WM0j : wmono bsegs m mj.
  Hypothesis FFR0j : ffr_pres WL LB m mj.
  Notation RSMj := (RSM ra s0 s1 s2 s3 s4 s5 s6 mj SPV lo HW RS NBP TLP WK wksz).
  Notation WJ := [(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (SPV - 2272, SPV)].

  (* [comment removed for export] *)
  Lemma rs_post_facts : forall m1, munch WJ mj m1 -> wmono bsegs mj m1 ->
    munch MUNCH m m1 /\ wmono bsegs m m1 /\ ffr_pres WL LB m m1 /\ AHEAP AI L RNG st LB m1.
  Proof.
    intros m1 MU WM. open_hy HY. clear RSTK RI RB RSB RNB RSNB RTL RSTL. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (ablk_lin _ _ ABB) as (Ba & Bb & Bc & Bd).
    split.
    { eapply munch_trans; [exact MU0j|]. eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside app fake_area] in *. clear - Hx. lia. }
    split; [eapply wmono_trans; [exact WM0j| exact WM]|].
    split.
    { eapply ffr_pres_trans; [exact FFR0j|].
      eapply (ffr_pres_appw AI L RNG st LB mj m1 WL [(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4)] [(SPV - 2272, SPV)]);
        [exact AHj| exact LBH| | | exact MU| exact WM].
      - constructor; [cbn [fst snd]; clear - LOS BOT SPR; lia| constructor].
      - destruct (fk_inblk_ablk LB NBP 4 LBH INNB ltac:(clear; lia)) as (A1 & N1 & AB1 & L1 & H1).
        destruct (fk_inblk_ablk LB TLP 4 LBH INTL ltac:(clear; lia)) as (A2 & N2 & AB2 & L2 & H2).
        constructor; [cbn [fst snd]; split; [exists B, (B + bsz); split; [exact ABB| clear - BRS RSHW HWB; lia]| split; [clear; lia| left; reflexivity]]|].
        constructor; [cbn [fst snd]; split; [exists B, (B + bsz); split; [exact ABB| clear - BRS RSHW HWB; lia]| split; [clear; lia| right; left; reflexivity]]|].
        constructor; [cbn [fst snd]; split; [exists A1, N1; split; [exact AB1| clear - L1 H1; lia]| split; [clear; lia| right; right; left; reflexivity]]|].
        constructor; [cbn [fst snd]; split; [exists A2, N2; split; [exact AB2| clear - L2 H2; lia]| split; [clear; lia| right; right; right; left; reflexivity]]| constructor]. }
    eapply (AI_frame AI); [exact AHj| exact MU| exact WM|].
    constructor; [cbn [fst snd]; replace (HW + 256 - HW) with 256 by (clear; lia); apply (fk_acr_inblk AI); eapply ainblk_sub; [exact INB| clear - BRS RSHW; lia| clear - HWB; lia]|].
    constructor; [cbn [fst snd]; replace (RS + 52 - RS) with 52 by (clear; lia); apply (fk_acr_inblk AI); eapply ainblk_sub; [exact INB| clear - BRS; lia| clear - RSHW HWB; lia]|].
    constructor; [cbn [fst snd]; replace (NBP + 4 - NBP) with 4 by (clear; lia); apply (fk_acr_inblk AI); exact INNB|].
    constructor; [cbn [fst snd]; replace (TLP + 4 - TLP) with 4 by (clear; lia); apply (fk_acr_inblk AI); exact INTL|].
    constructor; [cbn [fst snd]; apply (fk_acr_stack AI) with (lo := lo); clear - BOT LOS SPR; lia| constructor].
  Qed.

  (* [comment removed for export] *)
  Lemma rs_exit_arr : forall m1 hw rank wn wt r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    RSMj hw rank wn wt m1 -> 0 <= r < 2^64 -> zd_is_error r = true ->
    evtF bsegs RNG POST (STF 0xab6b0 m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RR RE. open_rsm I.
    destruct (rs_post_facts m1 MU WM) as (MU' & WM' & FFR' & AH').
    eapply (rs_exit_gen _ r); try eassumption.
    right. split; [exact RE|].
    split; [apply rw_cells_of_u8arr in HWC; apply stk_of_rw_cells in HWC; cbn [cells_size csize] in HWC; rewrite length_map in HWC;
            replace (HW + 256) with (HW + Z.of_nat (length hw + 0)) by lia; exact HWC|].
    split; [apply u8arr_of_u32arr in RK; apply rw_cells_of_u8arr in RK; apply stk_of_rw_cells in RK; cbn [cells_size csize] in RK;
            rewrite u32s_length, length_map in RK; replace (RS + 52) with (RS + Z.of_nat (4 * length rank + 0)) by lia; exact RK|].
    split; [apply stk_of_rw_cells in NBC; cbn [cells_size csize Nat.add] in NBC; exact NBC|].
    apply stk_of_rw_cells in TLC; cbn [cells_size csize Nat.add] in TLC; exact TLC.
  Qed.

  (* [comment removed for export] *)
  Lemma rs_exit_ok : forall m1 hw rank tl nbs r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    RSMj hw rank (Z_to_bv 64 nbs) (Z_to_bv 64 tl) m1 -> 1 <= r <= n -> huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 2 <= nbs <= 256 ->
    evtF bsegs RNG POST (STF 0xab6b0 m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RR OK NBS. open_rsm I. open_hy HY.
    destruct (rs_post_facts m1 MU WM) as (MU' & WM' & FFR' & AH').
    eapply (rs_exit_gen _ r); try eassumption; [clear - RR NR; lia|].
    left. split; [unfold zd_is_error, ZE_maxCode; apply Z.ltb_ge; clear - RR NR; lia|]. split; [exact RR|].
    exists hw, rank, tl, nbs. repeat (split; [eassumption|]). exact NBS.
  Qed.
  (* [comment removed for export] *)
  Notation KZB := [KZRange SPV (0x10007fff8000 + 5056) (2^47 - 16); KZRange HW 4096 (2^47 - 256); KZRange RS 4096 (2^47 - 52);
     KZRange NBP 4096 (2^47 - 12); KZRange TLP 4096 (2^47 - 12); KZRange B 4096 (2^47); KZRange (B + bsz) 4096 (2^47);
     KZAlign NBP 4; KZAlign TLP 4; KZAlign RS 4; KZAlign WK 4] (only parsing).
  (* [comment removed for export] *)
  Local Ltac rs_reunp :=
    repeat match goal with H : unpoisoned ?mx _ _ |- _ => lazymatch mx with mj => fail | _ => clear H end end;
    repeat match goal with H : art ?mx |- _ => lazymatch mx with mj => fail | _ => clear H end end;
    repeat match goal with H : rt_got _ |- _ => clear H | H : rt_got_ric _ |- _ => clear H | H : rt_shbase _ |- _ => clear H
                         | H : rt_inited _ |- _ => clear H | H : rt_layout _ |- _ => clear H | H : rt_real_mem _ |- _ => clear H end;
    lazymatch goal with
    | MU : munch _ mj ?m2, WM : wmono bsegs mj ?m2 |- _ =>
        pose proof (rs_unp_bM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UBj rs_cellbands m2 MU) as UB1;
        pose proof (rs_unp_nbM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UNBj rs_cellbands m2 MU) as UNB1;
        pose proof (rs_unp_tlM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UTLj rs_cellbands m2 MU) as UTL1;
        pose proof (rs_artM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY ARTj rs_cellbands m2 MU WM) as ART1;
        destruct ART1 as (GOT1 & RIC1 & SHB1 & INI1 & LAY1 & REAL1)
    end.
  (* [comment removed for export] *)
  Local Ltac kx_chk AKS STOP KX REGS :=
    kx_autoFLAc tt AKS [STOP] 24%nat (KZB ++ KX) (@nil (Z * Z)) (@nil (Z * Z));
    [ .. | kx_mem; kx_gen_regsF REGS; kx_tidy_run ]; try kx_z.

  (* [comment removed for export] *)
  Local Ltac rs_seps BNB BTL BSRC OFFB OFFNB OFFTL BRS RSHW RSWK HWB WKB LOS WKSZ0 :=
    assert (SHNB : HW + 256 <= NBP \/ NBP + 4 <= HW) by (clear - BNB BRS RSHW HWB; lia);
    assert (SRNB : RS + 52 <= NBP \/ NBP + 4 <= RS) by (clear - BNB BRS RSHW HWB; lia);
    assert (SHTL : HW + 256 <= TLP \/ TLP + 4 <= HW) by (clear - BTL BRS RSHW HWB; lia);
    assert (SRTL : RS + 52 <= TLP \/ TLP + 4 <= RS) by (clear - BTL BRS RSHW HWB; lia);
    assert (SHF : HW + 256 <= SPV + -64 \/ SPV <= HW) by (clear - OFFB BRS RSHW HWB LOS; lia);
    assert (SRF : RS + 52 <= SPV + -64 \/ SPV <= RS) by (clear - OFFB BRS RSHW HWB LOS; lia);
    assert (SHL : HW + 256 <= lo \/ SPV <= HW) by (clear - OFFB BRS RSHW HWB LOS; lia);
    assert (SRL : RS + 52 <= lo \/ SPV <= RS) by (clear - OFFB BRS RSHW HWB LOS; lia);
    assert (SWF : WK + wksz <= SPV + -64 \/ SPV <= WK) by (clear - OFFB BRS RSWK WKB LOS WKSZ0; lia);
    assert (SWL : WK + wksz <= lo \/ SPV <= WK) by (clear - OFFB BRS RSWK WKB LOS WKSZ0; lia);
    assert (SWNB : WK + wksz <= NBP \/ NBP + 4 <= WK) by (clear - BNB BRS RSWK WKB WKSZ0; lia);
    assert (SWTL : WK + wksz <= TLP \/ TLP + 4 <= WK) by (clear - BTL BRS RSWK WKB WKSZ0; lia);
    assert (SHS : HW + 256 <= SRC \/ SRC + n <= HW) by (clear - BSRC BRS RSHW HWB; lia);
    assert (SRS : RS + 52 <= SRC \/ SRC + n <= RS) by (clear - BSRC BRS RSHW HWB; lia);
    assert (SHR : HW + 256 <= RS \/ RS + 52 <= HW) by (clear - RSHW; lia);
    assert (SNBF : NBP + 4 <= SPV + -64 \/ SPV <= NBP) by (clear - OFFNB LOS; lia);
    assert (STLF : TLP + 4 <= SPV + -64 \/ SPV <= TLP) by (clear - OFFTL LOS; lia).

End RS.
End CANSEC1.
