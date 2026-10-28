(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_libc_iface AZ_seq_iface AZ_kx AZ_memmove AZ_copy_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
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
Definition sc_ctx (RNG : footprint) (m : amem) (SPV lo OP OENDW IP LEN OV WHI B0 B1 R0 R1 : Z) : Prop :=
  (4096 <= B0) /\ (B1 < 2^47) /\ (B0 <= OP) /\ (0 <= LEN) /\ (OP + LEN <= B1) /\ (B0 < B1) /\ (0 <= OENDW) /\ (OENDW + 32 <= B1) /\
  (WHI = Z.max (OP + LEN) (OENDW + 32)) /\
  (4096 <= R0) /\ (R1 < 2^47) /\ (R0 <= IP) /\
  ((OV = 1 /\ R0 = B0 /\ R1 = B1 /\ IP <= OP) \/ (OV = 0 /\ IP + LEN + 32 <= R1)) /\
  (apart R0 (R1 - R0) B0 (B1 - B0) \/ (B0 <= R0 /\ R1 <= B1)) /\
  (lo <= SPV - 2288) /\ (4096 <= SPV < 2^47) /\
  (B0 + (B1 - B0) <= lo \/ SPV <= B0) /\ (R0 + (R1 - R0) <= lo \/ SPV <= R0) /\
  (KHIGH <= lo) /\ (0x10007fff8000 <= SPV - 2288) /\ (rng RNG lo (SPV - lo)) /\ (rng_aimg RNG) /\
  (ablk B0 B1) /\ (unpoisoned m B0 B1) /\ (rng RNG B0 (B1 - B0)) /\ (rng RNG (shad B0) (shspan B0 (B1 - B0))) /\ (ahull RNG m B0 (B1 - B0)) /\
  (areg RNG m R0 (R1 - R0)) /\ (ahull RNG m R0 (R1 - R0)) /\ (rdbl bsegs m R0 R1) /\
  (art m) /\ (aro_client RNG m) /\ R1 = R1.
Ltac sc_open CTX := pose proof CTX as sc_ctx_copy;
  destruct sc_ctx_copy as (B0L & B1H & OPB & LEN0 & OPL & B01 & OW0 & OWH & WHID & R0L & R1H & IPR & OVC & SRCB & LOS & SPV47 & OFFB & OFFR & KLO & SPHI & RSTK & RI &
                           ABB & UB0 & RB & RBS & HB & ARL & HL & RDL & ART0 & AROC & _).

Section SAFECOPY2.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV lo OP OENDW IP LEN OV WHI B0 B1 R0 R1 : Z).
  Hypothesis CTX : sc_ctx RNG m SPV lo OP OENDW IP LEN OV WHI B0 B1 R0 R1.

  Notation POST := (zd_safecopy2_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP LEN OENDW B0 B1 R0 R1 lo m).
  (* [comment removed for export] *)
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -64)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 (OP + LEN)) xs6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation SAVED := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition FIN (m1 : amem) : Prop :=
    rw_cells bsegs m1 (SPV + -64) SAVED /\ stk bsegs m1 lo (SPV + -64) /\
    munch [(OP, WHI); (SPV - 2288, SPV)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 B0 B1.
  Ltac open_fin FI := destruct FI as (FR & STK & MU & WM & MI & REG).
  Ltac fin_close :=
    lazymatch goal with |- FIN ?m2 =>
      lazymatch goal with
      | FR2 : rw_cells _ m2 (SPV + -64) _, STK2 : stk _ m2 lo _, MU2 : munch _ m m2, WM2 : wmono _ m m2, MI2 : mem_inv _ m2, REG2 : stk _ m2 B0 B1 |- _ =>
          exact (conj FR2 (conj STK2 (conj MU2 (conj WM2 (conj MI2 REG2)))))
      end
    end.
  Lemma whi_facts : OP + LEN <= WHI /\ OENDW + 32 <= WHI /\ WHI <= B1.
  Proof. sc_open CTX. lia. Qed.

  Lemma ab_app : B1 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= B0.
  Proof. sc_open CTX. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold ablk, AIMG_HI, KLS in ABB. lia. Qed.
  (* [comment removed for export] *)
  Lemma arl_open : R0 < R1 -> ablk R0 R1 /\ unpoisoned m R0 R1 /\ rng RNG R0 (R1 - R0) /\ rng RNG (shad R0) (shspan R0 (R1 - R0)).
  Proof. sc_open CTX. intros H. destruct (ARL ltac:(lia)) as (A & U & Q1 & Q2). replace (R0 + (R1 - R0)) with R1 in A, U by lia. exact (conj A (conj U (conj Q1 Q2))). Qed.
  Lemma al_app : R0 < R1 -> R1 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= R0.
  Proof. sc_open CTX. intros H. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. destruct (arl_open H) as (ABL & _). unfold ablk, AIMG_HI, KLS in ABL. lia. Qed.

  Lemma fin_unp : forall m1, FIN m1 -> unpoisoned m1 B0 B1.
  Proof. sc_open CTX.
    intros m1 FI. open_fin FI. pose proof ab_app as BA.
    eapply unpoisoned_munch; [exact UB0 | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, KHIGH in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_unpL : forall m1, FIN m1 -> R0 < R1 -> unpoisoned m1 R0 R1.
  Proof. sc_open CTX.
    intros m1 FI HL0. open_fin FI. pose proof ab_app as BA. pose proof (al_app HL0) as BL. destruct (arl_open HL0) as (ABL & UL0 & RL & RLS).
    eapply unpoisoned_munch; [exact UL0 | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, KHIGH in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_art : forall m1, FIN m1 -> art m1.
  Proof. sc_open CTX.
    intros m1 FI. open_fin FI. pose proof ab_app as BA.
    eapply art_transport; [exact ART0| exact MU| exact WM|].
    unfold ablk, AIMG_HI, KLS, KHIGH in *. repeat constructor; cbn [fst]; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fin_rdl : forall m1, FIN m1 -> rdbl bsegs m1 R0 R1.
  Proof. sc_open CTX.
    intros m1 FI. open_fin FI. destruct SRCB as [AP|[IN1 IN2]].
    - eapply rdbl_transport; [exact RDL| exact MU|]. intros x Hx. left. unfold apart in *. cbn. lia.
    - eapply rdbl_sub; [apply rdbl_of_stk; exact REG| lia| lia].
  Qed.
  (* [comment removed for export] *)
  Lemma fin_bal : forall m1, FIN m1 -> exists bs, Z.of_nat (length bs) = R1 - R0 /\ bytes_at bsegs m1 R0 bs.
  Proof. sc_open CTX.
    intros m1 FI. destruct (rdbl_bytes bsegs m1 R0 R1 (fin_rdl _ FI) ltac:(lia)) as (bs & BL & BA).
    exists bs. split; [lia| exact BA].
  Qed.
  Lemma fin_areg : forall m1, FIN m1 -> areg RNG m1 B0 (B1 - B0).
  Proof. sc_open CTX.
    intros m1 FI _. split; [|split; [|split]]; [ replace (B0 + (B1 - B0)) with B1 by lia; exact ABB
      | replace (B0 + (B1 - B0)) with B1 by lia; exact (fin_unp _ FI) | exact RB | exact RBS ].
  Qed.
  Lemma fin_aro : forall m1 A n, FIN m1 -> B0 <= A -> 0 <= n -> A + n <= B1 -> aro RNG m1 A n.
  Proof. sc_open CTX.
    intros m1 A n FI H1 H2 H3. pose proof (fin_unp _ FI) as U. split; [| split].
    - eapply unpoisoned_sub; [exact U| lia| lia].
    - eapply rng_sub; [exact RB| lia| lia].
    - eapply rng_sub; [exact RBS| |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_aroL : forall m1 A n, FIN m1 -> R0 <= A -> 0 < n -> A + n <= R1 -> aro RNG m1 A n.
  Proof. sc_open CTX.
    intros m1 A n FI H1 H2 H3. pose proof (fin_unpL _ FI ltac:(lia)) as U. destruct (arl_open ltac:(lia)) as (ABL & UL0 & RL & RLS). split; [| split].
    - eapply unpoisoned_sub; [exact U| lia| lia].
    - eapply rng_sub; [exact RL| lia| lia].
    - eapply rng_sub; [exact RLS| |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_ahull : forall m1 A n, FIN m1 -> B0 <= A -> 0 <= n -> A + n <= B1 -> ahull RNG m1 A n.
  Proof. sc_open CTX.
    intros m1 A n FI H1 H2 H3. open_fin FI. destruct HB as (RLO & RHI & C1 & C2 & C3 & C4 & C5 & C6 & W & R).
    exists RLO, RHI. split; [lia|]. split; [lia|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|].
    split; [eapply wr_at_transport; [exact W| exact WM] | exact R].
  Qed.
  Lemma fin_ahullL : forall m1 A n, FIN m1 -> R0 <= A -> 0 <= n -> A + n <= R1 -> ahull RNG m1 A n.
  Proof. sc_open CTX.
    intros m1 A n FI H1 H2 H3. open_fin FI. destruct HL as (RLO & RHI & C1 & C2 & C3 & C4 & C5 & C6 & W & R).
    exists RLO, RHI. split; [lia|]. split; [lia|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|].
    split; [eapply wr_at_transport; [exact W| exact WM] | exact R].
  Qed.
  Lemma fin_app : forall A n, B0 <= A -> 0 <= n -> A + n <= B1 -> app_blk A (A + n).
  Proof. sc_open CTX. intros A n H1 H2 H3. pose proof ab_app. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
         unfold ablk, AIMG_HI, KLS in ABB. unfold app_blk, KLOW, KHIGH, KEND, ASHOFF. lia. Qed.
  Lemma fin_appL : forall A n, R0 <= A -> 0 < n -> A + n <= R1 -> app_blk A (A + n).
  Proof. sc_open CTX. intros A n H1 H2 H3. pose proof (al_app ltac:(lia)). pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
         destruct (arl_open ltac:(lia)) as (ABL & _). unfold ablk, AIMG_HI, KLS in ABL. unfold app_blk, KLOW, KHIGH, KEND, ASHOFF. lia. Qed.
  Lemma fin_stkD : forall m1 D n, FIN m1 -> B0 <= D -> 0 <= n -> D + n <= B1 -> stk bsegs m1 D (D + n).
  Proof. sc_open CTX.
    intros m1 D n FI H1 H2 H3. open_fin FI.
    destruct (stk_split bsegs m1 B0 D B1 REG ltac:(lia)) as [_ Q2]. destruct (stk_split bsegs m1 D (D + n) B1 Q2 ltac:(lia)) as [Q3 _]. exact Q3.
  Qed.
  Lemma fin_rdblL : forall m1 A n, FIN m1 -> R0 <= A -> A + n <= R1 -> rdbl bsegs m1 A (A + n).
  Proof. sc_open CTX. intros m1 A n FI H1 H2. eapply rdbl_sub; [exact (fin_rdl _ FI)| lia| lia]. Qed.
  Lemma fin_astk : astk RNG lo (SPV + -64).
  Proof. sc_open CTX. split; [exact KLO|]. split; [eapply rng_sub; [exact RSTK| lia| lia] | exact RI]. Qed.
  Lemma fin_stk : forall m1, FIN m1 -> stk bsegs m1 lo (SPV + -64).  Proof. sc_open CTX. intros m1 FI; open_fin FI; exact STK. Qed.
  Lemma fin_mi : forall m1, FIN m1 -> mem_inv bsegs m1.  Proof. sc_open CTX. intros m1 FI; open_fin FI; exact MI. Qed.
  Lemma fin_after_call : forall m1 m2 D n, FIN m1 -> B0 <= D -> 0 <= n -> D + n <= B1 -> OP <= D -> D + n <= WHI ->
    munch [(SPV + -64 - 2224, SPV + -64); (D, D + n)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
    stk bsegs m2 lo (SPV + -64) -> stk bsegs m2 D (D + n) -> FIN m2.
  Proof. sc_open CTX.
    intros m1 m2 D n FI H1 H2 H3 H4 H5 MUc WMc MI2 STK2 SD2. pose proof FI as FI0. open_fin FI.
    split; [| split; [exact STK2| split; [| split; [| split; [exact MI2|]]]]].
    - destruct FI0 as [FR0 _]. eapply rw_cells_transport; [exact FR0| exact MUc| exact WMc|]. cbn. lia.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. intros x. cbn. lia.
    - eapply wmono_trans; [exact WM| exact WMc].
    - destruct (stk_split bsegs m1 B0 D B1 REG ltac:(lia)) as [Q1 Q2]. destruct (stk_split bsegs m1 D (D + n) B1 Q2 ltac:(lia)) as [_ Q3].
      apply (stk_merge bsegs m2 B0 D B1); [| | lia].
      + eapply stk_transport_disjoint; [exact Q1| exact MUc| exact WMc| cbn; lia].
      + apply (stk_merge bsegs m2 D (D + n) B1); [exact SD2| | lia].
        eapply stk_transport_disjoint; [exact Q3| exact MUc| exact WMc| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Ltac mm_callL FI D S FI2 :=
    eapply evtF_cut;
    [ eapply (zd_memmoveZ_proofA RNG D S 16 (SPV + -64));
      [ apply (fin_stkD _ D 16 FI); lia | apply (fin_rdblL _ S 16 FI); lia | lia | exact (fin_stk _ FI) | lia | lia | lia | lia
      | apply fin_appL; lia | apply (fin_aroL _ S 16 FI); lia | apply (fin_ahullL _ S 16 FI); lia
      | apply fin_app; lia | apply (fin_aro _ D 16 FI); lia | apply (fin_ahull _ D 16 FI); lia
      | exact (fin_art _ FI) | exact fin_astk | exact (fin_mi _ FI) | reflexivity | reflexivity | reflexivity ]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in let m2 := fresh "m" in
      let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MI2 := fresh "MIc" in let STK2 := fresh "STKc" in let SD2 := fresh "SDc" in
      intros ms' PO;
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MI2 & STK2 & SD2);
      pose proof (fin_after_call _ m2 D 16 FI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) MUc WMc MI2 STK2 SD2) as FI2;
      clear MUc WMc MI2 STK2 SD2;
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end ].

  (* [comment removed for export] *)
  Lemma sc_epi : forall m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31,
    FIN m1 -> evtF bsegs RNG POST (ST 0x95bb8 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31).
  Proof.
    sc_open CTX. intros until x31. intros FI. pose proof (fin_rdl _ FI) as RD1. open_fin FI.
    kx_autoFLAx [KAApp (SPV - 64) 64] [] 24%nat [KZRange SPV 4096 (2^47); KZWr (SPV - 64) 64] [(SPV - 64, 64)] [(SPV - 64, 64)].
    all: try kx_z. all: try kx_acc RSTK.
    all: kx_mem. all: zstep.
    release_frame FR STK SPV.
    apply evtF_done. unfold zd_safecopy2_postA. do 15 eexists. exists m1.
    split; [reflexivity|]. split; [|split; [exact WM| split; [exact MI| split; [exact STK| split; [exact REG| exact RD1]]]]].
    eapply munch_weaken; [|exact MU]. intros x Hx; unfold outside in *; cbn in Hx |- *; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma sc_tail_loop : forall (n : nat) m1 (X Y : Z) (w : word) xra x5 x6 x7 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31,
    OP + LEN - Y <= Z.of_nat n -> R0 <= X -> X + (OP + LEN - Y) <= R1 -> OP <= Y -> Y < OP + LEN -> w = Z_to_bv 64 (X - Y) -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x95b60 m1 xra x5 x6 x7 w xs1 xa0 (Z_to_bv 64 Y) xa2 xa3 xa4 xa5 xa6 xa7
                             xs2 xs3 xs6 x28 x29 x30 x31).
  Proof.
    sc_open CTX.
    induction n as [|n IH]; intros until x31; intros HN HX HXE HOY HYE Hw FI; [exfalso; lia|].
    pose proof (fin_unp _ FI) as UB1. pose proof (fin_unpL _ FI ltac:(lia)) as UL1. destruct (fin_bal _ FI) as (bs & BL & BA).
    destruct (arl_open ltac:(lia)) as (ABL & UL0 & RL & RLS).
    pose proof FI as FI1. open_fin FI. pose proof ab_app as BA'. pose proof (al_app ltac:(lia)) as BL'. pose proof whi_facts as (W1 & W2 & W3).
    zstep. kx_mkR_fold.
    replace (Z_to_bv 64 (bv_unsigned w + Y)) with (Z_to_bv 64 X)
      by (rewrite Hw, Z_to_bv_unsigned; apply Z_to_bv_eqm; unfold bv_wrap; cbn [bv_modulus]; rewrite Zplus_mod_idemp_l; f_equal; lia).
    kx_autoFLAx [KAUnp X 1; KAUnp Y 1; KAApp Y 1] [0x95b60; 0x95bb8] 40%nat
      [KZRange X 4096 (2^47 - 1); KZRange Y 4096 (2^47 - 1); KZRange (OP + LEN) 0 (2^47);
       KZRange (OP + LEN - Y) 1 (2^47); KZRange (X - R0) 0 (2^47); KZRange (R1 - X) 1 (2^47); KZWr Y 1]
      [(X, 1)] [(X, 1); (Y, 1)].
    all: try kx_z. all: try kx_acc RB. all: try kx_acc RL.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613216) _ _ ?m2 _) =>   (* [comment removed for export] *)
             apply (IH m2 (X + 1) (Y + 1) w); try lia; [rewrite Hw; f_equal; lia | fin_close]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613304) _ _ ?m2 _) =>       (* [comment removed for export] *)
             apply sc_epi; fin_close
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma sc_tailE : forall m1 (IP0 OP0 : Z) xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31,
    R0 <= IP0 -> IP0 + (OP + LEN - OP0) <= R1 -> OP <= OP0 -> OP0 < OP + LEN -> OENDW < OP + LEN -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x95b50 m1 xra x5 x6 x7 (Z_to_bv 64 IP0) (Z_to_bv 64 OENDW) (Z_to_bv 64 OP0) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                             xs2 xs3 xs6 x28 x29 x30 x31).
  Proof. sc_open CTX.
    intros until x31; intros HI HIE HO HOO HOE FI. pose proof FI as FI1. open_fin FI. pose proof whi_facts as (W1 & W2 & W3).
    kx_autoFLAx (@nil kza) [0x95b60] 10%nat
      [KZRange IP0 4096 (2^47); KZRange OP0 4096 (2^47); KZRange OENDW 0 (2^47); KZRange (OP + LEN) 0 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ ?w _ _ (Z_to_bv 64 ?Y) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 613216) _ _ ?m2 _) =>
             apply (sc_tail_loop (Z.to_nat (OP + LEN - Y)) m2 (IP0 + (Y - OP0)) Y w); try lia; [f_equal; lia | fin_close]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma sc_tailW : forall m1 (IP0 OP0 OPc : Z) xra x5 x6 x7 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31,
    R0 <= IP0 -> IP0 + (OP + LEN - OP0) <= R1 -> OP <= OP0 -> OP0 <= OPc -> OENDW <= OPc -> OPc <= OP + LEN -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x95b4c m1 xra x5 x6 x7 (Z_to_bv 64 IP0) (Z_to_bv 64 OENDW) (Z_to_bv 64 OP0) (Z_to_bv 64 OPc) xa2 xa3 xa4 xa5 xa6 xa7
                             xs2 xs3 xs6 x28 x29 x30 x31).
  Proof. sc_open CTX.
    intros until x31; intros HI HIE HO HOC HWC HCE FI. pose proof FI as FI1. open_fin FI. pose proof whi_facts as (W1 & W2 & W3).
    kx_autoFLAx (@nil kza) [0x95b50; 0x95bb8] 12%nat
      [KZRange IP0 4096 (2^47); KZRange OP0 4096 (2^47); KZRange OENDW 0 (2^47); KZRange OPc 4096 (2^47);
       KZRange (OP + LEN) 0 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613304) _ _ ?m2 _) => apply sc_epi; fin_close
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613200) _ _ ?m2 _) => apply (sc_tailE m2 IP0 OP0); try lia; fin_close
         end.
  Qed.
  Notation SHP x := (Z_to_bv 64 (0x7fff8000 + x / 8)).
  (* [comment removed for export] *)
  Lemma sc_w8A : forall (n : nat) m1 (X Y IP0 OP0 : Z) xra x5 x6 x7 xa4 xs2 xs3 xs6 x28 x29 x30 x31,
    OENDW - Y < Z.of_nat n -> B0 <= X -> X + 8 <= Y -> X - Y = IP0 - OP0 -> B0 <= IP0 -> OP <= OP0 -> OP0 <= Y -> Y <= OENDW ->
    OENDW < OP + LEN -> R0 = B0 -> R1 = B1 -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x9582c m1 xra x5 x6 x7 (Z_to_bv 64 IP0) (Z_to_bv 64 OENDW)
                             (Z_to_bv 64 OP0) (SHP Y) (Z_to_bv 64 X) (Z_to_bv 64 Y) xa4 (SHP X) (Z_to_bv 64 Y) (Z_to_bv 64 X)
                             xs2 xs3 xs6 x28 x29 x30 x31).
  Proof. sc_open CTX.
    induction n as [|n IH]; intros until x31; intros HN HX HXY HPAR HI HO HOY HYW HWE HR0 HR1 FI; [exfalso; lia|].
    pose proof (fin_unp _ FI) as UB1. pose proof FI as FI1. open_fin FI. pose proof ab_app as BA. pose proof whi_facts as (W1 & W2 & W3).
    kx_autoFLAx [KAUnp X 8; KAUnp Y 8; KAApp X 8; KAApp Y 8; KAShp (0x7fff8000 + X / 8) X; KAShp (0x7fff8000 + Y / 8) Y]
      [0x9582c; 0x95b50; 0x95bb8] 140%nat
      [KZRange X 4096 (2^47); KZRange Y 4096 (2^47); KZRange OENDW 0 (2^47); KZRange (OP + LEN) 0 (2^47);
       KZRange IP0 4096 (2^47); KZRange OP0 4096 (2^47); KZRange (OENDW - OP0) 0 (2^47);
       KZRange (Y - X) 8 (2^47); KZRange (OENDW - Y) 0 (2^47); KZRange (OP + LEN - OENDW) 1 (2^47);
       KZWr Y 8; KZDisj Y 8 X 8]
      [(X, 8)] [(X, 8); (Y, 8)].
    all: try kx_z. all: try kx_acc RB.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 612396) _ _ ?m2 _) =>       (* [comment removed for export] *)
             replace (X / 8 + 2147450881) with (0x7fff8000 + (X + 8) / 8) by (Z.div_mod_to_equations; lia);
             replace (Y / 8 + 2147450881) with (0x7fff8000 + (Y + 8) / 8) by (Z.div_mod_to_equations; lia);
             apply (IH m2 (X + 8) (Y + 8) IP0 OP0); try lia; fin_close
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613200) _ _ ?m2 _) =>       (* [comment removed for export] *)
             apply sc_tailE; try lia; fin_close
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613304) _ _ ?m2 _) =>
             apply sc_epi; fin_close
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma sc_w8B : forall (n : nat) m1 (X Y : Z) xra x5 x6 x7 xs1 xa4 xa6 xa7 xs3 xs6 x28 x29 x30 x31,
    OP + LEN - Y < Z.of_nat n -> B0 <= X -> X + 8 <= Y -> OP <= Y -> Y <= OP + LEN -> OP + LEN <= OENDW -> R0 = B0 -> R1 = B1 -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x9597c m1 xra x5 x6 x7 (Z_to_bv 64 X) xs1
                             (Z_to_bv 64 Y) (SHP Y) (Z_to_bv 64 X) (Z_to_bv 64 Y) xa4 (SHP X) xa6 xa7
                             (Z_to_bv 64 (OP + LEN)) xs3 xs6 x28 x29 x30 x31).
  Proof. sc_open CTX.
    induction n as [|n IH]; intros until x31; intros HN HX HXY HOY HYE HEW HR0 HR1 FI; [exfalso; lia|].
    pose proof (fin_unp _ FI) as UB1. pose proof FI as FI1. open_fin FI. pose proof ab_app as BA. pose proof whi_facts as (W1 & W2 & W3).
    kx_autoFLAx [KAUnp X 8; KAUnp Y 8; KAApp X 8; KAApp Y 8; KAShp (0x7fff8000 + X / 8) X; KAShp (0x7fff8000 + Y / 8) Y]
      [0x9597c; 0x95bb8] 140%nat
      [KZRange X 4096 (2^47); KZRange Y 4096 (2^47); KZRange (OP + LEN) 0 (2^47);
       KZRange (Y - X) 8 (2^47); KZRange (OP + LEN + 8 - Y) 8 (2^47); KZWr Y 8; KZDisj Y 8 X 8]
      [(X, 8)] [(X, 8); (Y, 8)].
    all: try kx_z. all: try kx_acc RB.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 612732) _ _ ?m2 _) =>       (* [comment removed for export] *)
             replace (X / 8 + 2147450881) with (0x7fff8000 + (X + 8) / 8) by (Z.div_mod_to_equations; lia);
             replace (Y / 8 + 2147450881) with (0x7fff8000 + (Y + 8) / 8) by (Z.div_mod_to_equations; lia);
             apply (IH m2 (X + 8) (Y + 8)); try lia; fin_close
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613304) _ _ ?m2 _) =>       (* [comment removed for export] *)
             apply sc_epi; fin_close
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma sc_w16A : forall (n : nat) m1 (X Y IP0 OP0 : Z) xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31,
    OENDW - Y < Z.of_nat n -> R0 <= IP0 -> X - Y = IP0 - OP0 -> X + (OENDW - Y) + 31 <= R1 -> IP0 + (OP + LEN - OP0) <= R1 ->
    OP <= OP0 -> OP0 <= Y -> Y < OENDW -> OENDW < OP + LEN -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x95b18 m1 xra x5 x6 x7 (Z_to_bv 64 IP0) (Z_to_bv 64 OENDW) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                             (Z_to_bv 64 Y) (Z_to_bv 64 (X + 16)) (Z_to_bv 64 OP0) x28 x29 x30 x31).
  Proof. sc_open CTX.
    induction n as [|n IH]; intros until x31; intros HN HI HPAR HXE HIE HO HOY HYW HWE FI; [exfalso; lia|].
    pose proof FI as FI1. open_fin FI. pose proof whi_facts as (W1 & W2 & W3).
    (* [comment removed for export] *)
    kx_autoFLAx (@nil kza) (@nil Z) 10%nat [KZRange X 4096 (2^47); KZRange Y 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: kx_mem.
    mm_callL FI1 Y X FI2.
    (* [comment removed for export] *)
    kx_autoFLAx (@nil kza) (@nil Z) 12%nat [KZRange X 4096 (2^47); KZRange Y 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    mm_callL FI2 (Y + 16) (X + 16) FI3.
    (* [comment removed for export] *)
    kx_autoFLAx (@nil kza) [0x95b18; 0x95b4c] 12%nat [KZRange X 4096 (2^47); KZRange Y 4096 (2^47); KZRange OENDW 0 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613144) _ _ ?m2 _) =>       (* [comment removed for export] *)
             replace (X + 48) with ((X + 32) + 16) by lia;
             apply (IH m2 (X + 32) (Y + 32) IP0 OP0); try lia; first [assumption | fin_close]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613196) _ _ ?m2 _) =>       (* [comment removed for export] *)
             apply (sc_tailW m2 IP0 OP0 OENDW); try lia; first [assumption | fin_close]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma sc_w16Ae : forall m1 (IP0 OP0 : Z) xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31,
    R0 <= IP0 -> IP0 + (OENDW - OP0) + 31 <= R1 -> IP0 + (OP + LEN - OP0) <= R1 ->
    OP <= OP0 -> OP0 <= OENDW -> OENDW < OP + LEN -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x95af4 m1 xra x5 x6 x7 (Z_to_bv 64 IP0) (Z_to_bv 64 OENDW) (Z_to_bv 64 OP0) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                             xs2 xs3 xs6 x28 x29 x30 x31).
  Proof. sc_open CTX.
    intros until x31; intros HI HXE HIE HO HOW HWE FI. pose proof FI as FI1. open_fin FI. pose proof whi_facts as (W1 & W2 & W3).
    kx_autoFLAx (@nil kza) (@nil Z) 10%nat [KZRange IP0 4096 (2^47); KZRange OP0 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: kx_mem.
    mm_callL FI1 OP0 IP0 FI2.
    kx_autoFLAx (@nil kza) [0x95b18; 0x95b4c] 16%nat
      [KZRange IP0 4096 (2^47); KZRange OP0 4096 (2^47); KZRange OENDW 0 (2^47); KZRange (OENDW - OP0) 0 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613144) _ _ ?m2 _) =>       (* [comment removed for export] *)
             replace (IP0 + 32) with ((IP0 + 16) + 16) by lia;
             apply (sc_w16A (Z.to_nat (OENDW - OP0)) m2 (IP0 + 16) (OP0 + 16) IP0 OP0); try lia; first [assumption | fin_close]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613196) _ _ ?m2 _) =>       (* [comment removed for export] *)
             apply (sc_tailW m2 IP0 OP0 OENDW); try lia; first [assumption | fin_close]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma sc_w16B : forall (n : nat) m1 (X Y : Z) xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 x28 x29 x30 x31,
    OP + LEN - Y < Z.of_nat n -> R0 <= X -> X + (OP + LEN - Y) + 31 <= R1 -> OP <= Y -> Y < OP + LEN -> OP + LEN <= OENDW -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x95ac4 m1 xra x5 x6 x7 (Z_to_bv 64 (X + 16)) (Z_to_bv 64 Y) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                             (Z_to_bv 64 (OP + LEN)) xs3 xs6 x28 x29 x30 x31).
  Proof. sc_open CTX.
    induction n as [|n IH]; intros until x31; intros HN HX HXE HOY HYE HEW FI; [exfalso; lia|].
    pose proof FI as FI1. open_fin FI. pose proof whi_facts as (W1 & W2 & W3).
    kx_autoFLAx (@nil kza) (@nil Z) 10%nat [KZRange X 4096 (2^47); KZRange Y 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: kx_mem.
    mm_callL FI1 Y X FI2.
    kx_autoFLAx (@nil kza) (@nil Z) 12%nat [KZRange X 4096 (2^47); KZRange Y 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    mm_callL FI2 (Y + 16) (X + 16) FI3.
    kx_autoFLAx (@nil kza) [0x95ac4; 0x95bb8] 12%nat [KZRange X 4096 (2^47); KZRange Y 4096 (2^47); KZRange (OP + LEN) 0 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613060) _ _ ?m2 _) =>       (* [comment removed for export] *)
             replace (X + 48) with ((X + 32) + 16) by lia;
             apply (IH m2 (X + 32) (Y + 32)); try lia; first [assumption | fin_close]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613304) _ _ ?m2 _) =>       (* [comment removed for export] *)
             apply sc_epi; first [assumption | fin_close]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma sc_w16Be : forall m1 (IP1 OP1 : Z) xra x5 x6 x7 xs1 xa1 xa2 xa4 xa5 xa6 xa7 xs3 xs6 x28 x29 x30 x31,
    R0 <= IP1 -> IP1 + (OP + LEN - OP1) + 31 <= R1 -> OP <= OP1 -> OP1 <= OP + LEN -> OP + LEN <= OENDW -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x95aa0 m1 xra x5 x6 x7 (Z_to_bv 64 IP1) xs1 (Z_to_bv 64 OP1) xa1 xa2 (Z_to_bv 64 (OP + LEN - OP1)) xa4 xa5 xa6 xa7
                             (Z_to_bv 64 (OP + LEN)) xs3 xs6 x28 x29 x30 x31).
  Proof. sc_open CTX.
    intros until x31; intros HI HXE HO HOE HEW FI. pose proof FI as FI1. open_fin FI. pose proof whi_facts as (W1 & W2 & W3).
    kx_autoFLAx (@nil kza) (@nil Z) 10%nat [KZRange IP1 4096 (2^47); KZRange OP1 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: kx_mem.
    mm_callL FI1 OP1 IP1 FI2.
    kx_autoFLAx (@nil kza) [0x95ac4; 0x95bb8] 16%nat
      [KZRange IP1 4096 (2^47); KZRange OP1 4096 (2^47); KZRange (OP + LEN) 0 (2^47); KZRange (OP + LEN - OP1) 0 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613060) _ _ ?m2 _) =>       (* [comment removed for export] *)
             replace (IP1 + 32) with ((IP1 + 16) + 16) by lia;
             apply (sc_w16B (Z.to_nat (OP + LEN - OP1)) m2 (IP1 + 16) (OP1 + 16)); try lia; first [assumption | fin_close]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613304) _ _ ?m2 _) =>       (* [comment removed for export] *)
             apply sc_epi; first [assumption | fin_close]
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma sc_disp : forall m1 (IP1 OP1 : Z) xra x5 x6 x7 xa1 xa2 xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31,
    OP <= OP1 -> OP1 <= OP + LEN ->
    ((OV = 1 /\ R0 = B0 /\ R1 = B1 /\ B0 <= IP1 /\ IP1 + 8 <= OP1) \/ (OV = 0 /\ IP1 = IP /\ OP1 = OP)) -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x957f0 m1 xra x5 x6 x7 (Z_to_bv 64 IP1) (Z_to_bv 64 OENDW) (Z_to_bv 64 OP1) xa1 xa2 (Z_to_bv 64 (OP + LEN - OP1)) (Z_to_bv 64 OV)
                             xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31).
  Proof. sc_open CTX.
    intros until x31; intros HO HOE HOV FI. pose proof FI as FI1. pose proof (fin_unp _ FI) as UB1. open_fin FI.
    pose proof ab_app as BA. pose proof whi_facts as (W1 & W2 & W3).
    destruct HOV as [(HOV1 & HR0 & HR1 & HI & HD) | (HOV0 & -> & ->)].
    - rewrite HOV1. kx_autoFLAx (@nil kza) [0x9582c; 0x9597c; 0x95aa0; 0x95af4; 0x95b4c] 40%nat
        [KZRange IP1 4096 (2^47); KZRange OP1 4096 (2^47); KZRange OENDW 0 (2^47); KZRange (OP + LEN) 0 (2^47);
         KZRange (OP + LEN - OP1) 0 (2^47); KZRange (OP1 - IP1) 8 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)).
      all: try kx_z.
      all: kx_mem.
      all: try replace (Z_to_bv 64 (OP1 mod 2 ^ 64 / 8 + 2147450880)) with (SHP OP1) by (f_equal; rewrite Z.mod_small by lia; lia).
      all: try replace (Z_to_bv 64 (IP1 mod 2 ^ 64 / 8 + 2147450880)) with (SHP IP1) by (f_equal; rewrite Z.mod_small by lia; lia).
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613024) _ _ ?m2 _) => apply sc_w16Be; try lia; fin_close
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 612732) _ _ ?m2 _) => apply (sc_w8B (Z.to_nat (OP + LEN + 8 - OP1)) m2 IP1 OP1); try lia; fin_close
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613196) _ _ ?m2 _) => apply (sc_tailW m2 IP1 OP1 OP1); try lia; fin_close
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613108) _ _ ?m2 _) => apply sc_w16Ae; try lia; fin_close
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 612396) _ _ ?m2 _) => apply (sc_w8A (Z.to_nat (OENDW - OP1 + 1)) m2 IP1 OP1 IP1 OP1); try lia; fin_close
           end.
    - rewrite HOV0. kx_autoFLAx (@nil kza) [0x95aa0; 0x95af4; 0x95b4c] 40%nat
        [KZRange IP 4096 (2^47); KZRange OP 4096 (2^47); KZRange OENDW 0 (2^47); KZRange (OP + LEN) 0 (2^47); KZRange (OP + LEN - OP) 0 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)).
      all: try kx_z.
      all: kx_mem.
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613024) _ _ ?m2 _) => apply sc_w16Be; try lia; fin_close
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613196) _ _ ?m2 _) => apply (sc_tailW m2 IP OP OP); try lia; fin_close
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613108) _ _ ?m2 _) => apply sc_w16Ae; try lia; fin_close
           end.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sc_short_loop : forall (n : nat) m1 (X Y : Z) xra x5 x6 x7 xs1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31,
    OP + LEN - Y <= Z.of_nat n -> R0 <= X -> X + (OP + LEN - Y) <= R1 -> OP <= Y -> Y < OP + LEN -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x95500 m1 xra x5 x6 x7 (Z_to_bv 64 X) xs1 (Z_to_bv 64 Y) (Z_to_bv 64 Y) (Z_to_bv 64 X)
                             xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31).
  Proof. sc_open CTX.
    induction n as [|n IH]; intros until x31; intros HN HX HXE HOY HYE FI; [exfalso; lia|].
    pose proof (fin_unp _ FI) as UB1. pose proof (fin_unpL _ FI ltac:(lia)) as UL1. destruct (fin_bal _ FI) as (bs & BL & BA).
    destruct (arl_open ltac:(lia)) as (ABL & UL0 & RL & RLS).
    pose proof FI as FI1. open_fin FI. pose proof ab_app as BA'. pose proof (al_app ltac:(lia)) as BL'. pose proof whi_facts as (W1 & W2 & W3).
    kx_autoFLAx [KAUnp X 1; KAUnp Y 1; KAApp Y 1] [0x95500; 0x95bb8] 40%nat
      [KZRange X 4096 (2^47 - 1); KZRange Y 4096 (2^47 - 1); KZRange (OP + LEN) 0 (2^47);
       KZRange (OP + LEN - Y) 1 (2^47); KZRange (X - R0) 0 (2^47); KZRange (R1 - X) 1 (2^47); KZWr Y 1]
      [(X, 1)] [(X, 1); (Y, 1)].
    all: try kx_z. all: try kx_acc RB. all: try kx_acc RL.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 611584) _ _ ?m2 _) =>   (* [comment removed for export] *)
             apply (IH m2 (X + 1) (Y + 1)); try lia; fin_close
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613304) _ _ ?m2 _) =>       (* [comment removed for export] *)
             apply sc_epi; fin_close
         end.
  Qed.
  Lemma sc_dispw : forall m1 (IP1 OP1 : Z) (ovw : word) xra x5 x6 x7 xa1 xa2 xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31,
    ovw = Z_to_bv 64 OV -> OP <= OP1 -> OP1 <= OP + LEN ->
    ((OV = 1 /\ R0 = B0 /\ R1 = B1 /\ B0 <= IP1 /\ IP1 + 8 <= OP1) \/ (OV = 0 /\ IP1 = IP /\ OP1 = OP)) -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x957f0 m1 xra x5 x6 x7 (Z_to_bv 64 IP1) (Z_to_bv 64 OENDW) (Z_to_bv 64 OP1) xa1 xa2 (Z_to_bv 64 (OP + LEN - OP1)) ovw
                             xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31).
  Proof. intros until x31; intros -> HO HOE HOV FI. apply sc_disp; assumption. Qed.
  (* [comment removed for export] *)
  Lemma sc_copy8 : forall m1 xra x5 x6 x7 xa1 xa2 xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31,
    8 <= LEN -> OV = 1 -> R0 = B0 -> R1 = B1 -> B0 <= IP -> IP + 8 <= OP -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x95708 m1 xra x5 x6 x7 (Z_to_bv 64 IP) (Z_to_bv 64 OENDW) (Z_to_bv 64 OP) xa1 xa2 (Z_to_bv 64 LEN) (Z_to_bv 64 1)
                             xa5 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31).
  Proof. sc_open CTX.
    intros until x31; intros HLEN HOV HR0 HR1 HI HD FI.
    pose proof (fin_unp _ FI) as UB1. pose proof FI as FI1. open_fin FI. pose proof ab_app as BA. pose proof whi_facts as (W1 & W2 & W3).
    kx_autoFLAx [KAUnp IP 8; KAUnp OP 8; KAApp OP 8] [0x957f0] 120%nat
      [KZRange IP 4096 (2^47 - 8); KZRange OP 4096 (2^47 - 8); KZRange LEN 8 (2^47); KZRange OENDW 0 (2^47); KZRange (OP - IP) 8 (2^47);
       KZWr OP 8; KZDisj OP 8 IP 8]
      [(IP, 8)] [(IP, 8); (OP, 8)].
    all: try kx_z. all: try kx_acc RB.
    all: kx_mem.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 612336) _ _ ?m2 _) =>
      replace (Z_to_bv 64 (LEN + -8)) with (Z_to_bv 64 (OP + LEN - (OP + 8))) by (f_equal; lia);
      apply (sc_dispw m2 (IP + 8) (OP + 8)); [rewrite HOV; reflexivity | lia | lia | left; repeat split; lia | fin_close] end.
  Qed.
  (* [comment removed for export] *)
  Lemma aro_fin : forall m1 A n, FIN m1 -> aro RNG m A n -> A + n <= 0xd1740 -> 0 <= A -> aro RNG m1 A n.
  Proof. sc_open CTX.
    intros m1 A n FI (U & Q1 & Q2) HA HA0. open_fin FI. pose proof ab_app as BA. pose proof whi_facts as (W1 & W2 & W3).
    unfold ablk, AIMG_HI, KLS, KHIGH in *.
    split; [| split; [exact Q1| exact Q2]].
    eapply unpoisoned_munch; [exact U| exact MU|]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Ltac tbl_case Y HOV RB R32 R64 :=
    kx_autoFLAx [KAUnp IP 8; KAUnp Y 8; KAApp Y 8; KAUnp 0x22280 32; KAUnp 0x22240 32] [0x957f0] 140%nat
      [KZRange IP 4096 (2^47 - 8); KZRange LEN 8 (2^47); KZRange OENDW 0 (2^47); KZWr Y 8; KZImg 0x22240 0x222a0]
      [(IP, 8)] [(IP, 8); (Y, 8); (0x22280, 32); (0x22240, 32)];
    lazymatch goal with
    | |- evtF _ _ _ _ =>
        kx_mem;
        lazymatch goal with
        | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ (Z_to_bv 64 ?IPc) _ (Z_to_bv 64 ?OPc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 612336) _ _ ?m2 _) =>
            replace (Z_to_bv 64 (LEN + -8)) with (Z_to_bv 64 (OP + LEN - OPc)) by (f_equal; lia);
            apply (sc_dispw m2 IPc OPc); [rewrite HOV; reflexivity | lia | lia | left; repeat split; lia | fin_close]
        end
    | |- _ => first [kx_z | kx_acc RB | kx_acc R32 | kx_acc R64]
    end.
  Lemma sc_tbl : forall (d : Z) m1 xra x5 x6 x7 xa1 xa2 xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31,
    0 <= d <= 7 -> OP = IP + d -> 8 <= LEN -> OV = 1 -> R0 = B0 -> R1 = B1 -> B0 <= IP -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x95570 m1 xra x5 x6 x7 (Z_to_bv 64 IP) (Z_to_bv 64 OENDW) (Z_to_bv 64 (IP + d)) xa1 xa2 (Z_to_bv 64 LEN) (Z_to_bv 64 1)
                             (Z_to_bv 64 d) xa6 xa7 xs2 xs3 xs6 x28 x29 x30 x31).
  Proof. sc_open CTX.
    intros until x31; intros HD HOP HLEN HOV HR0 HR1 HI FI.
    pose proof (fin_unp _ FI) as UB1. pose proof FI as FI1. open_fin FI. pose proof ab_app as BA. pose proof whi_facts as (W1 & W2 & W3).
    assert (T32 : aro RNG m1 0x22280 32) by (apply (aro_fin m1 0x22280 32 FI1); [aro_cl AROC| lia| lia]).
    assert (T64 : aro RNG m1 0x22240 32) by (apply (aro_fin m1 0x22240 32 FI1); [aro_cl AROC| lia| lia]).
    destruct T32 as (U32 & R32 & RS32). destruct T64 as (U64 & R64 & RS64).
    assert (C : d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7) by lia.
    destruct C as [E | [E | [E | [E | [E | [E | [E | E]]]]]]]; subst d;
      [ replace (IP + 0) with IP by lia; tbl_case IP HOV RB R32 R64 | tbl_case (IP + 1) HOV RB R32 R64 | tbl_case (IP + 2) HOV RB R32 R64
      | tbl_case (IP + 3) HOV RB R32 R64 | tbl_case (IP + 4) HOV RB R32 R64 | tbl_case (IP + 5) HOV RB R32 R64 | tbl_case (IP + 6) HOV RB R32 R64
      | tbl_case (IP + 7) HOV RB R32 R64 ].
  Qed.
  (* [comment removed for export] *)
  Lemma sc_main : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    stk bsegs m lo SPV -> stk bsegs m B0 B1 -> mem_inv bsegs m ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OP) (Z_to_bv 64 OENDW) (Z_to_bv 64 IP) (Z_to_bv 64 LEN) (Z_to_bv 64 OV)
                                 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 APZD_SAFECOPY) fc None m (seg_rom bsegs)).
  Proof. sc_open CTX.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ST0 REG0 MI0.
    pose proof ART0 as (GOT & RIC & SHB & INI & LAY & REAL). pose proof ab_app as BA. pose proof whi_facts as (W1 & W2 & W3).
    assert (MU : munch [(OP, WHI); (SPV - 2288, SPV)] m m) by apply munch_refl. assert (WM : wmono bsegs m m) by apply wmono_refl.
    pose proof UB0 as UB1.
    carve_frame 64%nat ST0.
    unfold APZD_SAFECOPY.
    destruct OVC as [(HOV & HR0 & HR1 & HIO) | (HOV & HIL)]; rewrite HOV.
    - kx_autoFLAx [KAApp (SPV - 64) 64] [0x95bb8; 0x95500; 0x95708; 0x95570] 70%nat
        [KZRange SPV 4096 (2^47); KZRange IP 4096 (2^47); KZRange OP 4096 (2^47); KZRange LEN 0 (2^47); KZRange OENDW 0 (2^47);
         KZRange (OP + LEN) 0 (2^47); KZRange (OP - IP) 0 (2^47); KZWr (SPV - 64) 64]
        [(SPV - 64, 64)] [(SPV - 64, 64)].
      all: try kx_cell_lit. all: try kx_z. all: try kx_acc RSTK. all: try kx_acc RI.
      all: kx_mem.
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 612104) _ _ ?m2 _) =>       (* [comment removed for export] *)
               apply sc_copy8; try lia; fin_close
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 611696) _ _ ?m2 _) =>       (* [comment removed for export] *)
               replace (Z_to_bv 64 OP) with (Z_to_bv 64 (IP + (OP - IP))) by (f_equal; lia);
               replace (Z_to_bv 64 (OP + -1 * IP)) with (Z_to_bv 64 (OP - IP)) by (f_equal; lia);
               apply (sc_tbl (OP - IP)); try lia; fin_close
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613304) _ _ ?m2 _) =>       (* [comment removed for export] *)
               apply sc_epi; fin_close
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 611584) _ _ ?m2 _) =>       (* [comment removed for export] *)
               apply (sc_short_loop (Z.to_nat LEN) m2 IP OP); try lia; fin_close
           end.
    - kx_autoFLAx [KAApp (SPV - 64) 64] [0x95bb8; 0x95500; 0x957f0] 70%nat
        [KZRange SPV 4096 (2^47); KZRange IP 4096 (2^47); KZRange OP 4096 (2^47); KZRange LEN 0 (2^47); KZRange OENDW 0 (2^47);
         KZRange (OP + LEN) 0 (2^47); KZWr (SPV - 64) 64]
        [(SPV - 64, 64)] [(SPV - 64, 64)].
      all: try kx_cell_lit. all: try kx_z. all: try kx_acc RSTK. all: try kx_acc RI.
      all: kx_mem.
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 612336) _ _ ?m2 _) =>       (* [comment removed for export] *)
               replace (Z_to_bv 64 LEN) with (Z_to_bv 64 (OP + LEN - OP)) by (f_equal; lia);
               apply (sc_dispw m2 IP OP); [rewrite HOV; reflexivity | lia | lia | right; repeat split; lia | fin_close]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 613304) _ _ ?m2 _) =>       (* [comment removed for export] *)
               apply sc_epi; fin_close
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 611584) _ _ ?m2 _) =>       (* [comment removed for export] *)
               apply (sc_short_loop (Z.to_nat LEN) m2 IP OP); try lia; fin_close
           end.
  Qed.
End SAFECOPY2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem zd_safecopy2_proofA : zd_safecopy2_stmtA.
Proof.
  intros RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV lo OP OENDW IP LEN OV B0 B1 R0 R1.
  intros REG B0L B1H OPB LEN0 OPL OW0 OWH RDL R0L R1H IPR OVD STK LOS SPR OFFB OFFR B01 ARB HB ARL HL ART AST AROC MI -> -> -> -> ->.
  unfold off_stack in *.
  pose proof AST as (KLO & RSTK & RI). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  destruct (ARB ltac:(lia)) as (ABB & UB0 & RB & RBS). replace (B0 + (B1 - B0)) with B1 in ABB, UB0 by lia.
  assert (CTX : sc_ctx RNG m SPV lo OP OENDW IP LEN OV (Z.max (OP + LEN) (OENDW + 32)) B0 B1 R0 R1).
  { unfold sc_ctx. repeat (lazymatch goal with |- _ /\ _ => split end); try assumption; try reflexivity; try lia.
    all: destruct OVD as [(O1 & E0 & E1 & HIO) | (O0 & HIL & SB)].
    all: first [ left; repeat split; lia | right; repeat split; lia | right; split; lia | exact SB | right; lia ]. }
  exact (sc_main RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OENDW IP LEN OV _ B0 B1 R0 R1 CTX
                 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 STK REG MI).
Qed.
End CANSEC1.
