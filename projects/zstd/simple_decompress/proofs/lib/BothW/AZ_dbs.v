(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit MemRange.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_libc_iface AZ_seq_iface AZ_kx AZ_memmove AZ_dbs_iface.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
  Forall (fun iv : Z * Z => 0xd5d40 <= fst iv) W -> art m'.
Proof.
  intros W m m' (GOT & RIC & SHB & INI & LAY & REAL) MU WM HW.
  unfold art. repeat split.
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply disjoint_from_above; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply disjoint_from_above; [exact HW| cbn; lia]] ].
Qed.

(* [comment removed for export] *)
Definition db_ctx (RNG : footprint) (m : amem) (SPV lo OP IP LEN B0 B1 R0 R1 : Z) : Prop :=
  (4096 <= B0) /\ (B1 < 2^47) /\ (B0 <= OP) /\ (0 <= LEN) /\ (OP + LEN <= B1) /\ (B0 < B1) /\
  (4096 <= R0) /\ (R1 < 2^47) /\ (R0 <= IP) /\ (IP + LEN <= R1) /\
  (apart R0 (R1 - R0) B0 (B1 - B0) \/ (B0 <= R0 /\ R1 <= B1)) /\
  (lo <= SPV - 2304) /\ (4096 <= SPV < 2^47) /\
  (B0 + (B1 - B0) <= lo \/ SPV <= B0) /\ (R0 + (R1 - R0) <= lo \/ SPV <= R0) /\
  (KHIGH <= lo) /\ (0x10007fff8000 <= SPV - 2304) /\ (rng RNG lo (SPV - lo)) /\ (rng_aimg RNG) /\
  (ablk B0 B1) /\ (unpoisoned m B0 B1) /\ (rng RNG B0 (B1 - B0)) /\ (rng RNG (shad B0) (shspan B0 (B1 - B0))) /\ (ahull RNG m B0 (B1 - B0)) /\
  (areg RNG m R0 (R1 - R0)) /\ (ahull RNG m R0 (R1 - R0)) /\ (rdbl bsegs m R0 R1) /\
  (art m) /\ R1 = R1.
Ltac db_open CTX := pose proof CTX as db_ctx_copy;
  destruct db_ctx_copy as (B0L & B1H & OPB & LEN0 & OPL & B01 & R0L & R1H & IPR & IPL & SRCB & LOS & SPV47 & OFFB & OFFR & KLO & SPHI & RSTK & RI &
                           ABB & UB0 & RB & RBS & HB & ARL & HL & RDL & ART0 & _).

Section DBS.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV lo OP IP LEN B0 B1 R0 R1 : Z).
  Hypothesis CTX : db_ctx RNG m SPV lo OP IP LEN B0 B1 R0 R1.

  Notation POST := (zd_dbs_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP LEN B0 B1 R0 R1 lo m).
  (* [comment removed for export] *)
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs7 xs8 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -80)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 (OP + LEN)) xs6 xs7 xs8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation SAVED := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition FIN (m1 : amem) : Prop :=
    rw_cells bsegs m1 (SPV + -80) SAVED /\ stk bsegs m1 lo (SPV + -80) /\
    munch [(OP, OP + LEN); (SPV - 2304, SPV)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 B0 B1.
  Ltac open_fin FI := destruct FI as (FR & STK & MU & WM & MI & REG).
  Ltac fin_close :=
    lazymatch goal with |- FIN ?m2 =>
      lazymatch goal with
      | FR2 : rw_cells _ m2 (SPV + -80) _, STK2 : stk _ m2 lo _, MU2 : munch _ m m2, WM2 : wmono _ m m2, MI2 : mem_inv _ m2, REG2 : stk _ m2 B0 B1 |- _ =>
          exact (conj FR2 (conj STK2 (conj MU2 (conj WM2 (conj MI2 REG2)))))
      end
    end.

  Lemma ab_app : B1 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= B0.
  Proof. db_open CTX. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold ablk, AIMG_HI, KLS in ABB. lia. Qed.
  (* [comment removed for export] *)
  Lemma arl_open : R0 < R1 -> ablk R0 R1 /\ unpoisoned m R0 R1 /\ rng RNG R0 (R1 - R0) /\ rng RNG (shad R0) (shspan R0 (R1 - R0)).
  Proof. db_open CTX. intros H. destruct (ARL ltac:(lia)) as (A & U & Q1 & Q2). replace (R0 + (R1 - R0)) with R1 in A, U by lia. exact (conj A (conj U (conj Q1 Q2))). Qed.
  Lemma al_app : R0 < R1 -> R1 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= R0.
  Proof. db_open CTX. intros H. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. destruct (arl_open H) as (ABL & _). unfold ablk, AIMG_HI, KLS in ABL. lia. Qed.

  Lemma fin_unp : forall m1, FIN m1 -> unpoisoned m1 B0 B1.
  Proof. db_open CTX.
    intros m1 FI. open_fin FI. pose proof ab_app as BA.
    eapply unpoisoned_munch; [exact UB0 | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, KHIGH in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_unpL : forall m1, FIN m1 -> R0 < R1 -> unpoisoned m1 R0 R1.
  Proof. db_open CTX.
    intros m1 FI HL0. open_fin FI. pose proof ab_app as BA. pose proof (al_app HL0) as BL. destruct (arl_open HL0) as (ABL & UL0 & RL & RLS).
    eapply unpoisoned_munch; [exact UL0 | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, KHIGH in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_art : forall m1, FIN m1 -> art m1.
  Proof. db_open CTX.
    intros m1 FI. open_fin FI. pose proof ab_app as BA.
    eapply art_transport; [exact ART0| exact MU| exact WM|].
    unfold ablk, AIMG_HI, KLS, KHIGH in *. repeat constructor; cbn [fst]; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fin_rdl : forall m1, FIN m1 -> rdbl bsegs m1 R0 R1.
  Proof. db_open CTX.
    intros m1 FI. open_fin FI. destruct SRCB as [AP|[IN1 IN2]].
    - eapply rdbl_transport; [exact RDL| exact MU|]. intros x Hx. left. unfold apart in *. cbn. lia.
    - eapply rdbl_sub; [apply rdbl_of_stk; exact REG| lia| lia].
  Qed.
  Lemma fin_areg : forall m1, FIN m1 -> areg RNG m1 B0 (B1 - B0).
  Proof. db_open CTX.
    intros m1 FI _. split; [|split; [|split]]; [ replace (B0 + (B1 - B0)) with B1 by lia; exact ABB
      | replace (B0 + (B1 - B0)) with B1 by lia; exact (fin_unp _ FI) | exact RB | exact RBS ].
  Qed.
  Lemma fin_aro : forall m1 A n, FIN m1 -> B0 <= A -> 0 <= n -> A + n <= B1 -> aro RNG m1 A n.
  Proof. db_open CTX.
    intros m1 A n FI H1 H2 H3. pose proof (fin_unp _ FI) as U. split; [| split].
    - eapply unpoisoned_sub; [exact U| lia| lia].
    - eapply rng_sub; [exact RB| lia| lia].
    - eapply rng_sub; [exact RBS| |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_aroL : forall m1 A n, FIN m1 -> R0 <= A -> 0 < n -> A + n <= R1 -> aro RNG m1 A n.
  Proof. db_open CTX.
    intros m1 A n FI H1 H2 H3. pose proof (fin_unpL _ FI ltac:(lia)) as U. destruct (arl_open ltac:(lia)) as (ABL & UL0 & RL & RLS). split; [| split].
    - eapply unpoisoned_sub; [exact U| lia| lia].
    - eapply rng_sub; [exact RL| lia| lia].
    - eapply rng_sub; [exact RLS| |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fin_ahull : forall m1 A n, FIN m1 -> B0 <= A -> 0 <= n -> A + n <= B1 -> ahull RNG m1 A n.
  Proof. db_open CTX.
    intros m1 A n FI H1 H2 H3. open_fin FI. destruct HB as (RLO & RHI & C1 & C2 & C3 & C4 & C5 & C6 & W & R).
    exists RLO, RHI. split; [lia|]. split; [lia|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|].
    split; [eapply wr_at_transport; [exact W| exact WM] | exact R].
  Qed.
  Lemma fin_ahullL : forall m1 A n, FIN m1 -> R0 <= A -> 0 <= n -> A + n <= R1 -> ahull RNG m1 A n.
  Proof. db_open CTX.
    intros m1 A n FI H1 H2 H3. open_fin FI. destruct HL as (RLO & RHI & C1 & C2 & C3 & C4 & C5 & C6 & W & R).
    exists RLO, RHI. split; [lia|]. split; [lia|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|].
    split; [eapply wr_at_transport; [exact W| exact WM] | exact R].
  Qed.
  Lemma fin_app : forall A n, B0 <= A -> 0 <= n -> A + n <= B1 -> app_blk A (A + n).
  Proof. db_open CTX. intros A n H1 H2 H3. pose proof ab_app. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
         unfold ablk, AIMG_HI, KLS in ABB. unfold app_blk, KLOW, KHIGH, KEND, ASHOFF. lia. Qed.
  Lemma fin_appL : forall A n, R0 <= A -> 0 < n -> A + n <= R1 -> app_blk A (A + n).
  Proof. db_open CTX. intros A n H1 H2 H3. pose proof (al_app ltac:(lia)). pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
         destruct (arl_open ltac:(lia)) as (ABL & _). unfold ablk, AIMG_HI, KLS in ABL. unfold app_blk, KLOW, KHIGH, KEND, ASHOFF. lia. Qed.
  Lemma fin_stkD : forall m1 D n, FIN m1 -> B0 <= D -> 0 <= n -> D + n <= B1 -> stk bsegs m1 D (D + n).
  Proof. db_open CTX.
    intros m1 D n FI H1 H2 H3. open_fin FI.
    destruct (stk_split bsegs m1 B0 D B1 REG ltac:(lia)) as [_ Q2]. destruct (stk_split bsegs m1 D (D + n) B1 Q2 ltac:(lia)) as [Q3 _]. exact Q3.
  Qed.
  Lemma fin_rdblL : forall m1 A n, FIN m1 -> R0 <= A -> A + n <= R1 -> rdbl bsegs m1 A (A + n).
  Proof. db_open CTX. intros m1 A n FI H1 H2. eapply rdbl_sub; [exact (fin_rdl _ FI)| lia| lia]. Qed.
  Lemma fin_astk : astk RNG lo (SPV + -80).
  Proof. db_open CTX. split; [exact KLO|]. split; [eapply rng_sub; [exact RSTK| lia| lia] | exact RI]. Qed.
  Lemma fin_stk : forall m1, FIN m1 -> stk bsegs m1 lo (SPV + -80).  Proof. db_open CTX. intros m1 FI; open_fin FI; exact STK. Qed.
  Lemma fin_mi : forall m1, FIN m1 -> mem_inv bsegs m1.  Proof. db_open CTX. intros m1 FI; open_fin FI; exact MI. Qed.
  Lemma fin_after_call : forall m1 m2 D n, FIN m1 -> B0 <= D -> 0 <= n -> D + n <= B1 -> OP <= D -> D + n <= OP + LEN ->
    munch [(SPV + -80 - 2224, SPV + -80); (D, D + n)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
    stk bsegs m2 lo (SPV + -80) -> stk bsegs m2 D (D + n) -> FIN m2.
  Proof. db_open CTX.
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
    [ eapply (zd_memmoveZ_proofA RNG D S 16 (SPV + -80));
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
  Lemma db_epi : forall m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs7 xs8 x28 x29 x30 x31,
    FIN m1 -> evtF bsegs RNG POST (ST 0x96764 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof.
    db_open CTX. intros until x31. intros FI. pose proof (fin_rdl _ FI) as RD1. open_fin FI.
    kx_autoFLAx [KAApp (SPV - 80) 80] [] 20%nat [KZRange SPV 4096 (2^47); KZWr (SPV - 80) 80] [(SPV - 80, 80)] [(SPV - 80, 80)].
    all: try kx_z. all: try kx_acc RSTK.
    all: kx_mem. all: zstep.
    release_frame FR STK SPV.
    apply evtF_done. unfold zd_dbs_postA. do 15 eexists. exists m1.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|]. split; [exact REG| exact RD1].
  Qed.
  (* [comment removed for export] *)
  Lemma fin_bal : forall m1, FIN m1 -> exists bs, Z.of_nat (length bs) = R1 - R0 /\ bytes_at bsegs m1 R0 bs.
  Proof. db_open CTX.
    intros m1 FI. destruct (rdbl_bytes bsegs m1 R0 R1 (fin_rdl _ FI) ltac:(lia)) as (bs & BL & BA).
    exists bs. split; [lia| exact BA].
  Qed.

  (* [comment removed for export] *)
  Lemma db_tail_loop : forall (n : nat) m1 (X Y : Z) xra x5 x6 x7 xs1 xa5 xa6 xa7 xs2 xs3 xs6 xs7 xs8 x28 x29 x30 x31,
    OP + LEN - Y <= Z.of_nat n -> R0 <= X -> X - Y = IP - OP -> OP <= Y -> Y < OP + LEN -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x966f8 m1 xra x5 x6 x7 (Z_to_bv 64 X) xs1 (Z_to_bv 64 Y) (Z_to_bv 64 (OP + LEN - Y)) (Z_to_bv 64 2) (Z_to_bv 64 X) (Z_to_bv 64 Y)
                             xa5 xa6 xa7 xs2 xs3 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof. db_open CTX.
    induction n as [|n IH]; intros until x31; intros HN HX HPAR HOY HYE FI; [exfalso; lia|].
    pose proof (fin_unp _ FI) as UB1. pose proof (fin_unpL _ FI ltac:(lia)) as UL1. destruct (fin_bal _ FI) as (bs & BL & BA).
    destruct (arl_open ltac:(lia)) as (ABL & UL0 & RL & RLS).
    pose proof FI as FI1. open_fin FI. pose proof ab_app as BA'. pose proof (al_app ltac:(lia)) as BL'.
    kx_autoFLAx [KAUnp X 1; KAUnp Y 1; KAApp Y 1] [0x966f8; 0x96764] 40%nat
      [KZRange X 4096 (2^47 - 1); KZRange Y 4096 (2^47 - 1); KZRange (OP + LEN) 0 (2^47);
       KZRange (OP + LEN - Y) 1 (2^47); KZRange (X - R0) 0 (2^47); KZRange (R1 - X) 1 (2^47); KZWr Y 1]
      [(X, 1)] [(X, 1); (Y, 1)].
    all: try kx_z. all: try kx_acc RB. all: try kx_acc RL.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616340) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?C) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 616184) _ _ ?m2 _) =>   (* [comment removed for export] *)
             replace (Z_to_bv 64 C) with (Z_to_bv 64 (OP + LEN - (Y + 1))) by (f_equal; lia);
             apply (IH m2 (X + 1) (Y + 1)); try lia; fin_close
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616292) _ _ ?m2 _) =>       (* [comment removed for export] *)
             apply db_epi; fin_close
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma db_loopA : forall (n : nat) m1 (X Y : Z) xra x5 x6 x7 xs1 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs7 xs8 x28 x29 x30 x31,
    OP + LEN - Y <= Z.of_nat n -> R0 <= X -> X - Y = IP - OP -> OP <= Y -> Y < OP + LEN -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x96674 m1 xra x5 x6 x7 (Z_to_bv 64 X) xs1 (Z_to_bv 64 Y) (Z_to_bv 64 Y) (Z_to_bv 64 X) (Z_to_bv 64 2) xa4
                             xa5 xa6 xa7 xs2 xs3 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof. db_open CTX.
    induction n as [|n IH]; intros until x31; intros HN HX HPAR HOY HYE FI; [exfalso; lia|].
    pose proof (fin_unp _ FI) as UB1. pose proof (fin_unpL _ FI ltac:(lia)) as UL1. destruct (fin_bal _ FI) as (bs & BL & BA).
    destruct (arl_open ltac:(lia)) as (ABL & UL0 & RL & RLS).
    pose proof FI as FI1. open_fin FI. pose proof ab_app as BA'. pose proof (al_app ltac:(lia)) as BL'.
    kx_autoFLAx [KAUnp X 1; KAUnp Y 1; KAApp Y 1] [0x96674; 0x96764] 40%nat
      [KZRange X 4096 (2^47 - 1); KZRange Y 4096 (2^47 - 1); KZRange (OP + LEN) 0 (2^47);
       KZRange (OP + LEN - Y) 1 (2^47); KZRange (X - R0) 0 (2^47); KZRange (R1 - X) 1 (2^47); KZWr Y 1]
      [(X, 1)] [(X, 1); (Y, 1)].
    all: try kx_z. all: try kx_acc RB. all: try kx_acc RL.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616340) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616052) _ _ ?m2 _) =>   (* [comment removed for export] *)
             apply (IH m2 (X + 1) (Y + 1)); try lia; fin_close
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616292) _ _ ?m2 _) =>       (* [comment removed for export] *)
             apply db_epi; fin_close
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma db_tail : forall m1 (X Y : Z) xra x5 x6 x7 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs7 xs8 x28 x29 x30 x31,
    R0 <= X -> X - Y = IP - OP -> OP <= Y -> Y < OP + LEN -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x966e8 m1 xra x5 x6 x7 (Z_to_bv 64 X) xs1 (Z_to_bv 64 Y) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof. db_open CTX.
    intros until x31; intros HX HPAR HOY HYE FI. pose proof FI as FI1. open_fin FI.
    kx_autoFLAx (@nil kza) [0x966f8] 8%nat
      [KZRange OP 4096 (2^47); KZRange X 4096 (2^47); KZRange Y 4096 (2^47); KZRange (OP + LEN) 0 (2^47); KZRange (OP + LEN - Y) 1 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?C) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 616184) _ _ ?m2 _) =>
        replace (Z_to_bv 64 C) with (Z_to_bv 64 (OP + LEN - Y)) by (f_equal; lia);
        apply (db_tail_loop (Z.to_nat (OP + LEN - Y)) m2 X Y); try lia; fin_close
    end.
  Qed.

  (* [comment removed for export] *)
  Lemma db_wexit : forall m1 xra x5 x6 x7 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs8 x28 x29 x30 x31,
    32 <= LEN -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x96640 m1 xra x5 x6 x7 (Z_to_bv 64 IP) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                             xs2 xs3 (Z_to_bv 64 (OP + LEN - 32)) (Z_to_bv 64 (LEN - 32)) xs8 x28 x29 x30 x31).
  Proof. db_open CTX.
    intros until x31; intros HLEN FI. pose proof FI as FI1. open_fin FI.
    kx_autoFLAx (@nil kza) [0x966e8] 12%nat
      [KZRange IP 4096 (2^47); KZRange OP 4096 (2^47); KZRange (LEN - 32) 0 (2^47); KZRange (OP + LEN - 32) 4096 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616340) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_mem.
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ (Z_to_bv 64 ?CX) _ (Z_to_bv 64 ?CY) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 616168) _ _ ?m2 _) =>
        replace (Z_to_bv 64 CX) with (Z_to_bv 64 (IP + LEN - 32)) by (f_equal; lia);
        replace (Z_to_bv 64 CY) with (Z_to_bv 64 (OP + LEN - 32)) by (f_equal; lia);
        apply (db_tail m2 (IP + LEN - 32) (OP + LEN - 32)); try lia; fin_close
    end.
  Qed.

  (* [comment removed for export] *)
  Lemma db_w16_loop : forall (n : nat) m1 (D : Z) xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 x28 x29 x30 x31,
    OP + LEN - 32 - D <= Z.of_nat n -> OP + 16 <= D -> D < OP + LEN - 32 -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x965fc m1 xra x5 x6 x7 (Z_to_bv 64 IP) (Z_to_bv 64 (IP + (D - OP) + 16)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                             (Z_to_bv 64 D) xs3 (Z_to_bv 64 (OP + LEN - 32)) (Z_to_bv 64 (LEN - 32)) (Z_to_bv 64 18446744073709551599) x28 x29 x30 x31).
  Proof. db_open CTX.
    induction n as [|n IH]; intros until x31; intros HN HD HDE FI; [exfalso; lia|].
    pose proof FI as FI1. open_fin FI.
    kx_autoFLAx (@nil kza) (@nil Z) 10%nat [KZRange IP 4096 (2^47); KZRange D 4096 (2^47); KZRange (IP + (D - OP)) 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    all: replace (IP + (D + -1 * OP)) with (IP + (D - OP)) by lia.
    mm_callL FI1 D (IP + (D - OP)) FI2. clear FR STK MU WM REG; try clear MI. pose proof FI2 as FIo; open_fin FIo.
    kx_autoFLAx (@nil kza) (@nil Z) 10%nat [KZRange IP 4096 (2^47); KZRange D 4096 (2^47); KZRange (IP + (D - OP)) 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616340) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_mem.
    all: replace (IP + (D + -1 * OP) + 16) with (IP + (D - OP) + 16) by lia.
    mm_callL FI2 (D + 16) (IP + (D - OP) + 16) FI3. clear FR STK MU WM REG; try clear MI. pose proof FI3 as FIo; open_fin FIo.
    kx_autoFLAx (@nil kza) [0x965fc; 0x96640] 12%nat [KZRange IP 4096 (2^47); KZRange D 4096 (2^47); KZRange (IP + (D - OP)) 4096 (2^47); KZRange (OP + LEN - 32) 0 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616340) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_mem.
    all: lazymatch goal with
     | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?C1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 615932) _ _ ?m3 _) =>   (* [comment removed for export] *)
         replace (Z_to_bv 64 C1) with (Z_to_bv 64 (IP + ((D + 32) - OP) + 16)) by (f_equal; lia);
         apply (IH m3 (D + 32)); try lia; fin_close
     | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616000) _ _ ?m3 _) =>       (* [comment removed for export] *)
         apply (db_wexit m3); try lia; fin_close
     end.
  Qed.

  (* [comment removed for export] *)
  Lemma db_wild : forall m1 xra x5 x6 x7 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs7 xs8 x28 x29 x30 x31,
    32 <= LEN -> FIN m1 ->
    evtF bsegs RNG POST (ST 0x965c4 m1 xra x5 x6 x7 (Z_to_bv 64 IP) xs1 (Z_to_bv 64 OP) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                             xs2 xs3 (Z_to_bv 64 (OP + LEN - 32)) xs7 xs8 x28 x29 x30 x31).
  Proof. db_open CTX.
    intros until x31; intros HLEN FI. pose proof FI as FI1. open_fin FI.
    kx_autoFLAx (@nil kza) (@nil Z) 10%nat [KZRange IP 4096 (2^47); KZRange OP 4096 (2^47); KZRange (OP + LEN - 32) 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616340) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_mem.
    mm_callL FI1 OP IP FI2. clear FR STK MU WM REG; try clear MI. pose proof FI2 as FIo; open_fin FIo.
    kx_autoFLAx (@nil kza) [0x965fc; 0x96640] 14%nat [KZRange IP 4096 (2^47); KZRange OP 4096 (2^47); KZRange (LEN - 32) 0 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616340) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_mem.
    all: replace (LEN + -32) with (LEN - 32) by lia.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 615932) _ _ ?m3 _) =>   (* [comment removed for export] *)
             replace (Z_to_bv 64 (IP + 32)) with (Z_to_bv 64 (IP + ((OP + 16) - OP) + 16)) by (f_equal; lia);
             apply (db_w16_loop (Z.to_nat (LEN - 48)) m3 (OP + 16)); try lia; fin_close
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616000) _ _ ?m3 _) =>       (* [comment removed for export] *)
             apply (db_wexit m3); try lia; fin_close
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma db_shortE : forall m1 xra x5 x6 x7 xs1 xa1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs7 xs8 x28 x29 x30 x31,
    FIN m1 ->
    evtF bsegs RNG POST (ST 0x96664 m1 xra x5 x6 x7 (Z_to_bv 64 IP) xs1 (Z_to_bv 64 OP) xa1 (Z_to_bv 64 LEN) xa3 xa4 xa5 xa6 xa7
                             xs2 xs3 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof. db_open CTX.
    intros until x31; intros FI. pose proof FI as FI1. open_fin FI.
    kx_autoFLAx (@nil kza) [0x96674; 0x96764] 8%nat [KZRange IP 4096 (2^47); KZRange OP 4096 (2^47); KZRange LEN 0 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616052) _ _ ?m2 _) => apply (db_loopA (Z.to_nat LEN) m2 IP OP); try lia; fin_close
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616292) _ _ ?m2 _) => apply db_epi; fin_close
         end.
  Qed.
  (* [comment removed for export] *)
  Lemma db_tail0 : forall m1 xra x5 x6 x7 xs1 xa1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs7 xs8 x28 x29 x30 x31,
    FIN m1 ->
    evtF bsegs RNG POST (ST 0x966e4 m1 xra x5 x6 x7 (Z_to_bv 64 IP) xs1 (Z_to_bv 64 OP) xa1 (Z_to_bv 64 LEN) xa3 xa4 xa5 xa6 xa7
                             xs2 xs3 xs6 xs7 xs8 x28 x29 x30 x31).
  Proof. db_open CTX.
    intros until x31; intros FI. pose proof FI as FI1. open_fin FI.
    kx_autoFLAx (@nil kza) [0x966e8; 0x96764] 4%nat [KZRange LEN 0 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616168) _ _ ?m2 _) => apply (db_tail m2 IP OP); try lia; fin_close
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616292) _ _ ?m2 _) => apply db_epi; fin_close
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma db_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    stk bsegs m lo SPV -> stk bsegs m B0 B1 -> mem_inv bsegs m ->
    evtF bsegs RNG POST (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OP) (Z_to_bv 64 IP) (Z_to_bv 64 LEN) a3 a4
                                 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 APZD_DBS) fc None m (seg_rom bsegs)).
  Proof. db_open CTX.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST0 REG0 MI0.
    pose proof ART0 as (GOT & RIC & SHB & INI & LAY & REAL). pose proof ab_app as BA.
    assert (MU : munch [(OP, OP + LEN); (SPV - 2304, SPV)] m m) by apply munch_refl. assert (WM : wmono bsegs m m) by apply wmono_refl.
    carve_frame 80%nat ST0.
    unfold APZD_DBS.
    kx_autoFLAx [KAApp (SPV - 80) 80] [0x96664; 0x966e4; 0x965c4] 60%nat
      [KZRange SPV 4096 (2^47); KZRange IP 4096 (2^47); KZRange OP 4096 (2^47); KZRange LEN 0 (2^47); KZRange (OP + LEN) 4096 (2^47);
       KZWr (SPV - 80) 80]
      [(SPV - 80, 80)] [(SPV - 80, 80)].
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RSTK. all: try kx_acc RI.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616340) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_mem.
    all: try replace (OP + LEN + -32) with (OP + LEN - 32) by lia.
    all: lazymatch goal with
     | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616036) _ _ ?m2 _) => apply db_shortE; fin_close
     | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616164) _ _ ?m2 _) => apply db_tail0; fin_close
     | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 615876) _ _ ?m2 _) => apply db_wild; [lia | fin_close]
     end.
  Qed.
End DBS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem zd_dbs_proofA : zd_dbs_stmtA.
Proof.
  intros RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV lo OP IP LEN B0 B1 R0 R1.
  intros REG B0L B1H OPB LEN0 OPL RDL R0L R1H IPR IPL SRCB ST LOS SPV47 OFFB OFFR B01 ARB HB ARL HL ART AST MI -> -> ->.
  pose proof AST as (KLO & RSTK & RI). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  destruct (ARB ltac:(lia)) as (ABB & UB & RB & RBS). replace (B0 + (B1 - B0)) with B1 in ABB, UB by lia.
  unfold off_stack in OFFB, OFFR.
  apply (db_main RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP IP LEN B0 B1 R0 R1); try assumption.
  unfold db_ctx. repeat (split; [first [assumption | lia] |]). reflexivity.
Qed.
End CANSEC1.
