(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_NtStmt LbB_NtK LbB_NtD.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_HEmpD LbB_HEmpI LbB_HEmpS.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_INS : Z := 0xf5b30.

Lemma ntp_last_in : forall (T : Type) (l : list T) (x d : T), In (last (x :: l) d) (x :: l).
Proof.
  intros T l. induction l as [|y l IH]; intros x d; [left; reflexivity|].
  change (last (x :: y :: l) d) with (last (y :: l) d). right. apply IH.
Qed.

Lemma ntp_cellw_munch : forall (S : list Segment) (M M' : mem) (lo hi a : Z) (w : N) (v : Z),
  munch [(lo, hi)] M M' -> cellw S M a w v -> 0 <= a -> a + Z.of_N w <= 2 ^ 47 ->
  a + Z.of_N w <= lo \/ hi <= a -> cellw S M' a w v.
Proof.
  intros S M M' lo hi a w v HW C Ha Hb Hd.
  eapply cellw_agree; [exact C | | lia | lia].
  intros i Hi. apply HW. rewrite u64_of_Z by lia. cbn [outside]. split; [lia | exact I].
Qed.

Lemma ins_umapx : forall (LBl : list (Z * Z)) (m M1 : mem) (obj key p bl2 bc2 : Z) (l1 l2 : list (Z * (Z * (Z * Z * Z)))),
  umapx MI_A 32 (nval32 ASEGS) LBl m obj bl2 bc2 (l1 ++ l2) -> bc2 <> 0 -> Zlength (l1 ++ l2) + 1 <= bc2 -> 0 <= key < 2 ^ 32 ->
  In (p, 32) LBl -> 0 < p -> p + 32 <= 2 ^ 47 -> p mod 16 = 0 -> apart p 32 obj 40 ->
  (forall q n, In (q, n) (umap_blocks 32 bl2 bc2 (l1 ++ l2)) -> apart p 32 q n) ->
  mem_grows m M1 ->
  (forall a, umap_foot 32 obj bl2 bc2 (l1 ++ l2) a -> ~ (LbB_NtK.lasta (obj + 16) l1 <= a < LbB_NtK.lasta (obj + 16) l1 + 8) ->
             ~ (bl2 <= a < bl2 + 8 * bc2) -> M1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  cell8 ASEGS M1 p (hdaddr l2) -> cell8 ASEGS M1 (p + 8) key -> cell4 ASEGS M1 (p + 16) key ->
  cell4 ASEGS M1 (p + 20) 0 -> cell4 ASEGS M1 (p + 24) 0 -> cell4 ASEGS M1 (p + 28) 0 ->
  cell8 ASEGS M1 (LbB_NtK.lasta (obj + 16) l1) p ->
  (forall i, 0 <= i < bc2 -> exists b', cell8 ASEGS M1 (bl2 + 8 * i) b' /\ bucket_ok obj bc2 (l1 ++ (p, (key, (0, 0, 0))) :: l2) i b') ->
  forall M', munch [(obj + 24, obj + 32)] M1 M' -> mem_grows M1 M' ->
  cell8 ASEGS M' (obj + 24) (Zlength (l1 ++ l2) + 1) ->
  umapx MI_A 32 (nval32 ASEGS) LBl M' obj bl2 bc2 (l1 ++ (p, (key, (0, 0, 0))) :: l2).
Proof.
  intros LBl m M1 obj key p bl2 bc2 l1 l2 U Hbc Hload Hkr Hpl Hp0 Hpc Hpal Hpo Hpa HG1 HM1 Cn Ch Ck Ct Cw Ce Cpred HB
    M' HW HG2 Csz.
  pose proof U as U0.
  destruct U0 as [_ _ Holo Hohi _ _ _ _ Hbllo Hblhi Hblobj _ _ _ Hnode _].
  pose proof (Hbllo Hbc) as Hbl0. pose proof (Hblobj Hbc) as Hblo. unfold apart in Hblo, Hpo.
  assert (Hlast : 0 <= LbB_NtK.lasta (obj + 16) l1 /\ LbB_NtK.lasta (obj + 16) l1 + 8 <= 2 ^ 47
                  /\ (LbB_NtK.lasta (obj + 16) l1 + 8 <= obj + 24 \/ obj + 32 <= LbB_NtK.lasta (obj + 16) l1)).
  { destruct l1 as [|e l1']; cbn [LbB_NtK.lasta]; [lia|].
    match goal with |- context [last (e :: l1') ?d] =>
      pose proof (ntp_last_in _ l1' e d) as HI; revert HI; destruct (last (e :: l1') d) as [q [k v]]; intros HI end.
    cbn [fst].
    destruct (Hnode q k v (in_or_app _ _ _ (or_introl HI))) as (_ & Hq0 & Hq1 & _ & _ & _ & _ & _ & Hqo & _).
    unfold apart in Hqo. lia. }
  apply (LbB_NtK.umapx_link _ _ MI_A obj key LBl m M' p bl2 bc2 (0, 0, 0) l1 l2 U Hbc Hload Hkr Hpl Hp0 Hpc Hpal);
    [unfold apart; exact Hpo | exact Hpa | | | | | | | | |]; clear Hpal.
  - apply (ntp_cellw_munch _ M1 M' _ _ _ _ _ HW Cn); cbn [Z.of_N]; lia.
  - apply (ntp_cellw_munch _ M1 M' _ _ _ _ _ HW Ch); cbn [Z.of_N]; lia.
  - apply (ntp_cellw_munch _ M1 M' _ _ _ _ _ HW Ck); cbn [Z.of_N]; lia.
  - cbn [nval32]. split; [|split].
    + apply (ntp_cellw_munch _ M1 M' _ _ _ _ _ HW Ct); cbn [Z.of_N]; lia.
    + apply (ntp_cellw_munch _ M1 M' _ _ _ _ _ HW Cw); cbn [Z.of_N]; lia.
    + apply (ntp_cellw_munch _ M1 M' _ _ _ _ _ HW Ce); cbn [Z.of_N]; lia.
  - apply (ntp_cellw_munch _ M1 M' _ _ _ _ _ HW Cpred); cbn [Z.of_N]; lia.
  - exact Csz.
  - intros x Hx. apply HG2, HG1, Hx.
  - intros a Ha Hnl Hnsz Hnbl.
    assert (Har : 0 <= a < 2 ^ 47).
    { destruct Ha as [Ha|[[_ Ha]|[q [Hq Ha]]]]; [lia|lia|].
      apply in_map_iff in Hq. destruct Hq as [[q' [k v]] [Hq' Hin]]. cbn [fst] in Hq'. subst q'.
      destruct (Hnode q k v Hin) as (_ & Hq0 & Hq1 & _). lia. }
    rewrite (HW (Z_to_bv 64 a)) by (rewrite u64_of_Z by lia; cbn [outside]; split; [exact Hnsz | exact I]).
    apply HM1; assumption.
  - intros i Hi. destruct (HB i Hi) as [b' [Cb Hok]]. exists b'. split; [|exact Hok].
    apply (ntp_cellw_munch _ M1 M' _ _ _ _ _ HW Cb); cbn [Z.of_N]; lia.
Qed.

Lemma ncells_split : forall m A c1 c2 c3 c4 c5 c6, rw_cells asegs m A [C8 c1; C8 c2; C4 c3; C4 c4; C4 c5; C4 c6] ->
  rw_cells asegs m A [C8 c1] /\ rw_cells asegs m (A + 8) [C8 c2] /\ rw_cells asegs m (A + 16) [C4 c3]
  /\ rw_cells asegs m (A + 20) [C4 c4] /\ rw_cells asegs m (A + 24) [C4 c5] /\ rw_cells asegs m (A + 28) [C4 c6].
Proof.
  intros m A c1 c2 c3 c4 c5 c6 H.
  destruct (proj1 (rw_cells_app asegs m A [C8 c1] [C8 c2; C4 c3; C4 c4; C4 c5; C4 c6]) H) as [H1 R1].
  destruct (proj1 (rw_cells_app asegs m _ [C8 c2] [C4 c3; C4 c4; C4 c5; C4 c6]) R1) as [H2 R2].
  destruct (proj1 (rw_cells_app asegs m _ [C4 c3] [C4 c4; C4 c5; C4 c6]) R2) as [H3 R3].
  destruct (proj1 (rw_cells_app asegs m _ [C4 c4] [C4 c5; C4 c6]) R3) as [H4 R4].
  destruct (proj1 (rw_cells_app asegs m _ [C4 c5] [C4 c6]) R4) as [H5 H6].
  cbn [cells_size csize Nat.add] in H2, H3, H4, H5, H6. simpl Z.of_nat in H2, H3, H4, H5, H6.
  split; [exact H1|].
  split; [exact H2|].
  split; [replace (A + 16) with (A + 8 + 8) by lia; exact H3|].
  split; [replace (A + 20) with (A + 8 + 8 + 4) by lia; exact H4|].
  split; [replace (A + 24) with (A + 8 + 8 + 4 + 4) by lia; exact H5|].
  replace (A + 28) with (A + 8 + 8 + 4 + 4 + 4) by lia; exact H6.
Qed.

Definition srI : list expr :=
  srs sr_id [(9%bv, EVar 32); (15%bv, ELit SHBASE); (22%bv, EVar 36); (23%bv, EVar 33); (25%bv, EVar 34);
             (27%bv, EVar 35); (31%bv, ELit (2 ^ 60))].
Definition KNI : list kentry :=
  [KWord (SA (EVar 32) 640) 8 (EAlu ALU_SRL (EVar 34) (ELit 3)); KWord (SA (EVar 32) 592) 8 (LbB_NtD.shEe (EVar 33));
   KWord (SA (EVar 32) 616) 8 (ELit SHBASE); KWord (SA (EVar 32) 648) 8 (EAlu ALU_ADD (EVar 34) (ELit (-136)))].
Definition KNP0 : list kentry :=
  KNI ++ [KWr (SA (EVar 33) 0) (ELit 8); KWr (SA (EVar 38) 0) (ELit 8);
          KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672); KRange (EVar 34) 0x6e8000 (2 ^ 47 - 40);
          KRange (EVar 33) 0x6e8000 (2 ^ 47 - 32); KRange (EVar 38) 0x6e8000 (2 ^ 47 - 8)].
Definition SCR_PN := SCR [true; true; true; true; true; true] [EVar 37; EVar 38; EVar 39] [].

Ltac kni_tac obj S1 pp W640 W592 R616 R648 :=
  apply Forall_cons;
  [ eapply (kword_of_rw_cells _ _ _ _ _ 8%nat (C8 (Z_to_bv 64 (obj / 8))));
      [ exact W640 | reflexivity | reflexivity | lia
      | unfold SymExec3Sound.SX2S.estart; evs; rewrite ?HLib.u64_of_Z by lia; cbn [SymExec3.SX2.a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
      | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
      | cbn [cbytes]; evs; rewrite (LbB_HEmpS.srl3_val obj) by lia; reflexivity ] |];
  apply Forall_cons;
  [ eapply (kword_of_rw_cells _ _ _ _ _ 8%nat (C8 (Z_to_bv 64 (pp / 8 + SHBASE))));
      [ exact W592 | reflexivity | reflexivity | lia
      | unfold SymExec3Sound.SX2S.estart; evs; rewrite ?HLib.u64_of_Z by lia; cbn [SymExec3.SX2.a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
      | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
      | cbn [cbytes]; evs; rewrite (LbB_NtD.sh_word pp) by lia; reflexivity ] |];
  apply Forall_cons;
  [ eapply (kword_of_rw_cells _ _ _ _ _ 0%nat (C8 (Z_to_bv 64 SHBASE)));
      [ exact R616 | reflexivity | reflexivity | lia
      | unfold SymExec3Sound.SX2S.estart; evs; rewrite ?HLib.u64_of_Z by lia; cbn [SymExec3.SX2.a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
      | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
      | cbn [cbytes]; evs; reflexivity ] |];
  apply Forall_cons;
  [ eapply (kword_of_rw_cells _ _ _ _ _ 0%nat (C8 (Z_to_bv 64 (obj - 136))));
      [ exact R648 | reflexivity | reflexivity | lia
      | unfold SymExec3Sound.SX2S.estart; evs; rewrite ?HLib.u64_of_Z by lia; cbn [SymExec3.SX2.a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
      | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
      | cbn [cbytes]; evs; rewrite w_addm by lia; replace (obj + -136) with (obj - 136) by lia; reflexivity ] |].

Lemma ckT_align : forall M E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> a mod 8 = 0 ->
  sc_denot ASEGS M E (SCBr true BC_EQ (EAlu ALU_AND e (ELit 7)) (ELit 0)).
Proof.
  intros M E e a He Ha Hal. cbn [sc_denot]. cbn [edenot]. rewrite He.
  rewrite land7_val by lia. rewrite Hal. reflexivity.
Qed.

Lemma ckT_nz : forall M E e a, edenot E e = Z_to_bv 64 a -> 0 < a < 2 ^ 64 ->
  sc_denot ASEGS M E (SCBr true BC_NE e (ELit 0)).
Proof.
  intros M E e a He Ha. cbn [sc_denot]. rewrite He. cbn [edenot]. rewrite br_ne by lia.
  destruct (Z.eqb_spec a 0); [lia | reflexivity].
Qed.

Lemma ckT_geu : forall M E e1 e2 a b, edenot E e2 = Z_to_bv 64 a -> edenot E e1 = Z_to_bv 64 b ->
  0 <= a <= b -> b < 2 ^ 64 ->
  sc_denot ASEGS M E (SCBr true BC_GEU e1 e2).
Proof.
  intros M E e1 e2 a b H2 H1 Hab Hb. cbn [sc_denot]. rewrite H1, H2. rewrite br_geu by lia.
  destruct (Z.ltb_spec b a); [lia | reflexivity].
Qed.

Lemma ckT_srl : forall M E e a k, edenot E e = Z_to_bv 64 a -> 0 <= k < 64 -> 0 <= a < 2 ^ k ->
  sc_denot ASEGS M E (SCBr true BC_EQ (EAlu ALU_SRL e (ELit k)) (ELit 0)).
Proof.
  intros M E e a k He Hk Ha. cbn [sc_denot]. cbn [edenot]. rewrite He.
  assert (Ha64 : 0 <= a < 2 ^ 64) by (split; [lia|]; eapply Z.lt_le_trans; [apply (proj2 Ha)|]; apply Z.pow_le_mono_r; lia).
  rewrite HWord.w_srl by lia. rewrite (Z.div_small a (2 ^ k)) by lia. reflexivity.
Qed.

Lemma ckT_nulls : forall M E e1 e2 a b, edenot E e2 = Z_to_bv 64 a -> edenot E e1 = Z_to_bv 64 b ->
  0 < a < 2 ^ 64 -> 0 < b < 2 ^ 64 ->
  sc_denot ASEGS M E (SCBr true BC_NE (EAlu ALU_SLTU (ELit 0) e2) (EAlu ALU_SLTU e1 (ELit 1))).
Proof.
  intros M E e1 e2 a b H2 H1 Ha Hb. cbn [sc_denot]. cbn [edenot]. rewrite H1, H2.
  rewrite !HWord.w_sltu by lia.
  replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite br_ne by lia. reflexivity.
Qed.

Ltac sckT :=
  first [ eapply ckT_align; [LbB_HEmpS.sck_ev | lia | LbB_HEmpS.al8]
        | eapply ckT_nz; [LbB_HEmpS.sck_ev | lia]
        | eapply ckT_geu; [LbB_HEmpS.sck_ev | LbB_HEmpS.sck_ev | lia | lia]
        | eapply ckT_srl; [LbB_HEmpS.sck_ev | lia | lia]
        | eapply ckT_nulls; [LbB_HEmpS.sck_ev | LbB_HEmpS.sck_ev | lia | lia] ].

Lemma lasta_snocN : forall (l : list (Z * (Z * (Z * Z * Z)))) x t, LbB_NtK.lasta t (l ++ [x]) = fst x.
Proof.
  intros l x t. unfold LbB_NtK.lasta. destruct l as [|e l']; cbn [app]; [reflexivity|].
  rewrite app_comm_cons, last_last. reflexivity.
Qed.

Lemma in_fst_insN : forall (A B : list (Z * (Z * (Z * Z * Z)))) x y q,
  In q (map fst (A ++ x :: B)) -> In q (map fst ((A ++ [x]) ++ y :: B)).
Proof.
  intros A B x y q Hq. rewrite <- app_assoc. cbn [app]. rewrite map_app in *. cbn [map] in *.
  apply in_app_or in Hq. apply in_or_app.
  destruct Hq as [Hq | [Hq | Hq]]; [left; exact Hq | right; left; exact Hq | right; right; right; exact Hq].
Qed.

Lemma hdkey_snocN : forall (l1 l2 : list (Z * (Z * (Z * Z * Z)))) x y, hdkey ((l1 ++ [x]) ++ y :: l2) = hdkey (l1 ++ x :: l2).
Proof. intros l1 l2 x y. destruct l1; reflexivity. Qed.

Lemma lasta_cases : forall (l1 l2 : list (Z * (Z * (Z * Z * Z)))) t,
  l1 = [] /\ LbB_NtK.lasta t l1 = t \/ exists k v, In (LbB_NtK.lasta t l1, (k, v)) (l1 ++ l2).
Proof.
  intros l1 l2 t. destruct l1 as [|e l1']; [left; split; reflexivity | right].
  unfold LbB_NtK.lasta. destruct (last (e :: l1') (0, (0, (0, 0, 0)))) as [q [k v]] eqn:EL. exists k, v. cbn [fst].
  apply in_or_app; left. rewrite <- EL. apply LbB_HEmpI.last_in_ne. discriminate.
Qed.

Section NtI.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.
  Variables (gp tp s0 s4 ty wd enc : word) (S1 : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj key v408 v576 v624 : Z) (ents : list ent).
  Variables (bl bc lo B shi : Z) (m0 : mem) (mo0 : Model).

  Definition QI : config -> Prop :=
    QF H gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0.

  Definition IPRE (s : as_St H) (mo : Model) (m : mem) (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z)
      (ents2 : list ent) (rehashed : bool) (j584 : word) : Prop :=
    as_MPRES H mo0 mo
    /\ WSLOTS ty enc S1 obj m j584 (Z_to_bv 64 (p / 8 + SHBASE)) /\ nt_slots m S1 obj v408 v576 v624
    /\ 2 ^ 45 <= S1 /\ S1 + 672 <= 2 ^ 47 /\ 0 <= v408 < 2 ^ 64 /\ 0 <= v576 < 2 ^ 64 /\ 0 <= v624 < 2 ^ 64
    /\ mem_inv asegs m /\ stk asegs m lo (S1 + 672) /\ rw_cells asegs m (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m B
    /\ tp = Z_to_bv 64 ATP /\ aceil <= lo /\ lo <= S1
    /\ map_live_frame LF obj

    /\ umapx MI_A 32 (nval32 ASEGS) (lbl LB') m obj bl2 bc2 ents2 /\ umap_sh m 32 (bl2, bc2, ents2)
    /\ Permutation ents2 ents /\ bc2 <> 0 /\ Zlength ents + 1 <= bc2 /\ 0 <= key < 2 ^ 32
    /\ addressable m obj 40 /\ wr_at asegs m obj 40

    /\ 0 < p /\ p + 32 <= 2 ^ 47 /\ p mod 16 = 0 /\ apart p 32 obj 40
    /\ (forall q n, In (q, n) (umap_blocks 32 bl2 bc2 ents2) -> apart p 32 q n)
    /\ rw_cells asegs m p [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ addressable m p 32
    /\ (rehashed = false -> bl2 = bl /\ bc2 = bc) /\ (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc2 = bseq_next bc)
    /\ as_RHEAP H s LB' m /\ Permutation LB' (LB0 ++ LBm')
    /\ Permutation (lbl LBm') ((p, 32) :: umap_blocks 32 bl2 bc2 ents2)
    /\ lb_own LBm' m
    /\ xpres H LB0 S1 (nt_X S1 obj) m0 m
    /\ as_RFS H LF m /\ ACONST m /\ stack0 m lo shi
    /\ as_AL H s >= as_AL H sk0 - (if rehashed then ICM (8 * bc2) else 0).

  Definition ISTATE (msF : machine_state) (s : as_St H) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y28 y29 : word) (p bc2 idx : Z) : Prop :=
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 (Z_to_bv 64 SHBASE) y16 y17
                             y18 y19 s4 y21 (Z_to_bv 64 idx) (Z_to_bv 64 p) wd (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 24))
                             (Z_to_bv 64 bc2) y28 y29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60)))
                        F (Z_to_bv 64 E_INS) fc None m (seg_rom asegs).

  Lemma ins_post : forall (s : as_St H) (msF : machine_state) (mo : Model) (m M2 : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y22 y25 y27 y28 y29 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (l1 l2 : list ent) (rehashed : bool) (j584 : word) (W : list (Z * Z)),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 (Z_to_bv 64 SHBASE) y16 y17
                             y18 y19 s4 y21 y22 (Z_to_bv 64 p) wd y25 (Z_to_bv 64 (obj + 24)) y27 y28 y29
                             (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) y31)
                        F (Z_to_bv 64 E_END) fc None M2 (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPRE s mo m errv' LB' LBm' p bl2 bc2 (l1 ++ l2) rehashed j584 ->
    munch W m M2 -> wmono asegs m M2 -> mem_grows m M2 -> mem_inv asegs M2 -> stk asegs M2 lo (S1 + 672) ->
    Forall (fun iv => iv = (p, p + 8) \/ iv = (LbB_NtK.lasta (obj + 16) l1, LbB_NtK.lasta (obj + 16) l1 + 8)
                      \/ (bl2 <= fst iv /\ snd iv <= bl2 + 8 * bc2)) W ->
    rw_cells asegs M2 p [C8 (Z_to_bv 64 (hdaddr l2))] -> rw_cells asegs M2 (LbB_NtK.lasta (obj + 16) l1) [C8 (Z_to_bv 64 p)] ->
    (forall i, 0 <= i < bc2 -> exists b', cell8 ASEGS M2 (bl2 + 8 * i) b' /\ bucket_ok obj bc2 (l1 ++ (p, (key, (0, 0, 0))) :: l2) i b') ->
    as_SR H QI (mkCfg msF mo).
  Proof.
    intros s msF mo m M2 F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y22 y25 y27 y28 y29 y31
      errv' LB' LBm' p bl2 bc2 l1 l2 rehashed j584 W VIS FRZ KR IP MU2 WM2 MG2 MI2 ST2 FW Cn2 Cs2 CB2.
    destruct IP as (MP & WS & NS & SPL & SPH & V1 & V2 & V3 & MI & ST & ERR & RA & TPV & ACL & LOS & LFO & U2 & SH2 & PERM2 & BC2
                    & LOAD & KR32 & AD & WR & P0 & P1 & P16 & PO & PA & NC & ADP & CR3 & CR4 & RH & PE & PM & OWN & XP & RF & AC & S0 & AL).
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3).
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (u_obj_lo U2) as Ho0. pose proof (u_obj_hi U2) as Ho1. pose proof (u_obj_al U2) as Hoal.
    pose proof (u_bl_lo U2 BC2) as Hbl0. pose proof (u_bl_hi U2) as Hbl1. pose proof (u_bl_obj U2 BC2) as Hblo.
    pose proof (LbB_HFind.BSEQ_boundA bc2 (u_bseq U2)) as BCR.
    destruct (u_hdr U2) as [Cbl Cbc Cp1 Csz Cmlf Cdef].
    destruct SH2 as [SHb SHn]. unfold HStmts.t3a, HStmts.t3b, HStmts.t3c in SHb, SHn. cbn [Datatypes.fst Datatypes.snd] in SHb, SHn.
    assert (ZL : Zlength (l1 ++ l2) = Zlength ents) by (unfold Zlength; rewrite (Permutation_length PERM2); reflexivity).
    assert (ZL0 : 0 <= Zlength ents) by (unfold Zlength; lia).
    pose proof (ncells_split _ _ _ _ _ _ _ _ NC) as (NC0 & N8 & N16 & N20 & N24 & N28).
    pose proof PO as PO'. unfold apart in PO', Hblo.
    assert (INBL : In (bl2, 8 * bc2) (umap_blocks 32 bl2 bc2 (l1 ++ l2)))
      by (unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc2 0); [lia | left; reflexivity]).
    assert (PBL : p + 32 <= bl2 \/ bl2 + 8 * bc2 <= p) by (pose proof (PA bl2 (8 * bc2) INBL) as Hap; unfold apart in Hap; exact Hap).
    assert (INM : forall q n, In (q, n) (lbl LBm') -> exists qi, In (qi, q, n) LBm' /\ In (qi, q, n) LB'
                   /\ 0 < q /\ q mod 16 = 0 /\ AIMG_TOP <= q /\ q + n <= aceil /\ aapp q n).
    { intros q n Hq. destruct (lbl_in_inv LBm' q n Hq) as (qi & Qi).
      assert (QiL : In (qi, q, n) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact Qi).
      pose proof (ah_blocks H HH _ _ _ _ RH QiL) as (B0 & B16 & Bn & BI & BC & BF & BA).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in B0, B16, Bn, BI, BC, BF, BA.
      exists qi. repeat split; assumption. }
    destruct (INM p 32 (Permutation_in _ (Permutation_sym PM) (or_introl eq_refl))) as (qp & QPm & QPl & _ & _ & PIM & PCE & PAPP).
    destruct (INM bl2 (8 * bc2) (Permutation_in _ (Permutation_sym PM) (or_intror INBL))) as (qbl & QBm & QBl & _ & _ & BIM & BCE & BAPP).
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    assert (BW : forall q A N a1 a2, In (q, A, N) LB' -> A <= a1 -> a2 <= A + N ->
                 aclient_write_ok H LB' (a1, a2) /\ afs_write_ok H LF (a1, a2) /\ aconst_ok (a1, a2) /\ stack0_ok (a1, a2)
                 /\ (a2 <= ALOWSH_LO \/ AHI_LO <= a1)).
    { intros q A N a1 a2 Hq Ha1 Ha2. eapply LbB_NtD.blk_win; eassumption. }
    set (b0 := LbB_NtK.lasta (obj + 16) l1) in *.
    assert (B0C : b0 = obj + 16 \/
                  exists qb kb vb, In (qb, b0, 32) LBm' /\ In (qb, b0, 32) LB' /\ In (b0, (kb, vb)) (l1 ++ l2)
                                   /\ AIMG_TOP <= b0 /\ b0 + 32 <= aceil /\ aapp b0 32 /\ apart b0 32 obj 40 /\ apart p 32 b0 32).
    { destruct (lasta_cases l1 l2 (obj + 16)) as [[_ E0] | (kb & vb & Hin)]; [left; exact E0 | right].
      fold b0 in Hin.
      assert (INB : In (b0, 32) (umap_blocks 32 bl2 bc2 (l1 ++ l2))).
      { unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (b0, (kb, vb)). split; [reflexivity | exact Hin]. }
      destruct (INM b0 32 (Permutation_in _ (Permutation_sym PM) (or_intror INB))) as (qb & QB1 & QB2 & _ & _ & BB1 & BB2 & BB3).
      destruct (u_node U2 b0 kb vb Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & BOA & _).
      exists qb, kb, vb. split; [exact QB1|]. split; [exact QB2|]. split; [exact Hin|]. split; [exact BB1|].
      split; [exact BB2|]. split; [exact BB3|]. split; [exact BOA | exact (PA b0 32 INB)]. }
    assert (FWX : Forall (fun iv => aclient_write_ok H LB' iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv
                        /\ (snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) /\ wmix LBm' S1 (nt_X S1 obj) iv
                        /\ AIMG_TOP <= fst iv /\ snd iv <= aceil
                        /\ (snd iv <= obj + 24 \/ obj + 32 <= fst iv) /\ (snd iv <= p + 8 \/ p + 32 <= fst iv)) W).
    { eapply Forall_impl; [|exact FW]. intros iv [-> | [-> | (Hl & Hh)]].
      - destruct (BW qp p 32 p (p + 8) QPl ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4 & W5).
        split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
        split; [right; right; exists qp, p, 32; split; [exact QPm | cbn; lia]|].
        cbn [Datatypes.fst Datatypes.snd]. lia.
      - destruct B0C as [E0 | (qb & kb & vb & QB1 & QB2 & Hin & BB1 & BB2 & BB3 & BOA & BPA)].
        + rewrite E0. destruct (LbB_HEmpD.obj_window_ok H HH LF obj LB' m (obj + 16) (obj + 16 + 8) RF LFO ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4).
          split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|].
          split; [unfold aapp, aapp_lo, aapp_hi in VA; cbn [Datatypes.fst Datatypes.snd]; lia|].
          split; [right; left; intros a Ha; cbn [rin_ivs nt_X Datatypes.fst Datatypes.snd] in *; left; lia|].
          cbn [Datatypes.fst Datatypes.snd]. unfold AFS_SIZE in *. lia.
        + unfold apart in BOA, BPA.
          destruct (BW qb b0 32 b0 (b0 + 8) QB2 ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4 & W5).
          split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
          split; [right; right; exists qb, b0, 32; split; [exact QB1 | cbn; lia]|].
          cbn [Datatypes.fst Datatypes.snd]. lia.
      - destruct iv as [a1 a2]. cbn [Datatypes.fst Datatypes.snd] in Hl, Hh |- *.
        destruct (BW qbl bl2 (8 * bc2) a1 a2 QBl Hl Hh) as (W1 & W2 & W3 & W4 & W5).
        split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
        split; [right; right; exists qbl, bl2, (8 * bc2); split; [exact QBm | cbn; lia]|].
        lia. }
    assert (F1 : Forall (aclient_write_ok H LB') W) by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 X)).
    assert (F2 : Forall (afs_write_ok H LF) W) by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 X))).
    assert (F3 : Forall aconst_ok W) by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 (proj2 X)))).
    assert (F4 : Forall stack0_ok W) by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 (proj2 (proj2 X))))).
    assert (FAPP : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W)
      by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 (proj2 (proj2 (proj2 X)))))).
    assert (FMIX : Forall (wmix LBm' S1 (nt_X S1 obj)) W)
      by (eapply Forall_impl; [|exact FWX]; intros iv X; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 X))))))).
    assert (FDJ : forall a n, (a + n <= AIMG_TOP \/ aceil <= a \/ (obj + 24 <= a /\ a + n <= obj + 32) \/ (p + 8 <= a /\ a + n <= p + 32)) ->
                  disjoint_from W a n).
    { intros a n Hc. apply LbB_HEmpI.djI. eapply Forall_impl; [|exact FWX].
      intros iv (_ & _ & _ & _ & _ & _ & X1 & X2 & X3 & X4). lia. }
    destruct (client_frame H HH s LB' LF B W m M2 RH RF AC RA MU2 WM2 F1 F2 F3) as (RH2 & RF2 & AC2 & RA2).
    assert (S02 : stack0 M2 lo shi) by (eapply stack0_transport; [exact S0 | exact MU2 | exact WM2 | exact F4]).
    assert (ERR2 : rw_cells asegs M2 (errno_addr tp) [C4 errv']).
    { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
      eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 | apply FDJ; left; cbn; unfold ATP, AIMG_TOP; lia]. }
    assert (WS2 : WSLOTS ty enc S1 obj M2 j584 (Z_to_bv 64 (p / 8 + SHBASE))).
    { destruct WS as (W584 & W600 & W632 & W656). unfold WSLOTS, nt_wslots. split; [|split; [|split]];
        (eapply rw_cells_transport; [eassumption | exact MU2 | exact WM2 | apply FDJ; right; left; cbn; lia]). }
    assert (NS2 : nt_slots M2 S1 obj v408 v576 v624).
    { destruct NS as (R408 & R576 & R616 & R624 & R648). unfold nt_slots. split; [|split; [|split; [|split]]];
        (eapply rw_cells_transport; [eassumption | exact MU2 | exact WM2 | apply FDJ; right; left; cbn; lia]). }
    assert (ADO2 : addressable M2 obj 40)
      by (eapply addressable_transport; [exact AD | exact MU2 | exact WM2 | apply LbB_HEmpI.dsh_app; [exact FAPP | lia | lia | lia]]).
    assert (XP2 : xpres H LB0 S1 (nt_X S1 obj) m0 M2).
    { eapply (xpres_munch_mixed H HH s LB' LB0 LBm' S1 (nt_X S1 obj) W m0 m M2);
        [exact XP | exact RH | exact PE | lia | exact MU2 | exact WM2 | exact FMIX]. }
    assert (CSZ2 : rw_cells asegs M2 (obj + 24) [C8 (Z_to_bv 64 (Zlength ents))]).
    { rewrite <- ZL. eapply rw_cells_transport; [exact (rw_cells_of_cellw8 m (obj + 24) _ Csz ltac:(lia) ltac:(lia)) | exact MU2 | exact WM2 |].
      apply FDJ. right; right; left. cbn. lia. }
    assert (N82 : rw_cells asegs M2 (p + 8) [C8 (Z_to_bv 64 key)])
      by (eapply rw_cells_transport; [exact N8 | exact MU2 | exact WM2 | apply FDJ; right; right; right; cbn; lia]).
    assert (N162 : rw_cells asegs M2 (p + 16) [C4 (Z_to_bv 64 key)])
      by (eapply rw_cells_transport; [exact N16 | exact MU2 | exact WM2 | apply FDJ; right; right; right; cbn; lia]).
    assert (N202 : rw_cells asegs M2 (p + 20) [C4 (Z_to_bv 64 0)])
      by (eapply rw_cells_transport; [exact N20 | exact MU2 | exact WM2 | apply FDJ; right; right; right; cbn; lia]).
    assert (N242 : rw_cells asegs M2 (p + 24) [C4 (Z_to_bv 64 0)])
      by (eapply rw_cells_transport; [exact N24 | exact MU2 | exact WM2 | apply FDJ; right; right; right; cbn; lia]).
    assert (N282 : rw_cells asegs M2 (p + 28) [C4 (Z_to_bv 64 0)])
      by (eapply rw_cells_transport; [exact N28 | exact MU2 | exact WM2 | apply FDJ; right; right; right; cbn; lia]).
    assert (HFP : forall a, umap_foot 32 obj bl2 bc2 (l1 ++ l2) a -> ~ (p <= a < p + 32)).
    { intros a [Ha | [[Hbc Ha] | (q & Hq & Hqa)]] Hpa'.
      - lia.
      - lia.
      - apply in_map_iff in Hq. destruct Hq as ([z [k v]] & Hz & Hin). cbn in Hz. subst z.
        pose proof (PA q 32 ltac:(unfold umap_blocks; apply in_app_iff; right; apply in_map_iff; exists (q, (k, v)); split; [reflexivity | exact Hin])) as Hap.
        unfold apart in Hap. lia. }
    assert (HFR : forall a, umap_foot 32 obj bl2 bc2 (l1 ++ l2) a -> 0 <= a < 2 ^ 47).
    { intros a [Ha | [[Hbc Ha] | (q & Hq & Hqa)]]; [lia | lia |].
      apply in_map_iff in Hq. destruct Hq as ([z [k v]] & Hz & Hin). cbn in Hz. subst z.
      destruct (u_node U2 q k v Hin) as (_ & Hq0 & Hq1 & _). lia. }
    pose proof (proj1 Cp1) as Hfr.
    assert (B0R : 0 <= b0 /\ b0 + 8 <= 2 ^ 47).
    { destruct B0C as [E0 | (qb & kb & vb & _ & _ & Hin & _)]; [lia|].
      destruct (u_node U2 b0 kb vb Hin) as (_ & Hq0 & Hq1 & _). lia. }
    assert (HL2 : 0 <= hdaddr l2 < 2 ^ 64).
    { destruct l2 as [|[q [k v]] l2']; cbn [hdaddr]; [lia|].
      destruct (u_node U2 q k v ltac:(apply in_or_app; right; left; reflexivity)) as (_ & Hq0 & Hq1 & _). lia. }
    assert (HU : forall M', munch [(obj + 24, obj + 32)] M2 M' -> wmono asegs M2 M' ->
                   rw_cells asegs M' (obj + 24) [C8 (Z_to_bv 64 (Zlength ents + 1))] ->
                   umapx MI_A 32 (nval32 ASEGS) (lbl LB') M' obj bl2 bc2 (l1 ++ (p, (key, (0, 0, 0))) :: l2)).
    { intros M' MU' WM' CS'.
      exact (ins_umapx (lbl LB') m M2 obj key p bl2 bc2 l1 l2 U2 BC2 ltac:(rewrite ZL; lia) KR32 (lbl_in _ _ _ _ QPl) P0 P1 P16 PO PA MG2
        ltac:(intros a Ha Hnp Hnb; change (LbB_NtK.lasta (obj + 16) l1) with b0 in Hnp; pose proof (HFR a Ha) as Hr; pose proof (HFP a Ha) as Hnp';
              apply MU2; rewrite u64_of_Z by lia; apply LbB_HEmpI.outI; eapply Forall_impl; [|exact FW];
              intros iv [-> | [-> | (Hl & Hh)]]; cbn [Datatypes.fst Datatypes.snd]; lia)
        (cellw8_of_rw_cells M2 p (hdaddr l2) Cn2 HL2 ltac:(lia))
        (cellw8_of_rw_cells M2 (p + 8) key N82 ltac:(lia) ltac:(lia))
        (cellw4_of_rw_cells M2 (p + 16) key N162 KR32 ltac:(lia))
        (cellw4_of_rw_cells M2 (p + 20) 0 N202 ltac:(lia) ltac:(lia))
        (cellw4_of_rw_cells M2 (p + 24) 0 N242 ltac:(lia) ltac:(lia))
        (cellw4_of_rw_cells M2 (p + 28) 0 N282 ltac:(lia) ltac:(lia))
        (cellw8_of_rw_cells M2 b0 p Cs2 ltac:(lia) ltac:(lia))
        CB2 M' MU'
        (LbB_HEmpI.grows_of_munch_cell M2 M' (obj + 24) _ ltac:(replace (obj + 24 + 8) with (obj + 32) by lia; exact MU') CS'
           ltac:(lia) ltac:(lia))
        ltac:(rewrite ZL; exact (cellw8_of_rw_cells M' (obj + 24) (Zlength ents + 1) CS' ltac:(lia) ltac:(lia)))). }
    assert (SH2' : umap_sh M2 32 (bl2, bc2, l1 ++ (p, (key, (0, 0, 0))) :: l2)).
    { unfold umap_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c. cbn [Datatypes.fst Datatypes.snd]. split.
      - intros Hbc. eapply addressable_transport; [exact (SHb Hbc) | exact MU2 | exact WM2 | apply LbB_HEmpI.dsh_app; [exact FAPP | lia | lia | lia]].
      - intros q k v Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Hin | Hin]].
        + assert (Hin' : In (q, (k, v)) (l1 ++ l2)) by (apply in_or_app; left; exact Hin).
          destruct (u_node U2 q k v Hin') as (_ & Hq0 & Hq1 & _).
          eapply addressable_transport; [exact (SHn q k v Hin') | exact MU2 | exact WM2 | apply LbB_HEmpI.dsh_app; [exact FAPP | lia | lia | lia]].
        + injection Hin as E1 E2 E3. subst q. eapply addressable_transport; [exact ADP | exact MU2 | exact WM2 | apply LbB_HEmpI.dsh_app; [exact FAPP | lia | lia | lia]].
        + assert (Hin' : In (q, (k, v)) (l1 ++ l2)) by (apply in_or_app; right; exact Hin).
          destruct (u_node U2 q k v Hin') as (_ & Hq0 & Hq1 & _).
          eapply addressable_transport; [exact (SHn q k v Hin') | exact MU2 | exact WM2 | apply LbB_HEmpI.dsh_app; [exact FAPP | lia | lia | lia]]. }
    assert (NDR : forall q k v, In (q, (k, v)) (l1 ++ (p, (key, (0, 0, 0))) :: l2) -> 0 <= q /\ q + 32 <= 2 ^ 47).
    { intros q k v Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Hin | Hin]].
      - destruct (u_node U2 q k v ltac:(apply in_or_app; left; exact Hin)) as (_ & Hq0 & Hq1 & _); lia.
      - injection Hin as E1 E2 E3; subst q; lia.
      - destruct (u_node U2 q k v ltac:(apply in_or_app; right; exact Hin)) as (_ & Hq0 & Hq1 & _); lia. }
    assert (PM2 : Permutation (lbl LBm') (umap_blocks 32 bl2 bc2 (l1 ++ (p, (key, (0, 0, 0))) :: l2))).
    { eapply perm_trans; [exact PM|]. unfold umap_blocks. rewrite !map_app. cbn [map fst].
      rewrite !app_assoc. apply Permutation_middle. }
    assert (PERM3 : Permutation (l1 ++ (p, (key, (0, 0, 0))) :: l2) ((p, (key, (0, 0, 0))) :: ents)).
    { eapply perm_trans; [apply Permutation_sym, Permutation_middle | apply perm_skip; exact PERM2]. }
    unfold QI.
    eapply (LbB_NtD.stage_end H HH gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0
              s msF mo M2 F fc) with (LB' := LB') (LBm' := LBm') (p := p) (bl' := bl2) (bc' := bc2)
            (l1 := l1) (l2 := l2) (rehashed := rehashed) (j584 := j584);
      [ exact VIS | exact FRZ | exact KR | exact MP | exact WS2 | exact NS2 | exact SPL | exact SPH | exact V1 | exact V2 | exact V3
      | exact MI2 | exact ST2 | exact ERR2 | exact RA2 | exact TPV | exact LFO | exact Hoal | exact CSZ2 | lia | exact HU | exact SH2'
      | intros _; lia | exact NDR | exact PIM | exact P16 | exact ADO2 | exact (wr_at_wmono _ _ _ _ WR WM2) | exact PERM3
      | exact CR3 | exact CR4 | exact RH2 | exact PE | exact PM2 | exact (lb_own_wmono _ _ _ OWN WM2) | exact XP2
      | exact RF2 | exact AC2 | exact S02 | exact ACL | exact LOS | exact AL ].
  Qed.

  Lemma stage_ins_pn : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y28 y29 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (ents2 : list ent) (rehashed : bool) (j584 : word) (b : Z),
    ISTATE msF s m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y28 y29 p bc2 (hmod key bc2) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPRE s mo m errv' LB' LBm' p bl2 bc2 ents2 rehashed j584 ->
    cell8 ASEGS m (bl2 + 8 * hmod key bc2) b -> bucket_ok obj bc2 ents2 (hmod key bc2) b -> b <> 0 ->
    as_SR H QI (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y28 y29
      errv' LB' LBm' p bl2 bc2 ents2 rehashed j584 b VIS FRZ KR IP Cb Hbok Hbnz.
    unfold ISTATE in VIS.
    pose proof IP as IP0.
    destruct IP0 as (MP & WS & NS & SPL & SPH & V1 & V2 & V3 & MI & ST & ERR & RA & TPV & ACL & LOS & LFO & U2 & SH2 & PERM2 & BC2 & LOAD & KR32
                     & AD & WR & P0 & P1 & P16 & PO & PA & NC & ADP & CR3 & CR4 & RH & PE & PM & OWN & XP & RF & AC & S0 & AL).
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (u_obj_lo U2) as Ho0. pose proof (u_obj_hi U2) as Ho1. pose proof (u_obj_al U2) as Hoal.
    pose proof (u_bl_lo U2 BC2) as Hbl0. pose proof (u_bl_hi U2) as Hbl1. pose proof (u_bl_obj U2 BC2) as Hblo.
    pose proof (u_bl_al U2) as Hbla.
    pose proof (LbB_HFind.BSEQ_boundA bc2 (u_bseq U2)) as BCR.
    destruct (u_hdr U2) as [Cbl Cbc Cp1 Csz Cmlf Cdef].
    destruct SH2 as [SHb SHn]. unfold HStmts.t3a, HStmts.t3b, HStmts.t3c in SHb, SHn. cbn [Datatypes.fst Datatypes.snd] in SHb, SHn.
    pose proof PO as PO'. unfold apart in PO', Hblo.
    assert (INBL : In (bl2, 8 * bc2) (umap_blocks 32 bl2 bc2 ents2))
      by (unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc2 0); [lia | left; reflexivity]).
    assert (PBL : p + 32 <= bl2 \/ bl2 + 8 * bc2 <= p) by (pose proof (PA bl2 (8 * bc2) INBL) as Hap; unfold apart in Hap; exact Hap).
    assert (INM : forall q n, In (q, n) (lbl LBm') -> exists qi, In (qi, q, n) LBm' /\ In (qi, q, n) LB'
                   /\ 0 < q /\ q mod 16 = 0 /\ AIMG_TOP <= q /\ q + n <= aceil /\ aapp q n).
    { intros q n Hq. destruct (lbl_in_inv LBm' q n Hq) as (qi & Qi).
      assert (QiL : In (qi, q, n) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact Qi).
      pose proof (ah_blocks H HH _ _ _ _ RH QiL) as (B0 & B16 & Bn & BI & BC & BF & BA).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in B0, B16, Bn, BI, BC, BF, BA.
      exists qi. repeat split; assumption. }
    destruct (INM p 32 (Permutation_in _ (Permutation_sym PM) (or_introl eq_refl))) as (qp & QPm & QPl & _ & _ & PIM & PCE & PAPP).
    pose proof (lb_own_In LBm' m _ OWN QPm) as WRP. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in WRP.
    set (h := hmod key bc2) in *.
    assert (Hh : 0 <= h < bc2) by (subst h; unfold hmod; apply Z.mod_pos_bound; lia).
    assert (GZO : gz m obj 40) by (intros i Hi; eapply sh0_of_addressable; [exact AD | change (8 * (40 / 8)) with 40; lia]).
    assert (GZP : gz m p 32) by (intros i Hi; eapply sh0_of_addressable; [exact ADP | change (8 * (32 / 8)) with 32; lia]).
    assert (GZB : gz m bl2 (8 * bc2)).
    { apply LbB_HEmpI.gzA; [exact (SHb BC2) | rewrite Z.mul_comm, Z_mod_mult; reflexivity]. }
    assert (SPLIT : exists l1 l2, ents2 = l1 ++ l2 /\ LbB_NtK.lasta (obj + 16) l1 = b /\ cell8 ASEGS m b (hdaddr l2)
                     /\ AIMG_TOP <= b /\ b + 8 <= 2 ^ 47 /\ b mod 8 = 0 /\ gz m b 8 /\ wr_at asegs m b 8
                     /\ (p + 32 <= b \/ b + 8 <= p) /\ (bl2 + 8 * bc2 <= b \/ b + 8 <= bl2)
                     /\ (forall i, 0 <= i < bc2 -> exists b', cell8 ASEGS m (bl2 + 8 * i) b'
                                                    /\ bucket_ok obj bc2 (l1 ++ (p, (key, (0, 0, 0))) :: l2) i b')).
    { destruct Hbok as [Hb0 | [Hin | (Hbo & Hne & Hhk)]]; [exfalso; exact (Hbnz Hb0) | |].
      - destruct (LbB_HEmpS.in_split_entsS (Z * Z * Z) b ents2 Hin) as (l1 & k & v & l2 & Ee).
        assert (Hin' : In (b, (k, v)) ents2) by (rewrite Ee; apply in_or_app; right; left; reflexivity).
        destruct (u_node U2 b k v Hin') as (_ & Bq0 & Bq1 & Bq16 & _ & _ & _ & _ & BOA & BBL).
        assert (INB : In (b, 32) (umap_blocks 32 bl2 bc2 ents2)).
        { unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (b, (k, v)). split; [reflexivity | exact Hin']. }
        destruct (INM b 32 (Permutation_in _ (Permutation_sym PM) (or_intror INB))) as (qb & QB1 & QB2 & _ & _ & BB1 & BB2 & BB3).
        pose proof (lb_own_In LBm' m _ OWN QB1) as WRB. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in WRB.
        pose proof (PA b 32 INB) as PAB. unfold apart in PAB, BOA. specialize (BBL BC2). unfold apart in BBL.
        exists (l1 ++ [(b, (k, v))]), l2. split; [rewrite Ee, <- app_assoc; reflexivity|].
        split; [apply lasta_snocN|].
        split; [rewrite Ee in *; exact (LbB_HEmpI.chain_atA (Z * Z * Z) m l1 b k v l2 (u_chain U2))|].
        split; [lia|]. split; [lia|]. split; [apply LbB_HEmpS.al8_16; exact Bq16|].
        split; [intros i Hi; eapply sh0_of_addressable; [exact (SHn b k v Hin') | change (8 * (32 / 8)) with 32; lia]|].
        split; [exact (LbB_HEmpD.wr_at_subE m b 32 b 8 WRB ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [lia|]. split; [lia|].
        intros i Hi. destruct (u_bkt U2 i Hi) as (b' & Cb' & Hok'). exists b'. split; [exact Cb'|].
        rewrite Ee in Hok'. destruct Hok' as [H0 | [Hn | (Hs & Hne' & Hi')]]; [left; exact H0 | right; left | right; right].
        + apply in_fst_insN. exact Hn.
        + split; [exact Hs|]. split; [intros Hc; symmetry in Hc; exact (app_cons_not_nil _ _ _ Hc)|].
          rewrite hdkey_snocN. exact Hi'.
      - assert (Hbo' : b = obj + 16) by exact Hbo. subst b.
        exists [], ents2. split; [reflexivity|]. split; [reflexivity|].
        split; [exact Cp1|]. split; [unfold AIMG_TOP in *; lia|]. split; [lia|]. split; [LbB_HEmpS.al8|].
        split; [intros i Hi; replace (obj + 16 + i) with (obj + (16 + i)) by lia; apply GZO; lia|].
        split; [exact (LbB_HEmpD.wr_at_subE m obj 40 (obj + 16) 8 WR ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [lia|]. split; [lia|].
        intros i Hi. destruct (u_bkt U2 i Hi) as (b' & Cb' & Hok'). exists b'. split; [exact Cb'|].
        destruct Hok' as [H0 | [Hn | (Hs & Hne' & Hi')]]; [left; exact H0 | right; left | right; right].
        + cbn [app map fst]. right. exact Hn.
        + cbn [app]. split; [exact Hs|]. split; [discriminate|]. cbn [hdkey]. rewrite Hi', <- Hhk. reflexivity. }
    destruct SPLIT as (l1 & l2 & Ee & Lb & Cbn & Bim & Bhi & Bal & GZb & WRb & BP & BBL & BKT).
    pose proof (proj1 Cbn) as Hnr.
    assert (Bpos : 0 < b) by (unfold AIMG_TOP in Bim; lia).
    unfold cell8 in Cb, Cbn, Cbl.
    destruct WS as (W584 & W600 & W632 & W656).
    destruct NS as (R408 & R576 & R616 & R624 & R648).
    remember (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 (Z_to_bv 64 SHBASE) y16 y17
                  y18 y19 s4 y21 (Z_to_bv 64 h) (Z_to_bv 64 p) wd (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 24))
                  (Z_to_bv 64 bc2) y28 y29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60))) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 p; Z_to_bv 64 obj; Z_to_bv 64 bc2; Z_to_bv 64 h;
                        Z_to_bv 64 bl2; Z_to_bv 64 b; Z_to_bv 64 (hdaddr l2)]).
    assert (HR : regs_ok E srI R).
    { unfold srI. apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]).
      apply Forall_nil. }
    assert (HK : know_ok asegs E m (kn_fix 20 [E_END] SCR_PN E_INS srI KNP0 50)).
    { kn_eval. unfold know_ok.
      kni_tac obj S1 p W632 W584 R616 R648.
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WRP | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WRb | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 4 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; unfold AIMG_TOP in *; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R E_INS m (seg_rom asegs) HR HK 60%nat [E_END] SCR_PN 50%N.
    { split_scs; first [ sckT | sc_shdj
                       | eapply (sc_flat _ _ _ _ (8 * h + bl2)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | cbn; lia | lia | cbn; lia]
                       | eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cb); [cbn; lia | evs; rewrite w_mul, w_add, v_addi_Z by lia; f_equal; lia | evs; reflexivity]
                       | sc_rd Cbn | sc_rd Cbl ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M2 := mem_denot E m lg) in Hms end end.
    assert (MU2 : munch [(b, b + 8); (p, p + 8)] m M2).
    { subst M2. apply munch_mem_denot; [exact Hlf|].
      apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
                          cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; left; lia|].
      apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
                          cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; right; left; lia|].
      apply Forall_nil. }
    assert (WM2 : wmono asegs m M2) by (subst M2; apply wmono_mem_denot).
    assert (MG2 : mem_grows m M2) by (subst M2; apply mem_denot_grows).
    assert (MI2 : mem_inv asegs M2) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST2 : stk asegs M2 lo (S1 + 672)) by (subst M2; apply stk_mem_denot; exact ST).
    assert (WRp8 : wr_at asegs m p 8) by exact (LbB_HEmpD.wr_at_subE m p 32 p 8 WRP ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (Cs2 : rw_cells asegs M2 b [C8 (Z_to_bv 64 p)]) by (subst M2; rwc_new Hlf WRb).
    assert (Cn2 : rw_cells asegs M2 p [C8 (Z_to_bv 64 (hdaddr l2))]) by (subst M2; rwc_new Hlf WRp8).
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 9%bv G9. rreg HR' 15%bv G15. rreg HR' 23%bv G23.
    rewrite G9, G15, G23 in HRe.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    subst ents2.
    eapply (ins_post s msF1 mo1 m M2 F fc) with (l1 := l1) (l2 := l2) (W := [(b, b + 8); (p, p + 8)]) (j584 := j584);
      [ exact VIS1 | exact FRZ | exact KR1 | | exact MU2 | exact WM2 | exact MG2 | exact MI2 | exact ST2 | | | | ].
    - destruct IP as (MPx & IPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP1] | exact IPr].
    - rewrite Lb. apply Forall_cons; [right; left; reflexivity|]. apply Forall_cons; [left; reflexivity | apply Forall_nil].
    - exact Cn2.
    - rewrite Lb. exact Cs2.
    - intros i Hi. destruct (BKT i Hi) as (b' & Cb' & Hok'). exists b'. split; [|exact Hok'].
      eapply cellw_agree; [exact Cb' | | lia | cbn; lia]. intros j Hj.
      apply MU2. rewrite u64_of_Z by lia. cbn [outside]. split; [lia|]. split; [lia | exact I].
  Qed.
End NtI.
