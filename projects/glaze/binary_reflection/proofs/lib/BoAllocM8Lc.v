(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMHyp.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition malloc_cells (bt : as_boot) (TP TSDP PGP FL MIDEND : Z) : Prop :=
  In (0x10eebc, 4%nat, 30) (bt_consts bt)                      (* [comment removed for export] *)
  /\ In (0x105f08, 8%nat, 0x19fce8) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x19fd0a, 1%nat, 1) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x10ee98, 1%nat, 1) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x105ef8, 8%nat, PGP) (bt_consts bt)                  (* [comment removed for export] *)
  /\ In (PGP, 8%nat, 4096) (bt_consts bt)
  /\ In (0x10da20, 1%nat, 1) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x10da24, 4%nat, 0) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (TP - 88, 8%nat, TSDP) (bt_consts bt)                  (* [comment removed for export] *)
  /\ In (TSDP, 8%nat, bt_tctx bt) (bt_consts bt)               (* [comment removed for export] *)
  /\ In (0x190422, 1%nat, 0) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x10488, 8%nat, 0x0218a392cd3d5dbf) (bt_consts bt)    (* [comment removed for export] *)
  /\ In (0x104fc, 1%nat, 3) (bt_consts bt)                     (* [comment removed for export] *)
  /\ In (0x10600, 1%nat, 4) (bt_consts bt)                     (* [comment removed for export] *)
  /\ In (0x10629, 1%nat, 11) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x10b980, 2%nat, 16) (bt_consts bt)                   (* [comment removed for export] *)
  /\ In (0x10b982, 2%nat, 2048) (bt_consts bt)                 (* [comment removed for export] *)
  /\ In (0x10b978, 8%nat, 2 ^ 40) (bt_consts bt)               (* [comment removed for export] *)
  /\ In (0x10ab78, 8%nat, bt_spacebeg bt) (bt_consts bt)       (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ In (0x10da1c, 1%nat, 1) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x105f18, 8%nat, 0x10e1b8) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x105f20, 8%nat, 0x10eea8) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x10eea8, 8%nat, 0) (bt_consts bt)
  /\ In (0x105f28, 8%nat, 0x10eeb0) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x10eeb0, 8%nat, MIDEND) (bt_consts bt)
  /\ In (0x105f30, 8%nat, 0x10eea0) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x10eea0, 8%nat, 0x7fffffffffff) (bt_consts bt)
  /\ In (0x105f10, 8%nat, FL) (bt_consts bt)                   (* [comment removed for export] *)
  /\ In (FL + 85, 1%nat, 1) (bt_consts bt)                     (* [comment removed for export] *)
  /\ In (FL + 44, 4%nat, 4096) (bt_consts bt)                  (* [comment removed for export] *)
  /\ In (FL + 52, 4%nat, 0xbe) (bt_consts bt)                  (* [comment removed for export] *)
  /\ In (0x105f38, 8%nat, 0x107e58) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x107e58, 8%nat, 0xfc38c) (bt_consts bt)
  /\ In (0x106b70, 8%nat, 0x10) (bt_consts bt)                 (* [comment removed for export] *)
  /\ In (TP + 0x10, 4%nat, 0) (bt_consts bt)                   (* [comment removed for export] *)
  /\ In (0x103b0, 8%nat, MAGIC) (bt_consts bt)                 (* [comment removed for export] *)
  /\ In (0x19fc80, 8%nat, 0) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x19fce8 + 120, 8%nat, 18446744073709551615) (bt_consts bt)          (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ (0x10000 <= TSDP /\ TSDP + 8 <= 0x663000 /\ 0x10000 <= PGP /\ PGP + 8 <= 0x663000 /\ 0x10000 <= FL /\ FL + 4096 < 0x663000
      /\ 0 <= MIDEND < 2 ^ 64 /\ 0x10000 + 88 <= TP /\ TP + 0x40 <= 0x663000).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Xm (S T c p : Z) (z : Z) : Prop :=
  (S - 2480 <= z < S)
  \/ (T + T_PC + PC_SZ * c <= z < T + T_PC + PC_SZ * c + 4)
  \/ (T + 2784 <= z < T + 2792)
  \/ (p - 15 <= z < p - 8).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CHUNK.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)) (M : mem) (mdl : Model).
  Variables (n : Z) (ks : list Z) (k : Z).
  Hypothesis W : WF bt st Lc FF.
  Hypothesis RP : Rep bt st Lc FF M mdl.
  Hypothesis Hn : 1 <= n <= 64512.
  #[local] Abbreviation c := (class_of (needed n)).
  Hypothesis HC : a_cache st c = ks ++ [k].
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation ab := (chunk_of_compact (bt_spacebeg bt) (class_of (needed n)) k).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SG := (bt_segs bt).

  Lemma mc_needed : 24 <= needed n <= 65536 /\ needed n mod 8 = 0 /\ 1 <= c <= 30 /\ needed n <= csize c /\ is_primary n = true
                    /\ needed n = rounded n + rz n /\ Z.max n 8 <= rounded n <= Z.max n 8 + 7 /\ 16 <= rz n <= 1024.
  Proof using Hn.
    pose proof (rz_log_range n) as RL. pose proof (needed_facts n Hn) as [NB N8].
    assert (Hrz : 16 <= rz n <= 1024).
    { (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end). destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; lia. }
    assert (Hnd : needed n = rounded n + rz n) by reflexivity.
    assert (Hrd : Z.max n 8 <= rounded n <= Z.max n 8 + 7).
    { (lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia. }
    split; [exact NB|]. split; [exact N8|]. split; [apply class_of_range; lia|]. split; [apply csize_class_of; lia|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold is_primary in G in change_no_check G' end); apply Z.leb_le; lia|]. split; [exact Hnd|]. split; [exact Hrd | exact Hrz].
  Qed.

  Lemma mc_in : In k (a_cache st c).
  Proof using HC ks. rewrite HC. apply in_app_iff. right. left. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma mc_chunk :
    carved bt st c ab /\ AS_HEAPLO <= ab /\ ab + csize c <= CEIL /\ ab mod 16 = 0 /\ 0 <= k < 2 ^ 32
    /\ (ab + csize c <= T \/ T + PG <= ab)
    /\ (bt_tctx bt + 0x10000 <= ab \/ ab + csize c <= bt_tctx bt)
    /\ (forall p m, In (p, m) Lc -> ab + csize c <= p - 16 \/ p + up8 m <= ab)
    /\ (forall b, In b (a_tq st ++ a_gq st) -> ab + csize c <= ba_addr b \/ ba_addr b + BATCHSZ <= ab)
    /\ (forall z, ab <= z < ab + csize c -> lzb mdl z = false)
    /\ writableZ SG M ab (ab + csize c)
    /\ (forall z, ab <= z < ab + csize c -> rt_priv (bt_ia bt) Lc FF z).
  Proof using HC Hn RP W ks. pose proof mc_needed as (_ & _ & Hc & _). exact (OBL_cache_chunk_pf bt st Lc FF M mdl c k W RP Hc mc_in). Qed.

  (* [comment removed for export] *)
  Lemma mc_pclass :
    cellZ SG M (T + T_PC + PC_SZ * c) 4 (Z.of_nat (length ks) + 1)
    /\ cellZ SG M (T + T_PC + PC_SZ * c + 16 + 4 * Z.of_nat (length ks)) 4 k
    /\ (exists csz, cellZ SG M (T + T_PC + PC_SZ * c + 8) 8 csz)
    /\ Z.of_nat (length ks) + 1 <= 16.
  Proof using HC Hn RP W mdl FF Lc st RC.
    pose proof mc_needed as (_ & _ & Hc & _).
    destruct RP as (_ & _ & RT & _). destruct RT as (_ & _ & _ & _ & _ & _ & _ & PC & _).
    destruct (PC c Hc) as (X1 & X2 & X3 & X4). rewrite HC in X1, X4. rewrite length_app in X1. cbn [length] in X1.
    replace (Z.of_nat (length ks + 1)) with (Z.of_nat (length ks) + 1) in X1 by lia.
    split; [exact X1|]. split.
    - apply X4. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    - split; [wd_eexists; exact X3|].
      destruct W as (_ & WC & _). destruct (WC c Hc) as (L & _). rewrite HC, length_app in L. cbn [length] in L.
      assert (CM : cache_max c <= 16) by ((lazymatch goal with |- ?G => let G' := eval unfold cache_max, cache_hint in G in change_no_check G' end); lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_vs_node : forall id z, 1 <= id <= dp_nids (a_dep st) -> ab <= z < ab + csize c -> ~ foot_node bt (a_dep st) id z.
  Proof using HC Hn RP W ks mdl M FF Lc RC.
    intros id z Hid Hz HN. pose proof mc_needed as (_ & _ & Hc & _). pose proof mc_chunk as (CV & _).
    destruct (carved_range bt st Lc FF W c ab Hc CV) as (_ & _ & S1 & S2 & _).
    unfold foot_node in HN.
    destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & N1 & N2 & N3). pose proof (node_addr_block bt st id Hid) as Hbk.
    set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
    destruct HIn as [Eb | Hnb].
    - pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & INN & _) & _).
      rewrite Eb in INN. destruct (space_vs_fixed bt st Lc FF W _ _ INN ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)); unfold PG in *; lia.
    - destruct (space_vs_dyn bt st Lc FF W _ _ (node_dyn st bb Hnb)); unfold PG in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_T_stack_vs_node : forall id z, 1 <= id <= dp_nids (a_dep st) -> (T <= z < T + PG \/ CEIL <= z) -> ~ foot_node bt (a_dep st) id z.
  Proof using W FF Lc.
    intros id z Hid Hz HN. unfold foot_node in HN.
    destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & N1 & N2 & N3). pose proof (node_addr_block bt st id Hid) as Hbk.
    set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
    destruct (node_blocks_range bt st Lc FF W bb HIn) as (B1 & B2 & B3).
    destruct Hz as [Hz | Hz]; [| unfold CEIL, PG in *; lia].
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & _ & _ & _ & _ & INFS & INT & INN & _) & _).
    destruct HIn as [Eb | Hnb].
    - pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INT) (all_ranges_fixed bt st _ INN)
                    ltac:(intros EQ; injection EQ; intros; unfold PG in *; lia)) as D. hnf in D. cbn in D. rewrite <- Eb in *. unfold PG in *. lia.
    - pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT (node_dyn st bb Hnb)) as D. hnf in D. cbn in D. unfold PG in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_shadow_ab : exists b, byteZ SG M (SB + ab / 8) b /\ (b = FD \/ b = FA).
  Proof using HC Hn RP W ks mdl FF Lc st RC.
    pose proof mc_needed as (_ & _ & Hc & _). pose proof mc_chunk as (CV & A1 & A2 & A16 & _ & _ & _ & LIV & _).
    destruct (carved_range bt st Lc FF W c ab Hc CV) as (R1 & R2 & S1 & S2 & _).
    destruct W as ((WR & _) & _). destruct (WR c Hc) as (Q1 & _). 
    destruct RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RS & _). destruct RS as (SH1 & _).
    pose proof (csize_pos c Hc) as ((C1 & C2) & C3).
    assert (G : region_beg SBEG c / 8 <= ab / 8 < (region_beg SBEG c + r_mapped_user (a_reg st c)) / 8).
    { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). split; [apply Z.div_le_mono; lia | lia]. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (NL : ~ live_granule Lc (ab / 8)).
    { intros (p & m & Hin & G1 & G2). destruct (LIV p m Hin) as [D|D].
      - pose proof (live_range bt st Lc FF W p m Hin) as (_ & _ & Lm & Lp).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold up8 in D. lia.
      - pose proof (live_range bt st Lc FF W p m Hin) as (_ & _ & Lm & Lp). pose proof (up8_facts m ltac:(lia)) as (U1 & U2 & U3 & U4).
        unfold up8 in *. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    exists (if existsb (fun mn : Z * Z => ((fst mn + 16) / 8 <=? ab / 8) && (ab / 8 <? (fst mn + 16 + snd mn + 7) / 8))%bool (quar st) then FD else FA).
    split; [exact (SH1 c (ab / 8) Hc G NL)|]. destruct (existsb _ _); [left | right]; reflexivity.
  Qed.
End CHUNK.
End BoAllocMHyp.
Require Stdlib.NArith.NArith OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8Lk.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.AsanPlanSoundSums BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La.BoAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).


Section WithCeil.
Context {RC : run_ceil}.

(* [comment removed for export] *)
Definition pop_cells (bt : as_boot) : Prop :=
  In (0x10ab80, 4%nat, 0xffffffff) (bt_consts bt)               (* [comment removed for export] *)
  /\ In (0x10ab88, 8%nat, bt_spacebeg bt + KSPACE) (bt_consts bt) (* [comment removed for export] *)
  /\ In (0x10ab90, 1%nat, 0) (bt_consts bt)                      (* [comment removed for export] *)
  /\ In (0x19fdec, 1%nat, 0) (bt_consts bt)                      (* [comment removed for export] *)
  /\ In (0x19fd78, 8%nat, 0) (bt_consts bt).                     (* [comment removed for export] *)

Section POPKIT.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Variables (Y : Z -> Prop) (st : ast) (Lc FF : list (Z * Z)) (M M0 : mem) (mdl : Model).
  Hypothesis W : WF bt st Lc FF.
  Hypothesis RP : Rep bt st Lc FF M0 mdl.
  Hypothesis D : forall a : word, M a <> M0 a -> Y (U a) /\ M a <> None.
  Hypothesis YIMG : forall z, Y z -> ~ (AIMGLO <= z < AIMGHI).
  Hypothesis YCTX : forall z, Y z -> ~ (CTX + 152 <= z < CTX + 160).

  Lemma pk_def : forall a : word, M0 a <> None -> M a <> None.
  Proof using D Y.
    intros a H0. destruct (decide (M a = M0 a)) as [E | NE]; [rewrite E; exact H0 | exact (proj2 (D a NE))].
  Qed.

  Lemma pk_const : forall a (n : nat) v, In (a, n, v) (bt_consts bt) -> AIMGLO <= a -> a + Z.of_nat n <= AIMGHI ->
    rdn BSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
  Proof using YIMG D RP mdl M0 FF Lc st Y BT_segs RC.
    intros a n v Hin A0 A1. pose proof RP as (R1 & _). rewrite BT_segs in R1.
    apply (repx_rd Y M M0 D a n); [lia | lia | intros i Hi; intros HY; exact (YIMG i HY ltac:(lia)) | exact (const_cell bt M0 _ _ _ R1 Hin)].
  Qed.

  Lemma pk_shadow_def : forall z, shmaps z -> M (Z_to_bv 64 z) <> None.
  Proof using D RP mdl M0 FF Lc st Y bt RC.
    intros z Hz. apply pk_def. pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R15).
    destruct R15 as (_ & _ & _ & _ & SHD). first [exact (SHD z Hz) | exact (proj1 SHD z Hz)].   (* [comment removed for export] *)
  Qed.

  Lemma pk_thread_geom : 0 < T /\ T + 4096 <= CEIL /\ 0 < CTX /\ CTX + 0x10000 <= CEIL /\ T mod 4096 = 0
    /\ (T + 4096 <= AIMGLO \/ AIMGHI <= T) /\ (CTX + 0x10000 <= AIMGLO \/ AIMGHI <= CTX).
  Proof using W FF Lc st BT_ia.
    pose proof (fixed_facts bt st Lc FF W) as (T1 & T2 & C1 & C2 & _).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _).
    destruct WM as (RNG & _ & _ & _ & _ & _ & _ & INT & _ & _ & INC & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INT)) as ((D1 & D2 & D3 & D4 & D5) & _ & D6 & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INC)) as ((E1 & E2 & E3 & E4 & E5) & _).
    rewrite BT_ia in D4, E4. cbn [ia_img_lo ia_img_hi both_addrs] in D4, E4. unfold PG in *.
    repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pk_T_writable : writableZ BSEGS M T (T + 4096).
  Proof using D RP W mdl M0 FF Lc st Y BT_ia BT_segs RC.
    pose proof pk_thread_geom as (T1 & T2 & _). pose proof ceil_rng as CR.
    pose proof RP as (_ & _ & R3 & _). destruct R3 as (_ & _ & _ & _ & _ & _ & _ & _ & TW & _). rewrite BT_segs in TW. unfold PG in TW.
    apply (repx_wr Y M M0 D); [lia | lia | exact TW].
  Qed.

  (* [comment removed for export] *)
  Lemma pk_junk8 : forall lo hi z, writableZ BSEGS M lo hi -> lo <= z -> z + 8 <= hi -> 0 <= z -> hi < 2 ^ 64 ->
    exists v : word, rdn BSEGS M (Z_to_bv 64 z) 8 = Some (LE8 v).
  Proof using.
    intros lo hi z WR L H Z0 H1.
    destruct (rdn_defined_ex BSEGS M (Z_to_bv 64 z) 8) as (bs & Cbs & Lbs).
    { intros i Hi. rewrite u_Z2bv in Hi by lia. cbn in Hi. exact (proj1 (WR i ltac:(lia))). }
    { rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite Cbs. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Lbs | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma pk_poisonH : forall (slot : Z) (ra fsp : word),
    AS_HEAPLO <= slot -> slot + 2 ^ 18 <= CEIL -> slot mod 8 = 0 ->
    CEIL + 64 <= U fsp -> U fsp + 16 <= 2 ^ 47 -> writableZ BSEGS M (U fsp - 64) (U fsp) -> ret_ok ra ->
    poisonH BSEGS both_poison_tab M (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) ra fsp (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 0.
  Proof using YIMG D RP mdl M0 FF Lc st Y CELLS FL PGP TSDP TP BT_ia BT_segs bt.
    intros slot ra fsp S0 S1 S8 F0 F1 WST Hret. pose proof ceil_rng as CR. pose proof (u64_range fsp) as Hf.
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx
                      & CELL_rss & CELL_lmag & CELL_tbl2 & CELL_t16 & CELL_t2048 & CELL_minrz & CELL_maxrz & CELL_maxsz & CELL_sbeg
                      & CELL_cpm & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he & CELL_gfl & CELL_pp & CELL_mfs & CELL_fill
                      & CELL_grm & CELL_rm & CELL_glsn & CELL_lsn & CELL_magic & CELL_hook & CELL_thr64 & G_consts).
    assert (CSB : rdn BSEGS M (Z_to_bv 64 0x10e1b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000))).
    { pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R15). destruct R15 as (_ & _ & Csb & _).
      rewrite BT_ia, BT_segs in Csb. cbn [ia_rtc_sb both_addrs] in Csb. unfold SB in Csb.
      apply (repx_rd Y M M0 D 0x10e1b8 8); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; intros HY; exact (YIMG i HY ltac:(cbn in Hi; lia)) | exact Csb]. }
    unfold AS_HEAPLO in S0.
    split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_base pt_mset pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
    - exact (pk_const _ _ _ CELL_gsh ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact CSB.
    - exact (pk_const _ _ _ CELL_gmb ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_mb ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_gme ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_me ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_ghe ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_he ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_grm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - replace (word_to_le_bytes 8 (1033100 : word)) with (LE8 (Z_to_bv 64 0xfc38c)) by reflexivity.
      exact (pk_const _ _ _ CELL_rm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - vm_compute. discriminate.
    - apply ret_ok_even. reflexivity.
    - intros _. split; [| vm_compute; discriminate]. rewrite <- (w2b1 1) by lia. exact (pk_const _ _ _ CELL_cpm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - intros E0. exfalso. rewrite u_Z2bv in E0 by lia. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
      repeat (constructor; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]). constructor.
    - rewrite u_Z2bv by lia. exact S8.
    - rewrite u_Z2bv by lia. reflexivity.
    - left. rewrite !u_Z2bv by lia. lia.
    - lia.
    - apply (writableZ_sok M (U fsp - 64) (U fsp)); [exact WST | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end). rewrite !u_Z2bv by lia.
      assert (Q : 0x10007fff8000 / 8 <= slot / 8 /\ slot / 8 + 2 ^ 15 <= CEIL / 8).
      { split; [apply Z.div_le_mono; lia|]. replace (slot / 8 + 2 ^ 15) with ((slot + 2 ^ 18) / 8) by (rewrite <- (Z.div_add slot (2 ^ 15) 8) by lia; f_equal).
        apply Z.div_le_mono; lia. }
      assert (Q2 : CEIL / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
      assert (E1 : 0x10007fff8000 / 8 = 2199291686912) by reflexivity. assert (E2 : 0x7fffff800000 / 8 = 17592184995840) by reflexivity.
      rewrite E1 in Q. rewrite E2 in Q2.
      apply store_ok_of_all; [rewrite u_Z2bv by lia; change (2 ^ 18 / 8) with (2 ^ 15); rewrite Z2Nat.id by lia; lia|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. change (2 ^ 18 / 8) with (2 ^ 15) in Hx. rewrite Z2Nat.id in Hx by lia.
      assert (DEF : M x <> None).
      { rewrite <- (Z_to_bv_bv_unsigned _ x). apply pk_shadow_def. (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_GAPHI, AS_HEAPLO, AS_LO, AS_GAPLO in G in change_no_check G' end). right. lia. }
      (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (M x); [discriminate | exfalso; exact (DEF eq_refl)].
    - exact Hret.
  Qed.

  (* [comment removed for export] *)
  Lemma pk_gctH : forall (gsp tp : word), U tp = TP -> CEIL + 16 <= U gsp -> U gsp + 8 <= 2 ^ 47 -> writableZ BSEGS M (U gsp - 8) (U gsp) ->
    gctH BSEGS both_gct_tab M gsp tp (Z_to_bv 64 TSDP) (Z_to_bv 64 CTX) (Z_to_bv 64 T).
  Proof using YCTX YIMG D RP W mdl M0 FF Lc st Y CELLS MIDEND FL PGP BT_ia BT_segs.
    intros gsp tp Etp G0 G1 WST. pose proof ceil_rng as CR. pose proof (u64_range gsp) as Hg. pose proof (u64_range tp) as Htp.
    pose proof pk_thread_geom as (T1 & T2 & C1 & C2 & _).
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CREST).
    assert (G_consts : 0x10000 <= TSDP /\ TSDP + 8 <= 0x663000 /\ 0x10000 + 88 <= TP /\ TP + 0x40 <= 0x663000).
    { do 28 (destruct CREST as (_ & CREST)). destruct CREST as (A1 & A2 & _ & _ & _ & _ & _ & A8 & A9). repeat split; assumption. }
    destruct G_consts as (Gc1 & Gc2 & Gc8 & Gc9).
    pose proof RP as (_ & _ & R3 & _). destruct R3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Tback & _). rewrite BT_segs in Tback.
    split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end).
    - rewrite <- (w2b1 1) by lia. exact (pk_const _ _ _ CELL_kif ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - replace (at_ (Z_to_bv 64 0x10da20) 4) with (Z_to_bv 64 0x10da24 : word) by (apply bv_eq; reflexivity).
      exact (pk_const _ _ _ CELL_key ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - replace (at_ tp (-88)) with (Z_to_bv 64 (TP - 88)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia).
      exact (pk_const _ _ _ CELL_tsdp ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_tctx ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite (u_Z2bv CTX) by lia; reflexivity).
      apply (repx_rd Y M M0 D (CTX + 152) 8); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; intros HY; exact (YCTX i HY ltac:(cbn in Hi; lia)) | exact Tback].
    - rewrite u_Z2bv by lia. lia.
    - apply (writableZ_sok M (U gsp - 8) (U gsp)); [exact WST | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - lia.
    - rewrite u_Z2bv by lia. lia.
    - lia.
    - rewrite u_Z2bv by lia. lia.
    - rewrite u_Z2bv by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pk_thread_geom2 :
    (T + 4096 <= AS_LO \/ AS_HEAPLO <= T) /\ (CTX + 0x10000 <= AS_LO \/ AS_HEAPLO <= CTX)
    /\ (T + 4096 <= SBEG \/ SBEG + KSPACE + 4096 <= T) /\ (CTX + 0x10000 <= SBEG \/ SBEG + KSPACE + 4096 <= CTX)
    /\ 0 < SBEG /\ SBEG + KSPACE + 4096 <= CEIL /\ AS_HEAPLO <= SBEG.
  Proof using W FF Lc st.
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _).
    destruct WM as (RNG & _ & _ & _ & _ & _ & _ & INT & _ & _ & INC & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INT)) as ((D1 & D2 & D3 & D4 & D5) & _ & D6 & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INC)) as ((E1 & E2 & E3 & E4 & E5) & _).
    pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as TS.
    pose proof (space_vs_fixed bt st Lc FF W _ _ INC ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as CS.
    unfold PG in *. repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pk_nolazy_rt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> lzb mdl z = false.
  Proof using RP W M0 FF Lc st RC.
    intros z Hz. pose proof (free_obls_pf bt) as (OBL_nolazy_rt & _). unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt.
    apply (OBL_nolazy_rt st Lc FF M0 mdl z W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). tauto.
  Qed.
End POPKIT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MKH.
  Variable bt : as_boot.
  Hypothesis BT_ia : bt_ia bt = both_addrs.

  Lemma mkH_notlazy : forall (mdl : Model) (A : list (Z * Z)) z, 0 <= z < 2 ^ 64 -> lzb mdl z = false -> mkH (m_vm_lazy mdl) A (Z_to_bv 64 z) = false.
  Proof using. intros mdl A z Hz L. (lazymatch goal with |- ?G => let G' := eval unfold mkH in G in change_no_check G' end). unfold lzb in L. rewrite L. reflexivity. Qed.
  Lemma mkH_allowed : forall (L : list (word * word)) (A : list (Z * Z)) z, page_allowedb A (page_base (Z_to_bv 64 z)) = true -> mkH L A (Z_to_bv 64 z) = false.
  Proof using. intros L A z Ha. (lazymatch goal with |- ?G => let G' := eval unfold mkH in G in change_no_check G' end). rewrite Ha. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). apply andb_false_r. Qed.
  Lemma mkH_off_zone : forall st (mdl : Model) (A : list (Z * Z)) z, rep_ledger bt st mdl -> 0 <= z < 2 ^ 64 ->
    (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> mkH (m_vm_lazy mdl) A (Z_to_bv 64 z) = false.
  Proof using BT_ia.
    intros st mdl A z RL Hz Hr. apply mkH_notlazy; [exact Hz|]. destruct (lzb mdl z) eqn:E; [|reflexivity].
    exfalso. pose proof (lazy_zone bt st mdl z RL Hz E) as [Z1 Z2]. rewrite BT_ia in Z2. cbn [ia_img_lo ia_img_hi both_addrs] in Z2. lia.
  Qed.
  Lemma mkH_off_segments : forall st (mdl : Model) (A : list (Z * Z)), rep_ledger bt st mdl -> H_off_segments BSEGS (mkH (m_vm_lazy mdl) A).
  Proof using BT_ia.
    intros st mdl A RL a Ha. unfold mkH in Ha. apply andb_prop in Ha as [Ha _]. pose proof (u64_range a).
    assert (L : lzb mdl (U a) = true) by ((lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Z_to_bv_bv_unsigned; exact Ha).
    destruct (lazy_zone bt st mdl (U a) RL ltac:(lia) L) as [Z1 Z2]. rewrite BT_ia in Z2. cbn [ia_img_lo ia_img_hi both_addrs] in Z2.
    destruct (find_segment BSEGS (U a) 1) eqn:E; [|reflexivity]. exfalso. apply Z2. apply asanF_segs_hull. rewrite E. discriminate.
  Qed.
  (* [comment removed for export] *)
  Lemma lazy_cover_sub : forall (Hd : word -> bool) (lazy lazy' : list (word * word)) (A : list (Z * Z)),
    lazy_cover Hd lazy A -> (forall p, page_in_ranges p lazy' = true -> page_in_ranges p lazy = true) -> lazy_cover Hd lazy' A.
  Proof using. intros Hd lazy lazy' A LC SUB w Hl Hw. exact (LC w (SUB _ Hl) Hw). Qed.
End MKH.

(* [comment removed for export] *)
Lemma sh_band : forall p n, AS_HEAPLO <= p -> 0 <= n -> p + n <= CEIL -> n mod 8 = 0 ->
  AS_GAPHI <= SB + p / 8 /\ SB + p / 8 + n / 8 <= AS_HEAPLO /\ SB + p / 8 + n / 8 < CEIL.
Proof using.
  intros p n P0 N0 P1 N8. pose proof ceil_rng as CR. unfold AS_HEAPLO, AS_GAPHI, SB in *.
  assert (Q1 : 0x10007fff8000 / 8 <= p / 8) by (apply Z.div_le_mono; lia).
  assert (Q2 : (p + n) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  assert (Q3 : (p + n) / 8 = p / 8 + n / 8).
  { rewrite (Z.div_mod n 8) at 1 by lia. rewrite N8, Z.add_0_r. rewrite (Z.mul_comm 8), Z.div_add by lia. reflexivity. }
  assert (E1 : 0x10007fff8000 / 8 = 2199291686912) by reflexivity. assert (E2 : 0x7fffff800000 / 8 = 17592184995840) by reflexivity.
  rewrite E1 in Q1. rewrite E2 in Q2. lia.
Qed.
End WithCeil.
End BoAllocM8Lk.
Require Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8kh.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33.AsKSys3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvIStrlen.Bo_code_80b0c_815a0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1h.
Context {fx : FPState}.

Section MAPKH.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.

  Theorem rarmap_katsD_h :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v addr size name : word) (PGP CF : Z) (Qok Qf : config -> Prop)
           (MOK MKP : Model -> Model),
    let M1 := mfi_m1 mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := LE4 0xffffffffaaaaaaaa in
    (* [comment removed for export] *)
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 11 = addr -> getr regs 12 = size -> getr regs 13 = name ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra ->
    U addr mod 4096 = 0 -> (U size mod 4096 = 0 /\ U size + 4096 < 2 ^ 63) -> U name <> 0 ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok BSEGS mem (at_ sp (-400)) 400 = true ->
    rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0] ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    (* [comment removed for export] *)
    (AIMGHI <= U addr /\ U addr + U size < 2 ^ 63 /\ (U addr + U size <= U sp - 400 \/ U sp <= U addr)) ->
    (* [comment removed for export] *)
    hid_off Hd 0x105ef8 8 -> hid_off Hd PGP 8 -> hid_off Hd 0x105f08 8 -> hid_off Hd (CF + 260) 1 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd (U sp - 400) 400 ->
    (* [comment removed for export] *)
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (* [comment removed for export] *)
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = addr -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD BSEGS (mkCfg (mkst (regupd r1 10 addr) (0x811b0 : word) (zfill addr size M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf') ->
    (* [comment removed for export] *)
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        mfi_ret regs r' sp ra s0v s1v s2v s3v s4v addr ->
        katwD BSEGS (mkCfg (mkst r' ra (wbytes (zfill addr size M1) (at_ sp (-84)) SCR) rom) mdl4) Qok Qf) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl4 -> MInv A mdl4 ->
        mfi_ret regs r' sp ra s0v s1v s2v s3v s4v (Z_to_bv 64 0) ->
        katD BSEGS (mkCfg (mkst r' ra (wbytes (wbytes M1 (at_ sp (-84)) SCR) (at_ sp (-84)) (LE4 12)) rom) mdl4) Qf) ->
    katsD BSEGS (mkCfg (mkst regs (0x8b0f8 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v addr size name PGP CF Qok Qf MOK MKP M1 ENOMEMw SCR
           H1 H2 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Hret Haddr Hsize Hname HPGP HCF Hstk Rgpg Rpg Rgcf Rdpm Rlim
           Hslot HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD CONTOK CONTKP.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range addr) as Har. pose proof (u64_range size) as Hszr.
    destruct Hslot as (SL1 & SL2 & SL3). destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2].
    (* [comment removed for export] *)
    assert (Hstk' : store_ok BSEGS (mrestrict Hd mem) (at_ sp (-400)) 400 = true).
    { rewrite store_ok_mrestrict; [exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HDscr]. }
    assert (CELLR : forall (c : Z) (k : nat) v, 0 <= c < 2 ^ 32 -> Z.of_nat k <= 8 -> hid_off Hd c (Z.of_nat k) ->
               rdn BSEGS mem (Z_to_bv 64 c) k = Some v -> rdn BSEGS (mrestrict Hd mem) (Z_to_bv 64 c) k = Some v).
    { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (mfi_pre (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v addr size name PGP CF regs
                H1 H2 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Haddr Hsize Hname (conj PG1 PG2) (conj CF1 CF2) Hstk'
                (CELLR 0x105ef8 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgpg Rgpg) (CELLR PGP 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpg Rpg)
                (CELLR 0x105f08 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLR (CF + 260) 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDdpm Rdpm))
      as (r1 & RUN1 & B1 & B2 & B8 & B9 & B18 & B19 & B20 & B10 & B11 & B12 & B13 & B14 & B15 & B17 & AG1).
    assert (EM1 : mfi_m1 (mrestrict Hd mem) sp ra s0v s1v s2v s3v s4v s5v addr size name PGP = mrestrict Hd M1).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1, mfi_m1, mfi_m0 in G in change_no_check G' end).
      rewrite !wbytes_mrestrict; [reflexivity | ..];
        wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | intros x Hx; apply HDscr; lia]. }
    rewrite EM1 in RUN1.
    assert (M1hid : forall a : word, Hd a = true -> M1 a = mem a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mfi_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP Hsp).
      destruct (Z_lt_le_dec (U a) (U sp - 400)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katsD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst regs (0x8b0f8 : word) mem rom)
             (mkst r1 (0x811ac : word) (mrestrict Hd M1) rom) model Qok Qf LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN1. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x8b0f8 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M1 M1hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    (* [comment removed for export] *)
    apply (katsD_ecall BSEGS r1 (0x811ac : word) M1 rom mdlm W_811ac Qok Qf HALTm F_811ac E_811ac).
    rewrite B17.
    destruct (CHILD mdlm SBMm MIm) as ((HOK1 & HOK2 & HOK3) & _).
    (* [comment removed for export] *)
    assert (POSTF : forall MZ : word -> option byte,
               (forall x : word, U sp - 400 <= U x < U sp -> MZ x = M1 x) ->
               store_ok BSEGS (mrestrict Hd MZ) (at_ sp (-84)) 4 = true
               /\ (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, Z_to_bv 64 0x8b124); (-48, size);
                                                         (-56, addr); (-64, s2v); (-72, s3v); (-80, s4v)] ->
                      rdn BSEGS (mrestrict Hd MZ) (at_ sp k) 8 = Some (LE8 v))).
    { intros MZ EZ. split.
      - rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
        rewrite (store_ok_ext BSEGS 4 M1 MZ); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia].
        eapply store_ok_mono; [apply mfi_m1_grows|].
        eapply (store_ok_sub BSEGS mem (at_ sp (-400)) _ 400); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
      - intros k v Hin.
        assert (Hk : -80 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        rewrite rdn_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
        rewrite <- (mfi_m1_slots mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP Hsp k v Hin). fold M1.
        apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply EZ; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Q1 : forall v : word, getr (regupd r1 10 v) 1 = Z_to_bv 64 0x82f6c) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B1).
    assert (Q2 : forall v : word, getr (regupd r1 10 v) 2 = at_ sp (-128)) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B2).
    assert (Q8 : forall v : word, getr (regupd r1 10 v) 8 = size) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B8).
    assert (Q9 : forall v : word, getr (regupd r1 10 v) 9 = Z_to_bv 64 1) by (intros v; rewrite getr_other by (intros E; discriminate E); exact B9).
    assert (Q10 : forall v : word, getr (regupd r1 10 v) 10 = v) by (intros v; rewrite getr_same by (intros E; discriminate E); reflexivity).
    assert (AGC : forall (v : word) (r2 : bvmap 5 word), regs_agree (fun i : reg => In i mfi_clob2) (regupd r1 10 v) r2 ->
                    regs_agree (fun i : reg => In i mfi_clob2) regs r2).
    { intros v r2 AG2 x Hx. rewrite (AG2 x Hx).
      assert (NE10 : x <> 10%bv) by (intros ->; apply Hx; (lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]).
      rewrite getr_other by (intros E; apply NE10; exact E). apply AG1. exact Hx. }
    assert (HIDW : forall (MM : word -> option byte) bs (a : word), Hd a = true -> Z.of_nat (length bs) = 4 -> wbytes MM (at_ sp (-84)) bs a = MM a).
    { intros MM bs a Ha Hl.
      destruct (Z_lt_le_dec (U a) (U sp - 84)) as [C|C]; [apply wbytes_below; rewrite ?Hl, ?at_u by lia; lia|].
      destruct (Z_lt_le_dec (U a) (U sp - 80)) as [C'|C']; [exfalso; rewrite (HDscr a) in Ha by lia; discriminate Ha|].
      apply wbytes_above. rewrite Hl, at_u by lia. lia. }
    apply (NODE mdlm r1 SBMm MIm HALTm B10 B11 B12 B13 B14 B15 Qok Qf).
    - (* [comment removed for export] *)
      set (MZ := zfill addr size M1).
      assert (EZ : forall x : word, U sp - 400 <= U x < U sp -> MZ x = M1 x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end); apply zfill_out; lia).
      destruct (POSTF MZ EZ) as [SOKZ SLZ].
      assert (CELLZ : forall (c : Z) (k : nat) v, 0 <= c -> c + Z.of_nat k <= AIMGHI -> hid_off Hd c (Z.of_nat k) ->
                 rdn BSEGS mem (Z_to_bv 64 c) k = Some v -> rdn BSEGS (mrestrict Hd MZ) (Z_to_bv 64 c) k = Some v).
      { intros c k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [| first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh].
        rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        (lazymatch goal with |- ?G => let G' := eval unfold MZ in G in change_no_check G' end). rewrite zfill_out by lia. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply (mfi_m1_outside mem sp ra s0v s1v s2v s3v s4v s5v addr size name PGP Hsp). left. lia. }
      destruct (mfi_ok (mrestrict Hd MZ) rom sp ra s0v s1v s2v s3v s4v addr size CF (regupd r1 10 addr)
                  (Q1 addr) (Q2 addr) (Q8 addr) Hsp Hret (conj CF1 CF2) SOKZ
                  (SLZ (-8) ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-16) s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-24) s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])))
                  (SLZ (-32) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-40) (Z_to_bv 64 0x8b124) ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-48) size ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])))
                  (SLZ (-56) addr ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-64) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-72) s3v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]))) (SLZ (-80) s4v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])))
                  (Q10 addr) ltac:(lia) ltac:(lia)
                  (CELLZ 0x105f08 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDgcf Rgcf) (CELLZ (CF + 144) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDlim Rlim))
        as (r2 & RUN2 & C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & AG2).
      rewrite wbytes_mrestrict in RUN2; [| rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                          | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      apply (katwD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst (regupd r1 10 addr) (0x811b0 : word) MZ rom)
               (mkst r2 ra (mrestrict Hd (wbytes MZ (at_ sp (-84)) SCR)) rom) (MOK mdlm) Qok Qf HOK2 AWF HOK3 HOK1).
      { rewrite mk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst (regupd r1 10 addr) (0x811b0 : word) MZ rom)) with MZ by reflexivity.
      rewrite (mk_munrestrict_same Hd MZ (wbytes MZ (at_ sp (-84)) SCR)).
      2:{ intros a Ha. apply HIDW; [exact Ha | (lazymatch goal with |- ?G => let G' := eval unfold SCR in G in change_no_check G' end); rewrite length_N_to_le_bytes; reflexivity]. }
      apply (CONTOK r2 mdlm mdl4 SBMm MIm SBM4 MI4).
      (lazymatch goal with |- ?G => let G' := eval unfold mfi_ret in G in change_no_check G' end). repeat (split; [assumption|]). exact (AGC addr r2 AG2).
  Qed.

End MAPKH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NODE2H.

  (* [comment removed for export] *)
  Lemma node1_of_fixfree2_s :
    forall (r1 : bvmap 5 word) (M1 rom : word -> option byte) (mdlm : Model) (addr size : word) (Qok' Qf' : config -> Prop),
    m_halted mdlm = None ->
    getr r1 10 = addr -> getr r1 11 = size -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
    getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
    U addr mod 4096 = 0 -> 0 < U addr -> 0 < U size -> U size mod 4096 = 0 ->
    U addr + U size <= alloc_top (m_vmmaps mdlm) -> alloc_top (m_vmmaps mdlm) < two_pow_64 ->
    region_free (vm_reserved (m_vmmaps mdlm) ++ vm_maps (m_vmmaps mdlm)) addr size = true ->
    mmap_noreserve_backed_ok (Z_to_bv 64 50) mdlm (U size) = true ->
    katwD BSEGS (mkCfg (mkst (regupd r1 10 addr) (0x811b0 : word) (zfill addr size M1) rom)
                      (with_mmap_backing (Z_to_bv 64 50) addr size (mmap_model addr size mdlm))) Qok' Qf' ->
    katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Proof using.
    intros r1 M1 rom mdlm addr size Qok' Qf' HALT B10 B11 B12 B13 B14 B15 Hal Hpos Hsz Hszal Htop Htop64 Hrf Hbk KOK.
    pose proof (u64_range size) as Hszr.
    set (ms := epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)).
    assert (PRU : page_round_up_Z (U size) = U size) by (apply page_round_up_Z_aligned; [lia | (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact Hszal]).
    assert (EN : Z_to_bv 64 (page_round_up_Z (U size)) = size) by (rewrite PRU; apply Z_to_bv_bv_unsigned).
    assert (E0 : ms_gpr ms 0 = addr) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend0; exact B10).
    assert (E1 : ms_gpr ms 1 = Z_to_bv 64 (U size)) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend1, Z_to_bv_bv_unsigned; exact B11).
    assert (E2 : ms_gpr ms 2 = Z_to_bv 64 3) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend2; exact B12).
    assert (E3 : ms_gpr ms 3 = Z_to_bv 64 50) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend3; exact B13).
    assert (E4 : ms_gpr ms 4 = Z_to_bv 64 (-1)) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend4, B14; apply bv_eq; reflexivity).
    assert (E5 : ms_gpr ms 5 = Z_to_bv 64 0) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend5; exact B15).
    apply katsD_of_katwD.
    apply (katwD_node BSEGS _ _ tt _ Qok' Qf'
             (node_mmap_fixfree1 BSEGS ms mdlm (Z_to_bv 64 222) (Z_to_bv 64 50) addr (U size) HALT eq_refl
                ltac:(rewrite u_Z2bv by lia; reflexivity)
                E0 ltac:((lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact Hal) Hpos E1 Hsz ltac:(rewrite PRU; exact Htop) Htop64 E2 E3 ltac:(vm_compute; reflexivity) E4 E5
                ltac:(rewrite EN; exact Hrf) ltac:(rewrite PRU; exact Hbk))).
    intros [].
    (lazymatch goal with |- ?G => let G' := eval unfold fxfr_nx, fxfr_effs, fxfr_ms' in G in change_no_check G' end). rewrite EN. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end).
    rewrite (AsKSys6.MhKSys.adv_zerosr_epend r1 (0x811ac%bv : word) M1 rom (Z_to_bv 64 222) addr addr size).
    replace (v_addi (0x811ac%bv : word) 4) with (0x811b0%bv : word) by (apply bv_eq; vm_compute; reflexivity).
    exact KOK.
  Qed.
End NODE2H.
End FPGen1h.
End BoAllocM8kh.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8pa.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8xp.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.


Lemma both_poison_cells_img : Forall (fun c => 0 <= c /\ c + 8 <= AIMGHI) (poison_cells both_poison_tab).
Proof. (lazymatch goal with |- ?G => let G' := eval unfold poison_cells, both_poison_tab in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). repeat constructor; lia. Qed.

Section FPGen.
Context {fx : FPState}.

Section PFARM.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.
  (* [comment removed for export] *)
  Variable Hd2 : word -> bool.
  Hypothesis HOFFSEG2 : H_off_segments BSEGS Hd2.
  Variable A2 : list (Z * Z).
  Hypothesis AWF2 : A_wf A2.
  Variables (A : list (Z * Z)) (regs : bvmap 5 word) (mem rom : word -> option byte) (model : Model)
            (sp ra s0v s1v s2v s3v s4v s5v s6v thr tp gp tsdp ctxw v72 v80 vst midend : word) (cpm : byte)
            (RIz SPB c req au mu nf PGP CF T thr0 : Z) (Qok Qf : config -> Prop) (MOK MKP MDS : Model -> Model).
  #[local] Abbreviation stats := (at_ thr 2768).
  #[local] Abbreviation slot := (SPB + c * 2 ^ 32 + mu).
  #[local] Abbreviation SH := ((SPB + c * 2 ^ 32 + mu) / 8 + 0x7fff8000).
  #[local] Abbreviation M0 := (pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v).
  #[local] Abbreviation M1 := (mfi_m1 M0 (at_ sp (-64)) (Z_to_bv 64 0x51964) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18))
                     (Z_to_bv 64 slot) (Z_to_bv 64 (csize c)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x178e4) PGP).
  #[local] Abbreviation ENOMEMw := (Z_to_bv 64 (2 ^ 64 - 12) : word).
  #[local] Abbreviation SCR := (word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa)).
  #[local] Abbreviation MR := (pf_mr mem sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c mu PGP).
  (* [comment removed for export] *)
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
  Hypothesis H11 : getr regs 11 = stats.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 RIz.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 req.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v.
  Hypothesis Hsp : 2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hc : 1 <= c <= 30.
  Hypothesis Hreq : 1 <= req /\ csize c * req <= 2 ^ 18.
  Hypothesis Hau : 0 <= au <= mu /\ mu + 2 ^ 18 <= 0xE0000000.
  Hypothesis Hmap : mu < au + csize c * req.
  Hypothesis HSPB : 0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 63 /\ SPB mod 4096 = 0 /\ AIMGHI <= SPB.
  Hypothesis Hmu4k : mu mod 4096 = 0.
  Hypothesis Hnf : 0 <= nf <= 2 ^ 27.
  Hypothesis HRI : AIMGHI <= RIz /\ RIz + 128 <= U sp - 464.
  Hypothesis HPGP : AIMGLO <= PGP /\ PGP + 8 <= AIMGHI.
  Hypothesis HCF : AIMGLO <= CF /\ CF + 264 <= AIMGHI.
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-464)) 464 = true.
  Hypothesis C_sbeg : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  Hypothesis R_au : rdn BSEGS mem (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis R_mu : rdn BSEGS mem (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)).
  Hypothesis R_mm : rdn BSEGS mem (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis R_nf : rdn BSEGS mem (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis C_rel : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 40)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff)).
  Hypothesis C_pre : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 56)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rgpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlim : rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Hslot : slot + 2 ^ 18 <= U sp - 464 \/ U sp <= slot.
  Hypothesis HDsbeg : hid_off Hd (0x10ab58 + 32) 8.
  Hypothesis HDrel : hid_off Hd (0x10ab58 + 40) 4.
  Hypothesis HDpre : hid_off Hd (0x10ab58 + 56) 1.
  Hypothesis HDgpg : hid_off Hd 0x105ef8 8.
  Hypothesis HDpg : hid_off Hd PGP 8.
  Hypothesis HDgcf : hid_off Hd 0x105f08 8.
  Hypothesis HDdpm : hid_off Hd (CF + 260) 1.
  Hypothesis HDlim : hid_off Hd (CF + 144) 8.
  Hypothesis HDscr : hid_off Hd (U sp - 464) 464.
  Hypothesis HALT : m_halted model = None.
  Hypothesis LC : lazy_cover Hd (m_vm_lazy model) A.
  Hypothesis AWF : A_wf A.
  Hypothesis MI : MInv A model.
  Hypothesis NODE : forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 slot -> getr r1 11 = Z_to_bv 64 (2 ^ 18) -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD BSEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x811b0 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Hypothesis CHILD : forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))
        /\ (m_halted (MDS mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MDS mdlm)) A /\ MInv A (MDS mdlm)).
  Hypothesis OKSW : forall mdlm mdl4, same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        lazy_cover Hd2 (m_vm_lazy mdl4) A2 /\ MInv A2 mdl4.
  (* [comment removed for export] *)
  Hypothesis HT : U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 464 /\ T mod 8 = 0.
  Hypothesis HTRI : T + 4096 <= RIz \/ RIz + 128 <= T.
  Hypothesis HTSH : T + 4096 <= SH \/ SH + 2 ^ 15 <= T.
  Hypothesis HRSH : RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz.
  Hypothesis HTsl : T + 4096 <= slot \/ slot + 2 ^ 18 <= T.
  Hypothesis HRsl : RIz + 128 <= slot \/ slot + 2 ^ 18 <= RIz.
  Hypothesis PH : poisonH BSEGS both_poison_tab mem (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x51980) (at_ sp (-64)) cpm midend thr0.
  Hypothesis GH : gctH BSEGS both_gct_tab mem (at_ (at_ sp (-64)) (-16)) tp tsdp ctxw thr.
  Hypothesis GB : U (gt_tsd both_gct_tab) + 8 <= U sp - 464 /\ U tp - 80 <= U sp - 464 /\ U tsdp + 8 <= U sp - 464 /\ U ctxw + 160 <= U sp - 464.
  Hypothesis GS : (U (gt_tsd both_gct_tab) + 8 <= slot \/ slot + 2 ^ 18 <= U (gt_tsd both_gct_tab)) /\ (U tp - 80 <= slot \/ slot + 2 ^ 18 <= U tp - 88)
                  /\ (U tsdp + 8 <= slot \/ slot + 2 ^ 18 <= U tsdp) /\ (U ctxw + 160 <= slot \/ slot + 2 ^ 18 <= U ctxw + 152).
  Hypothesis G1 : U (gt_tsd both_gct_tab) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd both_gct_tab).
  Hypothesis G2 : U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88.
  Hypothesis G3 : U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp.
  Hypothesis G4 : U ctxw + 160 <= SH \/ SH + 2 ^ 15 <= U ctxw + 152.
  Hypothesis R72 : rdn BSEGS mem (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R80 : rdn BSEGS mem (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis Rst : rdn BSEGS mem (at_ thr 2792) 8 = Some (LE8 vst).
  Hypothesis SOKT : store_ok BSEGS mem thr 4096 = true.
  Hypothesis SOKRI : store_ok BSEGS mem (Z_to_bv 64 RIz) 128 = true.
  Hypothesis HDc : Forall (fun c => hid_off Hd2 c 8) (poison_cells both_poison_tab).
  Hypothesis HDsh : hid_off Hd2 SH (2 ^ 15).
  Hypothesis HD1 : hid_off Hd2 (U (gt_tsd both_gct_tab)) 8.
  Hypothesis HD2 : hid_off Hd2 (U tp - 88) 8.
  Hypothesis HD3 : hid_off Hd2 (U tsdp) 8.
  Hypothesis HD4 : hid_off Hd2 (U ctxw + 152) 8.
  Hypothesis HDT : hid_off Hd2 T 4096.
  Hypothesis HDRI : hid_off Hd2 RIz 128.
  Hypothesis HDscr2 : hid_off Hd2 (U sp - 464) 464.
  Hypothesis HDRIa : hid_off Hd RIz 128.
  (* [comment removed for export] *)
  Hypothesis CONT1 : forall (r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl5 -> MInv A2 mdl5 ->
      pf_regs sp RIz SPB c r -> getr r 1 = Z_to_bv 64 0x519d8 ->
      getr r 10 = Z_to_bv 64 0x10ab58 -> getr r 11 = Z_to_bv 64 RIz -> getr r 12 = Z_to_bv 64 (SPB + c * 2 ^ 32) ->
      getr r 13 = Z_to_bv 64 (nf + (mu + 2 ^ 18 - au) / csize c) ->
      getr r 9 = Z_to_bv 64 (nf + (mu + 2 ^ 18 - au) / csize c) -> getr r 19 = Z_to_bv 64 ((mu + 2 ^ 18 - au) / csize c) ->
      getr r 20 = Z_to_bv 64 (mu + 2 ^ 18 - au) -> getr r 4 = tp -> getr r 3 = gp ->
      katwD BSEGS (mkCfg (mkst r (0x4f508 : word) (pam_3 MR sp thr v72 v80 vst RIz SPB c slot mu) rom) mdl5) Qok Qf.
  Hypothesis CONT0K : forall (r' r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl5 -> MInv A mdl5 ->
      regs_agree (fun i : reg => In i pf_clob) regs r' -> pf_post0 sp ra s0v s1v s2v s3v s4v s5v s6v r' r ->
      katD BSEGS (mkCfg (mkst r ra (wbytes (wbytes M1 (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl5) Qf.
  Hypothesis CONT0D : forall (r' r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MDS mdlm) mdl5 -> MInv A mdl5 ->
      regs_agree (fun i : reg => In i pf_clob) regs r' -> pf_post0 sp ra s0v s1v s2v s3v s4v s5v s6v r' r ->
      katD BSEGS (mkCfg (mkst r ra (wbytes (wbytes (unfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl5) Qf.

  Theorem pf_map_arm_katsD : katsD BSEGS (mkCfg (mkst regs (0x51844 : word) mem rom) model) Qok Qf.
  Proof using CONT0D CONT0K CONT1 HDRIa HDscr2 HDRI HDT HD4 HD3 HD2 HD1 HDsh HDc SOKRI SOKT Rst R80 R72 G4 G3 G2 G1 GS GB GH PH HRsl HTsl HRSH HTSH HTRI HT OKSW CHILD NODE MI AWF LC HALT HDscr HDlim HDdpm HDgcf HDpg HDgpg HDpre HDrel HDsbeg Hslot Rlim Rdpm Rgcf Rpg Rgpg C_pre C_rel R_nf R_mm R_mu R_au C_sbeg Hstk HCF HPGP HRI Hnf Hmu4k HSPB Hmap Hau Hreq Hc Hret Hsp H22 H21 H20 H19 H18 H9 H8 H14 H13 H12 H11 H10 H3 H4 H2 H1 MDS MKP MOK thr0 T CF PGP nf mu au req c SPB RIz cpm midend vst v80 v72 ctxw tsdp gp tp thr s6v s5v s4v s3v s2v s1v s0v ra sp A AWF2 A2 HOFFSEG2 Hd2 WX HOFFSEG Hd.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HRI as [RI1 RI2]. destruct HSPB as (S1 & S2 & S3 & S4).
    destruct Hau as [[AU0 AU1] AU2]. destruct HT as (UT & T1 & T2 & T3). pose proof (u64_range thr) as Hthr.
    assert (SL : 0 <= slot /\ slot + 2 ^ 18 < 2 ^ 63) by lia.
    assert (HDf64 : hid_off Hd (U sp - 64) 64) by (eapply hid_off_sub; [exact HDscr | lia | lia]).
    assert (HDf128 : hid_off Hd2 (U sp - 128) 64) by (eapply hid_off_sub; [exact HDscr2 | lia | lia]).
    assert (FRAMES : forall mdlx mdly, m_halted mdlx = None -> lazy_cover Hd (m_vm_lazy mdlx) A -> same_but_materialized mdlx mdly ->
               m_halted mdly = None /\ lazy_cover Hd (m_vm_lazy mdly) A).
    { intros mdlx mdly HX LX SB. pose proof (same_but_materialized_frame mdlx mdly SB) as FR. split.
      - destruct FR as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_). rewrite Hh. exact HX.
      - destruct FR as (_ & _ & Hl & _). rewrite Hl. exact LX. }
    apply (pf_usermap_katsD Hd HOFFSEG WX A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c req au mu PGP CF Qok Qf MOK MKP MDS
             H1 H2 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 ltac:(lia) Hc Hreq (conj (conj AU0 AU1) AU2) Hmap (conj S1 (conj S2 (conj S3 S4))) Hmu4k (conj RI1 RI2) HPGP HCF Hstk
             C_sbeg R_au R_mu R_mm C_rel C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot
             HDsbeg ltac:(eapply hid_off_sub; [exact HDRIa | lia | lia]) ltac:(eapply hid_off_sub; [exact HDRIa | lia | lia]) ltac:(eapply hid_off_sub; [exact HDRIa | lia | lia])
             HDrel HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (PR & E9 & E19 & E20 & E22 & E10) AG.
      destruct (CHILD mdlm SBm MIm) as ((HOK & LOK & _) & _ & _).
      destruct (FRAMES _ _ HOK LOK SB4) as [HALT4 LC4].
      destruct (OKSW mdlm mdl4 SBm MIm SB4 MI4) as [LC2 MI2].
      assert (OUT : forall x : word, (U x < U sp - 464 \/ U sp <= U x) -> (U x < slot \/ slot + 2 ^ 18 <= U x) -> MR x = mem x)
        by (intros x X1 X2; apply pf_mr_outside; [lia | exact SL | exact X1 | exact X2]).
      assert (GR : mem_grows mem MR) by apply pf_mr_grows.
      assert (RDZ : forall (z : Z) (k : nat) v, 0 <= z -> z + Z.of_nat k <= U sp - 464 -> (z + Z.of_nat k <= slot \/ slot + 2 ^ 18 <= z) ->
                 rdn BSEGS mem (Z_to_bv 64 z) k = Some v -> rdn BSEGS MR (Z_to_bv 64 z) k = Some v).
      { intros z k v Z0 Z1 Z2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        apply OUT; clear - Hx Z1 Z2; lia. }
      assert (RDT : forall (k : Z) v, 0 <= k -> k + 8 <= 4096 -> rdn BSEGS mem (at_ thr k) 8 = Some v -> rdn BSEGS MR (at_ thr k) 8 = Some v).
      { intros k v K0 K1 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
        apply OUT; clear - Hx UT T2 HTsl K0 K1; lia. }
      change (wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-148)) SCR) with MR.
      apply (pf_after_map_katwD Hd2 HOFFSEG2 WX A2 r' MR rom mdl4 sp thr tp gp tsdp ctxw v72 v80 vst midend cpm RIz SPB c au mu nf T thr0 Qok Qf
               PR ltac:(rewrite (AG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H4)
               ltac:(rewrite (AG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H3)
               E9 E10 E19 E20 E22 (conj SP1 SP2) Hc (conj (conj AU0 AU1) AU2) Hnf ltac:(lia) ltac:(lia) ltac:(lia) HTRI HTSH HRSH).
      + apply (poisonH_keep_P BSEGS both_poison_tab mem MR _ _ _ _ _ cpm midend thr0
                 (fun z => (z < U sp - 464 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) PH); [intros x [X1 X2]; apply OUT; assumption | exact GR |].
        eapply Forall_impl; [|exact both_poison_cells_img]. cbv beta. intros c0 Hc0 z Hz. lia.
      + destruct GB as (B1 & B2 & B3 & B4). destruct GS as (Q1 & Q2 & Q3 & Q4).
        apply (gctH_keep_P BSEGS both_gct_tab mem MR _ tp tsdp ctxw thr
                 (fun z => (z < U sp - 464 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) GH);
          [intros x [X1 X2]; apply OUT; assumption | exact GR
          | intros z Hz; cbv beta; clear - Hz B1 Q1; lia | intros z Hz; cbv beta; clear - Hz B2 Q2; lia
          | intros z Hz; cbv beta; clear - Hz B3 Q3; lia | intros z Hz; cbv beta; clear - Hz B4 Q4; lia].
      + destruct GB as (B1 & B2 & B3 & B4). lia.
      + exact G1.
      + exact G2.
      + exact G3.
      + exact G4.
      + apply RDT; [lia | lia | exact R72].
      + apply RDT; [lia | lia | exact R80].
      + apply RDT; [lia | lia | exact Rst].
      + apply RDZ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HRsl; lia | exact R_au].
      + apply RDZ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HRsl; lia | exact R_mu].
      + apply RDZ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HRsl; lia | exact R_nf].
      + eapply store_ok_mono; [exact GR | exact SOKT].
      + eapply store_ok_mono; [exact GR | exact SOKRI].
      + exact HDc.
      + exact HDf128.
      + exact HDsh.
      + exact HD1.
      + exact HD2.
      + exact HD3.
      + exact HD4.
      + exact HDT.
      + exact HDRI.
      + exact HALT4.
      + exact LC2.
      + exact AWF2.
      + exact MI2.
      + intros r mdl5 SB5 MI5 D0 D1 D10 D11 D12 D13 D9 D19 D20 D4 D3.
        exact (CONT1 r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 D0 D1 D10 D11 D12 D13 D9 D19 D20 D4 D3).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (PR & E9 & E19 & E20 & E22 & E10) AG.
      destruct (CHILD mdlm SBm MIm) as (_ & (HKP & LKP & _) & _).
      destruct (FRAMES _ _ HKP LKP SB4) as [HALT4 LC4].
      set (MK := wbytes (wbytes M1 (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))).
      assert (AGR : forall x : word, U sp - 64 <= U x < U sp -> MK x = M0 x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        apply mfi_m1_outside; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]. }
      destruct PR as (P2 & _).
      apply (pf_fail_map_katD Hd HOFFSEG WX A r' MK rom mdl4 sp ra s0v s1v s2v s3v s4v s5v s6v Qf P2 E10 Hret ltac:(lia)
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-8) ra ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-16) s0v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-24) s1v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-32) s2v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-40) s3v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-48) s4v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-56) s5v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-64) s6v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               HDf64 HALT4 LC4 AWF MI4).
      intros r mdl5 SB5 MI5 POST.
      exact (CONT0K r' r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 AG POST).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (PR & E9 & E19 & E20 & E22 & E10) AG.
      destruct (CHILD mdlm SBm MIm) as (_ & _ & (HDS & LDS & _)).
      destruct (FRAMES _ _ HDS LDS SB4) as [HALT4 LC4].
      set (MK := wbytes (wbytes (unfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))).
      assert (AGR : forall x : word, U sp - 64 <= U x < U sp -> MK x = M0 x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        rewrite unfill_out by (rewrite !u_Z2bv by (clear - SL; lia); clear - Hx Hslot; lia).
        apply mfi_m1_outside; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]. }
      destruct PR as (P2 & _).
      apply (pf_fail_map_katD Hd HOFFSEG WX A r' MK rom mdl4 sp ra s0v s1v s2v s3v s4v s5v s6v Qf P2 E10 Hret ltac:(lia)
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-8) ra ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-16) s0v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-24) s1v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-32) s2v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-40) s3v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-48) s4v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-56) s5v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-64) s6v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               HDf64 HALT4 LC4 AWF MI4).
      intros r mdl5 SB5 MI5 POST.
      exact (CONT0D r' r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 AG POST).
  Qed.
End PFARM.
End FPGen.
End BoAllocM8pa.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8rh.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k BoAllocM8kh OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGenH.
Context {fx : FPState}.

Section USERMAPH.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.

  Theorem pf_usermap_katsD_h :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v s6v stats : word) (RIz SPB c req au mu PGP CF : Z) (Qok Qf : config -> Prop)
           (MOK MKP : Model -> Model),
    let slot := SPB + c * 2 ^ 32 + mu in
    let M0 := pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v in
    let M1 := mfi_m1 M0 (at_ sp (-64)) (Z_to_bv 64 0x51964) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18))
                     (Z_to_bv 64 slot) (Z_to_bv 64 (csize c)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x178e4) PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa) in
    (* [comment removed for export] *)
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = Z_to_bv 64 0x10ab58 -> getr regs 11 = stats -> getr regs 12 = Z_to_bv 64 c ->
    getr regs 13 = Z_to_bv 64 RIz -> getr regs 14 = Z_to_bv 64 req ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v -> getr regs 22 = s6v ->
    (2 ^ 24 + 64 <= U sp /\ U sp + 16 <= 2 ^ 47) -> 1 <= c <= 30 -> (1 <= req /\ csize c * req <= 2 ^ 18) ->
    (0 <= au <= mu /\ mu + 2 ^ 18 <= 0xE0000000) -> mu < au + csize c * req ->
    (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 63 /\ SPB mod 4096 = 0 /\ AIMGHI <= SPB) -> mu mod 4096 = 0 ->
    (AIMGHI <= RIz /\ RIz + 128 <= U sp - 464) ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok BSEGS mem (at_ sp (-464)) 464 = true ->
    (* [comment removed for export] *)
    rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SPB)) ->
    rdn BSEGS mem (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)) ->
    rdn BSEGS mem (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)) ->
    rdn BSEGS mem (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 40)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff)) ->
    rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 56)) 1 = Some [Z_to_bv 8 0] ->
    rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0] ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    (* [comment removed for export] *)
    (slot + 2 ^ 18 <= U sp - 464 \/ U sp <= slot) ->
    (* [comment removed for export] *)
    hid_off Hd (0x10ab58 + 32) 8 -> hid_off Hd (RIz + 32) 8 -> hid_off Hd (RIz + 48) 8 -> hid_off Hd (RIz + 56) 8 ->
    hid_off Hd (0x10ab58 + 40) 4 -> hid_off Hd (0x10ab58 + 56) 1 ->
    hid_off Hd 0x105ef8 8 -> hid_off Hd PGP 8 -> hid_off Hd 0x105f08 8 -> hid_off Hd (CF + 260) 1 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd (U sp - 464) 464 ->
    (* [comment removed for export] *)
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (* [comment removed for export] *)
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 slot -> getr r1 11 = Z_to_bv 64 (2 ^ 18) -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD BSEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x811b0 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf') ->
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        pf_at_ret sp stats RIz SPB c mu r' (Z_to_bv 64 slot) -> regs_agree (fun i : reg => In i pf_clob) regs r' ->
        katwD BSEGS (mkCfg (mkst r' (0x51964 : word) (wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-148)) SCR) rom) mdl4) Qok Qf) ->
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl4 -> MInv A mdl4 ->
        pf_at_ret sp stats RIz SPB c mu r' (Z_to_bv 64 0) -> regs_agree (fun i : reg => In i pf_clob) regs r' ->
        katD BSEGS (mkCfg (mkst r' (0x51964 : word) (wbytes (wbytes M1 (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl4) Qf) ->
    katsD BSEGS (mkCfg (mkst regs (0x51844 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c req au mu PGP CF Qok Qf MOK MKP slot M0 M1 ENOMEMw SCR
           H1 H2 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 Hsp Hc Hreq Hau Hmap HSPB Hmu4k HRI HPGP HCF Hstk
           C_sbeg R_au R_mu R_mm C_rel C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot
           HDsbeg HDau HDmu HDmm HDrel HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD CONTOK CONTKP.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HSPB as (S1 & S2 & S3 & S4). destruct HRI as [RI1 RI2].
    destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2]. destruct Hau as [AU1 AU2]. destruct Hreq as [RQ1 RQ2].
    pose proof (csize_pos c Hc) as [CS1 CS2].
    set (spm := at_ sp (-64)).
    assert (Uspm : U spm = U sp - 64) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    (* [comment removed for export] *)
    assert (CELLR : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 464 -> hid_off Hd cc (Z.of_nat k) ->
               rdn BSEGS mem (Z_to_bv 64 cc) k = Some v -> rdn BSEGS (mrestrict Hd mem) (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    assert (Hstk' : store_ok BSEGS (mrestrict Hd mem) (at_ sp (-64)) 64 = true).
    { rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      eapply (store_ok_sub BSEGS mem (at_ sp (-464)) _ 464); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    destruct (pf_head_map (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c req au mu regs
                H1 H2 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 ltac:(lia) Hc (conj RQ1 RQ2) (conj AU1 AU2) ltac:(lia) ltac:(lia) Hstk'
                (CELLR (0x10ab58 + 32) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDsbeg C_sbeg)
                (CELLR (RIz + 32) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDau R_au)
                (CELLR (RIz + 48) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDmu R_mu) Hmap)
      as (r1 & RUN1 & PR1 & A9 & A10 & A12 & A19 & A20 & AG1).
    rewrite pf_m0_mrestrict in RUN1 by (first [lia | intros x Hx; apply HDscr; lia]). fold M0 in RUN1.
    assert (M0out : forall x : word, (U x < U sp - 64 \/ U sp <= U x) -> M0 x = mem x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold M0 in G in change_no_check G' end); apply pf_m0_outside; [lia | exact Hx]).
    assert (CELL0 : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 464 ->
               rdn BSEGS mem (Z_to_bv 64 cc) k = Some v -> rdn BSEGS M0 (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply M0out. lia. }
    assert (CELLR0 : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 464 -> hid_off Hd cc (Z.of_nat k) ->
               rdn BSEGS mem (Z_to_bv 64 cc) k = Some v -> rdn BSEGS (mrestrict Hd M0) (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [apply CELL0; assumption | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (pf_map (mrestrict Hd M0) rom sp stats RIz SPB c (au + csize c * req) mu r1 PR1 A9 A10 A19 A20 ltac:(lia) Hc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                (CELLR0 (0x10ab58 + 40) 4%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDrel C_rel)
                (CELLR0 (0x10ab58 + 56) 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpre C_pre)
                (CELLR0 (RIz + 56) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDmm R_mm))
      as (r2 & RUN2 & PR2 & B9 & B1 & B11 & B12 & B13 & B19 & B20 & B22 & AG2).
    assert (M0hid : forall a : word, Hd a = true -> M0 a = mem a).
    { intros a Ha. apply M0out.
      destruct (Z_lt_le_dec (U a) (U sp - 64)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katsD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst regs (0x51844 : word) mem rom)
             (mkst r2 (0x8b0f8 : word) (mrestrict Hd M0) rom) model Qok Qf LC AWF MI HALT).
    { rewrite mk_restrict_mkst. eapply msteps_trans; [exact RUN1 | exact RUN2]. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x51844 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M0 M0hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    assert (LCm : lazy_cover Hd (m_vm_lazy mdlm) A) by (destruct FRm as (_ & _ & Hl & _); rewrite Hl; exact LC).
    destruct PR2 as (P2 & P8 & P18 & P21).
    assert (SUB : forall x : reg, In x mfi_clob2 -> In x pf_clob).
    { intros x Hin. unfold mfi_clob2, mfi_clob in Hin. cbn [In] in Hin. (lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end).
      repeat (destruct Hin as [<-|Hin]; [solve [in_list]|]). destruct Hin. }
    assert (RETK : forall (r' : bvmap 5 word) (res : word),
               mfi_ret r2 r' spm (Z_to_bv 64 0x51964) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 slot) res ->
               pf_at_ret sp stats RIz SPB c mu r' res).
    { intros r' res (C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & AGL). (lazymatch goal with |- ?G => let G' := eval unfold pf_at_ret, pf_regs in G in change_no_check G' end).
      assert (N21 : ~ In (21%bv : reg) mfi_clob2) by ((lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
      assert (N22 : ~ In (22%bv : reg) mfi_clob2) by ((lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
      rewrite (AGL 21%bv N21), (AGL 22%bv N22).
      repeat split; assumption. }
    assert (RETA : forall (r' : bvmap 5 word) (res : word),
               mfi_ret r2 r' spm (Z_to_bv 64 0x51964) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 slot) res ->
               regs_agree (fun i : reg => In i pf_clob) regs r').
    { intros r' res (_ & _ & _ & _ & _ & _ & _ & _ & AGL) x Hx.
      rewrite (AGL x) by (intros Hin; apply Hx; exact (SUB x Hin)).
      rewrite (AG2 x Hx). exact (AG1 x Hx). }
    (* [comment removed for export] *)
    apply (rarmap_katsD_h Hd HOFFSEG WX A r2 M0 rom mdlm spm (Z_to_bv 64 0x51964) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32))
             (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (csize c)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x178e4)
             PGP CF Qok Qf MOK MKP B1 P2 B11 B12 B13 P8 B9 P18 B19 B20 P21).
    - rewrite Uspm. lia.
    - apply ret_ok_lit; [lia | reflexivity].
    - rewrite u_Z2bv by ((lazymatch goal with |- ?G => let G' := eval unfold slot in G in change_no_check G' end); lia). (lazymatch goal with |- ?G => let G' := eval unfold slot in G in change_no_check G' end). replace (c * 2 ^ 32) with (c * 1048576 * 4096) by lia.
      rewrite Z.add_mod, (Z.add_mod SPB), Z.mod_mul, S3, Hmu4k by lia. reflexivity.
    - rewrite u_Z2bv by lia. split; [reflexivity | lia].
    - rewrite u_Z2bv by lia. lia.
    - lia.
    - lia.
    - replace (at_ spm (-400)) with (at_ sp (-464)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold M0 in G in change_no_check G' end); apply pf_m0_grows |].
      eapply (store_ok_sub BSEGS mem (at_ sp (-464)) _ 464); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rgpg].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rpg].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rgcf].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rdpm].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rlim].
    - rewrite !u_Z2bv by ((lazymatch goal with |- ?G => let G' := eval unfold slot in G in change_no_check G' end); lia). rewrite Uspm. unfold slot in *. split; [lia | split; [lia | lia]].
    - exact HDgpg.
    - exact HDpg.
    - exact HDgcf.
    - exact HDdpm.
    - exact HDlim.
    - eapply hid_off_sub; [exact HDscr | rewrite Uspm; lia | rewrite Uspm; lia].
    - exact HALTm.
    - exact LCm.
    - exact AWF.
    - exact MIm.
    - intros mdlm0 rr SB0 MI0 HL0 G10 G11 G12 G13 G14 G15 Qok' Qf' K1.
      exact (NODE mdlm0 rr (same_but_materialized_trans _ _ _ SBMm SB0) MI0 HL0 G10 G11 G12 G13 G14 G15 Qok' Qf' K1).
    - intros mdlm0 SB0 MI0. exact (CHILD mdlm0 (same_but_materialized_trans _ _ _ SBMm SB0) MI0).
    - intros r' mdlm0 mdl4 SB0 MI0 SB4 MI4 RET.
      replace (at_ spm (-84)) with (at_ sp (-148)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      replace (Z_to_bv 64 334180 : word) with (0x51964%bv : word) by (apply bv_eq; reflexivity).
      apply (CONTOK r' mdlm0 mdl4 (same_but_materialized_trans _ _ _ SBMm SB0) MI0 SB4 MI4); [apply (RETK r' _ RET) | apply (RETA r' _ RET)].
    - intros r' mdlm0 mdl4 SB0 MI0 SB4 MI4 RET.
      replace (at_ spm (-84)) with (at_ sp (-148)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      replace (Z_to_bv 64 334180 : word) with (0x51964%bv : word) by (apply bv_eq; reflexivity).
      apply (CONTKP r' mdlm0 mdl4 (same_but_materialized_trans _ _ _ SBMm SB0) MI0 SB4 MI4); [apply (RETK r' _ RET) | apply (RETA r' _ RET)].
  Qed.

End USERMAPH.

Section FAMAPH.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.

  Theorem efs_famap_katsD_h :
    forall (A : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v : word) (RIz rbeg tot mfa PGP CF : Z) (Qok Qf : config -> Prop)
           (MOK MKP : Model -> Model),
    let slot := rbeg + 0xE0000000 + mfa in
    let M0 := efs_m0 mem sp ra s0v s1v s2v s3v in
    let M1 := mfi_m1 M0 (at_ sp (-48)) (Z_to_bv 64 0x4f5a8) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz)
                     s4v s5v (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x19778) PGP in
    let ENOMEMw : word := Z_to_bv 64 (2 ^ 64 - 12) in
    let SCR := word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa) in
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = Z_to_bv 64 0x10ab58 -> getr regs 11 = Z_to_bv 64 RIz -> getr regs 12 = Z_to_bv 64 rbeg ->
    getr regs 13 = Z_to_bv 64 tot ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (2 ^ 24 + 48 <= U sp /\ U sp + 16 <= 2 ^ 47) ->
    (0 <= tot /\ 4 * tot <= 2 ^ 29) -> (0 <= mfa <= 2 ^ 29 /\ mfa mod 2 ^ 18 = 0) -> (mfa < 4 * tot <= mfa + 2 ^ 18) -> mfa + 2 ^ 18 <= 2 ^ 29 ->
    (AIMGHI <= rbeg /\ rbeg + 2 ^ 32 < 2 ^ 63 /\ rbeg mod 4096 = 0) ->
    (AIMGHI <= RIz /\ RIz + 128 <= U sp - 448) ->
    (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
    store_ok BSEGS mem (at_ sp (-448)) 448 = true ->
    rdn BSEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)) ->
    rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 56)) 1 = Some [Z_to_bv 8 0] ->
    rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
    rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0] ->
    rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    (slot + 2 ^ 18 <= U sp - 448 \/ U sp <= slot) ->
    hid_off Hd (RIz + 24) 8 -> hid_off Hd (0x10ab58 + 56) 1 ->
    hid_off Hd 0x105ef8 8 -> hid_off Hd PGP 8 -> hid_off Hd 0x105f08 8 -> hid_off Hd (CF + 260) 1 -> hid_off Hd (CF + 144) 8 ->
    hid_off Hd (U sp - 448) 448 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 slot -> getr r1 11 = Z_to_bv 64 (2 ^ 18) -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD BSEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x811b0 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf') ->
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))) ->
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        efs_at_ret sp s4v RIz slot mfa r' (Z_to_bv 64 slot) -> regs_agree (fun i : reg => In i efs_clob) regs r' ->
        katwD BSEGS (mkCfg (mkst r' (0x4f5a8 : word) (wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-132)) SCR) rom) mdl4) Qok Qf) ->
    (forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl4 -> MInv A mdl4 ->
        efs_at_ret sp s4v RIz slot mfa r' (Z_to_bv 64 0) -> regs_agree (fun i : reg => In i efs_clob) regs r' ->
        katD BSEGS (mkCfg (mkst r' (0x4f5a8 : word) (wbytes (wbytes M1 (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl4) Qf) ->
    katsD BSEGS (mkCfg (mkst regs (0x4f508 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v RIz rbeg tot mfa PGP CF Qok Qf MOK MKP slot M0 M1 ENOMEMw SCR
           H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Htot Hmfa Hneed Hroom Hrbeg HRI HPGP HCF Hstk
           R_mfa C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot
           HDmfa HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD CONTOK CONTKP.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct Hrbeg as (RB1 & RB2 & RB3). destruct HRI as [RI1 RI2].
    destruct HPGP as [PG1 PG2]. destruct HCF as [CF1 CF2]. destruct Hmfa as [MF1 MF2].
    set (spm := at_ sp (-48)).
    assert (Uspm : U spm = U sp - 48) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (CELLR : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 448 -> hid_off Hd cc (Z.of_nat k) ->
               rdn BSEGS mem (Z_to_bv 64 cc) k = Some v -> rdn BSEGS (mrestrict Hd mem) (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    assert (Hstk' : store_ok BSEGS (mrestrict Hd mem) (at_ sp (-48)) 48 = true).
    { rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply HDscr; lia].
      eapply (store_ok_sub BSEGS mem (at_ sp (-448)) _ 448); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    destruct (efs_map (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v RIz rbeg tot mfa regs
                H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 ltac:(lia) Htot (conj MF1 MF2) ltac:(lia) ltac:(lia) Hstk'
                (CELLR (RIz + 24) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDmfa R_mfa)
                (CELLR (0x10ab58 + 56) 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDpre C_pre) Hneed Hroom)
      as (r2 & RUN2 & B1 & B2 & B11 & B12 & B13 & B8 & B9 & B18 & B19 & AG2).
    rewrite efs_m0_mrestrict in RUN2 by (first [lia | intros x Hx; apply HDscr; lia]). fold M0 in RUN2.
    assert (M0out : forall x : word, (U x < U sp - 48 \/ U sp <= U x) -> M0 x = mem x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold M0 in G in change_no_check G' end); apply efs_m0_outside; [lia | exact Hx]).
    assert (CELL0 : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k <= U sp - 448 ->
               rdn BSEGS mem (Z_to_bv 64 cc) k = Some v -> rdn BSEGS M0 (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply M0out. lia. }
    assert (M0hid : forall a : word, Hd a = true -> M0 a = mem a).
    { intros a Ha. apply M0out.
      destruct (Z_lt_le_dec (U a) (U sp - 48)) as [C1|C1]; [left; exact C1|].
      destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [| right; exact C2].
      exfalso. rewrite (HDscr a) in Ha by lia. discriminate Ha. }
    apply (katsD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst regs (0x4f508 : word) mem rom)
             (mkst r2 (0x8b0f8 : word) (mrestrict Hd M0) rom) model Qok Qf LC AWF MI HALT).
    { rewrite mk_restrict_mkst. exact RUN2. }
    intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
    replace (RiscvSemantics.ms_mem (mkst regs (0x4f508 : word) mem rom)) with mem by reflexivity.
    rewrite (mk_munrestrict_same Hd mem M0 M0hid).
    pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
    assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
    assert (LCm : lazy_cover Hd (m_vm_lazy mdlm) A) by (destruct FRm as (_ & _ & Hl & _); rewrite Hl; exact LC).
    assert (A20 : getr r2 20 = s4v) by (rewrite (AG2 20%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H20).
    assert (A21 : getr r2 21 = s5v) by (rewrite (AG2 21%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H21).
    assert (SUB : forall x : reg, In x mfi_clob2 -> In x efs_clob).
    { intros x Hin. unfold mfi_clob2, mfi_clob in Hin. cbn [In] in Hin. (lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end).
      repeat (destruct Hin as [<-|Hin]; [solve [in_list]|]). destruct Hin. }
    assert (SUB2 : forall x : reg, In x [1%bv; 2%bv; 8%bv; 9%bv; 10%bv; 11%bv; 12%bv; 13%bv; 14%bv; 15%bv; 18%bv; 19%bv] -> In x efs_clob).
    { intros x Hin. cbn [In] in Hin. (lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end). repeat (destruct Hin as [<-|Hin]; [solve [in_list]|]). destruct Hin. }
    assert (RETK : forall (r' : bvmap 5 word) (res : word),
               mfi_ret r2 r' spm (Z_to_bv 64 0x4f5a8) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz) s4v res ->
               efs_at_ret sp s4v RIz slot mfa r' res).
    { intros r' res (C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & AGL). (lazymatch goal with |- ?G => let G' := eval unfold efs_at_ret in G in change_no_check G' end). repeat split; assumption. }
    assert (RETA : forall (r' : bvmap 5 word) (res : word),
               mfi_ret r2 r' spm (Z_to_bv 64 0x4f5a8) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz) s4v res ->
               regs_agree (fun i : reg => In i efs_clob) regs r').
    { intros r' res (_ & _ & _ & _ & _ & _ & _ & _ & AGL) x Hx.
      rewrite (AGL x) by (intros Hin; apply Hx; exact (SUB x Hin)).
      apply AG2. intros Hin. apply Hx. exact (SUB2 x Hin). }
    apply (rarmap_katsD_h Hd HOFFSEG WX A r2 M0 rom mdlm spm (Z_to_bv 64 0x4f5a8) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot)
             (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz) s4v s5v (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x19778)
             PGP CF Qok Qf MOK MKP B1 B2 B11 B12 B13 B8 B9 B18 B19 A20 A21).
    - rewrite Uspm. lia.
    - apply ret_ok_lit; [lia | reflexivity].
    - rewrite u_Z2bv by ((lazymatch goal with |- ?G => let G' := eval unfold slot in G in change_no_check G' end); lia). (lazymatch goal with |- ?G => let G' := eval unfold slot in G in change_no_check G' end). replace (rbeg + 0xE0000000 + mfa) with (rbeg + (917504 * 4096 + mfa)) by lia.
      rewrite Z.add_mod, RB3 by lia. rewrite (Z.add_mod (917504 * 4096)), Z.mod_mul by lia.
      assert (E : mfa mod 4096 = 0) by (clear - MF2; Z.div_mod_to_equations; lia). rewrite E. reflexivity.
    - rewrite u_Z2bv by lia. split; [reflexivity | lia].
    - rewrite u_Z2bv by lia. lia.
    - lia.
    - lia.
    - replace (at_ spm (-400)) with (at_ sp (-448)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold M0 in G in change_no_check G' end); apply efs_m0_grows |].
      eapply (store_ok_sub BSEGS mem (at_ sp (-448)) _ 448); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rgpg].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rpg].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rgcf].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rdpm].
    - apply CELL0; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rlim].
    - rewrite !u_Z2bv by ((lazymatch goal with |- ?G => let G' := eval unfold slot in G in change_no_check G' end); lia). rewrite Uspm. unfold slot in *. split; [lia | split; [lia | lia]].
    - exact HDgpg.
    - exact HDpg.
    - exact HDgcf.
    - exact HDdpm.
    - exact HDlim.
    - eapply hid_off_sub; [exact HDscr | rewrite Uspm; lia | rewrite Uspm; lia].
    - exact HALTm.
    - exact LCm.
    - exact AWF.
    - exact MIm.
    - intros mdlm0 rr SB0 MI0 HL0 G10 G11 G12 G13 G14 G15 Qok' Qf' K1.
      exact (NODE mdlm0 rr (same_but_materialized_trans _ _ _ SBMm SB0) MI0 HL0 G10 G11 G12 G13 G14 G15 Qok' Qf' K1).
    - intros mdlm0 SB0 MI0. exact (CHILD mdlm0 (same_but_materialized_trans _ _ _ SBMm SB0) MI0).
    - intros r' mdlm0 mdl4 SB0 MI0 SB4 MI4 RET.
      replace (at_ spm (-84)) with (at_ sp (-132)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      replace (Z_to_bv 64 325032 : word) with (0x4f5a8%bv : word) by (apply bv_eq; reflexivity).
      apply (CONTOK r' mdlm0 mdl4 (same_but_materialized_trans _ _ _ SBMm SB0) MI0 SB4 MI4); [apply (RETK r' _ RET) | apply (RETA r' _ RET)].
    - intros r' mdlm0 mdl4 SB0 MI0 SB4 MI4 RET.
      replace (at_ spm (-84)) with (at_ sp (-132)) by ((lazymatch goal with |- ?G => let G' := eval unfold spm in G in change_no_check G' end); rewrite at_at; reflexivity).
      replace (Z_to_bv 64 325032 : word) with (0x4f5a8%bv : word) by (apply bv_eq; reflexivity).
      apply (CONTKP r' mdlm0 mdl4 (same_but_materialized_trans _ _ _ SBMm SB0) MI0 SB4 MI4); [apply (RETK r' _ RET) | apply (RETA r' _ RET)].
  Qed.

End FAMAPH.
End FPGenH.
End BoAllocM8rh.
Module BoAllocM8pah.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8r BoAllocM8kh BoAllocM8rh BoAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8xp.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.


Section FPGenPH.
Context {fx : FPState}.

Section PFARMH.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.
  (* [comment removed for export] *)
  Variable Hd2 : word -> bool.
  Hypothesis HOFFSEG2 : H_off_segments BSEGS Hd2.
  Variable A2 : list (Z * Z).
  Hypothesis AWF2 : A_wf A2.
  Variables (A : list (Z * Z)) (regs : bvmap 5 word) (mem rom : word -> option byte) (model : Model)
            (sp ra s0v s1v s2v s3v s4v s5v s6v thr tp gp tsdp ctxw v72 v80 vst midend : word) (cpm : byte)
            (RIz SPB c req au mu nf PGP CF T thr0 : Z) (Qok Qf : config -> Prop) (MOK MKP : Model -> Model).
  #[local] Abbreviation stats := (at_ thr 2768).
  #[local] Abbreviation slot := (SPB + c * 2 ^ 32 + mu).
  #[local] Abbreviation SH := ((SPB + c * 2 ^ 32 + mu) / 8 + 0x7fff8000).
  #[local] Abbreviation M0 := (pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v).
  #[local] Abbreviation M1 := (mfi_m1 M0 (at_ sp (-64)) (Z_to_bv 64 0x51964) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18))
                     (Z_to_bv 64 slot) (Z_to_bv 64 (csize c)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x178e4) PGP).
  #[local] Abbreviation ENOMEMw := (Z_to_bv 64 (2 ^ 64 - 12) : word).
  #[local] Abbreviation SCR := (word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa)).
  #[local] Abbreviation MR := (pf_mr mem sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c mu PGP).
  (* [comment removed for export] *)
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
  Hypothesis H11 : getr regs 11 = stats.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 RIz.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 req.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v.
  Hypothesis Hsp : 2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hc : 1 <= c <= 30.
  Hypothesis Hreq : 1 <= req /\ csize c * req <= 2 ^ 18.
  Hypothesis Hau : 0 <= au <= mu /\ mu + 2 ^ 18 <= 0xE0000000.
  Hypothesis Hmap : mu < au + csize c * req.
  Hypothesis HSPB : 0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 63 /\ SPB mod 4096 = 0 /\ AIMGHI <= SPB.
  Hypothesis Hmu4k : mu mod 4096 = 0.
  Hypothesis Hnf : 0 <= nf <= 2 ^ 27.
  Hypothesis HRI : AIMGHI <= RIz /\ RIz + 128 <= U sp - 464.
  Hypothesis HPGP : AIMGLO <= PGP /\ PGP + 8 <= AIMGHI.
  Hypothesis HCF : AIMGLO <= CF /\ CF + 264 <= AIMGHI.
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-464)) 464 = true.
  Hypothesis C_sbeg : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  Hypothesis R_au : rdn BSEGS mem (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis R_mu : rdn BSEGS mem (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)).
  Hypothesis R_mm : rdn BSEGS mem (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis R_nf : rdn BSEGS mem (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis C_rel : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 40)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff)).
  Hypothesis C_pre : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 56)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rgpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlim : rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Hslot : slot + 2 ^ 18 <= U sp - 464 \/ U sp <= slot.
  Hypothesis HDsbeg : hid_off Hd (0x10ab58 + 32) 8.
  Hypothesis HDrel : hid_off Hd (0x10ab58 + 40) 4.
  Hypothesis HDpre : hid_off Hd (0x10ab58 + 56) 1.
  Hypothesis HDgpg : hid_off Hd 0x105ef8 8.
  Hypothesis HDpg : hid_off Hd PGP 8.
  Hypothesis HDgcf : hid_off Hd 0x105f08 8.
  Hypothesis HDdpm : hid_off Hd (CF + 260) 1.
  Hypothesis HDlim : hid_off Hd (CF + 144) 8.
  Hypothesis HDscr : hid_off Hd (U sp - 464) 464.
  Hypothesis HALT : m_halted model = None.
  Hypothesis LC : lazy_cover Hd (m_vm_lazy model) A.
  Hypothesis AWF : A_wf A.
  Hypothesis MI : MInv A model.
  Hypothesis NODE : forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 slot -> getr r1 11 = Z_to_bv 64 (2 ^ 18) -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD BSEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x811b0 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Hypothesis CHILD : forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm)).
  Hypothesis OKSW : forall mdlm mdl4, same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        lazy_cover Hd2 (m_vm_lazy mdl4) A2 /\ MInv A2 mdl4.
  (* [comment removed for export] *)
  Hypothesis HT : U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 464 /\ T mod 8 = 0.
  Hypothesis HTRI : T + 4096 <= RIz \/ RIz + 128 <= T.
  Hypothesis HTSH : T + 4096 <= SH \/ SH + 2 ^ 15 <= T.
  Hypothesis HRSH : RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz.
  Hypothesis HTsl : T + 4096 <= slot \/ slot + 2 ^ 18 <= T.
  Hypothesis HRsl : RIz + 128 <= slot \/ slot + 2 ^ 18 <= RIz.
  Hypothesis PH : poisonH BSEGS both_poison_tab mem (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x51980) (at_ sp (-64)) cpm midend thr0.
  Hypothesis GH : gctH BSEGS both_gct_tab mem (at_ (at_ sp (-64)) (-16)) tp tsdp ctxw thr.
  Hypothesis GB : U (gt_tsd both_gct_tab) + 8 <= U sp - 464 /\ U tp - 80 <= U sp - 464 /\ U tsdp + 8 <= U sp - 464 /\ U ctxw + 160 <= U sp - 464.
  Hypothesis GS : (U (gt_tsd both_gct_tab) + 8 <= slot \/ slot + 2 ^ 18 <= U (gt_tsd both_gct_tab)) /\ (U tp - 80 <= slot \/ slot + 2 ^ 18 <= U tp - 88)
                  /\ (U tsdp + 8 <= slot \/ slot + 2 ^ 18 <= U tsdp) /\ (U ctxw + 160 <= slot \/ slot + 2 ^ 18 <= U ctxw + 152).
  Hypothesis G1 : U (gt_tsd both_gct_tab) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd both_gct_tab).
  Hypothesis G2 : U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88.
  Hypothesis G3 : U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp.
  Hypothesis G4 : U ctxw + 160 <= SH \/ SH + 2 ^ 15 <= U ctxw + 152.
  Hypothesis R72 : rdn BSEGS mem (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R80 : rdn BSEGS mem (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis Rst : rdn BSEGS mem (at_ thr 2792) 8 = Some (LE8 vst).
  Hypothesis SOKT : store_ok BSEGS mem thr 4096 = true.
  Hypothesis SOKRI : store_ok BSEGS mem (Z_to_bv 64 RIz) 128 = true.
  Hypothesis HDc : Forall (fun c => hid_off Hd2 c 8) (poison_cells both_poison_tab).
  Hypothesis HDsh : hid_off Hd2 SH (2 ^ 15).
  Hypothesis HD1 : hid_off Hd2 (U (gt_tsd both_gct_tab)) 8.
  Hypothesis HD2 : hid_off Hd2 (U tp - 88) 8.
  Hypothesis HD3 : hid_off Hd2 (U tsdp) 8.
  Hypothesis HD4 : hid_off Hd2 (U ctxw + 152) 8.
  Hypothesis HDT : hid_off Hd2 T 4096.
  Hypothesis HDRI : hid_off Hd2 RIz 128.
  Hypothesis HDscr2 : hid_off Hd2 (U sp - 464) 464.
  Hypothesis HDRIa : hid_off Hd RIz 128.
  (* [comment removed for export] *)
  Hypothesis CONT1 : forall (r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl5 -> MInv A2 mdl5 ->
      pf_regs sp RIz SPB c r -> getr r 1 = Z_to_bv 64 0x519d8 ->
      getr r 10 = Z_to_bv 64 0x10ab58 -> getr r 11 = Z_to_bv 64 RIz -> getr r 12 = Z_to_bv 64 (SPB + c * 2 ^ 32) ->
      getr r 13 = Z_to_bv 64 (nf + (mu + 2 ^ 18 - au) / csize c) ->
      getr r 9 = Z_to_bv 64 (nf + (mu + 2 ^ 18 - au) / csize c) -> getr r 19 = Z_to_bv 64 ((mu + 2 ^ 18 - au) / csize c) ->
      getr r 20 = Z_to_bv 64 (mu + 2 ^ 18 - au) -> getr r 4 = tp -> getr r 3 = gp ->
      katwD BSEGS (mkCfg (mkst r (0x4f508 : word) (pam_3 MR sp thr v72 v80 vst RIz SPB c slot mu) rom) mdl5) Qok Qf.
  Hypothesis CONT0K : forall (r' r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl5 -> MInv A mdl5 ->
      regs_agree (fun i : reg => In i pf_clob) regs r' -> pf_post0 sp ra s0v s1v s2v s3v s4v s5v s6v r' r ->
      katD BSEGS (mkCfg (mkst r ra (wbytes (wbytes M1 (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl5) Qf.


  Theorem pf_map_arm_katsD_h : katsD BSEGS (mkCfg (mkst regs (0x51844 : word) mem rom) model) Qok Qf.
  Proof using CONT0K CONT1 HDRIa HDscr2 HDRI HDT HD4 HD3 HD2 HD1 HDsh HDc SOKRI SOKT Rst R80 R72 G4 G3 G2 G1 GS GB GH PH HRsl HTsl HRSH HTSH HTRI HT OKSW CHILD NODE MI AWF LC HALT HDscr HDlim HDdpm HDgcf HDpg HDgpg HDpre HDrel HDsbeg Hslot Rlim Rdpm Rgcf Rpg Rgpg C_pre C_rel R_nf R_mm R_mu R_au C_sbeg Hstk HCF HPGP HRI Hnf Hmu4k HSPB Hmap Hau Hreq Hc Hret Hsp H22 H21 H20 H19 H18 H9 H8 H14 H13 H12 H11 H10 H3 H4 H2 H1 MKP MOK thr0 T CF PGP nf mu au req c SPB RIz cpm midend vst v80 v72 ctxw tsdp gp tp thr s6v s5v s4v s3v s2v s1v s0v ra sp A AWF2 A2 HOFFSEG2 Hd2 WX HOFFSEG Hd.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HRI as [RI1 RI2]. destruct HSPB as (S1 & S2 & S3 & S4).
    destruct Hau as [[AU0 AU1] AU2]. destruct HT as (UT & T1 & T2 & T3). pose proof (u64_range thr) as Hthr.
    assert (SL : 0 <= slot /\ slot + 2 ^ 18 < 2 ^ 63) by lia.
    assert (HDf64 : hid_off Hd (U sp - 64) 64) by (eapply hid_off_sub; [exact HDscr | lia | lia]).
    assert (HDf128 : hid_off Hd2 (U sp - 128) 64) by (eapply hid_off_sub; [exact HDscr2 | lia | lia]).
    assert (FRAMES : forall mdlx mdly, m_halted mdlx = None -> lazy_cover Hd (m_vm_lazy mdlx) A -> same_but_materialized mdlx mdly ->
               m_halted mdly = None /\ lazy_cover Hd (m_vm_lazy mdly) A).
    { intros mdlx mdly HX LX SB. pose proof (same_but_materialized_frame mdlx mdly SB) as FR. split.
      - destruct FR as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_). rewrite Hh. exact HX.
      - destruct FR as (_ & _ & Hl & _). rewrite Hl. exact LX. }
    apply (pf_usermap_katsD_h Hd HOFFSEG WX A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c req au mu PGP CF Qok Qf MOK MKP
             H1 H2 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 ltac:(lia) Hc Hreq (conj (conj AU0 AU1) AU2) Hmap (conj S1 (conj S2 (conj S3 S4))) Hmu4k (conj RI1 RI2) HPGP HCF Hstk
             C_sbeg R_au R_mu R_mm C_rel C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot
             HDsbeg ltac:(eapply hid_off_sub; [exact HDRIa | lia | lia]) ltac:(eapply hid_off_sub; [exact HDRIa | lia | lia]) ltac:(eapply hid_off_sub; [exact HDRIa | lia | lia])
             HDrel HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (PR & E9 & E19 & E20 & E22 & E10) AG.
      destruct (CHILD mdlm SBm MIm) as ((HOK & LOK & _) & _).
      destruct (FRAMES _ _ HOK LOK SB4) as [HALT4 LC4].
      destruct (OKSW mdlm mdl4 SBm MIm SB4 MI4) as [LC2 MI2].
      assert (OUT : forall x : word, (U x < U sp - 464 \/ U sp <= U x) -> (U x < slot \/ slot + 2 ^ 18 <= U x) -> MR x = mem x)
        by (intros x X1 X2; apply pf_mr_outside; [lia | exact SL | exact X1 | exact X2]).
      assert (GR : mem_grows mem MR) by apply pf_mr_grows.
      assert (RDZ : forall (z : Z) (k : nat) v, 0 <= z -> z + Z.of_nat k <= U sp - 464 -> (z + Z.of_nat k <= slot \/ slot + 2 ^ 18 <= z) ->
                 rdn BSEGS mem (Z_to_bv 64 z) k = Some v -> rdn BSEGS MR (Z_to_bv 64 z) k = Some v).
      { intros z k v Z0 Z1 Z2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        apply OUT; clear - Hx Z1 Z2; lia. }
      assert (RDT : forall (k : Z) v, 0 <= k -> k + 8 <= 4096 -> rdn BSEGS mem (at_ thr k) 8 = Some v -> rdn BSEGS MR (at_ thr k) 8 = Some v).
      { intros k v K0 K1 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
        apply OUT; clear - Hx UT T2 HTsl K0 K1; lia. }
      change (wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-148)) SCR) with MR.
      apply (pf_after_map_katwD Hd2 HOFFSEG2 WX A2 r' MR rom mdl4 sp thr tp gp tsdp ctxw v72 v80 vst midend cpm RIz SPB c au mu nf T thr0 Qok Qf
               PR ltac:(rewrite (AG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H4)
               ltac:(rewrite (AG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H3)
               E9 E10 E19 E20 E22 (conj SP1 SP2) Hc (conj (conj AU0 AU1) AU2) Hnf ltac:(lia) ltac:(lia) ltac:(lia) HTRI HTSH HRSH).
      + apply (poisonH_keep_P BSEGS both_poison_tab mem MR _ _ _ _ _ cpm midend thr0
                 (fun z => (z < U sp - 464 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) PH); [intros x [X1 X2]; apply OUT; assumption | exact GR |].
        eapply Forall_impl; [|exact both_poison_cells_img]. cbv beta. intros c0 Hc0 z Hz. lia.
      + destruct GB as (B1 & B2 & B3 & B4). destruct GS as (Q1 & Q2 & Q3 & Q4).
        apply (gctH_keep_P BSEGS both_gct_tab mem MR _ tp tsdp ctxw thr
                 (fun z => (z < U sp - 464 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) GH);
          [intros x [X1 X2]; apply OUT; assumption | exact GR
          | intros z Hz; cbv beta; clear - Hz B1 Q1; lia | intros z Hz; cbv beta; clear - Hz B2 Q2; lia
          | intros z Hz; cbv beta; clear - Hz B3 Q3; lia | intros z Hz; cbv beta; clear - Hz B4 Q4; lia].
      + destruct GB as (B1 & B2 & B3 & B4). lia.
      + exact G1.
      + exact G2.
      + exact G3.
      + exact G4.
      + apply RDT; [lia | lia | exact R72].
      + apply RDT; [lia | lia | exact R80].
      + apply RDT; [lia | lia | exact Rst].
      + apply RDZ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HRsl; lia | exact R_au].
      + apply RDZ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HRsl; lia | exact R_mu].
      + apply RDZ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HRsl; lia | exact R_nf].
      + eapply store_ok_mono; [exact GR | exact SOKT].
      + eapply store_ok_mono; [exact GR | exact SOKRI].
      + exact HDc.
      + exact HDf128.
      + exact HDsh.
      + exact HD1.
      + exact HD2.
      + exact HD3.
      + exact HD4.
      + exact HDT.
      + exact HDRI.
      + exact HALT4.
      + exact LC2.
      + exact AWF2.
      + exact MI2.
      + intros r mdl5 SB5 MI5 D0 D1 D10 D11 D12 D13 D9 D19 D20 D4 D3.
        exact (CONT1 r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 D0 D1 D10 D11 D12 D13 D9 D19 D20 D4 D3).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (PR & E9 & E19 & E20 & E22 & E10) AG.
      destruct (CHILD mdlm SBm MIm) as (_ & (HKP & LKP & _)).
      destruct (FRAMES _ _ HKP LKP SB4) as [HALT4 LC4].
      set (MK := wbytes (wbytes M1 (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))).
      assert (AGR : forall x : word, U sp - 64 <= U x < U sp -> MK x = M0 x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        apply mfi_m1_outside; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]. }
      destruct PR as (P2 & _).
      apply (pf_fail_map_katD Hd HOFFSEG WX A r' MK rom mdl4 sp ra s0v s1v s2v s3v s4v s5v s6v Qf P2 E10 Hret ltac:(lia)
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-8) ra ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-16) s0v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-24) s1v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-32) s2v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-40) s3v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-48) s4v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-56) s5v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-64) s6v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               HDf64 HALT4 LC4 AWF MI4).
      intros r mdl5 SB5 MI5 POST.
      exact (CONT0K r' r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 AG POST).
  Qed.
End PFARMH.
End FPGenPH.
End BoAllocM8pah.
Module BoAllocM8yh.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8x.
Import BoAllocM8kh BoAllocM8rh OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8y.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGenYH.
Context {fx : FPState}.

Section EFSARMH.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.
  (* [comment removed for export] *)
  Variable Hd2 : word -> bool.
  Hypothesis HOFFSEG2 : H_off_segments BSEGS Hd2.
  Variable A2 : list (Z * Z).
  Hypothesis AWF2 : A_wf A2.
  Variables (A : list (Z * Z)) (regs : bvmap 5 word) (mem rom : word -> option byte) (model : Model)
            (sp ra s0v s1v s2v s3v s4v s5v thr tp gp tsdp ctxw v72 v80 midend : word) (cpm : byte)
            (RIz rbeg tot mfa PGP CF T thr0 : Z) (Qok Qf : config -> Prop) (MOK MKP : Model -> Model).
  #[local] Abbreviation slot := (rbeg + 0xE0000000 + mfa).
  #[local] Abbreviation SH := ((rbeg + 0xE0000000 + mfa) / 8 + 0x7fff8000).
  #[local] Abbreviation M0 := (efs_m0 mem sp ra s0v s1v s2v s3v).
  #[local] Abbreviation M1 := (mfi_m1 M0 (at_ sp (-48)) (Z_to_bv 64 0x4f5a8) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz)
                     s4v s5v (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x19778) PGP).
  #[local] Abbreviation ENOMEMw := (Z_to_bv 64 (2 ^ 64 - 12) : word).
  #[local] Abbreviation SCR := (word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa)).
  #[local] Abbreviation MR := (efs_mr mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP).
  (* [comment removed for export] *)
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 RIz.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 rbeg.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 tot.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis Hsp : 2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Htot : 0 <= tot /\ 4 * tot <= 2 ^ 29.
  Hypothesis Hmfa : 0 <= mfa <= 2 ^ 29 /\ mfa mod 2 ^ 18 = 0.
  Hypothesis Hneed : mfa < 4 * tot <= mfa + 2 ^ 18.
  Hypothesis Hroom : mfa + 2 ^ 18 <= 2 ^ 29.
  Hypothesis Hrbeg : AIMGHI <= rbeg /\ rbeg + 2 ^ 32 < 2 ^ 63 /\ rbeg mod 4096 = 0.
  Hypothesis HRI : AIMGHI <= RIz /\ RIz + 128 <= U sp - 448.
  Hypothesis HPGP : AIMGLO <= PGP /\ PGP + 8 <= AIMGHI.
  Hypothesis HCF : AIMGLO <= CF /\ CF + 264 <= AIMGHI.
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-448)) 448 = true.
  Hypothesis R_mfa : rdn BSEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)).
  Hypothesis C_pre : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 56)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rgpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlim : rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Hslot : slot + 2 ^ 18 <= U sp - 448 \/ U sp <= slot.
  Hypothesis HDmfa : hid_off Hd (RIz + 24) 8.
  Hypothesis HDpre : hid_off Hd (0x10ab58 + 56) 1.
  Hypothesis HDgpg : hid_off Hd 0x105ef8 8.
  Hypothesis HDpg : hid_off Hd PGP 8.
  Hypothesis HDgcf : hid_off Hd 0x105f08 8.
  Hypothesis HDdpm : hid_off Hd (CF + 260) 1.
  Hypothesis HDlim : hid_off Hd (CF + 144) 8.
  Hypothesis HDscr : hid_off Hd (U sp - 448) 448.
  Hypothesis HALT : m_halted model = None.
  Hypothesis LC : lazy_cover Hd (m_vm_lazy model) A.
  Hypothesis AWF : A_wf A.
  Hypothesis MI : MInv A model.
  Hypothesis NODE : forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 slot -> getr r1 11 = Z_to_bv 64 (2 ^ 18) -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD BSEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x811b0 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Hypothesis CHILD : forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm)).
  Hypothesis OKSW : forall mdlm mdl4, same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        lazy_cover Hd2 (m_vm_lazy mdl4) A2 /\ MInv A2 mdl4.
  (* [comment removed for export] *)
  Hypothesis HT : U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 448 /\ T mod 8 = 0.
  Hypothesis HTRI : T + 4096 <= RIz \/ RIz + 128 <= T.
  Hypothesis HTSH : T + 4096 <= SH \/ SH + 2 ^ 15 <= T.
  Hypothesis HRSH : RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz.
  Hypothesis HSSH : U sp <= SH \/ SH + 2 ^ 15 <= U sp - 448.
  Hypothesis HTsl : T + 4096 <= slot \/ slot + 2 ^ 18 <= T.
  Hypothesis PH : poisonH BSEGS both_poison_tab mem (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x4f5c4) (at_ sp (-48)) cpm midend thr0.
  Hypothesis PCB : Forall (fun c => c + 8 <= AIMGHI) (poison_cells both_poison_tab).
  Hypothesis GH : gctH BSEGS both_gct_tab mem (at_ (at_ sp (-48)) (-16)) tp tsdp ctxw thr.
  Hypothesis GB : U (gt_tsd both_gct_tab) + 8 <= U sp - 448 /\ U tp - 80 <= U sp - 448 /\ U tsdp + 8 <= U sp - 448 /\ U ctxw + 160 <= U sp - 448.
  Hypothesis GS : (U (gt_tsd both_gct_tab) + 8 <= slot \/ slot + 2 ^ 18 <= U (gt_tsd both_gct_tab)) /\ (U tp - 80 <= slot \/ slot + 2 ^ 18 <= U tp - 88)
                  /\ (U tsdp + 8 <= slot \/ slot + 2 ^ 18 <= U tsdp) /\ (U ctxw + 160 <= slot \/ slot + 2 ^ 18 <= U ctxw + 152).
  Hypothesis G1 : U (gt_tsd both_gct_tab) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd both_gct_tab).
  Hypothesis G2 : U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88.
  Hypothesis G3 : U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp.
  Hypothesis G4 : U ctxw + 160 <= SH \/ SH + 2 ^ 15 <= U ctxw + 152.
  Hypothesis R72 : rdn BSEGS mem (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R80 : rdn BSEGS mem (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis SOKT : store_ok BSEGS mem thr 4096 = true.
  Hypothesis SOKRI : store_ok BSEGS mem (Z_to_bv 64 RIz) 128 = true.
  Hypothesis HDc : Forall (fun c => hid_off Hd2 c 8) (poison_cells both_poison_tab).
  Hypothesis HDsh : hid_off Hd2 SH (2 ^ 15).
  Hypothesis HD1 : hid_off Hd2 (U (gt_tsd both_gct_tab)) 8.
  Hypothesis HD2 : hid_off Hd2 (U tp - 88) 8.
  Hypothesis HD3 : hid_off Hd2 (U tsdp) 8.
  Hypothesis HD4 : hid_off Hd2 (U ctxw + 152) 8.
  Hypothesis HDT : hid_off Hd2 T 4096.
  Hypothesis HDRI : hid_off Hd2 RIz 128.
  Hypothesis HDscr2 : hid_off Hd2 (U sp - 448) 448.
  (* [comment removed for export] *)
  Hypothesis CONT1 : forall (r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl5 -> MInv A2 mdl5 ->
      getr r 10 = Z_to_bv 64 1 -> getr r 2 = sp -> getr r 1 = ra ->
      getr r 8 = s0v -> getr r 9 = s1v -> getr r 18 = s2v -> getr r 19 = s3v -> getr r 20 = s4v -> getr r 21 = s5v -> getr r 4 = tp -> getr r 3 = gp ->
      katwD BSEGS (mkCfg (mkst r ra (eam_3 MR sp s4v s5v thr v72 v80 RIz slot mfa) rom) mdl5) Qok Qf.
  Hypothesis CONT0K : forall (r' r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl5 -> MInv A mdl5 ->
      regs_agree (fun i : reg => In i efs_clob) regs r' -> efs_post sp ra s0v s1v s2v s3v 0 r' r ->
      katD BSEGS (mkCfg (mkst r ra (wbytes (wbytes M1 (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl5) Qf.


  Theorem efs_map_arm_katwD_h : katwD BSEGS (mkCfg (mkst regs (0x4f508 : word) mem rom) model) Qok Qf.
  Proof using CONT0K CONT1 HDscr2 HDRI HDT HD4 HD3 HD2 HD1 HDsh HDc SOKRI SOKT R80 R72 G4 G3 G2 G1 GS GB GH PCB PH HTsl HSSH HRSH HTSH HTRI HT OKSW CHILD NODE MI AWF LC HALT HDscr HDlim HDdpm HDgcf HDpg HDgpg HDpre HDmfa Hslot Rlim Rdpm Rgcf Rpg Rgpg C_pre R_mfa Hstk HCF HPGP HRI Hrbeg Hroom Hneed Hmfa Htot Hret Hsp H21 H20 H19 H18 H9 H8 H13 H12 H11 H10 H3 H4 H2 H1 MKP MOK thr0 T CF PGP mfa tot rbeg RIz cpm midend v80 v72 ctxw tsdp gp tp thr s5v s4v s3v s2v s1v s0v ra sp A AWF2 A2 HOFFSEG2 Hd2 WX HOFFSEG Hd.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HRI as [RI1 RI2]. destruct Hrbeg as (RB1 & RB2 & RB3).
    destruct Hmfa as [[MF1 MF2] MF3]. destruct HT as (UT & T1 & T2 & T3). pose proof (u64_range thr) as Hthr.
    assert (SL : 0 <= slot /\ slot + 2 ^ 18 < 2 ^ 63) by lia.
    assert (HDf48 : hid_off Hd (U sp - 48) 48) by (eapply hid_off_sub; [exact HDscr | lia | lia]).
    assert (HDf112 : hid_off Hd2 (U sp - 112) 112) by (eapply hid_off_sub; [exact HDscr2 | lia | lia]).
    assert (FRAMES : forall mdlx mdly, m_halted mdlx = None -> lazy_cover Hd (m_vm_lazy mdlx) A -> same_but_materialized mdlx mdly ->
               m_halted mdly = None /\ lazy_cover Hd (m_vm_lazy mdly) A).
    { intros mdlx mdly HX LX SB. pose proof (same_but_materialized_frame mdlx mdly SB) as FR. split.
      - destruct FR as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_). rewrite Hh. exact HX.
      - destruct FR as (_ & _ & Hl & _). rewrite Hl. exact LX. }
    apply katsD_katwD.
    apply (efs_famap_katsD_h Hd HOFFSEG WX A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v RIz rbeg tot mfa PGP CF Qok Qf MOK MKP
             H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 ltac:(lia) Htot (conj (conj MF1 MF2) MF3) Hneed Hroom (conj RB1 (conj RB2 RB3)) (conj RI1 RI2) HPGP HCF Hstk
             R_mfa C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot HDmfa HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (E2 & E8 & E9 & E18 & E19 & E10 & E20) AG.
      destruct (CHILD mdlm SBm MIm) as ((HOK & LOK & _) & _).
      destruct (FRAMES _ _ HOK LOK SB4) as [HALT4 LC4].
      destruct (OKSW mdlm mdl4 SBm MIm SB4 MI4) as [LC2 MI2].
      assert (OUT : forall x : word, (U x < U sp - 448 \/ U sp <= U x) -> (U x < slot \/ slot + 2 ^ 18 <= U x) -> MR x = mem x)
        by (intros x X1 X2; apply efs_mr_outside; [lia | exact SL | exact X1 | exact X2]).
      assert (GR : mem_grows mem MR) by apply efs_mr_grows.
      change (wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-132)) SCR) with MR.
      apply (efs_after_map_katwD Hd2 HOFFSEG2 WX A2 r' MR rom mdl4 sp ra s0v s1v s2v s3v s4v s5v thr tp gp tsdp ctxw v72 v80 midend cpm RIz slot mfa T thr0 Qok Qf
               E2 ltac:(rewrite (AG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H4)
               ltac:(rewrite (AG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H3)
               E8 E9 E10 E18 E19 E20
               ltac:(rewrite (AG 21%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H21)
               (conj SP1 SP2) Hret ltac:(lia) (conj MF1 MF2) ltac:(lia) ltac:(lia) HTRI HTSH HRSH ltac:(clear - HSSH; lia)).
      + (* [comment removed for export] *)
        apply (poisonH_keep_P BSEGS both_poison_tab mem MR _ _ _ _ _ cpm midend thr0
                 (fun z => (z < U sp - 448 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) PH); [intros x [X1 X2]; apply OUT; assumption | exact GR |].
        eapply Forall_impl; [|exact PCB]. cbv beta. intros c Hc z Hz. lia.
      + (* [comment removed for export] *)
        destruct GB as (B1 & B2 & B3 & B4). destruct GS as (S1 & S2 & S3 & S4).
        apply (gctH_keep_P BSEGS both_gct_tab mem MR _ tp tsdp ctxw thr
                 (fun z => (z < U sp - 448 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) GH); [intros x [X1 X2]; apply OUT; assumption | exact GR
                 | intros z Hz; cbv beta; clear - Hz B1 S1; lia | intros z Hz; cbv beta; clear - Hz B2 S2; lia
                 | intros z Hz; cbv beta; clear - Hz B3 S3; lia | intros z Hz; cbv beta; clear - Hz B4 S4; lia].
      + destruct GB as (B1 & B2 & B3 & B4). lia.
      + exact G1.
      + exact G2.
      + exact G3.
      + exact G4.
      + rewrite <- R72. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply OUT; clear - Hx UT T2 HTsl; lia.
      + rewrite <- R80. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply OUT; clear - Hx UT T2 HTsl; lia.
      + eapply store_ok_mono; [exact GR | exact SOKT].
      + eapply store_ok_mono; [exact GR | exact SOKRI].
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-8) ra Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-16) s0v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-24) s1v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-32) s2v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-40) s3v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + exact HDc.
      + exact HDf112.
      + exact HDsh.
      + exact HD1.
      + exact HD2.
      + exact HD3.
      + exact HD4.
      + exact HDT.
      + exact HDRI.
      + exact HALT4.
      + exact LC2.
      + exact AWF2.
      + exact MI2.
      + intros r mdl5 SB5 MI5 C10 C2 C1 C8 C9 C18 C19 C20 C21 C4 C3.
        exact (CONT1 r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 C10 C2 C1 C8 C9 C18 C19 C20 C21 C4 C3).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (E2 & E8 & E9 & E18 & E19 & E10 & E20) AG.
      destruct (CHILD mdlm SBm MIm) as (_ & (HKP & LKP & _)).
      destruct (FRAMES _ _ HKP LKP SB4) as [HALT4 LC4].
      set (MK := wbytes (wbytes M1 (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))).
      assert (AGR : forall x : word, U sp - 48 <= U x < U sp -> MK x = M0 x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        apply mfi_m1_outside; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]. }
      apply (efs_fail_katD Hd HOFFSEG WX A r' MK rom mdl4 sp ra s0v s1v s2v s3v Qf E2 Hret E10 ltac:(lia)
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-8) ra ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-16) s0v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-24) s1v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-32) s2v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-40) s3v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               HDf48 HALT4 LC4 AWF MI4).
      intros r mdl5 SB5 MI5 POST.
      exact (CONT0K r' r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 AG POST).
  Qed.
End EFSARMH.
End FPGenYH.
End BoAllocM8yh.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8z.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section PAMRD.
  Variables (segs : list Segment) (M : word -> option byte) (sp thr v72 v80 vst : word) (RIz SPB c slot mu : Z).
  Hypothesis Hsp : 4096 <= U sp.
  Hypothesis Hslot : 0 <= slot < 2 ^ 63.
  Hypothesis HT : U thr + 4096 <= 2 ^ 64.
  Hypothesis HRI : 0 <= RIz /\ RIz + 128 <= 2 ^ 64.
  #[local] Abbreviation P3 := (pam_3 M sp thr v72 v80 vst RIz SPB c slot mu).
  #[local] Abbreviation SH := (slot / 8 + 0x7fff8000).

  Lemma pam_3_mu : rdn segs P3 (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 (mu + 2 ^ 18))).
  Proof using HRI. (lazymatch goal with |- ?G => let G' := eval unfold pam_3, pf_ms in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. Qed.


End PAMRD.

Section EAMRD.
  Variables (segs : list Segment) (M : word -> option byte) (sp s4x s5x thr v72 v80 : word) (RIz slot mfa : Z).
  Hypothesis Hsp : 4096 <= U sp.
  Hypothesis Hslot : 0 <= slot < 2 ^ 63.
  Hypothesis HT : U thr + 4096 <= 2 ^ 64.
  Hypothesis HRI : 0 <= RIz /\ RIz + 128 <= 2 ^ 64.
  #[local] Abbreviation E3 := (eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa).
  #[local] Abbreviation SH := (slot / 8 + 0x7fff8000).

  Lemma eam_3_mfa : rdn segs E3 (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 (mfa + 2 ^ 18))).
  Proof using HRI. (lazymatch goal with |- ?G => let G' := eval unfold eam_3, efs_ms in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. Qed.


End EAMRD.

(* [comment removed for export] *)
Lemma firstn1_skipn_repeat : forall {A} (b : A) (n i : nat), (i < n)%nat -> firstn 1 (skipn i (repeat b n)) = [b].
Proof.
  intros A b n. induction n as [|n IH]; intros i Hi; [lia|]. destruct i as [|i]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [repeat skipn] in G in change_no_check G' end). apply IH. lia.
Qed.

Lemma psfill_fill : forall segs M (fsp ra s0 s1 s2 s3 s4 s5 : word) slot (i : Z), 0 <= slot < 2 ^ 63 -> 0 <= i < 2 ^ 15 ->
  rdn segs (psfill M fsp ra s0 s1 s2 s3 s4 s5 slot) (Z_to_bv 64 (slot / 8 + 0x7fff8000 + i)) 1 = Some [cbyte (Z_to_bv 64 250)].
Proof.
  intros segs M fsp ra s0 s1 s2 s3 s4 s5 slot i Hs Hi. destruct (psfill_shad slot Hs) as (E1 & E2 & E3).
  assert (0 <= slot / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  (lazymatch goal with |- ?G => let G' := eval unfold psfill in G in change_no_check G' end).
  replace (Z_to_bv 64 (slot / 8 + 0x7fff8000 + i)) with (at_ (Z_to_bv 64 (shad (Z_to_bv 64 slot))) (Z.of_nat (Z.to_nat i)))
    by (apply bv_eq; rewrite at_u by (rewrite E3, Z2Nat.id by lia; lia); rewrite E3, Z2Nat.id, u_Z2bv by lia; reflexivity).
  rewrite rdn_wbytes_sub; [ | rewrite repeat_length, E2; lia | rewrite repeat_length, E2, E3; lia].
  rewrite firstn1_skipn_repeat by (rewrite E2; lia). reflexivity.
Qed.

Section FILLRD.
  Variables (segs : list Segment) (M : word -> option byte) (sp thr v72 v80 : word) (RIz slot : Z).
  Hypothesis Hsp : 4096 <= U sp /\ U sp < 2 ^ 63.
  Hypothesis Hslot : 0 <= slot < 2 ^ 63.
  Hypothesis HT : U thr + 4096 <= 2 ^ 63.
  Hypothesis HRI : 0 <= RIz /\ RIz + 128 <= 2 ^ 63.
  #[local] Abbreviation SH := (slot / 8 + 0x7fff8000).
  Hypothesis HSSH : U sp <= SH \/ SH + 2 ^ 15 <= U sp - 128.
  Hypothesis HTSH : U thr + 4096 <= SH \/ SH + 2 ^ 15 <= U thr.
  Hypothesis HRSH : RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz.

  Lemma pam_3_fill : forall (vst : word) SPB c mu (i : Z), 0 <= i < 2 ^ 15 ->
    rdn segs (pam_3 M sp thr v72 v80 vst RIz SPB c slot mu) (Z_to_bv 64 (SH + i)) 1 = Some [cbyte (Z_to_bv 64 250)].
  Proof using HRSH HTSH HSSH HRI HT Hslot Hsp.
    intros vst SPB c mu i Hi. destruct Hsp as [SP1 SP2]. destruct HRI as [R0 R1].
    assert (0 <= slot / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite <- (psfill_fill segs M (at_ sp (-64)) (Z_to_bv 64 0x51980) (Z_to_bv 64 RIz) (at_ thr 2768) (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18))
                  (Z_to_bv 64 slot) (Z_to_bv 64 (csize c)) slot i Hslot Hi).
    rewrite <- pam_1_eq. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
    (lazymatch goal with |- ?G => let G' := eval unfold pam_3 in G in change_no_check G' end). rewrite pf_ms_outside by lia. rewrite pam_2_eq, gts2_outside by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]). reflexivity.
  Qed.

  Hypothesis HSSHe : U sp <= SH \/ SH + 2 ^ 15 <= U sp - 112.
  Lemma eam_3_fill : forall (s4x s5x : word) mfa (i : Z), 0 <= i < 2 ^ 15 ->
    rdn segs (eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa) (Z_to_bv 64 (SH + i)) 1 = Some [cbyte (Z_to_bv 64 250)].
  Proof using HSSHe HRSH HTSH HSSH HRI HT Hslot Hsp.
    intros s4x s5x mfa i Hi. destruct Hsp as [SP1 SP2]. destruct HRI as [R0 R1].
    assert (0 <= slot / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite <- (psfill_fill segs M (at_ sp (-48)) (Z_to_bv 64 0x4f5c4) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz) s4x s5x slot i Hslot Hi).
    rewrite <- eam_1_eq. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
    (lazymatch goal with |- ?G => let G' := eval unfold eam_3 in G in change_no_check G' end). rewrite efs_ms_outside by lia. rewrite eam_2_eq, gts2_outside by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]). reflexivity.
  Qed.
End FILLRD.
End BoAllocM8z.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMHypR.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvOpsCI3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 BoAllocMHyp.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Lemma icmc_cache_max : forall i, 1 <= i <= 30 -> icmc i = cache_max i /\ iccs i = csize i.
Proof.
  intros i Hi.
  assert (C : forall k : nat, (k < 30)%nat -> icmc (Z.of_nat k + 1) = cache_max (Z.of_nat k + 1) /\ iccs (Z.of_nat k + 1) = csize (Z.of_nat k + 1)).
  { intros k Hk. do 30 (destruct k as [|k]; [split; vm_compute; reflexivity|]). lia. }
  destruct (C (Z.to_nat (i - 1)) ltac:(lia)) as [A B]. rewrite Z2Nat.id in A, B by lia. replace (i - 1 + 1) with i in A, B by lia. exact (conj A B).
Qed.

Section REFILLK.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)) (M : mem) (mdl : Model) (n : Z).
  Hypothesis W : WF bt st Lc FF.
  Hypothesis RP : Rep bt st Lc FF M mdl.
  Hypothesis Hn : 1 <= n <= 64512.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SG := (bt_segs bt).
  Definition rk_c : Z := class_of (needed n).
  #[local] Abbreviation c := rk_c.
  Definition rk_fl : list Z := r_free (a_reg st c).
  Definition rk_len : Z := Z.of_nat (length rk_fl).
  Definition rk_m : Z := cache_hint c.
  Hypothesis HC0 : a_cache st c = [].
  Hypothesis Hm : rk_m <= rk_len.

  Definition rk_faf (j : Z) : Z := nth (Z.to_nat j) rk_fl 0.





  Lemma rk_c_range : 1 <= c <= 30.
  Proof using Hn. (lazymatch goal with |- ?G => let G' := eval unfold rk_c in G in change_no_check G' end). pose proof (needed_facts n Hn) as [N1 N2]. apply class_of_range. lia. Qed.






  (* [comment removed for export] *)
  Lemma rk_cells :
    cellZ SG M (T + T_PC + PC_SZ * c) 4 0
    /\ cellZ SG M (T + T_PC + PC_SZ * c + 4) 4 (if a_cinit st then cache_max c else 0)
    /\ cellZ SG M (T + T_PC + PC_SZ * c + 8) 8 (if a_cinit st then csize c else 0)
    /\ cellZ SG M (reginfo bt c) 8 0 /\ cellZ SG M (reginfo bt c + 16) 8 rk_len /\ writableZ SG M (reginfo bt c) (reginfo bt c + 128)
    /\ (forall j, 0 <= j < rk_len -> cellZ SG M (fa_beg SBEG c + 4 * j) 4 (rk_faf j) /\ 0 <= rk_faf j < 2 ^ 32)
    /\ writableZ SG M (region_beg SBEG c) (region_beg SBEG c + r_mapped_user (a_reg st c))
    /\ writableZ SG M T (T + PG).
  Proof using HC0 Hn RP W mdl FF Lc RC.
    pose proof rk_c_range as Hc.
    pose proof RP as (R1 & R2 & R3 & R4 & _). destruct R3 as (_ & _ & _ & _ & _ & _ & _ & TPC & TW & _).
    destruct (TPC c Hc) as (P1 & P2 & P3 & P4). rewrite HC0 in P1. cbn [length Z.of_nat] in P1.
    destruct (R4 c Hc) as [(G1 & _ & G3 & _ & _ & _ & _ & _ & _ & GW) (F1 & F2 & F3)]. fold rk_fl in G3. fold rk_len in G3.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & Y9 & _). fold rk_fl in Y9.
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact G1|]. split; [exact G3|]. split; [exact GW|].
    split; [| exact (conj F3 TW)].
    intros j Hj.
    assert (NTH : nth_error rk_fl (Z.to_nat j) = Some (rk_faf j)).
    { (lazymatch goal with |- ?G => let G' := eval unfold rk_faf in G in change_no_check G' end). destruct (nth_error rk_fl (Z.to_nat j)) as [v|] eqn:E.
      - f_equal. symmetry. apply nth_error_nth. exact E.
      - exfalso. apply nth_error_None in E. unfold rk_len in Hj. lia. }
    split.
    - pose proof (F1 (Z.to_nat j) (rk_faf j) NTH) as X. rewrite Z2Nat.id in X by lia. exact X.
    - apply (proj1 (Y9 (rk_faf j) ltac:(eapply nth_error_In; exact NTH))).
  Qed.

  (* [comment removed for export] *)
  Lemma rk_geom :
    0 < SBEG /\ SBEG mod 2 ^ 16 = 0 /\ AS_HEAPLO <= SBEG /\ SBEG + KSPACE + PG <= CEIL
    /\ (T + PG <= SBEG \/ SBEG + KSPACE + PG <= T)
    /\ (bt_tctx bt + 0x10000 <= SBEG \/ SBEG + KSPACE + PG <= bt_tctx bt)
    /\ reginfo bt c = SBEG + KSPACE + 128 * c /\ fa_beg SBEG c = SBEG + c * 2 ^ 32 + 3758096384
    /\ 4 * rk_len <= r_mapped_fa (a_reg st c) <= 2 ^ 29 /\ 0 <= rk_len
    /\ region_beg SBEG c = SBEG + c * 2 ^ 32 /\ 0 <= r_mapped_user (a_reg st c) /\ region_beg SBEG c + r_mapped_user (a_reg st c) <= fa_beg SBEG c
    /\ 0 < T /\ T + PG <= CEIL /\ 0 < bt_tctx bt /\ bt_tctx bt + 0x10000 <= CEIL.
  Proof using Hn W FF Lc.
    pose proof rk_c_range as Hc.
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _ & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & _).
    pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as TS.
    pose proof (space_vs_fixed bt st Lc FF W _ _ INC ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as CS.
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    fold rk_fl in E7. fold rk_len in E7.
    split; [lia|]. split; [exact S3|]. split; [lia|]. split; [exact S2|]. split; [exact TS|]. split; [exact CS|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end); reflexivity|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end); reflexivity|].
    split; [lia|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold rk_len in G in change_no_check G' end); lia|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold region_beg, KREGION in G in change_no_check G' end); reflexivity|]. split; [lia|]. split; [lia|].
    exact (conj X1 (conj X2 (conj X3 X4))).
  Qed.

























End REFILLK.
End BoAllocMHypR.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La.BoAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8y BoAllocM8z BoAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La BoAllocM8Lk.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod4096_sum : forall x y, x mod 4096 = 0 -> y mod 4096 = 0 -> (x + y) mod 4096 = 0.
Proof. intros x y Hx Hy. lia. Qed.
Lemma pos_mod4096 : forall t, 0 < t -> t mod 4096 = 0 -> 4096 <= t /\ t mod 8 = 0.
Proof. intros t H0 Ht. lia. Qed.
Lemma mod8_of_4096_sum : forall x y, x mod 4096 = 0 -> y mod 4096 = 0 -> (x + y) mod 8 = 0.
Proof. intros x y Hx Hy. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Variable X : Z -> Prop.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation XL := (XL bt X).
  #[local] Abbreviation IA := (bt_ia bt).

  (* [comment removed for export] *)
  Definition famap_ledger (st : ast) (c : Z) (mdl mdl' : Model) : Prop :=
    let lo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    (r_fhole (a_reg st c) = false -> vm_maps (m_vmmaps mdl') = vm_maps (m_vmmaps mdl))
    /\ (r_fhole (a_reg st c) = true -> Permutation (vm_maps (m_vmmaps mdl')) ((Z_to_bv 64 lo, Z_to_bv 64 KFAMAP) :: vm_maps (m_vmmaps mdl)))
    /\ (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (lo <= a < lo + KFAMAP))
    /\ Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl'))
    /\ (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + KFAMAP))
    /\ Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0 /\ 0 < bv_unsigned (fst iv)
                                   /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                   /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo IA \/ ia_img_hi IA <= bv_unsigned (fst iv)))
              (m_vm_lazy mdl')
    /\ vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl)
    /\ vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl)
    /\ vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl)
    /\ eager_used mdl' <= eager_used mdl + KFAMAP.

  (* [comment removed for export] *)
  Definition N3F_stmt : Prop := forall st Lc FF M0 mdl c,
    WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> 1 <= c <= 30 -> r_fhole (a_reg st c) = false ->
    r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 -> BackingAlgebra.model_ivs_wf mdl -> m_halted mdl = None -> a_kact st <= KCAP ->
    let lo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    let addr : word := Z_to_bv 64 lo in let size : word := Z_to_bv 64 KFAMAP in
    let A2 := a_aa st ++ [(sh_lo lo, sh_lo lo + KFAMAP / 8)] in
    let OK := fixedin_ok_model 3 (Z_to_bv 64 50) addr size in let DS := fixedin_destroyed_model addr size in
    A_wf A2
    /\ (forall mdlm, same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
          U addr + U size <= alloc_top (m_vmmaps mdlm) /\ alloc_top (m_vmmaps mdlm) < two_pow_64
          /\ region_free (vm_reserved (m_vmmaps mdlm)) addr size = true /\ map_contains (vm_maps (m_vmmaps mdlm)) addr size = true
          /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdlm addr size = true
          /\ m_halted (OK mdlm) = None /\ MInv (a_aa st) (OK mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (OK mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true)
          /\ m_halted (DS mdlm) = None /\ MInv (a_aa st) (DS mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (DS mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true))
    /\ (forall mdlm mdl4, same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl4 -> MInv (a_aa st) mdl4 -> MInv A2 mdl4)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl' ->
          famap_ledger st c mdl mdl' /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (DS mdlm) mdl' ->
          ledger_destroyed bt mdl mdl' lo KFAMAP /\ eager_used mdl' <= eager_used mdl
          /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None).
  Hypothesis N3F : N3F_stmt.


  (* [comment removed for export] *)
  Lemma writableZ_of_def : forall (M : mem) lo hi, 0 <= lo -> hi < 2 ^ 64 -> (forall i, lo <= i < hi -> M (Z_to_bv 64 i) <> None) -> writableZ BSEGS M lo hi.
  Proof using.
    intros M lo hi L0 H1 DEF i Hi. split; [exact (DEF i Hi)|]. apply store_ok_of_all; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. assert (x = Z_to_bv 64 i) as -> by (apply bv_eq; rewrite u_Z2bv by lia; lia).
    (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). pose proof (DEF i Hi) as Dd. destruct (M (Z_to_bv 64 i)); [discriminate | exfalso; exact (Dd eq_refl)].
  Qed.
  Lemma lazy_kept_sbm : forall Lc FF mdl mdl', same_but_materialized mdl mdl' -> lazy_kept IA Lc FF mdl mdl'.
  Proof using.
    intros Lc FF mdl mdl' S a _. pose proof (same_but_materialized_frame mdl mdl' S) as (_ & _ & E & _). (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). rewrite E. reflexivity.
  Qed.
  Lemma halted_sbm : forall mdl mdl', same_but_materialized mdl mdl' -> m_halted mdl = None -> m_halted mdl' = None.
  Proof using. intros mdl mdl' S H. pose proof (same_but_materialized_frame mdl mdl' S) as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_). rewrite Hh. exact H. Qed.

  Theorem popBf_katwD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (sp ra s0v s1v s2v s3v s4v s5v tp gp : word) (tot : Z) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    r_fhole (a_reg st c) = false -> r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    r_mapped_fa (a_reg st c) <= 4 * (r_mapped_user (a_reg st c) / csize c) -> a_kact st <= KCAP ->       (* [comment removed for export] *)
    let r := a_reg st c in let mfa := r_mapped_fa r in let lo := fa_beg SBEG c + mfa in
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (lo <= z < lo + KFAMAP) /\ ~ (sh_lo lo <= z < sh_lo lo + KFAMAP / 8)) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 0x10ab58 ->
    getr regs 11 = Z_to_bv 64 (reginfo bt c) -> getr regs 12 = Z_to_bv 64 (region_beg SBEG c) -> getr regs 13 = Z_to_bv 64 tot ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (CEIL + 448 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra -> (0 <= tot /\ 4 * tot <= 2 ^ 29) -> (mfa < 4 * tot <= mfa + 2 ^ 18) ->
    writableZ BSEGS M (U sp - 448) (U sp) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        let st' := add_meter (op_famap st c) 0 [(sh_lo lo, sh_lo lo + KFAMAP / 8)] 0 in
        WF bt st' Lc FF -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a ->
            ((U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + KFAMAP) \/ (sh_lo lo <= U a < sh_lo lo + KFAMAP / 8)
             \/ (T + 2872 <= U a < T + 2888) \/ (reginfo bt c + 24 <= U a < reginfo bt c + 32)) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = sp -> getr r' 1 = ra ->
        getr r' 8 = s0v -> getr r' 9 = s1v -> getr r' 18 = s2v -> getr r' 19 = s3v -> getr r' 20 = s4v -> getr r' 21 = s5v -> getr r' 4 = tp -> getr r' 3 = gp ->
        katwD BSEGS (mkCfg (mkst r' ra M' rom) mdl') Qok Qf) ->
    (* [comment removed for export] *)
    (forall (r0 r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ st' = op_fhole st c) ->
        WF bt st' Lc FF -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> ((U sp - 448 <= U a < U sp) /\ M' a <> None) \/ (lo <= U a < lo + KFAMAP)) ->
        regs_agree (fun i : reg => In i efs_clob) regs r0 -> efs_post sp ra s0v s1v s2v s3v 0 r0 r' ->
        katD BSEGS (mkCfg (mkst r' ra M' rom) mdl') Qf) ->
    katwD BSEGS (mkCfg (mkst regs (0x4f508%bv : word) M rom) mdl) Qok Qf.
  Proof using N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v tp gp tot Qok Qf Hc W RX HALT MW FH ROOM FAQ KC r mfa lo XOFF
           H1 H2 H4 H3 Etp H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Hret Htot Hneed WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range sp) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14). fold mfa in E6, E7, E14.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & Y5 & Y6 & _). fold r mfa in Y5, Y6.
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CREST).
    assert (G_consts : 0x10000 <= TSDP /\ TSDP + 8 <= 0x663000 /\ 0x10000 <= PGP /\ PGP + 8 <= 0x663000 /\ 0x10000 + 88 <= TP /\ TP + 0x40 <= 0x663000).
    { do 32 (destruct CREST as (_ & CREST)). destruct CREST as (A1 & A2 & A3 & A4 & _ & _ & _ & A8 & A9). repeat split; assumption. }
    destruct G_consts as (Gs1 & Gs2 & Gp1 & Gp2 & Gt1 & Gt2).
    pose proof PCELLS as (PC_rel & PC_rib & PC_pre & PC_dpm & PC_lim).
    set (RIz := reginfo bt c) in *. set (rbeg := region_beg SBEG c) in *.
    assert (ERI : RIz = SBEG + KSPACE + 128 * c) by reflexivity.
    assert (ERB : rbeg = SBEG + c * 2 ^ 32) by ((lazymatch goal with |- ?G => let G' := eval unfold rbeg, region_beg, KREGION in G in change_no_check G' end); reflexivity).
    assert (ELO : lo = rbeg + 0xE0000000 + mfa) by ((lazymatch goal with |- ?G => let G' := eval unfold lo, fa_beg, KFAOFF in G in change_no_check G' end); fold rbeg; reflexivity).
    assert (ESH : sh_lo lo = (rbeg + 0xE0000000 + mfa) / 8 + 0x7fff8000) by (rewrite ELO; (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end); lia).
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct (R4 c Hc) as [(G0 & G8 & G16 & G24 & G32 & G40 & G48 & G56 & G68 & GW) (F1 & F2 & F3)]. fold r RIz mfa in G24, GW.
    rewrite BT_segs in *. destruct R14 as (Bw1 & Bw2 & _).
    (* [comment removed for export] *)
    pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & C1 & C2 & T4k & TIMG & CIMG).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (TBAND & CBAND & TSP & CSP & S1 & S2 & S3).
    unfold KSPACE, PG, KFAMAP, KFAOFF, AS_HEAPLO, AS_LO in *.
    assert (SLOT : SBEG <= lo /\ lo + 2 ^ 18 <= SBEG + 2 ^ 37 /\ lo mod 8 = 0).
    { split; [rewrite ELO, ERB; lia|]. split; [rewrite ELO; fold rbeg in E5; unfold fa_beg in E5; lia|].
      (lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end). apply mod8_of_4096_sum; [exact E12 | exact E14]. }
    destruct SLOT as (SL0 & SL1 & SL8).
    assert (SLa : 17594333495296 <= lo) by lia.
    assert (SLb : lo + 2 ^ 18 <= CEIL) by lia.
    destruct (sh_band lo (2 ^ 18) SLa ltac:(lia) SLb ltac:(reflexivity)) as (SHB0 & SHB1 & SHB2).
    unfold AS_GAPHI, AS_HEAPLO in SHB0, SHB1. replace (2 ^ 18 / 8) with (2 ^ 15) in SHB1, SHB2 by reflexivity.
    set (SH := sh_lo lo) in *. assert (ESH' : SH = SB + lo / 8) by reflexivity. rewrite <- ESH' in SHB0, SHB1, SHB2.
    (* [comment removed for export] *)
    assert (YIMG : forall z, XL c z -> ~ (AIMGLO <= z < AIMGHI)).
    { intros z [Hx | Hl]; [exact (proj1 (proj2 (XOFF z Hx))) | fold RIz in Hl; lia]. }
    assert (YCTX : forall z, XL c z -> ~ (CTX + 152 <= z < CTX + 160)).
    { intros z [Hx | Hl]; [exact (proj1 (proj2 (proj2 (XOFF z Hx)))) | fold RIz in Hl; clear - Hl CSP ERI E9 E10 C1; lia]. }
    assert (XRI : forall i, RIz + 8 <= i < RIz + 128 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj1 (XOFF i Hx) ltac:(fold RIz; lia)) | fold RIz in Hl; lia]. }
    assert (XSL : forall i, lo <= i < lo + 2 ^ 18 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj1 (proj2 (proj2 (proj2 (XOFF i Hx)))) Hi) | fold RIz in Hl; lia]. }
    assert (XSH : forall i, SH <= i < SH + 2 ^ 15 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [apply (proj2 (proj2 (proj2 (proj2 (XOFF i Hx))))); fold SH; replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; exact Hi | fold RIz in Hl; lia]. }
    (* [comment removed for export] *)
    destruct (N3F st Lc FF M0 mdl c W RP Hc FH ROOM MW HALT KC) as (AWF2 & NODEF & BUD & LEDOK & LEDDS).
    fold r mfa lo SH in AWF2, NODEF, BUD, LEDOK, LEDDS. unfold KFAMAP in AWF2, NODEF, BUD, LEDOK, LEDDS.
    set (addr := Z_to_bv 64 lo : word) in *. set (size := Z_to_bv 64 (2 ^ 18) : word) in *.
    set (A2 := a_aa st ++ [(SH, SH + 2 ^ 18 / 8)]) in *.
    set (OKm := fixedin_ok_model 3 (Z_to_bv 64 50) addr size) in *. set (DSm := fixedin_destroyed_model addr size) in *.
    (* [comment removed for export] *)
    set (Hd := HID st mdl). set (Hd2 := mkH (m_vm_lazy mdl) A2).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NH2s : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz Hr. exact (mkH_off_zone bt BT_ia st mdl A2 z R13 Hz Hr). }
    assert (NH2ri : forall z, RIz <= z < RIz + 128 -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NH2rt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_notlazy; [clear - Hz T1 T2 C1 C2 CR; lia|]. exact (pk_nolazy_rt bt st Lc FF M0 mdl W RP z Hz). }
    assert (NH2sh : forall z, SH <= z < SH + 2 ^ 15 -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_allowed. (lazymatch goal with |- ?G => let G' := eval unfold A2 in G in change_no_check G' end). apply (range_allowed_last (a_aa st) SH (SH + 2 ^ 18 / 8)); [ | | lia | replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; lia | replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; exact Hz].
      - pose proof AWF2 as AW. unfold A2, A_wf in AW. apply Forall_app in AW as [_ AW]. apply Forall_cons_iff in AW as [(_ & AW1 & _) _]. cbn [fst] in AW1. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact AW1.
      - pose proof AWF2 as AW. unfold A2, A_wf in AW. apply Forall_app in AW as [_ AW]. apply Forall_cons_iff in AW as [(_ & _ & AW2) _]. cbn [snd] in AW2. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact AW2. }
    assert (HOFF : forall (H : word -> bool) lo0 n, (forall z, lo0 <= z < lo0 + n -> H (Z_to_bv 64 z) = false) -> hid_off H lo0 n).
    { intros H lo0 n Hz x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    (* [comment removed for export] *)
    pose proof (pk_T_writable bt BT_segs BT_ia (XL c) st Lc FF M M0 mdl W RP D) as TWR.
    destruct (pk_junk8 M T (T + 4096) (T + 2872) TWR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (v72 & R72).
    destruct (pk_junk8 M T (T + 4096) (T + 2880) TWR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (v80 & R80).
    set (thr := Z_to_bv 64 T : word).
    assert (UT : U thr = T) by ((lazymatch goal with |- ?G => let G' := eval unfold thr in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    apply (efs_map_arm_katwD Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx Hd2 (mkH_off_segments bt BT_ia st mdl A2 R13) A2 AWF2 (a_aa st)
             regs M rom mdl sp ra s0v s1v s2v s3v s4v s5v thr tp gp (Z_to_bv 64 TSDP) (Z_to_bv 64 CTX) v72 v80 (Z_to_bv 64 MIDEND) (Z_to_bv 8 1)
             RIz rbeg tot mfa PGP 0x19fce8 T 0 Qok Qf OKm (fun m => m) DSm).
    all: try (first [exact H1 | exact H2 | exact H4 | exact H3 | exact H10 | exact H11 | exact H12 | exact H13 | exact H8 | exact H9 | exact H18 | exact H19 | exact H20 | exact H21
                    | exact Hret | exact Htot | exact HALT | exact Bw1 | exact Bw2 | exact Hneed]).
    - (* [comment removed for export] *) lia.
    - split; [lia | exact Y6].
    - exact ROOM.
    - split; [lia|]. split; [lia | exact E11].
    - lia.
    - lia.
    - lia.
    - apply (writableZ_sok M (U sp - 448) (U sp)); [exact WSTK | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply (repx_rd (XL c) M M0 D (RIz + 24) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G24].
    - change (1092440 + 56) with 0x10ab90. rewrite <- (w2b1 0) by lia. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ PC_pre ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_pg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_P ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_gcf ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - change (1703144 + 260) with 0x19fdec. rewrite <- (w2b1 0) by lia. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ PC_dpm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - change (1703144 + 144) with 0x19fd78. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ PC_lim ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - left. rewrite <- ELO. lia.
    - apply HOFF. intros z Hz. apply NHri. lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply lazy_cover_HID.
    - (* [comment removed for export] *)
      intros mdlm r1 SBm MIm HLm G10 G11 G12 G13 G14 G15 Qok' Qf' K1.
      destruct (NODEF mdlm SBm MIm) as (N1 & N2 & N3 & N4 & N5 & _).
      apply (node1_of_fixedin3_s r1 _ rom mdlm addr size Qok' Qf' HLm G10 G11 G12 G13 G14 G15); [ | | | | exact N1 | exact N2 | exact N3 | exact N4 | exact N5 | exact K1].
      + (lazymatch goal with |- ?G => let G' := eval unfold addr in G in change_no_check G' end). rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end). apply mod4096_sum; [exact E12 | exact E14].
      + (lazymatch goal with |- ?G => let G' := eval unfold addr in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
      + (lazymatch goal with |- ?G => let G' := eval unfold size in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
      + (lazymatch goal with |- ?G => let G' := eval unfold size in G in change_no_check G' end). rewrite u_Z2bv by lia. reflexivity.
    - (* [comment removed for export] *)
      intros mdlm SBm MIm. destruct (NODEF mdlm SBm MIm) as (_ & _ & _ & _ & _ & HOK & MOKI & LZOK & HDS & MDSI & LZDS).
      split; [| split].
      + split; [exact HOK|]. split; [| exact MOKI]. exact (lazy_cover_sub Hd _ _ _ (lazy_cover_HID st mdl) LZOK).
      + split; [exact (halted_sbm mdl mdlm SBm HALT)|]. split; [| exact MIm].
        pose proof (same_but_materialized_frame mdl mdlm SBm) as (_ & _ & EL & _). rewrite EL. apply lazy_cover_HID.
      + split; [exact HDS|]. split; [| exact MDSI]. exact (lazy_cover_sub Hd _ _ _ (lazy_cover_HID st mdl) LZDS).
    - (* [comment removed for export] *)
      intros mdlm mdl4 SBm MIm SB4 MI4. split; [| exact (BUD mdlm mdl4 SBm SB4 MI4)].
      destruct (NODEF mdlm SBm MIm) as (_ & _ & _ & _ & _ & _ & _ & LZOK & _).
      pose proof (same_but_materialized_frame _ _ SB4) as (_ & _ & EL & _). rewrite EL.
      exact (lazy_cover_sub Hd2 _ _ _ (lazy_cover_mkH (m_vm_lazy mdl) A2 (m_vm_lazy mdl) (incl_refl _)) LZOK).
    - destruct (pos_mod4096 T T1 T4k) as [T4 T8]. split; [exact UT|]. split; [exact T4|]. split; [lia | exact T8].
    - clear - TSP ERI E9 E10. lia.
    - rewrite <- ESH. clear - TBAND SHB0 SHB1. lia.
    - rewrite <- ESH. right. lia.
    - rewrite <- ESH. right. lia.
    - rewrite <- ELO. clear - TSP SL0 SL1. lia.
    - rewrite <- ELO.
      apply (pk_poisonH bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS (XL c) st Lc FF M M0 mdl RP D YIMG lo (Z_to_bv 64 325060) (at_ sp (-48)));
        [(lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); lia | lia | exact SL8 | rewrite at_u by lia; lia | rewrite at_u by lia; lia | | apply ret_ok_lit; [lia | reflexivity]].
      intros i Hi. rewrite at_u in Hi by lia. apply WSTK. lia.
    - eapply Forall_impl; [| exact both_poison_cells_img]. cbv beta. intros c0 [_ Hc0]. exact Hc0.
    - apply (pk_gctH bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS (XL c) st Lc FF M M0 mdl W RP D YIMG YCTX (at_ (at_ sp (-48)) (-16)) tp Etp);
        [rewrite !at_u by (rewrite ?at_u by lia; lia); lia | rewrite !at_u by (rewrite ?at_u by lia; lia); lia |].
      intros i Hi. rewrite !at_u in Hi by (rewrite ?at_u by lia; lia). apply WSTK. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite Etp. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite Etp. rewrite <- ELO.
      split; [left; lia|]. split; [left; lia|]. split; [left; lia|]. clear - CSP SL0 SL1. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite <- ESH. left. lia.
    - rewrite Etp. rewrite <- ESH. left. lia.
    - rewrite !u_Z2bv by lia. rewrite <- ESH. left. lia.
    - rewrite !u_Z2bv by lia. rewrite <- ESH. clear - CBAND SHB0 SHB1. lia.
    - replace (at_ thr 2872) with (Z_to_bv 64 (T + 2872)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia). exact R72.
    - replace (at_ thr 2880) with (Z_to_bv 64 (T + 2880)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia). exact R80.
    - apply (writableZ_sok M T (T + 4096)); [exact TWR | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply (writableZ_sok M RIz (RIz + 128)); [apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW] | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells, both_poison_tab in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm] in G in change_no_check G' end).
      repeat (constructor; [apply HOFF; intros z Hz; apply NH2s; lia|]). constructor.
    - rewrite <- ESH. apply HOFF. exact NH2sh.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end). rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite Etp. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2rt. right. lia.
    - apply HOFF. intros z Hz. apply NH2rt. left. lia.
    - apply HOFF. exact NH2ri.
    - apply HOFF. intros z Hz. apply NH2s; lia.
    - (* [comment removed for export] *)
      intros r' mdlm mdl5 SBm MIm SB5 MI5 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q4 Q3.
      rewrite <- ELO.
      destruct (LEDOK mdlm mdl5 SBm SB5) as (LED & SEV & LK & MW5 & HL5).
      set (MR := efs_mr M sp ra s0v s1v s2v s3v s4v s5v RIz lo mfa PGP).
      set (M' := eam_3 MR sp s4v s5v thr v72 v80 RIz lo mfa).
      assert (ESH2 : SH = lo / 8 + 2147450880) by (rewrite ESH'; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); lia).
      assert (OUTM : forall a : word, (U a < U sp - 448 \/ U sp <= U a) -> (U a < lo \/ lo + 2 ^ 18 <= U a) -> (U a < SH \/ SH + 2 ^ 15 <= U a) ->
                 (U a < T + 2872 \/ T + 2888 <= U a) -> (U a < RIz + 24 \/ RIz + 32 <= U a) -> M' a = M a).
      { intros a X1 X2 X3 X4 X5. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end).
        rewrite (eam_3_outside MR sp s4v s5v thr v72 v80 RIz lo mfa ltac:(lia) ltac:(lia) a
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - X1; lia)
                   ltac:(rewrite <- ESH2; exact X3) ltac:(rewrite UT; exact X4) X5).
        (lazymatch goal with |- ?G => let G' := eval unfold MR in G in change_no_check G' end). apply efs_mr_outside; [lia | lia | exact X1 | exact X2]. }
      assert (GRM : mem_grows M M').
      { (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). eapply mem_grows_trans; [| apply eam_3_grows]. (lazymatch goal with |- ?G => let G' := eval unfold MR in G in change_no_check G' end). apply efs_mr_grows. }
      assert (DEFSL : forall a : word, lo <= U a < lo + 2 ^ 18 -> M' a <> None).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply eam_3_grows. (lazymatch goal with |- ?G => let G' := eval unfold MR, efs_mr in G in change_no_check G' end). apply wbytes_grows. (lazymatch goal with |- ?G => let G' := eval unfold zfill, zmem in G in change_no_check G' end). rewrite !u_Z2bv by lia.
        rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. discriminate. }
      assert (WRIM : writableZ BSEGS M RIz (RIz + 128)) by (apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW]).
      assert (FOOTM : forall a : word, M' a <> M a ->
                ((U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + 2 ^ 18) \/ (SH <= U a < SH + 2 ^ 15)
                 \/ (T + 2872 <= U a < T + 2888) \/ (RIz + 24 <= U a < RIz + 32)) /\ M' a <> None).
      { intros a Ha.
        assert (IN : ((U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + 2 ^ 18) \/ (SH <= U a < SH + 2 ^ 15)
                      \/ (T + 2872 <= U a < T + 2888) \/ (RIz + 24 <= U a < RIz + 32))
                     \/ ((U a < U sp - 448 \/ U sp <= U a) /\ (U a < lo \/ lo + 2 ^ 18 <= U a) /\ (U a < SH \/ SH + 2 ^ 15 <= U a)
                         /\ (U a < T + 2872 \/ T + 2888 <= U a) /\ (U a < RIz + 24 \/ RIz + 32 <= U a))) by (clear; lia).
        destruct IN as [IN | (O1 & O2 & O3 & O4 & O5)]; [| exfalso; exact (Ha (OUTM a O1 O2 O3 O4 O5))].
        split; [exact IN|].
        destruct IN as [I1 | [I2 | [I3 | [I4 | I5]]]].
        - apply GRM. destruct (WSTK (U a) I1) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
        - exact (DEFSL a I2).
        - apply GRM. rewrite <- (Z_to_bv_bv_unsigned _ a). apply (pk_shadow_def bt (XL c) st Lc FF M M0 mdl RP D). (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). right. clear - I3 SHB0 SHB1. lia.
        - apply GRM. destruct (TWR (U a) ltac:(clear - I4; lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
        - apply GRM. destruct (WRIM (U a) ltac:(clear - I5; lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
      assert (W' : WF bt (add_meter (op_famap st c) 0 [(SH, SH + 2 ^ 18 / 8)] 0) Lc FF).
      { apply (WF_meter bt (op_famap st c) Lc FF 0 [(SH, SH + 2 ^ 18 / 8)] 0 (OPS_WF_famap_pf bt st Lc FF c W Hc ROOM FAQ)); lia. }
      assert (RX' : RepX bt (XL c) (add_meter (op_famap st c) 0 [(SH, SH + 2 ^ 18 / 8)] 0) Lc FF M' mdl5).
      { apply (AsAinvOpsRc73.AsAinvRepX3.RepX_mono bt (fun z => XL c z /\ ~ False) (XL c)); [intros z [Hz _]; exact Hz|].
        apply (repx_step bt (XL c) (fun _ => False)
                 (fun z => (U sp - 448 <= z < U sp) \/ (lo <= z < lo + 2 ^ 18) \/ (SH <= z < SH + 2 ^ 15) \/ (T + 2872 <= z < T + 2888) \/ (RIz + 24 <= z < RIz + 32))
                 Xdec_false st _ Lc Lc FF FF M M' mdl mdl5 RX FOOTM ltac:(intros a F; destruct F)).
        intros N0 N0' RPn Dn DIFF _ SAME.
        assert (EQF : forall a : word, ~ XL c (U a) -> N0' a = M' a) by (intros a Ha; apply SAME; exact (repx_off (XL c) M N0 Dn a Ha)).
        pose proof RPn as (_ & _ & _ & R4n & _). destruct (R4n c Hc) as [(_ & _ & _ & _ & _ & _ & _ & _ & _ & GWn) _]. rewrite BT_segs in GWn. fold RIz in GWn.
        destruct LED as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13).
        apply (OPS_REP_famap_pf bt st Lc FF N0 N0' mdl mdl5 c W RPn Hc ROOM); rewrite ?BT_segs.
        - intros a Ha. destruct (DIFF a Ha) as [[F | []] Dd]. split; [|exact Dd]. (lazymatch goal with |- ?G => let G' := eval unfold foot_famap, fslot in G in change_no_check G' end). fold r mfa lo RIz SH. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP, T_UNW in G in change_no_check G' end).
          replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. clear - F SP1 CR. lia.
        - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). fold r mfa RIz. rewrite (rdn_ext BSEGS 8 N0' M' (Z_to_bv 64 (RIz + 24))); [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | ].
          + (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). exact (eam_3_mfa BSEGS MR sp s4v s5v thr v72 v80 RIz lo mfa ltac:(lia)).
          + intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply EQF. apply XRI. lia.
        - fold RIz. apply (repx_wr (fun _ => True) N0' N0 (fun a Ha => conj I (proj2 (DIFF a Ha)))); [lia | lia | exact GWn].
        - fold r mfa lo. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). apply writableZ_of_def; [lia | lia |]. intros i Hi.
          rewrite (EQF (Z_to_bv 64 i)) by (rewrite u_Z2bv by lia; apply XSL; exact Hi). apply DEFSL. rewrite u_Z2bv by lia. exact Hi.
        - fold r mfa lo SH. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP, fillZ, byteZ, cellN in G in change_no_check G' end). replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. intros i Hi.
          rewrite w2b1 by ((lazymatch goal with |- ?G => let G' := eval unfold FA in G in change_no_check G' end); lia).
          rewrite (rdn_ext BSEGS 1 N0' M' (Z_to_bv 64 i)); [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; rewrite u_Z2bv in Hx by lia; cbn in Hx; apply EQF, XSH; lia].
          replace i with (lo / 8 + 2147450880 + (i - SH)) by lia.
          exact (eam_3_fill BSEGS MR sp thr v72 v80 RIz lo ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite <- ESH2; right; lia)
                   ltac:(rewrite <- ESH2, UT; clear - TBAND SHB0 SHB1; lia) ltac:(rewrite <- ESH2; right; lia) ltac:(rewrite <- ESH2; right; lia) s4v s5v mfa (i - SH) ltac:(lia)).
        - exact L1. - exact L2. - exact L3. - exact L4. - exact L5. - exact L6. - exact L7. - exact L8. - exact L9. - exact L10. - exact L11. - exact L12.
        - exact MI5.
        - exact L13. }
      apply (CONT1 r' M' mdl5 W' RX' SEV LK MW5 HL5); [| exact Q10 | exact Q2 | exact Q1 | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q20 | exact Q21 | exact Q4 | exact Q3].
      intros a Ha. destruct (FOOTM a Ha) as [F Dd]. split; [| exact Dd]. replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. fold RIz. clear - F. lia.
    - (* [comment removed for export] *)
      intros r0 r' mdlm mdl5 SBm MIm SB5 MI5 AG POST. cbv beta in SB5.
      match goal with |- katD _ (mkCfg (mkst _ _ ?MKK _) _) _ => set (MK := MKK) end.
      pose proof (same_but_materialized_trans _ _ _ SBm SB5) as SBK.
      assert (OUTK : forall a : word, (U a < U sp - 448 \/ U sp <= U a) -> MK a = M a).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        rewrite mfi_m1_outside by (rewrite ?at_u by lia; lia). apply efs_m0_outside; lia. }
      assert (GRK : mem_grows M MK).
      { (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end). do 2 (eapply mem_grows_trans; [| apply wbytes_grows]). eapply mem_grows_trans; [apply efs_m0_grows | apply mfi_m1_grows]. }
      assert (FOOTK : forall a : word, MK a <> M a -> (U sp - 448 <= U a < U sp) /\ MK a <> None).
      { intros a Ha. assert (IN : (U sp - 448 <= U a < U sp) \/ (U a < U sp - 448 \/ U sp <= U a)) by (clear; lia).
        destruct IN as [IN | O1]; [| exfalso; exact (Ha (OUTK a O1))]. split; [exact IN|].
        apply GRK. destruct (WSTK (U a) IN) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
      apply (CONT0 r0 r' MK mdl5 st (or_introl eq_refl) W); [ | exact (same_but_materialized_except_vm _ _ SBK) | exact (lazy_kept_sbm Lc FF mdl mdl5 SBK)
                                                              | exact (model_ivs_wf_sbm mdl mdl5 SBK MW) | exact (halted_sbm mdl mdl5 SBK HALT) | | exact AG | exact POST].
      + apply (repx_frame_step bt (XL c) st Lc FF M MK mdl mdl5 W RX); [| exact MI5 | exact SBK].
        intros a Ha. destruct (FOOTK a Ha) as [IN Dd]. split; [|exact Dd].
        intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U a) W RCa). lia.
      + intros a Ha. left. exact (FOOTK a Ha).
    - (* [comment removed for export] *)
      intros r0 r' mdlm mdl5 SBm MIm SB5 MI5 AG POST. rewrite <- ELO.
      match goal with |- katD _ (mkCfg (mkst _ _ ?MKK _) _) _ => set (MD := MKK) end.
      destruct (LEDDS mdlm mdl5 SBm SB5) as (LD & EAG & SEV & LK & MW5 & HL5).
      assert (OUTD : forall a : word, (U a < U sp - 448 \/ U sp <= U a) -> (U a < lo \/ lo + 2 ^ 18 <= U a) -> MD a = M a).
      { intros a Ha Hb. (lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        rewrite unfill_out by (rewrite !u_Z2bv by lia; exact Hb).
        rewrite mfi_m1_outside by (rewrite ?at_u by lia; lia). apply efs_m0_outside; lia. }
      assert (SLD : forall a : word, lo <= U a < lo + 2 ^ 18 -> MD a = None).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        (lazymatch goal with |- ?G => let G' := eval unfold unfill in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
      assert (STD : forall a : word, U sp - 448 <= U a < U sp -> MD a <> None).
      { intros a Ha. destruct (decide (MD a = M a)) as [E | NE]; [rewrite E; destruct (WSTK (U a) Ha) as [Dd _]; rewrite Z_to_bv_bv_unsigned in Dd; exact Dd|].
        (* [comment removed for export] *)
        unfold MD in NE |- *.
        set (MU := unfill (Z_to_bv 64 lo) (Z_to_bv 64 (2 ^ 18)) _) in *.
        assert (GU : forall x : word, U sp - 448 <= U x < U sp -> MU x <> None).
        { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MU in G in change_no_check G' end). rewrite unfill_out by (rewrite !u_Z2bv by lia; lia).
          apply mfi_m1_grows. apply efs_m0_grows. destruct (WSTK (U x) Hx) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
        do 2 apply wbytes_grows. exact (GU a Ha). }
      assert (FOOTD : forall a : word, MD a <> M a -> ((U sp - 448 <= U a < U sp) /\ MD a <> None) \/ (lo <= U a < lo + 2 ^ 18)).
      { intros a Ha. assert (IN : (U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + 2 ^ 18) \/ ((U a < U sp - 448 \/ U sp <= U a) /\ (U a < lo \/ lo + 2 ^ 18 <= U a))) by (clear; lia).
        destruct IN as [IN | [IN | [O1 O2]]]; [left; split; [exact IN | exact (STD a IN)] | right; exact IN | exfalso; exact (Ha (OUTD a O1 O2))]. }
      assert (W1 : WF bt (op_fhole st c) Lc FF) by (apply (WF_fhole bt st Lc FF c Hc ROOM W)).
      apply (CONT0 r0 r' MD mdl5 (op_fhole st c) (or_intror eq_refl) W1); [ | exact SEV | exact LK | exact MW5 | exact HL5 | | exact AG | exact POST].
      + (* [comment removed for export] *)
        set (N1 := unfill (Z_to_bv 64 lo) (Z_to_bv 64 (2 ^ 18)) M0).
        assert (RP1 : Rep bt (op_fhole st c) Lc FF N1 mdl5).
        { apply (OPS_REP_fhole_pf bt st Lc FF M0 N1 mdl mdl5 c W RP Hc FH ROOM); [ | exact LD | exact MI5 | exact EAG].
          intros a Ha. unfold N1, unfill in Ha |- *. rewrite !u_Z2bv in Ha |- * by lia. (lazymatch goal with |- ?G => let G' := eval unfold fslot in G in change_no_check G' end). fold r mfa lo. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end).
          destruct (Z.leb_spec lo (U a)); destruct (Z.ltb_spec (U a) (lo + 2 ^ 18)); cbn [andb] in Ha |- *; first [split; [lia | reflexivity] | exfalso; exact (Ha eq_refl)]. }
        set (N := fun a : word => if Z_le_dec lo (U a) then (if Z_lt_dec (U a) (lo + 2 ^ 18) then None else if decide (M a = M0 a) then MD a else M0 a)
                                  else if decide (M a = M0 a) then MD a else M0 a).
        assert (N1in : forall a : word, lo <= U a < lo + 2 ^ 18 -> N1 a = None).
        { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold N1, unfill in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
        assert (N1out : forall a : word, (U a < lo \/ lo + 2 ^ 18 <= U a) -> N1 a = M0 a).
        { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold N1 in G in change_no_check G' end). apply unfill_out. rewrite !u_Z2bv by lia. exact Ha. }
        exists N. split.
        * apply (Rep_frame bt (op_fhole st c) Lc FF N1 N mdl5 W1 RP1). intros a Ha. unfold N in Ha |- *.
          destruct (Z_le_dec lo (U a)) as [L1|L1]; [destruct (Z_lt_dec (U a) (lo + 2 ^ 18)) as [L2|L2]|].
          -- exfalso. apply Ha. symmetry. apply N1in. lia.
          -- rewrite (N1out a ltac:(lia)) in Ha. destruct (decide (M a = M0 a)) as [E | NE]; [| exfalso; exact (Ha eq_refl)].
             rewrite <- E in Ha. destruct (FOOTD a Ha) as [[IN Dd] | IN]; [| lia]. split; [|exact Dd].
             intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia (op_fhole st c) Lc FF (U a) W1 RCa). lia.
          -- rewrite (N1out a ltac:(lia)) in Ha. destruct (decide (M a = M0 a)) as [E | NE]; [| exfalso; exact (Ha eq_refl)].
             rewrite <- E in Ha. destruct (FOOTD a Ha) as [[IN Dd] | IN]; [| lia]. split; [|exact Dd].
             intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia (op_fhole st c) Lc FF (U a) W1 RCa). lia.
        * intros a Ha. unfold N in Ha.
          assert (CASE : forall (E : M a <> M0 a), XL c (U a) /\ MD a <> None).
          { intros NE. destruct (D a NE) as [HX Dd]. split; [exact HX|].
            destruct (decide (MD a = M a)) as [EQ2 | NE2]; [rewrite EQ2; exact Dd|].
            destruct (FOOTD a NE2) as [[_ Dd2] | IN]; [exact Dd2 | exfalso; exact (XSL (U a) IN HX)]. }
          destruct (Z_le_dec lo (U a)) as [L1|L1]; [destruct (Z_lt_dec (U a) (lo + 2 ^ 18)) as [L2|L2]|].
          -- exfalso. apply Ha. apply SLD. lia.
          -- destruct (decide (M a = M0 a)) as [E | NE]; [exfalso; exact (Ha eq_refl) | exact (CASE NE)].
          -- destruct (decide (M a = M0 a)) as [E | NE]; [exfalso; exact (Ha eq_refl) | exact (CASE NE)].
      + intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). exact (FOOTD a Ha).
  Qed.


End L3.
End WithCeil.
