(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsDepotPut AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_IAInit AW_FreePre
     AW_Put1 AW_Put2 AS_Free1 AS_Free2 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_Frame AG_FreeModel AG_WFFree AG_Free1 AG_Free2 SecLazy AG_WriteSet.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~03ast04a_AL03a_L03a_S04a_Zr05a_bot05a_ctx05a_fsb04a_st05a_thr05a_top05mkAst69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~o9h1set_internal_init3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticstfdmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Statehi65Model37Corelib7Numbers7BinNumshld4Npos35stdpp9bitvectorbdefinitionshne2bv37Corelib4Init5Logichq12exhq13and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hs25asegs37Corelib4Init9Datatypesig64listo96astateo96effecthnebbv_unsignedig64prodhq12eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~il53memig64Noneig64Someig66optionig64pair3h5LinuxProcessSemanticsfLinuxProcessSem3Runirc5mkCfg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AG_Frame~~~~~~iv17amframe79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_Malloc2~~~~~~jjacdepot_placed79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_MallocModel~~~~~~joafsame_but_shadow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAG_WriteSet~~~~~~ju16acomplju14avmx06ARHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AllocRepX~~~~~~kjc7AMODELXkjc8awin_viskjc9depot_covkjcaflagsx_rep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsDepotInv~~~~~~kqd5DEPOT79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7SecLazy~~~~~~kv6anonvm_sameo9cam_free_full69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~ll08restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~lpb4lzok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ltc3mkRltc3stkltc5wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~mif2MSmif6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mnc7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~ms17seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~ngb6sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~nkedhunspell_scfg99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAG_FreeNull3HCWcFreeNullGlue~~~~~~np6ffree_null_gpost89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAG_FreeNull3HCW~~~~~~nvb7null_s'04AREPil55aceil46Stdlib6ZArith6BinInt1Zola2le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~on84cellig64conson82C179OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~osa2b8ig63nil07AIAINITon82C279OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~pi18rw_cellsosa2wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AW_IAInit~~~~~~pme8ia_afterola3addhld1Zola6moduloola3pow03ATPig64boolig64true79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsUnwind~~~~~~pub9goodframepubbframe_chainhne7Z_to_bv" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Section NullPost.
  Variables (s : ast) (m m' : mem) (lo spv : Z).
  Let st := a_st s.
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Definition null_s' : ltac2:(zQ "10!je$0") := ltac2:(zQ "c0!k3!k9!ke!l3!l9!m0!m7!me!n4!nb!o2!sa@a$a@1$b@1$7?1s@1$8?1s@1$5?1s@1$6?1s@1$1?1s@1$2?1s@1$3?1s@1$0?1s@1$9?1s@1$4?1s").
  Let s' := null_s'.
  Let Wq : list ivl := [(lo, spv); (TH + 3168, TH + 3169); (AIAINIT, AIAINIT + 4); (AIAINST, AIAINST + 0x81030)].

  Hypothesis R : ltac2:(zQ "10!okb@3$0?5HCEIL?1s?1m").
  Hypothesis LO : ltac2:(zQ "20!ol1!on2@2$1@1$0?5HCEIL?2lo").
  Hypothesis AG : agree_on (outside Wq) m m'.
  Hypothesis WM : ltac2:(zQ "20!hvd!mi6@3$1$0?1m?2m'").
  Hypothesis UNW' : rw_cells asegs m' (TH + 3168) [C1 (b8 0)].
  Hypothesis FLG' : ltac2:(zQ "a0!or4!orc!os4!pg5!pgb!hvd!ph2!phb!plc!pm8@4$8$5?2m'$6@3$1$0@1$2@1$3+1@3$1$0@1$2@1$3Z@3$1$0@1$7@1$9Z@1$4$0").
  Hypothesis IA' : ltac2:(zQ "10!pqd@1$0?2m'").   (* [comment removed for export] *)

  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  Let OK' : ast_ok s'. Proof. split; [exact PL|]. eapply WF_ext; [ .. | exact WFs]; reflexivity. Qed.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

  (* [comment removed for export] *)
  Let BND : 4096 <= TH /\ TH + 4096 <= aceil /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ (TH + 4096 <= sb \/ sb + 137438953472 + 4096 <= TH) /\ 7430144 <= CTX /\ CTX + 160 <= aceil /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)
            /\ 7430144 <= a_pa s /\ a_pa s + 8388608 <= aceil /\ (a_pa s + 8388608 <= TH \/ TH + 4096 <= a_pa s).
  Proof.
    npose PL as (Y1 & Y2 & Y3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    apply akobj_env in T2; [| unfold kPageSize; clear; lia]. apply aapp_env in X2; [| clear; lia]. apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; lia].
    clear - Y2 Y3 P2 P3 T2 T3 X2 X3 D2 D4 TCX. zlets. unfold disj, a_sb, AHI_LO, kSpaceSize, kPageSize, kPtrArrayReserve in *. repeat split; lia.
  Qed.
  Let BANDS : hidden ((TH + 4096 <= 65536 \/ (7430144 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH)
                   /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                   /\ (a_pa s + 8388608 <= 2147446784 \/ 17594333495296 <= a_pa s)).
  Proof.
    npose PL as (_ & _ & _ & _ & P2 & _ & _ & T2 & _ & _ & X2 & _). fold TH in T2. fold CTX in X2.
    split. split; [exact (akobj_lit _ _ T2)|]. split; [exact (aapp_lit _ _ X2)|].
    pose proof (aapp_lit _ _ P2) as L. unfold kPtrArrayReserve in L. exact L.
  Qed.
  Tactic Notation "bands_as" simple_intropattern(p) := (let X := fresh "BX" in pose proof BANDS as X; destruct X as [p]).
  (* [comment removed for export] *)
  Lemma ZQ_core : forall a, a < aceil -> ~ (TH + 3168 <= a < TH + 3169) -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) -> outside Wq a.
  Proof. intros a Ha N0 N1 N2. clear - Ha N0 N1 N2 LO. unfold Wq in *. cbn [outside]. repeat split; try exact I; lia. Qed.
  Lemma ZQ_st : forall a, 65536 <= a < AIMG_TOP -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) -> outside Wq a.
  Proof. intros a Ha N1 N2. npose BND as (T1 & T2 & _). bands_as (BT & _). apply ZQ_core; try assumption; clear - Ha T1 T2 BT; acb; unfold AIMG_TOP in *; lia. Qed.
  Lemma ZQ_hi : forall a, (AIMG_TOP <= a < ALOWSH_LO \/ AHI_LO <= a < aceil) -> ~ (TH + 3168 <= a < TH + 3169) -> outside Wq a.
  Proof. intros a Ha N1. apply ZQ_core; [| exact N1| |]; clear - Ha N1; acb; unfold AIAINIT, AIAINST, AIMG_TOP, ALOWSH_LO, AHI_LO in *; lia. Qed.
  Lemma ZQ_sh : forall a, ASHADOW_BASE <= a < AHI_LO -> outside Wq a.
  Proof. intros a Ha. npose BND as (T1 & T2 & _). bands_as (BT & _). apply ZQ_core; clear - Ha T1 T2 BT; acb; unfold AIAINIT, AIAINST, AHI_LO, ASHADOW_BASE in *; lia. Qed.
  Lemma ZQ_shr : forall X k a, 0 <= X -> 0 <= k -> X + 8 * k <= aceil -> sh X <= a < sh X + k -> outside Wq a.
  Proof. intros X k a H1 H2 H3 Ha. apply ZQ_sh. exact (sh_range_in X k a H1 H2 H3 Ha). Qed.
  Lemma ZQ_space : forall a, sb <= a < sb + kSpaceSize + kPageSize -> outside Wq a.
  Proof. intros a Ha. npose BND as (_ & _ & S1 & S2 & D & _). apply ZQ_hi; clear - Ha S1 S2 D; zlets; unfold AHI_LO, AIMG_TOP, ALOWSH_LO, kSpaceSize, kPageSize in *; lia. Qed.
  Lemma ZQ_thr : forall a, TH <= a < TH + 3168 -> outside Wq a.
  Proof. intros a Ha. npose BND as (T1 & T2 & _). bands_as (BT & _). apply ZQ_core; clear - Ha T1 T2 BT; zlets; unfold AIAINIT, AIAINST in *; lia. Qed.
  Lemma ZQ_ctx : forall a, CTX <= a < CTX + 160 -> outside Wq a.
  Proof. intros a Ha. npose BND as (_ & _ & _ & _ & _ & C1 & C2 & D & _). bands_as (_ & BC & _). apply ZQ_hi; clear - Ha C1 C2 D BC; zlets; unfold AHI_LO, AIMG_TOP, ALOWSH_LO in *; lia. Qed.
  Lemma ZQ_rec : forall x a, In x (chunk_list st) -> ch_lo x <= a < ch_end x -> outside Wq a.
  Proof.
    intros x a Hx Ha. npose (record_ext s OK x Hx) as (X1 & X2 & _). pose proof (rec_vs_thread s m x R Hx) as RT.
    pose proof (record_band s OK x Hx) as RBx. unfold aapp, aapp_lo, aapp_hi in RBx.
    apply ZQ_hi; clear - Ha X1 X2 RT RBx; zlets; unfold AHI_LO, AIMG_TOP, ALOWSH_LO, kPageSize in *; lia.
  Qed.

  Ltac trc H Z := eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|];
                  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length repeat map];
                  let Ha := fresh in intros ? Ha; apply Z; clear - Ha; lia.
  Ltac trj H Z := eapply (junk_transport_pt _ _ _ AG WM); [exact H|]; let Ha := fresh in intros ? Ha; apply Z; clear - Ha; lia.

  (* [comment removed for export] *)
  Lemma null_flags : flags_rep s' m'.
  Proof.
    pose proof R as RR; ndestruct RR as (_ & _ & FL & _).
    ndestruct FL as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    unfold flags_rep. change (a_ctx s') with (a_ctx s). change (as_internal_init (a_st s')) with true.
    Ltac trf H := eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|];
                  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add length repeat map];
                  let Ha := fresh in intros ? Ha; apply ZQ_st; clear - Ha;
                  unfold AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT, AHOOKS,
                         ADYING, AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, ATP, AIMG_TOP in Ha |- *; lia.
    split; [trf F1|]. split; [trf F2|]. split; [trf F3|]. split; [trf F4|].
    split; [trf F5|]. split; [trf F6|]. split; [trf F7|]. split; [trf F8|].
    split; [trf F9|]. split; [trf F10|]. split; [trf F11|]. split; [trf F12|]. split; [trf F13|].
    split; [trf F14|]. split; [trf F15|].
    split. { exact FLG'. }
    split; [trf F17|]. split; [trf F18|]. split; [trf F19|].
    split. { eapply (rw_cells_transport_pt _ _ _ AG WM); [exact F20|]. change (Z.of_nat _) with 120. intros a0 Ha0.
             apply ZQ_st; clear - Ha0; unfold AGOT_LO, AIAINIT, AIAINST, AIMG_TOP in Ha0 |- *; lia. }
    split; [trf F21|]. split; [trf F22|]. split; [trf F23|].
    split; [trf F24|]. split; [trf F25|]. split; [trf F26|]. trf F27.
  Qed.

  (* [comment removed for export] *)
  Lemma null_thread : thread_rep s' m'.
  Proof.
    pose proof R as RR; ndestruct RR as (_ & _ & _ & THR & _).
    ndestruct THR as (T1 & T2 & T2b & T2c & T2d & T3 & T4 & J1 & J2 & J3 & T5).
    unfold thread_rep. change (a_ctx s') with CTX. change (a_thr s') with TH. change (a_top s') with (a_top s). change (a_bot s') with (a_bot s).
    change (a_cache s') with (a_cache s). change (as_tq (a_st s')) with (as_tq st).
    fold TH CTX st in T1, T2, T2b, T2c, T2d, T3, T4, J1, J2, J3, T5. unfold a_cache, OT_SWITCHING, OT_TQ, OT_CACHE, OT_STATS, OT_UNWINDING, CACHE_STATS in *. fold TH in J2 |- *.
    split; [trc T1 ZQ_thr|]. split; [trc T2 ZQ_ctx|]. split; [trc T2b ZQ_ctx|]. split; [trc T2c ZQ_thr|].
    split; [trc T2d ZQ_thr|]. split; [trc T3 ZQ_thr|]. split; [trc T4 ZQ_thr|].
    split; [trj J1 ZQ_thr|]. split; [trj J2 ZQ_thr|]. split; [trj J3 ZQ_thr| exact UNW'].
  Qed.

  Lemma null_regions : forall c0, 0 <= c0 < kNumClasses -> region_rep s' m' c0 /\ pclass_rep s' m' c0 /\ region_shadow_rep s' m' c0 /\ region_junk_rep s' m' c0.
  Proof.
    intros c0 Hc0. pose proof R as RR; ndestruct RR as (_ & _ & _ & _ & _ & _ & CL & _). ndestruct (CL c0 Hc0) as (RG & PC & RSH & RJ).
    npose BND as (T1 & T2 & S1 & S2 & _).
    pose proof (region_in_space st c0 ltac:(hci; unfold kNumClasses in Hc0; clear - Hc0; lia)) as [RS1 RS2].
    change (region_beg st c0) with (RB s c0) in RS1, RS2. change (as_space_beg st) with sb in RS1, RS2.
    pose proof (WF_region st c0 WFs Hc0) as RO.
    pose proof (ro_alloc_nonneg _ _ RO) as W1. pose proof (ro_alloc_le _ _ RO) as W2. pose proof (ro_mapped_bound _ _ RO) as W3.
    pose proof (ro_fa_le _ _ RO) as W4. pose proof (ro_fa_bound _ _ RO) as W5. pose proof (ro_numfreed _ _ RO) as W6.
    fold st in W1, W2, W3, W4, W5, W6.
    assert (EFA : FA s c0 = RB s c0 + kFreeArrayOffset) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
    npose (class_size_table_facts c0 Hc0) as (CT1 & CT2 & CT3 & _).
    unfold kFreeArraySize, kFreeArrayOffset, kUserMapSize, kSpaceSize in *.
    assert (ZFC : forall cp a, In cp (rg_free_array (get_region st c0)) \/ In cp (pc_chunks (get_pc st c0)) ->
                  compact_to_addr st c0 cp <= a < compact_to_addr st c0 cp + class_size c0 -> outside Wq a).
    { intros cp a Hin Ha. assert (CV : carved st c0 (compact_to_addr st c0 cp)) by (destruct Hin as [Hin|Hin]; [apply carved_free| apply carved_cache]; assumption).
      pose proof (carved_in_space s OK _ _ CV) as (C1 & C2 & C3). fold st sb in C1, C2. apply ZQ_space. clear - Ha C1 C2. unfold kSpaceSize, kPageSize in *. lia. }
    assert (ZFS : forall cp a, In cp (rg_free_array (get_region st c0)) \/ In cp (pc_chunks (get_pc st c0)) ->
                  sh (compact_to_addr st c0 cp) <= a < sh (compact_to_addr st c0 cp) + class_size c0 / 8 -> outside Wq a).
    { intros cp a Hin Ha. assert (CV : carved st c0 (compact_to_addr st c0 cp)) by (destruct Hin as [Hin|Hin]; [apply carved_free| apply carved_cache]; assumption).
      pose proof (carved_in_space s OK _ _ CV) as (C1 & C2 & C3). fold st sb in C1, C2.
      apply (ZQ_shr (compact_to_addr st c0 cp) (class_size c0 / 8) a); [clear - C1 S1; lia| clear - C3; lia| clear - C2 S2 CT3; unfold kSpaceSize in *; Z.div_mod_to_equations; lia| exact Ha]. }
    split; [| split; [| split]].
    - apply (region_rep_frame s' m m' _ AG WM OK' c0 Hc0); [| | | exact RG].
      + intros a Ha. apply ZQ_space. change (a_ri s') with (a_ri s) in Ha. unfold a_ri, kSpaceSize, kPageSize in *. fold sb in Ha. clear - Ha. lia.
      + intros a Ha. change (FA s' c0) with (FA s c0) in Ha. change (get_region (a_st s') c0) with (get_region st c0) in Ha.
        apply ZQ_space. unfold kSpaceSize, kPageSize. clear - Ha EFA RS1 RS2 W4 W5. lia.
      + intros a Ha. change (RB s' c0) with (RB s c0) in Ha. change (get_region (a_st s') c0) with (get_region st c0) in Ha.
        apply ZQ_space. unfold kSpaceSize, kPageSize. clear - Ha RS1 RS2 W1 W2 W3. lia.
    - unfold pclass_rep. change (a_st s') with (set_internal_init st). change (get_pc (set_internal_init st) c0) with (get_pc st c0).
      change (as_cache_inited (set_internal_init st)) with (as_cache_inited st). change (a_cache s') with (a_cache s).
      apply (pclass_rep_frame s m m' _ AG WM OK c0 Hc0); [| exact PC].
      intros a Ha. apply ZQ_thr. unfold a_cache, OT_CACHE, PCLASS_SIZE, kNumClasses in *. fold TH in Ha. clear - Ha Hc0. lia.
    - apply (region_shadow_rep_frame s' m m' _ AG WM OK' c0 Hc0); [| | | exact RSH].
      + exact ZFS.
      + intros a Ha. change (RB s' c0) with (RB s c0) in Ha. change (get_region (a_st s') c0) with (get_region st c0) in Ha.
        apply (ZQ_shr (RB s c0 + rg_allocated_user (get_region st c0)) ((rg_mapped_user (get_region st c0) - rg_allocated_user (get_region st c0)) / 8) a);
          [clear - RS1 S1 W1; lia| clear - W2; Z.div_mod_to_equations; lia| clear - RS2 S2 W2 W3; Z.div_mod_to_equations; lia| exact Ha].
      + intros a Ha. change (FA s' c0) with (FA s c0) in Ha. change (get_region (a_st s') c0) with (get_region st c0) in Ha.
        apply (ZQ_shr (FA s c0) (rg_mapped_free_array (get_region st c0) / 8) a);
          [clear - EFA RS1 S1; lia| clear - W4 W6; unfold zlen in *; Z.div_mod_to_equations; lia| clear - EFA RS2 S2 W5; Z.div_mod_to_equations; lia| exact Ha].
    - apply (region_junk_rep_frame s' m m' _ AG WM c0 Hc0); [exact ZFC| exact RJ].
  Qed.

  Lemma null_chunks : forall x, In x (chunk_list (a_st s')) -> chunk_rep m' x.
  Proof.
    intros x Hx. change (chunk_list (a_st s')) with (chunk_list st) in Hx.
    pose proof R as RR; ndestruct RR as (_ & _ & _ & _ & _ & _ & _ & CHR & _).
    npose (record_ext s OK x Hx) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    npose (chunk_geom s OK x Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & _).
    apply (chunk_rep_frame s' m m' _ AG WM OK' x Hx); [| exact (CHR x Hx)].
    intros a Ha. destruct Ha as [Ha|[Ha|[[_ Ha]|[Ha|[Ha|[[_ Ha]|[NP Ha]]]]]]].
    - apply (ZQ_rec x a Hx). clear - Ha X3 X7 G3 G5. lia.
    - apply (ZQ_rec x a Hx). clear - Ha X3 X6 X8 G3. lia.
    - apply (ZQ_rec x a Hx). clear - Ha X3 X6 X8 X7 G5. lia.
    - apply (ZQ_shr (ch_alloc_beg x) (ch_rz x / 8) a); [clear - X1 X3; unfold AHI_LO, AIMG_TOP in *; lia| clear - X8; Z.div_mod_to_equations; lia| clear - X2 X6 X7 G3 G5 X8; Z.div_mod_to_equations; lia| exact Ha].
    - apply (ZQ_shr (ch_user_beg x + round_up (ch_used x) 8) ((ch_end x - (ch_user_beg x + round_up (ch_used x) 8)) / 8) a);
        [clear - X1 X3 X6 X8 G3 G5; unfold AHI_LO, AIMG_TOP in *; lia| clear - X7; Z.div_mod_to_equations; lia| clear - X2 X7; Z.div_mod_to_equations; lia| exact Ha].
    - apply (ZQ_shr (ch_user_beg x) (nsh (ch_used x)) a); [clear - X1 X3 X6 X8; unfold AHI_LO, AIMG_TOP in *; lia| clear - G6 G5 G3; lia| clear - X2 X7 G6; lia| exact Ha].
    - ndestruct (record_secondary_map s OK x Hx NP) as (h & Hh & L0 & E0 & AB). npose PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
      npose (SEC h Hh) as (_ & Q1 & Q2 & Q3 & _). apply aapp_env in Q1; [| unfold kPageSize in Q3; clear - Q3; lia].
      apply (ZQ_shr (ch_alloc_beg x - kPageSize) 512 a); [clear - AB Q1; unfold kPageSize in *; lia| clear; lia| clear - AB Q2 Q3; unfold kPageSize in *; lia| exact Ha].
  Qed.

  Lemma null_batches : batches_rep m' (qc_list (as_tq st)) /\ batches_rep m' (qc_list (as_gq st)).
  Proof.
    pose proof R as RR; ndestruct RR as (_ & _ & _ & _ & _ & _ & _ & _ & BT & BG). npose BND as (_ & _ & S1 & S2 & _).
    assert (BOK : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> 0 <= qb_count b /\ 24 + 8 * qb_count b <= kBatchSize /\ qb_count b = zlen (qb_chunks b)).
    { intros b Hb. pose proof (WF_batch _ b WFs Hb) as (B1 & B2 & _). unfold kBatchSize, kBatchCount in *. clear - B1 B2. lia. }
    assert (ZB : forall b a, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) ->
                 (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> outside Wq a).
    { intros b a Hb Hr. pose proof (batch_carved s OK b Hb) as (CV & _). pose proof (carved_in_space s OK _ _ CV) as (C1 & C2 & _). fold st sb in C1, C2.
      change (class_size kBatchClass) with 8192 in C2. unfold kBatchSize in Hr.
      destruct Hr as [Hr|Hr]; [apply ZQ_space; clear - Hr C1 C2; unfold kSpaceSize, kPageSize in *; lia|].
      apply (ZQ_shr (qb_addr b) 1024 a); [clear - C1 S1; lia| clear; lia| clear - C2 S2; unfold kSpaceSize in *; lia| exact Hr]. }
    split.
    - eapply (batches_rep_transport _ m m' _ AG WM); [| | exact BT]; [intros b a Hb Hr; apply (ZB b a); [apply in_app_iff; left; exact Hb| exact Hr]| intros b Hb; apply BOK; apply in_app_iff; left; exact Hb].
    - eapply (batches_rep_transport _ m m' _ AG WM); [| | exact BG]; [intros b a Hb Hr; apply (ZB b a); [apply in_app_iff; right; exact Hb| exact Hr]| intros b Hb; apply BOK; apply in_app_iff; right; exact Hb].
  Qed.

  Theorem arep_after_null : AREP s' m'.
  Proof.
    pose proof R as RR; ndestruct RR as (_ & INST & _ & _ & SEC0 & _).
    split; [exact OK'|].
    split. { apply (inst_rep_frame s' m m' _ AG WM); [| exact INST]. intros a Ha. apply ZQ_st; unfold AINST, OI_MISMATCH, AIMG_TOP, AIAINIT, AIAINST in *; clear - Ha; lia. }
    split; [exact null_flags|].
    split; [exact null_thread|].
    split. { apply (sec_rep_frame s' m m' _ AG WM OK'); [| | exact SEC0].
             - intros a Ha. change (a_pa s') with (a_pa s) in Ha. change (as_n_reserved (a_st s')) with (as_n_reserved st) in Ha.
               npose BND as (_ & _ & _ & _ & _ & _ & _ & _ & P1 & P2 & PD).
               ndestruct WFs as (_ & _ & _ & _ & _ & _ & Wn & Wr & _). fold st in Wn, Wr. unfold kChunksBlockCount, kPtrArrayReserve in *.
               assert (0 <= zlen (as_sec st)) by (unfold zlen; clear; lia).
               bands_as (_ & _ & BP). apply ZQ_hi; clear - Ha P1 P2 PD Wn Wr H BP; unfold AHI_LO, AIMG_TOP, ALOWSH_LO in *; lia.
             - intros h a Hh Ha. change (as_sec (a_st s')) with (as_sec st) in Hh.
               npose PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
               npose (SEC h Hh) as (_ & Q1 & Q2 & Q3 & _ & _ & QT & _). unfold aapp, aapp_lo, aapp_hi in Q1.   (* [comment removed for export] *)
               apply ZQ_hi; clear - Ha Q1 Q2 Q3 QT; zlets; unfold AHI_LO, AIMG_TOP, ALOWSH_LO, disj, kPageSize in *; lia. }
    split; [unfold ia_rep; change (as_internal_init (a_st s')) with true; exact IA'|].
    split; [exact null_regions|].
    split; [exact null_chunks|].
    exact null_batches.
  Qed.
End NullPost.

(* [comment removed for export] *)
Section FreeNullGlue.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)).

  Let st : ltac2:(zQ "10!ii6$0") := ltac2:(zQ "10!me@1$0?1s").
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let s' : ltac2:(zQ "10!je$0") := ltac2:(zQ "10!ok0@1$0?1s").
  Let Wq : list ivl := [(lo, bv_unsigned sp); (TH + 3168, TH + 3169); (AIAINIT, AIAINIT + 4); (AIAINST, AIAINST + 0x81030)].

  Hypothesis HR : ltac2:(zQ "10!kj4@4$0?5HCEIL?1s?2LB?1m").
  Hypothesis AX : ltac2:(zQ "30!hrb!ko6!kpf@2$0@2$1?1s?1m@1$2?1m").
  Hypothesis AMX : ltac2:(zQ "10!knb@3$0?5HCEIL?1s?2mo").
  Hypothesis DEP : ltac2:(zQ "20!hvd!kud@3$1$0?1d?1m").
  Hypothesis DPL : ltac2:(zQ "10!jna@3$0?5HCEIL?1s?1d").
  Hypothesis DCOV : ltac2:(zQ "10!kp2@2$0?1d?2mo").
  Hypothesis MI : ltac2:(zQ "20!hvd!mr6@2$1$0?1m").
  Hypothesis ST : ltac2:(zQ "40!hn6!hvd!mhf!ij8@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis LO : ltac2:(zQ "20!ol1!on2@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "40!hn6!pr9!on2!ij8@2$2@2$1?2lo+ro0@2$3@1$0#k0?2sp").
  Hypothesis SPA : ltac2:(zQ "50!ikf!hn6!ps0!ps5!ij8@3$0$2@2$3@2$4@1$1#k0?2sp+h0Z").
  Hypothesis SPT : ltac2:(zQ "50!hn6!pr9!on2!psf!ij8@2$2@2$1@2$4@1$0#k0?2sp+h0@2$3+2+if").
  Hypothesis TP : ltac2:(zQ "50!ikf!hn6!pt6!pm8!hpb@3$0@1$4@1$1#k0?2tp@1$3$2").
  Hypothesis FCH : ltac2:(zQ "d0!hn6!ij8!nb!ptb!pu3!ikf!qi9!hrb!hvd!l9!qj6!pr9!on2>0@3$5$3@3$6@1$9?1s@2$1@1$0#k0?2sp@1$2?1s$4>0@3$5$3@3$6@2$1@1$0#k0?2sp@2$1@1$0#k0?2s0@1$2?1s$4@2$7@2$c@2$b@2$1@1$0#k0?2sp+h0@2$1@1$0#k0?2s0@5$a$8?1m@1$2?1s@2$1@1$0#k0?2s0?2CH").
  (* [comment removed for export] *)
  Hypothesis OK : ltac2:(zQ "60!iu8!hvd!k9!ke!l3!lt4@5$5$1@1$2?1s@1$3?1s@1$4?1s@2$0?3msF?2mo").
  Hypothesis VISE : ltac2:(zQ "e0!hn6!ipa!ikf!hh6!hvd!k9!ke!lof!mh8!mmc!ng0!pm8!qk5!hpb@3$2$3@3$7@1$5?1s@1$6?1s?3msF@7$9@hf$8?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1@1$bZ?2a1?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$c@1$0#k0+pgrm8?2fc@1$1@1$d@1$0#k0?1m@1$a$4").

  Definition free_null_gpost : ltac2:(zQ "20!hh6!hl4>4msF'$0>3mo'$1P") := ltac2:(zQ "id0!hn6!hpb!hr5!hrb!hvd!ihe!ii6!iif!ij8!ik7!ikf!hh6!k9!ke!ip3!ipa!iq2!iqa!ir4!iu8!hl4!jif!jna!jse!ki2!kic!kj4!l3!me!knb!ko6!kp2!kpf!kud!lj3!lk1!lof!lt4!mh8!mhf!mi6!mmc!mn2!mr6!ng0\4msF'$b\3mo'$h4@2$2@1$1@1$0#k0\3t0'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t2'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a0'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a4'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a5'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a6'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a7'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t3'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t4'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t5'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t6'@1$1@1$0#k0@2$2$e\2m'$e@2$3@5$i5$4@1$c?2s'@1$d?2s'@1$hb?2s'@2$h3^h2^h1@2$3@3$a$b@3$i4@1$c?2s'@1$d?2s'^h2@7$i9@hf$i6?2ra?2sp?2gp?2tp^h0^f^e?2s0?2s1^d^c^b^a^9^8^7^6?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11^5^4^3^2?1F@1$ia?2ra?2fc@1$f@1$1@1$0#k0^1@1$ic$4@2$3@4$ha?5HCEIL?2s'?2LB^1@2$3@2$he?2s'^1@2$3@1$i0^1@2$3@3$hd?5HCEIL?2s'^h1@2$3@2$i2?2mo^h1@2$3@3$i1$4?1d^1@2$3@3$h6?5HCEIL?2s'?1d@2$3@2$hf?1d^h1@2$3@2$ib$4^1@2$3@4$i7$4^1?2lo@2$8@1$0#k0?2sp@2$3@6$h5?5HCEIL?1s?2LB@2$8@1$0#k0?2sp?1m^1@2$3@3$i8$4?1m^1@2$3@7$h8?1s?2s'?1d?2lo@2$8@1$0#k0?2sp?1m^1@2$3@4$h9?1s?2s'?2mo^h1@2$2$6\4st''$6@2$2@1$5$7\2ev@1$5$7@2$3@3$a@1$h1@2$9$6@1$5$7@2$i3?2stZ@2$h0@2$9$6@1$5$7@4$h2$6@1$5$7^2^1@2$h7^2@1$hc?2s'").

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let HLB : forall b, In b LB -> In b (alb s). Proof. intros b Hb. exact (proj1 (proj2 (proj2 HR) b) Hb). Qed.
  (* [comment removed for export] *)
  Let FLG4 : rw_cells asegs m AIAINIT [C1 (b8 (if as_internal_init st then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Proof.
    pose proof R as RR. ndestruct RR as (_ & _ & FL & _).
    ndestruct FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F16 & _). exact F16.
  Qed.
  Let IAX : if as_internal_init st then ia_after m else ia_pristine m.
  Proof. pose proof R as RR. ndestruct RR as (_ & _ & _ & _ & _ & IA & _). unfold ia_rep in IA. unfold ia_after, ia_pristine. exact IA. Qed.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

  Theorem free_arep_null : ltac2:(zQ "70!iu8!hvd!nk4!no5!hh6!hl4!nu8>0>4msF'$4>3mo'$5>0@2$6^2^1@4$2$1$3?1Q@2$0^3^2@4$2$1$3?1Q@2$0?3msF?2mo").
  Proof.
    intros K. destruct AX as [AWV FXR].
    npose PL as (Y1 & Y2 & Y3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    npose DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof R as RR. ndestruct RR as (_ & _ & _ & THR & _). ndestruct THR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UNW). fold TH in UNW. unfold OT_UNWINDING in UNW.
    pose proof (ienv_of_arep s m R) as IEN.
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VISE).
    { eapply (@free_null _ ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo d (as_internal_init st)
                ATSD CTX TH (a_top s) (a_bot s) CH sb).
      - exact LO.
      - clear - HI; lia.   (* [comment removed for export] *)
      - constructor. exact SPA.
      - constructor. exact SPT.
      - constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - constructor. unfold ATSD, AIMG_TOP. fold TH in T1, T2, T3. fold CTX in X2, X3. unfold kPageSize in T1, T2, T3.
        split; [clear; lia|]. split; [clear; lia|]. split; [exact X2|]. split; [exact X3|]. split; [exact T2|]. split; [exact T3|]. clear - T1. zlets. Z.div_mod_to_equations. lia.
      - constructor. clear - D2 D3 TCX. zlets. unfold disj, a_sb, kSpaceSize, kPageSize in *. lia.
      - constructor. repeat match goal with |- _ /\ _ => split end; try exact G10; try exact G12;   (* [comment removed for export] *)
          clear - G1 G2 G3 G4 G5 G6; zlets; unfold a_sb, kSpaceSize, kPageSize, disj in *; lia.
      - constructor. clear - TCX. unfold kPageSize in TCX. lia.
      - clear - G11 G13 LO. lia.
      - exact FCH.
      - rewrite TP. exact IEN.
      - exact MI.
      - exact ST.
      - exact UNW.
      - exact FLG4.
      - exact IAX.
      - exact DEP. }
    cbv beta. intros msF' mo' OK' SBM _ PO.
    ndestruct PO as (m' & RET & MU' & WM' & MI' & UNW' & FLG' & IA' & DEP').
    ndestruct RET as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & VIS' & ST').
    pose proof (arep_after_null s m m' lo (bv_unsigned sp) R LO (munch_agree _ _ _ MU') WM' UNW' FLG' IA') as R'.
    apply K. unfold free_null_gpost.
    nexists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact OK'|]. split; [exact VIS'|].
    split; [split; [exact R'| exact (proj2 HR)]|].
    split; [intros x Hx; apply WM'; exact (AWV x Hx)|].
    split. { ndestruct FXR as (FXa & FXb & [g FXc] & FXd & [bb FXe]). unfold flagsx_rep, ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS in *.
             pose proof (munch_agree _ _ _ MU') as AG'.
             assert (ZT : forall a, 65536 <= a < 7430144 -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) -> outside [(lo, bv_unsigned sp); (TH + 3168, TH + 3169); (AIAINIT, AIAINIT + 4); (AIAINST, AIAINST + 528432)] a).
             { intros a Ha N1 N2. pose proof (akobj_lit _ _ T2) as BT. unfold kPageSize in BT. clear - Ha N1 N2 BT LO. acb. zlets. cbn [outside]. repeat split; try exact I; lia. }
             Ltac trz AG WM H ZT := eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|];
               cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
               let Ha := fresh in intros ? Ha; apply ZT; unfold AIAINIT, AIAINST; clear - Ha; lia.
             split; [trz AG' WM' FXa ZT|]. split; [trz AG' WM' FXb ZT|]. split; [exists g; trz AG' WM' FXc ZT|]. split; [trz AG' WM' FXd ZT|]. exists bb; trz AG' WM' FXe ZT. }
    split; [exact (AMODELX_mat s mo mo' AMX SBM)|].
    split; [exact (nonvm_same_mat mo mo' SBM)|].
    split; [exact DEP'|]. split; [exact DPL|].
    split; [unfold depot_cov; intros x Hx; rewrite (same_but_materialized_vmmaps mo mo' SBM); exact (DCOV x Hx)|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { apply (amframe_of_munch s LB (bv_unsigned sp) _ m m' MU').
             constructor; [cbn [fst snd]; apply (apriv_stack s OKs LB HLB); exact LO|].
             constructor; [cbn [fst snd]; apply (apriv_thread s OKs LB HLB); [| | | clear - LO HI; lia]; unfold kPageSize; clear; zlets; lia|].
             constructor; [cbn [fst snd]; apply (apriv_static s OKs LB HLB); [| clear - LO HI; lia|]; unfold AIAINIT, AIMG_TOP; clear; lia|].
             constructor; [cbn [fst snd]; apply (apriv_static s OKs LB HLB); [| clear - LO HI; lia|]; unfold AIAINST, AIMG_TOP; clear; lia|].
             constructor. }
    split; [exact WM'|].
    split. { apply (acompl_of_munch s s' d lo (bv_unsigned sp) _ m m' MU'). intros iv a Hiv Ha.
             destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; unfold awrit, astatw.
             - left. exact Ha.
             - right. left. unfold kPageSize. clear - Ha. zlets. lia.
             - do 6 right. left. right. right. left. exact Ha.
             - do 6 right. left. right. right. right. clear - Ha. lia. }
    split; [apply avmx_same; [rewrite (same_but_materialized_vmmaps mo mo' SBM); reflexivity| reflexivity]|].
    unfold am_free_full. cbn [Z.eqb].
    destruct (as_internal_init st) eqn:II.
    - exists st, []. split; [reflexivity|]. unfold same_but_shadow. change (a_st s') with (set_internal_init st). unfold set_internal_init. rewrite <- II.
      destruct st; cbn; repeat split; reflexivity.
    - exists (set_internal_init st), [EInternalAllocInit]. split; [reflexivity|]. apply sbs_refl.
  Qed.
End FreeNullGlue.
End HCW.
(* [comment removed for export] *)
