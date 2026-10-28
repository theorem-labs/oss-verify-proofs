(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts AgentLib FileSim
  SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemSplit Spec LibTail RefPrintfLib RefMemcpyLib
  SReach RegsEquivM MainEqv HeapCeil LazyRestrict LazySR LazyFdNodes MainWalk_defs MainSegs MainMem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Arr Step Frame MState SysStep Exec CellsX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0 AsAuxv
  ECH_Xpres ECH_Iface AsCall AsCallX RefExitBase AsPrintfFirst AsExitDefs
  AsDrvHeap AsDrvRun AsDrvOpen AsDrvRead AsDrvMem AsDrvDefs AsTRSegs AsTargetRun AsMainWalk_defs AsMainSegs AsMainPre N9_read AsDrvCells.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Loop.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable L : alib.
  Hypothesis LOK : alib_ok L.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.
  Variables (sp0 : word) (pp tid can : Z) (path data : list byte) (fs0 : Fs) (mem0 : word -> option byte).
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis HCE : hceil + 8388608 <= bv_unsigned sp0.
  Hypothesis Hdata : fs_lookup fs0 path = Some data.
  Hypothesis Htid : 0 < tid < 2 ^ 22.
  Hypothesis TRC : adrv_traces H L.
  Hypothesis LIVE : ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H.

  Let SPlo : 0x7fff80000000 <= bv_unsigned sp0 := proj1 Hvsp.
  Let SPhi : bv_unsigned sp0 <= 0x800000000000 := proj1 (proj2 Hvsp).
  Let SP16 : bv_unsigned sp0 mod 16 = 0 := proj2 (proj2 Hvsp).
  Let rom := seg_rom asegs.
  Let lo : Z := bv_unsigned sp0 - 128 - ATR_STACK.
  Let ppw : word := Z_to_bv 64 pp.
  Let Elo : lo = bv_unsigned sp0 - 128 - 65536. Proof. reflexivity. Qed.
  Let COSTS : cost_laws H. Proof. exact (ah_costs H HH). Qed.

  (* [comment removed for export] *)
  Lemma aceil_lo : aceil + 4096 <= lo.
  Proof. pose proof Elo. acb. lia. Qed.

  (* [comment removed for export] *)
  Record mstatics (m : word -> option byte) : Prop := MST {
    mst_inv   : mem_inv asegs m;
    mst_stk   : stk asegs m lo (bv_unsigned sp0);
    mst_ac    : ACONST m;
    mst_relro : arelro_none m;
    mst_glb   : aglb_none m;
    mst_cells : cells_ok m adrv_cells;
    mst_out   : cells_ok m astdout0;
    mst_tid   : atid_cell m tid;
    mst_can   : acanary m can;
    mst_rfs   : as_RFS H [] m;
    mst_reg   : cells_ok m aatexit_pre_cells;                                        (* [comment removed for export] *)
    mst_lib   : forall i, rin_ivs (al_LIBX0 L) i -> m (Z_to_bv 64 i) = None;        (* [comment removed for export] *)
    mst_ossl  : m (Z_to_bv 64 0xbdd420) = None /\ m (Z_to_bv 64 ACLEANUP) = None;    (* [comment removed for export] *)
    mst_sh0   : exists shi, stack0 m lo shi /\ 0x800000000000 <= shi;
    mst_above : forall a : word, bv_unsigned sp0 <= bv_unsigned a -> m a = mem0 a;
    mst_frame : amframe sp0 m;
    mst_aux   : exists B, as_rauxv_ok H m B /\ bv_unsigned sp0 <= B < 2 ^ 64 /\ aauxv_ok m B;   (* [comment removed for export] *)
    mst_musl0 : amusl0 m                                                              (* [comment removed for export] *) }.

  (* [comment removed for export] *)
  Lemma mst_stk_ok : forall m, mstatics m -> stk_ok RSEGS m (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK.
  Proof.
    intros m ST. pose proof SPlo. pose proof SPhi. pose proof Elo.
    eapply astk_stk_ok; [exact (mst_stk m ST) | unfold MSTK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold MSTK; lia | lia].
  Qed.
  Lemma mst_ro : forall m, mstatics m -> aro_none m.
  Proof. intros m ST. exact (amem_inv_ro_none m (mst_inv m ST)). Qed.
  Lemma mst_stk_spm : forall m, mstatics m -> stk asegs m lo (bv_unsigned sp0 - 128).
  Proof.
    intros m ST. pose proof Elo. destruct (mst_stk m ST) as (S1 & S2 & S3).
    split; [exact S1|]. split; [lia|]. intros a Ha. apply S3. lia.
  Qed.

  (* [comment removed for export] *)
  Definition mwin (LB : list block) (iv : Z * Z) : Prop :=
    (lo <= fst iv /\ snd iv <= bv_unsigned sp0 - 128)
    \/ iv = (AERRNO, AERRNO + 4)
    \/ iv = (AREAD_STAGE, AREAD_STAGE + 65536)
    \/ (exists b, In b LB /\ ablock_range H (blk_addr b) (blk_size b) /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).


  (* [comment removed for export] *)
  Lemma mstatics_munch : forall m m' W LB,
    mstatics m -> munch W m m' -> wmono asegs m m' -> Forall (mwin LB) W ->
    mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp0 - 128) -> ACONST m' ->
    mstatics m'.
  Proof.
    intros m m' W LB [INV STK AC RELRO GLB CELLS OUT TID CAN RFS REG LIBP [OS1 OS2] [shi [SH0 Hshi]] ABOVE FR [B' [AUX [HB' AUXV]]] MUSL] MU WM HW INV' STK' AC'.
    pose proof SPlo. pose proof SPhi. pose proof aceil_lo as HCL. pose proof Elo. acb.
    pose proof (ah_RFS_range H HH _ _ RFS) as [(F1 & F2 & F3 & F4) _]. unfold AIMG_TOP in F1.
    assert (SHT : 0x80178800 <= sh aceil).
    { unfold sh. rewrite ASHADOW_BASE_val. assert (A8 : 0 < 8) by lia. assert (ACL : 0x7fff7f800000 <= aceil) by lia.
      pose proof (Z.div_le_mono _ _ _ A8 ACL) as DM. change (0x7fff7f800000 / 8) with 0xfffeff00000 in DM. lia. }
    pose proof (proj1 (Forall_forall _ _) HW) as HW'.
    (* [comment removed for export] *)
    assert (OUTX : forall x, (bv_unsigned sp0 - 128 <= x \/ (x < 0xc04000 /\ ~ (AERRNO <= x < AERRNO + 4) /\ ~ (AREAD_STAGE <= x < AREAD_STAGE + 65536))) ->
                   outside W x).
    { intros x Hx. apply outside_of_Forall. apply Forall_forall. intros [l h] Hiv. pose proof (HW' _ Hiv) as Hm.
      unfold mwin in Hm. cbn [fst snd] in *.
      destruct Hm as [Hm|[Hm|[Hm|(b & _ & (R1 & R2 & R3 & R4 & R5 & R6 & R7) & Hb1 & Hb2)]]];
        [lia | injection Hm as -> ->; unfold AERRNO, ATP in *; lia | injection Hm as -> ->; unfold AREAD_STAGE in *; lia | unfold AIMG_TOP in R4; lia]. }
    assert (DISJ : forall a n, a + n <= 0xc04000 -> (a + n <= AERRNO \/ AERRNO + 4 <= a) -> (a + n <= AREAD_STAGE \/ AREAD_STAGE + 65536 <= a) ->
                  disjoint_from W a n).
    { intros a n Q1 Q2 Q3. apply disjoint_of_Forall. apply Forall_forall. intros [l h] Hiv. pose proof (HW' _ Hiv) as Hm.
      unfold mwin in Hm. cbn [fst snd] in *.
      destruct Hm as [Hm|[Hm|[Hm|(b & _ & (R1 & R2 & R3 & R4 & R5 & R6 & R7) & Hb1 & Hb2)]]];
        [lia | injection Hm as -> ->; lia | injection Hm as -> ->; lia | unfold AIMG_TOP in R4; lia]. }
    assert (AG : forall x : word, bv_unsigned sp0 - 128 <= bv_unsigned x -> m' x = m x).
    { intros x Hx. apply MU. apply OUTX. left. exact Hx. }
    split.
    - exact INV'.
    - destruct STK as (S1 & S2 & S3). destruct STK' as (_ & _ & S3'). split; [exact S1|]. split; [exact S2|].
      intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp0 - 128)) as [Lc|Lc]; [apply S3'; lia|].
      assert (E : m' (wa a) = m (wa a)) by (apply AG; rewrite wa_eq, u_small by lia; lia).
      unfold wview, mrd. rewrite E. apply S3. lia.
    - exact AC'.
    - intros i Hi. rewrite <- (RELRO i Hi), <- wa_eq. apply MU. rewrite wa_eq, u_small by lia. apply OUTX. right.
      unfold AERRNO, ATP, AREAD_STAGE. lia.
    - destruct GLB as [G1 G2]. split; intros i Hi; [rewrite <- (G1 i Hi) | rewrite <- (G2 i Hi)]; rewrite <- wa_eq; apply MU;
        rewrite wa_eq, u_small by lia; apply OUTX; right; unfold AERRNO, ATP, AREAD_STAGE; lia.
    - eapply cells_ok_munchW; [apply adrv_cells_wf | exact CELLS | exact MU |].
      eapply Forall_impl; [| apply adrv_cells_range]. intros [[a w] v] Ra. apply DISJ; unfold AERRNO, ATP, AREAD_STAGE; lia.
    - eapply cells_ok_munchW; [apply astdout0_wf | exact OUT | exact MU |].
      eapply Forall_impl; [| apply astdout0_range]. intros [[a w] v] Ra. apply DISJ; unfold AERRNO, ATP, AREAD_STAGE; lia.
    - destruct TID as [TID Ht]. split; [|exact Ht]. eapply rdn_munchW; [exact MU | exact TID | lia | cbn; lia |].
      intros x Hx. cbn in Hx. apply OUTX. right. unfold AERRNO, ATP, AREAD_STAGE. lia.
    - destruct CAN as [CAN Hc]. split; [|exact Hc]. eapply rdn_munchW; [exact MU | exact CAN | lia | cbn; lia |].
      intros x Hx. cbn in Hx. apply OUTX. right. unfold AERRNO, ATP, AREAD_STAGE. lia.
    - eapply (ah_RFS_frame H HH); [exact RFS | exact MU | exact WM |].
      apply Forall_forall. intros [l h] Hiv. pose proof (HW' _ Hiv) as Hm. unfold mwin in Hm. cbn [fst snd] in Hm.
      unfold afs_write_ok. left. cbn [fst snd]. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP.
      destruct Hm as [Hm|[Hm|[Hm|(b & _ & (R1 & R2 & R3 & R4 & R5 & R6 & R7) & Hb1 & Hb2)]]];
        [lia | injection Hm as -> ->; unfold AERRNO, ATP; lia | injection Hm as -> ->; unfold AREAD_STAGE; lia | unfold AIMG_TOP in R4; lia].
    - eapply cells_ok_munchW; [vm_compute; reflexivity | exact REG | exact MU |].
      unfold aatexit_pre_cells. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; apply DISJ; unfold AERRNO, ATP, AREAD_STAGE; lia |]). apply Forall_nil.
    - intros i Hi. rewrite <- (LIBP i Hi), <- wa_eq. apply MU. pose proof (alo_libx L LOK i (alo_sub L LOK i Hi)) as WX. unfold alibx_ok in WX.
      rewrite wa_eq, u_small by lia. apply OUTX. right. unfold AERRNO, ATP, AREAD_STAGE. lia.
    - split; [rewrite <- OS1 | rewrite <- OS2]; rewrite <- wa_eq; apply MU; rewrite wa_eq, u_small by (unfold ACLEANUP; lia); apply OUTX; right; unfold AERRNO, ATP, AREAD_STAGE, ACLEANUP; lia.
    - exists shi. split; [|exact Hshi]. eapply stack0_transport; [exact SH0 | exact MU | exact WM |].
      apply Forall_forall. intros [l h] Hiv. pose proof (HW' _ Hiv) as Hm. unfold mwin in Hm. cbn [fst snd] in Hm.
      destruct Hm as [Hm|[Hm|[Hm|(b & _ & (R1 & R2 & R3 & R4 & R5 & R6 & R7) & Hb1 & Hb2)]]];
        [ apply stack0_ok_app; cbn [fst]; unfold AHI_LO; lia
        | injection Hm as -> ->; right; cbn [snd]; unfold AERRNO, ATP; lia
        | injection Hm as -> ->; right; cbn [snd]; unfold AREAD_STAGE; lia
        | eapply stack0_ok_aapp; [exact R7 | cbn [fst]; lia | cbn [snd]; lia] ].
    - intros a Ha. rewrite <- (ABOVE a Ha). apply AG. lia.
    - destruct FR as [FRa FRs]. split.
      + eapply rdn_munchW; [exact MU | exact FRa | lia | cbn; lia |]. intros x Hx. cbn in Hx. apply OUTX. left. lia.
      + intros i Hi. destruct (FRs i Hi) as [w Hw]. exists w.
        eapply rdn_munchW; [exact MU | exact Hw | lia | cbn; lia |]. intros x Hx. cbn in Hx. apply OUTX. left. lia.
    - exists B'. split; [|split; [exact HB'|]].
      + eapply (ah_rauxv_frame H HH LB); [exact AUX | exact MU | exact WM |].
        apply Forall_forall. intros [l h] Hiv. pose proof (HW' _ Hiv) as Hm. unfold mwin in Hm. cbn [fst snd] in Hm.
        unfold aclient_write_ok. cbn [fst snd].
        destruct Hm as [Hm|[Hm|[Hm|(b & HIn & BR & Hb1 & Hb2)]]];
          [ left; lia
          | injection Hm as -> ->; right; left; unfold aimg_client_w, AERRNO, ATLS_PRIV_LO, ATP; lia
          | injection Hm as -> ->; right; left; unfold aimg_client_w, AREAD_STAGE, ATLS_PRIV_LO, ATP; lia
          | right; right; left; exists b; split; [exact HIn | lia] ].
      + pose proof SPlo as HSPLO. pose proof Elo as HELO. eapply aauxv_ok_frame; [exact AUXV | exact MU | exact WM |].
        apply Forall_forall. intros [l h] Hiv. pose proof (HW' _ Hiv) as Hm. unfold mwin in Hm. cbn [fst snd] in Hm.
        unfold aauxv_win_ok, AAUXV_CELL. cbn [fst snd].
        destruct Hm as [Hm|[Hm|[Hm|(b & HIn & (R1 & R2 & R3 & R4 & R5 & R6 & R7) & Hb1 & Hb2)]]];
          [ clear - Hm HB' HSPLO HELO HCL; lia
          | injection Hm as -> ->; unfold AERRNO, ATP; clear - HB' HSPLO; lia
          | injection Hm as -> ->; unfold AREAD_STAGE; clear - HB' HSPLO; lia
          | unfold AIMG_TOP in R4; clear - R4 R5 Hb1 Hb2 HB' HSPLO HELO HCL; lia ] .
    - (* [comment removed for export] *)
      eapply amusl0_frame; [exact MUSL | exact MU | exact WM |]. intros x Hx. unfold alibx_ok in Hx.
      apply OUTX. right. unfold AERRNO, ATP, AREAD_STAGE. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mstatics_frameL : forall m m', mstatics m -> frame_mod m m' (regL_w sp0) -> mstatics m'.
  Proof.
    intros m m' ST FM. pose proof SPlo. pose proof SPhi. pose proof Elo. pose proof aceil_lo as HCL. acb.
    pose proof (frame_mod_munch _ _ _ FM) as MU. pose proof (aframe_mod_wmono _ _ _ FM) as WM.
    unfold regL_w, ivls, MSTK in MU. cbn [map fst snd] in MU. rewrite u_small in MU by lia.
    eapply (mstatics_munch m m' _ [] ST MU WM).
    - constructor; [|constructor]. left. cbn [fst snd]. lia.
    - eapply amem_inv_frame; [exact (mst_inv m ST) | exact FM |]. constructor; [|constructor]. cbn [fst snd]. unfold MSTK. rewrite u_small by lia. lia.
    - apply (astk_grows m m'); [exact (mst_stk_spm m ST) | lia | lia | exact (proj2 FM)].
    - eapply ACONST_frame; [exact (mst_ac m ST) | exact MU | exact WM |]. constructor; [|constructor]. apply aconst_ok_hi. cbn [fst]. unfold AHI_LO. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mstatics_apres : forall m m' LB1 B2,
    mstatics m -> apres H LB1 (bv_unsigned sp0 - 128) m m' ->
    mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp0 - 128) -> ACONST m' ->
    as_rauxv_ok H m' B2 -> bv_unsigned sp0 <= B2 < 2 ^ 64 -> aauxv_ok m' B2 ->
    mstatics m'.
  Proof.
    intros m m' LB1 B2 [INV STK AC RELRO GLB CELLS OUT TID CAN RFS REG LIBP [OS1 OS2] [shi [SH0 Hshi]] ABOVE FR [B' [AUX [HB' AUXV]]] MUSL] HP INV' STK' AC' AUX' HB2 AUXV'.
    pose proof SPlo. pose proof SPhi. pose proof Elo.
    assert (AG : forall x : word, bv_unsigned sp0 - 128 <= bv_unsigned x -> m' x = m x).
    { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP _ (u64_range x) ltac:(left; lia))). }
    assert (IMG : forall x, aimg_client x -> 0 <= x < 2 ^ 64 -> m' (wa x) = m (wa x)).
    { intros x Hx Hx64. exact (proj1 (HP x Hx64 ltac:(right; left; exact Hx))). }
    split; try assumption.
    - destruct STK as (S1 & S2 & S3). destruct STK' as (_ & _ & S3'). split; [exact S1|]. split; [exact S2|].
      intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp0 - 128)) as [Lc|Lc]; [apply S3'; lia|].
      assert (E : m' (wa a) = m (wa a)) by (apply AG; rewrite wa_eq, u_small by lia; lia).
      unfold wview, mrd. rewrite E. apply S3. lia.
    - intros i Hi. rewrite <- (RELRO i Hi), <- wa_eq. apply IMG; [unfold aimg_client; lia | lia].
    - destruct GLB as [G1 G2]. split; intros i Hi; [rewrite <- (G1 i Hi) | rewrite <- (G2 i Hi)]; rewrite <- wa_eq;
        apply IMG; first [lia | unfold aimg_client; lia].
    - eapply cells_ok_apresW; [apply adrv_cells_wf | exact CELLS | exact HP | apply adrv_cells_client].
    - eapply cells_ok_apresW; [apply astdout0_wf | exact OUT | exact HP | apply astdout0_client].
    - destruct TID as [TID Ht]. split; [|exact Ht]. eapply rdn_apresW; [exact HP | exact TID | lia | cbn; lia |].
      intros x Hx. right; left. unfold aimg_client. cbn in Hx. lia.
    - destruct CAN as [CAN Hc]. split; [|exact Hc]. eapply rdn_apresW; [exact HP | exact CAN | lia | cbn; lia |].
      intros x Hx. right; left. unfold aimg_client. cbn in Hx. lia.
    - eapply (RFS_via_apres H HH); [exact RFS | exact HP].
    - eapply cells_ok_apresW; [vm_compute; reflexivity | exact REG | exact HP |].
      unfold aatexit_pre_cells, aimg_client. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil.
    - intros i Hi. rewrite <- (LIBP i Hi), <- wa_eq. pose proof (alo_libx L LOK i (alo_sub L LOK i Hi)) as WX. unfold alibx_ok in WX.
      assert (Hi64 : 0 <= i < 2 ^ 64) by lia. exact (proj1 (HP i Hi64 ltac:(right; left; unfold aimg_client; lia))).
    - split; [rewrite <- OS1 | rewrite <- OS2]; rewrite <- wa_eq; [exact (proj1 (HP 0xbdd420 ltac:(lia) ltac:(right; left; unfold aimg_client; lia))) | exact (proj1 (HP ACLEANUP ltac:(unfold ACLEANUP; lia) ltac:(right; left; unfold aimg_client, ACLEANUP; lia)))].
    - exists shi. split; [|exact Hshi]. eapply (stack0_xpres H); [apply xpres_of_apres; exact HP | exact SH0 | constructor].
    - intros a Ha. rewrite <- (ABOVE a Ha). apply AG. lia.
    - destruct FR as [FRa FRs]. split.
      + eapply rdn_apresW; [exact HP | exact FRa | lia | cbn; lia |]. intros x Hx. left. cbn in Hx. lia.
      + intros i Hi. destruct (FRs i Hi) as [w Hw]. exists w.
        eapply rdn_apresW; [exact HP | exact Hw | lia | cbn; lia |]. intros x Hx. left. cbn in Hx. lia.
    - exists B2. split; [assumption | split; assumption].
    - (* [comment removed for export] *) eapply amusl0_agree; [exact MUSL|]. intros a Ha64 Hx. unfold alibx_ok in Hx.
      exact (HP a Ha64 ltac:(right; left; unfold aimg_client; lia)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition TRC26 : Z := as_Cm H (2 ^ 26) + as_Cf H (2 ^ 26) + 4 * fuzz_cost H L (2 ^ 26).
  Definition CU26 : Z := as_Cm H (2 ^ 26) + as_Cf H (2 ^ 26).
  (* [comment removed for export] *)
  Definition aleft (k : Z) : Z := (10 - k) * CU26 + as_Cf H (2 ^ 26) + TRC26.

  Lemma CU26_nonneg : 0 <= CU26.
  Proof. unfold CU26. destruct COSTS as (C1 & C2 & C3 & C4 & C5 & C6). pose proof (C1 (2 ^ 26) ltac:(lia)). pose proof (C3 (2 ^ 26) ltac:(lia)). lia. Qed.
  Lemma Cm_le26 : forall n, 0 <= n <= 2 ^ 26 -> 0 <= as_Cm H n <= as_Cm H (2 ^ 26).
  Proof. intros n Hn. destruct COSTS as (C1 & C2 & C3 & C4 & C5 & C6). split; [apply C1; lia | apply C2; lia]. Qed.
  Lemma Cf_le26 : forall n, 0 <= n <= 2 ^ 26 -> 0 <= as_Cf H n <= as_Cf H (2 ^ 26).
  Proof. intros n Hn. destruct COSTS as (C1 & C2 & C3 & C4 & C5 & C6). split; [apply C3; lia | apply C4; lia]. Qed.
  Lemma fuzz_cost_mono : forall n n', 0 <= n <= n' -> 0 <= fuzz_cost H L n <= fuzz_cost H L n'.
  Proof.   (* [comment removed for export] *)
    intros n n' Hn. split; [unfold fuzz_cost; apply (alo_cost0 L LOK H _ HH); exact (proj1 Hn)| unfold fuzz_cost; apply (alo_costm L LOK H _ _ HH); exact Hn].
  Qed.
  Lemma atr_cost_le : forall d : list byte, Z.of_nat (length d) < MAX_INPUT -> 6 + hdr_cfg d <= Z.of_nat (length d) -> atr_cost H L d <= TRC26.
  Proof.
    intros d Hd H6. unfold atr_cost, TRC26, MAX_INPUT in *. pose proof (hdr_calls_range d) as HC. pose proof (hdr_cfg_range d) as HG.
    assert (HN : 0 <= hdr_payload_len d <= 2 ^ 26) by (unfold hdr_payload_len; lia).
    pose proof (Cm_le26 _ HN). pose proof (Cf_le26 _ HN). pose proof (fuzz_cost_mono (hdr_payload_len d) (2 ^ 26) ltac:(lia)). nia.
  Qed.

  (* [comment removed for export] *)
  Lemma aleft_malloc : forall k AL n, 0 <= k < 10 -> aleft k <= AL -> 0 <= n <= 2 ^ 26 -> as_Cm H n <= AL.
  Proof.
    intros k AL n Hk HAL Hn. unfold aleft, CU26, TRC26 in HAL.
    pose proof (Cm_le26 n Hn). pose proof (Cm_le26 (2 ^ 26) ltac:(lia)). pose proof (Cf_le26 (2 ^ 26) ltac:(lia)).
    pose proof (fuzz_cost_mono (2 ^ 26) (2 ^ 26) ltac:(lia)). nia.
  Qed.
  Lemma aleft_free : forall k AL AL2 n m, 0 <= k < 10 -> aleft k <= AL -> 0 <= n <= 2 ^ 26 -> 0 <= m <= 2 ^ 26 ->
    AL2 >= AL - as_Cm H n -> as_Cf H m <= AL2.
  Proof.
    intros k AL AL2 n m Hk HAL Hn Hm H2. unfold aleft, CU26, TRC26 in HAL.
    pose proof (Cm_le26 n Hn). pose proof (Cf_le26 m Hm). pose proof (Cm_le26 (2 ^ 26) ltac:(lia)). pose proof (Cf_le26 (2 ^ 26) ltac:(lia)).
    pose proof (fuzz_cost_mono (2 ^ 26) (2 ^ 26) ltac:(lia)). nia.
  Qed.
  Lemma aleft_next : forall k AL AL2 AL3 n m, 0 <= k < 10 -> aleft k <= AL -> 0 <= n <= 2 ^ 26 -> 0 <= m <= 2 ^ 26 ->
    AL2 >= AL - as_Cm H n -> AL3 >= AL2 - as_Cf H m -> aleft (k + 1) <= AL3.
  Proof.
    intros k AL AL2 AL3 n m Hk HAL Hn Hm H2 H3. unfold aleft, CU26, TRC26 in *.
    pose proof (Cm_le26 n Hn). pose proof (Cf_le26 m Hm). pose proof (Cm_le26 (2 ^ 26) ltac:(lia)). pose proof (Cf_le26 (2 ^ 26) ltac:(lia)).
    pose proof (fuzz_cost_mono (2 ^ 26) (2 ^ 26) ltac:(lia)). nia.
  Qed.
  (* [comment removed for export] *)
  Lemma aleft_final : forall k AL, 0 <= k <= 10 -> aleft k <= AL -> TRC26 + as_Cf H (2 ^ 26) <= AL.
  Proof. intros k AL Hk HAL. unfold aleft in HAL. pose proof CU26_nonneg. nia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Record ARInv (len cap A : Z) (s : as_St H) (p : bptr) (regs : bvmap 5 word) (mem : word -> option byte) (mo : Model) : Prop := ARI {
    ari_regs : aread_call_regs sp0 regs ppw A len cap (Z.min (cap - len) 65536);
    ari_len  : 0 <= len < cap /\ len <= Z.of_nat (length data);
    ari_cap  : 65536 <= cap <= 67108864;
    ari_pow  : exists k, 0 <= k /\ cap = 65536 * 2 ^ k /\ aleft k <= as_AL H s;
    ari_heap : as_RHEAP H s [(p, A, cap)] mem;
    ari_cb   : exists junk, rw_cells asegs mem A [CB (Z.to_nat cap) junk];
    ari_addr : addressable mem A cap;
    ari_data : rdn RSEGS mem (Z_to_bv 64 A) (Z.to_nat len) = Some (firstn (Z.to_nat len) data);
    ari_st   : mstatics mem;
    ari_fs   : m_fs mo = fs0;
    ari_fd3  : fd_lookup (m_fds mo) (Z_to_bv 64 3) = Some (FdFile path (Z_to_bv 64 len));
    ari_fd1  : fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    ari_fd2  : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  Record AMInv (len n cap A : Z) (s : as_St H) (p : bptr) (regs : bvmap 5 word) (mem : word -> option byte) (mo : Model) : Prop := AMI {
    ami_regs : am_regs sp0 regs ppw A len cap n;
    ami_len  : 0 <= len /\ 1 <= n /\ len + n <= cap /\ len + n <= Z.of_nat (length data);
    ami_cap  : 65536 <= cap <= 67108864;
    ami_pow  : exists k, 0 <= k /\ cap = 65536 * 2 ^ k /\ aleft k <= as_AL H s;
    ami_heap : as_RHEAP H s [(p, A, cap)] mem;
    ami_cb   : exists junk, rw_cells asegs mem A [CB (Z.to_nat cap) junk];
    ami_addr : addressable mem A cap;
    ami_data : rdn RSEGS mem (Z_to_bv 64 A) (Z.to_nat (len + n)) = Some (firstn (Z.to_nat (len + n)) data);
    ami_st   : mstatics mem;
    ami_fs   : m_fs mo = fs0;
    ami_fd3  : fd_lookup (m_fds mo) (Z_to_bv 64 3) = Some (FdFile path (Z_to_bv 64 (len + n)));
    ami_fd1  : fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    ami_fd2  : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  Record ACInv (cap A : Z) (s : as_St H) (p : bptr) (regs : bvmap 5 word) (mem : word -> option byte) (mo : Model) : Prop := ACI {
    aci_r1 : getr regs 1 = Z_to_bv 64 0x570c10;  aci_r2 : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 144);
    aci_r4 : getr regs 4 = Z_to_bv 64 0xbe1c90;  aci_r8 : getr regs 8 = Z_to_bv 64 2;  aci_r9 : getr regs 9 = Z_to_bv 64 A;
    aci_r10 : getr regs 10 = Z_to_bv 64 3;  aci_r17 : getr regs 17 = Z_to_bv 64 57;  aci_r18 : getr regs 18 = ppw;
    aci_r19 : getr regs 19 = Z_to_bv 64 (Z.of_nat (length data));  aci_r20 : getr regs 20 = Z_to_bv 64 3;
    aci_r21 : getr regs 21 = Z_to_bv 64 cap;  aci_r22 : getr regs 22 = Z_to_bv 64 0xbccf50;
    aci_cap  : Z.of_nat (length data) <= cap /\ 65536 <= cap <= 67108864;
    aci_lt   : Z.of_nat (length data) < MAX_INPUT;
    aci_pow  : exists k, 0 <= k /\ cap = 65536 * 2 ^ k /\ aleft k <= as_AL H s;
    aci_heap : as_RHEAP H s [(p, A, cap)] mem;
    aci_cb   : exists junk, rw_cells asegs mem A [CB (Z.to_nat cap) junk];
    aci_addr : addressable mem A cap;
    aci_data : rdn RSEGS mem (Z_to_bv 64 A) (length data) = Some data;
    aci_st   : mstatics mem;
    aci_ra   : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1eee20));
    aci_fs   : m_fs mo = fs0;
    aci_fd3  : exists e3, fd_lookup (m_fds mo) (Z_to_bv 64 3) = Some e3;
    aci_fd1  : fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    aci_fd2  : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  Record AXInv (cap A : Z) (s : as_St H) (p : bptr) (regs : bvmap 5 word) (mem : word -> option byte) (mo : Model) : Prop := AXI {
    axi_r1 : getr regs 1 = Z_to_bv 64 0x570c10;  axi_r2 : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 144);
    axi_r4 : getr regs 4 = Z_to_bv 64 0xbe1c90;  axi_r8 : getr regs 8 = Z_to_bv 64 2;  axi_r9 : getr regs 9 = Z_to_bv 64 A;
    axi_r10 : getr regs 10 = Z_to_bv 64 0;  axi_r17 : getr regs 17 = Z_to_bv 64 57;  axi_r18 : getr regs 18 = ppw;
    axi_r19 : getr regs 19 = Z_to_bv 64 (Z.of_nat (length data));  axi_r20 : getr regs 20 = Z_to_bv 64 3;
    axi_r21 : getr regs 21 = Z_to_bv 64 cap;  axi_r22 : getr regs 22 = Z_to_bv 64 0xbccf50;
    axi_cap  : Z.of_nat (length data) <= cap /\ 65536 <= cap <= 67108864;
    axi_lt   : Z.of_nat (length data) < MAX_INPUT;
    axi_pow  : exists k, 0 <= k /\ cap = 65536 * 2 ^ k /\ aleft k <= as_AL H s;
    axi_heap : as_RHEAP H s [(p, A, cap)] mem;
    axi_cb   : exists junk, rw_cells asegs mem A [CB (Z.to_nat cap) junk];
    axi_addr : addressable mem A cap;
    axi_data : rdn RSEGS mem (Z_to_bv 64 A) (length data) = Some data;
    axi_st   : mstatics mem;
    axi_ra   : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1eee20));
    axi_fs   : m_fs mo = fs0;
    axi_fd1  : fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    axi_fd2  : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blk_range : forall s p A cap m, as_RHEAP H s [(p, A, cap)] m -> ablock_range H A cap.
  Proof. intros s p A cap m RH. exact (ah_blocks H HH _ _ _ (p, A, cap) RH ltac:(left; reflexivity)). Qed.

  (* [comment removed for export] *)
  Lemma rheap_frameL : forall s LB m m', as_RHEAP H s LB m -> frame_mod m m' (regL_w sp0) -> as_RHEAP H s LB m'.
  Proof.
    intros s LB m m' RH FM. pose proof SPlo. pose proof SPhi. pose proof aceil_lo as HCL. pose proof Elo. acb.
    pose proof (frame_mod_munch _ _ _ FM) as MU. pose proof (aframe_mod_wmono _ _ _ FM) as WM.
    unfold regL_w, ivls, MSTK in MU. cbn [map fst snd] in MU. rewrite u_small in MU by lia.
    eapply (ah_RHEAP_frame H HH); [exact RH | exact MU | exact WM |]. constructor; [|constructor]. left. cbn [fst]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma blkR_frameL : forall A cap m m' junk (k : nat) bs,
    ablock_range H A cap -> frame_mod m m' (regL_w sp0) ->
    rw_cells asegs m A [CB (Z.to_nat cap) junk] -> addressable m A cap -> rdn RSEGS m (Z_to_bv 64 A) k = Some bs -> (Z.of_nat k <= cap) ->
    rw_cells asegs m' A [CB (Z.to_nat cap) junk] /\ addressable m' A cap /\ rdn RSEGS m' (Z_to_bv 64 A) k = Some bs.
  Proof.
    intros A cap m m' junk k bs BR FM HCB AD RD Hk. pose proof SPlo. pose proof SPhi. pose proof aceil_lo as HCL. pose proof Elo. acb.
    pose proof BR as (R1 & R2 & R3 & R4 & R5 & R6 & R7). unfold AIMG_TOP in R4.
    pose proof (frame_mod_munch _ _ _ FM) as MU. pose proof (aframe_mod_wmono _ _ _ FM) as WM.
    unfold regL_w, ivls, MSTK in MU. cbn [map fst snd] in MU. rewrite u_small in MU by lia.
    split; [|split].
    - eapply rw_cells_transport; [exact HCB | exact MU | exact WM |]. cbn. lia.
    - eapply addressable_transport; [exact AD | exact MU | exact WM |]. cbn.
      pose proof (sh_aapp_range A cap R7 R3) as (X1 & X2 & X3). unfold AHI_LO in X3. lia.
    - eapply rdn_munchW; [exact MU | exact RD | lia | lia |]. intros x Hx. cbn. lia.
  Qed.

  Lemma blk_frameL : forall s p A cap m m' junk (k : nat) bs,
    as_RHEAP H s [(p, A, cap)] m -> frame_mod m m' (regL_w sp0) ->
    rw_cells asegs m A [CB (Z.to_nat cap) junk] -> addressable m A cap -> rdn RSEGS m (Z_to_bv 64 A) k = Some bs -> (Z.of_nat k <= cap) ->
    as_RHEAP H s [(p, A, cap)] m' /\ rw_cells asegs m' A [CB (Z.to_nat cap) junk] /\ addressable m' A cap
    /\ rdn RSEGS m' (Z_to_bv 64 A) k = Some bs.
  Proof.
    intros s p A cap m m' junk k bs RH FM HCB AD RD Hk. split; [eapply rheap_frameL; [exact RH | exact FM]|].
    eapply blkR_frameL; try eassumption. exact (blk_range _ _ _ _ _ RH).
  Qed.

  (* [comment removed for export] *)
  Lemma mo_sb : forall mo mo', same_but_materialized mo mo' -> m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo.
  Proof. intros mo mo' SB. split; [apply same_but_materialized_fs | apply same_but_materialized_fds]; exact SB. Qed.
  Lemma mo_mp : forall mo mo', as_MPRES H mo mo' -> m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo.
  Proof. intros mo mo' MP. destruct (adl_mpres H DL _ _ MP) as (E1 & E2 & _). split; [exact E1 | exact E2]. Qed.
  Lemma mo_tr : forall mo1 mo2 mo3, m_fs mo2 = m_fs mo1 /\ m_fds mo2 = m_fds mo1 -> m_fs mo3 = m_fs mo2 /\ m_fds mo3 = m_fds mo2 ->
    m_fs mo3 = m_fs mo1 /\ m_fds mo3 = m_fds mo1.
  Proof. intros mo1 mo2 mo3 [A1 B1] [A2 B2]. split; congruence. Qed.

  Lemma file_read_next : forall len cnt,
    0 <= len -> 0 <= cnt < 2 ^ 64 -> len < 2 ^ 64 ->
    file_read data (Z_to_bv 64 len) (Z_to_bv 64 cnt) = firstn (Z.to_nat cnt) (skipn (Z.to_nat len) data)
    /\ length (file_read data (Z_to_bv 64 len) (Z_to_bv 64 cnt)) = Nat.min (Z.to_nat cnt) (length data - Z.to_nat len).
  Proof.
    intros len cnt Hl Hc Hl2. split.
    - rewrite file_read_unguarded. unfold word_to_nat. rewrite !u_small by lia. reflexivity.
    - rewrite length_file_read. unfold word_to_nat. rewrite !u_small by lia. reflexivity.
  Qed.

  Lemma firstn_app_read : forall (k : nat) (l : list byte) bs,
    bs = firstn (length bs) (skipn k l) -> firstn k l ++ bs = firstn (k + length bs) l.
  Proof. intros k l bs E. rewrite (FileSim.firstn_add l k (length bs)), <- E. reflexivity. Qed.

  Lemma Z_to_bv_1da3cc : forall a b : Z, (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
  Proof. intros. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. bv_wrap_simplify_solve. Qed.

  (* [comment removed for export] *)
  Ltac kept K r E := rewrite (K r ltac:(unfold aheap_kept; cbn [In]; repeat (first [left; reflexivity | right]))); exact E.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma read_step : forall s msF mo regs mem p (A len cap : Z) K,
    as_VIS H s msF = mkst regs (Z_to_bv 64 AREAD_STUB) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    ARInv len cap A s p regs mem mo ->
    (forall regs' mem' msF' mo' n,
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x1eeda0) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       AMInv len n cap A s p regs' mem' mo' -> realizes asegs (mkCfg msF' mo') K) ->
    (len = Z.of_nat (length data) -> forall regs' mem' msF' mo',
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x56aabc) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       ACInv cap A s p regs' mem' mo' -> realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem p A len cap K HV HA [RC [Hlen Hld] Hcap HPOW RH [junk HCB] AD HDATA ST Hfs Hfd3 Hfd1 Hfd2] KMORE KEOF.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof Elo. pose proof aceil_lo as HCL. acb.
    set (cnt := Z.min (cap - len) 65536) in RC.
    destruct RC as (R1 & R2 & R4 & R8 & R9 & R10 & R11 & R12 & R18 & R19 & R20 & R21 & R22).
    pose proof (blk_range _ _ _ _ _ RH) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). unfold AIMG_TOP in B4.
    assert (Hc1 : 1 <= cnt <= 65536) by lia. assert (Hc2 : len + cnt <= cap) by lia.
    destruct (file_read_next len cnt ltac:(lia) ltac:(lia) ltac:(lia)) as [FR FL].
    set (bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 cnt)) in *.
    (* [comment removed for export] *)
    eapply (aread_stage_file H HH DL s msF mo regs mem 3 cnt lo path (Z_to_bv 64 len) data 0x1eee08 K HV HA R1);
      [ lia | reflexivity | exact R4 | exact R10 | exact R11 | exact R12 | lia | exact Hc1
      | rewrite R2, u_small by lia; exact (mst_stk_spm _ ST) | lia | rewrite R2, u_small by lia; unfold AREAD_STACK; lia
      | exact (mst_inv _ ST) | exact (mst_ac _ ST) | exact Hfd3 | rewrite Hfs; exact Hdata | ].
    cbv zeta. fold bs. rewrite R2, !u_small by lia.
    intros regs1 mem1 msF1 mo1 HV1 HA1 KEPT1 Q10 MU1 WM1 INV1 STK1 AC1 RD1 FS1 FDS1.
    assert (ST1 : mstatics mem1).
    { eapply (mstatics_munch mem mem1 _ [] ST MU1 WM1); [| exact INV1 | exact STK1 | exact AC1].
      constructor; [right; right; left; reflexivity | constructor; [left; cbn [fst snd]; unfold AREAD_STACK; lia | constructor]]. }
    assert (BLK1 : as_RHEAP H s [(p, A, cap)] mem1 /\ rw_cells asegs mem1 A [CB (Z.to_nat cap) junk] /\ addressable mem1 A cap
                   /\ rdn RSEGS mem1 (Z_to_bv 64 A) (Z.to_nat len) = Some (firstn (Z.to_nat len) data)).
    { assert (DJ : disjoint_from [(AREAD_STAGE, AREAD_STAGE + 65536); (bv_unsigned sp0 - 128 - AREAD_STACK, bv_unsigned sp0 - 128)] A cap).
      { cbn. unfold AREAD_STAGE, AREAD_STACK. (first [clear - B5 B4 HCL H0 Hvsp; lia | lia]). }
      split; [|split; [|split]].
      - eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 |].
        constructor; [right; left; unfold aimg_client_w, AREAD_STAGE, ATLS_PRIV_LO, ATP; cbn [fst snd]; lia | constructor; [left; cbn [fst]; unfold AREAD_STACK; lia | constructor]].
      - eapply rw_cells_transport; [exact HCB | exact MU1 | exact WM1 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact DJ.
      - eapply addressable_transport; [exact AD | exact MU1 | exact WM1 |]. cbn. unfold AREAD_STAGE, AREAD_STACK.
        pose proof (sh_aapp_range A cap B7 B3) as (X1 & X2 & X3). unfold AHI_LO in X3.
        change (sh AIMG_TOP) with 0x80178800 in X1. lia.
      - eapply rdn_munchW; [exact MU1 | exact HDATA | lia | lia |]. intros x Hx. cbn. unfold AREAD_STAGE, AREAD_STACK. lia. }
    destruct BLK1 as (RH1 & CB1 & AD1 & HDATA1).
    (* [comment removed for export] *)
    assert (RR1 : aread_ret_regs sp0 regs1 ppw A len cap (len_word bs)).
    { unfold aread_ret_regs, albase_regs, abase_regs.
      repeat split; first [ exact Q10 | kept KEPT1 (2:reg)%bv R2 | kept KEPT1 (4:reg)%bv R4 | kept KEPT1 (8:reg)%bv R8
                          | kept KEPT1 (18:reg)%bv R18 | kept KEPT1 (20:reg)%bv R20 | kept KEPT1 (22:reg)%bv R22
                          | kept KEPT1 (9:reg)%bv R9 | kept KEPT1 (19:reg)%bv R19 | kept KEPT1 (21:reg)%bv R21 ]. }
    destruct (Nat.eq_dec (length bs) 0) as [Z0 | NZ].
    - (* [comment removed for export] *)
      assert (Elen : len = Z.of_nat (length data)) by (rewrite FL in Z0; lia).
      assert (Ebs : bs = []) by (destruct bs; [reflexivity | cbn in Z0; lia]).
      assert (Elw : len_word bs = Z_to_bv 64 0) by (rewrite Ebs; reflexivity).
      rewrite Elw in RR1.
      eapply (aseg_L5b H DL sp0 Hvsp s msF1 mo1 regs1 mem1 ppw A len cap K RR1 (mst_stk_ok _ ST1) (mst_ro _ ST1) (mst_relro _ ST1));
        [| exact HV1 | exact HA1].
      intros regs2 mem2 msF2 mo2 HV2 HA2 SB2 T1 T2 T4 T8 T9 T10 T17 T18 T19 T20 T21 T22 FM2 STK2 RA2.
      destruct (blk_frameL s p A cap mem1 mem2 junk (Z.to_nat len) _ RH1 FM2 CB1 AD1 HDATA1 ltac:(lia)) as (RH2 & CB2 & AD2 & HDATA2).
      apply (KEOF Elen regs2 mem2 msF2 mo2 HV2 HA2). split; try assumption.
      + rewrite <- Elen. exact T19.
      + lia.
      + unfold MAX_INPUT. lia.
      + exists junk. exact CB2.
      + rewrite Elen, Nat2Z.id, firstn_all in HDATA2. exact HDATA2.
      + eapply mstatics_frameL; [exact ST1 | exact FM2].
      + rewrite (same_but_materialized_fs _ _ SB2), FS1. exact Hfs.
      + rewrite (same_but_materialized_fds _ _ SB2), FDS1, fd_lookup_insert_eq. eexists. reflexivity.
      + rewrite (same_but_materialized_fds _ _ SB2), FDS1, fd_lookup_insert_neq; [exact Hfd1 | intros E; apply (f_equal bv_unsigned) in E; discriminate].
      + rewrite (same_but_materialized_fds _ _ SB2), FDS1, fd_lookup_insert_neq; [exact Hfd2 | intros E; apply (f_equal bv_unsigned) in E; discriminate].
    - (* [comment removed for export] *)
      set (n := Z.of_nat (length bs)).
      assert (Hn : 1 <= n <= cnt /\ len + n <= Z.of_nat (length data)) by (subst n; rewrite FL; (first [clear - NZ FL Hvsp; lia | lia])).
      assert (Elw : len_word bs = Z_to_bv 64 n) by reflexivity.
      rewrite Elw in RR1.
      eapply (aseg_L5a H DL sp0 Hvsp s msF1 mo1 regs1 mem1 ppw A len cap n K RR1);
        [lia | lia | lia | lia | exact (mst_stk_ok _ ST1) | exact (mst_ro _ ST1) | exact (mst_relro _ ST1) | | exact HV1 | exact HA1].
      intros regs2 mem2 msF2 mo2 HV2 HA2 SB2 LB2 T1 T9 T10 T11 T12 T19 T21 T23 FM2 STK2.
      pose proof (mstatics_frameL _ _ ST1 FM2) as ST2.
      destruct (blk_frameL s p A cap mem1 mem2 junk (Z.to_nat len) _ RH1 FM2 CB1 AD1 HDATA1 ltac:(lia)) as (RH2 & CB2 & AD2 & HDATA2).
      assert (RD2 : rdn RSEGS mem2 (Z_to_bv 64 AREAD_STAGE) (length bs) = Some bs).
      { eapply ardn_frame; [exact FM2 | exact RD1 | unfold AREAD_STAGE; lia | unfold AREAD_STAGE; (first [clear - Hvsp SPlo ACEILB B1 Hc1 FL NZ; lia | lia]) |].
        intros r Hr. unfold regL_w, MSTK in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. unfold AREAD_STAGE. lia. }
      (* [comment removed for export] *)
      destruct (rw_cells_CB_split asegs mem2 A (Z.to_nat cap) (Z.to_nat len) junk CB2 ltac:(lia)) as [CBa CBbc].
      rewrite Z2Nat.id in CBbc by lia.
      destruct (rw_cells_CB_split asegs mem2 (A + len) (Z.to_nat cap - Z.to_nat len) (Z.to_nat n) _ CBbc ltac:((first [clear - Hvsp SPlo Hlen Hcap ACEILB B1 Hc1 FL NZ Hn; lia | lia]))) as [CBb CBc].
      rewrite Z2Nat.id in CBc by lia.
      destruct LB2 as ((U2 & U4 & U8 & U18 & U20) & U22).
      pose proof (aapp_bounds A cap B7 B3) as (_ & _ & AHI & _).
      change (Z_to_bv 64 0x1bdaac) with (Z_to_bv 64 AMEMCPY_STUB) in HV2.
      eapply (amemcpy_call H HH DL regs2 mem2 msF2 mo2 s (bv_unsigned sp0 - 128) (A + len) AREAD_STAGE n lo bs _ 0x1eeda0 K HV2 HA2 T1);
        [ lia | reflexivity | exact U2 | exact T10 | exact T11 | exact T12
        | apply ardn_bytes_at; [exact RD2 | unfold AREAD_STAGE; lia | unfold AREAD_STAGE; lia]
        | subst n; lia
        | exact CBb
        | left; unfold AREAD_STAGE; lia
        | lia | unfold AREAD_STAGE; lia | lia
        | eapply addressable_accessible; [apply ACONST_read_stage; exact (mst_ac _ ST2) | lia | unfold AREAD_STAGE; lia | unfold AREAD_STAGE, AAPP_HI; lia]
        | eapply addressable_accessible; [exact AD2 | lia | lia | lia]
        | apply ACONST_shvis; [exact (mst_ac _ ST2) | unfold AREAD_STAGE, AIMG_LO; lia | lia | unfold AREAD_STAGE, AIMG_TOP; lia]
        | eapply shvis_sub; [eapply (ah_blk_shvis H HH); [exact RH2 | left; reflexivity] | cbn; lia | cbn; lia | cbn; (first [clear - Hn Hvsp; lia | lia]) | lia | cbn; lia]
        | left; unfold AREAD_STAGE; rewrite ASHADOW_BASE_val; lia
        | eapply aapp_in_app_mem; [exact B7 | lia | lia]
        | eapply aconst_ok_aapp; [exact B7 | lia | lia]
        | exact (mst_stk_spm _ ST2) | lia | lia | lia
        | left; (first [clear - Hvsp HCE SPlo H0 ACEILB B1 B5 Hc1 FL NZ; lia | lia]) | left; unfold AREAD_STAGE; lia
        | exact (mst_inv _ ST2) | exact (mst_ac _ ST2) | ].
      intros regs3 mem3 msF3 mo3 HV3 HA3 MP3 KEPT3 Z10 MU3 WM3 INV3 STK3 CB3 BY3 AC3.
      pose proof (u64_range ppw) as Hpp.
      (* [comment removed for export] *)
      assert (ST3 : mstatics mem3).
      { eapply (mstatics_munch mem2 mem3 _ [(p, A, cap)] ST2 MU3 WM3); [| exact INV3 | exact STK3 | exact AC3].
        constructor; [| constructor; [left; cbn [fst snd]; lia | constructor]].
        right; right; right. exists (p, A, cap). split; [left; reflexivity|]. split; [exact (blk_range _ _ _ _ _ RH2)|]. cbn. lia. }
      assert (RH3 : as_RHEAP H s [(p, A, cap)] mem3).
      { eapply (ah_RHEAP_frame H HH); [exact RH2 | exact MU3 | exact WM3 |].
        constructor; [| constructor; [left; cbn [fst]; lia | constructor]].
        right; right; left. exists (p, A, cap). split; [left; reflexivity|]. cbn. lia. }
      assert (CBa3 : rw_cells asegs mem3 A [CB (Z.to_nat len) (take (Z.to_nat len) junk)]).
      { eapply rw_cells_transport; [exact CBa | exact MU3 | exact WM3 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. cbn. lia. }
      assert (CBc3 : rw_cells asegs mem3 (A + len + n) [CB (Z.to_nat cap - Z.to_nat len - Z.to_nat n) (drop (Z.to_nat n) (drop (Z.to_nat len) junk))]).
      { eapply rw_cells_transport; [exact CBc | exact MU3 | exact WM3 |]. cbn [cells_size csize]. rewrite Nat.add_0_r. cbn. (first [clear - Hn B5 HCL H0 Hvsp; lia | lia]). }
      pose proof (rw_cells_CB_join asegs mem3 A (Z.to_nat len) (Z.to_nat n) (take (Z.to_nat len) junk) bs CBa3) as J1.
      rewrite Z2Nat.id in J1 by lia. specialize (J1 CB3).
      pose proof (rw_cells_CB_join asegs mem3 A (Z.to_nat len + Z.to_nat n) (Z.to_nat cap - Z.to_nat len - Z.to_nat n)
                    (take (Z.to_nat len) junk ++ bs) (drop (Z.to_nat n) (drop (Z.to_nat len) junk)) J1) as J2.
      rewrite Nat2Z.inj_add, !Z2Nat.id in J2 by lia. replace (A + (len + n)) with (A + len + n) in J2 by lia. specialize (J2 CBc3).
      replace (Z.to_nat len + Z.to_nat n + (Z.to_nat cap - Z.to_nat len - Z.to_nat n))%nat with (Z.to_nat cap) in J2 by (first [clear - Hn Hcap Hvsp; lia | lia]).
      assert (AD3 : addressable mem3 A cap).
      { eapply addressable_transport; [exact AD2 | exact MU3 | exact WM3 |]. cbn.
        pose proof (aapp_disjoint_sh A cap A cap B7 ltac:(lia) ltac:(lia) B3) as DS.
        pose proof (sh_aapp_range A cap B7 B3) as (X1 & X2 & X3). unfold AHI_LO in X3. (first [clear - X3 X2 DS Hn ACEILB HCL H0 Hlen Hvsp; lia | lia]). }
      assert (HD3 : rdn RSEGS mem3 (Z_to_bv 64 A) (Z.to_nat (len + n)) = Some (take (Z.to_nat (len + n)) data)).
      { replace (Z.to_nat (len + n)) with (Z.to_nat len + length bs)%nat by (first [clear - Hlen Hvsp; lia | lia]).
        rewrite <- (firstn_app_read (Z.to_nat len) data bs)
          by (rewrite FL, FR, <- (take_take (drop _ _)), (take_ge (drop (Z.to_nat len) data) (length data - Z.to_nat len)) by (rewrite length_drop; lia); reflexivity).
        apply rdn_app_Z; [| | lia | lia].
        - eapply rdn_munchW; [exact MU3 | exact HDATA2 | lia | lia |]. intros x Hx. cbn. (first [clear - Hx Hn B5 HCL H0 Hvsp; lia | lia]).
        - rewrite Z2Nat.id by lia. pose proof (bytes_at_rdn asegs mem3 (A + len) bs 0 (length bs) (proj1 (u8arr_of_rw_cells asegs mem3 _ _ _ CB3)) ltac:(lia)) as R.
          cbn [Z.of_nat drop] in R. rewrite Z.add_0_r, wa_eq, firstn_all in R. exact R. }
      (* [comment removed for export] *)
      apply (KMORE regs3 mem3 msF3 mo3 n HV3 HA3). split.
      + unfold am_regs, albase_regs, abase_regs.
        repeat split; first [ kept KEPT3 (2:reg)%bv U2 | kept KEPT3 (4:reg)%bv U4 | kept KEPT3 (8:reg)%bv U8
                            | kept KEPT3 (18:reg)%bv U18 | kept KEPT3 (20:reg)%bv U20 | kept KEPT3 (22:reg)%bv U22
                            | kept KEPT3 (9:reg)%bv T9 | kept KEPT3 (19:reg)%bv T19 | kept KEPT3 (21:reg)%bv T21 | kept KEPT3 (23:reg)%bv T23 ].
      + lia.
      + exact Hcap.
      + exact HPOW.
      + exact RH3.
      + eexists. exact J2.
      + exact AD3.
      + exact HD3.
      + exact ST3.
      + rewrite (proj1 (adl_mpres H DL _ _ MP3)), (same_but_materialized_fs _ _ SB2), FS1. exact Hfs.
      + destruct (adl_mpres H DL _ _ MP3) as (_ & E & _). rewrite E, (same_but_materialized_fds _ _ SB2), FDS1, fd_lookup_insert_eq, Elw, Z_to_bv_1da3cc. reflexivity.
      + destruct (adl_mpres H DL _ _ MP3) as (_ & E & _). rewrite E, (same_but_materialized_fds _ _ SB2), FDS1, fd_lookup_insert_neq; [exact Hfd1 | intros E'; apply (f_equal bv_unsigned) in E'; discriminate].
      + destruct (adl_mpres H DL _ _ MP3) as (_ & E & _). rewrite E, (same_but_materialized_fds _ _ SB2), FDS1, fd_lookup_insert_neq; [exact Hfd2 | intros E'; apply (f_equal bv_unsigned) in E'; discriminate].
  Qed.

  (* [comment removed for export] *)
  Lemma aerrno_rw : forall m regs, getr regs 4 = Z_to_bv 64 ATP -> exists e : word, rw_cells asegs m (bv_unsigned (getr regs 4) + -164) [C4 e].
  Proof.
    intros m regs H4. rewrite H4, u_small by (unfold ATP; lia). replace (ATP + -164) with AERRNO by reflexivity. apply aerrno_rw_any.
  Qed.

  (* [comment removed for export] *)
  Lemma blk_apres : forall LB1 p A cap m m' junk (k : nat) bs,
    apres H LB1 (bv_unsigned sp0 - 128) m m' -> In (p, A, cap) LB1 -> 0 <= A -> 0 <= cap -> A + cap <= 2 ^ 64 ->
    rw_cells asegs m A [CB (Z.to_nat cap) junk] -> addressable m A cap -> rdn RSEGS m (Z_to_bv 64 A) k = Some bs -> Z.of_nat k <= cap ->
    rw_cells asegs m' A [CB (Z.to_nat cap) junk] /\ addressable m' A cap /\ rdn RSEGS m' (Z_to_bv 64 A) k = Some bs.
  Proof.
    intros LB1 p A cap m m' junk k bs HP HIn HA0 Hcap HA64 HCB AD RD Hk. split; [|split].
    - eapply apres_rw_cells; [exact HP | exact HCB |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
      eapply aclient_range_block; [exact HIn | lia | lia].
    - eapply apres_addressable; [exact HP | exact AD | exact HIn].
    - eapply rdn_apresW; [exact HP | exact RD | lia | lia |]. intros x Hx. right; right; left. exists (p, A, cap). split; [exact HIn | cbn; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma AECALL2 : fetch_word asegs (Z_to_bv 64 0x56aabc) = Some ECALLW.
  Proof. exact AECALL. Qed.

  Lemma close_step : forall s msF mo regs mem p A cap K,
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x56aabc) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    ACInv cap A s p regs mem mo ->
    (forall regs' msF' mo', as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x56aac0) mem rom -> as_AKREL H s (mkCfg msF' mo') ->
       AXInv cap A s p regs' mem mo' -> realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem p A cap K HV HA CI HK.
    destruct CI as [R1 R2 R4 R8 R9 R10 R17 R18 R19 R20 R21 R22 Hcap Hlen HPOW RH HCB AD HDATA ST Hra Hfs [e3 He3] Hfd1 Hfd2].
    eapply (drv_close H DL s msF regs (Z_to_bv 64 0x56aabc) mem mo ECALLW (Z_to_bv 64 3) e3 K AECALL2 is_ecall_ECALLW HV HA R17 R10);
      [ rewrite u_small by lia; lia | exact He3 |].
    intros msF' HV' HA'. rewrite AgentLib.v_addi_lit in HV' by lia. change (0x56aabc + 4)%Z with 0x56aac0%Z in HV'.
    apply (HK _ msF' _ HV' HA'). split; try assumption;
      try (rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate); assumption).
    - apply getr_same. intros E; apply (f_equal bv_unsigned) in E; discriminate.
    - rewrite with_fds_fds, fd_lookup_remove_neq; [exact Hfd1 | intros E; apply (f_equal bv_unsigned) in E; discriminate].
    - rewrite with_fds_fds, fd_lookup_remove_neq; [exact Hfd2 | intros E; apply (f_equal bv_unsigned) in E; discriminate].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma m_cont : forall s msF mo regs mem p (A len n cap : Z) K,
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x1eeda0) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    AMInv len n cap A s p regs mem mo -> len + n <> cap ->
    (forall regs' mem' msF' mo', as_VIS H s msF' = mkst regs' (Z_to_bv 64 AREAD_STUB) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       ARInv (len + n) cap A s p regs' mem' mo' -> realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem p A len n cap K HV HA [MR Hlen Hcap HPOW RH [junk HCB] AD HDATA ST Hfs Hfd3 Hfd1 Hfd2] Hne HK.
    pose proof SPlo. pose proof SPhi. pose proof Elo. acb.
    pose proof (blk_range _ _ _ _ _ RH) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    eapply (aseg_Ma H DL sp0 Hvsp s msF mo regs mem ppw A len cap n K MR); [lia | lia | lia | lia | exact Hne
      | exact (mst_stk_ok _ ST) | exact (mst_ro _ ST) | exact (mst_relro _ ST) | | exact HV | exact HA].
    intros regs1 mem1 msF1 mo1 HV1 HA1 SB1 NR1 Q9 FM1 STK1.
    pose proof (mstatics_frameL _ _ ST FM1) as ST1.
    destruct (blk_frameL s p A cap mem mem1 junk _ _ RH FM1 HCB AD HDATA ltac:(lia)) as (RH1 & CB1 & AD1 & HDATA1).
    eapply (aseg_N H DL sp0 Hvsp s msF1 mo1 regs1 mem1 ppw A (len + n) cap K NR1); [lia | lia
      | exact STK1 | exact (mst_ro _ ST1) | exact (mst_relro _ ST1) | | exact HV1 | exact HA1].
    intros regs2 mem2 msF2 mo2 HV2 HA2 SB2 RC2 FM2 STK2.
    destruct (blk_frameL s p A cap mem1 mem2 junk _ _ RH1 FM2 CB1 AD1 HDATA1 ltac:(lia)) as (RH2 & CB2 & AD2 & HDATA2).
    change (Z_to_bv 64 0x1a8728) with (Z_to_bv 64 AREAD_STUB) in HV2.
    apply (HK regs2 mem2 msF2 mo2 HV2 HA2). split; try assumption.
    - lia.
    - exists junk. exact CB2.
    - eapply mstatics_frameL; [exact ST1 | exact FM2].
    - rewrite (same_but_materialized_fs _ _ SB2), (same_but_materialized_fs _ _ SB1). exact Hfs.
    - rewrite (same_but_materialized_fds _ _ SB2), (same_but_materialized_fds _ _ SB1). exact Hfd3.
    - rewrite (same_but_materialized_fds _ _ SB2), (same_but_materialized_fds _ _ SB1). exact Hfd1.
    - rewrite (same_but_materialized_fds _ _ SB2), (same_but_materialized_fds _ _ SB1). exact Hfd2.
  Qed.

  (* [comment removed for export] *)
  Record ARfInv (A : Z) (s : as_St H) (p : bptr) (regs : bvmap 5 word) (mem : word -> option byte) (mo : Model) : Prop := ARFI {
    arf_regs : abase_regs sp0 regs ppw;
    arf_r9   : getr regs 9 = Z_to_bv 64 A;
    arf_heap : exists cap, as_RHEAP H s [(p, A, cap)] mem;
    arf_st   : mstatics mem;
    arf_fs   : m_fs mo = fs0;
    arf_fd1  : fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    arf_fd2  : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  Lemma m_refuse : forall s msF mo regs mem p (A len n cap : Z) K,
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x1eeda0) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    AMInv len n cap A s p regs mem mo -> len + n = cap -> MAX_INPUT <= cap ->
    (forall regs' mem' msF' mo', as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x1eef6c) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       ARfInv A s p regs' mem' mo' -> realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem p A len n cap K HV HA [MR Hlen Hcap HPOW RH [junk HCB] AD HDATA ST Hfs Hfd3 Hfd1 Hfd2] Hcapeq Hbig HK.
    pose proof SPlo. pose proof SPhi. pose proof Elo. acb. unfold MAX_INPUT in Hbig.
    pose proof (blk_range _ _ _ _ _ RH) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    eapply (aseg_Mb H DL sp0 Hvsp s msF mo regs mem ppw A len cap n K MR); [lia | lia | lia | exact Hcapeq
      | exact (mst_stk_ok _ ST) | exact (mst_ro _ ST) | exact (mst_relro _ ST) | | exact HV | exact HA].
    intros regs1 mem1 msF1 mo1 HV1 HA1 SB1 GR1 FM1 STK1.
    pose proof (mstatics_frameL _ _ ST FM1) as ST1.
    destruct (blk_frameL s p A cap mem mem1 junk _ _ RH FM1 HCB AD HDATA ltac:(lia)) as (RH1 & CB1 & AD1 & HDATA1).
    eapply (aseg_Gr H DL sp0 Hvsp s msF1 mo1 regs1 mem1 ppw A cap K GR1); [lia
      | exact STK1 | exact (mst_ro _ ST1) | exact (mst_relro _ ST1) | | exact HV1 | exact HA1].
    intros regs2 mem2 msF2 mo2 HV2 HA2 SB2 BR2 Q9 FM2 STK2.
    destruct (blk_frameL s p A cap mem1 mem2 junk _ _ RH1 FM2 CB1 AD1 HDATA1 ltac:(lia)) as (RH2 & CB2 & AD2 & HDATA2).
    apply (HK regs2 mem2 msF2 mo2 HV2 HA2). split.
    - exact BR2.
    - exact Q9.
    - exists cap. exact RH2.
    - eapply mstatics_frameL; [exact ST1 | exact FM2].
    - rewrite (same_but_materialized_fs _ _ SB2), (same_but_materialized_fs _ _ SB1). exact Hfs.
    - rewrite (same_but_materialized_fds _ _ SB2), (same_but_materialized_fds _ _ SB1). exact Hfd1.
    - rewrite (same_but_materialized_fds _ _ SB2), (same_but_materialized_fds _ _ SB1). exact Hfd2.
  Qed.

  (* [comment removed for export] *)
  Lemma m_grow : forall s msF mo regs mem p (A len n cap : Z) K,
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x1eeda0) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    AMInv len n cap A s p regs mem mo -> len + n = cap -> cap < MAX_INPUT ->
    (forall regs' mem' msF' mo' A' s' p', as_VIS H s' msF' = mkst regs' (Z_to_bv 64 AREAD_STUB) mem' rom -> as_AKREL H s' (mkCfg msF' mo') ->
       ARInv cap (2 * cap) A' s' p' regs' mem' mo' -> realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof using HCEIL H HH DL L LOK sp0 pp tid can path data fs0 mem0 Hvsp HCE Htid TRC LIVE.
    intros s msF mo regs mem p A len n cap K HV HA [MR Hlen Hcap [k (Hk & HPOW & HAL)] RH [junk HCB] AD HDATA ST Hfs Hfd3 Hfd1 Hfd2] Hcapeq Hsmall HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof Elo. pose proof aceil_lo as HCL. acb. unfold MAX_INPUT in Hsmall.
    pose proof (blk_range _ _ _ _ _ RH) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). unfold AIMG_TOP in B4.
    assert (Hk10 : k < 10).
    { destruct (Z_lt_le_dec k 10) as [?|Hge]; [assumption|]. exfalso.
      pose proof (Z.pow_le_mono_r 2 10 k ltac:(lia) Hge) as X. change (2 ^ 10) with 1024 in X. lia. }
    assert (Hcap2 : 2 * cap <= 67108864).
    { pose proof (Z.pow_le_mono_r 2 (k + 1) 10 ltac:(lia) ltac:(lia)) as X. rewrite Z.pow_succ_r in X by lia. change (2 ^ 10) with 1024 in X. lia. }
    rewrite Hcapeq in HDATA, Hfd3.
    (* [comment removed for export] *)
    eapply (aseg_Mb H DL sp0 Hvsp s msF mo regs mem ppw A len cap n K MR); [lia | lia | lia | exact Hcapeq
      | exact (mst_stk_ok _ ST) | exact (mst_ro _ ST) | exact (mst_relro _ ST) | | exact HV | exact HA].
    intros regsA memA msFA moA HVA HAA SBA GRA FMA STKA.
    pose proof (mstatics_frameL _ _ ST FMA) as STA.
    destruct (blk_frameL s p A cap mem memA junk _ _ RH FMA HCB AD HDATA ltac:(lia)) as (RHA & CBA & ADA & HDA).
    (* [comment removed for export] *)
    eapply (aseg_Gb H DL sp0 Hvsp s msFA moA regsA memA ppw A cap K GRA); [lia
      | exact STKA | exact (mst_ro _ STA) | exact (mst_relro _ STA) | | exact HVA | exact HAA].
    intros regsB memB msFB moB HVB HAB SBB ((Q2 & Q4 & Q8 & Q18 & Q20) & Q22) Q1 Q9 Q10 Q19 Q21 Q23 FMB STKB.
    pose proof (mstatics_frameL _ _ STA FMB) as STB.
    destruct (blk_frameL s p A cap memA memB junk _ _ RHA FMB CBA ADA HDA ltac:(lia)) as (RHB & CBB & ADB & HDB).
    (* [comment removed for export] *)
    destruct (aerrno_rw memB regsB Q4) as [errv ERR]. destruct (mst_aux _ STB) as [B' [AUXB [HB' AUXVB]]].
    change (Z_to_bv 64 0x1bf174) with (Z_to_bv 64 AMALLOC_STUB) in HVB.
    eapply (amalloc_call H HH DL regsB memB msFB moB s [(p, A, cap)] (2 * cap) lo B' errv 0x1eedc8 [] K HVB HAB Q1);
      [ lia | reflexivity | exact Q4 | exact Q10 | lia | exact RHB
      | apply (ah_alloc H HH s [(p, A, cap)] memB (2 * cap) RHB); [lia | cbn [lb_bytes fold_right blk_size snd]; unfold ADRV_LIVE in LIVE; lia | cbn [length]; unfold ADRV_CNT in LIVE; lia]
      | apply (aleft_malloc k); [lia | exact HAL | lia]
      | exact AUXB | rewrite Q2, u_small by lia; lia
      | rewrite Q2, u_small by lia; exact (mst_stk_spm _ STB) | lia | rewrite Q2, u_small by lia; unfold AMALLOC_STACK; lia
      | rewrite Q2, u_small by lia; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
      | exact ERR | exact (mst_inv _ STB) | exact (mst_ac _ STB)
      | apply (ah_chain_nil H HH); rewrite Q8, u_small by lia; lia
      | cbn [map]; destruct TRC as (_ & T2 & _); exact T2 |].
    rewrite Q2, !u_small by lia.
    intros regsC memC msFC moC A2 p2 s2 errv2 junk2 HVC HAC MPC KEPTC R10 INVC STKC ERRC AUXC HPC BR2 RHC CB2 AD2 ACC HALC.
    pose proof (mo_tr _ _ _ (mo_sb _ _ SBA) (mo_tr _ _ _ (mo_sb _ _ SBB) (mo_mp _ _ MPC))) as EQC.
    assert (STC : mstatics memC) by (eapply (mstatics_apres memB memC); [exact STB | exact HPC | exact INVC | exact STKC | exact ACC | exact AUXC | exact HB' | eapply (aauxv_ok_apres H); [exact AUXVB | exact HPC | lia]]).
    destruct (blk_apres [(p, A, cap)] p A cap memB memC junk _ _ HPC ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) CBB ADB HDB ltac:(lia))
      as (CBC & ADC & HDC).
    pose proof BR2 as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold AIMG_TOP in C4.
    pose proof (aapp_bounds A2 (2 * cap) C7 C3) as (_ & _ & AHI2 & _). pose proof (aapp_bounds A cap B7 B3) as (_ & _ & AHI & _).
    (* [comment removed for export] *)
    assert (Hp : p2 <> p).
    { intros E. pose proof (ah_nodup H HH s2 _ memC RHC) as ND. cbn [map blk_id fst] in ND. subst p2. inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
    assert (DISJ : A2 + 2 * cap <= A \/ A + cap <= A2).
    { pose proof (ah_disj H HH s2 _ memC (p2, A2, 2 * cap) (p, A, cap) RHC ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hp) as D.
      cbn [blk_addr blk_size fst snd] in D. lia. }
    (* [comment removed for export] *)
    assert (S2 : getr regsC 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)) by (kept KEPTC (2:reg)%bv Q2).
    assert (S4 : getr regsC 4 = Z_to_bv 64 0xbe1c90) by (kept KEPTC (4:reg)%bv Q4).
    assert (S8 : getr regsC 8 = Z_to_bv 64 2) by (kept KEPTC (8:reg)%bv Q8).
    assert (S18 : getr regsC 18 = ppw) by (kept KEPTC (18:reg)%bv Q18).
    assert (S20 : getr regsC 20 = Z_to_bv 64 3) by (kept KEPTC (20:reg)%bv Q20).
    assert (S22 : getr regsC 22 = Z_to_bv 64 0xbccf50) by (kept KEPTC (22:reg)%bv Q22).
    assert (S9 : getr regsC 9 = Z_to_bv 64 A) by (kept KEPTC (9:reg)%bv Q9).
    assert (S19 : getr regsC 19 = Z_to_bv 64 cap) by (kept KEPTC (19:reg)%bv Q19).
    assert (S21 : getr regsC 21 = Z_to_bv 64 (2 * cap)) by (kept KEPTC (21:reg)%bv Q21).
    assert (S23 : getr regsC 23 = Z_to_bv 64 A) by (kept KEPTC (23:reg)%bv Q23).
    (* [comment removed for export] *)
    eapply (aseg_L2 H DL sp0 Hvsp s2 msFC moC regsC memC ppw A cap (2 * cap) A2 K);
      [ split; [split; [exact S2 | split; [exact S4 | split; [exact S8 | split; [exact S18 | exact S20]]]] | exact S22]
      | exact R10 | exact S19 | exact S21 | exact S9 | exact S23 | lia | lia
      | exact (mst_stk_ok _ STC) | exact (mst_ro _ STC) | exact (mst_relro _ STC) | | exact HVC | exact HAC].
    intros regsD memD msFD moD HVD HAD SBD ((T2 & T4 & T8 & T18 & T20) & T22) T1 T9 T10 T11 T12 T19 T21 T23 FMD STKD.
    pose proof (mo_tr _ _ _ EQC (mo_sb _ _ SBD)) as EQD.
    pose proof (mstatics_frameL _ _ STC FMD) as STD. pose proof (rheap_frameL _ _ _ _ RHC FMD) as RHD.
    destruct (blkR_frameL A cap memC memD junk _ _ (blk_range _ _ _ _ _ RHB) FMD CBC ADC HDC ltac:(lia)) as (CBD & ADD & HDD).
    destruct (blkR_frameL A2 (2 * cap) memC memD junk2 0%nat [] BR2 FMD CB2 AD2 ltac:(reflexivity) ltac:(lia)) as (CB2D & AD2D & _).
    (* [comment removed for export] *)
    set (bsrc := take (Z.to_nat cap) data) in *.
    assert (Lbs : length bsrc = Z.to_nat cap) by (subst bsrc; rewrite length_take; lia).
    destruct (rw_cells_CB_split asegs memD A2 (Z.to_nat (2 * cap)) (Z.to_nat cap) junk2 CB2D ltac:(lia)) as [CB2a CB2b].
    rewrite Z2Nat.id in CB2b by lia.
    change (Z_to_bv 64 0x1bdaac) with (Z_to_bv 64 AMEMCPY_STUB) in HVD.
    eapply (amemcpy_call H HH DL regsD memD msFD moD s2 (bv_unsigned sp0 - 128) A2 A cap lo bsrc _ 0x1eede4 K HVD HAD T1);
      [ lia | reflexivity | exact T2 | exact T10 | exact T11 | exact T12
      | apply ardn_bytes_at; [rewrite Lbs; exact HDD | lia | lia]
      | exact Lbs
      | exact CB2a
      | lia | lia | lia | lia
      | eapply addressable_accessible; [exact ADD | lia | lia | lia]
      | eapply addressable_accessible; [exact AD2D | lia | lia | lia]
      | eapply (ah_blk_shvis H HH); [exact RHD | right; left; reflexivity]
      | eapply shvis_sub; [eapply (ah_blk_shvis H HH); [exact RHD | left; reflexivity] | cbn; lia | cbn; lia | cbn; lia | lia | cbn; lia]
      | eapply aapp_in_app_mem; [exact B7 | lia | lia]
      | eapply aapp_in_app_mem; [exact C7 | lia | lia]
      | eapply aconst_ok_aapp; [exact C7 | lia | lia]
      | exact (mst_stk_spm _ STD) | lia | lia | lia
      | left; lia | left; lia
      | exact (mst_inv _ STD) | exact (mst_ac _ STD) | ].
    intros regsE memE msFE moE HVE HAE MPE KEPTE Z10 MUE WME INVE STKE CBE BYE ACE.
    pose proof (mo_tr _ _ _ EQD (mo_mp _ _ MPE)) as EQE.
    assert (STE : mstatics memE).
    { eapply (mstatics_munch memD memE _ [(p2, A2, 2 * cap); (p, A, cap)] STD MUE WME); [| exact INVE | exact STKE | exact ACE].
      constructor; [| constructor; [left; cbn [fst snd]; lia | constructor]].
      right; right; right. exists (p2, A2, 2 * cap). split; [left; reflexivity|]. split; [exact BR2|]. cbn. lia. }
    assert (RHE : as_RHEAP H s2 [(p2, A2, 2 * cap); (p, A, cap)] memE).
    { eapply (ah_RHEAP_frame H HH); [exact RHD | exact MUE | exact WME |].
      constructor; [| constructor; [left; cbn [fst]; lia | constructor]].
      right; right; left. exists (p2, A2, 2 * cap). split; [left; reflexivity|]. cbn. lia. }
    (* [comment removed for export] *)
    assert (CB2bE : rw_cells asegs memE (A2 + cap) [CB (Z.to_nat (2 * cap) - Z.to_nat cap) (drop (Z.to_nat cap) junk2)]).
    { eapply rw_cells_transport; [exact CB2b | exact MUE | exact WME |]. cbn [cells_size csize]. rewrite Nat.add_0_r. cbn. (first [clear - Hvsp HCE SPlo Hcap Hk ACEILB B1 B5 C1 C3 C5; lia | lia]). }
    pose proof (rw_cells_CB_join asegs memE A2 (Z.to_nat cap) (Z.to_nat (2 * cap) - Z.to_nat cap) bsrc (drop (Z.to_nat cap) junk2) CBE) as J2.
    rewrite Z2Nat.id in J2 by lia. specialize (J2 CB2bE).
    replace (Z.to_nat cap + (Z.to_nat (2 * cap) - Z.to_nat cap))%nat with (Z.to_nat (2 * cap)) in J2 by (first [clear - Hvsp; lia | lia]).
    assert (AD2E : addressable memE A2 (2 * cap)).
    { eapply addressable_transport; [exact AD2D | exact MUE | exact WME |]. cbn.
      pose proof (aapp_disjoint_sh A2 (2 * cap) A2 (2 * cap) C7 ltac:(lia) ltac:(lia) ltac:(lia)) as DS.
      pose proof (sh_aapp_range A2 (2 * cap) C7 C3) as (X1 & X2 & X3). unfold AHI_LO in X3. lia. }
    assert (HD2E : rdn RSEGS memE (Z_to_bv 64 A2) (Z.to_nat cap) = Some bsrc).
    { pose proof (bytes_at_rdn asegs memE A2 bsrc 0 (length bsrc) (proj1 (u8arr_of_rw_cells asegs memE _ _ _ CBE)) ltac:(lia)) as R.
      cbn [Z.of_nat drop] in R. rewrite Z.add_0_r, wa_eq, firstn_all, Lbs in R. exact R. }
    (* [comment removed for export] *)
    assert (CBEo : rw_cells asegs memE A [CB (Z.to_nat cap) junk]).
    { eapply rw_cells_transport; [exact CBD | exact MUE | exact WME |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. cbn. lia. }
    assert (ADEo : addressable memE A cap).
    { eapply addressable_transport; [exact ADD | exact MUE | exact WME |]. cbn.
      pose proof (aapp_disjoint_sh A2 (2 * cap) A cap C7 ltac:(lia) ltac:(lia) ltac:(lia)) as DS.
      pose proof (sh_aapp_range A cap B7 B3) as (X1 & X2 & X3). unfold AHI_LO in X3. lia. }
    (* [comment removed for export] *)
    assert (U2 : getr regsE 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)) by (kept KEPTE (2:reg)%bv T2).
    assert (U4 : getr regsE 4 = Z_to_bv 64 0xbe1c90) by (kept KEPTE (4:reg)%bv T4).
    assert (U8 : getr regsE 8 = Z_to_bv 64 2) by (kept KEPTE (8:reg)%bv T8).
    assert (U18 : getr regsE 18 = ppw) by (kept KEPTE (18:reg)%bv T18).
    assert (U20 : getr regsE 20 = Z_to_bv 64 3) by (kept KEPTE (20:reg)%bv T20).
    assert (U22 : getr regsE 22 = Z_to_bv 64 0xbccf50) by (kept KEPTE (22:reg)%bv T22).
    assert (U9 : getr regsE 9 = Z_to_bv 64 A2) by (kept KEPTE (9:reg)%bv T9).
    assert (U19 : getr regsE 19 = Z_to_bv 64 cap) by (kept KEPTE (19:reg)%bv T19).
    assert (U21 : getr regsE 21 = Z_to_bv 64 (2 * cap)) by (kept KEPTE (21:reg)%bv T21).
    assert (U23 : getr regsE 23 = Z_to_bv 64 A) by (kept KEPTE (23:reg)%bv T23).
    (* [comment removed for export] *)
    eapply (aseg_L3 H DL sp0 Hvsp s2 msFE moE regsE memE ppw A cap (2 * cap) A2 K);
      [ split; [split; [exact U2 | split; [exact U4 | split; [exact U8 | split; [exact U18 | exact U20]]]] | exact U22]
      | exact U9 | exact U19 | exact U21 | exact U23
      | exact (mst_stk_ok _ STE) | exact (mst_ro _ STE) | exact (mst_relro _ STE) | | exact HVE | exact HAE].
    intros regsF memF msFF moF HVF HAF SBF ((V2 & V4 & V8 & V18 & V20) & V22) V1 V9 V10 V19 V21 FMF STKF.
    pose proof (mo_tr _ _ _ EQE (mo_sb _ _ SBF)) as EQF.
    pose proof (mstatics_frameL _ _ STE FMF) as STF. pose proof (rheap_frameL _ _ _ _ RHE FMF) as RHF.
    destruct (blkR_frameL A2 (2 * cap) memE memF _ _ _ BR2 FMF J2 AD2E HD2E ltac:(lia)) as (CB2F & AD2F & HD2F).
    destruct (blkR_frameL A cap memE memF junk 0%nat [] (blk_range _ _ _ _ _ RHB) FMF CBEo ADEo ltac:(reflexivity) ltac:(lia)) as (CBFo & ADFo & _).
    (* [comment removed for export] *)
    destruct (aerrno_rw memF regsF V4) as [errvF ERRF]. destruct (mst_aux _ STF) as [BF [AUXF [HBF AUXVF]]].
    change (Z_to_bv 64 0x1bf170) with (Z_to_bv 64 AFREE_STUB) in HVF.
    eapply (afree_call H HH DL regsF memF msFF moF s2 [(p2, A2, 2 * cap); (p, A, cap)] p A cap lo BF errvF 0x1eedec [] junk (shadow_of cap) K HVF HAF V1);
      [ lia | reflexivity | exact V4 | exact V10 | exact RHF | right; left; reflexivity
      | apply (aleft_free k (as_AL H s) _ (2 * cap) cap); [lia | exact HAL | lia | lia | exact HALC]
      | exact CBFo | exact (proj2 ADFo) | apply shadow_of_length; lia
      | exact AUXF | rewrite V2, u_small by lia; lia
      | rewrite V2, u_small by lia; exact (mst_stk_spm _ STF) | lia | rewrite V2, u_small by lia; unfold AFREE_STACK; lia
      | rewrite V2, u_small by lia; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
      | exact ERRF | exact (mst_inv _ STF) | exact (mst_ac _ STF)
      | apply (ah_chain_nil H HH); rewrite V8, u_small by lia; lia
      | cbn [map]; destruct TRC as (_ & _ & T3 & _); exact T3 |].
    rewrite V2, !u_small by lia.
    intros regsG memG msFG moG s3 HVG HAG MPG KEPTG INVG STKG ERRG AUXG HPG RHG ACG HALG.
    pose proof (mo_tr _ _ _ EQF (mo_mp _ _ MPG)) as EQG.
    assert (ELB : as_lb_remove H p [(p2, A2, 2 * cap); (p, A, cap)] = [(p2, A2, 2 * cap)]).
    { destruct (ah_lb_remove H HH) as (L1 & L2 & L3). rewrite (L2 p (p2, A2, 2 * cap)) by (cbn; exact Hp). rewrite (L1 p A cap []) by (cbn; (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])])). reflexivity. }
    rewrite ELB in HPG, RHG.
    assert (STG : mstatics memG) by (eapply (mstatics_apres memF memG); [exact STF | exact HPG | exact INVG | exact STKG | exact ACG | exact AUXG | exact HBF | eapply (aauxv_ok_apres H); [exact AUXVF | exact HPG | lia]]).
    destruct (blk_apres [(p2, A2, 2 * cap)] p2 A2 (2 * cap) memF memG _ _ _ HPG ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) CB2F AD2F HD2F ltac:(lia))
      as (CB2G & AD2G & HD2G).
    assert (W2 : getr regsG 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)) by (kept KEPTG (2:reg)%bv V2).
    assert (W4 : getr regsG 4 = Z_to_bv 64 0xbe1c90) by (kept KEPTG (4:reg)%bv V4).
    assert (W8 : getr regsG 8 = Z_to_bv 64 2) by (kept KEPTG (8:reg)%bv V8).
    assert (W18 : getr regsG 18 = ppw) by (kept KEPTG (18:reg)%bv V18).
    assert (W20 : getr regsG 20 = Z_to_bv 64 3) by (kept KEPTG (20:reg)%bv V20).
    assert (W22 : getr regsG 22 = Z_to_bv 64 0xbccf50) by (kept KEPTG (22:reg)%bv V22).
    assert (W9 : getr regsG 9 = Z_to_bv 64 A2) by (kept KEPTG (9:reg)%bv V9).
    assert (W19 : getr regsG 19 = Z_to_bv 64 cap) by (kept KEPTG (19:reg)%bv V19).
    assert (W21 : getr regsG 21 = Z_to_bv 64 (2 * cap)) by (kept KEPTG (21:reg)%bv V21).
    (* [comment removed for export] *)
    eapply (aseg_R H DL sp0 Hvsp s3 msFG moG regsG memG ppw A2 cap (2 * cap) K);
      [ split; [split; [split; [exact W2 | split; [exact W4 | split; [exact W8 | split; [exact W18 | exact W20]]]] | exact W22] |]
      | lia | lia
      | exact (mst_stk_ok _ STG) | exact (mst_ro _ STG) | exact (mst_relro _ STG) | | exact HVG | exact HAG].
    { split; [exact W19 | split; [exact W21 | exact W9]]. }
    intros regsH memH msFH moH HVH HAH SBH RCH FMH STKH.
    pose proof (mo_tr _ _ _ EQG (mo_sb _ _ SBH)) as [EFS EFDS].
    pose proof (rheap_frameL _ _ _ _ RHG FMH) as RHH.
    destruct (blkR_frameL A2 (2 * cap) memG memH _ _ _ BR2 FMH CB2G AD2G HD2G ltac:(lia)) as (CB2H & AD2H & HD2H).
    change (Z_to_bv 64 0x1a8728) with (Z_to_bv 64 AREAD_STUB) in HVH.
    apply (HK regsH memH msFH moH A2 s3 p2 HVH HAH). split.
    - exact RCH.
    - lia.
    - lia.
    - exists (k + 1). split; [lia|]. split; [rewrite Z.pow_succ_r by lia; lia|].
      eapply (aleft_next k (as_AL H s) (as_AL H s2) (as_AL H s3) (2 * cap) cap); [lia | exact HAL | lia | lia | exact HALC | exact HALG].
    - exact RHH.
    - eexists. exact CB2H.
    - exact AD2H.
    - fold bsrc. exact HD2H.
    - eapply mstatics_frameL; [exact STG | exact FMH].
    - rewrite EFS. exact Hfs.
    - rewrite EFDS. exact Hfd3.
    - rewrite EFDS. exact Hfd1.
    - rewrite EFDS. exact Hfd2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma loop_sound : forall (n : nat) len cap A s p regs mem msF mo K,
    Z.of_nat (length data) - len <= Z.of_nat n ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 AREAD_STUB) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    ARInv len cap A s p regs mem mo ->
    (forall cap' A' s' p' regs' mem' msF' mo',
       as_VIS H s' msF' = mkst regs' (Z_to_bv 64 0x56aabc) mem' rom -> as_AKREL H s' (mkCfg msF' mo') ->
       ACInv cap' A' s' p' regs' mem' mo' -> realizes asegs (mkCfg msF' mo') K) ->
    (MAX_INPUT <= Z.of_nat (length data) -> forall A' s' p' regs' mem' msF' mo',
       as_VIS H s' msF' = mkst regs' (Z_to_bv 64 0x1eef6c) mem' rom -> as_AKREL H s' (mkCfg msF' mo') ->
       ARfInv A' s' p' regs' mem' mo' -> realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof using HCEIL H HH DL L LOK sp0 pp tid can path data fs0 mem0 Hvsp HCE Hdata Htid TRC LIVE.
    induction n as [|n IH]; intros len cap A s p regs mem msF mo K Hn HV HA RI KEOF KREF.
    - (* [comment removed for export] *)
      pose proof (ari_len _ _ _ _ _ _ _ _ RI) as Hlen.
      eapply read_step; [exact HV | exact HA | exact RI | | intros _; exact (KEOF cap A s p)].
      intros regs' mem' msF' mo' n0 _ _ MI. exfalso. pose proof (ami_len _ _ _ _ _ _ _ _ _ MI). lia.
    - pose proof (ari_len _ _ _ _ _ _ _ _ RI) as Hlen. pose proof (ari_cap _ _ _ _ _ _ _ _ RI) as Hcap.
      eapply read_step; [exact HV | exact HA | exact RI | | intros _; exact (KEOF cap A s p)].
      intros regs1 mem1 msF1 mo1 n0 HV1 HA1 MI. pose proof (ami_len _ _ _ _ _ _ _ _ _ MI) as Hlen1.
      destruct (Z.eq_dec (len + n0) cap) as [Heq | Hne].
      + destruct (Z_lt_le_dec cap MAX_INPUT) as [Hsmall | Hbig].
        * eapply m_grow; [exact HV1 | exact HA1 | exact MI | exact Heq | exact Hsmall |]. intros regs2 mem2 msF2 mo2 A2 s2 p2 HV2 HA2 RI2.
          eapply (IH cap); [lia | exact HV2 | exact HA2 | exact RI2 | exact KEOF | exact KREF].
        * eapply m_refuse; [exact HV1 | exact HA1 | exact MI | exact Heq | exact Hbig |]. intros regs2 mem2 msF2 mo2 HV2 HA2 RF2.
          exact (KREF ltac:(lia) A s p regs2 mem2 msF2 mo2 HV2 HA2 RF2).
      + eapply m_cont; [exact HV1 | exact HA1 | exact MI | exact Hne |]. intros regs2 mem2 msF2 mo2 HV2 HA2 RI2.
        eapply (IH (len + n0)); [lia | exact HV2 | exact HA2 | exact RI2 | exact KEOF | exact KREF].
  Qed.
End Loop.
