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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0
  AsCall AsCallX RefExitBase AsPrintfFirst AsExitDefs AsExit AsTailExit AsRefused AsDrvTails AsSxKit
  AsDrvHeap AsDrvRun AsDrvMem AsDrvDefs AsTRSegs AsMainWalk_defs AsMainSegs AsMainPre AsMainLoop AsDrvCells ECH_Iface.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma stk_store_ok : forall m lo hi (a : word) n,
  stk asegs m lo hi -> lo <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= hi -> hi < 2 ^ 64 ->
  store_ok RSEGS m a n = true.
Proof.
  intros m lo hi a n (S1 & S2 & S3) Hlo Hhi H64. apply astore_ok_of_wview; [lia|].
  intros i Hi. rewrite <- wa_eq. exact (proj1 (S3 (bv_unsigned a + i) ltac:(lia))).
Qed.

Lemma zero_lines_length : forall k, length (zero_lines k) = (2 * k)%nat.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [zero_lines length]. rewrite IH. lia. Qed.
Lemma zero_lines_S : forall k, zero_lines (S k) = [Z_to_bv 8 48; Z_to_bv 8 10] ++ zero_lines k.
Proof. reflexivity. Qed.

Section Exit.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable L : alib.
  Hypothesis LOK : alib_ok L.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.
  Variables (sp0 : word) (tid can : Z).
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis HCE : hceil + 8388608 <= bv_unsigned sp0.
  Hypothesis Htid : 0 < tid < 2 ^ 22.
  Hypothesis TRC : adrv_traces H L.

  Let SPlo : 0x7fff80000000 <= bv_unsigned sp0 := proj1 Hvsp.
  Let SPhi : bv_unsigned sp0 <= 0x800000000000 := proj1 (proj2 Hvsp).
  Let SP16 : bv_unsigned sp0 mod 16 = 0 := proj2 (proj2 Hvsp).
  Let rom := seg_rom asegs.
  Let lo : Z := bv_unsigned sp0 - 128 - ATR_STACK.
  Let Elo : lo = bv_unsigned sp0 - 128 - 65536. Proof. reflexivity. Qed.

  Lemma aceil_loX : aceil + 4096 <= lo.
  Proof. pose proof Elo. acb. lia. Qed.

  (* [comment removed for export] *)
  Record xstat (m : word -> option byte) : Prop := XS {
    xs_inv   : mem_inv asegs m;
    xs_stk   : stk asegs m lo (bv_unsigned sp0);
    xs_ac    : ACONST m;
    xs_relro : arelro_none m;
    xs_glb   : aglb_none m;
    xs_cells : cells_ok m xdrv_cells;
    xs_tid   : exists t, atid_cell m t;
    xs_can   : exists c, acanary m c;
    xs_frame : amframe sp0 m;
    xs_aux   : exists B, as_rauxv_ok H m B /\ bv_unsigned sp0 <= B < 2 ^ 64;
    xs_err   : exists we re : word, rdn RSEGS m (Z_to_bv 64 0x5edcd0) 8 = Some (word_to_le_bytes 8 we) /\ rdn RSEGS m (Z_to_bv 64 0x5edce0) 8 = Some (word_to_le_bytes 8 we)
                                 /\ rdn RSEGS m (Z_to_bv 64 0x5edcb0) 8 = Some (word_to_le_bytes 8 re) /\ rdn RSEGS m (Z_to_bv 64 0x5edcb8) 8 = Some (word_to_le_bytes 8 re);
    xs_elock : cell_ok m (0x5edd34, 4%nat, 0xffffffff) }.

  (* [comment removed for export] *)
  Definition ostate (pending : list byte) (m : word -> option byte) : Prop :=
    (pending = [] /\ cells_ok m astdout0) \/ (exists k, (k <= 3)%nat /\ astdout_after m k /\ pending = zero_lines k).

  (* [comment removed for export] *)
  Lemma xstat_of_mstatics : forall mem0 m, mstatics H L sp0 tid can mem0 m -> xstat m.
  Proof.
    intros mem0 m [INV STK AC RELRO GLB CELLS OUT TID CAN RFS REG LIBP OSSL SH0 ABOVE FR [B' [AUX [HB' AUXV]]]]. split; try assumption; try (exists B'; split; [exact AUX | exact HB']).   (* [comment removed for export] *)
    - apply xdrv_of_adrv. exact CELLS.
    - exists tid. exact TID.
    - exists can. exact CAN.
    - exists (Z_to_bv 64 0), (Z_to_bv 64 0). pose proof (fun c => cells_ok_In _ _ c CELLS) as CI.
      repeat split; [ exact (CI (0x5edcd0, 8%nat, 0) ltac:(in_solve)) | exact (CI (0x5edce0, 8%nat, 0) ltac:(in_solve))
                    | exact (CI (0x5edcb0, 8%nat, 0) ltac:(in_solve)) | exact (CI (0x5edcb8, 8%nat, 0) ltac:(in_solve)) ].
    - exact (cells_ok_In _ _ (0x5edd34, 4%nat, 0xffffffff) CELLS ltac:(in_solve)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma img_rdn_frameL : forall m m' (a : Z) n bs,
    frame_mod m m' (regL_w sp0) -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= AIMG_TOP ->
    rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros m m' a n bs FM RD Ha Hn. pose proof SPlo. pose proof SPhi. unfold AIMG_TOP in Hn.
    eapply ardn_frame; [exact FM | exact RD | lia | lia |].
    intros r Hr. unfold regL_w, MSTK in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. lia.
  Qed.
  Lemma img_rdn_apres : forall LB m m' (a : Z) n bs,
    apres H LB (bv_unsigned sp0 - 128) m m' -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a ->
    (forall x, a <= x < a + Z.of_nat n -> aimg_client x) -> a + Z.of_nat n <= AIMG_TOP ->
    rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros LB m m' a n bs HP RD Ha HC Hn. unfold AIMG_TOP in Hn. eapply rdn_apresW; [exact HP | exact RD | lia | lia |].
    intros x Hx. right; left. apply HC. exact Hx.
  Qed.

  Lemma ostate_pres : forall pending m m',
    (forall (a : Z) n bs, 0x5ede88 <= a -> a + Z.of_nat n <= 0xc02ba8 -> (a + Z.of_nat n <= 0x5edf1c \/ 0xc027a8 <= a) ->
       rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> rdn RSEGS m' (Z_to_bv 64 a) n = Some bs) ->
    ostate pending m -> ostate pending m'.
  Proof.
    intros pending m m' T [[E ST]|(k & Hk & ST & E)].
    - left. split; [exact E|]. unfold cells_ok in *. apply Forall_forall. intros [[a w] v] Hin.
      pose proof (proj1 (Forall_forall _ _) ST _ Hin) as C. pose proof (proj1 (Forall_forall _ _) astdout0_range _ Hin) as R.
      cbn [fst snd] in R. unfold cell_ok in *. apply T; [lia | lia | lia | exact C].
    - right. exists k. split; [exact Hk|]. split; [|exact E].
      destruct ST as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14]. pose proof (zero_lines_length k) as ZL.
      split; (apply T; [cbn; lia | cbn; try rewrite ZL; lia | cbn; try rewrite ZL; lia | assumption]).
  Qed.

  Lemma ostate_frameL : forall pending m m', ostate pending m -> frame_mod m m' (regL_w sp0) -> ostate pending m'.
  Proof.
    intros pending m m' OS FM. eapply ostate_pres; [|exact OS]. intros a n bs H1 H2 H3 RD.
    eapply img_rdn_frameL; [exact FM | exact RD | lia | unfold AIMG_TOP; lia].
  Qed.
  Lemma ostate_apres : forall pending LB m m', ostate pending m -> apres H LB (bv_unsigned sp0 - 128) m m' -> ostate pending m'.
  Proof.
    intros pending LB m m' OS HP. eapply ostate_pres; [|exact OS]. intros a n bs H1 H2 H3 RD.
    eapply img_rdn_apres; [exact HP | exact RD | lia | | unfold AIMG_TOP; lia]. intros x Hx. unfold aimg_client. lia.
  Qed.

  Lemma xstat_frameL : forall m m', xstat m -> frame_mod m m' (regL_w sp0) -> xstat m'.
  Proof.
    intros m m' [INV STK AC RELRO GLB CELLS [t [TID Ht]] [c [CAN Hc]] [FRa FRs] [B' [AUX HB']] (we & re & E1 & E2 & E3 & E4) EL] FM.
    pose proof SPlo. pose proof SPhi. pose proof Elo. pose proof aceil_loX as HCL. acb.
    pose proof (frame_mod_munch _ _ _ FM) as MU. pose proof (aframe_mod_wmono _ _ _ FM) as WM.
    unfold regL_w, ivls, MSTK in MU. cbn [map fst snd] in MU. rewrite u_small in MU by lia.
    assert (T : forall (a : Z) n bs, rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= AIMG_TOP -> rdn RSEGS m' (Z_to_bv 64 a) n = Some bs).
    { intros a n bs RD Ha Hn. eapply img_rdn_frameL; eassumption. }
    split.
    - eapply amem_inv_frame; [exact INV | exact FM |]. constructor; [|constructor]. cbn [fst snd]. unfold MSTK. rewrite u_small by lia. lia.
    - destruct STK as (S1 & S2 & S3).
      assert (STK1 : stk asegs m lo (bv_unsigned sp0 - 128)) by (split; [exact S1|]; split; [lia|]; intros x Hx; apply S3; lia).
      pose proof (astk_grows m m' lo (bv_unsigned sp0 - 128) STK1 ltac:(lia) ltac:(lia) (proj2 FM)) as (_ & _ & S3').
      split; [exact S1|]. split; [exact S2|].
      intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp0 - 128)) as [Lc|Lc].
      + apply S3'. lia.
      + assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_eq, u_small by lia; cbn; lia).
        unfold wview, mrd. rewrite E. apply S3. lia.
    - eapply ACONST_frame; [exact AC | exact MU | exact WM |]. constructor; [|constructor]. apply aconst_ok_hi. cbn [fst]. unfold AHI_LO. lia.
    - intros i Hi. rewrite <- (RELRO i Hi), <- wa_eq. apply MU. rewrite wa_eq, u_small by lia. cbn. lia.
    - destruct GLB as [G1 G2]. split; intros i Hi; [rewrite <- (G1 i Hi) | rewrite <- (G2 i Hi)]; rewrite <- wa_eq; apply MU;
        rewrite wa_eq, u_small by lia; cbn; lia.
    - eapply cells_ok_munchW; [apply xdrv_cells_wf | exact CELLS | exact MU |].
      eapply Forall_impl; [| apply xdrv_cells_range]. intros [[a w] v] Ra. cbn. lia.
    - exists t. split; [|exact Ht]. apply T; [exact TID | lia | unfold AIMG_TOP; cbn; lia].
    - exists c. split; [|exact Hc]. apply T; [exact CAN | lia | unfold AIMG_TOP; cbn; lia].
    - split.
      + eapply rdn_munchW; [exact MU | exact FRa | lia | cbn; lia |]. intros x Hx. cbn in Hx |- *. lia.
      + intros i Hi. destruct (FRs i Hi) as [w Hw]. exists w. eapply rdn_munchW; [exact MU | exact Hw | lia | cbn; lia |]. intros x Hx. cbn in Hx |- *. lia.
    - exists B'. split; [|exact HB']. eapply (ah_rauxv_frame H HH []); [exact AUX | exact MU | exact WM |].
      constructor; [|constructor]. left. cbn [fst]. lia.
    - exists we, re. repeat split; (apply T; [assumption | lia | unfold AIMG_TOP; cbn; lia]).
    - unfold cell_ok in *. apply T; [exact EL | lia | unfold AIMG_TOP; cbn; lia].
  Qed.

  Lemma xstat_apres : forall m m' LB1 B2,
    xstat m -> apres H LB1 (bv_unsigned sp0 - 128) m m' ->
    mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp0 - 128) -> ACONST m' ->
    as_rauxv_ok H m' B2 -> bv_unsigned sp0 <= B2 < 2 ^ 64 ->
    xstat m'.
  Proof.
    intros m m' LB1 B2 [INV STK AC RELRO GLB CELLS [t [TID Ht]] [c [CAN Hc]] [FRa FRs] AUX (we & re & E1 & E2 & E3 & E4) EL] HP INV' STK' AC' AUX' HB2.
    pose proof SPlo. pose proof SPhi. pose proof Elo.
    assert (AG : forall x : word, bv_unsigned sp0 - 128 <= bv_unsigned x -> m' x = m x).
    { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP _ (u64_range x) ltac:(left; lia))). }
    assert (IMG : forall x, aimg_client x -> 0 <= x < 2 ^ 64 -> m' (wa x) = m (wa x)).
    { intros x Hx Hx64. exact (proj1 (HP x Hx64 ltac:(right; left; exact Hx))). }
    assert (T : forall (a : Z) n bs, rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a -> (forall x, a <= x < a + Z.of_nat n -> aimg_client x) ->
               a + Z.of_nat n <= AIMG_TOP -> rdn RSEGS m' (Z_to_bv 64 a) n = Some bs).
    { intros a n bs RD Ha HC Hn. eapply img_rdn_apres; eassumption. }
    split; try assumption.
    - destruct STK as (S1 & S2 & S3). destruct STK' as (_ & _ & S3'). split; [exact S1|]. split; [exact S2|].
      intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp0 - 128)) as [Lc|Lc]; [apply S3'; lia|].
      assert (E : m' (wa a) = m (wa a)) by (apply AG; rewrite wa_eq, u_small by lia; lia).
      unfold wview, mrd. rewrite E. apply S3. lia.
    - intros i Hi. rewrite <- (RELRO i Hi), <- wa_eq. apply IMG; [unfold aimg_client; lia | lia].
    - destruct GLB as [G1 G2]. split; intros i Hi; [rewrite <- (G1 i Hi) | rewrite <- (G2 i Hi)]; rewrite <- wa_eq;
        apply IMG; first [lia | unfold aimg_client; lia].
    - eapply cells_ok_apresW; [apply xdrv_cells_wf | exact CELLS | exact HP | apply xdrv_cells_client].
    - exists t. split; [|exact Ht]. apply T; [exact TID | lia | intros x Hx; unfold aimg_client; cbn in Hx; lia | unfold AIMG_TOP; cbn; lia].
    - exists c. split; [|exact Hc]. apply T; [exact CAN | lia | intros x Hx; unfold aimg_client; cbn in Hx; lia | unfold AIMG_TOP; cbn; lia].
    - split.
      + eapply rdn_apresW; [exact HP | exact FRa | lia | cbn; lia |]. intros x Hx. left. cbn in Hx. lia.
      + intros i Hi. destruct (FRs i Hi) as [w Hw]. exists w. eapply rdn_apresW; [exact HP | exact Hw | lia | cbn; lia |]. intros x Hx. left. cbn in Hx. lia.
    - exists B2. split; assumption.
    - exists we, re. repeat split; (apply T; [assumption | lia | intros x Hx; unfold aimg_client; cbn in Hx; lia | unfold AIMG_TOP; cbn; lia]).
    - unfold cell_ok in *. apply T; [exact EL | lia | intros x Hx; unfold aimg_client; cbn in Hx; lia | unfold AIMG_TOP; cbn; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma abi_any : forall m, exists b : byte, rdn RSEGS m (Z_to_bv 64 0xbdd420) 1 = Some [b].
  Proof.
    intros m. change (rdn RSEGS) with (OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.rdn asegs). rewrite rdn_unfold.
    assert (E : exists b, mrd asegs m (Z_to_bv 64 0xbdd420) = Some b).
    { unfold mrd. destruct (m (Z_to_bv 64 0xbdd420)) as [b|]; [exists b; reflexivity|].
      exists (Z_to_bv 8 0). rewrite seg_rom_same. vm_compute. reflexivity. }
    destruct E as [b E]. rewrite E. exists b. reflexivity.
  Qed.
  Lemma byte_refold : forall b : byte, word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned b)) = [b].
  Proof.
    intros b. rewrite AsSxKit.word_to_le_bytes_1. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
    pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. unfold bv_wrap, bv_modulus. apply Z.mod_small. lia.
  Qed.
  Lemma abi_none0 : forall m, m (Z_to_bv 64 0xbdd420) = None -> rdn RSEGS m (Z_to_bv 64 0xbdd420) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
  Proof.
    intros m Hn. change (rdn RSEGS) with (OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.rdn asegs). rewrite rdn_unfold.
    unfold mrd. rewrite Hn. rewrite seg_rom_same. vm_compute. reflexivity.
  Qed.
  Lemma adgc_cell0 : forall m, m (Z_to_bv 64 ACLEANUP) = None -> cell_ok m (0xbdd440, 1%nat, 0).
  Proof.
    intros m Hn. unfold cell_ok, ACLEANUP in *. change (rdn RSEGS) with (OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.rdn asegs). rewrite rdn_unfold.
    unfold mrd. rewrite Hn. rewrite seg_rom_same. vm_compute. reflexivity.
  Qed.
  Lemma none_frameL : forall m m' (a : Z), frame_mod m m' (regL_w sp0) -> 0 <= a < AIMG_TOP -> m (Z_to_bv 64 a) = None -> m' (Z_to_bv 64 a) = None.
  Proof.
    intros m m' a FM Ha Hn. pose proof SPlo. pose proof SPhi. unfold AIMG_TOP in Ha. rewrite <- Hn. apply (proj1 FM). apply outside_of_disjoint.
    intros r Hr. unfold regL_w, MSTK in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite !u_small by lia. lia.
  Qed.
  Lemma none_apres : forall LB m m' (a : Z), apres H LB (bv_unsigned sp0 - 128) m m' -> aimg_client a -> 0 <= a < 2 ^ 64 ->
    m (Z_to_bv 64 a) = None -> m' (Z_to_bv 64 a) = None.
  Proof. intros LB m m' a HP HC Ha Hn. rewrite <- Hn, <- wa_eq. exact (proj1 (HP a Ha ltac:(right; left; exact HC))). Qed.
  Lemma atxc_frameL : forall ax2 m m', cells_ok m (ax_atexit_cells ax2) -> frame_mod m m' (regL_w sp0) -> cells_ok m' (ax_atexit_cells ax2).
  Proof.
    intros ax2 m m' HC FM. pose proof SPlo. pose proof SPhi. eapply acells_ok_frame; [destruct ax2; vm_compute; reflexivity | exact HC | exact FM |].
    destruct ax2; unfold ax_atexit_cells;
      repeat (apply Forall_cons; [intros r Hr; unfold regL_w, MSTK in Hr; cbn [In] in Hr; destruct Hr as [<-|[]]; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by lia; lia |]);
      apply Forall_nil.
  Qed.
  Lemma atxc_apres : forall ax2 LB m m', cells_ok m (ax_atexit_cells ax2) -> apres H LB (bv_unsigned sp0 - 128) m m' -> cells_ok m' (ax_atexit_cells ax2).
  Proof.
    intros ax2 LB m m' HC HP. eapply cells_ok_apresW; [destruct ax2; vm_compute; reflexivity | exact HC | exact HP |].
    destruct ax2; unfold ax_atexit_cells, aimg_client; repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]); apply Forall_nil.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma axH_of : forall ax2 m (ro : word),
    xstat m ->
    rdn RSEGS m (Z_to_bv 64 0x5ede90) 8 = Some (word_to_le_bytes 8 ro) -> rdn RSEGS m (Z_to_bv 64 0x5ede98) 8 = Some (word_to_le_bytes 8 ro) ->
    cell_ok m (0x5edf14, 4%nat, 0xffffffff) ->
    cells_ok m (ax_atexit_cells ax2) -> m (Z_to_bv 64 ACLEANUP) = None ->
    exists t c we re, axH ax2 m (Z_to_bv 64 (bv_unsigned sp0 - 48)) t c we re ro.
  Proof.
    intros ax2 m ro [INV STK AC RELRO [G1 G2] CELLS [t [TID Ht]] [c [CAN Hc]] FR AUX (we & re & E1 & E2 & E3 & E4) EL] R1 R2 OL ATX DGC.
    pose proof SPlo. pose proof SPhi. pose proof SP16. pose proof Elo.
    exists t, c, we, re. split; try assumption.
    - rewrite u_small by lia. rewrite <- Zminus_mod_idemp_l, SP16. reflexivity.
    - unfold ASP_LO. rewrite u_small by lia. lia.
    - unfold ASP_HI. rewrite u_small by lia. lia.
    - eapply astk_stk_ok; [exact STK | rewrite u_small by lia; lia | rewrite u_small by lia; lia | lia | lia].
    - lia.
    - exact (amem_inv_ro_none m INV).
    - exact (amem_inv_text_none m INV).
    - apply ax_lit_cells_of; try assumption. apply adgc_cell0. exact DGC.
    - intros a n Ha Hn. pose proof (ACONST_imgvis m AC) as SV.
      change (sh AIMG_LO) with 0x7fffa000 in SV. change (sh AIMG_TOP) with 0x80178800 in SV.
      eapply stk_store_ok; [exact SV | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem free_exit : forall (ax2 : bool) s msF mo regs mem p (A cap : Z) (status : word) (pending : list byte) junk (LBX : list block),
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x1eef18) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr regs 4 = Z_to_bv 64 ATP -> getr regs 8 = status -> getr regs 9 = Z_to_bv 64 A ->
    bv_unsigned status < 256 ->
    as_RHEAP H s LBX mem -> In (p, A, cap) LBX -> rw_cells asegs mem A [CB (Z.to_nat cap) junk] -> addressable mem A cap ->
    as_Cf H cap <= as_AL H s ->
    xstat mem -> ostate pending mem ->
    cells_ok mem (ax_atexit_cells ax2) -> mem (Z_to_bv 64 ACLEANUP) = None ->                 (* [comment removed for export] *)
    (ax2 = false -> mem (Z_to_bv 64 0xbdd420) = None /\ pending = []) ->                    (* [comment removed for export] *)
    fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    realizes asegs (mkCfg msF mo) (t_emit (W 1 pending) (t_exit (bv_and status (Z_to_bv 64 255)) (m_fs mo))).
  Proof.
    intros ax2 s msF mo regs mem p A cap status pending junk LBX HV HA R2 R4 R8 R9 Hst RH HInA HCB AD HCF XS OS ATX DGC PRE2 Hfd1. pose proof (u64_range status) as HstR.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof Elo. pose proof aceil_loX as HCL. acb.
    pose proof (ah_blocks H HH _ _ _ (p, A, cap) RH HInA) as BR. pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in *.
    (* [comment removed for export] *)
    assert (STK0 : stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK).
    { eapply astk_stk_ok; [exact (xs_stk _ XS) | unfold MSTK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold MSTK; lia | lia]. }
    eapply (aseg_I H DL sp0 Hvsp s msF mo regs mem (getr regs 18) A status _ R2 R4 R8 R9 STK0 (amem_inv_ro_none _ (xs_inv _ XS)) (xs_relro _ XS));
      [| exact HV | exact HA].
    intros regs1 mem1 msF1 mo1 HV1 HA1 SB1 Q2 Q4 Q8 Q1 Q9 Q10 KP FM1 STK1.
    pose proof (xstat_frameL _ _ XS FM1) as XS1. pose proof (ostate_frameL _ _ _ OS FM1) as OS1.
    pose proof (atxc_frameL ax2 _ _ ATX FM1) as ATX1. pose proof (none_frameL _ _ ACLEANUP FM1 ltac:(unfold ACLEANUP, AIMG_TOP; lia) DGC) as DGC1.
    assert (PRE2a : ax2 = false -> mem1 (Z_to_bv 64 0xbdd420) = None /\ pending = []).
    { intros E. destruct (PRE2 E) as [B P]. split; [exact (none_frameL _ _ 0xbdd420 FM1 ltac:(unfold AIMG_TOP; lia) B) | exact P]. }
    pose proof (rheap_frameL H HH sp0 Hvsp HCE _ _ _ _ RH FM1) as RH1.
    destruct (blkR_frameL H sp0 Hvsp HCE A cap mem mem1 junk 0%nat [] BR FM1 HCB AD ltac:(reflexivity) ltac:(lia)) as (CB1 & AD1 & _).
    (* [comment removed for export] *)
    destruct (aerrno_rw_any mem1) as [errv ERR]. destruct (xs_aux _ XS1) as [B' [AUX1 HB']].
    assert (STKlo : stk asegs mem1 lo (bv_unsigned sp0 - 128)).
    { destruct (xs_stk _ XS1) as (S1 & S2 & S3). split; [exact S1|]. split; [lia|]. intros a Ha. apply S3. lia. }
    change (Z_to_bv 64 0x1bf170) with (Z_to_bv 64 AFREE_STUB) in HV1.
    eapply (afree_call H HH DL regs1 mem1 msF1 mo1 s LBX p A cap lo B' errv 0x1eef20 [] junk (shadow_of cap) _ HV1 HA1 Q1);
      [ lia | reflexivity | exact Q4 | exact Q10 | exact RH1 | exact HInA | exact HCF
      | exact CB1 | exact (proj2 AD1) | apply shadow_of_length; lia
      | exact AUX1 | rewrite Q2, u_small by lia; lia
      | rewrite Q2, u_small by lia; exact STKlo | lia | rewrite Q2, u_small by lia; unfold AFREE_STACK; lia
      | rewrite Q2, u_small by lia; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
      | rewrite Q4; unfold ATP; rewrite u_small by lia; exact ERR | exact (xs_inv _ XS1) | exact (xs_ac _ XS1)
      | apply (ah_chain_nil H HH); rewrite Q8; lia
      | cbn [map]; destruct TRC as (_ & _ & _ & T4 & _); exact T4 |].
    rewrite Q2, !u_small by lia.
    intros regs2 mem2 msF2 mo2 s2 HV2 HA2 MP2 KEPT2 INV2 STK2 ERR2 AUX2 HP2 RH2 AC2 HAL2.
    pose proof (xstat_apres _ _ _ _ XS1 HP2 INV2 STK2 AC2 AUX2 HB') as XS2. pose proof (ostate_apres _ _ _ _ OS1 HP2) as OS2.
    pose proof (atxc_apres ax2 _ _ _ ATX1 HP2) as ATX2. pose proof (none_apres _ _ _ ACLEANUP HP2 ltac:(unfold aimg_client, ACLEANUP; lia) ltac:(unfold ACLEANUP; lia) DGC1) as DGC2.
    assert (PRE2b : ax2 = false -> mem2 (Z_to_bv 64 0xbdd420) = None /\ pending = []).
    { intros E. destruct (PRE2a E) as [B P]. split; [exact (none_apres _ _ _ 0xbdd420 HP2 ltac:(unfold aimg_client; lia) ltac:(lia) B) | exact P]. }
    destruct (abi_any mem2) as [bib BIB]. pose proof (u8_range bib) as BIB8 || pose proof (bv_unsigned_in_range 8 bib) as BIB8.
    assert (S2 : getr regs2 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)) by (rewrite (KEPT2 2%bv ltac:(in_solve)); exact Q2).
    assert (S4 : getr regs2 4 = Z_to_bv 64 0xbe1c90) by (rewrite (KEPT2 4%bv ltac:(in_solve)); exact Q4).
    assert (S8 : getr regs2 8 = status) by (rewrite (KEPT2 8%bv ltac:(in_solve)); exact Q8).
    (* [comment removed for export] *)
    assert (STK2' : stk_ok RSEGS mem2 (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK).
    { eapply astk_stk_ok; [exact (xs_stk _ XS2) | unfold MSTK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold MSTK; lia | lia]. }
    eapply (aseg_X H DL sp0 Hvsp s2 msF2 mo2 regs2 mem2 status _ S2 S4 S8 STK2' (amem_inv_ro_none _ (xs_inv _ XS2)) (xs_relro _ XS2) (xs_frame _ XS2));
      [| exact HV2 | exact HA2].
    intros regs3 msF3 mo3 HV3 HA3 SB3 T2 T4 T10 T1.
    (* [comment removed for export] *)
    assert (EQ3 : m_fs mo3 = m_fs mo /\ m_fds mo3 = m_fds mo).
    { pose proof (mo_tr _ _ _ (mo_sb _ _ SB1) (mo_tr _ _ _ (mo_mp H DL _ _ MP2) (mo_sb _ _ SB3))) as [E1 E2]. split; assumption. }
    destruct EQ3 as [EFS EFDS]. rewrite <- EFS.
    (* [comment removed for export] *)
    apply (drv_lazy H DL s2 msF3 mo3 regs3 _ mem2 _ HV3 HA3). intros Lz Sz Zr OK RS _.
    change (Z_to_bv 64 0x55e55c) with (Z_to_bv 64 AEXIT) in RS.
    destruct OS2 as [[-> ST0] | (k & Hk & STA & ->)].
    - (* [comment removed for export] *)
      pose proof (fun c => cells_ok_In _ _ c ST0) as CI.
      destruct (axH_of ax2 mem2 (Z_to_bv 64 0) XS2 (CI (0x5ede90, 8%nat, 0) ltac:(in_solve)) (CI (0x5ede98, 8%nat, 0) ltac:(in_solve))
                  (CI (0x5edf14, 4%nat, 0xffffffff) ltac:(in_solve)) ATX2 DGC2) as (t & c & we & re & XH).
      eapply rz_conseq; [| apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
      destruct ax2.
      + eapply (as_exit_clean2 Lz Sz Zr regs3 mem2 msF3 mo3 _ status we re (Z_to_bv 64 0) (Z_to_bv 64 0) t c (bv_unsigned bib) XH);
          [ rewrite byte_refold; exact BIB | cbn in BIB8; lia
          | exact (CI (0x5edeb0, 8%nat, 0) ltac:(in_solve)) | exact (CI (0x5edec0, 8%nat, 0) ltac:(in_solve))
          | exact T2 | exact T4 | exact T10 | exact OK | exact RS ].
      + destruct (PRE2b eq_refl) as [B0 _].
        eapply (as_exit_clean1 Lz Sz Zr regs3 mem2 msF3 mo3 _ status we re (Z_to_bv 64 0) (Z_to_bv 64 0) t c XH);
          [ exact (abi_none0 _ B0)
          | exact (CI (0x5edeb0, 8%nat, 0) ltac:(in_solve)) | exact (CI (0x5edec0, 8%nat, 0) ltac:(in_solve))
          | exact T2 | exact T4 | exact T10 | exact OK | exact RS ].
    - destruct STA as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14].
      destruct (axH_of ax2 mem2 (Z_to_bv 64 0) XS2 F2 F3 F12 ATX2 DGC2) as (t & c & we & re & XH).
      destruct k as [|k'].
      + (* [comment removed for export] *)
        cbn [zero_lines]. eapply rz_conseq; [| apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
        destruct ax2.
        * eapply (as_exit_clean2 Lz Sz Zr regs3 mem2 msF3 mo3 _ status we re (Z_to_bv 64 0) (Z_to_bv 64 0xc027a8) t c (bv_unsigned bib) XH);
            [ rewrite byte_refold; exact BIB | cbn in BIB8; lia
            | cbn [Z.of_nat Z.mul Z.add] in F5; exact F5 | exact F6
            | exact T2 | exact T4 | exact T10 | exact OK | exact RS ].
        * destruct (PRE2b eq_refl) as [B0 _].
          eapply (as_exit_clean1 Lz Sz Zr regs3 mem2 msF3 mo3 _ status we re (Z_to_bv 64 0) (Z_to_bv 64 0xc027a8) t c XH);
            [ exact (abi_none0 _ B0)
            | cbn [Z.of_nat Z.mul Z.add] in F5; exact F5 | exact F6
            | exact T2 | exact T4 | exact T10 | exact OK | exact RS ].
      + (* [comment removed for export] *)
        destruct ax2; [| destruct (PRE2b eq_refl) as [_ P]; pose proof (f_equal (@length byte) P) as PL; rewrite zero_lines_length in PL; cbn in PL; lia].
        unfold W.
        eapply (as_exit_flush2 Lz Sz Zr regs3 mem2 msF3 mo3 _ status we re (Z_to_bv 64 0) t c (0xc027a8 + 2 * Z.of_nat (S k')) (bv_unsigned bib) (zero_lines (S k')) XH);
          [ rewrite byte_refold; exact BIB | cbn in BIB8; lia
          | exact F5 | eapply ax_flush_cells_of; split; eassumption | lia | rewrite zero_lines_length; lia
          | rewrite zero_lines_length; exact F14
          | exact T2 | exact T4 | exact T10
          | rewrite EFDS; exact Hfd1 | exact OK | exact RS ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem refuse_exit : forall mem0 pp fs0 s msF mo regs mem p (A : Z),
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x1eef6c) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    ARfInv H L sp0 pp tid can fs0 mem0 A s p regs mem mo ->
    realizes asegs (mkCfg msF mo) (t_die msg_refused fs0).
  Proof.
    intros mem0 pp fs0 s msF mo regs mem p A HV HA [(R2 & R4 & R8 & R18 & R20) R9 [cap RH] ST EFS Hfd1 Hfd2]. rewrite <- EFS.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SP16. pose proof Elo. pose proof aceil_loX as HCL. acb.
    destruct ST as [INV STK AC RELRO [G1 G2] CELLS OUT [TID Ht] [CAN Hc] RFS REG LIBP [OS1 OS2] [shi [SH0 Hshi]] ABOVE FR AUX].
    pose proof (fun c => cells_ok_In _ _ c OUT) as CO. pose proof (fun c => cells_ok_In _ _ c CELLS) as CE.
    apply (drv_lazy H DL s msF mo regs _ mem _ HV HA). intros Lz Sz Zr OK RS _.
    apply (as_refused Lz Sz Zr regs mem msF mo (Z_to_bv 64 (bv_unsigned sp0 - 128)) can tid (Z_to_bv 64 0) (Z_to_bv 64 0));
      [| | exact R4 | exact OK | exact RS | exact Hfd2].
    - (* [comment removed for export] *) split.
      + exact R2.
      + rewrite u_small by lia. rewrite <- Zminus_mod_idemp_l, SP16. reflexivity.
      + unfold ASP_LO. rewrite u_small by lia. lia.
      + unfold ASP_HI. rewrite u_small by lia. lia.
      + eapply astk_stk_ok; [exact STK | unfold RF_FR; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold RF_FR; lia | lia].
      + exact (amem_inv_ro_none _ INV).
      + exact RELRO.
      + apply rf_cells_of; assumption.
      + exact CAN.
      + exact Hc.
      + intros a Ha. rewrite u_small in Ha by lia.
        apply (stack0_qsh0 mem lo shi (bv_unsigned sp0 - 128) SH0 ltac:(lia) ltac:(lia)). rewrite ASHADOW_BASE_val. lia.
    - (* [comment removed for export] *) split.
      + lia.
      + exact TID.
      + exact G1.
      + exact G2.
      + exact (CO (0x5ede90, 8%nat, 0) ltac:(in_solve)).
      + exact (CO (0x5ede98, 8%nat, 0) ltac:(in_solve)).
      + exact (CO (0x5edeb0, 8%nat, 0) ltac:(in_solve)).
      + exact (CO (0x5edec0, 8%nat, 0) ltac:(in_solve)).
      + apply ax_lit_cells_of; [exact AC | apply xdrv_of_adrv; exact CELLS | exact (CE (0x5edd34, 4%nat, 0xffffffff) ltac:(in_solve)) | exact (CO (0x5edf14, 4%nat, 0xffffffff) ltac:(in_solve)) | apply adgc_cell0; exact OS2].
      + apply ax_atexit_cells_of_pre. exact REG.
      + apply abi_none0. exact OS1.
      + exact (amem_inv_text_none _ INV).
      + intros a n Ha Hn. pose proof (ACONST_imgvis mem AC) as SV.
        change (sh AIMG_LO) with 0x7fffa000 in SV. change (sh AIMG_TOP) with 0x80178800 in SV.
        eapply stk_store_ok; [exact SV | lia | lia | lia].
  Qed.
End Exit.
