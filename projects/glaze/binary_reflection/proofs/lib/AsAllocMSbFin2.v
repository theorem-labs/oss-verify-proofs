(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSa OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMTopS4.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1.AsAllocM8Lq OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1.AsAllocM8Lr OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocMRunNs OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSa.AsAllocMSecDefs.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
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

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma restrict_mkst_t : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
  restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma store_ok1_defT : forall (m : mem) (a : word), m a <> None -> store_ok ASEGS m a 1%nat = true.
Proof.
  intros m a D. apply store_ok_of_all; [pose proof (u64_range a); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
  intros x Hx. assert (x = a) by (apply bv_eq; cbn in Hx; lia). subst x. (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (m a); [discriminate | exact (False_ind _ (D eq_refl))].
Qed.

Section WithCeil.
Context {RC : run_ceil}.

Section TOPS4.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis NCELL : In (0x1897e1, 1%nat, 1) (bt_consts bt).                       (* [comment removed for export] *)
  Hypothesis HTP : TP = ia_tp asan_addrs.
  (* [comment removed for export] *)
  Hypothesis OOM_NOT_REP : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x1897e0.

  #[local] Abbreviation T := (bt_thread bt).

  (* [comment removed for export] *)
  Lemma errno_wins_ok : as_wins_ok asan_addrs [(ia_errno asan_addrs, ia_errno asan_addrs + 4)].
  Proof using.
    intros a (lo & hi & Hin & Ha). cbn [In] in Hin. destruct Hin as [E | []]. injection E as <- <-.
    unfold ia_errno in Ha. cbn [ia_tp asan_addrs] in Ha.
    split; [(lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end); lia|].
    split; [| split].
    - intros (lo' & hi' & Hin & Hr). cbn [ia_priv asan_addrs In] in Hin.
      repeat (destruct Hin as [E | Hin]; [injection E as <- <-; lia|]). destruct Hin.
    - (lazymatch goal with |- ?G => let G' := eval unfold in_rtc in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ia_rtc_sb ia_rtc_uar asan_addrs] in G in change_no_check G' end). lia.
    - intros (lo' & hi' & Hin & Hr). cbn [ia_const asan_addrs In] in Hin.
      repeat (destruct Hin as [E | Hin]; [injection E as <- <-; lia|]). destruct Hin.
  Qed.

  Definition sec_null_stmt (HPf : option Z -> ast -> Prop) : Prop :=
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z) (st : ast) (c' : config),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> HPf (Some n) st -> BackingAlgebra.model_ivs_wf mdl ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A ->
      U (getr R 10) = n -> 64512 < n <= NMAX -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      at_sec_null bt fx R M mdl Lc FF n st c' ->
      katD ASEGS c' (malloc_null ASEGS FXOK asan_addrs (fun h0 => AAINVP (HPf h0) bt) MSTK_A R M mdl Lc FF B C K ret n sp).

  Theorem sec_null : forall HPf, sec_null_stmt HPf.
  Proof using OOM_NOT_REP NCELL CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros HPf h fx R M mdl Lc FF B C K ret n sp st c' HLT HFX W RP BD HPN MW CP HR10 Hn FPC HB HC HK AR.
    destruct AR as (rq & Mq & mdlq & AR). cbv zeta in AR.
    destruct AR as (Ec & HLq & MWq & RPq & Q10 & SF & ACC0 & SEVq & LKq).
    destruct SF as (x18 & x19 & sz & bsz & SF). cbv zeta in SF.
    destruct SF as (PRL & Q21 & Q4 & Q3 & Q26 & Q27 & FA & FI & FS4 & FS8 & Lsz & SZ1 & FTR & FC & FLA & STKq).
    pose proof W as Wq.
    assert (Hn34 : 64513 <= n <= 2 ^ 34) by (destruct BD as ((BP & BP2) & _); unfold GBUDGET, MBLK in HB; lia).
    subst c'.
    pose proof ceil_rng as CR.
    set (S := getr R 2) in *. set (tp := getr R 4) in *.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S in CP2. fold tp in CP4.
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & _).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & _). unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt.
    pose proof (thread_dyn bt st Lc FF Wq) as (GT0 & GTC & GTI & GTB & TPG & _).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    pose proof RPq as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi asan_addrs] in GTI.
    pose proof (u64_range S) as HSr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG in *.
    assert (GTS : TSIDE T) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); exact (conj GTI GTB)). hidehyp GTB.
    assert (Etp : tp = Z_to_bv 64 (ia_tp asan_addrs)) by exact CP4.
    assert (Utp : U tp = ia_tp asan_addrs) by (rewrite Etp; reflexivity).
    (* [comment removed for export] *)
    set (Hd := HID st mdlq).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdlq z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). lia. }
    destruct R14 as (Bw1 & Bw2 & _).
    set (Mr := mrestrict Hd Mq).
    Ltac hoff NH := apply hid_off_of; intros z Hz; split; [lia | apply NH; lia].
    Ltac konst Hd M R1 NHs C := apply (cellZ_restrict Hd M _ _ _ (const_cell bt M _ _ _ R1 C)); [lia | lia | hoff NHs].
    assert (K_mcs : rdn ASEGS Mr (Z_to_bv 64 0x10827c) 4 = Some (LE4 30)) by konst Hd Mq R1 NHs CELL_mcs.
    assert (K_gcf : rdn ASEGS Mr (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8))) by konst Hd Mq R1 NHs CELL_gcf.
    assert (K_fum : rdn ASEGS Mr (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1]) by konst Hd Mq R1 NHs CELL_fum.
    assert (K_inited : rdn ASEGS Mr (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1]) by konst Hd Mq R1 NHs CELL_inited.
    assert (K_mrn : rdn ASEGS Mr (Z_to_bv 64 0x1897e1) 1 = Some [Z_to_bv 8 1]) by konst Hd Mq R1 NHs NCELL.
    assert (STKr : forall x : word, U S - 3584 <= U x < U S -> Mr x = Mq x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [pose proof (u64_range x); lia|]. left. rewrite CP2 in Hx. lia. }
    assert (RDr : forall (k : Z) (w : nat) (bs : list byte), -3584 <= k -> k + Z.of_nat w <= 0 -> rdn ASEGS Mq (at_ S k) w = Some bs -> rdn ASEGS Mr (at_ S k) w = Some bs).
    { intros k w bs K1 K2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply STKr. lia. }
    assert (SOKstk : store_ok ASEGS Mr (at_ S (-3584)) 3584 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply (proj2 (STKq x ltac:(lia))). }
    assert (SOKoom : store_ok ASEGS Mr (Z_to_bv 64 0x1897e0) 1 = true) by (apply store_ok_wseg; vm_cast_no_check (eq_refl true)).
    assert (SOKerr : store_ok ASEGS Mr (at_ tp (-164)) 4 = true).
    { rewrite Etp. replace (at_ (Z_to_bv 64 (ia_tp asan_addrs)) (-164)) with (Z_to_bv 64 (ia_errno asan_addrs) : word) by (apply bv_eq; reflexivity).
      apply store_ok_wseg. vm_cast_no_check (eq_refl true). }
    assert (FCr : forall (o : Z) (v : word),
              In (o, v) [(-8, at_ ARB 0x4bdc4); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048)]%Z ->
              rdn ASEGS Mr (at_ (at_ S (-2272)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -48 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. apply FC.
      replace (at_ ARB 0x4bdc4) with (Z_to_bv 64 0x4bdc4 : word) in Hin by (symmetry; apply ARB_litNs; lia). exact Hin. }
    assert (FLr : forall (o : Z) (v : word),
              In (o, v) [(-8, Z_to_bv 64 0x50324); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048);
                         (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x103f18); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)]%Z ->
              rdn ASEGS Mr (at_ (at_ S (-2320)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -88 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FLA o v Hin). }
    assert (FAr : forall (k : Z) (v : word), In (k, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
              rdn ASEGS Mr (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hin. pose proof (ma_slotsA_range S n x18 x19 _ _ _ _ _ _ k v Hin) as [Hk1 Hk2]. apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FA k v Hin)]. }
    assert (FIr : forall (k : Z) (v : word),
              In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
              rdn ASEGS Mr (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hin.
      assert (Hk : -56 <= k /\ k + 8 <= 0) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FI k v Hin)]. }
    assert (RETR : ret_ok (getr R 1)) by (rewrite CP1; apply ret_ok_lit; [lia | exact CPe]).
    (* [comment removed for export] *)
    destruct (run_mS_null Mr (seg_rom ASEGS) rq R S tp T n x18 x19 PRL Q4 Q3 Q10 RETR)
      as (r3 & RUN & X10 & X1 & X2 & X3 & X4 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27).
    all: try assumption.
    all: try (rewrite ?CP2; split; [split; [exact GT4 | exact GTS] | lia]).
    all: try (rewrite ?CP2, ?Utp; (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp asan_addrs] in G in change_no_check G' end); lia).
    all: try (rewrite ?CP2, ?Utp; (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp asan_addrs] in G in change_no_check G' end); repeat split; lia).
    all: let k := numgoals in guard k = 1.
    (* [comment removed for export] *)
    set (MC := mn_mem Mr S tp) in RUN.
    apply (katD_msteps_acct ASEGS Hd (HID_off_segments bt st Lc FF Mq mdlq BT_ia RPq) asanF_segs_wx (a_aa st)
             (@mkst fx rq (Z_to_bv 64 0x50610) Mq (seg_rom ASEGS)) (@mkst fx r3 (getr R 1) MC (seg_rom ASEGS)) mdlq).
    { apply lazy_cover_HID. }
    { exact Bw1. }
    { exact Bw2. }
    { exact HLq. }
    { rewrite restrict_mkst_t. exact RUN. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx rq (Z_to_bv 64 0x50610) Mq (seg_rom ASEGS))) with Mq by reflexivity.
    set (MDin := munrestrict Hd Mq MC).
    apply katD_refl.
    (* [comment removed for export] *)
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0) by (rewrite CP2; lia).
    assert (Gtpm : AIMGLO + 164 <= U tp /\ U tp <= AIMGHI) by (rewrite Utp; (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp asan_addrs] in G in change_no_check G' end); lia).
    assert (GRin : mem_grows Mq MDin).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MDin, munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:Ex; [exact Hx|]. apply (mn_mem_grows Mr S tp). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off by exact Ex. exact Hx. }
    assert (DIFF : forall a : word, MDin a <> Mq a ->
              U a = 0x1897e0 \/ (U S - 2152 <= U a < U S - 2144) \/ (ia_errno asan_addrs <= U a < ia_errno asan_addrs + 4)).
    { intros a NE. unfold MDin, munrestrict in NE. destruct (Hd a) eqn:Eh; [exfalso; exact (NE eq_refl)|].
      assert (EMr : Mr a = Mq a) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); apply mrestrict_off; exact Eh).
      destruct (Z.eq_dec (U a) 0x1897e0) as [E|N1]; [left; exact E|].
      destruct (Z_lt_le_dec (U a) (U S - 2152)) as [L1|L1]; [| destruct (Z_lt_le_dec (U a) (U S - 2144)) as [L2|L2]; [right; left; lia|]].
      all: destruct (Z_lt_le_dec (U a) (U tp - 164)) as [L3|L3]; [| destruct (Z_lt_le_dec (U a) (U tp - 160)) as [L4|L4]; [right; right; (lazymatch goal with |- ?G => let G' := eval unfold ia_errno in G in change_no_check G' end); rewrite <- Utp; lia|]].
      all: exfalso; apply NE; rewrite <- EMr; apply (mn_mem_outside Mr S tp GSm Gtpm); lia. }
    assert (DEF : forall a : word, MDin a <> Mq a -> MDin a <> None).
    { intros a NE. destruct (MDin a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (Mq a) eqn:E2; [|reflexivity].
      exfalso. assert (X : Mq a <> None) by (rewrite E2; discriminate). apply GRin in X. rewrite E1 in X. exact (X eq_refl). }
    (* [comment removed for export] *)
    assert (RPf : Rep bt st Lc FF MDin mdl1).
    { apply (Rep_frame bt st Lc FF Mq MDin mdl1 Wq (Rep_sbm bt st Lc FF Mq mdlq mdl1 RPq MI1 SBM1)).
      intros a NE. split; [| exact (DEF a NE)]. intros RCa.
      destruct (DIFF a NE) as [E | [E | E]].
      - rewrite E in RCa. exact (OOM_NOT_REP st Lc FF Wq RCa).
      - pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U a) Wq RCa). rewrite CP2 in E. lia.
      - refine (win_vs_rep bt st Lc FF Wq [(ia_errno asan_addrs, ia_errno asan_addrs + 4)] (U a) _ _ RCa).
        + rewrite BT_ia. exact errno_wins_ok.
        + exists (ia_errno asan_addrs), (ia_errno asan_addrs + 4). split; [left; reflexivity | exact E]. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold malloc_null in G in change_no_check G' end). exists fx, r3, MDin, mdl1.
    split; [(lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end); rewrite CP1; reflexivity|]. split; [exact HFX|].
    split.
    { (* [comment removed for export] *)
      intros r Hr. unfold as_callee_saved in Hr. cbn [In] in Hr.
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 2) with (2%bv : reg) by (apply bv_eq; reflexivity); rewrite X2; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 3) with (3%bv : reg) by (apply bv_eq; reflexivity); rewrite X3; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 4) with (4%bv : reg) by (apply bv_eq; reflexivity); rewrite X4; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 8) with (8%bv : reg) by (apply bv_eq; reflexivity); rewrite X8; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 9) with (9%bv : reg) by (apply bv_eq; reflexivity); rewrite X9; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 18) with (18%bv : reg) by (apply bv_eq; reflexivity); rewrite X18; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 19) with (19%bv : reg) by (apply bv_eq; reflexivity); rewrite X19; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 20) with (20%bv : reg) by (apply bv_eq; reflexivity); rewrite X20; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 21) with (21%bv : reg) by (apply bv_eq; reflexivity); rewrite X21; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 22) with (22%bv : reg) by (apply bv_eq; reflexivity); rewrite X22; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 23) with (23%bv : reg) by (apply bv_eq; reflexivity); rewrite X23; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 24) with (24%bv : reg) by (apply bv_eq; reflexivity); rewrite X24; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 25) with (25%bv : reg) by (apply bv_eq; reflexivity); rewrite X25; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 26) with (26%bv : reg) by (apply bv_eq; reflexivity); rewrite X26; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 27) with (27%bv : reg) by (apply bv_eq; reflexivity); rewrite X27; reflexivity|].
      destruct Hr. }
    split; [exact X10|].
    split.
    { (* [comment removed for export] *) intros a NE. (lazymatch goal with |- ?G => let G' := eval unfold as_changed in G in change_no_check G' end). rewrite ?BT_ia.
      destruct (decide (MDin a = Mq a)) as [E | N].
      - rewrite E in NE. pose proof (ACC0 a NE) as F. left. rewrite <- CP2. fold S. (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end). lia.
      - destruct (DIFF a N) as [E | [E | E]].
        + right; right; left. exists 0x10825a, 0x1990a8. split; [(lazymatch goal with |- ?G => let G' := eval cbn [ia_priv asan_addrs In] in G in change_no_check G' end); tauto | lia].
        + left. rewrite <- CP2. fold S. (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end). lia.
        + right; right; right. exact E. }
    split.
    { (* [comment removed for export] *) intros a Ha Dm. unfold in_errno, ia_errno in Ha. cbn [ia_tp asan_addrs] in Ha.
      (lazymatch goal with |- ?G => let G' := eval unfold MDin in G in change_no_check G' end). rewrite munrestrict_off by (rewrite <- (Z_to_bv_bv_unsigned 64 a); apply NHs; [pose proof (u64_range a); lia | right; lia]).
      apply (mn_mem_errno Mr S tp Gtpm). rewrite Utp. (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp asan_addrs] in G in change_no_check G' end). lia. }
    split.
    { (* [comment removed for export] *) intros a Ha. assert (D : MDin a <> None) by (apply GRin; apply (proj1 (STKq a ltac:((lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end); rewrite CP2; exact Ha)))).
      split; [exact D | exact (store_ok1_defT MDin a D)]. }
    split.
    { (* [comment removed for export] *)
      exists st. split; [exact Wq|]. split; [exact RPf|]. split; [| exact (model_ivs_wf_sbm mdlq mdl1 SBM1 MWq)].
      split; [exact BD | exact HPN]. }
    split; [eapply same_except_vm_trans; [exact SEVq | apply same_but_materialized_except_vm; exact SBM1]|].
    split; [| exact (halted_sbm mdlq mdl1 SBM1 HLq)].
    intros a Ha. pose proof (lazy_kept_sbm bt Lc FF mdlq mdl1 SBM1 a) as L1. rewrite ?BT_ia in L1. rewrite (L1 Ha). pose proof (LKq a) as L2. rewrite ?BT_ia in L2. exact (L2 Ha).
  Qed.
End TOPS4.
End WithCeil.
End AsAllocMTopS4.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMSbAsm.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP4.AsAllocMTopP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSa.AsAllocMSecK OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSa.AsAllocMSecDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSa AsAllocMTopS4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbTop.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.

Section WithCeil.
Context {RC : run_ceil}.

Section ASM.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis SCELLS : sec_cells bt.
  Hypothesis NCELL : In (0x1897e1, 1%nat, 1) (bt_consts bt).                 (* [comment removed for export] *)
  Hypothesis OOM_NOT_REP : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x1897e0.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis BOOTG : boot_geom bt.
  Hypothesis BOK : boot_ok bt.
  Hypothesis BTOT : boot_totals bt.
  Hypothesis HTP : TP = ia_tp asan_addrs.

  (* [comment removed for export] *)
  Definition sec_granted_stmt : Prop :=
    forall fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp n : Z) (st : ast) (h : option Z) (c' : config) (Qok : config -> Prop),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> holes_le h st -> hole_ok h n ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A -> U (getr R 10) = n -> 64512 < n <= NMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      at_sec_grant bt fx R M mdl Lc FF n st c' ->
      (forall c'', runS_post bt FXOK st Lc FF R M mdl n c'' -> katD ASEGS c'' Qok) ->
      katD ASEGS c' Qok.
  Hypothesis SEC_GRANTED : sec_granted_stmt.

  (* [comment removed for export] *)
  Theorem malloc_sec_gen : forall (HPf : option Z -> ast -> Prop)
      (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z) (st : ast),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> HPf h st -> BackingAlgebra.model_ivs_wf mdl -> hole_ok h n ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A ->
      U (getr R 10) = n -> 64512 < n <= NMAX -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      holes_le h st ->                                                           (* [comment removed for export] *)
      HPf (Some n) st ->                                                         (* [comment removed for export] *)
      (forall st', (forall c, a_reg st' c = a_reg st c /\ a_cache st' c = a_cache st c) ->
                   a_kact st' = a_kact st + kcost_malloc n -> HPf None st') ->   (* [comment removed for export] *)
      katsD ASEGS (cfg ASEGS fx R (ia_malloc asan_addrs) M mdl)
            (malloc_ok ASEGS FXOK asan_addrs (fun h0 => AAINVP (HPf h0) bt) MSTK_A R M mdl Lc FF B C K ret n sp)
            (malloc_null ASEGS FXOK asan_addrs (fun h0 => AAINVP (HPf h0) bt) MSTK_A R M mdl Lc FF B C K ret n sp).
  Proof using SEC_GRANTED HTP BTOT BOK BOOTG GEOM OOM_NOT_REP NCELL SCELLS PCELLS CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros HPf h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HP MW HO CP HR10 Hn FPC HB HC HK HLE HPN HCL.
    apply (malloc_sec_to_mmap bt FXOK TP TSDP PGP FL MIDEND BT_segs BT_ia CELLS PCELLS SCELLS GEOM BOOTG BOK BTOT HTP
             fx R M mdl Lc FF B C K ret sp n st h _ _ HFX HLT MW W RP BD HLE HO CP HR10 Hn FPC HB HC HK).
    - (* [comment removed for export] *)
      intros c' AG. apply katwD_of_katD.
      apply (SEC_GRANTED fx R M mdl Lc FF B C K ret sp n st h c' _ HFX HLT MW W RP BD HLE HO CP HR10 Hn HB HC HK AG).
      intros c'' RPOST.
      exact (malloc_partBs bt FXOK TP TSDP PGP FL MIDEND BT_segs BT_ia CELLS (proj1 SCELLS) HTP HPf
               h fx R M mdl Lc FF B C K ret n sp st c'' HLT HFX W BD HP HO CP HR10 Hn FPC HB HC HK HCL RPOST).
    - (* [comment removed for export] *)
      intros c' AN.
      exact (sec_null bt FXOK TP TSDP PGP FL MIDEND BT_segs BT_ia CELLS NCELL OOM_NOT_REP HPf
               h fx R M mdl Lc FF B C K ret n sp st c' HLT HFX W RP BD HPN MW CP HR10 Hn FPC HB HC HK AN).
  Qed.

  (* [comment removed for export] *)
  Lemma sec_holes_ls : forall h n st, holes_le h st -> hole_ok h n -> 64512 < n -> holes_ls n st.
  Proof using.
    intros h n st HL HO Hn c F. exfalso. destruct (sec_flags_clear h n st HL HO Hn c) as [F1 F2].
    destruct F as [F | F]; [rewrite F1 in F | rewrite F2 in F]; discriminate F.
  Qed.

  (* [comment removed for export] *)
  Theorem malloc_sec_S : MCASE_S bt FXOK (ia_malloc asan_addrs) P_sec.
  Proof using SEC_GRANTED HTP BTOT BOK BOOTG GEOM OOM_NOT_REP NCELL SCELLS PCELLS CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn FPC HB HC HK HP. unfold P_sec in HP.
    pose proof (holes_lsopt_le h st HL) as HLE.
    exact (malloc_sec_gen holes_lsopt h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 (conj HP (proj2 Hn)) FPC HB HC HK HLE
             (sec_holes_ls h n st HLE HO HP)
             (fun st' E _ => sec_holes_none h n st st' HLE HO HP (fun c => proj1 (E c)))).
  Qed.

  (* [comment removed for export] *)
  Theorem malloc_sec_DR : MALLOC_ALT_SEC ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_malloc asan_addrs) true.
  Proof using SEC_GRANTED HTP BTOT BOK BOOTG GEOM OOM_NOT_REP NCELL SCELLS PCELLS CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros fx R M mdl Lc FF B C K ret n sp PRE Hbig.
    destruct PRE as (HLT & HFX & AI & HO & CP & HR10 & Hn & FPC & HB & HC & HK).
    destruct AI as (st & W & RP & (BD & HP) & MW).
    pose proof HP as (HL & DH). pose proof (holes_lsopt_le None st HL) as HLE.
    assert (K0 : 0 <= a_kact st) by (destruct BD as (_ & _ & BK); exact (proj1 BK)).
    exact (malloc_sec_gen (HP_q drv_hist) None fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HP MW HO CP HR10 (conj Hbig (proj2 Hn)) (FPC eq_refl) HB HC HK HLE
             (sec_holes_ls None n st HLE HO Hbig)
             (fun st' E EK => conj (sec_holes_none None n st st' HLE HO Hbig (fun c => proj1 (E c)))
                                   (drv_hist_malloc_sec st st' n DH Hbig K0 E ltac:(rewrite EK; apply Z.le_refl)))).
  Qed.
End ASM.
End WithCeil.
End AsAllocMSbAsm.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsGrowDie.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMSbFin.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvDepotObl3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP4.AsAllocMTopP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSa OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b.AsDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop6.AsDepotGrantEx OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsGrowDie AsAllocMSbAsm.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Theorem hyp_depot9_closed : forall {RC : run_ceil} (bt : as_boot) (FXOK : FPState -> Prop),
  boot_facts bt -> boot_totals bt -> bt_segs bt = ASEGS -> bt_ia bt = asan_addrs -> depot_cells bt -> depot_cells2 bt ->
  forall KD, 576 <= KD -> AsDepotTop3.AsDepotHyp9.HYP_DEPOT9_stmt bt FXOK KD.
Proof.
  intros RC bt FXOK BF BTOT BT_segs BT_ia DC DC2 KD HKD.
  pose proof (boot_facts_ok bt BF) as BOK. pose proof (boot_facts_geom bt BF) as BG.
  destruct (dep0_bounds bt BOK) as [DEP0 [_ DFR0]].
  apply (hyp_depot9_pf bt FXOK BT_segs BT_ia DC DC2 (depot_obls_pf bt)).
  - intros st Lc FF W ROOM KC. exact (depot_frames_room bt st Lc FF W ROOM KC DFR0).
  - exact DEP0.
  - exact BG.
  - exact (grant_ex_pf bt BOK BTOT).
  - exact (grant_nr_ex_pf bt BOK BTOT).
  - exact HKD.
Qed.

Section FinAt.
  Context {RC : run_ceil}.
  Variable hv : bvars.
  #[local] Abbreviation bt := (asan_bt hv).
  #[local] Abbreviation FXOK := AzSymStepR.fx_ok.
  Hypothesis BF : boot_facts bt.
  Hypothesis BTOT : boot_totals bt.

  Ltac in_consts_old := rewrite asan_bt_consts; (lazymatch goal with |- ?G => let G' := eval unfold asan_consts in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end); repeat (first [left; reflexivity | right]).
  (* [comment removed for export] *)
  Ltac in_consts_nat i := lazymatch i with O => idtac | S ?j => in_consts_nat j end.
  Ltac in_consts_fast :=
    let G := match goal with |- ?G => eval cbv beta in G end in
    lazymatch G with In (?a, ?n, ?v) ?L =>
      let i := eval lazy in ((fix f (l : list (Z * nat * Z)) : nat := match l with [] => O | (a', n', _) :: l' =>
                                if (Z.eqb a a' && Nat.eqb n n')%bool then O else S (f l') end) L) in
      in_consts_nat i; exact (nth_error_In L i eq_refl)
    end.
  Ltac in_consts := first [in_consts_fast | in_consts_old].
  #[local] Abbreviation TP := (ia_tp asan_addrs).

  (* [comment removed for export] *)
  Lemma MCELLS_s : malloc_cells bt TP 0x65bae8 0x197020 0x104d78 0.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold malloc_cells in G in change_no_check G' end). repeat (split; [in_consts|]). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. Qed.
  Lemma PCELLS_s : pop_cells bt.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold pop_cells in G in change_no_check G' end). repeat (split; [in_consts|]). in_consts. Qed.
  Lemma SCELLS_s : sec_cells bt.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold sec_cells in G in change_no_check G' end). repeat (split; [in_consts|]). in_consts. Qed.
  Lemma DCELLS_s : depot_cells bt /\ depot_cells2 bt.
  Proof using. exact (depot_cells_asan bt _ _ _ _ (asan_bt_consts hv)). Qed.
  Lemma OOM_s : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x1897e0.
  Proof using. intros st Lc FF W. exact (oom_not_rep_A hv st Lc FF _ _ W). Qed.
  Lemma GEOM_s : free_boot_geom bt.  Proof using BF RC. exact (boot_facts_stack bt BF). Qed.
  Lemma BOOTG_s : boot_geom bt.  Proof using BF RC. exact (boot_facts_geom bt BF). Qed.
  Lemma HYP_DEPOT9_s : AsDepotTop3.AsDepotHyp9.HYP_DEPOT9_stmt bt FXOK 1312.
  Proof using BTOT BF. apply (hyp_depot9_closed bt FXOK BF BTOT eq_refl eq_refl (proj1 DCELLS_s) (proj2 DCELLS_s) 1312). lia. Qed.

  (* [comment removed for export] *)
  Lemma GROW_DIE_s :
    forall (fx : FPState) (regs : bvmap 5 word) (M rom : word -> option byte) (sp addr v44 : word),
      FXOK fx -> getr regs 2 = sp -> getr regs 18 = addr ->
      2 ^ 32 + 4096 <= U sp <= 2 ^ 47 - 16 -> U sp mod 16 = 0 -> 4096 <= U addr < 2 ^ 47 ->
      store_ok ASEGS M (at_ sp (-1072)) 1168 = true -> rdn ASEGS M (at_ sp 44) 4 = Some (word_to_le_bytes 4 v44) ->
      rdn ASEGS M (Z_to_bv 64 0x1e23c) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x612079726f6d656d)) ->
      rdn ASEGS M (Z_to_bv 64 0x1e244) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7365726464612074)) ->
      rdn ASEGS M (Z_to_bv 64 0x1e24c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x70252073)) ->
      rdn ASEGS M (Z_to_bv 64 0x1e250) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->
      rdn ASEGS M (Z_to_bv 64 0x22760) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x60940)) ->
      rdn ASEGS M (Z_to_bv 64 0x104b0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xaaaaaaaaaaaaaaaa)) ->
      rdn ASEGS M (Z_to_bv 64 0xff2b0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
      rdn ASEGS M (Z_to_bv 64 0x19909c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
      exists fx' r M', msteps ASEGS (@mkst fx regs (0x82578%bv : word) M rom) (@mkst fx' r (0x7bfb4%bv : word) M' rom).
  Proof using. exact GD.grow_die_w. Qed.

  (* [comment removed for export] *)
  Hypothesis SEC_GRANTED_at : sec_granted_stmt bt FXOK.

  Theorem H_SEC_S_at : MCASE_S bt FXOK (ia_malloc asan_addrs) P_sec.
  Proof using SEC_GRANTED_at BTOT BF.
    exact (malloc_sec_S bt FXOK TP 0x65bae8 0x197020 0x104d78 0 eq_refl eq_refl MCELLS_s PCELLS_s SCELLS_s (may_return_null_row_A hv) OOM_s
             GEOM_s BOOTG_s (boot_facts_ok bt BF) BTOT eq_refl SEC_GRANTED_at).
  Qed.
  Theorem H_SEC_DR_at : MALLOC_ALT_SEC ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_malloc asan_addrs) true.
  Proof using SEC_GRANTED_at BTOT BF.
    exact (malloc_sec_DR bt FXOK TP 0x65bae8 0x197020 0x104d78 0 eq_refl eq_refl MCELLS_s PCELLS_s SCELLS_s (may_return_null_row_A hv) OOM_s
             GEOM_s BOOTG_s (boot_facts_ok bt BF) BTOT eq_refl SEC_GRANTED_at).
  Qed.
End FinAt.
End AsAllocMSbFin.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvDepotObl3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSg. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP4.AsAllocMTopP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSg AsAllocMSbAsm AsAllocMSbFin.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section Fin2.
  Context {RC : run_ceil}.
  Variable hv : bvars.
  Hypothesis BF : boot_facts (asan_bt hv).
  Hypothesis BTOT : boot_totals (asan_bt hv).

  Theorem SEC_GRANTED_at : sec_granted_stmt (asan_bt hv) AzSymStepR.fx_ok.
  Proof using BTOT BF.
    exact (sec_granted (asan_bt hv) AzSymStepR.fx_ok (ia_tp asan_addrs) 0x65bae8 0x197020 0x104d78 0 1312 eq_refl eq_refl
             (MCELLS_s hv) (PCELLS_s hv) (SCELLS_s hv) BF eq_refl ltac:(lia) ltac:(right; lia) (HYP_DEPOT9_s hv BF BTOT) (GROW_DIE_s)).
  Qed.

  Theorem H_SEC_S : MCASE_S (asan_bt hv) AzSymStepR.fx_ok (ia_malloc asan_addrs) P_sec.
  Proof using BTOT BF. exact (H_SEC_S_at hv BF BTOT SEC_GRANTED_at). Qed.

  Theorem H_SEC_DR : MALLOC_ALT_SEC ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX (asan_bt hv)) MSTK_A (ia_malloc asan_addrs) true.
  Proof using BTOT BF. exact (H_SEC_DR_at hv BF BTOT SEC_GRANTED_at). Qed.
End Fin2.
