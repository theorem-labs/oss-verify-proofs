(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the driver-law record gains adl_rdr, that the model-preservation relation keeps the channel reader; vcm2, the clean invariant of each of the vDSO pair's two entries, the vvar pages and the text; the run's driver-law record asan_driver_laws_run, whose walks are over the run's segment list asegs ++ tail from the state with that list's read-only backing, whose kernel relation carries vcm2, and which says the pair lies above the image's top with the vvar entry first; the notation arz for such a walk, and the facts that no segment of the binary reaches the image's top or is the vDSO text). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import SReach LazyRestrict LazySR ShapeAlg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require PropExec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Exec MState.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomBase.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require RunTail PairCleanAll.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition ADRV_LIVE : Z := 2^28.
Definition ADRV_CNT  : Z := 2850.

Record asan_driver_laws (H : asr) : Prop := ADL {
  (* [comment removed for export] *)
  adl_sr : forall (Q : config -> Prop) c T,
      as_SR H Q c -> (forall c', Q c' -> ShapeAlg.realizes asegs c' T) -> ShapeAlg.realizes asegs c T;
  (* [comment removed for export] *)
  adl_lazy : forall s, exists L S Zr,
         (forall msF, as_VIS H s msF = restrict L S msF)
      /\ (forall c, as_AKREL H s c -> lzok asegs L S Zr c)
      /\ (forall ms mo ms' mo', as_AKREL H s (mkCfg ms mo) -> lzok asegs L S Zr (mkCfg ms' mo') ->
            m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> as_AKREL H s (mkCfg ms' mo'));
  (* [comment removed for export] *)
  adl_mpres : forall mo mo', as_MPRES H mo mo' -> m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_halted mo' = m_halted mo;
  (* [comment removed for export] *)
  adl_sb : forall mo mo', same_but_materialized mo mo' -> as_MPRES H mo mo';
  (* A write to a channel needs [m_channel_reader mo = true]
     (Both/As/AsDrvIO.v:54), and [adl_mpres] carries no reader fact, so a step model gets the
     launch's reader through this law.  The instance's [as_MPRES] is [SecLazy.nonvm_same],
     which equates [m_proc]; [m_channel_reader] is a projection of [m_proc].  Every
     consumer of this record uses named projections; the only application of [ADL] is
     Both/As/AS_InstLaws1.v [inst_driver_laws], which is plain bullets. *)
  adl_rdr : forall mo mo', as_MPRES H mo mo' -> m_channel_reader mo' = m_channel_reader mo;
  (* [comment removed for export] *)
  adl_live : ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H }.

End HCW.

(** * The run's segment list (LPS 727298f3)

    A run that calls time() reads the vDSO image and jumps into it: the run's segment list is the
    binary's [asegs] followed by the launch's vDSO/vvar pair ([Run.run_segments]), the tail of a
    [RunTail.RunTail] instance.  The main phase is a walk over that list from the configuration
    with that list's read-only backing; [arz c T] is that walk from [c]. *)
Notation arz c T :=
  (ShapeAlg.realizes (asegs ++ RunTail.rt_tail)
     (cwrom c (OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.seg_rom (asegs ++ RunTail.rt_tail))) T)
  (only parsing).

(** No segment of the binary at or above the image's top. *)
Lemma asr_find_none_above : forall (sl : list Segment) (top x : Z),
  (forall s, In s sl -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= top) -> top <= x ->
  find_segment sl x 1 = None.
Proof.
  induction sl as [|s0 rest IH]; intros top x Hb Hx; [reflexivity|].
  pose proof (Hb s0 (in_eq s0 rest)) as H0.
  cbn [find_segment].
  match goal with |- (if ?b then _ else _) = None => destruct b eqn:E end.
  - exfalso. apply andb_true_iff in E. destruct E as [_ E2]. apply Z.leb_le in E2. lia.
  - exact (IH top x (fun s Hs => Hb s (in_cons s0 s rest Hs)) Hx).
Qed.

Lemma asegs_find_none : forall x, AIMG_TOP <= x -> find_segment asegs x 1 = None.
Proof. intros x Hx. exact (asr_find_none_above asegs AIMG_TOP x asegs_below_top Hx). Qed.

(* no segment of the binary is the vDSO text ([RiscvSemantics.vdso_image]) *)
Lemma vdso_image_asegs : vdso_image asegs = None.
Proof. reflexivity. Qed.

(** * The vDSO pair's two entries

    The pair is two reserved entries, the vvar pages [vlo, vb) and the text [vb, vhi).  A single
    window [vlo, vhi) cannot satisfy [MmVdso.mm_vinv], which holds the whole window inside one
    reserved entry, so the invariant is [PairCleanAll.vcm_cfg] once per entry. *)

(* the pair's vvar entry [vlo, vb) and text entry [vb, vhi), each clean and reserved with no map
   meeting it ([PairCleanAll.vcm_cfg] holds the whole of its window inside one reserved entry) *)
Definition vcm2 (vlo vb vhi : Z) (c : config) : Prop :=
  PairCleanAll.vcm_cfg vlo vb c /\ PairCleanAll.vcm_cfg vb vhi c.

(** * The driver laws over the run's list

    The record above with the walk over [asegs ++ tail] from the state with that list's
    read-only backing ([adlr_sr]).  The lazy view stays [lzok asegs] ([adlr_lazy]); its third
    conjunct takes the pair's invariant of the new configuration ([vcm2 vlo vb vhi]: for each of
    the two entries, the overlay holds no byte of it, it is one of the launch's reserved pair, no
    map meets it, the pins are well formed), which a kernel relation carrying the pair's
    invariant needs, and [adlr_vcm] gives that invariant back from the kernel relation.
    [adlr_top] and [adlr_ord]: the pair lies above the binary's image, the vvar entry first, so
    no segment of the binary holds a byte of either entry ([asegs_find_none]). *)
Record asan_driver_laws_run (tail : list Segment) (vlo vb vhi : Z) (H : asr) : Prop := ADLR {
  adlr_sr : forall (Q : config -> Prop) c T,
      as_SR H Q c ->
      (forall c', Q c' ->
         ShapeAlg.realizes (asegs ++ tail)
           (cwrom c' (OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.seg_rom (asegs ++ tail))) T) ->
      ShapeAlg.realizes (asegs ++ tail)
        (cwrom c (OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.seg_rom (asegs ++ tail))) T;
  adlr_lazy : forall s, exists L S Zr,
         (forall msF, as_VIS H s msF = restrict L S msF)
      /\ (forall c, as_AKREL H s c -> lzok asegs L S Zr c)
      /\ (forall ms mo ms' mo', as_AKREL H s (mkCfg ms mo) -> lzok asegs L S Zr (mkCfg ms' mo') ->
            m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo ->
            vcm2 vlo vb vhi (mkCfg ms' mo') -> as_AKREL H s (mkCfg ms' mo'));
  adlr_vcm : forall s c, as_AKREL H s c -> vcm2 vlo vb vhi c;
  adlr_mpres : forall mo mo', as_MPRES H mo mo' -> m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_halted mo' = m_halted mo;
  adlr_sb : forall mo mo', same_but_materialized mo mo' -> as_MPRES H mo mo';
  adlr_rdr : forall mo mo', as_MPRES H mo mo' -> m_channel_reader mo' = m_channel_reader mo;
  adlr_live : ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H;
  adlr_top : AIMG_TOP <= vlo;
  adlr_ord : vlo <= vb }.

