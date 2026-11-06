(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contracts.
(* [comment removed for export] *)
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).   (* [comment removed for export] *)
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable SHC : list (Z * Z).      (* [comment removed for export] *)
Variable VSH : list (Z * Z).      (* [comment removed for export] *)
Variable AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.   (* [comment removed for export] *)
Variable KCAP : Z.
Variable FTOPc : Z.   (* [comment removed for export] *)
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable G : gtable.
Variable bcap ccap : Z.          (* [comment removed for export] *)

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition OBL_imgload : Prop := node1_stmt always (node_imgload IT nx0 G).
Definition OBL_opnew : Prop := GPS.node1_stmtN SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ always (node_opnew SEGS nx0 G bcap ccap).
  (* [comment removed for export] *)
Definition OBL_free : Prop := node1_stmt always (node_free SEGS nx0 G).
Definition OBL_opdel : Prop := node1_stmt always (node_opdel SEGS nx0 G).
Definition OBL_opdel_sized : Prop := node1_stmt always (node_opdel_sized SEGS nx0 G).
Definition OBL_memcpy : Prop := node1_stmt always (node_memcpy SEGS A nx0 G).
Definition OBL_memset : Prop := node1_stmt always (node_memset A nx0 G).
Definition OBL_memmove : Prop := node1_stmt always (node_memmove SEGS A nx0 G).
Definition OBL_strlen : Prop := node1_stmt always (node_strlen SEGS nx0 G).
Definition OBL_amemcpy : Prop := node1_stmt always (node_amemcpy SEGS A nx0 G).    (* [comment removed for export] *)
Definition OBL_amemset : Prop := node1_stmt always (node_amemset A nx0 G).
Definition OBL_amemmove : Prop := node1_stmt always (node_amemmove SEGS A nx0 G).
Definition OBL_stkmal : Prop := forall args, node1_stmt always (node_stack_malloc nx0 G args).   (* [comment removed for export] *)
Definition OBL_fakerel : Prop := node1_stmt always (node_fake_release SEGS IT nx0 G).
Definition OBL_blkfact : Prop := forall args, node1_stmt always (node_blkfact G args).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition node2_stmt (node : acs -> option (acs * acs)) : Prop :=
  forall cs csa csb E fx R M model T,
    GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model -> node cs = Some (csa, csb) -> T [] ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E' csa fx' R' M' model' ->
        m_fs model' = m_fs model -> RZ (cfgF SEGS fx' R' (pc csa) M' model') T) ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E' csb fx' R' M' model' ->
        m_fs model' = m_fs model -> RZ (cfgF SEGS fx' R' (pc csb) M' model') T) ->
    RZ (cfgF SEGS fx R (pc cs) M model) T.



Record gcontracts : Prop := GC {
  gc_imgload : OBL_imgload;
  gc_opnew : OBL_opnew;
  gc_free : OBL_free;       gc_blkfact : OBL_blkfact;   gc_opdel : OBL_opdel;     gc_opdel_sized : OBL_opdel_sized;
  gc_memcpy : OBL_memcpy;   gc_memset : OBL_memset;   gc_memmove : OBL_memmove;   gc_strlen : OBL_strlen;
  gc_amemcpy : OBL_amemcpy; gc_amemset : OBL_amemset; gc_amemmove : OBL_amemmove;       (* [comment removed for export] *)
  gc_stkmal : OBL_stkmal;   gc_fakerel : OBL_fakerel                                              (* [comment removed for export] *)
}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma XNg_sound : gcontracts -> GPS.ext_stmt SEGS nx0 (XNg SEGS IT A nx0 G bcap ccap) PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ.
Proof.
  intros GCs id args. unfold XNg.
  destruct GCs as [g0 g20 g11 g13 g21 g22 g1 g2 g3 g4 g5 g6 g7 g50 g51].
  repeat (destruct id as [|id];
    [ first [ assumption
            | apply GPS.node1_stmt_N; assumption
            | apply GPS.node1_stmt_N; exact (g50 args)
            | apply GPS.node1_stmt_N; exact (g13 args)
            | apply GPS.node1_stmt_N; exact (node_divmagic_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ args)
            | apply GPS.node1_stmt_N; exact (node_enumrange_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ args)
            | apply GPS.node1_stmt_N; exact (node_shok_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ args)   (* [comment removed for export] *)
            | (intros cs cs' E fx R M model T _ _ _ Hn; discriminate Hn) ] |]).
  intros cs cs' E fx R M model T _ _ _ Hn. discriminate Hn.
Qed.


(* [comment removed for export] *)
Lemma XBg_sound0 : GPS.ext2_stmt SEGS nx0 (XBg SEGS nx0 G bcap ccap) PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ.
Proof. intros id args cs csa csb E fx R M model T _ Hn. discriminate Hn. Qed.


(* [comment removed for export] *)
Record gcontracts_core : Prop := GCC {
  gcc_imgload : OBL_imgload;
  gcc_free : OBL_free;       gcc_blkfact : OBL_blkfact;   gcc_opdel : OBL_opdel;     gcc_opdel_sized : OBL_opdel_sized;
  gcc_memcpy : OBL_memcpy;   gcc_memset : OBL_memset;   gcc_memmove : OBL_memmove;   gcc_strlen : OBL_strlen;
  gcc_amemcpy : OBL_amemcpy; gcc_amemset : OBL_amemset; gcc_amemmove : OBL_amemmove;
  gcc_stkmal : OBL_stkmal;   gcc_fakerel : OBL_fakerel
}.


(* [comment removed for export] *)
Definition XNg_core (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with 20%nat => None | _ => XNg SEGS IT A nx0 G bcap ccap id args cs end.

Lemma XNg_core_sound : gcontracts_core -> GPS.ext_stmt SEGS nx0 XNg_core PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ.
Proof.
  intros GCs id args. unfold XNg_core, XNg.
  destruct GCs as [g0 g11 g13 g21 g22 g1 g2 g3 g4 g5 g6 g7 g50 g51].
  repeat (destruct id as [|id];
    [ first [ assumption
            | apply GPS.node1_stmt_N; assumption
            | apply GPS.node1_stmt_N; exact (g50 args)
            | apply GPS.node1_stmt_N; exact (g13 args)
            | apply GPS.node1_stmt_N; exact (node_divmagic_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ args)
            | apply GPS.node1_stmt_N; exact (node_enumrange_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ args)
            | apply GPS.node1_stmt_N; exact (node_shok_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ args)   (* [comment removed for export] *)
            | (intros cs cs' E fx R M model T _ _ _ Hn; discriminate Hn) ] |]).
  intros cs cs' E fx R M model T _ _ _ Hn. discriminate Hn.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition callee_saved_regs : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

End Contracts.
