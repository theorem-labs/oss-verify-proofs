(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence FinInput.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgUbs ItabUbs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs DefsE DefsW.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Import Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GLib PkOps ClientX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import UnpInst TdInst PkInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import G0 G1 G2 G2B G2Z G3 G3P G4 G6 GRoom GCap GNz GShr GCur GBnd GSplit VDestroy GName GVEnd GInv GPerm PkInv PkBody PkCap PkEnter PkExit PkFld PkPeek PkStack PkRegrow Td TdEnter.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import LdPart.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import LdPartSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require PkBodyCtr MemcpyG.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U Require T_Ubs2U.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require T_Ubs2UE.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Ubs_u_1 Ubs_u_2 Ubs_u_3 Ubs_u_4 Ubs_u_5 Ubs_u_6 Ubs_u_7 Ubs_u_8 Ubs_u_9 Ubs_u_10 Ubs_u_11 Ubs_u_12 Ubs_u_13 Ubs_u_14 Ubs_u_15 Ubs_u_16.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Ops.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Ceiling.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require StateGlue.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require AW HeapCtr HeapCtrB MemcpyCtr MemcpyWCtr StrCtr RstageCtr AWInit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require NodesM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2F Require T_Ubs2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2A Require T_Ubs2A.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2D Require T_Ubs2D.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2T Require T_Ubs2T.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.UbsNU Require T_UbsNU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2L Require T_Ubs2L.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2E Require T_Ubs2E.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StackInit Nodes CertSound OblsLib Ops SysSpec CtrSys DrvShape DrvRoot DrvLib DrvTop LibLib RunCeil RunUbs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Ubs_r8 Ubs_r9.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Glue.Ops.Ops CtrS DrvShape DrvRoot DrvLib LibLib.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module RX := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.RunUbs.RunUbs.
Module L8 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun.Ubs_r8.LibRunUbs_r8.
Module L9 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun.Ubs_r9.LibRunUbs_r9.
Module LU := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun.Ubs_u_16.LibRunUbs_u_16.

Module TopHypsUbs.

Definition CANARY : sv := RunCeil.CANARY.
Definition MALLOC_PC : int := 300740%uint63.
Definition FREE_PC : int := 300420%uint63.
Definition RSI : int := 360729%uint63.

Section RUN.

Variable inp : ProcInput.
Variables (sp brk0 mb : word) (rnd : EntryDraw) (lim : Z).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hhw : valid_hwcap (in_hwcap inp).
Hypothesis Hsz : in_va_size inp = Sv48.
Hypothesis Hen : valid_entry (mkImage SEGS PC PH) (mkEntry sp brk0 mb rnd) inp.
Hypothesis Hlim : 2 ^ 31 <= lim.

Definition CLG : Ceiling.ceiling := RunCeil.CLG sp rnd.
Lemma Hvsp : valid_sp sp.
Proof. pose proof (proj1 (valid_entry_sv48 _ _ _ Hsz) Hen) as (H & _ & _ & _). exact H. Qed.
Lemma ceil_le : @Ceiling.alloc_ceiling CLG <= bv_unsigned sp - DrvTop.WOFF.
Proof. exact (RunCeil.ceil_le sp rnd Hvsp). Qed.
Lemma canary_eq : den (RunCeil.Ecan rnd) CANARY = Z_to_bv 64 (@Ceiling.ssp_canary CLG).
Proof. exact (RunCeil.canary_eq sp rnd). Qed.
Lemma secret_eq : forall i, (i < 8)%nat ->
  nth_error (at_random_bytes (ed_random rnd)) (8 + i) = nth_error (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem.le8 (Z_to_bv 64 (@Ceiling.ctx_secret CLG))) i.
Proof. exact (RunCeil.secret_eq sp rnd). Qed.

Definition XW : HeapOp.client_world := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.ClientX.CX.XTP SEGS.
Definition Cw : HeapOp.client_world := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Ops.UO.unp_cw SEGS XW.

Lemma CW3 : forall ca LB ws m, HeapOp.cw_holds Cw 3 ca LB ws m -> OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkOps.PK.cw_pk_holds SEGS ca LB ws m.
Proof. intros ca LB ws m H. exact H. Qed.
Lemma CW3i : forall ca LB ws m, OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkOps.PK.cw_pk_holds SEGS ca LB ws m -> HeapOp.cw_holds Cw 3 ca LB ws m.
Proof. intros ca LB ws m H. exact H. Qed.
Lemma cw_init : forall lo m, HeapOp.cw_holds Cw 0 [] [] [HeapOp.Win lo DrvTop.WLEN 0] m.
Proof.
  intros lo m. cbn [Cw HeapOp.cw_holds OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Ops.UO.unp_cw].
  unfold OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Ops.UO.cw_unp_holds. cbn. first [exact I | (constructor; [intros [A _]; exact (A eq_refl)| constructor])].
Qed.

Definition A : HeapOp.alloc_world SEGS RX.XCL := @AW.TwinB.AWI CLG.
Lemma aw_fds : forall aw LB ws m mo fds, HeapOp.aw_holds SEGS RX.XCL A aw LB ws m mo -> HeapOp.aw_holds SEGS RX.XCL A aw LB ws m (with_fds fds mo).
Proof. intros aw LB ws m mo fds [H N]. split; [exact (@AW.TwinB.aw_fds CLG aw LB m mo fds H)| exact N]. Qed.
Lemma aw_init : forall mem tid lo,
  (forall a, RX.AST_LO <= a < RX.AST_HI -> rb SEGS mem a = img_byte SEGS a) ->
  HeapOp.aw_holds SEGS RX.XCL A (Z_to_bv 64 0) [] [HeapOp.Win lo DrvTop.WLEN 0] mem (with_tid tid (RX.model0 inp sp brk0 mb rnd lim)).
Proof.
  intros mem tid lo HI. pose proof (proj1 (valid_entry_sv48 _ _ _ Hsz) Hen) as (_ & Hbrk & _ & _).
  apply (@AWInit.TwinB.aw_init CLG mem brk0 mb sp lim inp tid Hbrk (AWInit.TwinB.ceil_clamp_ok sp Hvsp) Hlim HI).
  intros w [<-|[]]. cbn. unfold HeapOp.K_GHOST. lia.
Qed.

Lemma aw_ceil_fds : forall mo fds, HeapOp.aw_ceiling SEGS RX.XCL A (with_fds fds mo) = HeapOp.aw_ceiling SEGS RX.XCL A mo.
Proof. intros mo fds. reflexivity. Qed.
Lemma aw_ceil0 : forall tid, HeapOp.aw_ceiling SEGS RX.XCL A (with_tid tid (RX.model0 inp sp brk0 mb rnd lim)) <= bv_unsigned sp - DrvTop.WOFF.
Proof. intros tid. exact ceil_le. Qed.

Definition R : drun := RX.R inp sp rnd Hva A Cw aw_fds aw_ceil_fds.
Let MP := RX.MP inp.
Let PB := RX.PB inp sp rnd.

Lemma OPS_holds1 : forall args m mo, op_holds (OPS R) CtrLib.HEAP_ID args m mo = HeapOp.heap_holds SEGS RX.XCL A Cw args m mo.
Proof. intros. reflexivity. Qed.
Lemma OPS_fp1 : forall args, op_fp (OPS R) CtrLib.HEAP_ID args = HeapOp.heap_fp RX.XCL args.
Proof. intros. reflexivity. Qed.

Lemma comp_other : forall id, id <> CtrLib.HEAP_ID ->
  Ops.comp_of (RX.HEAPC A Cw) (FD3 (RX.p1 inp) (RX.file inp)) (RSTAGE (RX.file inp) RX.RS RX.RS_range) FD3DIR FDINIT RX.EXT id =
  (if PrimInt63.eqb id 2%uint63 then FD3 (RX.p1 inp) (RX.file inp)
   else if PrimInt63.eqb id 3%uint63 then RSTAGE (RX.file inp) RX.RS RX.RS_range
   else if PrimInt63.eqb id 4%uint63 then FD3DIR
   else if PrimInt63.eqb id 5%uint63 then FDINIT
   else if PrimInt63.eqb id 7%uint63 then RX.POOLC
   else if PrimInt63.eqb id 6%uint63 then DrvTop.SPLINK else oc_true).
Proof.
  intros id Hid. unfold Ops.comp_of. destruct (PrimInt63.eqb id 1%uint63) eqn:E1.
  - exfalso. apply Hid. apply Uint63.eqb_correct in E1. exact E1.
  - unfold RX.EXT. reflexivity.
Qed.

Lemma OPS_frame_other : forall id args m m' mo, id <> CtrLib.HEAP_ID -> op_holds (OPS R) id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp (OPS R) id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  op_holds (OPS R) id args m' mo.
Proof.
  intros id args m m' mo Hid H AG. unfold OPS, CtrSys.OPS in *. rewrite mk_holds in *. rewrite mk_fp in AG.
  cbn [r_heap r_ext r_p1 r_file r_RS r_RSr R RX.R] in *. rewrite (comp_other id Hid) in *.
  destruct (PrimInt63.eqb id 2%uint63); [exact H|].
  destruct (PrimInt63.eqb id 3%uint63).
  { cbn [RSTAGE oc_holds oc_fp] in *. destruct args as [|off [|n [|]]]; cbn [rstage_holds] in *; try exact H.
    destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi. rewrite <- (H3 i Hi).
    pose proof RX.RS_range as RR. unfold RX.RS, RS_LEN, two64 in *.
    rewrite (AG (360729 + i)); [reflexivity | lia |].
    apply Exists_cons_hd. cbn [fst snd]. unfold RS_LEN. lia. }
  destruct (PrimInt63.eqb id 4%uint63); [exact H|].
  destruct (PrimInt63.eqb id 5%uint63); [exact H|].
  destruct (PrimInt63.eqb id 7%uint63).
  { cbn [RX.POOLC oc_holds oc_fp] in *. destruct args as [|sel [|]]; cbn [Pool.pool_holds] in *; try exact H.
    destruct H as [H|[(s & Hs & Hlt & HF)|(l & Hl & Hlt & HF)]]; [left; exact H| right; left| right; right].
    - exists s. split; [exact Hs|]. split; [exact Hlt|].
      apply Forall_forall. intros e He i Hi. pose proof (proj1 (Forall_forall _ _) HF e He i Hi) as B. rewrite <- B.
      destruct (PoolSnd.tbl_facts RX.FL RX.FL8 RX.FLB s e He) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      unfold rb. rewrite (AG (to_Z (Pool.pe_addr e) + i)); [reflexivity| rewrite RX.FLz in C6; unfold two64; lia|].
      rewrite RX.pool_fp_eq. replace (bv_unsigned sel =? 3) with false by (symmetry; apply Z.eqb_neq; unfold Pool.NSTATES in Hlt; lia).
      replace (bv_unsigned sel <? 3) with true by (symmetry; apply Z.ltb_lt; unfold Pool.NSTATES in Hlt; lia).
      unfold RX.PFP. rewrite RX.FLz in C6. destruct C6 as [C6|C6]; [apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd]; cbn [fst snd]; lia.
    -
      exists l. split; [exact Hl|]. split; [exact Hlt|].
      apply Forall_forall. intros e He i Hi. pose proof (proj1 (Forall_forall _ _) HF e He i Hi) as B. rewrite <- B.
      destruct (PoolSnd.ptbl_facts RX.FL RX.FL8 RX.FLB l e He) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      unfold rb. rewrite (AG (to_Z (Pool.pe_addr e) + i)); [reflexivity| rewrite RX.FLz in C6; unfold two64; lia|].
      rewrite RX.pool_fp_eq. replace (bv_unsigned sel =? 3) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (bv_unsigned sel <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
      unfold RX.PFP_PARK. rewrite RX.FLz in C6.
      destruct C6 as [C6|[C6|C6]]; [apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd]; cbn [fst snd]; lia. }
  destruct (PrimInt63.eqb id 6%uint63); exact H.
Qed.

Lemma OPS_fp_other0 : forall id args a, id <> CtrLib.HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp (OPS R) id args) ->
  RX.RS <= a < RX.RS + 65536 \/ DrvTop.inZ RX.PFP a.
Proof.
  intros id args a Hid X. unfold OPS, CtrSys.OPS in X. rewrite mk_fp in X.
  cbn [r_heap r_ext r_p1 r_file r_RS r_RSr R RX.R] in X. rewrite (comp_other id Hid) in X.
  assert (G : (RX.RS <= a < RX.RS + 65536 \/ DrvTop.inZ RX.PFP a) -> RX.RS <= a < RX.RS + 65536 \/ DrvTop.inZ RX.PFP a) by (intros Y; exact Y).
  destruct (PrimInt63.eqb id 2%uint63); [inversion X|].
  destruct (PrimInt63.eqb id 3%uint63).
  { apply G. left. cbn [RSTAGE oc_fp] in X. unfold rstage_fp in X. apply Exists_cons in X as [X|X]; [cbn [fst snd] in X; unfold RS_LEN, RX.RS in *; lia | exfalso; inversion X]. }
  destruct (PrimInt63.eqb id 4%uint63); [inversion X|].
  destruct (PrimInt63.eqb id 5%uint63); [inversion X|].
  destruct (PrimInt63.eqb id 7%uint63).
  { apply G. right. cbn [RX.POOLC oc_fp] in X. destruct args as [|sel [|x l]]; [inversion X| |inversion X].
    rewrite RX.pool_fp_eq in X. destruct (bv_unsigned sel =? 3); [inversion X|]. destruct (bv_unsigned sel <? 3); [exact X| exact (RX.pfp_park_sub a X)]. }
  destruct (PrimInt63.eqb id 6%uint63); inversion X.
Qed.

Lemma OPS_fp_other : forall id args a, id <> CtrLib.HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp (OPS R) id args) ->
  0x53000 <= a < 0x8a000 /\ ~ OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref.RMalloc_iface.TwinB.ralloc_static a.
Proof.
  intros id args a Hid X. pose proof (OPS_fp_other0 id args a Hid X) as Y.
  unfold OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref.RMalloc_iface.TwinB.ralloc_static. unfold OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref.RMalloc_iface.TwinB.ralloc_static, OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref.RMallocRep.TwinB.RLIBC, OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref.RMallocRep.TwinB.RCTX, OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref.RMallocRep.TwinB.RERRNO, OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref.RMallocRep.TwinB.RSSP_GUARD, OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref.RMallocRep.TwinB.RGOT_SSP. unfold RX.RS, RX.PFP, DrvTop.inZ in Y.
  destruct Y as [Y|Y]; [| repeat (apply Exists_cons in Y as [Y|Y]; [cbn [fst snd] in Y|]); [| | inversion Y]]; lia.
Qed.

Lemma HOPS : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.heap_ops SEGS RX.XCL A Cw (OPS R).
Proof.
  constructor.
  - exact OPS_holds1.
  - exact OPS_fp1.
  - intros id args a Hid X. pose proof (OPS_fp_other0 id args a Hid X) as Y. left. apply HeapCtrB.TwinB.hi_seg.
    unfold RX.RS, RX.PFP, DrvTop.inZ in Y.
    destruct Y as [Y|Y]; [| repeat (apply Exists_cons in Y as [Y|Y]; [cbn [fst snd] in Y|]); [| | inversion Y]]; lia.
  - apply OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.plain_cover_law. exact (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds).
  - apply OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.plain_acc_user_law. exact (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds).
Qed.

Definition MEMCPY_PC : int := 332524%uint63.
Lemma CS_g6 : forall isV, contract_sound SEGS (OPS R) MP PB (G6.g6_contract MEMCPY_PC isV).
Proof.
  intros isV. eapply (UnpInst.g6_sound SEGS RX.XCL A (OPS R) HOPS MP PB (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds)).
  intros; eapply MemcpyG.TwinB.memcpy_G; eauto.
Qed.

Lemma OPS_mo_other : forall id args m mo mo', id <> CtrLib.HEAP_ID -> StateGlue.vm_agree mo mo' ->
  op_holds (OPS R) id args m mo -> op_holds (OPS R) id args m mo'.
Proof.
  intros id args m mo mo' Hid (VM & VC & _) H. unfold OPS, CtrSys.OPS in *. rewrite mk_holds in *.
  cbn [r_heap r_ext r_p1 r_file r_RS r_RSr R RX.R] in *. rewrite (comp_other id Hid) in *.
  assert (FDS : m_fds mo' = m_fds mo) by (rewrite VM; reflexivity).
  destruct (PrimInt63.eqb id 2%uint63). { cbn [FD3 oc_pure oc_holds] in *. unfold fd3_holds in *. destruct args as [|x [|y l]]; try exact H. rewrite FDS. exact H. }
  destruct (PrimInt63.eqb id 3%uint63). { cbn [RSTAGE oc_holds] in *. destruct args as [|off [|n [|]]]; exact H. }
  destruct (PrimInt63.eqb id 4%uint63). { cbn [FD3DIR oc_pure oc_holds] in *. unfold fd3dir_holds in *. destruct args as [|x l]; try exact H. rewrite FDS. exact H. }
  destruct (PrimInt63.eqb id 5%uint63). { cbn [FDINIT oc_pure oc_holds] in *. unfold fdinit_holds in *. destruct args as [|x l]; try exact H. rewrite FDS. exact H. }
  destruct (PrimInt63.eqb id 7%uint63). { cbn [RX.POOLC oc_holds] in *. destruct args as [|sel [|]]; exact H. }
  destruct (PrimInt63.eqb id 6%uint63); [| exact H].
  cbn [DrvTop.SPLINK oc_pure oc_holds] in *. unfold DrvTop.splink_holds in *. destruct args as [|w [|]]; try exact H.
  destruct VC as (_ & _ & _ & _ & VS). rewrite VS. exact H.
Qed.

Lemma MP_vm : forall mo mo', StateGlue.vm_agree mo mo' -> MP mo -> MP mo'.
Proof. intros mo mo' (VM & _) H. unfold MP, RX.MP in *. rewrite VM. exact H. Qed.

Lemma PB_blob6 : forall E, PB (eb E) -> eb E 6%uint63 = at_random_bytes (ed_random rnd).
Proof. intros E H. unfold PB, RX.PB in H. rewrite H. reflexivity. Qed.
Lemma PB_canary : forall E, PB (eb E) -> den E CANARY = Z_to_bv 64 (@Ceiling.ssp_canary CLG).
Proof.
  intros E H. rewrite <- canary_eq. pose proof (PB_blob6 E H) as B6.
  unfold CANARY, RunCeil.CANARY. cbn [den eb RunCeil.Ecan PrimInt63.eqb]. rewrite B6. reflexivity.
Qed.
Lemma PB_secret : forall E, PB (eb E) -> forall i, (i < 8)%nat ->
  nth_error (eb E 6%uint63) (8 + i) = nth_error (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem.le8 (Z_to_bv 64 (@Ceiling.ctx_secret CLG))) i.
Proof. intros E H i Hi. rewrite (PB_blob6 E H). exact (secret_eq i Hi). Qed.

Lemma PB5 : forall E, PB (eb E) -> forall i, 0 <= i < bv_unsigned (den E CtrM.B13) ->
  nth (Z.to_nat (bv_unsigned (den E CtrM.B14) + i)) (eb E 4%uint63) (Z_to_bv 8 0) = nth (Z.to_nat i) (eb E 5%uint63) (Z_to_bv 8 0).
Proof.
  intros E H i Hi. unfold PB, RX.PB in H.
  assert (E4 : eb E 4%uint63 = RX.file inp) by (rewrite H; reflexivity).
  assert (E5 : eb E 5%uint63 = payload (RX.file inp)) by (rewrite H; reflexivity).
  assert (E13 : eb E 13%uint63 = LE8 (Z.max 0 (fsize (RX.file inp) - 6 - cfg_len (RX.file inp)))) by (rewrite H; reflexivity).
  assert (E14 : eb E 14%uint63 = LE8 (6 + cfg_len (RX.file inp))) by (rewrite H; reflexivity).
  pose proof (Z.mod_pos_bound (cfgw (RX.file inp)) 32768 ltac:(lia)) as CB. unfold fsize in *.
  assert (R13 : 0 <= Z.max 0 (Z.min (Z.of_nat (length (RX.file inp))) (2 ^ 62) - 6 - cfg_len (RX.file inp)) < 2 ^ 64) by (unfold cfg_len; lia).
  assert (R14 : 0 <= 6 + cfg_len (RX.file inp) < 2 ^ 64) by (unfold cfg_len; lia).
  unfold CtrM.B13, CtrM.B14 in *. change wzero with (wp 0%uint63) in *.
  rewrite (OL.den_param8_u E 13%uint63 _ E13 R13) in Hi. rewrite (OL.den_param8_u E 14%uint63 _ E14 R14).
  rewrite E4, E5. unfold payload. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma PBstr1 : forall E, PB (eb E) -> exists str, eb E 1%uint63 = str ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) str /\
  bv_unsigned (den E (CtrA.SZ 9%uint63)) = Z.of_nat (length str) + 1.
Proof.
  intros E H. unfold PB, RX.PB in H. exists (RX.a0 inp). pose proof (RX.a0_len inp Hva) as L.
  assert (E1 : eb E 1%uint63 = RX.a0 inp ++ [Z_to_bv 8 0]) by (rewrite H; reflexivity).
  assert (E9 : eb E 9%uint63 = LE8 (Z.of_nat (length (RX.a0 inp)) + 1)) by (rewrite H; reflexivity).
  split; [exact E1|]. split; [exact (RX.a0_nz inp Hva)|].
  unfold CtrA.SZ. change wzero with (wp 0%uint63). exact (OL.den_param8_u E 9%uint63 _ E9 ltac:(lia)).
Qed.
Lemma PBstr3 : forall E, PB (eb E) -> exists str, eb E 3%uint63 = str ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) str /\
  bv_unsigned (den E (CtrA.SZ 10%uint63)) = Z.of_nat (length str) + 1.
Proof.
  intros E H. unfold PB, RX.PB in H. exists (RX.p1 inp). pose proof (RX.p1_len inp Hva) as L.
  assert (E3 : eb E 3%uint63 = RX.p1 inp ++ [Z_to_bv 8 0]) by (rewrite H; reflexivity).
  assert (E10 : eb E 10%uint63 = LE8 (Z.of_nat (length (RX.p1 inp)) + 1)) by (rewrite H; reflexivity).
  split; [exact E3|]. split; [exact (RX.p1_nz inp Hva)|].
  unfold CtrA.SZ. change wzero with (wp 0%uint63). exact (OL.den_param8_u E 10%uint63 _ E10 ltac:(lia)).
Qed.
Lemma PB12 : forall E, PB (eb E) -> bv_unsigned (den E (CtrA.SZ 15%uint63)) = Z.of_nat (length (eb E 12%uint63)) /\ Z.of_nat (length (eb E 12%uint63)) mod 8 = 0.
Proof.
  intros E H. unfold PB, RX.PB in H.
  assert (E12 : eb E 12%uint63 = SI.strarea (in_argv inp) (in_envp inp)) by (rewrite H; reflexivity).
  assert (E15 : eb E 15%uint63 = LE8 (Z.of_nat (length (SI.strarea (in_argv inp) (in_envp inp))))) by (rewrite H; reflexivity).
  pose proof (proj1 (valid_entry_sv48 _ _ _ Hsz) Hen) as (Hsp' & _ & _ & Hfit).
  pose proof (SI.BSB_top PH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd Hfit) as T. rewrite SI.length_BSB in T.
  pose proof (SI.length_strarea (in_argv inp) (in_envp inp)) as L. pose proof (SI.SP_lo sp Hsp') as LO.
  rewrite E12. split; [| apply SI.strarea_len8].
  unfold CtrA.SZ. change wzero with (wp 0%uint63). apply (OL.den_param8_u E 15%uint63 _ E15). unfold SI.raw_len, SI.SP in *. lia.
Qed.

Definition CS_free := @HeapCtrB.TwinB.free_sound CLG Cw (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) OPS_holds1 OPS_fp1 OPS_frame_other OPS_fp_other OPS_mo_other MP MP_vm PB CANARY PB_canary PB_secret.
Definition CS_roomcap := @HeapCtr.TwinB.roomcap_sound CLG Cw (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) OPS_holds1 OPS_fp1 MP PB.
Definition CS_roomdrop := @HeapCtr.TwinB.roomdrop_sound CLG Cw (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) OPS_holds1 OPS_fp1 MP PB.
Definition MFORK := @HeapCtrB.TwinB.malloc_nofork CLG Cw (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) OPS_holds1 OPS_fp1 OPS_frame_other OPS_fp_other OPS_mo_other MP MP_vm PB CANARY PB_canary PB_secret.

Definition CS_malloc_s := @HeapCtrB.TwinB.malloc_s_sound CLG Cw (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) OPS_holds1 OPS_fp1 OPS_frame_other OPS_fp_other OPS_mo_other MP MP_vm PB CANARY PB_canary PB_secret.
Definition CS_realloc := @HeapCtrB.TwinB.realloc_sound CLG Cw (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) OPS_holds1 OPS_fp1 OPS_frame_other OPS_fp_other OPS_mo_other MP MP_vm PB CANARY PB_canary PB_secret.
Definition CS_aligned := @HeapCtrB.TwinB.aligned_alloc_sound CLG Cw (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) OPS_holds1 OPS_fp1 OPS_frame_other OPS_fp_other OPS_mo_other MP MP_vm PB CANARY PB_canary PB_secret.

Definition CS_aligned1 := @HeapCtrB.TwinB.aligned_alloc1_sound CLG Cw (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) OPS_holds1 OPS_fp1 OPS_frame_other OPS_fp_other OPS_mo_other MP MP_vm PB CANARY PB_canary PB_secret.
Definition CS_blkside := @HeapCtrB.TwinB.blk_side_sound CLG Cw (OPS R) OPS_holds1 MP PB.

Lemma P_holds : forall args m md, op_holds (OPS R) Pool.POOL_ID args m md <-> Pool.pool_holds RX.FL SEGS args m md.
Proof. intros. unfold OPS, CtrSys.OPS. rewrite mk_holds. cbn [r_heap r_ext r_p1 r_file r_RS r_RSr R RX.R]. rewrite (comp_other Pool.POOL_ID ltac:(discriminate)). cbn. tauto. Qed.
Lemma P_fp : forall args, op_fp (OPS R) Pool.POOL_ID args = Pool.pool_fp RX.FL args.
Proof. intros. unfold OPS, CtrSys.OPS. rewrite mk_fp. cbn [r_heap r_ext r_p1 r_file r_RS r_RSr R RX.R]. rewrite (comp_other Pool.POOL_ID ltac:(discriminate)). reflexivity. Qed.
Lemma P_others : forall id args a, PrimInt63.eqb id Pool.POOL_ID = false ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp (OPS R) id args) ->
  ~ (to_Z RX.FL <= a < to_Z RX.FL + 8) /\ ~ (to_Z RX.FL + 16 <= a < to_Z RX.FL + 528).
Proof.
  intros id args a Hid X. rewrite RX.FLz. unfold OPS, CtrSys.OPS in X. rewrite mk_fp in X. cbn [r_heap r_ext r_p1 r_file r_RS r_RSr R RX.R] in X.
  destruct (PrimInt63.eqb id 1%uint63) eqn:E1.
  - apply Uint63.eqb_correct in E1. subst id. rewrite comp_1 in X. cbn [RX.HEAPC oc_fp] in X.
    destruct (HeapOp.decode args) as [[[[md aw] ws] ca]|] eqn:D.
    + destruct (proj1 (HeapOp.fp_spec RX.XCL args md aw ws ca a D) X) as (_ & NX & _).
      split; intros Ha; apply NX; unfold HeapOp.in_ivs, RX.XCL; apply Exists_cons_hd; unfold HeapOp.in_iv; cbn [fst snd]; lia.
    + unfold HeapOp.heap_fp in X. rewrite D in X. inversion X.
  - assert (Hid' : id <> CtrLib.HEAP_ID) by (intros ->; discriminate E1). rewrite (comp_other id Hid') in X.
    destruct (PrimInt63.eqb id 2%uint63); [inversion X|].
    destruct (PrimInt63.eqb id 3%uint63).
    { cbn [RSTAGE oc_fp] in X. unfold rstage_fp in X. apply Exists_cons in X as [X|X]; [cbn [fst snd] in X; unfold RS_LEN, RX.RS in *; lia | exfalso; inversion X]. }
    destruct (PrimInt63.eqb id 4%uint63); [inversion X|].
    destruct (PrimInt63.eqb id 5%uint63); [inversion X|].
    unfold Pool.POOL_ID in Hid. rewrite Hid in X. destruct (PrimInt63.eqb id 6%uint63); inversion X.
Qed.
Lemma P_cov : forall args a, ~ op_cov1 (OPS R) Pool.POOL_ID args a.
Proof. intros args a H. exact H. Qed.
Definition CS_pool_open := PoolSnd.open_sound SEGS (OPS R) RX.FL MP PB RX.FL8 RX.FLB P_holds P_fp P_cov P_others.
Definition CS_pool_close := PoolSnd.close_sound SEGS (OPS R) RX.FL MP PB RX.FL8 RX.FLB P_holds P_fp P_cov.
Definition CS_pool_park := PoolSnd.park_sound SEGS (OPS R) RX.FL MP PB RX.FL8 RX.FLB P_holds P_fp P_cov.
Definition CS_pool_unpark := PoolSnd.unpark_sound SEGS (OPS R) RX.FL MP PB RX.FL8 RX.FLB P_holds P_fp P_cov P_others.

Lemma RSI_val : to_Z RSI = RX.RS. Proof. reflexivity. Qed.
Lemma RS_range3 : 0x10000 <= to_Z RSI /\ to_Z RSI + 65536 <= 0x8a000. Proof. rewrite RSI_val. unfold RX.RS. lia. Qed.
Lemma OPS3_bytes : forall E woff wn m mo, PB (eb E) -> op_holds (OPS R) 3%uint63 [woff; wn] m mo ->
  bv_unsigned wn <= 65536 /\ forall i, 0 <= i < bv_unsigned wn -> m (Z_to_bv 64 (to_Z RSI + i)) = Some (nth (Z.to_nat (bv_unsigned woff + i)) (eb E 4%uint63) (Z_to_bv 8 0)).
Proof.
  intros E woff wn m mo HPB H. unfold OPS, CtrSys.OPS in H. rewrite mk_holds in H. cbn [r_heap r_ext r_p1 r_file r_RS r_RSr R RX.R] in H.
  rewrite comp_3 in H. cbn [RSTAGE oc_holds rstage_holds] in H. destruct H as (H1 & H2 & H3). unfold RS_LEN in H2.
  assert (E4 : eb E 4%uint63 = RX.file inp) by (unfold PB, RX.PB in HPB; rewrite HPB; reflexivity).
  split; [exact H2|]. intros i Hi. rewrite RSI_val, E4. exact (H3 i Hi).
Qed.
Lemma OPS3_advance : forall woff wn m m' mo, op_holds (OPS R) 3%uint63 [woff; wn] m mo -> op_holds (OPS R) 3%uint63 [(woff + wn)%bv; Z_to_bv 64 0] m' mo.
Proof.
  intros woff wn m m' mo H. unfold OPS, CtrSys.OPS in *. rewrite mk_holds in *. cbn [r_heap r_ext r_p1 r_file r_RS r_RSr R RX.R] in *.
  rewrite comp_3 in *. cbn [RSTAGE oc_holds rstage_holds] in *. destruct H as (H1 & H2 & H3).
  rewrite bv_add_unsigned. unfold bv_wrap. change (bv_unsigned (Z_to_bv 64 0)) with 0. unfold RS_LEN in *.
  pose proof (bv_unsigned_in_range _ woff). pose proof (bv_unsigned_in_range _ wn).
  pose proof (Z.mod_le (bv_unsigned woff + bv_unsigned wn) (bv_modulus 64) ltac:(lia) ltac:(rewrite bv_modulus_64; unfold two64; lia)).
  split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.
Lemma OPS3_fp : forall args args', op_fp (OPS R) 3%uint63 args = op_fp (OPS R) 3%uint63 args'.
Proof. intros. unfold OPS, CtrSys.OPS. rewrite !mk_fp. rewrite comp_3. reflexivity. Qed.
Definition CS_rstage := @RstageCtr.TwinB.rstage_sound CLG Cw (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) OPS_holds1 OPS_fp1 OPS_fp_other MP PB RSI RS_range3 OPS3_bytes OPS3_advance OPS3_fp.

Lemma mf_ok : mnofork_ok SEGS R MALLOC_PC (c_apply (Contract MALLOC_PC (CtrA.malloc_apply SEGS HeapCtr.TwinB.ERRNO HeapCtr.TwinB.LIBC HeapCtr.TwinB.GOT HeapCtr.TwinB.GUARD HeapCtr.TwinB.TP CANARY))).
Proof.
  intros st stA stB KB E ms m Hpc Happ HS HMP HPB HB.
  exact (MFORK MALLOC_PC st stA stB KB E ms m eq_refl Hpc Happ HS HMP HPB HB).
Qed.

Definition need (cid : int) (TAB : IMap.t contract) : Prop :=
  forall ct, IMap.find cid TAB = Some ct -> contract_sound SEGS (OPS R) MP PB ct.

Ltac tabcase H :=
  apply imap_of_find_in in H; cbn [In] in H;
  repeat (destruct H as [H|H]; [symmetry in H; injection H as -> ->|]); try (exfalso; exact H).

Lemma ctabL :  ctab_ok SEGS R T_Ubs2L.CONTRACTS.
Proof.
  intros  cid ct Hf. pose proof Hf as Hf0. unfold T_Ubs2L.CONTRACTS in Hf. tabcase Hf.
  - apply (MemcpyCtr.TwinB.memcpy_rr_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB). reflexivity.
  - apply CS_malloc_s. reflexivity.
Qed.
Lemma ctabE :  ctab_ok SEGS R T_Ubs2E.CONTRACTS.
Proof.
  intros  cid ct Hf. pose proof Hf as Hf0. unfold T_Ubs2E.CONTRACTS in Hf. tabcase Hf.
  - apply CS_free. reflexivity.
  - apply CS_blkside; reflexivity.
  - apply CS_aligned1; reflexivity.
  - apply CS_malloc_s. reflexivity.
  - apply CS_pool_open.
  - apply CS_pool_close.
  - apply (MemcpyWCtr.TwinB.memcpy_w_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB). reflexivity.
Qed.

Lemma lib8 :   lib_ok SEGS R (t_st T_Ubs2F.T_LIBGEN_r8) (t_st T_Ubs2F.R_LIBGEN_r8_RET).
Proof. intros. apply L8.lib_ok_r8; [apply ctabL; assumption | apply ctabE; assumption]. Qed.
Definition G0_stmt : Prop := (forall E0 K, r_PB R (eb E0) -> LNODE SEGS R L9.N E0 K (t_st T_Ubs2F.R_LIBGEN_r9_RET) -> LNODE SEGS R L9.N E0 K (t_st T_Ubs2L.T_G0_r14o5n0o7n1o1n24o3n2)).
Lemma lib9 :   G0_stmt -> lib_ok SEGS R (t_st T_Ubs2F.T_LIBGEN_r9) (t_st T_Ubs2F.R_LIBGEN_r9_RET).
Proof. intros. apply L9.lib_ok_r9; [apply ctabL; assumption | apply ctabE; assumption | assumption]. Qed.

Lemma ctabU : ctab_ok SEGS R T_Ubs2U.CONTRACTS.
Proof.
  intros  cid ct Hf. pose proof Hf as Hf0. unfold T_Ubs2U.CONTRACTS in Hf. tabcase Hf.
  - apply CS_free. reflexivity.
  - apply (MemcpyCtr.TwinB.memcpy_rr_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB). reflexivity.
  - apply CS_malloc_s. reflexivity.
  - apply CS_realloc. reflexivity.
  - apply (MemcpyCtr.TwinB.memcpy_sink_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB). reflexivity.
  - apply (TdInst.tdenter_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (TdInst.znext_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.g0_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.g2z_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.g2_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.g2b_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.g3p_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.groom_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.groom_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.groom_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gshr_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.g3r_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gcur_sound SEGS (OPS R) MP PB).
  - apply (UnpInst.gbnd_sound SEGS (OPS R) MP PB).
  - apply (UnpInst.gcap_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gcap_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gcap_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gnz_sound SEGS (OPS R) MP PB).
  - apply (UnpInst.gnz_sound SEGS (OPS R) MP PB).
  - apply (UnpInst.g4_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.vd_sound SEGS (OPS R) MP PB (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds)).
  - apply (UnpInst.gsplit_sound SEGS (OPS R) MP PB).
  - apply (UnpInst.gsplit_sound SEGS (OPS R) MP PB).
  - apply (UnpInst.g1_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.g1_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.g1_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.g1_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.g1_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.g1_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply CS_g6.
  - apply CS_g6.
  - apply (PkInst.roome_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (PkInst.push_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (PkInst.next_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (PkInst.pop_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (PkInst.push0_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (PkInst.pkenter_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (PkInst.pkexit_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (PkInst.pkexit_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (PkBodyCtr.TwinB.pkmemcpy_sound RX.XCL A Cw (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) HOPS CW3 MP PB). reflexivity.
  - apply (PkInst.peek_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkRegrow.pkregrow_sound _ SEGS RX.XCL A Cw (OPS R) HOPS CW3 CW3i MP PB (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds)). intros; eapply MemcpyG.TwinB.memcpy_G; eauto.
  - apply (PkBodyCtr.TwinB.pkextb_sound RX.XCL A Cw (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) HOPS CW3 MP PB).
  - apply (PkInst.pkcap_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gname_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gname_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gname_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gname_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gname_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gname_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gve_sound SEGS (OPS R) MP PB).
  - apply (UnpInst.ginv_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.ginv_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.ginv_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (PkInst.pkinv_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (PkInst.pkinv_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.ginv_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gperm_kinds_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gperm_kinds_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gperm_kinds_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.gperm_kinds_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (LdPartSound.ldpart_sound SEGS (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB).
  - apply (LdPartSound.ldpart_sound SEGS (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB).
  - apply (LdPartSound.ldpart_sound SEGS (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB).
  - apply (LdPartSound.ldpart_sound SEGS (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB).
  - apply (LdPartSound.ldpart_sound SEGS (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB).
  - apply (LdPartSound.ldpart_sound SEGS (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB).
  - apply (LdPartSound.ldpart_sound SEGS (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB).
  - apply (PkInst.pkfld_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkfld_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
  - apply (PkInst.pkload_sound SEGS RX.XCL A (OPS R) HOPS MP PB (r_MPA R)).
Qed.
Lemma ctabUE : ctab_ok SEGS R T_Ubs2UE.CONTRACTS.
Proof.
  intros  cid ct Hf. pose proof Hf as Hf0. unfold T_Ubs2UE.CONTRACTS in Hf. tabcase Hf.
  - apply CS_free. reflexivity.
  - apply CS_blkside; reflexivity.
  - apply CS_aligned1; reflexivity.
  - apply CS_malloc_s. reflexivity.
  - apply CS_pool_open.
  - apply CS_pool_close.
  - apply (TdInst.znext_sound SEGS RX.XCL A (OPS R) HOPS MP PB).
  - apply (UnpInst.vd_sound SEGS (OPS R) MP PB (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds)).
  - apply (UnpInst.vd_sound SEGS (OPS R) MP PB (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds)).
  - apply (UnpInst.vd_sound SEGS (OPS R) MP PB (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds)).
  - apply (MemcpyWCtr.TwinB.memcpy_w_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB). reflexivity.
  - apply CS_pool_park.
  - apply CS_pool_unpark.
  - apply CS_pool_unpark.
Qed.
Lemma G0_ok : G0_stmt.
Proof.
  intros     E0 K HPB HRET.
  exact (LU.g0_ok R ltac:(apply ctabU; assumption) ltac:(apply ctabUE; assumption)  E0 K HPB  HRET).
Qed.
Lemma ext_F :
  RX.ext_ok inp sp rnd Hva A Cw aw_fds aw_ceil_fds T_Ubs2F.CONTRACTS [21; 23; 24]%uint63.
Proof.
  intros cid ct Hf Hn. pose proof Hf as Hf0. unfold T_Ubs2F.CONTRACTS in Hf. tabcase Hf.
  - apply CS_roomcap.
  - apply CS_free. reflexivity.
  - apply (MemcpyCtr.TwinB.memcpy_rr_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB). reflexivity.
  - apply (MemcpyCtr.TwinB.memcpy_blob_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB). reflexivity.
  - apply CS_rstage. reflexivity.
  - apply (MemcpyCtr.TwinB.memcpy_payload_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB PB5). reflexivity.
  - apply (StrCtr.TwinB.strnlen_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB PBstr1 PBstr3 PB12). reflexivity.
  - apply CS_roomdrop.
  - apply CS_roomdrop.
  - exfalso. apply Hn. cbn [In]. tauto.
  - exfalso. apply Hn. cbn [In]. tauto.
  - exfalso. apply Hn. cbn [In]. tauto.
Qed.
Lemma FamF :
  lib_ok SEGS R (t_st T_Ubs2F.T_LIBGEN_r8) (t_st T_Ubs2F.R_LIBGEN_r8_RET) -> lib_ok SEGS R (t_st T_Ubs2F.T_LIBGEN_r9) (t_st T_Ubs2F.R_LIBGEN_r9_RET) ->
  RX.FamHypsF inp sp rnd Hva A Cw aw_fds aw_ceil_fds.
Proof. intros L8 L9. exact (RX.FHF inp sp rnd Hva A Cw aw_fds aw_ceil_fds ext_F mf_ok L8 L9). Qed.
Lemma ext_D :
  RX.ext_ok inp sp rnd Hva A Cw aw_fds aw_ceil_fds T_Ubs2D.CONTRACTS [22]%uint63.
Proof.
  intros cid ct Hf Hn. pose proof Hf as Hf0. unfold T_Ubs2D.CONTRACTS in Hf. tabcase Hf.
  - apply (MemcpyCtr.TwinB.memcpy_rr_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB). reflexivity.
  - apply (StrCtr.TwinB.strnlen_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB PBstr1 PBstr3 PB12). reflexivity.
  - apply CS_roomdrop.
  - exfalso. apply Hn. cbn [In]. tauto.
Qed.
Lemma FamD : RX.FamHypsD inp sp rnd Hva A Cw aw_fds aw_ceil_fds.
Proof. exact (RX.FHD inp sp rnd Hva A Cw aw_fds aw_ceil_fds ext_D mf_ok). Qed.
Lemma ext_A :
  RX.ext_ok inp sp rnd Hva A Cw aw_fds aw_ceil_fds T_Ubs2A.CONTRACTS [26]%uint63.
Proof.
  intros cid ct Hf Hn. pose proof Hf as Hf0. unfold T_Ubs2A.CONTRACTS in Hf. tabcase Hf.
  - apply (MemcpyCtr.TwinB.memcpy_rr_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB). reflexivity.
  - apply (StrCtr.TwinB.strnlen_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB PBstr1 PBstr3 PB12). reflexivity.
  - apply CS_roomdrop.
  - exfalso. apply Hn. cbn [In]. tauto.
Qed.
Lemma FamA : RX.FamHypsA inp sp rnd Hva A Cw aw_fds aw_ceil_fds.
Proof. exact (RX.FHA inp sp rnd Hva A Cw aw_fds aw_ceil_fds ext_A). Qed.
Lemma ext_T :
  RX.ext_ok inp sp rnd Hva A Cw aw_fds aw_ceil_fds T_Ubs2T.CONTRACTS [27]%uint63.
Proof.
  intros cid ct Hf Hn. pose proof Hf as Hf0. unfold T_Ubs2T.CONTRACTS in Hf. tabcase Hf.
  - apply (MemcpyCtr.TwinB.memcpy_rr_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB). reflexivity.
  - apply (StrCtr.TwinB.strnlen_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB PBstr1 PBstr3 PB12). reflexivity.
  - apply CS_roomdrop.
  - exfalso. apply Hn. cbn [In]. tauto.
Qed.
Lemma FamT : RX.FamHypsT inp sp rnd Hva A Cw aw_fds aw_ceil_fds.
Proof. exact (RX.FHT inp sp rnd Hva A Cw aw_fds aw_ceil_fds ext_T). Qed.
Lemma ext_N :
  RX.ext_ok inp sp rnd Hva A Cw aw_fds aw_ceil_fds T_UbsNU.CONTRACTS [].
Proof.
  intros cid ct Hf Hn. pose proof Hf as Hf0. unfold T_UbsNU.CONTRACTS in Hf. tabcase Hf.
  - apply (MemcpyCtr.TwinB.memcpy_rr_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB). reflexivity.
  - apply (StrCtr.TwinB.strnlen_sound (OPS R) (RX.OPS_plain_R inp sp rnd Hva A Cw aw_fds aw_ceil_fds) MP PB PBstr1 PBstr3 PB12). reflexivity.
  - apply CS_roomdrop.
Qed.
Lemma FamN : RX.FamHypsN inp sp rnd Hva A Cw aw_fds aw_ceil_fds.
Proof. exact (RX.FHN inp sp rnd Hva A Cw aw_fds aw_ceil_fds ext_N). Qed.

Theorem all_hyps :
    G0_stmt ->
  RX.AllHyps inp sp rnd Hva A Cw aw_fds aw_ceil_fds.
Proof.
  intros  G0.
  exact (RX.AH inp sp rnd Hva A Cw aw_fds aw_ceil_fds (FamF (lib8 ) (lib9  G0)) FamD FamA FamT FamN).
Qed.

Theorem rz :
    G0_stmt ->
  realizes SEGS (RX.c0 inp sp brk0 mb rnd lim) (K inp).
Proof.
  intros  G0.
  exact (RX.rz inp sp brk0 mb rnd lim Hva Hve Hhw Hsz Hen A Cw aw_fds aw_ceil_fds cw_init aw_ceil0 aw_init
           (all_hyps  G0)).
Qed.

End RUN.
End TopHypsUbs.
