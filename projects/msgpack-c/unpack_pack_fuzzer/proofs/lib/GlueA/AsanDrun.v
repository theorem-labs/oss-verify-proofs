(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AInstanceM AInstanceU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2 AInstanceU2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Ops CtrSys StackInit InitLib CertSound DrvShape DrvLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA FakeLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import AsanOps AsanRun.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val St Ops CtrLib HeapOp CertS DrvShape DrvLib.
Open Scope Z_scope.
Unset Lia Cache.

Local Notation AIu2 := (AInstanceU2.AIu2 ExhFirst.exh_first).
Local Notation AIu_fake := (FakeLaw.AIu_fake ExhFirst.exh_first).
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Section Drun.
Context {rc : runConstT}.

Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AIu2 IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.
Hypothesis ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Hypothesis ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AIu2 L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> sh_cov z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo'.
Variable UNIV : list (list Z).
Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AIu2 L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (AM.wa a) = m (AM.wa a)) -> wmono asegs m m' -> AHEAP AIu2 L RNG st LB m'.
Variable Cw : client_world.

Hypothesis ACCT_fds : forall aw L RNG st LBa mo f, ACCT aw L RNG st LBa mo -> ACCT aw L RNG st LBa (with_fds f mo).

Hypothesis IMGX_rs3 : forall a, RS3 <= a < RS3 + 65536 -> in_ivs IMGX a.

Variable inp : ProcInput.
Variables (sp : word) (rnd : EntryDraw).
Hypothesis Hva : valid_argv (in_argv inp).

Definition fs0 : Fs := in_fs inp.
Definition a0 : list byte := hd [] (in_argv inp).
Definition p1 : list byte := hd [] (tl (in_argv inp)).
Definition file : list byte := match fs_lookup fs0 p1 with Some f => f | None => [] end.

Definition xb (j : int) : list byte :=
  match to_Z j with
  | 4 => file
  | 5 => payload file
  | 11 => LE8 (fsize file)
  | 13 => LE8 (Z.max 0 (fsize file - 6 - cfg_len file))
  | 14 => LE8 (6 + cfg_len file)
  | _ => []
  end.
Definition E0 : env := InitLib.E0 sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd xb.
Definition MP (m : Model) : Prop := m_fs m = fs0.
Definition PB (b : int -> list byte) : Prop := b = eb E0.

Let OPSA : optable := AsanRun.OPSA IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file.
Let heapA : opcomp := AsanRun.heapA IMGX IMGX_aci ACCT UNIV AI_frame_top Cw.
Let extA : int -> opcomp := AsanRun.extA file.
Let TM := AsanRun.asan_tm IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file.

Lemma heap_fds : forall args m model fds, oc_holds heapA args m model -> oc_holds heapA args m (with_fds fds model).
Proof.
  intros args m model fds H.
  apply (heap_holdsA_intro AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake Cw).
  apply (heap_holdsA_inv AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake Cw) in H.
  destruct H as (md & aw & ws & ca & LB & W & D & HW & WF & HC & TI). exists md, aw, ws, ca, LB, W.
  split; [exact D|]. split; [| auto].
  destruct HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  unfold aw_holds_w. repeat (split; [assumption|]). split; [exact (ACCT_fds _ _ _ _ _ _ fds AC)|]. auto.
Qed.
Lemma heap_fp_stage : forall args a, RS3 <= a < RS3 + 65536 -> ~ Exists (fun iv => fst iv <= a < snd iv) (oc_fp heapA args).
Proof.
  intros args a Ha X. change (Exists (fun iv => fst iv <= a < snd iv) (heap_fp IMGX args)) in X.
  destruct (decode args) as [[[[md aw] ws] ca]|] eqn:D.
  - destruct (proj1 (fp_spec IMGX args md aw ws ca a D) X) as (_ & NX & _). exact (NX (IMGX_rs3 a Ha)).
  - unfold heap_fp in X. rewrite D in X. inversion X.
Qed.
Lemma ext_fds : forall id args m model fds, oc_holds (extA id) args m model -> oc_holds (extA id) args m (with_fds fds model).
Proof.
  intros id args m model fds H. unfold extA, AsanRun.extA, ext_asan in *.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; exact H.
Qed.
Lemma ext_fp_stage : forall id args a, RS3 <= a < RS3 + 65536 -> ~ Exists (fun iv => fst iv <= a < snd iv) (oc_fp (extA id) args).
Proof.
  intros id args a Ha X. unfold RS3 in Ha. unfold extA, AsanRun.extA, ext_asan in X.
  repeat match type of X with context [if ?c then _ else _] => destruct c end.
  - pose proof (pool_fp_hull args a X). lia.
  - inversion X.
  - cbn [oc_fp zsh_c] in X. apply Exists_exists in X as (iv & [<-|[]] & Hx). cbn [fst snd] in Hx. unfold ReadPre.ZSC_LO, ReadPre.ZSC_HI in Hx. lia.
  - inversion X.
  - cbn [oc_fp zro_c] in X. apply Exists_exists in X as (iv & [<-|[]] & Hx). cbn [fst snd] in Hx. unfold LowImg.ZRO_LO, LowImg.ZRO_HI in Hx. lia.
  - pose proof (AsanRun.stk_sh_lo a (zarg_fp_stk args a X)). lia.
  - cbn [oc_fp rstv_c] in X. apply Exists_exists in X as (iv & [<-|[]] & Hx). cbn [fst snd] in Hx. unfold ReadPre.STAGE in Hx. lia.
  - cbn [oc_fp zpb_c] in X. apply Exists_exists in X as (iv & Hiv & Hx). unfold PubImg.ZPBW in Hiv. cbn [In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hx; lia.
  - cbn [oc_fp gsh_c] in X. pose proof (gsh_hull a X). lia.
  - inversion X.
Qed.

Lemma MP_fs : forall m, MP m -> m_fs m = fs0. Proof. intros m H. exact H. Qed.
Lemma MP_fds : forall fds m, MP m -> MP (with_fds fds m). Proof. intros fds m H. exact H. Qed.
Lemma MP_stable : mp_stable MP.
Proof. intros mo acc mo' H M. unfold MP in *. destruct (materialize_model_accesses_frame _ _ _ M) as (_ & _ & _ & _ & F & _). unfold m_fs. rewrite F. exact H. Qed.
Lemma eb1 : eb E0 1%uint63 = cstr a0. Proof. reflexivity. Qed.
Lemma eb3 : eb E0 3%uint63 = cstr p1. Proof. reflexivity. Qed.
Lemma eb9 : eb E0 9%uint63 = LE8 (Z.of_nat (length a0) + 1). Proof. reflexivity. Qed.
Lemma eb10 : eb E0 10%uint63 = LE8 (Z.of_nat (length p1) + 1). Proof. reflexivity. Qed.
Lemma a0_In : In a0 (in_argv inp).
Proof. unfold a0. destruct Hva as (Hn & _). destruct (in_argv inp); [cbn in Hn; lia | left; reflexivity]. Qed.
Lemma p1_In : p1 = [] \/ In p1 (in_argv inp).
Proof. unfold p1. destruct (in_argv inp) as [|x [|y l]]; [left; reflexivity | left; reflexivity | right; right; left; reflexivity]. Qed.
Lemma a0_len : Z.of_nat (length a0) <= 131071.
Proof. destruct Hva as (_ & _ & HL & _). exact (proj1 (Forall_forall _ _) HL a0 a0_In). Qed.
Lemma p1_len : Z.of_nat (length p1) <= 131071.
Proof. destruct Hva as (_ & _ & HL & _). destruct p1_In as [-> | Hin]; [cbn; lia | exact (proj1 (Forall_forall _ _) HL p1 Hin)]. Qed.
Lemma p1_nz : ~ In (Z_to_bv 8 0) p1.
Proof. destruct Hva as (_ & _ & _ & HZ & _). destruct p1_In as [-> | Hin]; [intros [] | exact (proj1 (Forall_forall _ _) HZ p1 Hin)]. Qed.

Lemma TM_fds : forall mo fds, op_minv (CtrSys.OPS heapA extA p1 file RS3 RS3_range TM) mo -> op_minv (CtrSys.OPS heapA extA p1 file RS3 RS3_range TM) (with_fds fds mo).
Proof. intros mo fds [H L]. split; [exact H| exact L]. Qed.
Lemma TM_cov1 : forall id args a, op_cov1 (CtrSys.OPS heapA extA p1 file RS3 RS3_range TM) id args a -> id = 1%uint63.
Proof. intros id args a [E _]. apply Uint63.eqb_correct in E. exact E. Qed.

Definition RA : drun :=
  DRun heapA extA a0 p1 file fs0 RS3 RS3_range MP PB MP_fs MP_fds MP_stable heap_fds heap_fp_stage ext_fds ext_fp_stage
       (fun b (H : PB b) => match eq_sym H in (_ = e) return (e 1%uint63 = cstr a0 /\ e 9%uint63 = LE8 (Z.of_nat (length a0) + 1)) with eq_refl => conj eb1 eb9 end)
       (fun b (H : PB b) => match eq_sym H in (_ = e) return (e 3%uint63 = cstr p1 /\ e 10%uint63 = LE8 (Z.of_nat (length p1) + 1)) with eq_refl => conj eb3 eb10 end)
       a0_len p1_len p1_nz TM TM_fds TM_cov1.
Lemma OPS_RA : DrvLib.OPS RA = OPSA. Proof. reflexivity. Qed.

Theorem close_sound_RA : forall pc, PlanSound.PlanS.ecall_at asegs pc -> PlanSound.PlanS.contract_sound asegs OPSA MP PB (CtrS.c_close pc).
Proof.
  intros pc Hat. eapply (CtrSys.close_sound asegs heapA extA p1 file RS3); try eassumption; try exact MP_fds; try exact TM_fds; try exact TM_cov1; try exact MP_stable;
    try exact heap_fds; try exact ext_fds.
Qed.
Theorem ioctl_sound_RA : forall pc, PlanSound.PlanS.ecall_at asegs pc -> PlanSound.PlanS.contract_sound asegs OPSA MP PB (CtrS.c_ioctl pc).
Proof.
  intros pc Hat. eapply (CtrSys.ioctl_sound asegs heapA extA p1 file RS3); try eassumption; try exact MP_fds; try exact TM_fds; try exact TM_cov1; try exact MP_stable;
    try exact heap_fds; try exact ext_fds.
Qed.

Lemma PB_arg1_RA : forall b, PB b -> b 3%uint63 = p1 ++ [Z_to_bv 8 0] /\ b 10%uint63 = Z_to_le_bytes 8 (Z.of_nat (length p1) + 1).
Proof. intros b ->. split; reflexivity. Qed.
Theorem open_absent_sound_RA : forall (FAM_ABSENT :
  path_has_slash p1 = false /\ path_is_dirref p1 = false /\ (length p1 < 4096)%nat /\ (p1 = [] \/ forall model, MP model -> fs_lookup (m_fs model) p1 = None)),
  forall pc, PlanSound.PlanS.ecall_at asegs pc -> PlanSound.PlanS.contract_sound asegs OPSA MP PB (CtrS.c_open_absent pc).
Proof.
  intros FAM pc Hat. eapply (CtrSys.open_absent_sound asegs heapA extA p1 file RS3); try eassumption; try exact MP_fds; try exact TM_fds; try exact TM_cov1; try exact MP_stable;
    try exact heap_fds; try exact ext_fds; try exact PB_arg1_RA; try exact p1_nz; try exact p1_len.
Qed.
Theorem open_toolong_sound_RA : forall (FAM_TOOLONG : (4096 <= length p1)%nat),
  forall pc, PlanSound.PlanS.ecall_at asegs pc -> PlanSound.PlanS.contract_sound asegs OPSA MP PB (CtrS.c_open_toolong pc).
Proof.
  intros FAM pc Hat. eapply (CtrSys.open_toolong_sound asegs heapA extA p1 file RS3); try eassumption; try exact MP_fds; try exact TM_fds; try exact TM_cov1; try exact MP_stable;
    try exact heap_fds; try exact ext_fds; try exact PB_arg1_RA; try exact p1_nz; try exact p1_len.
Qed.
Lemma file_pb_RA : file_pb RA. Proof. intros b ->. cbn [r_file RA]. repeat split; reflexivity. Qed.
End Drun.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AInstanceM.TwinB AInstanceU.TwinB.
Import AMalloc_iface2.TwinB AInstanceU2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Ops OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.CtrSys OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.StackInit OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.InitLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.CertSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.DrvShape OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.DrvLib.
Import Ledger.TwinB Op.TwinB.
Import AsanOps.TwinB AsanRun.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val St Ops CtrLib HeapOp CertS DrvShape DrvLib.
Open Scope Z_scope.
Unset Lia Cache.

Local Notation AIu2 := (AInstanceU2.TwinB.AIu2 ExhFirst.TwinB.exh_first).
Local Notation AIu_fake := (FakeLaw.TwinB.AIu_fake ExhFirst.TwinB.exh_first).
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Section Drun.
Context {rc : runConstT}.

Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AIu2 IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.
Hypothesis ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Hypothesis ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AIu2 L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> sh_cov z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo'.
Variable UNIV : list (list Z).
Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AIu2 L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (AM.wa a) = m (AM.wa a)) -> wmono bsegs m m' -> AHEAP AIu2 L RNG st LB m'.
Variable Cw : client_world.

Hypothesis ACCT_fds : forall aw L RNG st LBa mo f, ACCT aw L RNG st LBa mo -> ACCT aw L RNG st LBa (with_fds f mo).

Hypothesis IMGX_rs3 : forall a, RS3 <= a < RS3 + 65536 -> in_ivs IMGX a.

Variable inp : ProcInput.
Variables (sp : word) (rnd : EntryDraw).
Hypothesis Hva : valid_argv (in_argv inp).

Definition fs0 : Fs := in_fs inp.
Definition a0 : list byte := hd [] (in_argv inp).
Definition p1 : list byte := hd [] (tl (in_argv inp)).
Definition file : list byte := match fs_lookup fs0 p1 with Some f => f | None => [] end.

Definition xb (j : int) : list byte :=
  match to_Z j with
  | 4 => file
  | 5 => payload file
  | 11 => LE8 (fsize file)
  | 13 => LE8 (Z.max 0 (fsize file - 6 - cfg_len file))
  | 14 => LE8 (6 + cfg_len file)
  | _ => []
  end.
Definition E0 : env := InitLib.E0 sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd xb.
Definition MP (m : Model) : Prop := m_fs m = fs0.
Definition PB (b : int -> list byte) : Prop := b = eb E0.

Let OPSA : optable := AsanRun.TwinB.OPSA IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file.
Let heapA : opcomp := AsanRun.TwinB.heapA IMGX IMGX_aci ACCT UNIV AI_frame_top Cw.
Let extA : int -> opcomp := AsanRun.TwinB.extA file.
Let TM := AsanRun.TwinB.asan_tm IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file.

Lemma heap_fds : forall args m model fds, oc_holds heapA args m model -> oc_holds heapA args m (with_fds fds model).
Proof.
  intros args m model fds H.
  apply (heap_holdsA_intro AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake Cw).
  apply (heap_holdsA_inv AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake Cw) in H.
  destruct H as (md & aw & ws & ca & LB & W & D & HW & WF & HC & TI). exists md, aw, ws, ca, LB, W.
  split; [exact D|]. split; [| auto].
  destruct HW as (AH & HT & ND & HFA & NDF & HLB & EQ & MAP & ZC0 & ZCB & AC & HU & CLS & VFL & INC).
  unfold aw_holds_w. repeat (split; [assumption|]). split; [exact (ACCT_fds _ _ _ _ _ _ fds AC)|]. auto.
Qed.
Lemma heap_fp_stage : forall args a, RS3 <= a < RS3 + 65536 -> ~ Exists (fun iv => fst iv <= a < snd iv) (oc_fp heapA args).
Proof.
  intros args a Ha X. change (Exists (fun iv => fst iv <= a < snd iv) (heap_fp IMGX args)) in X.
  destruct (decode args) as [[[[md aw] ws] ca]|] eqn:D.
  - destruct (proj1 (fp_spec IMGX args md aw ws ca a D) X) as (_ & NX & _). exact (NX (IMGX_rs3 a Ha)).
  - unfold heap_fp in X. rewrite D in X. inversion X.
Qed.
Lemma ext_fds : forall id args m model fds, oc_holds (extA id) args m model -> oc_holds (extA id) args m (with_fds fds model).
Proof.
  intros id args m model fds H. unfold extA, AsanRun.TwinB.extA, ext_asan in *.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; exact H.
Qed.
Lemma ext_fp_stage : forall id args a, RS3 <= a < RS3 + 65536 -> ~ Exists (fun iv => fst iv <= a < snd iv) (oc_fp (extA id) args).
Proof.
  intros id args a Ha X. unfold RS3 in Ha. unfold extA, AsanRun.TwinB.extA, ext_asan in X.
  repeat match type of X with context [if ?c then _ else _] => destruct c end.
  - pose proof (pool_fp_hull args a X). lia.
  - inversion X.
  - cbn [oc_fp zsh_c] in X. apply Exists_exists in X as (iv & [<-|[]] & Hx). cbn [fst snd] in Hx. unfold ReadPre.TwinB.ZSC_LO, ReadPre.TwinB.ZSC_HI in Hx. lia.
  - inversion X.
  - cbn [oc_fp zro_c] in X. apply Exists_exists in X as (iv & [<-|[]] & Hx). cbn [fst snd] in Hx. unfold LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI in Hx. lia.
  - pose proof (AsanRun.TwinB.stk_sh_lo a (zarg_fp_stk args a X)). lia.
  - cbn [oc_fp rstv_c] in X. apply Exists_exists in X as (iv & [<-|[]] & Hx). cbn [fst snd] in Hx. unfold ReadPre.TwinB.STAGE in Hx. lia.
  - cbn [oc_fp zpb_c] in X. apply Exists_exists in X as (iv & Hiv & Hx). unfold PubImg.TwinB.ZPBW in Hiv. cbn [In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hx; lia.
  - cbn [oc_fp gsh_c] in X. pose proof (gsh_hull a X). lia.
  - inversion X.
Qed.

Lemma MP_fs : forall m, MP m -> m_fs m = fs0. Proof. intros m H. exact H. Qed.
Lemma MP_fds : forall fds m, MP m -> MP (with_fds fds m). Proof. intros fds m H. exact H. Qed.
Lemma MP_stable : mp_stable MP.
Proof. intros mo acc mo' H M. unfold MP in *. destruct (materialize_model_accesses_frame _ _ _ M) as (_ & _ & _ & _ & F & _). unfold m_fs. rewrite F. exact H. Qed.
Lemma eb1 : eb E0 1%uint63 = cstr a0. Proof. reflexivity. Qed.
Lemma eb3 : eb E0 3%uint63 = cstr p1. Proof. reflexivity. Qed.
Lemma eb9 : eb E0 9%uint63 = LE8 (Z.of_nat (length a0) + 1). Proof. reflexivity. Qed.
Lemma eb10 : eb E0 10%uint63 = LE8 (Z.of_nat (length p1) + 1). Proof. reflexivity. Qed.
Lemma a0_In : In a0 (in_argv inp).
Proof. unfold a0. destruct Hva as (Hn & _). destruct (in_argv inp); [cbn in Hn; lia | left; reflexivity]. Qed.
Lemma p1_In : p1 = [] \/ In p1 (in_argv inp).
Proof. unfold p1. destruct (in_argv inp) as [|x [|y l]]; [left; reflexivity | left; reflexivity | right; right; left; reflexivity]. Qed.
Lemma a0_len : Z.of_nat (length a0) <= 131071.
Proof. destruct Hva as (_ & _ & HL & _). exact (proj1 (Forall_forall _ _) HL a0 a0_In). Qed.
Lemma p1_len : Z.of_nat (length p1) <= 131071.
Proof. destruct Hva as (_ & _ & HL & _). destruct p1_In as [-> | Hin]; [cbn; lia | exact (proj1 (Forall_forall _ _) HL p1 Hin)]. Qed.
Lemma p1_nz : ~ In (Z_to_bv 8 0) p1.
Proof. destruct Hva as (_ & _ & _ & HZ & _). destruct p1_In as [-> | Hin]; [intros [] | exact (proj1 (Forall_forall _ _) HZ p1 Hin)]. Qed.

Lemma TM_fds : forall mo fds, op_minv (CtrSys.OPS heapA extA p1 file RS3 RS3_range TM) mo -> op_minv (CtrSys.OPS heapA extA p1 file RS3 RS3_range TM) (with_fds fds mo).
Proof. intros mo fds [H L]. split; [exact H| exact L]. Qed.
Lemma TM_cov1 : forall id args a, op_cov1 (CtrSys.OPS heapA extA p1 file RS3 RS3_range TM) id args a -> id = 1%uint63.
Proof. intros id args a [E _]. apply Uint63.eqb_correct in E. exact E. Qed.

Definition RA : drun :=
  DRun heapA extA a0 p1 file fs0 RS3 RS3_range MP PB MP_fs MP_fds MP_stable heap_fds heap_fp_stage ext_fds ext_fp_stage
       (fun b (H : PB b) => match eq_sym H in (_ = e) return (e 1%uint63 = cstr a0 /\ e 9%uint63 = LE8 (Z.of_nat (length a0) + 1)) with eq_refl => conj eb1 eb9 end)
       (fun b (H : PB b) => match eq_sym H in (_ = e) return (e 3%uint63 = cstr p1 /\ e 10%uint63 = LE8 (Z.of_nat (length p1) + 1)) with eq_refl => conj eb3 eb10 end)
       a0_len p1_len p1_nz TM TM_fds TM_cov1.
Lemma OPS_RA : DrvLib.OPS RA = OPSA. Proof. reflexivity. Qed.

Theorem close_sound_RA : forall pc, PlanSound.PlanS.ecall_at bsegs pc -> PlanSound.PlanS.contract_sound bsegs OPSA MP PB (CtrS.c_close pc).
Proof.
  intros pc Hat. eapply (CtrSys.close_sound bsegs heapA extA p1 file RS3); try eassumption; try exact MP_fds; try exact TM_fds; try exact TM_cov1; try exact MP_stable;
    try exact heap_fds; try exact ext_fds.
Qed.
Theorem ioctl_sound_RA : forall pc, PlanSound.PlanS.ecall_at bsegs pc -> PlanSound.PlanS.contract_sound bsegs OPSA MP PB (CtrS.c_ioctl pc).
Proof.
  intros pc Hat. eapply (CtrSys.ioctl_sound bsegs heapA extA p1 file RS3); try eassumption; try exact MP_fds; try exact TM_fds; try exact TM_cov1; try exact MP_stable;
    try exact heap_fds; try exact ext_fds.
Qed.

Lemma PB_arg1_RA : forall b, PB b -> b 3%uint63 = p1 ++ [Z_to_bv 8 0] /\ b 10%uint63 = Z_to_le_bytes 8 (Z.of_nat (length p1) + 1).
Proof. intros b ->. split; reflexivity. Qed.
Theorem open_absent_sound_RA : forall (FAM_ABSENT :
  path_has_slash p1 = false /\ path_is_dirref p1 = false /\ (length p1 < 4096)%nat /\ (p1 = [] \/ forall model, MP model -> fs_lookup (m_fs model) p1 = None)),
  forall pc, PlanSound.PlanS.ecall_at bsegs pc -> PlanSound.PlanS.contract_sound bsegs OPSA MP PB (CtrS.c_open_absent pc).
Proof.
  intros FAM pc Hat. eapply (CtrSys.open_absent_sound bsegs heapA extA p1 file RS3); try eassumption; try exact MP_fds; try exact TM_fds; try exact TM_cov1; try exact MP_stable;
    try exact heap_fds; try exact ext_fds; try exact PB_arg1_RA; try exact p1_nz; try exact p1_len.
Qed.
Theorem open_toolong_sound_RA : forall (FAM_TOOLONG : (4096 <= length p1)%nat),
  forall pc, PlanSound.PlanS.ecall_at bsegs pc -> PlanSound.PlanS.contract_sound bsegs OPSA MP PB (CtrS.c_open_toolong pc).
Proof.
  intros FAM pc Hat. eapply (CtrSys.open_toolong_sound bsegs heapA extA p1 file RS3); try eassumption; try exact MP_fds; try exact TM_fds; try exact TM_cov1; try exact MP_stable;
    try exact heap_fds; try exact ext_fds; try exact PB_arg1_RA; try exact p1_nz; try exact p1_len.
Qed.
Lemma file_pb_RA : file_pb RA. Proof. intros b ->. cbn [r_file RA]. repeat split; reflexivity. Qed.
End Drun.
End TwinB.
