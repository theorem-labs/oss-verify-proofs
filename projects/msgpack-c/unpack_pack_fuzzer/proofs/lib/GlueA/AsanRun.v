(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Ops CtrSys.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require ShLoadLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA FakeLaw Actr ShLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Seal Inv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggPre UnreggC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadC ReadPre ReadPost StackSh LowImg StrReg StrRegC RangeC PubC PubImg GshC GshImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import AsanOps.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 St Ops CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Local Notation AIu2 := (AInstanceU2.AIu2 ExhFirst.exh_first).
Local Notation AIu_fake := (FakeLaw.AIu_fake ExhFirst.exh_first).
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Section Run.
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
Variables p1 file : list byte.

Hypothesis IMGX_stage : forall a, ReadPre.STAGE <= a < ReadPre.STAGE + 65536 -> in_ivs IMGX a.

Definition heapA : opcomp :=
  OpComp (heap_holdsA AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake Cw) (heap_fp IMGX)
         (fun args m m' mo AG DM H => heap_frameA AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake Cw args m m' mo AG DM H).

Definition RS3 : Z := 0x10000.
Lemma RS3_range : 0 <= RS3 /\ RS3 + 65536 <= two64.
Proof. unfold RS3, two64. lia. Qed.

Definition extA : int -> opcomp := ext_asan file.
Definition holdsT : int -> list word -> (word -> option byte) -> Model -> Prop :=
  comp_holds heapA (FD3 p1 file) (RSTAGE file RS3 RS3_range) FD3DIR FDINIT extA.

Definition ledgered (id : int) : bool := PrimInt63.eqb id 1%uint63.

Lemma T_led : forall id args m mo, ledgered id = true -> holdsT id args m mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Proof.
  intros id args m mo L H. unfold ledgered in L. apply Uint63.eqb_correct in L. subst id.
  exact (H_ledA AIu2 IMGX IMGX_aci ACCT COVP NMAX ACCT_led UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake Cw 1%uint63 args m mo eq_refl H).
Qed.

Lemma T_cov : forall id args m mo z, holdsT id args m mo -> cov1 id args z ->
  ledgered id = true /\ (page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z)).
Proof.
  intros id args m mo z H C. pose proof C as [E _]. change OPID with 1%uint63 in E. pose proof E as E1. apply Uint63.eqb_correct in E1. subst id.
  split; [reflexivity|].
  exact (proj2 (H_covA AIu2 IMGX IMGX_aci ACCT COVP ACCT_cov ACCT_cov_sh UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake Cw 1%uint63 args m mo z H C)).
Qed.

Lemma same_but_mat_fds : forall mo mo', same_but_mat mo mo' -> m_fds mo' = m_fds mo.
Proof. intros mo mo' ->. destruct mo as [fd [mp lzz mt] io fs pr lm tm]. reflexivity. Qed.

Lemma T_mat : forall id args m mo mo', holdsT id args m mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  holdsT id args m mo'.
Proof.
  intros id args m mo mo' H SB ND NEW. unfold holdsT, comp_holds, comp_of in *.
  destruct (PrimInt63.eqb id 1%uint63) eqn:Q1.
  { apply Uint63.eqb_correct in Q1. subst id. exact (H_matA AIu2 IMGX IMGX_aci ACCT COVP ACCT_mat UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake Cw 1%uint63 args m mo mo' H SB ND NEW). }
  pose proof (same_but_mat_fds mo mo' SB) as FDS.
  destruct (PrimInt63.eqb id 2%uint63). { cbn [oc_holds FD3 oc_pure] in *. unfold fd3_holds in *. rewrite FDS. exact H. }
  destruct (PrimInt63.eqb id 3%uint63). { exact H. }
  destruct (PrimInt63.eqb id 4%uint63). { cbn [oc_holds FD3DIR oc_pure] in *. unfold fd3dir_holds in *. rewrite FDS. exact H. }
  destruct (PrimInt63.eqb id 5%uint63). { cbn [oc_holds FDINIT oc_pure] in *. unfold fdinit_holds in *. rewrite FDS. exact H. }
  unfold extA, ext_asan in *.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; exact H.
Qed.

Definition asan_tm : tab_model heapA (FD3 p1 file) (RSTAGE file RS3 RS3_range) FD3DIR FDINIT extA :=
  TabModel heapA (FD3 p1 file) (RSTAGE file RS3 RS3_range) FD3DIR FDINIT extA
           (asan_minv C0) C0 cov1 (asan_minv_halted C0)
           (asan_acc holdsT C0 cov1 COVP NMAX ledgered T_led T_cov T_mat).

Definition OPSA : optable := CtrSys.OPS heapA extA p1 file RS3 RS3_range asan_tm.

Lemma OPSA_holds1 : forall args m mo, op_holds OPSA HEAP_ID args m mo <-> heap_holdsX AIu2 ACCT UNIV Cw args m mo.
Proof.
  intros args m mo. split; intros H.
  - exact (heap_holdsA_inv AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake Cw args m mo H).
  - exact (heap_holdsA_intro AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake Cw args m mo H).
Qed.
Lemma OPSA_fp1 : forall args, op_fp OPSA HEAP_ID args = heap_fp IMGX args.
Proof. reflexivity. Qed.
Lemma OPSA_cov1 : forall args z, op_cov1 OPSA HEAP_ID args z <-> cov1 HEAP_ID args z.
Proof. intros. reflexivity. Qed.
Lemma OPSA_cov1_heap : forall id args z, op_cov1 OPSA id args z -> id = HEAP_ID.
Proof. intros id args z [E _]. apply Uint63.eqb_correct in E. exact E. Qed.

Ltac ids id :=
  unfold OPSA, CtrSys.OPS in *; rewrite ?mk_holds, ?mk_fp in *; unfold comp_of in *;
  destruct (PrimInt63.eqb id 1%uint63) eqn:Q1;
  [| destruct (PrimInt63.eqb id 2%uint63) eqn:Q2;
     [| destruct (PrimInt63.eqb id 3%uint63) eqn:Q3;
        [| destruct (PrimInt63.eqb id 4%uint63) eqn:Q4;
           [| destruct (PrimInt63.eqb id 5%uint63) eqn:Q5;
              [| unfold extA, ext_asan in *;
                 destruct (PrimInt63.eqb id 7%uint63) eqn:Q7;
                 [| destruct (PrimInt63.eqb id 10%uint63) eqn:Q10;
                 [| destruct (PrimInt63.eqb id 11%uint63) eqn:Q11;
                    [| destruct (PrimInt63.eqb id 12%uint63) eqn:Q12;
                       [| destruct (PrimInt63.eqb id 13%uint63) eqn:Q13;
                          [| destruct (PrimInt63.eqb id 14%uint63) eqn:Q14;
                             [| destruct (PrimInt63.eqb id 15%uint63) eqn:Q15;
                                [| destruct (PrimInt63.eqb id 16%uint63) eqn:Q16;
                                   [| destruct (PrimInt63.eqb id 17%uint63) eqn:Q17]]]]]]]]]]]]].

Lemma OPSA_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPSA id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AIu2) a \/ (exists a', in_ranges (aci AIu2) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPSA id args m' mo.
Proof.
  intros id args m m' mo NI H AG WP. ids id.
  - exfalso. apply NI. apply Uint63.eqb_correct in Q1. exact Q1.
  - exact H.
  -
    destruct args as [|off [|n [|? ?]]]; cbn [oc_holds RSTAGE rstage_holds] in *; try exact H.
    destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
    rewrite <- (AG (RS3 + i)); [apply H3; exact Hi| unfold RS3, RS_LEN, two64 in *; lia|].
    constructor. cbn [fst snd]. unfold RS_LEN in *. lia.
  - exact H.
  - exact H.
  - exact (pool_agree args m m' mo AG H).
  - exact (shmap_pres args m m' mo H AG WP).
  - exact (zsh_pres args m m' mo H AG WP).
  - exact (ssh_pres args m m' mo H AG WP).
  - exact (zro_pres args m m' mo H AG WP).
  - exact (zarg_pres args m m' mo H AG WP).
  - exact (rstv_pres file args m m' mo H AG WP).
  - exact (zpb_pres args m m' mo H AG WP).
  - exact (gsh_pres args m m' mo H AG WP).
  - exact H.
Qed.

Lemma OPSA_fp_other3 : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) -> pres_set a.
Proof.
  intros id args a NI FP. ids id; cbn [oc_fp FD3 FD3DIR FDINIT oc_pure oc_true shmap_c ssh_c] in FP; try (apply Exists_nil in FP; destruct FP).
  - exfalso. apply NI. apply Uint63.eqb_correct in Q1. exact Q1.
  - cbn [oc_fp RSTAGE rstage_fp] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold RS3, RS_LEN in Ha.
    left. change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.msg_img_ranges, in_ranges. exists (0x10000, 0x22c60). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exact (pres2_set a (pool_fp_class args a FP)).
  - exact (pres2_set a (zsh_fp_class args a FP)).
  - exact (pres2_set a (zro_fp_class args a FP)).
  - exact (zarg_fp_class args a FP).
  - exact (pres2_set a (rstv_fp_class file args a FP)).
  - exact (pres2_set a (zpb_fp_class args a FP)).
  - exact (pres2_set a (gsh_fp_class args a FP)).
Qed.

Lemma OPSA_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  in_ranges (aci AIu2) a \/ (exists a', in_ranges (aci AIu2) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Proof. exact OPSA_fp_other3. Qed.

Lemma OPSA_fp_other2 : forall id args a, id <> HEAP_ID -> id <> StrRegC.StrRegC.ZARG_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  in_ranges (aci AIu2) a \/ exists a', in_ranges (aci AIu2) a' /\ a = shad a'.
Proof.
  intros id args a NI NZ FP. ids id; cbn [oc_fp FD3 FD3DIR FDINIT oc_pure oc_true shmap_c ssh_c] in FP; try (apply Exists_nil in FP; destruct FP).
  - exfalso. apply NI. apply Uint63.eqb_correct in Q1. exact Q1.
  - cbn [oc_fp RSTAGE rstage_fp] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold RS3, RS_LEN in Ha.
    left. change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.msg_img_ranges, in_ranges. exists (0x10000, 0x22c60). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exact (pool_fp_class args a FP).
  - exact (zsh_fp_class args a FP).
  - exact (zro_fp_class args a FP).
  - exfalso. apply NZ. apply Uint63.eqb_correct in Q14. exact Q14.
  - exact (rstv_fp_class file args a FP).
  - exact (zpb_fp_class args a FP).
  - exact (gsh_fp_class args a FP).
Qed.

Lemma OPSA_stk_sh_zero : forall id args m mo a, id <> HEAP_ID -> op_holds OPSA id args m mo ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) -> (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a') -> m (AM.wa a) = Some (Z_to_bv 8 0).
Proof.
  intros id args m mo a NI H FP STK.
  destruct (PrimInt63.eqb id StrRegC.StrRegC.ZARG_ID) eqn:QZ.
  - apply Uint63.eqb_correct in QZ. subst id. exact (zarg_fp_zero args m mo a H FP).
  - exfalso. apply Uint63.eqb_false_spec in QZ. exact (pres2_not_stk a (OPSA_fp_other2 id args a NI QZ FP) STK).
Qed.

Definition OTHERA (mo mo' : Model) : Prop := m_fds mo' = m_fds mo.
Lemma OPSA_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHERA mo mo' -> op_holds OPSA id args m mo -> op_holds OPSA id args m mo'.
Proof.
  intros id args m mo mo' NI OT H. unfold OTHERA in OT. ids id; try exact H.
  - exfalso. apply NI. apply Uint63.eqb_correct in Q1. exact Q1.
  - cbn [oc_holds FD3 oc_pure] in *. unfold fd3_holds in *. rewrite OT. exact H.
  - cbn [oc_holds FD3DIR oc_pure] in *. unfold fd3dir_holds in *. rewrite OT. exact H.
  - cbn [oc_holds FDINIT oc_pure] in *. unfold fdinit_holds in *. rewrite OT. exact H.
Qed.
Lemma OTHERA_refl : forall mo, OTHERA mo mo.
Proof. intros mo. reflexivity. Qed.

Lemma OPSA_holds_ssh : forall m mo, op_holds OPSA StackSh.SSH_ID [] m mo -> StackSh.ssh_holds m.
Proof. intros m mo H. exact H. Qed.
Lemma OPSA_holds_zro : forall m mo, op_holds OPSA RangeC.RangeC.ZRO_ID [] m mo -> LowImg.zro_holds m.
Proof. intros m mo H. exact H. Qed.
Lemma OPSA_holds_zpb : forall m mo, op_holds OPSA PubC.PubC.ZPB_ID [] m mo -> PubImg.zpb_holds m.
Proof. intros m mo H. exact H. Qed.
Lemma OPSA_holds_pool : forall args m mo, op_holds OPSA Pool.Pool.POOL_ID args m mo <-> Pool.Pool.pool_holds FLA asegs args m mo.
Proof. intros args m mo. reflexivity. Qed.
Lemma OPSA_fp_pool : forall args, op_fp OPSA Pool.Pool.POOL_ID args = Pool.Pool.pool_fp FLA args.
Proof. reflexivity. Qed.
Lemma OPSA_holds_gsh : forall m mo, op_holds OPSA GshC.GshC.GSH_ID [] m mo -> GshImg.gsh_holds GshC.GshC.GSH_TAB_ASAN m.
Proof. intros m mo H. exact H. Qed.
Lemma OPSA_holds_zarg : forall az m mo, op_holds OPSA StrRegC.StrRegC.ZARG_ID [az] m mo -> StrReg.zarg_holds az m.
Proof. intros az m mo H. exact (proj2 H). Qed.
Lemma OPSA_holds_zsh : forall m mo, op_holds OPSA (ReadC.ReadC.r_zsh ReadC.ReadC.CFG_ASAN) [] m mo -> ReadPre.zsh_holds m.
Proof. intros m mo H. exact H. Qed.
Lemma OPSA_holds_shmap : forall m mo, op_holds OPSA (UnreggC.UnreggC.u_shmap UnreggC.UnreggC.CFG_ASAN) [] m mo -> UnreggPre.shmap_holds m.
Proof. intros m mo H. exact H. Qed.
Lemma OPSA_holds_rstage : forall args m mo, op_holds OPSA ReadC.ReadC.RSTV_ID args m mo -> ReadPost.rstage_holds_v file args m.
Proof. intros args m mo H. exact H. Qed.
Lemma OPSA_holds_rstage' : forall args m mo, ReadPost.rstage_holds_v file args m -> op_holds OPSA ReadC.ReadC.RSTV_ID args m mo.
Proof. intros args m mo H. exact H. Qed.
Lemma OPSA_holds_fd3 : forall args m mo, op_holds OPSA CtrS.FD3_ID args m mo -> fd3_holds p1 file args mo.
Proof. intros args m mo H. exact H. Qed.
Lemma OPSA_holds_fd3' : forall args m mo, fd3_holds p1 file args mo -> op_holds OPSA CtrS.FD3_ID args m mo.
Proof. intros args m mo H. exact H. Qed.

Lemma OPSA_holds_fd3dir : forall args m mo, op_holds OPSA CtrS.FD3DIR_ID args m mo -> fd3dir_holds args mo.
Proof. intros args m mo H. exact H. Qed.

Lemma OPSA_fp_fd3 : forall args, op_fp OPSA CtrS.FD3_ID args = [].
Proof. reflexivity. Qed.
Lemma OPSA_fp_rstage : forall args args', op_fp OPSA ReadC.ReadC.RSTV_ID args = op_fp OPSA ReadC.ReadC.RSTV_ID args'.
Proof. reflexivity. Qed.
Lemma OPSA_fp_nostage : forall id args a, id <> ReadC.ReadC.RSTV_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  ~ (ReadPre.STAGE <= a < ReadPre.STAGE + 65536).
Proof.
  intros id args a NI FP IN. ids id; cbn [oc_fp FD3 FD3DIR FDINIT oc_pure oc_true shmap_c ssh_c] in FP; try (apply Exists_nil in FP; destruct FP).
  -
    cbn [oc_fp heapA] in FP. unfold heap_fp in FP. destruct (decode args) as [[[[md aw] ws] ca]|] eqn:D; [| apply Exists_nil in FP; destruct FP].
    assert (FP' : Exists (fun p => fst p <= a < snd p) (heap_fp IMGX args)) by (unfold heap_fp; rewrite D; exact FP).
    apply (proj1 (fp_spec IMGX args md aw ws ca a D)) in FP' as (_ & NX & _). exact (NX (IMGX_stage a IN)).
  - cbn [oc_fp RSTAGE rstage_fp] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold RS3, RS_LEN, ReadPre.STAGE in *. lia.
  - pose proof (pool_fp_hull args a FP) as PH. unfold ReadPre.STAGE in *. lia.
  - cbn [oc_fp zsh_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.ZSC_LO, ReadPre.ZSC_HI, ReadPre.STAGE in *. lia.
  - cbn [oc_fp zro_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold LowImg.ZRO_LO, LowImg.ZRO_HI, ReadPre.STAGE in *. lia.
  - apply (pres2_not_stk a); [| exact (zarg_fp_stk args a FP)].
    left. change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.msg_img_ranges, in_ranges. exists (0x5fc110, 0x60cc28). split; [cbn [In]; tauto| cbn [fst snd]; unfold ReadPre.STAGE in IN; lia].
  - exfalso. apply NI. apply Uint63.eqb_correct in Q15. exact Q15.
  - cbn [oc_fp zpb_c] in FP. apply Exists_exists in FP as (iv & Hiv & Ha). unfold PubImg.ZPBW in Hiv. cbn [In] in Hiv. unfold ReadPre.STAGE in *.
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Ha; lia.
  - cbn [oc_fp gsh_c] in FP. pose proof (gsh_hull a FP) as GH. unfold ReadPre.STAGE in *. lia.
Qed.

Hypothesis IMGX_pool : forall a, 0x60c160 <= a < 0x60c370 -> in_ivs IMGX a.
Lemma OPSA_fp_nopool : forall id args a, PrimInt63.eqb id Pool.Pool.POOL_ID = false -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  ~ (0x60c160 <= a < 0x60c370).
Proof.
  intros id args a NI FP IN. unfold Pool.Pool.POOL_ID in NI.
  ids id; cbn [oc_fp FD3 FD3DIR FDINIT oc_pure oc_true shmap_c ssh_c] in FP; try (apply Exists_nil in FP; destruct FP).
  -
    cbn [oc_fp heapA] in FP. unfold heap_fp in FP. destruct (decode args) as [[[[md aw] ws] ca]|] eqn:D; [| apply Exists_nil in FP; destruct FP].
    assert (FP' : Exists (fun p => fst p <= a < snd p) (heap_fp IMGX args)) by (unfold heap_fp; rewrite D; exact FP).
    apply (proj1 (fp_spec IMGX args md aw ws ca a D)) in FP' as (_ & NX & _). exact (NX (IMGX_pool a IN)).
  - cbn [oc_fp RSTAGE rstage_fp] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold RS3, RS_LEN in *. lia.
  - discriminate NI.
  - cbn [oc_fp zsh_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.ZSC_LO, ReadPre.ZSC_HI in *. lia.
  - cbn [oc_fp zro_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold LowImg.ZRO_LO, LowImg.ZRO_HI in *. lia.
  - apply (pres2_not_stk a); [| exact (zarg_fp_stk args a FP)].
    left. change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.msg_img_ranges, in_ranges. exists (0x5fc110, 0x60cc28). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - cbn [oc_fp rstv_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.STAGE in *. lia.
  - cbn [oc_fp zpb_c] in FP. apply Exists_exists in FP as (iv & Hiv & Ha). unfold PubImg.ZPBW in Hiv. cbn [In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Ha; lia.
  - cbn [oc_fp gsh_c] in FP. pose proof (gsh_hull a FP) as GH. lia.
Qed.
Lemma OPSA_others_pool : forall id args a, PrimInt63.eqb id Pool.Pool.POOL_ID = false -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  ~ (to_Z FLA <= a < to_Z FLA + 8) /\ ~ (to_Z FLA + 16 <= a < to_Z FLA + 528).
Proof. intros id args a NI FP. pose proof (OPSA_fp_nopool id args a NI FP) as N. change (to_Z FLA) with 6340960. split; intros X; apply N; lia. Qed.
Lemma OPSA_cov_pool : forall args a, ~ op_cov1 OPSA Pool.Pool.POOL_ID args a.
Proof. intros args a C. pose proof (OPSA_cov1_heap _ _ _ C) as X. discriminate X. Qed.

Lemma OPSA_fp_cases : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  0x10000 <= a < 0x20000 \/ ReadPre.ZSC_LO <= a < ReadPre.ZSC_HI \/ LowImg.ZRO_LO <= a < LowImg.ZRO_HI
  \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a') \/ ReadPre.STAGE <= a < ReadPre.STAGE + 65536 \/ 0x800b9828 <= a < 0x800bdca8
  \/ (id = 17%uint63 /\ 0x7fffc58c <= a < 0x7fffc66c) \/ 0x60c160 <= a < 0x60c370.
Proof.
  intros id args a NI FP. ids id; cbn [oc_fp FD3 FD3DIR FDINIT oc_pure oc_true shmap_c ssh_c] in FP; try (apply Exists_nil in FP; destruct FP).
  - exfalso. apply NI. apply Uint63.eqb_correct in Q1. exact Q1.
  - cbn [oc_fp RSTAGE rstage_fp] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold RS3, RS_LEN in Ha. left. lia.
  - do 7 right. exact (pool_fp_hull args a FP).
  - cbn [oc_fp zsh_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. right; left. exact Ha.
  - cbn [oc_fp zro_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. right; right; left. exact Ha.
  - right; right; right; left. exact (zarg_fp_stk args a FP).
  - cbn [oc_fp rstv_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. right; right; right; right; left. exact Ha.
  - cbn [oc_fp zpb_c] in FP. apply Exists_exists in FP as (iv & Hiv & Ha). unfold PubImg.ZPBW in Hiv. cbn [In] in Hiv. right; right; right; right; right; left.
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Ha; lia.
  - cbn [oc_fp gsh_c] in FP. right; right; right; right; right; right; left. split; [apply Uint63.eqb_correct; exact Q17| exact (gsh_hull a FP)].
Qed.
Lemma stk_sh_lo : forall a, (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a') -> 0x10006fef8000 <= a.
Proof.
  intros a (a' & R & ->). pose proof atop_range as ATR. unfold shad. rewrite Z.shiftr_div_pow2 by lia. unfold ASHOFF. Z.div_mod_to_equations; lia.
Qed.
Lemma OPSA_fp_errno : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) -> ~ (ReadPre.ERRNO <= a < ReadPre.ERRNO + 4).
Proof.
  intros id args a NI FP IN. destruct (OPSA_fp_cases id args a NI FP) as [C|[C|[C|[C|[C|[C|[[_ C]|C]]]]]]]; try apply stk_sh_lo in C;
    unfold ReadPre.ERRNO, ReadPre.ZSC_LO, ReadPre.ZSC_HI, LowImg.ZRO_LO, LowImg.ZRO_HI, ReadPre.STAGE in *; lia.
Qed.
Lemma OPSA_fp_mtx : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) -> ~ (0xd7370 <= a < 0xd7378).
Proof.
  intros id args a NI FP IN. destruct (OPSA_fp_cases id args a NI FP) as [C|[C|[C|[C|[C|[C|[[_ C]|C]]]]]]]; try apply stk_sh_lo in C;
    unfold ReadPre.ZSC_LO, ReadPre.ZSC_HI, LowImg.ZRO_LO, LowImg.ZRO_HI, ReadPre.STAGE in *; lia.
Qed.

Lemma OPSA_fp_shw : forall id args a, id <> HEAP_ID -> id <> UnreggC.UnreggC.GSH_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  ~ (UnreggPre.SH_LO <= a < UnreggPre.SH_HI) /\ ~ (UnreggPre.ASH_LO <= a < UnreggPre.ASH_HI).
Proof.
  intros id args a NI NG FP. destruct (OPSA_fp_cases id args a NI FP) as [C|[C|[C|[C|[C|[C|[[C _]|C]]]]]]]; [| | | | | | exfalso; exact (NG C) |]; try apply stk_sh_lo in C;
    unfold UnreggPre.SH_LO, UnreggPre.SH_HI, UnreggPre.ASH_LO, UnreggPre.ASH_HI, ReadPre.ZSC_LO, ReadPre.ZSC_HI, LowImg.ZRO_LO, LowImg.ZRO_HI, ReadPre.STAGE in *; lia.
Qed.
Lemma ACI_errno_u : exists iv0, In iv0 (aci AIu2) /\ fst iv0 <= ReadPre.ERRNO /\ ReadPre.ERRNO + 4 <= snd iv0.
Proof. exists (0x5fc110, 0x60cc28). split; [change (aci AIu2) with aci_I; unfold aci_I, AInstanceM.msg_img_ranges; cbn [In]; tauto| unfold ReadPre.ERRNO; cbn [fst snd]; lia]. Qed.

Lemma OPSA_fds_other : forall id args m mo f, id <> HEAP_ID -> CtrS.is_fd_op (OpI id []) = false -> op_holds OPSA id args m mo -> op_holds OPSA id args m (with_fds f mo).
Proof.
  intros id args m mo f NI NF H. unfold CtrS.is_fd_op in NF. cbn [op_id] in NF. apply orb_false_iff in NF as [NF N4]. apply orb_false_iff in NF as [N5 N2].
  change CtrS.FDINIT_ID with 5%uint63 in N5. change CtrS.FD3_ID with 2%uint63 in N2. change CtrS.FD3DIR_ID with 4%uint63 in N4.
  ids id; try exact H; try congruence.
  exfalso. apply NI. apply Uint63.eqb_correct in Q1. exact Q1.
Qed.
Lemma OPSA_minv_fds : forall mo f, op_minv OPSA mo -> op_minv OPSA (with_fds f mo).
Proof. intros mo f [H L]. split; [exact H| exact L]. Qed.

Lemma find_segment_lo : forall (sgs : list Segment) a n seg B,
  forallb (fun s => Z.leb B (Z.of_N (seg_base s))) sgs = true -> find_segment sgs a n = Some seg -> B <= a.
Proof.
  induction sgs as [|sg sgs IH]; intros a n seg B Hf H; cbn [find_segment] in H; [discriminate|].
  cbn [forallb] in Hf. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1.
  destruct (Z.leb (Z.of_N (seg_base sg)) a && Z.leb (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:Hc.
  - apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. lia.
  - exact (IH a n seg B H2 H).
Qed.

Lemma OPSA_minv : forall mo, op_minv OPSA mo -> m_halted mo = None.
Proof. intros mo [H _]. exact H. Qed.
Lemma OPSA_cov0_stk : forall a, ATOP <= a < 2 ^ 47 -> op_cov0 OPSA a.
Proof. intros a Ha. right. unfold two64. lia. Qed.
Lemma OPSA_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPSA a.
Proof.
  intros a [seg Hs]. left. split.
  - apply (find_segment_lo asegs a 1 seg 0x10000); [vm_compute; reflexivity| exact Hs].
  - destruct (Z_lt_le_dec a AIMG_HI) as [L|G]; [exact L|]. exfalso. rewrite (UnreggPre.no_seg_above a ltac:(unfold AIMG_HI in G; lia)) in Hs. discriminate Hs.
Qed.

Notation AWAx := (AWA AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake).

Hypothesis IMGX_cov : forall v a, In v IMGX -> in_iv v a -> C0 a \/ sh_cov a.

Theorem OPSA_cover_law : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.cover_law asegs OPSA.
Proof.
  split.
  - exact OPSA_cov0_img.
  - intros args m mo a HH Ha NFP.
    assert (HX : heap_holds asegs IMGX AWAx Cw args m mo) by exact HH.
    pose proof HX as (md & aw & ws & ca & LB & D & HA & WF & HC).
    assert (NFP' : ~ Exists (fun iv => fst iv <= a < snd iv) (heap_fp IMGX args)) by exact NFP.
    assert (CASES : in_ivs IMGX a \/ in_ws ws a).
    { destruct (in_ivs_b IMGX a) eqn:E1; [left; apply in_ivs_b_spec; exact E1|].
      destruct (in_ivs_b (map w_iv ws) a) eqn:E2; [right; unfold in_ws; apply in_ivs_b_spec; exact E2|]. exfalso. apply NFP'.
      apply (proj2 (fp_spec IMGX args md aw ws ca a D)). split; [exact Ha|]. split; intros X; apply in_ivs_b_spec in X; congruence. }
    assert (COV1 : forall z, in_ws (heap_ws ws) z \/ sh_cov z -> op_cov OPSA [(OPID, args)] z).
    { intros z Hz. right. constructor. apply (proj2 (OPSA_cov1 args z)). split; [reflexivity|]. exists md, aw, ws, ca. split; [exact D| exact Hz]. }
    destruct CASES as [IX|IW].
    + apply in_ivs_In in IX as (v & Hv & Hin). destruct (IMGX_cov v a Hv Hin) as [C|S]; [left; exact C| apply COV1; right; exact S].
    + unfold in_ws in IW. apply in_ivs_In in IW as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
      destruct (Z.eq_dec (w_kind w) K_STACK) as [KS|NK].
      * left. right. pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[_ CE]|[[KB _]|[KB _]]]);
          [| rewrite KS in KB; unfold K_BLOCK, K_STACK in KB; lia| rewrite KS in KB; unfold K_SUB, K_STACK in KB; lia].
        cbn [aw_ceiling AWA] in CE. unfold aw_ceiling_asan in CE. unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. lia.
      * apply COV1. left. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [exact Hw|].
        destruct (Z.eqb_spec (w_kind w) K_STACK); [contradiction| reflexivity].
Qed.

Lemma T_sem : forall id args m mo z, holdsT id args m mo ->
  semvA AIu2 ACCT UNIV id args m mo z ->
  ledgered id = true /\ (page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z)).
Proof.
  intros id args m mo z H S. pose proof S as [E _]. change OPID with 1%uint63 in E. pose proof E as E1. apply Uint63.eqb_correct in E1. subst id.
  split; [reflexivity|].
  refine (proj2 (H_semA AIu2 IMGX IMGX_aci ACCT COVP ACCT_cov UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake Cw
                   1%uint63 args m mo z _ S)).
  unfold holdsA. change (PrimInt63.eqb 1%uint63 OPID) with true. cbv iota. exact H.
Qed.

Theorem OPSA_acc_user_law : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.acc_user_law asegs IMGX AWAx OPSA.
Proof.
  intros os m mo acc MI HO HC.
  assert (HO' : Forall (fun o => holdsT (fst o) (snd o) m mo) os).
  { apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HO o Ho) as X. unfold OPSA, CtrSys.OPS in X. rewrite mk_holds in X. exact X. }
  destruct (asan_acc_user holdsT C0 cov1 COVP NMAX ledgered T_led T_cov T_mat
              (semvA AIu2 ACCT UNIV) T_sem os m mo acc MI HO') as (mo' & MA & MI' & HO2).
  { intros a n j Hin Hj. destruct (HC a n j Hin Hj) as [C|(args & md & aw & ws & ca & LB & Ho & D & HA & U)]; [left; exact C| right].
    apply Exists_exists. exists (OPID, args). split; [exact Ho|]. cbn [fst snd]. split; [reflexivity|].
    exists md, aw, ws, ca, LB. split; [exact D|]. split; [exact (aw_holdsA_plain AIu2 ACCT UNIV aw LB ws m mo HA)|].
    unfold in_user in U. apply in_ivs_In in U as (v & Hv & Hz). exists v. split; [exact Hv| left; exact Hz]. }
  exists mo'. split; [exact MA|]. split; [exact MI'|].
  apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HO2 o Ho) as X. unfold OPSA, CtrSys.OPS. rewrite mk_holds. exact X.
Qed.

Definition CHSAx (os : list oinst) (m : word -> option byte) (mo : Model) (z : Z) : Prop :=
  op_cov OPSA os z \/ Exists (fun o => semvA AIu2 ACCT UNIV (fst o) (snd o) m mo z) os.

Theorem OPSA_acc_user_lawA : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  op_minv OPSA mo -> Forall (fun o => op_holds OPSA (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> CHSAx os m mo (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPSA mo' /\
              Forall (fun o => op_holds OPSA (fst o) (snd o) m mo') os.
Proof.
  intros os m mo acc MI HO HC.
  assert (HO' : Forall (fun o => holdsT (fst o) (snd o) m mo) os).
  { apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HO o Ho) as X. unfold OPSA, CtrSys.OPS in X. rewrite mk_holds in X. exact X. }
  destruct (asan_acc_user holdsT C0 cov1 COVP NMAX ledgered T_led T_cov T_mat
              (semvA AIu2 ACCT UNIV) T_sem os m mo acc MI HO') as (mo' & MA & MI' & HO2).
  { intros a n j Hin Hj. destruct (HC a n j Hin Hj) as [C|S]; [left; exact C| right; exact S]. }
  exists mo'. split; [exact MA|]. split; [exact MI'|].
  apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HO2 o Ho) as X. unfold OPSA, CtrSys.OPS. rewrite mk_holds. exact X.
Qed.

Lemma op_cov_heap_OPSA : forall os z,
  op_cov (asan_heap_optable AIu2 IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake Cw) os z ->
  op_cov OPSA os z.
Proof.
  intros os z [C|E]; [left; exact C| right].
  apply Exists_exists in E as (o & Ho & C1). apply Exists_exists. exists o. split; [exact Ho|].
  pose proof C1 as [E1 _]. change OPID with HEAP_ID in E1. apply Uint63.eqb_correct in E1.
  destruct o as [id args]. cbn [fst snd] in *. subst id. apply (proj2 (OPSA_cov1 args z)). exact C1.
Qed.

Theorem OPSA_shlaw : forall os args md aw ws ca LB m mo cs c p,
  In (OPID, args) os -> decode args = Some (md, aw, ws, ca) ->
  aw_holds asegs IMGX AWAx aw LB ws m mo -> windows_wf ws LB (aw_ceiling asegs IMGX AWAx mo) ->
  Seal.Seal.seal_ok ws cs -> In c cs -> In (Inv.chunk_block c) LB ->
  (forall w, In w ws -> (w_kind w = K_BLOCK \/ K_GHOST <= w_kind w) -> forall a, in_iv (w_iv w) a -> ~ in_iv (Inv.chunk_block c) a) ->
  in_iv (Inv.chunk_block c) p ->
  m (Z_to_bv 64 (Seal.Seal.shadZ p)) = Some (Z_to_bv 8 0) /\ CHSAx os m mo (Seal.Seal.shadZ p).
Proof.
  intros os args md aw ws ca LB m mo cs c p Hos D HA WF SEAL Hc HLB APART INP.
  destruct (ShLaw.asan_shlaw AIu2 IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top (GlueA.wmono_ofA asegs) AIu_fake Cw
              os args md aw ws ca LB m mo cs c p Hos D HA WF SEAL Hc HLB APART INP) as [M CH].
  split; [exact M|]. destruct CH as [C|S]; [left; exact (op_cov_heap_OPSA _ _ C)| right; exact S].
Qed.

Hypothesis IMGX_shlit : forall v a, In v SHLIT -> fst v <= a < snd v -> in_ivs IMGX a.
Hypothesis IMGX_stksh : forall a', ATOP <= a' < 2 ^ 47 -> in_ivs IMGX (shad a').

Lemma seg_cover : forall (sgs : list Segment) lo hi,
  existsb (fun sg => (Z.of_N (seg_base sg) <=? lo) && (hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool sgs = true ->
  forall a, lo <= a < hi -> exists seg, find_segment sgs a 1 = Some seg.
Proof.
  induction sgs as [|sg sgs IH]; cbn [existsb find_segment]; intros lo hi H a Ha; [discriminate H|]. cbv zeta.
  destruct ((Z.of_N (seg_base sg) <=? a) && (a + 1 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:Q; [eexists; reflexivity|].
  apply orb_prop in H as [H|H]; [| exact (IH lo hi H a Ha)].
  exfalso. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. apply andb_false_iff in Q as [Q|Q]; [apply Z.leb_gt in Q| apply Z.leb_gt in Q]; lia.
Qed.

Theorem OPSA_ho_other_z : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  (exists seg, find_segment asegs a 1 = Some seg) \/ in_ivs IMGX a.
Proof.
  intros id args a NI FP. ids id; cbn [oc_fp FD3 FD3DIR FDINIT oc_pure oc_true shmap_c ssh_c] in FP; try (apply Exists_nil in FP; destruct FP).
  - exfalso. apply NI. apply Uint63.eqb_correct in Q1. exact Q1.
  -
    cbn [oc_fp RSTAGE rstage_fp] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold RS3, RS_LEN in Ha.
    left. apply (seg_cover asegs 0x10000 0x20000); [vm_compute; reflexivity| lia].
  -   left. apply (seg_cover asegs 0x60c160 0x60c370); [vm_compute; reflexivity| exact (pool_fp_hull args a FP)].
  -
    cbn [oc_fp zsh_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.ZSC_LO, ReadPre.ZSC_HI in Ha.
    right. apply (IMGX_shlit (0x800b7820, 0x800b9828) a); [apply STGSH_SHLIT; left; reflexivity| cbn [fst snd]; lia].
  -
    cbn [oc_fp zro_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold LowImg.ZRO_LO, LowImg.ZRO_HI in Ha.
    right. apply (IMGX_shlit (0x7fffa000, 0x7fffc66c) a); [apply IMGSH_SHLIT; left; reflexivity| cbn [fst snd]; lia].
  -   right. destruct (zarg_fp_stk args a FP) as (a' & R & ->). exact (IMGX_stksh a' R).
  -
    cbn [oc_fp rstv_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. right. exact (IMGX_stage a Ha).
  -
    cbn [oc_fp zpb_c] in FP. apply Exists_exists in FP as (iv & Hiv & Ha). right. exact (IMGX_shlit iv a (PUBSH_SHLIT iv Hiv) Ha).
  -
    cbn [oc_fp gsh_c] in FP. pose proof (gsh_hull a FP) as GH.
    right. apply (IMGX_shlit (0x7fffa000, 0x7fffc66c) a); [apply IMGSH_SHLIT; left; reflexivity| cbn [fst snd]; lia].
Qed.

Theorem OPSA_heap_ops : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.heap_ops asegs IMGX AWAx Cw OPSA.
Proof.
  constructor.
  - intros args m mo. reflexivity.
  - exact OPSA_fp1.
  - exact OPSA_ho_other_z.
  - exact OPSA_cover_law.
  - exact OPSA_acc_user_law.
Qed.

Lemma zpb_sh_wins_in : forall a, ShLoadLit.ShLoadLit.in_wins PubC.PubC.ZPB_SH_WINS a = true ->
  exists w, In w PubImg.ZPBW /\ fst w <= to_Z a < snd w.
Proof.
  intros a H. unfold ShLoadLit.ShLoadLit.in_wins, PubC.PubC.ZPB_SH_WINS in H. cbn [existsb fst snd] in H.
  rewrite !orb_true_iff, !andb_true_iff, !Uint63.leb_spec, !Uint63.ltb_spec in H.
  change (to_Z 2148243496%uint63) with 0x800b9828 in H. change (to_Z 2148243840%uint63) with 0x800b9980 in H.
  change (to_Z 2148243864%uint63) with 0x800b9998 in H. change (to_Z 2148260328%uint63) with 0x800bd9e8 in H.
  change (to_Z 2148260336%uint63) with 0x800bd9f0 in H. change (to_Z 2148260736%uint63) with 0x800bdb80 in H.
  change (to_Z 2148260744%uint63) with 0x800bdb88 in H. change (to_Z 2148261032%uint63) with 0x800bdca8 in H.
  change (to_Z 2148260869%uint63) with 0x800bdc05 in H. change (to_Z 2148260870%uint63) with 0x800bdc06 in H.
  unfold PubImg.ZPBW.
  destruct H as [H|[H|[H|[H|[H|H]]]]]; [| | | | | discriminate H].
  - exists (0x800b9828, 0x800b9980). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x800b9998, 0x800bd9e8). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x800bd9f0, 0x800bdb80). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x800bdb88, 0x800bdc05). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x800bdc06, 0x800bdca8). split; [cbn [In]; tauto| cbn [fst snd]; lia].
Qed.

Theorem OPSA_zpb_HZ : forall (os : list oinst) (m : word -> option byte) (mo : Model) (a : int),
  (forall id, In id PubC.PubC.ZPB_VIDS -> exists args, In (id, args) os /\ op_holds OPSA id args m mo) ->
  ShLoadLit.ShLoadLit.in_wins PubC.PubC.ZPB_SH_WINS a = true ->
  m (Z_to_bv 64 (to_Z a)) = Some (Z_to_bv 8 0) /\
  OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.chg_user asegs IMGX AWAx OPSA os m mo (to_Z a).
Proof.
  intros os m mo a V W. destruct (zpb_sh_wins_in a W) as (w & Hw & Ha).
  destruct (V 16%uint63 ltac:(left; reflexivity)) as (zargs & _ & H16).
  destruct (V 1%uint63 ltac:(right; left; reflexivity)) as (hargs & Hin1 & HH).
  split.
  - assert (ZH : PubImg.zpb_holds m) by exact H16.
    exact (proj1 (ZH (to_Z a) (ex_intro _ w (conj Hw Ha)))).
  - left. right. apply Exists_exists. exists (1%uint63, hargs). split; [exact Hin1|]. cbn [fst snd].
    apply (proj2 (OPSA_cov1 hargs (to_Z a))). split; [reflexivity|].
    assert (HX : heap_holds asegs IMGX AWAx Cw hargs m mo) by exact HH.
    destruct HX as (md & aw & ws & ca & LB & D & _). exists md, aw, ws, ca. split; [exact D|].
    right. right. exists w. split; [apply PUBSH_SHLIT; exact Hw| exact Ha].
Qed.

Theorem azpb_shload_sound : forall (MP : Model -> Prop) (PB : (int -> list byte) -> Prop)
  (HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'),
  forall pc, PlanSound.PlanS.contract_sound asegs OPSA MP PB (ShLoadLit.ShLoadLit.shloadlit_c asegs PubC.PubC.ZPB_VIDS PubC.PubC.ZPB_SH_WINS pc).
Proof.
  intros MP PB HMPA pc.
  exact (ShLoadLit.ShLoadLit.shloadlit_sound asegs OPSA PubC.PubC.ZPB_VIDS PubC.PubC.ZPB_SH_WINS
           (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.chg_user asegs IMGX AWAx OPSA) OPSA_acc_user_law OPSA_zpb_HZ MP PB HMPA pc).
Qed.

Lemma gsh_zero_wins_tab : forall w, In w GshC.GshC.GSH_ZERO_WINS_ASAN ->
  In (to_Z (fst w), to_Z (snd w) - to_Z (fst w), 0) GshC.GshC.GSH_TAB_ASAN /\ 0x7fffc58c <= to_Z (fst w) /\ to_Z (snd w) <= 0x7fffc66c.
Proof.
  intros w Hw.
  assert (C : forallb (fun w => (existsb (fun e => (fst (fst e) =? to_Z (fst w)) && (snd (fst e) =? to_Z (snd w) - to_Z (fst w)) && (snd e =? 0)) GshC.GshC.GSH_TAB_ASAN
                                && (0x7fffc58c <=? to_Z (fst w)) && (to_Z (snd w) <=? 0x7fffc66c))%bool) GshC.GshC.GSH_ZERO_WINS_ASAN = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) C w Hw) as Q. apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q Q2]. apply Z.leb_le in Q2, Q3.
  split; [| lia]. apply existsb_exists in Q as ([[a n] v] & He & QQ). cbn [fst snd] in QQ.
  apply andb_prop in QQ as [QQ E3]. apply andb_prop in QQ as [E1 E2]. apply Z.eqb_eq in E1, E2, E3. subst a n v. exact He.
Qed.

Theorem OPSA_gsh_HZ : forall (os : list oinst) (m : word -> option byte) (mo : Model) (a : int),
  (forall id, In id GshC.GshC.GSH_VIDS -> exists args, In (id, args) os /\ op_holds OPSA id args m mo) ->
  ShLoadLit.ShLoadLit.in_wins GshC.GshC.GSH_ZERO_WINS_ASAN a = true ->
  m (Z_to_bv 64 (to_Z a)) = Some (Z_to_bv 8 0) /\
  OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.chg_user asegs IMGX AWAx OPSA os m mo (to_Z a).
Proof.
  intros os m mo a V W. unfold ShLoadLit.ShLoadLit.in_wins in W. apply existsb_exists in W as (w & Hw & Q).
  apply andb_prop in Q as [Q1 Q2]. apply Uint63.leb_spec in Q1. apply Uint63.ltb_spec in Q2.
  destruct (gsh_zero_wins_tab w Hw) as (HT & B1 & B2).
  destruct (V 17%uint63 ltac:(left; reflexivity)) as (gargs & _ & H17).
  destruct (V 1%uint63 ltac:(right; left; reflexivity)) as (hargs & Hin1 & HH).
  split.
  - assert (GH : GshImg.gsh_holds GshC.GshC.GSH_TAB_ASAN m) by exact H17.
    pose proof (GH _ _ _ HT (to_Z a - to_Z (fst w)) ltac:(lia)) as X. unfold AM.wa in X.
    replace (to_Z (fst w) + (to_Z a - to_Z (fst w))) with (to_Z a) in X by lia. exact X.
  - left. right. apply Exists_exists. exists (1%uint63, hargs). split; [exact Hin1|]. cbn [fst snd].
    apply (proj2 (OPSA_cov1 hargs (to_Z a))). split; [reflexivity|].
    assert (HX : heap_holds asegs IMGX AWAx Cw hargs m mo) by exact HH.
    destruct HX as (md & aw & ws & ca & LB & D & _). exists md, aw, ws, ca. split; [exact D|].
    right. right. exists (0x7fffa000, 0x7fffc66c). split; [apply IMGSH_SHLIT; left; reflexivity| cbn [fst snd]; lia].
Qed.

Theorem agsh_shload_sound : forall (MP : Model -> Prop) (PB : (int -> list byte) -> Prop)
  (HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'),
  forall pc, PlanSound.PlanS.contract_sound asegs OPSA MP PB (ShLoadLit.ShLoadLit.shloadlit_c asegs GshC.GshC.GSH_VIDS GshC.GshC.GSH_ZERO_WINS_ASAN pc).
Proof.
  intros MP PB HMPA pc.
  exact (ShLoadLit.ShLoadLit.shloadlit_sound asegs OPSA GshC.GshC.GSH_VIDS GshC.GshC.GSH_ZERO_WINS_ASAN
           (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.chg_user asegs IMGX AWAx OPSA) OPSA_acc_user_law OPSA_gsh_HZ MP PB HMPA pc).
Qed.
End Run.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AInstanceM.TwinB AInstanceU.TwinB.
Import AMalloc_iface2.TwinB AInstanceU2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Ops OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.CtrSys.
Import Ledger.TwinB Op.TwinB.
Import AsanOps.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 St Ops CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Local Notation AIu2 := (AInstanceU2.TwinB.AIu2 ExhFirst.TwinB.exh_first).
Local Notation AIu_fake := (FakeLaw.TwinB.AIu_fake ExhFirst.TwinB.exh_first).
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Section Run.
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
Variables p1 file : list byte.

Hypothesis IMGX_stage : forall a, ReadPre.TwinB.STAGE <= a < ReadPre.TwinB.STAGE + 65536 -> in_ivs IMGX a.

Definition heapA : opcomp :=
  OpComp (heap_holdsA AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake Cw) (heap_fp IMGX)
         (fun args m m' mo AG DM H => heap_frameA AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake Cw args m m' mo AG DM H).

Definition RS3 : Z := 0x10000.
Lemma RS3_range : 0 <= RS3 /\ RS3 + 65536 <= two64.
Proof. unfold RS3, two64. lia. Qed.

Definition extA : int -> opcomp := ext_asan file.
Definition holdsT : int -> list word -> (word -> option byte) -> Model -> Prop :=
  comp_holds heapA (FD3 p1 file) (RSTAGE file RS3 RS3_range) FD3DIR FDINIT extA.

Definition ledgered (id : int) : bool := PrimInt63.eqb id 1%uint63.

Lemma T_led : forall id args m mo, ledgered id = true -> holdsT id args m mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Proof.
  intros id args m mo L H. unfold ledgered in L. apply Uint63.eqb_correct in L. subst id.
  exact (H_ledA AIu2 IMGX IMGX_aci ACCT COVP NMAX ACCT_led UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake Cw 1%uint63 args m mo eq_refl H).
Qed.

Lemma T_cov : forall id args m mo z, holdsT id args m mo -> cov1 id args z ->
  ledgered id = true /\ (page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z)).
Proof.
  intros id args m mo z H C. pose proof C as [E _]. change OPID with 1%uint63 in E. pose proof E as E1. apply Uint63.eqb_correct in E1. subst id.
  split; [reflexivity|].
  exact (proj2 (H_covA AIu2 IMGX IMGX_aci ACCT COVP ACCT_cov ACCT_cov_sh UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake Cw 1%uint63 args m mo z H C)).
Qed.

Lemma same_but_mat_fds : forall mo mo', same_but_mat mo mo' -> m_fds mo' = m_fds mo.
Proof. intros mo mo' ->. destruct mo as [fd [mp lzz mt] io fs pr lm tm]. reflexivity. Qed.

Lemma T_mat : forall id args m mo mo', holdsT id args m mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  holdsT id args m mo'.
Proof.
  intros id args m mo mo' H SB ND NEW. unfold holdsT, comp_holds, comp_of in *.
  destruct (PrimInt63.eqb id 1%uint63) eqn:Q1.
  { apply Uint63.eqb_correct in Q1. subst id. exact (H_matA AIu2 IMGX IMGX_aci ACCT COVP ACCT_mat UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake Cw 1%uint63 args m mo mo' H SB ND NEW). }
  pose proof (same_but_mat_fds mo mo' SB) as FDS.
  destruct (PrimInt63.eqb id 2%uint63). { cbn [oc_holds FD3 oc_pure] in *. unfold fd3_holds in *. rewrite FDS. exact H. }
  destruct (PrimInt63.eqb id 3%uint63). { exact H. }
  destruct (PrimInt63.eqb id 4%uint63). { cbn [oc_holds FD3DIR oc_pure] in *. unfold fd3dir_holds in *. rewrite FDS. exact H. }
  destruct (PrimInt63.eqb id 5%uint63). { cbn [oc_holds FDINIT oc_pure] in *. unfold fdinit_holds in *. rewrite FDS. exact H. }
  unfold extA, ext_asan in *.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; exact H.
Qed.

Definition asan_tm : tab_model heapA (FD3 p1 file) (RSTAGE file RS3 RS3_range) FD3DIR FDINIT extA :=
  TabModel heapA (FD3 p1 file) (RSTAGE file RS3 RS3_range) FD3DIR FDINIT extA
           (asan_minv C0) C0 cov1 (asan_minv_halted C0)
           (asan_acc holdsT C0 cov1 COVP NMAX ledgered T_led T_cov T_mat).

Definition OPSA : optable := CtrSys.OPS heapA extA p1 file RS3 RS3_range asan_tm.

Lemma OPSA_holds1 : forall args m mo, op_holds OPSA HEAP_ID args m mo <-> heap_holdsX AIu2 ACCT UNIV Cw args m mo.
Proof.
  intros args m mo. split; intros H.
  - exact (heap_holdsA_inv AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake Cw args m mo H).
  - exact (heap_holdsA_intro AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake Cw args m mo H).
Qed.
Lemma OPSA_fp1 : forall args, op_fp OPSA HEAP_ID args = heap_fp IMGX args.
Proof. reflexivity. Qed.
Lemma OPSA_cov1 : forall args z, op_cov1 OPSA HEAP_ID args z <-> cov1 HEAP_ID args z.
Proof. intros. reflexivity. Qed.
Lemma OPSA_cov1_heap : forall id args z, op_cov1 OPSA id args z -> id = HEAP_ID.
Proof. intros id args z [E _]. apply Uint63.eqb_correct in E. exact E. Qed.

Ltac ids id :=
  unfold OPSA, CtrSys.OPS in *; rewrite ?mk_holds, ?mk_fp in *; unfold comp_of in *;
  destruct (PrimInt63.eqb id 1%uint63) eqn:Q1;
  [| destruct (PrimInt63.eqb id 2%uint63) eqn:Q2;
     [| destruct (PrimInt63.eqb id 3%uint63) eqn:Q3;
        [| destruct (PrimInt63.eqb id 4%uint63) eqn:Q4;
           [| destruct (PrimInt63.eqb id 5%uint63) eqn:Q5;
              [| unfold extA, ext_asan in *;
                 destruct (PrimInt63.eqb id 7%uint63) eqn:Q7;
                 [| destruct (PrimInt63.eqb id 10%uint63) eqn:Q10;
                 [| destruct (PrimInt63.eqb id 11%uint63) eqn:Q11;
                    [| destruct (PrimInt63.eqb id 12%uint63) eqn:Q12;
                       [| destruct (PrimInt63.eqb id 13%uint63) eqn:Q13;
                          [| destruct (PrimInt63.eqb id 14%uint63) eqn:Q14;
                             [| destruct (PrimInt63.eqb id 15%uint63) eqn:Q15;
                                [| destruct (PrimInt63.eqb id 16%uint63) eqn:Q16;
                                   [| destruct (PrimInt63.eqb id 17%uint63) eqn:Q17]]]]]]]]]]]]].

Lemma OPSA_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPSA id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AIu2) a \/ (exists a', in_ranges (aci AIu2) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPSA id args m' mo.
Proof.
  intros id args m m' mo NI H AG WP. ids id.
  - exfalso. apply NI. apply Uint63.eqb_correct in Q1. exact Q1.
  - exact H.
  -
    destruct args as [|off [|n [|? ?]]]; cbn [oc_holds RSTAGE rstage_holds] in *; try exact H.
    destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
    rewrite <- (AG (RS3 + i)); [apply H3; exact Hi| unfold RS3, RS_LEN, two64 in *; lia|].
    constructor. cbn [fst snd]. unfold RS_LEN in *. lia.
  - exact H.
  - exact H.
  - exact (pool_agree args m m' mo AG H).
  - exact (shmap_pres args m m' mo H AG WP).
  - exact (zsh_pres args m m' mo H AG WP).
  - exact (ssh_pres args m m' mo H AG WP).
  - exact (zro_pres args m m' mo H AG WP).
  - exact (zarg_pres args m m' mo H AG WP).
  - exact (rstv_pres file args m m' mo H AG WP).
  - exact (zpb_pres args m m' mo H AG WP).
  - exact (gsh_pres args m m' mo H AG WP).
  - exact H.
Qed.

Lemma OPSA_fp_other3 : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) -> pres_set a.
Proof.
  intros id args a NI FP. ids id; cbn [oc_fp FD3 FD3DIR FDINIT oc_pure oc_true shmap_c ssh_c] in FP; try (apply Exists_nil in FP; destruct FP).
  - exfalso. apply NI. apply Uint63.eqb_correct in Q1. exact Q1.
  - cbn [oc_fp RSTAGE rstage_fp] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold RS3, RS_LEN in Ha.
    left. change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.TwinB.msg_img_ranges, in_ranges. exists (0x10000, 0x22d00). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exact (pres2_set a (pool_fp_class args a FP)).
  - exact (pres2_set a (zsh_fp_class args a FP)).
  - exact (pres2_set a (zro_fp_class args a FP)).
  - exact (zarg_fp_class args a FP).
  - exact (pres2_set a (rstv_fp_class file args a FP)).
  - exact (pres2_set a (zpb_fp_class args a FP)).
  - exact (pres2_set a (gsh_fp_class args a FP)).
Qed.

Lemma OPSA_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  in_ranges (aci AIu2) a \/ (exists a', in_ranges (aci AIu2) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Proof. exact OPSA_fp_other3. Qed.

Lemma OPSA_fp_other2 : forall id args a, id <> HEAP_ID -> id <> StrRegC.TwinB.StrRegC.ZARG_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  in_ranges (aci AIu2) a \/ exists a', in_ranges (aci AIu2) a' /\ a = shad a'.
Proof.
  intros id args a NI NZ FP. ids id; cbn [oc_fp FD3 FD3DIR FDINIT oc_pure oc_true shmap_c ssh_c] in FP; try (apply Exists_nil in FP; destruct FP).
  - exfalso. apply NI. apply Uint63.eqb_correct in Q1. exact Q1.
  - cbn [oc_fp RSTAGE rstage_fp] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold RS3, RS_LEN in Ha.
    left. change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.TwinB.msg_img_ranges, in_ranges. exists (0x10000, 0x22d00). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exact (pool_fp_class args a FP).
  - exact (zsh_fp_class args a FP).
  - exact (zro_fp_class args a FP).
  - exfalso. apply NZ. apply Uint63.eqb_correct in Q14. exact Q14.
  - exact (rstv_fp_class file args a FP).
  - exact (zpb_fp_class args a FP).
  - exact (gsh_fp_class args a FP).
Qed.

Lemma OPSA_stk_sh_zero : forall id args m mo a, id <> HEAP_ID -> op_holds OPSA id args m mo ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) -> (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a') -> m (AM.wa a) = Some (Z_to_bv 8 0).
Proof.
  intros id args m mo a NI H FP STK.
  destruct (PrimInt63.eqb id StrRegC.TwinB.StrRegC.ZARG_ID) eqn:QZ.
  - apply Uint63.eqb_correct in QZ. subst id. exact (zarg_fp_zero args m mo a H FP).
  - exfalso. apply Uint63.eqb_false_spec in QZ. exact (pres2_not_stk a (OPSA_fp_other2 id args a NI QZ FP) STK).
Qed.

Definition OTHERA (mo mo' : Model) : Prop := m_fds mo' = m_fds mo.
Lemma OPSA_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHERA mo mo' -> op_holds OPSA id args m mo -> op_holds OPSA id args m mo'.
Proof.
  intros id args m mo mo' NI OT H. unfold OTHERA in OT. ids id; try exact H.
  - exfalso. apply NI. apply Uint63.eqb_correct in Q1. exact Q1.
  - cbn [oc_holds FD3 oc_pure] in *. unfold fd3_holds in *. rewrite OT. exact H.
  - cbn [oc_holds FD3DIR oc_pure] in *. unfold fd3dir_holds in *. rewrite OT. exact H.
  - cbn [oc_holds FDINIT oc_pure] in *. unfold fdinit_holds in *. rewrite OT. exact H.
Qed.
Lemma OTHERA_refl : forall mo, OTHERA mo mo.
Proof. intros mo. reflexivity. Qed.

Lemma OPSA_holds_ssh : forall m mo, op_holds OPSA StackSh.TwinB.SSH_ID [] m mo -> StackSh.TwinB.ssh_holds m.
Proof. intros m mo H. exact H. Qed.
Lemma OPSA_holds_zro : forall m mo, op_holds OPSA RangeC.TwinB.RangeC.ZRO_ID [] m mo -> LowImg.TwinB.zro_holds m.
Proof. intros m mo H. exact H. Qed.
Lemma OPSA_holds_zpb : forall m mo, op_holds OPSA PubC.TwinB.PubC.ZPB_ID [] m mo -> PubImg.TwinB.zpb_holds m.
Proof. intros m mo H. exact H. Qed.
Lemma OPSA_holds_pool : forall args m mo, op_holds OPSA Pool.Pool.POOL_ID args m mo <-> Pool.Pool.pool_holds FLA bsegs args m mo.
Proof. intros args m mo. reflexivity. Qed.
Lemma OPSA_fp_pool : forall args, op_fp OPSA Pool.Pool.POOL_ID args = Pool.Pool.pool_fp FLA args.
Proof. reflexivity. Qed.
Lemma OPSA_holds_gsh : forall m mo, op_holds OPSA GshC.TwinB.GshC.GSH_ID [] m mo -> GshImg.TwinB.gsh_holds GshC.TwinB.GshC.GSH_TAB_ASAN m.
Proof. intros m mo H. exact H. Qed.
Lemma OPSA_holds_zarg : forall az m mo, op_holds OPSA StrRegC.TwinB.StrRegC.ZARG_ID [az] m mo -> StrReg.TwinB.zarg_holds az m.
Proof. intros az m mo H. exact (proj2 H). Qed.
Lemma OPSA_holds_zsh : forall m mo, op_holds OPSA (ReadC.TwinB.ReadC.r_zsh ReadC.TwinB.ReadC.CFG_ASAN) [] m mo -> ReadPre.TwinB.zsh_holds m.
Proof. intros m mo H. exact H. Qed.
Lemma OPSA_holds_shmap : forall m mo, op_holds OPSA (UnreggC.TwinB.UnreggC.u_shmap UnreggC.TwinB.UnreggC.CFG_ASAN) [] m mo -> UnreggPre.TwinB.shmap_holds m.
Proof. intros m mo H. exact H. Qed.
Lemma OPSA_holds_rstage : forall args m mo, op_holds OPSA ReadC.TwinB.ReadC.RSTV_ID args m mo -> ReadPost.TwinB.rstage_holds_v file args m.
Proof. intros args m mo H. exact H. Qed.
Lemma OPSA_holds_rstage' : forall args m mo, ReadPost.TwinB.rstage_holds_v file args m -> op_holds OPSA ReadC.TwinB.ReadC.RSTV_ID args m mo.
Proof. intros args m mo H. exact H. Qed.
Lemma OPSA_holds_fd3 : forall args m mo, op_holds OPSA CtrS.FD3_ID args m mo -> fd3_holds p1 file args mo.
Proof. intros args m mo H. exact H. Qed.
Lemma OPSA_holds_fd3' : forall args m mo, fd3_holds p1 file args mo -> op_holds OPSA CtrS.FD3_ID args m mo.
Proof. intros args m mo H. exact H. Qed.

Lemma OPSA_holds_fd3dir : forall args m mo, op_holds OPSA CtrS.FD3DIR_ID args m mo -> fd3dir_holds args mo.
Proof. intros args m mo H. exact H. Qed.

Lemma OPSA_fp_fd3 : forall args, op_fp OPSA CtrS.FD3_ID args = [].
Proof. reflexivity. Qed.
Lemma OPSA_fp_rstage : forall args args', op_fp OPSA ReadC.TwinB.ReadC.RSTV_ID args = op_fp OPSA ReadC.TwinB.ReadC.RSTV_ID args'.
Proof. reflexivity. Qed.
Lemma OPSA_fp_nostage : forall id args a, id <> ReadC.TwinB.ReadC.RSTV_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  ~ (ReadPre.TwinB.STAGE <= a < ReadPre.TwinB.STAGE + 65536).
Proof.
  intros id args a NI FP IN. ids id; cbn [oc_fp FD3 FD3DIR FDINIT oc_pure oc_true shmap_c ssh_c] in FP; try (apply Exists_nil in FP; destruct FP).
  -
    cbn [oc_fp heapA] in FP. unfold heap_fp in FP. destruct (decode args) as [[[[md aw] ws] ca]|] eqn:D; [| apply Exists_nil in FP; destruct FP].
    assert (FP' : Exists (fun p => fst p <= a < snd p) (heap_fp IMGX args)) by (unfold heap_fp; rewrite D; exact FP).
    apply (proj1 (fp_spec IMGX args md aw ws ca a D)) in FP' as (_ & NX & _). exact (NX (IMGX_stage a IN)).
  - cbn [oc_fp RSTAGE rstage_fp] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold RS3, RS_LEN, ReadPre.TwinB.STAGE in *. lia.
  - pose proof (pool_fp_hull args a FP) as PH. unfold ReadPre.TwinB.STAGE in *. lia.
  - cbn [oc_fp zsh_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.TwinB.ZSC_LO, ReadPre.TwinB.ZSC_HI, ReadPre.TwinB.STAGE in *. lia.
  - cbn [oc_fp zro_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI, ReadPre.TwinB.STAGE in *. lia.
  - apply (pres2_not_stk a); [| exact (zarg_fp_stk args a FP)].
    left. change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.TwinB.msg_img_ranges, in_ranges. exists (0x5fe2d0, 0x60ede8). split; [cbn [In]; tauto| cbn [fst snd]; unfold ReadPre.TwinB.STAGE in IN; lia].
  - exfalso. apply NI. apply Uint63.eqb_correct in Q15. exact Q15.
  - cbn [oc_fp zpb_c] in FP. apply Exists_exists in FP as (iv & Hiv & Ha). unfold PubImg.TwinB.ZPBW in Hiv. cbn [In] in Hiv. unfold ReadPre.TwinB.STAGE in *.
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Ha; lia.
  - cbn [oc_fp gsh_c] in FP. pose proof (gsh_hull a FP) as GH. unfold ReadPre.TwinB.STAGE in *. lia.
Qed.

Hypothesis IMGX_pool : forall a, 0x60e320 <= a < 0x60e530 -> in_ivs IMGX a.
Lemma OPSA_fp_nopool : forall id args a, PrimInt63.eqb id Pool.Pool.POOL_ID = false -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  ~ (0x60e320 <= a < 0x60e530).
Proof.
  intros id args a NI FP IN. unfold Pool.Pool.POOL_ID in NI.
  ids id; cbn [oc_fp FD3 FD3DIR FDINIT oc_pure oc_true shmap_c ssh_c] in FP; try (apply Exists_nil in FP; destruct FP).
  -
    cbn [oc_fp heapA] in FP. unfold heap_fp in FP. destruct (decode args) as [[[[md aw] ws] ca]|] eqn:D; [| apply Exists_nil in FP; destruct FP].
    assert (FP' : Exists (fun p => fst p <= a < snd p) (heap_fp IMGX args)) by (unfold heap_fp; rewrite D; exact FP).
    apply (proj1 (fp_spec IMGX args md aw ws ca a D)) in FP' as (_ & NX & _). exact (NX (IMGX_pool a IN)).
  - cbn [oc_fp RSTAGE rstage_fp] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold RS3, RS_LEN in *. lia.
  - discriminate NI.
  - cbn [oc_fp zsh_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.TwinB.ZSC_LO, ReadPre.TwinB.ZSC_HI in *. lia.
  - cbn [oc_fp zro_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI in *. lia.
  - apply (pres2_not_stk a); [| exact (zarg_fp_stk args a FP)].
    left. change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.TwinB.msg_img_ranges, in_ranges. exists (0x5fe2d0, 0x60ede8). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - cbn [oc_fp rstv_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.TwinB.STAGE in *. lia.
  - cbn [oc_fp zpb_c] in FP. apply Exists_exists in FP as (iv & Hiv & Ha). unfold PubImg.TwinB.ZPBW in Hiv. cbn [In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Ha; lia.
  - cbn [oc_fp gsh_c] in FP. pose proof (gsh_hull a FP) as GH. lia.
Qed.
Lemma OPSA_others_pool : forall id args a, PrimInt63.eqb id Pool.Pool.POOL_ID = false -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  ~ (to_Z FLA <= a < to_Z FLA + 8) /\ ~ (to_Z FLA + 16 <= a < to_Z FLA + 528).
Proof. intros id args a NI FP. pose proof (OPSA_fp_nopool id args a NI FP) as N. change (to_Z FLA) with 6349600. split; intros X; apply N; lia. Qed.
Lemma OPSA_cov_pool : forall args a, ~ op_cov1 OPSA Pool.Pool.POOL_ID args a.
Proof. intros args a C. pose proof (OPSA_cov1_heap _ _ _ C) as X. discriminate X. Qed.

Lemma OPSA_fp_cases : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  0x10000 <= a < 0x20000 \/ ReadPre.TwinB.ZSC_LO <= a < ReadPre.TwinB.ZSC_HI \/ LowImg.TwinB.ZRO_LO <= a < LowImg.TwinB.ZRO_HI
  \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a') \/ ReadPre.TwinB.STAGE <= a < ReadPre.TwinB.STAGE + 65536 \/ 0x800b9c60 <= a < 0x800be0e0
  \/ (id = 17%uint63 /\ 0x7fffc5a0 <= a < 0x7fffc6a0) \/ 0x60e320 <= a < 0x60e530.
Proof.
  intros id args a NI FP. ids id; cbn [oc_fp FD3 FD3DIR FDINIT oc_pure oc_true shmap_c ssh_c] in FP; try (apply Exists_nil in FP; destruct FP).
  - exfalso. apply NI. apply Uint63.eqb_correct in Q1. exact Q1.
  - cbn [oc_fp RSTAGE rstage_fp] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold RS3, RS_LEN in Ha. left. lia.
  - do 7 right. exact (pool_fp_hull args a FP).
  - cbn [oc_fp zsh_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. right; left. exact Ha.
  - cbn [oc_fp zro_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. right; right; left. exact Ha.
  - right; right; right; left. exact (zarg_fp_stk args a FP).
  - cbn [oc_fp rstv_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. right; right; right; right; left. exact Ha.
  - cbn [oc_fp zpb_c] in FP. apply Exists_exists in FP as (iv & Hiv & Ha). unfold PubImg.TwinB.ZPBW in Hiv. cbn [In] in Hiv. right; right; right; right; right; left.
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Ha; lia.
  - cbn [oc_fp gsh_c] in FP. right; right; right; right; right; right; left. split; [apply Uint63.eqb_correct; exact Q17| exact (gsh_hull a FP)].
Qed.
Lemma stk_sh_lo : forall a, (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a') -> 0x10006fef8000 <= a.
Proof.
  intros a (a' & R & ->). pose proof atop_range as ATR. unfold shad. rewrite Z.shiftr_div_pow2 by lia. unfold ASHOFF. Z.div_mod_to_equations; lia.
Qed.
Lemma OPSA_fp_errno : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) -> ~ (ReadPre.TwinB.ERRNO <= a < ReadPre.TwinB.ERRNO + 4).
Proof.
  intros id args a NI FP IN. destruct (OPSA_fp_cases id args a NI FP) as [C|[C|[C|[C|[C|[C|[[_ C]|C]]]]]]]; try apply stk_sh_lo in C;
    unfold ReadPre.TwinB.ERRNO, ReadPre.TwinB.ZSC_LO, ReadPre.TwinB.ZSC_HI, LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI, ReadPre.TwinB.STAGE in *; lia.
Qed.
Lemma OPSA_fp_mtx : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) -> ~ (0xd9530 <= a < 0xd9538).
Proof.
  intros id args a NI FP IN. destruct (OPSA_fp_cases id args a NI FP) as [C|[C|[C|[C|[C|[C|[[_ C]|C]]]]]]]; try apply stk_sh_lo in C;
    unfold ReadPre.TwinB.ZSC_LO, ReadPre.TwinB.ZSC_HI, LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI, ReadPre.TwinB.STAGE in *; lia.
Qed.

Lemma OPSA_fp_shw : forall id args a, id <> HEAP_ID -> id <> UnreggC.TwinB.UnreggC.GSH_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  ~ (UnreggPre.TwinB.SH_LO <= a < UnreggPre.TwinB.SH_HI) /\ ~ (UnreggPre.TwinB.ASH_LO <= a < UnreggPre.TwinB.ASH_HI).
Proof.
  intros id args a NI NG FP. destruct (OPSA_fp_cases id args a NI FP) as [C|[C|[C|[C|[C|[C|[[C _]|C]]]]]]]; [| | | | | | exfalso; exact (NG C) |]; try apply stk_sh_lo in C;
    unfold UnreggPre.TwinB.SH_LO, UnreggPre.TwinB.SH_HI, UnreggPre.TwinB.ASH_LO, UnreggPre.TwinB.ASH_HI, ReadPre.TwinB.ZSC_LO, ReadPre.TwinB.ZSC_HI, LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI, ReadPre.TwinB.STAGE in *; lia.
Qed.
Lemma ACI_errno_u : exists iv0, In iv0 (aci AIu2) /\ fst iv0 <= ReadPre.TwinB.ERRNO /\ ReadPre.TwinB.ERRNO + 4 <= snd iv0.
Proof. exists (0x5fe2d0, 0x60ede8). split; [change (aci AIu2) with aci_I; unfold aci_I, AInstanceM.TwinB.msg_img_ranges; cbn [In]; tauto| unfold ReadPre.TwinB.ERRNO; cbn [fst snd]; lia]. Qed.

Lemma OPSA_fds_other : forall id args m mo f, id <> HEAP_ID -> CtrS.is_fd_op (OpI id []) = false -> op_holds OPSA id args m mo -> op_holds OPSA id args m (with_fds f mo).
Proof.
  intros id args m mo f NI NF H. unfold CtrS.is_fd_op in NF. cbn [op_id] in NF. apply orb_false_iff in NF as [NF N4]. apply orb_false_iff in NF as [N5 N2].
  change CtrS.FDINIT_ID with 5%uint63 in N5. change CtrS.FD3_ID with 2%uint63 in N2. change CtrS.FD3DIR_ID with 4%uint63 in N4.
  ids id; try exact H; try congruence.
  exfalso. apply NI. apply Uint63.eqb_correct in Q1. exact Q1.
Qed.
Lemma OPSA_minv_fds : forall mo f, op_minv OPSA mo -> op_minv OPSA (with_fds f mo).
Proof. intros mo f [H L]. split; [exact H| exact L]. Qed.

Lemma find_segment_lo : forall (sgs : list Segment) a n seg B,
  forallb (fun s => Z.leb B (Z.of_N (seg_base s))) sgs = true -> find_segment sgs a n = Some seg -> B <= a.
Proof.
  induction sgs as [|sg sgs IH]; intros a n seg B Hf H; cbn [find_segment] in H; [discriminate|].
  cbn [forallb] in Hf. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1.
  destruct (Z.leb (Z.of_N (seg_base sg)) a && Z.leb (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:Hc.
  - apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. lia.
  - exact (IH a n seg B H2 H).
Qed.

Lemma OPSA_minv : forall mo, op_minv OPSA mo -> m_halted mo = None.
Proof. intros mo [H _]. exact H. Qed.
Lemma OPSA_cov0_stk : forall a, ATOP <= a < 2 ^ 47 -> op_cov0 OPSA a.
Proof. intros a Ha. right. unfold two64. lia. Qed.
Lemma OPSA_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPSA a.
Proof.
  intros a [seg Hs]. left. split.
  - apply (find_segment_lo bsegs a 1 seg 0x10000); [vm_compute; reflexivity| exact Hs].
  - destruct (Z_lt_le_dec a AIMG_HI) as [L|G]; [exact L|]. exfalso. rewrite (UnreggPre.TwinB.no_seg_above a ltac:(unfold AIMG_HI in G; lia)) in Hs. discriminate Hs.
Qed.

Notation AWAx := (AWA AIu2 IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake).

Hypothesis IMGX_cov : forall v a, In v IMGX -> in_iv v a -> C0 a \/ sh_cov a.

Theorem OPSA_cover_law : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.cover_law bsegs OPSA.
Proof.
  split.
  - exact OPSA_cov0_img.
  - intros args m mo a HH Ha NFP.
    assert (HX : heap_holds bsegs IMGX AWAx Cw args m mo) by exact HH.
    pose proof HX as (md & aw & ws & ca & LB & D & HA & WF & HC).
    assert (NFP' : ~ Exists (fun iv => fst iv <= a < snd iv) (heap_fp IMGX args)) by exact NFP.
    assert (CASES : in_ivs IMGX a \/ in_ws ws a).
    { destruct (in_ivs_b IMGX a) eqn:E1; [left; apply in_ivs_b_spec; exact E1|].
      destruct (in_ivs_b (map w_iv ws) a) eqn:E2; [right; unfold in_ws; apply in_ivs_b_spec; exact E2|]. exfalso. apply NFP'.
      apply (proj2 (fp_spec IMGX args md aw ws ca a D)). split; [exact Ha|]. split; intros X; apply in_ivs_b_spec in X; congruence. }
    assert (COV1 : forall z, in_ws (heap_ws ws) z \/ sh_cov z -> op_cov OPSA [(OPID, args)] z).
    { intros z Hz. right. constructor. apply (proj2 (OPSA_cov1 args z)). split; [reflexivity|]. exists md, aw, ws, ca. split; [exact D| exact Hz]. }
    destruct CASES as [IX|IW].
    + apply in_ivs_In in IX as (v & Hv & Hin). destruct (IMGX_cov v a Hv Hin) as [C|S]; [left; exact C| apply COV1; right; exact S].
    + unfold in_ws in IW. apply in_ivs_In in IW as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
      destruct (Z.eq_dec (w_kind w) K_STACK) as [KS|NK].
      * left. right. pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[_ CE]|[[KB _]|[KB _]]]);
          [| rewrite KS in KB; unfold K_BLOCK, K_STACK in KB; lia| rewrite KS in KB; unfold K_SUB, K_STACK in KB; lia].
        cbn [aw_ceiling AWA] in CE. unfold aw_ceiling_asan in CE. unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. lia.
      * apply COV1. left. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [exact Hw|].
        destruct (Z.eqb_spec (w_kind w) K_STACK); [contradiction| reflexivity].
Qed.

Lemma T_sem : forall id args m mo z, holdsT id args m mo ->
  semvA AIu2 ACCT UNIV id args m mo z ->
  ledgered id = true /\ (page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z)).
Proof.
  intros id args m mo z H S. pose proof S as [E _]. change OPID with 1%uint63 in E. pose proof E as E1. apply Uint63.eqb_correct in E1. subst id.
  split; [reflexivity|].
  refine (proj2 (H_semA AIu2 IMGX IMGX_aci ACCT COVP ACCT_cov UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake Cw
                   1%uint63 args m mo z _ S)).
  unfold holdsA. change (PrimInt63.eqb 1%uint63 OPID) with true. cbv iota. exact H.
Qed.

Theorem OPSA_acc_user_law : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.acc_user_law bsegs IMGX AWAx OPSA.
Proof.
  intros os m mo acc MI HO HC.
  assert (HO' : Forall (fun o => holdsT (fst o) (snd o) m mo) os).
  { apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HO o Ho) as X. unfold OPSA, CtrSys.OPS in X. rewrite mk_holds in X. exact X. }
  destruct (asan_acc_user holdsT C0 cov1 COVP NMAX ledgered T_led T_cov T_mat
              (semvA AIu2 ACCT UNIV) T_sem os m mo acc MI HO') as (mo' & MA & MI' & HO2).
  { intros a n j Hin Hj. destruct (HC a n j Hin Hj) as [C|(args & md & aw & ws & ca & LB & Ho & D & HA & U)]; [left; exact C| right].
    apply Exists_exists. exists (OPID, args). split; [exact Ho|]. cbn [fst snd]. split; [reflexivity|].
    exists md, aw, ws, ca, LB. split; [exact D|]. split; [exact (aw_holdsA_plain AIu2 ACCT UNIV aw LB ws m mo HA)|].
    unfold in_user in U. apply in_ivs_In in U as (v & Hv & Hz). exists v. split; [exact Hv| left; exact Hz]. }
  exists mo'. split; [exact MA|]. split; [exact MI'|].
  apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HO2 o Ho) as X. unfold OPSA, CtrSys.OPS. rewrite mk_holds. exact X.
Qed.

Definition CHSAx (os : list oinst) (m : word -> option byte) (mo : Model) (z : Z) : Prop :=
  op_cov OPSA os z \/ Exists (fun o => semvA AIu2 ACCT UNIV (fst o) (snd o) m mo z) os.

Theorem OPSA_acc_user_lawA : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  op_minv OPSA mo -> Forall (fun o => op_holds OPSA (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> CHSAx os m mo (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPSA mo' /\
              Forall (fun o => op_holds OPSA (fst o) (snd o) m mo') os.
Proof.
  intros os m mo acc MI HO HC.
  assert (HO' : Forall (fun o => holdsT (fst o) (snd o) m mo) os).
  { apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HO o Ho) as X. unfold OPSA, CtrSys.OPS in X. rewrite mk_holds in X. exact X. }
  destruct (asan_acc_user holdsT C0 cov1 COVP NMAX ledgered T_led T_cov T_mat
              (semvA AIu2 ACCT UNIV) T_sem os m mo acc MI HO') as (mo' & MA & MI' & HO2).
  { intros a n j Hin Hj. destruct (HC a n j Hin Hj) as [C|S]; [left; exact C| right; exact S]. }
  exists mo'. split; [exact MA|]. split; [exact MI'|].
  apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HO2 o Ho) as X. unfold OPSA, CtrSys.OPS. rewrite mk_holds. exact X.
Qed.

Lemma op_cov_heap_OPSA : forall os z,
  op_cov (asan_heap_optable AIu2 IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake Cw) os z ->
  op_cov OPSA os z.
Proof.
  intros os z [C|E]; [left; exact C| right].
  apply Exists_exists in E as (o & Ho & C1). apply Exists_exists. exists o. split; [exact Ho|].
  pose proof C1 as [E1 _]. change OPID with HEAP_ID in E1. apply Uint63.eqb_correct in E1.
  destruct o as [id args]. cbn [fst snd] in *. subst id. apply (proj2 (OPSA_cov1 args z)). exact C1.
Qed.

Theorem OPSA_shlaw : forall os args md aw ws ca LB m mo cs c p,
  In (OPID, args) os -> decode args = Some (md, aw, ws, ca) ->
  aw_holds bsegs IMGX AWAx aw LB ws m mo -> windows_wf ws LB (aw_ceiling bsegs IMGX AWAx mo) ->
  Seal.Seal.seal_ok ws cs -> In c cs -> In (Inv.chunk_block c) LB ->
  (forall w, In w ws -> (w_kind w = K_BLOCK \/ K_GHOST <= w_kind w) -> forall a, in_iv (w_iv w) a -> ~ in_iv (Inv.chunk_block c) a) ->
  in_iv (Inv.chunk_block c) p ->
  m (Z_to_bv 64 (Seal.Seal.shadZ p)) = Some (Z_to_bv 8 0) /\ CHSAx os m mo (Seal.Seal.shadZ p).
Proof.
  intros os args md aw ws ca LB m mo cs c p Hos D HA WF SEAL Hc HLB APART INP.
  destruct (ShLaw.TwinB.asan_shlaw AIu2 IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AIu_fake Cw
              os args md aw ws ca LB m mo cs c p Hos D HA WF SEAL Hc HLB APART INP) as [M CH].
  split; [exact M|]. destruct CH as [C|S]; [left; exact (op_cov_heap_OPSA _ _ C)| right; exact S].
Qed.

Hypothesis IMGX_shlit : forall v a, In v SHLIT -> fst v <= a < snd v -> in_ivs IMGX a.
Hypothesis IMGX_stksh : forall a', ATOP <= a' < 2 ^ 47 -> in_ivs IMGX (shad a').

Lemma seg_cover : forall (sgs : list Segment) lo hi,
  existsb (fun sg => (Z.of_N (seg_base sg) <=? lo) && (hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool sgs = true ->
  forall a, lo <= a < hi -> exists seg, find_segment sgs a 1 = Some seg.
Proof.
  induction sgs as [|sg sgs IH]; cbn [existsb find_segment]; intros lo hi H a Ha; [discriminate H|]. cbv zeta.
  destruct ((Z.of_N (seg_base sg) <=? a) && (a + 1 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:Q; [eexists; reflexivity|].
  apply orb_prop in H as [H|H]; [| exact (IH lo hi H a Ha)].
  exfalso. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. apply andb_false_iff in Q as [Q|Q]; [apply Z.leb_gt in Q| apply Z.leb_gt in Q]; lia.
Qed.

Theorem OPSA_ho_other_z : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPSA id args) ->
  (exists seg, find_segment bsegs a 1 = Some seg) \/ in_ivs IMGX a.
Proof.
  intros id args a NI FP. ids id; cbn [oc_fp FD3 FD3DIR FDINIT oc_pure oc_true shmap_c ssh_c] in FP; try (apply Exists_nil in FP; destruct FP).
  - exfalso. apply NI. apply Uint63.eqb_correct in Q1. exact Q1.
  -
    cbn [oc_fp RSTAGE rstage_fp] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold RS3, RS_LEN in Ha.
    left. apply (seg_cover bsegs 0x10000 0x20000); [vm_compute; reflexivity| lia].
  -   left. apply (seg_cover bsegs 0x60e320 0x60e530); [vm_compute; reflexivity| exact (pool_fp_hull args a FP)].
  -
    cbn [oc_fp zsh_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.TwinB.ZSC_LO, ReadPre.TwinB.ZSC_HI in Ha.
    right. apply (IMGX_shlit (0x800b7c58, 0x800b9c60) a); [apply STGSH_SHLIT; left; reflexivity| cbn [fst snd]; lia].
  -
    cbn [oc_fp zro_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI in Ha.
    right. apply (IMGX_shlit (0x7fffa000, 0x7fffc6a0) a); [apply IMGSH_SHLIT; left; reflexivity| cbn [fst snd]; lia].
  -   right. destruct (zarg_fp_stk args a FP) as (a' & R & ->). exact (IMGX_stksh a' R).
  -
    cbn [oc_fp rstv_c] in FP. apply Exists_exists in FP as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. right. exact (IMGX_stage a Ha).
  -
    cbn [oc_fp zpb_c] in FP. apply Exists_exists in FP as (iv & Hiv & Ha). right. exact (IMGX_shlit iv a (PUBSH_SHLIT iv Hiv) Ha).
  -
    cbn [oc_fp gsh_c] in FP. pose proof (gsh_hull a FP) as GH.
    right. apply (IMGX_shlit (0x7fffa000, 0x7fffc6a0) a); [apply IMGSH_SHLIT; left; reflexivity| cbn [fst snd]; lia].
Qed.

Theorem OPSA_heap_ops : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.heap_ops bsegs IMGX AWAx Cw OPSA.
Proof.
  constructor.
  - intros args m mo. reflexivity.
  - exact OPSA_fp1.
  - exact OPSA_ho_other_z.
  - exact OPSA_cover_law.
  - exact OPSA_acc_user_law.
Qed.

Lemma zpb_sh_wins_in : forall a, ShLoadLit.ShLoadLit.in_wins PubC.TwinB.PubC.ZPB_SH_WINS a = true ->
  exists w, In w PubImg.TwinB.ZPBW /\ fst w <= to_Z a < snd w.
Proof.
  intros a H. unfold ShLoadLit.ShLoadLit.in_wins, PubC.TwinB.PubC.ZPB_SH_WINS in H. cbn [existsb fst snd] in H.
  rewrite !orb_true_iff, !andb_true_iff, !Uint63.leb_spec, !Uint63.ltb_spec in H.
  change (to_Z 2148244576%uint63) with 0x800b9c60 in H. change (to_Z 2148244920%uint63) with 0x800b9db8 in H.
  change (to_Z 2148244944%uint63) with 0x800b9dd0 in H. change (to_Z 2148261408%uint63) with 0x800bde20 in H.
  change (to_Z 2148261416%uint63) with 0x800bde28 in H. change (to_Z 2148261816%uint63) with 0x800bdfb8 in H.
  change (to_Z 2148261824%uint63) with 0x800bdfc0 in H. change (to_Z 2148262112%uint63) with 0x800be0e0 in H.
  change (to_Z 2148261949%uint63) with 0x800be03d in H. change (to_Z 2148261950%uint63) with 0x800be03e in H.
  unfold PubImg.TwinB.ZPBW.
  destruct H as [H|[H|[H|[H|[H|H]]]]]; [| | | | | discriminate H].
  - exists (0x800b9c60, 0x800b9db8). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x800b9dd0, 0x800bde20). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x800bde28, 0x800bdfb8). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x800bdfc0, 0x800be03d). split; [cbn [In]; tauto| cbn [fst snd]; lia].
  - exists (0x800be03e, 0x800be0e0). split; [cbn [In]; tauto| cbn [fst snd]; lia].
Qed.

Theorem OPSA_zpb_HZ : forall (os : list oinst) (m : word -> option byte) (mo : Model) (a : int),
  (forall id, In id PubC.TwinB.PubC.ZPB_VIDS -> exists args, In (id, args) os /\ op_holds OPSA id args m mo) ->
  ShLoadLit.ShLoadLit.in_wins PubC.TwinB.PubC.ZPB_SH_WINS a = true ->
  m (Z_to_bv 64 (to_Z a)) = Some (Z_to_bv 8 0) /\
  OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.chg_user bsegs IMGX AWAx OPSA os m mo (to_Z a).
Proof.
  intros os m mo a V W. destruct (zpb_sh_wins_in a W) as (w & Hw & Ha).
  destruct (V 16%uint63 ltac:(left; reflexivity)) as (zargs & _ & H16).
  destruct (V 1%uint63 ltac:(right; left; reflexivity)) as (hargs & Hin1 & HH).
  split.
  - assert (ZH : PubImg.TwinB.zpb_holds m) by exact H16.
    exact (proj1 (ZH (to_Z a) (ex_intro _ w (conj Hw Ha)))).
  - left. right. apply Exists_exists. exists (1%uint63, hargs). split; [exact Hin1|]. cbn [fst snd].
    apply (proj2 (OPSA_cov1 hargs (to_Z a))). split; [reflexivity|].
    assert (HX : heap_holds bsegs IMGX AWAx Cw hargs m mo) by exact HH.
    destruct HX as (md & aw & ws & ca & LB & D & _). exists md, aw, ws, ca. split; [exact D|].
    right. right. exists w. split; [apply PUBSH_SHLIT; exact Hw| exact Ha].
Qed.

Theorem azpb_shload_sound : forall (MP : Model -> Prop) (PB : (int -> list byte) -> Prop)
  (HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'),
  forall pc, PlanSound.PlanS.contract_sound bsegs OPSA MP PB (ShLoadLit.ShLoadLit.shloadlit_c bsegs PubC.TwinB.PubC.ZPB_VIDS PubC.TwinB.PubC.ZPB_SH_WINS pc).
Proof.
  intros MP PB HMPA pc.
  exact (ShLoadLit.ShLoadLit.shloadlit_sound bsegs OPSA PubC.TwinB.PubC.ZPB_VIDS PubC.TwinB.PubC.ZPB_SH_WINS
           (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.chg_user bsegs IMGX AWAx OPSA) OPSA_acc_user_law OPSA_zpb_HZ MP PB HMPA pc).
Qed.

Lemma gsh_zero_wins_tab : forall w, In w GshC.TwinB.GshC.GSH_ZERO_WINS_ASAN ->
  In (to_Z (fst w), to_Z (snd w) - to_Z (fst w), 0) GshC.TwinB.GshC.GSH_TAB_ASAN /\ 0x7fffc5a0 <= to_Z (fst w) /\ to_Z (snd w) <= 0x7fffc6a0.
Proof.
  intros w Hw.
  assert (C : forallb (fun w => (existsb (fun e => (fst (fst e) =? to_Z (fst w)) && (snd (fst e) =? to_Z (snd w) - to_Z (fst w)) && (snd e =? 0)) GshC.TwinB.GshC.GSH_TAB_ASAN
                                && (0x7fffc5a0 <=? to_Z (fst w)) && (to_Z (snd w) <=? 0x7fffc6a0))%bool) GshC.TwinB.GshC.GSH_ZERO_WINS_ASAN = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) C w Hw) as Q. apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q Q2]. apply Z.leb_le in Q2, Q3.
  split; [| lia]. apply existsb_exists in Q as ([[a n] v] & He & QQ). cbn [fst snd] in QQ.
  apply andb_prop in QQ as [QQ E3]. apply andb_prop in QQ as [E1 E2]. apply Z.eqb_eq in E1, E2, E3. subst a n v. exact He.
Qed.

Theorem OPSA_gsh_HZ : forall (os : list oinst) (m : word -> option byte) (mo : Model) (a : int),
  (forall id, In id GshC.TwinB.GshC.GSH_VIDS -> exists args, In (id, args) os /\ op_holds OPSA id args m mo) ->
  ShLoadLit.ShLoadLit.in_wins GshC.TwinB.GshC.GSH_ZERO_WINS_ASAN a = true ->
  m (Z_to_bv 64 (to_Z a)) = Some (Z_to_bv 8 0) /\
  OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.chg_user bsegs IMGX AWAx OPSA os m mo (to_Z a).
Proof.
  intros os m mo a V W. unfold ShLoadLit.ShLoadLit.in_wins in W. apply existsb_exists in W as (w & Hw & Q).
  apply andb_prop in Q as [Q1 Q2]. apply Uint63.leb_spec in Q1. apply Uint63.ltb_spec in Q2.
  destruct (gsh_zero_wins_tab w Hw) as (HT & B1 & B2).
  destruct (V 17%uint63 ltac:(left; reflexivity)) as (gargs & _ & H17).
  destruct (V 1%uint63 ltac:(right; left; reflexivity)) as (hargs & Hin1 & HH).
  split.
  - assert (GH : GshImg.TwinB.gsh_holds GshC.TwinB.GshC.GSH_TAB_ASAN m) by exact H17.
    pose proof (GH _ _ _ HT (to_Z a - to_Z (fst w)) ltac:(lia)) as X. unfold AM.wa in X.
    replace (to_Z (fst w) + (to_Z a - to_Z (fst w))) with (to_Z a) in X by lia. exact X.
  - left. right. apply Exists_exists. exists (1%uint63, hargs). split; [exact Hin1|]. cbn [fst snd].
    apply (proj2 (OPSA_cov1 hargs (to_Z a))). split; [reflexivity|].
    assert (HX : heap_holds bsegs IMGX AWAx Cw hargs m mo) by exact HH.
    destruct HX as (md & aw & ws & ca & LB & D & _). exists md, aw, ws, ca. split; [exact D|].
    right. right. exists (0x7fffa000, 0x7fffc6a0). split; [apply IMGSH_SHLIT; left; reflexivity| cbn [fst snd]; lia].
Qed.

Theorem agsh_shload_sound : forall (MP : Model -> Prop) (PB : (int -> list byte) -> Prop)
  (HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'),
  forall pc, PlanSound.PlanS.contract_sound bsegs OPSA MP PB (ShLoadLit.ShLoadLit.shloadlit_c bsegs GshC.TwinB.GshC.GSH_VIDS GshC.TwinB.GshC.GSH_ZERO_WINS_ASAN pc).
Proof.
  intros MP PB HMPA pc.
  exact (ShLoadLit.ShLoadLit.shloadlit_sound bsegs OPSA GshC.TwinB.GshC.GSH_VIDS GshC.TwinB.GshC.GSH_ZERO_WINS_ASAN
           (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.UG.chg_user bsegs IMGX AWAx OPSA) OPSA_acc_user_law OPSA_gsh_HZ MP PB HMPA pc).
Qed.
End Run.
End TwinB.
