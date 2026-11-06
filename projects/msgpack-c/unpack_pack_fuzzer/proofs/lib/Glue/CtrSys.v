(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes Ops SysSpec OblsLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CtrLib CtrS Ops SysSpec OL.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module CtrSys.

Lemma is_lit_den : forall E v w, is_lit v w = true -> den E v = wbv w.
Proof. intros E v w H. unfold is_lit in H. apply sv_eqb_eq in H. subst v. reflexivity. Qed.

Lemma wlit_word : forall i, wbv (wlit i) = Z_to_bv 64 (to_Z i).
Proof. intros i. apply bv_eq. rewrite wbv_unsigned, wlit_ok, Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  pose proof (Uint63.to_Z_bounded i). unfold bv_modulus. change wB with (2 ^ 63) in H. lia. Qed.

Lemma find_op_In : forall id os args, find_op id os = Some args -> In (OpI id args) os.
Proof.
  induction os as [|o os IH]; intros args H; cbn [find_op] in H; [discriminate|].
  destruct (PrimInt63.eqb (op_id o) id) eqn:E.
  - injection H as <-. apply Uint63.eqb_correct in E. left. destruct o; cbn in E |- *. subst. reflexivity.
  - right. apply IH. exact H.
Qed.

Lemma ops_hold_In : forall OPS E os m model o, ops_hold OPS E os m model -> In o os ->
  op_holds OPS (op_id o) (map (den E) (op_args o)) m model.
Proof. intros OPS E os m model o H Hin. exact (proj1 (Forall_forall _ _) H o Hin). Qed.

Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Lemma remove_op_keep : forall id os o, In o os -> PrimInt63.eqb (op_id o) id = false -> In o (remove_op id os).
Proof.
  induction os as [|x os IH]; intros o Ho Hid; cbn [remove_op]; [exact Ho|].
  destruct (PrimInt63.eqb (op_id x) id) eqn:Ex.
  - destruct Ho as [<-|Ho]; [rewrite Hid in Ex; discriminate Ex| exact Ho].
  - destruct Ho as [<-|Ho]; [left; reflexivity| right; exact (IH o Ho Hid)].
Qed.
Lemma set_op_keep : forall id args os o, In o os -> PrimInt63.eqb (op_id o) id = false -> In o (set_op id args os).
Proof.
  induction os as [|x os IH]; intros o Ho Hid; cbn [set_op]; [exact Ho|].
  destruct (PrimInt63.eqb (op_id x) id) eqn:Ex.
  - destruct Ho as [<-|Ho]; [rewrite Hid in Ex; discriminate Ex| right; exact Ho].
  - destruct Ho as [<-|Ho]; [left; reflexivity| right; exact (IH o Ho Hid)].
Qed.

Definition svc_post_mem (ms : machine_state) (ret : word) (m' : word -> option byte) : machine_state :=
  ms_upd ms (rset (reg_of_r5 X10) ret (with_pc (ms_pc_val ms + Z_to_bv 64 4)%bv (core_of ms))) m'.

Lemma svc_post_mem_eq : forall ms x8 r ws cps,
  advance_past_svc (apply_effect (pend ms x8) (mkEffectU r ws [] [] [] cps)) = svc_post_mem ms r (apply_writes (ms_mem ms) ws).
Proof. intros. unfold svc_post_mem, advance_past_svc, apply_effect, set_gpr0, set_reg. rewrite reg10. reflexivity. Qed.

Lemma st_ok_sys : forall E T ms model model' ret v fs' os' n' (m' : word -> option byte),
  st_ok segs OPS E T ms model ->
  PrimInt63.ltb (s_pc T) bit62i = true ->
  den E v = ret ->
  Forall (fact_holds E) fs' ->
  op_minv OPS model' ->
  ops_hold OPS E os' m' model' ->
  ops_apart segs OPS E os' (s_regs T) (s_priv T) ->
  (forall a, fx_acc segs E (s_regs T) a -> op_cov OPS (insts E os') a) ->
  (forall a, 0 <= a < two64 -> (find_segment segs a 1 = None \/ ~ in_priv (s_priv T) a) ->
     m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->

  (forall a b, m' a = Some b -> ms_mem ms a = None -> forall seg, find_segment segs (bv_unsigned a) 1 = Some seg -> seg_writable seg = true) ->
  st_ok segs OPS E (SS (PrimInt63.add (s_pc T) 4%uint63) (rf_set (s_rf T) X10 v) (s_ff T) (s_resv T) (s_regs T)
                      (fs' ++ s_facts T) os' (s_priv T) n')
        (svc_post_mem ms ret m') model'.
Proof.
  intros E T ms model model' ret v fs' os' n' m' HS Hpc Hv Hfs Hmf Hops Hapart Hcov Hmem Hnew.
  pose proof (st_ok_reg_pc segs OPS E T ms model X10 v ret (PrimInt63.add (s_pc T) 4%uint63) HS Hv) as H1.
  rewrite (pc4_ok (s_pc T) Hpc), <- (so_pc _ _ _ _ _ _ HS) in H1. rewrite (setr_eq T X10 v eq_refl) in H1.
  destruct H1 as [Hpc' Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops' Hapart' Hmf0 Hcov0 Hminv].
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv setpc svc_post_mem ms_upd ms_regs ms_fregs ms_pc_val ms_svc_pending
              ms_resv ms_fcsr ms_mem ms_rom] in *; try assumption.
  - intros k r Hk. apply (MemP.region_ok_frame segs (s_priv T) E (ms_mem ms) m' k r Hz (Hreg k r Hk)).
    intros a Ha Hbased Habs. apply Hmem; [exact Ha|].
    destruct (PrimInt63.eqb k 0%uint63) eqn:Hk0.
    + right. exact (proj2 (Habs eq_refl)).
    + left. exact (proj2 (proj2 (ro_valid _ _ _ _ _ _ (Hreg k r Hk) Hk0 a (Hbased eq_refl)))).
  - unfold facts_hold. apply Forall_app. split; assumption.
  - intros a b Hb seg Hseg. destruct (ms_mem ms a) as [b0|] eqn:Hm.
    + exact (Hminv a b0 Hm seg Hseg).
    + exact (Hnew a b Hb Hm seg Hseg).
Qed.

Lemma st_ok_sys_acc : forall E T ms model model' ret v fs' os' n' (m' : word -> option byte) acc,
  st_ok segs OPS E T ms model ->
  PrimInt63.ltb (s_pc T) bit62i = true ->
  den E v = ret ->
  Forall (fact_holds E) fs' ->
  op_minv OPS model' ->
  ops_hold OPS E os' m' model' ->
  ops_apart segs OPS E os' (s_regs T) (s_priv T) ->
  (forall a, fx_acc segs E (s_regs T) a -> op_cov OPS (insts E os') a) ->
  (forall a, 0 <= a < two64 -> (find_segment segs a 1 = None \/ ~ in_priv (s_priv T) a) ->
     m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
  (forall a b, m' a = Some b -> ms_mem ms a = None -> forall seg, find_segment segs (bv_unsigned a) 1 = Some seg -> seg_writable seg = true) ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> op_cov OPS (insts E os') (bv_unsigned a + j)) ->
  materialize_model_accesses model' acc = Some (matz model' acc) /\
  st_ok segs OPS E (SS (PrimInt63.add (s_pc T) 4%uint63) (rf_set (s_rf T) X10 v) (s_ff T) (s_resv T) (s_regs T)
                      (fs' ++ s_facts T) os' (s_priv T) n')
        (svc_post_mem ms ret m') (matz model' acc).
Proof.
  intros E T ms model model' ret v fs' os' n' m' acc HS Hpc Hv Hfs Hmf Hops Hapart Hcov Hmem Hnew Hacc.
  destruct (sys_acc OPS E os' m' model' acc Hmf Hops Hacc) as (Hmat & Hmi2 & Hops2).
  split; [exact Hmat|]. exact (st_ok_sys E T ms model (matz model' acc) ret v fs' os' n' m' HS Hpc Hv Hfs Hmi2 Hops2 Hapart Hcov Hmem Hnew).
Qed.

Lemma st_ok_sys0 : forall E T ms model model' ret v os' (m' : word -> option byte),
  st_ok segs OPS E T ms model ->
  PrimInt63.ltb (s_pc T) bit62i = true ->
  den E v = ret ->
  op_minv OPS model' ->
  ops_hold OPS E os' m' model' ->
  ops_apart segs OPS E os' (s_regs T) (s_priv T) ->
  (forall a, fx_acc segs E (s_regs T) a -> op_cov OPS (insts E os') a) ->
  (forall a, 0 <= a < two64 -> (find_segment segs a 1 = None \/ ~ in_priv (s_priv T) a) ->
     m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
  (forall a b, m' a = Some b -> ms_mem ms a = None -> forall seg, find_segment segs (bv_unsigned a) 1 = Some seg -> seg_writable seg = true) ->
  st_ok segs OPS E (SS (PrimInt63.add (s_pc T) 4%uint63) (rf_set (s_rf T) X10 v) (s_ff T) (s_resv T) (s_regs T)
                      (s_facts T) os' (s_priv T) (s_next T))
        (svc_post_mem ms ret m') model'.
Proof.
  intros. change (s_facts T) with ([] ++ s_facts T). eapply st_ok_sys; eauto.
Qed.

End WithSegs.

Lemma remove_op_subset : forall id os o, In o (remove_op id os) -> In o os.
Proof.
  induction os as [|x os IH]; intros o H; cbn [remove_op] in H; [exact H|].
  destruct (PrimInt63.eqb (op_id x) id); [right; exact H|]. destruct H as [<-|H]; [left; reflexivity | right; apply IH; exact H].
Qed.

Lemma set_op_In : forall id args os o, In o (set_op id args os) -> o = OpI id args \/ In o os.
Proof.
  induction os as [|x os IH]; intros o H; cbn [set_op] in H; [destruct H|].
  destruct (PrimInt63.eqb (op_id x) id).
  - destruct H as [<-|H]; [left; reflexivity | right; right; exact H].
  - destruct H as [<-|H]; [right; left; reflexivity|]. destruct (IH o H) as [E|Hin]; [left; exact E | right; right; exact Hin].
Qed.

Lemma iff_unit : forall (P : Prop) (A : Type) (o x : A), (P <-> o = x) -> (P <-> exists _ : unit, o = x).
Proof. intros P A o x [H1 H2]. split; [intros H; exists tt; exact (H1 H) | intros [_ H]; exact (H2 H)]. Qed.

Lemma in_arg_sys : forall segs ms x8 k, in_arg (sys_input segs ms x8) k = nth k (syscall_args ms) (Z_to_bv 64 0).
Proof. reflexivity. Qed.
Lemma in_arg0 : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0. Proof. reflexivity. Qed.
Lemma in_arg1 : forall segs ms x8, in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1. Proof. reflexivity. Qed.
Lemma in_arg2 : forall segs ms x8, in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2. Proof. reflexivity. Qed.
Lemma in_mem_sys : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms. Proof. reflexivity. Qed.
Lemma in_wmem_sys : forall segs ms x8, in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms. Proof. reflexivity. Qed.

Lemma fd32_3 : fd32 (Z_to_bv 64 3) = Z_to_bv 64 3. Proof. apply fd32_id. rewrite Z_to_bv_small; [lia | unfold bv_modulus; lia]. Qed.
Lemma fd32_1 : fd32 (Z_to_bv 64 1) = Z_to_bv 64 1. Proof. apply fd32_id. rewrite Z_to_bv_small; [lia | unfold bv_modulus; lia]. Qed.

Section Drv.
Variables (segs : list Segment) (heap : opcomp) (ext : int -> opcomp) (p1 file : list byte) (RS : Z) (READ_STAGE : int).
Hypothesis RS_range : 0 <= RS /\ RS + 65536 <= two64.
Hypothesis HRS : to_Z READ_STAGE = RS.

Hypothesis heap_fp_stage : forall args a, RS <= a < RS + 65536 -> ~ Exists (fun iv => fst iv <= a < snd iv) (oc_fp heap args).
Hypothesis heap_fds : forall args m model fds, oc_holds heap args m model -> oc_holds heap args m (with_fds fds model).
Hypothesis ext_fp_stage : forall id args a, RS <= a < RS + 65536 -> ~ Exists (fun iv => fst iv <= a < snd iv) (oc_fp (ext id) args).
Hypothesis ext_fds : forall id args m model fds, oc_holds (ext id) args m model -> oc_holds (ext id) args m (with_fds fds model).

Variable TM : tab_model heap (FD3 p1 file) (RSTAGE file RS RS_range) FD3DIR FDINIT ext.
Definition OPS : optable := mk_optable_g heap (FD3 p1 file) (RSTAGE file RS RS_range) FD3DIR FDINIT ext TM.
Hypothesis TM_fds : forall mo fds, op_minv OPS mo -> op_minv OPS (with_fds fds mo).
Hypothesis TM_cov1 : forall id args a, op_cov1 OPS id args a -> id = 1%uint63.

Variable MP : Model -> Prop.
Hypothesis MP_fds : forall fds model, MP model -> MP (with_fds fds model).
Hypothesis MP_mat : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.
Variable PB : (int -> list byte) -> Prop.

Lemma cover_post : forall E st ms model os',
  st_ok segs OPS E st ms model ->
  (forall o, In o (s_ops st) -> op_id o = 1%uint63 -> In o os') ->
  forall a, fx_acc segs E (s_regs st) a -> op_cov OPS (insts E os') a.
Proof.
  intros E st ms model os' HS Hk a Ha. apply (cov_keep OPS E (s_ops st)); [| exact (so_cover _ _ _ _ _ _ HS a Ha)].
  intros o Ho [z Hz]. exact (Hk o Ho (TM_cov1 _ _ _ Hz)).
Qed.
Lemma cover_same : forall E st ms model, st_ok segs OPS E st ms model ->
  forall a, fx_acc segs E (s_regs st) a -> op_cov OPS (insts E (s_ops st)) a.
Proof. intros E st ms model HS. exact (so_cover _ _ _ _ _ _ HS). Qed.

Lemma op_holds_of : forall E st ms model id args,
  st_ok segs OPS E st ms model -> find_op id (s_ops st) = Some args ->
  oc_holds (comp_of heap (FD3 p1 file) (RSTAGE file RS RS_range) FD3DIR FDINIT ext id) (map (den E) args) (ms_mem ms) model.
Proof.
  intros E st ms model id args HS Hf.
  exact (ops_hold_In OPS E _ _ _ _ (so_ops _ _ _ _ _ _ HS) (find_op_In id _ _ Hf)).
Qed.

Lemma fds_of_FD3 : forall E st ms model off,
  st_ok segs OPS E st ms model -> find_op CtrS.FD3_ID (s_ops st) = Some [off] ->
  m_fds model = (fd3, FdFile p1 (den E off)) :: FDS0 /\ bv_unsigned (den E off) <= fsize file.
Proof. intros E st ms model off HS Hf. exact (op_holds_of E st ms model CtrS.FD3_ID [off] HS Hf). Qed.
Lemma fds_of_FD3DIR : forall E st ms model,
  st_ok segs OPS E st ms model -> find_op CtrS.FD3DIR_ID (s_ops st) = Some [] -> m_fds model = (fd3, FdDir) :: FDS0.
Proof. intros E st ms model HS Hf. exact (op_holds_of E st ms model CtrS.FD3DIR_ID [] HS Hf). Qed.
Lemma fds_of_FDINIT : forall E st ms model,
  st_ok segs OPS E st ms model -> find_op CtrS.FDINIT_ID (s_ops st) = Some [] -> m_fds model = FDS0.
Proof. intros E st ms model HS Hf. exact (op_holds_of E st ms model CtrS.FDINIT_ID [] HS Hf). Qed.

Lemma sysno_ok : forall E st n, sysno st n = true ->
  bv_unsigned (den E (getr st X17)) = to_Z n /\ PrimInt63.ltb (s_pc st) bit62i = true /\ one_fd_op st = true.
Proof.
  intros E st n H. unfold sysno in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [|split; [exact H2 | exact H3]]. rewrite (is_lit_den E _ _ H1), wbv_unsigned. apply wlit_ok.
Qed.

Lemma op_keep_fds : forall E o m model fds,
  is_fd_op o = false ->
  op_holds OPS (op_id o) (map (den E) (op_args o)) m model ->
  op_holds OPS (op_id o) (map (den E) (op_args o)) m (with_fds fds model).
Proof.
  intros E o m model fds Hnf H. cbn [OPS mk_optable_g op_holds] in *. unfold comp_holds, comp_of in *.
  unfold is_fd_op in Hnf. rewrite !orb_false_iff in Hnf. destruct Hnf as [[H5 H2] H4].
  change CtrS.FDINIT_ID with 5%uint63 in H5. change CtrS.FD3_ID with 2%uint63 in H2. change CtrS.FD3DIR_ID with 4%uint63 in H4.
  destruct (PrimInt63.eqb (op_id o) 1%uint63); [apply heap_fds; exact H|].
  rewrite H2 in *. destruct (PrimInt63.eqb (op_id o) 3%uint63).
  - exact H.
  - rewrite H4, H5 in *. apply ext_fds. exact H.
Qed.

Lemma ops_hold_fd_update : forall E st ms model fds (newop : opinst) os',
  st_ok segs OPS E st ms model ->
  op_holds OPS (op_id newop) (map (den E) (op_args newop)) (ms_mem ms) (with_fds fds model) ->
  (forall o, In o os' -> o = newop \/ (In o (s_ops st) /\ is_fd_op o = false)) ->
  ops_hold OPS E os' (ms_mem ms) (with_fds fds model).
Proof.
  intros E st ms model fds newop os' HS Hnew Hos. unfold ops_hold. apply Forall_forall. intros o Ho.
  destruct (Hos o Ho) as [->|[Hin Hnf]]; [exact Hnew|].
  apply op_keep_fds; [exact Hnf|]. exact (ops_hold_In OPS E _ _ _ _ (so_ops _ _ _ _ _ _ HS) Hin).
Qed.

Lemma ops_apart_fd_update : forall E st ms model (newop : opinst) os',
  st_ok segs OPS E st ms model -> is_fd_op newop = true ->
  (forall o, In o os' -> o = newop \/ In o (s_ops st)) ->
  ops_apart segs OPS E os' (s_regs st) (s_priv st).
Proof.
  intros E st ms model newop os' HS Hfd Hos. unfold ops_apart. apply Forall_forall. intros o Ho a Ha.
  destruct (Hos o Ho) as [->|Hin].
  - exfalso. revert Ha. cbn [OPS mk_optable_g op_fp]. unfold comp_of. unfold is_fd_op in Hfd.
    change CtrS.FDINIT_ID with 5%uint63 in Hfd. change CtrS.FD3_ID with 2%uint63 in Hfd. change CtrS.FD3DIR_ID with 4%uint63 in Hfd.
    destruct (PrimInt63.eqb (op_id newop) 1%uint63) eqn:E1.
    { apply Uint63.eqb_correct in E1. rewrite E1 in Hfd. discriminate Hfd. }
    destruct (PrimInt63.eqb (op_id newop) 2%uint63); [intros X; inversion X|].
    destruct (PrimInt63.eqb (op_id newop) 3%uint63) eqn:E3.
    { apply Uint63.eqb_correct in E3. rewrite E3 in Hfd. discriminate Hfd. }
    destruct (PrimInt63.eqb (op_id newop) 4%uint63); [intros X; inversion X|].
    destruct (PrimInt63.eqb (op_id newop) 5%uint63); [intros X; inversion X|]. cbn in Hfd. discriminate Hfd.
  - exact (proj1 (Forall_forall _ _) (so_apart _ _ _ _ _ _ HS) o Hin a Ha).
Qed.

Lemma is_fd_op_id : forall o, is_fd_op o = is_fd_op (OpI (op_id o) []).
Proof. intros [id args]. reflexivity. Qed.

Lemma count_fd_nil : forall os, count_fd_ops os = 0%nat -> forall o, In o os -> is_fd_op o = false.
Proof.
  induction os as [|x os IH]; intros H o Hin; [destruct Hin|]. cbn [count_fd_ops] in H.
  destruct (is_fd_op x) eqn:Ex; [lia|]. destruct Hin as [<-|Hin]; [exact Ex | exact (IH H o Hin)].
Qed.

Lemma find_op_fd_count : forall os oid oargs, find_op oid os = Some oargs -> is_fd_op (OpI oid oargs) = true ->
  (1 <= count_fd_ops os)%nat.
Proof.
  induction os as [|x os IH]; intros oid oargs Hf Hfd; cbn [find_op] in Hf; [discriminate|]. cbn [count_fd_ops].
  destruct (PrimInt63.eqb (op_id x) oid) eqn:E.
  - apply Uint63.eqb_correct in E. rewrite (is_fd_op_id x), E. rewrite (is_fd_op_id (OpI oid oargs)) in Hfd. cbn [op_id] in Hfd. rewrite Hfd. lia.
  - pose proof (IH oid oargs Hf Hfd). destruct (is_fd_op x); lia.
Qed.

Lemma remove_fd_op_others : forall os oid oargs, Nat.eqb (count_fd_ops os) 1%nat = true ->
  find_op oid os = Some oargs -> is_fd_op (OpI oid oargs) = true ->
  forall o, In o (remove_op oid os) -> is_fd_op o = false.
Proof.
  induction os as [|x os IH]; intros oid oargs Hc Hf Hfd o Hin; cbn [find_op remove_op count_fd_ops] in *; [destruct Hin|].
  apply Nat.eqb_eq in Hc.
  destruct (PrimInt63.eqb (op_id x) oid) eqn:E.
  - apply Uint63.eqb_correct in E. rewrite (is_fd_op_id x), E in Hc. rewrite (is_fd_op_id (OpI oid oargs)) in Hfd. cbn [op_id] in Hfd.
    rewrite Hfd in Hc. apply (count_fd_nil os); [lia | exact Hin].
  - destruct (is_fd_op x) eqn:Ex.
    + exfalso. pose proof (find_op_fd_count os oid oargs Hf Hfd). lia.
    + destruct Hin as [<-|Hin]; [exact Ex|]. apply (IH oid oargs); [apply Nat.eqb_eq; cbn [Nat.add] in Hc; exact Hc | exact Hf | exact Hfd | exact Hin].
Qed.

Theorem close_sound : forall pc, ecall_at segs pc -> contract_sound segs OPS MP PB (c_close pc).
Proof.
  intros pc Hat st sts Hpc Happ K E ms model HS HMP HPB Hk. cbn [c_close c_pc c_apply] in Hpc, Happ.
  unfold close_apply in Happ.
  destruct (sysno st 57 && is_lit (getr st X10) (wlit 3)) eqn:Hpre; [|discriminate Happ].
  apply andb_prop in Hpre as [Hno H3]. destruct (sysno_ok E st _ Hno) as (H57 & Hpc62 & Hone).
  pose proof (so_mf _ _ _ _ _ _ HS) as Hmi. pose proof (op_minv_halted OPS _ Hmi) as Hh.
  assert (Ha0 : ms_gpr (pend ms (den E (getr st X17))) 0 = Z_to_bv 64 3).
  { rewrite pend_gpr, (so_a0 segs OPS E st ms model HS), (is_lit_den E _ _ H3). rewrite wlit_word. reflexivity. }

  assert (CASES : exists e oldid oldargs,
            m_fds model = (fd3, e) :: FDS0 /\ find_op oldid (s_ops st) = Some oldargs /\
            is_fd_op (OpI oldid oldargs) = true /\
            sts = [sysret (set_ops st (OpI CtrS.FDINIT_ID [] :: remove_op oldid (s_ops st))) (VL wzero)]).
  { destruct (find_op CtrS.FD3_ID (s_ops st)) as [[|off [|? ?]]|] eqn:Hf3;
    destruct (find_op CtrS.FD3DIR_ID (s_ops st)) as [[|? ?]|] eqn:Hf4; try discriminate Happ; injection Happ as <-.
    - destruct (fds_of_FD3 E st ms model off HS Hf3) as [Hfds _]. exists (FdFile p1 (den E off)), CtrS.FD3_ID, [off].
      rewrite Hfds. repeat split; try reflexivity; assumption.
    - pose proof (fds_of_FD3DIR E st ms model HS Hf4) as Hfds. exists FdDir, CtrS.FD3DIR_ID, [].
      rewrite Hfds. repeat split; try reflexivity; assumption. }
  destruct CASES as (e & oid & oargs & Hfds & Hfo & Hisfd & ->).
  assert (Hlk : fd_lookup (m_fds model) fd3 = Some e) by (rewrite Hfds; reflexivity).

  rewrite <- Hpc in Hat. apply (rz_pend segs OPS E st ms model K HS Hat).
  set (x8 := den E (getr st X17)) in *.
  set (model' := with_fds (fd_remove (m_fds model) fd3) model).
  apply (rz_silent_all segs _ unit (fun _ => mkCfg (advance_past_svc (apply_effect (pend ms x8) (mkEffect (Z_to_bv 64 0) [] []))) model') tt K).
  - apply (node_silent_a segs (pend ms x8) model x8 unit (fun _ => mkEffect (Z_to_bv 64 0) [] []) (fun _ => model') (fun _ => model') Hh eq_refl
             (fun _ => nonspur_nonalloc segs _ _ _ _ (nonalloc_eq x8 _ H57 eq_refl))).
    + intros o. apply iff_unit.
      assert (H57s : bv_unsigned (in_sysno (sys_input segs (pend ms x8) x8)) = 57) by (rewrite in_sysno_sys_input; exact H57).
      assert (Hlk' : fd_lookup (m_fds model) (fd32 (in_arg (sys_input segs (pend ms x8) x8) 0)) = Some e)
        by (rewrite in_arg0, Ha0, fd32_3; exact Hlk).
      pose proof (close_outcome _ model e o H57s Hlk') as X. rewrite in_arg0, Ha0, fd32_3 in X. exact X.
    + intros _. subst model'. split; [rewrite m_halted_with_fds; exact Hh | exact (mat_nil _)].
  - intros []. change (mkEffect (Z_to_bv 64 0) [] []) with (mkEffectU (Z_to_bv 64 0) [] [] [] [] []).
    rewrite svc_post_mem_eq. cbn [apply_writes].
    apply (Hk _ (or_introl eq_refl) E _ model'); [apply env_ext_refl' | apply MP_fds; exact HMP |].
    change (sysret (set_ops st (OpI CtrS.FDINIT_ID [] :: remove_op oid (s_ops st))) (VL wzero)) with
      (SS (PrimInt63.add (s_pc st) 4%uint63) (rf_set (s_rf st) X10 (VL wzero)) (s_ff st) (s_resv st) (s_regs st)
          (s_facts st) (OpI CtrS.FDINIT_ID [] :: remove_op oid (s_ops st)) (s_priv st) (s_next st)).
    apply (st_ok_sys0 segs OPS E st ms model model' (Z_to_bv 64 0) (VL wzero)); try assumption.
    + cbn [den]. rewrite wbv_wzero. reflexivity.
    + subst model'. apply TM_fds. exact Hmi.
    + subst model'. apply (ops_hold_fd_update E st ms model _ (OpI CtrS.FDINIT_ID [])); [exact HS| |].
      * cbn [op_id op_args map OPS mk_optable_g op_holds]. unfold comp_holds, comp_of. cbn. rewrite m_fds_with_fds, Hfds. reflexivity.
      * intros o [<-|Ho]; [left; reflexivity | right]. pose proof (remove_op_subset _ _ _ Ho) as Hin. split; [exact Hin|].
        exact (remove_fd_op_others (s_ops st) oid oargs Hone Hfo Hisfd o Ho).
    + apply (ops_apart_fd_update E st ms model (OpI CtrS.FDINIT_ID [])); [exact HS | reflexivity |].
      intros o [<-|Ho]; [left; reflexivity | right; exact (remove_op_subset _ _ _ Ho)].
    + apply (cover_post E st ms model _ HS). intros o Ho H1. right. apply (remove_op_keep _ _ _ Ho).
      rewrite H1. unfold is_fd_op in Hisfd. cbn [op_id] in Hisfd.
      destruct (PrimInt63.eqb 1%uint63 oid) eqn:E1; [|reflexivity]. apply Uint63.eqb_correct in E1. subst oid. discriminate Hisfd.
    + intros a _ _. reflexivity.
    + intros a b Hb Hn. rewrite Hb in Hn. discriminate Hn.
Qed.

Lemma fd1_channel : forall E st ms model,
  st_ok segs OPS E st ms model -> has_fds st = true -> fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Proof.
  intros E st ms model HS H. unfold has_fds in H.
  destruct (find_op CtrS.FDINIT_ID (s_ops st)) as [[|? ?]|] eqn:H5;
  destruct (find_op CtrS.FD3_ID (s_ops st)) as [[|off [|? ?]]|] eqn:H2;
  destruct (find_op CtrS.FD3DIR_ID (s_ops st)) as [[|? ?]|] eqn:H4; try discriminate H;
  first [ rewrite (fds_of_FDINIT E st ms model HS H5); reflexivity
        | rewrite (proj1 (fds_of_FD3 E st ms model off HS H2)); reflexivity
        | rewrite (fds_of_FD3DIR E st ms model HS H4); reflexivity ].
Qed.

Lemma det_nomem_tail_cp : forall (pc : int) (st : sstate) K E ms model (ret : word) (v : sv) (no : Z) cps,
  st_ok segs OPS E st ms model -> ecall_at segs (s_pc st) -> MP model ->
  bv_unsigned (den E (getr st X17)) = no -> PrimInt63.ltb (s_pc st) bit62i = true -> den E v = ret ->
  (forall o, syscall_spec (sys_input segs (pend ms (den E (getr st X17))) (den E (getr st X17))) model o <->
             o = Ok (mkEffectU ret [] [] [] [] cps) model []) ->
  (forall a n j, In (a, n) cps -> 0 <= j < Z.of_nat n -> fx_acc segs E (s_regs st) (bv_unsigned a + j)) ->
  (forall E' ms' model', env_ext (s_next st) E E' -> MP model' ->
      st_ok segs OPS E' (sysret st v) ms' model' -> realizes segs (mkCfg ms' model') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros pc st K E ms model ret v no cps HS Hat HMP Hno Hpc62 Hv Hspec Hcps Hk.
  pose proof (so_mf _ _ _ _ _ _ HS) as Hmi. pose proof (op_minv_halted OPS _ Hmi) as Hh.
  assert (ACC : forall a n j, In (a, n) (syscall_effect_accesses (mkEffectU ret [] [] [] [] cps)) -> 0 <= j < Z.of_nat n ->
                  op_cov OPS (insts E (s_ops st)) (bv_unsigned a + j)).
  { intros a n j Hin Hj. unfold syscall_effect_accesses in Hin. cbn [eff_copyins eff_writes write_accesses] in Hin. rewrite app_nil_r in Hin.
    exact (so_cover _ _ _ _ _ _ HS _ (Hcps a n j Hin Hj)). }
  destruct (sys_acc OPS E (s_ops st) (ms_mem ms) model _ Hmi (so_ops _ _ _ _ _ _ HS) ACC) as (Hmat & Hmi2 & Hops2).
  set (mo2 := matz model (syscall_effect_accesses (mkEffectU ret [] [] [] [] cps))) in *.
  apply (rz_pend segs OPS E st ms model K HS Hat). set (x8 := den E (getr st X17)) in *.
  apply (rz_silent_all segs _ unit (fun _ => mkCfg (advance_past_svc (apply_effect (pend ms x8) (mkEffectU ret [] [] [] [] cps))) mo2) tt K).
  - apply (node_silent_a segs (pend ms x8) model x8 unit (fun _ => mkEffectU ret [] [] [] [] cps) (fun _ => model) (fun _ => mo2) Hh eq_refl
             (fun _ => nonspur_det _ _ _ _ _ Hspec)).
    + intros o. apply iff_unit. apply Hspec.
    + intros _. split; [exact Hh| exact Hmat].
  - intros []. rewrite svc_post_mem_eq. cbn [apply_writes].
    apply (Hk E _ mo2); [apply env_ext_refl' | exact (MP_mat _ _ _ HMP Hmat) |].
    change (sysret st v) with
      (SS (PrimInt63.add (s_pc st) 4%uint63) (rf_set (s_rf st) X10 v) (s_ff st) (s_resv st) (s_regs st)
          (s_facts st) (s_ops st) (s_priv st) (s_next st)).
    apply (st_ok_sys0 segs OPS E st ms model mo2 ret v); try assumption.
    + exact (so_apart _ _ _ _ _ _ HS).
    + exact (cover_same E st ms model HS).
    + intros a _ _. reflexivity.
    + intros a b Hb Hn. rewrite Hb in Hn. discriminate Hn.
Qed.

Lemma det_nomem_tail : forall (pc : int) (st : sstate) K E ms model (ret : word) (v : sv) (no : Z),
  st_ok segs OPS E st ms model -> ecall_at segs (s_pc st) -> MP model ->
  bv_unsigned (den E (getr st X17)) = no -> PrimInt63.ltb (s_pc st) bit62i = true -> den E v = ret ->
  (forall o, syscall_spec (sys_input segs (pend ms (den E (getr st X17))) (den E (getr st X17))) model o <->
             o = Ok (mkEffect ret [] []) model []) ->
  (forall E' ms' model', env_ext (s_next st) E E' -> MP model' ->
      st_ok segs OPS E' (sysret st v) ms' model' -> realizes segs (mkCfg ms' model') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros pc st K E ms model ret v no HS Hat HMP Hno Hpc Hv Hspec Hk.
  apply (det_nomem_tail_cp pc st K E ms model ret v no [] HS Hat HMP Hno Hpc Hv Hspec); [intros a n j []| exact Hk].
Qed.

Lemma neg_den : forall E e, den E (errv e) = errno_ret e.
Proof.
  intros E e. cbn [den errv]. unfold errno_ret, neg. apply bv_eq. rewrite wbv_unsigned, Z_to_bv_unsigned, Z2w_ok.
  unfold bv_wrap, bv_modulus, two64. reflexivity.
Qed.

Theorem ioctl_sound : forall pc, ecall_at segs pc -> contract_sound segs OPS MP PB (c_ioctl pc).
Proof.
  intros pc Hat st sts Hpc Happ K E ms model HS HMP HPB Hk. cbn [c_ioctl c_pc c_apply] in Hpc, Happ.
  unfold ioctl_apply in Happ.
  destruct (sysno st 29 && is_lit (getr st X10) (wlit 1) && is_lit (getr st X11) (wlit 21523) && has_fds st) eqn:Hpre; [|discriminate Happ].
  injection Happ as <-.
  apply andb_prop in Hpre as [Hpre Hfds]. apply andb_prop in Hpre as [Hpre H11]. apply andb_prop in Hpre as [Hno H10].
  destruct (sysno_ok E st _ Hno) as (H29 & Hpc62 & Hone). rewrite <- Hpc in Hat.
  apply (det_nomem_tail pc st K E ms model (errno_ret ENOTTY) (errv ENOTTY) 29 HS Hat HMP H29 Hpc62 (neg_den E ENOTTY)).
  - intros o. apply (ioctl_outcome _ model (Z_to_bv 64 1) o).
    + rewrite in_sysno_sys_input. exact H29.
    + rewrite in_arg0, pend_gpr, (so_a0 segs OPS E st ms model HS), (is_lit_den E _ _ H10), wlit_word. change (to_Z 1%uint63) with 1.
      rewrite fd32_1. exact (fd1_channel E st ms model HS Hfds).
    + rewrite in_arg1, pend_gpr, (so_a1 segs OPS E st ms model HS), (is_lit_den E _ _ H11), wlit_word. change (to_Z 21523%uint63) with 21523. reflexivity.
  - intros E' ms' model' HX HMP' HS'. exact (Hk _ (or_introl eq_refl) E' ms' model' HX HMP' HS').
Qed.

Lemma want_ok_small : forall v w, want_ok v = Some w -> v = VL w /\ 0 < w2Z w <= 65536.
Proof.
  intros v w H. unfold want_ok in H. destruct v; try discriminate H.
  destruct (wltu wzero w0 && wleu w0 (wlit STAGE_LEN)) eqn:Hc; [|discriminate H]. injection H as <-.
  apply andb_prop in Hc as [H1 H2]. rewrite wltu_w2Z in H1. rewrite wleu_w2Z in H2.
  apply Z.ltb_lt in H1. apply Z.leb_le in H2. rewrite wlit_ok in H2. change (w2Z wzero) with 0 in H1.
  change (to_Z STAGE_LEN) with 65536 in H2. split; [reflexivity | lia].
Qed.

Hypothesis RS_user : RS + 2 ^ 40 <= 2 ^ 47.

Lemma access_stage : forall n, 0 <= n <= 2 ^ 40 -> access_okb (Z_to_bv 64 RS) n = true.
Proof.
  intros n Hn. unfold access_okb, TASK_SIZE. rewrite Z_to_bv_small by (unfold bv_modulus; unfold two64 in RS_range; lia).
  apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Theorem read_dir_sound : forall pc, ecall_at segs pc -> contract_sound segs OPS MP PB (c_read_dir READ_STAGE pc).
Proof.
  intros pc Hat st sts Hpc Happ K E ms model HS HMP HPB Hk. cbn [c_read_dir c_pc c_apply] in Hpc, Happ.
  unfold read_dir_apply in Happ.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:Hpre; [|discriminate Happ] end.
  injection Happ as <-.
  apply andb_prop in Hpre as [Hpre Hf4]. apply andb_prop in Hpre as [Hpre H12]. apply andb_prop in Hpre as [Hpre H11]. apply andb_prop in Hpre as [Hno H10].
  destruct (sysno_ok E st _ Hno) as (H63 & Hpc62 & Hone). rewrite <- Hpc in Hat.
  destruct (find_op CtrS.FD3DIR_ID (s_ops st)) as [[|? ?]|] eqn:Hf; try discriminate Hf4.
  apply (det_nomem_tail pc st K E ms model (errno_ret EISDIR) (errv EISDIR) 63 HS Hat HMP H63 Hpc62 (neg_den E EISDIR)).
  - intros o. apply (read_dir_outcome _ model o).
    + rewrite in_sysno_sys_input. exact H63.
    + rewrite in_arg0, pend_gpr, (so_a0 segs OPS E st ms model HS), (is_lit_den E _ _ H10), wlit_word. change (to_Z 3%uint63) with 3.
      rewrite fd32_3, (fds_of_FD3DIR E st ms model HS Hf). reflexivity.
    + rewrite in_arg1, in_arg2, !pend_gpr, (so_a1 segs OPS E st ms model HS), (so_a2 segs OPS E st ms model HS), (is_lit_den E _ _ H11), wlit_word, HRS.
      apply access_stage.
      destruct (want_ok (getr st X12)) as [w|] eqn:Hw.
      * destruct (want_ok_small _ _ Hw) as [-> Hr]. cbn [den]. rewrite wbv_unsigned. lia.
      * rewrite (is_lit_den E _ _ H12). rewrite wbv_unsigned. change (w2Z wzero) with 0. lia.
  - intros E' ms' model' HX HMP' HS'. exact (Hk _ (or_introl eq_refl) E' ms' model' HX HMP' HS').
Qed.

Let S : Z := fsize file.

Hypothesis PB_size : forall b, PB b -> b 11%uint63 = Z_to_le_bytes 8 S.
Hypothesis MP_file : forall model, MP model -> fs_lookup (m_fs model) p1 = Some file.

Hypothesis stage_writable : Mem.abs_writable segs RS 65536 = true.

Lemma S_range : 0 <= S <= Z.of_nat (length file) /\ S <= 2 ^ 62.
Proof. unfold S, fsize. lia. Qed.

Lemma den_SIZE11 : forall E, PB (eb E) -> den E SIZE11 = Z_to_bv 64 S.
Proof. intros E HPB. unfold SIZE11. apply (den_param8 E 11%uint63 S (PB_size _ HPB)). pose proof S_range. lia. Qed.
Lemma den_SIZE11_u : forall E, PB (eb E) -> bv_unsigned (den E SIZE11) = S.
Proof. intros E HPB. rewrite (den_SIZE11 E HPB). apply Z_to_bv64_unsigned. pose proof S_range. lia. Qed.

Lemma known_leu_sound : forall E st ms model a b, st_ok segs OPS E st ms model ->
  known_leu (s_facts st) a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros E st ms model a b HS H. unfold known_leu, dec_false in H.
  destruct (decide_ltu (s_facts st) b a) as [[|]|] eqn:Hd; try discriminate H.
  pose proof (ValP.decide_ltu_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) b a false Hd) as X.
  apply (proj1 (ltu_iff _ _ false)) in X. exact X.
Qed.

Lemma decide_ltu_holds : forall E st ms model a b r, st_ok segs OPS E st ms model ->
  decide_ltu (s_facts st) a b = Some r -> (if r then bv_unsigned (den E a) < bv_unsigned (den E b) else bv_unsigned (den E b) <= bv_unsigned (den E a)).
Proof.
  intros E st ms model a b r HS Hd.
  pose proof (ValP.decide_ltu_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) a b r Hd) as X.
  apply (proj1 (ltu_iff _ _ r)) in X. exact X.
Qed.

Lemma stage_wb : forall m i, 0 <= i < 65536 -> wb segs m (RS + i) = true /\ exists seg, find_segment segs (RS + i) 1 = Some seg.
Proof.
  intros m i Hi. destruct (MemP.abs_writable_sound segs RS 65536 ltac:(lia) ltac:(lia) stage_writable) as [_ H].
  destruct (H i Hi) as [Hw [seg [Hs _]]]. split; [apply Hw | exists seg; exact Hs].
Qed.
Lemma stage_seg_writable : forall i seg, 0 <= i < 65536 -> find_segment segs (RS + i) 1 = Some seg -> seg_writable seg = true.
Proof.
  intros i seg Hi Hs. destruct (MemP.abs_writable_sound segs RS 65536 ltac:(lia) ltac:(lia) stage_writable) as [_ H].
  destruct (H i Hi) as [_ [seg' [Hs' Hw']]]. rewrite Hs in Hs'. injection Hs' as <-. exact Hw'.
Qed.

Lemma stage_readable_n : forall ms (n : nat), Z.of_nat n <= 65536 ->
  exists w, read_bytes_aux (ms_writable_byte segs ms) (Z_to_bv 64 RS) n = Some w.
Proof.
  intros ms n Hn. apply read_bytes_aux_some. intros j Hj.
  destruct (stage_wb (ms_mem ms) (Z.of_nat j) ltac:(lia)) as [Hw _]. unfold wb in Hw. unfold ms_writable_byte.
  destruct (wview segs (ms_mem ms) (Z_to_bv 64 (RS + Z.of_nat j))); [discriminate | discriminate Hw].
Qed.

Lemma apply_writes_delivered : forall m buf bs, apply_writes m (delivered_writes buf bs) = write_to_mem m buf bs.
Proof. intros m buf bs. destruct bs; reflexivity. Qed.

Lemma file_read_eq : forall off w, bv_unsigned w <= MAX_RW_COUNT ->
  file_read file off (Z_to_bv 64 (rw_count_clamp w)) = firstn (Z.to_nat (bv_unsigned w)) (skipn (Z.to_nat (bv_unsigned off)) file).
Proof.
  intros off w Hw. rewrite file_read_unguarded. unfold word_to_nat. rewrite (rw_count_clamp_small w Hw).
  rewrite Z_to_bv64_unsigned by (pose proof (u64_range w); lia). reflexivity.
Qed.

Lemma count_ops_zero : forall id os o, count_ops id os = 0%nat -> In o os -> PrimInt63.eqb (op_id o) id = false.
Proof.
  induction os as [|x os IH]; intros o H Hin; [destruct Hin|]. cbn [count_ops] in H.
  destruct (PrimInt63.eqb (op_id x) id) eqn:Ex; [lia|]. destruct Hin as [<-|Hin]; [exact Ex | exact (IH o H Hin)].
Qed.

Lemma set_op_others : forall id args os o, Nat.eqb (count_ops id os) 1%nat = true ->
  In o (set_op id args os) -> o = OpI id args \/ (In o os /\ PrimInt63.eqb (op_id o) id = false).
Proof.
  induction os as [|x os IH]; intros o Hc Hin; cbn [set_op count_ops] in *; [destruct Hin|].
  apply Nat.eqb_eq in Hc. destruct (PrimInt63.eqb (op_id x) id) eqn:Ex.
  - destruct Hin as [<-|Hin]; [left; reflexivity|]. right. split; [right; exact Hin|]. apply (count_ops_zero id os); [lia | exact Hin].
  - destruct Hin as [<-|Hin]; [right; split; [left; reflexivity | exact Ex]|].
    destruct (IH o ltac:(apply Nat.eqb_eq; lia) Hin) as [E|[H1 H2]]; [left; exact E | right; split; [right; exact H1 | exact H2]].
Qed.

Lemma set_fd_others : forall os off o, Nat.eqb (count_fd_ops os) 1%nat = true -> find_op CtrS.FD3_ID os = Some [off] ->
  In o os -> PrimInt63.eqb (op_id o) CtrS.FD3_ID = false -> is_fd_op o = false.
Proof.
  induction os as [|x os IH]; intros off o Hc Hf Hin Hne; [destruct Hin|]. cbn [count_fd_ops find_op] in *.
  apply Nat.eqb_eq in Hc.
  destruct (PrimInt63.eqb (op_id x) CtrS.FD3_ID) eqn:Ex.
  - assert (Hfx : is_fd_op x = true) by (unfold is_fd_op; rewrite Ex; destruct (PrimInt63.eqb (op_id x) CtrS.FDINIT_ID); reflexivity).
    rewrite Hfx in Hc. destruct Hin as [<-|Hin]; [congruence|]. apply (count_fd_nil os); [lia | exact Hin].
  - destruct Hin as [<-|Hin].
    + destruct (is_fd_op x) eqn:Eo; [|reflexivity]. exfalso.
      pose proof (find_op_fd_count os CtrS.FD3_ID [off] Hf eq_refl). lia.
    + destruct (is_fd_op x); [|exact (IH off o ltac:(apply Nat.eqb_eq; lia) Hf Hin Hne)].
      exfalso. pose proof (find_op_fd_count os CtrS.FD3_ID [off] Hf eq_refl). lia.
Qed.

Lemma op_keep_stage : forall E o m m' model fds,
  is_fd_op o = false -> PrimInt63.eqb (op_id o) CtrS.RSTAGE_ID = false ->
  (forall a, 0 <= a < two64 -> ~ (RS <= a < RS + 65536) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  op_holds OPS (op_id o) (map (den E) (op_args o)) m model ->
  op_holds OPS (op_id o) (map (den E) (op_args o)) m' (with_fds fds model).
Proof.
  intros E o m m' model fds Hnf Hnr AG NU H. cbn [OPS mk_optable_g op_holds] in *. unfold comp_holds, comp_of in *.
  unfold is_fd_op in Hnf. rewrite !orb_false_iff in Hnf. destruct Hnf as [[H5 H2] H4].
  change CtrS.FDINIT_ID with 5%uint63 in H5. change CtrS.FD3_ID with 2%uint63 in H2. change CtrS.FD3DIR_ID with 4%uint63 in H4.
  change CtrS.RSTAGE_ID with 3%uint63 in Hnr.
  destruct (PrimInt63.eqb (op_id o) 1%uint63).
  - apply heap_fds. apply (oc_frame heap _ m m' model); [| exact NU | exact H].
    intros a Ha Hfp. apply AG; [exact Ha|]. intros Hin. exact (heap_fp_stage _ a Hin Hfp).
  - rewrite H2, Hnr, H4, H5 in *. apply ext_fds. apply (oc_frame (ext (op_id o)) _ m m' model); [| exact NU | exact H].
    intros a Ha Hfp. apply AG; [exact Ha|]. intros Hin. exact (ext_fp_stage _ _ a Hin Hfp).
Qed.

Lemma fd_op_is : forall os args o, Nat.eqb (count_fd_ops os) 1%nat = true -> find_op CtrS.FD3_ID os = Some args ->
  In o os -> is_fd_op o = true -> o = OpI CtrS.FD3_ID args.
Proof.
  induction os as [|x os IH]; intros args o Hc Hf Hin Hfd; [destruct Hin|]. cbn [count_fd_ops find_op] in *.
  apply Nat.eqb_eq in Hc.
  destruct (PrimInt63.eqb (op_id x) CtrS.FD3_ID) eqn:Ex.
  - injection Hf as <-. assert (Hfx : is_fd_op x = true) by (unfold is_fd_op; rewrite Ex; destruct (PrimInt63.eqb (op_id x) CtrS.FDINIT_ID); reflexivity).
    rewrite Hfx in Hc. destruct Hin as [<-|Hin].
    + apply Uint63.eqb_correct in Ex. destruct x as [xid xargs]; cbn in Ex |- *. subst. reflexivity.
    + exfalso. pose proof (count_fd_nil os ltac:(lia) o Hin). congruence.
  - destruct Hin as [<-|Hin].
    + exfalso. rewrite Hfd in Hc. pose proof (find_op_fd_count os CtrS.FD3_ID args Hf eq_refl). lia.
    + destruct (is_fd_op x); [exfalso; pose proof (find_op_fd_count os CtrS.FD3_ID args Hf eq_refl); lia|].
      exact (IH args o ltac:(apply Nat.eqb_eq; lia) Hf Hin Hfd).
Qed.

Lemma count_ops_set_op_ne : forall id1 id2 args os, PrimInt63.eqb id2 id1 = false ->
  count_ops id1 (set_op id2 args os) = count_ops id1 os.
Proof.
  induction os as [|x os IH]; intros Hne; cbn [set_op count_ops]; [reflexivity|].
  destruct (PrimInt63.eqb (op_id x) id2) eqn:Ex; cbn [count_ops op_id].
  - apply Uint63.eqb_correct in Ex. rewrite Ex, Hne. reflexivity.
  - rewrite (IH Hne). reflexivity.
Qed.

Lemma count_FD3_le_fd : forall os, (count_ops CtrS.FD3_ID os <= count_fd_ops os)%nat.
Proof.
  induction os as [|x os IH]; cbn [count_ops count_fd_ops]; [lia|].
  unfold is_fd_op. destruct (PrimInt63.eqb (op_id x) CtrS.FD3_ID); [rewrite orb_true_r; cbn [orb]; lia|].
  destruct (_ || _); lia.
Qed.

Lemma find_op_count : forall id os args, find_op id os = Some args -> (1 <= count_ops id os)%nat.
Proof.
  induction os as [|x os IH]; intros args Hf; cbn [find_op count_ops] in *; [discriminate Hf|].
  destruct (PrimInt63.eqb (op_id x) id); [lia|]. pose proof (IH args Hf). lia.
Qed.

Lemma count_FD3_one : forall os off, Nat.eqb (count_fd_ops os) 1%nat = true -> find_op CtrS.FD3_ID os = Some [off] ->
  Nat.eqb (count_ops CtrS.FD3_ID os) 1%nat = true.
Proof.
  intros os off Hc Hf. apply Nat.eqb_eq in Hc. apply Nat.eqb_eq.
  pose proof (count_FD3_le_fd os). pose proof (find_op_count _ _ _ Hf). lia.
Qed.

Lemma wbv_Z : forall w, wbv w = Z_to_bv 64 (w2Z w).
Proof.
  intros w. apply bv_eq. rewrite wbv_unsigned, Z_to_bv64_unsigned; [reflexivity|]. rewrite <- wbv_unsigned. apply u64_range.
Qed.

Lemma nth_window : forall (i n k : nat) (l : list byte) d,
  (i < length (firstn n (skipn k l)))%nat -> nth i (firstn n (skipn k l)) d = nth (k + i) l d.
Proof.
  intros i n k l d Hi. rewrite length_firstn in Hi. rewrite nth_firstn.
  destruct (Nat.ltb i n) eqn:Hlt; [apply nth_skipn|]. apply Nat.ltb_ge in Hlt. lia.
Qed.

Lemma len_word_u : forall (bs : list byte), Z.of_nat (length bs) <= 65536 -> bv_unsigned (len_word bs) = Z.of_nat (length bs).
Proof. intros bs H. unfold len_word. apply Z_to_bv64_unsigned. lia. Qed.

Lemma read_post_ok : forall E st ms model off (bs : list byte) (newoff nsv : sv) (fs' : list fact) (os' : list opinst),
  st_ok segs OPS E st ms model -> PrimInt63.ltb (s_pc st) bit62i = true ->
  priv_has st READ_STAGE STAGE_LEN = true ->
  find_op CtrS.FD3_ID (s_ops st) = Some [off] ->
  (exists r1 r2, In (OpI CtrS.RSTAGE_ID [r1; r2]) (s_ops st)) ->
  den E newoff = (den E off + len_word bs)%bv ->
  bv_unsigned (den E off) + Z.of_nat (length bs) <= S ->
  den E nsv = len_word bs -> Z.of_nat (length bs) <= 65536 ->
  (forall i, (i < length bs)%nat -> nth i bs (Z_to_bv 8 0) = nth (Z.to_nat (bv_unsigned (den E off)) + i) file (Z_to_bv 8 0)) ->
  Forall (fact_holds E) fs' ->
  (forall o, In o os' -> o = OpI CtrS.FD3_ID [newoff] \/ o = OpI CtrS.RSTAGE_ID [off; nsv] \/
                         (In o (s_ops st) /\ is_fd_op o = false /\ PrimInt63.eqb (op_id o) CtrS.RSTAGE_ID = false)) ->
  (forall o, In o (s_ops st) -> op_id o = 1%uint63 -> In o os') ->
  let model' := with_fds (fd_insert (m_fds model) fd3 (FdFile p1 (den E off + len_word bs)%bv)) model in
  let acc := syscall_effect_accesses (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 RS) bs) []) in
  materialize_model_accesses model' acc = Some (matz model' acc) /\
  st_ok segs OPS E (SS (PrimInt63.add (s_pc st) 4%uint63) (rf_set (s_rf st) X10 nsv) (s_ff st) (s_resv st) (s_regs st)
                      (fs' ++ s_facts st) os' (s_priv st) (s_next st))
        (svc_post_mem ms (len_word bs) (write_to_mem (ms_mem ms) (Z_to_bv 64 RS) bs))
        (matz model' acc).
Proof.
  intros E st ms model off bs newoff nsv fs' os' HS Hpc62 Hpriv Hf3 [r1 [r2 Hrs]] Hnew Hle Hn Hlen Hbytes Hfs Hos Hkeep model' acc.
  destruct (fds_of_FD3 E st ms model off HS Hf3) as [Hfds Hoff]. pose proof S_range as HSr. pose proof (so_mf _ _ _ _ _ _ HS) as Hmi.
  pose proof RS_range as HR.
  assert (Hlenw : bv_unsigned (len_word bs) = Z.of_nat (length bs)).
  { unfold len_word. apply Z_to_bv64_unsigned. lia. }

  assert (FR : forall a, 0 <= a < two64 -> ~ (RS <= a < RS + 65536) ->
               ms_mem ms (Z_to_bv 64 a) = write_to_mem (ms_mem ms) (Z_to_bv 64 RS) bs (Z_to_bv 64 a)).
  { intros a Ha Hna. symmetry. apply MemP.write_to_mem_frame; lia. }
  apply (st_ok_sys_acc segs OPS E st ms model model'); try assumption.
  - subst model'. apply TM_fds. exact Hmi.
  -   subst model'. unfold ops_hold. apply Forall_forall. intros o Ho.
    destruct (Hos o Ho) as [-> | [-> | (Hin & Hnf & Hnr)]]; cbn [op_id op_args map].
    + cbn [OPS mk_optable_g op_holds]. unfold comp_holds, comp_of. cbn. rewrite m_fds_with_fds, Hfds. cbn.
      rewrite Hnew. split; [reflexivity|]. rewrite bv_add_unsigned, Hlenw. fold S.
      rewrite bv_wrap_small; [lia|]. unfold bv_modulus. pose proof (u64_range (den E off)). lia.
    + cbn [OPS mk_optable_g op_holds]. unfold comp_holds, comp_of. cbn. rewrite Hn, Hlenw. unfold RS_LEN. split; [lia|]. split; [lia|].
      intros i Hi. pose proof (u64_range (den E off)) as Hur. rewrite (MemP.write_to_mem_in (ms_mem ms) RS bs i) by lia.
      rewrite (nth_error_nth' bs (Z_to_bv 8 0)) by lia. f_equal. rewrite (Hbytes (Z.to_nat i)) by lia. f_equal. lia.
    + apply (op_keep_stage E o (ms_mem ms)); [exact Hnf | exact Hnr | exact FR | intros a _ Hm; apply MemP.write_to_mem_mapped; exact Hm |].
      exact (ops_hold_In OPS E _ _ _ _ (so_ops _ _ _ _ _ _ HS) Hin).
  -   unfold ops_apart. apply Forall_forall. intros o Ho a Ha.
    destruct (Hos o Ho) as [-> | [-> | (Hin & _ & _)]].
    + exfalso. revert Ha. cbn [op_id op_args map OPS mk_optable_g op_fp]. unfold comp_of. cbn. intros X; inversion X.
    + revert Ha. cbn [op_id op_args map OPS mk_optable_g op_fp]. unfold comp_of. cbn [oc_fp RSTAGE rstage_fp]. intros Ha.
      pose proof (proj1 (Forall_forall _ _) (so_apart _ _ _ _ _ _ HS) _ Hrs a) as X.
      cbn [op_id op_args map OPS mk_optable_g op_fp] in X. unfold comp_of in X. cbn [oc_fp RSTAGE rstage_fp] in X. exact (X Ha).
    + exact (proj1 (Forall_forall _ _) (so_apart _ _ _ _ _ _ HS) o Hin a Ha).
  -   exact (cover_post E st ms model os' HS Hkeep).
  -   intros a Ha Hout. symmetry. apply FR; [exact Ha|]. intros Hin.
    destruct Hout as [Hseg | Hnp].
    + destruct (stage_wb (ms_mem ms) (a - RS) ltac:(lia)) as [_ [seg Hseg']]. replace (RS + (a - RS)) with a in Hseg' by lia. congruence.
    + apply Hnp. unfold priv_has in Hpriv. apply existsb_exists in Hpriv as ([lo hi] & Hinp & Heq).
      apply andb_prop in Heq as [E1 E2]. cbn [fst snd] in E1, E2. apply Uint63.eqb_correct in E1. apply Uint63.eqb_correct in E2. subst lo hi.
      unfold in_priv. apply Exists_exists. exists (READ_STAGE, PrimInt63.add READ_STAGE STAGE_LEN). split; [exact Hinp|]. cbn [fst snd].
      rewrite HRS. assert (HA : to_Z (PrimInt63.add READ_STAGE STAGE_LEN) = RS + 65536).
      { rewrite Uint63.add_spec, HRS. change (to_Z STAGE_LEN) with 65536. apply Z.mod_small. change wB with (2 ^ 63). lia. }
      rewrite HA. lia.
  -
    intros a b Hb Hnone seg Hseg. assert (Ha : 0 <= bv_unsigned a < two64) by (pose proof (u64_range a); unfold two64; lia).
    destruct (Z_lt_le_dec (bv_unsigned a) RS) as [Hlt|Hge]; [| destruct (Z_lt_le_dec (bv_unsigned a) (RS + 65536)) as [Hlt2|Hge2]].
    + exfalso. rewrite <- (Z_to_bv_bv_unsigned 64 a), <- FR in Hb by lia. rewrite Z_to_bv_bv_unsigned in Hb. congruence.
    + apply (stage_seg_writable (bv_unsigned a - RS) seg); [lia|]. replace (RS + (bv_unsigned a - RS)) with (bv_unsigned a) by lia. exact Hseg.
    + exfalso. rewrite <- (Z_to_bv_bv_unsigned 64 a), <- FR in Hb by lia. rewrite Z_to_bv_bv_unsigned in Hb. congruence.
  -
    intros a n j Hin Hj. subst acc. unfold syscall_effect_accesses in Hin. cbn [eff_copyins eff_writes app] in Hin.
    destruct bs as [|b0 bs']; [destruct Hin|]. cbn [delivered_writes write_accesses] in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <-.
    apply (cover_post E st ms model os' HS Hkeep). right.
    rewrite Z_to_bv_small by (unfold bv_modulus; unfold two64 in HR; lia).
    cbn [length] in Hlen, Hj. destruct (stage_wb (ms_mem ms) j ltac:(lia)) as [_ [seg Hseg]]. exists seg. exact Hseg.
Qed.

Theorem read_file_sound : forall pc, ecall_at segs pc -> contract_sound segs OPS MP PB (c_read_file READ_STAGE pc).
Proof.
  intros pc Hat st sts Hpc Happ K E ms model HS HMP HPB Hk. cbn [c_read_file c_pc c_apply] in Hpc, Happ.
  unfold read_file_apply in Happ.
  destruct (read_pre READ_STAGE st) as [off|] eqn:Hpre; [|discriminate Happ].
  unfold read_pre in Hpre.
  match type of Hpre with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate Hpre] end.
  apply andb_prop in Hc as [Hc Hrs]. apply andb_prop in Hc as [Hc Hpriv]. apply andb_prop in Hc as [Hc H11]. apply andb_prop in Hc as [Hno H10].
  destruct (sysno_ok E st _ Hno) as (H63 & Hpc62 & Hone). rewrite <- Hpc in Hat.
  destruct (find_op CtrS.RSTAGE_ID (s_ops st)) as [[|r1 [|r2 [|? ?]]]|] eqn:Hfr; try discriminate Hrs.
  destruct (find_op CtrS.FD3_ID (s_ops st)) as [[|off' [|? ?]]|] eqn:Hf3; try discriminate Hpre. injection Hpre as ->.
  destruct (fds_of_FD3 E st ms model off HS Hf3) as [Hfds Hoff].
  pose proof (so_mf _ _ _ _ _ _ HS) as Hmi. pose proof (op_minv_halted OPS _ Hmi) as Hh. pose proof S_range as HSr. change (fsize file) with S in Hoff. pose proof (u64_range (den E off)) as Hur.
  pose proof (den_SIZE11_u E HPB) as HS11.
  set (OFF := bv_unsigned (den E off)) in *.
  set (x8 := den E (getr st X17)) in *.
  assert (Ha0 : ms_gpr (pend ms x8) 0 = Z_to_bv 64 3).
  { rewrite pend_gpr, (so_a0 segs OPS E st ms model HS), (is_lit_den E _ _ H10), wlit_word. reflexivity. }
  assert (Ha1 : ms_gpr (pend ms x8) 1 = Z_to_bv 64 RS).
  { rewrite pend_gpr, (so_a1 segs OPS E st ms model HS), (is_lit_den E _ _ H11), wlit_word, HRS. reflexivity. }

  assert (NODE : forall (cnt : word) (bs : list byte) (mo2 : Model),
    ms_gpr (pend ms x8) 2 = cnt -> bv_unsigned cnt <= 2 ^ 40 ->
    bs = file_read file (den E off) (Z_to_bv 64 (rw_count_clamp cnt)) -> Z.of_nat (length bs) <= 65536 ->
    materialize_model_accesses (with_fds (fd_insert (m_fds model) fd3 (FdFile p1 (den E off + len_word bs)%bv)) model)
      (syscall_effect_accesses (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 RS) bs) [])) = Some mo2 ->
    node_ok segs (mkCfg (pend ms x8) model) unit (fun _ => [])
      (fun _ => mkCfg (advance_past_svc (apply_effect (pend ms x8)
                   (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 RS) bs) [])))
                   mo2)).
  { intros cnt bs mo2 Hcnt Hcnt40 Hbs Hlen Hmat.
    destruct (stage_readable_n (pend ms x8) (length bs) Hlen) as [wr Hwr].
    apply (node_silent_a segs (pend ms x8) model x8 unit _ (fun _ => with_fds (fd_insert (m_fds model) fd3 (FdFile p1 (den E off + len_word bs)%bv)) model) (fun _ => mo2) Hh eq_refl
             (fun _ => nonspur_nonalloc segs _ _ _ _ (nonalloc_eq x8 _ H63 eq_refl))).
    - intros o. apply iff_unit.
      assert (X := read_file_outcome (sys_input segs (pend ms x8) x8) model o p1 (den E off) file bs wr).
      rewrite in_sysno_sys_input, !in_arg0, !in_arg1, !in_arg2, in_wmem_sys, Ha0, Ha1, Hcnt, fd32_3 in X.
      apply X; try assumption; try reflexivity.
      + rewrite Hfds. reflexivity.
      + apply access_stage. pose proof (u64_range cnt). lia.
      + apply (MP_file model HMP).
      + rewrite read_bytes_map_eq. unfold word_to_nat, len_word. rewrite Z_to_bv64_unsigned by lia. rewrite Nat2Z.id. exact Hwr.
    - intros _. split; [rewrite m_halted_with_fds; exact Hh | exact Hmat]. }

  assert (TAIL : forall (cnt : word) (bs : list byte) (st' : sstate) (newoff nsv : sv) (fs' : list fact) (os' : list opinst),
    ms_gpr (pend ms x8) 2 = cnt -> bv_unsigned cnt <= 2 ^ 40 ->
    bs = file_read file (den E off) (Z_to_bv 64 (rw_count_clamp cnt)) -> Z.of_nat (length bs) <= 65536 ->
    In st' sts ->
    st' = SS (PrimInt63.add (s_pc st) 4%uint63) (rf_set (s_rf st) X10 nsv) (s_ff st) (s_resv st) (s_regs st)
             (fs' ++ s_facts st) os' (s_priv st) (s_next st) ->
    den E newoff = (den E off + len_word bs)%bv ->
    OFF + Z.of_nat (length bs) <= S ->
    den E nsv = len_word bs ->
    (forall i, (i < length bs)%nat -> nth i bs (Z_to_bv 8 0) = nth (Z.to_nat OFF + i) file (Z_to_bv 8 0)) ->
    Forall (fact_holds E) fs' ->
    (forall o, In o os' -> o = OpI CtrS.FD3_ID [newoff] \/ o = OpI CtrS.RSTAGE_ID [off; nsv] \/
                           (In o (s_ops st) /\ is_fd_op o = false /\ PrimInt63.eqb (op_id o) CtrS.RSTAGE_ID = false)) ->
    (forall o, In o (s_ops st) -> op_id o = 1%uint63 -> In o os') ->
    realizes segs (mkCfg (pend ms x8) model) K).
  { intros cnt bs st' newoff nsv fs' os' Hcnt Hcnt40 Hbs Hlen Hin Hst' Hnew Hle Hn Hbytes Hfs Hos Hkeep.
    destruct (read_post_ok E st ms model off bs newoff nsv fs' os' HS Hpc62 Hpriv Hf3 (ex_intro _ r1 (ex_intro _ r2 (find_op_In _ _ _ Hfr)))
                Hnew Hle Hn Hlen Hbytes Hfs Hos Hkeep) as [Hmat HSok].
    apply (rz_silent_all segs _ unit _ tt K (NODE cnt bs _ Hcnt Hcnt40 Hbs Hlen Hmat)). intros [].
    change (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 RS) bs) []) with
           (mkEffectU (len_word bs) (delivered_writes (Z_to_bv 64 RS) bs) [] [] [] []).
    rewrite svc_post_mem_eq, apply_writes_delivered. cbn [ms_mem pend].
    apply (Hk st' Hin E _ _); [apply env_ext_refl' | exact (MP_mat _ _ _ (MP_fds _ _ HMP) Hmat) |].
    rewrite Hst'. exact HSok. }
  apply (rz_pend segs OPS E st ms model K HS Hat). fold x8.
  assert (H40 : bv_unsigned (den E OFF_MAX) = 2 ^ 40).
  { cbn [den OFF_MAX]. rewrite wbv_unsigned, wlit_ok. reflexivity. }
  assert (Ha2 : ms_gpr (pend ms x8) 2 = den E (getr st X12)) by (rewrite pend_gpr; apply (so_a2 segs OPS E st ms model HS)).
  assert (Hadd0 : forall w : word, (w + len_word (@nil byte))%bv = w).
  { intros w. apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (len_word (@nil byte))) with 0. rewrite Z.add_0_r.
    apply bv_wrap_small. apply u64_range. }
  cbv zeta in Happ.
  destruct (known_leu (s_facts st) SIZE11 off) eqn:Heof.
  -
    destruct (known_leu (s_facts st) off OFF_MAX && known_leu (s_facts st) (getr st X12) OFF_MAX) eqn:Hmx; [|discriminate Happ].
    injection Happ as <-. apply andb_prop in Hmx as [Hom Hcm].
    pose proof (known_leu_sound E st ms model _ _ HS Heof) as H1. rewrite HS11 in H1.
    pose proof (known_leu_sound E st ms model _ _ HS Hom) as H2. rewrite H40 in H2.
    pose proof (known_leu_sound E st ms model _ _ HS Hcm) as H3. rewrite H40 in H3.
    change (bv_unsigned (den E off)) with OFF in H1, H2.
    assert (HOS : OFF = S /\ S = Z.of_nat (length file)) by (unfold S, fsize in *; lia).
    assert (Hbs : (@nil byte) = file_read file (den E off) (Z_to_bv 64 (rw_count_clamp (den E (getr st X12))))).
    { rewrite file_read_unguarded. unfold word_to_nat. change (bv_unsigned (den E off)) with OFF.
      rewrite skipn_all2 by lia. rewrite firstn_nil. reflexivity. }
    apply (TAIL (den E (getr st X12)) [] _ off (VL wzero) [] (set_op CtrS.RSTAGE_ID [off; VL wzero] (s_ops st)) Ha2 H3 Hbs
             ltac:(cbn; lia) (or_introl eq_refl) eq_refl).
    + symmetry. apply Hadd0.
    + cbn [length Z.of_nat]. lia.
    + cbn [den]. rewrite wbv_wzero. reflexivity.
    + intros i Hi. cbn in Hi. lia.
    + constructor.
    + intros o Ho. destruct (set_op_others _ _ _ o Hrs Ho) as [->|[Hin Hne]]; [right; left; reflexivity|].
      destruct (PrimInt63.eqb (op_id o) CtrS.FD3_ID) eqn:E2.
      * left. apply (fd_op_is (s_ops st) [off] o Hone Hf3 Hin). unfold is_fd_op. rewrite E2, orb_true_r. reflexivity.
      * right; right. split; [exact Hin|]. split; [exact (set_fd_others (s_ops st) off o Hone Hf3 Hin E2) | exact Hne].
    + intros o Ho Hid1. apply set_op_keep; [exact Ho| rewrite Hid1; reflexivity].
  -
    destruct (want_ok (getr st X12)) as [w|] eqn:Hw; [|discriminate Happ].
    destruct (want_ok_small _ _ Hw) as [HX12 Hwr].
    destruct (known_leu (s_facts st) (sv_alu ALU_ADD off (VL w)) OFF_MAX) eqn:Hem; [|discriminate Happ]. cbn [negb] in Happ.
    pose proof (known_leu_sound E st ms model _ _ HS Hem) as H2. rewrite H40 in H2.
    set (e := sv_alu ALU_ADD off (VL w)) in *. set (nB := sv_alu ALU_SUB SIZE11 off) in *.
    assert (He : den E e = (den E off + wbv w)%bv) by (subst e; rewrite den_sv_alu; reflexivity).
    assert (Heu : bv_unsigned (den E e) = OFF + w2Z w).
    { rewrite He, bv_add_unsigned, wbv_unsigned. apply bv_wrap_small. unfold bv_modulus. subst OFF. lia. }
    rewrite Heu in H2.
    set (bs := firstn (Z.to_nat (w2Z w)) (skipn (Z.to_nat OFF) file)).
    assert (Hbs : bs = file_read file (den E off) (Z_to_bv 64 (rw_count_clamp (wbv w)))).
    { rewrite (file_read_eq (den E off) (wbv w)) by (rewrite wbv_unsigned; unfold MAX_RW_COUNT; lia). rewrite wbv_unsigned. reflexivity. }
    assert (Hcnt : ms_gpr (pend ms x8) 2 = wbv w) by (rewrite Ha2, HX12; reflexivity).
    assert (Hw40 : bv_unsigned (wbv w) <= 2 ^ 40) by (rewrite wbv_unsigned; lia).
    assert (Hlenbs : length bs = Nat.min (Z.to_nat (w2Z w)) (length file - Z.to_nat OFF)).
    { subst bs. rewrite length_firstn, length_skipn. reflexivity. }
    assert (Hbytes : forall i, (i < length bs)%nat -> nth i bs (Z_to_bv 8 0) = nth (Z.to_nat OFF + i) file (Z_to_bv 8 0)).
    { intros i Hi. subst bs. apply nth_window. exact Hi. }
    assert (Hc2 : forall x : sv, Nat.eqb (count_ops CtrS.FD3_ID (set_op CtrS.RSTAGE_ID [off; x] (s_ops st))) 1%nat = true).
    { intros x. rewrite (count_ops_set_op_ne CtrS.FD3_ID CtrS.RSTAGE_ID) by reflexivity. exact (count_FD3_one _ off Hone Hf3). }

    assert (HOSx : forall (newoff nsv : sv) o,
      In o (set_op CtrS.FD3_ID [newoff] (set_op CtrS.RSTAGE_ID [off; nsv] (s_ops st))) ->
      o = OpI CtrS.FD3_ID [newoff] \/ o = OpI CtrS.RSTAGE_ID [off; nsv] \/
      (In o (s_ops st) /\ is_fd_op o = false /\ PrimInt63.eqb (op_id o) CtrS.RSTAGE_ID = false)).
    { intros newoff nsv o Ho. destruct (set_op_others _ _ _ o (Hc2 nsv) Ho) as [->|[Ho1 Hne2]]; [left; reflexivity|right].
      destruct (set_op_others _ _ _ o Hrs Ho1) as [->|[Hin Hne3]]; [left; reflexivity|right].
      split; [exact Hin|]. split; [exact (set_fd_others (s_ops st) off o Hone Hf3 Hin Hne2) | exact Hne3]. }
    assert (CASE_A : OFF + w2Z w <= S ->
      In (addfact (sysret (set_ops st (set_op CtrS.FD3_ID [e] (set_op CtrS.RSTAGE_ID [off; VL w] (s_ops st)))) (VL w)) (FULe e SIZE11)) sts ->
      realizes segs (mkCfg (pend ms x8) model) K).
    { intros HA Hin.
      assert (Hlw : length bs = Z.to_nat (w2Z w)) by (rewrite Hlenbs; unfold S, fsize in *; lia).
      assert (Hlword : len_word bs = wbv w).
      { unfold len_word. rewrite Hlw, wbv_Z. f_equal. lia. }
      apply (TAIL (wbv w) bs _ e (VL w) [FULe e SIZE11] _ Hcnt Hw40 Hbs ltac:(lia) Hin eq_refl).
      + rewrite Hlword. exact He.
      + rewrite Hlw. lia.
      + rewrite Hlword. reflexivity.
      + exact Hbytes.
      + constructor; [|constructor]. cbn [fact_holds]. rewrite Heu, HS11. exact HA.
      + apply HOSx.
      + intros o Ho Hid1. apply set_op_keep; [apply set_op_keep; [exact Ho| rewrite Hid1; reflexivity]| rewrite Hid1; reflexivity]. }
    assert (CASE_B : S < OFF + w2Z w ->
      In (addfact (sysret (set_ops st (set_op CtrS.FD3_ID [SIZE11] (set_op CtrS.RSTAGE_ID [off; nB] (s_ops st)))) nB) (FULt SIZE11 e)) sts ->
      realizes segs (mkCfg (pend ms x8) model) K).
    { intros HB Hin.
      assert (HSl : S = Z.of_nat (length file)) by (unfold S, fsize in *; lia).
      assert (Hlw : Z.of_nat (length bs) = S - OFF) by (rewrite Hlenbs; lia).
      assert (Hlword : len_word bs = Z_to_bv 64 (S - OFF)).
      { unfold len_word. rewrite Hlw. reflexivity. }
      assert (HnB : den E nB = Z_to_bv 64 (S - OFF)).
      { subst nB. rewrite den_sv_alu. cbn [alu64 alu]. apply bv_eq. rewrite bv_sub_unsigned, HS11, Z_to_bv64_unsigned by lia.
        change (bv_unsigned (den E off)) with OFF. apply bv_wrap_small. unfold bv_modulus. lia. }
      apply (TAIL (wbv w) bs _ SIZE11 nB [FULt SIZE11 e] _ Hcnt Hw40 Hbs ltac:(lia) Hin eq_refl).
      + rewrite Hlword, (den_SIZE11 E HPB). apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv64_unsigned by lia.
        change (bv_unsigned (den E off)) with OFF. replace (OFF + (S - OFF)) with S by lia. symmetry. apply bv_wrap_small. unfold bv_modulus. lia.
      + lia.
      + rewrite Hlword. exact HnB.
      + exact Hbytes.
      + constructor; [|constructor]. cbn [fact_holds]. rewrite Heu, HS11. exact HB.
      + apply HOSx.
      + intros o Ho Hid1. apply set_op_keep; [apply set_op_keep; [exact Ho| rewrite Hid1; reflexivity]| rewrite Hid1; reflexivity]. }
    destruct (decide_ltu (s_facts st) SIZE11 e) as [[|]|] eqn:Hd; injection Happ as <-.
    + apply CASE_B; [|left; reflexivity]. pose proof (decide_ltu_holds E st ms model _ _ _ HS Hd) as X. cbn [negb] in X. rewrite HS11, Heu in X. exact X.
    + apply CASE_A; [|left; reflexivity]. pose proof (decide_ltu_holds E st ms model _ _ _ HS Hd) as X. cbn [negb] in X. rewrite HS11, Heu in X. exact X.
    + destruct (Z_lt_le_dec S (OFF + w2Z w)) as [HB|HA].
      * apply CASE_B; [exact HB | right; left; reflexivity].
      * apply CASE_A; [lia | left; reflexivity].
Qed.

Hypothesis PB_arg1 : forall b, PB b -> b 3%uint63 = p1 ++ [Z_to_bv 8 0] /\ b 10%uint63 = Z_to_le_bytes 8 (Z.of_nat (length p1) + 1).
Hypothesis p1_nz : ~ In (Z_to_bv 8 0) p1.
Hypothesis p1_len : Z.of_nat (length p1) <= 131071.

Lemma fdcwd_ok : bv_eqb (fd32 (wbv AT_FDCWD_w)) AT_FDCWD32 = true.
Proof. unfold bv_eqb. apply Z.eqb_eq. vm_compute. reflexivity. Qed.

Lemma flags_ok : forall E v, open_flags_ok v = true -> Z.ldiff (bv_unsigned (den E v)) open_ignored_flags = 0.
Proof.
  intros E v H. unfold open_flags_ok in H. apply orb_prop in H as [H|H]; rewrite (is_lit_den E _ _ H), wbv_unsigned.
  - rewrite wlit_ok. reflexivity.
  - change (w2Z wzero) with 0. reflexivity.
Qed.

Lemma alloc_fd_FDS0 : alloc_fd FDS0 = fd3.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma lookup3_FDS0 : fd_lookup FDS0 fd3 = None.
Proof. reflexivity. Qed.
Lemma insert3_FDS0 : forall e, fd_insert FDS0 fd3 e = (fd3, e) :: FDS0.
Proof. intros e. reflexivity. Qed.

Lemma nth_open_errnos : forall n, In (nth n open_errnos ENOMEM) openat_errnos.
Proof. intros [|[|[|[|[|n]]]]]; cbn; tauto. Qed.

Lemma open_pre_facts : forall E st ms model,
  st_ok segs OPS E st ms model -> PB (eb E) -> open_pre st = true ->
  let x8 := den E (getr st X17) in
  let i := sys_input segs (pend ms x8) x8 in
  let A := bv_unsigned (ev E 10%uint63) in
  bv_unsigned (in_sysno i) = 56 /\
  bv_eqb (fd32 (in_arg i 0)) AT_FDCWD32 = true /\
  Z.ldiff (bv_unsigned (in_arg i 2)) open_ignored_flags = 0 /\
  modeled_open_flags (in_arg i 2) = true /\
  in_arg i 1 = Z_to_bv 64 A /\
  A + (Z.of_nat (length p1) + 1) < two64 /\
  (forall j, (j <= length p1)%nat -> in_mem i (Z_to_bv 64 (A + Z.of_nat j)) = Some (nth j (p1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) /\
  m_fds model = FDS0 /\
  PrimInt63.ltb (s_pc st) bit62i = true /\ one_fd_op st = true /\ find_op CtrS.FDINIT_ID (s_ops st) = Some [].
Proof.
  intros E st ms model HS HPB H. unfold open_pre in H.
  apply andb_prop in H as [H Hfd]. apply andb_prop in H as [H Hreg]. apply andb_prop in H as [H Hfl].
  apply andb_prop in H as [H H11]. apply andb_prop in H as [Hno H10].
  destruct (sysno_ok E st _ Hno) as (H56 & Hpc62 & Hone).
  destruct (find_op CtrS.FDINIT_ID (s_ops st)) as [[|? ?]|] eqn:Hf5; try discriminate Hfd.
  destruct (PB_arg1 _ HPB) as [Hb3 Hb10]. pose proof (u64_range (ev E 10%uint63)) as HA.

  unfold region10_ok in Hreg.
  destruct (IMap.find 10%uint63 (s_regs st)) as [[lo hi w bg cells]|] eqn:Hr; [|discriminate Hreg].
  destruct bg as [| | | |j sh]; try discriminate Hreg.
  apply andb_prop in Hreg as [Hreg Hcells]. apply andb_prop in Hreg as [Hreg Hsh]. apply andb_prop in Hreg as [Hreg Hj].
  apply andb_prop in Hreg as [Hreg Hw]. apply andb_prop in Hreg as [Hlo Hhi].
  apply Uint63.eqb_correct in Hlo. apply sv_eqb_eq in Hhi. apply Uint63.eqb_correct in Hj. apply Uint63.eqb_correct in Hsh.
  destruct w; [discriminate Hw|]. destruct cells; [|discriminate Hcells]. subst lo hi j sh.
  pose proof (so_reg _ _ _ _ _ _ HS 10%uint63 _ Hr) as R.
  assert (HhiZ : hiZ E (Region 0%uint63 SIZE10 false (BGBlob 3%uint63 0%uint63) IMap.Leaf) = Z.of_nat (length p1) + 1).
  { unfold hiZ. cbn [rg_hi]. unfold SIZE10. apply (den_param8_u E 10%uint63 _ Hb10). lia. }
  assert (HloZ : loZ (Region 0%uint63 SIZE10 false (BGBlob 3%uint63 0%uint63) IMap.Leaf) = 0) by reflexivity.
  pose proof (ro_range _ _ _ _ _ _ R eq_refl) as Hrange. rewrite HhiZ, HloZ in Hrange.
  cbv zeta. repeat split.
  - rewrite in_sysno_sys_input. exact H56.
  - rewrite in_arg0, pend_gpr, (so_a0 segs OPS E st ms model HS), (is_lit_den E _ _ H10). apply fdcwd_ok.
  - rewrite in_arg2, pend_gpr, (so_a2 segs OPS E st ms model HS). apply flags_ok. exact Hfl.
  - rewrite in_arg2, pend_gpr, (so_a2 segs OPS E st ms model HS). apply modeled_open_flags_rd. apply flags_ok. exact Hfl.
  - rewrite in_arg1, pend_gpr, (so_a1 segs OPS E st ms model HS), (sv_eqb_eq _ _ H11). cbn [den]. rewrite wbv_wzero.
    apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. rewrite Z.add_0_r. reflexivity.
  - lia.
  - intros j Hj. rewrite in_mem_sys. unfold ms_read_byte. cbn [ms_mem ms_rom pend]. rewrite (so_rom _ _ _ _ _ _ HS).
    pose proof (ro_bg _ _ _ _ _ _ R (Z.of_nat j)) as B.
    cbn [rg_bg rg_cells bg_byte] in B. rewrite HhiZ, HloZ in B. change (to_Z 0%uint63) with 0 in B. rewrite Z.sub_0_r, Nat2Z.id, Hb3 in B.
    unfold rb in B. apply B.
    + intros _. lia.
    + intros X; discriminate X.
    + intros g gr _ Hg. cbn in Hg. discriminate Hg.
  - exact (fds_of_FDINIT E st ms model HS Hf5).
  - exact Hpc62.
  - exact Hone.
Qed.

Lemma open_path_acc : forall E st ms model,
  st_ok segs OPS E st ms model -> PB (eb E) -> open_pre st = true ->
  let x8 := den E (getr st X17) in
  let i := sys_input segs (pend ms x8) x8 in
  forall a n j, In (a, n) (CP i) -> 0 <= j < Z.of_nat n -> fx_acc segs E (s_regs st) (bv_unsigned a + j).
Proof.
  intros E st ms model HS HPB Hpre x8 i a n j Hin Hj.
  destruct (open_pre_facts E st ms model HS HPB Hpre) as (H56 & Hcwd & Hld & Hmf & Ha1 & HA & Hmem & Hfds & Hpc62 & Hone & Hf5).
  fold x8 in Ha1, Hmem. fold i in Ha1, Hmem.
  unfold CP in Hin. destruct Hin as [Hin|[]].
  pose proof (f_equal fst Hin) as Ea. pose proof (f_equal snd Hin) as En. cbn [fst snd] in Ea, En. clear Hin. subst a n.
  rewrite Ha1 in Hj. rewrite Ha1.
  pose proof (cstr_access_len_le (in_mem i) p1 (bv_unsigned (ev E 10%uint63)) path_max p1_nz Hmem) as L.
  pose proof (u64_range (ev E 10%uint63)) as HAr.
  rewrite Z_to_bv_small by (unfold bv_modulus; unfold two64 in *; lia).

  unfold open_pre in Hpre. apply andb_prop in Hpre as [Hpre _]. apply andb_prop in Hpre as [_ Hreg].
  unfold region10_ok in Hreg.
  destruct (IMap.find 10%uint63 (s_regs st)) as [[lo hi w bg cells]|] eqn:Hr; [|discriminate Hreg].
  destruct bg as [| | | |jj sh]; try discriminate Hreg.
  apply andb_prop in Hreg as [Hreg Hcells]. apply andb_prop in Hreg as [Hreg Hsh]. apply andb_prop in Hreg as [Hreg Hjj].
  apply andb_prop in Hreg as [Hreg Hw]. apply andb_prop in Hreg as [Hlo Hhi].
  apply Uint63.eqb_correct in Hlo. apply sv_eqb_eq in Hhi. subst lo hi.
  destruct (PB_arg1 _ HPB) as [Hb3 Hb10].
  left. exists 10%uint63, (Region 0%uint63 SIZE10 w (BGBlob jj sh) cells). split; [exact Hr|]. split; [reflexivity|].
  assert (HhiZ : hiZ E (Region 0%uint63 SIZE10 w (BGBlob jj sh) cells) = Z.of_nat (length p1) + 1).
  { unfold hiZ. cbn [rg_hi]. unfold SIZE10. apply (den_param8_u E 10%uint63 _ Hb10). lia. }
  rewrite HhiZ. change (loZ (Region 0%uint63 SIZE10 w (BGBlob jj sh) cells)) with 0. lia.
Qed.

Section Absent.
Hypothesis fam_absent : path_has_slash p1 = false /\ path_is_dirref p1 = false /\ (length p1 < 4096)%nat /\
                        (p1 = [] \/ forall model, MP model -> fs_lookup (m_fs model) p1 = None).

Theorem open_absent_sound : forall pc, ecall_at segs pc -> contract_sound segs OPS MP PB (c_open_absent pc).
Proof.
  intros pc Hat st sts Hpc Happ K E ms model HS HMP HPB Hk. cbn [c_open_absent c_pc c_apply] in Hpc, Happ.
  unfold open_absent_apply in Happ. destruct (open_pre st) eqn:Hpre; [|discriminate Happ]. injection Happ as <-.
  destruct (open_pre_facts E st ms model HS HPB Hpre) as (H56 & Hcwd & Hld & Hmf & Ha1 & HA & Hmem & Hfds & Hpc62 & Hone & Hf5).
  destruct fam_absent as (Hsl & Hdr & Hlen & Habs).
  rewrite <- Hpc in Hat. set (x8 := den E (getr st X17)) in *. set (i := sys_input segs (pend ms x8) x8) in *.
  assert (Hcs : read_cstr (in_mem i) (in_arg i 1) = CstrOk p1).
  { rewrite Ha1. unfold read_cstr. apply read_cstr_aux_ok; [exact p1_nz | unfold path_max; exact Hlen | exact Hmem]. }
  apply (det_nomem_tail_cp pc st K E ms model (errno_ret ENOENT) (errv ENOENT) 56 (CP i) HS Hat HMP); try assumption;
    [| | exact (open_path_acc E st ms model HS HPB Hpre) |].
  - apply neg_den.
  - intros o. apply (openat_absent_outcome i model o p1 H56 Hld Hcs Hcwd Hsl Hdr).
    destruct Habs as [Habs|Habs]; [left; rewrite Habs; reflexivity | right; exact (Habs model HMP)].
  - intros E' ms' model' HX HMP' HS'. exact (Hk _ (or_introl eq_refl) E' ms' model' HX HMP' HS').
Qed.
End Absent.

Section TooLong.
Hypothesis fam_toolong : (4096 <= length p1)%nat.

Theorem open_toolong_sound : forall pc, ecall_at segs pc -> contract_sound segs OPS MP PB (c_open_toolong pc).
Proof.
  intros pc Hat st sts Hpc Happ K E ms model HS HMP HPB Hk. cbn [c_open_toolong c_pc c_apply] in Hpc, Happ.
  unfold open_toolong_apply in Happ. destruct (open_pre st) eqn:Hpre; [|discriminate Happ]. injection Happ as <-.
  destruct (open_pre_facts E st ms model HS HPB Hpre) as (H56 & Hcwd & Hld & Hmf & Ha1 & HA & Hmem & Hfds & Hpc62 & Hone & Hf5).
  rewrite <- Hpc in Hat. set (x8 := den E (getr st X17)) in *. set (i := sys_input segs (pend ms x8) x8) in *.
  assert (Hcs : read_cstr (in_mem i) (in_arg i 1) = CstrTooLong).
  { rewrite Ha1. unfold read_cstr. apply (read_cstr_aux_toolong _ _ _ (fun j => nth j p1 (Z_to_bv 8 0))).
    intros j Hj. unfold path_max in Hj. split.
    - rewrite (Hmem j) by lia. rewrite app_nth1 by lia. reflexivity.
    - intros Hz. apply p1_nz. rewrite <- Hz. apply nth_In. lia. }
  apply (det_nomem_tail_cp pc st K E ms model (errno_ret ENAMETOOLONG) (errv ENAMETOOLONG) 56 (CP i) HS Hat HMP); try assumption;
    [| | exact (open_path_acc E st ms model HS HPB Hpre) |].
  - apply neg_den.
  - intros o. apply (openat_toolong_outcome i model o H56 Hmf Hcs).
  - intros E' ms' model' HX HMP' HS'. exact (Hk _ (or_introl eq_refl) E' ms' model' HX HMP' HS').
Qed.
End TooLong.

Definition open_entry (isfile : bool) : FdEntry := if isfile then FdFile p1 (Z_to_bv 64 0) else FdDir.
Definition open_newop (isfile : bool) : opinst := if isfile then OpI CtrS.FD3_ID [VL wzero] else OpI CtrS.FD3DIR_ID [].
Definition open_okpost (isfile : bool) (st : sstate) : sstate :=
  sysret (set_ops st (open_newop isfile :: remove_op CtrS.FDINIT_ID (s_ops st))) (VL (wlit 3%uint63)).

Lemma open_fork : forall (isfile : bool) st (KA KB : TSet) E ms model,
  open_pre st = true ->
  st_ok segs OPS E st ms model -> MP model -> PB (eb E) -> ecall_at segs (s_pc st) ->
  let x8 := den E (getr st X17) in
  let i := sys_input segs (pend ms x8) x8 in
  (forall o, syscall_spec i model o <->
     (exists e, In e openat_errnos /\ o = Ok (open_err e i) model []) \/
     (exists fd, fd_lookup (m_fds model) fd = None /\ fd = alloc_fd (m_fds model) /\
                 o = Ok (open_ret fd i) (with_fds (fd_insert (m_fds model) fd (open_entry isfile)) model) [])) ->
  (forall ms' model', MP model' -> st_ok segs OPS E (open_okpost isfile st) ms' model' -> realizes segs (mkCfg ms' model') KA) ->
  (forall st', In st' (open_err_posts st) ->
     forall ms' model', MP model' -> st_ok segs OPS E st' ms' model' -> realizes segs (mkCfg ms' model') KB) ->
  realizes segs (mkCfg ms model) (t_alt2 KA KB).
Proof.
  intros isfile st KA KB E ms model Hpre HS HMP HPB Hat x8 i Hspec HA HB.
  destruct (open_pre_facts E st ms model HS HPB Hpre) as (H56 & Hcwd & Hld & Hmf & Ha1 & HAA & Hmem & Hfds & Hpc62 & Hone & Hf5).
  pose proof (so_mf _ _ _ _ _ _ HS) as Hmi. pose proof (op_minv_halted OPS _ Hmi) as Hh.
  pose proof (open_path_acc E st ms model HS HPB Hpre) as PACC. fold x8 in PACC. fold i in PACC.
  set (model' := with_fds (fd_insert (m_fds model) fd3 (open_entry isfile)) model).

  assert (SUCC : materialize_model_accesses model' (syscall_effect_accesses (open_ret fd3 i)) = Some (matz model' (syscall_effect_accesses (open_ret fd3 i))) /\
                 st_ok segs OPS E (open_okpost isfile st) (svc_post_mem ms fd3 (ms_mem ms)) (matz model' (syscall_effect_accesses (open_ret fd3 i)))).
  { unfold open_okpost.
    change (sysret (set_ops st (open_newop isfile :: remove_op CtrS.FDINIT_ID (s_ops st))) (VL (wlit 3%uint63))) with
      (SS (PrimInt63.add (s_pc st) 4%uint63) (rf_set (s_rf st) X10 (VL (wlit 3%uint63))) (s_ff st) (s_resv st) (s_regs st)
          ([] ++ s_facts st) (open_newop isfile :: remove_op CtrS.FDINIT_ID (s_ops st)) (s_priv st) (s_next st)).
    assert (KEEP : forall o, In o (s_ops st) -> op_id o = 1%uint63 -> In o (open_newop isfile :: remove_op CtrS.FDINIT_ID (s_ops st))).
    { intros o Ho Hid1. right. apply remove_op_keep; [exact Ho| rewrite Hid1; reflexivity]. }
    apply (st_ok_sys_acc segs OPS E st ms model model' fd3 (VL (wlit 3%uint63))); try assumption.
    + cbn [den]. rewrite wlit_word. reflexivity.
    + constructor.
    + subst model'. apply TM_fds. exact Hmi.
    + subst model'. apply (ops_hold_fd_update E st ms model _ (open_newop isfile)); [exact HS| |].
      * cbn [op_id op_args map OPS mk_optable_g op_holds]. unfold comp_holds, comp_of.
        destruct isfile; cbn; rewrite Hfds; cbn.
        -- rewrite wbv_wzero. split; [reflexivity|]. unfold fsize. match goal with |- ?x <= _ => replace x with 0 by reflexivity end. lia.
        -- reflexivity.
      * intros o [<-|Ho]; [left; reflexivity | right]. split; [exact (remove_op_subset _ _ _ Ho)|].
        exact (remove_fd_op_others (s_ops st) CtrS.FDINIT_ID [] Hone Hf5 eq_refl o Ho).
    + apply (ops_apart_fd_update E st ms model (open_newop isfile)); [exact HS | destruct isfile; reflexivity |].
      intros o [<-|Ho]; [left; reflexivity | right; exact (remove_op_subset _ _ _ Ho)].
    + exact (cover_post E st ms model _ HS KEEP).
    + intros a _ _. reflexivity.
    + intros a b Hb Hn. rewrite Hb in Hn. discriminate Hn.
    + intros a n j Hin Hj. unfold syscall_effect_accesses, open_ret in Hin. cbn [eff_copyins eff_writes write_accesses] in Hin. rewrite app_nil_r in Hin.
      exact (cover_post E st ms model _ HS KEEP _ (PACC a n j Hin Hj)). }
  assert (ERR : forall e, materialize_model_accesses model (syscall_effect_accesses (open_err e i)) = Some (matz model (syscall_effect_accesses (open_err e i))) /\
                 st_ok segs OPS E (sysret st (errv e)) (svc_post_mem ms (errno_ret e) (ms_mem ms)) (matz model (syscall_effect_accesses (open_err e i)))).
  { intros e.
    change (sysret st (errv e)) with
      (SS (PrimInt63.add (s_pc st) 4%uint63) (rf_set (s_rf st) X10 (errv e)) (s_ff st) (s_resv st) (s_regs st)
          ([] ++ s_facts st) (s_ops st) (s_priv st) (s_next st)).
    apply (st_ok_sys_acc segs OPS E st ms model model (errno_ret e) (errv e)); try assumption.
    + apply neg_den.
    + constructor.
    + exact (so_ops _ _ _ _ _ _ HS).
    + exact (so_apart _ _ _ _ _ _ HS).
    + exact (cover_same E st ms model HS).
    + intros a _ _. reflexivity.
    + intros a b Hb Hn. rewrite Hb in Hn. discriminate Hn.
    + intros a n j Hin Hj. unfold syscall_effect_accesses, open_err in Hin. cbn [eff_copyins eff_writes write_accesses] in Hin. rewrite app_nil_r in Hin.
      exact (cover_same E st ms model HS _ (PACC a n j Hin Hj)). }
  apply (rz_pend segs OPS E st ms model _ HS Hat). fold x8.
  set (EFF := fun x : unit + nat => match x with inl _ => open_ret fd3 i | inr n => open_err (nth n open_errnos ENOMEM) i end).
  set (MO := fun x : unit + nat => match x with inl _ => model' | inr _ => model end).
  set (MO2 := fun x : unit + nat => matz (MO x) (syscall_effect_accesses (EFF x))).
  apply (rz_alt2 segs (mkCfg (pend ms x8) model) unit nat (fun x => mkCfg (advance_past_svc (apply_effect (pend ms x8) (EFF x))) (MO2 x))
           KA KB tt 0%nat).
  -
    apply (node_silent_a segs (pend ms x8) model x8 (unit + nat) EFF MO MO2 Hh eq_refl
             (fun _ => nonspur_nonalloc segs _ _ _ _ (nonalloc_eq x8 _ H56 eq_refl))).
    + intros o. subst model'. split.
      * intros Ho. apply (proj1 (Hspec o)) in Ho. rewrite Hfds, alloc_fd_FDS0 in Ho. destruct Ho as [(e & He & ->) | (fd & _ & -> & ->)].
        -- destruct (In_nth _ _ ENOMEM He) as (n & _ & Hn). exists (inr n). cbn [EFF MO]. change open_errnos with openat_errnos. rewrite Hn. reflexivity.
        -- exists (inl tt). cbn [EFF MO]. rewrite Hfds. reflexivity.
      * intros [[[]|n] ->]; cbn [EFF MO]; apply (proj2 (Hspec _)); rewrite Hfds, ?alloc_fd_FDS0.
        -- right. exists fd3. split; [apply lookup3_FDS0|]. split; reflexivity.
        -- left. exists (nth n open_errnos ENOMEM). split; [apply nth_open_errnos | reflexivity].
    + intros [[]|n]; unfold MO2; cbn [MO EFF].
      * split; [subst model'; rewrite m_halted_with_fds; exact Hh | exact (proj1 SUCC)].
      * split; [exact Hh | exact (proj1 (ERR _))].
  -   intros []. unfold MO2. cbn [EFF MO]. unfold open_ret. rewrite svc_post_mem_eq. cbn [apply_writes].
    apply (HA _ _ (MP_mat _ _ _ (MP_fds _ _ HMP) (proj1 SUCC))). exact (proj2 SUCC).
  -   intros n. unfold MO2. cbn [EFF MO]. unfold open_err. rewrite svc_post_mem_eq. cbn [apply_writes].
    set (e := nth n open_errnos ENOMEM).
    apply (HB (sysret st (errv e))).
    { unfold open_err_posts. apply (in_map (fun e0 => sysret st (errv e0))). unfold open_errnos. apply nth_open_errnos. }
    { exact (MP_mat _ _ _ HMP (proj1 (ERR e))). }
    exact (proj2 (ERR e)).
Qed.

Section File.
Hypothesis fam_file : path_has_slash p1 = false /\ path_is_dirref p1 = false /\ (length p1 < 4096)%nat /\ p1 <> [].

Theorem open_file_fork : forall st sts (KA KB : TSet) E ms model,
  open_file_apply st = Some sts ->
  st_ok segs OPS E st ms model -> MP model -> PB (eb E) -> ecall_at segs (s_pc st) ->
  (forall ms' model', MP model' -> st_ok segs OPS E (hd st sts) ms' model' -> realizes segs (mkCfg ms' model') KA) ->
  (forall st', In st' (tl sts) ->
     forall ms' model', MP model' -> st_ok segs OPS E st' ms' model' -> realizes segs (mkCfg ms' model') KB) ->
  realizes segs (mkCfg ms model) (t_alt2 KA KB).
Proof.
  intros st sts KA KB E ms model Happ HS HMP HPB Hat HA HB.
  unfold open_file_apply in Happ. destruct (open_pre st) eqn:Hpre; [|discriminate Happ]. injection Happ as <-.
  cbn [hd tl] in HA, HB. destruct fam_file as (Hsl & Hdr & Hlen & Hne).
  destruct (open_pre_facts E st ms model HS HPB Hpre) as (H56 & Hcwd & Hld & Hmf & Ha1 & HAA & Hmem & Hfds & Hpc62 & Hone & Hf5).
  apply (open_fork true st KA KB E ms model Hpre HS HMP HPB Hat); [|exact HA|exact HB].
  set (x8 := den E (getr st X17)) in *. set (i := sys_input segs (pend ms x8) x8) in *.
  assert (Hcs : read_cstr (in_mem i) (in_arg i 1) = CstrOk p1).
  { rewrite Ha1. unfold read_cstr. apply read_cstr_aux_ok; [exact p1_nz | unfold path_max; exact Hlen | exact Hmem]. }
  intros o. apply (openat_file_outcome i model o p1 file H56 Hld Hcs); try assumption.
  - assert (G : forall p : list byte, p <> [] -> path_eqb p [] = false) by (intros [|b p] Hp; [exfalso; apply Hp; reflexivity | reflexivity]).
    exact (G p1 Hne).
  - exact (MP_file model HMP).
Qed.
End File.

Section Dir.
Hypothesis fam_dir : path_is_dirref p1 = true.

Lemma dirref_facts : path_has_slash p1 = false /\ (length p1 < 4096)%nat /\ path_eqb p1 [] = false.
Proof.
  unfold path_is_dirref in fam_dir. apply orb_prop in fam_dir as [H|H]; apply path_eqb_eq in H; rewrite H; cbn; repeat split; try reflexivity; lia.
Qed.

Theorem open_dir_fork : forall st sts (KA KB : TSet) E ms model,
  open_dir_apply st = Some sts ->
  st_ok segs OPS E st ms model -> MP model -> PB (eb E) -> ecall_at segs (s_pc st) ->
  (forall ms' model', MP model' -> st_ok segs OPS E (hd st sts) ms' model' -> realizes segs (mkCfg ms' model') KA) ->
  (forall st', In st' (tl sts) ->
     forall ms' model', MP model' -> st_ok segs OPS E st' ms' model' -> realizes segs (mkCfg ms' model') KB) ->
  realizes segs (mkCfg ms model) (t_alt2 KA KB).
Proof.
  intros st sts KA KB E ms model Happ HS HMP HPB Hat HA HB.
  unfold open_dir_apply in Happ. destruct (open_pre st) eqn:Hpre; [|discriminate Happ]. injection Happ as <-.
  cbn [hd tl] in HA, HB. destruct dirref_facts as (Hsl & Hlen & Hne).
  destruct (open_pre_facts E st ms model HS HPB Hpre) as (H56 & Hcwd & Hld & Hmf & Ha1 & HAA & Hmem & Hfds & Hpc62 & Hone & Hf5).
  apply (open_fork false st KA KB E ms model Hpre HS HMP HPB Hat); [|exact HA|exact HB].
  set (x8 := den E (getr st X17)) in *. set (i := sys_input segs (pend ms x8) x8) in *.
  assert (Hcs : read_cstr (in_mem i) (in_arg i 1) = CstrOk p1).
  { rewrite Ha1. unfold read_cstr. apply read_cstr_aux_ok; [exact p1_nz | unfold path_max; exact Hlen | exact Hmem]. }
  intros o. apply (openat_dir_outcome i model o p1 H56 Hld Hcs Hne Hcwd Hsl fam_dir).
Qed.
End Dir.

End Drv.

End CtrSys.
