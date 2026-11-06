(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import CatSim PropExec.

Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanAcct () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.Build_machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_regs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_fregs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_pc_val"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_resv"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_fcsr"; "mrestrict"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_rom"; "munrestrict"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.andb"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_executable"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_writable"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_size"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.nat"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.and"; "range_avoids"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Logic.not"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.false"; "Stdlib.ZArith.BinInt.Z.of_nat"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.seg_ov_read_bytes"; "LinuxProcessSemantics.Riscv.Sem.eff"; "LinuxProcessSemantics.Riscv.Sem.core"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_access"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_report"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.interp_eff_accesses"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.mkAccessReport"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.ex"; "ranges_avoid"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.decode_exec_accesses"; "restrict"; "unrestrict"; "hclean"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step_accesses"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_value"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.accessed_ranges"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_reg"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Stdlib.Lists.List.existsb"; "Stdlib.ZArith.BinInt.Z.leb"; "Corelib.Init.Datatypes.fst"; "LinuxProcessSemantics.LinuxProcessSem.State.page_size"; "Corelib.Init.Datatypes.snd"; "Corelib.Lists.ListDef.Forall"; "Stdlib.ZArith.BinInt.Z.modulo"; "LinuxProcessSemantics.LinuxProcessSem.State.page_in_ranges"; "LinuxProcessSemantics.LinuxProcessSem.State.page_base"; "page_allowedb"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_backing_used"; "eager_used"; "Stdlib.ZArith.BinInt.Z.mul"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "same_but_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.FdState"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fd"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.IoState"; "LinuxProcessSemantics.LinuxProcessSem.State.m_io"; "LinuxProcessSemantics.LinuxProcessSem.State.FsState"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fsys"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcState"; "LinuxProcessSemantics.LinuxProcessSem.State.m_proc"; "LinuxProcessSemantics.LinuxProcessSem.State.LimState"; "LinuxProcessSemantics.LinuxProcessSem.State.m_lim"; "LinuxProcessSemantics.LinuxProcessSem.State.TimeState"; "LinuxProcessSemantics.LinuxProcessSem.State.m_time"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.PipeBuf"; "LinuxProcessSemantics.LinuxProcessSem.State.m_pipes"; "LinuxProcessSemantics.LinuxProcessSem.State.InputStream"; "LinuxProcessSemantics.LinuxProcessSem.State.m_stdin"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "LinuxProcessSemantics.LinuxProcessSem.State.m_tid"; "LinuxProcessSemantics.LinuxProcessSem.State.m_rlimit_core"; "LinuxProcessSemantics.LinuxProcessSem.State.m_clock"; "A_wf"; "A_pages"; "Stdlib.Lists.List.NoDup"; "A_bytes"; "LinuxProcessSemantics.LinuxProcessSem.State.access_pages_acc"; "Corelib.Init.Logic.or"; "Corelib.Init.Peano.lt"; "LinuxProcessSemantics.LinuxProcessSem.State.page_base_of"; "LinuxProcessSemantics.LinuxProcessSem.State.accesses_pages"; "lazy_cover"; "LinuxProcessSemantics.LinuxProcessSem.State.newly_materialized_pages"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "MInv"; "LinuxProcessSemantics.LinuxProcessSem.State.with_vm_backing"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "LinuxProcessSemantics.LinuxProcessSem.Run.mi_account_step"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "Nodes.node_ok"; "Corelib.Init.Datatypes.unit"; "OSSVerify.KrLib.ABoot.CatSim.msteps"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Ok"; "LinuxProcessSemantics.LinuxProcessSem.Monad.outcome"; "LinuxProcessSemantics.LinuxProcessSem.State.syscall_effect_accesses"; "materialized_succ"; "node_ok"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "Stdlib.Lists.List.forallb"; "Corelib.Init.Datatypes.orb"; "Corelib.Init.Datatypes.negb"; "seg_top"; "segs_below_b"; "H_off_segments"; "ranges_from_b"; "mkH"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mrestrict (H : word -> bool) (m : word -> option byte)
    : word -> option byte :=
  fun a => if H a then None else m a.

(* [comment removed for export] *)
Definition munrestrict (H : word -> bool) (full m' : word -> option byte)
    : word -> option byte :=
  fun a => if H a then full a else m' a.

Definition restrict (H : word -> bool) (ms : machine_state) : machine_state := ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "(0.(1.O1.)(2.O1.)(3.O1.)(4.O1.)(5.O1.)(6.O1.)(7.O2.(8.O1.))(9.O1.))")
(* [comment removed for export] *).

Definition unrestrict (H : word -> bool) (full : word -> option byte)
    (ms' : machine_state) : machine_state := ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "(0.(1.O1.)(2.O1.)(3.O1.)(4.O1.)(5.O1.)(6.O1.)(:.O3.O2.(8.O1.))(9.O1.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition H_off_segments (segs : list Segment) (H : word -> bool) : Prop :=
  forall a, H a = true -> find_segment segs (bv_unsigned a) 1 = None.

(* [comment removed for export] *)
Definition wx_segs_nowrap (segs : list Segment) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pseg,$;.P,(<.$;.R1.O1.)P,(=.$>.(?.(10.R2.)(11.R2.))$12.)(13.(14.(15.(16.R3.))(15.(17.R3.)))(18.+2.+40.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition woff (a : word) (k : nat) : word :=
  Z_to_bv 64 (bv_unsigned a + Z.of_nat k).

Definition range_avoids (H : word -> bool) (a : word) (n : nat) : Prop :=
  forall k, (k < n)%nat -> H (woff a k) = false.

Definition ranges_avoid (H : word -> bool) (l : list (word * nat)) : Prop :=
  forall a n, In (a, n) l -> range_avoids H a n.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma woff_0 : forall a, woff a 0 = a.
Proof.
  intros a. unfold woff. apply bv_eq. rewrite Z_to_bv_unsigned.
  rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma woff_succ : forall a k, woff (a + 1) k = woff a (S k).
Proof.
  intros a k. unfold woff. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
  assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma range_avoids_hd : forall H a n,
  range_avoids H a (S n) -> H a = false.
Proof.
  intros H a n Hr. rewrite <- (woff_0 a). apply Hr. lia.
Qed.

Lemma range_avoids_tl : forall H a n,
  range_avoids H a (S n) -> range_avoids H (a + 1) n.
Proof.
  intros H a n Hr k Hk. rewrite woff_succ. apply Hr. lia.
Qed.

Lemma range_avoids_cons : forall H a n,
  H a = false -> range_avoids H (a + 1) n -> range_avoids H a (S n).
Proof.
  intros H a n H0 Hr k Hk. destruct k as [|k].
  - rewrite woff_0. exact H0.
  - rewrite <- woff_succ. apply Hr. lia.
Qed.

Lemma ranges_avoid_nil : forall H, ranges_avoid H [].
Proof. intros H a n Hin. destruct Hin. Qed.

Lemma ranges_avoid_cons : forall H a n l,
  range_avoids H a n -> ranges_avoid H l -> ranges_avoid H ((a, n) :: l).
Proof.
  intros H a n l Ha Hl a' n' [Heq | Hin].
  - injection Heq as <- <-. exact Ha.
  - exact (Hl a' n' Hin).
Qed.

Lemma ranges_avoid_app : forall H l1 l2,
  ranges_avoid H l1 -> ranges_avoid H l2 -> ranges_avoid H (l1 ++ l2).
Proof.
  intros H l1 l2 H1 H2 a n Hin. apply in_app_or in Hin as [Hin | Hin];
    [exact (H1 a n Hin) | exact (H2 a n Hin)].
Qed.

(* [comment removed for export] *)
Lemma restrict_svc_pending : forall H ms,
  ms_svc_pending (restrict H ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.
Lemma restrict_pc : forall H ms, ms_pc (restrict H ms) = ms_pc ms.
Proof. reflexivity. Qed.
Lemma restrict_regs : forall H ms, ms_regs (restrict H ms) = ms_regs ms.
Proof. reflexivity. Qed.
Lemma restrict_reg : forall H ms r, ms_reg (restrict H ms) r = ms_reg ms r.
Proof. reflexivity. Qed.
Lemma restrict_rom : forall H ms, ms_rom (restrict H ms) = ms_rom ms.
Proof. reflexivity. Qed.
Lemma restrict_mem : forall H ms, ms_mem (restrict H ms) = mrestrict H (ms_mem ms).
Proof. reflexivity. Qed.
Lemma unrestrict_svc_pending : forall H full ms,
  ms_svc_pending (unrestrict H full ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.
Lemma unrestrict_mem : forall H full ms,
  ms_mem (unrestrict H full ms) = munrestrict H full (ms_mem ms).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma restrict_mkst : forall H regs pc mem rom,
  restrict H (mkst regs pc mem rom) = mkst regs pc (mrestrict H mem) rom.
Proof. reflexivity. Qed.

Lemma mrestrict_idem : forall H m, mrestrict H (mrestrict H m) = mrestrict H m.
Proof.
  intros H m. apply functional_extensionality. intro a. unfold mrestrict.
  destruct (H a); reflexivity.
Qed.

Lemma munrestrict_mrestrict : forall H m,
  munrestrict H m (mrestrict H m) = m.
Proof.
  intros H m. apply functional_extensionality. intro a.
  unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Lemma mrestrict_munrestrict : forall H full m,
  mrestrict H (munrestrict H full m) = mrestrict H m.
Proof.
  intros H full m. apply functional_extensionality. intro a.
  unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Lemma unrestrict_restrict : forall H ms,
  unrestrict H (ms_mem ms) (restrict H ms) = ms.
Proof.
  intros H ms. destruct ms. unfold unrestrict, restrict. cbn.
  rewrite munrestrict_mrestrict. reflexivity.
Qed.

Lemma restrict_unrestrict : forall H full ms,
  restrict H (unrestrict H full ms) = restrict H ms.
Proof.
  intros H full ms. destruct ms. unfold unrestrict, restrict. cbn.
  rewrite mrestrict_munrestrict. reflexivity.
Qed.

(* [comment removed for export] *)
Definition hclean (H : word -> bool) (ms : machine_state) : Prop :=
  forall a, H a = true -> ms_mem ms a = None.

Lemma restrict_hclean : forall H ms, hclean H (restrict H ms).
Proof.
  intros H ms a Ha. cbn. unfold mrestrict. rewrite Ha. reflexivity.
Qed.

Lemma hclean_restrict_id : forall H ms, hclean H ms -> restrict H ms = ms.
Proof.
  intros H ms Hc. destruct ms. unfold restrict. cbn. f_equal.
  apply functional_extensionality. intro a. unfold mrestrict.
  destruct (H a) eqn:E; [symmetry; exact (Hc a E) | reflexivity].
Qed.

Lemma restrict_unrestrict_clean : forall H full ms,
  hclean H ms -> restrict H (unrestrict H full ms) = ms.
Proof.
  intros H full ms Hc. rewrite restrict_unrestrict. apply hclean_restrict_id. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ISA.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
#[using="HH"] Lemma memory_read1_hidden : forall a, H a = true -> memory_read segs a 1 = None.
Proof.
  intros a Ha. unfold memory_read. cbn [Z.of_N]. rewrite (HH a Ha). reflexivity.
Qed.

#[using="HH"] Lemma ov_read_bytes_restrict : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pn,$19.Pm,P,(1:.&40.)(1;.(1:.&8.))Pa,(1:.&40.)Pbs,(1<.(1:.&8.))P,(=.(1;.(1<.(1:.&8.)))(1=.Vsegs,(7.VH,R3.)R2.R4.)(1>.(1<.(1:.&8.))R1.))(1?.(=.(1;.(1<.(1:.&8.)))(1=.Vsegs,R4.R3.R5.)(1>.(1<.(1:.&8.))R2.))(20.VH,R3.R5.))")
(* [comment removed for export] *).
Proof.
  induction n as [|n IH]; intros m a bs Hr.
  - cbn in Hr |- *. split; [exact Hr | intros k Hk; lia].
  - cbn [ov_read_bytes] in Hr |- *.
    unfold mrestrict in Hr at 1.
    destruct (H a) eqn:Ha.
    + rewrite (memory_read1_hidden a Ha) in Hr. discriminate.
    + destruct (match m a with
                | Some b => Some b
                | None => match memory_read segs a 1 with
                          | Some (b :: _) => Some b | _ => None end
                end) as [b|]; [|discriminate].
      destruct (ov_read_bytes segs (mrestrict H m) (a + 1) n) as [rest|] eqn:Hrest;
        [|discriminate].
      destruct (IH m (a + 1) rest Hrest) as [Hfull Hav].
      rewrite Hfull. split; [exact Hr|].
      apply range_avoids_cons; assumption.
Qed.

#[using="HH"] Lemma wview_restrict : forall m a,
  wview segs (mrestrict H m) a =
    if H a then None else wview segs m a.
Proof.
  intros m a. unfold wview, mrestrict. destruct (H a) eqn:Ha; [|reflexivity].
  rewrite (HH a Ha). reflexivity.
Qed.

#[using="HH"] Lemma store_ok_restrict : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pn,$19.Pm,P,(1:.&40.)(1;.(1:.&8.))Pa,(1:.&40.)P,(=.$>.(21.Vsegs,(7.VH,R2.)R1.R3.)$12.)(1?.(=.$>.(21.Vsegs,R3.R2.R4.)$12.)(20.VH,R2.R4.))")
(* [comment removed for export] *).
Proof.
  induction n as [|n IH]; intros m a Hs.
  - split; [reflexivity | intros k Hk; lia].
  - cbn [store_ok] in Hs |- *. rewrite wview_restrict in Hs.
    destruct (H a) eqn:Ha; [discriminate|].
    destruct (wview segs m a) as [b|]; [|discriminate].
    destruct (IH m (a + 1) Hs) as [Hfull Hav].
    split; [exact Hfull | apply range_avoids_cons; assumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma write_to_mem_restrict : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pbs,(1<.(1:.&8.))Pm,P,(1:.&40.)(1;.(1:.&8.))Pa,(1:.&40.)P,(20.VH,R1.(22.(1:.&8.)R3.))(=.P,(1:.&40.)(1;.(1:.&8.))(23.(7.VH,R3.)R2.R4.)(7.VH,(23.R3.R2.R4.)))")
(* [comment removed for export] *).
Proof.
  induction bs as [|b bs IH]; intros m a Hav; [reflexivity|].
  cbn [write_to_mem length] in *.
  pose proof (range_avoids_hd H a _ Hav) as Ha.
  pose proof (range_avoids_tl H a _ Hav) as Htl.
  rewrite <- (IH _ (a + 1) Htl). f_equal.
  apply functional_extensionality. intro x. unfold mrestrict.
  destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
  unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
  rewrite Ha. reflexivity.
Qed.

#[using="Type"] Lemma write_to_mem_hidden : forall bs m a x,
  range_avoids H a (length bs) -> H x = true ->
  write_to_mem m a bs x = m x.
Proof.
  induction bs as [|b bs IH]; intros m a x Hav Hx; [reflexivity|].
  cbn [write_to_mem length] in *.
  pose proof (range_avoids_hd H a _ Hav) as Ha.
  pose proof (range_avoids_tl H a _ Hav) as Htl.
  rewrite (IH _ (a + 1) x Htl Hx). cbv beta.
  destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
  unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
  rewrite Ha in Hx. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mrestrict_visible : forall (H0 : word -> bool) m a,
  H0 a = false -> mrestrict H0 m a = m a.
Proof. intros H0 m a Ha. unfold mrestrict. rewrite Ha. reflexivity. Qed.

#[using="Type"] Lemma ov_read_bytes_mrestrict_eq : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PH0,P,(1:.&40.)$>.Pn,$19.Pm,P,(1:.&40.)(1;.(1:.&8.))Pa,(1:.&40.)P,(20.R4.R1.R3.)(=.(1;.(1<.(1:.&8.)))(1=.Vsegs,(7.R5.R3.)R2.R4.)(1=.Vsegs,R3.R2.R4.))")
(* [comment removed for export] *).
Proof.
  intros H0. induction n as [|n IH]; intros m a Hav; [reflexivity|].
  cbn [ov_read_bytes]. unfold mrestrict at 1. rewrite (range_avoids_hd H0 a n Hav).
  rewrite (IH m (a + 1) (range_avoids_tl H0 a n Hav)). reflexivity.
Qed.

#[using="Type"] Lemma rdn_mrestrict_eq : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PH0,P,(1:.&40.)$>.Pn,$19.Pm,P,(1:.&40.)(1;.(1:.&8.))Pa,(1:.&40.)P,(20.R4.R1.R3.)(=.(1;.(1<.(1:.&8.)))(24.Vsegs,(7.R5.R3.)R2.R4.)(24.Vsegs,R3.R2.R4.))")
(* [comment removed for export] *).
Proof.
  intros H0 n m a Hav. rewrite <- !ov_rdn. apply ov_read_bytes_mrestrict_eq. exact Hav.
Qed.

#[using="Type"] Lemma wview_mrestrict_eq : forall (H0 : word -> bool) m a,
  H0 a = false -> wview segs (mrestrict H0 m) a = wview segs m a.
Proof. intros H0 m a Ha. unfold wview, mrestrict. rewrite Ha. reflexivity. Qed.

#[using="Type"] Lemma store_ok_mrestrict_eq : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PH0,P,(1:.&40.)$>.Pn,$19.Pm,P,(1:.&40.)(1;.(1:.&8.))Pa,(1:.&40.)P,(20.R4.R1.R3.)(=.$>.(21.Vsegs,(7.R5.R3.)R2.R4.)(21.Vsegs,R3.R2.R4.))")
(* [comment removed for export] *).
Proof.
  intros H0. induction n as [|n IH]; intros m a Hav; [reflexivity|].
  cbn [store_ok]. rewrite (wview_mrestrict_eq H0 m a (range_avoids_hd H0 a n Hav)).
  destruct (wview segs m a); [|reflexivity].
  exact (IH m (a + 1) (range_avoids_tl H0 a n Hav)).
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma find_segment_some_spec : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pl,(1<.$;.)Paddr,$25.Pn,$25.Pseg,$;.P,(=.(1;.$;.)(26.R4.R3.R2.)(1>.$;.R1.))(1?.(<.$;.R2.R5.)(1?.(13.(15.(16.R2.))R4.)(13.(14.R4.R3.)(14.(15.(16.R2.))(15.(17.R2.))))))")
(* [comment removed for export] *).
Proof.
  induction l as [|s l IH]; intros addr n seg Hf; [discriminate|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E.
  - injection Hf as ->. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity | split; assumption].
  - destruct (IH addr n seg Hf) as (Hin & H1 & H2).
    split; [right; exact Hin | split; assumption].
Qed.

#[using="Type"] Lemma find_segment_none_spec : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pl,(1<.$;.)Paddr,$25.Pn,$25.P,(=.(1;.$;.)(26.R3.R2.R1.)(27.$;.))Pseg,$;.P,(<.$;.R1.R5.)(28.(1?.(13.(15.(16.R2.))R5.)(13.(14.R5.R4.)(14.(15.(16.R2.))(15.(17.R2.))))))")
(* [comment removed for export] *).
Proof.
  induction l as [|s l IH]; intros addr n Hf seg Hin; [destruct Hin|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E;
    [discriminate|].
  destruct Hin as [<- | Hin].
  - intros [H1 H2]. apply andb_false_iff in E as [E | E].
    + apply Z.leb_gt in E. lia.
    + apply Z.leb_gt in E. lia.
  - exact (IH addr n Hf seg Hin).
Qed.

(* [comment removed for export] *)
#[using="HH"] Lemma in_segment_not_hidden : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Px,(1:.&40.)Pseg,$;.P,(<.$;.R1.Vsegs,)P,(13.(15.(16.R2.))(29.&40.R3.))P,(13.(14.(29.&40.R4.)+1.)(14.(15.(16.R3.))(15.(17.R3.))))(=.$>.A1.VH,R5.$2:.)")
(* [comment removed for export] *).
Proof.
  intros x seg Hin H1 H2. destruct (H x) eqn:Hx; [|reflexivity].
  exfalso. exact (find_segment_none_spec segs (bv_unsigned x) 1 (HH x Hx) seg Hin (conj H1 H2)).
Qed.

#[using="HH"] Lemma seg_ov_read_bytes_restrict : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pn,$19.Pm,P,(1:.&40.)(1;.(1:.&8.))Pseg,$;.Pa,(1:.&40.)P,(<.$;.R2.Vsegs,)P,(13.(15.(16.R3.))(29.&40.R2.))P,(13.(14.(29.&40.R3.)(2;.R6.))(14.(15.(16.R4.))(15.(17.R4.))))P,(13.(14.(15.(16.R5.))(15.(17.R5.)))(18.+2.+40.))(=.(1;.(1<.(1:.&8.)))(2<.(7.VH,R7.)R6.R5.R8.)(2<.R7.R6.R5.R8.))")
(* [comment removed for export] *).
Proof.
  induction n as [|n IH]; intros m seg a Hin Hlo Hhi Htop; [reflexivity|].
  cbn [seg_ov_read_bytes].
  assert (Ha : H a = false) by (apply (in_segment_not_hidden a seg Hin); lia).
  unfold mrestrict at 1. rewrite Ha.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z).
    { rewrite bv_add_unsigned.
      assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
      apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z.
      pose proof (bv_unsigned_in_range 64 a). lia. }
    rewrite (IH m seg (a + 1) Hin) by lia. reflexivity.
Qed.

#[using="HH Hwx"] Lemma code_read_ov_restrict : forall m a n,
  code_read_ov segs (mrestrict H m) a n = code_read_ov segs m a n.
Proof.
  intros m a n. unfold code_read_ov.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf; [|reflexivity].
  destruct (seg_executable seg && seg_writable seg) eqn:Ewx; [|reflexivity].
  destruct (find_segment_some_spec segs _ _ seg Hf) as (Hin & H1 & H2).
  apply seg_ov_read_bytes_restrict; [exact Hin | exact H1 | | exact (Hwx seg Hin Ewx)].
  rewrite N_nat_Z. exact H2.
Qed.

#[using="HH Hwx"] Lemma fetch_word_ov_restrict : forall m a,
  fetch_word_ov segs (mrestrict H m) a = fetch_word_ov segs m a.
Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

#[using="HH Hwx"] Lemma fetch_half_ov_restrict : forall m a,
  fetch_half_ov segs (mrestrict H m) a = fetch_half_ov segs m a.
Proof. intros m a. unfold fetch_half_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

#[using="HH Hwx"] Lemma fetch_half_any_restrict : forall m a,
  fetch_half_any segs (mrestrict H m) a = fetch_half_any segs m a.
Proof. intros m a. unfold fetch_half_any. rewrite fetch_half_ov_restrict. reflexivity. Qed.

#[using="HH Hwx"] Lemma fetch_tail_any_restrict : forall m a,
  fetch_tail_any segs (mrestrict H m) a = fetch_tail_any segs m a.
Proof. intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_restrict. reflexivity. Qed.

#[using="HH Hwx"] Lemma fetch_failure_restrict : forall m a,
  fetch_failure segs (mrestrict H m) a = fetch_failure segs m a.
Proof. intros m a. unfold fetch_failure. rewrite fetch_half_any_restrict. reflexivity. Qed.

(* [comment removed for export] *)
#[using="HH"] Lemma interp_eff_accesses_restrict : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pt,$2=.Pm,P,(1:.&40.)(1;.(1:.&8.))Pc,$2>.Pmr',P,(1:.&40.)(1;.(1:.&8.))Prs,(1<.$2?.)P,(=.(30.(31.(32.$2>.P,(1:.&40.)(1;.(1:.&8.)))))(33.Vsegs,R5.(7.VH,R4.))(34.(31.(32.$2>.P,(1:.&40.)(1;.(1:.&8.))))(35.(32.$2>.P,(1:.&40.)(1;.(1:.&8.)))(36.$2>.P,(1:.&40.)(1;.(1:.&8.))R3.R2.)R1.)))(37.P,(1:.&40.)(1;.(1:.&8.))Lmf',P,(1:.&40.)(1;.(1:.&8.))(1?.(=.(30.(31.(32.$2>.P,(1:.&40.)(1;.(1:.&8.)))))(33.Vsegs,R7.R6.)(34.(31.(32.$2>.P,(1:.&40.)(1;.(1:.&8.))))(35.(32.$2>.P,(1:.&40.)(1;.(1:.&8.)))(36.$2>.P,(1:.&40.)(1;.(1:.&8.))R5.R1.)R3.)))(1?.(=.P,(1:.&40.)(1;.(1:.&8.))R4.(7.VH,R1.))(1?.Px,(1:.&40.)P,(=.$>.A1.VH,R1.$12.)(=.(1;.(1:.&8.))A1.R3.R2.A1.R8.R2.)(38.VH,R3.)))))")
(* [comment removed for export] *).
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH]; (* [comment removed for export] *)
    intros m c mr' rs Hi; cbn [interp_eff_accesses] in Hi |- *;
    try discriminate.
  - (* [comment removed for export] *)
    injection Hi as <- <- <-. exists m.
    split; [reflexivity|]. split; [reflexivity|]. split; [intros; reflexivity|].
    apply ranges_avoid_nil.
  - (* [comment removed for export] *)
    destruct (ov_read_bytes segs (mrestrict H m) a (width_bytes n)) as [bs|] eqn:Hrd;
      [|discriminate].
    destruct (ov_read_bytes_restrict _ m a bs Hrd) as [Hfull Hav].
    rewrite Hfull.
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) (mrestrict H m))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ m c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split; [exact Hhid|].
    apply ranges_avoid_cons; assumption.
  - (* [comment removed for export] *)
    destruct (store_ok segs (mrestrict H m) a (width_bytes n)) eqn:Hso; [|discriminate].
    destruct (store_ok_restrict _ m a Hso) as [Hfull Hav]. rewrite Hfull.
    assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
      by apply length_Z_to_le_bytes.
    rewrite (write_to_mem_restrict (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a)
      in Hi by (rewrite Hlen; exact Hav).
    destruct (interp_eff_accesses segs k
                (mrestrict H (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split.
    + intros x Hx. rewrite (Hhid x Hx).
      apply (write_to_mem_hidden _ m a x); [rewrite Hlen; exact Hav | exact Hx].
    + apply ranges_avoid_cons; assumption.
Qed.

(* [comment removed for export] *)
#[using="HH"] Lemma decode_exec_accesses_restrict : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pms,$39.Pw,(1:.&20.)Pmsr',$39.Prs',(1<.$2?.)P,(=.(30.(31.$39.))(3:.Vsegs,(3;.VH,R4.)R3.)(34.(31.$39.)(35.$39.R2.R1.)))(1?.(=.(30.(31.$39.))(3:.Vsegs,R5.R4.)(34.(31.$39.)(35.$39.(3<.VH,(8.R5.)R3.)R2.)))(1?.(38.VH,R2.)(3=.VH,R3.)))")
(* [comment removed for export] *).
Proof.
  intros ms w msr' rs' Hd. unfold decode_exec_accesses in Hd |- *.
  destruct (is_ecall w) eqn:Hec.
  - injection Hd as <- <-.
    split; [|split; [apply ranges_avoid_nil | apply (restrict_hclean H ms)]].
    unfold unrestrict, restrict. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending].
    rewrite munrestrict_mrestrict. destruct ms; reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom restrict] in Hd.
    destruct (interp_eff_accesses segs
                (exec (Z_to_bv 64 isz) i
                   {| c_regs := ms_regs ms; c_fregs := ms_fregs ms;
                      c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms;
                      c_resv := ms_resv ms |})
                (mrestrict H (ms_mem ms)))
      as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate.
    cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-.
    destruct (interp_eff_accesses_restrict _ _ c1 m1 rs1 Hint)
      as (mf' & Hfull & -> & Hhid & Hrs).
    rewrite Hfull. cbn [access_value accessed_ranges].
    split; [|split; [exact Hrs|]].
    + unfold unrestrict. cbn.
      replace (munrestrict H (ms_mem ms) (mrestrict H mf')) with mf'; [reflexivity|].
      apply functional_extensionality. intro x. unfold munrestrict, mrestrict.
      destruct (H x) eqn:Hx; [exact (Hhid x Hx) | reflexivity].
    + intros x Hx. cbn. unfold mrestrict. rewrite Hx. reflexivity.
Qed.

#[using="HH Hwx"] Theorem step_accesses_restrict : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pms,$39.Pmsr',$39.Prs',(1<.$2?.)P,(=.(30.(31.$39.))(3>.Vsegs,(3;.VH,R3.))(34.(31.$39.)(35.$39.R2.R1.)))(1?.(=.(30.(31.$39.))(3>.Vsegs,R4.)(34.(31.$39.)(35.$39.(3<.VH,(8.R4.)R3.)R2.)))(1?.(38.VH,R2.)(3=.VH,R3.)))")
(* [comment removed for export] *).
Proof.
  intros ms msr' rs' Hs. unfold step_accesses in Hs |- *.
  rewrite restrict_pc in Hs. cbn [ms_mem restrict] in Hs.
  rewrite fetch_word_ov_restrict, fetch_tail_any_restrict, fetch_failure_restrict in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  exfalso. unfold fetch_failure in Hs.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

(* [comment removed for export] *)
#[using="HH Hwx"] Theorem step_restrict_sound : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pms,$39.Pmsr',$39.P,(=.(30.$39.)(3?.Vsegs,(3;.VH,R2.))(34.$39.R1.))(37.(31.$39.)Lrep,(31.$39.)(1?.(=.(30.(31.$39.))(3>.Vsegs,R4.)(34.(31.$39.)R1.))(1?.(=.$39.(40.$39.R1.)(3<.VH,(8.R4.)R3.))(1?.(38.VH,(41.$39.R1.))(1?.(3=.VH,R3.)(=.$39.(3;.VH,(3<.VH,(8.R4.)R3.))R3.))))))")
(* [comment removed for export] *).
Proof.
  intros ms msr' Hs. unfold RiscvSemantics.step, drop_access_report in Hs.
  destruct (step_accesses segs (restrict H ms)) as [[v rs]| |] eqn:Hsa; try discriminate.
  injection Hs as ->.
  destruct (step_accesses_restrict ms msr' rs Hsa) as (Hfull & Hrs & Hcl).
  exists (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs).
  split; [exact Hfull|]. split; [reflexivity|]. split; [exact Hrs|]. split; [exact Hcl|].
  apply restrict_unrestrict_clean. exact Hcl.
Qed.

(* [comment removed for export] *)
#[using="HH Hwx"] Corollary step_restrict_step : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pms,$39.Pmsr',$39.P,(=.(30.$39.)(3?.Vsegs,(3;.VH,R2.))(34.$39.R1.))(=.(30.$39.)(3?.Vsegs,R3.)(34.$39.(3<.VH,(8.R3.)R2.)))")
(* [comment removed for export] *).
Proof.
  intros ms msr' Hs.
  destruct (step_restrict_sound ms msr' Hs) as (rep & Hsa & Hv & _).
  unfold RiscvSemantics.step, drop_access_report. rewrite Hsa, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_accesses_ecall_shape : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pms,$39.Pmsr',$39.Prs',(1<.$2?.)P,(=.(30.(31.$39.))(3>.Vsegs,R3.)(34.(31.$39.)(35.$39.R2.R1.)))P,(28.(=.(1;.(1:.&40.))(4.R3.)(27.(1:.&40.))))(1?.(=.(1<.$2?.)R3.(42.$2?.))(1?.(=.P,(1:.&40.)(1;.(1:.&8.))(8.R4.)(8.R5.))(1?.(=.(43.&5.(1:.&40.))(1.R4.)(1.R5.))(=.(1;.(1:.&40.))(4.R4.)(1>.(1:.&40.)(44.R5.(45.&5.+11.$46.)))))))")
(* [comment removed for export] *).
Proof.
  intros ms msr' rs' Hs Hsvc.
  assert (Hdec : forall w, decode_exec_accesses segs ms w = MachineOk (@mkAccessReport _ msr' rs') ->
            rs' = [] /\ ms_mem msr' = ms_mem ms /\ ms_regs msr' = ms_regs ms
            /\ ms_svc_pending msr' = Some (ms_reg ms 17)).
  { intros w Hd. unfold decode_exec_accesses in Hd.
    destruct (is_ecall w).
    - injection Hd as <- <-. cbn. repeat split; reflexivity.
    - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
      destruct (interp_eff_accesses segs _ _) as [[[c1 m1] rs1]| |]; try discriminate.
      cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-. cbn in Hsvc.
      exfalso. apply Hsvc. reflexivity. }
  unfold step_accesses in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  exfalso. destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) eqn:Hf; try discriminate.
  unfold fetch_failure in Hf.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

End ISA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition page_allowedb (A : list (Z * Z)) (p : word) : bool := ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "(47.(32.$25.$25.)Liv,(32.$25.$25.)(?.(48.(49.$25.$25.R1.)(29.&40.O1.))(48.(14.(29.&40.O1.)$4:.)(4;.$25.$25.R1.)))O2.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition A_wf (A : list (Z * Z)) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "(4<.(32.$25.$25.)Liv,(32.$25.$25.)(1?.(13.(49.$25.$25.R1.)(4;.$25.$25.R1.))(1?.(=.$25.(4=.(49.$25.$25.R1.)$4:.)=)(=.$25.(4=.(4;.$25.$25.R1.)$4:.)=)))O1.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Fixpoint A_bytes (A : list (Z * Z)) : Z :=
  match A with
  | [] => 0
  | iv :: r => (snd iv - fst iv) + A_bytes r
  end%Z.

(* [comment removed for export] *)
Definition lazy_cover (H : word -> bool) (lazy : list (word * word))
    (A : list (Z * Z)) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pw,(1:.&40.)P,(=.$>.(4>.(4?.R1.)O2.)$12.)P,(=.$>.A1.O3.R2.$2:.)(=.$>.(50.O1.(4?.R3.))$12.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition eager_used (m : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)).

Lemma vm_backing_used_split : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pm,$51.(=.$25.(52.R1.)(14.(53.R1.)(54.(2;.(22.(1:.&40.)(55.R1.)))$4:.)))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Record MInv (A : list (Z * Z)) (m : Model) : Prop := mkMInv {
  minv_nodup    : List.NoDup (m_vm_materialized m);
  minv_aligned  : forall p, In p (m_vm_materialized m) ->
                    (bv_unsigned p mod page_size = 0)%Z;
  minv_allowed  : forall p, In p (m_vm_materialized m) -> page_allowedb A p = true;
  minv_lazy     : forall p, In p (m_vm_materialized m) ->
                    page_in_ranges p (m_vm_lazy m) = true;
  minv_budget   : (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z
}.

(* [comment removed for export] *)
Definition same_but_materialized (m m' : Model) : Prop :=
  m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m.

Lemma same_but_materialized_refl : forall m, same_but_materialized m m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma same_but_materialized_trans : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pm1,$51.Pm2,$51.Pm3,$51.P,(56.R3.R2.)P,(56.R3.R2.)(56.R5.R3.)")
(* [comment removed for export] *).
Proof.
  unfold same_but_materialized. intros m1 m2 m3 -> ->.
  destruct m1 as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
Qed.

Lemma with_vm_backing_same : forall m mat',
  same_but_materialized m (with_vm_backing (m_vm_lazy m) mat' m).
Proof.
  intros [fd [maps lazy mat] io fs proc lim tm] mat'. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma same_but_materialized_frame : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pm,$51.Pm',$51.P,(56.R2.R1.)(1?.(=.$57.(58.R2.)(58.R3.))(1?.(=.$59.(5:.R2.)(5:.R3.))(1?.(=.(1<.(32.(1:.&40.)(1:.&40.)))(5;.R2.)(5;.R3.))(1?.(=.$5<.(5=.R2.)(5=.R3.))(1?.(=.$5>.(5?.R2.)(5?.R3.))(1?.(=.$60.(61.R2.)(61.R3.))(1?.(=.$62.(63.R2.)(63.R3.))(1?.(=.$64.(65.R2.)(65.R3.))(1?.(=.(1<.(32.(1:.&40.)$66.))(67.R2.)(67.R3.))(1?.(=.(1<.(32.(1:.&40.)$68.))(69.R2.)(69.R3.))(1?.(=.$6:.(6;.R2.)(6;.R3.))(1?.(=.$6<.(6=.R2.)(6=.R3.))(1?.(=.(1;.(1:.&40.))(6>.R2.)(6>.R3.))(1?.(=.(1;.(1:.&40.))(6?.R2.)(6?.R3.))(1?.(=.(1;.(1<.(1:.&8.)))(70.R2.)(70.R3.))(1?.(=.(1:.&40.)(71.R2.)(71.R3.))(=.$25.(53.R2.)(53.R3.))))))))))))))))))")
(* [comment removed for export] *).
Proof.
  intros m m' ->. destruct m as [fd [maps lazy mat] io fs proc lim tm].
  repeat split; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint A_pages (A : list (Z * Z)) : list Z :=
  match A with
  | [] => []
  | iv :: r =>
      map (fun i => (fst iv + page_size * Z.of_nat i)%Z)
          (seq 0 (Z.to_nat ((snd iv - fst iv) / page_size)))
      ++ A_pages r
  end.

Lemma Zmod0_multiple : forall a, (a mod page_size = 0)%Z -> exists q, a = (page_size * q)%Z.
Proof.
  intros a Ha. exists (a / page_size)%Z.
  pose proof (Z.div_mod a page_size ltac:(unfold page_size; lia)) as Hdm.
  rewrite Ha, Z.add_0_r in Hdm. exact Hdm.
Qed.

Lemma A_pages_length : forall A,
  A_wf A -> (Z.of_nat (length (A_pages A)) * page_size = A_bytes A)%Z.
Proof.
  induction A as [|[lo hi] A IH]; intros Hwf; [reflexivity|].
  cbn [A_pages A_bytes fst snd]. inversion Hwf as [|x l [Hle [Hlo Hhi]] Hwf']; subst.
  cbn [fst snd] in *.
  rewrite length_app, length_map, length_seq, Nat2Z.inj_add, Z.mul_add_distr_r.
  rewrite (IH Hwf').
  destruct (Zmod0_multiple lo Hlo) as [qlo ->].
  destruct (Zmod0_multiple hi Hhi) as [qhi ->].
  replace (page_size * qhi - page_size * qlo)%Z with ((qhi - qlo) * page_size)%Z by lia.
  rewrite Z.div_mul by (unfold page_size; lia).
  rewrite Z2Nat.id by (unfold page_size in Hle; lia).
  reflexivity.
Qed.

Lemma A_pages_in : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PA,(1<.(32.$25.$25.))Pp,(1:.&40.)P,(72.R2.)P,(=.$25.(4=.(29.&40.R2.)$4:.)=)P,(=.$>.(50.R4.R3.)$12.)(<.$25.(29.&40.R4.)(73.R5.))")
(* [comment removed for export] *).
Proof.
  induction A as [|[lo hi] A IH]; intros p Hwf Hal Hpa; [discriminate|].
  inversion Hwf as [|x l [Hle [Hlo Hhi]] Hwf']; subst. cbn [fst snd] in *.
  cbn [A_pages fst snd]. apply in_or_app.
  unfold page_allowedb in Hpa. cbn [existsb fst snd] in Hpa.
  apply orb_true_iff in Hpa as [Hpa | Hpa].
  - left. apply andb_true_iff in Hpa as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    destruct (Zmod0_multiple lo Hlo) as [qlo Eqlo].
    destruct (Zmod0_multiple hi Hhi) as [qhi Eqhi].
    destruct (Zmod0_multiple (bv_unsigned p) Hal) as [qp Eqp].
    rewrite Eqp in *. rewrite Eqlo, Eqhi in *.
    replace (page_size * qhi - page_size * qlo)%Z with ((qhi - qlo) * page_size)%Z by lia.
    rewrite Z.div_mul by (unfold page_size; lia).
    apply in_map_iff. exists (Z.to_nat (qp - qlo)).
    unfold page_size in *.
    split.
    + rewrite Z2Nat.id by lia. lia.
    + apply in_seq. lia.
  - right. apply IH; [exact Hwf' | exact Hal | exact Hpa].
Qed.

Lemma NoDup_map_bv_unsigned : forall (l : list word),
  List.NoDup l -> List.NoDup (map bv_unsigned l).
Proof.
  intros l Hnd. induction Hnd as [|x l Hx Hnd IH]; cbn; constructor; [|exact IH].
  intros Hin. apply in_map_iff in Hin as (y & Hy & Hiny).
  apply bv_eq in Hy. subst y. exact (Hx Hiny).
Qed.

Theorem allowed_pages_bound : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PA,(1<.(32.$25.$25.))Ppages,(1<.(1:.&40.))P,(72.R2.)P,(74.(1:.&40.)R2.)P,Pp,(1:.&40.)P,(<.(1:.&40.)R1.R4.)(=.$25.(4=.(29.&40.R2.)$4:.)=)P,Pp,(1:.&40.)P,(<.(1:.&40.)R1.R5.)(=.$>.(50.R7.R2.)$12.)(13.(54.(2;.(22.(1:.&40.)R5.))$4:.)(75.R6.))")
(* [comment removed for export] *).
Proof.
  intros A pages Hwf Hnd Hal Hpa.
  rewrite <- (A_pages_length A Hwf).
  assert (Hlen : (length pages <= length (A_pages A))%nat).
  { rewrite <- (length_map bv_unsigned pages).
    apply NoDup_incl_length.
    - apply NoDup_map_bv_unsigned. exact Hnd.
    - intros z Hz. apply in_map_iff in Hz as (p & <- & Hp).
      apply A_pages_in; [exact Hwf | exact (Hal p Hp) | exact (Hpa p Hp)]. }
  unfold page_size. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma two64_as_pages : (2 ^ 64 = page_size * 2 ^ 52)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma page_base_woff : forall a k,
  page_base (woff a k) = page_base_of (bv_unsigned a + Z.of_nat k).
Proof.
  intros a k. unfold page_base, woff, page_base_of.
  set (z := (bv_unsigned a + Z.of_nat k)%Z).
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  assert (Hz : (0 <= z)%Z) by (unfold z; lia).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite !two64_as_pages.
  set (r := (z mod (page_size * 2 ^ 52))%Z).
  assert (Hps : (0 < page_size)%Z) by (unfold page_size; lia).
  (* [comment removed for export] *)
  pose proof (Z.div_mod z (page_size * 2 ^ 52) ltac:(lia)) as Hdm.
  fold r in Hdm.
  set (q := (z / (page_size * 2 ^ 52))%Z) in Hdm.
  assert (Hfl : (z / page_size * page_size = page_size * 2 ^ 52 * q + r / page_size * page_size)%Z).
  { rewrite Hdm at 1.
    replace (page_size * 2 ^ 52 * q + r)%Z with (r + (2 ^ 52 * q) * page_size)%Z by lia.
    rewrite Z.div_add by lia. lia. }
  rewrite Hfl.
  replace (page_size * 2 ^ 52 * q + r / page_size * page_size)%Z
    with (r / page_size * page_size + q * (page_size * 2 ^ 52))%Z by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma page_base_of_aligned : forall z,
  (bv_unsigned (page_base_of z) mod page_size = 0)%Z.
Proof.
  intros z. unfold page_base_of. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z. rewrite two64_as_pages.
  rewrite (Z.mul_comm (z / page_size) page_size).
  rewrite Zmult_mod_distr_l.
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma page_insert_nodup : forall p pages,
  List.NoDup pages -> List.NoDup (page_insert p pages).
Proof.
  intros p pages Hnd. unfold page_insert.
  destruct (page_mem p pages) eqn:Hm; [exact Hnd|].
  constructor; [|exact Hnd].
  intros Hin. unfold page_mem in Hm.
  assert (Ht : existsb (bv_eqb p) pages = true).
  { apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
  rewrite Ht in Hm. discriminate.
Qed.

Lemma page_mem_false_not_in : forall p pages,
  page_mem p pages = false -> ~ In p pages.
Proof.
  intros p pages Hm Hin. unfold page_mem in Hm.
  assert (Ht : existsb (bv_eqb p) pages = true).
  { apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
  rewrite Ht in Hm. discriminate.
Qed.

Lemma access_pages_acc_nodup : forall n base pages,
  List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof.
  induction n as [|n IH]; intros base pages Hnd; cbn [access_pages_acc]; [exact Hnd|].
  apply IH. apply page_insert_nodup. exact Hnd.
Qed.

Lemma accesses_pages_nodup : forall accs pages,
  List.NoDup pages -> List.NoDup (accesses_pages accs pages).
Proof.
  induction accs as [|[a n] accs IH]; intros pages Hnd; cbn [accesses_pages]; [exact Hnd|].
  apply IH. apply access_pages_acc_nodup. exact Hnd.
Qed.

Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages Hin. unfold page_insert in Hin.
  destruct (page_mem q pages); [right; exact Hin|].
  destruct Hin as [Hqp | Hin]; [left; symmetry; exact Hqp | right; exact Hin].
Qed.

Lemma access_pages_acc_in : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pn,$19.Pbase,$25.Ppages,(1<.(1:.&40.))Pp,(1:.&40.)P,(<.(1:.&40.)R1.(76.R3.R4.R2.))(77.(<.(1:.&40.)R2.R3.)(37.$19.Lk,$19.(1?.(78.R1.R6.)(=.(1:.&40.)R3.(79.(14.R5.(2;.R1.)))))))")
(* [comment removed for export] *).
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p Hin.
  - left; exact Hin.
  - destruct (IH (base + 1)%Z _ p Hin) as [Hin' | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin') as [-> | Hin''].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin''.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Paccs,(1<.(32.(1:.&40.)$19.))Ppages,(1<.(1:.&40.))Pp,(1:.&40.)P,(<.(1:.&40.)R1.(7:.R3.R2.))(77.(<.(1:.&40.)R2.R3.)(37.(1:.&40.)La,(1:.&40.)(37.$19.Ln,$19.(37.$19.Lk,$19.(1?.(<.(32.(1:.&40.)$19.)(36.(1:.&40.)$19.R3.R2.)R7.)(1?.(78.R1.R2.)(=.(1:.&40.)R5.(79.(14.(29.&40.R3.)(2;.R1.))))))))))")
(* [comment removed for export] *).
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages p Hin.
  - left; exact Hin.
  - destruct (IH _ p Hin) as [Hin' | (a' & n' & k & Hin' & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin') as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k. split; [left; reflexivity | split; assumption].
    + right. exists a', n', k. split; [right; exact Hin' | split; assumption].
Qed.

(* [comment removed for export] *)
Lemma new_pages_props : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PH,P,(1:.&40.)$>.PA,(1<.(32.$25.$25.))Plazy,(1<.(32.(1:.&40.)(1:.&40.)))Pmat,(1<.(1:.&40.))Pranges,(1<.(32.(1:.&40.)$19.))P,(7;.R5.R3.R4.)P,(38.R6.R2.)Znew,(1<.(1:.&40.))(7<.R5.R4.R3.)(1?.(74.(1:.&40.)R1.)(1?.Pp,(1:.&40.)P,(<.(1:.&40.)R1.R2.)(28.(<.(1:.&40.)R2.R7.))(1?.Pp,(1:.&40.)P,(<.(1:.&40.)R1.R2.)(=.$25.(4=.(29.&40.R2.)$4:.)=)(1?.Pp,(1:.&40.)P,(<.(1:.&40.)R1.R2.)(=.$>.(4>.R2.R8.)$12.)Pp,(1:.&40.)P,(<.(1:.&40.)R1.R2.)(=.$>.(50.R9.R2.)$12.)))))")
(* [comment removed for export] *).
Proof.
  intros H A lazy mat ranges Hcov Hav new.
  assert (Hchar : forall p, In p new ->
            page_in_ranges p lazy = true /\ page_mem p mat = false
            /\ exists a n k, In (a, n) ranges /\ (k < n)%nat
                             /\ p = page_base_of (bv_unsigned a + Z.of_nat k)%Z).
  { intros p Hin. unfold new, newly_materialized_pages in Hin.
    apply filter_In in Hin as [Hin Hf]. apply andb_true_iff in Hf as [Hl Hm].
    split; [exact Hl|]. split; [destruct (page_mem p mat); [discriminate | reflexivity]|].
    destruct (accesses_pages_in ranges [] p Hin) as [[] | Hex]. exact Hex. }
  split; [|split; [|split; [|split]]].
  - unfold new, newly_materialized_pages. apply NoDup_filter.
    apply accesses_pages_nodup. constructor.
  - intros p Hp. destruct (Hchar p Hp) as (_ & Hm & _). apply page_mem_false_not_in. exact Hm.
  - intros p Hp. destruct (Hchar p Hp) as (_ & _ & a & n & k & _ & _ & ->).
    apply page_base_of_aligned.
  - intros p Hp. destruct (Hchar p Hp) as (Hl & _). exact Hl.
  - intros p Hp. destruct (Hchar p Hp) as (Hl & _ & a & n & k & Hin & Hk & Ep).
    pose proof (Hav a n Hin k Hk) as Hw.
    rewrite <- page_base_woff in Ep. rewrite Ep in Hl |- *.
    exact (Hcov (woff a k) Hl Hw).
Qed.

(* [comment removed for export] *)
Lemma m_vm_materialized_wvb : forall l X m,
  m_vm_materialized (with_vm_backing l X m) = X.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_wvb : forall l X m, m_vm_lazy (with_vm_backing l X m) = l.
Proof. reflexivity. Qed.
Lemma m_vmmaps_wvb : forall l X m, m_vmmaps (with_vm_backing l X m) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma m_halted_wvb : forall l X m, m_halted (with_vm_backing l X m) = m_halted m.
Proof. reflexivity. Qed.
Lemma eager_used_wvb : forall X m,
  eager_used (with_vm_backing (m_vm_lazy m) X m) = eager_used m.
Proof. reflexivity. Qed.

Lemma with_vm_backing_id : forall m,
  with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma MInv_wvb : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PA,(1<.(32.$25.$25.))Pm,$51.PX,(1<.(1:.&40.))P,(74.(1:.&40.)R1.)P,Pp,(1:.&40.)P,(<.(1:.&40.)R1.R3.)(=.$25.(4=.(29.&40.R2.)$4:.)=)P,Pp,(1:.&40.)P,(<.(1:.&40.)R1.R4.)(=.$>.(50.R7.R2.)$12.)P,Pp,(1:.&40.)P,(<.(1:.&40.)R1.R5.)(=.$>.(4>.R2.(5;.R7.))$12.)P,(13.(14.(53.R6.)(75.R7.))(7=.(5:.R6.)))(7>.R8.(7?.(5;.R7.)R6.R7.))")
(* [comment removed for export] *).
Proof.
  intros A m X H1 H2 H3 H4 H5. constructor;
    rewrite ?m_vm_materialized_wvb, ?m_vm_lazy_wvb, ?m_vmmaps_wvb, ?eager_used_wvb;
    assumption.
Qed.

(* [comment removed for export] *)
Theorem materialize_restricted : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PH,P,(1:.&40.)$>.PA,(1<.(32.$25.$25.))Pm,$51.Pranges,(1<.(32.(1:.&40.)$19.))P,(7;.R4.(5;.R2.)R3.)P,(72.R4.)P,(7>.R5.R4.)P,(38.R7.R4.)(37.(1<.(1:.&40.))Lmat',(1<.(1:.&40.))(1?.(=.(1;.$51.)(80.R7.R6.)(1>.$51.(7?.(5;.R7.)R1.R7.)))(7>.R8.(7?.(5;.R7.)R1.R7.))))")
(* [comment removed for export] *).
Proof.
  intros H A m ranges Hcov Hwf [Hnd Hal Hpa Hlz Hbud] Hav.
  destruct (new_pages_props H A (m_vm_lazy m) (m_vm_materialized m) ranges Hcov Hav)
    as (Nnd & Nfresh & Nal & Nlz & Npa).
  unfold materialize_model_accesses, materialize_accesses.
  set (new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges) in *.
  assert (Happ_nd : List.NoDup (new ++ m_vm_materialized m)).
  { apply NoDup_app; [exact Nnd | exact Hnd | exact Nfresh]. }
  assert (Happ_al : forall p, In p (new ++ m_vm_materialized m) ->
                      (bv_unsigned p mod page_size = 0)%Z).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nal p Hp) | exact (Hal p Hp)]. }
  assert (Happ_pa : forall p, In p (new ++ m_vm_materialized m) -> page_allowedb A p = true).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Npa p Hp) | exact (Hpa p Hp)]. }
  assert (Happ_lz : forall p, In p (new ++ m_vm_materialized m) ->
                      page_in_ranges p (m_vm_lazy m) = true).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nlz p Hp) | exact (Hlz p Hp)]. }
  pose proof (allowed_pages_bound A (new ++ m_vm_materialized m) Hwf Happ_nd Happ_al Happ_pa)
    as Hbound.
  rewrite length_app, Nat2Z.inj_add in Hbound.
  destruct new as [|p0 new'] eqn:Enew.
  - exists (m_vm_materialized m). split; [reflexivity|].
    apply MInv_wvb; assumption.
  - rewrite vm_backing_used_split.
    replace (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size
             + Z.of_nat (length (p0 :: new')) * page_size
             <=? vm_limit (m_vmmaps m))%Z with true.
    2:{ symmetry. apply Z.leb_le. unfold page_size in *. lia. }
    exists ((p0 :: new') ++ m_vm_materialized m). split; [reflexivity|].
    apply MInv_wvb; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "(1?.Pi,O3.(81.Vsegs,O4.A1.O2.R1.(82.A1.O1.R1.))Pe,(1<.$83.)Pst,$84.P,(81.Vsegs,O4.R2.R1.)(37.O3.Li,O3.(1?.(=.(1<.$83.)R4.A1.O2.R1.)(=.$84.R3.(82.A1.O1.R1.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="HH Hwx"] Theorem mi_account_step_restricted : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PA,(1<.(32.$25.$25.))Pms,$39.Pmsr',$39.Pmodel,$51.P,(7;.VH,(5;.R1.)R4.)P,(72.R5.)P,(7>.R6.R3.)P,(=.(30.$39.)(3?.Vsegs,(3;.VH,R6.))(34.$39.R5.))(37.(1<.(1:.&40.))Lmat',(1<.(1:.&40.))(1?.(=.(30.(32.$39.$51.))(85.Vsegs,R8.R6.)(34.(32.$39.$51.)(36.$39.$51.(3<.VH,(8.R8.)R7.)(7?.(5;.R6.)R1.R6.))))(1?.(7>.R9.(7?.(5;.R6.)R1.R6.))(3=.VH,R7.))))")
(* [comment removed for export] *).
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hs.
  destruct (step_restrict_sound segs H HH Hwx ms msr' Hs) as (rep & Hsa & Hv & Hrs & Hcl & _).
  destruct (materialize_restricted H A model (accessed_ranges _ rep) Hcov Hwf Hinv Hrs)
    as (mat' & Hmat & Hinv').
  exists mat'. unfold mi_account_step. rewrite Hsa, Hmat, Hv.
  split; [reflexivity | split; [exact Hinv' | exact Hcl]].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_instr_det : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Pms,$39.Pmodel,$51.Pms1,$39.Pmodel1,$51.Pe,(1<.$83.)Pst,$84.P,(=.(1;.(1:.&40.))(4.R6.)(27.(1:.&40.)))P,(=.(30.(32.$39.$51.))(85.Vsegs,R7.R6.)(34.(32.$39.$51.)(36.$39.$51.R5.R4.)))P,(81.Vsegs,(86.R8.R7.)R4.R3.)(1?.(=.(1<.$83.)R5.(42.$83.))(=.$84.R4.(82.(86.R7.R6.))))")
(* [comment removed for export] *).
Proof.
  intros ms model ms1 model1 e st Hsvc Hacc Hss.
  inversion Hss; subst;
    match goal with
    | Hp : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in Hp; discriminate
    | Ha : mi_account_step segs ms model = _ |- _ =>
        rewrite Hacc in Ha; try discriminate; injection Ha as <- <-; split; reflexivity
    end.
Qed.

(* [comment removed for export] *)
#[using="HH Hwx"] Theorem node_instr_restricted : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PA,(1<.(32.$25.$25.))Pms,$39.Pmsr',$39.Pmodel,$51.P,(7;.VH,(5;.R1.)R4.)P,(72.R5.)P,(7>.R6.R3.)P,(=.(1;.(1:.&40.))(6>.R4.)(27.(1:.&40.)))P,(=.(1;.(1:.&40.))(4.R7.)(27.(1:.&40.)))P,(=.(30.$39.)(3?.Vsegs,(3;.VH,R8.))(34.$39.R7.))(37.$51.Lmodel',$51.(1?.(7>.R;.R1.)(1?.(56.R8.R1.)(1?.(3=.VH,R9.)(1?.(=.(30.(32.$39.$51.))(85.Vsegs,R:.R8.)(34.(32.$39.$51.)(36.$39.$51.(3<.VH,(8.R:.)R9.)R1.)))(87.(86.R:.R8.)$88.L,$88.(42.$83.)L,$88.(86.(3<.VH,(8.R;.)R:.)R2.)))))))")
(* [comment removed for export] *).
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs.
  destruct (mi_account_step_restricted A ms msr' model Hcov Hwf Hinv Hs)
    as (mat' & Hacc & Hinv' & Hcl).
  exists (with_vm_backing (m_vm_lazy model) mat' model).
  split; [exact Hinv'|]. split; [apply with_vm_backing_same|]. split; [exact Hcl|].
  split; [exact Hacc|].
  split.
  - intros []. apply sstep_instr; [exact Hh | exact Hsvc | exact Hacc].
  - intros e st Hss. exists tt.
    exact (sstep_instr_det ms model _ _ e st Hsvc Hacc Hss).
Qed.

(* [comment removed for export] *)
#[using="HH Hwx"] Lemma step_hclean : forall ms ms',
  hclean H ms ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  hclean H ms'.
Proof.
  intros ms ms' Hc Hs. rewrite <- (hclean_restrict_id H ms Hc) in Hs.
  destruct (step_restrict_sound segs H HH Hwx ms ms' Hs) as (rep & _ & _ & _ & Hcl & _).
  exact Hcl.
Qed.

#[using="HH Hwx"] Lemma msteps_hclean : forall ms ms',
  msteps segs ms ms' -> hclean H ms -> hclean H ms'.
Proof.
  intros ms ms' Hms. induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hrest IH]; intros Hc.
  - exact Hc.
  - apply IH. exact (step_hclean ms ms1 Hc Hstep).
Qed.

#[using="Type"] Lemma unrestrict_munrestrict : forall f g ms',
  unrestrict H (munrestrict H f g) ms' = unrestrict H f ms'.
Proof.
  intros f g ms'. unfold unrestrict. f_equal.
  apply functional_extensionality. intro x. unfold munrestrict.
  destruct (H x); reflexivity.
Qed.

(* [comment removed for export] *)
Variable P : config -> Prop.
Hypothesis P_silent1 : forall c c',
  node_ok c unit (fun _ => []) (fun _ => c') -> P c' -> P c.

#[using="HH Hwx P_silent1"] Theorem rz_step_restricted : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PA,(1<.(32.$25.$25.))Pms,$39.Pmsr',$39.Pmodel,$51.P,(7;.VH,(5;.R1.)R4.)P,(72.R5.)P,(7>.R6.R3.)P,(=.(1;.(1:.&40.))(6>.R4.)(27.(1:.&40.)))P,(=.(1;.(1:.&40.))(4.R7.)(27.(1:.&40.)))P,(=.(30.$39.)(3?.Vsegs,(3;.VH,R8.))(34.$39.R7.))P,Pmodel',$51.P,(7>.R;.R1.)P,(56.R9.R2.)A1.VP,(86.(3<.VH,(8.R<.)R;.)R3.)A1.VP,(86.R:.R8.)")
(* [comment removed for export] *).
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs Hk.
  destruct (node_instr_restricted A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs)
    as (model' & Hinv' & Hsame & _ & _ & Hnode).
  exact (P_silent1 _ _ Hnode (Hk model' Hinv' Hsame)).
Qed.

#[using="HH Hwx P_silent1"] Theorem rz_msteps_restricted : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PA,(1<.(32.$25.$25.))Pmsr0,$39.Pmsr',$39.P,(89.Vsegs,R2.R1.)Pms,$39.Pmodel,$51.P,(=.$39.R5.(3;.VH,R2.))P,(7;.VH,(5;.R2.)R7.)P,(72.R8.)P,(7>.R9.R4.)P,(=.(1;.(1:.&40.))(6>.R5.)(27.(1:.&40.)))P,Pmodel',$51.P,(7>.R<.R1.)P,(56.R8.R2.)A1.VP,(86.(3<.VH,(8.R:.)R<.)R3.)A1.VP,(86.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros A msr0 msr' Hms.
  induction Hms as [msr | msr msr1 msr2 Hsvc Hstep Hrest IH];
    intros ms model -> Hcov Hwf Hinv Hh Hk.
  - specialize (Hk model Hinv (same_but_materialized_refl model)).
    rewrite unrestrict_restrict in Hk. exact Hk.
  - rewrite restrict_svc_pending in Hsvc.
    destruct (node_instr_restricted A ms msr1 model Hcov Hwf Hinv Hh Hsvc Hstep)
      as (model1 & Hinv1 & Hsame1 & Hcl1 & _ & Hnode).
    apply (P_silent1 _ _ Hnode).
    pose proof (same_but_materialized_frame model model1 Hsame1) as Hfr.
    apply (IH (unrestrict H (ms_mem ms) msr1) model1).
    + symmetry. apply restrict_unrestrict_clean. exact Hcl1.
    + replace (m_vm_lazy model1) with (m_vm_lazy model) by (symmetry; apply Hfr). exact Hcov.
    + exact Hwf.
    + exact Hinv1.
    + replace (m_halted model1) with (m_halted model) by (symmetry; apply Hfr). exact Hh.
    + intros model' Hinv' Hsame'.
      rewrite unrestrict_mem, unrestrict_munrestrict.
      apply Hk; [exact Hinv' | exact (same_but_materialized_trans _ _ _ Hsame1 Hsame')].
Qed.
(* [comment removed for export] *)
#[using="HH Hwx P_silent1"] Theorem rz_msteps_restricted' : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PA,(1<.(32.$25.$25.))Pms,$39.Pmsr',$39.Pmodel,$51.P,(7;.VH,(5;.R1.)R4.)P,(72.R5.)P,(7>.R6.R3.)P,(=.(1;.(1:.&40.))(6>.R4.)(27.(1:.&40.)))P,(89.Vsegs,(3;.VH,R7.)R6.)P,Pmodel',$51.P,(7>.R:.R1.)P,(56.R8.R2.)P,(3=.VH,R:.)A1.VP,(86.(3<.VH,(8.R<.)R;.)R4.)A1.VP,(86.R9.R7.)")
(* [comment removed for export] *).
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hms Hk.
  pose proof (msteps_hclean _ _ Hms (restrict_hclean H ms)) as Hcl.
  apply (rz_msteps_restricted A (restrict H ms) msr' Hms ms model eq_refl Hcov Hwf Hinv Hh).
  intros model' Hinv' Hsame'. exact (Hk model' Hinv' Hsame' Hcl).
Qed.

End Nodes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma materialize_model_accesses_nil : forall m,
  materialize_model_accesses m [] = Some m.
Proof.
  intros m. unfold materialize_model_accesses, materialize_accesses.
  unfold newly_materialized_pages. cbn [accesses_pages List.filter].
  rewrite with_vm_backing_id. reflexivity.
Qed.

(* [comment removed for export] *)
Definition materialized_succ (m : Model) (accs : list (word * nat)) : Model :=
  match materialize_model_accesses m accs with
  | Some m' => m'
  | None => m
  end.

Section SyscallNode.
Variable segs : list Segment.
Variable H : word -> bool.

(* [comment removed for export] *)
#[using="Type"] Theorem node_syscall_restricted : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PA,(1<.(32.$25.$25.))Pms,$39.Pmodel,$51.Px8,(1:.&40.)PI,StPeff,P,R1.$8:.Pmdl,P,R2.$51.Pevs,P,R3.(1<.$83.)P,(72.R8.)P,(=.(1;.(1:.&40.))(6>.R7.)(27.(1:.&40.)))P,(=.(1;.(1:.&40.))(4.R9.)(1>.(1:.&40.)R7.))P,Pi,R7.(8;.(8<.Vsegs,R;.R9.)R:.(8=.$8:.A1.R7.R1.A1.R6.R1.A1.R5.R1.))P,Pr,(8>.$8:.)P,(8;.(8<.Vsegs,R<.R:.)R;.R1.)(37.R:.Li,R:.(=.(8>.$8:.)R3.(8=.$8:.A1.R:.R1.A1.R9.R1.A1.R8.R1.)))P,Pi,R9.(=.(1;.(1:.&40.))(6>.A1.R8.R1.)(27.(1:.&40.)))P,Pi,R:.(7;.VH,(5;.A1.R9.R1.)R?.)P,Pi,R;.(7>.R10.A1.R:.R1.)P,Pi,R<.(38.VH,(8?.A1.R<.R1.))(1?.Pi,R=.(1?.(7>.R12.(90.A1.R<.R1.(8?.A1.R=.R1.)))(56.A1.R<.R1.(90.A1.R<.R1.(8?.A1.R=.R1.))))(91.Vsegs,(86.R10.R?.)R=.R:.Li,R=.(86.(92.(93.R11.A1.R=.R1.))(90.A1.R<.R1.(8?.A1.R=.R1.)))))")
(* [comment removed for export] *).
Proof.
  intros A ms model x8 I eff mdl evs Hwf Hh Hsvc Hsound Hcompl Hnh Hcov Hinv Hav.
  assert (Hmat : forall i, exists mat',
            materialize_model_accesses (mdl i) (syscall_effect_accesses (eff i))
              = Some (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))
            /\ MInv A (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))).
  { intros i. exact (materialize_restricted H A (mdl i) _ (Hcov i) Hwf (Hinv i) (Hav i)). }
  split.
  - intros i. destruct (Hmat i) as (mat' & Hm & Hinv').
    unfold materialized_succ. rewrite Hm. split; [exact Hinv' | apply with_vm_backing_same].
  - split.
    + intros i. destruct (Hmat i) as (mat' & Hm & Hinv').
      unfold materialized_succ. rewrite Hm.
      eapply sstep_syscall; [exact Hh | exact Hsvc | exact (Hsound i) | exact (Hnh i) | exact Hm].
    + intros e st Hss. inversion Hss; subst;
        match goal with
        | Hp : ms_svc_pending ms = None |- _ => rewrite Hsvc in Hp; discriminate
        | Hp : ms_svc_pending ms = Some ?x |- _ =>
            rewrite Hsvc in Hp; injection Hp as <-
        end;
        match goal with
        | Hsp : syscall_spec _ _ ?r |- _ =>
            destruct (Hcompl _ Hsp) as [i Ei]; try discriminate Ei;
            injection Ei as -> -> ->
        end.
      * (* [comment removed for export] *)
        exists i. split; [reflexivity|].
        unfold materialized_succ.
        match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ => rewrite Hm end.
        reflexivity.
      * (* [comment removed for export] *)
        destruct (Hmat i) as (mat' & Hm & _).
        match goal with Hn : materialize_model_accesses _ _ = None |- _ => rewrite Hm in Hn; discriminate end.
      * (* [comment removed for export] *)
        match goal with Hc : m_halted (mdl i) = Some _ |- _ => rewrite (Hnh i) in Hc; discriminate end.
      * (* [comment removed for export] *)
        match goal with Hk : m_killed (mdl i) = Some _ |- _ =>
          rewrite (m_killed_of_m_halted_none _ (Hnh i)) in Hk; discriminate end.
Qed.
End SyscallNode.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkH (L : list (word * word)) (A : list (Z * Z)) : word -> bool :=
  fun a => page_in_ranges (page_base a) L && negb (page_allowedb A (page_base a)).

Lemma page_in_ranges_incl : forall p l L,
  incl l L -> page_in_ranges p l = true -> page_in_ranges p L = true.
Proof.
  intros p l L Hincl Hp. unfold page_in_ranges in *.
  apply existsb_exists in Hp as (r & Hin & Hr).
  apply existsb_exists. exists r. split; [exact (Hincl r Hin) | exact Hr].
Qed.

Lemma lazy_cover_mkH : forall L A lazy,
  incl lazy L -> lazy_cover (mkH L A) lazy A.
Proof.
  intros L A lazy Hincl w Hl Hw. unfold mkH in Hw.
  rewrite (page_in_ranges_incl _ _ _ Hincl Hl) in Hw. cbn in Hw.
  destruct (page_allowedb A (page_base w)); [reflexivity | discriminate].
Qed.

(* [comment removed for export] *)
Definition seg_top (seg : Segment) : Z :=
  (Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.

Definition wx_segs_nowrap_b (segs : list Segment) : bool := ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "(94.$;.Lseg,$;.(95.(96.(?.(10.R1.)(11.R1.)))(48.(97.R1.)(18.+2.+40.)))O1.)")
(* [comment removed for export] *).

Lemma wx_segs_nowrap_of_b : forall segs,
  wx_segs_nowrap_b segs = true -> wx_segs_nowrap segs.
Proof.
  intros segs Hb seg Hin Hwx. unfold wx_segs_nowrap_b in Hb.
  rewrite forallb_forall in Hb. specialize (Hb seg Hin). rewrite Hwx in Hb. cbn in Hb.
  apply Z.leb_le in Hb. exact Hb.
Qed.

Definition segs_below_b (segs : list Segment) (top : Z) : bool :=
  forallb (fun seg => (seg_top seg <=? top)%Z) segs.

Lemma find_segment1_none_above : forall segs top x,
  segs_below_b segs top = true -> (top <= x)%Z -> find_segment segs x 1 = None.
Proof.
  induction segs as [|s l IH]; intros top x Hb Hx; [reflexivity|].
  cbn [segs_below_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply Z.leb_le in Hs. unfold seg_top in Hs.
  cbn [find_segment].
  replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z
    with false.
  - exact (IH top x Hl Hx).
  - symmetry. apply andb_false_iff. right. apply Z.leb_gt. lia.
Qed.

(* [comment removed for export] *)
Lemma H_off_segments_above : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Psegs,(1<.$;.)PH,P,(1:.&40.)$>.Ptop,$25.P,(=.$>.(98.R3.R1.)$12.)P,Pa,(1:.&40.)P,(=.$>.A1.R4.R1.$12.)(13.R4.(29.&40.R2.))(99.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros segs H top Hb Ha a HHa. exact (find_segment1_none_above segs top _ Hb (Ha a HHa)).
Qed.

(* [comment removed for export] *)
Definition ranges_from_b (L : list (word * word)) (top : Z) : bool :=
  forallb (fun r => (top <=? bv_unsigned (fst r))%Z) L.

Lemma page_base_le : forall a, (bv_unsigned (page_base a) <= bv_unsigned a)%Z.
Proof.
  intros a. unfold page_base, page_base_of. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  pose proof (Z.div_mod (bv_unsigned a) page_size ltac:(unfold page_size; lia)) as Hdm.
  pose proof (Z.mod_pos_bound (bv_unsigned a) page_size ltac:(unfold page_size; lia)) as Hmb.
  assert (Hq : (0 <= bv_unsigned a / page_size)%Z)
    by (apply Z.div_pos; unfold page_size in *; lia).
  set (q := (bv_unsigned a / page_size)%Z) in *.
  change (bv_modulus 64) with (2 ^ 64)%Z in *. unfold page_size in *.
  rewrite bv_wrap_small; [lia|].
  change (bv_modulus 64) with (2 ^ 64)%Z. lia.
Qed.

Lemma mkH_above : forall L A top a,
  ranges_from_b L top = true -> mkH L A a = true -> (top <= bv_unsigned a)%Z.
Proof.
  intros L A top a Hb Ha. unfold mkH in Ha. apply andb_true_iff in Ha as [Hp _].
  unfold page_in_ranges in Hp. apply existsb_exists in Hp as ([lo sz] & Hin & Hr).
  cbn [fst snd] in Hr. apply andb_true_iff in Hr as [H1 _]. apply Z.leb_le in H1.
  unfold ranges_from_b in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Hin).
  cbn [fst] in Hb. apply Z.leb_le in Hb.
  pose proof (page_base_le a). lia.
Qed.

Corollary H_off_segments_mkH : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "Psegs,(1<.$;.)PL,(1<.(32.(1:.&40.)(1:.&40.)))PA,(1<.(32.$25.$25.))Ptop,$25.P,(=.$>.(98.R4.R1.)$12.)P,(=.$>.(9:.R4.R2.)$12.)(99.R6.(9;.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros segs L A top Hs HL.
  apply (H_off_segments_above segs (mkH L A) top Hs).
  intros a Ha. exact (mkH_above L A top a HL Ha).
Qed.

(* [comment removed for export] *)
Lemma MInv_intro_empty : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PA,(1<.(32.$25.$25.))Pm,$51.P,(=.(1<.(1:.&40.))(55.R1.)(42.(1:.&40.)))P,(13.(14.(53.R2.)(75.R3.))(7=.(5:.R2.)))(7>.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros A m He Hb. constructor; rewrite ?He;
    [constructor | intros p Hp; destruct Hp | intros p Hp; destruct Hp
    | intros p Hp; destruct Hp | exact Hb].
Qed.

(* [comment removed for export] *)
Lemma MInv_transport : ltac2:(CDefT.buildp (gd_tbl_AsanAcct ()) "PA,(1<.(32.$25.$25.))Pm,$51.Pm',$51.P,(7>.R3.R2.)P,(=.(1<.(1:.&40.))(55.R2.)(55.R3.))P,(=.(1<.(32.(1:.&40.)(1:.&40.)))(5;.R3.)(5;.R4.))P,(13.(14.(53.R4.)(75.R6.))(7=.(5:.R4.)))(7>.R7.R5.)")
(* [comment removed for export] *).
Proof.
  intros A m m' [H1 H2 H3 H4 H5] Hm Hl Hb. constructor; rewrite ?Hm, ?Hl; assumption.
Qed.

