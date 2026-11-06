(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanCeil.  (* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes SpecConsts.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_RefNodes () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_brk"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_result"; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.check_syscall"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.check_mmap"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.check_munmap"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "WithSegs.three"; "OSSVerify.KrLib.ABoot.ShapeAlg.TSet"; "OSSVerify.KrLib.ABoot.ShapeAlg.node_ok"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "OSSVerify.KrLib.ABoot.ShapeAlg.realizes"; "WithSegs.T1"; "WithSegs.T2"; "WithSegs.T3"; "t_alt3"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "OSSVerify.KrLib.ABoot.AgentNodes.epend"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "asanreflect_fx"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.ABoot.MmapSim.zfill"; "OSSVerify.KrLib.ABoot.MmapSim.unfill"; "OSSVerify.KrLib.ABoot.CatExec.wbytes"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "OSSVerify.KrLib.ABoot.MmapSim.munmap_model"; "LinuxProcessSemantics.LinuxProcessSem.State.with_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.map_remove"; "LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract"; "Stdlib.ZArith.BinInt.Z.add"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "Corelib.Init.Specif.sig"; "OSSVerify.KrLib.ABoot.AllocSim.brk_resolution_ok"; "Corelib.Init.Specif.proj1_sig"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_zeros"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_unmaps"; "OSSVerify.KrLib.ABoot.AllocSim.brk_model"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.iff"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_grow_ok"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "LinuxProcessSemantics.LinuxProcessSem.State.page_size"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.ltb"; "Stdlib.ZArith.BinInt.Z.leb"; "OSSVerify.KrLib.ABoot.AsanCeil.alloc_ceiling"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.ABoot.AsanCeil.hint_placement_ok_b"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_top"; "OSSVerify.KrLib.ABoot.AsanCeil.placement_policy"; "WithSegs.grant_ok_na_pin"; "WithSegs.grant_ok_na"; "OSSVerify.KrLib.ABoot.AsanCeil.init_sp_ok"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.errno_ret_in"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_errnos"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mprotect.check_mprotect"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_forget_range"; "WithSegs.fixed_noaccess_model"; "WithSegs.fixed_destroyed_model"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Fork.check_set_tid_address"; "LinuxProcessSemantics.LinuxProcessSem.State.m_tid"; "WithSegs.tid_I"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork.PID_MAX_ENVELOPE"; "LinuxProcessSemantics.LinuxProcessSem.State.with_tid"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_exit"; "stdpp.bitvector.definitions.bv_and"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_backing_used"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_backed_bytes"; "LinuxProcessSemantics.LinuxProcessSem.State.sp_window_lo"; "LinuxProcessSemantics.LinuxProcessSem.State.reserved_top"; "Stdlib.Lists.List.In"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.State.iv_subtract"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.snd"; "LinuxProcessSemantics.LinuxProcessSem.State.live_bytes"; "LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract_all"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_live_bytes"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_budget_ok"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.Fs.file_read"; "Stdlib.Arith.PeanoNat.Nat.min"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.word_to_nat"; "Corelib.Init.Nat.sub"; "Corelib.Init.Peano.le"; "zconflict"; "cand"; "Stdlib.Lists.List.NoDup"; "Corelib.Init.Datatypes.S"; "Stdlib.Lists.List.filter"; "Corelib.Init.Datatypes.negb"; "Corelib.Init.Peano.lt"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition t_alt3 (A B C : TSet) : TSet := t_alt2 A (t_alt2 B C).

Lemma t_alt2_idem : forall A, t_eq (t_alt2 A A) A.
Proof. intros A tr. unfold t_alt2. tauto. Qed.

Lemma t_alt3_idem : forall A, t_eq (t_alt3 A A A) A.
Proof. intros A tr. unfold t_alt3, t_alt2. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_fds_halted' : forall fds m, m_halted (with_fds fds m) = m_halted m.
Proof. intros fds m. reflexivity. Qed.

Lemma with_fds_lazy : forall fds m, m_vm_lazy (with_fds fds m) = m_vm_lazy m.
Proof. intros fds m. reflexivity. Qed.

Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. intros t m. reflexivity. Qed.

Lemma with_tid_lazy : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof. intros t m. reflexivity. Qed.

Lemma with_vmmaps_lazy' : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. intros h m. reflexivity. Qed.

Lemma with_vmmaps_eta : forall m,
  with_vmmaps (m_vmmaps m) m = m.
Proof. intros m. destruct m as [? [? ? ?] ? ? ? ?]; reflexivity. Qed.

Lemma vmmaps_eta : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Ph,$0.(1.$0.(2.(3.R1.)(4.R1.)(5.R1.)(6.R1.)(7.R1.)(8.R1.)(9.R1.)(:.R1.))R1.)")
(* [comment removed for export] *).
Proof. intros h. destruct h; reflexivity. Qed.

Lemma Z_to_bv_u_eq' : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma vm_forget_range_id : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_forget_range lo hi m = m.
Proof.
  intros lo hi m Hl Hm. unfold vm_forget_range, with_vm_backing.
  rewrite Hl, Hm. cbn [maps_subtract List.filter].
  destruct m as [? [? l mt] ? ? ? ?]. cbn in Hl, Hm. subst. reflexivity.
Qed.

Lemma vm_forget_range_lazy_nil : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_lazy (vm_forget_range lo hi m) = [].
Proof.
  intros lo hi m Hl. unfold vm_forget_range, with_vm_backing. cbn [m_vm_lazy]. rewrite Hl. reflexivity.
Qed.

Lemma vm_forget_range_halted : forall lo hi m,
  m_halted (vm_forget_range lo hi m) = m_halted m.
Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_check : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pms,$;.Px8,(<.&40.)Pmodel,$=.Peff,$>.P,(1.$?.(10.&40.R3.)+=>.)(1.$11.(12.(13.Vsegs,R5.R4.)R2.R3.)(14.(15.R5.#0.)(15.R5.#1.)(15.R5.#2.)(15.R5.#3.)(15.R5.#4.)(15.R5.#5.)R2.R3.))")
(* [comment removed for export] *).
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

#[using="Type"] Lemma munmap_check : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pms,$;.Px8,(<.&40.)Pmodel,$=.Peff,$>.P,(1.$?.(10.&40.R3.)+=7.)(1.$11.(12.(13.Vsegs,R5.R4.)R2.R3.)(16.(15.R5.#0.)(15.R5.#1.)R2.R3.))")
(* [comment removed for export] *).
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive three : Type := T1 | T2 | T3.

#[using="Type"] Lemma rz_alt3 : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pc,$17.Pnx,P,$18.$17.PA,$19.PB,$19.PC,$19.P,(1:.Vsegs,R5.$18.L,$18.(1;.$1<.)R4.)P,(1=.Vsegs,A1.R5.$1>.R4.)P,(1=.Vsegs,A1.R6.$1?.R4.)P,(1=.Vsegs,A1.R7.$20.R4.)(1=.Vsegs,R9.(21.R7.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros c nx A B C Hnode HA HB HC.
  apply (rz_conseq segs c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
  - apply (rz_cases segs c three nx _ T1 Hnode). intros [| |]; assumption.
  - intros tr. unfold t_alt3, t_alt2, t_alt. split.
    + intros [[| |] H]; tauto.
    + intros [H | [H | H]]; [exists T1 | exists T2 | exists T3]; exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_of_iff : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pc,$17.PI,StPevs,P,R1.(22.$1<.)Pnx,P,R2.$17.P,Pi,R3.(23.Vsegs,R5.A1.R3.R1.(24.A1.R2.R1.))P,Pe,(22.$1<.)Pst,$25.P,(23.Vsegs,R7.R2.R1.)(26.R7.Li,R7.(27.(1.(22.$1<.)R4.A1.R7.R1.)(1.$25.R3.(24.A1.R6.R1.))))(1:.Vsegs,R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof. intros; split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma adv_ret_epend : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pregs,(28.&5.(<.&40.))Ppc,(<.&40.)Pmem,P,(<.&40.)(29.(<.&8.))Prom,P,(<.&40.)(29.(<.&8.))Px8,(<.&40.)Pr,(<.&40.)(1.$;.(2:.(2;.(2<.R6.R5.R4.R3.R2.)(2=.R1.(1;.(2>.(<.&40.)(22.(<.&8.))))(1;.(2>.(<.&40.)(<.&40.)))(1;.(2>.(<.&40.)(<.&40.)))(1;.$2?.)(1;.(2>.(<.&40.)$30.)))))(31.$32.(33.R6.(34.&5.+:.$35.)R1.)(36.R5.+4.)R4.R3.))")
(* [comment removed for export] *).
Proof. intros. unfold epend. apply adv_eff_ret. Qed.

#[using="Type"] Lemma adv_zeros1_epend : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pregs,(28.&5.(<.&40.))Ppc,(<.&40.)Pmem,P,(<.&40.)(29.(<.&8.))Prom,P,(<.&40.)(29.(<.&8.))Px8,(<.&40.)Pr,(<.&40.)Pa,(<.&40.)Pn,(<.&40.)(1.$;.(2:.(2;.(2<.R8.R7.R6.R5.R4.)(2=.R3.(1;.(2>.(<.&40.)(22.(<.&8.))))(37.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)R2.R1.)(1;.(2>.(<.&40.)(<.&40.))))(1;.(2>.(<.&40.)(<.&40.)))(1;.$2?.)(1;.(2>.(<.&40.)$30.)))))(31.$32.(33.R8.(34.&5.+:.$35.)R3.)(36.R7.+4.)(39.R2.R1.R6.)R5.))")
(* [comment removed for export] *).
Proof.
  intros. unfold epend.
  assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
  { cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

#[using="Type"] Lemma adv_unmaps1_epend : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pregs,(28.&5.(<.&40.))Ppc,(<.&40.)Pmem,P,(<.&40.)(29.(<.&8.))Prom,P,(<.&40.)(29.(<.&8.))Px8,(<.&40.)Pr,(<.&40.)Pa,(<.&40.)Pn,(<.&40.)(1.$;.(2:.(2;.(2<.R8.R7.R6.R5.R4.)(2=.R3.(1;.(2>.(<.&40.)(22.(<.&8.))))(1;.(2>.(<.&40.)(<.&40.)))(37.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)R2.R1.)(1;.(2>.(<.&40.)(<.&40.))))(1;.$2?.)(1;.(2>.(<.&40.)$30.)))))(31.$32.(33.R8.(34.&5.+:.$35.)R3.)(36.R7.+4.)(3:.R2.R1.R6.)R5.))")
(* [comment removed for export] *).
Proof.
  intros. unfold epend.
  assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) [] = unfill a n mem).
  { cbn [apply_writes apply_zeros].
    apply functional_extensionality. intro x.
    unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
    rewrite orb_false_r. reflexivity. }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

#[using="Type"] Lemma adv_write1_epend : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pregs,(28.&5.(<.&40.))Ppc,(<.&40.)Pmem,P,(<.&40.)(29.(<.&8.))Prom,P,(<.&40.)(29.(<.&8.))Px8,(<.&40.)Pr,(<.&40.)Pbuf,(<.&40.)Pdata,(22.(<.&8.))(1.$;.(2:.(2;.(2<.R8.R7.R6.R5.R4.)(2=.R3.(37.(2>.(<.&40.)(22.(<.&8.)))(38.(<.&40.)(22.(<.&8.))R2.R1.)(1;.(2>.(<.&40.)(22.(<.&8.)))))(1;.(2>.(<.&40.)(<.&40.)))(1;.(2>.(<.&40.)(<.&40.)))(1;.$2?.)(1;.(2>.(<.&40.)$30.)))))(31.$32.(33.R8.(34.&5.+:.$35.)R3.)(36.R7.+4.)(3;.R6.R2.R1.)R5.))")
(* [comment removed for export] *).
Proof. intros. unfold epend. rewrite adv_apply_write, write_to_mem_wbytes. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

#[using="Type"] Lemma munmap_model_simple : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pa,(<.&40.)Pn,(<.&40.)Pm,$=.P,(1.(22.(2>.(<.&40.)(<.&40.)))(3<.R1.)(1;.(2>.(<.&40.)(<.&40.))))P,(1.(22.(<.&40.))(3=.R2.)(1;.(<.&40.)))(1.$=.(3>.R5.R4.R3.)(3?.(2.(3.(40.R3.))(41.(4.(40.R3.))R5.)(42.(5.(40.R3.))(10.&40.R5.)(43.(10.&40.R5.)(10.&40.R4.)))(6.(40.R3.))(7.(40.R3.))(8.(40.R3.))(9.(40.R3.))(:.(40.R3.)))R3.))")
(* [comment removed for export] *).
Proof.
  intros a n m Hl Hm. unfold munmap_model, with_mmap_destroyed.
  apply vm_forget_range_id; [rewrite with_vmmaps_lazy'; exact Hl | exact Hm].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma node_brk : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pms,$;.Pmodel,$=.Px8,(<.&40.)P,(1.(29.(<.&40.))(44.R2.)(45.(<.&40.)))P,(1.(22.(2>.(<.&40.)(<.&40.)))(3<.R3.)(1;.(2>.(<.&40.)(<.&40.))))P,(1.(29.(<.&40.))(46.R5.)(47.(<.&40.)R3.))P,(1.$?.(10.&40.R4.)+=6.)(1:.Vsegs,(48.R7.R6.)(49.(<.&40.)Lr,(<.&40.)(4:.R7.(15.R8.#0.)R1.))L,(49.(<.&40.)Lr,(<.&40.)(4:.R7.(15.R8.#0.)R1.))(1;.$1<.)Li,(49.(<.&40.)Lr,(<.&40.)(4:.R7.(15.R8.#0.)R1.))(48.(2:.(2;.R8.(2=.(4;.(<.&40.)Lr,(<.&40.)(4:.R8.(15.R9.#0.)R1.)R1.)(1;.(2>.(<.&40.)(22.(<.&8.))))(4<.(15.R8.#0.)(4;.(<.&40.)Lr,(<.&40.)(4:.R8.(15.R9.#0.)R1.)R1.)(7.(40.R7.)))(4=.(4;.(<.&40.)Lr,(<.&40.)(4:.R8.(15.R9.#0.)R1.)R1.)(7.(40.R7.)))(1;.$2?.)(1;.(2>.(<.&40.)$30.)))))(4>.(15.R8.#0.)(4;.(<.&40.)Lr,(<.&40.)(4:.R8.(15.R9.#0.)R1.)R1.)R7.)))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno. split.
  - intros [r Hr]. cbn [proj1_sig].
    pose proof (brk_ok_intro segs ms x8 model r Hno Hr) as Hspec.
    destruct (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno Hspec) as (_ & Hh' & _ & _ & Hlazy').
    apply (sstep_syscall segs ms model x8 _ _ _ [] Hh Hsvc Hspec Hh').
    apply materialize_model_accesses_no_lazy. rewrite Hlazy'. exact Hlazy.
  - intros e st Hss.
    destruct (sstep_brk_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hss) as (eff & model' & Hspec & -> & ->).
    apply (brk_ok_iff segs ms x8 model eff model' [] Hno) in Hspec.
    destruct Hspec as (Heff & _ & Hok & ->).
    exists (exist _ (eff_ret eff) Hok). cbn [proj1_sig]. rewrite <- Heff. split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma brk_r_ok_grow_cases : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pm,$=.Preq,(<.&40.)Pr,(<.&40.)Zh,$0.(40.R3.)P,(4?.=(10.&40.R3.))P,(50.(10.&40.(6.R2.))(10.&40.R4.))P,(50.(10.&40.(7.R3.))(10.&40.R5.))(51.(4:.R7.R6.R5.)(52.(1.(<.&40.)R5.(7.R4.))(27.(1.(<.&40.)R5.R6.)(1.$53.(54.R7.R6.R6.)$55.))))")
(* [comment removed for export] *).
Proof.
  intros m req r h Hpos Hs Hb.
  unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta. fold h.
  assert (E0 : w_is0 req = false).
  { unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E0. unfold min_brk.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [orb].
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. split.
  - intros [[-> | ->] Hg]; [right; auto | left; reflexivity].
  - intros [-> | [-> Hg]]; split; [right; reflexivity | | left; reflexivity | exact Hg].
    unfold Mmap.brk_grow_ok. fold h. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_model_keep : forall m req,
  brk_model req (vm_brk (m_vmmaps m)) m = m.
Proof.
  intros m req. unfold brk_model, with_brk_next. cbv zeta.
  rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r, brk_grants_keep, brk_unmaps_keep.
  cbn [app maps_subtract_ranges fold_left]. rewrite vmmaps_eta. apply with_vmmaps_eta.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_model_grow_eq : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pm,$=.Pd,$?.Zh,$0.(40.R2.)Zb,(<.&40.)(7.R1.)P,(4?.=R3.)P,(4?.=(10.&40.R2.))P,(4?.(43.(10.&40.R3.)R5.)(56.+2.+40.))P,(1.$?.(57.(10.&40.R4.)$58.)=)P,(1.$?.(57.R7.$58.)=)(1.$=.(4>.(59.&40.(43.(10.&40.R6.)R8.))(59.&40.(43.(10.&40.R6.)R8.))R9.)(3?.(2.(3.R7.)(37.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)R6.(59.&40.R8.))(4.R7.))(5.R7.)(6.R7.)(59.&40.(43.(10.&40.R6.)R8.))(8.R7.)(9.R7.)(:.R7.))R9.))")
(* [comment removed for export] *).
Proof.
  intros m d h b Hd Hb0 Hnw Hbal Hdal.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)).
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  unfold brk_model, with_brk_next. cbv zeta. fold h. fold b.
  rewrite (brk_unmaps_grow req b) by lia. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next. fold b.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned b))) by lia. rewrite andb_false_r.
  rewrite (brk_grants_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
  cbn [app maps_subtract_ranges fold_left].
  replace (req - b) with (Z_to_bv 64 d); [reflexivity|].
  apply bv_eq. rewrite bv_sub_unsigned, Hureq.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition noaccess_model (a n : word) (m : Model) : Model := ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "(3?.(2.(3.(40.O1.))(37.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)O3.O2.)(4.(40.O1.)))(37.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)O3.O2.)(5.(40.O1.)))(6.(40.O1.))(7.(40.O1.))(8.(40.O1.))(9.(40.O1.))(:.(40.O1.)))O1.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool := ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "(5:.(5:.(5:.(5:.(5;.(57.(10.&40.O2.)$58.)=)(5<.=(10.&40.O2.)))(5=.(43.(10.&40.O2.)O1.)$5>.))(5?.(60.(2>.(<.&40.)(<.&40.))(3.(40.O3.))(4.(40.O3.)))O2.(59.&40.O1.)))(61.O4.(40.O3.)(10.&40.O2.)O1.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition grant_ok_na_pin (m : Model) (a : word) (n : Z) : bool := ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "(5:.(5:.(5:.(5;.(57.(10.&40.O2.)$58.)=)(5<.=(10.&40.O2.)))(5=.(43.(10.&40.O2.)O1.)(62.(40.O3.))))(5?.(60.(2>.(<.&40.)(<.&40.))(3.(40.O3.))(4.(40.O3.)))O2.(59.&40.O1.)))")
(* [comment removed for export] *).

#[using="Type"] Lemma grant_ok_na_of_pin : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "P,$63.Phint,(<.&40.)Pm,$=.Pa,(<.&40.)Pn,$?.P,(4?.=R1.)P,(1.$?.(57.R2.$58.)=)P,(1.$53.(64.R5.R4.R3.)$55.)(1.$53.(65.R7.R6.R5.R4.)$55.)")
(* [comment removed for export] *).
Proof.
  intros PL hint m a n Hn Hnal H. unfold grant_ok_na_pin in H.
  apply andb_true_iff in H as [H Hrf]. apply andb_true_iff in H as [H Htop]. apply andb_true_iff in H as [Hal Hpos].
  destruct (PL (m_vmmaps m) a n Hn Hnal (proj1 (Z.eqb_eq _ _) Hal) (proj1 (Z.ltb_lt _ _) Hpos) (proj1 (Z.leb_le _ _) Htop) Hrf) as [Hce Hpl].
  unfold grant_ok_na. rewrite Hal, Hpos, Hrf, (proj2 (Z.leb_le _ _) Hce). cbn [andb].
  unfold hint_placement_ok_b. destruct (w_is0 hint); [exact Hpl | reflexivity].
Qed.

#[using="Type"] Lemma grant_ok_na_pin_of_grant_ok : forall hint m a n, grant_ok hint m a n = true -> grant_ok_na_pin m a n = true.
Proof.
  intros hint m a n H. unfold grant_ok in H. unfold grant_ok_na_pin.
  apply andb_true_iff in H as [H _]. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma grant_ok_na_pin_of_gate : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Phint,(<.&40.)Pm,$=.Pa,(<.&40.)Pn,$?.P,(66.(40.R3.))P,(1.$53.(65.R5.R4.R3.R2.)$55.)(1.$53.(64.R5.R4.R3.)$55.)")
(* [comment removed for export] *).
Proof.
  intros hint m a n Hisp H. unfold grant_ok_na in H. unfold grant_ok_na_pin.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H Hrf]. apply andb_true_iff in H as [H Hce].
  apply andb_true_iff in H as [Hal Hpos].
  assert (Htop : (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z)
    by (apply (alloc_top_ge_of_ceiling _ _ Hisp); apply Z.leb_le; exact Hce).
  rewrite Hal, Hpos, Hrf, (proj2 (Z.leb_le _ _) Htop). reflexivity.
Qed.

#[using="Type"] Lemma grant_na_pin_not_errno : forall m a n,
  (0 <= n)%Z -> grant_ok_na_pin m a n = true -> errno_ret_in mmap_errnos a = false.
Proof.
  intros m a n Hn Hg. unfold grant_ok_na_pin in Hg.
  apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Hg Htop]. apply Z.leb_le in Htop.
  apply errno_ret_in_below; [reflexivity|]. alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

Definition mmap_noaccess_args_ok (ms : machine_state) : Prop := ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "(27.(67.(1.(<.&40.)(15.O1.#1.)(59.&40.=)))(27.(1.(<.&40.)(15.O1.#2.)(59.&40.=))(27.(1.(<.&40.)(15.O1.#3.)(59.&40.+22.))(27.(1.(<.&40.)(15.O1.#4.)(59.&40.-1.))(1.(<.&40.)(15.O1.#5.)(59.&40.=))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma mmap_noaccess_check : forall ms x8 model eff,
  bv_unsigned x8 = 222%Z -> mmap_noaccess_args_ok ms ->
  check_syscall (sys_input segs ms x8) eff model
  = let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
    match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if grant_ok_na_pin model r n && listNN_eqb us [(r, Z_to_bv 64 n)]
             then CheckOk (noaccess_model r (Z_to_bv 64 n) model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff Hno (H1 & H2 & H3 & H4 & H5).
  rewrite (mmap_check ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 34)) with true by (vm_compute; reflexivity).
  replace (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with false
    by (vm_compute; reflexivity).
  replace (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true
    by (vm_compute; reflexivity).
  cbn [negb]. cbv beta iota zeta.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  destruct (errno_ret_in mmap_errnos r); [reflexivity|].
  unfold grant_ok_na_pin, noaccess_model, with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
  rewrite <- !andb_assoc. reflexivity.
Qed.

#[using="Type"] Lemma grant_na_not_errno : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Phint,(<.&40.)Pmodel,$=.Pa,(<.&40.)Pn,$?.P,(50.=R1.)P,(1.$53.(65.R5.R4.R3.R2.)$55.)(1.$53.(68.$69.R4.)$6:.)")
(* [comment removed for export] *).
Proof.
  intros hint model a n Hn Hg. unfold grant_ok_na in Hg.
  apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Hg Hce]. apply Z.leb_le in Hce.
  apply errno_ret_in_below; [reflexivity|].
  pose proof alloc_ceiling_val. unfold two_pow_64. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mprotect_model (addr n : word) (m : Model) : Model := ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "(3?.(2.(3.(40.O1.))(4.(40.O1.))(42.(5.(40.O1.))(10.&40.O3.)(43.(10.&40.O3.)(10.&40.O2.)))(6.(40.O1.))(7.(40.O1.))(8.(40.O1.))(9.(40.O1.))(:.(40.O1.)))O1.)")
(* [comment removed for export] *).

#[using="Type"] Lemma mprotect_model_next_eq : forall m addr n, mprotect_model_next m addr n = mprotect_model addr n m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma check_syscall_226 : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pms,$;.Px8,(<.&40.)Peff,$>.Pm,$=.P,(1.$?.(10.&40.R3.)+>2.)(1.$11.(12.(13.Vsegs,R5.R4.)R3.R2.)(6;.(15.R5.#0.)(15.R5.#1.)(15.R5.#2.)R3.R2.))")
(* [comment removed for export] *).
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

#[using="Type"] Lemma mprotect_check : forall ms x8 model eff (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mprotect_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
             then CheckOk (mprotect_model addr n model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; unfold two_pow_64 in Hlen'; lia).
  rewrite (check_syscall_226 ms x8 eff model Hno). unfold check_mprotect.
  rewrite H0, H2, Hu1.
  replace (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false by (vm_compute; reflexivity).
  replace (mprotect_modeled_b (Z_to_bv 64 3)) with true by (vm_compute; reflexivity).
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0, bv_eqb. rewrite Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E1. rewrite (proj2 (Z.leb_gt _ _)) by lia.
  cbv beta iota zeta. fold n. rewrite Hna, Hma. cbn [andb].
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  destruct cs; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  destruct ci; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  reflexivity.
Qed.

#[using="Type"] Lemma ENOMEM_in_mprotect_errnos : In ENOMEM mprotect_errnos.
Proof. left. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixed_noaccess_model (addr n : word) (m : Model) : Model := ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "(6<.(10.&40.O3.)(43.(10.&40.O3.)(10.&40.O2.))(3?.(2.(3.(40.O1.))(4.(40.O1.))(37.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)O3.O2.)(42.(5.(40.O1.))(10.&40.O3.)(43.(10.&40.O3.)(10.&40.O2.))))(6.(40.O1.))(7.(40.O1.))(8.(40.O1.))(9.(40.O1.))(:.(40.O1.)))O1.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fixed_destroyed_model (addr n : word) (m : Model) : Model := ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "(6<.(10.&40.O3.)(43.(10.&40.O3.)(10.&40.O2.))(3?.(2.(3.(40.O1.))(42.(4.(40.O1.))(10.&40.O3.)(43.(10.&40.O3.)(10.&40.O2.)))(42.(5.(40.O1.))(10.&40.O3.)(43.(10.&40.O3.)(10.&40.O2.)))(6.(40.O1.))(7.(40.O1.))(8.(40.O1.))(9.(40.O1.))(:.(40.O1.)))O1.))")
(* [comment removed for export] *).

#[using="Type"] Lemma fixed_noaccess_model_simple : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Paddr,(<.&40.)Pn,(<.&40.)Pm,$=.P,(1.(22.(2>.(<.&40.)(<.&40.)))(3<.R1.)(1;.(2>.(<.&40.)(<.&40.))))P,(1.(22.(<.&40.))(3=.R2.)(1;.(<.&40.)))(1.$=.(6=.R5.R4.R3.)(3?.(2.(3.(40.R3.))(4.(40.R3.))(37.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)R5.R4.)(42.(5.(40.R3.))(10.&40.R5.)(43.(10.&40.R5.)(10.&40.R4.))))(6.(40.R3.))(7.(40.R3.))(8.(40.R3.))(9.(40.R3.))(:.(40.R3.)))R3.))")
(* [comment removed for export] *).
Proof. intros. unfold fixed_noaccess_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.

#[using="Type"] Lemma fixed_destroyed_model_simple : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Paddr,(<.&40.)Pn,(<.&40.)Pm,$=.P,(1.(22.(2>.(<.&40.)(<.&40.)))(3<.R1.)(1;.(2>.(<.&40.)(<.&40.))))P,(1.(22.(<.&40.))(3=.R2.)(1;.(<.&40.)))(1.$=.(6>.R5.R4.R3.)(3?.(2.(3.(40.R3.))(42.(4.(40.R3.))(10.&40.R5.)(43.(10.&40.R5.)(10.&40.R4.)))(42.(5.(40.R3.))(10.&40.R5.)(43.(10.&40.R5.)(10.&40.R4.)))(6.(40.R3.))(7.(40.R3.))(8.(40.R3.))(9.(40.R3.))(:.(40.R3.)))R3.))")
(* [comment removed for export] *).
Proof. intros. unfold fixed_destroyed_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.

Definition mmap_fixed_args_ok (ms : machine_state) : Prop := ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "(27.(67.(1.(<.&40.)(15.O1.#1.)(59.&40.=)))(27.(1.(<.&40.)(15.O1.#2.)(59.&40.=))(27.(1.(<.&40.)(15.O1.#3.)(59.&40.+32.))(27.(1.(<.&40.)(15.O1.#4.)(59.&40.-1.))(1.(<.&40.)(15.O1.#5.)(59.&40.=))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma check_syscall_96 : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pms,$;.Px8,(<.&40.)Peff,$>.Pm,$=.P,(1.$?.(10.&40.R3.)+60.)(1.$11.(12.(13.Vsegs,R5.R4.)R3.R2.)(6?.R3.R2.))")
(* [comment removed for export] *).
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

Definition tid_I : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.

#[using="Type"] Lemma one_tid_ok : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

#[using="Type"] Lemma node_set_tid : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pms,$;.Pmodel,$=.Px8,(<.&40.)P,(1.(29.(<.&40.))(44.R2.)(45.(<.&40.)))P,(1.(22.(2>.(<.&40.)(<.&40.)))(3<.R3.)(1;.(2>.(<.&40.)(<.&40.))))P,(1.(29.(<.&40.))(46.R5.)(47.(<.&40.)R3.))P,(1.$?.(10.&40.R4.)+60.)P,(1.(29.(<.&40.))(70.R6.)(45.(<.&40.)))(1:.Vsegs,(48.R8.R7.)$71.L,$71.(1;.$1<.)Li,$71.(48.(2:.(72.R9.(4;.(<.&40.)Lt,(<.&40.)(27.(4?.=(10.&40.R1.))(4?.(10.&40.R1.)$73.))R1.)))(74.(4;.(<.&40.)Lt,(<.&40.)(27.(4?.=(10.&40.R1.))(4?.(10.&40.R1.)$73.))R1.)R8.)))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Htid.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
     match eff with
     | mkEffectU ret [] [] [] [] [] =>
         if (0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z
         then CheckOk (with_tid ret model) [] else CheckReject
     | _ => CheckReject end).
  { intros eff. rewrite (check_syscall_96 ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
  pose (effs := fun i : tid_I => mkEffectU (proj1_sig i) [] [] [] [] []).
  assert (Enx : forall i : tid_I,
    mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model)).
  { intros [t Ht]. cbn [proj1_sig effs]. rewrite <- (apply_effect_no_write ms t). reflexivity. }
  split.
  - intros i. rewrite Enx. apply (sstep_of_check segs ms model x8); [exact Hh | exact Hsvc | | rewrite with_tid_halted; exact Hh | rewrite with_tid_lazy; exact Hlazy].
    destruct i as [t [Ht1 Ht2]]. subst effs. cbn [proj1_sig]. rewrite Hchk.
    rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
  - assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
              exists i : tid_I, eff = effs i /\ m' = with_tid (proj1_sig i) model /\ ev = []).
    { intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z) eqn:Eb; [|discriminate].
      apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
      injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity. }
    intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans (with_tid_lazy _ model) Hlazy)) in Hmat.
      injection Hmat as <-. exists i. rewrite Enx. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans (with_tid_lazy _ model) Hlazy)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite with_tid_halted in Hh2. congruence.
    + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z); discriminate.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rz_exit_at : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pregs,(28.&5.(<.&40.))Ppc,(<.&40.)Pmem,P,(<.&40.)(29.(<.&8.))Prom,P,(<.&40.)(29.(<.&8.))Pmodel,$=.Pw,(<.&20.)Pcode,(<.&40.)P,(1.(29.(<.&20.))(75.Vsegs,R6.)(47.(<.&20.)R2.))P,(1.$53.(76.R3.)$55.)P,(1.(29.(<.&40.))(44.R5.)(45.(<.&40.)))P,(1.(22.(2>.(<.&40.)(<.&40.)))(3<.R6.)(1;.(2>.(<.&40.)(<.&40.))))P,(52.(1.(<.&40.)(77.R;.(34.&5.+11.$35.))(59.&40.+5>.))(1.(<.&40.)(77.R;.(34.&5.+11.$35.))(59.&40.+5=.)))P,(1.(<.&40.)(77.R<.(34.&5.+:.$35.))R6.)(1=.Vsegs,(48.(31.$32.R=.R<.R;.R:.)R9.)(78.(79.&40.R7.(59.&40.+??.))(7:.R9.)))")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply rz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_exit_at_lit : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pregs,(28.&5.(<.&40.))Ppc,(<.&40.)Pmem,P,(<.&40.)(29.(<.&8.))Prom,P,(<.&40.)(29.(<.&8.))Pmodel,$=.Pw,(<.&20.)Pcode,$?.P,(1.(29.(<.&20.))(75.Vsegs,R6.)(47.(<.&20.)R2.))P,(1.$53.(76.R3.)$55.)P,(1.(29.(<.&40.))(44.R5.)(45.(<.&40.)))P,(1.(22.(2>.(<.&40.)(<.&40.)))(3<.R6.)(1;.(2>.(<.&40.)(<.&40.))))P,(52.(1.(<.&40.)(77.R;.(34.&5.+11.$35.))(59.&40.+5>.))(1.(<.&40.)(77.R;.(34.&5.+11.$35.))(59.&40.+5=.)))P,(1.(<.&40.)(77.R<.(34.&5.+:.$35.))(59.&40.R6.))P,(27.(50.=R7.)(4?.R7.+100.))(1=.Vsegs,(48.(31.$32.R>.R=.R<.R;.)R:.)(78.(59.&40.R8.)(7:.R:.)))")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10 Hc.
  rewrite <- (bv_and_255_small code Hc). eapply rz_exit_at; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma vm_backing_used_simple : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pm,$=.P,(1.(22.(2>.(<.&40.)(<.&40.)))(3<.R1.)(1;.(2>.(<.&40.)(<.&40.))))P,(1.(22.(<.&40.))(3=.R2.)(1;.(<.&40.)))(1.$?.(7;.R3.)(7<.(40.R3.)))")
(* [comment removed for export] *).
Proof.
  intros m Hl Hm. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat Z.mul]. unfold vm_backed_bytes. lia.
Qed.

#[using="Type"] Lemma vm_backed_bytes_no_noaccess : forall h,
  vm_noaccess h = [] -> vm_backed_bytes h = vm_live_bytes h.
Proof. intros h H. unfold vm_backed_bytes, vm_backed_maps. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_grow_ok_aligned_intro : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pm,$=.Pd,$?.Zh,$0.(40.R2.)Zb,(<.&40.)(7.R1.)P,(1.$?.(57.(10.&40.R1.)$58.)=)P,(1.$?.(57.R4.$58.)=)P,(4?.=R5.)P,(4?.=(10.&40.R4.))P,(50.(43.(10.&40.R5.)R7.)$5>.)P,(66.R7.)P,(1.$53.(5?.(60.(2>.(<.&40.)(<.&40.))(3.R8.)(4.R8.))R7.(59.&40.(43.R9.$58.)))$55.)P,(50.(43.(7;.R;.)R:.)(8.R9.))(1.$53.(54.R<.(59.&40.(43.(10.&40.R9.)R;.))(59.&40.(43.(10.&40.R9.)R;.)))$55.)")
(* [comment removed for export] *).
Proof.
  intros m d h b Hbal Hdal Hd Hb0 Hce Hisp Hrf Hlive.
  pose proof alloc_ceiling_val as Hcv. pose proof (u64_range b) as Hbr.
  pose proof (alloc_ceiling_le_alloc_top h Hisp) as Htop.
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
  unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok. fold h. fold b. rewrite Hureq.
  rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) by lia. cbn [andb].
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d))
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z by lia. rewrite Hrf.
  replace (bv_unsigned (Z_to_bv 64 (bv_unsigned b + d) - b)) with d.
  2:{ rewrite bv_sub_unsigned, Hureq. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia. }
  rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_grow_admissible_init : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Preserved,(22.(2>.(<.&40.)(<.&40.)))Pbrk0,(<.&40.)Pmbase,(<.&40.)Psp,(<.&40.)Plim,$?.Pmodel,$=.Pd,$?.P,(50.$7=.(10.&40.R4.))P,(50.(7>.R8.)(10.&40.R7.))P,(1.$?.(57.(10.&40.R8.)$58.)=)P,(1.$?.(57.R4.$58.)=)P,(4?.=R5.)P,(4?.=(10.&40.R;.))P,(50.(43.(10.&40.R<.)R7.)$5>.)P,(50.R8.R:.)P,(1.$0.(40.R:.)(2.R?.(1;.(2>.(<.&40.)(<.&40.)))(1;.(2>.(<.&40.)(<.&40.)))R>.R>.R;.R=.R<.))P,(1.(22.(2>.(<.&40.)(<.&40.)))(3<.R;.)(1;.(2>.(<.&40.)(<.&40.))))P,(1.(22.(<.&40.))(3=.R<.)(1;.(<.&40.)))(1.$53.(54.R=.(59.&40.(43.(10.&40.R11.)R<.))(59.&40.(43.(10.&40.R11.)R<.)))$55.)")
(* [comment removed for export] *).
Proof.
  intros reserved brk0 mbase sp lim model d Hsp Htop Hbal Hdal Hd Hb0 Hce Hlim Hvm Hlz Hmt.
  pose proof (brk_grow_ok_aligned_intro model d) as H. cbv zeta in H. rewrite Hvm in H. cbn in H.
  apply H; try assumption; try lia.  (* [comment removed for export] *)
  - rewrite app_nil_r. apply region_free_above_top. exact Htop.
  - rewrite vm_backing_used_simple by assumption. rewrite Hvm. cbn. lia.
Qed.

End WithSegs.

(* [comment removed for export] *)
Local Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_roundtrip : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma region_free_app : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pl1,(22.(2>.(<.&40.)(<.&40.)))Pl2,(22.(2>.(<.&40.)(<.&40.)))Plo,(<.&40.)Pn,(<.&40.)(1.$53.(5?.(60.(2>.(<.&40.)(<.&40.))R4.R3.)R2.R1.)(5:.(5?.R4.R2.R1.)(5?.R3.R2.R1.)))")
(* [comment removed for export] *).
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
  cbn [region_free app]. rewrite IH, andb_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_In : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pl,(22.(2>.(<.&40.)(<.&40.)))Plo,(<.&40.)Pn,(<.&40.)Pb,(<.&40.)Ps,(<.&40.)P,(1.$53.(5?.R5.R4.R3.)$55.)P,(7?.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)R3.R2.)R6.)(52.(50.(43.(10.&40.R6.)(10.&40.R5.))(10.&40.R4.))(50.(43.(10.&40.R4.)(10.&40.R3.))(10.&40.R6.)))")
(* [comment removed for export] *).
Proof.
  induction l as [|[b' s'] l IH]; intros lo n b s Hrf Hin; [destruct Hin|].
  apply region_free_cons in Hrf as [Hd Hrf].
  destruct Hin as [E | Hin]; [injection E as -> ->; exact Hd | exact (IH _ _ _ _ Hrf Hin)].
Qed.

Lemma region_free_intro : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pl,(22.(2>.(<.&40.)(<.&40.)))Plo,(<.&40.)Pn,(<.&40.)P,Pb,(<.&40.)Ps,(<.&40.)P,(7?.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)R2.R1.)R5.)(52.(50.(43.(10.&40.R5.)(10.&40.R4.))(10.&40.R3.))(50.(43.(10.&40.R3.)(10.&40.R2.))(10.&40.R5.)))(1.$53.(5?.R4.R3.R2.)$55.)")
(* [comment removed for export] *).
Proof.
  induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
  cbn [region_free]. rewrite IH by (intros b' s' Hin; apply H; right; exact Hin).
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
  destruct (H b s (or_introl eq_refl)) as [Hl | Hr]; [right | left]; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
Lemma map_has_head : forall (a n : word) l, map_has ((a, n) :: l) a n = true.
Proof. intros. unfold map_has. cbn [existsb fst snd]. rewrite !bv_eqb_refl. reflexivity. Qed.

Lemma map_has_cons : forall p (a n : word) l, map_has l a n = true -> map_has (p :: l) a n = true.
Proof. intros p a n l H. unfold map_has in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

Lemma map_contains_head : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pa,(<.&40.)Psz,(<.&40.)Plo,(<.&40.)Pn,(<.&40.)Pl,(22.(2>.(<.&40.)(<.&40.)))P,(50.(10.&40.R5.)(10.&40.R3.))P,(50.(43.(10.&40.R4.)(10.&40.R3.))(43.(10.&40.R6.)(10.&40.R5.)))(1.$53.(80.(37.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)R7.R6.)R3.)R5.R4.)$55.)")
(* [comment removed for export] *).
Proof.
  intros a sz lo n l H1 H2. unfold map_contains. cbn [existsb fst snd].
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.

Lemma map_contains_cons : forall p (lo n : word) l,
  map_contains l lo n = true -> map_contains (p :: l) lo n = true.
Proof. intros p lo n l H. unfold map_contains in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

(* [comment removed for export] *)
Lemma map_remove_nil : forall (a : word), map_remove [] a = [].
Proof. reflexivity. Qed.

Lemma map_remove_head : forall (a n : word) l, map_remove ((a, n) :: l) a = map_remove l a.
Proof. intros. unfold map_remove. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma map_remove_skip : forall (b s a : word) l,
  b <> a -> map_remove ((b, s) :: l) a = (b, s) :: map_remove l a.
Proof. intros b s a l H. unfold map_remove. cbn [List.filter fst]. rewrite (bv_eqb_neq _ _ H). reflexivity. Qed.

Lemma map_remove_notin : forall l (a : word),
  (forall b s, In (b, s) l -> b <> a) -> map_remove l a = l.
Proof.
  induction l as [|[b s] l IH]; intros a H; [reflexivity|].
  rewrite map_remove_skip by (apply (H b s); left; reflexivity).
  rewrite IH by (intros b' s' Hin; apply (H b' s'); right; exact Hin). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma disjoint_base_ne : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Plo,(<.&40.)Pn,(<.&40.)Pb,(<.&40.)Ps,(<.&40.)P,(4?.=(10.&40.R3.))P,(4?.=(10.&40.R2.))P,(52.(50.(43.(10.&40.R6.)(10.&40.R5.))(10.&40.R4.))(50.(43.(10.&40.R4.)(10.&40.R3.))(10.&40.R6.)))(67.(1.(<.&40.)R5.R7.))")
(* [comment removed for export] *).
Proof. intros lo n b s Hn Hs Hd ->. lia. Qed.

(* [comment removed for export] *)
Lemma live_bytes_cons : forall (a n : word) l, live_bytes ((a, n) :: l) = bv_unsigned n + live_bytes l.
Proof. reflexivity. Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; [cbn; lia|]. cbn [live_bytes]. pose proof (u64_range n). lia. Qed.

Lemma live_bytes_map_remove_le : forall l (a : word), live_bytes (map_remove l a) <= live_bytes l.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [live_bytes];
    fold (map_remove l a); pose proof (IH a); pose proof (u64_range s); lia.
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_nil : forall (lo hi : Z), maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

Lemma maps_subtract_cons : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pa,(<.&40.)Psz,(<.&40.)Plo,$?.Phi,$?.Pl,(22.(2>.(<.&40.)(<.&40.)))(1.(22.(2>.(<.&40.)(<.&40.)))(42.(37.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)R5.R4.)R1.)R3.R2.)(60.(2>.(<.&40.)(<.&40.))(81.R5.R4.R3.R2.)(42.R1.R3.R2.)))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

Lemma maps_subtract_app : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pl1,(22.(2>.(<.&40.)(<.&40.)))Pl2,(22.(2>.(<.&40.)(<.&40.)))Plo,$?.Phi,$?.(1.(22.(2>.(<.&40.)(<.&40.)))(42.(60.(2>.(<.&40.)(<.&40.))R4.R3.)R2.R1.)(60.(2>.(<.&40.)(<.&40.))(42.R4.R2.R1.)(42.R3.R2.R1.)))")
(* [comment removed for export] *).
Proof.
  induction l1 as [|[a sz] l1 IH]; intros l2 lo hi; [reflexivity|].
  cbn [maps_subtract app]. rewrite IH, app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_covered : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pa,(<.&40.)Psz,(<.&40.)Plo,$?.Phi,$?.P,(50.R2.(10.&40.R4.))P,(50.(43.(10.&40.R5.)(10.&40.R4.))R2.)(1.(22.(2>.(<.&40.)(<.&40.)))(81.R6.R5.R4.R3.)(1;.(2>.(<.&40.)(<.&40.))))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi H1 H2. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_self : forall (a sz : word),
  iv_subtract a sz (bv_unsigned a) (bv_unsigned a + bv_unsigned sz) = [].
Proof. intros a sz. apply iv_subtract_covered; lia. Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pa,(<.&40.)Psz,(<.&40.)Plo,$?.Phi,$?.P,(4?.=(10.&40.R3.))P,(50.R3.R2.)P,(52.(50.R3.(10.&40.R6.))(50.(43.(10.&40.R6.)(10.&40.R5.))R4.))(1.(22.(2>.(<.&40.)(<.&40.)))(81.R7.R6.R5.R4.)(37.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)R7.R6.)(1;.(2>.(<.&40.)(<.&40.)))))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi Hsz Hlh Hd. unfold iv_subtract.
  destruct Hd as [Hd | Hd].
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
    rewrite Z.max_l by lia. rewrite u64_roundtrip.
    replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite u64_roundtrip. reflexivity.
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [app].
    rewrite Z.min_l by lia. rewrite u64_roundtrip. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_suffix : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pa,(<.&40.)Psz,(<.&40.)Plo,$?.Phi,$?.P,(4?.(10.&40.R4.)R2.)P,(50.R3.(43.(10.&40.R5.)(10.&40.R4.)))P,(50.(43.(10.&40.R6.)(10.&40.R5.))R3.)(1.(22.(2>.(<.&40.)(<.&40.)))(81.R7.R6.R5.R4.)(37.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)R7.(59.&40.(82.R5.(10.&40.R7.))))(1;.(2>.(<.&40.)(<.&40.)))))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_ge _ _) H3). cbn [app].
  rewrite Z.min_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_prefix : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pa,(<.&40.)Psz,(<.&40.)Plo,$?.Phi,$?.P,(50.R2.(10.&40.R4.))P,(50.(10.&40.R5.)R2.)P,(4?.R3.(43.(10.&40.R6.)(10.&40.R5.)))(1.(22.(2>.(<.&40.)(<.&40.)))(81.R7.R6.R5.R4.)(37.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)(59.&40.R4.)(59.&40.(82.(43.(10.&40.R7.)(10.&40.R6.))R4.)))(1;.(2>.(<.&40.)(<.&40.)))))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H3). cbn [app].
  rewrite Z.max_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_sizes : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pa,(<.&40.)Psz,(<.&40.)Plo,$?.Phi,$?.PN,$?.P,(50.=R3.)P,(4?.R3.(56.+2.+40.))P,(50.(10.&40.R6.)R3.)(83.(2>.(<.&40.)(<.&40.))Lp,(2>.(<.&40.)(<.&40.))(50.(10.&40.(84.(<.&40.)(<.&40.)R1.))R5.)(81.R8.R7.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi N Hlo Hhi Hs. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract. apply Forall_app. split.
  - destruct (bv_unsigned a <? lo) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64_lit by lia. lia.
Qed.

Lemma maps_subtract_sizes : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pl,(22.(2>.(<.&40.)(<.&40.)))Plo,$?.Phi,$?.PN,$?.P,(50.=R3.)P,(4?.R3.(56.+2.+40.))P,(83.(2>.(<.&40.)(<.&40.))Lp,(2>.(<.&40.)(<.&40.))(50.(10.&40.(84.(<.&40.)(<.&40.)R1.))R4.)R6.)(83.(2>.(<.&40.)(<.&40.))Lp,(2>.(<.&40.)(<.&40.))(50.(10.&40.(84.(<.&40.)(<.&40.)R1.))R5.)(42.R7.R6.R5.))")
(* [comment removed for export] *).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi N Hlo Hhi H; [constructor|].
  inversion H as [|p l' Hp Hl]; subst. cbn [maps_subtract]. apply Forall_app. split.
  - apply iv_subtract_sizes; assumption.
  - apply IH; assumption.
Qed.

Lemma map_remove_sizes : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pl,(22.(2>.(<.&40.)(<.&40.)))Pa,(<.&40.)PN,$?.P,(83.(2>.(<.&40.)(<.&40.))Lp,(2>.(<.&40.)(<.&40.))(50.(10.&40.(84.(<.&40.)(<.&40.)R1.))R2.)R3.)(83.(2>.(<.&40.)(<.&40.))Lp,(2>.(<.&40.)(<.&40.))(50.(10.&40.(84.(<.&40.)(<.&40.)R1.))R3.)(41.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros l a N H. unfold map_remove. apply List.incl_Forall with (l1 := l); [|exact H].
  apply List.incl_filter.
Qed.

Lemma maps_subtract_length : forall l (lo hi : Z),
  (length (maps_subtract l lo hi) <= 2 * length l)%nat.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi; [cbn; lia|].
  cbn [maps_subtract]. rewrite length_app. cbn [length].
  assert (length (iv_subtract a sz lo hi) <= 2)%nat.
  { unfold iv_subtract. rewrite length_app.
    destruct (_ <? _); destruct (_ <? _); cbn; lia. }
  specialize (IH lo hi). lia.
Qed.

Lemma map_remove_length : forall l (a : word), (length (map_remove l a) <= length l)%nat.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [length];
    fold (map_remove l a); specialize (IH a); lia.
Qed.

(* [comment removed for export] *)
Lemma live_bytes_iv_subtract_le : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pa,(<.&40.)Psz,(<.&40.)Plo,$?.Phi,$?.P,(50.R2.R1.)(50.(85.(81.R5.R4.R3.R2.))(10.&40.R4.))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi Hlh. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    cbn [app live_bytes];
    first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
    rewrite ?u64_lit by lia; lia.
Qed.

Lemma live_bytes_maps_subtract_le : forall l (lo hi : Z),
  lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma maps_subtract_all_nil : forall maps, maps_subtract_all maps [] = maps.
Proof. reflexivity. Qed.

Lemma maps_subtract_all_cons : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pmaps,(22.(2>.(<.&40.)(<.&40.)))Pa,(<.&40.)Pn,(<.&40.)Pcuts,(22.(2>.(<.&40.)(<.&40.)))(1.(22.(2>.(<.&40.)(<.&40.)))(86.R4.(37.(2>.(<.&40.)(<.&40.))(38.(<.&40.)(<.&40.)R3.R2.)R1.))(86.(42.R4.(10.&40.R3.)(43.(10.&40.R3.)(10.&40.R2.)))R1.))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

Lemma live_bytes_maps_subtract_all_le : forall cuts maps,
  live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; [cbn; lia|].
  rewrite maps_subtract_all_cons. etransitivity; [apply IH|].
  apply live_bytes_maps_subtract_le. pose proof (u64_range n). lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backed_bytes_le_live : forall h, vm_backed_bytes h <= vm_live_bytes h.
Proof. intros h. unfold vm_backed_bytes, vm_backed_maps, vm_live_bytes. apply live_bytes_maps_subtract_all_le. Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le_live : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pm,$=.P,(1.(22.(2>.(<.&40.)(<.&40.)))(3<.R1.)(1;.(2>.(<.&40.)(<.&40.))))P,(1.(22.(<.&40.))(3=.R2.)(1;.(<.&40.)))(50.(7;.R3.)(87.(40.R3.)))")
(* [comment removed for export] *).
Proof.
  intros m Hl Hm. rewrite (vm_backing_used_simple m Hl Hm). apply vm_backed_bytes_le_live.
Qed.

Lemma grant_budget_intro : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pm,$=.Pn,$?.P,(1.(22.(2>.(<.&40.)(<.&40.)))(3<.R2.)(1;.(2>.(<.&40.)(<.&40.))))P,(1.(22.(<.&40.))(3=.R3.)(1;.(<.&40.)))P,(50.(43.(87.(40.R4.))R3.)(8.(40.R4.)))(50.(43.(7;.R5.)R4.)(8.(40.R5.)))")
(* [comment removed for export] *).
Proof. intros m n Hl Hm H. pose proof (vm_backing_used_le_live m Hl Hm). lia. Qed.

(* [comment removed for export] *)
Lemma mprotect_budget_ok_intro : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pm,$=.Paddr,(<.&40.)Pn,(<.&40.)P,(1.(22.(2>.(<.&40.)(<.&40.)))(3<.R3.)(1;.(2>.(<.&40.)(<.&40.))))P,(1.(22.(<.&40.))(3=.R4.)(1;.(<.&40.)))P,(50.(87.(40.R5.))(8.(40.R5.)))(1.$53.(88.R6.R5.R4.)$55.)")
(* [comment removed for export] *).
Proof.
  intros m addr n Hl Hm Hlive. unfold mprotect_budget_ok, vm_backing_within_limit.
  rewrite mprotect_model_next_eq. apply Z.leb_le.
  etransitivity; [apply vm_backing_used_le_live; [unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hl | exact Hm]|].
  unfold mprotect_model. rewrite with_vmmaps_vm. cbn [vm_live_bytes vm_maps vm_limit]. exact Hlive.
Qed.

(* [comment removed for export] *)
Lemma file_read_length_eq : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pdata,(22.(<.&8.))Poff,(<.&40.)Pcount,(<.&40.)(1.$30.(89.(<.&8.)(8:.R3.R2.R1.))(8;.(8<.R1.)(8=.(89.(<.&8.)R3.)(8<.R2.))))")
(* [comment removed for export] *).
Proof. intros. rewrite length_file_read. reflexivity. Qed.

Lemma file_read_length_le : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pdata,(22.(<.&8.))Poff,(<.&40.)Pcount,(<.&40.)(27.(8>.(89.(<.&8.)(8:.R3.R2.R1.))(8<.R1.))(8>.(89.(<.&8.)(8:.R3.R2.R1.))(8=.(89.(<.&8.)R3.)(8<.R2.))))")
(* [comment removed for export] *).
Proof. intros data off count. rewrite file_read_length_eq. split; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cand (N : Z) (j : nat) : Z := bottomup_floor + Z.of_nat j * (2 * N).

Definition zconflict (a n : Z) (p : word * word) : Prop :=
  a < bv_unsigned (fst p) + bv_unsigned (snd p) /\ bv_unsigned (fst p) < a + n.

Definition zconflictb (a n : Z) (p : word * word) : bool :=
  (a <? bv_unsigned (fst p) + bv_unsigned (snd p)) && (bv_unsigned (fst p) <? a + n).

Lemma zconflictb_spec : forall a n p, zconflictb a n p = true <-> zconflict a n p.
Proof.
  intros a n p. unfold zconflictb, zconflict. rewrite andb_true_iff, !Z.ltb_lt. tauto.
Qed.

Lemma cand_spacing : forall N j k, 0 <= N -> (j < k)%nat -> cand N j + 2 * N <= cand N k.
Proof. intros N j k HN H. unfold cand. rewrite bottomup_floor_val. nia. Qed.

(* [comment removed for export] *)
Lemma conflict_unique : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "PN,$?.Pn,$?.Pp,(2>.(<.&40.)(<.&40.))Pj,$30.Pk,$30.P,(27.(50.=R4.)(50.R4.R5.))P,(50.(10.&40.(84.(<.&40.)(<.&40.)R4.))R6.)P,(8?.(90.R7.R4.)R6.R5.)P,(8?.(90.R8.R4.)R7.R6.)(1.$30.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros N n p j k Hn Hs [A1 A2] [B1 B2].
  destruct (Nat.lt_trichotomy j k) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - pose proof (cand_spacing N j k ltac:(lia) Hlt). lia.
  - pose proof (cand_spacing N k j ltac:(lia) Hgt). lia.
Qed.

(* [comment removed for export] *)
Lemma filter_keep_all_but_one : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "PP,P,$30.$53.Pjs,(22.$30.)P,(91.$30.R1.)P,Pj,$30.Pk,$30.P,(7?.$30.R2.R4.)P,(7?.$30.R2.R5.)P,(1.$53.A1.R7.R4.$55.)P,(1.$53.A1.R8.R4.$55.)(1.$30.R6.R5.)(8>.(89.$30.R3.)(92.(89.$30.(93.$30.Lj,$30.(94.A1.R5.R1.)R3.))))")
(* [comment removed for export] *).
Proof.
  intros P js Hnd Huniq. induction js as [|j js IH]; [cbn; lia|].
  inversion Hnd as [|x l Hnotin Hnd']; subst.
  cbn [List.filter List.length]. destruct (P j) eqn:Pj; cbn [negb].
  - (* [comment removed for export] *)
    assert (Hall : forall k, In k js -> P k = false).
    { intros k Hk. destruct (P k) eqn:Pk; [|reflexivity].
      exfalso. assert (j = k) by (apply Huniq; [left; reflexivity | right; exact Hk | exact Pj | exact Pk]).
      subst k. exact (Hnotin Hk). }
    assert (Hid : List.filter (fun j0 => negb (P j0)) js = js).
    { clear -Hall. induction js as [|k js IH]; [reflexivity|].
      cbn [List.filter]. rewrite (Hall k (or_introl eq_refl)). cbn [negb]. f_equal. apply IH.
      intros k' Hk'. apply Hall. right. exact Hk'. }
    rewrite Hid. lia.
  - cbn [List.length].
    assert (IH' : (length js <= S (length (List.filter (fun j0 : nat => negb (P j0)) js)))%nat).
    { apply IH; [exact Hnd'|]. intros a b Ha Hb Pa Pb. apply Huniq; [right | right | |]; assumption. }
    lia.
Qed.

Lemma pick_candidate : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "PN,$?.Pn,$?.Pl,(22.(2>.(<.&40.)(<.&40.)))Pjs,(22.$30.)P,(27.(50.=R3.)(50.R3.R4.))P,(83.(2>.(<.&40.)(<.&40.))Lp,(2>.(<.&40.)(<.&40.))(50.(10.&40.(84.(<.&40.)(<.&40.)R1.))R6.)R3.)P,(91.$30.R3.)P,(95.(89.(2>.(<.&40.)(<.&40.))R5.)(89.$30.R4.))(26.$30.Lj,$30.(27.(7?.$30.R1.R6.)Pp,(2>.(<.&40.)(<.&40.))P,(7?.(2>.(<.&40.)(<.&40.))R1.R8.)(67.(8?.(90.R;.R3.)R:.R2.))))")
(* [comment removed for export] *).
Proof.
  intros N n l. induction l as [|p l IH]; intros js Hn Hsz Hnd Hlen.
  - destruct js as [|j js]; [cbn in Hlen; lia|]. exists j. split; [left; reflexivity | intros q []].
  - inversion Hsz as [|p' l' Hp Hl]; subst.
    set (js' := List.filter (fun j => negb (zconflictb (cand N j) n p)) js).
    assert (Hnd' : List.NoDup js') by (apply List.NoDup_filter; exact Hnd).
    assert (Hlen' : (length js <= S (length js'))%nat).
    { apply filter_keep_all_but_one; [exact Hnd|].
      intros j k _ _ Pj Pk. apply zconflictb_spec in Pj. apply zconflictb_spec in Pk.
      eapply (conflict_unique N n p); eassumption. }
    destruct (IH js' Hn Hl Hnd' ltac:(cbn in Hlen; lia)) as (j & Hj & Hfree).
    exists j. unfold js' in Hj. apply filter_In in Hj as [Hj Hnp]. split; [exact Hj|].
    intros q [<- | Hq].
    + intros Hc. apply zconflictb_spec in Hc. rewrite Hc in Hnp. discriminate.
    + apply Hfree. exact Hq.
Qed.

Lemma region_free_of_noconflict : ltac2:(CDefT.buildp (gd_tbl_RefNodes ()) "Pl,(22.(2>.(<.&40.)(<.&40.)))Pa,$?.Pn,$?.P,(50.=R2.)P,(50.=R2.)P,(4?.(43.R4.R3.)(56.+2.+40.))P,Pp,(2>.(<.&40.)(<.&40.))P,(7?.(2>.(<.&40.)(<.&40.))R1.R7.)(67.(8?.R7.R6.R2.))(1.$53.(5?.R7.(59.&40.R6.)(59.&40.R5.))$55.)")
(* [comment removed for export] *).
Proof.
  induction l as [|[b s] l IH]; intros a n Ha Hn Hnw Hno; [reflexivity|].
  cbn [region_free]. rewrite IH; [| lia | lia | lia | intros p Hp; apply Hno; right; exact Hp].
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap.
  rewrite !u64_lit by lia.
  specialize (Hno (b, s) (or_introl eq_refl)). unfold zconflict in Hno. cbn [fst snd] in Hno.
  apply andb_false_iff. destruct (Z_lt_le_dec a (bv_unsigned b + bv_unsigned s)).
  - right. apply Z.ltb_ge. lia.
  - left. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
