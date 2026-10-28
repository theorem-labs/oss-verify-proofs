(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt AStep HeapIface HeapRz RegsExt Shape ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_layout U_exit_base.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb ShapeLaws StoreOk SymExec2 SymExec2Sound SymDriveX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec TopContract.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import MemcpyLib Hoare CatExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_img U_startup U_main_entry U_main_open U_main_cut U_cutkit U_tailkit U_readcall U_fwrite_err U_printf1 U_printfN U_exit_main U_exitkit U_memcpy_base U_memcpy.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.
Set Printing Width 200.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_main_file () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "drv_mem"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.bool"; "Stdlib.Lists.List.forallb"; "Stdlib.ZArith.BinInt.Z.leb"; "Stdlib.ZArith.BinInt.Z.of_N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.U.U_layout.U_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "Corelib.Init.Datatypes.false"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.Fs.file_read"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "RocqVerifyHarness.AgentSubmission.U.U_main_cut.cut_mem"; "RocqVerifyHarness.AgentSubmission.U.U_main_open.model1g"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "stdpp.bitvector.definitions.bv_unsigned"; "Driver.dinv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.BB.StoreOk.mem_grows"; "RocqVerifyHarness.AgentSubmission.U.U_tailkit.tail_mem"; "RocqVerifyHarness.AgentSubmission.U.U_fwrite_err.fw_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_eq"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_alt2"; "Driver.File.OOM"; "Driver.File.LSHAPE"; "Stdlib.ZArith.BinInt.Z.mul"; "LinuxProcessSemantics.LinuxProcessSem.State.FdFile"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_insert"; "Driver.File.FDS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.U.U_main_entry.p1"; "Corelib.Init.Datatypes.nat"; "Driver.File.LINV"; "Corelib.Init.Datatypes.S"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "Driver.File.LREGS"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Driver.File.BODY"; "RocqVerifyHarness.AgentSubmission.U.U_main_cut.file_kont_concrete"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_opened"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.dot_path"; "LinuxProcessSemantics.LinuxProcessSem.State.FdDir"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_opened_dir"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_steps : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Pmo,$0.Pms,$1.PT,$2.P,(3.$4.R3.Lc,$5.(6.$4.R1.R2.)R2.)(6.$4.(7.R3.R4.)R2.)")
(* [comment removed for export] *).
Proof. intros mo ms T H. eapply aevt_realizes; [exact H|]. intros c' Hc'. exact Hc'. Qed.

Lemma MOK_with_fds : forall fds mo, MOK mo -> MOK (with_fds fds mo).
Proof. intros fds mo [A B]. split; [exact A | exact B]. Qed.

(* [comment removed for export] *)
Ltac post_acall2 segs m :=
  let ms' := fresh "ms'" in let mo' := fresh "mo'" in let PO := fresh "POST" in
  intros ms' mo' PO;
  destruct_exs PO;
  let E := fresh "E" in
  destruct PO as [E PO];
  injection E; clear E; let E1 := fresh "E" in let E2 := fresh "E" in intros E1 E2; subst ms'; subst mo';
  try destruct_ands PO;
  try (lazymatch goal with
  | |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Tactic Notation "acall2" uconstr(SPEC) :=
  lazymatch goal with
  | |- aevtM ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply aevtM_cut; [ eapply SPEC | post_acall2 segs m ]
  end.

(* [comment removed for export] *)
Ltac ifc b :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then _ else _) _ _ _ _) =>
      let H := fresh "C" in
      assert (H : c = b) by (unfold_cond; rewrite ?bv_lts_zero_r, ?bv_lts_zero_l; rewrite ?u_small by lia; fold_lit_ux; solve_cond_rec);
      rewrite H; clear H
  end.

(* [comment removed for export] *)
Ltac norm_getr :=
  repeat match goal with
  | |- context [getr (TNode ?a ?b ?c) ?r] =>
      let p := eval vm_compute in (bv_key r) in
      let v := eval cbn [tget] in (match tget p (TNode a b c) with Some v => v | None => w0 end) in
      change (getr (TNode a b c) r) with v
  end.

(* [comment removed for export] *)
Record drv_mem (M : mem) : Prop := DRV_MEM {
  dm_files : forall a : Z, 0x4cd30 <= a < 0x4cf20 -> M (wa a) = None;   (* [comment removed for export] *)
  dm_comp  : forall a : Z, 0x4cf68 <= a < 0x4cf69 -> M (wa a) = None;   (* [comment removed for export] *)
  dm_lock  : forall a : Z, 0x7d328 <= a < 0x7d32c -> M (wa a) = None;   (* [comment removed for export] *)
  dm_ofl   : forall a : Z, 0x7d770 <= a < 0x7d788 -> M (wa a) = None;   (* [comment removed for export] *)
  dm_ecp   : forall a : Z, 0x5cf90 <= a < 0x5cff8 -> M (wa a) = None;   (* [comment removed for export] *)
  dm_atx   : forall a : Z, 0x7d108 <= a < 0x7d328 -> M (wa a) = None;   (* [comment removed for export] *)
  dm_flags : forall a : Z, 0x5cf70 <= a < 0x5cf78 -> M (wa a) = None    (* [comment removed for export] *)
}.

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L29566453808.12L36445497104.12L59338911088.12L7470082832.12 00000600<00B00HS1a2HaS1a2HaS1a2HaS1a2Ha". (* [comment removed for export] *)
Lemma drv_mem_agree : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "PM,P,(8.&40.)(9.(8.&8.))PM',Px,(8.&40.)(9.(8.&8.))P,(:.R2.)P,Pa,$;.P,(<.(=.+4<=30.R1.)(>.R1.+7=788.))P,(?.(<.(=.+5=024.R2.)(>.R2.+5=028.)))P,(?.(<.(=.+7=330.R3.)(>.R3.+7=76<.)))P,(?.(<.(=.+4<?69.R4.)(>.R4.+5<?69.)))(10.(9.(8.&8.))A1.R7.(11.R5.)A1.R8.(11.R5.))(:.R3.)")
(* [comment removed for export] *).
Proof.
  intros M M' [F C L O E X G] AG. split; intros a Ha; rewrite AG by lia; auto.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L56765667309.2L59309037779.6L59309070547.4L59309070547.6L59309070672.6L59315336847.4L59315369869.400000600>00F00O00W00_00`S1a2HaS1a1n2n0S1a2Ha1nS1a2Ha2n0S1a1n2n0S1a2Ha1nF". (* [comment removed for export] *)
Lemma ro_addr_text : forall a : Z, 0x10000 <= a < 0x48000 -> ro_addr usegs (wa a) = true.
Proof.
  intros a Ha. unfold ro_addr, wa. rewrite (u_small a) by lia.
  unfold usegs, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments. cbn [find_segment].
  let b0 := eval vm_compute in (Z.of_N (seg_base Ubsan.Ubsan_segment_000)) in
  let s0 := eval vm_compute in (Z.of_N (seg_size Ubsan.Ubsan_segment_000)) in
  let b1 := eval vm_compute in (Z.of_N (seg_base Ubsan.Ubsan_segment_001)) in
  let s1 := eval vm_compute in (Z.of_N (seg_size Ubsan.Ubsan_segment_001)) in
  let w0 := eval vm_compute in (seg_writable Ubsan.Ubsan_segment_000) in
  let w1 := eval vm_compute in (seg_writable Ubsan.Ubsan_segment_001) in
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_000)) with b0 by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_000)) with s0 by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_001)) with b1 by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_001)) with s1 by (vm_compute; reflexivity);
  replace (seg_writable Ubsan.Ubsan_segment_000) with w0 by (vm_compute; reflexivity);
  replace (seg_writable Ubsan.Ubsan_segment_001) with w1 by (vm_compute; reflexivity);
  destruct (Z.leb_spec0 b0 a); destruct (Z.leb_spec0 (a + 1) (b0 + s0)); cbn [andb negb]; try reflexivity; try (exfalso; lia);
  destruct (Z.leb_spec0 b1 a); destruct (Z.leb_spec0 (a + 1) (b1 + s1)); cbn [andb negb]; try reflexivity; exfalso; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L26788021726.12L26790095361.12L26790095746.12L3177102371.12 00000100200K00]FFS3seg4rest1z1n2LO2H12Hz1lS3seg1z2LO2H12Hz1l". (* [comment removed for export] *)
Lemma find_segment_below : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Psegs,(12.$13.)Pz,$;.Pn,$;.PLO,$;.P,(10.$14.(15.$13.Lseg,$13.(16.R2.(17.(18.R1.)))R4.)$19.)P,(>.R4.R2.)P,(>.=R4.)(10.(9.$13.)(1:.R7.R6.R5.)(1;.$13.))")
(* [comment removed for export] *).
Proof.
  induction segs as [|seg rest IH]; intros z n LO Hb Hz Hn; [reflexivity|].
  cbn [forallb] in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1.
  cbn [find_segment].
  destruct (Z.leb_spec0 (Z.of_N (seg_base seg)) z);
    destruct (Z.leb_spec0 (z + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg))); cbn [andb]; try lia;
    apply (IH z n LO H2 Hz Hn).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L56765667309.2L62700000556.2L6755913069.2 00000600<00=S1a2HaS1a2HaS". (* [comment removed for export] *)
Lemma ro_addr_low : forall a : Z, 0 <= a < 0x10000 -> ro_addr usegs (wa a) = false.
Proof.
  intros a Ha. unfold ro_addr, wa. rewrite (u_small a) by lia.
  rewrite (find_segment_below usegs a 1 0x10000); [reflexivity | vm_compute; reflexivity | lia | lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L16083901835.7000006S1a2Ha". (* [comment removed for export] *)
Lemma mem_inv_text_none : forall m (a : Z), mem_inv usegs m -> 0x10000 <= a < 0x48000 -> m (wa a) = None.
Proof.
  intros m a MI Ha. destruct (m (wa a)) as [b|] eqn:E; [|reflexivity].
  exfalso. pose proof (MI _ _ E) as X. rewrite ro_addr_text in X by lia. discriminate.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L16085733908.12L56765662601.1200000600<S1a2HaS1a2Ha". (* [comment removed for export] *)
Lemma statics_ok_pres : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Psp0,(8.&40.)PLB,(12.$1<.)PSP,$;.Pm,P,(8.&40.)(9.(8.&8.))Pm',P,(8.&40.)(9.(8.&8.))P,(1=.$4.(1>.R5.)R2.)P,(1?.$4.(1>.R6.)R5.R4.R3.R2.)(1=.$4.(1>.R7.)R3.)")
(* [comment removed for export] *).
Proof.
  (intros sp0 LB SP m m' dd_H; ddestruct dd_H as (L1 & L2 & ST); intros HP). split; [exact L1|]. split; [exact L2|]. intros a Ha HE.
  cbn [hl_data_lo hl_data_hi hl_written U_layout] in *.
  rewrite (proj1 (HP a ltac:(lia) ltac:(right; left; cbn [hl_data_lo hl_data_hi hl_static U_layout]; split; [lia|];
                                         intros X; apply HE; apply U_static_written; exact X))).
  apply ST; assumption.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L32162225246.12L56765548429.1300000<00BS1a2Ha2N12N2S1a2Ha". (* [comment removed for export] *)
Lemma drv_mem_pres : forall sp0 LB SP m m',
  drv_mem m -> heap_pres usegs (U_layout sp0) LB SP m m' -> drv_mem m'.
Proof.
  intros sp0 LB SP m m' DM HP. eapply drv_mem_agree; [exact DM|].
  intros a Ha N1 N2 N3.
  assert (CA : client_addr (U_layout sp0) LB SP a).
  { right; left. cbn [hl_data_lo hl_data_hi hl_static U_layout]. unfold U_static. lia. }
  exact (proj1 (HP a ltac:(lia) CA)).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L23630112039.13L27045534584.1300000C00HS2SP3top3Hle1x2Hx1HS1x1H". (* [comment removed for export] *)
Lemma munch_above_pres : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Psp0,(8.&40.)PLB,(12.$1<.)PSP,$;.Ptop,$;.Pm0,P,(8.&40.)(9.(8.&8.))Pm,P,(8.&40.)(9.(8.&8.))Pm',P,(8.&40.)(9.(8.&8.))P,(20.(21.(22.$;.$;.)(23.$;.$;.=R4.)(24.(22.$;.$;.)))R3.R2.)P,(1?.$4.(1>.R8.)R7.R6.R3.R2.)P,(=.R7.R6.)(20.(21.(22.$;.$;.)(23.$;.$;.=R7.)(24.(22.$;.$;.)))R6.R4.)")
(* [comment removed for export] *).
Proof.
  intros sp0 LB SP top m0 m m' MU HP Hle x Hx. cbn [outside] in Hx. pose proof (u64_range x).
  rewrite <- (MU x) by (cbn [outside]; tauto).
  rewrite <- (Z_to_bv_bv_unsigned x). apply (proj1 (HP (bv_unsigned x) ltac:(lia) ltac:(left; lia))).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma mo_frame_fds : forall mo mo', mo_frame mo mo' -> m_fds mo' = m_fds mo.
Proof. intros mo mo' (H & _). unfold m_fds. rewrite H. reflexivity. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L10621336554.8L29432812610.6L3826542350.8 L52365085825.6L56765667309.800000<00D00T00\010S2lo2hi1a2HaS2lo3HloS2lo2hi3Hlo1a2HaS2hi3HhiS2lo2hi3Hlo3Hhi1a2Ha". (* [comment removed for export] *)
Lemma stk_of_wview : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Pm,P,(8.&40.)(9.(8.&8.))Plo,$;.Phi,$;.P,(=.+7>000.R2.)P,(=.R2.(25.+2.+40.))P,Pa,$;.P,(<.(=.R5.R1.)(>.R1.R4.))(?.(10.(9.(8.&8.))(26.$4.R7.(11.R2.))(1;.(8.&8.))))(27.$4.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros m lo hi Hlo Hhi W. split; [lia|]. split; [lia|]. intros a Ha. split; [apply W; lia|].
  pose proof (wview_high_some m (wa a) ltac:(unfold wa; rewrite u_small by lia; lia) (W a Ha)) as S.
  unfold mrd. destruct (m (wa a)) as [b|]; [exists b; reflexivity | exfalso; apply S; reflexivity].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L27051824992.12L32022970208.12000005006S1x1HF". (* [comment removed for export] *)
Lemma mem_inv_agree : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Pm,P,(8.&40.)(9.(8.&8.))Pm',Px,(8.&40.)(9.(8.&8.))PP,P,$;.SpP,(28.$4.R3.)P,Pa,$;.P,(<.(=.=R1.)(>.R1.(25.+2.+40.)))P,(?.A1.R4.R2.)(10.(9.(8.&8.))A1.R6.(11.R3.)A1.R7.(11.R3.))P,Pa,$;.P,A1.R4.R1.(10.$14.(29.$4.(11.R2.))$2:.)(28.$4.R5.)")
(* [comment removed for export] *).
Proof.
  intros m m' P MI AG RO x b Hx. pose proof (u64_range x).
  rewrite <- (Z_to_bv_bv_unsigned x) in Hx |- *. change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)) in Hx |- *.
  destruct (ro_addr usegs (wa (bv_unsigned x))) eqn:ERO; [| reflexivity]. exfalso.
  assert (HP : ~ P (bv_unsigned x)) by (intros HP; rewrite (RO _ HP) in ERO; discriminate).
  rewrite AG in Hx by (try lia; exact HP). rewrite (MI _ _ Hx) in ERO. discriminate.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zbv_add : forall a b : Z, (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma firstn_plus_skipn {A} : forall (a b : nat) (l : list A), firstn a l ++ firstn b (skipn a l) = firstn (a + b) l.
Proof.
  induction a as [|a IH]; intros b l; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct b; reflexivity|]. f_equal. apply IH.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L2180849679.4 L62789046539.400000900BS1A1n1l1HS1A1n1l1H". (* [comment removed for export] *)
Lemma firstn_min_length {A} : forall (n : nat) (l : list A), firstn (Nat.min n (length l)) l = firstn n l.
Proof.
  intros n l. destruct (Nat.le_ge_cases n (length l)).
  - rewrite Nat.min_l by lia. reflexivity.
  - rewrite Nat.min_r by lia. rewrite firstn_all. rewrite firstn_all2 by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L22116553188.8L29946093357.8L49140597834.8L5231142375.6 L65121081947.600000I00b01601B01XS5fdata3len1w1L4Hlen2Hw1rS5fdata3len1w1L4Hlen2Hw1rS5fdata3len1w1L2Hw1rS5fdata1w2HwS5fdata3len4Hlen5Hlen2". (* [comment removed for export] *)
Lemma read_bs : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Pfdata,(12.(8.&8.))Plen,$;.Pw,$;.P,(<.(=.=R2.)(=.R2.(2;.(2<.(8.&8.)R3.))))P,(>.R3.(25.+2.+3>.))P,(<.(=.+1.R3.)(=.R3.+10000.))Zbs,(12.(8.&8.))(2=.R6.(2>.&40.R5.)(2>.&40.R4.))Znb,$;.(2;.(2<.(8.&8.)R1.))(<.(<.(=.=R1.)(=.R1.R6.))(<.(2?.(<.(=.(30.R7.R6.)(2;.(2<.(8.&8.)R8.)))(10.$;.R1.R6.))(<.(>.(2;.(2<.(8.&8.)R8.))(30.R7.R6.))(10.$;.R1.(31.(2;.(2<.(8.&8.)R8.))R7.))))(10.(12.(8.&8.))(32.(8.&8.)(33.(8.&8.)(34.R7.)R8.)R2.)(33.(8.&8.)(34.(30.R7.R1.))R8.))))")
(* [comment removed for export] *).
Proof.
  intros fdata len w Hlen Hlen2 Hw. cbv zeta.
  rewrite file_read_unguarded. unfold word_to_nat.
  rewrite (u_small w) by lia. rewrite (u_small len) by lia.
  rewrite firstn_length, skipn_length.
  set (L := length fdata) in *. set (r := (L - Z.to_nat len)%nat).
  split; [lia|]. split; [lia|].
  rewrite <- (firstn_min_length (Z.to_nat w) (skipn (Z.to_nat len) fdata)) at 1. rewrite skipn_length. fold L. fold r.
  rewrite firstn_plus_skipn. f_equal. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L18484129585.8 L26983617159.8 L5744834796.8  L59309037779.1000000900B00K00[S1a2bs2HlS1a2bs2HaS2bs1x2HxS1a2bs1x2Hn1l2l0". (* [comment removed for export] *)
Lemma write_other : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Pm,P,(8.&40.)(9.(8.&8.))Pa,$;.Pbs,(12.(8.&8.))Px,$;.P,(=.=R3.)P,(=.(30.R4.(2;.(2<.(8.&8.)R3.)))(25.+2.+40.))P,(<.(=.=R3.)(>.R3.(25.+2.+40.)))P,(?.(<.(=.R6.R4.)(>.R4.(30.R6.(2;.(2<.(8.&8.)R5.))))))(10.(9.(8.&8.))(35.R8.(11.R7.)R6.(11.R5.))A1.R8.(11.R5.))")
(* [comment removed for export] *).
Proof.
  intros m a bs x Ha Hl Hx Hn. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity. exfalso; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41475919908.600000=S1A1B1n1k1H1e". (* [comment removed for export] *)
Lemma lb_remove_2 : forall (A B : Z) n k, A <> B -> lb_remove B [(A, n); (B, k)] = [(A, n)].
Proof.
  intros A B n k H. cbn [lb_remove fst]. destruct (Z.eqb_spec A B); [lia|]. rewrite Z.eqb_refl. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Driver.
  Context {AMB : Amb}.
  Context {LM : Lim}.   (* [comment removed for export] *)
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variables (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream).
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid rd regs0 mem0.
  Hypothesis Hbrk : valid_brk usegs brk.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* [comment removed for export] *)
  Variable HI : heap_iface usegs (U_layout sp0).
  Hypothesis HSTAT : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Ph,(36.$4.(1>.Vsp0,)VHI,)PLB,(12.$1<.)Pm,P,(8.&40.)(9.(8.&8.))Pmo,$0.P,(37.$4.(1>.Vsp0,)VHI,R4.R3.R2.R1.)(<.(38.$4.R3.+7=353.(21.$39.(3:.(2>.&8.=))(24.$39.)))(<.(3;.(8.&40.)Lg,(8.&40.)(38.$4.R4.+7=330.(21.$39.(3<.R1.)(24.$39.))))(38.$4.R3.+4;<=8.(21.$39.(3<.(2>.&40.+7=330.))(24.$39.)))))")
(* [comment removed for export] *).          (* [comment removed for export] *)
  Variable DRV : nat -> HST usegs (U_layout sp0) HI -> Model -> Prop.
  Variable NS : HST usegs (U_layout sp0) HI -> Prop.
  Hypothesis MRZ : malloc_rz_stmt usegs (U_layout sp0) HI DRV NS.
  Hypothesis FREEC : free_c_stmt usegs (U_layout sp0) HI DRV.
  Hypothesis DRVMO : drv_mo_stmt usegs (U_layout sp0) HI DRV.
  Hypothesis DRVLE : drv_le_stmt usegs (U_layout sp0) HI DRV.
  Hypothesis HINIT : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "PM,P,(8.&40.)(9.(8.&8.))Pfd3,$3=.P,(3>.Vsp0,Va0s,Vpath,Venvv,Vmem0,R2.)(3;.(36.$4.(1>.Vsp0,)VHI,)Lh,(36.$4.(1>.Vsp0,)VHI,)(<.(37.$4.(1>.Vsp0,)VHI,R1.(24.$1<.)R4.(3?.VAMB,VLM,Vsp0,Vtid,Vbrk,Vmbase,Vfs0,Vstdin0,R3.))(<.(10.$;.(40.$4.(1>.Vsp0,)VHI,R1.)(41.&40.Vsp0,))(<.A3.VDRV,#>.R1.(3?.VAMB,VLM,Vsp0,Vtid,Vbrk,Vmbase,Vfs0,Vstdin0,R3.)A1.VNS,R1.))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Ltac cutfact lem H :=
    pose proof lem as H;
    first [specialize (H sp0)|idtac]; first [specialize (H a0s)|idtac]; first [specialize (H path)|idtac];
    first [specialize (H envv)|idtac]; first [specialize (H tid)|idtac]; first [specialize (H rd)|idtac]; first [specialize (H regs0)|idtac];
    first [specialize (H mem0)|idtac]; first [specialize (H Hva)|idtac]; first [specialize (H Hve)|idtac];
    first [specialize (H Hvsp)|idtac]; first [specialize (H Htid)|idtac]; first [specialize (H ME)|idtac];
    lazymatch goal with CM : cut_mem _ _ _ _ _ ?M |- _ => specialize (H M CM) end.

  (* [comment removed for export] *)
  Definition FRAME : list cell := ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "(21.$39.(3<.(2>.&40.=))(21.$39.(3<.(2>.&40.=))(21.$39.(3<.(2>.&40.=))(21.$39.(3<.(2>.&40.=))(21.$39.(3<.(2>.&40.(30.(41.&40.Vsp0,)+20.)))(21.$39.(3<.(2>.&40.+1=24<.))(21.$39.(3<.(2>.&40.+2.))(21.$39.(3<.(2>.&40.(30.(41.&40.Vsp0,)+8.)))(21.$39.(3<.(2>.&40.+3?2:8.))(24.$39.))))))))))")
(* [comment removed for export] *).
  Record dinv (m : mem) : Prop := DINV {
    di_win : forall a : Z, bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 -> wview usegs m (wa a) <> None;
    di_frame : rw_cells usegs m (bv_unsigned sp0 - 120) FRAME;
    di_minv : mem_inv usegs m;
    di_statics : statics_ok usegs (U_layout sp0) m;
    di_drv : drv_mem m;
    di_tid : rw_cells usegs m 0x5d020 [C4 tid];
    di_above : munch [(0, bv_unsigned sp0)] mem0 m
  }.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L18928845742.40L22973599159.43L31111523699.42L31111528215.43L34467128655.42L56765667309.42L68075135701.40L8871453363.43 L8871456983.42 00000500B00S00d00n01B01G01Q01[S3sp0S3sp01x2Hx2H1S3sp04SPlo1H1a2HaS3sp04SPlo1H1a2HaS3sp01a2HaS3sp04SPlo1H2H01a2HaS3sp0S3sp01a2HES3sp01a2Ha". (* [comment removed for export] *)
  #[using="AMB rd regs0 Hvsp Htid ME SPlo SPhi"] Lemma dinv_cut : forall M, cut_mem sp0 a0s path envv mem0 M -> dinv M.
  Proof.
    intros M CM. cutfact cut_mem_inv MI. cutfact cut_clear CL. cutfact cut_frame FRM. cutfact cut_tid_cell TIDC.
    pose proof SPlo. pose proof SPhi.
    split.
    - intros a Ha. apply (cm_win _ _ _ _ _ _ CM). unfold wa. rewrite u_small by lia. lia.
    - exact FRM.
    - exact MI.
    - split; [cbn; lia|]. split; [cbn; lia|]. cbn [hl_data_lo hl_data_hi hl_written U_layout]. unfold U_written.
      intros a Ha HE. apply CL; lia.
    - split; intros a Ha; apply CL; lia.
    - exact TIDC.
    - intros x Hx. cbn [outside] in Hx. pose proof (u64_range x). apply (cm_above _ _ _ _ _ _ CM). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L24376346147.36L34467128655.38L64936856764.3600000:00D00NS3sp04SPloS3sp01a2HaS3sp04SPhi". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma dinv_stk : forall m, dinv m -> stk usegs m (bv_unsigned sp0 - 8388608) (bv_unsigned sp0 - 128).
  Proof.
    intros m D. pose proof SPlo. pose proof SPhi. apply stk_of_wview; [lia|lia|]. intros a Ha. apply (di_win m D). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L32162264840.52L34467122463.53L37275296262.53L42409521467.50L47536040637.53L49652024439.50L56765677501.5300000:00D00Q00]00m01901MS3sp01a2HaS3sp01a2HaS3sp02SP1a2H1S3sp02SP3HSPS3sp02SP1a2Ha2H1S3sp02SP3HSPS3sp04SPlo1H2H01a2Ha". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma dinv_heap : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "PLB,(12.$1<.)PSP,$;.Pm,P,(8.&40.)(9.(8.&8.))Pm',P,(8.&40.)(9.(8.&8.))P,(42.R2.)P,(1?.$4.(1>.Vsp0,)R5.R4.R3.R2.)P,(28.$4.R3.)P,(27.$4.R4.(31.(41.&40.Vsp0,)+800000.)R6.)P,(=.R7.(31.(41.&40.Vsp0,)+80.))P,(=.(43.(1>.Vsp0,))R8.)(42.R7.)")
(* [comment removed for export] *).
  Proof.
    intros LB SP m m' D HP MI' ST' HSP HSP2. pose proof SPlo. pose proof SPhi. destruct D as [W F MI SO DM TI AB].
    split.
    - intros a Ha. destruct (Z.lt_ge_cases a SP).
      + apply (proj1 (proj2 (proj2 ST') a ltac:(lia))).
      + apply (proj2 (HP a ltac:(lia) ltac:(left; lia))). apply W. lia.
    - eapply heap_pres_rw_cells; [exact HP| exact F |]. cbn. apply client_range_stack. lia.
    - exact MI'.
    - eapply statics_ok_pres; eauto.
    - eapply drv_mem_pres; eauto.
    - eapply heap_pres_rw_cells; [exact HP| exact TI |]. intros a Ha. right; left.
      cbn [hl_data_lo hl_data_hi hl_static U_layout]. unfold U_static. cbn in Ha. lia.
    - eapply munch_above_pres; eauto. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0?L11303449684.52L12180585073.57L12894880909.57L12894885609.54L16085729392.51L27051828931.52L29566453808.57L29566458452.54L29566460129.52L29566460903.53L34467128655.51L41730347118.52L41730358326.57L49335788265.57L52101703855.52L52101704617.53L53505208731.52L53505208989.53L53900435230.52L56765662601.54L56765667309.57L56765676602.53L56765677372.52L63136217354.52L6354960761.51 L6354970921.52 L64204622775.52L66782601509.57L7470072007.53 L7470072769.52 L7470082832.57 L7470086516.54 L8923421326.52 L8923428566.57 L8929206777.57 00000C00P00Z00d00n01801B01L01\01f02002A02Y02j03=03Q03d04D04N04X04b04l05605C05W06506>06O06Y06i07307=07N07f08=S3sp02lo2hi1a2Ha2H1S3sp02B21i2HiS3sp01a2HaS3sp01a2HaS3sp01a2HaS3sp01x2H1S3sp01a2HaS3sp01a2HES3sp02lo2hi1a2H2S3sp01a2H4S3sp01a2HaS3sp04SPlo1H1x2HxS3sp04SPlo2B21H1i2Hi3tidS3sp03tid2B21i2HiS3sp02lo2hi1a2H12H2S3sp04SPlo1H1a2H22H3S3sp02lo2hi1a2H12H2S3sp04SPlo2lo2hi2Hr1H1a2H22H32H4S3sp04SPloS3sp01a2HaS3sp01a2HaS3sp01a2H1S3sp01a2H1S3sp01x2Hx2H1S3sp04SPlo1H2H01a2HaS3sp04SPlo2lo2hi2Hr2H01a2Ha2H1S3sp03tidS3sp03tid2B21i2HiS3sp01a2H3S3sp02lo2hi1a2H2S3sp01a2HaS3sp01a2HES3sp04SPlo1H1x2HxS3sp04SPlo2B21H1i2Hi3tidS3sp04SPlo2B21H2H01i2Hi". (* [comment removed for export] *)
  #[using="Hvsp Htid SPlo SPhi"] Lemma dinv_agree : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Pm,P,(8.&40.)(9.(8.&8.))Pm',Px,(8.&40.)(9.(8.&8.))Plo,$;.Phi,$;.P,(42.R4.)P,Pa,$;.P,(<.(=.=R1.)(>.R1.(25.+2.+40.)))P,(?.(<.(=.(31.(41.&40.Vsp0,)+800000.)R2.)(>.R2.(31.(41.&40.Vsp0,)+80.))))P,(?.(<.(=.R6.R3.)(>.R3.R5.)))P,(?.(<.(=.+5=024.R4.)(>.R4.+5=028.)))P,(?.(<.(=.+4<?69.R5.)(>.R5.+5<?69.)))(10.(9.(8.&8.))A1.R:.(11.R6.)A1.R;.(11.R6.))P,(44.R6.R5.)P,(2?.(<.(=.+7>000.R5.)(=.R4.(31.(41.&40.Vsp0,)+800000.)))(2?.(=.R4.+10000.)(=.R4.R5.)))(42.R7.)")
(* [comment removed for export] *).
  Proof.
    intros m m' lo hi D AG GR Hr. pose proof SPlo. pose proof SPhi. destruct D as [W F MI SO DM TI AB].
    assert (AG' : forall a : Z, 0 <= a < 2 ^ 64 -> (bv_unsigned sp0 - 128 <= a \/ 0x10000 <= a < 0x7e000) -> ~ (0x5d024 <= a < 0x5d028) ->
                  ~ (0x4cf69 <= a < 0x5cf69) -> m' (wa a) = m (wa a)).
    { intros a H1 H2 H3 H4. apply AG; lia. }
    split.
    - intros a Ha. apply (mem_grows_wmono m m' GR). apply W. lia.
    - ddestruct F as [CA [W1 [W2 W3]]]. split; [| split; [lia|]; split; [exact W2|]; intros i Hi; apply (mem_grows_wmono m m' GR); apply W3; exact Hi].
      destruct CA as [WF (B1 & B2 & B3)]. split; [exact WF|]. split; [exact B1|]. split; [exact B2|].
      intros i Hi. unfold mrd. rewrite AG' by (cbn in Hi, B2; lia). apply B3. exact Hi.
    - eapply (mem_inv_agree m m' (fun a => (bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 - 128) \/ (lo <= a < hi /\ 0 <= a) \/ (0x5d024 <= a < 0x5d028)
                                          \/ (0x4cf69 <= a < 0x5cf69))); [exact MI| |].
      + intros a H1 H2. apply AG; lia.
      + intros a [Ha|[Ha|[Ha|Ha]]]; [apply ro_addr_high; lia | | apply ro_addr_data; lia | apply ro_addr_data; lia].
        destruct (Z.lt_ge_cases a 0x10000); [apply ro_addr_low; lia | apply ro_addr_high; lia].
    - ddestruct SO as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha HE.
      cbn [hl_data_lo hl_data_hi hl_written U_layout] in *. unfold U_written in HE.
      rewrite AG' by lia. apply S3; [exact Ha|]. unfold U_written. exact HE.
    - destruct DM as [D1 D2 D3 D4]. split; intros a Ha; rewrite AG' by lia; auto.
    - ddestruct TI as [CA [W1 [W2 W3]]]. split; [| split; [lia|]; split; [exact W2|]; intros i Hi; apply (mem_grows_wmono m m' GR); apply W3; exact Hi].
      destruct CA as [WF (B1 & B2 & B3)]. split; [exact WF|]. split; [exact B1|]. split; [exact B2|].
      intros i Hi. unfold mrd. rewrite AG' by (cbn in Hi, B2; lia). apply B3. exact Hi.
    - intros x Hx. cbn [outside] in Hx. pose proof (u64_range x). rewrite <- (AB x) by (cbn [outside]; tauto).
      rewrite <- (Z_to_bv_bv_unsigned x). apply AG'; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L10259216302.57L10646848565.57L1080380655.60 L10917014968.59L11401374120.59L16085739552.60L37082574059.58L37179978549.57L42566393902.57L57454710446.57L59788594222.57L62099307120.59L63078755253.57L63350670752.60L66801373109.57L68706383422.60L9550212712.59 00000500:00D00N00X00e01301801=01B01G01Q01V01c01h02502?S3sp0S3sp0S3sp01a2HaS3sp01i2HiS3sp01i2HiS3sp01a2Ha2H1S3sp03tid4HtidS3sp0S3sp0S3sp0S3sp0S3sp01a2HaS3sp0S3sp01a2Ha2H1S3sp0S3sp01a2Ha2H1S3sp01i2Hi". (* [comment removed for export] *)
  #[using="Hvsp Htid SPlo SPhi HSTAT"] Lemma dinv_tail_mem : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Pm,P,(8.&40.)(9.(8.&8.))Ph,(36.$4.(1>.Vsp0,)VHI,)PLB,(12.$1<.)Pmo,$0.P,(42.R4.)P,(37.$4.(1>.Vsp0,)VHI,R4.R3.R5.R2.)(45.Vsp0,(41.&40.Vtid,)R6.)")
(* [comment removed for export] *).
  Proof.
    intros m h LB mo D HH. pose proof SPlo. pose proof SPhi. destruct D as [W F MI SO DM TI AB].
    ddestruct (HSTAT h LB m mo HH) as (NL & [canw CA] & GOT). ddestruct SO as (_ & _ & ST). pose proof DM as [DF DC DL DO DE].
    cbn [hl_data_lo hl_data_hi hl_written U_layout] in ST. unfold U_written in ST.
    split.
    - intros a Ha. pose proof (u64_range a). rewrite <- (Z_to_bv_bv_unsigned a). apply W. lia.
    - intros a Ha. destruct (Z.lt_ge_cases a 0x48000); [apply mem_inv_text_none; [exact MI|lia] | apply ST; lia].
    - apply rw_cells_rdn8. exact GOT.
    - intros a Ha. destruct (Z.lt_ge_cases a 0x4cd30); [apply ST; lia | apply DF; lia].
    - rewrite (rdn_none_img m 0x4cf68 1); [exact img_49818_1 | intros i Hi; apply DC; lia | lia | lia].
    - pose proof (rw_cells_rdn4 _ _ _ TI) as T. rewrite Z_to_bv_bv_unsigned. exact T.
    - pose proof Htid. lia.
    - rewrite (rdn_none_img m 0x7d328 4); [exact img_59c58_4 | intros i Hi; apply DL; lia | lia | lia].
    - exists canw. apply rw_cells_rdn8. exact CA.
    - apply rw_cells_rdn1. exact NL.
    - rewrite (rdn_none_img m 0x7d770 8); [exact img_5a0a0_8 | intros i Hi; apply DO; lia | lia | lia].
    - rewrite (rdn_none_img m 0x7d780 8); [exact img_5a0b0_8 | intros i Hi; apply DO; lia | lia | lia].
    - intros a Ha. apply (dm_atx m DM). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00\0?L12113272004.57L15690264964.57L16085729392.59L1748097566.57 L20629502660.57L21011980132.57L23515878686.57L23982118078.57L28070455742.57L29566453808.59L29566460774.59L3077252804.57 L35575990628.57L38415669604.57L38828685214.57L39071876414.57L40324139364.57L41208547172.57L41730358455.64L43333725758.57L46332287646.57L51063455902.57L52101704488.59L52326541156.57L52945209630.57L53505208860.59L56559771492.57L56765666148.64L56765676731.59L57007104708.57L60556448318.57L6065560878.57 L61180623918.57L63013951172.57L6395539652.57 L64644785982.57L66103035076.57L66188260615.64L66702410020.57L66919148446.57L6759395518.57 L7470071878.59 L7470082832.59 L8923428439.64 00000500:00D00I00N00S00X00]00b00l01601;01@01E01J01O01T01Y01o02402902>02O02T02Y03703<03U03_03d03i03n04304804=04B04G04`04e04j04o05905C05YS3sp0S3sp0S3sp01a2HaS3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp01a2HaS3sp01a2H3S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp04SPlo1a1n2H31j2HjS3sp0S3sp0S3sp0S3sp04SPlo1H1a2H1S3sp0S3sp0S3sp04SPlo2lo2hi2Hr1a2H12H22H3S3sp0S3sp04SPlo1a1n2H12H21j2HjS3sp01a2H1S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp04SPlo1a1n2H12H21j2HjS3sp0S3sp0S3sp0S3sp01a2H2S3sp01a2HaS3sp04SPlo1a1n2H41j2Hj". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma tail_mem_agree : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Pm,P,(8.&40.)(9.(8.&8.))Pm',Px,(8.&40.)(9.(8.&8.))Plo,$;.Phi,$;.P,(45.Vsp0,(41.&40.Vtid,)R4.)P,Pa,$;.P,(<.(=.=R1.)(>.R1.(25.+2.+40.)))P,(?.(<.(=.(31.(41.&40.Vsp0,)+800000.)R2.)(>.R2.(31.(41.&40.Vsp0,)+80.))))P,(?.(<.(=.R6.R3.)(>.R3.R5.)))P,(?.(<.(=.+5=024.R4.)(>.R4.+5=028.)))P,(?.(<.(=.+4<?69.R5.)(>.R5.+5<?69.)))(10.(9.(8.&8.))A1.R:.(11.R6.)A1.R;.(11.R6.))P,(44.R6.R5.)P,(2?.(<.(=.+7>000.R5.)(=.R4.(31.(41.&40.Vsp0,)+800000.)))(2?.(=.R4.+10000.)(=.R4.R5.)))(45.Vsp0,(41.&40.Vtid,)R7.)")
(* [comment removed for export] *).
  Proof.
    intros m m' lo hi TM AG GR Hr. pose proof SPlo. pose proof SPhi. destruct TM as [W RO GOT DA CO TI TR LO [canw CA] NL SI OF ATX].
    assert (AG' : forall a : Z, 0x10000 <= a < 0x7e000 -> ~ (0x5d024 <= a < 0x5d028) -> ~ (0x4cf69 <= a < 0x5cf69) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a H1 H2 H3. apply AG; lia. }
    assert (RD : forall (a : Z) n, 0x10000 <= a -> a + Z.of_nat n <= 0x7e000 -> (a + Z.of_nat n <= 0x5d024 \/ 0x5d028 <= a) ->
                 (a + Z.of_nat n <= 0x4cf69 \/ 0x5cf69 <= a) ->
                 rdn RSEGS m' (Z_to_bv 64 a) n = rdn RSEGS m (Z_to_bv 64 a) n).
    { intros a n H1 H2 H3 H4. symmetry. apply rdn_agree. intros j Hj. rewrite u_small by lia. symmetry. apply AG'; lia. }
    split.
    - intros a Ha. apply (mem_grows_wmono m m' GR). apply W. exact Ha.
    - intros a Ha. rewrite AG' by lia. apply RO. exact Ha.
    - rewrite RD by (cbn; lia). exact GOT.
    - intros a Ha. rewrite AG' by lia. apply DA. exact Ha.
    - rewrite RD by (cbn; lia). exact CO.
    - rewrite RD by (cbn; lia). exact TI.
    - exact TR.
    - rewrite RD by (cbn; lia). exact LO.
    - exists canw. rewrite RD by (cbn; lia). exact CA.
    - rewrite RD by (cbn; lia). exact NL.
    - rewrite RD by (cbn; lia). exact SI.
    - rewrite RD by (cbn; lia). exact OF.
    - intros a Ha. rewrite AG' by lia. apply ATX. exact Ha.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Hvsp Htid SPlo SPhi HSTAT"] Lemma dinv_fw_mem : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Pm,P,(8.&40.)(9.(8.&8.))Ph,(36.$4.(1>.Vsp0,)VHI,)PLB,(12.$1<.)Pmo,$0.P,(42.R4.)P,(37.$4.(1>.Vsp0,)VHI,R4.R3.R5.R2.)(3;.(8.&40.)Lcanw,(8.&40.)(46.Vsp0,R1.R7.))")
(* [comment removed for export] *).
  Proof.
    intros m h LB mo D HH. destruct (dinv_tail_mem m h LB mo D HH) as [? ? ? ? ? ? ? ? [canw CA] ? ? ? ?]. exists canw. split; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma model1g_MOK : forall fd3, MOK (model1g sp0 tid brk mbase fs0 stdin0 fd3).
  Proof. intros. split; reflexivity. Qed.

  #[using="Type"] Lemma t_die_nil' : forall msg fs, t_die msg fs [].
  Proof. intros. unfold t_die. apply t_emit_has_nil. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section File.
    Variable fdata : list byte.
    Hypothesis Hfs : fs_lookup fs0 path = Some fdata.

    Definition OOM : TSet := t_die msg_oom fs0.
    Definition BODY : TSet := t_body fdata fs0.
    (* [comment removed for export] *)
    Definition LSHAPE (cap : Z) : TSet :=
      if ((cap <=? Z.of_nat (length fdata)) && (cap <? 67108864))%bool then t_alt2 OOM BODY else BODY.

    #[using="Type"] Lemma OOM_nil : OOM []. Proof. unfold OOM. apply t_die_nil'. Qed.
    #[using="Type"] Lemma BODY_nil : BODY [].
    Proof.
      unfold BODY, t_body.
      repeat first [ apply t_die_nil' | apply t_emit_has_nil | apply t_exit_has_nil | apply t_alt2_has_nil_l
                   | lazymatch goal with |- (if ?c then _ else _) [] => destruct c | |- (match ?c with _ => _ end) [] => destruct c end ].
    Qed.
    #[using="Type"] Lemma LSHAPE_nil : forall cap, LSHAPE cap [].
    Proof. intros cap. unfold LSHAPE. destruct (_ && _)%bool; [apply t_alt2_has_nil_l; apply OOM_nil | apply BODY_nil]. Qed.
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L31704847007.37L32174474944.3700000B00TS3sp05fdata3cap2H1S3sp05fdata3cap2H2". (* [comment removed for export] *)
    #[using="sp0"] Lemma LSHAPE_grow : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Pcap,$;.P,(=.R1.(2;.(2<.(8.&8.)Vfdata,)))P,(>.R2.+4000000.)(47.(48.$49.(4:.(4;.+2.R3.)))(4:.R3.))")
(* [comment removed for export] *).
    Proof.
      intros cap H1 H2. unfold LSHAPE at 2. replace (_ && _)%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      unfold LSHAPE. destruct (_ && _)%bool; [apply t_alt2_absorb | apply t_eq_refl].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L17711284858.36L56232753123.3600000;00LS3sp03cap1HS3sp05fdata3cap1H". (* [comment removed for export] *)
    #[using="sp0"] Lemma LSHAPE_body : forall cap, (Z.of_nat (length fdata) < cap \/ 67108864 <= cap) -> LSHAPE cap = BODY.
    Proof.
      intros cap H. unfold LSHAPE. replace (_ && _)%bool with false; [reflexivity|].
      symmetry. destruct H; [apply andb_false_intro1; apply Z.leb_gt; lia | apply andb_false_intro2; apply Z.ltb_ge; lia].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Definition FDS (off : word) : list (word * FdEntry) := ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "(21.(22.(8.&40.)$3=.)(23.(8.&40.)$3=.(2>.&40.+3.)(4<.Vpath,O1.))(21.(22.(8.&40.)$3=.)(23.(8.&40.)$3=.(2>.&40.=)(4=.(2>.&40.=)))(21.(22.(8.&40.)$3=.)(23.(8.&40.)$3=.(2>.&40.+1.)(4=.(2>.&40.+1.)))(21.(22.(8.&40.)$3=.)(23.(8.&40.)$3=.(2>.&40.+2.)(4=.(2>.&40.+2.)))(24.(22.(8.&40.)$3=.))))))")
(* [comment removed for export] *).
        #[using="Type"] Lemma FDS_insert : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Poff,(8.&40.)Pe,$3=.(10.(12.(22.(8.&40.)$3=.))(4>.(4?.R2.)(2>.&40.+3.)R1.)(21.(22.(8.&40.)$3=.)(23.(8.&40.)$3=.(2>.&40.+3.)R1.)(21.(22.(8.&40.)$3=.)(23.(8.&40.)$3=.(2>.&40.=)(4=.(2>.&40.=)))(21.(22.(8.&40.)$3=.)(23.(8.&40.)$3=.(2>.&40.+1.)(4=.(2>.&40.+1.)))(21.(22.(8.&40.)$3=.)(23.(8.&40.)$3=.(2>.&40.+2.)(4=.(2>.&40.+2.)))(24.(22.(8.&40.)$3=.)))))))")
(* [comment removed for export] *).
    Proof. intros. reflexivity. Qed.
    #[using="Type"] Lemma FDS_lookup3 : forall off, fd_lookup (FDS off) (Z_to_bv 64 3) = Some (FdFile path off).
    Proof. intros. reflexivity. Qed.
    #[using="Type"] Lemma FDS_lookup2 : forall off, fd_lookup (FDS off) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
    Proof. intros. reflexivity. Qed.
    
    Definition cap_ok (cap : Z) : Prop := exists e : Z, 16 <= e <= 26 /\ cap = 2 ^ e.
    Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L34748030316.36L40614228022.36L41415985561.3600000:00D00IS3sp01e2HeS3sp01e2HeS3sp0". (* [comment removed for export] *)
    #[using="sp0"] Lemma cap_ok_bounds : forall cap, cap_ok cap -> 65536 <= cap <= 67108864.
    Proof.
      (intros cap dd_H; ddestruct dd_H as (e & He & ->)). change 65536 with (2 ^ 16). change 67108864 with (2 ^ 26).
      split; apply Z.pow_le_mono_r; lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L2814112575.37 L30531358683.38L38714715259.38L41422282358.38L65029210250.37L7276640029.38 L9540568638.37 00000;00D00P00W00^00h00oS3sp01e3HltS3sp01e1HS3sp01e2He1HS3sp01eS3sp01eS3sp01e2HeS3sp01e". (* [comment removed for export] *)
    #[using="sp0"] Lemma cap_ok_double : forall cap, cap_ok cap -> cap < 67108864 -> cap_ok (2 * cap) /\ 2 * cap <= 67108864.
    Proof.
      (intros cap dd_H; ddestruct dd_H as (e & He & ->); intros Hlt). change 67108864 with (2 ^ 26) in *.
      assert (e < 26) by (apply (Z.pow_lt_mono_r_iff 2); lia).
      rewrite <- Z.pow_succ_r by lia. split; [exists (Z.succ e); split; [lia|reflexivity] | apply Z.pow_le_mono_r; lia].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Definition LREGS (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (buf len cap : Z) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "(50.O14.(2>.&40.(31.(41.&40.Vsp0,)+80.))(2>.&40.+10800.)(2>.&40.+5=0<8.)O13.O12.O11.(2>.&40.+2.)(2>.&40.O3.)O10.O?.O>.O=.O<.O;.O:.O9.(51.Vsp0,Va0s,Vpath,Venvv,)(2>.&40.O2.)(2>.&40.+3.)(2>.&40.O1.)(2>.&40.+4<?69.)O8.(2>.&40.=)(2>.&40.=)(2>.&40.=)(2>.&40.=)O7.O6.O5.O4.)")
(* [comment removed for export] *).

    Record LINV (buf len cap : Z) (k : nat) (m : mem) (mo : Model) (h : HST usegs (U_layout sp0) HI) : Prop := MKLINV {
      li_dinv : dinv m;
      li_heap : HEAP usegs (U_layout sp0) HI h [(buf, cap)] m mo;
      li_drv : DRV k h mo;
      li_credit : 2 ^ 27 <= cap * 2 ^ (Z.of_nat k);
      li_top : heap_top usegs (U_layout sp0) HI h = bv_unsigned sp0;
      li_mok : MOK mo;
      li_fs : m_fs mo = fs0;
      li_fds : m_fds mo = FDS (Z_to_bv 64 len);
      li_bytes : bytes_at usegs m buf (firstn (Z.to_nat len) fdata);
      li_wr : wr_at usegs m buf cap;
      li_len : 0 <= len <= Z.of_nat (length fdata);
      li_capok : cap_ok cap;
      li_block : block_range (U_layout sp0) buf cap
    }.

    (* [comment removed for export] *)
    Definition after_loop_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Pbuf,$;.Pcap,$;.Pk,$52.Pra,(8.&40.)Pt0,(8.&40.)Pt1,(8.&40.)Pt2,(8.&40.)Pa1,(8.&40.)Pa2,(8.&40.)Pa3,(8.&40.)Pa4,(8.&40.)Pa5,(8.&40.)Pa6,(8.&40.)Pa7,(8.&40.)Pt3,(8.&40.)Pt4,(8.&40.)Pt5,(8.&40.)Pt6,(8.&40.)Pm,P,(8.&40.)(9.(8.&8.))Pmo,$0.Ph,(36.$4.(1>.Vsp0,)VHI,)P,(53.R15.(2;.(2<.(8.&8.)Vfdata,))R14.(54.R13.)R3.R2.R1.)P,(>.(2;.(2<.(8.&8.)Vfdata,))R15.)(6.$4.(7.(55.(56.R14.R13.R12.R11.(2>.&40.=)R10.R?.R>.R=.R<.R;.R:.(2>.&40.=)R9.R8.R7.R6.R17.(2;.(2<.(8.&8.)Vfdata,))R16.)(57.&5.(8.&40.))(2>.&40.+1=340.)(2>.&20.=)(1;.(8.&40.))R5.(58.$4.))R4.)$59.)")
(* [comment removed for export] *).

    Section Loop.
      Hypothesis AFTER : after_loop_stmt.

      (* [comment removed for export] *)
      Local Ltac2 Set LiaOrc.tbl := fun () => "02Y0@L10171163275.125L10398360587.130L10588871529.173L1080386751.91  L10804480356.129L11650333758.119L12273870215.119L13918813557.174L14185767736.108L15047127963.173L15538036371.120L15938186933.173L1605857809.119 L17521935756.173L17579853785.173L18247827302.213L18274225714.119L18274372236.90 L18390611844.90 L18761043168.119L18878088489.165L18878136745.160L18878136756.213L1946584659.88  L19570514310.172L19618459855.88 L19681329345.173L22124929028.88 L22225449282.180L22225473019.184L22225538297.187L22251784836.98 L24595372494.119L24632377621.119L24969123061.129L25079625719.88 L25322763655.187L25322863131.160L25322944646.212L25322946203.165L25329382528.136L25797806186.119L26421301722.98 L26421880318.91 L27631758958.184L28325775620.113L28325841664.116L28325907599.108L28469289050.119L2898871050.130 L29063104852.187L29069592659.136L2965893286.130 L31042154173.113L31042219193.116L31042284342.108L31044147901.114L31044149123.91 L31093871211.173L31158054446.187L31692383135.136L31900188233.130L32037034229.130L32162264840.110L32168048614.134L32170145728.136L34106073370.180L34106105251.184L34106170529.187L34313350223.87 L34317690731.173L34319854798.130L34321867478.134L34326014414.130L34509677411.130L34515218871.173L34852927659.129L34852993582.132L34852997513.125L35999465718.116L36407780302.88 L36682342399.125L36682394712.132L36682591965.129L3719648633.213 L37622514262.116L37622514262.132L37713156615.182L37872805885.87 L38329117622.212L39123319083.165L39123369387.160L40037302066.136L40039726645.187L40041574668.180L40041627408.125L40041663288.108L40588156143.119L41215730597.125L41235828747.173L41358841388.117L42167667556.165L42571139497.160L42571139508.213L42571222313.165L43545370476.113L44183686636.129L45341829978.91 L45572044828.119L45878554845.185L46047846405.173L47346353273.134L47350793447.120L48580182456.108L48769423462.172L50847763777.213L51316762330.98 L51463444997.88 L51814518551.213L52522401946.134L52681284618.212L53504591286.134L53510883898.134L53516962962.119L53517156363.173L53519235339.161L54292421761.113L54292551946.108L54292618885.116L54790496069.74 L55555926517.173L56222201069.120L56866275927.90 L57303814198.134L5744825397.116 L5744825397.132 L5744825397.187 L57689562082.130L57695985378.130L58249195698.119L58492558908.136L58806973186.119L58807122689.117L59214911463.173L59321100261.119L59323443447.133L59583261834.88 L60566122166.180L60568333838.213L63181003941.213L6406847242.113 L64799627043.130L64861874661.114L64863870437.113L64864000110.108L64864067553.116L65005379746.213L65041719018.134L65127317551.87 L65366727684.128L66736784087.134L6749541530.134 L67582271585.120L67903737220.136L67906161795.187L68557234835.180L68559479339.213L7586430697.113 L7875230973.134 00000]01m03d04I05?06E07E08I09209f0:W0;N0<70=Y0>f0?]0@F0@f0AF0B30Bd0CU0DL0E60F?0F_0HV0I:0JM0K`0M30MW0NS0OW0PL0Q20R30Rn0So0Tj0Ue0VW0W=0Wc0Y50Yc0ZQ0[?0\20]I0^@0_10_Z0`C0`l0aU0b>0b^0ck0f00gJ0hE0i`0ja0ke0ld0m_0nZ0oU10<11311c12S13C14>15G16=17317i19>1:81;@1<H1=P1?J1@81Ab1Bo1CS1DJ1E;1El1F]1GT1HK1I41I]1Je1Ke1M21Mn1Nk1O\1PS1QD1R[1SQ1TD1UX1V_1Wc1X`1Yi1ZR1[F1\@1]41]Z1^e1_N1`k1aT1b=1bf1cZ1dK1e91eg1fU1h41hl1j51jd1kd1lR1m@1n<1o=20D21722623624225i26Z27K27k28b29Y2:M2;62<E2=A2>=2?92@52@l2AU2BM2CS2D@2Di2El2F]2GT2H[2Ib2Jc2L7S3sp05fdata4fuel3buf3len1k5Hfuel3LEN2bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3BR11w3Hw22bs2nb3NB13NB22L83NB07NOTFULLS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB3BR13BR23BR51w2bs2nb3NB13NB22L83NB04FULL5CAPLT2A03BQ13BQ23BQ33BQ55APARTS3sp05fdata4fuel3buf3len1k5Hfuel1a2HaS3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3LEN3BR12bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3Hlc3LEN3Hhi3BR13BR42bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3BR11w3Hw22bs2nb3NB12L8S3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB3BR12bs2nb2L82A03BQ1S3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A0S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L8S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB2bs2nb2L82A0S3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB3BR13BR51w2bs2nb3NB12L83NB05CAPLT2A03BQ13BQ55APARTS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR3Hhi3BR12bs2nb2L82A03BQ13BQ33BQ4S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A02FLS3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp05fdata4fuel3buf3len1k5HfuelS3sp05fdata4fuel3buf3len1k5HfuelS3sp05fdata4fuel3buf3len1k5Hfuel3LEN2bs2nb2L8S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L8S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L8S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A02FLS3sp05fdata4fuel3buf3len3cap1k5Hfuel3Hlc1HS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB3BR12bs2nb2L84FULL2A03BQ1S3sp05fdata4fuel3buf3len1k5HfuelS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB3BR13BR23BR51w2bs2nb3NB13NB22L83NB04FULL5CAPLT2A03BQ13BQ23BQ33BQ55APARTS3sp05fdata4fuel3buf3len3cap1k5HfuelS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR3Hhi2CB3BR12bs2nb2L82A03BQ13BQ33BQ42FLS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR3Hhi2CB3BR12bs2nb2L82A03BQ13BQ33BQ42FLS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR3Hhi2CB3BR12bs2nb2L82A03BQ13BQ33BQ42FLS3sp05fdata4fuel3buf3len1k5Hfuel3LENS3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3BR11w3Hw12bs2nb3NB12L8S3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3LEN3BR11w3Hw12bs2nb3NB22L83NB0S3sp05fdata4fuel3buf3len3cap1k5Hfuel3BR43BR52bs2nb2L8S3sp05fdata4fuel3buf3len3cap1k5Hfuel1HS3sp04SPlo4SPhi5fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A02FLS3sp04SPlo4SPhi5fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L8S3sp04SPlo4SPhi5fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A02FLS3sp04SPlo4SPhi5fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L8S3sp04SPlo4SPhi5fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3BR12bs2nb2L8S3sp05fdata4fuel3buf3len1k5Hfuel1w3Hw1S3sp05fdata4fuel3buf3len1k5Hfuel1w3Hw1S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB1w2bs2nb3NB12L83NB05CAPLT2A03BQ43BQ52FLS3sp04SPlo5fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp05fdata4fuel3buf3len1k5Hfuel1w2bs2nb3NB12L83NB0S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3Hlc2CB3BR13BR21w3Hw22bs2nb3NB12L83NB07NOTFULLS3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A02FLS3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L8S3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp05fdata4fuel3buf3len1k5HfuelS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR3Hhi3BR12bs2nb2L82A03BQ13BQ33BQ4S3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR3Hlo2CB3BR13BR43BR51w2bs2nb3NB12L83NB04FULL5CAPLT2A03BQ13BQ33BQ43BQ55APART2FL1x2H32H42H5S3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB3BR13BR21w2bs2nb3NB13NB22L83NB04FULL5CAPLTS3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3BR12bs2nb2L84FULLS3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3LEN2CB3BR13BR21w3Hw22bs2nb3NB13NB22L83NB07NOTFULLS3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3BR11w3Hw12bs2nb3NB12L81a2HaS3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB1w2bs2nb3NB12L83NB05CAPLTS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR3BR12bs2nb2L84CAP2S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A03BQ12FLS3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A03BQ12FLS3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A03BQ12FLS3sp05fdata4fuel3buf3len3cap1k5Hfuel2CBS3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB2bs2nb2L82A0S3sp05fdata4fuel3buf3len3cap1k5Hfuel2CB2bs2nb2L8S3sp05fdata4fuel3buf3len3cap1k5Hfuel2CB2bs2nb2L8S3sp05fdata4fuel3buf3len3cap1k5Hfuel2CB2bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3BR12bs2nb2L84FULLS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR3Hhi3BR13BR42bs2nb2L82A03BQ1S3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3LEN3BR12bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3LEN3BR12bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3LEN3BR12bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3LEN3Hlo3BR13BR21w3Hw13Hw22bs2nb3NB22L81x2H5S3sp05fdata4fuel3buf3len3cap1k5Hfuel3Hlc1H4SPlo3LEN2CB3BR1S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3Hhi3BR13BR41w3Hw22bs2nb3NB12L8S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3Hhi3BR13BR41w3Hw22bs2nb3NB12L8S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3Hhi3BR13BR41w3Hw22bs2nb3NB12L8S3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB3BR13BR23BR51w2bs2nb3NB13NB22L83NB04FULL5CAPLT2A03BQ13BQ23BQ33BQ55APART2FLS3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L81x2H2S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3LEN3Hlo2CB3BR13BR23BR43BR51w3Hw22bs2nb3NB13NB22L83NB01x2H32H42H5S3sp03a0s4path4envv5fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A05regs31i2HiS3sp05fdata4fuel3buf3len3cap1k5HfuelS3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A02FLS3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L8S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L8S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L8S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A02FLS3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A02FLS3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3Hhi3BR13BR41w3Hw22bs2nb3NB12L8S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3BR11w3Hw22bs2nb3NB12L8S3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR3Hhi3BR13BR42bs2nb2L82A03BQ13BQ3S3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3BR11w3Hw12bs2nb3NB12L8S3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB3BR12bs2nb2L8S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L8S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A02FLS3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3Hlc3LEN2CB3BR13BR23BR51w3Hw13Hw22bs2nb3NB22L8S3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3LEN3BR12bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3Hlo3BR11w3Hw1S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3LEN3BR13BR51w3Hw13Hw22bs2nb3NB13NB22L83NB0S3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB3BR12bs2nb2L82A03BQ12FLS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB3BR12bs2nb2L82A03BQ1S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3BR12bs2nb2L86CAPMAXS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR3BR11w3Hw13Hw22bs2nb2L84LENFS3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A0S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB2bs2nb2L82A02FLS3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3Hlc2CB3BR1S3sp05fdata4fuel3buf3len3cap1k5Hfuel1HS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel3Hlc2CR2CB3BR12bs2nb2L82A03BQ12FLS3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB3BR11w2bs2nb3NB12L83NB05CAPLT2A03BQ15APART2FLS3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A0S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L8S3sp04SPhi5fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp04SPhi5fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp04SPhi5fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp05fdata3buf3len3cap1k2ra2t02t12t22a02a12a22a32a42a52a62a72s72t32t42t52t61m2mo5Hfuel7li_len0S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A03BQ1S3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR3BR11w3Hw13Hw22bs2nb2L84LENFS3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3BR11w3Hw1S3sp05fdata4fuel3buf3len3cap1k5Hfuel2CB1w2bs2nb3NB12L83NB05CAPLTS3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L81x2H1S3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L81x2H1S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A02FL1x2H1S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel2CR2CB3BR12bs2nb2L84FULLS3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3LEN2CB3BR11w3Hw22bs2nb3NB12L8S3sp05fdata4fuel3buf3len1k5Hfuel1w2bs2nb3NB12L83NB0S3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR3BR12bs2nb2L84CAP2S3sp05fdata4fuel3buf3len1k5Hfuel1w2bs2nb3NB12L83NB04SPlo3BR13Hw1S3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3BR11w3Hw12bs2nb3NB12L8S3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB3BR13BR23BR51w2bs2nb3NB13NB22L83NB04FULL5CAPLT2A03BQ13BQ23BQ33BQ55APARTS3sp05fdata4fuel3buf3len3cap5Hfuel2CR2CB2bs2nb2L8S3sp05fdata4fuel3buf3len3cap5Hfuel2CR2CB2bs2nb2L8S3sp05fdata4fuel3buf3len1k5HfuelS3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A02FLS3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A02FLS3sp05fdata4fuel3buf3len3cap2k'5Hfuel2bs2nb2L82A02FLS3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel2CB3BR13BR21w2bs2nb3NB12L83NB07NOTFULLS3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3BR11w3Hw12bs2nb3NB12L8S3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3BR11w3Hw12bs2nb3NB12L8S3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3BR11w3Hw12bs2nb3NB12L8S3sp04SPlo5fdata4fuel3buf3len1k5Hfuel3BR11w3Hw12bs2nb3NB12L8S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A02FLS3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3Hlc3LEN2CB3BR1S3sp03a0s4path4envv5fdata4fuel3buf3len3cap1k5Hfuel2bs2nb2L85regs21i2HiS3sp05fdata4fuel3buf3len3cap1k5Hfuel2bs2nb2L8S3sp05fdata4fuel3buf3len1k5Hfuel2bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR3LEN3BR12bs2nb2L84LENFS3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L8S3sp05fdata4fuel3buf3len3cap2k'5Hfuel2CR2bs2nb2L82A02FLS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB3BR12bs2nb2L82A03BQ12FLS3sp04SPlo5fdata4fuel3buf3len3cap2k'5Hfuel2CR2CB3BR12bs2nb2L82A03BQ12FLS3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3Hlc2CB3BR13BR42bs2nb2L8S3sp04SPlo5fdata4fuel3buf3len3cap1k5Hfuel3BR13BR21w2bs2nb3NB13NB22L83NB04FULL6CAPMAX". (* [comment removed for export] *)
      #[using="Hvsp Htid SPlo SPhi HSTAT NS MRZ FREEC DRVMO Hfs AFTER"] Lemma read_loop : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "Pfuel,$52.Pbuf,$;.Plen,$;.Pcap,$;.Pk,$52.Pra,(8.&40.)Pt0,(8.&40.)Pt1,(8.&40.)Pt2,(8.&40.)Pa0,(8.&40.)Pa1,(8.&40.)Pa2,(8.&40.)Pa3,(8.&40.)Pa4,(8.&40.)Pa5,(8.&40.)Pa6,(8.&40.)Pa7,(8.&40.)Ps7,(8.&40.)Pt3,(8.&40.)Pt4,(8.&40.)Pt5,(8.&40.)Pt6,(8.&40.)Pm,P,(8.&40.)(9.(8.&8.))Pmo,$0.Ph,(36.$4.(1>.Vsp0,)VHI,)P,(>.(31.(2;.(2<.(8.&8.)Vfdata,))R17.)(2;.R19.))P,(>.R18.R17.)P,(53.R1:.R19.R18.R17.R5.R4.R3.)(6.$4.(7.(55.(56.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R1;.R1:.R19.)(57.&5.(8.&40.))(2>.&40.+1=318.)(2>.&20.=)(1;.(8.&40.))R6.(58.$4.))R5.)(4:.R19.))")
(* [comment removed for export] *).
      Proof.
        induction fuel as [|fuel IH]; intros buf len cap k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 m mo h Hfuel Hlc LI.
        { destruct LI. lia. }
        pose proof SPlo as Hlo. pose proof SPhi as Hhi.
        destruct LI as [D HH HD CR HT MK FS FDSq BY WR LEN COK BR].
        pose proof (cap_ok_bounds cap COK) as CB.
        dpose BR as (BR1 & BR2 & BR3 & BR4 & BR5). rewrite (U_alloc_ceiling_eq sp0 Hvsp) in BR4.
        cbn [hl_img_lo hl_img_hi U_layout] in BR5.
        pose proof MK as MK2; destruct MK2 as [Hh Hl].
        assert (K : forall w : Z, 1 <= w <= 65536 -> w <= cap - len ->
          aevtM usegs mo (fun c => realizes usegs c (LSHAPE cap))
            (MS (LREGS ra t0 t1 t2 (Z_to_bv 64 65536) a1 (Z_to_bv 64 w) a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 buf len cap)
                bvmap_empty (Z_to_bv 64 0x1d328) (Z_to_bv 32 0) None m (seg_rom usegs))).
        { intros w Hw1 Hw2. unfold LREGS.
          step. step. step. apply aevtM_done.       (* [comment removed for export] *)
          change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pc Mx rom).
          assert (WIN : forall a : word, bv_unsigned sp0 - 8388608 <= bv_unsigned a < bv_unsigned sp0 -> wview usegs m a <> None).
          { intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply (di_win m D). lia. }
          (* [comment removed for export] *)
          assert (BOK : store_ok usegs m (Z_to_bv 64 0x4cf69) (Z.to_nat w) = true).
          { apply store_ok_data; rewrite u_small by lia; lia. }
          refine (read_file_call sp0 mo Hvsp Hh Hl _ m WIN _ _ _ _ 0x4cf69 w path (Z_to_bv 64 len) fdata
                    _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) BOK _ _ _ _);
            [ norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity
            | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity
            | rewrite FDSq; apply FDS_lookup3 | rewrite FS; exact Hfs | ].
          intros a1' a2' a3' a4' a5' a6' a7'. norm_getr.
          ddestruct (read_bs fdata len w ltac:(lia) ltac:(lia) ltac:(lia)) as (NB1 & NB2 & APP).
          set (bs := file_read fdata (Z_to_bv 64 len) (Z_to_bv 64 w)) in *.
          set (nb := Z.of_nat (length bs)) in *.
          change (len_word bs) with (Z_to_bv 64 nb).
          rewrite zbv_add. rewrite FDSq.
          change (fd_insert (FDS (Z_to_bv 64 len)) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 (len + nb)))) with (FDS (Z_to_bv 64 (len + nb))).
          set (mo1 := with_fds (FDS (Z_to_bv 64 (len + nb))) mo).
          (* [comment removed for export] *)
          set (m1 := write_to_mem (write_to_mem m (wa (bv_unsigned sp0 - 136)) (le8 (Z_to_bv 64 0x1d334))) (wa 0x4cf69) bs).
          assert (MK1 : MOK mo1) by (apply MOK_with_fds; exact MK).
          assert (FS1 : m_fs mo1 = fs0) by exact FS.
          assert (FDS1 : m_fds mo1 = FDS (Z_to_bv 64 (len + nb))) by reflexivity.
          pose proof (length_le8 (Z_to_bv 64 0x1d334)) as L8.
          assert (HH1 : HEAP usegs (U_layout sp0) HI h [(buf, cap)] m1 mo1).
          { apply (heap_mo usegs (U_layout sp0) HI h [(buf, cap)] m1 mo mo1); [| reflexivity | reflexivity | reflexivity].
            subst m1. eapply (heap_write usegs (U_layout sp0) HI) with (SP := bv_unsigned sp0 - 8388608);
              [ eapply (heap_write usegs (U_layout sp0) HI) with (SP := bv_unsigned sp0 - 8388608);
                [ exact HH | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia
                | apply client_wrange_stack; [lia | rewrite L8, HT; cbn; lia] | lia | rewrite L8; lia ]
              | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia
              | intros a Ha; right; left; cbn [hl_data_lo hl_data_hi hl_static U_layout]; unfold U_static; lia
              | lia | lia ]. }
          assert (HD1 : DRV k h mo1) by (eapply DRVMO; [exact HD | reflexivity | reflexivity | reflexivity | reflexivity]).
          assert (AG1 : forall x : Z, 0 <= x < 2 ^ 64 -> ~ (bv_unsigned sp0 - 8388608 <= x < bv_unsigned sp0 - 128) -> ~ (0 <= x < 0) ->
                        ~ (0x5d024 <= x < 0x5d028) -> ~ (0x4cf69 <= x < 0x5cf69) -> m1 (wa x) = m (wa x)).
          { intros x H1 H2 H3 H4 H5. subst m1. rewrite write_other by lia. apply write_other; rewrite ?L8; lia. }
          assert (GR1 : mem_grows m m1) by (subst m1; eapply mem_grows_trans; apply write_to_mem_grows).
          pose proof (dinv_agree m m1 0 0 D AG1 GR1 ltac:(lia)) as D1.
          assert (BY1 : bytes_at usegs m1 buf (firstn (Z.to_nat len) fdata)).
          { subst m1. apply bytes_at_write_other; [apply bytes_at_write_other; [exact BY | lia | rewrite L8; lia | rewrite firstn_length; lia] | lia | lia | rewrite firstn_length; lia]. }
          assert (ST1 : bytes_at usegs m1 0x4cf69 bs) by (subst m1; apply bytes_at_write_same; lia).
          assert (WR1 : wr_at usegs m1 buf cap) by (subst m1; apply wr_at_write; apply wr_at_write; exact WR).
          clearbody m1.
          (* [comment removed for export] *)
          assert (C0 : bv_lts (Z_to_bv 64 nb) (Z_to_bv 64 0) = false).
          { rewrite bv_lts_zero_r. rewrite u_small by lia. apply Z.leb_gt. lia. }
          apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). step. rewrite C0.           (* [comment removed for export] *)
          step.                                       (* [comment removed for export] *)
          step.                                       (* [comment removed for export] *)
          destruct (Z.eq_dec nb 0) as [NB0|NB0].
          - (* [comment removed for export] *)
            ifc false. apply aevtM_done.
            assert (LENF : len = Z.of_nat (length fdata)) by lia.
            destruct k as [|k']. { exfalso. rewrite Z.pow_0_r in CR. lia. }
            rewrite (LSHAPE_body cap) by lia.
            rewrite NB0. replace (Z_to_bv 64 len) with (Z_to_bv 64 (Z.of_nat (length fdata)) : word) by (f_equal; lia).
            apply (AFTER buf cap k' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 mo1 h); [| lia].
            rewrite NB0, Z.add_0_r in FDS1. rewrite LENF in FDS1, BY1.
            split; try assumption. lia.
          - (* [comment removed for export] *)
            ifc true.
            step.                                     (* [comment removed for export] *)
            step. step.                               (* [comment removed for export] *)
            step.                                     (* [comment removed for export] *)
            apply aevtM_done.
            assert (MC : mcH m1 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 0x4cf69) nb bs).
            { split.
              - lia.
              - lia.
              - pose proof (bytes_at_rdn usegs m1 0x4cf69 bs 0 (length bs) ST1 ltac:(lia)) as RD.
                rewrite Z.add_0_r in RD. unfold wa in RD. rewrite skipn_O, firstn_all in RD. exact RD.
              - pose proof (wr_at_store_ok usegs m1 buf cap len (length bs) WR1 ltac:(lia) ltac:(lia)) as SO. exact SO.
              - rewrite !u_small by lia. lia.
              - rewrite u_small by lia. lia.
              - rewrite u_small by lia. lia. }
            change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pc Mx rom).
            pose proof MK1 as MK3; destruct MK3 as [Hh1 Hl1].
            lazymatch goal with |- realizes _ (mkCfg (mkst ?R _ _ _) _) _ =>
              destruct (ref_memcpy m1 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 0x4cf69) nb bs (seg_rom usegs) MC R (Z_to_bv 64 0x1d2cc)
                          ltac:(apply ret_ok_even; reflexivity)
                          ltac:(norm_getr; reflexivity) ltac:(norm_getr; reflexivity) ltac:(norm_getr; reflexivity) ltac:(norm_getr; reflexivity))
                as (regs2 & RUN & KP)
            end.
            replace (Z_to_bv 64 289344 : word) with (289344%bv : word) by (apply bv_eq; vm_compute; reflexivity).
            eapply (rz_msteps usegs); [exact Hh1 | exact Hl1 | exact RUN |].
            apply (realizes_getr_ext usegs
                     (mkR (Z_to_bv 64 0x1d2cc) (Z_to_bv 64 (bv_unsigned sp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8)
                          (getr regs2 5) (getr regs2 6) (getr regs2 7) (Z_to_bv 64 2) (Z_to_bv 64 buf) (Z_to_bv 64 (buf + len))
                          (getr regs2 11) (getr regs2 12) (getr regs2 13) (getr regs2 14) (getr regs2 15) (getr regs2 16) (getr regs2 17)
                          (p1 sp0 a0s path envv) (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 0x4cf69) (Z_to_bv 64 nb)
                          (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                          (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31)) regs2).
            { intros r. pose proof (ridx_range r) as Hi. rewrite <- (ridx_roundtrip r). set (i := ridx r) in *. clearbody i.
              destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
                lazymatch goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
                  let rk := eval vm_compute in (Z.of_nat kk) in change (Z.of_nat kk) with rk end;
                unfold mkR; norm_getr;
                first [ reflexivity
                      | f_equal; apply bv_eq; reflexivity
                      | lazymatch goal with |- _ = getr _ ?r =>
                          rewrite (KP r ltac:(apply in_regs_dec; reflexivity)); norm_getr; reflexivity end
                      | unfold getr, w0; cbn; reflexivity ]. }
            change (@mkst PropExec.fx0 ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
            rewrite <- write_to_mem_wbytes. change (Z_to_bv 64 (buf + len)) with (wa (buf + len)) at 2.
            (* [comment removed for export] *)
            set (m2 := write_to_mem m1 (wa (buf + len)) bs).
            assert (HH2 : HEAP usegs (U_layout sp0) HI h [(buf, cap)] m2 mo1).
            { subst m2. eapply (heap_write usegs (U_layout sp0) HI) with (SP := bv_unsigned sp0 - 8388608);
                [ exact HH1 | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia
                | eapply client_wrange_block; [left; reflexivity | lia | lia] | lia | lia ]. }
            assert (AG2 : forall x : Z, 0 <= x < 2 ^ 64 -> ~ (bv_unsigned sp0 - 8388608 <= x < bv_unsigned sp0 - 128) -> ~ (buf <= x < buf + cap) ->
                          ~ (0x5d024 <= x < 0x5d028) -> ~ (0x4cf69 <= x < 0x5cf69) -> m2 (wa x) = m1 (wa x)).
            { intros x H1 H2 H3 H4 H5. subst m2. apply write_other; lia. }
            assert (GR2 : mem_grows m1 m2) by (subst m2; apply write_to_mem_grows).
            pose proof (dinv_agree m1 m2 buf (buf + cap) D1 AG2 GR2 ltac:(lia)) as D2.
            assert (BY2 : bytes_at usegs m2 buf (firstn (Z.to_nat (len + nb)) fdata)).
            { rewrite <- APP. subst m2. apply (proj2 (bytes_at_app _ _ _ _ _)). split.
              - apply bytes_at_write_other; [exact BY1 | lia | lia | rewrite firstn_length; lia].
              - rewrite firstn_length. replace (buf + Z.of_nat (Nat.min (Z.to_nat len) (length fdata))) with (buf + len) by lia.
                apply bytes_at_write_same; lia. }
            assert (WR2 : wr_at usegs m2 buf cap) by (subst m2; apply wr_at_write; exact WR1).
            clearbody m2. clear MC RUN KP.
            (* [comment removed for export] *)
            apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs).
            step.                                     (* [comment removed for export] *)
            step.                                     (* [comment removed for export] *)
            step.                                     (* [comment removed for export] *)
            destruct (Z.eq_dec (len + nb) cap) as [FULL|NOTFULL].
            + (* [comment removed for export] *)
              ifc true.
              replace (Z_to_bv 64 (nb + len)) with (Z_to_bv 64 cap : word) by (f_equal; lia).
              step.                                   (* [comment removed for export] *)
              step.                                   (* [comment removed for export] *)
              pose proof MK1 as MK2; destruct MK2 as [Hh1' Hl1'].
              assert (FD2 : fd_lookup (m_fds mo1) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite FDS1; apply FDS_lookup2).
              destruct (Z.eq_dec cap 67108864) as [CAPMAX|CAPLT].
              * (* [comment removed for export] *)
                replace (Z.shiftr (bv_unsigned (Z_to_bv 64 cap)) 26) with 1 by (rewrite CAPMAX; vm_compute; reflexivity).
                ifc true. apply aevtM_done.
                rewrite (LSHAPE_body cap) by lia.
                replace BODY with (t_die msg_refused (m_fs mo1)).
                2:{ unfold BODY, t_body. replace (MAX_INPUT <=? Z.of_nat (length fdata)) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; lia).
                    rewrite FS1. reflexivity. }
                change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pc Mx rom).
                eapply (refused_tail sp0 mo1 (bv_unsigned tid) Hvsp Hh1' Hl1' FD2);
                  [ norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | ].
                eapply dinv_tail_mem; [exact D2 | exact HH2].
              * (* [comment removed for export] *)
                replace (Z.shiftr (bv_unsigned (Z_to_bv 64 cap)) 26) with 0
                  by (rewrite u_small by lia; rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
                ifc false.
                step.                                 (* [comment removed for export] *)
                step.                                 (* [comment removed for export] *)
                step.                                 (* [comment removed for export] *)
                apply aevtM_done.
                replace (Z.shiftl (bv_unsigned (Z_to_bv 64 cap)) 1) with (2 * cap) by (rewrite u_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
                destruct k as [|k']. { exfalso. rewrite Z.pow_0_r in CR. lia. }
                pose proof (cap_ok_double cap COK ltac:(lia)) as [COK2 CAP2].
                eapply rz_conseq; [ | apply (LSHAPE_grow cap); lia ].
                eapply (MRZ k') with (lo := bv_unsigned sp0 - 8388608) (n := 2 * cap);
                  [ exact HH2 | exact HD1
                  | rewrite u_small by lia; apply dinv_stk; exact D2
                  | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia
                  | rewrite u_small by lia; cbn [hl_stack U_layout]; lia
                  | exact (di_minv _ D2)
                  | reflexivity
                  | rewrite u_small by lia; rewrite HT; lia
                  | reflexivity
                  | lia
                  | apply OOM_nil
                  | apply LSHAPE_nil
                  | | ].
                -- (* [comment removed for export] *)
                   intros t0' t1' t2' a1q a2q a3q a4q a5q a6q a7q t3' t4' t5' t6' m' mo' h' MI' ST' MF HP HT' HH' MK'.
                   rewrite u_small in ST', HP by lia.
                   replace (ret_pc (Z_to_bv 64 0x1d2f4)) with (Z_to_bv 64 0x1d2f4 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
                   pose proof (dinv_heap [(buf, cap)] _ m2 m' D2 HP MI' ST' ltac:(lia) ltac:(rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia)) as D'.
                   apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). step. ifc true. apply aevtM_done.
                   unfold OOM. replace fs0 with (m_fs mo') by (rewrite (mo_frame_fs _ _ MF); exact FS1).
                   change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pc Mx rom).
                   pose proof MK' as MK3; destruct MK3 as [Hh' Hl'].
                   assert (FD2' : fd_lookup (m_fds mo') (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite (mo_frame_fds _ _ MF); exact FD2).
                   eapply (oom_tail sp0 mo' (bv_unsigned tid) Hvsp Hh' Hl' FD2');
                     [ left; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | ].
                   eapply dinv_tail_mem; [exact D' | exact HH'].
                -- (* [comment removed for export] *)
                   intros t0' t1' t2' a1q a2q a3q a4q a5q a6q a7q t3' t4' t5' t6' m' mo' h' A0 junk MI' ST' MF HP HT' BRn HH' MK' RW HD'.
                   specialize (HD' ltac:(right; unfold MMAP_THRESHOLD_Z; lia)).
                   rewrite u_small in ST', HP by lia.
                   replace (ret_pc (Z_to_bv 64 0x1d2f4)) with (Z_to_bv 64 0x1d2f4 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
                   pose proof (dinv_heap [(buf, cap)] _ m2 m' D2 HP MI' ST' ltac:(lia) ltac:(rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia)) as D'.
                   dpose BRn as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5). rewrite (U_alloc_ceiling_eq sp0 Hvsp) in BQ4.
                   cbn [hl_img_lo hl_img_hi U_layout] in BQ5.
                   pose proof (heap_blocks usegs (U_layout sp0) HI _ _ _ _ HH') as [_ APART]. cbn [blocks_apart] in APART.
                   destruct APART as [APART _]. specialize (APART buf cap ltac:(left; reflexivity)).
                   pose proof (heap_pres_bytes_at usegs (U_layout sp0) _ _ _ _ _ _ HP BY2
                                 ltac:(eapply client_range_block; [left; reflexivity | lia | rewrite firstn_length; lia])) as BY'.
                   apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs).
                   step. ifc false.                   (* [comment removed for export] *)
                   step.                              (* [comment removed for export] *)
                   step. ifc false.                   (* [comment removed for export] *)
                   step. step. step.                  (* [comment removed for export] *)
                   step.                              (* [comment removed for export] *)
                   apply aevtM_done.
                   (* [comment removed for export] *)
                   assert (MC : mcH m' (Z_to_bv 64 A0) (Z_to_bv 64 buf) cap (firstn (Z.to_nat cap) fdata)).
                   { split.
                     - lia.
                     - rewrite firstn_length. lia.
                     - rewrite firstn_length. replace (Nat.min (Z.to_nat cap) (length fdata)) with (Z.to_nat cap) by lia.
                       pose proof (bytes_at_rdn usegs m' buf _ 0 (Z.to_nat cap) BY' ltac:(rewrite firstn_length; lia)) as RD.
                       rewrite Z.add_0_r in RD. unfold wa in RD. etransitivity; [exact RD|]. rewrite skipn_O, FULL, firstn_firstn. f_equal. f_equal. lia.
                     - rewrite firstn_length. replace (Nat.min (Z.to_nat cap) (length fdata)) with (Z.to_nat cap) by lia.
                       destruct RW as [_ WRn]. cbn [cells_size csize Nat.add] in WRn.
                       pose proof (wr_at_store_ok usegs m' A0 _ 0 (Z.to_nat cap) WRn ltac:(lia) ltac:(lia)) as SO. rewrite Z.add_0_r in SO. exact SO.
                     - rewrite !u_small by lia. lia.
                     - rewrite u_small by lia. lia.
                     - rewrite u_small by lia. lia. }
                   change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pc Mx rom).
                   pose proof MK' as MK3; destruct MK3 as [Hh' Hl'].
                   lazymatch goal with |- realizes _ (mkCfg (mkst ?R _ _ _) _) _ =>
                     destruct (ref_memcpy m' (Z_to_bv 64 A0) (Z_to_bv 64 buf) cap (firstn (Z.to_nat cap) fdata) (seg_rom usegs) MC R (Z_to_bv 64 0x1d310)
                                 ltac:(apply ret_ok_even; reflexivity)
                                 ltac:(norm_getr; reflexivity) ltac:(norm_getr; reflexivity) ltac:(norm_getr; reflexivity) ltac:(norm_getr; reflexivity))
                       as (regs3 & RUN & KP)
                   end.
                   replace (Z_to_bv 64 289344 : word) with (289344%bv : word) by (apply bv_eq; vm_compute; reflexivity).
                   eapply (rz_msteps usegs); [exact Hh' | exact Hl' | exact RUN |].
                   apply (realizes_getr_ext usegs
                            (mkR (Z_to_bv 64 0x1d310) (Z_to_bv 64 (bv_unsigned sp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8)
                                 (getr regs3 5) (getr regs3 6) (getr regs3 7) (Z_to_bv 64 2) (Z_to_bv 64 A0) (Z_to_bv 64 A0)
                                 (getr regs3 11) (getr regs3 12) (getr regs3 13) (getr regs3 14) (getr regs3 15) (getr regs3 16) (getr regs3 17)
                                 (p1 sp0 a0s path envv) (Z_to_bv 64 cap) (Z_to_bv 64 3) (Z_to_bv 64 (2 * cap)) (Z_to_bv 64 0x4cf69) (Z_to_bv 64 buf)
                                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                 (getr regs3 28) (getr regs3 29) (getr regs3 30) (getr regs3 31)) regs3).
                   { intros r. pose proof (ridx_range r) as Hi. rewrite <- (ridx_roundtrip r). set (i := ridx r) in *. clearbody i.
                     destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
                       lazymatch goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
                         let rk := eval vm_compute in (Z.of_nat kk) in change (Z.of_nat kk) with rk end;
                       unfold mkR; norm_getr;
                       first [ reflexivity
                             | f_equal; apply bv_eq; reflexivity
                             | lazymatch goal with |- _ = getr _ ?r =>
                                 rewrite (KP r ltac:(apply in_regs_dec; reflexivity)); norm_getr; reflexivity end
                             | unfold getr, w0; cbn; reflexivity ]. }
                   change (@mkst PropExec.fx0 ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
                   rewrite <- write_to_mem_wbytes. change (Z_to_bv 64 A0) with (wa A0) at 3.
                   set (m3 := write_to_mem m' (wa A0) (firstn (Z.to_nat cap) fdata)).
                   pose proof (firstn_length (Z.to_nat cap) fdata) as FL.
                   assert (HH3 : HEAP usegs (U_layout sp0) HI h' [(A0, 2 * cap); (buf, cap)] m3 mo').
                   { subst m3. eapply (heap_write usegs (U_layout sp0) HI) with (SP := bv_unsigned sp0 - 8388608);
                       [ exact HH' | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia
                       | eapply client_wrange_block; [left; reflexivity | lia | rewrite FL; lia] | lia | rewrite FL; lia ]. }
                   assert (AG3 : forall x : Z, 0 <= x < 2 ^ 64 -> ~ (bv_unsigned sp0 - 8388608 <= x < bv_unsigned sp0 - 128) -> ~ (A0 <= x < A0 + 2 * cap) ->
                        ~ (0x5d024 <= x < 0x5d028) -> ~ (0x4cf69 <= x < 0x5cf69) -> m3 (wa x) = m' (wa x)).
                   { intros x H1 H2 H3 H4 H5. subst m3. apply write_other; rewrite ?FL; lia. }
                   assert (GR3 : mem_grows m' m3) by (subst m3; apply write_to_mem_grows).
                   pose proof (dinv_agree m' m3 A0 (A0 + 2 * cap) D' AG3 GR3 ltac:(lia)) as D3.
                   assert (BY3 : bytes_at usegs m3 A0 (firstn (Z.to_nat cap) fdata)) by (subst m3; apply bytes_at_write_same; rewrite ?FL; lia).
                   assert (WR3 : wr_at usegs m3 A0 (2 * cap)).
                   { subst m3. apply wr_at_write. destruct RW as [_ WRn]. cbn [cells_size csize Nat.add] in WRn.
                     replace (2 * cap) with (Z.of_nat (Z.to_nat (2 * cap) + 0)) by lia. exact WRn. }
                   clearbody m3.
                   (* [comment removed for export] *)
                   apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). step. step.
                   eapply aevtM_cut.
                   { eapply (FREEC k' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 mo' h' [(A0, 2 * cap); (buf, cap)] buf cap (bv_unsigned sp0 - 8388608)
                             HH3 HD' ltac:(right; left; reflexivity));
                       [ rewrite u_small by lia; apply dinv_stk; exact D3
                       | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia
                       | rewrite u_small by lia; cbn [hl_stack U_layout]; lia
                       | exact (di_minv _ D3)
                       | reflexivity
                       | rewrite u_small by lia; rewrite HT', HT; lia
                       | reflexivity ]. }
                   intros ms4 mo4 PO.
                   ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m4 & mo4' & E4 & MI4 & ST4 & MF4 & HP4 & h4 & HT4 & HH4 & HD4).
                   injection E4; clear E4; intros Emo Ems. subst ms4 mo4'.
                   rewrite u_small in ST4, HP4 by lia. rewrite lb_remove_2 in HP4, HH4 by lia.
                   replace (ret_pc (Z_to_bv 64 0x1d318)) with (Z_to_bv 64 0x1d318 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
                   pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ HH4) as MK4.
                   apply aevtM_done.
                   apply (IH A0 cap (2 * cap) k' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 mo4 h4); [lia | lia |].
                   split.
                   ++ eapply (dinv_heap [(A0, 2 * cap)] _ m3 m4 D3 HP4 MI4 ST4); [lia | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia].
                   ++ exact HH4.
                   ++ exact HD4.
                   ++ rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia. lia.
                   ++ rewrite HT4, HT', HT. reflexivity.
                   ++ exact MK4.
                   ++ rewrite (mo_frame_fs _ _ MF4), (mo_frame_fs _ _ MF). exact FS1.
                   ++ rewrite (mo_frame_fds _ _ MF4), (mo_frame_fds _ _ MF), <- FULL. exact FDS1.
                   ++ eapply (heap_pres_bytes_at usegs (U_layout sp0)); [exact HP4 | exact BY3 | eapply client_range_block; [left; reflexivity | lia | rewrite FL; lia]].
                   ++ eapply (heap_pres_wr_at usegs (U_layout sp0)); [exact HP4 | exact WR3 | eapply client_range_block; [left; reflexivity | lia | lia]].
                   ++ lia.
                   ++ exact COK2.
                   ++ exact BRn.
            + (* [comment removed for export] *)
              ifc false. step. step. apply aevtM_done.
              replace (Z_to_bv 64 (nb + len)) with (Z_to_bv 64 (len + nb) : word) by (f_equal; lia).
              apply (IH buf (len + nb) cap k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 mo1 h); [lia | lia |].
              split; try assumption. lia. }
        (* [comment removed for export] *)
        unfold LREGS. apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs).
        step.                                         (* [comment removed for export] *)
        step.                                         (* [comment removed for export] *)
        step.                                         (* [comment removed for export] *)
        rewrite ?(u_small len), ?(u_small cap) by lia. try replace (cap + - len) with (cap - len) by lia.
        destruct (Z.lt_ge_cases (cap - len) 65536).
        - ifc true. apply (K (cap - len)); lia.
        - ifc false. step. apply (K 65536); lia.
      Qed.
      Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

      #[using="Type"] Lemma LSHAPE_absorb : forall cap, t_eq (t_alt2 OOM (LSHAPE cap)) (t_alt2 OOM BODY).
      Proof. intros cap. unfold LSHAPE. destruct (_ && _)%bool; [apply t_alt2_absorb | apply t_eq_refl]. Qed.

      (* [comment removed for export] *)
      Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L10287183753.55L10645107738.90L18878088489.84L18878136745.79L18926662313.90L20948626091.84L20948708907.79L25322863131.79L25322940633.55L25322946203.84L29063123978.55L31093872373.90L40039506795.55L42571139497.79L42571222313.84L53517157525.90L55555927403.90L57488796975.90L63938289472.90L67905917405.5500000500C00H00M00U00Z00_00n01=01L01Q01j01o02402902A02M02[02c02hS3sp0S3sp05fdata2A0S3sp0S3sp0S3sp02A0S3sp0S3sp0S3sp04SPlo4SPhiS3sp04SPlo4SPhiS3sp04SPlo4SPhiS3sp0S3sp04SPlo3Hhi2A03BR13BR4S3sp0S3sp0S3sp0S3sp02A0S3sp02A03BR1S3sp05fdata2A0S3sp02A0S3sp0". (* [comment removed for export] *)
      #[using="rd regs0 Hvsp Htid ME SPlo SPhi HI HSTAT DRV NS MRZ FREEC DRVMO HINIT Hfs AFTER"] Lemma file_kont_core : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "(5:.VAMB,VLM,Vsp0,Va0s,Vpath,Venvv,Vtid,Vmem0,Vbrk,Vmbase,Vfs0,Vstdin0,(4<.Vpath,(2>.&40.=))(5;.Vfdata,Vfs0,))")
(* [comment removed for export] *).
      Proof.
        intros t1 t2 a12 t3 t4 t5 t6 M CM.
        pose proof (dinv_cut M CM) as D. pose proof (dinv_stk M D) as ST. pose proof (di_minv M D) as MI.
        ddestruct (HINIT M (FdFile path (Z_to_bv 64 0)) CM) as (h & HH & HT & HD & HNS).
        pose proof (model1g_MOK (FdFile path (Z_to_bv 64 0))) as MK.
        pose proof SPlo as Hlo. pose proof SPhi as Hhi.
        unfold t_opened. fold OOM. fold BODY.
        (* [comment removed for export] *)
        apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). unfold cut_regs, pathp.
        step. if_false. step. step. step. step.
        apply aevtM_done.
        eapply rz_conseq; [ | apply (LSHAPE_absorb 65536) ].
        eapply (MRZ 13%nat); try eassumption.
        - rewrite u_small by lia. exact ST.
        - rewrite (U_alloc_ceiling_eq sp0 Hvsp). lia.
        - rewrite u_small by lia. cbn [hl_stack U_layout]. lia.
        - reflexivity.
        - rewrite u_small by lia. rewrite HT. lia.
        - reflexivity.
        - lia.
        - apply OOM_nil.
        - apply LSHAPE_nil.
        - (* [comment removed for export] *)
          intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' h' MI' ST' MF HP HT' HH' MK'.
          rewrite u_small in ST', HP by lia.
          replace (ret_pc (Z_to_bv 64 0x1d2a0)) with (Z_to_bv 64 0x1d2a0 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
          pose proof (dinv_heap [] _ M m' D HP MI' ST' ltac:(lia) ltac:(rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia)) as D'.
          apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). step. if_true. apply aevtM_done.
          unfold OOM. replace fs0 with (m_fs mo') by (rewrite (mo_frame_fs _ _ MF); reflexivity).
          change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pc Mx rom).
          pose proof MK' as MK2; destruct MK2 as [Hh' Hl'].
          assert (FD2 : fd_lookup (m_fds mo') (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite (mo_frame_fds _ _ MF); reflexivity).
          eapply (oom_tail sp0 mo' (bv_unsigned tid) Hvsp Hh' Hl' FD2);
            [ right; reflexivity | reflexivity | reflexivity | reflexivity | eapply dinv_tail_mem; eauto ].
        - (* [comment removed for export] *)
          intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' h' A0 junk MI' ST' MF HP HT' BR HH' MK' RW HD'.
          specialize (HD' ltac:(left; split; [reflexivity | exact HNS])).
          rewrite u_small in ST', HP by lia.
          replace (ret_pc (Z_to_bv 64 0x1d2a0)) with (Z_to_bv 64 0x1d2a0 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
          pose proof (dinv_heap [] _ M m' D HP MI' ST' ltac:(lia) ltac:(rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia)) as D'.
          dpose BR as (BR1 & BR2 & BR3 & BR4 & BR5). rewrite (U_alloc_ceiling_eq sp0 Hvsp) in BR4.
          apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs).
          step. ifc false.                 (* [comment removed for export] *)
          step. step.                      (* [comment removed for export] *)
          step. step.                      (* [comment removed for export] *)
          step. if_true.                   (* [comment removed for export] *)
          step. step.                      (* [comment removed for export] *)
          apply aevtM_done.
          apply (read_loop (S (length fdata)) A0 0 65536 13%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' mo' h'); [lia | lia |].
          split.
          + exact D'.
          + exact HH'.
          + exact HD'.
          + apply Z.leb_le. vm_compute. reflexivity.
          + rewrite HT', HT. reflexivity.
          + exact MK'.
          + rewrite (mo_frame_fs _ _ MF). reflexivity.
          + rewrite (mo_frame_fds _ _ MF). reflexivity.
          + cbn [Z.to_nat firstn]. apply bytes_at_nil. lia.
          + destruct RW as [_ WRn]. cbn [cells_size csize Nat.add] in WRn. exact WRn.
          + lia.
          + exists 16. split; [lia | reflexivity].
          + exact BR.
      Qed.
      Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    End Loop.
  End File.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00O0@L10287183753.53 L1080386751.92  L18284857387.91 L18401096995.91 L18878088489.82 L18878136745.77 L19613286045.92 L19614366794.92 L20948626091.82 L20948708907.77 L21690283217.102L21692366833.102L22700267513.106L25322863131.77 L25322940633.53 L25322946203.82 L29063123978.53 L31044149123.92 L31096007531.87 L34140740681.92 L40039506795.53 L42571139497.77 L42571222313.82 L43068839414.92 L52108169754.109L53519235339.87 L55553921269.87 L56759158153.109L56868372720.91 L67905917405.53 L7468169588.109 00000500B00J00R00W00\00]00e00j00o01701?01L01[01j02902>02F02_02l03103603;03<03I03Q03]03j04204704DS3sp0S3sp02A01a2HaS3sp02A0S3sp02A0S3sp0S3sp0FS3sp02A0S3sp0S3sp0S3sp02A0S3sp02A0S3sp02A01a2HaS3sp04SPlo4SPhiS3sp04SPlo4SPhiS3sp04SPlo4SPhiS3sp0S3sp02A0S3sp04SPlo3Hhi2A03BR13BR4S3sp04SPlo2A0S3sp0S3sp0S3sp0FS3sp02A01a2H2S3sp02A0S3sp02A03BR1S3sp02A01a2H1S3sp02A0S3sp0S3sp02A01a2H4". (* [comment removed for export] *)
  #[using="rd regs0 Hva Hve Hvsp Htid ME SPlo SPhi HI HSTAT DRV NS MRZ HINIT"] Theorem dir_kont : ltac2:(CDefT.buildp (gd_tbl_P_main_file ()) "P,(10.(12.(8.&8.))Vpath,$5<.)(5:.VAMB,VLM,Vsp0,Va0s,Vpath,Venvv,Vtid,Vmem0,Vbrk,Vmbase,Vfs0,Vstdin0,$5=.(5>.$5<.Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros Hdot t1 t2 a12 t3 t4 t5 t6 M CM.
    pose proof (dinv_cut M CM) as D. pose proof (dinv_stk M D) as ST. pose proof (di_minv M D) as MI.
    ddestruct (HINIT M FdDir CM) as (h & HH & HT & HD & HNS).
    pose proof (model1g_MOK FdDir) as MK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    unfold t_opened_dir.
    (* [comment removed for export] *)
    apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). unfold cut_regs, pathp.
    step. if_false. step. step. step. step.
    apply aevtM_done.
    eapply (MRZ 13%nat); try eassumption.
    - rewrite u_small by lia. exact ST.
    - rewrite (U_alloc_ceiling_eq sp0 Hvsp). lia.
    - rewrite u_small by lia. cbn [hl_stack U_layout]. lia.
    - reflexivity.
    - rewrite u_small by lia. rewrite HT. lia.
    - reflexivity.
    - lia.
    - apply t_die_nil'.
    - apply t_die_nil'.
    - (* [comment removed for export] *)
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' h' MI' ST' MF HP HT' HH' MK'.
      rewrite u_small in ST', HP by lia.
      replace (ret_pc (Z_to_bv 64 0x1d2a0)) with (Z_to_bv 64 0x1d2a0 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      pose proof (dinv_heap [] _ M m' D HP MI' ST' ltac:(lia) ltac:(rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia)) as D'.
      apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). step. if_true. apply aevtM_done.
      replace fs0 with (m_fs mo') by (rewrite (mo_frame_fs _ _ MF); reflexivity).
      change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pc Mx rom).
      pose proof MK' as MK2; destruct MK2 as [Hh' Hl'].
      assert (FD2 : fd_lookup (m_fds mo') (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite (mo_frame_fds _ _ MF); reflexivity).
      eapply (oom_tail sp0 mo' (bv_unsigned tid) Hvsp Hh' Hl' FD2);
        [ right; reflexivity | reflexivity | reflexivity | reflexivity | eapply dinv_tail_mem; eauto ].
    - (* [comment removed for export] *)
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' h' A0 junk MI' ST' MF HP HT' BR HH' MK' RW HD'.
      rewrite u_small in ST', HP by lia.
      replace (ret_pc (Z_to_bv 64 0x1d2a0)) with (Z_to_bv 64 0x1d2a0 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      pose proof (dinv_heap [] _ M m' D HP MI' ST' ltac:(lia) ltac:(rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia)) as D'.
      ddestruct BR as (BR1 & BR2 & BR3 & BR4 & BR5). rewrite (U_alloc_ceiling_eq sp0 Hvsp) in BR4.
      apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs).
      assert (KA0 : bv_eqb (Z_to_bv 64 A0) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !u_small by lia; apply Z.eqb_neq; lia).
      step. rewrite KA0. cbv iota.      (* [comment removed for export] *)
      step. step.                      (* [comment removed for export] *)
      step. step.                      (* [comment removed for export] *)
      step. if_true.                   (* [comment removed for export] *)
      step. step.                      (* [comment removed for export] *)
      step. step. step. if_false.      (* [comment removed for export] *)
      step. step. step. step.          (* [comment removed for export] *)
      apply aevtM_done.
      (* [comment removed for export] *)
      change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pc Mx rom).
      pose proof MK' as MK2; destruct MK2 as [Hh' Hl'].
      assert (WIN' : forall a : word, bv_unsigned sp0 - 8388608 <= bv_unsigned a < bv_unsigned sp0 -> wview usegs m' a <> None).
      { intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply (di_win m' D'). lia. }
      assert (BOK : store_ok usegs m' (Z_to_bv 64 0x4cf69) (Z.to_nat 65536) = true).
      { apply store_ok_data; rewrite u_small by lia; lia. }
      eapply (read_dir_call sp0 mo' Hvsp Hh' Hl'); try exact WIN'; try reflexivity; try exact BOK; try lia.
      { rewrite (mo_frame_fds _ _ MF). reflexivity. }
      intros a1 a2 a3 a4 a5 a6 a7 M' AG GR. norm_getr.
      pose proof (dinv_agree m' M' 0 0 D' ltac:(intros a H1 H2 H3 H4 H5; pose proof (AG (wa a)) as E; unfold wa in E; rewrite u_small in E by lia; apply E; lia) GR ltac:(right; lia)) as D2.
      (* [comment removed for export] *)
      apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). step. if_true. apply aevtM_done.
      replace fs0 with (m_fs mo') by (rewrite (mo_frame_fs _ _ MF); reflexivity).
      change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pc Mx rom).
      subst path.
      assert (FD2 : fd_lookup (m_fds mo') (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite (mo_frame_fds _ _ MF); reflexivity).
      eapply (dir_tail sp0 mo' (bv_unsigned tid) Hvsp Hh' Hl' FD2 a0s envv tid rd regs0 mem0);
        [ exact Hva | exact Hve | exact Htid | exact ME
        | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity
        | eapply (tail_mem_agree m' M' 0 0); [eapply dinv_tail_mem; [exact D' | exact HH']
                                              | intros a H1 H2 H3 H4 H5; pose proof (AG (wa a)) as E; unfold wa in E; rewrite u_small in E by lia; apply E; lia
                                              | exact GR | right; lia] | ].
      intros a Ha. pose proof (di_above M' D2 a) as E. cbn [outside] in E. apply E. pose proof (u64_range a). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Driver.
