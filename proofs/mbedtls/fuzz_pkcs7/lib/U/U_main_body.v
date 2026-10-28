(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt AStep HeapIface HeapRz RegsExt Shape ZBridge Statics Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_layout.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb ShapeLaws StoreOk SymExec2 SymExec2Sound SymDriveX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import MemcpyLib Hoare CatExec StepTac LibTail.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX Cells Mem Step Bytes Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec TopContract SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Frame Asn1AuxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_img U_startup U_main_entry U_main_open U_main_cut U_cutkit U_tailkit U_readcall U_fwrite_err U_printf1 U_printfN U_exit_base U_exit_main U_exitkit U_memcpy_base U_memcpy U_main_file.
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
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_main_body () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.lor"; "stdpp.bitvector.definitions.bv_unsigned"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Stdlib.ZArith.BinInt.Z.shiftl"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.sxb"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.zxb"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_layout.U_layout"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.AgentSubmission.U.U_exit_base.file_clean"; "RocqVerifyHarness.AgentSubmission.U.U_printf1.stdout_buffered"; "Body.stdout_state"; "Body.fin_mem"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.U.U_exitkit.exit_mem"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.W"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_exit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.exit_code"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_fp"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.zero_lines"; "Body.out_pristine"; "Body.out_pend"; "Body.bmem"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_wf"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Statics.img_bytes_b"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_bytes"; "Corelib.Init.Datatypes.true"; "Body.atx"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell_at"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.csize"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cbytes"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Body.TRF"; "Body.status"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_short"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_overrun"; "RocqVerifyHarness.AgentSubmission.U.U_main_file.dinv"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_die"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Peano.lt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "Corelib.Lists.ListDef.nth"; "RocqVerifyHarness.AgentSubmission.U.U_printfN.pn_mem"; "RocqVerifyHarness.AgentSubmission.U.U_fwrite_err.fw_mem"; "Body.PLoop.PL"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_P"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "Body.CALLS"; "Body.SUCC"; "Corelib.Init.Datatypes.S"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_alt2"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Body.TAIL"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"].


Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L11029985341.4 L40068201139.4 L50038617690.7 L52613109795.21L5367510356.21 L56122408125.4 L56321275688.35L63374408857.7 00000100800E00U00g00h01j027SS2b02R0S2b02b12B02B1S2b02b12B02R02B1S2b02b12B02B11r2H0SS2b02b12B02B11q1r2r21H2H02q02r02H42H52q12r12H93H102q23H143H152R11nS2b02b12B02B1". (* [comment removed for export] *)
Lemma hdr_cfglen : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pb0,(0.&8.)Pb1,(0.&8.)(1.$2.(3.(4.&40.(5.&40.(6.(4.&40.(5.&40.(7.(4.&40.(8.R1.))+39.)))+31.)))(4.&40.(9.R2.)))(:.(4.&8.R2.)(;.+100.(<.(4.&8.R1.)+80.))))")
(* [comment removed for export] *).
Proof.
  intros b0 b1.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. unfold bv_modulus in R0, R1. cbn in R0, R1.
  unfold zxb. rewrite (SX2S.u_small (bv_unsigned b0)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite sxb_unsigned.
  set (B1 := bv_unsigned b1) in *. set (B0 := bv_unsigned b0) in *.
  assert (E : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 ((if B1 <? 128 then B1 else B1 + 2 ^ 64 - 256) * 2 ^ 57)) / 2 ^ 49)) = (B1 mod 128) * 256).
  { rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    destruct (Z.ltb_spec0 B1 128); Z.div_mod_to_equations; lia. }
  rewrite E. replace (B1 mod 128 * 256) with (Z.shiftl (B1 mod 128) 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm. rewrite lor_shiftl8_add by (Z.div_mod_to_equations; lia). reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59913653220.1800000OS2B02B11H1q1r2H12H22q02r02H62H7". (* [comment removed for export] *)
Lemma cfg_mod : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "PB0,$2.PB1,$2.P,(=.(>.=R2.)(?.R2.+100.))P,(=.(>.=R2.)(?.R2.+100.))(1.$2.(<.(:.R4.(;.+100.R3.))+8000.)(:.R4.(;.+100.(<.R3.+80.))))")
(* [comment removed for export] *).
Proof. intros. Z.div_mod_to_equations. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac ifc2 b :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then _ else _) _ _ _ _) =>
      let H := fresh "C" in
      assert (H : c = b) by (rewrite ?bv_lts_zero_r, ?bv_lts_zero_l; unfold_cond; rewrite ?u_small by lia; fold_lit_ux; solve_cond_rec);
      rewrite H; clear H
  end.

(* [comment removed for export] *)
Ltac mem_after_store ::=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) (seg_rom ?segs)) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.


Ltac mem_after_store_opt ::=
  lazymatch goal with
  | |- ?EVHD (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) (seg_rom ?segs)) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac   (* [comment removed for export] *)
      end
  | _ => idtac
  end.


(* [comment removed for export] *)
Ltac lit_store :=
  match goal with
  | |- _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (Mem.le8 (Z_to_bv 64 z)); mem_after_store
  | |- _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (Mem.le4 (Z_to_bv 64 z)); mem_after_store
  | |- _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
      change (Z_to_le_bytes 1 z) with ([Z_to_bv 8 z]); mem_after_store
  | _ => idtac
  end.

Section Body.
  Context {AMB : Amb}.
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

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* [comment removed for export] *)
  Variable HI : heap_iface usegs (U_layout sp0).
  Hypothesis HSTAT : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Ph,(10.$11.(12.Vsp0,)VHI,)PLB,(13.$14.)Pm,P,(0.&40.)(15.(0.&8.))Pmo,$16.P,(17.$11.(12.Vsp0,)VHI,R4.R3.R2.R1.)(=.(18.$11.R3.+7=353.(19.$1:.(1;.(5.&8.=))(1<.$1:.)))(=.(1=.(0.&40.)Lg,(0.&40.)(18.$11.R4.+7=330.(19.$1:.(1>.R1.)(1<.$1:.))))(18.$11.R3.+4;<=8.(19.$1:.(1>.(5.&40.+7=330.))(1<.$1:.)))))")
(* [comment removed for export] *).
  Variable DRV : nat -> HST usegs (U_layout sp0) HI -> Model -> Prop.
  Variable NS : HST usegs (U_layout sp0) HI -> Prop.
  Hypothesis MRZ : malloc_rz_stmt usegs (U_layout sp0) HI DRV NS.
  Hypothesis FREEC : free_c_stmt usegs (U_layout sp0) HI DRV.
  Hypothesis DRVMO : drv_mo_stmt usegs (U_layout sp0) HI DRV.
  (* [comment removed for export] *)
  Variable SI : sinv (U_layout sp0).
  Hypothesis SIFP : forall a : Z, ~ outside (si_fp SI) a -> 0x5cf90 <= a < 0x5cff8.
  Hypothesis FUZZ : fuzz_entry_stmt usegs (U_layout sp0) HI SI 0x1d6ec.

  Variable fdata : list byte.
  Hypothesis Hfs : fs_lookup fs0 path = Some fdata.

  Local Notation DINV := (dinv sp0 tid mem0).
  Local Notation DAG := (dinv_agree sp0 tid mem0 Hvsp Htid).
  Local Notation DHP := (dinv_heap sp0 tid mem0 Hvsp).
  Local Notation DTM := (dinv_tail_mem sp0 tid mem0 Hvsp Htid HI HSTAT).
  Local Notation DFW := (dinv_fw_mem sp0 tid mem0 Hvsp Htid HI HSTAT).
  Local Notation DSTK := (dinv_stk sp0 tid mem0 Hvsp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Inductive stdout_state (m : mem) : list byte -> Prop :=
  | SO_none : (forall a : Z, 0x4ce20 <= a < 0x4cf08 -> m (wa a) = None) -> stdout_state m []
  | SO_one : stdout_buffered m 0x7d798 -> stdout_state m []
  | SO_many : forall (wp : Z) (pending : list byte),
      stdout_buffered m wp -> 0x7d798 < wp <= 0x7db98 -> wp - 0x7d798 = Z.of_nat (length pending) ->
      rdn usegs m (Z_to_bv 64 0x7d798) (length pending) = Some pending -> stdout_state m pending.

  Record fin_mem (m : mem) : Prop := FIN_MEM {
    fm_win : forall a : Z, bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 -> wview usegs m (wa a) <> None;
    fm_frame : rw_cells usegs m (bv_unsigned sp0 - 120) (FRAME sp0);
    fm_minv : mem_inv usegs m;
    fm_statics : statics_ok usegs (U_layout sp0) m;
    fm_used2 : forall a : Z, 0x4ce18 <= a < 0x4ce20 -> m (wa a) = None;
    fm_used1 : forall a : Z, 0x4cf08 <= a < 0x4cf20 -> m (wa a) = None;
    fm_comp : forall a : Z, 0x4cf68 <= a < 0x4cf69 -> m (wa a) = None;
    fm_lock : forall a : Z, 0x7d328 <= a < 0x7d32c -> m (wa a) = None;
    fm_ofl : forall a : Z, 0x7d770 <= a < 0x7d788 -> m (wa a) = None;
    fm_tid : rw_cells usegs m 0x5d020 [C4 tid];
    fm_err : exists wp2 rp2, file_clean m 0x4cd30 wp2 rp2;
    fm_atexit : exists b : bool, atexit_st b m          (* [comment removed for export] *)
  }.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L53024458802.42L56765666148.4200000>00WS3sp01a1n1j2HjS3sp04SPlo1a1n2Ha2Hn1j2Hj". (* [comment removed for export] *)
  #[using="sp0 Hvsp SPlo"] Lemma rdn_agree_Z : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,Px,(0.&40.)(15.(0.&8.))Pm',Px,(0.&40.)(15.(0.&8.))Pa,$2.Pn,$1?.P,(>.=R2.)P,(>.(:.R3.(20.R2.))(21.+2.+40.))P,Px,$2.P,(=.(>.R5.R1.)(?.R1.(:.R5.(20.R4.))))(1.(15.(0.&8.))A1.R7.(22.R2.)A1.R8.(22.R2.))(1.(15.(13.(0.&8.)))(23.$11.R6.(5.&40.R5.)R4.)(23.$11.R7.(5.&40.R5.)R4.))")
(* [comment removed for export] *).
  Proof.
    intros m m' a n Ha Hn AG. symmetry. apply rdn_agree. intros j Hj. rewrite u_small by lia. symmetry. apply AG. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L20847619077.43L25282362416.43L29033508208.43L29509857135.45L37320873776.43L44228354885.43L49357285936.43L5255814692.43 L60273535557.43L603065413.43  L68294030789.43L7216262064.43 00000500:00?00I00N00S00X00Y00^00c00h00mS3sp0S3sp0S3sp0S3sp01x2HxS3sp0S3sp0S3sp0FS3sp0S3sp0S3sp0S3sp0". (* [comment removed for export] *)
  #[using="sp0 Hvsp SPlo"] Lemma file_clean_agree : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Pm',Px,(0.&40.)(15.(0.&8.))Pwp,(0.&40.)Prp,(0.&40.)P,(24.R4.+4<=30.R2.R1.)P,Px,$2.P,(=.(>.+4<=30.R1.)(?.R1.+4<>18.))(1.(15.(0.&8.))A1.R6.(22.R2.)A1.R7.(22.R2.))(24.R5.+4<=30.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    (intros m m' wp rp dd_H; ddestruct dd_H as (A & B & C & D & E); intros AG). unfold file_clean.
    rewrite !(rdn_agree_Z m m') by (first [lia | intros x Hx; apply AG; lia]). repeat split; assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0?L10151071941.49L11179650885.49L19230709957.49L21494513200.49L22720821317.49L23762612848.49L24992233111.49L27216442949.49L33543508272.49L34220940101.49L3447289264.49 L35245322693.49L38729142597.49L39554369200.49L44751581452.49L47576542575.51L50266169925.49L51590732208.49L5255814692.49 L54089389317.49L54098505008.49L57620467504.49L58286665157.49L66139111472.49L67149110960.49L939500080.49  00000500:00?00D00I00N00S00X00]00b00g00l01101601;01E01J01O01P01U01Z01_01d01i01n023S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp01x2HxS3sp0S3sp0FS3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0". (* [comment removed for export] *)
  #[using="sp0 Hvsp SPlo"] Lemma stdout_buffered_agree : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Pm',Px,(0.&40.)(15.(0.&8.))Pw,$2.P,(25.R3.R1.)P,Px,$2.P,(=.(>.+4<>20.R1.)(?.R1.+4<?08.))(1.(15.(0.&8.))A1.R5.(22.R2.)A1.R6.(22.R2.))(25.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros m m' w SB AG. destruct SB. split; rewrite (rdn_agree_Z m m') by (first [lia | intros x Hx; apply AG; lia]); assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L19764412655.45L35517592357.43L45825646418.43L46811946924.43L48167097588.43L5257911839.43 L53410765808.4000000S00g01A01N01l01m027S3sp04SPlo2wp7pending3Hwp4Hlen1x2HxS3sp02wp7pending3HwpS3sp04SPlo2wp7pending4HlenS3sp07pendingS3sp04SPlo2wp7pending3Hwp4HlenFS3sp01a2Ha". (* [comment removed for export] *)
  #[using="sp0 Hvsp SPlo"] Lemma stdout_state_agree : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Pm',Px,(0.&40.)(15.(0.&8.))Ppending,(13.(0.&8.))P,(26.R3.R1.)P,Px,$2.P,(=.(>.+4<>20.R1.)(?.R1.+4<?08.))(1.(15.(0.&8.))A1.R5.(22.R2.)A1.R6.(22.R2.))P,Px,$2.P,(=.(>.+7=798.R1.)(?.R1.+7=;98.))(1.(15.(0.&8.))A1.R6.(22.R2.)A1.R7.(22.R2.))(26.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros m m' pending SO AG1 AG2. destruct SO as [N1 | SB | wp pending SB Hwp Hlen RD].
    - apply SO_none. intros a Ha. rewrite AG1 by lia. apply N1. lia.
    - apply SO_one. eapply stdout_buffered_agree; eauto.
    - apply (SO_many m' wp pending); [eapply stdout_buffered_agree; eauto | lia | lia |].
      rewrite (rdn_agree_Z m m') by (first [lia | intros x Hx; apply AG2; lia]). exact RD.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L11705891568.56L1264665186.56 L1264665839.57 L1264665839.58 L16085729392.56L18302140630.56L18302143821.57L18302143821.58L19888265732.54L26913609127.57L32162264840.56L34467122463.57L45268348272.56L50720805552.56L54891425692.57L56765677501.57L5744833911.56 L59165595296.56L8559398896.56 00000:00D00N00X00b00l01601@01E01O01Y01c01m02702D02[02e02o039S3sp01a2HaS3sp01x2HxS3sp01x2HxS3sp01x2HxS3sp01a2HaS3sp01a2HaS3sp01x2HxS3sp01x2HxS3sp0S3sp01a2H1S3sp01a2HaS3sp01a2HaS3sp01a2HaS3sp01a2HaS3sp01a2Ha2H1S3sp04SPlo1H2H01a2Ha2H1S3sp01x2HxS3sp01a2HaS3sp01a2Ha". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma fin_mem_heap : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "PLB,(13.$14.)Pm,P,(0.&40.)(15.(0.&8.))Pm',P,(0.&40.)(15.(0.&8.))P,(27.R2.)P,(28.$11.(12.Vsp0,)R4.(29.(4.&40.Vsp0,)+80.)R3.R2.)P,(2:.$11.R3.)P,(2;.$11.R4.(29.(4.&40.Vsp0,)+800000.)(29.(4.&40.Vsp0,)+80.))(27.R5.)")
(* [comment removed for export] *).
  Proof.
    intros LB m m' FM HP MI' ST'. pose proof SPlo. pose proof SPhi. destruct FM as [W F MI SO U2 U1 CO LO OF TI ER AT].
    assert (AGD : forall x : Z, 0x48000 <= x < 0x7e000 -> ~ U_static x -> m' (wa x) = m (wa x)).
    { intros x Hx Hs. apply (proj1 (HP x ltac:(lia) ltac:(right; left; cbn [hl_data_lo hl_data_hi hl_static U_layout]; split; [lia| exact Hs]))). }
    split.
    - intros a Ha. destruct (Z.lt_ge_cases a (bv_unsigned sp0 - 128)).
      + apply (proj1 (proj2 (proj2 ST') a ltac:(lia))).
      + apply (proj2 (HP a ltac:(lia) ltac:(left; lia))). apply W. lia.
    - eapply heap_pres_rw_cells; [exact HP | exact F |]. apply client_range_stack. lia.
    - exact MI'.
    - eapply statics_ok_pres; eauto.
    - intros a Ha. rewrite AGD by (unfold U_static; lia). apply U2. lia.
    - intros a Ha. rewrite AGD by (unfold U_static; lia). apply U1. lia.
    - intros a Ha. rewrite AGD by (unfold U_static; lia). apply CO. lia.
    - intros a Ha. rewrite AGD by (unfold U_static; lia). apply LO. lia.
    - intros a Ha. rewrite AGD by (unfold U_static; lia). apply OF. lia.
    - eapply heap_pres_rw_cells; [exact HP | exact TI |]. intros a Ha. right; left.
      cbn [hl_data_lo hl_data_hi hl_static U_layout]. unfold U_static. cbn in Ha. lia.
    - ddestruct ER as (wp2 & rp2 & FC). dexists wp2, rp2. eapply file_clean_agree; [exact FC|]. intros x Hx. apply AGD; unfold U_static; lia.
    - destruct AT as [b AT]. exists b. eapply atexit_st_agree; [exact AT|]. intros x Hx. unfold atexit_fp in Hx. apply AGD; unfold U_static; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L1264665186.42 L1264665839.42 L18302143821.42L5744833911.42 00000:00D00N00XS3sp01x2HxS3sp01x2HxS3sp01x2HxS3sp01x2Hx". (* [comment removed for export] *)
  #[using="Hvsp SPlo"] Lemma stdout_state_heap : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "PLB,(13.$14.)Pm,P,(0.&40.)(15.(0.&8.))Pm',P,(0.&40.)(15.(0.&8.))Ppending,(13.(0.&8.))P,(26.R3.R1.)P,(28.$11.(12.Vsp0,)R5.(29.(4.&40.Vsp0,)+80.)R4.R3.)(26.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros LB m m' pending SO HP.
    assert (AGD : forall x : Z, 0x48000 <= x < 0x7e000 -> ~ U_static x -> m' (wa x) = m (wa x)).
    { intros x Hx Hs. apply (proj1 (HP x ltac:(lia) ltac:(right; left; cbn [hl_data_lo hl_data_hi hl_static U_layout]; split; [lia| exact Hs]))). }
    eapply stdout_state_agree; [exact SO | |]; intros x Hx; apply AGD; unfold U_static; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L10237765898.56L10667350673.56L1080380655.59 L10917014968.58L11401374120.58L11705891568.58L16085729392.58L16085739552.59L37082574059.57L37200440721.56L42554326666.56L45268348272.58L57476222986.56L59775472266.56L63057278225.56L66788315409.56L68706377326.58L68706383422.59L9550212712.58 00000500:00D00N00X00b00l01901G01L01Q01[01`01e01j01o02902C02MS3sp0S3sp0S3sp01a2HaS3sp01i2HiS3sp01i2HiS3sp01a2HaS3sp01a2HaS3sp01a2Ha2H1S3sp03tid4HtidS3sp0S3sp0S3sp01a2HaS3sp0S3sp0S3sp0S3sp0S3sp01a2HaS3sp01a2HaS3sp01i2Hi". (* [comment removed for export] *)
  #[using="Hvsp Htid SPlo SPhi HSTAT"] Lemma fin_exit_mem : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Ph,(10.$11.(12.Vsp0,)VHI,)PLB,(13.$14.)Pmo,$16.P,(27.R4.)P,(17.$11.(12.Vsp0,)VHI,R4.R3.R5.R2.)(2<.Vsp0,(4.&40.Vtid,)R6.)")
(* [comment removed for export] *).
  Proof.
    intros m h LB mo FM HH. pose proof SPlo. pose proof SPhi. destruct FM as [W F MI SO U2 U1 CO LO OF TI ER AT].
    ddestruct (HSTAT h LB m mo HH) as (NL & [canw CA] & GOT). ddestruct SO as (_ & _ & ST).
    cbn [hl_data_lo hl_data_hi hl_written U_layout] in ST. unfold U_written in ST.
    split.
    - intros a Ha. pose proof (u64_range a). rewrite <- (Z_to_bv_bv_unsigned a). apply W. lia.
    - intros a Ha. destruct (Z.lt_ge_cases a 0x48000); [apply mem_inv_text_none; [exact MI|lia] | apply ST; lia].
    - apply rw_cells_rdn8. exact GOT.
    - intros a Ha. apply ST; lia.
    - intros a Ha. apply U2. lia.
    - intros a Ha. apply U1. lia.
    - rewrite (rdn_none_img m 0x4cf68 1); [exact img_49818_1 | intros i Hi; apply CO; lia | lia | lia].
    - pose proof (rw_cells_rdn4 _ _ _ TI) as T. rewrite Z_to_bv_bv_unsigned. exact T.
    - pose proof Htid. lia.
    - rewrite (rdn_none_img m 0x7d328 4); [exact img_59c58_4 | intros i Hi; apply LO; lia | lia | lia].
    - exists canw. apply rw_cells_rdn8. exact CA.
    - apply rw_cells_rdn1. exact NL.
    - rewrite (rdn_none_img m 0x7d770 8); [exact img_5a0a0_8 | intros i Hi; apply OF; lia | lia | lia].
    - rewrite (rdn_none_img m 0x7d780 8); [exact img_5a0b0_8 | intros i Hi; apply OF; lia | lia | lia].
    - exact ER.
    - exact AT.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L24376346147.37L34467128655.39L64936856764.3700000:00D00NS3sp04SPloS3sp01a2HaS3sp04SPhi". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma fin_stk : forall m, fin_mem m -> stk usegs m (bv_unsigned sp0 - 8388608) (bv_unsigned sp0 - 128).
  Proof.
    intros m FM. pose proof SPlo. pose proof SPhi. apply stk_of_wview; [lia|lia|]. intros a Ha. apply (fm_win m FM). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L10338436541.102L16813669303.98 L18480231485.102L25322944647.98 L25324926630.74 L25620507197.102L26513423336.102L26949584158.102L29065136757.74 L29198511421.102L3198160829.102 L35519803416.109L36336689981.102L40041757972.74 L41183659698.103L45823663215.109L49618111410.102L59308844908.108L59449660688.105L61212989117.102L67908194210.74 L68357459133.10200000500:00?00N00]00b00g00l01101601;01O01T01Y01^02802=02N02c02h02m032S3sp0S3sp0S3sp0S3sp04SPlo4SPhiS3sp04SPlo4SPhiS3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp07pending2wp3HwpS3sp0S3sp0S3sp0S3sp04SPlo7pending2wp4HlenS3sp0S3sp02wp3Hwp4HlenS3sp04SPlo4code5HcodeS3sp0S3sp0S3sp0". (* [comment removed for export] *)
  #[using="Hvsp Htid SPlo SPhi HSTAT"] Theorem fin : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pcode,$2.Ppending,(13.(0.&8.))Pbuf,$2.Pcap,$2.PLB,(13.$14.)Pra,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(15.(0.&8.))Pmo,$16.Ph,(10.$11.(12.Vsp0,)VHI,)P,(17.$11.(12.Vsp0,)VHI,R1.R19.R3.R2.)P,(2=.(2>.$2.$2.)(2?.$2.$2.R1<.R1;.)R1:.)P,(1.$2.(30.$11.(12.Vsp0,)VHI,R3.)(4.&40.Vsp0,))P,(1.$31.(32.R5.)Vfs0,)P,(27.R7.)P,(26.R8.R21.)P,P,(33.(1.(13.(0.&8.))R22.(1<.(0.&8.))))(1.(15.$34.)(35.(36.R9.)(5.&40.+1.))(37.$34.(38.(5.&40.+1.))))P,(39.(1.$2.R24.=)(1.$2.R24.+2.))(3:.$11.(3;.(3<.(3=.R20.(5.&40.(29.(4.&40.Vsp0,)+80.))(5.&40.+10800.)(5.&40.+5=0<8.)R1?.R1>.R1=.(5.&40.R25.)(5.&40.R23.)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R?.R>.R=.R<.)(3>.&5.(0.&40.))(5.&40.+1=440.)(5.&20.=)(3?.(0.&40.))R;.(40.$11.))R:.)(41.(42.+1.R24.)(43.(44.R25.)Vfs0,)))")
(* [comment removed for export] *).
  Proof.
    intros code pending buf cap LB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 m mo h HH IN HT FS FM SO FD1 Hcode.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ HH) as MK.
    pose proof (fin_stk m FM) as ST.
    apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). step. step.
    eapply aevtM_cut.
    { eapply (heap_free usegs (U_layout sp0) HI) with (lo := bv_unsigned sp0 - 8388608);
        [ exact HH | exact IN
        | rewrite u_small by lia; exact ST
        | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia
        | rewrite u_small by lia; cbn [hl_stack U_layout]; lia
        | exact (fm_minv _ FM)
        | reflexivity
        | rewrite u_small by lia; rewrite HT; lia
        | reflexivity ]. }
    intros ms3 mo3 PO.
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m3 & mo3' & E3 & MI3 & ST3 & MF3 & HP3 & h3 & HT3 & HH3).
    injection E3; clear E3; intros Emo Ems. subst ms3 mo3'.
    rewrite u_small in ST3, HP3 by lia.
    replace (ret_pc (Z_to_bv 64 0x1d448)) with (Z_to_bv 64 0x1d448 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ HH3) as MK3.
    pose proof (fin_mem_heap _ m m3 FM HP3 MI3 ST3) as FM3.
    pose proof (stdout_state_heap _ m m3 pending SO HP3) as SO3.
    pose proof (fm_frame m3 FM3) as FR3. unfold FRAME in FR3.
    replace (bv_unsigned sp0 - 120) with (bv_unsigned sp0 - 128 + 8) in FR3 by lia.   (* [comment removed for export] *)
    step.                                   (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step.   (* [comment removed for export] *)
    step.                                   (* [comment removed for export] *)
    step.                                   (* [comment removed for export] *)
    apply aevtM_done.
    replace (bv_unsigned sp0 - 128 + 80) with (bv_unsigned sp0 - 48) by lia.
    rewrite <- (mo_frame_fs _ _ MF3) in FS. rewrite <- FS.
    change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pc Mx rom).
    pose proof MK3 as MK4; destruct MK4 as [Hh3 Hl3].
    pose proof (fin_exit_mem m3 h3 _ mo3 FM3 HH3) as XM.
    apply main_ret_exit_code; [lia|].
    destruct SO3 as [N1 | SB | wp pending SB Hwp Hlen RD].
    - eapply (exit_pre_nostdout sp0 mo3 (bv_unsigned tid) Hvsp Hh3 Hl3);
        [ norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | exact XM | ].
      intros a Ha. apply N1. exact Ha.
    - eapply (exit_pre_flushed sp0 mo3 (bv_unsigned tid) Hvsp Hh3 Hl3);
        [ norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | exact XM | exact SB ].
    - eapply (exit_pre_pending sp0 mo3 (bv_unsigned tid) Hvsp Hh3 Hl3);
        [ norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | exact XM | exact SB | lia | lia | exact RD | ].
      rewrite (mo_frame_fds _ _ MF3). apply FD1. intros E. subst pending. cbn in Hlen. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Record bmem (m : mem) : Prop := BMEM {
    bm_win : forall a : Z, bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 -> wview usegs m (wa a) <> None;
    bm_frame : rw_cells usegs m (bv_unsigned sp0 - 120) (FRAME sp0);
    bm_minv : mem_inv usegs m;
    bm_statics : statics_ok usegs (U_layout sp0) m;
    bm_err : forall a : Z, 0x4cd30 <= a < 0x4ce20 -> m (wa a) = None;
    bm_used1 : forall a : Z, 0x4cf08 <= a < 0x4cf20 -> m (wa a) = None;
    bm_comp : forall a : Z, 0x4cf68 <= a < 0x4cf69 -> m (wa a) = None;
    bm_lock : forall a : Z, 0x7d328 <= a < 0x7d32c -> m (wa a) = None;
    bm_ofl : forall a : Z, 0x7d770 <= a < 0x7d788 -> m (wa a) = None;
    bm_tid : rw_cells usegs m 0x5d020 [C4 tid]
  }.
  Definition out_pristine (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "(=.Pa,$2.P,(=.(>.+4<>20.R1.)(?.R1.+4<?08.))(1.(15.(0.&8.))A1.O1.(22.R2.)(3?.(0.&8.)))Pa,$2.P,(=.(>.+5<?90.R1.)(?.R1.+5<??8.))(1.(15.(0.&8.))A1.O1.(22.R2.)(3?.(0.&8.))))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Notation XFP := [(0x5cf90, 0x5cff8)].
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30021726115.3700000?S3sp02SI1a2Ha1H". (* [comment removed for export] *)
  #[using="SIFP"] Lemma nfp : forall a : Z, (a < 0x5cf90 \/ 0x5cff8 <= a) -> outside (si_fp SI) a.
  Proof. intros a Ha. destruct (outside_dec (si_fp SI) a) as [O|NO]; [exact O|]. pose proof (SIFP a NO). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010<L46260786.4200000:S3sp01a2Ho". (* [comment removed for export] *)
  #[using="SIFP"] Lemma hpx_fp : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "PLB,(13.$14.)PSP,$2.Pm,P,(0.&40.)(15.(0.&8.))Pm',P,(0.&40.)(15.(0.&8.))P,(45.$11.(12.Vsp0,)R4.R3.(46.(12.Vsp0,)VSI,)R2.R1.)(45.$11.(12.Vsp0,)R5.R4.(19.(2>.$2.$2.)(2?.$2.$2.+5<?90.+5<??8.)(1<.(2>.$2.$2.)))R3.R2.)")
(* [comment removed for export] *).
  Proof. intros LB SP m m' HP a Ha Hc Ho. apply HP; [exact Ha| exact Hc|]. apply nfp. cbn [outside] in Ho. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma hpx_of_pres : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "PLB,(13.$14.)PSP,$2.Pm,P,(0.&40.)(15.(0.&8.))Pm',P,(0.&40.)(15.(0.&8.))P,(28.$11.(12.Vsp0,)R4.R3.R2.R1.)(45.$11.(12.Vsp0,)R5.R4.(19.(2>.$2.$2.)(2?.$2.$2.+5<?90.+5<??8.)(1<.(2>.$2.$2.)))R3.R2.)")
(* [comment removed for export] *).
  Proof. intros. apply heap_presx_of_pres. assumption. Qed.
  #[using="SIFP"] Lemma si_of_out_pristine : forall m, out_pristine m -> si_P SI m.
  Proof. intros m [_ E]. apply (si_init SI). intros a Ha NO. apply E. exact (SIFP a NO). Qed.
  (* [comment removed for export] *)
  Definition out_pend (m : mem) (d : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "(=.(25.O2.(:.+7=798.(;.+2.O1.)))(=.(=.(>.=O1.)(>.O1.+8.))(1.(15.(13.(0.&8.)))(23.$11.O2.(5.&40.+7=798.)(47.(;.+2.O1.)))(37.(13.(0.&8.))(48.(47.O1.))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L14192962416.4700000:S3sp01a2Ha". (* [comment removed for export] *)
  #[using="Type"] Lemma bmem_fin : forall m, bmem m -> (exists b : bool, atexit_st b m) -> fin_mem m.
  Proof.
    intros m [W F MI SO ER U1 CO LO OF TI] AT. split; try assumption.
    - intros a Ha. apply ER. lia.
    - dexists (Z_to_bv 64 0), (Z_to_bv 64 0). apply stderr_pristine_clean. intros a Ha. apply ER. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L63350681072.4900000:S3sp01a2Ha". (* [comment removed for export] *)
  #[using="Type"] Lemma bmem_of_dinv : forall m, DINV m -> bmem m /\ out_pristine m.
  Proof.
    intros m [W F MI SO DM TI AB]. destruct DM as [DF DC DL DO DE]. split; [split; try assumption| split; [| exact DE]].
    - intros a Ha. apply DF. lia.
    - intros a Ha. apply DF. lia.
    - intros a Ha. apply DF. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L41773568036.3500000:S3sp01n2IH". (* [comment removed for export] *)
  #[using="sp0"] Lemma zero_lines_length : forall n, length (zero_lines n) = (2 * n)%nat.
  Proof. induction n as [|n IH]; [reflexivity|]. cbn [zero_lines length]. rewrite IH. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma zero_lines_snoc : forall n, zero_lines n ++ [Z_to_bv 8 48; Z_to_bv 8 10] = zero_lines (S n).
  Proof. induction n as [|n IH]; [reflexivity|]. cbn [zero_lines app]. rewrite IH. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L15054460549.40L44896004660.40L55848622441.4000000@00S00_S3sp04SPlo1d3Hd1S3sp04SPlo1d2Hd3HneS3sp04SPlo1d". (* [comment removed for export] *)
  #[using="sp0 Hvsp SPlo"] Lemma out_state_of : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Pd,$2.P,(39.(=.(49.R2.)(1.$2.R1.=))(=.(4:.R2.(29.R1.+1.))(>.+1.R1.)))(26.R3.(48.(47.(29.R2.+1.))))")
(* [comment removed for export] *).
  Proof.
    intros m d [[OP ->]|[(SB & Hd & RD) Hd1]].
    - cbn. apply SO_none. exact (proj1 OP).
    - destruct (Z.eq_dec d 1) as [->|Hne].
      + cbn. apply SO_one. exact SB.
      + apply (SO_many m (0x7d798 + 2 * (d - 1))); [exact SB | lia | rewrite zero_lines_length; lia |].
        rewrite zero_lines_length. replace (2 * Z.to_nat (d - 1))%nat with (Z.to_nat (2 * (d - 1))) by lia. exact RD.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L1264667633.58 L14192962416.57L16085729392.57L18302140630.57L22706552983.58L22706563650.58L32162264840.57L34467122463.58L37275296262.58L42411724175.55L45150863211.55L45268348272.57L46263072.57   L47536040637.58L50720805552.57L56765677501.58L5744835812.58 L58840515755.55L59165595296.57L8559398896.57 00000:00D00N00X00b01301=01G01T01`01e01o02902I02S02g03103;03E03OS3sp01x2HxS3sp01a2HaS3sp01a2HaS3sp01a2HaS3sp01x2HfS3sp04SPlo1H1a2HaS3sp01a2HaS3sp01a2HaS3sp02SP1a2H1S3sp02SP3HSPS3sp0S3sp01a2HaS3sp01a2HaS3sp02SP1a2Ha2H1S3sp01a2HaS3sp04SPlo1H2H01a2HaS3sp01x2HxS3sp04SPloS3sp01a2HaS3sp01a2Ha". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma bmem_heapx : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "PLB,(13.$14.)PSP,$2.Pm,P,(0.&40.)(15.(0.&8.))Pm',P,(0.&40.)(15.(0.&8.))P,(4;.R2.)P,(45.$11.(12.Vsp0,)R5.R4.(19.(2>.$2.$2.)(2?.$2.$2.+5<?90.+5<??8.)(1<.(2>.$2.$2.)))R3.R2.)P,(2:.$11.R3.)P,(4<.$11.(12.Vsp0,)R4.)P,(2;.$11.R5.(29.(4.&40.Vsp0,)+800000.)R7.)P,(>.R8.(29.(4.&40.Vsp0,)+80.))(4;.R7.)")
(* [comment removed for export] *).
  Proof.
    intros LB SP m m' BM HP MI' SO' ST' HSP. pose proof SPlo. pose proof SPhi. destruct BM as [W F MI SO ER U1 CO LO OF TI].
    assert (AGD : forall x : Z, 0x48000 <= x < 0x7e000 -> ~ U_static x -> (x < 0x5cf90 \/ 0x5cff8 <= x) -> m' (wa x) = m (wa x)).
    { intros x Hx Hs Hf. apply (proj1 (HP x ltac:(lia) ltac:(right; left; cbn [hl_data_lo hl_data_hi hl_static U_layout]; split; [lia| exact Hs]) ltac:(cbn [outside]; lia))). }
    split.
    - intros a Ha. destruct (Z.lt_ge_cases a SP).
      + apply (proj1 (proj2 (proj2 ST') a ltac:(lia))).
      + apply (proj2 (HP a ltac:(lia) ltac:(left; lia) ltac:(cbn [outside]; lia))). apply W. lia.
    - eapply heap_presx_rw_cells; [exact HP | exact F | apply client_range_stack; lia| cbn; lia].
    - exact MI'.
    - exact SO'.
    - intros a Ha. rewrite AGD by (unfold U_static; lia). apply ER. lia.
    - intros a Ha. rewrite AGD by (unfold U_static; lia). apply U1. lia.
    - intros a Ha. rewrite AGD by (unfold U_static; lia). apply CO. lia.
    - intros a Ha. rewrite AGD by (unfold U_static; lia). apply LO. lia.
    - intros a Ha. rewrite AGD by (unfold U_static; lia). apply OF. lia.
    - eapply heap_presx_rw_cells; [exact HP | exact TI | | cbn; lia]. intros a Ha. right; left.
      cbn [hl_data_lo hl_data_hi hl_static U_layout]. unfold U_static. cbn in Ha. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma bmem_heap : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "PLB,(13.$14.)PSP,$2.Pm,P,(0.&40.)(15.(0.&8.))Pm',P,(0.&40.)(15.(0.&8.))P,(4;.R2.)P,(28.$11.(12.Vsp0,)R5.R4.R3.R2.)P,(2:.$11.R3.)P,(4<.$11.(12.Vsp0,)R4.)P,(2;.$11.R5.(29.(4.&40.Vsp0,)+800000.)R7.)P,(>.R8.(29.(4.&40.Vsp0,)+80.))(4;.R7.)")
(* [comment removed for export] *).
  Proof. intros LB SP m m' BM HP. apply (bmem_heapx LB SP m m' BM (hpx_of_pres _ _ _ _ HP)). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L1550461168.42 L32162264840.42L53410765808.42L56765667309.4200000:00D00N00XS3sp01a2HaS3sp01a2HaS3sp01a2HaS3sp01a2Ha". (* [comment removed for export] *)
  #[using="Type"] Lemma out_pristine_heap : forall LB SP m m', out_pristine m -> heap_pres usegs (U_layout sp0) LB SP m m' -> out_pristine m'.
  Proof.
    intros LB SP m m' [OP OE] HP. split; intros a Ha.
    - rewrite (proj1 (HP a ltac:(lia) ltac:(right; left; cbn [hl_data_lo hl_data_hi hl_static U_layout]; unfold U_static; lia))). apply OP. lia.
    - rewrite (proj1 (HP a ltac:(lia) ltac:(right; left; cbn [hl_data_lo hl_data_hi hl_static U_layout]; unfold U_static; lia))). apply OE. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L1264665839.45 L1264667633.46 L18302143821.45L22706552983.46L46811946906.43L48167097538.43L53644337151.43L5744835812.46 L8263071343.45 00000D00N00Z00d00i01801B01L01XS3sp01x2Hx4SPlo1d2HdS3sp01x2HxS3sp01x2Hx1dS3sp01x2HfS3sp0S3sp04SPlo1d2HdS3sp01d2HdS3sp01x2HxS3sp01x2Hx1d". (* [comment removed for export] *)
    #[using="Hvsp SPlo"] Lemma out_pend_heapx : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "PLB,(13.$14.)PSP,$2.Pm,P,(0.&40.)(15.(0.&8.))Pm',P,(0.&40.)(15.(0.&8.))Pd,$2.P,(4:.R3.R1.)P,(45.$11.(12.Vsp0,)R6.R5.(19.(2>.$2.$2.)(2?.$2.$2.+5<?90.+5<??8.)(1<.(2>.$2.$2.)))R4.R3.)(4:.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    (intros LB SP m m' d dd_H; ddestruct dd_H as (SB & Hd & RD); intros HP).
    assert (AGD : forall x : Z, 0x48000 <= x < 0x7e000 -> ~ U_static x -> (x < 0x5cf90 \/ 0x5cff8 <= x) -> m' (wa x) = m (wa x)).
    { intros x Hx Hs Hf. apply (proj1 (HP x ltac:(lia) ltac:(right; left; cbn [hl_data_lo hl_data_hi hl_static U_layout]; split; [lia| exact Hs]) ltac:(cbn [outside]; lia))). }
    split; [|split; [lia|]].
    - eapply stdout_buffered_agree; [exact SB|]. intros x Hx. apply AGD; unfold U_static; lia.
    - rewrite (rdn_agree_Z m m'); [exact RD | lia | lia |]. intros x Hx. apply AGD; unfold U_static; lia.
  Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Hvsp SPlo"] Lemma out_pend_heap : forall LB SP m m' d, out_pend m d -> heap_pres usegs (U_layout sp0) LB SP m m' -> out_pend m' d.
  Proof. intros LB SP m m' d OP HP. exact (out_pend_heapx LB SP m m' d OP (hpx_of_pres _ _ _ _ HP)). Qed.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00V0?L11303449684.58L14192962416.57L16085729392.57L16325462418.60L16325467126.57L16325472674.60L16325473063.58L16874567469.63L17061314817.58L17061315460.60L17061325264.57L17061329844.60L24980720096.63L42039822672.57L42039827252.60L42039828865.58L42039829252.60L45268348272.57L50720805552.57L53505208731.58L53505209118.60L53898338110.58L56765662601.60L56765667309.57L56765676985.60L56765677372.58L57929791175.63L59165595296.57L5960748193.57 L5960752837.60 L6354960761.57 L6354970921.58 L64202525591.58L66693783798.63L66782601509.63L67010277494.63L8559398896.57 L8929206777.63 00000C00M00W00k01?01L01b01o02B02L02V02`03?03I03S03f04004:04D04Z05:05D05N05X05b05l06=06G06Q06[07607T07]08508F08^08h09?S3sp02lo2hi1a2Ha2H1S3sp01a2HaS3sp01a2HaS3sp04SPlo2SB1H1a2HaS3sp04SPlo2SB1H1a2HaS3sp02SB1a2H2S3sp02SB2lo2hi1a2H12H2S3sp02B21i2HiS3sp02SB2lo2hi1a2H2S3sp01a2H4S3sp01a2HaS3sp01a2HES3sp04SPlo2SB2B23HSB1i2Hi3tid1HS3sp01a2HaS3sp01a2HES3sp02SB2lo2hi1a2H2S3sp01a2H3S3sp01a2HaS3sp01a2HaS3sp02SB2lo2hi1a2H12H2S3sp04SPlo2lo2hi2Hr1H1a2H32H42H5S3sp04SPloS3sp01a2HaS3sp01a2HaS3sp01a2H1S3sp01a2H1S3sp03tid2B21i2HiS3sp01a2HaS3sp01a2HaS3sp01a2HaS3sp04SPlo2SB3HSB1H2H01a2HaS3sp04SPlo2lo2hi2Hr2H01a2Ha2H1S3sp03tidS3sp04SPlo2B21H1i2Hi3tidS3sp03tid2B21i2HiS3sp04SPlo2B21H1i2Hi3tidS3sp01a2HaS3sp04SPlo2B21H2H01i2Hi". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma bmem_agree_gen : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Pm',Px,(0.&40.)(15.(0.&8.))PSB,$2.Plo,$2.Phi,$2.P,(4;.R5.)P,Pa,$2.P,(=.(>.=R1.)(?.R1.(21.+2.+40.)))P,(33.(=.(>.(29.(4.&40.Vsp0,)+800000.)R2.)(?.R2.R6.)))P,(33.(=.(>.+4<>20.R3.)(?.R3.+4<?08.)))P,(33.(=.(>.+7=798.R4.)(?.R4.+7=;98.)))P,(33.(=.(>.R8.R5.)(?.R5.R7.)))(1.(15.(0.&8.))A1.R;.(22.R6.)A1.R<.(22.R6.))P,(4=.$11.R7.R6.)P,(>.R6.(29.(4.&40.Vsp0,)+80.))P,(39.(=.(>.+7>000.R6.)(>.R5.(29.(4.&40.Vsp0,)+800000.)))(39.(>.R5.+10000.)(>.R5.R6.)))(4;.R9.)")
(* [comment removed for export] *).
  Proof.
    intros m m' SB lo hi BM AG0 GR HSB Hr. pose proof SPlo. pose proof SPhi. destruct BM as [W F MI SO ER U1 CO LO OF TI].
    assert (AG : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp0 - 8388608 <= a < SB) -> ~ (0x4ce20 <= a < 0x4cf08) ->
                   ~ (0x7d798 <= a < 0x7db98) -> (0x10000 <= a < 0x7e000 \/ bv_unsigned sp0 - 128 <= a) -> m' (wa a) = m (wa a)).
    { intros a H1 H2 H3 H4 H5. apply AG0; lia. }
    split.
    - intros a Ha. apply GR. apply W. exact Ha.
    - ddestruct F as [CA [W1 [W2 W3]]]. split; [| split; [lia|]; split; [exact W2|]; intros i Hi; apply GR; apply W3; exact Hi].
      destruct CA as [WF (B1 & B2 & B3)]. split; [exact WF|]. split; [exact B1|]. split; [exact B2|].
      intros i Hi. unfold mrd. rewrite AG by (cbn in Hi, B2; lia). apply B3. exact Hi.
    - eapply (mem_inv_agree m m' (fun a => (bv_unsigned sp0 - 8388608 <= a < SB) \/ (0x4ce20 <= a < 0x4cf08) \/ (0x7d798 <= a < 0x7db98) \/ (lo <= a < hi /\ 0 <= a))); [exact MI| |].
      + intros a H1 H2. apply AG0; lia.
      + intros a [Ha|[Ha|[Ha|Ha]]]; [apply ro_addr_high; lia | apply ro_addr_data; lia | apply ro_addr_data; lia |].
        destruct (Z.lt_ge_cases a 0x10000); [apply ro_addr_low; lia | apply ro_addr_high; lia].
    - ddestruct SO as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha HE.
      cbn [hl_data_lo hl_data_hi hl_written U_layout] in *. unfold U_written in HE.
      rewrite AG by lia. apply S3; [exact Ha|]. unfold U_written. exact HE.
    - intros a Ha. rewrite AG by lia. apply ER. lia.
    - intros a Ha. rewrite AG by lia. apply U1. lia.
    - intros a Ha. rewrite AG by lia. apply CO. lia.
    - intros a Ha. rewrite AG by lia. apply LO. lia.
    - intros a Ha. rewrite AG by lia. apply OF. lia.
    - ddestruct TI as [CA [W1 [W2 W3]]]. split; [| split; [lia|]; split; [exact W2|]; intros i Hi; apply GR; apply W3; exact Hi].
      destruct CA as [WF (B1 & B2 & B3)]. split; [exact WF|]. split; [exact B1|]. split; [exact B2|].
      intros i Hi. unfold mrd. rewrite AG by (cbn in Hi, B2; lia). apply B3. exact Hi.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59278113288.42000005S3sp0". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma bmem_agree : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Pm',Px,(0.&40.)(15.(0.&8.))Plo,$2.Phi,$2.P,(4;.R4.)P,Pa,$2.P,(=.(>.=R1.)(?.R1.(21.+2.+40.)))P,(33.(=.(>.(29.(4.&40.Vsp0,)+800000.)R2.)(?.R2.(29.(4.&40.Vsp0,)+=0.))))P,(33.(=.(>.+4<>20.R3.)(?.R3.+4<?08.)))P,(33.(=.(>.+7=798.R4.)(?.R4.+7=;98.)))P,(33.(=.(>.R8.R5.)(?.R5.R7.)))(1.(15.(0.&8.))A1.R:.(22.R6.)A1.R;.(22.R6.))P,(4=.$11.R6.R5.)P,(39.(=.(>.+7>000.R5.)(>.R4.(29.(4.&40.Vsp0,)+800000.)))(39.(>.R4.+10000.)(>.R4.R5.)))(4;.R7.)")
(* [comment removed for export] *).
  Proof. intros m m' lo hi BM AG GR Hr. pose proof SPlo. eapply (bmem_agree_gen m m' (bv_unsigned sp0 - 208) lo hi BM AG GR ltac:(lia) Hr). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L24376346147.39L34467128655.41L8759891693.39 00000:00P00dS3sp04SPloS3sp04SPlo2SP3HSP1a2HaS3sp04SPlo2SP3HSP2H0". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma bmem_stk : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))PSP,$2.P,(4;.R2.)P,(=.(>.(29.(4.&40.Vsp0,)+800000.)R2.)(>.R2.(4.&40.Vsp0,)))(2;.$11.R4.(29.(4.&40.Vsp0,)+800000.)R3.)")
(* [comment removed for export] *).
  Proof.
    intros m SP BM HSP. pose proof SPlo. pose proof SPhi. apply stk_of_wview; [lia|lia|]. intros a Ha. apply (bm_win m BM). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition atx0 (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "(=.(18.$11.O1.+5<?70.(19.$1:.(1;.(5.&8.=))(1<.$1:.)))(=.(18.$11.O1.+5<?74.(19.$1:.(1;.(5.&8.=))(1<.$1:.)))(=.(18.$11.O1.+7=108.(19.$1:.(1;.(5.&8.=))(1<.$1:.)))(=.(18.$11.O1.+7=10<.(19.$1:.(4>.(5.&40.=))(19.$1:.(4>.(5.&40.=))(1<.$1:.))))(=.(18.$11.O1.+7=118.(19.$1:.(1>.(5.&40.=))(19.$1:.(1>.(5.&40.=))(19.$1:.(1>.(5.&40.=))(1<.$1:.)))))(18.$11.O1.+7=228.(19.$1:.(1>.(5.&40.=))(1<.$1:.))))))))")
(* [comment removed for export] *).                                        (* [comment removed for export] *)
  Definition atx (icb : Z) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "(=.(18.$11.O1.+5<?70.(19.$1:.(1;.(5.&8.+1.))(1<.$1:.)))(=.(18.$11.O1.+5<?74.(19.$1:.(1;.(5.&8.O2.))(1<.$1:.)))(=.(18.$11.O1.+7=10<.(19.$1:.(4>.(5.&40.=))(19.$1:.(4>.(5.&40.+1.))(1<.$1:.))))(=.(18.$11.O1.+7=118.(19.$1:.(1>.(5.&40.+7=120.))(19.$1:.(1>.(5.&40.=))(19.$1:.(1>.(5.&40.+3?6?8.))(1<.$1:.)))))(18.$11.O1.+7=228.(19.$1:.(1>.(5.&40.+1=674.))(1<.$1:.)))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L1310026161.42 L22713141186.44L24933839879.42L33628000956.46L33628179521.44L37710277390.42L55515436080.42L55686714054.45L61943176380.4400000B00^01001P02002>02L02X034S3sp01A2cs3Hhi3LENS3sp04SPlo1A2cs3Hhi3LEN1i2HiS3sp01A2cs3Hlo3LENS3sp04SPlo1A2cs3Hlo3Hhi3LEN1i2HiS3sp04SPlo1A2cs3Hlo3Hhi3LEN1i2HiS3sp01A2cs3LENS3sp01A2cs3LENS3sp02cs3LENS3sp04SPlo1A2cs3Hlo3LEN1i2Hi". (* [comment removed for export] *)
  #[using="sp0 Hvsp SPlo"] Lemma rw_cells_img : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,Px,(0.&40.)(15.(0.&8.))PA,$2.Pcs,(13.$1:.)P,Pa,$2.P,(=.(>.R3.R1.)(?.R1.(:.R3.(20.(4?.R2.)))))(1.(15.(0.&8.))A1.R5.(22.R2.)(3?.(0.&8.)))P,(50.R2.)P,(1.$51.(52.$11.R4.(53.R3.))$54.)P,(>.+4<000.R5.)P,(>.(:.R6.(20.(4?.R5.)))+7>000.)(18.$11.R8.R7.R6.)")
(* [comment removed for export] *).
  Proof.
    intros m A cs NONE WF IMG Hlo Hhi.
    pose proof (cells_bytes_length cs WF) as LEN.
    split; [split; [exact WF|]|].
    - eapply (pristine_bytes_at usegs A (A + Z.of_nat (cells_size cs)) (fun _ : Z => False));
        [ split; [lia|]; split; [lia|]; intros a Ha _; apply NONE; exact Ha | exact IMG | lia | rewrite LEN; lia | intros a _ C; exact C ].
    - split; [lia|]. split; [lia|]. intros i Hi.
      pose proof (store_ok_data m (Z_to_bv 64 (A + i)) 1 ltac:(rewrite u_small by lia; lia) ltac:(rewrite u_small by lia; cbn; lia)) as SO.
      pose proof (store_ok_wview usegs m (Z_to_bv 64 (A + i)) 1 0 SO ltac:(lia)) as WV.
      unfold wa in WV |- *. rewrite Z.add_0_r, u_small in WV by lia. exact WV.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L10336822102.43L14514651888.45L21851109142.43L22332758934.43L24137097398.43L2449432854.43 L26112413238.43L27500267382.43L3561136374.43 L35962147350.43L45787445686.43L50059895478.43L62099307120.45L8522972374.43 00000500?00D00I00N00S00X00]00b00g00l01101;01@S3sp0S3sp01a2HaS3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp01a2HaS3sp0". (* [comment removed for export] *)
  #[using="Hvsp SPlo"] Lemma atx0_of_dinv : forall m, DINV m -> atx0 m.
  Proof.
    intros m [W F MI SO DM TI AB]. pose proof (dm_atx m DM) as AX. pose proof (dm_flags m DM) as FL.
    split; [|split; [|split; [|split; [|split]]]];
      (apply rw_cells_img; [ intros a Ha; cbn in Ha; first [apply FL; lia | apply AX; lia]
                           | cbn; repeat split; reflexivity | vm_compute; reflexivity | lia | cbn; lia ]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L23517522163.4600000?S3sp01A2cs1i2Hi". (* [comment removed for export] *)
  #[using="sp0"] Lemma rw_cells_agree : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Pm',Px,(0.&40.)(15.(0.&8.))PA,$2.Pcs,(13.$1:.)P,(18.$11.R4.R2.R1.)P,Pa,$2.P,(=.(>.R4.R1.)(?.R1.(:.R4.(20.(4?.R3.)))))(1.(15.(0.&8.))A1.R6.(22.R2.)A1.R7.(22.R2.))P,(4=.$11.R6.R5.)(18.$11.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros m m' A cs [[WF BY] WR] AG WM. split; [split; [exact WF|]|].
    - ddestruct BY as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|]. intros i Hi. unfold mrd.
      rewrite AG by (rewrite (cells_bytes_length cs WF) in Hi; lia). apply B3. exact Hi.
    - eapply wr_at_transport; [exact WR | exact WM].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L19373157572.4500000:S3sp01a2Ha". (* [comment removed for export] *)
  #[using="sp0"] Lemma atx_agree : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Picb,$2.Pm,P,(0.&40.)(15.(0.&8.))Pm',Px,(0.&40.)(15.(0.&8.))P,(55.R3.R2.)P,Pa,$2.P,(39.(=.(>.+5<?70.R1.)(?.R1.+5<?78.))(39.(=.(>.+7=108.R1.)(?.R1.+7=130.))(=.(>.+7=228.R1.)(?.R1.+7=230.))))(1.(15.(0.&8.))A1.R4.(22.R2.)A1.R5.(22.R2.))P,(4=.$11.R4.R3.)(55.R6.R4.)")
(* [comment removed for export] *).
  Proof.
    (intros icb m m' dd_H; ddestruct dd_H as (A1 & A2 & A3 & A4 & A5); intros AG WM).
    split; [|split; [|split; [|split]]]; (eapply rw_cells_agree; [eassumption | intros a Ha; cbn in Ha; apply AG; lia | exact WM]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L18821235583.44L29721515263.44L30666086399.44L32162264840.46L36420195775.44L6969011007.44 00000500:00?00I00N00SS3sp0S3sp0S3sp0S3sp01a2HaS3sp0S3sp0". (* [comment removed for export] *)
  #[using="Type"] Lemma atx_heapx : forall icb LB SP m m', atx icb m -> heap_presx usegs (U_layout sp0) LB SP XFP m m' -> atx icb m'.
  Proof.
    (intros icb LB SP m m' dd_H; ddestruct dd_H as (A1 & A2 & A3 & A4 & A5); intros HP).
    split; [|split; [|split; [|split]]]; (eapply heap_presx_rw_cells; [exact HP | eassumption | | cbn; lia];
                   intros a Ha; right; left; cbn [hl_data_lo hl_data_hi hl_static U_layout]; unfold U_static; cbn in Ha; lia).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma atx_heap : forall icb LB SP m m', atx icb m -> heap_pres usegs (U_layout sp0) LB SP m m' -> atx icb m'.
  Proof. intros icb LB SP m m' AX HP. exact (atx_heapx icb LB SP m m' AX (hpx_of_pres _ _ _ _ HP)). Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L1103985138.51 L14972635071.53L20950030165.51L20950182638.53L21289925285.51L23960581679.53L26214766575.53L26983627995.53L26983727456.51L34649641327.53L35531472367.53L3826659940.51 L39937718706.51L55949683437.53L56765514375.51L57219035078.53L5744826032.53 L5744833530.53 L62982007234.5300000@00P00`01001G01W01g02702G02W02g03703G03a04104C04S04c05=S3sp01a2bs2LB2HaS3sp02bs2LB1x2HxS3sp01a2bs2LB2HaS3sp01a2bs2LB2HaS3sp04SPlo1a2bs2LB2Ha1HS3sp02bs2LB1x2HxS3sp02bs2LB1x2HxS3sp01a2bs2LB2HaS3sp01a2bs2LB2HaS3sp02bs2LB1x2HxS3sp02bs2LB1x2HxS3sp01a2bs2LB2HaS3sp01a2bs2LB2HaS3sp04SPlo1a2bs2LB2Ha1x2HxS3sp01a2bs2LB2HaS3sp01a2bs2LB1x2H2S3sp02bs2LB1x2H1S3sp02bs2LB1x2HxS3sp04SPlo1a2bs2LB2Ha1i2Hi". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma bmem_flag_write : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Pa,$2.Pbs,(13.(0.&8.))P,(1.$1?.(56.(0.&8.)R1.)#1.)P,(=.(>.+5<?70.R3.)(?.R3.+5<?78.))P,(4;.R5.)(4;.(57.R6.(22.R5.)R4.))")
(* [comment removed for export] *).
  Proof.
    intros m a bs LB Ha BM. pose proof SPlo. pose proof SPhi. destruct BM as [W F MI SO ER U1 CO LO OF TI].
    assert (AG : forall x : Z, 0 <= x < 2 ^ 64 -> x <> a -> write_to_mem m (wa a) bs (wa x) = m (wa x)).
    { intros x H1 H2. apply write_other; rewrite ?LB; cbn; lia. }
    split.
    - intros x Hx. apply wview_write_mono. apply W. exact Hx.
    - apply rw_cells_frame; [exact F | lia | rewrite LB; lia | rewrite LB; cbn; lia].
    - apply mem_inv_store; [exact MI|]. rewrite LB. apply store_ok_data; rewrite u_small by lia; cbn; lia.
    - unfold statics_ok in *. apply pristine_write; [exact SO | lia | rewrite LB; lia |].
      intros i Hi. right; right. cbn [hl_written U_layout]. unfold U_written. rewrite LB in Hi. cbn in Hi. lia.
    - intros x Hx. rewrite AG by lia. apply ER. lia.
    - intros x Hx. rewrite AG by lia. apply U1. lia.
    - intros x Hx. rewrite AG by lia. apply CO. lia.
    - intros x Hx. rewrite AG by lia. apply LO. lia.
    - intros x Hx. rewrite AG by lia. apply OF. lia.
    - apply rw_cells_frame; [exact TI | lia | rewrite LB; lia | rewrite LB; cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L14192962416.54L16325462418.57L16325467126.54L16369009204.57L16369012816.54L18979375056.54L18979378612.57L45268348272.54L50720805552.54L56765662601.57L56765667309.54L59165595296.54L8559398896.54 00000:00N00f01001A01R01\01f02002:02N02X02bS3sp01a2HaS3sp04SPlo2SB1H1a2HaS3sp04SPlo2SB3HSB1a2Ha1HS3sp01a2HES3sp04SPlo1H1a2HaS3sp04SPlo1H1a2HaS3sp01a2HES3sp01a2HaS3sp01a2HaS3sp01a2HaS3sp04SPlo1H2H01a2HaS3sp01a2HaS3sp01a2Ha". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma bmem_agree_atx : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Pm',Px,(0.&40.)(15.(0.&8.))PSB,$2.P,(4;.R3.)P,Pa,$2.P,(=.(>.=R1.)(?.R1.(21.+2.+40.)))P,(33.(=.(>.(29.(4.&40.Vsp0,)+800000.)R2.)(?.R2.R4.)))P,(33.(=.(>.+5<?70.R3.)(?.R3.+5<?78.)))P,(33.(=.(>.+7=108.R4.)(?.R4.+7=328.)))(1.(15.(0.&8.))A1.R8.(22.R5.)A1.R9.(22.R5.))P,(4=.$11.R5.R4.)P,(2:.$11.R5.)P,(>.R5.(29.(4.&40.Vsp0,)+80.))(4;.R7.)")
(* [comment removed for export] *).
  Proof.
    intros m m' SB BM AG WM MI' HSB. pose proof SPlo. pose proof SPhi. destruct BM as [W F MI SO ER U1 CO LO OF TI].
    split.
    - intros a Ha. apply WM. apply W. exact Ha.
    - eapply rw_cells_agree; [exact F | intros a Ha; cbn in Ha; apply AG; lia | exact WM].
    - exact MI'.
    - ddestruct SO as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha HE.
      cbn [hl_data_lo hl_data_hi hl_written U_layout] in *. unfold U_written in HE.
      rewrite AG by lia. apply S3; [exact Ha|]. unfold U_written. exact HE.
    - intros a Ha. rewrite AG by lia. apply ER. lia.
    - intros a Ha. rewrite AG by lia. apply U1. lia.
    - intros a Ha. rewrite AG by lia. apply CO. lia.
    - intros a Ha. rewrite AG by lia. apply LO. lia.
    - intros a Ha. rewrite AG by lia. apply OF. lia.
    - eapply rw_cells_agree; [exact TI | intros a Ha; cbn in Ha; apply AG; lia | exact WM].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L19778913932.41L23894002060.41L28375090290.41L51633741452.41L60564444300.41L67226955881.4100000500:00?00D00I00NS3sp0S3sp0S3sp0S3sp0S3sp0S3sp0". (* [comment removed for export] *)
  #[using="sp0"] Lemma atx_incb : forall icb j m, atx icb m -> atx j (write_to_mem m (wa 0x5cf74) [Z_to_bv 8 j]).
  Proof.
    (intros icb j m dd_H; ddestruct dd_H as (A1 & A2 & A3 & A4 & A5)).
    split; [|split; [|split; [|split]]]; try (apply rw_cells_frame; [assumption | lia | cbn; lia | cbn; lia]).
    pose proof (rw_cells_write usegs m 0x5cf74 [C1 (Z_to_bv 8 icb)] 0 (C1 (Z_to_bv 8 icb)) (C1 (Z_to_bv 8 j)) A2 eq_refl eq_refl I) as W.
    rewrite Z.add_0_r in W. exact W.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma rw_cells_rdn_at : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))PA,$2.Pcs,(13.$1:.)Pk,$1?.Pc,$1:.P,(18.$11.R5.R4.R3.)P,(1.(15.$1:.)(58.R4.R3.)(37.$1:.R2.))(1.(15.(13.(0.&8.)))(23.$11.R7.(5.&40.(:.R6.(20.R4.)))(59.R3.))(37.(13.(0.&8.))(5:.R3.)))")
(* [comment removed for export] *).
  Proof.
    intros m A cs k c RW CA. rewrite <- ov_rdn. exact (rw_cells_read usegs m A cs k c RW CA).
  Qed.
  #[using="Type"] Lemma atx_atexit : forall m, atx 0 m -> atexit_st true m.
  Proof.
    (intros m dd_H; ddestruct dd_H as (A1 & A2 & A3 & A4 & A5)). change (atexit_reg m). unfold atexit_reg.
    pose proof (rw_cells_rdn_at m 0x7d10c _ 0 _ A3 eq_refl) as L0. pose proof (rw_cells_rdn_at m 0x7d10c _ 4 _ A3 eq_refl) as L4.
    pose proof (rw_cells_rdn_at m 0x7d118 _ 0 _ A4 eq_refl) as H0. pose proof (rw_cells_rdn_at m 0x7d118 _ 8 _ A4 eq_refl) as H8.
    pose proof (rw_cells_rdn_at m 0x7d118 _ 16 _ A4 eq_refl) as H16.
    pose proof (rw_cells_rdn_at m 0x7d228 _ 0 _ A5 eq_refl) as B0. pose proof (rw_cells_rdn_at m 0x5cf74 _ 0 _ A2 eq_refl) as I0.
    cbn [csize cbytes Z.of_nat Z.add Pos.of_succ_nat Pos.add Pos.succ] in L0, L4, H0, H8, H16, B0, I0.
    repeat split; first [exact H0 | exact L0 | exact L4 | exact H8 | exact H16 | exact B0 | exact I0].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition TRF (junk : list byte) (s6m : word) (b1 : byte) (s4m s3m s2m s0m : word) (buf : Z) : list cell := ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "(19.$1:.(5;.#8.O8.)(19.$1:.(1>.(5.&40.=))(19.$1:.(1>.O7.)(19.$1:.(1>.(8.O6.))(19.$1:.(1>.O5.)(19.$1:.(1>.O4.)(19.$1:.(1>.O3.)(19.$1:.(1>.(5.&40.O1.))(19.$1:.(1>.O2.)(19.$1:.(1>.(5.&40.+1=3<0.))(1<.$1:.)))))))))))")
(* [comment removed for export] *).

  Definition status (rv : Z) (b1 : byte) : Z := if (128 <=? bv_unsigned b1) then 0 else rv.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L10484949602.86L13776167583.85L160330747.86  L20479760346.86L20486663190.86L53517175478.86L56917881745.86L65117341362.87L66142614706.8600000=00B00V00b00g00l01A01F01KS3sp02b14NCNTS3sp0S3sp04SPlo2b12SX3CNTS3sp02b13CNTS3sp0S3sp0S3sp04SPlo2b14RB1r2SXS3sp0S3sp0". (* [comment removed for export] *)
  #[using="Hvsp Htid SPlo SPhi HSTAT"] Lemma ret_to_fin : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Prv,$2.Ppending,(13.(0.&8.))Pbuf,$2.Pcap,$2.PLB,(13.$14.)Pjunk,(13.(0.&8.))Pb1,(0.&8.)Ps6m,(0.&40.)Ps4m,(0.&40.)Ps3m,(0.&40.)Ps2m,(0.&40.)Ps0m,(0.&40.)Pra,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(15.(0.&8.))Pmo,$16.Ph,(10.$11.(12.Vsp0,)VHI,)P,(17.$11.(12.Vsp0,)VHI,R1.R22.R3.R2.)P,(2=.(2>.$2.$2.)(2?.$2.$2.R25.R24.)R23.)P,(1.$2.(30.$11.(12.Vsp0,)VHI,R3.)(4.&40.Vsp0,))P,(1.$31.(32.R5.)Vfs0,)P,(27.R7.)P,(26.R8.R2:.)P,P,(33.(1.(13.(0.&8.))R2;.(1<.(0.&8.))))(1.(15.$34.)(35.(36.R9.)(5.&40.+1.))(37.$34.(38.(5.&40.+1.))))P,(39.(1.$2.R2=.=)(1.$2.R2=.+2.))P,(18.$11.R;.(29.(4.&40.Vsp0,)+=0.)(5<.R29.R27.R28.R26.R25.R24.R23.R2<.))(3:.$11.(3;.(3<.(3=.R23.(5.&40.(29.(4.&40.Vsp0,)+=0.))(5.&40.+10800.)(5.&40.+5=0<8.)R22.R21.R20.R1?.R1>.(5.&40.R2?.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R10.R?.R>.R=.)(3>.&5.(0.&40.))(5.&40.+1=620.)(5.&20.=)(3?.(0.&40.))R<.(40.$11.))R;.)(41.(42.+1.R2>.)(43.(44.(5=.R2?.R29.))Vfs0,)))")
(* [comment removed for export] *).
  Proof.
    intros rv pending buf cap LB junk b1 s6m s4m s3m s2m s0m ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 m mo h
           HH IN HT FS FM SO FD1 Hrv FR.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ HH) as MK.
    pose proof (bv_unsigned_in_range 8 b1) as RB1r. unfold bv_modulus in RB1r. cbn in RB1r.
    pose proof (sxb_unsigned b1) as SX.
    unfold TRF in FR. unfold status.
    apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs).
    step. step. step. step. step. step. step. step. step.    (* [comment removed for export] *)
    step.                                        (* [comment removed for export] *)
    step.                                        (* [comment removed for export] *)
    replace (bv_unsigned sp0 - 208 + 80) with (bv_unsigned sp0 - 128) by lia.
    step.                                        (* [comment removed for export] *)
    destruct (Z.leb_spec0 128 (bv_unsigned b1)) as [CNT|NCNT].
    - (* [comment removed for export] *)
      replace (bv_unsigned b1 <? 128) with false in SX by (symmetry; apply Z.ltb_ge; lia).
      ifc2 true. step. step. step. step. step. step. ifc true. apply aevtM_done.
      eapply (fin 0 pending buf cap LB); [exact HH | exact IN | exact HT | exact FS | exact FM | exact SO | exact FD1 | left; reflexivity].
    - replace (bv_unsigned b1 <? 128) with true in SX by (symmetry; apply Z.ltb_lt; lia).
      ifc2 false. step. step. apply aevtM_done.
      eapply (fin rv pending buf cap LB); [exact HH | exact IN | exact HT | exact FS | exact FM | exact SO | exact FD1 | exact Hrv].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L23323968259.42L6000339285.42 L68706377326.4400000:00D00aS3sp01A2H2S3sp01A2H1S3sp04SPlo1m1A1v2H32Hb1X1a2Ha". (* [comment removed for export] *)
  #[using="Hvsp SPlo"] Lemma const_cell8 : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))PA,$2.Pv,(0.&40.)P,(4<.$11.(12.Vsp0,)R3.)P,(>.+48000.R3.)P,(>.(:.R4.+8.)+7>000.)P,(39.(>.(:.R5.+8.)+4;<=8.)(=.(>.+4;<>0.R5.)(>.(:.R5.+8.)+4<=30.)))P,(1.$51.(52.$11.R6.(5>.R5.))$54.)(5?.$11.R8.R7.(19.$1:.(1>.R6.)(1<.$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros m A v SOK H1 H2 H3 Hb.
    pose proof (statics_ok_cells usegs (U_layout sp0) m A (le8 v) SOK) as X. rewrite length_le8 in X.
    apply (ro_cells_reshape usegs m A [CB 8 (le8 v)]); [apply X | cbn; split; exact I | reflexivity].
    - unfold const_at. cbn [hl_data_lo hl_data_hi hl_written U_layout]. unfold U_written. split; [lia|]. split; [lia|]. intros a Ha. lia.
    - exact Hb.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12688731362.35L30843934076.35L45292144439.3500000500:00?S3sp0S3sp0S3sp0". (* [comment removed for export] *)
  #[using="Hvsp SPlo"] Lemma got_stderr : forall m, statics_ok usegs (U_layout sp0) m -> ro_cells usegs m 0x4bc90 [C8 (Z_to_bv 64 0x4bc40)].
  Proof. intros m SOK. apply const_cell8; [exact SOK | lia | lia | lia | vm_compute; reflexivity]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L14327295458.35L32669104183.35L67718973308.3500000500:00?S3sp0S3sp0S3sp0". (* [comment removed for export] *)
  #[using="Hvsp SPlo"] Lemma ptr_stderr : forall m, statics_ok usegs (U_layout sp0) m -> ro_cells usegs m 0x4bc40 [C8 (Z_to_bv 64 0x4cd30)].
  Proof. intros m SOK. apply const_cell8; [exact SOK | lia | lia | lia | vm_compute; reflexivity]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L47421557175.35L49450280290.35L65160770684.3500000500:00?S3sp0S3sp0S3sp0". (* [comment removed for export] *)
  #[using="Hvsp SPlo"] Lemma got_fuzzinit : forall m, statics_ok usegs (U_layout sp0) m -> ro_cells usegs m 0x4bc98 [C8 (Z_to_bv 64 0)].
  Proof. intros m SOK. apply const_cell8; [exact SOK | lia | lia | lia | vm_compute; reflexivity]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma img_msg_short : rdn usegs (fun _ => None) (Z_to_bv 64 0x10972) 31 = Some msg_short.
  Proof. vm_compute. reflexivity. Qed.
  #[using="Type"] Lemma img_msg_overrun : rdn usegs (fun _ => None) (Z_to_bv 64 0x104aa) 31 = Some msg_overrun.
  Proof. vm_compute. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L17543312104.42L20948063317.40L26985693792.4000000G00Q00[S3sp04SPlo1a2H12H21i2HiS3sp01a2H2S3sp01a2H1". (* [comment removed for export] *)
  #[using="sp0 Hvsp SPlo"] Lemma rodata_msg : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Pa,$2.Pmsg,(13.(0.&8.))P,(2:.$11.R3.)P,(>.+10000.R3.)P,(>.(:.R4.+1?.)+48000.)P,(1.(15.(13.(0.&8.)))(23.$11.L,(0.&40.)(3?.(0.&8.))(5.&40.R5.)#1?.)(37.(13.(0.&8.))R4.))(1.(15.(13.(0.&8.)))(23.$11.R7.(5.&40.R6.)#1?.)(37.(13.(0.&8.))R5.))")
(* [comment removed for export] *).
  Proof.
    intros m a msg MI H1 H2 IMG. unfold usegs in *. rewrite (rdn_none_img m a 31); [exact IMG | | lia | lia].
    intros i Hi. apply (mem_inv_text_none m i MI). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma t_emit_congr : forall (e : list event) (T T' : TSet), t_eq T T' -> t_eq (t_emit e T) (t_emit e T').
  Proof.
    intros e T T' H tr. unfold t_emit. split; (intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]]).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L15746290806.64L15866041217.59L15866046772.61L15866051408.58L15868356916.60L16085729392.58L34301895276.64L37622523289.58L50720805552.58L52101693566.58L52101698074.61L52101703855.59L52108169754.60L53900435230.59L56759158153.60L56765662601.61L56765667309.58L56765677372.59L5744833530.58 L59165595296.58L62099307120.58L63350681072.58L6354960761.58 L64204622775.59L65267197447.58L66782601509.64L8559398896.58 L8929206777.64 00000H00R00\00f01001:01R01c01m02>02O02Y02c02m03703A03K03U03_03i04304=04Q04Z04d05505?05VS3sp04SPlo2B21H1i2Hi3tidS3sp01a2H2S3sp01a2HES3sp01a2HaS3sp01a2H3S3sp01a2HaS3sp02B21i2Hi3tid4SPlo1HS3sp04SPlo1H1x2HxS3sp01a2HaS3sp04SPlo1H1a2HaS3sp04SPlo1H1a2HaS3sp01a2H2S3sp01a2H2S3sp04SPloS3sp01a2H1S3sp01a2HaS3sp01a2HaS3sp01a2H1S3sp01x2HxS3sp01a2HaS3sp01a2HaS3sp01a2HaS3sp04SPlo1H2H01a2HaS3sp03tidS3sp01x2HxS3sp03tid2B21i2HiS3sp01a2HaS3sp04SPlo2B21H2H01i2Hi". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma fin_of_fw : forall m m', DINV m -> fw_post sp0 m m' -> fin_mem m' /\ stdout_state m' [].
  Proof.
    intros m m' D FP. pose proof SPlo. pose proof SPhi. destruct FP as [AG MU GR WM FC].
    destruct D as [W F MI SO DM TI AB]. destruct DM as [DF DC DL DO DE DX DG].
    assert (AG' : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp0 - 304 <= a < bv_unsigned sp0 - 128) -> ~ (0x4cd30 <= a < 0x4ce18) -> m' (wa a) = m (wa a)).
    { intros a H1 H2 H3. pose proof (AG (wa a)) as E. unfold wa in E. rewrite u_small in E by lia. apply E; lia. }
    split; [split|].
    - intros a Ha. apply (mem_grows_wmono _ _ GR). apply W. exact Ha.
    - ddestruct F as [CA [W1 [W2 W3]]]. split; [| split; [lia|]; split; [exact W2|]; intros i Hi; apply (mem_grows_wmono _ _ GR); apply W3; exact Hi].
      destruct CA as [WF (B1 & B2 & B3)]. split; [exact WF|]. split; [exact B1|]. split; [exact B2|].
      intros i Hi. unfold mrd. rewrite AG' by (cbn in Hi, B2; lia). apply B3. exact Hi.
    - eapply (mem_inv_agree m m' (fun a => (bv_unsigned sp0 - 304 <= a < bv_unsigned sp0 - 128) \/ (0x4cd30 <= a < 0x4ce18))); [exact MI| |].
      + intros a H1 H2. apply AG'; lia.
      + intros a [Ha|Ha]; [apply ro_addr_high; lia | apply ro_addr_data; lia].
    - ddestruct SO as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha HE.
      cbn [hl_data_lo hl_data_hi hl_written U_layout] in *. unfold U_written in HE.
      rewrite AG' by lia. apply S3; [exact Ha|]. unfold U_written. exact HE.
    - intros a Ha. rewrite AG' by lia. apply DF. lia.
    - intros a Ha. rewrite AG' by lia. apply DF. lia.
    - intros a Ha. rewrite AG' by lia. apply DC. lia.
    - intros a Ha. rewrite AG' by lia. apply DL. lia.
    - intros a Ha. rewrite AG' by lia. apply DO. lia.
    - ddestruct TI as [CA [W1 [W2 W3]]]. split; [| split; [lia|]; split; [exact W2|]; intros i Hi; apply (mem_grows_wmono _ _ GR); apply W3; exact Hi].
      destruct CA as [WF (B1 & B2 & B3)]. split; [exact WF|]. split; [exact B1|]. split; [exact B2|].
      intros i Hi. unfold mrd. rewrite AG' by (cbn in Hi, B2; lia). apply B3. exact Hi.
    - dexists (Z_to_bv 64 0x7d790), (Z_to_bv 64 0). exact FC.
    - exists false. eapply atexit_st_agree; [apply atexit_st_none_of_pristine; intros a Ha; apply DX; lia |].
      intros x Hx. unfold atexit_fp in Hx. apply AG'; lia.
    - apply SO_none. intros a Ha. rewrite AG' by lia. apply DF. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0@L13921442920.72 L18021137229.72 L18468286302.75 L32168731758.108L34460694057.108L40039661481.103L53048077918.75 L56759158153.107L62919756493.72 L67386695656.72 00000500:00?00H00Q00V00[00e00j00oS3sp0S3sp0S3sp0S3sp01a1CS3sp01a1CS3sp0S3sp0S3sp01a2HaS3sp0S3sp0". (* [comment removed for export] *)
  #[using="Hvsp Htid SPlo SPhi HSTAT"] Lemma err_tail : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Ppc,$2.Pma,$2.Pmsg,(13.(0.&8.))Pbuf,$2.Pcap,$2.Pk,$1?.Pra,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(15.(0.&8.))Pmo,$16.Ph,(10.$11.(12.Vsp0,)VHI,)P,(39.(=.(1.$2.R1>.+1=404.)(=.(1.$2.R1=.+10972.)(1.(13.(0.&8.))R1<.$60.)))(=.(1.$2.R1>.+1=420.)(=.(1.$2.R1=.+104::.)(1.(13.(0.&8.))R1<.$61.))))P,(62.Vsp0,Vtid,Vmem0,R4.)P,(17.$11.(12.Vsp0,)VHI,R3.(19.(2>.$2.$2.)(2?.$2.$2.R1=.R1<.)(1<.(2>.$2.$2.)))R5.R4.)P,(1.$2.(30.$11.(12.Vsp0,)VHI,R4.)(4.&40.Vsp0,))P,(1.$31.(32.R6.)Vfs0,)P,(1.(15.$34.)(35.(36.R7.)(5.&40.+2.))(37.$34.(38.(5.&40.+2.))))(3:.$11.(3;.(3<.(3=.R1>.(5.&40.(29.(4.&40.Vsp0,)+80.))(5.&40.+10800.)(5.&40.+5=0<8.)R1=.R1<.R1;.(5.&40.+2.)(5.&40.R21.)R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R=.R<.R;.R:.)(3>.&5.(0.&40.))(5.&40.R24.)(5.&20.=)(3?.(0.&40.))R9.(40.$11.))R8.)(63.R22.Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros pc ma msg buf cap k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 m mo h CASE D HH HT FS FD2.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ HH) as MK. pose proof MK as MK2; destruct MK2 as [Hh Hl].
    pose proof (got_stderr m (di_statics _ _ _ m D)) as GOT1. pose proof (ptr_stderr m (di_statics _ _ _ m D)) as GOT2.
    assert (MSG : rdn usegs m (Z_to_bv 64 ma) 31 = Some msg).
    { destruct CASE as [(-> & -> & ->)|(-> & -> & ->)]; (apply rodata_msg; [exact (di_minv _ _ _ m D) | lia | lia |]);
        [apply img_msg_short | apply img_msg_overrun]. }
    assert (Hma : 0x10000 <= ma /\ ma <= 0x4b000) by (destruct CASE as [(_ & -> & _)|(_ & -> & _)]; lia).
    unfold t_die. eapply rz_conseq; [| apply t_emit_congr; apply (t_emit_W_nil 1); apply t_exit_has_nil ].
    (* [comment removed for export] *)
    assert (STEPS : aevtM usegs mo (fun c => realizes usegs c (t_emit (W 2 msg) (t_emit (W 1 []) (t_exit (exit_code 2) fs0))))
              (MS (mkR (Z_to_bv 64 0x1d440) (Z_to_bv 64 (bv_unsigned sp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8) t0 t1 t2
                       (Z_to_bv 64 2) (Z_to_bv 64 buf) (Z_to_bv 64 ma) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 0x4cd30) a4 a5 a6 a7 s2 s3 s4 s5 s6
                       (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
                  bvmap_empty (Z_to_bv 64 0x41d98) (Z_to_bv 32 0) None m (seg_rom usegs)) ->
            realizes usegs (mkCfg (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8) t0 t1 t2
                                   (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                                   (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
                              bvmap_empty (Z_to_bv 64 pc) (Z_to_bv 32 0) None m (seg_rom usegs)) mo)
                     (t_emit (W 2 msg) (t_emit (W 1 []) (t_exit (exit_code 2) fs0)))).
    { intros K. destruct CASE as [(-> & -> & ->)|(-> & -> & ->)]; apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs).
      - step. step. step. step. step. step. step. step. step. exact K.
      - step. step. step. step. step. step. step. step. exact K. }
    apply STEPS. clear STEPS. apply aevtM_done.
    change (MS ?Rx bvmap_empty ?pcx (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pcx Mx rom).
    destruct (DFW m h _ mo D HH) as [canw FWM].
    refine (fwrite_err sp0 mo Hvsp Hh Hl FD2 ma msg _ m canw Hma _ MSG _ _ _ _ _ _ _ _ FWM _ _ _);
      [ destruct CASE as [(_ & _ & ->)|(_ & _ & ->)]; reflexivity
      | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity
      | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity
      | apply t_emit_has_nil | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' FP. norm_getr.
    destruct (fin_of_fw m m' D FP) as [FM' SO'].
    assert (HH' : HEAP usegs (U_layout sp0) HI h [(buf, cap)] m' mo).
    { destruct FP as [AG MU GR WM FC].
      eapply (heap_frame usegs (U_layout sp0) HI) with (SP := bv_unsigned sp0 - 8388608);
        [ exact HH | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia | | exact WM ].
      intros a Ha Hnc. pose proof (AG (wa a)) as E. unfold wa in E. rewrite u_small in E by lia. apply E.
      - intros C. apply Hnc. left. rewrite HT. lia.
      - intros C. apply Hnc. right; left. cbn [hl_data_lo hl_data_hi hl_static U_layout]. unfold U_static. lia. }
    apply (fin 2 [] buf cap [(buf, cap)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' mo h HH' ltac:(left; reflexivity) HT FS FM' SO');
      [ intros C; exfalso; apply C; reflexivity | right; reflexivity ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L53649721933.3900000=S3sp02bs1k2Hk". (* [comment removed for export] *)
  #[using="sp0"] Lemma nth_byte_read : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Pa,$2.Pbs,(13.(0.&8.))Pk,$1?.P,(64.$11.R4.R3.R2.)P,(65.R2.(56.(0.&8.)R3.))(1.(15.(13.(0.&8.)))(66.$11.R6.(22.(:.R5.(20.R3.)))#1.)(37.(13.(0.&8.))(19.(0.&8.)(67.(0.&8.)R3.R4.(5.&8.=))(1<.(0.&8.)))))")
(* [comment removed for export] *).
  Proof.
    intros m a bs k BY Hk. rewrite (bytes_at_ov_read usegs m a bs k 1 BY) by lia.
    f_equal. rewrite <- (firstn_skipn_step bs k 0 (nth k bs (Z_to_bv 8 0))); [reflexivity|].
    apply nth_error_nth'. exact Hk.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L1080380655.62 L16085729392.61L16085739552.62L28939420519.59L68706377326.61L68706383422.6200000:00D00Q00d00n018S3sp01a2HaS3sp01a2HaS3sp01a2Ha2H1S3sp04SPlo1d2Hd3Hd2S3sp01a2HaS3sp01a2Ha". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi HSTAT"] Lemma pn_mem_of : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Ph,(10.$11.(12.Vsp0,)VHI,)PLB,(13.$14.)Pmo,$16.Pd,$2.P,(4;.R5.)P,(17.$11.(12.Vsp0,)VHI,R5.R4.R6.R3.)P,(4:.R7.R3.)P,(=.(>.=R4.)(>.R4.+1?4.))(1=.(0.&40.)Lcanw,(0.&40.)(68.Vsp0,(:.+7=798.(;.+2.R6.))R1.R:.))")
(* [comment removed for export] *).
  Proof.
    (intros m h LB mo d BM HH dd_H; ddestruct dd_H as (SB & Hd & RD); intros Hd2). pose proof SPlo. pose proof SPhi. destruct BM as [W F MI SO ER U1 CO LO OF TI].
    ddestruct (HSTAT h LB m mo HH) as (NL & [canw CA] & GOT). ddestruct SO as (_ & _ & ST).
    cbn [hl_data_lo hl_data_hi hl_written U_layout] in ST. unfold U_written in ST.
    exists canw. split.
    - intros a Ha. pose proof (u64_range a). rewrite <- (Z_to_bv_bv_unsigned a). apply W. lia.
    - intros a Ha. destruct (Z.lt_ge_cases a 0x48000); [apply mem_inv_text_none; [exact MI|lia] | apply ST; lia].
    - apply rw_cells_rdn8. exact GOT.
    - intros a Ha. apply ST; lia.
    - apply rw_cells_rdn8. exact CA.
    - exact SB.
    - lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L1080380655.58 L14192952225.59L16085739552.58L45268338214.60L53410771110.60L68706383422.5800000:00G00T00a00n01;S3sp01a2HaS3sp01a2H12H2S3sp01a2Ha2H1S3sp01a2Ha2H3S3sp01a2H22H3S3sp01a2Ha2H1". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi HSTAT"] Lemma fw_mem_of : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Ph,(10.$11.(12.Vsp0,)VHI,)PLB,(13.$14.)Pmo,$16.P,(4;.R4.)P,Pa,$2.P,(=.(>.+4<>20.R1.)(?.R1.+4<?08.))(1.(15.(0.&8.))A1.R7.(22.R2.)(3?.(0.&8.)))P,(17.$11.(12.Vsp0,)VHI,R5.R4.R6.R3.)(1=.(0.&40.)Lcanw,(0.&40.)(69.Vsp0,R1.R8.))")
(* [comment removed for export] *).
  Proof.
    intros m h LB mo BM OP HH. pose proof SPlo. pose proof SPhi. destruct BM as [W F MI SO ER U1 CO LO OF TI].
    ddestruct (HSTAT h LB m mo HH) as (NL & [canw CA] & GOT). ddestruct SO as (_ & _ & ST).
    cbn [hl_data_lo hl_data_hi hl_written U_layout] in ST. unfold U_written in ST.
    exists canw. split.
    - intros a Ha. pose proof (u64_range a). rewrite <- (Z_to_bv_bv_unsigned a). apply W. lia.
    - intros a Ha. destruct (Z.lt_ge_cases a 0x48000); [apply mem_inv_text_none; [exact MI|lia] | apply ST; lia].
    - apply rw_cells_rdn8. exact GOT.
    - intros a Ha. destruct (Z.lt_ge_cases a 0x4cd30); [apply ST; lia|]. destruct (Z.lt_ge_cases a 0x4ce20); [apply ER; lia|].
      destruct (Z.lt_ge_cases a 0x4cf08); [apply OP; lia| apply U1; lia].
    - apply rw_cells_rdn8. exact CA.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L13770793400.51L15224799736.51L24500950254.48L28706889150.48L37616188006.51L38298267132.48L46809998126.48L48164890742.48L53688827087.48L5738359813.51 L63156302647.4800000<00H00W00^01501D01I01Y01h02=02KS3sp01d1x2HxS3sp01d1x2HxS3sp04SPlo1d2HdS3sp01dS3sp04SPlo1d3Hd71H1x2HxS3sp04SPlo1d2HdS3sp0S3sp04SPlo1d3Hd7S3sp04SPlo1d2HdS3sp04SPlo1d3Hd71x2HxS3sp01d2Hd3Hd7". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma out_pend_next : forall m m' d, out_pend m d -> d <= 7 -> pn_post sp0 (0x7d798 + 2 * d) m m' -> out_pend m' (d + 1).
  Proof.
    (intros m m' d dd_H; ddestruct dd_H as (SB & Hd & RD); intros Hd7 [AG MU GR WM SB' BY]). pose proof SPlo. pose proof SPhi.
    split; [|split; [lia|]].
    - replace (0x7d798 + 2 * (d + 1)) with (0x7d798 + 2 * d + 2) by lia. exact SB'.
    - replace (Z.to_nat (2 * (d + 1))) with (Z.to_nat (2 * d) + 2)%nat by lia.
      replace (Z.to_nat (d + 1)) with (S (Z.to_nat d)) by lia. rewrite <- zero_lines_snoc.
      apply rdn_app_Z; [| | lia | lia].
      + rewrite (rdn_agree_Z m m'); [exact RD | lia | lia |].
        intros x Hx. pose proof (AG (wa x)) as E. unfold wa in E. rewrite u_small in E by lia. apply E; lia.
      + replace (0x7d798 + Z.of_nat (Z.to_nat (2 * d))) with (0x7d798 + 2 * d) by lia. exact BY.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L43985082463.4000000HS3sp04SPlo1A1B1k1r3Hne1e". (* [comment removed for export] *)
  #[using="sp0 Hvsp SPlo"] Lemma in_lb_remove : forall (A B k : Z) (LB : list blk), In (B, k) LB -> B <> A -> In (B, k) (lb_remove A LB).
  Proof.
    intros A B k LB. induction LB as [|b r IH]; intros HIn Hne; [destruct HIn|].
    cbn [lb_remove]. destruct HIn as [->|HIn].
    - cbn [fst]. destruct (Z.eqb_spec B A); [lia|]. left. reflexivity.
    - destruct (Z.eqb_spec (fst b) A); [exact HIn | right; apply IH; assumption].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Section PLoop.
    Variables (DATA plen owned buf cap : Z) (bs junk : list byte) (s6m : word) (b1 : byte) (s4m s3m s2m s0m : word).
    Hypothesis Hbs : Z.of_nat (length bs) = plen.
    Hypothesis Hplen : 0 <= plen < 2 ^ 26.
    Hypothesis HDATA : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "(=.(?.=VDATA,)(=.(>.(:.VDATA,Vplen,)(29.(4.&40.Vsp0,)+800000.))(39.(>.(:.VDATA,Vplen,)+10000.)(39.(>.+7>000.VDATA,)(1.$2.Vplen,=)))))")
(* [comment removed for export] *).
    Let TRFm : list cell := TRF junk s6m b1 s4m s3m s2m s0m buf.

    (* [comment removed for export] *)
    Record PL (icb : Z) (LB : list blk) (m : mem) (mo : Model) (h : HST usegs (U_layout sp0) HI) : Prop := MKPL {
      pl_bmem : bmem m;
      pl_trf : rw_cells usegs m (bv_unsigned sp0 - 208) TRFm;
      pl_heap : HEAP usegs (U_layout sp0) HI h LB m mo;
      pl_buf : In (buf, cap) LB;
      pl_owned : owned = 0 \/ In (owned, plen) LB /\ owned <> buf;
      pl_top : heap_top usegs (U_layout sp0) HI h = bv_unsigned sp0;
      pl_fs : m_fs mo = fs0;
      pl_fd1 : fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
      pl_data : bytes_at usegs m DATA bs;
      pl_client : client_range (U_layout sp0) LB (bv_unsigned sp0 - 208) DATA plen;
      pl_si : si_P SI m;
      pl_atx : atx icb m
    }.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L36745418172.86L58840400410.85L59273919541.85L59308586248.90L67809572149.8500000V00n01A01e028S3sp04SPlo4DATA4plen2bs5Hplen5HDATA2PnS3sp04SPlo4plen2bs5HplenS3sp04plen2bs5HplenS3sp04SPlo4plen2bs3Hbs5Hplen2P01i2HiS3sp04plen2bs5Hplen". (* [comment removed for export] *)
    #[using="Hvsp SPlo SPhi SIFP Hbs Hplen HDATA"] Lemma PL_fuzz_post : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Picb,$2.PLB,(13.$14.)Pm,P,(0.&40.)(15.(0.&8.))Pmo,$16.Ph,(10.$11.(12.Vsp0,)VHI,)Pm',P,(0.&40.)(15.(0.&8.))Pmo',$16.Ph',(10.$11.(12.Vsp0,)VHI,)PLBx,(13.$14.)P,(6:.R9.R8.R7.R6.R5.)P,(2:.$11.R5.)P,(4<.$11.(12.Vsp0,)R6.)P,(6;.(12.Vsp0,)VSI,R7.)P,(2;.$11.R8.(29.(4.&40.Vsp0,)+800000.)(29.(4.&40.Vsp0,)+=0.))P,(6<.R;.R8.)P,(45.$11.(12.Vsp0,)R>.(29.(4.&40.Vsp0,)+=0.)(46.(12.Vsp0,)VSI,)R=.R:.)P,(17.$11.(12.Vsp0,)VHI,R9.(6=.$14.R8.R?.)R;.R:.)P,(1.$2.(30.$11.(12.Vsp0,)VHI,R:.)(30.$11.(12.Vsp0,)VHI,R=.))(6:.R12.(6=.$14.R:.R11.)R=.R<.R;.)")
(* [comment removed for export] *).
    Proof.
      intros icb LB m mo h m' mo' h' LBx P MI' SO' SI' ST' MF HP0 HH' HT'. pose proof SPlo. pose proof SPhi. pose proof (hpx_fp _ _ _ _ HP0) as HP.
      destruct P as [BM TR HH IB IO HT FS FD1 BY CR SIc AX]. ddestruct HDATA as (HD1 & HD2 & HD3). split.
      - eapply bmem_heapx; eauto. lia.
      - eapply heap_presx_rw_cells; [exact HP | exact TR | apply client_range_stack; lia| cbn; lia].
      - exact HH'.
      - apply in_app_iff. right. exact IB.
      - destruct IO as [E|[I NE]]; [left; exact E | right; split; [apply in_app_iff; right; exact I | exact NE]].
      - rewrite HT'. exact HT.
      - rewrite (mo_frame_fs _ _ MF). exact FS.
      - rewrite (mo_frame_fds _ _ MF). exact FD1.
      - destruct (Z.eq_dec plen 0) as [P0|Pn].
        + ddestruct BY as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|]. intros i Hi. exfalso. lia.
        + eapply heap_presx_bytes_at; [exact HP | exact BY | rewrite Hbs; exact CR| rewrite Hbs; cbn; lia].
      - intros a Ha. destruct (CR a Ha) as [C|[C|C]]; [left; exact C | right; left; exact C | right; right].
        ddestruct C as (b & Hb & Hr). exists b. split; [apply in_app_iff; right; exact Hb | exact Hr].
      - exact SI'.
      - eapply atx_heapx; [exact AX | exact HP].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L19484584866.73L28375238262.77L28375378091.74L28377349616.73L32162264840.75L34656666014.77L40039511349.73L42288611405.74L49606997401.73L56765677501.77L59308586248.78L67227071085.77L67227196592.74L67229157867.7300000C00V00i01<01T01l02?02f03>03V04:04M04`053S3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5Hplen1a2HaS3sp04plen2bs5Hplen1a2H1S3sp04plen2bs5HplenS3sp04SPlo4DATA4plen2bs3Hbs5Hplen5HDATAS3sp04SPlo4plen2bs5HplenS3sp04plen2bs5Hplen1a2HaS3sp04SPlo4plen2bs3Hbs5Hplen2P01i2HiS3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5Hplen". (* [comment removed for export] *)
    #[using="Hvsp SPlo SPhi SIFP Hbs Hplen HDATA"] Lemma PL_incb : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Picb,$2.Pj,$2.PLB,(13.$14.)Pm,P,(0.&40.)(15.(0.&8.))Pmo,$16.Ph,(10.$11.(12.Vsp0,)VHI,)P,(6:.R6.R4.R3.R2.R1.)(6:.R6.R5.(57.R4.(22.+5<?74.)(19.(0.&8.)(5.&8.R6.)(1<.(0.&8.))))R3.R2.)")
(* [comment removed for export] *).
    Proof.
      intros icb j LB m mo h P. pose proof SPlo. pose proof SPhi.
      destruct P as [BM TR HH IB IO HT FS FD1 BY CR SIc AX]. ddestruct HDATA as (HD1 & HD2 & HD3). split.
      - apply bmem_flag_write; [reflexivity | lia | exact BM].
      - apply rw_cells_frame; [exact TR | lia | cbn; lia | cbn; lia].
      - eapply (heap_write usegs (U_layout sp0) HI) with (SP := bv_unsigned sp0 - 8388608);
          [ exact HH | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia | | lia | cbn; lia ].
        intros a Ha. right; left. cbn in Ha. cbn [hl_data_lo hl_data_hi hl_static U_layout]. unfold U_static. lia.
      - exact IB.
      - exact IO.
      - exact HT.
      - exact FS.
      - exact FD1.
      - destruct (Z.eq_dec plen 0) as [P0|Pn].
        + ddestruct BY as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|]. intros i Hi. exfalso. lia.
        + apply bytes_at_write_other; [exact BY | lia | cbn; lia | cbn; lia].
      - exact CR.
      - eapply (si_frame SI); [exact SIc|]. intros a Ha NO. pose proof (SIFP a NO). apply write_other; cbn; lia.
      - apply (atx_incb icb). exact AX.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L39428301447.116L39432544319.92 L40043721101.92 L41335366715.92 L53134038508.92 L54268190519.116L54272335247.91 L59273919029.116L60778098721.92 L63099320715.116L67809571637.116L7231746835.119 00000M00j01=01P01c02602I02\02o03T03g04AS3sp04SPlo4SPhi4plen2bs5HplenS3sp04SPlo4SPhi4plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04SPlo4plen5owned3buf2bs5Hplen2NES3sp04plen2bs5HplenS3sp04plen2bs5Hplen2dd3Hdd". (* [comment removed for export] *)
    #[using="Hvsp Htid SPlo SPhi HSTAT Hplen"] Lemma last_free : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pdd,$2.PLB,(13.$14.)Pra,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps3,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(15.(0.&8.))Pmo,$16.Ph,(10.$11.(12.Vsp0,)VHI,)P,(=.(>.+1.R16.)(>.R16.+8.))P,(6:.=R16.R4.R3.R2.)P,(4:.R5.(29.R18.+1.))(6>.$11.R5.Lc,$6?.(3:.$11.R1.(41.(42.+1.(48.(47.(29.R1:.+1.))))(43.(44.(5=.=Vb1,))Vfs0,)))(3<.(3=.R17.(5.&40.(29.(4.&40.Vsp0,)+=0.))(5.&40.+10800.)(5.&40.+5=0<8.)R16.R15.R14.(5.&40.Vplen,)(5.&40.VDATA,)R13.R12.R11.R10.R?.R>.R=.R<.(5.&40.Vowned,)R;.(5.&40.+5<?70.)(5.&40.=)(5.&40.=)(5.&40.-2.)(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R:.R9.R8.R7.)(3>.&5.(0.&40.))(5.&40.+1=60<.)(5.&20.=)(3?.(0.&40.))R6.(40.$11.)))")
(* [comment removed for export] *).
    Proof.
      intros dd LB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 m2 mo' h' Hdd P OP2.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      pose proof P as [BM2 TR2 HH2 IB IO HT FS FD1 BY2 CR SI2 AX2].
      pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ HH2) as MK.
      step. step.                                (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (K : forall (m3 : mem) (mo3 : Model) (h3 : HST usegs (U_layout sp0) HI) (LB3 : list blk)
                       (w0 w1 w2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 : word),
                 bmem m3 -> atx 0 m3 -> out_pend m3 (dd - 1) -> rw_cells usegs m3 (bv_unsigned sp0 - 208) TRFm ->
                 HEAP usegs (U_layout sp0) HI h3 LB3 m3 mo3 -> In (buf, cap) LB3 -> heap_top usegs (U_layout sp0) HI h3 = bv_unsigned sp0 ->
                 m_fs mo3 = fs0 -> fd_lookup (m_fds mo3) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
                 aevtM usegs mo3 (fun c => realizes usegs c (t_emit (W 1 (zero_lines (Z.to_nat (dd - 1)))) (t_exit (exit_code (status 0 b1)) fs0)))
                   (MS (mkR (Z_to_bv 64 0x1d614) (Z_to_bv 64 (bv_unsigned sp0 - 208)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8) w0 w1 w2
                            (Z_to_bv 64 plen) (Z_to_bv 64 DATA) wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7
                            (Z_to_bv 64 owned) s3 (Z_to_bv 64 0x5cf70) (Z_to_bv 64 0) (Z_to_bv 64 0)
                            (Z_to_bv 64 (-2)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) w3 w4 w5 w6)
                       bvmap_empty (Z_to_bv 64 0x1d614) (Z_to_bv 32 0) None m3 (seg_rom usegs))).
      { intros m3 mo3 h3 LB3 w0 w1 w2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 BM3 AX3 OP3 TR3 HH3 IB3 HT3 FS3 FD3.
        pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ HH3) as MK3.
        step. step. step.                        (* [comment removed for export] *)
        apply aevtM_done.
        eapply (ret_to_fin 0 _ buf cap LB3 junk b1 s6m s4m s3m s2m s0m); [exact HH3 | exact IB3 | exact HT3 | exact FS3
          | apply bmem_fin; [exact BM3 | exists true; apply atx_atexit; exact AX3]
          | apply out_state_of; right; split; [exact OP3 | lia]
          | intros _; exact FD3 | left; reflexivity | exact TR3 ]. }
      destruct IO as [OW0 | [IO NE]].
      + (* [comment removed for export] *)
        eapply aevtM_cut_evt; [exact MK | apply (heap_free_null usegs (U_layout sp0) HI); rewrite OW0; reflexivity |].
        intros ms3 ->.
        replace (ret_pc (Z_to_bv 64 0x1d614)) with (Z_to_bv 64 0x1d614 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
        apply (K m2 mo' h' LB); assumption.
      + (* [comment removed for export] *)
        eapply aevtM_cut.
        { eapply (heap_free usegs (U_layout sp0) HI) with (lo := bv_unsigned sp0 - 8388608);
            [ exact HH2 | exact IO
            | rewrite u_small by lia; apply bmem_stk; [exact BM2 | lia]
            | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia
            | rewrite u_small by lia; cbn [hl_stack U_layout]; lia
            | exact (bm_minv _ BM2)
            | reflexivity
            | rewrite u_small by lia; rewrite HT; lia
            | reflexivity ]. }
        intros ms3 mo3 PO.
        ddestruct PO as (x0 & x1 & x2 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x3 & x4 & x5 & x6 & m3 & mo3' & E3 & MI3 & ST3 & MF3 & HP3 & h3 & HT3 & HH3).
        injection E3; clear E3; intros Emo Ems. subst ms3 mo3'.
        rewrite u_small in ST3, HP3 by lia.
        replace (ret_pc (Z_to_bv 64 0x1d614)) with (Z_to_bv 64 0x1d614 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
        apply (K m3 mo3 h3 (lb_remove owned LB)).
        * eapply bmem_heap; [exact BM2 | exact HP3 | exact MI3 | eapply statics_ok_pres; [exact (bm_statics _ BM2) | exact HP3] | exact ST3 | lia].
        * eapply atx_heap; [exact AX2 | exact HP3].
        * eapply out_pend_heap; [exact OP2 | exact HP3].
        * eapply heap_pres_rw_cells; [exact HP3 | exact TR2 |]. apply client_range_stack. lia.
        * exact HH3.
        * apply in_lb_remove; [exact IB | lia].
        * rewrite HT3, HT. reflexivity.
        * rewrite (mo_frame_fs _ _ MF3). exact FS.
        * rewrite (mo_frame_fds _ _ MF3). exact FD1.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L10336707543.106L10336707543.78 L27320800273.93 L28375238391.111L28375238391.83 L29065630073.93 L32162258905.123L34656665887.111L34656665887.83 L3560988791.106 L3560988791.78  L37794208624.93 L3928448929.123 L39428304027.119L39430548138.93 L40041462552.93 L41333108398.93 L45100645466.93 L46253041.123   L52978755911.111L54854397327.106L54854397327.78 L56765677372.111L56765677372.123L56765677372.83 L60780362420.93 L67227071212.111L67227071212.83 L9784907179.119 00000C00V01401G01Z01m02E02]03503H03[04904V05305P05c06606N06f07>07Q07d08<08T08l09?09R09e0:8S3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04DATA4plen2bs5Hplen5HDATAS3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5Hplen1a2H2S3sp04plen2bs5Hplen1a2H2S3sp04plen2bs5Hplen1a2H2S3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04DATA4plen2bs5Hplen5HDATAS3sp04SPlo4plen2bs5Hplen1a2H2S3sp04SPlo4SPhi4plen2bs5HplenS3sp04SPlo4SPhi4plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04SPlo4plen2bs5HplenS3sp04plen2bs5Hplen1a2H2S3sp04plen2bs5Hplen1a2H2S3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5Hplen1a2H1S3sp04plen2bs5Hplen1a2H1S3sp04plen2bs5Hplen1a2H1S3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5HplenS3sp04plen2bs5Hplen". (* [comment removed for export] *)
    #[using="Hvsp SPlo SPhi SPal SIFP FUZZ Hbs Hplen HDATA"] Lemma pcall : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "PLB,(13.$14.)PQ,P,$6?.SpPra,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps3,(0.&40.)Ps5,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(15.(0.&8.))Pmo,$16.Ph,(10.$11.(12.Vsp0,)VHI,)P,(6:.=R17.R3.R2.R1.)P,Pt0',(0.&40.)Pt1',(0.&40.)Pt2',(0.&40.)Pa2',(0.&40.)Pa3',(0.&40.)Pa4',(0.&40.)Pa5',(0.&40.)Pa6',(0.&40.)Pa7',(0.&40.)Pt3',(0.&40.)Pt4',(0.&40.)Pt5',(0.&40.)Pt6',(0.&40.)Pm',P,(0.&40.)(15.(0.&8.))Pmo',$16.Ph',(10.$11.(12.Vsp0,)VHI,)PLBx,(13.$14.)P,(6:.=(6=.$14.R1.R29.)R4.R3.R2.)P,(6<.R15.R4.)P,Pa,$2.P,(=.(>.=R1.)(?.R1.(21.+2.+40.)))P,(39.(=.(>.+4<>20.R2.)(?.R2.+4<?08.))(=.(>.+7=798.R2.)(?.R2.+7=;98.)))(1.(15.(0.&8.))A1.R9.(22.R3.)A1.R1:.(22.R3.))(6>.$11.R6.R2;.(3<.(3=.(5.&40.+1=5?8.)(5.&40.(29.(4.&40.Vsp0,)+=0.))(5.&40.+10800.)(5.&40.+5=0<8.)R14.R13.R12.(5.&40.Vplen,)(5.&40.VDATA,)(5.&40.=)(5.&40.=)R11.R10.R?.R>.R=.R<.(5.&40.Vowned,)(5.&40.=)(5.&40.+5<?70.)R1=.(5.&40.=)(5.&40.-2.)(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R;.R:.R9.R8.)(3>.&5.(0.&40.))(5.&40.+1=6:4.)(5.&20.=)(3?.(0.&40.))R7.(40.$11.)))(6>.$11.R4.R18.(3<.(3=.R17.(5.&40.(29.(4.&40.Vsp0,)+=0.))(5.&40.+10800.)(5.&40.+5=0<8.)R16.R15.R14.(5.&40.Vplen,)(5.&40.VDATA,)R13.R12.R11.R10.R?.R>.R=.R<.(5.&40.Vowned,)R;.(5.&40.+5<?70.)R:.(5.&40.=)(5.&40.-2.)(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R9.R8.R7.R6.)(3>.&5.(0.&40.))(5.&40.+1=5=4.)(5.&20.=)(3?.(0.&40.))R5.(40.$11.)))")
(* [comment removed for export] *).
    Proof.
      intros LB Q ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 t3 t4 t5 t6 m mo h P K.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ (pl_heap _ _ _ _ _ P)) as MK.
      (* [comment removed for export] *)
      assert (FST : store_ok usegs m (Z_to_bv 64 0x5cf74) 1 = true) by (apply store_ok_data; rewrite u_small by lia; lia).
      step. step.                                  (* [comment removed for export] *)
      change (le1 (Z_to_bv 64 1)) with [Z_to_bv 8 1]. change (Z_to_bv 64 380788) with (wa 0x5cf74).
      pose proof (PL_incb 0 1 LB m mo h P) as P1.
      assert (AG1 : forall a : Z, 0 <= a < 2 ^ 64 -> a <> 0x5cf74 -> write_to_mem m (wa 0x5cf74) [Z_to_bv 8 1] (wa a) = m (wa a)).
      { intros a H1 H2. apply write_other; cbn; lia. }
      clear FST. set (m1 := write_to_mem m (wa 0x5cf74) [Z_to_bv 8 1]) in *. clearbody m1.
      pose proof P1 as [BM TR HH IB IO HT FS FD1 BY CR SIc AX].
      (* [comment removed for export] *)
      step. step. step.                            (* [comment removed for export] *)
      eapply aevtM_cut.
      { eapply FUZZ with (lo := bv_unsigned sp0 - 8388608) (DATA := DATA) (n := plen) (bs := bs) (h := h) (LB := LB);
          [ exact HH | exact BY | exact Hbs | lia | lia
          | rewrite u_small by lia; exact CR
          | rewrite u_small by lia; lia
          | rewrite u_small by lia; apply bmem_stk; [exact BM | lia]
          | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia
          | rewrite u_small by lia; lia
          | rewrite u_small by lia; rewrite <- Zminus_mod_idemp_l, SPal; reflexivity
          | rewrite u_small by lia; rewrite HT; lia
          | exact (bm_minv _ BM) | exact (bm_statics _ BM) | exact SIc | reflexivity | reflexivity | reflexivity ]. }
      intros ms' mo' PO.
      ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' & mo'' & h' & LBx & E & A0 & MI' & SO' & SI' & ST' & MF & HP & HH' & HT').
      injection E; clear E; intros Emo Ems. subst ms' mo'' ua0.
      rewrite u_small in ST', HP by lia.
      replace (ret_pc (Z_to_bv 64 0x1d5e8)) with (Z_to_bv 64 0x1d5e8 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      pose proof (PL_fuzz_post 1 LB m1 mo h m' mo' h' LBx P1 MI' SO' SI' ST' MF HP HH' HT') as P'.
      assert (AG' : forall a : Z, 0 <= a < 2 ^ 64 -> (0x4ce20 <= a < 0x4cf08 \/ 0x7d798 <= a < 0x7db98) -> m' (wa a) = m (wa a)).
      { intros a H1 H2. rewrite <- (AG1 a) by lia.
        apply (proj1 (HP a ltac:(lia) ltac:(right; left; cbn [hl_data_lo hl_data_hi hl_static U_layout]; unfold U_static; lia) ltac:(apply nfp; lia))). }
      clear P P1 BM TR HH IB IO HT FS FD1 BY CR MK SIc AX AG1.
      pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ (pl_heap _ _ _ _ _ P')) as MK.
      (* [comment removed for export] *)
      assert (FST : store_ok usegs m' (Z_to_bv 64 0x5cf74) 1 = true) by (apply store_ok_data; rewrite u_small by lia; lia).
      step. step.                                  (* [comment removed for export] *)
      change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. change (Z_to_bv 64 380788) with (wa 0x5cf74).
      pose proof (PL_incb 1 0 (LBx ++ LB) m' mo' h' P') as P2.
      assert (AG2 : forall a : Z, 0 <= a < 2 ^ 64 -> (0x4ce20 <= a < 0x4cf08 \/ 0x7d798 <= a < 0x7db98) -> write_to_mem m' (wa 0x5cf74) [Z_to_bv 8 0] (wa a) = m (wa a)).
      { intros a H1 H2. rewrite write_other by (cbn; lia). apply AG'; lia. }
      clear FST P' AG'. set (m2 := write_to_mem m' (wa 0x5cf74) [Z_to_bv 8 0]) in *. clearbody m2.
      step. step.                                  (* [comment removed for export] *)
      apply (K _ _ _ _ _ _ _ _ _ _ _ _ _ m2 mo' h' LBx P2 MF AG2).
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L11215980613.59L46809849751.57L48165000399.57L53642239986.57L5744833530.59 00000R00e01B01Z02<S3sp04plen2bs5Hplen1x2Hx4SPlo1d2HdS3sp04plen2bs5HplenS3sp04SPlo4plen2bs5Hplen1d2HdS3sp04plen2bs5Hplen1d2HdS3sp04plen2bs5Hplen1x2Hx4SPlo1d2Hd". (* [comment removed for export] *)
    #[using="sp0 Hvsp SPlo plen bs Hplen"] Lemma out_pend_agree : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pm,P,(0.&40.)(15.(0.&8.))Pm',Px,(0.&40.)(15.(0.&8.))Pd,$2.P,(4:.R3.R1.)P,Pa,$2.P,(=.(>.=R1.)(?.R1.(21.+2.+40.)))P,(39.(=.(>.+4<>20.R2.)(?.R2.+4<?08.))(=.(>.+7=798.R2.)(?.R2.+7=;98.)))(1.(15.(0.&8.))A1.R6.(22.R3.)A1.R7.(22.R3.))(4:.R4.R3.)")
(* [comment removed for export] *).
    Proof.
      (intros m m' d dd_H; ddestruct dd_H as (SB & Hd & RD); intros AG). split; [|split; [lia|]].
      - eapply stdout_buffered_agree; [exact SB|]. intros x Hx. apply AG; lia.
      - rewrite (rdn_agree_Z m m'); [exact RD | lia | lia |]. intros x Hx. apply AG; lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L12849618965.72L1509515487.72 L16075491453.73L16077671799.71L36438673573.73L53512850223.71L53519060517.73L5592608096.72 L68646534965.7200000H00I00f01A01a02702O02l03DS3sp04plen2bs5Hplen1r2HrFS3sp04SPlo4plen2bs5Hplen1r2HrS3sp04SPlo4plen2bs5Hplen2HrS3sp04SPlo4plen2bs5Hplen1r2Hr2NES3sp04plen2bs5Hplen2HrS3sp04plen2bs5Hplen1r2HrS3sp04SPlo4plen2bs5Hplen1r2HrS3sp04plen2bs5Hplen1r2Hr". (* [comment removed for export] *)
    #[using="Hvsp SPlo bs Hplen"] Lemma piter_tail : forall (r : nat) (Q : config -> Prop) (mo : Model)
        (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
      MOK mo -> (1 <= r <= 4)%nat ->
      aevtM usegs mo Q
        (MS (mkR (Z_to_bv 64 0x1d5f8) (Z_to_bv 64 (bv_unsigned sp0 - 208)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8) t0 t1 t2
                 (Z_to_bv 64 plen) (Z_to_bv 64 DATA) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 owned) (Z_to_bv 64 (-1)) (Z_to_bv 64 0x5cf70) (Z_to_bv 64 (Z.of_nat (r - 1))) (Z_to_bv 64 0)
                 (Z_to_bv 64 (-2)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
            bvmap_empty (Z_to_bv 64 (if (r =? 1)%nat then 0x1d60c else 0x1d5d4)) (Z_to_bv 32 0) None m (seg_rom usegs)) ->
      aevtM usegs mo Q
        (MS (mkR (Z_to_bv 64 0x1d5f8) (Z_to_bv 64 (bv_unsigned sp0 - 208)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8) t0 t1 t2
                 (Z_to_bv 64 plen) (Z_to_bv 64 DATA) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 owned) (Z_to_bv 64 0) (Z_to_bv 64 0x5cf70) (Z_to_bv 64 (Z.of_nat r)) (Z_to_bv 64 0)
                 (Z_to_bv 64 (-2)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
            bvmap_empty (Z_to_bv 64 0x1d5f8) (Z_to_bv 32 0) None m (seg_rom usegs)).
    Proof.
      intros r Q mo t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m MK Hr K.
      step.                                        (* [comment removed for export] *)
      step.                                        (* [comment removed for export] *)
      ifc true.
      step.                                        (* [comment removed for export] *)
      step.                                        (* [comment removed for export] *)
      rewrite (u_small (Z.of_nat r)) by lia. rewrite swrap32_id by lia.
      replace (Z.of_nat r + -1) with (Z.of_nat (r - 1)) by lia.
      destruct (Nat.eqb_spec r 1) as [->|NE].
      - ifc false. exact K.
      - ifc true. exact K.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "00Z0@L11505503796.146L15047080576.141L16144880061.128L17055038523.145L17061315460.147L17061325264.143L20073309579.127L2220983053.143 L22401552087.141L27318705339.143L28267525695.136L32168731758.145L34301895276.145L34460694057.145L38581424559.145L40039363506.141L41160043580.127L42037730491.145L42039822672.143L42039829252.147L44351294807.115L44971241298.128L45081411243.141L47718591620.77 L4781915919.128 L49876773361.127L52101693566.143L52101704234.147L52107990421.145L52108169754.146L54477486999.141L56759158153.146L56759370246.145L56763568491.144L56765667309.143L56765676985.147L60611026206.134L6196536613.141 L64043943924.146L65689690084.128L66693783798.145L67010277494.14500000S01101P02202U03803T04:04]05F05l06N07I07k08f09D09h0:J0:m0;P0<60<U0=30>Y0?;0?Z0@F0@i0AT0BF0Bi0CL0Co0DR0E50EX0F;0Fb0GE0Gk0Hb0IYS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a2H3S3sp04plen2bs5Hplen1r1d2Hr3HdrS3sp04plen2bs5Hplen2r'1d2Hr3HdrS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a1HS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a2H4S3sp04plen2bs5Hplen1r1d2Hr3Hdr1a2HaS3sp04plen2bs5Hplen1d2Hr3HdrS3sp04DATA4plen2bs5Hplen1r1d2Hr3Hdr2B2S3sp04SPlo4plen2bs5Hplen1r1d2Hr3HdrS3sp04DATA4plen2bs5Hplen5HDATA1r1d2Hr3HdrS3sp04SPlo4plen2bs5Hplen1r1d2Hr2Hd3HdrS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a1CS3sp04SPlo4DATA4plen2bs3Hbs5Hplen5HDATA1r1d2Hr3Hdr3Hlo1i2HiS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a1CS3sp04SPlo4DATA4plen2bs3Hbs5Hplen5HDATA1r1d2Hr3Hdr3Hhi1i2HiS3sp04plen2bs5Hplen1r1d2Hr3HdrS3sp04SPlo4plen2bs5Hplen1d2Hr2Hd3HdrS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a1HS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a2HaS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a2H3S3sp04SPlo4plen2bs5Hplen1r1d2Hr2Hd3HdrS3sp04plen2bs5Hplen2r'1d2Hr3HdrS3sp04plen2bs5Hplen1r1d2Hr3HdrS3sp03fs04DATA4plen5owned2bs2b15Hplen1d2ra2t02t12t22a02a12a22a32a42a52a62a72s32t32t42t52t61m2mo2Hr3HdrS3sp04plen2bs5Hplen2r'1d2Hr2Hd3HdrS3sp04plen2bs5Hplen1d2Hr2Hd3HdrS3sp04SPlo4plen2bs5Hplen1r1d2Hr3Hdr3Hlo1a2HaS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a2H2S3sp04SPlo4plen2bs5Hplen1r1d2Hr3Hdr3Hlo1a1HS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a2H24SPlo2Hd3Hlo2H4S3sp04SPlo4plen2bs5Hplen1r1d2Hr3HdrS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a2H1S3sp04plen2bs5Hplen1r1d2Hr3Hdr1a2HaS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a2HaS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a2HaS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a2H1S3sp04SPlo4plen2bs5Hplen1r1d2Hr3HdrS3sp04SPlo4plen2bs5Hplen1r1d2Hr3Hdr3HloS3sp04plen2bs5Hplen1r1d2Hr3Hdr1a2H3S3sp04SPlo4plen2bs5Hplen1r1d2Hr2Hd3HdrS3sp04SPlo4DATA4plen2bs3Hbs5Hplen5HDATA1r1d2Hr3Hdr1i2HiS3sp04SPlo4DATA4plen2bs3Hbs5Hplen5HDATA1r1d2Hr3Hdr1i2Hi". (* [comment removed for export] *)
    #[using="Hvsp Htid SPlo SPhi SPal HSTAT SIFP FUZZ Hbs Hplen HDATA"] Lemma ploop : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pr,$1?.Pd,$2.PLB,(13.$14.)Pra,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps3,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(15.(0.&8.))Pmo,$16.Ph,(10.$11.(12.Vsp0,)VHI,)P,(70.#1.R17.)P,(>.=R17.)P,(>.(:.R18.(20.R19.))+4.)P,(6:.=R18.R6.R5.R4.)P,(4:.R7.R1:.)(3:.$11.(3;.(3<.(3=.R19.(5.&40.(29.(4.&40.Vsp0,)+=0.))(5.&40.+10800.)(5.&40.+5=0<8.)R18.R17.R16.(5.&40.Vplen,)(5.&40.VDATA,)R15.R14.R13.R12.R11.R10.R?.R>.(5.&40.Vowned,)R=.(5.&40.+5<?70.)(5.&40.(20.R1<.))(5.&40.=)(5.&40.-2.)(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R<.R;.R:.R9.)(3>.&5.(0.&40.))(5.&40.+1=5=4.)(5.&20.=)(3?.(0.&40.))R8.(40.$11.))R7.)(41.(42.+1.(48.(71.(47.R1;.)R1<.)))(43.(44.(5=.=Vb1,))Vfs0,)))")
(* [comment removed for export] *).
    Proof.
      induction r as [|r IH]; intros d LB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 m mo h Hr Hd Hdr P OP; [lia|].
      pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ (pl_heap _ _ _ _ _ P)) as MK.
      apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs).
      apply (pcall LB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m mo h P).
      intros t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' h' LBx P' MF AG'.
      pose proof (out_pend_agree m m' d OP AG') as OP'. clear P MK OP.
      pose proof P' as [BM TR HH IB IO HT FS FD1 BY CR SIc AX].
      pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ HH) as MK. pose proof MK as MK2; destruct MK2 as [Hh Hl].
      apply aevtM_done.
      change (MS ?Rx bvmap_empty ?pcx (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pcx Mx rom).
      destruct (pn_mem_of m' h' _ mo' d BM HH OP' ltac:(lia)) as [canw PNM].
      refine (printfN sp0 mo' Hvsp Hh Hl (0x7d798 + 2 * d) _ m' canw _ _ _ _ _ PNM _ _);
        [ norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | ].
      intros v0 v1 v2 va0 va1 va2 va3 va4 va5 va6 va7 v3 v4 v5 v6 m2 PP. norm_getr. change Ubsan.M.loaded_segments with usegs.
      pose proof (out_pend_next m' m2 d OP' ltac:(lia) PP) as OP2.
      assert (P2 : PL 0 (LBx ++ LB) m2 mo' h').
      { destruct PP as [AG MU GR WM SB' BY'].
        assert (AG2 : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 - 208) -> ~ (0x4ce20 <= a < 0x4cf08) ->
                      ~ (0x7d798 <= a < 0x7db98) -> m2 (wa a) = m' (wa a)).
        { intros a H1 H2 H3 H4. pose proof (AG (wa a)) as E. unfold wa in E. rewrite u_small in E by lia. apply E; lia. }
        split.
        - eapply (bmem_agree m' m2 0 0 BM); [intros a H1 H2 H3 H4 H5; apply AG2; lia | exact WM | right; right; lia].
        - eapply rw_cells_transport; [exact TR | exact MU | exact WM |]. cbn. unfold TRF. cbn [cells_size csize Nat.add]. repeat split; lia.
        - eapply (heap_frame usegs (U_layout sp0) HI) with (SP := bv_unsigned sp0 - 8388608);
            [ exact HH | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia | | exact WM ].
          intros a Ha Hnc. apply AG2; [lia | | |]; intros C; apply Hnc.
          + left. rewrite HT. lia.
          + right; left. cbn [hl_data_lo hl_data_hi hl_static U_layout]. unfold U_static. lia.
          + right; left. cbn [hl_data_lo hl_data_hi hl_static U_layout]. unfold U_static. lia.
        - exact IB.
        - exact IO.
        - exact HT.
        - exact FS.
        - exact FD1.
        - ddestruct BY as (B1 & B2 & B3). split; [lia|]. split; [lia|]. intros i Hi.
          unfold mrd. rewrite AG2 by lia. apply B3. exact Hi.
        - exact CR.
        - eapply (si_frame SI); [exact SIc|]. intros a Ha NO. pose proof (SIFP a NO). apply AG2; lia.
        - eapply atx_agree; [exact AX | intros a Ha; apply AG2; lia | exact WM]. }
      replace (zero_lines (Z.to_nat d + S r)) with (zero_lines (Z.to_nat (d + 1) + r)) by (f_equal; lia).
      clear P' BM TR HH BY OP' SIc AX.
      apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs).
      apply (piter_tail (S r)); [exact MK | lia |]. change (S r - 1)%nat with (r - 0)%nat. rewrite Nat.sub_0_r.
      destruct r as [|r'].
      - (* [comment removed for export] *)
        cbn [Nat.eqb].
        replace (Z.to_nat (d + 1) + 0)%nat with (Z.to_nat (d + 2 - 1)) by lia.
        apply (last_free (d + 2) (LBx ++ LB) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 mo' h'); [lia | exact P2 | replace (d + 2 - 1) with (d + 1) by lia; exact OP2].
      - (* [comment removed for export] *)
        cbn [Nat.eqb]. apply aevtM_done.
        apply (IH (d + 1) (LBx ++ LB) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 mo' h'); [lia | lia | lia | exact P2 | exact OP2].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    #[using="Type"] Lemma zero_lines_app : forall a b, zero_lines (a + b) = zero_lines a ++ zero_lines b.
    Proof. induction a as [|a IH]; intros b; [reflexivity|]. cbn [zero_lines Nat.add app]. rewrite IH. reflexivity. Qed.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00W0@L15045003137.125L15047080576.136L15285258199.136L15930220084.125L17055038523.140L17061315460.142L17061325264.138L2220983053.138 L27318705339.138L31206959662.125L32168731758.140L34301895276.140L34460694057.140L3749949990.125 L38581424559.140L38796153428.141L40039363506.136L42037730491.140L42037910324.141L42039822672.138L42039829252.142L52101693566.138L52101704234.142L52107990421.140L52108169754.141L52978745750.100L56759158153.141L56759370246.140L56763568491.139L56765667309.100L56765667309.138L56765676985.142L64543194770.134L66693783798.140L66710138795.136L67010277494.140L7466548286.124 L9333936356.111 L9928079495.136 00000L00h01I01h02H02i03J03n04U05605V06O06o07S08L09;09W0:70:X0;90;Z0<D0<e0=N0=o0>P0?10?R0@30@T0A50AV0B20Bg0CC0D80DT0E50EVS3sp04plen2bs5Hplen5calls2HcS3sp04plen2bs5Hplen5calls2HcS3sp04SPlo4plen2bs5Hplen5calls2HcS3sp04plen2bs5Hplen5calls2Hc2C1S3sp04plen2bs5Hplen5calls2Hc1a1HS3sp04plen2bs5Hplen5calls2Hc1a2H4S3sp04plen2bs5Hplen5calls2Hc1a2HaS3sp04DATA4plen2bs5Hplen5calls2Hc2B2S3sp04DATA4plen2bs5Hplen5HDATA5calls2HcS3sp04SPlo4plen2bs5Hplen5calls2HcS3sp04plen2bs5Hplen5calls2Hc1a1CS3sp04SPlo4DATA4plen2bs3Hbs5Hplen5HDATA5calls2Hc3Hlo1i2HiS3sp04plen2bs5Hplen5calls2Hc1a1CS3sp04SPlo4plen2bs5Hplen5calls2Hc2C1S3sp04SPlo4DATA4plen2bs3Hbs5Hplen5HDATA5calls2Hc3Hhi1i2HiS3sp04SPlo4SPal4plen2bs5Hplen5calls2Hc3Hlo1a2H4S3sp04plen2bs5Hplen5calls2HcS3sp04plen2bs5Hplen5calls2Hc1a1HS3sp04plen2bs5Hplen5calls2Hc1a2H3S3sp04plen2bs5Hplen5calls2Hc1a2HaS3sp04plen2bs5Hplen5calls2Hc1a2H3S3sp04SPlo4plen2bs5Hplen5calls2Hc3Hlo1a2HaS3sp04plen2bs5Hplen5calls2Hc1a2H2S3sp04SPlo4plen2bs5Hplen5calls2Hc3Hlo1a1HS3sp04plen2bs5Hplen5calls2Hc1a2H2S3sp04plen2bs5Hplen5calls2Hc1a2HaS3sp04plen2bs5Hplen5calls2Hc1a2H1S3sp04plen2bs5Hplen5calls2Hc1a2HaS3sp04plen2bs5Hplen5calls2Hc1a2HaS3sp04plen2bs5Hplen5calls2Hc1a2HaS3sp04plen2bs5Hplen5calls2Hc1a2HaS3sp04plen2bs5Hplen5calls2Hc1a2H1S3sp04plen2bs5Hplen5calls2HcS3sp04SPlo4DATA4plen2bs3Hbs5Hplen5HDATA5calls2Hc1i2HiS3sp04plen2bs5Hplen5calls2HcS3sp04SPlo4DATA4plen2bs3Hbs5Hplen5HDATA5calls2Hc1i2HiS3sp04plen2bs5Hplen5calls2HcS3sp04SPlo4plen2bs5Hplen5calls2HcS3sp04SPlo4plen2bs5Hplen5calls2Hc". (* [comment removed for export] *)
    #[using="Hvsp Htid SPlo SPhi SPal HSTAT SIFP FUZZ Hbs Hplen HDATA"] Lemma piter1 : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pcalls,$1?.PLB,(13.$14.)Pra,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps3,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(15.(0.&8.))Pmo,$16.Ph,(10.$11.(12.Vsp0,)VHI,)P,(=.(70.#1.R16.)(70.R16.#4.))P,(6:.=R16.R4.R3.R2.)P,(49.R5.)(3:.$11.(3;.(3<.(3=.R17.(5.&40.(29.(4.&40.Vsp0,)+=0.))(5.&40.+10800.)(5.&40.+5=0<8.)R16.R15.R14.(5.&40.Vplen,)(5.&40.VDATA,)R13.R12.R11.R10.R?.R>.R=.R<.(5.&40.Vowned,)R;.(5.&40.+5<?70.)(5.&40.(20.R19.))(5.&40.=)(5.&40.-2.)(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R:.R9.R8.R7.)(3>.&5.(0.&40.))(5.&40.+1=5=4.)(5.&20.=)(3?.(0.&40.))R6.(40.$11.))R5.)(41.(42.+1.(48.R19.))(43.(44.(5=.=Vb1,))Vfs0,)))")
(* [comment removed for export] *).
    Proof.
      intros calls LB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 m mo h Hc P OPR.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ (pl_heap _ _ _ _ _ P)) as MK.
      apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs).
      apply (pcall LB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m mo h P).
      intros t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' h' LBx P' MF AG'.
      assert (OPR' : forall a : Z, 0x4ce20 <= a < 0x4cf08 -> m' (wa a) = None).
      { intros a Ha. rewrite AG' by lia. apply (proj1 OPR). exact Ha. }
      clear P MK OPR.
      pose proof P' as [BM TR HH IB IO HT FS FD1 BY CR SIc AX].
      pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ HH) as MK. pose proof MK as MK2; destruct MK2 as [Hh Hl].
      apply aevtM_done.
      replace calls with (1 + (calls - 1))%nat at 2 by lia. rewrite zero_lines_app.
      eapply rz_conseq; [ | apply (t_emit_W_app 1) ].
      change (MS ?Rx bvmap_empty ?pcx (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pcx Mx rom).
      destruct (fw_mem_of m' h' _ mo' BM OPR' HH) as [canw FWM].
      refine (printf1 sp0 mo' Hvsp Hh Hl FD1 _ m' canw _ _ _ _ _ FWM _ _ _);
        [ norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity
        | apply t_emit_has_nil | ].
      intros v0 v1 v2 va0 va1 va2 va3 va4 va5 va6 va7 v3 v4 v5 v6 m2 PP. norm_getr. change Ubsan.M.loaded_segments with usegs.
      assert (OP2 : out_pend m2 0).
      { destruct PP as [AG MU GR WM SB']. split; [rewrite Z.mul_0_r, Z.add_0_r; exact SB' |]. split; [lia|]. reflexivity. }
      assert (P2 : PL 0 (LBx ++ LB) m2 mo' h').
      { destruct PP as [AG MU GR WM SB'].
        assert (AG2 : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 - 208) -> ~ (0x4ce20 <= a < 0x4cf08) ->
                      ~ (0x7d798 <= a < 0x7db98) -> m2 (wa a) = m' (wa a)).
        { intros a H1 H2 H3 H4. pose proof (AG (wa a)) as E. unfold wa in E. rewrite u_small in E by lia. apply E; lia. }
        split.
        - eapply (bmem_agree m' m2 0 0 BM); [intros a H1 H2 H3 H4 H5; apply AG2; lia | exact WM | right; right; lia].
        - eapply rw_cells_transport; [exact TR | exact MU | exact WM |]. cbn. unfold TRF. cbn [cells_size csize Nat.add]. repeat split; lia.
        - eapply (heap_frame usegs (U_layout sp0) HI) with (SP := bv_unsigned sp0 - 8388608);
            [ exact HH | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia | | exact WM ].
          intros a Ha Hnc. apply AG2; [lia | | |]; intros C; apply Hnc.
          + left. rewrite HT. lia.
          + right; left. cbn [hl_data_lo hl_data_hi hl_static U_layout]. unfold U_static. lia.
          + right; left. cbn [hl_data_lo hl_data_hi hl_static U_layout]. unfold U_static. lia.
        - exact IB.
        - exact IO.
        - exact HT.
        - exact FS.
        - exact FD1.
        - ddestruct BY as (B1 & B2 & B3). split; [lia|]. split; [lia|]. intros i Hi.
          unfold mrd. rewrite AG2 by lia. apply B3. exact Hi.
        - exact CR.
        - eapply (si_frame SI); [exact SIc|]. intros a Ha NO. pose proof (SIFP a NO). apply AG2; lia.
        - eapply atx_agree; [exact AX | intros a Ha; apply AG2; lia | exact WM]. }
      clear P' BM TR HH BY OPR' SIc AX.
      apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs).
      apply (piter_tail calls); [exact MK | lia |].
      destruct (Nat.eqb_spec calls 1) as [C1|C1].
      - (* [comment removed for export] *)
        rewrite C1. cbn [Nat.eqb Nat.sub].
        change (1 - 1)%nat with (Z.to_nat (1 - 1)).
        apply (last_free 1 (LBx ++ LB) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 mo' h'); [lia | exact P2 | exact OP2].
      - (* [comment removed for export] *)
        replace (calls =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; exact C1). apply aevtM_done.
        change (zero_lines (calls - 1)) with (zero_lines (Z.to_nat 0 + (calls - 1))).
        apply (ploop (calls - 1) 0 (LBx ++ LB) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 mo' h'); [lia | lia | lia | exact P2 | exact OP2].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End PLoop.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition CALLS (cl : Z) : nat := if cl =? 0 then 1%nat else S (Z.to_nat (bv_unsigned (nth 2 fdata (Z_to_bv 8 0)) mod 4)).
  Definition SUCC (cl : Z) : TSet := t_emit (W 1 (zero_lines (CALLS cl))) (t_exit (exit_code 0) fs0).
  Definition TAIL (cl plen : Z) : TSet :=
    if plen =? 0 then SUCC cl
    else t_alt2 (t_emit (W 1 []) (t_exit (exit_code (status 2 (nth 1 fdata (Z_to_bv 8 0)))) fs0)) (SUCC cl).

  #[using="Type"] Lemma status0 : forall b, status 0 b = 0.
  Proof. intros b. unfold status. destruct (128 <=? bv_unsigned b); reflexivity. Qed.

  (* [comment removed for export] *)
  Section TP.
    Variables (buf cap cl plen : Z) (junk : list byte) (s6m : word).
    Hypothesis BR : block_range (U_layout sp0) buf cap.
    Hypothesis LCAP : Z.of_nat (length fdata) <= cap.
    Hypothesis CAPMAX : cap <= 67108864.
    Hypothesis Hcl : 0 <= cl.
    Hypothesis Hplen : 0 <= plen.
    Hypothesis HL : cl + 6 + plen = Z.of_nat (length fdata).
    Let b1 : byte := nth 1 fdata (Z_to_bv 8 0).
    Let PAY : Z := buf + 2 + cl + 4.
    Let pay : list byte := skipn (Z.to_nat (cl + 6)) fdata.
    Let TRFm : list cell := TRF junk s6m b1 (Z_to_bv 64 plen) (Z_to_bv 64 PAY) (Z_to_bv 64 cl) (Z_to_bv 64 (buf + 2)) buf.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L40665719618.4800000]S3sp04SPlo5fdata3buf2cl4plen3Hcl5Hplen2HL3PAY". (* [comment removed for export] *)
    #[using="sp0 Hvsp SPlo buf Hcl Hplen HL PAY"] Lemma pay_len : Z.of_nat (length pay) = plen.
    Proof. subst pay. rewrite skipn_length. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L3767899476.50 L40829935281.49L43583347225.4900000M00c019S3sp04SPlo5fdata3buf2cl3PAY1HS3sp05fdata3buf2cl3PAYS3sp05fdata3buf2cl3PAY". (* [comment removed for export] *)
    #[using="sp0 Hvsp SPlo buf PAY"] Lemma CALLS_range : (1 <= CALLS cl <= 4)%nat.
    Proof. unfold CALLS. destruct (cl =? 0); [lia|]. pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 fdata (Z_to_bv 8 0))) 4 ltac:(lia)). lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L13174506721.83L2201991189.83 L29865706316.85L45100709583.83L58228553743.8300000W01G02602]036S3sp05fdata3buf2cl4plen5Hplen3PAY2P02CRS3sp04SPlo5fdata3buf2cl4plen5Hplen3PAY2P03Hlo2CRS3sp04SPlo5fdata3buf3cap2cl4plen3PAY2P02CR1a2HaS3sp05fdata3buf2cl4plen5Hplen3PAY2P02CRS3sp05fdata3buf2cl3PAY2CR". (* [comment removed for export] *)
    #[using="Hvsp Htid SPlo SPhi SPal HSTAT SI SIFP FUZZ Hplen"] Lemma tp_empty : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pra,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(15.(0.&8.))Pmo,$16.Ph,(10.$11.(12.Vsp0,)VHI,)P,(1.$2.Vplen,=)P,(4;.R4.)P,(55.=R5.)P,(49.R6.)P,(18.$11.R7.(29.(4.&40.Vsp0,)+=0.)VTRFm,)P,(17.$11.(12.Vsp0,)VHI,R6.(19.(2>.$2.$2.)(2?.$2.$2.Vbuf,Vcap,)(1<.(2>.$2.$2.)))R8.R7.)P,(1.$2.(30.$11.(12.Vsp0,)VHI,R7.)(4.&40.Vsp0,))P,(1.$31.(32.R9.)Vfs0,)P,(1.(15.$34.)(35.(36.R:.)(5.&40.+1.))(37.$34.(38.(5.&40.+1.))))(3:.$11.(3;.(3<.(3=.R1>.(5.&40.(29.(4.&40.Vsp0,)+=0.))(5.&40.+10800.)(5.&40.+5=0<8.)R1=.R1<.R1;.(5.&40.Vplen,)(5.&40.VPAY,)R1:.R19.R18.R17.R16.R15.R14.R13.(5.&40.Vcl,)(5.&40.(:.Vbuf,+2.))(5.&40.+5<?70.)(5.&40.(20.(72.Vcl,)))R12.R11.(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R10.R?.R>.R=.)(3>.&5.(0.&40.))(5.&40.+1=5<4.)(5.&20.=)(3?.(0.&40.))R<.(40.$11.))R;.)(73.Vcl,))")
(* [comment removed for export] *).
    Proof.
      intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 m mo h P0 BM AX OPR TR HH HT FS FD1.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof CALLS_range as CR.
      pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ HH) as MK.
      apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). step. step. step. step. apply aevtM_done.   (* [comment removed for export] *)
      unfold SUCC. replace (exit_code 0) with (exit_code (status 0 b1)) by (rewrite status0; reflexivity).
      apply (piter1 0x5cf80 plen 0 buf cap [] junk s6m b1 (Z_to_bv 64 plen) (Z_to_bv 64 PAY) (Z_to_bv 64 cl) (Z_to_bv 64 (buf + 2))
               ltac:(cbn; lia) ltac:(lia) ltac:(lia) (CALLS cl) [(buf, cap)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m mo h CR); [| exact OPR].
      split; try assumption; try (apply si_of_out_pristine; assumption).
      - left. reflexivity.
      - left. reflexivity.
      - apply bytes_at_nil. lia.
      - intros a Ha. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00l0@L15047358524.133L1550461168.147 L19562928109.133L19574726587.126L20319390318.146L20319633490.137L2462960893.139 L24648805744.132L25965980603.132L29350650903.146L30042381628.137L35221082670.133L36184341560.133L36184730655.132L38124017691.119L38125802027.115L39209403577.146L39428382747.115L39430302251.119L39430479935.91 L40039641358.137L40041656717.91 L41062624625.133L41180729673.137L41181024501.141L41181027061.142L41183227509.141L41333171259.91 L41747807492.132L44395218905.147L44395228557.147L45098548336.146L45100709583.91 L45302818031.142L45302820591.141L45303115603.137L45304811631.141L46048144290.133L48756858459.126L53140297196.91 L53410765808.147L53517065099.132L53517158923.116L56765667309.147L56765676985.147L57184993495.133L57428328620.133L5744826032.141 L58076399520.133L59063334394.142L59274000553.115L59286650772.125L60080974485.141L60780294177.91 L63316670876.141L64048045272.133L67809407145.116L67809409705.127L68047693700.146L68110426016.13300000P01501m02R03203R04D05P06R07I08208k09h0:a0;:0;S0<f0=I0=l0>O0>o0?H0@50@Y0A=0Aa0BE0B^0C>0DL0E60FE0GI0HG0IE0JC0KA0Kf0LB0L[0M@0M\0N50NZ0O?0P90QH0Qm0S:0T40TM0Ti0UV0Uo0WK0XG0X`0Y<0Ya0ZZS3sp05fdata3buf2cl3PAY3pay2CR2A3S3sp05fdata3buf2cl3PAY3pay2CR2A31a2HaS3sp04SPlo5fdata3buf2cl4plen3Hcl2HL3PAY2Hp2CR3BR12A33BQ1S3sp05fdata3buf3cap2cl4LCAP3PAY2CR2A3S3sp05fdata3buf2cl3PAY3pay2CR2A3S3sp05fdata3buf2cl3PAY3pay2CR2A3S3sp05fdata3buf2cl4plen3PAY2s62s72CR2A35regs21i2HiS3sp04SPlo5fdata3buf3cap2cl4plen4LCAP3Hcl2HL3pay2CR3BR13BR52A33BQ13BQ55APARTS3sp04SPlo5fdata3buf3cap2cl4plen4LCAP2HL3pay3Hhi2CR3BR13BR42A33BQ1S3sp05fdata3buf2cl4plen5Hplen3PAY3pay2CR2A33BQ13BQ43BQ5S3sp05fdata3buf2cl4plen3PAY3pay2CR2A33PLNS3sp04SPlo5fdata3buf2cl4plen3PAY3pay2Hp2CR3BR12A33BQ13PLNS3sp04SPlo5fdata3buf2cl4plen3PAY3pay2Hp3Hhi2CR3BR12A33BQ13BQ4S3sp04SPlo5fdata3buf2cl4plen3PAY2Hp3Hhi2CR3BR12A33BQ13BQ4S3sp05fdata3buf2cl3PAY2CRS3sp05fdata3buf2cl3PAY2CRS3sp04SPlo5fdata3buf3cap2cl4plen4LCAP3Hcl2HL3PAY3pay2Hp2CR3BR13BR52A33BQ13BQ55APARTS3sp04SPlo4SPhi5fdata3buf2cl3PAY2CRS3sp04SPlo4SPhi5fdata3buf2cl3PAY2CRS3sp04SPlo4SPhi5fdata3buf2cl3PAY2CRS3sp05fdata3buf2cl3PAY3pay2CR2A3S3sp05fdata3buf2cl3PAY2CRS3sp04SPlo5fdata3buf2cl3Hcl3pay2CR3BR12A33BQ1S3sp05fdata3buf2cl3PAY3pay2CR2A33BQ1S3sp05fdata3buf2cl3PAY3pay2CR2A33BQ1S3sp05fdata3buf2cl3PAY3pay2CR2A33BQ1S3sp05fdata3buf2cl3PAY3pay2CR2A33BQ1S3sp05fdata3buf2cl3PAY2CRS3sp05fdata3buf2cl3PAY2CR2A33BQ1S3sp04SPlo5fdata3buf3cap2cl4plen4LCAP3Hcl2HL3PAY3pay2Hp2CR3BR12A33BQ13BQ51a2HaS3sp05fdata3buf2cl4plen3PAY3pay2CR2A31a2H5S3sp04SPlo5fdata3buf3cap2cl4plen4LCAP6CAPMAX3Hcl5Hplen2HL3PAY3pay2CR3BR12A33BQ1S3sp04SPlo5fdata3buf3cap2cl4plen4LCAP6CAPMAX3Hcl5Hplen2HL3PAY2CR3BR1S3sp04SPlo5fdata3buf2cl4plen3PAY3pay3Hhi2CR3BR12A33BQ13BQ43PLNS3sp04SPlo5fdata3buf2cl4plen3PAY3pay3Hhi2CR3BR12A33BQ13BQ43PLNS3sp04SPlo5fdata3buf2cl4plen3PAY3pay3Hhi2CR3BR12A33BQ13BQ43PLNS3sp04SPlo5fdata3buf2cl4plen3PAY3pay3Hhi2CR3BR12A33BQ13BQ43PLNS3sp05fdata3buf2cl4plen3PAY3pay2CR2A3S3sp05fdata3buf2cl3PAY2CR2A3S3sp05fdata3buf2cl3PAY2CRS3sp05fdata3buf2cl3PAY3pay2CR2A31a2HaS3sp05fdata3buf2cl3PAY2CR2A3S3sp05fdata3buf2cl3PAY2CRS3sp05fdata3buf2cl3PAY3pay2CR2A31a2HaS3sp05fdata3buf2cl3PAY3pay2CR2A31a2H1S3sp04SPlo5fdata3buf2cl4plen3PAY3pay3Hhi2CR3BR12A33BQ13BQ4S3sp04SPlo5fdata3buf3cap2cl4plen4LCAP6CAPMAX3Hcl5Hplen2HL3PAY3pay2CR3BR12A33BQ1S3sp05fdata3buf2cl3PAY3pay2CR2A31x2H1S3sp04SPlo5fdata3buf3cap2cl4plen4LCAP3Hcl2HL3PAY3pay2Hp3Hhi2CR3BR13BR42A33BQ1S3sp04SPlo5fdata3buf2cl4plen3PAY3pay2CR3BR12A33BQ13BQ43PLNS3sp05fdata3buf2cl3PAY2CRS3sp05fdata3buf2cl3PAY2CR2A3S3sp05fdata3buf2cl4plen3PAY3pay2CR2A33BQ43BQ5S3sp05fdata3buf2cl3PAY2CRS3sp04SPlo5fdata3buf3cap2cl4plen4LCAP3Hcl2HL3PAY3pay2Hp2CR3BR13BR52A33BQ13BQ55APART3PLN1x2H2S3sp04SPlo5fdata3buf2cl4plen3Hcl2HL3PAY3pay2Hp2CR3BR12A33BQ1S3sp05fdata3buf2cl3PAY2CRS3sp05fdata3buf2cl3PAY2CR2A3S3sp05fdata3buf2cl4plen3PAY3pay2CR2A3S3sp04SPlo5fdata3buf2cl4plen3PAY3pay2Hp2CR3BR12A33BQ13PLN". (* [comment removed for export] *)
    #[using="Hvsp Htid SPlo SPhi SPal HSTAT NS MRZ SI SIFP FUZZ BR LCAP CAPMAX Hcl Hplen HL pay"] Lemma tp_copy : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pk,$1?.Pra,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(15.(0.&8.))Pmo,$16.Ph,(10.$11.(12.Vsp0,)VHI,)P,(?.=Vplen,)P,(4;.R4.)P,(55.=R5.)P,(49.R6.)P,(18.$11.R7.(29.(4.&40.Vsp0,)+=0.)VTRFm,)P,(17.$11.(12.Vsp0,)VHI,R6.(19.(2>.$2.$2.)(2?.$2.$2.Vbuf,Vcap,)(1<.(2>.$2.$2.)))R8.R7.)P,A3.VDRV,(74.R1<.)R7.R8.P,(1.$2.(30.$11.(12.Vsp0,)VHI,R8.)(4.&40.Vsp0,))P,(1.$31.(32.R:.)Vfs0,)P,(1.(15.$34.)(35.(36.R;.)(5.&40.+1.))(37.$34.(38.(5.&40.+1.))))P,(64.$11.R=.Vbuf,Vfdata,)(3:.$11.(3;.(3<.(3=.R20.(5.&40.(29.(4.&40.Vsp0,)+=0.))(5.&40.+10800.)(5.&40.+5=0<8.)R1?.R1>.R1=.(5.&40.Vplen,)(5.&40.VPAY,)R1<.R1;.R1:.R19.R18.R17.R16.R15.(5.&40.Vcl,)(5.&40.(:.Vbuf,+2.))(5.&40.+5<?70.)(5.&40.(20.(72.Vcl,)))R14.R13.(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R12.R11.R10.R?.)(3>.&5.(0.&40.))(5.&40.+1=578.)(5.&20.=)(3?.(0.&40.))R>.(40.$11.))R=.)(75.(41.(42.+1.(1<.(0.&8.)))(43.(44.(5=.+2.Vb1,))Vfs0,))(73.Vcl,)))")
(* [comment removed for export] *).
    Proof.
      intros k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 m mo h Hp BM AX OPR TR HH HD HT FS FD1 BY.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof CALLS_range as CR.
      dpose BR as (BR1 & BR2 & BR3 & BR4 & BR5). rewrite (U_alloc_ceiling_eq sp0 Hvsp) in BR4.
      cbn [hl_img_lo hl_img_hi U_layout] in BR5.
      pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ HH) as MK.
      apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). step. step. apply aevtM_done.
      eapply (MRZ k) with (lo := bv_unsigned sp0 - 8388608) (n := plen);
        [ exact HH | exact HD
        | rewrite u_small by lia; apply bmem_stk; [exact BM | lia]
        | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia
        | rewrite u_small by lia; cbn [hl_stack U_layout]; lia
        | exact (bm_minv _ BM)
        | reflexivity
        | rewrite u_small by lia; rewrite HT; lia
        | reflexivity
        | lia
        | apply t_emit_has_nil
        | unfold SUCC; apply t_emit_has_nil
        | | ].
      - (* [comment removed for export] *)
        intros t0' t1' t2' a1q a2q a3q a4q a5q a6q a7q t3' t4' t5' t6' m' mo' h' MI' ST' MF HP HT' HH' MK'.
        rewrite u_small in ST', HP by lia.
        replace (ret_pc (Z_to_bv 64 0x1d580)) with (Z_to_bv 64 0x1d580 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
        assert (BM' : bmem m') by (eapply bmem_heap; [exact BM | exact HP | exact MI' | eapply statics_ok_pres; [exact (bm_statics _ BM) | exact HP] | exact ST' | lia]).
        apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). step. ifc true. step. step. apply aevtM_done.   (* [comment removed for export] *)
        eapply (ret_to_fin 2 [] buf cap [(buf, cap)] junk b1 s6m);
          [ exact HH' | left; reflexivity | rewrite HT', HT; reflexivity | rewrite (mo_frame_fs _ _ MF); exact FS
          | apply bmem_fin; [exact BM' | exists true; apply atx_atexit; eapply atx_heap; [exact AX | exact HP]]
          | apply SO_none; eapply proj1; eapply out_pristine_heap; [exact OPR | exact HP]
          | intros C; exfalso; apply C; reflexivity | right; reflexivity
          | eapply heap_pres_rw_cells; [exact HP | exact TR | apply client_range_stack; lia] ].
      - (* [comment removed for export] *)
        intros t0' t1' t2' a1q a2q a3q a4q a5q a6q a7q t3' t4' t5' t6' m' mo' h' A3 junk3 MI' ST' MF HP HT' BRn HH' MK' RW _.
        rewrite u_small in ST', HP by lia.
        replace (ret_pc (Z_to_bv 64 0x1d580)) with (Z_to_bv 64 0x1d580 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
        dpose BRn as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5). rewrite (U_alloc_ceiling_eq sp0 Hvsp) in BQ4.
        cbn [hl_img_lo hl_img_hi U_layout] in BQ5.
        pose proof (heap_blocks usegs (U_layout sp0) HI _ _ _ _ HH') as [_ APART]. cbn [blocks_apart] in APART.
        destruct APART as [APART _]. specialize (APART buf cap ltac:(left; reflexivity)).
        assert (BM' : bmem m') by (eapply bmem_heap; [exact BM | exact HP | exact MI' | eapply statics_ok_pres; [exact (bm_statics _ BM) | exact HP] | exact ST' | lia]).
        pose proof (heap_pres_bytes_at usegs (U_layout sp0) _ _ _ _ _ _ HP BY ltac:(eapply client_range_block; [left; reflexivity | lia | lia])) as BY'.
        pose proof (heap_pres_rw_cells usegs (U_layout sp0) _ _ _ _ _ _ HP TR ltac:(apply client_range_stack; cbn; lia)) as TR'.
        pose proof (out_pristine_heap _ _ m m' OPR HP) as OPR'.
        pose proof (atx_heap 0 _ _ m m' AX HP) as AX'.
        pose proof MK' as MK3; destruct MK3 as [Hh' Hl'].
        apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs).
        step. ifc false.                   (* [comment removed for export] *)
        step. step. step.                  (* [comment removed for export] *)
        step.                              (* [comment removed for export] *)
        apply aevtM_done.
        assert (MC : mcH m' (Z_to_bv 64 A3) (Z_to_bv 64 PAY) plen pay).
        { pose proof pay_len as PLN. split.
          - lia.
          - lia.
          - replace (length pay) with (Z.to_nat plen) by lia.
            pose proof (bytes_at_rdn usegs m' buf fdata (Z.to_nat (cl + 6)) (Z.to_nat plen) BY' ltac:(lia)) as RD.
            replace (buf + Z.of_nat (Z.to_nat (cl + 6))) with PAY in RD by (subst PAY; lia). unfold wa in RD. etransitivity; [exact RD|].
            subst pay. rewrite firstn_all2; [reflexivity|]. rewrite skipn_length. lia.
          - replace (length pay) with (Z.to_nat plen) by lia.
            destruct RW as [_ WRn]. cbn [cells_size csize Nat.add] in WRn.
            pose proof (wr_at_store_ok usegs m' A3 _ 0 (Z.to_nat plen) WRn ltac:(lia) ltac:(lia)) as SO. rewrite Z.add_0_r in SO. exact SO.
          - rewrite !u_small by lia. subst PAY. lia.
          - rewrite u_small by lia. subst PAY. lia.
          - rewrite u_small by lia. lia. }
        change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pc Mx rom).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?R _ _ _) _) _ =>
          destruct (ref_memcpy m' (Z_to_bv 64 A3) (Z_to_bv 64 PAY) plen pay (seg_rom usegs) MC R (Z_to_bv 64 0x1d594)
                      ltac:(apply ret_ok_even; reflexivity)
                      ltac:(norm_getr; reflexivity) ltac:(norm_getr; reflexivity) ltac:(norm_getr; reflexivity) ltac:(norm_getr; reflexivity))
            as (regs2 & RUN & KP)
        end.
        replace (Z_to_bv 64 289344 : word) with (289344%bv : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply (rz_msteps usegs); [exact Hh' | exact Hl' | exact RUN |].
        apply (realizes_getr_ext usegs
                 (mkR (Z_to_bv 64 0x1d594) (Z_to_bv 64 (bv_unsigned sp0 - 208)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8)
                      (getr regs2 5) (getr regs2 6) (getr regs2 7) (Z_to_bv 64 plen) (Z_to_bv 64 PAY) (Z_to_bv 64 A3)
                      (getr regs2 11) (getr regs2 12) (getr regs2 13) (getr regs2 14) (getr regs2 15) (getr regs2 16) (getr regs2 17)
                      (Z_to_bv 64 A3) (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 0x5cf70) (Z_to_bv 64 (Z.of_nat (CALLS cl))) s6
                      s7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
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
        rewrite <- write_to_mem_wbytes. change (Z_to_bv 64 A3) with (wa A3) at 3.
        set (m2 := write_to_mem m' (wa A3) pay).
        pose proof pay_len as PLN.
        assert (HH2 : HEAP usegs (U_layout sp0) HI h' [(A3, plen); (buf, cap)] m2 mo').
        { subst m2. eapply (heap_write usegs (U_layout sp0) HI) with (SP := bv_unsigned sp0 - 8388608);
            [ exact HH' | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia
            | eapply client_wrange_block; [left; reflexivity | lia | lia] | lia | lia ]. }
        assert (AG2 : forall x : Z, 0 <= x < 2 ^ 64 -> ~ (A3 <= x < A3 + plen) -> m2 (wa x) = m' (wa x)).
        { intros x H1 H2. subst m2. apply write_other; lia. }
        assert (WM2 : wmono usegs m' m2) by (subst m2; apply wmono_write; apply wmono_refl).
        assert (BM2 : bmem m2).
        { eapply (bmem_agree m' m2 A3 (A3 + plen) BM'); [intros a H1 H2 H3 H4 H5; apply AG2; lia | exact WM2 | lia]. }
        assert (BY2 : bytes_at usegs m2 A3 pay) by (subst m2; apply bytes_at_write_same; lia).
        assert (TR2 : rw_cells usegs m2 (bv_unsigned sp0 - 208) TRFm).
        { subst m2. apply rw_cells_frame; [exact TR' | lia | lia | cbn; lia]. }
        assert (OPR2 : out_pristine m2) by (destruct OPR' as [O1 O2]; split; intros a Ha; rewrite AG2 by lia; [apply O1| apply O2]; lia).
        assert (AX2 : atx 0 m2) by (eapply atx_agree; [exact AX' | intros a Ha; apply AG2; lia | exact WM2]).
        clearbody m2.
        apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). step. step. step. step. apply aevtM_done.   (* [comment removed for export] *)
        unfold SUCC. replace (exit_code 0) with (exit_code (status 0 b1)) by (rewrite status0; reflexivity).
        apply (piter1 A3 plen A3 buf cap pay junk s6m b1 (Z_to_bv 64 plen) (Z_to_bv 64 PAY) (Z_to_bv 64 cl) (Z_to_bv 64 (buf + 2))
                 PLN ltac:(lia) ltac:(lia) (CALLS cl) [(A3, plen); (buf, cap)] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 mo' h' CR); [| exact OPR2].
        split; try assumption; try (apply si_of_out_pristine; assumption).
        + right; left. reflexivity.
        + right. split; [left; reflexivity | lia].
        + rewrite HT', HT. reflexivity.
        + rewrite (mo_frame_fs _ _ MF). exact FS.
        + rewrite (mo_frame_fds _ _ MF). exact FD1.
        + eapply client_range_block; [left; reflexivity | lia | lia].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End TP.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0?L12334604646.63L14981969176.65L15778296756.65L21788557364.65L21971292696.65L22120147736.65L27816271540.65L30025195366.64L31722891288.65L33825024820.65L34234375064.65L39853128116.65L45874533940.65L51126253464.64L51884795060.65L55410642130.63L56498182552.65L57912504628.65L6274867352.65 L63492974498.63L67856165528.65L67949014923.63L9616775837.61 L9748489524.64 00000500:00?00D00I00N00S00X00]00b00g00l01101601;01@01E01J01O01T01Y01^01c01hS3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp0". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma tr_prologue : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps6,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Ps0v,$2.Ps2v,$2.Ps3v,$2.Ps4v,$2.Pb1,(0.&8.)Pbuf,$2.Pm,P,(0.&40.)(15.(0.&8.))P,(2;.$11.R1.(29.(4.&40.Vsp0,)+800000.)(29.(4.&40.Vsp0,)+80.))(76.$11.Lms',$77.(1=.P,(0.&40.)(15.(0.&8.))Lm',P,(0.&40.)(15.(0.&8.))(1=.(13.(0.&8.))Ljunk,(13.(0.&8.))(=.(1.$77.R3.(3<.(3=.(5.&40.+1=3<0.)(5.&40.(:.(29.(4.&40.Vsp0,)+80.)-50.))(5.&40.+10800.)(5.&40.+5=0<8.)R1;.R1:.R19.(5.&40.R;.)(5.&40.R6.)R18.R17.R16.R15.R14.R13.R12.R11.(5.&40.R:.)(5.&40.R9.)(5.&40.R8.)(8.R7.)R10.(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R?.R>.R=.R<.)(3>.&5.(0.&40.))(5.&40.+1=544.)(5.&20.=)(3?.(0.&40.))R2.(40.$11.)))(=.(78.(19.(2>.$2.$2.)(2?.$2.$2.(29.(4.&40.Vsp0,)+=0.)(29.(4.&40.Vsp0,)+80.))(1<.(2>.$2.$2.)))R5.R2.)(=.(4=.$11.R5.R2.)(18.$11.R2.(29.(4.&40.Vsp0,)+=0.)(5<.R1.R10.R7.(5.&40.R8.)(5.&40.R9.)(5.&40.R:.)(5.&40.R;.)R6.)))))))(3<.(3=.(5.&40.+1=3<0.)(5.&40.(29.(4.&40.Vsp0,)+80.))(5.&40.+10800.)(5.&40.+5=0<8.)R18.R17.R16.(5.&40.R8.)(5.&40.R3.)R15.R14.R13.R12.R11.R10.R?.R>.(5.&40.R7.)(5.&40.R6.)(5.&40.R5.)(8.R4.)R=.(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R<.R;.R:.R9.)(3>.&5.(0.&40.))(5.&40.+1=51<.)(5.&20.=)(3?.(0.&40.))R2.(40.$11.)))")
(* [comment removed for export] *).
  Proof.
    intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 s0v s2v s3v s4v b1 buf m ST.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (munch_refl [(bv_unsigned sp0 - 208, bv_unsigned sp0 - 128)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step.                                              (* [comment removed for export] *)
    carve_frame 80%nat ST.
    replace (bv_unsigned sp0 + -128 + -80) with (bv_unsigned sp0 + -208) in * by lia.
    replace (bv_unsigned sp0 + -128) with (bv_unsigned sp0 - 128) in MU by lia.
    step; lit_store. step; lit_store. step; lit_store. step; lit_store. step; lit_store.
    step; lit_store. step; lit_store. step; lit_store. step; lit_store.          (* [comment removed for export] *)
    apply evt_done.
    lazymatch goal with
    | FRH : rw_cells _ ?mm (bv_unsigned sp0 + -208) (CB 8 ?jk :: _), MUH : munch _ _ ?mm2, WMH : wmono _ _ ?mm3 |- _ =>
        exists mm, jk; split; [reflexivity|]; split; [exact MUH|]; split; [exact WMH|];
        replace (bv_unsigned sp0 - 208) with (bv_unsigned sp0 + -208) by lia; exact FRH
    end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac zlit := try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity);
               try replace (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity);
               try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00W0?L10941586071.73L12730873752.71L17900280306.70L19664886920.69L19679447156.68L19858566552.71L21000097076.71L24358461111.70L27798819992.71L30025195366.70L32465858924.70L33000165740.70L33547404564.73L35901952407.73L37097180948.73L39064127156.71L40163727282.71L45075059508.71L45210756786.71L46140939540.73L46748519700.73L47879549470.68L49557536139.70L49901484876.70L50062819604.73L51096330676.71L52514062606.68L52567164907.68L53389155122.71L53517207447.70L53519189168.70L55686649364.73L57123520052.71L63521357730.70L63943628056.71L6406369644.70 L67495603052.70L67510093848.71L67553191767.7300000I00N00S00a00i00n01301801=01B01V01j02O02h03M03R03W03\03a04F04k05005505I05n06306806@06E06J06O07407907>07C07W07k08008IS3sp04SPlo2HB5Ha_st5Hl_stS3sp0S3sp0S3sp02HB5Ha_stS3sp02HBS3sp0S3sp0S3sp0S3sp0S3sp0S3sp02HB5Ha_st5Hl_stS3sp02HB5Ha_st5Hl_stS3sp04SPlo2HB5Ha_st5Hl_st2s02s12s22s3S3sp04SPlo2HB5Ha_st5Hl_stS3sp04SPlo2HB5Ha_st5Hl_st2s02s12s22s3S3sp0S3sp0S3sp0S3sp0S3sp04SPlo2HB5Ha_st5Hl_st2s02s12s22s3S3sp04SPlo2HB5Ha_st5Hl_st2s02s12s22s3S3sp0S3sp0S3sp02HB5Ha_st5Hl_stS3sp04SPlo2HB5Ha_st5Hl_st2s02s12s22s3S3sp0S3sp0S3sp02HBS3sp0S3sp0S3sp0S3sp04SPlo2HB5Ha_st5Hl_st2s02s12s22s3S3sp0S3sp0S3sp0S3sp02HB5Ha_st5Hl_stS3sp02HB5Ha_st5Hl_stS3sp0S3sp04SPlo2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma tr_atexit : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(15.(0.&8.))P,(2;.$11.R1.(29.(4.&40.Vsp0,)+800000.)(29.(4.&40.Vsp0,)+=0.))P,(2:.$11.R2.)P,(18.$11.R3.+7=353.(19.$1:.(1;.(5.&8.=))(1<.$1:.)))P,(18.$11.R4.+5<?70.(19.$1:.(1;.(5.&8.=))(1<.$1:.)))P,(18.$11.R5.+7=108.(19.$1:.(1;.(5.&8.=))(1<.$1:.)))P,(18.$11.R6.+7=10<.(19.$1:.(4>.(5.&40.=))(19.$1:.(4>.(5.&40.=))(1<.$1:.))))P,(18.$11.R7.+7=118.(19.$1:.(1>.(5.&40.=))(19.$1:.(1>.(5.&40.=))(19.$1:.(1>.(5.&40.=))(1<.$1:.)))))P,(18.$11.R8.+7=228.(19.$1:.(1>.(5.&40.=))(1<.$1:.)))(76.$11.Lms',$77.(1=.P,(0.&40.)(15.(0.&8.))Lm',P,(0.&40.)(15.(0.&8.))(=.(1.$77.R2.(3<.(3=.(5.&40.+1=5;0.)(5.&40.(29.(4.&40.Vsp0,)+=0.))(5.&40.+10800.)(5.&40.+5=0<8.)R20.R1?.R1>.R1=.R1<.(5.&40.=)(5.&40.=)(5.&40.+3?6?8.)(5.&40.=)R17.R16.R15.R14.R13.R12.(5.&40.+5<?70.)R11.R10.(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R?.R>.R=.R<.)(3>.&5.(0.&40.))(5.&40.+1=5;0.)(5.&20.=)(3?.(0.&40.))R1.(40.$11.)))(=.(78.(19.(2>.$2.$2.)(2?.$2.$2.(29.(4.&40.Vsp0,)+100.)(29.(4.&40.Vsp0,)+=0.))(19.(2>.$2.$2.)(2?.$2.$2.+5<?70.+5<?71.)(19.(2>.$2.$2.)(2?.$2.$2.+7=110.+7=114.)(19.(2>.$2.$2.)(2?.$2.$2.+7=118.+7=120.)(19.(2>.$2.$2.)(2?.$2.$2.+7=128.+7=130.)(19.(2>.$2.$2.)(2?.$2.$2.+7=228.+7=230.)(1<.(2>.$2.$2.))))))))R;.R1.)(=.(4=.$11.R;.R1.)(=.(2:.$11.R1.)(=.(18.$11.R1.+5<?70.(19.$1:.(1;.(5.&8.+1.))(1<.$1:.)))(=.(18.$11.R1.+7=10<.(19.$1:.(4>.(5.&40.=))(19.$1:.(4>.(5.&40.+1.))(1<.$1:.))))(=.(18.$11.R1.+7=118.(19.$1:.(1>.(5.&40.+7=120.))(19.$1:.(1>.(5.&40.=))(19.$1:.(1>.(5.&40.+3?6?8.))(1<.$1:.)))))(18.$11.R1.+7=228.(19.$1:.(1>.(5.&40.+1=674.))(1<.$1:.)))))))))))(3<.(3=.(5.&40.+1=3<0.)(5.&40.(29.(4.&40.Vsp0,)+=0.))(5.&40.+10800.)(5.&40.+5=0<8.)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.(5.&40.+5<?70.)R?.R>.(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R=.R<.R;.R:.)(3>.&5.(0.&40.))(5.&40.+1=59<.)(5.&20.=)(3?.(0.&40.))R9.(40.$11.)))")
(* [comment removed for export] *).
  Proof.
    intros t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 t3 t4 t5 t6 m ST MI NL FL AT1 AT2 AT3 AT4.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (munch_refl [(bv_unsigned sp0 - 256, bv_unsigned sp0 - 208); (0x5cf70, 0x5cf71); (0x7d110, 0x7d114); (0x7d118, 0x7d120);
                            (0x7d128, 0x7d130); (0x7d228, 0x7d230)] m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    step.                                              (* [comment removed for export] *)
    step; lit_store.                                   (* [comment removed for export] *)
    rewrite (u_small 1) in FL by lia.
    step. step.                                        (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    carve_frame 48%nat ST.
    replace (bv_unsigned sp0 + -208 + -48) with (bv_unsigned sp0 + -256) in * by lia.
    step; lit_store. step; lit_store. step; lit_store. step; lit_store. step; lit_store.   (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step. step.                                        (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step. step.                                        (* [comment removed for export] *)
    step. zlit. ifc true.                              (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step. zlit. ifc false.                             (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step. ifc false.                                   (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step; lit_store.                                   (* [comment removed for export] *)
    step. zlit.                                        (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step. ifc true.                                    (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step. step.                                        (* [comment removed for export] *)
    step. step. step.                                  (* [comment removed for export] *)
    step; lit_store.                                   (* [comment removed for export] *)
    step; lit_store.                                   (* [comment removed for export] *)
    step; lit_store.                                   (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step. zlit.                                        (* [comment removed for export] *)
    step. ifc false.                                   (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step. step. step. step. step.                      (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    replace (bv_unsigned sp0 + -208) with (bv_unsigned sp0 - 208) in * by lia.
    apply evt_done.
    lazymatch goal with
    | MUH : munch _ _ ?mm, WMH : wmono _ _ _, MIH : mem_inv _ _,
      F1 : rw_cells _ _ 0x5cf70 _, A2 : rw_cells _ _ 0x7d10c _, A3 : rw_cells _ _ 0x7d118 _, A4 : rw_cells _ _ 0x7d228 _ |- _ =>
        exists mm; split; [reflexivity|]; split; [exact MUH|]; split; [exact WMH|]; split; [exact MIH|];
        split; [exact F1|]; split; [exact A2|]; split; [exact A3| exact A4]
    end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L41415985948.35000005S3sp0". (* [comment removed for export] *)
  #[using="sp0"] Lemma land3_mod4 : forall b : Z, 0 <= b -> Z.land b 3 = b mod 4.
  Proof. intros b Hb. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Section TP2.
    Variables (buf cap cl plen : Z) (junk : list byte) (s6m : word).
    Hypothesis BR : block_range (U_layout sp0) buf cap.
    Hypothesis LCAP : Z.of_nat (length fdata) <= cap.
    Hypothesis CAPMAX : cap <= 67108864.
    Hypothesis Hcl : 0 <= cl.
    Hypothesis Hplen : 0 <= plen.
    Hypothesis HL : cl + 6 + plen = Z.of_nat (length fdata).
    Let b1 : byte := nth 1 fdata (Z_to_bv 8 0).
    Let PAY : Z := buf + 2 + cl + 4.
    Let TRFm : list cell := TRF junk s6m b1 (Z_to_bv 64 plen) (Z_to_bv 64 PAY) (Z_to_bv 64 cl) (Z_to_bv 64 (buf + 2)) buf.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L15425253222.92L15425253222.95L15425376038.91L27193321446.92L27193321446.95L27193706406.91L37265372640.92L37265372640.95L40829904044.93L41481127826.90L44533710052.90L4455481414.90 L5054431440.90 L5060493202.93 L52755101919.93L53517175698.90L53519037842.92L53519037842.95L55804373005.94L57426247314.92L57426247314.95L66917522954.9300000T01@01^02B02f03J03n04Z05006506S07D07b08@08^09409J09`0:G0;K0<O0<mS3sp05fdata3buf2cl4plen5Hplen3PAY2P0S3sp05fdata3buf2cl4plen3Hcl5Hplen3PAY3CL02P0S3sp05fdata3buf2cl4plen3PAY2HpS3sp05fdata3buf2cl4plen5Hplen3PAY2P0S3sp05fdata3buf2cl4plen5Hplen3PAY2P0S3sp05fdata3buf2cl4plen5Hplen3PAY2HpS3sp05fdata3buf2cl4plen5Hplen3PAY2P0S3sp05fdata3buf2cl4plen3Hcl5Hplen3PAY3CL02P0S3sp05fdata3buf2cl3PAYS3sp05fdata3buf2cl3Hcl3PAY3CL04SPlo3cap4plen4LCAP6CAPMAX5Hplen2HL3BR1S3sp05fdata3buf2cl3Hcl3PAY3CL0S3sp04SPlo5fdata3buf2cl4plen3Hcl5Hplen2HL3PAY3BR1S3sp05fdata3buf2cl3Hcl3PAY3CL0S3sp05fdata3buf2cl3Hcl3PAY3CL0S3sp05fdata3buf2cl3PAY2b24RB2rS3sp05fdata3buf2cl3PAYS3sp05fdata3buf2cl3PAYS3sp05fdata3buf2cl3PAYS3sp04SPlo5fdata3buf2cl3PAY3BR12b24RB2rS3sp05fdata3buf2cl4plen5Hplen3PAY2P04SPlo3cap4LCAP6CAPMAX2HL3BR13CL0S3sp05fdata3buf2cl4plen5Hplen3PAY2P04SPlo3cap4LCAP6CAPMAX3Hcl2HL3BR1S3sp05fdata3buf2cl3PAY2b24RB2r". (* [comment removed for export] *)
    #[using="Hvsp Htid SPlo SPhi SPal HSTAT NS MRZ SI SIFP FUZZ BR LCAP CAPMAX Hcl Hplen HL"] Lemma target_phase2 : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pk,$1?.Pra,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(15.(0.&8.))Pmo,$16.Ph,(10.$11.(12.Vsp0,)VHI,)P,(4;.R3.)P,(55.=R4.)P,(49.R5.)P,(18.$11.R6.(29.(4.&40.Vsp0,)+=0.)VTRFm,)P,(17.$11.(12.Vsp0,)VHI,R5.(19.(2>.$2.$2.)(2?.$2.$2.Vbuf,Vcap,)(1<.(2>.$2.$2.)))R7.R6.)P,A3.VDRV,(74.R1;.)R6.R7.P,(1.$2.(30.$11.(12.Vsp0,)VHI,R7.)(4.&40.Vsp0,))P,(1.$31.(32.R9.)Vfs0,)P,(1.(15.$34.)(35.(36.R:.)(5.&40.+1.))(37.$34.(38.(5.&40.+1.))))P,(64.$11.R<.Vbuf,Vfdata,)(3:.$11.(3;.(3<.(3=.R1?.(5.&40.(29.(4.&40.Vsp0,)+=0.))(5.&40.+10800.)(5.&40.+5=0<8.)R1>.R1=.R1<.(5.&40.Vplen,)(5.&40.VPAY,)R1;.R1:.R19.R18.R17.R16.R15.R14.(5.&40.Vcl,)(5.&40.(:.Vbuf,+2.))(5.&40.+5<?70.)R13.R12.(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R11.R10.R?.R>.)(3>.&5.(0.&40.))(5.&40.+1=564.)(5.&20.=)(3?.(0.&40.))R=.(40.$11.))R<.)(79.Vcl,Vplen,))")
(* [comment removed for export] *).
    Proof.
      intros k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 t3 t4 t5 t6 m mo h BM AX OPR TR HH HD HT FS FD1 BY.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      dpose BR as (BR1 & BR2 & BR3 & BR4 & BR5). rewrite (U_alloc_ceiling_eq sp0 Hvsp) in BR4.
      pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ HH) as MK.
      (* [comment removed for export] *)
      assert (JOIN : forall (q0 q1 sv : word) (pc : Z), (pc = 0x1d578 /\ 0 < plen \/ pc = 0x1d5c4 /\ plen = 0) ->
        sv = Z_to_bv 64 (Z.of_nat (CALLS cl)) ->
        aevtM usegs mo (fun c => realizes usegs c (TAIL cl plen))
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 208)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8) t0 t1 t2
                   (Z_to_bv 64 plen) (Z_to_bv 64 PAY) q0 q1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 cl) (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 0x5cf70) sv s6
                   (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
              bvmap_empty (Z_to_bv 64 pc) (Z_to_bv 32 0) None m (seg_rom usegs))).
      { intros q0 q1 sv pc [[-> Hp]|[-> Hp]] ->; apply aevtM_done; unfold TAIL.
        - replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
          eapply (tp_copy buf cap cl plen junk s6m); first [eassumption | lia].
        - replace (plen =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
          eapply (tp_empty buf cap cl plen junk s6m); first [eassumption | lia]. }
      apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). step.                              (* [comment removed for export] *)
      destruct (Z.eq_dec cl 0) as [CL0|CL0].
      - (* [comment removed for export] *)
        ifc true. step. step.
        assert (SV : (Z_to_bv 64 1 : word) = Z_to_bv 64 (Z.of_nat (CALLS cl))).
        { unfold CALLS. replace (cl =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
        destruct (Z.eq_dec plen 0) as [P0|P0].
        + ifc false. apply JOIN; [right; split; [reflexivity | exact P0] | exact SV].
        + ifc true. apply JOIN; [left; split; [reflexivity | lia] | exact SV].
      - (* [comment removed for export] *)
        ifc false.
        pose proof (nth_byte_read m buf fdata 2 BY ltac:(lia)) as RB2. change (Z.of_nat 2) with 2 in RB2.
        step.                                            (* [comment removed for export] *)
        step. step.                                      (* [comment removed for export] *)
        step.                                            (* [comment removed for export] *)
        set (b2 := nth 2 fdata (Z_to_bv 8 0)) in *.
        pose proof (bv_unsigned_in_range 8 b2) as RB2r. unfold bv_modulus in RB2r. cbn in RB2r.
        assert (SV : (Z_to_bv 64 (Z.land (bv_unsigned (zxb b2)) 3 + 1) : word) = Z_to_bv 64 (Z.of_nat (CALLS cl))).
        { unfold CALLS. replace (cl =? 0) with false by (symmetry; apply Z.eqb_neq; lia). fold b2.
          unfold zxb. rewrite u_small by lia. rewrite land3_mod4 by lia. f_equal.
          pose proof (Z.mod_pos_bound (bv_unsigned b2) 4 ltac:(lia)). lia. }
        destruct (Z.eq_dec plen 0) as [P0|P0].
        + ifc true. apply JOIN; [right; split; [reflexivity | exact P0] | exact SV].
        + ifc false. apply JOIN; [left; split; [reflexivity | lia] | exact SV].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End TP2.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00e0@L1147549074.100 L13332014903.99 L16369012816.100L16369012816.99 L16369023879.100L16479583265.77 L16773145846.101L18878202803.83 L1893543047.99  L18979375056.100L18979375056.99 L18979384327.100L2141872711.99  L25017371783.99 L27004492662.101L32168731758.103L34301895276.101L34460694057.103L34460694057.90 L35192704412.85 L40039414451.86 L40039710258.99 L40892843410.100L4679144850.100 L47423652190.100L51907527250.100L52101693566.100L52101693566.87 L52101693566.94 L52101693566.99 L52101703855.85 L52101704234.89 L52101704617.100L52101704617.99 L53517205904.82 L53517207446.85 L56763568491.102L56763568491.89 L56765667309.100L56765667309.87 L56765667309.94 L56765667309.99 L56765676602.100L56765676602.99 L56765676985.89 L56765677372.85 L58176590682.80 L59274066610.95 L60780277920.86 L61978127234.100L62064896647.99 L6406878858.83  L94994261.101   00000?00S01401H01\01k02T02c03703X03l04@04T04h05Q05d06M06`07307X07g08608E08T08h09709K09l0:M0:n0;B0;V0;j0<>0<M0<\0=00=D0=i0>=0>Q0>e0?90?M0?a0@50@D0@S0@b0A10AE0AT0BES3sp05fdata3bufS3sp05fdata3buf1a2H3S3sp04SPlo5fdata3buf3Hlo3BR11a2HaS3sp05fdata3buf1a2HaS3sp05fdata3buf1a2H3S3sp05fdata3bufS3sp04SPlo5fdata3buf3cap4LCAP3BR52B11i2HiS3sp05fdata3bufS3sp05fdata3buf1a2H4S3sp04SPlo5fdata3buf3Hlo3BR11a2HaS3sp05fdata3buf1a2HaS3sp05fdata3buf1a2H4S3sp05fdata3buf1a2H4S3sp05fdata3buf1a2H4S3sp04SPlo5fdata3buf3cap4LCAP3BR52B11i2HiS3sp05fdata3buf1a1CS3sp04SPlo5fdata3buf3cap4LCAP3BR42B11i2HiS3sp05fdata3buf1a1CS3sp05fdata3buf1a1CS3sp04SPlo5fdata3buf3cap4LCAP3BR13BR4S3sp05fdata3bufS3sp05fdata3bufS3sp05fdata3bufS3sp05fdata3bufS3sp04SPlo5fdata3bufS3sp05fdata3bufS3sp05fdata3buf1a2HaS3sp04SPlo5fdata3buf3Hlo3BR11a2HaS3sp04SPlo5fdata3buf3Hlo3BR11a2HaS3sp04SPlo5fdata3buf3Hlo3BR11a2HaS3sp05fdata3buf1a2H2S3sp05fdata3buf1a2H2S3sp05fdata3buf1a2H2S3sp05fdata3buf1a2H2S3sp05fdata3bufS3sp05fdata3bufS3sp05fdata3buf1a2HaS3sp05fdata3buf1a2HaS3sp04SPlo5fdata3buf3Hlo3Hhi3BR11a2HaS3sp05fdata3buf1a2HaS3sp05fdata3buf1a2HaS3sp05fdata3buf1a2HaS3sp05fdata3buf1a2H1S3sp05fdata3buf1a2H1S3sp05fdata3buf1a2H1S3sp05fdata3buf1a2H1S3sp05fdata3bufS3sp05fdata3bufS3sp05fdata3bufS3sp05fdata3bufS3sp05fdata3buf1a2H4S3sp05fdata3bufS3sp04SPlo5fdata3buf3cap4LCAP3Hhi3BR13BR42B11i2Hi". (* [comment removed for export] *)
  #[using="Hvsp Htid SPlo SPhi SPal HSTAT NS MRZ SI SIFP FUZZ"] Theorem target_phase : ltac2:(CDefT.buildp (gd_tbl_P_main_body ()) "Pbuf,$2.Pcap,$2.Pcl,$2.Pplen,$2.Pk,$1?.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps6,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(15.(0.&8.))Pmo,$16.Ph,(10.$11.(12.Vsp0,)VHI,)P,(62.Vsp0,Vtid,Vmem0,R3.)P,(17.$11.(12.Vsp0,)VHI,R2.(19.(2>.$2.$2.)(2?.$2.$2.R15.R14.)(1<.(2>.$2.$2.)))R4.R3.)P,A3.VDRV,(74.R12.)R3.R4.P,(1.$2.(30.$11.(12.Vsp0,)VHI,R4.)(4.&40.Vsp0,))P,(1.$31.(32.R6.)Vfs0,)P,(1.(15.$34.)(35.(36.R7.)(5.&40.+1.))(37.$34.(38.(5.&40.+1.))))P,(64.$11.R9.R1:.Vfdata,)P,(7:.(12.Vsp0,)R1;.R1:.)P,(>.(20.(56.(0.&8.)Vfdata,))R1;.)P,(>.R1<.+4000000.)P,(>.=R1<.)P,(>.=R1<.)P,(1.$2.(:.(:.R1>.+6.)R1=.)(20.(56.(0.&8.)Vfdata,)))(3:.$11.(3;.(3<.(3=.(5.&40.+1=3<0.)(5.&40.(29.(4.&40.Vsp0,)+80.))(5.&40.+10800.)(5.&40.+5=0<8.)R1<.R1;.R1:.(5.&40.(:.R21.+2.))(5.&40.R21.)(5.&40.(:.R21.+2.))(5.&40.R1?.)(5.&40.(:.(:.(:.R21.+2.)R1?.)+4.))(5.&40.R1>.)R19.R18.R17.R16.(5.&40.R1?.)(5.&40.(:.(:.(:.R21.+2.)R1?.)+4.))(5.&40.R1>.)(8.(67.(0.&8.)#1.Vfdata,(5.&8.=)))R15.(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)(5.&40.=)R14.R13.R12.R11.)(3>.&5.(0.&40.))(5.&40.+1=51<.)(5.&20.=)(3?.(0.&40.))R10.(40.$11.))R?.)(79.R1?.R1>.))")
(* [comment removed for export] *).
  Proof.
    intros buf cap cl plen k t0 t1 t2 a4 a5 a6 a7 s6 t3 t4 t5 t6 m mo h D HH HD HT FS FD1 BY BR LCAP CAPMAX Hcl Hplen HL.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    set (b1 := nth 1 fdata (Z_to_bv 8 0)) in *.
    dpose BR as (BR1 & BR2 & BR3 & BR4 & BR5). rewrite (U_alloc_ceiling_eq sp0 Hvsp) in BR4.
    cbn [hl_img_lo hl_img_hi U_layout] in BR5.
    destruct (bmem_of_dinv m D) as [BM OPR]. pose proof (atx0_of_dinv m D) as AX0. clear D.
    pose proof (heap_mok usegs (U_layout sp0) HI _ _ _ _ HH) as MK.
    (* [comment removed for export] *)
    apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). eapply aevtM_cut_evt; [exact MK | apply tr_prologue; apply bmem_stk; [exact BM | lia] |].
    (intros ms' dd_H; ddestruct dd_H as (m1 & junk & -> & MU & WM & TR)).
    assert (AG1 : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp0 - 208 <= a < bv_unsigned sp0 - 128) -> m1 (wa a) = m (wa a)).
    { intros a H1 H2. apply MU. cbn [outside]. unfold wa. rewrite u_small by lia. split; [lia | exact I]. }
    assert (BM1 : bmem m1).
    { eapply (bmem_agree_gen m m1 (bv_unsigned sp0 - 128) 0 0 BM); [intros a H1 H2 H3 H4 H5; apply AG1; lia | exact WM | lia | lia]. }
    assert (OPR1 : out_pristine m1) by (destruct OPR as [O1 O2]; split; intros a Ha; rewrite AG1 by lia; [apply O1| apply O2]; exact Ha).
    assert (BY1 : bytes_at usegs m1 buf fdata).
    { eapply bytes_at_transport; [exact BY | exact MU | cbn; lia]. }
    assert (HH1 : HEAP usegs (U_layout sp0) HI h [(buf, cap)] m1 mo).
    { eapply (heap_frame usegs (U_layout sp0) HI) with (SP := bv_unsigned sp0 - 8388608);
        [ exact HH | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia | | exact WM ].
      intros a Ha Hnc. apply AG1; [lia|]. intros C. apply Hnc. left. rewrite HT. lia. }
    assert (AX1 : atx0 m1).
    { ddestruct AX0 as (X1 & X2 & X3 & X4 & X5 & X6).
      split; [|split; [|split; [|split; [|split]]]]; (eapply rw_cells_agree; [eassumption | intros a Ha; cbn in Ha; apply AG1; lia | exact WM]). }
    clear BM OPR BY HH MU WM AG1 AX0.
    replace (bv_unsigned sp0 - 128 + -80) with (bv_unsigned sp0 - 208) by lia.
    ddestruct AX1 as (FL & ICB & AT1 & AT2 & AT3 & AT4).
    step. step. step.                                  (* [comment removed for export] *)
    step. step.                                        (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    ifc true.
    (* [comment removed for export] *)
    ddestruct (HSTAT h [(buf, cap)] m1 mo HH1) as (NL & _ & _).
    eapply aevtM_cut_evt; [exact MK | apply (tr_atexit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 ltac:(apply bmem_stk; [exact BM1 | lia]) (bm_minv _ BM1) NL FL AT1 AT2 AT3 AT4) |].
    (intros ms' dd_H; ddestruct dd_H as (m2 & -> & MU & WM & MI2 & FL2 & AT2' & AT3' & AT4')).
    assert (AG2 : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp0 - 256 <= a < bv_unsigned sp0 - 208) ->
                  ~ (0x5cf70 <= a < 0x5cf78) -> ~ (0x7d108 <= a < 0x7d328) -> m2 (wa a) = m1 (wa a)).
    { intros a H1 H2 H3 H4. apply MU. cbn [outside]. unfold wa. rewrite u_small by lia. repeat split; lia. }
    assert (BM2 : bmem m2).
    { eapply (bmem_agree_atx m1 m2 (bv_unsigned sp0 - 208) BM1); [intros a H1 H2 H3 H4; apply AG2; lia | exact WM | exact MI2 | lia]. }
    assert (OPR2 : out_pristine m2) by (destruct OPR1 as [O1 O2]; split; intros a Ha; rewrite AG2 by lia; [apply O1| apply O2]; exact Ha).
    assert (BY2 : bytes_at usegs m2 buf fdata).
    { ddestruct BY1 as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|]. intros i Hi. unfold mrd. rewrite AG2 by lia. apply B3. exact Hi. }
    assert (TR2 : rw_cells usegs m2 (bv_unsigned sp0 - 208) (TRF junk s6 b1 (Z_to_bv 64 plen) (Z_to_bv 64 (buf + 2 + cl + 4)) (Z_to_bv 64 cl) (Z_to_bv 64 (buf + 2)) buf)).
    { eapply rw_cells_agree; [exact TR | intros a Ha; cbn in Ha; apply AG2; lia | exact WM]. }
    assert (HH2 : HEAP usegs (U_layout sp0) HI h [(buf, cap)] m2 mo).
    { eapply (heap_frame usegs (U_layout sp0) HI) with (SP := bv_unsigned sp0 - 8388608);
        [ exact HH1 | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia | | exact WM ].
      intros a Ha Hnc. apply AG2; [lia | | |]; intros C; apply Hnc.
      - left. rewrite HT. lia.
      - right; left. cbn [hl_data_lo hl_data_hi hl_static U_layout]. unfold U_static. lia.
      - right; left. cbn [hl_data_lo hl_data_hi hl_static U_layout]. unfold U_static. lia. }
    assert (AX2 : atx 0 m2).
    { split; [exact FL2|]. split; [| split; [exact AT2' | split; [exact AT3' | exact AT4']]].
      eapply rw_cells_transport; [exact ICB | exact MU | exact WM |]. cbn. repeat split; lia. }
    clear MU WM AG2 FL ICB AT1 AT2 AT3 AT4 FL2 AT2' AT3' AT4' NL TR BM1 OPR1 BY1 HH1.
    (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    ifc true.
    (* [comment removed for export] *)
    pose proof (got_fuzzinit m2 (bm_statics _ BM2)) as GOTI.
    step. step.                                        (* [comment removed for export] *)
    clear GOTI.
    step.                                              (* [comment removed for export] *)
    ifc true. apply aevtM_done.
    eapply (target_phase2 buf cap cl plen junk s6); first [eassumption | lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  Local Ltac2 Set LiaOrc.tbl := fun () => "01A0@L1080386751.81  L11447729958.143L11447729963.126L12500131315.120L13682529659.101L13743529534.115L15032387483.96 L15851360259.102L16671906440.115L16855619843.116L16882893957.111L17860996235.100L17863467798.100L18333377149.105L18908639431.114L20851998927.108L21270650342.115L22169021323.110L23021371095.114L23031543152.110L23031558635.100L23033639148.110L23033970294.100L26160698123.116L27645142961.103L28484349774.115L30484933857.108L32171964359.114L33774851885.105L34190485912.115L34301895276.103L3438875127.100 L34460694057.101L34515218861.102L37027934275.114L37188191798.115L37616188006.99 L37622514262.102L38656133426.100L39473603378.115L39539844901.114L39662949959.100L39665507649.110L39675549414.114L40041533107.97 L4006124574.119 L40461942136.115L41480849815.114L42250547024.114L42432736191.114L42491452171.110L42512514889.110L44116245048.115L44261801751.117L45244042635.102L45244203531.101L46603631616.76 L47612646578.115L48266928741.114L48948562694.115L512889190.119  L51984082967.100L52016692352.110L52018345767.114L52157358816.114L52776274919.113L54178039336.115L5456914291.114 L56237046750.114L56763568491.100L5738359813.99  L5744825397.102 L61981755008.114L62341220886.112L64446297340.110L64448393568.110L6764619768.115 L6967381616.114 L7622844822.115 L8164361855.110 L94994261.103   00000O00P00Q01901Y01Z02402\02]03b04f05@05Z05[06H0700710850950:70:e0;e0<I0=D0=l0=m0>U0??0?@0?A0@00@Y0A70AW0B>0B?0B^0C=0C]0DD0Dk0ET0FR0GN0Gh0I00IW0JB0Jm0KX0LW0MD0Mk0O>0O[0P80PY0PZ0QZ0RA0SQ0T00Tj0Ud0VO0WS0WT0XI0YB0Ya0Z@0Z_0[J0\N0]90]d0^K0_60_70_c0`ZS3sp05fdata3buf3cap1k2CR1L1a2HaFFS3sp04SPlo5fdata3cap1k2CR1L2b04RB0r1r2H0S3sp05fdata3buf3cap1k2CR1L2B12B2FS3sp05fdata3buf3cap1k2CR1LS3sp04SPlo5fdata3buf3cap1k2CR1L3BR14LONGFS3sp04SPlo5fdata3buf3cap1k2CR1L2CB3BR13BR22b02b14RB1r2cl3CLr2E23CFG1ES3sp04SPlo5fdata3buf3cap1k2CR1L3BR14LONG2b02b14RB1r2cl3CLr3CFG5OKLENS3sp05fdata3buf3cap1k2CR1LS3sp05fdata3buf3cap1k2CR1LFS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CFG5OKLENS3sp05fdata3buf3cap1k2CR1L2b02b14RB0r2clFS3sp04SPlo5fdata3buf3cap1k2CR1L3BR14LONG2b02b14RB1r2cl3CLr3CFG5OKLENS3sp04SPlo5fdata3buf3cap1k2CR1L3LEN3HLc2CB3BR12b02b14RB1r2cl3CFGS3sp04SPlo5fdata3buf3cap1k2CR1L3LEN3BR12b02b14RB1r2cl3CLr3CFG4OVERS3sp04SPlo5fdata3buf3cap1k2CR1L3LEN3HLc2CB3BR1S3sp04SPlo5fdata3buf3cap1k2CR1L3LEN3HLc2CB3BR12b02b14RB1r2cl3CFGS3sp05fdata3buf3cap1k2CR1L3LEN5SHORTS3sp04SPlo5fdata3buf3cap1k2CR1L3BR12b02b14RB1r2cl3CFG2EC2PZS3sp04SPlo5fdata3buf3cap1k2CR1L3BR14LONGFS3sp05fdata3buf3cap1k2CR1L2b02b14RB1r2clS3sp05fdata3buf3cap1k2CR1L2CB2b02b12cl3CFGFFS3sp04SPlo5fdata3buf3cap1k2CR1L2B13HLc3BR41i2HiS3sp04SPlo5fdata3buf3cap1k2CR1L3BR15SHORTS3sp05fdata3buf3cap1k2CR1L1a1CS3sp05fdata3buf3cap1k2CR1L2W12W2S3sp05fdata3buf3cap1k2CR1L2b02b12cl3CFGFS3sp05fdata3buf3cap1k2CR1L1x2H2S3sp05fdata3buf3cap1k2CR1L1x2H2S3sp05fdata3buf3cap1k2CR1L5SHORTS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CFGS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CFGS3sp04SPlo5fdata3buf3cap1k2CR1L3BR15SHORTS3sp04SPlo5fdata3buf3cap1k2CR1L3BR12b02b14RB1r2cl3CLr3CFG4OVERS3sp04SPlo5fdata3buf3cap1k2CR1L3HLc2CB3BR12b02b14RB1r2cl3CFGS3sp05fdata3buf3cap1k2CR1LS3sp04SPlo5fdata3buf3cap1k2CR1L3BR12b02b14RB0r4RB1r2cl3CLr3CFG2EC1n2E31lS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CFGS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CLr3CFGS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CLr3CFGS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CLr3CFGS3sp04SPlo5fdata3buf3cap1k2CR1L3BR14LONG2b02b14RB1r2cl3CFG4OVERS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CFG5OKLENS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CFGS3sp03fs04SPlo5fdata3buf3cap1k2CR1L2CB3BR13BR22b02b14RB1r2cl3CLr3CFG5OKLEN2EC2PZ2E3S3sp05fdata3buf3cap1k2CR1L2W1S3sp05fdata3buf3cap1k2CR1L2B1S3sp04SPlo5fdata3buf3cap1k2CR3BR1FS3sp04SPlo5fdata3buf3cap1k2CR1L3BR14LONG2b02b14RB1r2cl3CFG5OKLENS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CFGS3sp04SPlo5fdata3buf3cap1k2CR1L2CB3BR13BR22b02b14RB1r2cl3CFG5OKLEN2EC2PZ1n2E32n0S3sp05fdata3buf3cap1k2CR1L4LONGS3sp04SPlo5fdata3buf3cap1k2CR1L3BR14LONG2b02b14RB1r2cl3CFGS3sp04SPlo5fdata3buf3cap1k2CR1L3BR14LONG2b02b14RB1r2cl3CFGS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CLr3CFGS3sp04SPlo5fdata3buf3cap1k2CR1L3BR14LONG2b02b14RB1r2cl3CLr3CFG5OKLENFS3sp04SPlo5fdata3buf3cap1k2CR1L3BR12b02b14RB1r2cl3CFGS3sp04SPlo5fdata3buf3cap1k2CR1L3HLc3BR12b02b14RB1r2cl3CFGS3sp05fdata3buf3cap1k2CR1L1a2HaS3sp05fdata3buf3cap1k2CR1L1x2H1S3sp05fdata3buf3cap1k2CR1L1x2H1S3sp05fdata3buf3cap1k2CR1L2b02b12cl3CLr3CFGS3sp04SPlo5fdata3buf3cap1k2CR1L3BR14LONG2b02b14RB1r2cl3CLr3CFG5OKLENS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CLr3CFGS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CLr3CFGS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CFGS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CLr3CFGFS3sp05fdata3buf3cap1k2CR1L2b02b12cl3CFG4OVERS3sp04SPlo5fdata3buf3cap1k2CR1L2B13HLc3Hhi3BR13BR41i2Hi". (* [comment removed for export] *)
  #[using="Hvsp Htid SPlo SPhi SPal HSTAT NS MRZ DRVMO SI SIFP FUZZ"] Theorem after_loop : after_loop_stmt sp0 a0s path envv tid mem0 fs0 HI DRV fdata.
  Proof.
    intros buf cap k ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m mo h LI HLc.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct LI as [D HH HD CR HT MK FS FDSq BY WR LEN COK BR].
    pose proof (cap_ok_bounds sp0 cap COK) as CB.
    dpose BR as (BR1 & BR2 & BR3 & BR4 & BR5). rewrite (U_alloc_ceiling_eq sp0 Hvsp) in BR4.
    cbn [hl_img_lo hl_img_hi U_layout] in BR5.
    rewrite firstn_all2 in BY by lia.
    set (L := Z.of_nat (length fdata)) in *.
    pose proof MK as MK2; destruct MK2 as [Hh Hl].
    unfold LREGS. apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs).
    step. step.                                        (* [comment removed for export] *)
    apply aevtM_done.
    change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (@mkst PropExec.fx0 Rx pc Mx rom).
    assert (WIN : forall a : word, bv_unsigned sp0 - 8388608 <= bv_unsigned a < bv_unsigned sp0 -> wview usegs m a <> None).
    { intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply (di_win _ _ _ m D). lia. }
    refine (close_call sp0 mo Hvsp Hh Hl _ m WIN _ _ _ _ _ (FdFile path (Z_to_bv 64 L)) _ _ _);
      [ norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity | norm_getr; reflexivity
      | rewrite FDSq; apply FDS_lookup3 | ].
    intros a1' a2' a3' a4' a5' a6' a7' m1 AG1 GR1. norm_getr. change Ubsan.M.loaded_segments with usegs.
    rewrite FDSq. set (mo1 := with_fds _ mo).
    assert (MK1 : MOK mo1) by (apply MOK_with_fds; exact MK).
    assert (FS1 : m_fs mo1 = fs0) by exact FS.
    assert (FD1 : fd_lookup (m_fds mo1) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) by reflexivity.
    assert (FD2 : fd_lookup (m_fds mo1) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by reflexivity.
    assert (AG1' : forall x : Z, 0 <= x < 2 ^ 64 -> ~ (bv_unsigned sp0 - 144 <= x < bv_unsigned sp0 - 128) -> m1 (wa x) = m (wa x)).
    { intros x H1 H2. pose proof (AG1 (wa x)) as E. unfold wa in E. rewrite u_small in E by lia. apply E. lia. }
    pose proof (DAG m m1 0 0 D ltac:(intros x H1 H2 H3 H4 H5; apply AG1'; lia) GR1 ltac:(right; right; lia)) as D1.
    assert (HH1 : HEAP usegs (U_layout sp0) HI h [(buf, cap)] m1 mo1).
    { apply (heap_mo usegs (U_layout sp0) HI h [(buf, cap)] m1 mo mo1); [| reflexivity | reflexivity | reflexivity].
      eapply (heap_frame usegs (U_layout sp0) HI) with (SP := bv_unsigned sp0 - 8388608);
        [ exact HH | rewrite (U_alloc_ceiling_eq sp0 Hvsp); lia | | apply (mem_grows_wmono _ _ GR1) ].
      intros a Ha Hnc. apply AG1'; [lia |]. intros C. apply Hnc. left. rewrite HT. lia. }
    assert (HD1 : DRV (S k) h mo1) by (eapply DRVMO; [exact HD | reflexivity | reflexivity | reflexivity | reflexivity]).
    assert (BY1 : bytes_at usegs m1 buf fdata).
    { ddestruct BY as (B1 & B2 & B3). split; [lia|]. split; [lia|]. intros i Hi. unfold mrd. rewrite AG1' by lia. apply B3. exact Hi. }
    assert (WR1 : wr_at usegs m1 buf cap).
    { ddestruct WR as (W1 & W2 & W3). split; [lia|]. split; [lia|]. intros i Hi. apply (mem_grows_wmono _ _ GR1). apply W3. exact Hi. }
    clear AG1 WIN. clearbody mo1.
    (* [comment removed for export] *)
    apply rz_steps; change (seg_rom RSEGS) with (seg_rom usegs). step. step.
    destruct (Z.lt_ge_cases L 6) as [SHORT|LONG].
    { (* [comment removed for export] *)
      ifc true. apply aevtM_done.
      replace (BODY fs0 fdata) with (t_die msg_short fs0).
      2:{ unfold BODY, t_body. replace (MAX_INPUT <=? Z.of_nat (length fdata)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
          replace (length fdata <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
      eapply (err_tail 0x1d404 0x10972 msg_short buf cap k); [left; repeat split; reflexivity | exact D1 | exact HH1 | exact HT | exact FS1 | exact FD2]. }
    ifc false.
    (* [comment removed for export] *)
    set (b0 := nth 0 fdata (Z_to_bv 8 0)). set (b1 := nth 1 fdata (Z_to_bv 8 0)).
    pose proof (nth_byte_read m1 buf fdata 0 BY1 ltac:(lia)) as RB0. rewrite Z.add_0_r in RB0. fold b0 in RB0.
    pose proof (nth_byte_read m1 buf fdata 1 BY1 ltac:(lia)) as RB1. change (Z.of_nat 1) with 1 in RB1. fold b1 in RB1.
    step.                                  (* [comment removed for export] *)
    step.                                  (* [comment removed for export] *)
    step. step. step.                      (* [comment removed for export] *)
    step.                                  (* [comment removed for export] *)
    step.                                  (* [comment removed for export] *)
    rewrite hdr_cfglen.
    pose proof (bv_unsigned_in_range 8 b0) as RB0r. pose proof (bv_unsigned_in_range 8 b1) as RB1r. unfold bv_modulus in RB0r, RB1r. cbn in RB0r, RB1r.
    set (cl := bv_unsigned b0 + 256 * (bv_unsigned b1 mod 128)) in *.
    assert (CLr : 0 <= cl < 32768) by (subst cl; Z.div_mod_to_equations; lia).
    assert (CFG : Z.to_nat ((bv_unsigned (nth 0 fdata (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 fdata (Z_to_bv 8 0))) mod 32768) = Z.to_nat cl).
    { fold b0 b1. rewrite cfg_mod by lia. reflexivity. }
    destruct (Z.lt_ge_cases L (cl + 6)) as [OVER|OKLEN].
    { (* [comment removed for export] *)
      ifc true. apply aevtM_done.
      replace (BODY fs0 fdata) with (t_die msg_overrun fs0).
      2:{ unfold BODY, t_body. replace (MAX_INPUT <=? Z.of_nat (length fdata)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
          replace (length fdata <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia). cbv zeta. rewrite CFG.
          replace (length fdata <? 6 + Z.to_nat cl)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
      eapply (err_tail 0x1d420 0x104aa msg_overrun buf cap k); [right; repeat split; reflexivity | exact D1 | exact HH1 | exact HT | exact FS1 | exact FD2]. }
    ifc false.
    (* [comment removed for export] *)
    pose proof (nth_byte_read m1 buf fdata (Z.to_nat (cl + 2)) BY1 ltac:(lia)) as RP0.
    pose proof (nth_byte_read m1 buf fdata (Z.to_nat (cl + 3)) BY1 ltac:(lia)) as RP1.
    pose proof (nth_byte_read m1 buf fdata (Z.to_nat (cl + 4)) BY1 ltac:(lia)) as RP2.
    pose proof (nth_byte_read m1 buf fdata (Z.to_nat (cl + 5)) BY1 ltac:(lia)) as RP3.
    rewrite Z2Nat.id in RP0, RP1, RP2, RP3 by lia.
    step. step.                            (* [comment removed for export] *)
    step. step. step. step.                (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step.
    step.                                  (* [comment removed for export] *)
    step.                                  (* [comment removed for export] *)
    step. step. step. step.                (* [comment removed for export] *)
    step.                                  (* [comment removed for export] *)
    apply aevtM_done.
    rewrite ?(u_small L), ?(u_small cl) by lia.
    try replace (L + - cl + -6) with (L - cl - 6) by lia. try replace (L - cl + -6) with (L - cl - 6) by lia.
    eapply rz_conseq.
    - eapply (target_phase buf cap cl (L - cl - 6) k); first [exact D1 | exact HH1 | exact HD1 | exact HT | exact FS1 | exact FD1 | exact BY1 | exact BR | lia].
    - (* [comment removed for export] *)
      unfold TAIL, SUCC, CALLS, BODY, t_body.
      replace (MAX_INPUT <=? Z.of_nat (length fdata)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
      replace (length fdata <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia). cbv zeta. rewrite CFG.
      replace (length fdata <? 6 + Z.to_nat cl)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
      fold b0 b1.
      assert (EC : (if cl =? 0 then 1%nat else S (Z.to_nat (bv_unsigned (nth 2 fdata (Z_to_bv 8 0)) mod 4)))
                   = match Z.to_nat cl with 0%nat => 1%nat | S _ => S (Z.to_nat (bv_unsigned (nth 2 fdata (Z_to_bv 8 0)) mod 4)) end).
      { destruct (Z.eqb_spec cl 0) as [E|E]; [rewrite E; reflexivity|]. destruct (Z.to_nat cl) eqn:E2; [lia | reflexivity]. }
      rewrite EC.
      destruct (Z.eqb_spec (L - cl - 6) 0) as [PZ|PZ].
      + replace (length fdata - 6 - Z.to_nat cl)%nat with 0%nat by lia. apply t_eq_refl.
      + destruct (length fdata - 6 - Z.to_nat cl)%nat eqn:E3; [lia|].
        apply t_alt2_congr_l.
        unfold status. replace (128 <=? bv_unsigned b1) with (32768 <=? bv_unsigned b0 + 256 * bv_unsigned b1).
        2:{ destruct (Z.leb_spec0 128 (bv_unsigned b1)); [apply (proj2 (Z.leb_le _ _)); lia | apply (proj2 (Z.leb_gt _ _)); lia]. }
        apply (t_emit_W_nil 1). apply t_exit_has_nil.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Body.

