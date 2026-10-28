(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import StepTac CatExec AxSymExec3 AxSymExec3Sound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs AsanPlanImages. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanInit AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_exit_base A_exit_lib A_exit_front1 A_tailkit_defs A_main_inv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AHeapR AH0Facts AH0Base AH0Layout AH0Mem0 AH0Mem1 AH0XR.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_entry_mem () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.cell_ok"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanCertDefs.ASEGS"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.CWr"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.v_addi"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.winst"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WMd"; "LinuxProcessSemantics.Riscv.Instr.M_MUL"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WLit"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WVar"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_s1"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_s2"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "EntryMem.SSH0"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Base.STKPG"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Base.zev"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "EntryMem.SSH8"; "EntryMem.SSH1"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.CZero"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_LO"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_HI"; "RocqVerifyHarness.AgentSubmission.B.A_exit_front1.atexit_cells"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "EntryMem.JF"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.tail_memA"; "EntryMem.CAN"; "EntryMem.TID"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.total_arg_bytes_nat"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.nth"; "EntryMem.APTR"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.ABoot.CatExec.cat_struct_size"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.argH0"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanPlanImages.APH"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.E0"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.app"; "EntryMem.ESTKHI"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ro_addr_offtextA : forall a : word, (bv_unsigned a < 0x10000 \/ 0x0f1000 <= bv_unsigned a) -> ro_addr asegs a = false.
Proof.
  intros a Ha. pose proof (ABoot.PropExec.u64_range a) as Ra. unfold ro_addr. set (z := bv_unsigned a) in *.
  unfold asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
  repeat match goal with
  | |- context [Z.of_N (seg_base ?s)] => let v := eval vm_compute in (Z.of_N (seg_base s)) in replace (Z.of_N (seg_base s)) with v by (vm_compute; reflexivity)
  | |- context [Z.of_N (seg_size ?s)] => let v := eval vm_compute in (Z.of_N (seg_size s)) in replace (Z.of_N (seg_size s)) with v by (vm_compute; reflexivity)
  | |- context [seg_writable ?s] => let v := eval vm_compute in (seg_writable s) in replace (seg_writable s) with v by (vm_compute; reflexivity)
  end.
  repeat match goal with
  | |- context [((?lo <=? z) && (?y <=? ?hi))%bool] =>
      destruct (Z.leb_spec0 lo z); destruct (Z.leb_spec0 y hi); cbn [andb negb]; try (exfalso; lia)
  end;
  repeat match goal with
  | |- context [seg_writable ?s] => let v := eval vm_compute in (seg_writable s) in replace (seg_writable s) with v by (vm_compute; reflexivity)
  end; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ro_cells_rdn1 : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "Pmem,P,(0.&40.)(1.(0.&8.))PA,$2.Pbs,(3.(0.&8.))Pcs,(3.$4.)P,(5.$6.R4.R3.R1.)P,(7.(3.(0.&8.))(8.R2.)R3.)(7.(1.(3.(0.&8.)))(9.$6.R6.(:.&40.R5.)(;.(0.&8.)R4.))(<.(3.(0.&8.))R4.))")
(* [comment removed for export] *).
Proof.
  intros mem A bs cs [WF B] E. rewrite E in B.
  pose proof (bytes_at_rdn asegs mem A bs 0 (length bs) B ltac:(lia)) as R.
  rewrite Z.add_0_r in R. cbn [skipn] in R. rewrite firstn_all in R. exact R.
Qed.

Section EntryMem.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).   (* [comment removed for export] *)
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable mem : word -> option byte.
  Variable p : me_params.
  Hypothesis HI : me_init sp brk0 rdraw argv envp uid hw p.
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).
  Hypothesis HCOM : Forall (cell_ok ASEGS mem) (cells_common p).
  Hypothesis Hargs : me_args sp brk0 rdraw argv envp uid hw mem.
  Hypothesis Hwin : me_stkwin sp rdraw argv envp uid hw mem.
  Hypothesis HDEF : me_def p mem.

  Let HF := HF mem p HCOM.
  Let SIMG := build_stack_bytes APH sp argv envp uid hw rdraw.
  (* [comment removed for export] *)
  Definition ESTKHI : Z := entry_page_top sp SIMG.
  Let sp0 : Z := bv_unsigned sp.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit HI HCN"] Lemma HSP : sp0 = SP p.
  Proof.
    pose proof (r_s1 p HCN) as R1. pose proof (r_s2 p HCN) as R2.
    unfold sp0. rewrite <- (sp0w_eq sp brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit p HI).
    unfold sp0w, AsanMainEntryLemmas.SP0, SP. rewrite (zev_exact p) by (cbn [zev]; lia). cbn [zev]. lia.
  Qed.
  #[using="Hsp"] Lemma sp0_range : 0x7fff80000000 <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0.
  Proof. ddestruct Hsp as (LO & HIw & AL). unfold sp_window_lo in LO. unfold sp_window_hi in HIw. unfold sp0. lia. Qed.
  #[using="Hfit"] Lemma stkhi_facts : sp0 < ESTKHI /\ ESTKHI mod 4096 = 0 /\ ESTKHI <= 2 ^ 47 /\ sp0 + Z.of_nat (length SIMG) <= ESTKHI.
  Proof.
    pose proof (entry_page_top_ge sp SIMG) as GE. unfold entry_block_top in GE.
    pose proof (entry_page_top_within_window APH sp argv envp uid hw rdraw Hfit) as WIN. unfold sp_window_hi in WIN.
    destruct (build_stack_bytes_split_random APH sp argv envp uid hw) as [pre E].
    assert (LEN : (16 <= length SIMG)%nat).
    { unfold SIMG. rewrite E, length_app. unfold at_random_bytes. rewrite ?length_map, ?length_firstn, ?length_app, ?repeat_length. cbn. lia. }
    fold SIMG in GE, WIN.
    assert (PG : ESTKHI mod 4096 = 0).
    { unfold ESTKHI, entry_page_top, page_round_up_Z, page_size, entry_block_top.
      rewrite Z.mul_comm. apply Z_mod_mult || (rewrite Z.mul_comm; apply Z_mod_mult). }
    unfold ESTKHI, sp0 in *. lia.
  Qed.
  #[using="Type"] Lemma u_lit64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof. intros z Hz. rewrite u_zbv. apply Z.mod_small. exact Hz. Qed.
  #[using="HCN"] Lemma r_tid : 1 <= uv p v_tid <= 0x3fffff.   (* [comment removed for export] *)
  Proof. apply (vrange p HCN). vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Local Ltac zdec := repeat match goal with |- _ /\ _ => split end;
    first [ apply Z.leb_le; vm_compute; reflexivity | apply Z.ltb_lt; vm_compute; reflexivity | apply Z.eqb_eq; vm_compute; reflexivity ].
  (* [comment removed for export] *)
  Local Ltac orc :=
    lazymatch goal with |- ro_cells ?sg ?m ?A ?cs =>
      change (ro_cells asegs m A cs); apply (chk_ro_cells m p CT_COMMON HF QLit A cs);
      [ vm_compute; reflexivity | cbn; repeat split; reflexivity | zdec | zdec ] end.
  Local Ltac orw :=
    lazymatch goal with |- rw_cells ?sg ?m ?A ?cs =>
      change (rw_cells asegs m A cs); apply (chk_rw_cells m p CT_COMMON HF QLit A cs);
      [ vm_compute; reflexivity | cbn; repeat split; reflexivity | zdec | zdec ] end.
  (* [comment removed for export] *)
  Local Ltac ordn cs :=
    lazymatch goal with |- rdn _ ?m (Z_to_bv 64 ?A) _ = Some ?bs =>
      change (rdn asegs m (Z_to_bv 64 A) (length bs) = Some bs);
      apply (ro_cells_rdn1 m A bs cs); [orc | reflexivity] end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac img_cell lo hi :=
    exact (proj1 (Forall_forall _ _) HF (CImg lo hi) ltac:(apply in_map_iff; exists (TImg lo hi); split; [reflexivity | unfold CT_COMMON; rewrite !in_app_iff; left; cbn; tauto])).
  #[using="p HCOM HF"] Lemma img1 : forall i, 0x10000 <= i < 0xf7d10 -> mem (Z_to_bv 64 i) = None.   Proof. img_cell 0x10000 0xf7d10. Qed.
  #[using="p HCOM HF"] Lemma img2 : forall i, 0xf7d2c <= i < 0x106340 -> mem (Z_to_bv 64 i) = None.  Proof. img_cell 0xf7d2c 0x106340. Qed.
  #[using="p HCOM HF"] Lemma img3 : forall i, 0x63c084 <= i < 0x63c9c0 -> mem (Z_to_bv 64 i) = None. Proof. img_cell 0x63c084 0x63c9c0. Qed.

  #[using="sp p HCOM HF sp0"] Theorem entry_files : files_pristine mem.
  Proof. intros a Ha. apply img2. lia. Qed.
  #[using="sp p HCOM HF sp0"] Theorem entry_sifp : forall a, 0x63c0a0 <= a < 0x63c180 -> mem (wa a) = None.
  Proof. intros a Ha. unfold wa. apply img3. lia. Qed.
  #[using="sp p HCOM HF sp0"] Theorem entry_mem_inv : mem_inv asegs mem.
  Proof.
    intros a b Hab. pose proof (ABoot.PropExec.u64_range a) as Ra.
    destruct (Z.ltb_spec0 (bv_unsigned a) 0x10000) as [L|L]; [apply ro_addr_offtextA; lia|].
    destruct (Z.leb_spec0 0x0f1000 (bv_unsigned a)) as [G|G]; [apply ro_addr_offtextA; lia|].
    exfalso. rewrite <- (Z_to_bv_bv_unsigned a) in Hab. rewrite (img1 (bv_unsigned a)) in Hab by lia. discriminate Hab.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCOM HF"] Lemma stack_cell : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "(=.$>.Vmem,(?.(10.(11.Vp,(12.$13.(14.$15.(16.+8000.)(17.$18.))(14.$15.(16.+10.)(17.$19.))))-800000.)(11.Vp,(16.+800000.))))")
(* [comment removed for export] *).
  Proof. me_wr HF ((((#0x8000 * v_s1) + (#16 * v_s2)) .+ (-0x800000)))%tm X. exact X. Qed.
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit HI HCN"] Lemma u_stack_base : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "(7.$2.(1:.&40.(10.(11.Vp,(12.$13.(14.$15.(16.+8000.)(17.$18.))(14.$15.(16.+10.)(17.$19.))))-800000.))(1;.Vsp0,(1<.+2.+17.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (r_s1 p HCN) as R1. pose proof (r_s2 p HCN) as R2. rewrite HSP.
    unfold ABoot.PropExec.v_addi. rewrite u_zbv. rewrite (zev_exact p) by (cbn [zev]; lia). cbn [zev]. unfold SP. rewrite Z.mod_small; lia.
  Qed.
  #[using="sp sp0"] Lemma u_stack_len : bv_unsigned (winst p (#0x800000)%tm) = 2 ^ 23.
  Proof. rewrite (zev_exact p) by (cbn [zev]; lia). reflexivity. Qed.

  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit p HI HCN HCOM HF"] Theorem entry_stk : stk asegs mem (sp0 - 2 ^ 23) sp0.
  Proof.
    dpose sp0_range as (S1 & S2 & S3).
    pose proof (cwr_wr_at mem _ _ stack_cell) as W. rewrite u_stack_base, u_stack_len in W. ddestruct W as (_ & _ & W).
    pose proof (cwr_defined mem _ _ stack_cell) as D. rewrite u_stack_base, u_stack_len in D.
    split; [lia|]. split; [lia|]. intros a Ha. split.
    - specialize (W (a - (sp0 - 2 ^ 23)) ltac:(lia)). replace (sp0 - 2 ^ 23 + (a - (sp0 - 2 ^ 23))) with a in W by lia. exact W.
    - specialize (D ltac:(intros z Hz; unfold AsanPlanSound.APS.in_hull; cbn [AsanPlan.AP.img_lo AsanPlan.AP.img_hi AsanPlan.AP.BOTH]; apply andb_false_iff; right; apply Z.ltb_ge; lia)
                    (a - (sp0 - 2 ^ 23)) ltac:(lia)).
      replace (sp0 - 2 ^ 23 + (a - (sp0 - 2 ^ 23))) with a in D by lia.
      unfold mrd, wa. destruct (mem (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; exact (D eq_refl)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition zimgP (g : Z) : bool := ((0x2000 <=? g) && (g <? 0x49a5))%bool.
  #[using="Type"] Lemma zimg_clear : nz_clear zimgP CELLS_lowshadow = true.
  Proof. vm_compute. reflexivity. Qed.
  #[using="sp p HCOM sp0"] Theorem entry_zimg : forall a : Z, ZIMG_LO <= a < ZIMG_HI -> mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. unfold ZIMG_LO, ZIMG_HI in Ha. replace a with (0x7fff8000 + (a - 0x7fff8000)) by lia.
    apply (me_img_shadow_zero zimgP zimg_clear mem p (HF_low mem p HCOM)).
    - unfold zimgP. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    - lia.
  Qed.
  #[using="sp p HDEF sp0"] Theorem entry_mapped : mapped mem 0x7fffa000 0x800d3000.
  Proof.
    pose proof HDEF as D. unfold me_def in D. ddestruct D as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Dlow).
    revert Dlow. rewrite !(zev_exact p) by (cbn [zev]; lia). cbn [zev]. intros Dlow.
    intros x Hx. specialize (Dlow (wa x) ltac:(rewrite wa_unsigned by lia; lia)).
    destruct (mem (wa x)) as [b|]; [exists b; reflexivity | exfalso; exact (Dlow eq_refl)].
  Qed.

  (* [comment removed for export] *)
  Definition SSH0 : Z := 0x7fff8000 + (STKPG p - 2 ^ 23) / 8.
  Definition SSH1 : Z := 0x10007fff8000.
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit HI HCN"] Lemma ssh0_le : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "(1=.(1>.$1?.(20.+7???8000.(21.(1;.Vsp0,(1<.+2.+17.))+8.)))(1=.(7.$2.(22.(1;.(23.Vp,)(1<.+2.+17.))+1000.)=)(1=.(1>.(23.Vp,)Vsp0,)(1>.+7???7?800000.(1;.(23.Vp,)(1<.+2.+17.))))))")
(* [comment removed for export] *).
  Proof.
    pose proof (r_s1 p HCN) as R1. pose proof (r_s2 p HCN) as R2. pose proof HSP as E. unfold SP in E. unfold SSH0, STKPG.
    repeat split; try nia.
  Qed.
  Definition SSH8 : Z := 4096 * uv p v_s1 + 512 * (uv p v_s2 / 256).
  #[using="sp sp0"] Lemma ssh8_val : 8 * SSH8 = STKPG p.
  Proof. unfold SSH8, STKPG. lia. Qed.
  #[using="sp HCN sp0"] Lemma zev_ssh : zev p ((#0x1000 * v_s1) + (#512 * (WAlu Instr.ALU_SRL v_s2 (#8)%tm)))%tm = SSH8.
  Proof.
    pose proof (r_s1 p HCN) as R1. pose proof (r_s2 p HCN) as R2.
    cbn [zev]. unfold SSH8. rewrite (Z.mod_small (uv p v_s2)) by lia. rewrite (Z.mod_small 8) by lia. try change (2 ^ (8 mod 64)) with 256; try change (2 ^ 8) with 256. reflexivity.
  Qed.
  #[using="sp HCN sp0"] Lemma zev_sshlen : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "(7.$2.(24.Vp,(12.$13.(12.$13.(14.$15.(16.-1000.)(17.$18.))(14.$15.(16.-200.)(12.$25.(17.$19.)(16.+8.))))(16.+100000100000.)))(1;.+100000100000.$26.))")
(* [comment removed for export] *).
  Proof.
    pose proof (r_s1 p HCN) as R1. pose proof (r_s2 p HCN) as R2.
    cbn [zev]. unfold SSH8. rewrite (Z.mod_small (uv p v_s2)) by lia. rewrite (Z.mod_small 8) by lia. try change (2 ^ (8 mod 64)) with 256; try change (2 ^ 8) with 256. lia.
  Qed.
  #[using="sp HCN sp0"] Lemma ssh8_range : 0xffff0000000 <= SSH8 <= 0xffffffffffe.
  Proof. pose proof (r_s1 p HCN) as R1. pose proof (r_s2 p HCN) as R2. unfold SSH8. pose proof (Z.div_pos (uv p v_s2) 256). pose proof (Z.div_lt_upper_bound (uv p v_s2) 256 8 ltac:(lia) ltac:(lia)). lia. Qed.
  #[using="sp HCN sp0"] Lemma u_ssh_base : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "(7.$2.(1:.&40.(10.(11.Vp,(12.$13.(14.$15.(16.+1000.)(17.$18.))(14.$15.(16.+200.)(12.$25.(17.$19.)(16.+8.)))))+7?>?8000.))$1?.)")
(* [comment removed for export] *).
  Proof.
    pose proof ssh8_range as R. pose proof ssh8_val as V.
    unfold ABoot.PropExec.v_addi. rewrite u_zbv. rewrite (zev_exact p) by (rewrite zev_ssh; lia). rewrite zev_ssh.
    unfold SSH0. rewrite Z.mod_small by lia. rewrite <- V. rewrite (Z.mul_comm 8 SSH8).
    replace (SSH8 * 8 - 2 ^ 23) with ((SSH8 - 2 ^ 20) * 8) by lia. rewrite Z.div_mul by lia. lia.
  Qed.
  #[using="sp HCN sp0"] Lemma u_ssh_len : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "(7.$2.(1:.&40.(11.Vp,(12.$13.(12.$13.(14.$15.(16.-1000.)(17.$18.))(14.$15.(16.-200.)(12.$25.(17.$19.)(16.+8.))))(16.+100000100000.))))(1;.$27.$1?.))")
(* [comment removed for export] *).
  Proof.
    pose proof ssh8_range as R. pose proof ssh8_val as V.
    rewrite (zev_exact p) by (rewrite zev_sshlen; lia). rewrite zev_sshlen.
    unfold SSH0, SSH1. rewrite <- V. rewrite (Z.mul_comm 8 SSH8).
    replace (SSH8 * 8 - 2 ^ 23) with ((SSH8 - 2 ^ 20) * 8) by lia. rewrite Z.div_mul by lia. lia.
  Qed.
  #[using="HCOM HF"] Lemma ssh_zcell : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "(=.$>.Vmem,(28.(10.(11.Vp,(12.$13.(14.$15.(16.+1000.)(17.$18.))(14.$15.(16.+200.)(12.$25.(17.$19.)(16.+8.)))))+7?>?8000.)(11.Vp,(12.$13.(12.$13.(14.$15.(16.-1000.)(17.$18.))(14.$15.(16.-200.)(12.$25.(17.$19.)(16.+8.))))(16.+100000100000.)))))")
(* [comment removed for export] *).
  Proof. me_zrun HF ((((#0x1000 * v_s1) + (#512 * (WAlu Instr.ALU_SRL v_s2 #8))) .+ 0x7fef8000))%tm X. exact X. Qed.
  #[using="HCOM HF"] Lemma ssh_wcell : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "(=.$>.Vmem,(?.(10.(11.Vp,(12.$13.(14.$15.(16.+1000.)(17.$18.))(14.$15.(16.+200.)(12.$25.(17.$19.)(16.+8.)))))+7?>?8000.)(11.Vp,(12.$13.(12.$13.(14.$15.(16.-1000.)(17.$18.))(14.$15.(16.-200.)(12.$25.(17.$19.)(16.+8.))))(16.+100000100000.)))))")
(* [comment removed for export] *).
  Proof. me_wr HF ((((#0x1000 * v_s1) + (#512 * (WAlu Instr.ALU_SRL v_s2 #8))) .+ 0x7fef8000))%tm X. exact X. Qed.
  #[using="sp HCN HCOM HF sp0"] Lemma ssh_zero : forall z, SSH0 <= z < SSH1 -> mem (Z_to_bv 64 z) = Some (Z_to_bv 8 0).
  Proof.
    pose proof ssh_zcell as [_ X]. rewrite u_ssh_base, u_ssh_len in X.
    intros z Hz. specialize (X (z - SSH0) ltac:(lia)). replace (SSH0 + (z - SSH0)) with z in X by lia. exact X.
  Qed.
  #[using="sp HCN HCOM HF sp0"] Lemma ssh_wr : wr_at asegs mem SSH0 (SSH1 - SSH0).
  Proof. pose proof (cwr_wr_at mem _ _ ssh_wcell) as W. rewrite u_ssh_base, u_ssh_len in W. exact W. Qed.

  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit p HI HCN HCOM HF"] Theorem entry_zstk : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "Pa,$2.P,(1=.(1>.(29.(:.&40.(1;.Vsp0,+80.)))R1.)(2:.R1.(2;.(:.&40.(1;.Vsp0,+80.)))))(7.(1.(0.&8.))A1.Vmem,(:.&40.R2.)(<.(0.&8.)(:.&8.=)))")
(* [comment removed for export] *).
  Proof.
    dpose sp0_range as (S1 & S2 & S3). dpose ssh0_le as (L0 & _ & L1 & L2).
    intros a Ha. unfold SSH_LO, SSH_HI in Ha. rewrite u_lit64 in Ha by lia. apply ssh_zero. unfold SSH1.
    nia.
  Qed.

  #[using="brk0 Hsp Hva Hve Hfit p HI HCN HCOM HF"] Theorem entry_sshad : sshad asegs AL0 mem (sp0 - 2 ^ 23) ESTKHI.
  Proof.
    dpose sp0_range as (S1 & S2 & S3). dpose ssh0_le as (L0 & LM & L1 & L2). dpose stkhi_facts as (T1 & T2 & T3 & _).
    dpose ssh_wr as (_ & _ & W).
    split; [nia|].
    split; [nia|].
    intros g G1 G2 G3. unfold shadow_of. cbn [al_sb AL0].
    assert (R : SSH0 <= 2147450880 + g / 8 < SSH1).
    { unfold SSH1. unfold SSH0 in *. nia. }
    split.
    - split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; unfold SSH1 in R; lia|].
      intros i Hi.
      cbn in Hi.
      assert (Hi0 : i = 0%nat) by lia.
      subst i.
      cbn [nth_error].
      rewrite Z.add_0_r.
      unfold mrd, wa.
      rewrite (ssh_zero _ R).
      reflexivity.
    - split.
      1: lia.
      split.
      1: change (Z.of_nat (cells_size [C1 (Z_to_bv 8 0)])) with 1; unfold SSH1 in R; lia.
      intros i Hi. change (Z.of_nat (cells_size [C1 (Z_to_bv 8 0)])) with 1 in Hi.
      specialize (W (2147450880 + g / 8 - SSH0) ltac:(lia)).
      replace (SSH0 + (2147450880 + g / 8 - SSH0)) with (2147450880 + g / 8) in W by lia.
      replace (2147450880 + g / 8 + i) with (2147450880 + g / 8) by lia.
      exact W.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition CAN : word := canary p.
  Definition TID : Z := uv p v_tid.
  (* [comment removed for export] *)
  Definition JF : list byte := ltac:(let v := eval vm_compute in (match fbytes QLit CT_COMMON 0x65cb10 240 with Some l => l | None => [] end) in exact v).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="sp HCOM HF sp0"] Lemma entry_can_ro : ro_cells asegs mem 0x65cad0 [C8 CAN].
  Proof. me_word HF (ALit 0x65cad0) 8%nat X. apply (cword_C8 mem _ _ _ _ X); [apply u_lit64; lia | reflexivity | zdec]. Qed.
  #[using="sp HCOM HF sp0"] Lemma entry_can : rdn asegs mem (Z_to_bv 64 0x65cad0) 8%nat = Some (word_to_le_bytes 8 CAN).
  Proof. apply (ro_cells_rdn1 mem 0x65cad0 (word_to_le_bytes 8 CAN) [C8 CAN] entry_can_ro). cbn [cells_bytes cbytes app]. rewrite app_nil_r. reflexivity. Qed.
  #[using="sp HCOM HF sp0"] Lemma entry_mtid : rw_cells asegs mem 0x63c9e8 [C4 (Z_to_bv 64 TID)].
  Proof.
    me_word HF (ALit 0x63c9e8) 4%nat X. split.
    - apply (cword_C4 mem _ _ _ _ X); [apply u_lit64; lia | unfold TID, uv; cbn [pget]; apply Z_to_bv_bv_unsigned | zdec].
    - apply (chk_wr_at mem p CT_COMMON HF QLit 0x63c9e8 4); [vm_compute; reflexivity | zdec | zdec].
  Qed.
  #[using="p HCOM HF"] Lemma entry_atexit : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "(2<.$2=.Vmem,(:.&8.=)(2>.(0.&8.)(:.&8.=)(2>.(0.&8.)(:.&8.=)(2>.(0.&8.)(:.&8.=)(2?.(0.&8.)))))(2>.(0.&8.)(:.&8.=)(2>.(0.&8.)(:.&8.=)(2>.(0.&8.)(:.&8.=)(2>.(0.&8.)(:.&8.=)(2?.(0.&8.))))))$30.)")
(* [comment removed for export] *).
  Proof. unfold atexit_cells, JF. orw. Qed.
  #[using="p HCOM HF"] Lemma entry_glob : stdio_globals mem.
  Proof.
    unfold stdio_globals. repeat match goal with |- _ /\ _ => split end.
    - ordn [C1 (Z_to_bv 8 0)].
    - ordn [C8 (Z_to_bv 64 0)].
    - ordn [C8 (Z_to_bv 64 0x0fa668)].
    - ordn [C8 (Z_to_bv 64 0x0fa578)].
    - ordn [C8 (Z_to_bv 64 0x0fa488)].
  Qed.
  #[using="p HCOM HF"] Lemma entry_file_in : file_clean mem 0x0fa668 (Z_to_bv 64 0) (Z_to_bv 64 0).
  Proof.
    unfold file_clean. repeat match goal with |- _ /\ _ => split end.
    - ordn [C4 (Z_to_bv 64 4294967295)].
    - ordn [C8 (Z_to_bv 64 0)]. - ordn [C8 (Z_to_bv 64 0)]. - ordn [C8 (Z_to_bv 64 0)]. - ordn [C8 (Z_to_bv 64 0)].
  Qed.
  #[using="p HCOM HF"] Lemma entry_file_out : file_clean mem 0x0fa578 (Z_to_bv 64 0) (Z_to_bv 64 0).
  Proof.
    unfold file_clean. repeat match goal with |- _ /\ _ => split end.
    - ordn [C4 (Z_to_bv 64 4294967295)].
    - ordn [C8 (Z_to_bv 64 0)]. - ordn [C8 (Z_to_bv 64 0)]. - ordn [C8 (Z_to_bv 64 0)]. - ordn [C8 (Z_to_bv 64 0)].
  Qed.

  (* [comment removed for export] *)
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit HI HCN HCOM HDEF HF"] Theorem entry_tailA : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "(31.(:.&40.(1;.Vsp0,+80.))Vmem,$32.$33.(:.&40.=)(:.&40.=)(:.&40.=)(:.&40.=))")
(* [comment removed for export] *).
  Proof.
    dpose sp0_range as (S1 & S2 & S3). dpose entry_stk as (_ & _ & ST). pose proof r_tid as RT.
    split.
    - (* [comment removed for export] *) intros a Ha. rewrite u_lit64 in Ha by lia. rewrite <- (Z_to_bv_bv_unsigned a). exact (proj1 (ST (bv_unsigned a) ltac:(lia))).
    - (* [comment removed for export] *) intros a Ha. apply img1. lia.
    - (* [comment removed for export] *) intros a Ha. apply img2. lia.
    - exact entry_can.
    - exact (h0_asan_rtc mem p HCOM).
    - exact entry_zimg.
    - exact entry_zstk.
    - (* [comment removed for export] *) rewrite u_lit64 by lia. eapply (proj2 (stk_split asegs mem (sp0 - 2 ^ 23) (sp0 - 128 - 4096) (sp0 - 128) _ ltac:(lia))).
      Unshelve. exact (proj1 (stk_split asegs mem (sp0 - 2 ^ 23) (sp0 - 128) sp0 entry_stk ltac:(lia))).
    - exact entry_mem_inv.
    - unfold TID. lia.
    - (* [comment removed for export] *) orw.
    - exact entry_mtid.
    - eexists _, _, _. exact entry_atexit.
    - (* [comment removed for export] *) orc.
    - (* [comment removed for export] *) orw.
    - exact entry_mapped.
    - exact entry_glob.
    - exact entry_file_in.
    - exact entry_file_out.
    - (* [comment removed for export] *) orw.
    - (* [comment removed for export] *) orw.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let argc : Z := Z.of_nat (length argv).
  Let envc : Z := Z.of_nat (length envp).
  (* [comment removed for export] *)
  Definition APTR (k : nat) : word := cat_argv_ptr sp argv envp k.

  #[using="sp sp0"] Lemma struct_size_val : Z.of_nat (cat_struct_size argv envp) = 8 * argc + 8 * envc + 184.
  Proof. unfold cat_struct_size, argc, envc. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. change (Z.of_nat auxv_size) with 160. lia. Qed.
  #[using="sp0 argc envc"] Lemma bsb_len_lowerA : (cat_struct_size argv envp + ABoot.PropExec.total_arg_bytes_nat argv + 16 <= length SIMG)%nat.
  Proof.
    unfold SIMG, build_stack_bytes, cat_struct_size. cbv zeta.
    rewrite (string_addrs_pair argv). cbv beta iota. rewrite (string_addrs_pair envp). cbv beta iota.
    rewrite !length_app, !ABoot.PropExec.length_flat_map_le8, !ABoot.PropExec.length_string_addrs_fst, !ABoot.PropExec.length_n_to_le_8, length_auxv_bytes,
      !ABoot.PropExec.length_flatten_strings, !repeat_length, length_at_random_bytes.
    lia.
  Qed.
  #[using="sp envp sp0 argc envc"] Lemma total_firstn_le : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "Pk,$34.P,(35.R1.(;.(3.(0.&8.))Vargv,))(36.(37.(37.(38.(39.(3.(0.&8.))R2.Vargv,))(;.(0.&8.)(3:.(3.(0.&8.))R2.Vargv,(2?.(0.&8.)))))#1.)(38.Vargv,))")
(* [comment removed for export] *).
  Proof.
    intros k Hk. revert k Hk. generalize argv as l. induction l as [|s l IH]; intros k Hk; [cbn in Hk; lia|].
    destruct k as [|k]; cbn [firstn nth]; rewrite ?total_arg_bytes_cons.
    - change (ABoot.PropExec.total_arg_bytes_nat []) with 0%nat. lia.
    - cbn in Hk. specialize (IH k ltac:(lia)). lia.
  Qed.
  (* [comment removed for export] *)
  #[using="Hsp Hfit argc envc"] Lemma aptr_val : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "Pk,$34.P,(35.R1.(;.(3.(0.&8.))Vargv,))(1=.(7.$2.(1:.&40.(3;.R2.))(20.(20.Vsp0,(3<.(3=.Vargv,Venvp,)))(3<.(38.(39.(3.(0.&8.))R2.Vargv,)))))(1>.(20.(20.(1:.&40.(3;.R2.))(3<.(;.(0.&8.)(3:.(3.(0.&8.))R2.Vargv,(2?.(0.&8.))))))+1.)(1;.(20.Vsp0,(3<.(;.(0.&8.)VSIMG,)))+10.)))")
(* [comment removed for export] *).
  Proof.
    intros k Hk. dpose sp0_range as (S1 & S2 & S3). dpose stkhi_facts as (T1 & T2 & T3 & T4).
    pose proof bsb_len_lowerA as LOW. pose proof (total_firstn_le k Hk) as MONO.
    assert (E : bv_unsigned (APTR k) = sp0 + Z.of_nat (cat_struct_size argv envp) + Z.of_nat (ABoot.PropExec.total_arg_bytes_nat (firstn k argv))).
    { unfold APTR. rewrite (cat_argv_ptr_offset sp argv envp k Hk). unfold cat_string_base. rewrite nat_to_word_add_merge, word_add_nat.
      unfold sp0 in *. rewrite u_Z2bv by lia. lia. }
    split; [exact E | rewrite E; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hfit Hwin argc envc"] Lemma win_wr_at : forall lo n, sp0 <= lo -> 0 <= n -> lo + n <= sp0 + Z.of_nat (length SIMG) -> wr_at asegs mem lo n.
  Proof.
    intros lo n H1 H2 H3. dpose stkhi_facts as (T1 & T2 & T3 & T4). dpose sp0_range as (S1 & S2 & S3).
    apply (def_wr_at mem); [| lia | lia | lia]. intros a Ha. apply Hwin. unfold ESTKHI, SIMG, sp0 in *. lia.
  Qed.
  #[using="brk0 rdraw uid hw Hsp Hva Hve Hfit p HI HCN HCOM Hwin HF SIMG argc envc"] Theorem entry_argv_ptr0 : rw_cells asegs mem (sp0 + 8) [C8 (APTR 0)].
  Proof.
    dpose sp0_range as (S1 & S2 & S3). dpose stkhi_facts as (T1 & T2 & T3 & T4). pose proof bsb_len_lowerA as LOW.
    pose proof (r_s1 p HCN) as R1. pose proof (r_s2 p HCN) as R2. pose proof (valid_argv_nonempty argv Hva) as NE.
    destruct (aptr_val 0%nat ltac:(lia)) as [E B]. replace (Z.of_nat (ABoot.PropExec.total_arg_bytes_nat (firstn 0 argv))) with 0 in E by reflexivity. rewrite struct_size_val in E.
    pose proof HI as IE. ddestruct IE as (_ & Iargc & Ienvc & Ilen0 & _).
    pose proof (valid_argv_len argv Hva) as AVL. destruct Hve as (EVL & _).
    assert (Hargc : uv p v_argc = argc). { unfold uv. cbn [pget]. rewrite Iargc. unfold argc. apply u_lit64. lia. }
    assert (Henvc : uv p v_envc = envc). { unfold uv. cbn [pget]. rewrite Ienvc. unfold envc. apply u_lit64. lia. }
    me_word HF ((((#0x8000 * v_s1) + (#16 * v_s2)) .+ 8))%tm 8%nat X0.
    pose proof (X0 : cell_ok ASEGS mem (CWord (ABoot.PropExec.v_addi (winst p ((#0x8000 * v_s1) + (#16 * v_s2))%tm) 8) 8
                                              (winst p (((#0x8000 * v_s1) + ((#8 * v_argc) + ((#8 * v_envc) + (#16 * v_s2)))) + #184)%tm))) as X. clear X0.
    split.
    - apply (cword_C8 mem _ _ _ _ X).
      + unfold ABoot.PropExec.v_addi. rewrite u_zbv, (zev_exact p) by (cbn [zev]; lia). cbn [zev]. rewrite HSP. unfold SP. apply Z.mod_small. lia.
      + apply bv_eq. rewrite E, (zev_exact p) by (cbn [zev]; nia). cbn [zev]. rewrite HSP in *. unfold SP in *.
        nia.
      + lia.
    - change (Z.of_nat (cells_size [C8 (APTR 0)])) with 8. apply win_wr_at; rewrite ?struct_size_val in LOW |- *; lia.
  Qed.
  #[using="brk0 rdraw uid hw Hsp Hva Hve Hfit p HI HCN HCOM Hwin HF SIMG argc envc"] Theorem entry_argv_ptr1 : (2 <= length argv)%nat -> rw_cells asegs mem (sp0 + 16) [C8 (APTR 1)].
  Proof.
    intros H2. dpose sp0_range as (S1 & S2 & S3). dpose stkhi_facts as (T1 & T2 & T3 & T4). pose proof bsb_len_lowerA as LOW.
    pose proof (r_s1 p HCN) as R1. pose proof (r_s2 p HCN) as R2.
    destruct (aptr_val 1%nat ltac:(lia)) as [E B]. rewrite struct_size_val in E.
    assert (F1 : forall l : list (list byte), (2 <= length l)%nat ->
                 Z.of_nat (ABoot.PropExec.total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1).
    { intros [|a0 l] Hl; [cbn in Hl; lia|]. cbn [firstn nth]. rewrite total_arg_bytes_cons. change (ABoot.PropExec.total_arg_bytes_nat (firstn 0 l)) with 0%nat. lia. }
    rewrite (F1 argv H2) in E.
    pose proof HI as IE. ddestruct IE as (_ & Iargc & Ienvc & Ilen0 & _).
    pose proof (valid_argv_len argv Hva) as AVL. destruct Hve as (EVL & _).
    pose proof (valid_argv_str_len argv 0%nat Hva ltac:(lia)) as L0.
    assert (Hargc : uv p v_argc = argc). { unfold uv. cbn [pget]. rewrite Iargc. unfold argc. apply u_lit64. lia. }
    assert (Henvc : uv p v_envc = envc). { unfold uv. cbn [pget]. rewrite Ienvc. unfold envc. apply u_lit64. lia. }
    assert (Hlen0 : uv p v_len0 = Z.of_nat (length (nth 0 argv []))). { unfold uv. cbn [pget]. rewrite Ilen0. apply u_lit64. lia. }
    me_word HF ((((#0x8000 * v_s1) + (#16 * v_s2)) .+ 16))%tm 8%nat X0.
    pose proof (X0 : cell_ok ASEGS mem (CWord (ABoot.PropExec.v_addi (winst p ((#0x8000 * v_s1) + (#16 * v_s2))%tm) 16) 8
                                              (winst p ((#1 <u v_argc) * (((#0x8000 * v_s1) + ((#8 * v_argc) + ((#8 * v_envc) + (v_len0 + (#16 * v_s2))))) + #185))%tm))) as X. clear X0.
    split.
    - apply (cword_C8 mem _ _ _ _ X).
      + unfold ABoot.PropExec.v_addi. rewrite u_zbv, (zev_exact p) by (cbn [zev]; lia). cbn [zev]. rewrite HSP. unfold SP. apply Z.mod_small. lia.
      + apply bv_eq. rewrite E, (zev_sound p). cbn [zev]. change (1 mod 2 ^ 64) with 1.
        rewrite (Z.mod_small (uv p v_argc)) by (rewrite Hargc; unfold argc; lia). rewrite Hargc, Henvc, Hlen0.
        replace (1 <? argc) with true by (symmetry; apply Z.ltb_lt; unfold argc; lia). cbv iota. rewrite Z.mul_1_l.
        rewrite HSP in *. unfold SP in *. rewrite Z.mod_small; nia.
      + lia.
    - change (Z.of_nat (cells_size [C8 (APTR 1)])) with 8. apply win_wr_at; rewrite ?struct_size_val in LOW |- *; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma argH_string : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "Pa,(0.&40.)P,(1=.(1>.(20.Vsp0,(20.(20.(3>.+8.Vargc,)(3>.+8.Venvc,))+;8.))(1:.&40.R1.))(2:.(1:.&40.R1.)(1;.(20.Vsp0,(3<.(;.(0.&8.)VSIMG,)))+10.)))(7.$3?.(40.$41.Vsp,Vrdraw,Vargv,Venvp,Vuid,Vhw,(42.$41.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)R2.)$43.)")
(* [comment removed for export] *).
  Proof.
    intros a Ha. pose proof (bsb_ge APH sp rdraw argv envp uid hw) as [G M]. fold SIMG in G, M.
    unfold argH0. apply orb_true_intro. right. apply andb_true_intro.
    fold SIMG. unfold argc, envc, sp0 in *.
    set (W := (Z.of_nat (length SIMG) - 16 - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184)) / 8) in *.
    assert (HW : 8 * W = Z.of_nat (length SIMG) - 16 - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184)).
    { subst W. nia. }
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  #[using="brk0 Hsp Hfit Hargs"] Theorem entry_argv_str : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "Pk,$34.P,(35.R1.(;.(3.(0.&8.))Vargv,))(1=.(44.$6.Vmem,(1:.&40.(3;.R2.))(45.(0.&8.)(3:.(3.(0.&8.))R2.Vargv,(2?.(0.&8.)))(2>.(0.&8.)(:.&8.=)(2?.(0.&8.)))))(1=.(1>.(20.(20.(20.Vsp0,(3>.+8.Vargc,))(3>.+8.Venvc,))+;8.)(1:.&40.(3;.R2.)))(1>.(20.(20.(1:.&40.(3;.R2.))(3<.(;.(0.&8.)(3:.(3.(0.&8.))R2.Vargv,(2?.(0.&8.))))))+11.)$46.)))")
(* [comment removed for export] *).      (* [comment removed for export] *)
  Proof.
    intros k Hk. dpose sp0_range as (S1 & S2 & S3). dpose stkhi_facts as (T1 & T2 & T3 & T4).
    destruct (aptr_val k Hk) as [E B]. rewrite struct_size_val in E.
    assert (NW : bv_unsigned sp + Z.of_nat (length (build_stack_bytes APH sp argv envp uid hw rdraw)) < 2 ^ 64) by (fold SIMG; unfold sp0 in *; lia).
    split; [| split; [lia | lia]].
    split; [lia|]. split; [rewrite length_app; cbn [length]; lia|].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    pose proof (read_argv_byte_k APH asegs sp argv envp k i uid hw rdraw Hk ltac:(lia) NW) as RD.
    apply (rdn_nth asegs _ 1%nat _ _ 0%nat) in RD; [|lia]. cbn [nth_error] in RD. rewrite woff0 in RD.
    fold (APTR k) in RD. rewrite word_add_nat in RD.
    set (a := Z_to_bv 64 (bv_unsigned (APTR k) + Z.of_nat i)) in RD.
    assert (Ua : bv_unsigned a = bv_unsigned (APTR k) + Z.of_nat i) by (subst a; apply u_lit64; lia).
    assert (AH : argH0 APH sp rdraw argv envp uid hw (E0 APH sp rdraw brk0 argv envp uid hw) a = true) by (apply argH_string; rewrite Ua; lia).
    pose proof (Hargs a AH) as MA. rewrite (ABoot.PropExec.wrap_above_sp APH sp argv envp a uid hw rdraw) in MA by (rewrite Ua; unfold sp0 in *; lia).
    rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite length_app; cbn [length]; lia).
    rewrite <- RD. unfold wa. fold a. unfold mrd. rewrite MA. reflexivity.
  Qed.
End EntryMem.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
