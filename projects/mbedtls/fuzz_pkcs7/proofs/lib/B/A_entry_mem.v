(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the section takes the launch input and mmap base main_entry_A names, with their ties, the launch premises and the new stack cells; the stack-window premise me_stkwin no longer takes argv, envp, uid and hwcap; the stack VMA's end ESTKHI is the draw's page top, its facts from the launch; the stack below sp is the window [sp0 - 6144512, sp0) read from the new stack cell; the argv pointer words and strings are read from the new stack cells and the launch's layout lemmas, the strings now at the top of the block, with the bound pathp + length + 11 <= ESTKHI; entry_stk, entry_sshad and entry_tailA use the new floor). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import StepTac CatExec AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs AsanPlanImages. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanInit AsanMainEntryKit. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Asn1Aux CellsX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_exit_base A_exit_lib A_exit_front1 A_tailkit_defs A_main_inv.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AHeapR AH0Facts AH0Base AH0Layout AH0Mem0 AH0Mem1 AH0XR.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_entry_mem () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Step.ro_cells"; "OSSVerify.KrLib.B.AImg.asegs"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.Cells.cells_bytes"; "OSSVerify.KrLib.Lib.PropExec.rdn"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.ABoot.AsanMainEntryKit.cell_ok"; "OSSVerify.KrLib.BBoot.AsanCertDefs.ASEGS"; "OSSVerify.KrLib.ABoot.AsanMainEntryKit.CWr"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "OSSVerify.KrLib.BBoot.AsanMainEntryFacts.winst"; "OSSVerify.KrLib.BBoot.AsanMainEntryFacts.WAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "OSSVerify.KrLib.BBoot.AsanMainEntryFacts.WMd"; "LinuxProcessSemantics.Riscv.Instr.M_MUL"; "OSSVerify.KrLib.BBoot.AsanMainEntryFacts.WLit"; "OSSVerify.KrLib.BBoot.AsanMainEntryFacts.WVar"; "OSSVerify.KrLib.BBoot.AsanMainEntryFacts.v_s1"; "OSSVerify.KrLib.BBoot.AsanMainEntryFacts.v_s2"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "EntryMem.SSH0"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.BHeap.AH0Base.STKPG"; "OSSVerify.KrLib.BHeap.AH0Base.zev"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "EntryMem.SSH8"; "EntryMem.SSH1"; "OSSVerify.KrLib.ABoot.AsanMainEntryKit.CZero"; "OSSVerify.KrLib.B.A_tailkit_defs.SSH_LO"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.B.A_tailkit_defs.SSH_HI"; "OSSVerify.KrLib.B.A_exit_front1.atexit_cells"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "EntryMem.JF"; "OSSVerify.KrLib.B.A_tailkit_defs.tail_memA"; "EntryMem.CAN"; "EntryMem.TID"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "OSSVerify.KrLib.ABoot.PropExec.total_arg_bytes_nat"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.nth"; "EntryMem.APTR"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.ABoot.CatExec.cat_struct_size"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.ABoot.AsanInit.argH0"; "OSSVerify.KrLib.BBoot.AsanPlanImages.APH"; "OSSVerify.KrLib.ABoot.AsanInit.E0"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.app"; "EntryMem.ESTKHI"].


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
  (* LPS 727298f3: the launch input and the mmap base that [main_entry_A] names, with their ties
     and the launch premises *)
  Variable inp : ProcInput.
  Variable mb : word.
  Hypothesis Eav : in_argv inp = argv.
  Hypothesis Eev : in_envp inp = envp.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mb rdraw) inp.
  Variable mem : word -> option byte.
  Variable p : me_params.
  Hypothesis HI : me_init sp brk0 rdraw inp p.
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).
  Hypothesis HCOM : Forall (cell_ok ASEGS mem) (cells_common p).
  (* LPS 727298f3: the new stack cells (the window below sp, the argv[0] and argv[1] words) *)
  Hypothesis HSTK : Forall (cell_ok ASEGS mem) (cells_stk (RZI inp) p).
  Hypothesis Hargs : me_args sp brk0 rdraw inp mb mem.
  (* #38: [me_stkwin]'s bound is now [entry_page_top rdraw], so it no longer mentions
     [argv]/[envp]/[uid]/[hw] and no longer discharges over them. *)
  Hypothesis Hwin : me_stkwin sp rdraw mem.
  Hypothesis HDEF : me_def p mem.
  #[local] Notation ENTW := (Z_to_bv 64 (Z.of_N AsanUbsan.M.init_pc)) (only parsing).

  Let HF := HF mem p HCOM.
  (* LPS 727298f3: the stack VMA's end is the draw's [ed_top] ([Run.entry_page_top]) *)
  Definition ESTKHI : Z := entry_page_top rdraw.
  Let sp0 : Z := bv_unsigned sp.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit HI HCN"] Lemma HSP : sp0 = SP p.
  Proof.
    pose proof (r_s1 p HCN) as R1. pose proof (r_s2 p HCN) as R2.
    unfold sp0. rewrite <- (sp0w_eq sp brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp p HI).
    unfold sp0w, AsanMainEntryLemmas.SP0, SP. rewrite (zev_exact p) by (cbn [zev]; lia). cbn [zev]. lia.
  Qed.
  #[using="Hsp"] Lemma sp0_range : 0x7fff80000000 <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0.
  Proof. ddestruct Hsp as (LO & HIw & AL). unfold sp_window_lo in LO. unfold sp_window_hi in HIw. unfold sp0. lia. Qed.
  (* LPS 727298f3: the block's head (argc, the pointer vectors, the auxv, the AT_RANDOM bytes) is
     at least 472 bytes, so the stack VMA's end is well above sp ([launch_stkhi_facts]) *)
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp mb Eav Eev Hvl Hlau mem p HI HCN HCOM HSTK Hargs Hwin HDEF HF sp0"] Lemma stkhi_facts : sp0 + 128 < ESTKHI /\ ESTKHI mod 4096 = 0 /\ ESTKHI <= 2 ^ 47 /\ ESTKHI <= sp0 + 2101782.
  Proof.
    destruct (launch_stkhi_facts sp brk0 mb rdraw inp Hvl Hlau) as (T2 & T3 & T1 & T4).
    pose proof (AsanPlanCore.APC.AUXSZ_of (kb_rseq (in_kernel inp))) as HX. unfold AsanPlanCore.APC.AUXSZ in HX.
    pose proof (AsanPlanCore.APC.rseq_z_range (kb_rseq (in_kernel inp))) as HR.
    pose proof (Nat2Z.is_nonneg (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
    unfold block_head_size in T1. cbv zeta in T1.
    unfold ESTKHI, sp0. repeat split; lia.
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
  (* LPS 727298f3: the stack window is the first of the new stack cells: [sp0 - 6144513, sp0),
     the window the launch maps below sp ([MemSplit.wok_lo]); the stack floor is sp0 - 6144512. *)
  #[using="HSTK"] Lemma stack_cell : cell_ok ASEGS mem (CWr (ABoot.PropExec.v_addi (winst p SP_T) (-6144513)) (winst p (WLit 6144513))).
  Proof. apply (proj1 (Forall_forall _ _) HSTK). unfold cells_stk, CELLS_stk. cbn [map In]. left. reflexivity. Qed.
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit HI HCN sp0"] Lemma u_stack_base : bv_unsigned (ABoot.PropExec.v_addi (winst p SP_T) (-6144513)) = sp0 - 6144513.
  Proof.
    pose proof (r_s1 p HCN) as R1. pose proof (r_s2 p HCN) as R2. rewrite HSP.
    unfold ABoot.PropExec.v_addi. rewrite u_zbv. unfold SP_T. rewrite (zev_exact p) by (cbn [zev]; lia). cbn [zev]. unfold SP. rewrite Z.mod_small; lia.
  Qed.
  #[using="sp sp0"] Lemma u_stack_len : bv_unsigned (winst p (WLit 6144513)) = 6144513.
  Proof. rewrite (zev_exact p) by (cbn [zev]; lia). reflexivity. Qed.

  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp mb Eav Eev Hvl Hlau mem p HI HCN HCOM HSTK Hargs Hwin HDEF HF sp0"] Theorem entry_stk : stk asegs mem (sp0 - 6144512) sp0.
  Proof.
    dpose sp0_range as (S1 & S2 & S3).
    pose proof (cwr_wr_at mem _ _ stack_cell) as W. rewrite u_stack_base, u_stack_len in W. ddestruct W as (_ & _ & W).
    pose proof (cwr_defined mem _ _ stack_cell) as D. rewrite u_stack_base, u_stack_len in D.
    split; [lia|]. split; [lia|]. intros a Ha. split.
    - specialize (W (a - (sp0 - 6144513)) ltac:(lia)). replace (sp0 - 6144513 + (a - (sp0 - 6144513))) with a in W by lia. exact W.
    - specialize (D ltac:(intros z Hz; unfold AsanPlanSound.APS.in_hull; cbn [AsanPlan.AP.img_lo AsanPlan.AP.img_hi AsanPlan.AP.BOTH]; apply andb_false_iff; right; apply Z.ltb_ge; lia)
                    (a - (sp0 - 6144513)) ltac:(lia)).
      replace (sp0 - 6144513 + (a - (sp0 - 6144513))) with a in D by lia.
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

  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp mb Eav Eev Hvl Hlau mem p HI HCN HCOM HSTK Hargs Hwin HDEF HF sp0"] Theorem entry_sshad : sshad asegs AL0 mem (sp0 - 6144512) ESTKHI.
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
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp mb Eav Eev Hvl Hlau mem p HI HCN HCOM HSTK Hargs Hwin HDEF HF sp0"] Theorem entry_tailA : ltac2:(CDefT.buildp (gd_tbl_A_entry_mem ()) "(31.(:.&40.(1;.Vsp0,+80.))Vmem,$32.$33.(:.&40.=)(:.&40.=)(:.&40.=)(:.&40.=))")
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
    - (* [comment removed for export] *) rewrite u_lit64 by lia. eapply (proj2 (stk_split asegs mem (sp0 - 6144512) (sp0 - 128 - 4096) (sp0 - 128) _ ltac:(lia))).
      Unshelve. exact (proj1 (stk_split asegs mem (sp0 - 6144512) (sp0 - 128) sp0 entry_stk ltac:(lia))).
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
  (* LPS 727298f3: the argv pointers and strings sit where the launch puts them: the strings at
     the TOP of the block, argv[0] at [STRB = ed_top - 8 - L] ([CatExec.u_cat_string_base]), which is
     [sp0 + C + W] ([StackLayout.block_pad_len]); the pointer words at sp0+8 and sp0+16 are the second
     and third new stack cells, whose values are that address over [me_params]. *)
  Let argc : Z := Z.of_nat (length argv).
  Let envc : Z := Z.of_nat (length envp).
  Definition APTR (k : nat) : word := cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) k.
  Definition STRB : Z := bv_unsigned (ed_top rdraw) - 8 - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)).

  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp mb Eav Eev Hvl Hlau mem p HI HCN HCOM HSTK Hargs Hwin HDEF HF sp0 argc envc"] Lemma aptr_u : forall k, (k < length argv)%nat ->
    bv_unsigned (APTR k) = STRB + Z.of_nat (ABoot.PropExec.total_arg_bytes_nat (firstn k argv))
    /\ bv_unsigned (APTR k) + Z.of_nat (length (nth k argv [])) + 11 <= ESTKHI.
  Proof.
    intros k Hk.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Eav; exact Hk).
    pose proof (CatExec.u_cat_string_base Sv48 inp mb sp brk0 rdraw Hlau) as HU.
    pose proof (CatExec.launch_string_base_arith Sv48 inp mb sp brk0 rdraw Hlau) as HA.
    pose proof (CatExec.total_arg_bytes_firstn_within (in_argv inp) k Hk') as HW.
    pose proof (valid_execfn_len (in_execfn inp) (proj1 Hvl)) as HX.
    pose proof (ABoot.PropExec.u64_range sp) as R1. pose proof (ABoot.PropExec.u64_range (ed_top rdraw)) as R2.
    pose proof (Nat2Z.is_nonneg (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))) as R3.
    (* the strings after argv[k]'s NUL include at least the exec file name and its NUL *)
    assert (HLn : (ABoot.PropExec.total_arg_bytes_nat (firstn k (in_argv inp)) + length (nth k (in_argv inp) []) + 3
                   <= launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))%nat).
    { unfold launch_string_bytes. rewrite !ABoot.PropExec.length_flatten_strings.
      apply (Nat.le_trans _ (ABoot.PropExec.total_arg_bytes_nat (in_argv inp) + 2)).
      - replace (ABoot.PropExec.total_arg_bytes_nat (firstn k (in_argv inp)) + length (nth k (in_argv inp) []) + 3)%nat
          with (ABoot.PropExec.total_arg_bytes_nat (firstn k (in_argv inp)) + length (nth k (in_argv inp) []) + 1 + 2)%nat
          by (rewrite <- !Nat.add_assoc; reflexivity).
        apply Nat.add_le_mono; [exact HW | apply Nat.le_refl].
      - clear - HX. lia. }
    assert (HL : Z.of_nat (ABoot.PropExec.total_arg_bytes_nat (firstn k (in_argv inp))) + Z.of_nat (length (nth k (in_argv inp) [])) + 3
                 <= Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
    { clear - HLn. lia. }
    assert (EA : APTR k = cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
      by (unfold APTR; rewrite Eav, Eev; reflexivity).
    rewrite EA. rewrite <- Eav.
    rewrite (CatExec.cat_argv_ptr_offset _ _ _ _ k Hk'), CatExec.word_add_nat_Z2bv, HU.
    (* the facts in this file's own terms, each by lia on its few premises, then used up to conversion *)
    assert (Z1 : 0 <= bv_unsigned (ed_top rdraw) - 8 - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))
                      + Z.of_nat (ABoot.PropExec.total_arg_bytes_nat (firstn k (in_argv inp)))) by (clear - HA R1 R3; lia).
    assert (Z2 : bv_unsigned (ed_top rdraw) - 8 - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))
                 + Z.of_nat (ABoot.PropExec.total_arg_bytes_nat (firstn k (in_argv inp))) < 2 ^ 64) by (clear - HL R2; lia).
    assert (Z3 : bv_unsigned (ed_top rdraw) - 8 - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))
                 + Z.of_nat (ABoot.PropExec.total_arg_bytes_nat (firstn k (in_argv inp)))
                 + Z.of_nat (length (nth k (in_argv inp) [])) + 11 <= bv_unsigned (ed_top rdraw)) by (clear - HL; lia).
    rewrite CatExec.u_Z2bv_lt by first [exact Z1 | exact Z2].
    unfold STRB, ESTKHI, entry_page_top. split; [reflexivity | exact Z3].
  Qed.

  (* [STRB] over [me_params]: [C = 8*argc + 8*envc + 472 + 32*rz + 8*G] ([StackLayout.block_head_size],
     [AsanPlanCore.AUXSZ_of]), and the pad [W] is what the launch leaves ([StackLayout.block_pad_len]) *)
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp mb Eav Eev Hvl Hlau mem p HI HCN HCOM HSTK Hargs Hwin HDEF HF sp0 argc envc"] Lemma strb_val :
    STRB = sp0 + 8 * argc + 8 * envc + 472 + 32 * RZI inp + 8 * uv p v_vg + uv p v_wblk
    /\ 0 <= uv p v_vg <= 1 /\ 0 <= uv p v_wblk.
  Proof.
    pose proof (CatExec.launch_string_base_arith Sv48 inp mb sp brk0 rdraw Hlau) as HA.
    pose proof (AsanPlanCore.APC.AUXSZ_of (kb_rseq (in_kernel inp))) as HX. unfold AsanPlanCore.APC.AUXSZ in HX.
    pose proof (ABoot.PropExec.u64_range sp). pose proof (ABoot.PropExec.u64_range (ed_top rdraw)).
    pose proof (Nat2Z.is_nonneg (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
    pose proof (Nat2Z.is_nonneg (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
    pose proof HI as IE. ddestruct IE as (_ & _ & _ & _ & Iw & _ & _ & _ & _ & _ & Ig & _).
    pose proof (Nat.mod_upper_bound (block_items (in_argv inp) (in_envp inp)) 2 ltac:(lia)) as G2.
    assert (UW : uv p v_wblk = Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp))).
    { unfold uv. cbn [pget]. rewrite Iw. apply u_lit64. unfold block_pad_len. rewrite Z2Nat.id by lia. lia. }
    assert (UG : uv p v_vg = Z.of_nat (block_items (in_argv inp) (in_envp inp) mod 2)).
    { unfold uv. cbn [pget]. rewrite Ig. apply u_lit64. lia. }
    rewrite UW, UG.
    unfold block_pad_len. rewrite Z2Nat.id by lia.
    unfold STRB, RZI, argc, envc, sp0. rewrite <- Eav, <- Eev.
    unfold block_head_size, block_items in *. cbv zeta in *. split; [|split]; lia.
  Qed.

  (* the words at sp0+8 and sp0+16 are writable: they are stack VMA bytes above sp *)
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp mb Eav Eev Hvl Hlau mem p HI HCN HCOM HSTK Hargs Hwin HDEF HF sp0 argc envc"] Lemma win_wr_at : forall lo n, sp0 <= lo -> 0 <= n -> lo + n <= ESTKHI -> wr_at asegs mem lo n.
  Proof.
    intros lo n H1 H2 H3. dpose stkhi_facts as (T1 & T2 & T3 & T4). dpose sp0_range as (S1 & S2 & S3).
    apply (def_wr_at mem); [| lia | lia | lia]. intros a Ha. apply Hwin. unfold ESTKHI, sp0 in *. lia.
  Qed.
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp mb Eav Eev Hvl Hlau mem p HI HCN HCOM HSTK Hargs Hwin HDEF HF sp0 argc envc"] Lemma argv0_cell : cell_ok ASEGS mem (cinst p (TWord (AOff SP_T 8) 8 (STR0_T (RZI inp)))).
  Proof. apply (proj1 (Forall_forall _ _) HSTK). unfold cells_stk, CELLS_stk. cbn [map In]. right. left. reflexivity. Qed.
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp mb Eav Eev Hvl Hlau mem p HI HCN HCOM HSTK Hargs Hwin HDEF HF sp0 argc envc"] Lemma argv1_cell : cell_ok ASEGS mem (cinst p (TWord (AOff SP_T 16) 8 (WMd M_MUL (WAlu ALU_SLTU (WLit 1) (WVar v_argc)) (STR1_T (RZI inp))))).
  Proof. apply (proj1 (Forall_forall _ _) HSTK). unfold cells_stk, CELLS_stk. cbn [map In]. right. right. left. reflexivity. Qed.
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp mb Eav Eev Hvl Hlau mem p HI HCN HCOM HSTK Hargs Hwin HDEF HF sp0 argc envc"] Lemma uv_argc_envc : uv p v_argc = argc /\ uv p v_envc = envc /\ uv p v_len0 = Z.of_nat (length (nth 0 argv [])).
  Proof.
    pose proof HI as IE. ddestruct IE as (_ & Iargc & Ienvc & Ilen0 & _).
    pose proof (valid_argv_len argv Hva) as AVL. pose proof Hve as (EVL & _).
    pose proof (valid_argv_str_len argv 0%nat Hva ltac:(pose proof (valid_argv_nonempty argv Hva); lia)) as L0.
    unfold uv, argc, envc. cbn [pget]. rewrite Iargc, Ienvc, Ilen0, Eav, Eev.
    split; [|split]; apply u_lit64; lia.
  Qed.

  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp mb Eav Eev Hvl Hlau mem p HI HCN HCOM HSTK Hargs Hwin HDEF HF sp0 argc envc"] Theorem entry_argv_ptr0 : rw_cells asegs mem (sp0 + 8) [C8 (APTR 0)].
  Proof.
    dpose sp0_range as (S1 & S2 & S3). dpose stkhi_facts as (T1 & T2 & T3 & T4).
    pose proof (r_s1 p HCN) as R1. pose proof (r_s2 p HCN) as R2. pose proof (valid_argv_nonempty argv Hva) as NE.
    pose proof (valid_argv_len argv Hva) as AVL. pose proof Hve as (EVL & _).
    assert (AE : 0 <= argc /\ 0 <= envc) by (unfold argc, envc; lia).
    destruct (aptr_u 0%nat ltac:(lia)) as [E B]. replace (Z.of_nat (ABoot.PropExec.total_arg_bytes_nat (firstn 0 argv))) with 0 in E by reflexivity.
    destruct strb_val as (SV & G01 & W0). destruct uv_argc_envc as (Hargc & Henvc & _).
    pose proof (RZI_range inp) as RZR. pose proof (ABoot.PropExec.u64_range (APTR 0)) as UA.
    pose proof argv0_cell as X. cbn [cinst ainst] in X.
    split.
    - apply (cword_C8 mem _ _ _ _ X).
      + unfold ABoot.PropExec.v_addi. rewrite u_zbv, (zev_exact p) by (unfold SP_T; cbn [zev]; lia). unfold SP_T. cbn [zev]. rewrite HSP. unfold SP. apply Z.mod_small. lia.
      + apply bv_eq. rewrite E, (zev_exact p) by (unfold STR0_T; cbn [zev]; rewrite HSP in *; unfold SP in *; nia). unfold STR0_T. cbn [zev].
        rewrite HSP in *. unfold SP in *. nia.
      + lia.
    - change (Z.of_nat (cells_size [C8 (APTR 0)])) with 8. apply win_wr_at; lia.
  Qed.
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp mb Eav Eev Hvl Hlau mem p HI HCN HCOM HSTK Hargs Hwin HDEF HF sp0 argc envc"] Theorem entry_argv_ptr1 : (2 <= length argv)%nat -> rw_cells asegs mem (sp0 + 16) [C8 (APTR 1)].
  Proof.
    intros H2. dpose sp0_range as (S1 & S2 & S3). dpose stkhi_facts as (T1 & T2 & T3 & T4).
    pose proof (r_s1 p HCN) as R1. pose proof (r_s2 p HCN) as R2.
    pose proof (valid_argv_len argv Hva) as AVL. pose proof Hve as (EVL & _).
    pose proof (valid_argv_str_len argv 0%nat Hva ltac:(lia)) as L0.
    assert (AE : 0 <= argc /\ 0 <= envc) by (unfold argc, envc; lia).
    destruct (aptr_u 1%nat ltac:(lia)) as [E B].
    assert (F1 : forall l : list (list byte), (2 <= length l)%nat ->
                 Z.of_nat (ABoot.PropExec.total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1).
    { intros [|a0 l] Hl; [cbn in Hl; lia|].
      change (Z.of_nat (length a0 + 1 + 0)%nat = Z.of_nat (length a0) + 1).
      rewrite Nat.add_0_r, Nat2Z.inj_add. reflexivity. }
    rewrite (F1 argv H2) in E.
    destruct strb_val as (SV & G01 & W0). destruct uv_argc_envc as (Hargc & Henvc & Hlen0).
    pose proof (RZI_range inp) as RZR. pose proof (ABoot.PropExec.u64_range (APTR 1)) as UA.
    pose proof argv1_cell as X. cbn [cinst ainst] in X.
    split.
    - apply (cword_C8 mem _ _ _ _ X).
      + unfold ABoot.PropExec.v_addi. rewrite u_zbv, (zev_exact p) by (unfold SP_T; cbn [zev]; lia). unfold SP_T. cbn [zev]. rewrite HSP. unfold SP. apply Z.mod_small. lia.
      + apply bv_eq. rewrite E, (zev_sound p). unfold STR1_T. cbn [zev]. change (1 mod 2 ^ 64) with 1.
        rewrite (Z.mod_small (uv p v_argc)) by (rewrite Hargc; unfold argc; lia). rewrite Hargc, Henvc, Hlen0.
        replace (1 <? argc) with true by (symmetry; apply Z.ltb_lt; unfold argc; lia). cbv iota. rewrite Z.mul_1_l.
        rewrite HSP in *. unfold SP in *. rewrite Z.mod_small; nia.
      + lia.
    - change (Z.of_nat (cells_size [C8 (APTR 1)])) with 8. apply win_wr_at; lia.
  Qed.

  (* the strings: [me_args] makes [mem] the launch's image on the string area [STRB, ed_top)
     ([AsanInit.argH0]'s second part) *)
  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp mb Eav Eev Hvl Hlau mem p HI HCN HCOM HSTK Hargs Hwin HDEF HF sp0 argc envc"] Lemma argH_string : forall a : word, STRB <= bv_unsigned a < ESTKHI ->
    argH0 sp rdraw inp (E0 sp rdraw brk0 inp) a = true.
  Proof.
    intros a Ha. pose proof (CatExec.launch_string_base_arith Sv48 inp mb sp brk0 rdraw Hlau) as HA.
    pose proof (ABoot.PropExec.u64_range sp). pose proof (ABoot.PropExec.u64_range (ed_top rdraw)).
    pose proof (Nat2Z.is_nonneg (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
    pose proof (Nat2Z.is_nonneg (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
    unfold argH0. cbv zeta. apply orb_true_intro. right. apply andb_true_intro.
    unfold block_pad_len. rewrite Z2Nat.id by lia.
    unfold STRB, ESTKHI, entry_page_top in *. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  #[using="brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp mb Eav Eev Hvl Hlau mem p HI HCN HCOM HSTK Hargs Hwin HDEF HF sp0 argc envc"] Theorem entry_argv_str : forall k, (k < length argv)%nat ->
    bytes_at asegs mem (bv_unsigned (APTR k)) (nth k argv [] ++ [Z_to_bv 8 0])
    /\ sp0 + 8 * argc + 8 * envc + 472 <= bv_unsigned (APTR k)
    /\ bv_unsigned (APTR k) + Z.of_nat (length (nth k argv [])) + 11 <= ESTKHI.
  Proof.
    intros k Hk. dpose sp0_range as (S1 & S2 & S3). dpose stkhi_facts as (T1 & T2 & T3 & T4).
    destruct (aptr_u k Hk) as [E B]. destruct strb_val as (SV & G01 & W0). pose proof (RZI_range inp) as RZR.
    assert (AE : 0 <= argc /\ 0 <= envc) by (unfold argc, envc; lia).
    pose proof (Nat2Z.is_nonneg (ABoot.PropExec.total_arg_bytes_nat (firstn k argv))).
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Eav; exact Hk).
    assert (EA : APTR k = cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
      by (unfold APTR; rewrite Eav, Eev; reflexivity).
    split; [| split; [lia | lia]].
    split; [lia|]. split; [rewrite length_app; cbn [length]; lia|].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    assert (Hi' : (i <= length (nth k (in_argv inp) []))%nat) by (rewrite Eav; lia).
    pose proof (CatExec.read_argv_byte_k Sv48 asegs inp mb APH ENTW sp brk0 rdraw k i Hlau Hk' Hi') as RD.
    apply (rdn_nth asegs _ 1%nat _ _ 0%nat) in RD; [|lia]. cbn [nth_error] in RD. rewrite woff0 in RD.
    set (a := Z_to_bv 64 (bv_unsigned (APTR k) + Z.of_nat i)).
    (* RD's address read back as [a], up to conversion *)
    assert (RD2 : mrd asegs (stack_to_mem sp (entry_stack_image inp mb APH ENTW sp rdraw)) a
                  = Some (nth i (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
    { subst a. rewrite <- word_add_nat, EA. exact RD. }
    clear RD. rename RD2 into RD.
    assert (Ua : bv_unsigned a = bv_unsigned (APTR k) + Z.of_nat i) by (subst a; apply u_lit64; lia).
    assert (AH : argH0 sp rdraw inp (E0 sp rdraw brk0 inp) a = true) by (apply argH_string; rewrite Ua; lia).
    pose proof (Hargs a AH) as MA. rewrite (ABoot.PropExec.wrap_above_sp inp mb APH ENTW sp rdraw a) in MA by (rewrite Ua; unfold sp0 in *; lia).
    rewrite Eav in RD.
    rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite length_app; cbn [length]; lia).
    rewrite <- RD. unfold wa. fold a. unfold mrd. rewrite MA. reflexivity.
  Qed.
End EntryMem.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
