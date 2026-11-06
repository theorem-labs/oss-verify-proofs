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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Import Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2 Require T_Ubs2 C_S0 C_LE C_LP C_S3.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.UbsN Require T_UbsN C_S0 C_LE C_LP C_S3.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2F Require T_Ubs2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2A Require T_Ubs2A.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2D Require T_Ubs2D.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2T Require T_Ubs2T.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.UbsNU Require T_UbsNU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound StackInit InitLib InitClf RootUbs2 InitUbs2 RootUbsN InitUbsN OblsLib OblsClf
  Ops SysSpec CtrSys StdioWrite DrvShape DrvRoot DrvLib DrvEdges OblsStart DrvTop.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Ubs2F_9 Ubs2A_5 Ubs2D_10 Ubs2T_5 UbsNU_6 Ubs2F_1 Ubs2A_1 Ubs2D_1 Ubs2T_1 UbsNU_1.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS SW DrvShape DrvRoot DrvLib.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module T2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2.T_Ubs2.
Module S0_2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2.C_S0.
Module LE_2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2.C_LE.
Module LP_2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2.C_LP.
Module S3_2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2.C_S3.
Module TN := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.UbsN.T_UbsN.
Module S0_N := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.UbsN.C_S0.
Module LE_N := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.UbsN.C_LE.
Module LP_N := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.UbsN.C_LP.
Module S3_N := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.UbsN.C_S3.
Module DF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2F.T_Ubs2F.
Module DA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2A.T_Ubs2A.
Module DD := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2D.T_Ubs2D.
Module DT := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2T.T_Ubs2T.
Module DN := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.UbsNU.T_UbsNU.
Module RF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Ubs2F_9.
Module RA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Ubs2A_5.
Module RD := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Ubs2D_10.
Module RT := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Ubs2T_5.
Module RN := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.UbsNU_6.
Module HF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Ubs2F_1.
Module HA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Ubs2A_1.
Module HD := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Ubs2D_1.
Module HT := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Ubs2T_1.
Module HN := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.UbsNU_1.

Module RunUbs.

Definition RS : Z := 360729.
Lemma RS_range : 0 <= RS /\ RS + 65536 <= two64. Proof. unfold RS, two64. lia. Qed.
Definition REMAT : list (int * int) := [(355944, 8); (360400, 4); (360408, 8); (360416, 8); (360432, 8); (360440, 8); (360456, 8); (360472, 8); (360536, 4); (360544, 4); (429036, 4); (560896, 8); (560931, 1); (562024, 1); (562025, 1); (562026, 1); (562027, 1); (562028, 1); (562029, 1); (562030, 1); (562031, 1); (428984, 1); (428985, 1); (428986, 1); (428987, 1); (428988, 1); (428989, 1); (428990, 1); (428991, 1); (426328, 8); (426336, 4)]%uint63.

Definition XCL : list HeapOp.iv := [(65536, 495504); (561984, 3264)].
Definition XCLZ : list (Z * Z) := map HeapOp.to_lohi XCL.
Definition AST_LO : Z := 561040.
Definition AST_HI : Z := 561984.
Definition HULL : list (Z * Z) := [(65536, 565248)].

Definition FL : int := 426352%uint63.
Definition PFP : list (Z * Z) := [(426352, 426352 + 8); (426352 + 16, 426352 + 528)].
Lemma FL8 : to_Z FL mod 8 = 0. Proof. reflexivity. Qed.
Lemma FLB : to_Z FL + 1024 < 2 ^ 62. Proof. reflexivity. Qed.
Lemma FLz : to_Z FL = 426352. Proof. reflexivity. Qed.
Definition POOLC : opcomp := OpComp (Pool.pool_holds FL SEGS) (Pool.pool_fp FL) (PoolSnd.pool_frame SEGS FL (fun _ => True) FL8 FLB).

Definition PFP_PARK : list (Z * Z) := [(426352, 426352 + 8); (426352 + 24, 426352 + 32); (426352 + 216, 426352 + 224)].
Lemma pool_fp_eq : forall w, Pool.pool_fp FL [w] = if (bv_unsigned w =? 3) then [] else if (bv_unsigned w <? 3) then PFP else PFP_PARK.
Proof. intros w. unfold Pool.pool_fp. destruct (bv_unsigned w =? 3); [reflexivity|]. destruct (bv_unsigned w <? 3); vm_compute; reflexivity. Qed.
Lemma pfp_park_sub : forall a, Exists (fun iv => fst iv <= a < snd iv) PFP_PARK -> Exists (fun iv => fst iv <= a < snd iv) PFP.
Proof.
  intros a X. unfold PFP_PARK, PFP in *.
  apply Exists_cons in X as [X|X]; [apply Exists_cons_hd; cbn [fst snd] in *; lia|].
  apply Exists_cons_tl. apply Exists_cons_hd.
  apply Exists_cons in X as [X|X]; [cbn [fst snd] in *; lia|]. apply Exists_cons in X as [X|X]; [cbn [fst snd] in *; lia| inversion X].
Qed.

Definition WNOFF : w64 := wn 9223372036846387200%uint63.
Lemma WNOFF_val : w2Z WNOFF = two64 - DrvTop.WOFF. Proof. reflexivity. Qed.
Definition HARGS : list sv := DrvTop.HARGS WNOFF.

Definition BL : list (int * Z) := [(15%uint63, 2147483648)].
Definition DRVOPS : list opinst := [OpI 7%uint63 [VL wzero]; OpI 1%uint63 HARGS; OpI 5%uint63 []; OpI 3%uint63 [VL wzero; VL wzero]].

Definition R0_2 : region := match IMap.find 0%uint63 (s_regs (t_st T2.T_MAIN2)) with Some r => r | None => Region 0%uint63 (VL wzero) false BGImage IMap.empty end.
Definition R0_N : region := match IMap.find 0%uint63 (s_regs (t_st TN.T_MAINN)) with Some r => r | None => Region 0%uint63 (VL wzero) false BGImage IMap.empty end.
Lemma FIND0_2 : IMap.find 0%uint63 (s_regs (t_st T2.T_MAIN2)) = Some R0_2. Proof. vm_compute. reflexivity. Qed.
Lemma FIND0_N : IMap.find 0%uint63 (s_regs (t_st TN.T_MAINN)) = Some R0_N. Proof. vm_compute. reflexivity. Qed.
Lemma BG0_2 : rg_bg R0_2 = BGImage. Proof. vm_compute. reflexivity. Qed.
Lemma BG0_N : rg_bg R0_N = BGImage. Proof. vm_compute. reflexivity. Qed.
Lemma UNT_FL_2 : DrvTop.range_untouched R0_2 426352 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma UNT_FL_N : DrvTop.range_untouched R0_N 426352 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma UNT_AST_2 : DrvTop.range_untouched R0_2 AST_LO (AST_HI - AST_LO) = true. Proof. vm_compute. reflexivity. Qed.
Lemma UNT_AST_N : DrvTop.range_untouched R0_N AST_LO (AST_HI - AST_LO) = true. Proof. vm_compute. reflexivity. Qed.
Lemma ZERO_FL : DrvTop.range_zero SEGS 426352 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma AST_IMAGE : DrvTop.range_in_image SEGS AST_LO (AST_HI - AST_LO) = true. Proof. vm_compute. reflexivity. Qed.
Lemma SP_2 : DrvTop.ranged (s_facts (t_st T2.T_MAIN2)) 1%uint63 DrvTop.SPLO DrvTop.WLEN = true. Proof. vm_compute. reflexivity. Qed.
Lemma SP_N : DrvTop.ranged (s_facts (t_st TN.T_MAINN)) 1%uint63 DrvTop.SPLO DrvTop.WLEN = true. Proof. vm_compute. reflexivity. Qed.
Lemma OPS_F : s_ops DF.T_DRV2 = DRVOPS. Proof. reflexivity. Qed.
Lemma OPS_A : s_ops DA.T_DRV2 = DRVOPS. Proof. reflexivity. Qed.
Lemma OPS_D : s_ops DD.T_DRV2 = DRVOPS. Proof. reflexivity. Qed.
Lemma OPS_T : s_ops DT.T_DRV2 = DRVOPS. Proof. reflexivity. Qed.
Lemma OPS_N : s_ops DN.T_DRVN = DRVOPS. Proof. reflexivity. Qed.

Lemma DRV_CHK_F : DrvTop.drv_chk SEGS BL HULL XCLZ PFP RS REMAT 0%uint63 (t_st T2.T_MAIN2) DF.T_DRV2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma DRV_CHK_A : DrvTop.drv_chk SEGS BL HULL XCLZ PFP RS REMAT 0%uint63 (t_st T2.T_MAIN2) DA.T_DRV2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma DRV_CHK_D : DrvTop.drv_chk SEGS BL HULL XCLZ PFP RS REMAT 0%uint63 (t_st T2.T_MAIN2) DD.T_DRV2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma DRV_CHK_T : DrvTop.drv_chk SEGS BL HULL XCLZ PFP RS REMAT 0%uint63 (t_st T2.T_MAIN2) DT.T_DRV2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma DRV_CHK_N : DrvTop.drv_chk SEGS BL HULL XCLZ PFP RS REMAT 0%uint63 (t_st TN.T_MAINN) DN.T_DRVN = true. Proof. vm_compute. reflexivity. Qed.

Lemma main2_resv : s_resv (t_st T2.T_MAIN2) = RNone. Proof. reflexivity. Qed.
Lemma mainN_resv : s_resv (t_st TN.T_MAINN) = RNone. Proof. reflexivity. Qed.
Lemma s3_eq2 : post_set_tid T2.T_SETTID2 = Some T2.ROOT_S32. Proof. vm_compute. reflexivity. Qed.
Lemma s3_eqN : post_set_tid TN.T_SETTIDN = Some TN.ROOT_S3N. Proof. vm_compute. reflexivity. Qed.
Lemma start_obls_LE2 : forallb OblsStart.chk_start_obl LE_2.OBLS = true. Proof. vm_compute. reflexivity. Qed.
Lemma start_obls_LP2 : forallb OblsStart.chk_start_obl LP_2.OBLS = true. Proof. vm_compute. reflexivity. Qed.
Lemma start_obls_LEN : forallb OblsStart.chk_start_obl LE_N.OBLS = true. Proof. vm_compute. reflexivity. Qed.
Lemma start_obls_LPN : forallb OblsStart.chk_start_obl LP_N.OBLS = true. Proof. vm_compute. reflexivity. Qed.

Section TOP.

Variable inp : ProcInput.
Variables (sp brk0 mb : word) (rnd : EntryDraw) (lim : Z).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hhw : valid_hwcap (in_hwcap inp).
Hypothesis Hsz : in_va_size inp = Sv48.
Hypothesis Hen : valid_entry (mkImage SEGS PC PH) (mkEntry sp brk0 mb rnd) inp.

Definition c0 : config := init_config SEGS PC PH sp brk0 mb rnd lim inp.
Definition model0 : Model := cfg_model c0.
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
Definition MP0 (m : Model) : Prop := m = model0.
Definition MP1 (m : Model) : Prop := exists tid, m = with_tid tid model0.

Variables (A : HeapOp.alloc_world SEGS XCL) (C : HeapOp.client_world).

Hypothesis aw_fds : forall aw LB ws m mo fds, HeapOp.aw_holds SEGS XCL A aw LB ws m mo -> HeapOp.aw_holds SEGS XCL A aw LB ws m (with_fds fds mo).
Hypothesis aw_ceil_fds : forall mo fds, HeapOp.aw_ceiling SEGS XCL A (with_fds fds mo) = HeapOp.aw_ceiling SEGS XCL A mo.

Hypothesis cw_init : forall lo m, HeapOp.cw_holds C 0 [] [] [HeapOp.Win lo DrvTop.WLEN 0] m.
Definition HEAPC : opcomp := OpComp (HeapOp.heap_holds SEGS XCL A C) (HeapOp.heap_fp XCL) (HeapOp.heap_frame SEGS XCL A C).
Lemma heap_fds : forall args m model fds, oc_holds HEAPC args m model -> oc_holds HEAPC args m (with_fds fds model).
Proof.
  intros args m model fds (md & aw & ws & ca & LB & D & HA & WF & HC). cbn [oc_holds HEAPC]. unfold HeapOp.heap_holds.
  exists md, aw, ws, ca, LB. rewrite aw_ceil_fds. repeat split; try assumption. apply aw_fds. exact HA.
Qed.
Lemma heap_fp_stage : forall args a, RS <= a < RS + 65536 -> ~ Exists (fun iv => fst iv <= a < snd iv) (oc_fp HEAPC args).
Proof.
  intros args a Ha X. cbn [oc_fp HEAPC] in X.
  destruct (HeapOp.decode args) as [[[[md aw] ws] ca]|] eqn:D.
  - destruct (proj1 (HeapOp.fp_spec XCL args md aw ws ca a D) X) as (_ & NX & _). apply NX.
    unfold HeapOp.in_ivs, XCL. apply Exists_cons_hd. unfold HeapOp.in_iv. cbn [fst snd]. unfold RS in Ha. lia.
  - unfold HeapOp.heap_fp in X. rewrite D in X. inversion X.
Qed.
Lemma pool_fds : forall args m model fds, oc_holds POOLC args m model -> oc_holds POOLC args m (with_fds fds model).
Proof. intros args m model fds H. cbn [oc_holds POOLC] in *. destruct args as [|w [|]]; exact H. Qed.
Lemma pool_fp_stage : forall args a, RS <= a < RS + 65536 -> ~ Exists (fun iv => fst iv <= a < snd iv) (oc_fp POOLC args).
Proof.
  intros args a Ha X. cbn [oc_fp POOLC] in X. destruct args as [|w [|w' l]]; [inversion X | | inversion X].
  rewrite pool_fp_eq in X. destruct (bv_unsigned w =? 3); [inversion X|].
  assert (X' : Exists (fun iv => fst iv <= a < snd iv) PFP) by (destruct (bv_unsigned w <? 3); [exact X| exact (pfp_park_sub a X)]).
  clear X. unfold PFP, RS in *.
  repeat (apply Exists_cons in X' as [X'|X']; [cbn [fst snd] in X'; lia|]). inversion X'.
Qed.

Definition EXT (id : int) : opcomp :=
  if PrimInt63.eqb id 7%uint63 then POOLC else if PrimInt63.eqb id 6%uint63 then DrvTop.SPLINK else oc_true.
Lemma ext_fds : forall id args m model fds, oc_holds (EXT id) args m model -> oc_holds (EXT id) args m (with_fds fds model).
Proof.
  intros id. unfold EXT. destruct (PrimInt63.eqb id 7%uint63); [apply pool_fds |].
  destruct (PrimInt63.eqb id 6%uint63); [| intros; exact I].
  intros args m model fds H. destruct args as [|w [|w' l]]; cbn [oc_holds DrvTop.SPLINK oc_pure DrvTop.splink_holds] in *; exact H.
Qed.
Lemma ext_fp_stage : forall id args a, RS <= a < RS + 65536 -> ~ Exists (fun iv => fst iv <= a < snd iv) (oc_fp (EXT id) args).
Proof.
  intros id. unfold EXT. destruct (PrimInt63.eqb id 7%uint63); [apply pool_fp_stage |].
  destruct (PrimInt63.eqb id 6%uint63); intros args a _ X; inversion X.
Qed.

Hypothesis aw_ceil0 : forall tid, HeapOp.aw_ceiling SEGS XCL A (with_tid tid model0) <= bv_unsigned sp - DrvTop.WOFF.
Hypothesis aw_init : forall mem tid lo,
  (forall a, AST_LO <= a < AST_HI -> rb SEGS mem a = img_byte SEGS a) ->
  HeapOp.aw_holds SEGS XCL A (Z_to_bv 64 0) [] [HeapOp.Win lo DrvTop.WLEN 0] mem (with_tid tid model0).

Lemma model0_tid : m_tid model0 = None. Proof. reflexivity. Qed.
Lemma MP_fs : forall m, MP m -> m_fs m = fs0. Proof. intros m H. exact H. Qed.
Lemma MP_fds : forall fds m, MP m -> MP (with_fds fds m). Proof. intros fds m H. exact H. Qed.

Lemma MP_stable : mp_stable MP.
Proof. intros mo acc mo' H M. unfold MP in *. destruct (materialize_model_accesses_frame _ _ _ M) as (_ & _ & _ & _ & F & _). unfold m_fs. rewrite F. exact H. Qed.
Lemma model0_lazy : m_vm_lazy model0 = []. Proof. reflexivity. Qed.
Lemma MP0_stable : mp_stable MP0.
Proof. intros mo acc mo' -> H. rewrite (materialize_model_accesses_no_lazy _ _ model0_lazy) in H. injection H as <-. reflexivity. Qed.
Lemma MP1_stable : mp_stable MP1.
Proof. intros mo acc mo' (tid & ->) H. assert (L : m_vm_lazy (with_tid tid model0) = []) by exact model0_lazy.
  rewrite (materialize_model_accesses_no_lazy _ _ L) in H. injection H as <-. exists tid. reflexivity. Qed.
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
Lemma a0_nz : ~ In (Z_to_bv 8 0) a0.
Proof. destruct Hva as (_ & _ & _ & HZ & _). exact (proj1 (Forall_forall _ _) HZ a0 a0_In). Qed.
Lemma p1_noslash : path_has_slash p1 = false /\ path_eqb p1 dotdot_path = false.
Proof.
  destruct Hva as (_ & _ & _ & _ & HS). unfold p1. destruct (in_argv inp) as [|x [|y l]]; cbn [hd tl]; try (split; reflexivity).
  exact (proj1 (Forall_forall _ _) HS y (or_introl eq_refl)).
Qed.

Definition TM : tab_model HEAPC (FD3 p1 file) (RSTAGE file RS RS_range) FD3DIR FDINIT EXT :=
  plain_tm HEAPC (FD3 p1 file) (RSTAGE file RS RS_range) FD3DIR FDINIT EXT.
Lemma TM_fds : forall mo fds, op_minv (CtrSys.OPS HEAPC EXT p1 file RS RS_range TM) mo -> op_minv (CtrSys.OPS HEAPC EXT p1 file RS RS_range TM) (with_fds fds mo).
Proof. intros mo fds [H L]. split; assumption. Qed.
Lemma TM_cov1 : forall id args a, op_cov1 (CtrSys.OPS HEAPC EXT p1 file RS RS_range TM) id args a -> id = 1%uint63.
Proof. intros id args a []. Qed.
Lemma TM_plain : plain_table (CtrSys.OPS HEAPC EXT p1 file RS RS_range TM).
Proof. split; [intros mo; reflexivity| intros a; exact I]. Qed.

Definition R : drun :=
  DRun HEAPC EXT a0 p1 file fs0 RS RS_range MP PB MP_fs MP_fds MP_stable heap_fds heap_fp_stage ext_fds ext_fp_stage
       (fun b (H : PB b) => match eq_sym H in (_ = e) return (e 1%uint63 = cstr a0 /\ e 9%uint63 = LE8 (Z.of_nat (length a0) + 1)) with eq_refl => conj eb1 eb9 end)
       (fun b (H : PB b) => match eq_sym H in (_ = e) return (e 3%uint63 = cstr p1 /\ e 10%uint63 = LE8 (Z.of_nat (length p1) + 1)) with eq_refl => conj eb3 eb10 end)
       a0_len p1_len p1_nz TM TM_fds TM_cov1.
Lemma OPS_R : OPS R = CtrSys.OPS HEAPC EXT p1 file RS RS_range TM. Proof. reflexivity. Qed.

Lemma OPS_plain_R : plain_table (OPS R). Proof. exact TM_plain. Qed.
Lemma file_pb_R : file_pb R. Proof. intros b ->. cbn [r_file R]. repeat split; reflexivity. Qed.
Lemma HBL : forall E j c, r_PB R (eb E) -> In (j, c) BL -> bv_unsigned (den E (VBlob false j (VL wzero) 8%uint63)) <= c.
Proof.
  intros E j c HPB [H|[]]. injection H as <- <-. cbn [r_PB R] in HPB. unfold PB in HPB.
  assert (E15 : eb E 15%uint63 = LE8 (Z.of_nat (length (SI.strarea (in_argv inp) (in_envp inp))))) by (rewrite HPB; reflexivity).
  pose proof (proj1 (valid_entry_sv48 _ _ _ Hsz) Hen) as (Hsp' & _ & _ & Hfit).
  pose proof (SI.BSB_top PH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd Hfit) as T. rewrite SI.length_BSB in T.
  pose proof (SI.length_strarea (in_argv inp) (in_envp inp)) as L. pose proof (SI.SP_lo sp Hsp') as LO.
  change wzero with (wp 0%uint63). rewrite (OL.den_param8_u E 15%uint63 _ E15); unfold SI.raw_len, SI.SP in *; lia.
Qed.

Lemma splink_iff : forall E mem m o, ops_hold (OPS R) E [OpI 6%uint63 [VP 1%uint63 o]] mem m <->
  bv_unsigned (den E (VP 1%uint63 o)) = bv_unsigned (vm_init_sp (m_vmmaps m)).
Proof.
  intros E mem m o. unfold ops_hold, OPS, CtrSys.OPS. cbn [r_heap r_ext r_p1 r_file r_RS r_RSr R].
  rewrite Forall_cons_iff, Forall_nil_iff, mk_holds. cbn [op_id op_args map].
  rewrite (comp_ext HEAPC (FD3 p1 file) (RSTAGE file RS RS_range) FD3DIR FDINIT EXT 6%uint63) by reflexivity.
  unfold EXT. cbn [PrimInt63.eqb oc_holds DrvTop.SPLINK oc_pure DrvTop.splink_holds]. tauto.
Qed.
Lemma splink_tid : forall E mem m tid o, ops_hold (OPS R) E [OpI 6%uint63 [VP 1%uint63 o]] mem m ->
  ops_hold (OPS R) E [OpI 6%uint63 [VP 1%uint63 o]] mem (with_tid tid m).
Proof. intros E mem m tid o H. apply splink_iff. apply splink_iff in H. exact H. Qed.
Lemma settid_pure2 : forall E mem m tid, ops_hold (OPS R) E (s_ops T2.T_SETTID2) mem m -> ops_hold (OPS R) E (s_ops T2.T_SETTID2) mem (with_tid tid m).
Proof. intros E mem m tid. exact (splink_tid E mem m tid (wp 0%uint63)). Qed.
Lemma settid_pureN : forall E mem m tid, ops_hold (OPS R) E (s_ops TN.T_SETTIDN) mem m -> ops_hold (OPS R) E (s_ops TN.T_SETTIDN) mem (with_tid tid m).
Proof. intros E mem m tid. exact (splink_tid E mem m tid (wp 0%uint63)). Qed.

Lemma main_sp : forall MAIN E ms tid, s_ops MAIN = [OpI 6%uint63 [VP 1%uint63 (wp 0%uint63)]] ->
  st_ok SEGS (OPS R) E MAIN ms (with_tid tid model0) -> bv_unsigned (ev E 1%uint63) = bv_unsigned sp.
Proof.
  intros MAIN E ms tid HO HS. pose proof (so_ops _ _ _ _ _ _ HS) as H. rewrite HO in H. apply splink_iff in H.
  rewrite (DrvTop.den_VP_zero E 1%uint63 (wp 0%uint63) eq_refl) in H. exact H.
Qed.

Lemma root_ops2 : forall ms, st_ok SEGS (OPS R) E0 ROOT_Ubs2 ms model0 -> st_ok SEGS (OPS R) E0 S0_2.ROOT ms model0.
Proof.
  intros ms HS. apply (with_ops_priv_sound SEGS R E0 ROOT_Ubs2 RootUbs2.ROOT_OPS RootUbs2.ROOT_PRIV S0_2.ROOT ms model0 HS).
  - unfold S0_2.ROOT. rewrite InitUbs2.root_eq. reflexivity.
  - apply splink_iff. rewrite (DrvTop.den_VP_zero E0 1%uint63 (wp 0%uint63) eq_refl). reflexivity.
  - apply Forall_cons; [|constructor]. intros a Ha. exfalso. unfold OPS, CtrSys.OPS in Ha. rewrite mk_fp in Ha. cbn [op_id op_args r_heap r_ext r_p1 r_file r_RS r_RSr R] in Ha.
    rewrite (comp_ext HEAPC (FD3 p1 file) (RSTAGE file RS RS_range) FD3DIR FDINIT EXT 6%uint63) in Ha by reflexivity.
    unfold EXT in Ha. cbn in Ha. inversion Ha.
  - intros r g gr c _ _ _ i _ X. inversion X.
Qed.
Lemma root_opsN : forall ms, st_ok SEGS (OPS R) E0 ROOT_UbsN ms model0 -> st_ok SEGS (OPS R) E0 S0_N.ROOT ms model0.
Proof.
  intros ms HS. apply (with_ops_priv_sound SEGS R E0 ROOT_UbsN RootUbsN.ROOT_OPS RootUbsN.ROOT_PRIV S0_N.ROOT ms model0 HS).
  - unfold S0_N.ROOT. rewrite InitUbsN.root_eq. reflexivity.
  - apply splink_iff. rewrite (DrvTop.den_VP_zero E0 1%uint63 (wp 0%uint63) eq_refl). reflexivity.
  - apply Forall_cons; [|constructor]. intros a Ha. exfalso. unfold OPS, CtrSys.OPS in Ha. rewrite mk_fp in Ha. cbn [op_id op_args r_heap r_ext r_p1 r_file r_RS r_RSr R] in Ha.
    rewrite (comp_ext HEAPC (FD3 p1 file) (RSTAGE file RS RS_range) FD3DIR FDINIT EXT 6%uint63) in Ha by reflexivity.
    unfold EXT in Ha. cbn in Ha. inversion Ha.
  - intros r g gr c _ _ _ i _ X. inversion X.
Qed.

Definition ops0_ok (MAIN D : sstate) : Prop :=
  forall E ms m tid, st_ok SEGS (OPS R) E MAIN ms m -> m = with_tid tid model0 -> ops_hold (OPS R) E (s_ops D) (ms_mem ms) m.
Definition op_init (MAIN : sstate) (Cmp : opcomp) (args : list sv) : Prop :=
  forall E ms m tid, st_ok SEGS (OPS R) E MAIN ms m -> m = with_tid tid model0 -> oc_holds Cmp (map (den E) args) (ms_mem ms) m.

Lemma ops0_of_parts : forall MAIN D, s_ops D = DRVOPS -> op_init MAIN POOLC [VL wzero] -> op_init MAIN HEAPC HARGS -> ops0_ok MAIN D.
Proof.
  intros MAIN D HD HP HH E ms m tid HS Hm. rewrite HD. unfold ops_hold, DRVOPS.
  unfold OPS, CtrSys.OPS. cbn [r_heap r_ext r_p1 r_file r_RS r_RSr R].
  repeat apply Forall_cons; try apply Forall_nil; rewrite mk_holds; cbn [op_id op_args].
  - rewrite (comp_ext HEAPC (FD3 p1 file) (RSTAGE file RS RS_range) FD3DIR FDINIT EXT 7%uint63) by reflexivity.
    unfold EXT. cbn. exact (HP E ms m tid HS Hm).
  - rewrite comp_1. exact (HH E ms m tid HS Hm).
  - rewrite comp_5. cbn [FDINIT oc_pure oc_holds fdinit_holds map]. subst m. rewrite m_fds_with_tid. reflexivity.
  - rewrite comp_3. cbn [RSTAGE oc_holds rstage_holds map den]. rewrite !wbv_unsigned. change (w2Z wzero) with 0.
    unfold RS_LEN. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma decode_HARGS : forall E, HeapOp.decode (map (den E) HARGS) = Some (0, wbv wzero, [HeapOp.Win (DrvTop.wlo WNOFF E) DrvTop.WLEN 0], []).
Proof.
  intros E. cbn [map den HARGS DrvTop.HARGS]. unfold HeapOp.decode. rewrite (wbv_unsigned (W64 false 1%uint63)).
  change (Z.to_nat (w2Z (W64 false 1%uint63))) with 1%nat. cbn [HeapOp.decode_windows].
  rewrite !wbv_unsigned. change (w2Z wzero) with 0. change (w2Z (W64 false 140737488355328%uint63)) with 140737488355328. reflexivity.
Qed.
Lemma inZ_lohi : forall L a, DrvTop.inZ (map HeapOp.to_lohi L) a -> HeapOp.in_ivs L a.
Proof.
  intros L a H. unfold DrvTop.inZ in H. apply Exists_exists in H as (iv & Hiv & Ha). apply in_map_iff in Hiv as (v & <- & Hv).
  unfold HeapOp.in_ivs. apply Exists_exists. exists v. split; [exact Hv|]. unfold HeapOp.in_iv, HeapOp.to_lohi in *. cbn [fst snd] in Ha. lia.
Qed.
Lemma heap_fp_drv : forall E a, DrvTop.inZ (oc_fp (r_heap R) (map (den E) HARGS)) a ->
  ~ DrvTop.inZ XCLZ a /\ ~ (DrvTop.wlo WNOFF E <= a < DrvTop.wlo WNOFF E + DrvTop.WLEN).
Proof.
  intros E a H. cbn [r_heap R HEAPC oc_fp] in H.
  destruct (proj1 (HeapOp.fp_spec XCL (map (den E) HARGS) 0 (wbv wzero) [HeapOp.Win (DrvTop.wlo WNOFF E) DrvTop.WLEN 0] [] a (decode_HARGS E)) H) as (_ & NX & NW).
  split.
  - intros X. apply NX. apply inZ_lohi. exact X.
  - intros X. apply NW. unfold HeapOp.in_ws, HeapOp.in_ivs. cbn [map HeapOp.w_iv HeapOp.w_lo HeapOp.w_len]. apply Exists_cons_hd.
    unfold HeapOp.in_iv. cbn [fst snd]. exact X.
Qed.
Lemma pool_fp_drv : forall w a, DrvTop.inZ (oc_fp (r_ext R 7%uint63) [w]) a -> DrvTop.inZ PFP a.
Proof.
  intros w a H. cbn [r_ext R EXT PrimInt63.eqb POOLC oc_fp] in H. rewrite pool_fp_eq in H.
  destruct (bv_unsigned w =? 3); [inversion H |]. destruct (bv_unsigned w <? 3); [exact H | exact (pfp_park_sub a H)].
Qed.
Lemma RS_R : r_RS R = RS. Proof. reflexivity. Qed.

Lemma pool_init2 : op_init (t_st T2.T_MAIN2) POOLC [VL wzero].
Proof.
  intros E ms m tid HS _. cbn [oc_holds POOLC map den]. rewrite wbv_wzero.
  apply (PoolSnd.pool_holds_fresh SEGS FL (fun _ => True) FL8 FLB). rewrite FLz. intros i Hi.
  apply (DrvTop.image_zeros SEGS (OPS R) E (t_st T2.T_MAIN2) ms m R0_2 426352 8 HS eq_refl FIND0_2 BG0_2); try lia.
  - exact UNT_FL_2.
  - exact ZERO_FL.
Qed.
Lemma pool_initN : op_init (t_st TN.T_MAINN) POOLC [VL wzero].
Proof.
  intros E ms m tid HS _. cbn [oc_holds POOLC map den]. rewrite wbv_wzero.
  apply (PoolSnd.pool_holds_fresh SEGS FL (fun _ => True) FL8 FLB). rewrite FLz. intros i Hi.
  apply (DrvTop.image_zeros SEGS (OPS R) E (t_st TN.T_MAINN) ms m R0_N 426352 8 HS eq_refl FIND0_N BG0_N); try lia.
  - exact UNT_FL_N.
  - exact ZERO_FL.
Qed.

Lemma heap_init_at : forall MAIN r0, IMap.find 0%uint63 (s_regs MAIN) = Some r0 -> rg_bg r0 = BGImage -> s_priv MAIN = [] ->
  DrvTop.range_untouched r0 AST_LO (AST_HI - AST_LO) = true -> DrvTop.ranged (s_facts MAIN) 1%uint63 DrvTop.SPLO DrvTop.WLEN = true ->
  s_ops MAIN = [OpI 6%uint63 [VP 1%uint63 (wp 0%uint63)]] ->
  op_init MAIN HEAPC HARGS.
Proof.
  intros MAIN r0 Hr0 Hbg Hpriv HU HSP HO6 E ms m tid HS Hm. pose proof HS as HS0. rewrite Hm in HS0 |- *. clear Hm.
  cbn [oc_holds HEAPC]. unfold HeapOp.heap_holds.
  exists 0, (wbv wzero), [HeapOp.Win (DrvTop.wlo WNOFF E) DrvTop.WLEN 0], [], []. split; [exact (decode_HARGS E)|].
  pose proof (DrvTop.ranged_sound E (s_facts MAIN) 1%uint63 DrvTop.SPLO DrvTop.WLEN (so_facts _ _ _ _ _ _ HS) HSP) as SP.
  pose proof (DrvTop.wlo_val WNOFF WNOFF_val E SP) as WLO. pose proof (main_sp MAIN E ms tid HO6 HS0) as ESP.
  split; [|split].
  - rewrite wbv_wzero. apply aw_init. intros a Ha. replace a with (AST_LO + (a - AST_LO)) by lia.
    apply (DrvTop.image_bytes SEGS (OPS R) E MAIN ms _ r0 AST_LO (AST_HI - AST_LO) HS Hpriv Hr0 Hbg); try (unfold AST_LO, AST_HI in *; lia).
    + exact HU.
    + exact AST_IMAGE.
  - unfold HeapOp.windows_wf. constructor; [|constructor]. unfold HeapOp.window_wf. cbn [HeapOp.w_lo HeapOp.w_len HeapOp.w_kind HeapOp.w_iv].
    pose proof (aw_ceil0 tid). unfold DrvTop.SPLO, DrvTop.WLEN, DrvTop.WOFF, two64 in *.
    split; [lia|]. split; [lia|]. split; [lia|]. left. split; [reflexivity| lia].
  - apply cw_init.
Qed.
Lemma heap_init2 : op_init (t_st T2.T_MAIN2) HEAPC HARGS.
Proof. exact (heap_init_at (t_st T2.T_MAIN2) R0_2 FIND0_2 BG0_2 eq_refl UNT_AST_2 SP_2 eq_refl). Qed.
Lemma heap_initN : op_init (t_st TN.T_MAINN) HEAPC HARGS.
Proof. exact (heap_init_at (t_st TN.T_MAINN) R0_N FIND0_N BG0_N eq_refl UNT_AST_N SP_N eq_refl). Qed.
Lemma OPS0_F : ops0_ok (t_st T2.T_MAIN2) DF.T_DRV2. Proof. exact (ops0_of_parts _ _ OPS_F pool_init2 heap_init2). Qed.
Lemma OPS0_A : ops0_ok (t_st T2.T_MAIN2) DA.T_DRV2. Proof. exact (ops0_of_parts _ _ OPS_A pool_init2 heap_init2). Qed.
Lemma OPS0_D : ops0_ok (t_st T2.T_MAIN2) DD.T_DRV2. Proof. exact (ops0_of_parts _ _ OPS_D pool_init2 heap_init2). Qed.
Lemma OPS0_T : ops0_ok (t_st T2.T_MAIN2) DT.T_DRV2. Proof. exact (ops0_of_parts _ _ OPS_T pool_init2 heap_init2). Qed.
Lemma OPS0_N : ops0_ok (t_st TN.T_MAINN) DN.T_DRVN. Proof. exact (ops0_of_parts _ _ OPS_N pool_initN heap_initN). Qed.

Section Chain2.
Hypothesis Hargc2 : length (in_argv inp) = 2%nat.
Let INIT := InitUbs2.init_ok (OPS R) inp sp brk0 mb rnd lim xb OPS_plain_R Hva Hve Hhw Hsz Hargc2 Hen.
Lemma PB_CLF_of2 : forall b, PB b -> InitClf.PB_CLF b.
Proof. intros b ->. destruct (proj1 INIT) as (x & e & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _). exists x, e. repeat split; assumption. Qed.
Lemma argv_eq : in_argv inp = [a0; p1].
Proof.
  unfold a0, p1. pose proof Hargc2 as L. set (l := in_argv inp) in L |- *. clearbody l.
  destruct l as [|x [|y [|z l']]]; cbn in L; try discriminate L. reflexivity.
Qed.

Variable K : TSet.
Hypothesis main_leaf : tpl_realizes SEGS (OPS R) MP1 K E0 (t_st T2.T_MAIN2).

Lemma S3_sound2 : tpl_realizes SEGS (OPS R) MP1 K E0 T2.ROOT_S32.
Proof.
  intros E ms m Heb HMP HS.
  eapply (cert_sound SEGS (OPS R) S3_2.CTX S3_2.PLAN S3_2.ROOT S3_2.OBLS MP1 PB MP1_stable S3_2.WF ITAB_ok eq_refl S3_2.CHK);
    [constructor | reflexivity | exact HS | exact Heb | exact HMP |].
  split.
  - intros tid T Hf E' ms' m' Heb' HMP' HS' _. apply imap_of_find_in in Hf. destruct Hf as [Hf|[]]. injection Hf as _ <-.
    exact (main_leaf E' ms' m' ltac:(congruence) HMP' HS').
  - intros eid T Hf. exfalso. apply imap_of_find_in in Hf. exact Hf.
Qed.
Lemma settid_leaf2 : forall E ms m, eb E = eb E0 -> MP0 m -> st_ok SEGS (OPS R) E T2.T_SETTID2 ms m ->
  ecall_at SEGS (s_pc T2.T_SETTID2) -> realizes SEGS (mkCfg ms m) K.
Proof.
  intros E ms m Heb -> HS Hat.
  apply (fx_node_set_tid SEGS (OPS R) OPS_plain_R T2.T_SETTID2 T2.ROOT_S32 s3_eq2 settid_pure2 K E ms model0 HS Hat model0_tid).
  intros E' ms' m' tid HX HS' Htid ->. apply (S3_sound2 E' ms'); [destruct HX as [Hb _]; congruence | exists tid; reflexivity | exact HS'].
Qed.
Lemma LP_sound2 : tpl_realizes SEGS (OPS R) MP0 K E0 (t_st T2.HEAD_P2).
Proof.
  eapply (loop_sound SEGS (OPS R) LP_2.CTX LP_2.PLAN LP_2.OBLS 20%uint63 T2.HEAD_P2 MP0 PB K E0
            MP0_stable LP_2.WF ITAB_ok (contracts_ok_empty SEGS (OPS R) LP_2.CTX MP0 PB eq_refl) eq_refl eq_refl LP_2.CHK
            (OblsStart.obls_start_sound PB LP_2.OBLS PB_CLF_of2 start_obls_LP2) eq_refl eq_refl eq_refl).
  - intros tid T Hf Hne'. exfalso. apply imap_of_find_in in Hf. destruct Hf as [Hf|[]]. injection Hf as <- _. rewrite Uint63.eqb_refl in Hne'. discriminate.
  - intros eid T Hf E' ms' m' Heb' HMP' HS' Hat'. apply imap_of_find_in in Hf. destruct Hf as [Hf|[]]. injection Hf as _ <-.
    exact (settid_leaf2 E' ms' m' Heb' HMP' HS' Hat').
Qed.
Lemma LE_sound2 : tpl_realizes SEGS (OPS R) MP0 K E0 (t_st T2.HEAD_E2).
Proof.
  eapply (loop_sound SEGS (OPS R) LE_2.CTX LE_2.PLAN LE_2.OBLS 10%uint63 T2.HEAD_E2 MP0 PB K E0
            MP0_stable LE_2.WF ITAB_ok (contracts_ok_empty SEGS (OPS R) LE_2.CTX MP0 PB eq_refl) eq_refl eq_refl LE_2.CHK
            (OblsStart.obls_start_sound PB LE_2.OBLS PB_CLF_of2 start_obls_LE2) eq_refl eq_refl eq_refl).
  - intros tid T Hf Hne'. apply imap_of_find_in in Hf. destruct Hf as [Hf|[Hf|[]]].
    + exfalso. injection Hf as <- _. rewrite Uint63.eqb_refl in Hne'. discriminate.
    + injection Hf as _ <-. exact LP_sound2.
  - intros eid T Hf. exfalso. apply imap_of_find_in in Hf. exact Hf.
Qed.
Theorem rz_chain2 : realizes SEGS c0 K.
Proof.
  pose proof (proj2 (proj2 INIT)) as HS0. change (InitUbs2.E0 _ _ _ _ _ _ _) with E0 in HS0.
  unfold c0. change (init_config SEGS PC PH sp brk0 mb rnd lim inp) with (mkCfg (cfg_ms c0) model0).
  eapply (cert_sound SEGS (OPS R) S0_2.CTX S0_2.PLAN S0_2.ROOT S0_2.OBLS MP0 PB MP0_stable S0_2.WF ITAB_ok eq_refl S0_2.CHK);
    [constructor | reflexivity | exact (root_ops2 _ HS0) | reflexivity | reflexivity |].
  split.
  - intros tid T Hf E' ms' m' Heb' HMP' HS' _. apply imap_of_find_in in Hf. destruct Hf as [Hf|[]]. injection Hf as _ <-.
    exact (LE_sound2 E' ms' m' Heb' HMP' HS').
  - intros eid T Hf. exfalso. apply imap_of_find_in in Hf. exact Hf.
Qed.
End Chain2.

Section ChainN.
Hypothesis HargcN : length (in_argv inp) <> 2%nat.
Let INIT := InitUbsN.init_ok (OPS R) inp sp brk0 mb rnd lim xb OPS_plain_R Hva Hve Hhw Hsz HargcN Hen.
Lemma PB_CLF_ofN : forall b, PB b -> InitClf.PB_CLF b.
Proof. intros b ->. destruct (proj1 INIT) as (x & e & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _). exists x, e. repeat split; assumption. Qed.

Variable K : TSet.
Hypothesis main_leaf : tpl_realizes SEGS (OPS R) MP1 K E0 (t_st TN.T_MAINN).

Lemma S3_soundN : tpl_realizes SEGS (OPS R) MP1 K E0 TN.ROOT_S3N.
Proof.
  intros E ms m Heb HMP HS.
  eapply (cert_sound SEGS (OPS R) S3_N.CTX S3_N.PLAN S3_N.ROOT S3_N.OBLS MP1 PB MP1_stable S3_N.WF ITAB_ok eq_refl S3_N.CHK);
    [constructor | reflexivity | exact HS | exact Heb | exact HMP |].
  split.
  - intros tid T Hf E' ms' m' Heb' HMP' HS' _. apply imap_of_find_in in Hf. destruct Hf as [Hf|[]]. injection Hf as _ <-.
    exact (main_leaf E' ms' m' ltac:(congruence) HMP' HS').
  - intros eid T Hf. exfalso. apply imap_of_find_in in Hf. exact Hf.
Qed.
Lemma settid_leafN : forall E ms m, eb E = eb E0 -> MP0 m -> st_ok SEGS (OPS R) E TN.T_SETTIDN ms m ->
  ecall_at SEGS (s_pc TN.T_SETTIDN) -> realizes SEGS (mkCfg ms m) K.
Proof.
  intros E ms m Heb -> HS Hat.
  apply (fx_node_set_tid SEGS (OPS R) OPS_plain_R TN.T_SETTIDN TN.ROOT_S3N s3_eqN settid_pureN K E ms model0 HS Hat model0_tid).
  intros E' ms' m' tid HX HS' Htid ->. apply (S3_soundN E' ms'); [destruct HX as [Hb _]; congruence | exists tid; reflexivity | exact HS'].
Qed.
Lemma LP_soundN : tpl_realizes SEGS (OPS R) MP0 K E0 (t_st TN.HEAD_PN).
Proof.
  eapply (loop_sound SEGS (OPS R) LP_N.CTX LP_N.PLAN LP_N.OBLS 20%uint63 TN.HEAD_PN MP0 PB K E0
            MP0_stable LP_N.WF ITAB_ok (contracts_ok_empty SEGS (OPS R) LP_N.CTX MP0 PB eq_refl) eq_refl eq_refl LP_N.CHK
            (OblsStart.obls_start_sound PB LP_N.OBLS PB_CLF_ofN start_obls_LPN) eq_refl eq_refl eq_refl).
  - intros tid T Hf Hne'. exfalso. apply imap_of_find_in in Hf. destruct Hf as [Hf|[]]. injection Hf as <- _. rewrite Uint63.eqb_refl in Hne'. discriminate.
  - intros eid T Hf E' ms' m' Heb' HMP' HS' Hat'. apply imap_of_find_in in Hf. destruct Hf as [Hf|[]]. injection Hf as _ <-.
    exact (settid_leafN E' ms' m' Heb' HMP' HS' Hat').
Qed.
Lemma LE_soundN : tpl_realizes SEGS (OPS R) MP0 K E0 (t_st TN.HEAD_EN).
Proof.
  eapply (loop_sound SEGS (OPS R) LE_N.CTX LE_N.PLAN LE_N.OBLS 10%uint63 TN.HEAD_EN MP0 PB K E0
            MP0_stable LE_N.WF ITAB_ok (contracts_ok_empty SEGS (OPS R) LE_N.CTX MP0 PB eq_refl) eq_refl eq_refl LE_N.CHK
            (OblsStart.obls_start_sound PB LE_N.OBLS PB_CLF_ofN start_obls_LEN) eq_refl eq_refl eq_refl).
  - intros tid T Hf Hne'. apply imap_of_find_in in Hf. destruct Hf as [Hf|[Hf|[]]].
    + exfalso. injection Hf as <- _. rewrite Uint63.eqb_refl in Hne'. discriminate.
    + injection Hf as _ <-. exact LP_soundN.
  - intros eid T Hf. exfalso. apply imap_of_find_in in Hf. exact Hf.
Qed.
Theorem rz_chainN : realizes SEGS c0 K.
Proof.
  pose proof (proj2 INIT) as HS0. change (InitUbsN.E0 _ _ _ _ _ _ _) with E0 in HS0.
  unfold c0. change (init_config SEGS PC PH sp brk0 mb rnd lim inp) with (mkCfg (cfg_ms c0) model0).
  eapply (cert_sound SEGS (OPS R) S0_N.CTX S0_N.PLAN S0_N.ROOT S0_N.OBLS MP0 PB MP0_stable S0_N.WF ITAB_ok eq_refl S0_N.CHK);
    [constructor | reflexivity | exact (root_opsN _ HS0) | reflexivity | reflexivity |].
  split.
  - intros tid T Hf E' ms' m' Heb' HMP' HS' _. apply imap_of_find_in in Hf. destruct Hf as [Hf|[]]. injection Hf as _ <-.
    exact (LE_soundN E' ms' m' Heb' HMP' HS').
  - intros eid T Hf. exfalso. apply imap_of_find_in in Hf. exact Hf.
Qed.
End ChainN.

Definition ext_ok (TAB : IMap.t contract) (mine : list int) : Prop :=
  forall cid ct, IMap.find cid TAB = Some ct -> ~ In cid mine -> contract_sound SEGS (OPS R) MP PB ct.
Lemma stage_writable : Mem.abs_writable SEGS RS 65536 = true. Proof. vm_compute. reflexivity. Qed.
Lemma RS_user : RS + 2 ^ 40 <= 2 ^ 47. Proof. unfold RS. lia. Qed.
Lemma ecall_cp : ecall_at SEGS 335240%uint63. Proof. apply (ecall_atb_sound SEGS). vm_compute. reflexivity. Qed.
Lemma ecall_ioctl : ecall_at SEGS 312896%uint63. Proof. apply (ecall_atb_sound SEGS). vm_compute. reflexivity. Qed.
Lemma PB_arg1_R : forall b, PB b -> b 3%uint63 = p1 ++ [Z_to_bv 8 0] /\ b 10%uint63 = Z_to_le_bytes 8 (Z.of_nat (length p1) + 1).
Proof. intros b ->. split; reflexivity. Qed.
Lemma PB_size_R : forall b, PB b -> b 11%uint63 = Z_to_le_bytes 8 (fsize file). Proof. intros b ->. reflexivity. Qed.

Lemma TABF_21 : IMap.find 21%uint63 DF.CONTRACTS = Some (CtrS.c_read_file 360729%uint63 335240%uint63). Proof. reflexivity. Qed.
Lemma TABF_23 : IMap.find 23%uint63 DF.CONTRACTS = Some (CtrS.c_close 335240%uint63). Proof. reflexivity. Qed.
Lemma TABF_24 : IMap.find 24%uint63 DF.CONTRACTS = Some (CtrS.c_ioctl 312896%uint63). Proof. reflexivity. Qed.
Lemma TABD_22 : IMap.find 22%uint63 DD.CONTRACTS = Some (CtrS.c_read_dir 360729%uint63 335240%uint63). Proof. reflexivity. Qed.
Lemma TABA_26 : IMap.find 26%uint63 DA.CONTRACTS = Some (CtrS.c_open_absent 335240%uint63). Proof. reflexivity. Qed.
Lemma TABT_27 : IMap.find 27%uint63 DT.CONTRACTS = Some (CtrS.c_open_toolong 335240%uint63). Proof. reflexivity. Qed.
Lemma ctab_of : forall (TAB : IMap.t contract) (mine : list int),
  ext_ok TAB mine -> (forall cid ct, In cid mine -> IMap.find cid TAB = Some ct -> contract_sound SEGS (OPS R) MP PB ct) ->
  ctab_ok SEGS R TAB.
Proof.
  intros TAB mine HE HM cid ct Hf. destruct (in_dec (fun x y => ltac:(destruct (Uint63.eqs x y); [left; assumption | right; assumption])) cid mine) as [Hin|Hn].
  - exact (HM cid ct Hin Hf).
  - exact (HE cid ct Hf Hn).
Qed.

Lemma ctab_F : fs_lookup fs0 p1 = Some file -> ext_ok DF.CONTRACTS [21; 23; 24]%uint63 -> ctab_ok SEGS R DF.CONTRACTS.
Proof.
  intros Hfile HE. apply (ctab_of _ _ HE). intros cid ct Hin Hf.
  destruct Hin as [<-|[<-|[<-|[]]]]; [rewrite TABF_21 in Hf | rewrite TABF_23 in Hf | rewrite TABF_24 in Hf]; injection Hf as <-.
  - eapply (CtrSys.read_file_sound SEGS HEAPC EXT p1 file RS); try eassumption; try exact MP_fds; try exact TM_fds; try exact TM_cov1; try exact MP_stable; try exact heap_fds; try exact heap_fp_stage;
      try exact ext_fds; try exact ext_fp_stage; try exact RS_user; try exact PB_size_R; try exact stage_writable; try exact ecall_cp; try reflexivity.

    intros m Hm. rewrite (MP_fs m Hm). exact Hfile.
  - eapply (CtrSys.close_sound SEGS HEAPC EXT p1 file RS); try eassumption; try exact MP_fds; try exact TM_fds; try exact TM_cov1; try exact MP_stable; try exact heap_fds; try exact ext_fds; try exact ecall_cp.
  - eapply (CtrSys.ioctl_sound SEGS HEAPC EXT p1 file RS); try eassumption; try exact MP_fds; try exact TM_fds; try exact TM_cov1; try exact MP_stable; try exact heap_fds; try exact ext_fds; try exact ecall_ioctl.
Qed.

Lemma ctab_D : path_is_dirref p1 = true -> ext_ok DD.CONTRACTS [22]%uint63 -> ctab_ok SEGS R DD.CONTRACTS.
Proof.
  intros Hdir HE. apply (ctab_of _ _ HE). intros cid ct Hin Hf.
  destruct Hin as [<-|[]]. rewrite TABD_22 in Hf. injection Hf as <-.
  eapply (CtrSys.read_dir_sound SEGS HEAPC EXT p1 file RS); try eassumption; try exact MP_fds; try exact TM_fds; try exact TM_cov1; try exact MP_stable; try exact heap_fds; try exact heap_fp_stage;
    try exact ext_fds; try exact ext_fp_stage; try exact RS_user; try exact ecall_cp; try reflexivity.
Qed.

Lemma ctab_A : (length p1 < 4096)%nat -> (p1 = [] \/ (path_is_dirref p1 = false /\ fs_lookup fs0 p1 = None)) ->
  ext_ok DA.CONTRACTS [26]%uint63 -> ctab_ok SEGS R DA.CONTRACTS.
Proof.
  intros Hshort Hcase HE. apply (ctab_of _ _ HE). intros cid ct Hin Hf.
  destruct Hin as [<-|[]]. rewrite TABA_26 in Hf. injection Hf as <-.
  eapply (CtrSys.open_absent_sound SEGS HEAPC EXT p1 file RS); try eassumption; try exact MP_fds; try exact TM_fds; try exact TM_cov1; try exact MP_stable; try exact heap_fds; try exact ext_fds;
    try exact PB_arg1_R; try exact p1_nz; try exact p1_len; try exact ecall_cp.
  pose proof p1_noslash as [Hs _]. split; [exact Hs|]. split; [| split; [exact Hshort|]].
  - destruct Hcase as [-> | [Hd _]]; [reflexivity | exact Hd].
  - destruct Hcase as [-> | [_ Hl]]; [left; reflexivity | right]. intros m Hm. rewrite (MP_fs m Hm). exact Hl.
Qed.

Lemma ctab_T : (4096 <= length p1)%nat -> ext_ok DT.CONTRACTS [27]%uint63 -> ctab_ok SEGS R DT.CONTRACTS.
Proof.
  intros Hlong HE. apply (ctab_of _ _ HE). intros cid ct Hin Hf.
  destruct Hin as [<-|[]]. rewrite TABT_27 in Hf. injection Hf as <-.
  eapply (CtrSys.open_toolong_sound SEGS HEAPC EXT p1 file RS); try eassumption; try exact MP_fds; try exact TM_fds; try exact TM_cov1; try exact MP_stable; try exact heap_fds; try exact ext_fds;
    try exact PB_arg1_R; try exact p1_nz; try exact p1_len; try exact Hlong; try exact ecall_cp.
Qed.

Lemma ctab_N : ext_ok DN.CONTRACTS [] -> ctab_ok SEGS R DN.CONTRACTS.
Proof. intros HE. apply (ctab_of _ _ HE). intros cid ct []. Qed.

Lemma bridge2 : forall (D : sstate) (KS : shp), s_ops D = DRVOPS ->
  DrvTop.drv_chk SEGS BL HULL XCLZ PFP RS REMAT 0%uint63 (t_st T2.T_MAIN2) D = true -> ops0_ok (t_st T2.T_MAIN2) D ->
  NODE SEGS R D (DR R KS) -> tpl_realizes SEGS (OPS R) MP1 (DR R KS) E0 (t_st T2.T_MAIN2).
Proof.
  intros D KS HO HC Hops HN E ms m Heb [tid ->] HS.
  destruct (DrvTop.drv_bridgeE SEGS R BL HBL WNOFF WNOFF_val HULL XCLZ PFP heap_fp_drv pool_fp_drv RS RS_R REMAT 0%uint63 (t_st T2.T_MAIN2) D E ms _
              (VL wzero) (VL wzero) (VL wzero) HO HC HS Heb (or_introl main2_resv) (Hops E ms _ tid HS eq_refl)) as (E' & Heb' & HS').
  apply (HN E' ms (with_tid tid model0)); [cbn [r_PB R]; unfold PB; congruence | reflexivity | exact HS'].
Qed.
Lemma bridgeN : forall (D : sstate) (KS : shp), s_ops D = DRVOPS ->
  DrvTop.drv_chk SEGS BL HULL XCLZ PFP RS REMAT 0%uint63 (t_st TN.T_MAINN) D = true -> ops0_ok (t_st TN.T_MAINN) D ->
  NODE SEGS R D (DR R KS) -> tpl_realizes SEGS (OPS R) MP1 (DR R KS) E0 (t_st TN.T_MAINN).
Proof.
  intros D KS HO HC Hops HN E ms m Heb [tid ->] HS.
  destruct (DrvTop.drv_bridgeE SEGS R BL HBL WNOFF WNOFF_val HULL XCLZ PFP heap_fp_drv pool_fp_drv RS RS_R REMAT 0%uint63 (t_st TN.T_MAINN) D E ms _
              (VL wzero) (VL wzero) (VL wzero) HO HC HS Heb (or_introl mainN_resv) (Hops E ms _ tid HS eq_refl)) as (E' & Heb' & HS').
  apply (HN E' ms (with_tid tid model0)); [cbn [r_PB R]; unfold PB; congruence | reflexivity | exact HS'].
Qed.

Record FamHypsF : Prop := FHF {
  fhf_ext : ext_ok DF.CONTRACTS [21; 23; 24]%uint63;
  fhf_mf : mnofork_ok SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63)))));
  fhf_lib8 : lib_ok SEGS R (t_st DF.T_LIBGEN_r8) (t_st DF.R_LIBGEN_r8_RET);
  fhf_lib9 : lib_ok SEGS R (t_st DF.T_LIBGEN_r9) (t_st DF.R_LIBGEN_r9_RET) }.
Theorem rz_file : length (in_argv inp) = 2%nat -> fs_lookup fs0 p1 = Some file -> path_is_dirref p1 = false -> p1 <> [] ->
  (length p1 < 4096)%nat -> FamHypsF -> realizes SEGS c0 (K inp).
Proof.
  intros Hargc2 Hfile Hndir Hne Hshort [HE HMF HL8 HL9]. pose proof (ctab_F Hfile HE) as HC.
  pose proof OPS0_F as HO.
  assert (HD : HF.hyps R).
  { refine (HF.Hyps R HC file_pb_R _ _ HMF HL8 HL9).
    - intros m Hm. cbn [r_p1 r_file R]. rewrite (MP_fs m Hm). exact Hfile.
    - cbn [r_p1 R]. pose proof p1_noslash as [Hs _]. repeat split; assumption. }
  assert (HK : K inp = DR R (FILE file)).
  { unfold K. rewrite (argv_eq Hargc2). unfold DR, K2. cbn [r_fs r_a0 r_p1 R].
    replace (4096 <=? Z.of_nat (length p1)) with false by (symmetry; apply Z.leb_gt; lia).
    replace (path_eqb p1 []) with false by (destruct p1; [exfalso; apply Hne; reflexivity | reflexivity]).
    rewrite Hndir. fold fs0. rewrite Hfile. reflexivity. }
  rewrite HK. apply (rz_chain2 Hargc2). apply (bridge2 DF.T_DRV2 _ OPS_F DRV_CHK_F HO). exact (RF.N_T_DRV2 R HD).
Qed.

Record FamHypsD : Prop := FHD {
  fhd_ext : ext_ok DD.CONTRACTS [22]%uint63;
  fhd_mf : mnofork_ok SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) }.
Theorem rz_dir : length (in_argv inp) = 2%nat -> path_is_dirref p1 = true -> FamHypsD -> realizes SEGS c0 (K inp).
Proof.
  intros Hargc2 Hdir [HE HMF]. pose proof (ctab_D Hdir HE) as HC.
  pose proof OPS0_D as HO.
  assert (HDG : HD.hyps R) by (exact (HD.Hyps R HC Hdir HMF)).
  assert (Hp : p1 = [Z_to_bv 8 46]).
  { destruct p1_noslash as [_ Hdd]. unfold path_is_dirref in Hdir. apply orb_prop in Hdir. destruct Hdir as [H1|H2].
    - apply path_eqb_eq in H1. exact H1.
    - rewrite H2 in Hdd. discriminate Hdd. }
  assert (HK : K inp = DR R DIR).
  { unfold K. rewrite (argv_eq Hargc2). unfold DR, K2. cbn [r_fs r_a0 r_p1 R].
    replace (4096 <=? Z.of_nat (length p1)) with false by (rewrite Hp; reflexivity).
    replace (path_eqb p1 []) with false by (rewrite Hp; reflexivity). rewrite Hdir. reflexivity. }
  rewrite HK. apply (rz_chain2 Hargc2). apply (bridge2 DD.T_DRV2 _ OPS_D DRV_CHK_D HO). exact (RD.N_T_DRV2 R HDG).
Qed.

Record FamHypsA : Prop := FHA {
  fha_ext : ext_ok DA.CONTRACTS [26]%uint63 }.
Theorem rz_absent : length (in_argv inp) = 2%nat -> (length p1 < 4096)%nat -> (p1 = [] \/ (path_is_dirref p1 = false /\ fs_lookup fs0 p1 = None)) ->
  FamHypsA -> realizes SEGS c0 (K inp).
Proof.
  intros Hargc2 Hshort Hcase [HE]. pose proof (ctab_A Hshort Hcase HE) as HC.
  pose proof OPS0_A as HO. assert (HDG : HA.hyps R) by (exact (HA.Hyps R HC)).
  assert (HK : K inp = DR R OPENFAIL).
  { unfold K. rewrite (argv_eq Hargc2). unfold DR, K2. cbn [r_fs r_a0 r_p1 R].
    replace (4096 <=? Z.of_nat (length p1)) with false by (symmetry; apply Z.leb_gt; lia).
    destruct Hcase as [-> | [Hnd Hno]]; [reflexivity|].
    destruct (path_eqb p1 []); [reflexivity|]. rewrite Hnd. fold fs0. rewrite Hno. reflexivity. }
  rewrite HK. apply (rz_chain2 Hargc2). apply (bridge2 DA.T_DRV2 _ OPS_A DRV_CHK_A HO). exact (RA.N_T_DRV2 R HDG).
Qed.

Record FamHypsT : Prop := FHT {
  fht_ext : ext_ok DT.CONTRACTS [27]%uint63 }.
Theorem rz_toolong : length (in_argv inp) = 2%nat -> (4096 <= length p1)%nat -> FamHypsT -> realizes SEGS c0 (K inp).
Proof.
  intros Hargc2 Hlong [HE]. pose proof (ctab_T Hlong HE) as HC.
  pose proof OPS0_T as HO. assert (HDG : HT.hyps R) by (exact (HT.Hyps R HC)).
  assert (HK : K inp = DR R OPENFAIL).
  { unfold K. rewrite (argv_eq Hargc2). unfold DR, K2. cbn [r_fs r_a0 r_p1 R].
    replace (4096 <=? Z.of_nat (length p1)) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  rewrite HK. apply (rz_chain2 Hargc2). apply (bridge2 DT.T_DRV2 _ OPS_T DRV_CHK_T HO). exact (RT.N_T_DRV2 R HDG).
Qed.

Record FamHypsN : Prop := FHN {
  fhn_ext : ext_ok DN.CONTRACTS [] }.
Theorem rz_usage : length (in_argv inp) <> 2%nat -> FamHypsN -> realizes SEGS c0 (K inp).
Proof.
  intros HargcN [HE]. pose proof (ctab_N HE) as HC.
  pose proof OPS0_N as HO. assert (HDG : HN.hyps R) by (exact (HN.Hyps R HC)).
  assert (HK : K inp = DR R USAGE).
  { unfold K, DR. cbn [r_fs r_a0 r_p1 R]. unfold a0, p1. pose proof HargcN as L. set (l := in_argv inp) in L |- *. clearbody l.
    destruct l as [|x [|y [|z l']]]; cbn [hd tl]; try reflexivity. exfalso. apply L. reflexivity. }
  rewrite HK. apply (rz_chainN HargcN). apply (bridgeN DN.T_DRVN _ OPS_N DRV_CHK_N HO). exact (RN.N_T_DRVN R HDG).
Qed.

Record AllHyps : Prop := AH { ah_f : FamHypsF; ah_d : FamHypsD; ah_a : FamHypsA; ah_t : FamHypsT; ah_n : FamHypsN }.
Theorem rz : AllHyps -> realizes SEGS c0 (K inp).
Proof.
  intros [HFm HDm HAm HTm HNm].
  destruct (Nat.eq_dec (length (in_argv inp)) 2) as [H2 | HN2]; [| exact (rz_usage HN2 HNm)].
  destruct (Nat.lt_ge_cases (length p1) 4096) as [Hs | Hl]; [| exact (rz_toolong H2 Hl HTm)].
  destruct (list_eq_dec (@bv_eq_dec 8) p1 []) as [Hnil | Hne]; [exact (rz_absent H2 Hs (or_introl Hnil) HAm)|].
  destruct (path_is_dirref p1) eqn:Hd; [exact (rz_dir H2 Hd HDm)|].
  destruct (fs_lookup fs0 p1) as [f|] eqn:Hl.
  - apply (rz_file H2); try assumption. unfold file. rewrite Hl. reflexivity.
  - exact (rz_absent H2 Hs (or_intror (conj Hd Hl)) HAm).
Qed.

End TOP.
End RunUbs.
