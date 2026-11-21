(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Glue/RunSrc.v: the argc <> 2 branch (rz_usage) restated over BudgetWit.Rzb.rzb *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's caps and far-end reader as section hypotheses; the start environment by InitLib.E0 of the launch's ProcInput; the run's CONFIG_RSEQ flag rflag, with the loops' measure and plain-cut checks proved at each value; the run predicate's far-end channel reader TM_rdr passed to DRun; the set_tid, root and pool facts for both CONFIG_RSEQ copies of the certificates; HBL bounds the string area, now SI.strarea of the ProcInput, by the stack block's geometry under the launch, as Glue/RunSrc.v; FX's region names imported by their full path, as Glue/RunSrc.v; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence FinInput.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgSrc ItabSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Import Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2 Require T_Src2 C_S0 C_LE C_LP C_S3.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.SrcN Require T_SrcN C_S0 C_LE C_LP C_S3.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2F Require T_Src2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2A Require T_Src2A.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2D Require T_Src2D.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2T Require T_Src2T.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.SrcNU Require T_SrcNU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound StackInit InitLib InitClf RootSrc2 InitSrc2 RootSrcN InitSrcN OblsLib OblsClf
  Ops SysSpec CtrSys StdioWrite DrvShape DrvRoot DrvLib DrvEdges OblsStart DrvTop.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Src2F_9 Src2A_5 Src2D_10 Src2T_5 SrcNU_6 Src2F_1 Src2A_1 Src2D_1 Src2T_1 SrcNU_1.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require RunSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit Require Import Rzb PlanSoundB CertSoundB NodesB StdioWriteB DrvLibB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit.Run Require SrcNUB_6 SrcNUB_1.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS SW DrvShape DrvRoot DrvLib.
(* the short name [Mem] above can resolve to another loaded [Mem] library; [region] and its
   constructors are FX's (as Glue/RunSrc.v) *)
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem.
Import PlanSB CertSB FXNB SWB DrvLibB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module T2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2.T_Src2.
Module S0_2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2.C_S0.
Module LE_2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2.C_LE.
Module LP_2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2.C_LP.
Module S3_2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2.C_S3.
Module TN := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.SrcN.T_SrcN.
Module S0_N := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.SrcN.C_S0.
Module LE_N := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.SrcN.C_LE.
Module LP_N := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.SrcN.C_LP.
Module S3_N := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.SrcN.C_S3.
Module DF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2F.T_Src2F.
Module DA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2A.T_Src2A.
Module DD := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2D.T_Src2D.
Module DT := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2T.T_Src2T.
Module DN := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.SrcNU.T_SrcNU.
Module RF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Src2F_9.
Module RA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Src2A_5.
Module RD := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Src2D_10.
Module RT := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Src2T_5.
Module RN := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit.Run.SrcNUB_6.
Module HF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Src2F_1.
Module HA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Src2A_1.
Module HD := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Src2D_1.
Module HT := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run.Src2T_1.
Module HN := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit.Run.SrcNUB_1.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.RunSrc.RunSrc.

Module RunSrcB.
Section TOP.

Variable inp : ProcInput.
Variables (sp brk0 mb : word) (rnd : EntryDraw) (lim : Z).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hhw : valid_hwcap (in_hwcap inp).
Hypothesis Hsz : in_va_size inp = Sv48.
(* the launch's caps, for the start state's window below sp (ALib/InitMem.v's stack_window_lo_valid) *)
Hypothesis Hvl : valid_launch inp.
(* the launch's far-end reader ([Run.valid_input]): the start model's [mfacts] reads it *)
Hypothesis Hrdr : in_channel_reader inp = true.
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
Definition E0 : env := InitLib.E0 PC PH sp mb inp rnd xb.
(* the run's CONFIG_RSEQ value: the start-up chain and the main phase's start state are this value's *)
Definition rflag : bool := la_rseq (SI.LA sp mb inp).
(* the loops' measure and plain-cut checks at each CONFIG_RSEQ value (they do not compute at the run's own value;
   [rb] stays the memory read) *)
Lemma vbB_LEN : forall b, vars_below (s_next (t_st (S0_N.HEAD_EN b))) (t_measure (S0_N.HEAD_EN b)) = true. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma vbB_LPN : forall b, vars_below (s_next (t_st (LE_N.HEAD_PN b))) (t_measure (LE_N.HEAD_PN b)) = true. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma upcB_LEN : forall b, uses_plain_cut (LE_N.PLAN b) 10%uint63 = false. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma upcB_LPN : forall b, uses_plain_cut (LP_N.PLAN b) 20%uint63 = false. Proof. intros [|]; vm_compute; reflexivity. Qed.
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
(* LPS 08b1429: the run predicate's far-end channel reader, as Glue/RunSrc.v's [TM_rdr] *)
Lemma TM_rdr : forall m, MP m -> op_minv (CtrSys.OPS HEAPC EXT p1 file RS RS_range TM) m -> m_channel_reader m = true.
Proof. intros m _ H. exact (mf_reader _ (plain_mf _ _ TM_plain H)). Qed.

Definition R : drun :=
  DRun HEAPC EXT a0 p1 file fs0 RS RS_range MP PB MP_fs MP_fds MP_stable heap_fds heap_fp_stage ext_fds ext_fp_stage
       (fun b (H : PB b) => match eq_sym H in (_ = e) return (e 1%uint63 = cstr a0 /\ e 9%uint63 = LE8 (Z.of_nat (length a0) + 1)) with eq_refl => conj eb1 eb9 end)
       (fun b (H : PB b) => match eq_sym H in (_ = e) return (e 3%uint63 = cstr p1 /\ e 10%uint63 = LE8 (Z.of_nat (length p1) + 1)) with eq_refl => conj eb3 eb10 end)
       a0_len p1_len p1_nz TM TM_fds TM_cov1 TM_rdr.
Lemma OPS_R : OPS R = CtrSys.OPS HEAPC EXT p1 file RS RS_range TM. Proof. reflexivity. Qed.

Lemma OPS_plain_R : plain_table (OPS R). Proof. exact TM_plain. Qed.
Lemma file_pb_R : file_pb R. Proof. intros b ->. cbn [r_file R]. repeat split; reflexivity. Qed.
Lemma HBL : forall E j c, r_PB R (eb E) -> In (j, c) BL -> bv_unsigned (den E (VBlob false j (VL wzero) 8%uint63)) <= c.
Proof.
  intros E j c HPB [H|[]]. injection H as <- <-. cbn [r_PB R] in HPB. unfold PB in HPB.
  assert (E15 : eb E 15%uint63 = LE8 (Z.of_nat (length (SI.strarea inp)))) by (rewrite HPB; reflexivity).
  pose proof (proj1 (valid_entry_sv48 _ _ _ Hsz) Hen) as (Hsp' & _ & _ & _ & Hlau).
  pose proof (SI.geom sp brk0 mb inp rnd Hlau) as G. pose proof (SI.top_hi sp brk0 mb inp rnd Hlau) as T.
  pose proof (SI.length_strarea inp) as L. pose proof (SI.SP_lo sp Hsp') as LO.
  change wzero with (wp 0%uint63). rewrite (OL.den_param8_u E 15%uint63 _ E15); unfold SI.SP in *; lia.
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
Lemma settid_pureN : forall b E mem m tid, ops_hold (OPS R) E (s_ops (LP_N.T_SETTIDN b)) mem m -> ops_hold (OPS R) E (s_ops (LP_N.T_SETTIDN b)) mem (with_tid tid m).
Proof. intros [|] E mem m tid; exact (splink_tid E mem m tid (wp 0%uint63)). Qed.

Lemma main_sp : forall MAIN E ms tid, s_ops MAIN = [OpI 6%uint63 [VP 1%uint63 (wp 0%uint63)]] ->
  st_ok SEGS (OPS R) E MAIN ms (with_tid tid model0) -> bv_unsigned (ev E 1%uint63) = bv_unsigned sp.
Proof.
  intros MAIN E ms tid HO HS. pose proof (so_ops _ _ _ _ _ _ HS) as H. rewrite HO in H. apply splink_iff in H.
  rewrite (DrvTop.den_VP_zero E 1%uint63 (wp 0%uint63) eq_refl) in H. exact H.
Qed.

Lemma root_opsN : forall b ms, st_ok SEGS (OPS R) E0 (ROOT_SrcN b) ms model0 -> st_ok SEGS (OPS R) E0 (S0_N.ROOT b) ms model0.
Proof.
  intros b ms HS. apply (with_ops_priv_sound SEGS R E0 (ROOT_SrcN b) RootSrcN.ROOT_OPS RootSrcN.ROOT_PRIV (S0_N.ROOT b) ms model0 HS).
  - rewrite (InitSrcN.root_eq b). reflexivity.
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

Lemma pool_initN : forall b, op_init (t_st (S3_N.T_MAINN b)) POOLC [VL wzero].
Proof.
  intros b E ms m tid HS _. cbn [oc_holds POOLC map den]. rewrite wbv_wzero.
  apply (PoolSnd.pool_holds_fresh SEGS FL (fun _ => True) FL8 FLB). rewrite FLz. intros i Hi.
  apply (DrvTop.image_zeros SEGS (OPS R) E (t_st (S3_N.T_MAINN b)) ms m (R0_N b) 420208 8 HS (PRIV_N b) (FIND0_N b) (BG0_N b)); try lia.
  - exact (UNT_FL_N b).
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
Lemma heap_initN : forall b, op_init (t_st (S3_N.T_MAINN b)) HEAPC HARGS.
Proof. intros b. exact (heap_init_at (t_st (S3_N.T_MAINN b)) (R0_N b) (FIND0_N b) (BG0_N b) (PRIV_N b) (UNT_AST_N b) (SP_N b) (OPS6_N b)). Qed.
Lemma OPS0_N : forall b, ops0_ok (t_st (S3_N.T_MAINN b)) DN.T_DRVN. Proof. intros b. exact (ops0_of_parts _ _ OPS_N (pool_initN b) (heap_initN b)). Qed.

Section ChainN.
Hypothesis HargcN : length (in_argv inp) <> 2%nat.
Let INIT := InitSrcN.init_ok (OPS R) inp sp brk0 mb rnd lim xb OPS_plain_R Hva Hve Hhw Hsz Hvl Hrdr HargcN Hen.
Lemma PB_CLF_ofN : forall b, PB b -> InitClf.PB_CLF b.
Proof. intros b ->. destruct (proj1 INIT) as (x & e & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _). exists x, e. repeat split; assumption. Qed.

Variable K : TSet.
Hypothesis main_leaf : tpl_rzb SEGS (OPS R) MP1 K E0 (t_st (S3_N.T_MAINN rflag)).

Lemma S3_soundN_b : tpl_rzb SEGS (OPS R) MP1 K E0 (S3_N.ROOT rflag).
Proof.
  intros E ms m Heb HMP HS.
  eapply (cert_sound_b SEGS (OPS R) (S3_N.CTX rflag) (S3_N.PLAN rflag) (S3_N.ROOT rflag) S3_N.OBLS MP1 PB MP1_stable (S3_N.WF rflag) ITAB_ok eq_refl (S3_N.CHK rflag));
    [constructor | reflexivity | exact HS | exact Heb | exact HMP |].
  split.
  - intros tid T Hf E' ms' m' Heb' HMP' HS' _. apply imap_of_find_in in Hf. destruct Hf as [Hf|[]]. injection Hf as _ <-.
    exact (main_leaf E' ms' m' ltac:(congruence) HMP' HS').
  - intros eid T Hf. exfalso. apply imap_of_find_in in Hf. exact Hf.
Qed.
Lemma settid_leafN_b : forall E ms m, eb E = eb E0 -> MP0 m -> st_ok SEGS (OPS R) E (LP_N.T_SETTIDN rflag) ms m ->
  ecall_at SEGS (s_pc (LP_N.T_SETTIDN rflag)) -> rzb SEGS (mkCfg ms m) K.
Proof.
  intros E ms m Heb -> HS Hat.
  apply (fx_node_set_tid_b SEGS (OPS R) OPS_plain_R (LP_N.T_SETTIDN rflag) (S3_N.ROOT rflag) (s3_eqN rflag) (settid_pureN rflag) K E ms model0 HS Hat model0_tid).
  intros E' ms' m' tid HX HS' Htid ->. apply (S3_soundN_b E' ms'); [destruct HX as [Hb _]; congruence | exists tid; reflexivity | exact HS'].
Qed.
Lemma LP_soundN_b : tpl_rzb SEGS (OPS R) MP0 K E0 (t_st (LE_N.HEAD_PN rflag)).
Proof.
  eapply (loop_sound_b SEGS (OPS R) (LP_N.CTX rflag) (LP_N.PLAN rflag) (LP_N.OBLS rflag) 20%uint63 (LE_N.HEAD_PN rflag) MP0 PB K E0
            MP0_stable (LP_N.WF rflag) ITAB_ok (contracts_ok_empty_b SEGS (OPS R) (LP_N.CTX rflag) MP0 PB eq_refl) eq_refl eq_refl (LP_N.CHK rflag)
            (OblsStart.obls_start_sound PB (LP_N.OBLS rflag) PB_CLF_ofN (start_obls_LPN rflag)) (vbB_LPN rflag) (upcB_LPN rflag) eq_refl).
  - intros tid T Hf Hne'. exfalso. apply imap_of_find_in in Hf. destruct Hf as [Hf|[]]. injection Hf as <- _. rewrite Uint63.eqb_refl in Hne'. discriminate.
  - intros eid T Hf E' ms' m' Heb' HMP' HS' Hat'. apply imap_of_find_in in Hf. destruct Hf as [Hf|[]]. injection Hf as _ <-.
    exact (settid_leafN_b E' ms' m' Heb' HMP' HS' Hat').
Qed.
Lemma LE_soundN_b : tpl_rzb SEGS (OPS R) MP0 K E0 (t_st (S0_N.HEAD_EN rflag)).
Proof.
  eapply (loop_sound_b SEGS (OPS R) (LE_N.CTX rflag) (LE_N.PLAN rflag) (LE_N.OBLS rflag) 10%uint63 (S0_N.HEAD_EN rflag) MP0 PB K E0
            MP0_stable (LE_N.WF rflag) ITAB_ok (contracts_ok_empty_b SEGS (OPS R) (LE_N.CTX rflag) MP0 PB eq_refl) eq_refl eq_refl (LE_N.CHK rflag)
            (OblsStart.obls_start_sound PB (LE_N.OBLS rflag) PB_CLF_ofN (start_obls_LEN rflag)) (vbB_LEN rflag) (upcB_LEN rflag) eq_refl).
  - intros tid T Hf Hne'. apply imap_of_find_in in Hf. destruct Hf as [Hf|[Hf|[]]].
    + exfalso. injection Hf as <- _. rewrite Uint63.eqb_refl in Hne'. discriminate.
    + injection Hf as _ <-. exact LP_soundN_b.
  - intros eid T Hf. exfalso. apply imap_of_find_in in Hf. exact Hf.
Qed.
Theorem rzb_chainN : rzb SEGS c0 K.
Proof.
  pose proof (proj2 INIT) as HS0. change (InitSrcN.E0 _ _ _ _ _) with E0 in HS0.
  unfold c0. change (init_config SEGS PC PH sp brk0 mb rnd lim inp) with (mkCfg (cfg_ms c0) model0).
  eapply (cert_sound_b SEGS (OPS R) (S0_N.CTX rflag) (S0_N.PLAN rflag) (S0_N.ROOT rflag) S0_N.OBLS MP0 PB MP0_stable (S0_N.WF rflag) ITAB_ok eq_refl (S0_N.CHK rflag));
    [constructor | reflexivity | exact (root_opsN rflag _ HS0) | reflexivity | reflexivity |].
  split.
  - intros tid T Hf E' ms' m' Heb' HMP' HS' _. apply imap_of_find_in in Hf. destruct Hf as [Hf|[]]. injection Hf as _ <-.
    exact (LE_soundN_b E' ms' m' Heb' HMP' HS').
  - intros eid T Hf. exfalso. apply imap_of_find_in in Hf. exact Hf.
Qed.
End ChainN.

Definition ext_ok_b (TAB : IMap.t contract) (mine : list int) : Prop :=
  forall cid ct, IMap.find cid TAB = Some ct -> ~ In cid mine -> contract_sound_b SEGS (OPS R) MP PB ct.
Lemma stage_writable : Mem.abs_writable SEGS RS 65536 = true. Proof. vm_compute. reflexivity. Qed.
Lemma RS_user : RS + 2 ^ 40 <= 2 ^ 47. Proof. unfold RS. lia. Qed.
Lemma ecall_cp : ecall_at SEGS 329092%uint63. Proof. apply (ecall_atb_sound SEGS). vm_compute. reflexivity. Qed.
Lemma ecall_ioctl : ecall_at SEGS 306748%uint63. Proof. apply (ecall_atb_sound SEGS). vm_compute. reflexivity. Qed.
Lemma PB_arg1_R : forall b, PB b -> b 3%uint63 = p1 ++ [Z_to_bv 8 0] /\ b 10%uint63 = Z_to_le_bytes 8 (Z.of_nat (length p1) + 1).
Proof. intros b ->. split; reflexivity. Qed.
Lemma PB_size_R : forall b, PB b -> b 11%uint63 = Z_to_le_bytes 8 (fsize file). Proof. intros b ->. reflexivity. Qed.

Lemma TABF_21 : IMap.find 21%uint63 DF.CONTRACTS = Some (CtrS.c_read_file 354585%uint63 329092%uint63). Proof. reflexivity. Qed.
Lemma TABF_23 : IMap.find 23%uint63 DF.CONTRACTS = Some (CtrS.c_close 329092%uint63). Proof. reflexivity. Qed.
Lemma TABF_24 : IMap.find 24%uint63 DF.CONTRACTS = Some (CtrS.c_ioctl 306748%uint63). Proof. reflexivity. Qed.
Lemma TABD_22 : IMap.find 22%uint63 DD.CONTRACTS = Some (CtrS.c_read_dir 354585%uint63 329092%uint63). Proof. reflexivity. Qed.
Lemma TABA_26 : IMap.find 26%uint63 DA.CONTRACTS = Some (CtrS.c_open_absent 329092%uint63). Proof. reflexivity. Qed.
Lemma TABT_27 : IMap.find 27%uint63 DT.CONTRACTS = Some (CtrS.c_open_toolong 329092%uint63). Proof. reflexivity. Qed.
Lemma ctab_of_b : forall (TAB : IMap.t contract) (mine : list int),
  ext_ok_b TAB mine -> (forall cid ct, In cid mine -> IMap.find cid TAB = Some ct -> contract_sound_b SEGS (OPS R) MP PB ct) ->
  ctab_ok_b SEGS R TAB.
Proof.
  intros TAB mine HE HM cid ct Hf. destruct (in_dec (fun x y => ltac:(destruct (Uint63.eqs x y); [left; assumption | right; assumption])) cid mine) as [Hin|Hn].
  - exact (HM cid ct Hin Hf).
  - exact (HE cid ct Hf Hn).
Qed.

Lemma ctab_N_b : ext_ok_b DN.CONTRACTS [] -> ctab_ok_b SEGS R DN.CONTRACTS.
Proof. intros HE. apply (ctab_of_b _ _ HE). intros cid ct []. Qed.

Lemma bridgeN_b : forall b (D : sstate) (KS : shp), s_ops D = DRVOPS ->
  DrvTop.drv_chk SEGS BL HULL XCLZ PFP RS REMAT 0%uint63 (t_st (S3_N.T_MAINN b)) D = true -> ops0_ok (t_st (S3_N.T_MAINN b)) D ->
  NODE_b SEGS R D (DR R KS) -> tpl_rzb SEGS (OPS R) MP1 (DR R KS) E0 (t_st (S3_N.T_MAINN b)).
Proof.
  intros b D KS HO HC Hops HN E ms m Heb [tid ->] HS.
  destruct (DrvTop.drv_bridgeE SEGS R BL HBL WNOFF WNOFF_val HULL XCLZ PFP heap_fp_drv pool_fp_drv RS RS_R REMAT 0%uint63 (t_st (S3_N.T_MAINN b)) D E ms _
              (VL wzero) (VL wzero) (VL wzero) HO HC HS Heb (or_introl (mainN_resv b)) (Hops E ms _ tid HS eq_refl)) as (E' & Heb' & HS').
  apply (HN E' ms (with_tid tid model0)); [cbn [r_PB R]; unfold PB; congruence | reflexivity | exact HS'].
Qed.

Record FamHypsN_b : Prop := FHN {
  fhn_ext : ext_ok_b DN.CONTRACTS [] }.
Theorem rzb_usage : length (in_argv inp) <> 2%nat -> FamHypsN_b -> rzb SEGS c0 (K inp).
Proof.
  intros HargcN [HE]. pose proof (ctab_N_b HE) as HC.
  assert (HDG : HN.hyps_b R) by (exact (HN.Hyps R HC)).
  assert (HK : K inp = DR R USAGE).
  { unfold K, DR. cbn [r_fs r_a0 r_p1 R]. unfold a0, p1. pose proof HargcN as L. set (l := in_argv inp) in L |- *. clearbody l.
    destruct l as [|x [|y [|z l']]]; cbn [hd tl]; try reflexivity. exfalso. apply L. reflexivity. }
  rewrite HK. apply (rzb_chainN HargcN). apply (bridgeN_b rflag DN.T_DRVN _ OPS_N (DRV_CHK_N rflag) (OPS0_N rflag)). exact (RN.N_T_DRVN_b R HDG).
Qed.

Theorem rzb_usage_full : length (in_argv inp) <> 2%nat -> FamHypsN_b -> rzb SEGS c0 (K inp).
Proof using inp sp brk0 mb rnd lim Hva Hve Hhw Hsz Hvl Hrdr Hen A C aw_fds aw_ceil_fds cw_init aw_ceil0 aw_init.
  exact rzb_usage.
Qed.

End TOP.
End RunSrcB.
