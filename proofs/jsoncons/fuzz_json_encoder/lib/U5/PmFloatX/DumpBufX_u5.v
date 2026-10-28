(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmFloatXSpecs_u5 PmFloatXTu_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncSinkBridges_u5 EncTail_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_db_xsrc_T_u5 Cut_db_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DBX.
Import PMES.
Module G := Cut_db_xsrc_u5.
Module GT := Cut_db_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.
Definition RETPC : Z := 0x441c0.
Definition S2E : expr := EVar 32.
Definition F0W (w : Z) : list SGP.region := [(EVar 2, -w, ELit w)].
Definition F0 : list SGP.region := F0W 8608.
Definition SCRT : Z := 8608.      (* [comment removed for export] *)

Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
(* [comment removed for export] *)
Definition sink_j (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> CA.blocks -> option CH2.cinfo) (i k j : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (match CH2.ret_of G.RETS i k with Some j' => Nat.eqb j' j | None => false end &&
   match nth_error G.CPS j with Some cj => isSome (f c ps cj (nth i G.BLS []) (nth j G.BLS [])) | None => false end)%bool.
(* [comment removed for export] *)
Definition ret_cut (i k : nat) : nat := match i, k with 2%nat, _ => 9%nat | 1%nat, 1%nat => 3%nat | 1%nat, 2%nat => 4%nat | 1%nat, 3%nat => 5%nat | 1%nat, 6%nat => 6%nat | 1%nat, 9%nat => 7%nat | 1%nat, _ => 8%nat | _, _ => 10%nat end.
(* [comment removed for export] *)
Definition is_tail (i : nat) : bool := match i with 6%nat | 8%nat | 10%nat => true | _ => false end.
Definition is_after_push (i : nat) : bool := match i with 3%nat | 4%nat | 5%nat | 7%nat | 9%nat => true | _ => false end.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  (SP.F_sub (CC.cp_F c) F0 && (Nat.leb 50 (CC.cp_nx c) || Nat.eqb i 0)) &&
  match t with
  | CC.TGoto j s =>
      match i, j with
      | 0%nat, 1%nat => expr_eqb (CC.slook s 48) (EVar 11) && expr_eqb (CC.slook s 49) (ELit 1)
      | 1%nat, 1%nat => expr_eqb (CC.slook s 48) (EAlu Instr.ALU_ADD (EVar 48) (ELit (-1))) && expr_eqb (CC.slook s 49) (EVar 49) &&
                                      PB.prove (CC.cp_know c) (KRange (EVar 48) 1 99)
      | 1%nat, 2%nat => expr_eqb (CC.slook s 48) (EVar 48) && (expr_eqb (CC.slook s 49) (EVar 49) || expr_eqb (CC.slook s 49) (ELit 0))
      | _, 1%nat => is_after_push i && expr_eqb (CC.slook s 48) (EAlu Instr.ALU_ADD (EVar 48) (ELit (-1))) && PB.prove (CC.cp_know c) (KRange (EVar 48) 1 99)
      | _, _ => false
      end
  | CC.TOther pc =>
      if Z.eqb pc PML.PC_STR_PUSH_BACK then
        if is_tail i then
          (Z.eqb (SR.ps_pc ps) PML.PC_STR_PUSH_BACK && ETL.tail_base_chk GT.NF c ps && CL.ps_reg_is ps 10 (EVar 32) && CL.ps_reg_is ps 11 (ELit 48))%bool
        else
          (Z.eqb (SR.ps_pc ps) PML.PC_STR_PUSH_BACK && sink_j (ESB.pushb_chk GT.NF G.HDECL S2E 0) i k (ret_cut i k) c ps &&
           match i with 1%nat | 2%nat => true | 9%nat => PB.prove cells (KRange (EVar 48) 1 99) | _ => false end)%bool
      else
        (PB.exit_base_chk GT.NF RETPC c ps && PB.prove cells (KRange (EVar 48) 1 99) &&
         match i with
         | 1%nat => PB.prove cells (KRange (EVar 49) 0 0)
         | _ => is_after_push i end)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition phase (n : Z) (i : nat) (E : env) (p : Z) : Prop :=
  match i with
  | 0%nat => p = 0
  | 1%nat => 0 <= p <= n - uv E (EVar 48) /\ (uv E (EVar 49) = 1 \/ 1 <= p)
  | 2%nat => 0 <= p <= n - uv E (EVar 48)
  | 3%nat | 4%nat | 5%nat | 7%nat | 9%nat => 1 <= p <= n + 1 - uv E (EVar 48)
  | 6%nat | 8%nat | 10%nat => 1 <= p <= n + 1
  | _ => False
  end.

Lemma after_push_phase : forall n i E p, is_after_push i = true -> phase n i E p -> 1 <= p <= n + 1 - uv E (EVar 48).
Proof. intros n i E p A H. destruct i as [|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]; try discriminate A; exact H. Qed.

Lemma uv_add_lit : forall E e z, uv E (EAlu Instr.ALU_ADD e (ELit z)) = (uv E e + z) mod 2 ^ 64.
Proof.
  intros. pose proof (PB.uv_eaddz E e z) as H. unfold APC.eaddz, PB.uv in H. rewrite AX2S.mkAlu_denot in H. unfold uv, PB.uv. cbn [edenot] in H |- *. exact H.
Qed.
Lemma uv_lit1 : forall E z, 0 <= z < 2 ^ 64 -> uv E (ELit z) = z.
Proof. intros. unfold uv, PB.uv. cbn [edenot]. apply u64_of_Z; lia. Qed.

Section DumpBufOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis PUSHB_OK : str_push_back_x_spec L HI.

(* [comment removed for export] *)
Section Stretch.
Variables (E0 : env) (sp S2 : Z).
Variable WIN : Z.
Hypothesis U2 : bv_unsigned (ev E0 2) = sp.
Hypothesis WIN0 : 0 <= WIN.
Hypothesis SPR : hl_ceil L + WIN <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis S2OBJ : PML.obj_on_stack L sp S2 24.

Lemma out_F0 : forall (F : list SGP.region) E' a, SP.F_sub F (F0W WIN) = true -> env_agree GT.NF E0 E' -> 0 <= a < 2 ^ 64 ->
  ~ (sp - WIN <= a < sp) -> SGP.outside E' F (Z_to_bv 64 a).
Proof.
  intros F E' a HF Hag Ha N1. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0. rewrite L5.unsigned_lit by lia.
  destruct SPR as (P1 & P2 & P3).
  unfold F0W in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|[]]; injection X as <- <- <-.
  rewrite (PB.estart_agree GT.NF E0 E' (EVar 2) (-WIN) Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U2. rewrite (u64_of_Z WIN) by lia. lia.
Qed.

Lemma sink_stretch : forall (F : list SGP.region) E' (M M' : mem) g, SP.F_sub F (F0W WIN) = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) ->
  (forall b, In b (PML.srep_blocks (ESB.s_rep g)) -> block_range L (fst b) (snd b)) ->
  ESB.sink_inv M S2 g -> ESB.sink_inv M' S2 g.
Proof.
  intros F E' M M' g HF Hag HFR HB (HS & HL).
  destruct S2OBJ as (O1 & O2 & O3). destruct SPR as (P1 & P2 & P3).
  assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - WIN \/ sp <= a) -> L5C.agree_on M M' a n).
  { intros a n H0 H1 H2 i Hi. apply HFR. apply (out_F0 F E' i HF Hag); lia. }
  split; [|exact HL].
  apply (EK.sink_at_agree M M' S2 (ESB.s_rep g)); [lia | lia | apply AG; lia | | exact HS].
  destruct (ESB.s_rep g) as [s|cap p s] eqn:Hrep; [exact I|].
  destruct (HB (p, cap) ltac:(left; reflexivity)) as (R0 & R1 & R2 & R3 & R4). cbn [fst snd] in *.
  split; [lia|]. split; [lia|]. apply AG; unfold hl_ceil in *; lia.
Qed.
End Stretch.

End DumpBufOk.
End DBX.
