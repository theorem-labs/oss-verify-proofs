(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopSpecs_u5 ReadKit_u5 ChunkKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_pcd_a_xsrc_u5 Cut_pcd_b_xsrc_u5 Cut_pcd_c_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Module PT.
Definition LOOP : Z := 0x4babc.      Definition INC : Z := 0x4bad4.      Definition R_SETEC : Z := 0x4bb1c.      Definition RET : Z := 0x4bb40.
Definition FRAME : Z := 80.          (* [comment removed for export] *)
Definition TEMP : Z := 12.           (* [comment removed for export] *)
Definition MASK : Z := 4294977024.   (* [comment removed for export] *)
End PT.

Module PS.
Module GA := Cut_pcd_a_xsrc_u5.  Module GB := Cut_pcd_b_xsrc_u5.  Module GC := Cut_pcd_c_xsrc_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ret_pcd : CL.is_ret_at RSEGS PT.RET. Proof. CL.solve_is_ret. Qed.

(* [comment removed for export] *)
Definition KO4 : list nat := [3; 4; 23; 24; 25; 26; 27]%nat.
(* [comment removed for export] *)
Definition pcd_live (R : bvmap 5 word) (P E : Z) : Prop :=
  getr R 9%bv = Z_to_bv 64 P /\ getr R 8%bv = Z_to_bv 64 E /\ getr R 18%bv = Z_to_bv 64 (P + 96) /\ getr R 19%bv = Z_to_bv 64 32 /\ getr R 20%bv = Z_to_bv 64 4 /\
  getr R 21%bv = Z_to_bv 64 1 /\ getr R 22%bv = Z_to_bv 64 PT.MASK.
Definition pcd_cur (R : bvmap 5 word) (p e : Z) : Prop := getr R 10%bv = Z_to_bv 64 p.
Definition same_s04 (R0 R' : bvmap 5 word) : Prop :=
  getr R' 8%bv = getr R0 8%bv /\ getr R' 9%bv = getr R0 9%bv /\ getr R' 18%bv = getr R0 18%bv /\ getr R' 19%bv = getr R0 19%bv /\ getr R' 20%bv = getr R0 20%bv /\
  getr R' 21%bv = getr R0 21%bv /\ getr R' 22%bv = getr R0 22%bv.
Definition pcd_frame (M : mem) (sp1 rav : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp1 - 8) rav /\ L5.u64_at RSEGS M (sp1 - 16) (bv_unsigned (getr R0 8%bv)) /\ L5.u64_at RSEGS M (sp1 - 24) (bv_unsigned (getr R0 9%bv)) /\
  L5.u64_at RSEGS M (sp1 - 32) (bv_unsigned (getr R0 18%bv)) /\ L5.u64_at RSEGS M (sp1 - 40) (bv_unsigned (getr R0 19%bv)) /\ L5.u64_at RSEGS M (sp1 - 48) (bv_unsigned (getr R0 20%bv)) /\
  L5.u64_at RSEGS M (sp1 - 56) (bv_unsigned (getr R0 21%bv)) /\ L5.u64_at RSEGS M (sp1 - 64) (bv_unsigned (getr R0 22%bv)).

Lemma pcd_frame_x : forall (K : Z -> Prop) (M M' : mem) sp1 rav R0, TK.samem K M M' -> 2 ^ 40 <= sp1 <= 2 ^ 47 -> (forall i, sp1 - 64 <= i < sp1 -> K i) ->
  pcd_frame M sp1 rav R0 -> pcd_frame M' sp1 rav R0.
Proof.
  intros K M M' sp1 rav R0 AG Hsp HK (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). unfold pcd_frame.
  repeat split; (eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]).
Qed.
Lemma pcd_live_keep : forall R R' P E, (forall q : reg, In (ridx q) [8; 9; 18; 19; 20; 21; 22]%nat -> getr R' q = getr R q) -> pcd_live R P E -> pcd_live R' P E.
Proof.
  intros R R' P E HK (H9 & H8 & H18 & H19 & H20 & H21 & H22). unfold pcd_live.
  rewrite (HK 9%bv ltac:(ck_in)), (HK 8%bv ltac:(ck_in)), (HK 18%bv ltac:(ck_in)), (HK 19%bv ltac:(ck_in)), (HK 20%bv ltac:(ck_in)), (HK 21%bv ltac:(ck_in)), (HK 22%bv ltac:(ck_in)). repeat split; assumption.
Qed.
Lemma rp_final : forall R0 R' : bvmap 5 word, getr R' 2%bv = getr R0 2%bv -> same_s04 R0 R' -> TK.keepsR KO4 R0 R' -> regs_preserved R0 R'.
Proof.
  intros R0 R' H2 (Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22) HK. apply CK.rp_of_keeps; [exact H2|]. intros q Hq. unfold CK.CSR in Hq. cbn [In] in Hq.
  assert (QQ : forall m : nat, ridx q = m -> q = Z_to_bv 5 (Z.of_nat m)) by (intros m <-; symmetry; apply ridx_roundtrip).
  assert (HK' : In (ridx q) KO4 -> getr R' q = getr R0 q) by (apply HK). unfold KO4 in HK'. cbn [In] in HK'.
  destruct Hq as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|Hq]]]]]]]]].
  - apply HK'. left. exact Hq.
  - apply HK'. right. left. exact Hq.
  - rewrite (QQ _ (eq_sym Hq)). exact Q8.
  - rewrite (QQ _ (eq_sym Hq)). exact Q9.
  - rewrite (QQ _ (eq_sym Hq)). exact Q18.
  - rewrite (QQ _ (eq_sym Hq)). exact Q19.
  - rewrite (QQ _ (eq_sym Hq)). exact Q20.
  - rewrite (QQ _ (eq_sym Hq)). exact Q21.
  - rewrite (QQ _ (eq_sym Hq)). exact Q22.
  - apply HK'. right. right. exact Hq.
Qed.
Lemma ko4_rp : forall R R', regs_preserved R R' -> TK.keepsR KO4 R R'.
Proof. intros R R' RP. apply TK.keepsR_preserved; [exact RP|]. intros q Hq. unfold KO4 in Hq. unfold callee_saved_idx. cbn [In] in *. intuition (subst; cbn; tauto). Qed.
Lemma sp_rp : forall (R R' : bvmap 5 word), regs_preserved R R' -> getr R' 2%bv = getr R 2%bv.
Proof. intros R R' RP. apply RP. ck_in. Qed.
Definition hv_slotX (off : Z) (pins : list (nat * Z)) (xp : list (nat * expr)) (q : nat) : expr :=
  match List.find (fun p => Nat.eqb (fst p) q) xp with Some p => snd p | None => RK.hv_slot off pins q end.
Definition hv_shapeX (sr : list expr) (off : Z) (pins : list (nat * Z)) (xp : list (nat * expr)) : bool :=
  forallb (fun q => expr_eqb (nth q sr (ELit 0)) (hv_slotX off pins xp q)) (seq 1 31).
Lemma regs_ok_hvBX : forall sr off pins xp sp0 R gl bl,
  hv_shapeX sr off pins xp = true -> 0 <= sp0 < 2 ^ 64 -> 0 <= sp0 + off < 2 ^ 64 ->
  getr R 2%bv = Z_to_bv 64 (sp0 + off) ->
  (forall q z, In (q, z) pins -> getr R (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z) ->
  (forall q x, In (q, x) xp -> getr R (Z_to_bv 5 (Z.of_nat q)) = edenot (CK.hvB sp0 R gl bl) x) ->
  regs_ok (CK.hvB sp0 R gl bl) sr R.
Proof.
  intros sr off pins xp sp0 R gl bl Hsh Hsp Hspo H2 Hpins Hxp. apply APSX.regs_ok_pointwise. intros r Hr0.
  assert (Hq : In (ridx r) (seq 1 31)).
  { apply in_seq. pose proof (ridx_range r). assert (ridx r <> 0%nat).
    { intros X. apply Hr0. rewrite <- (ridx_roundtrip r), X. apply bv_eq. reflexivity. } lia. }
  unfold hv_shapeX in Hsh. rewrite forallb_forall in Hsh. specialize (Hsh _ Hq). apply expr_eqb_eq in Hsh. rewrite Hsh.
  unfold hv_slotX. destruct (find (fun p => Nat.eqb (fst p) (ridx r)) xp) as [[q x]|] eqn:Hx.
  - apply find_some in Hx as [Hin Hq2]. cbn [fst] in Hq2. apply Nat.eqb_eq in Hq2. subst q. cbn [snd].
    rewrite <- (Hxp _ _ Hin), ridx_roundtrip. reflexivity.
  - unfold RK.hv_slot. destruct (Nat.eqb (ridx r) 2) eqn:E2.
    + apply Nat.eqb_eq in E2. assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r), E2; apply bv_eq; reflexivity). subst r.
      destruct (Z.eqb_spec off 0) as [->|Hne].
      * cbn [edenot ev CK.hvB]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite H2. f_equal. lia.
      * cbn [edenot ev CK.hvB]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite TK.add_lit by lia. exact H2.
    + destruct (find (fun p => Nat.eqb (fst p) (ridx r)) pins) as [[q z]|] eqn:Hf.
      * apply find_some in Hf as [Hin Hq2]. cbn [fst] in Hq2. apply Nat.eqb_eq in Hq2. subst q. cbn [snd edenot].
        rewrite <- (Hpins _ _ Hin), ridx_roundtrip. reflexivity.
      * cbn [edenot]. symmetry. apply CK.hvB_reg.
Qed.
Ltac ck_openX FPM cp plans off gl bl pn xp sp0 R M fx model K Hh Hl Hfp H2 Hpins Hxp :=
  let E := fresh "E" in set (E := CK.hvB sp0 R gl bl);
  assert (U2 : bv_unsigned (ev E 2) = sp0) by (apply CK.hvB_sp; lia);
  apply (TK.stretch_cps FPM cp fx E R M model K plans Hh Hl Hfp);
  [ apply (regs_ok_hvBX _ off pn xp); [vm_compute; reflexivity | lia | lia | first [exact H2 | rewrite Z.add_0_r; exact H2] | Hpins | Hxp] | | ].
Ltac ck_xpins X0 := let q := fresh in let x := fresh in let X := fresh in intros q x X; cbn [In] in X;
  destruct X as [X|[]]; injection X as <- <-; exact X0.
Lemma r18_this : forall sp0 R gl bl P, getr R 9%bv = Z_to_bv 64 P -> getr R 18%bv = Z_to_bv 64 (P + 96) -> 0 <= P -> P + 96 < 2 ^ 64 ->
  getr R 18%bv = edenot (CK.hvB sp0 R gl bl) (APC.eaddz (EVar 41) 96).
Proof.
  intros sp0 R gl bl P H9 H18 HP HP2. change (APC.eaddz (EVar 41) 96) with (EAlu ALU_ADD (EVar (32 + ridx (9%bv : reg))) (ELit 96)).
  cbn [edenot]. rewrite CK.hvB_reg, H18, H9. symmetry. apply TK.add_lit; lia.
Qed.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

(* [comment removed for export] *)
Lemma s_pcd_entry : forall (fx : FPState) R M model K sp1 P E p e rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 P -> getr R 11%bv = Z_to_bv 64 E ->
  2 ^ 40 <= P <= 2 ^ 47 -> 0 <= E < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 ->
  L5.u64_at RSEGS M (P + 192) e -> L5.u64_at RSEGS M (P + 200) p -> L5.defined M (sp1 - 80) 80 -> sp1 <= P ->
  (p = e -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> TK.keepsR CK.CSR R R' ->
      TK.samem (fun a => ~ (sp1 - 80 <= a < sp1)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  (p <> e -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> pcd_live R' P E -> pcd_cur R' p e -> pcd_frame M' sp1 rav R -> TK.keepsR KO4 R R' ->
      TK.samem (fun a => ~ (sp1 - 80 <= a < sp1)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PT.LOOP M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_PCHECK_DONE M model) K.
Proof.
  intros fx R M model K sp1 P E p e rav Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 HP HE Hp He C192 C200 DF J1 Kret Kloop.
  change PML.PC_PCHECK_DONE with (CC.cp_pc GA.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  ck_open FPM GA.cp0 (GA.plans 0%nat _ eq_refl) 0 [e; p] (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E0 (10%bv : reg) H10. ck_gh E0 0%nat e. ck_gh E0 1%nat p.
    unfold know_ok, GA.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + ck_kw64 (P + 192) e C192. + ck_kw64 (P + 200) p C200. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E0 (10%bv : reg) H10. ck_reg E0 (11%bv : reg) H11. ck_reg E0 (1%bv : reg) H1. ck_gh E0 0%nat e. ck_gh E0 1%nat p.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 80 <= a < sp1)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk1; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    (ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]); ck_probes HLF PF.
    + destruct PF as (PF & _). ck_w2z PF. apply RK.w_inj in PF; [|lia|lia].
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (rewrite (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ [1%nat] 1%bv HLF eq_refl Hag64 ltac:(ck_in)); exact H1).
      apply (CK.ret_leaf fx' R' _ M' model K rav ret_pcd Hh Hl R1 Hra).
      apply (Kret PF fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | ck_keeps HLF Hag64 CK.CSR | exact FRM | exact MG].
    + destruct PF as (PF & _). ck_w2z PF. assert (NE : p <> e) by (intros X; apply PF; rewrite X; reflexivity).
      apply (Kloop NE fx' R' M' Hfp').
      * tk_lin HLF (2%bv : reg).
      * unfold pcd_live, PT.MASK. repeat split; [tk_lin HLF (9%bv : reg) | tk_lin HLF (8%bv : reg) | tk_lin HLF (18%bv : reg) | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | tk_lin HLF (21%bv : reg) | tk_lin HLF (22%bv : reg)].
      * unfold pcd_cur. tk_lin HLF (10%bv : reg).
      * unfold pcd_frame. repeat split.
        -- ck_cell64 HLF (EVar 2) (-8) (EVar 33). ck_atom.
        -- ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg).
        -- ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg).
        -- ck_saved HLF Hag64 (-32) 50%nat (18%bv : reg).
        -- ck_saved HLF Hag64 (-40) 51%nat (19%bv : reg).
        -- ck_saved HLF Hag64 (-48) 52%nat (20%bv : reg).
        -- ck_saved HLF Hag64 (-56) 53%nat (21%bv : reg).
        -- ck_saved HLF Hag64 (-64) 54%nat (22%bv : reg).
      * ck_keeps HLF Hag64 KO4. * exact FRM. * exact MG.
Qed.

(* [comment removed for export] *)
Lemma s_pcd_loop : forall (fx : FPState) R M model K sp1 P E p e b mo,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> CK.spok sp1 -> pcd_live R P E -> pcd_cur R p e ->
  2 ^ 40 <= P <= 2 ^ 47 -> 0 <= E < 2 ^ 64 -> 2 ^ 12 <= p <= 2 ^ 47 -> 0 <= e < 2 ^ 64 -> 0 <= b <= 255 -> 0 <= mo < 2 ^ 64 ->
  L5.u8_at RSEGS M p b -> L5.u64_at RSEGS M (P + 128) (P + 96) -> L5.u64_at RSEGS M (P + 96) PML.VT_FUNC -> PML.img_ro M -> L5.u8_at RSEGS M (P + 211) mo ->
  L5.defined M (P + 211) 1 -> L5.defined M (sp1 - 80 + 12) 4 -> sp1 <= P -> p + 1 <= sp1 - 80 -> P mod 8 = 0 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> pcd_live R' P E -> pcd_cur R' p e -> TK.keepsR KO4 R R' ->
      L5.u8_at RSEGS M' (P + 211) mo -> TK.samem (fun a => ~ (sp1 - 80 + 12 <= a < sp1 - 80 + 16) /\ ~ (P + 211 <= a < P + 212)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PT.INC M' model) K) ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 1%bv = Z_to_bv 64 PT.R_SETEC -> getr R' 10%bv = Z_to_bv 64 E -> getr R' 11%bv = Z_to_bv 64 4 ->
      TK.keepsR KO4 R R' -> L5.u8_at RSEGS M' (P + 211) 0 -> TK.samem (fun a => ~ (sp1 - 80 + 12 <= a < sp1 - 80 + 16) /\ ~ (P + 211 <= a < P + 212)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SET_EC M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PT.LOOP M model) K.
Proof.
  intros fx R M model K sp1 P E p e b mo Hh Hl Hfp H2 [Hsp Hal] (H9 & H8 & H18 & H19 & H20 & H21 & H22) H10 HP HE Hp He Hb Hmo Cb C128 C96 RO C211 D211 DT J1 J2 PAL Kinc Kerr.
  change PT.LOOP with (CC.cp_pc GB.cp0). unfold PT.MASK in H22. unfold pcd_cur in H10.
  pose proof (r18_this sp1 R [b; mo] (fun _ : nat => @nil byte) P H9 H18 ltac:(lia) ltac:(lia)) as X18.
  ck_openX FPM GB.cp0 (GB.plans 0%nat _ eq_refl) (-80) [b; mo] (fun _ : nat => @nil byte) [(19%nat, 32); (20%nat, 4); (21%nat, 1); (22%nat, 4294977024)] [(18%nat, APC.eaddz (EVar 41) 96)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins ltac:(ck_xpins X18).
  - ck_reg E0 (9%bv : reg) H9. ck_reg E0 (10%bv : reg) H10. ck_gh E0 0%nat b. ck_gh E0 1%nat mo.
    unfold know_ok, GB.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_range. + ck_kw8 p b Cb. + e_range. + ck_kw64 (P + 128) (P + 96) C128. + unfold PML.VT_FUNC in C96. ck_kw64 (P + 96) 804528 C96. + tk_kimg RO.
    + ck_kw8 (P + 211) mo C211. + e_wr. + e_unk. + e_wr. + e_disj. + e_disj. + e_disj. + e_align PAL.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E0 (9%bv : reg) H9. ck_reg E0 (8%bv : reg) H8. ck_reg E0 (10%bv : reg) H10. ck_gh E0 0%nat b. ck_gh E0 1%nat mo.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 80 + 12 <= a < sp1 - 80 + 16) /\ ~ (P + 211 <= a < P + 212)) M M').
    { apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside. }
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    assert (ERR : srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SET_EC M' model) K -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SET_EC M' model) K) by (intros X; exact X).
    ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]].
    + apply (Kerr fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold PT.R_SETEC; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | ck_keeps HLF Hag64 KO4 | | exact FRM | exact MG].
      ck_cell8 HLF (EVar 41) 211 (ELit 0). reflexivity.
    + apply (Kerr fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold PT.R_SETEC; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | ck_keeps HLF Hag64 KO4 | | exact FRM | exact MG].
      ck_cell8 HLF (EVar 41) 211 (ELit 0). reflexivity.
    + apply (Kinc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | | ck_keeps HLF Hag64 KO4 | | exact FRM | exact MG].
      * unfold pcd_live, PT.MASK. repeat split; [tk_lin HLF (9%bv : reg) | tk_lin HLF (8%bv : reg) | tk_lin HLF (18%bv : reg) | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | tk_lin HLF (21%bv : reg) | tk_lin HLF (22%bv : reg)].
      * unfold pcd_cur. tk_lin HLF (10%bv : reg).
      * ck_cell8 HLF (EVar 41) 211 (EVar 65). ck_atom.
Qed.

(* [comment removed for export] *)
Lemma s_pcd_inc : forall (fx : FPState) R M model K sp1 P E p e p0 rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> CK.spok sp1 -> pcd_live R P E -> pcd_cur R p e ->
  2 ^ 40 <= P <= 2 ^ 47 -> 0 <= E < 2 ^ 64 -> 2 ^ 12 <= p <= 2 ^ 47 -> 0 <= e < 2 ^ 64 -> 0 <= p0 < 2 ^ 64 ->
  L5.u64_at RSEGS M (P + 200) p0 -> L5.defined M (P + 200) 8 -> L5.u64_at RSEGS M (P + 192) e -> pcd_frame M sp1 rav R0 -> L5.ra_ok rav -> sp1 <= P ->
  (p + 1 = e -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s04 R0 R' -> TK.keepsR KO4 R R' ->
      L5.u64_at RSEGS M' (P + 200) (p + 1) -> TK.samem (fun a => ~ (P + 200 <= a < P + 208)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  (p + 1 <> e -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> pcd_live R' P E -> pcd_cur R' (p + 1) e -> TK.keepsR KO4 R R' ->
      L5.u64_at RSEGS M' (P + 200) (p + 1) -> TK.samem (fun a => ~ (P + 200 <= a < P + 208)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PT.LOOP M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PT.INC M model) K.
Proof.
  intros fx R M model K sp1 P E p e p0 rav R0 Hh Hl Hfp H2 [Hsp Hal] (H9 & H8 & H18 & H19 & H20 & H21 & H22) H10 HP HE Hp He Hp0 C200 D200 C192 (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8) Hra J1 Kret Kloop.
  change PT.INC with (CC.cp_pc GA.cp1). unfold pcd_cur in H10.
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20. pose proof (RG 21%bv) as G21. pose proof (RG 22%bv) as G22.
  set (gl := [rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv); p0;
              bv_unsigned (getr R0 21%bv); bv_unsigned (getr R0 22%bv); e]).
  ck_open FPM GA.cp1 (GA.plans 1%nat _ eq_refl) (-80) gl (fun _ : nat => @nil byte) [(21%nat, 1)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_reg E0 (9%bv : reg) H9. ck_reg E0 (10%bv : reg) H10. ck_gh E0 0%nat rav. ck_gh E0 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E0 2%nat (bv_unsigned (getr R0 9%bv)).
    ck_gh E0 3%nat (bv_unsigned (getr R0 18%bv)). ck_gh E0 4%nat (bv_unsigned (getr R0 19%bv)). ck_gh E0 5%nat (bv_unsigned (getr R0 20%bv)). ck_gh E0 6%nat p0.
    ck_gh E0 7%nat (bv_unsigned (getr R0 21%bv)). ck_gh E0 8%nat (bv_unsigned (getr R0 22%bv)). ck_gh E0 9%nat e.
    unfold know_ok, GA.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6.
    + ck_kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7. + ck_kw64 (sp1 - 64) (bv_unsigned (getr R0 22%bv)) F8.
    + e_range. + ck_kw64 (P + 200) p0 C200. + e_wr. + e_range. + e_disj. + ck_kw64 (P + 192) e C192.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E0 (9%bv : reg) H9. ck_reg E0 (8%bv : reg) H8. ck_reg E0 (10%bv : reg) H10.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 10)%nat) by (change 10%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx GA.cp1) with 74%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (P + 200 <= a < P + 208)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk1; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    assert (G73 : ev E' 73%nat = Z_to_bv 64 e) by exact (GH 9%nat _ eq_refl).
    (ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]); ck_probes HLF PF;
      (assert (C200' : L5.u64_at RSEGS M' (P + 200) (p + 1)) by (ck_cell64 HLF (EVar 41) 200 (EAlu ALU_ADD (EVar 42) (ELit 1)); ck_vlin)).
    + destruct PF as (PF & _). ck_w2z PF. rewrite RK.add_w in PF by lia. rewrite G73 in PF. apply RK.w_inj in PF; [|lia|lia].
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
      apply (CK.ret_leaf fx' R' _ M' model K rav ret_pcd Hh Hl R1 Hra).
      apply (Kret PF fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 KO4 | exact C200' | exact FRM | exact MG].
      unfold same_s04. repeat split.
      * tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (20%bv : reg). etransitivity; [exact (GH 5%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (21%bv : reg). etransitivity; [exact (GH 7%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (22%bv : reg). etransitivity; [exact (GH 8%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + destruct PF as (PF & _). ck_w2z PF. rewrite RK.add_w in PF by lia. rewrite G73 in PF. assert (NE : p + 1 <> e) by (intros X; apply PF; rewrite X; reflexivity).
      apply (Kloop NE fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | | ck_keeps HLF Hag64 KO4 | exact C200' | exact FRM | exact MG].
      * unfold pcd_live. repeat split; [tk_lin HLF (9%bv : reg) | tk_lin HLF (8%bv : reg) | | | | | ].
        -- rewrite (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ [18%nat] 18%bv HLF eq_refl Hag64 ltac:(ck_in)); exact H18.
        -- rewrite (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ [19%nat] 19%bv HLF eq_refl Hag64 ltac:(ck_in)); exact H19.
        -- rewrite (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ [20%nat] 20%bv HLF eq_refl Hag64 ltac:(ck_in)); exact H20.
        -- tk_lin HLF (21%bv : reg).
        -- rewrite (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ [22%nat] 22%bv HLF eq_refl Hag64 ltac:(ck_in)); exact H22.
      * unfold pcd_cur. tk_lin HLF (10%bv : reg).
Qed.

(* [comment removed for export] *)
Lemma s_pcd_r_setec : forall (fx : FPState) R M model K sp1 rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> CK.spok sp1 -> pcd_frame M sp1 rav R0 -> L5.ra_ok rav ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s04 R0 R' -> TK.keepsR KO4 R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PT.R_SETEC M model) K.
Proof.
  intros fx R M model K sp1 rav R0 Hh Hl Hfp H2 [Hsp Hal] (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8) Hra Hcont.
  change PT.R_SETEC with (CC.cp_pc GC.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20. pose proof (RG 21%bv) as G21. pose proof (RG 22%bv) as G22.
  set (gl := [rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv);
              bv_unsigned (getr R0 21%bv); bv_unsigned (getr R0 22%bv)]).
  ck_open FPM GC.cp0 (GC.plans 0%nat _ eq_refl) (-80) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 2%nat (bv_unsigned (getr R0 9%bv)). ck_gh E 3%nat (bv_unsigned (getr R0 18%bv)). ck_gh E 4%nat (bv_unsigned (getr R0 19%bv)).
    ck_gh E 5%nat (bv_unsigned (getr R0 20%bv)). ck_gh E 6%nat (bv_unsigned (getr R0 21%bv)). ck_gh E 7%nat (bv_unsigned (getr R0 22%bv)).
    unfold know_ok, GC.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5.
    + ck_kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7. + ck_kw64 (sp1 - 64) (bv_unsigned (getr R0 22%bv)) F8. + ck_kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 8)%nat) by (change 8%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx GC.cp0) with 72%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'. pose proof (TK.frame_nil _ _ _ _ _ _ HLF eq_refl) as EQ. subst M'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M model K rav ret_pcd Hh Hl R1 Hra).
    apply (Hcont fx' R' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 KO4].
    unfold same_s04. repeat split.
    + tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (20%bv : reg). etransitivity; [exact (GH 5%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (21%bv : reg). etransitivity; [exact (GH 6%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (22%bv : reg). etransitivity; [exact (GH 7%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
Qed.
End S.
End PS.
