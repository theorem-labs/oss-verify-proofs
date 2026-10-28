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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_skipws_a_xsrc_u5 Cut_skipws_b_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Module SWT.
Definition LOOP : Z := 0x4765c.      Definition R_SPACE : Z := 0x476c0.      Definition R_POP : Z := 0x476d4.      Definition RET : Z := 0x47708.
Definition FRAME : Z := 80.          (* [comment removed for export] *)
Definition MASK : Z := 4294977024.   (* [comment removed for export] *)
End SWT.

Module SWS.
Module GA := Cut_skipws_a_xsrc_u5.  Module GB := Cut_skipws_b_xsrc_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ret_sw : CL.is_ret_at RSEGS SWT.RET. Proof. CL.solve_is_ret. Qed.

(* [comment removed for export] *)
Definition wsb (n : nat) : bool := negb (Z.eqb (bv_unsigned (alu64 ALU_AND (alu64 ALU_SRL (Z_to_bv 64 SWT.MASK) (Z_to_bv 64 (Z.of_nat n))) (Z_to_bv 64 1))) 0).
Lemma ws_tab : forallb (fun n => implb (wsb n) (existsb (Nat.eqb n) [9; 10; 13; 32]%nat)) (seq 0 33) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ws_class : forall b, 0 <= b <= 32 -> alu64 ALU_AND (alu64 ALU_SRL (Z_to_bv 64 SWT.MASK) (Z_to_bv 64 b)) (Z_to_bv 64 1) <> Z_to_bv 64 0 -> In b [9; 10; 13; 32].
Proof.
  intros b Hb H. pose proof ws_tab as T. rewrite forallb_forall in T. specialize (T (Z.to_nat b) ltac:(apply in_seq; lia)).
  assert (W : wsb (Z.to_nat b) = true).
  { unfold wsb. rewrite Z2Nat.id by lia. apply negb_true_iff. apply Z.eqb_neq. intros X. apply H. apply bv_eq. rewrite X. reflexivity. }
  rewrite W in T. cbn [implb] in T. apply existsb_exists in T as (m & Hm & Heq). apply Nat.eqb_eq in Heq. subst m.
  cbn [In] in Hm. cbn [In]. lia.
Qed.

(* [comment removed for export] *)
Definition KO7 : list nat := [3; 4; 24; 25; 26; 27]%nat.
(* [comment removed for export] *)
Definition sw_live (R : bvmap 5 word) (P e : Z) : Prop :=
  getr R 8%bv = Z_to_bv 64 P /\ getr R 9%bv = Z_to_bv 64 (P + 200) /\ getr R 18%bv = Z_to_bv 64 e /\
  getr R 19%bv = Z_to_bv 64 28 /\ getr R 20%bv = Z_to_bv 64 10 /\ getr R 21%bv = Z_to_bv 64 (-1) /\ getr R 22%bv = Z_to_bv 64 32 /\
  getr R 23%bv = Z_to_bv 64 SWT.MASK.
Definition SV : list nat := [8; 9; 18; 19; 20; 21; 22; 23]%nat.
Definition same_s06 (R0 R' : bvmap 5 word) : Prop :=
  getr R' 8%bv = getr R0 8%bv /\ getr R' 9%bv = getr R0 9%bv /\ getr R' 18%bv = getr R0 18%bv /\ getr R' 19%bv = getr R0 19%bv /\ getr R' 20%bv = getr R0 20%bv /\
  getr R' 21%bv = getr R0 21%bv /\ getr R' 22%bv = getr R0 22%bv /\ getr R' 23%bv = getr R0 23%bv.
Lemma same_s06_all : forall R0 R', same_s06 R0 R' -> forall q : reg, In (ridx q) SV -> getr R' q = getr R0 q.
Proof.
  intros R0 R' (Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23) q Hq. unfold SV in Hq. cbn [In] in Hq.
  assert (QQ : forall m : nat, m = ridx q -> q = Z_to_bv 5 (Z.of_nat m)) by (intros m ->; symmetry; apply ridx_roundtrip).
  repeat (destruct Hq as [Hq|Hq]; [rewrite (QQ _ Hq); assumption|]). destruct Hq.
Qed.
Definition sw_frame (M : mem) (sp1 rav : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp1 - 8) rav /\ L5.u64_at RSEGS M (sp1 - 16) (bv_unsigned (getr R0 8%bv)) /\ L5.u64_at RSEGS M (sp1 - 24) (bv_unsigned (getr R0 9%bv)) /\
  L5.u64_at RSEGS M (sp1 - 32) (bv_unsigned (getr R0 18%bv)) /\ L5.u64_at RSEGS M (sp1 - 40) (bv_unsigned (getr R0 19%bv)) /\ L5.u64_at RSEGS M (sp1 - 48) (bv_unsigned (getr R0 20%bv)) /\
  L5.u64_at RSEGS M (sp1 - 56) (bv_unsigned (getr R0 21%bv)) /\ L5.u64_at RSEGS M (sp1 - 64) (bv_unsigned (getr R0 22%bv)) /\ L5.u64_at RSEGS M (sp1 - 72) (bv_unsigned (getr R0 23%bv)).

Lemma sw_frame_x : forall (K : Z -> Prop) (M M' : mem) sp1 rav R0, TK.samem K M M' -> 2 ^ 40 <= sp1 <= 2 ^ 47 -> (forall i, sp1 - 80 <= i < sp1 -> K i) ->
  sw_frame M sp1 rav R0 -> sw_frame M' sp1 rav R0.
Proof.
  intros K M M' sp1 rav R0 AG Hsp HK (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9). unfold sw_frame.
  repeat split; (eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]).
Qed.
Lemma sw_live_keep : forall R R' P e, (forall q : reg, In (ridx q) SV -> getr R' q = getr R q) -> sw_live R P e -> sw_live R' P e.
Proof.
  intros R R' P e HK (H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23). unfold sw_live.
  rewrite (HK 8%bv ltac:(ck_in)), (HK 9%bv ltac:(ck_in)), (HK 18%bv ltac:(ck_in)), (HK 19%bv ltac:(ck_in)), (HK 20%bv ltac:(ck_in)), (HK 21%bv ltac:(ck_in)), (HK 22%bv ltac:(ck_in)), (HK 23%bv ltac:(ck_in)).
  repeat split; assumption.
Qed.
Lemma sv_rp : forall R R', regs_preserved R R' -> forall q : reg, In (ridx q) SV -> getr R' q = getr R q.
Proof. intros R R' RP. apply (TK.keepsR_preserved SV R R' RP). intros q Hq. unfold SV in Hq. unfold callee_saved_idx. cbn [In] in *. intuition (subst; cbn; tauto). Qed.
Lemma rp_final : forall R0 R' : bvmap 5 word, getr R' 2%bv = getr R0 2%bv -> same_s06 R0 R' -> TK.keepsR KO7 R0 R' -> regs_preserved R0 R'.
Proof.
  intros R0 R' H2 SS HK. apply CK.rp_of_keeps; [exact H2|]. intros q Hq.
  assert (D : In (ridx q) KO7 \/ In (ridx q) SV) by (unfold CK.CSR, KO7, SV in *; cbn [In] in *; intuition).
  destruct D as [D|D]; [apply HK; exact D | apply (same_s06_all _ _ SS); exact D].
Qed.
Lemma ko7_rp : forall R R', regs_preserved R R' -> TK.keepsR KO7 R R'.
Proof. intros R R' RP. apply TK.keepsR_preserved; [exact RP|]. intros q Hq. unfold KO7 in Hq. unfold callee_saved_idx. cbn [In] in *. intuition (subst; cbn; tauto). Qed.
Lemma sp_rp : forall (R R' : bvmap 5 word), regs_preserved R R' -> getr R' 2%bv = getr R 2%bv.
Proof. intros R R' RP. apply RP. ck_in. Qed.
Ltac sw_reg HLF r := first [tk_lin HLF r | tk_reg HLF r; first [reflexivity | apply bv_eq; vm_compute; reflexivity]].

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

(* [comment removed for export] *)
Definition KF (P : Z) (a : Z) : Prop := ~ (P + 160 <= a < P + 184) /\ ~ (P + 200 <= a < P + 208).

(* [comment removed for export] *)
Lemma s_sw_entry : forall (fx : FPState) R M model K sp1 P p e rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 P ->
  2 ^ 40 <= P <= 2 ^ 47 - 272 -> 0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 ->
  L5.u64_at RSEGS M (P + 192) e -> L5.u64_at RSEGS M (P + 200) p -> L5.defined M (sp1 - 80) 80 -> sp1 <= P ->
  (p = e -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> TK.keepsR CK.CSR R R' ->
      TK.samem (fun a => ~ (sp1 - 80 <= a < sp1)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  (p <> e -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> sw_live R' P e -> getr R' 10%bv = Z_to_bv 64 p -> sw_frame M' sp1 rav R -> TK.keepsR KO7 R R' ->
      TK.samem (fun a => ~ (sp1 - 80 <= a < sp1)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' SWT.LOOP M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_SKIP_WS M model) K.
Proof.
  intros fx R M model K sp1 P p e rav Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 HP Hp He C192 C200 DF J1 Kret Kloop.
  change PML.PC_SKIP_WS with (CC.cp_pc GA.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  ck_open FPM GA.cp0 (GA.plans 0%nat _ eq_refl) 0 [e; p] (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_gh E 0%nat e. ck_gh E 1%nat p.
    unfold know_ok, GA.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + ck_kw64 (P + 192) e C192. + ck_kw64 (P + 200) p C200. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) H10. ck_reg E (1%bv : reg) H1. ck_gh E 0%nat e. ck_gh E 1%nat p.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 80 <= a < sp1)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk1; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    (ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]); ck_probes HLF PF.
    + destruct PF as (PF & _). ck_w2z PF. apply RK.w_inj in PF; [|lia|lia].
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (rewrite (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ [1%nat] 1%bv HLF eq_refl Hag64 ltac:(ck_in)); exact H1).
      apply (CK.ret_leaf fx' R' _ M' model K rav ret_sw Hh Hl R1 Hra).
      apply (Kret PF fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | ck_keeps HLF Hag64 CK.CSR | exact FRM | exact MG].
    + destruct PF as (PF & _). ck_w2z PF. assert (NE : p <> e) by (intros X; apply PF; rewrite X; reflexivity).
      apply (Kloop NE fx' R' M' Hfp').
      * tk_lin HLF (2%bv : reg).
      * unfold sw_live, SWT.MASK. repeat split; [tk_lin HLF (8%bv : reg) | tk_lin HLF (9%bv : reg) | tk_lin HLF (18%bv : reg) | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | sw_reg HLF (21%bv : reg) | tk_lin HLF (22%bv : reg) | tk_lin HLF (23%bv : reg)].
      * tk_lin HLF (10%bv : reg).
      * unfold sw_frame. repeat split.
        -- ck_cell64 HLF (EVar 2) (-8) (EVar 33). ck_atom.
        -- ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg).
        -- ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg).
        -- ck_saved HLF Hag64 (-32) 50%nat (18%bv : reg).
        -- ck_saved HLF Hag64 (-40) 51%nat (19%bv : reg).
        -- ck_saved HLF Hag64 (-48) 52%nat (20%bv : reg).
        -- ck_saved HLF Hag64 (-56) 53%nat (21%bv : reg).
        -- ck_saved HLF Hag64 (-64) 54%nat (22%bv : reg).
        -- ck_saved HLF Hag64 (-72) 55%nat (23%bv : reg).
      * ck_keeps HLF Hag64 KO7. * exact FRM. * exact MG.
Qed.

(* [comment removed for export] *)
Definition ghf (rav : Z) (R0 : bvmap 5 word) (l : list Z) : list Z :=
  rav :: bv_unsigned (getr R0 8%bv) :: bv_unsigned (getr R0 9%bv) :: bv_unsigned (getr R0 18%bv) :: bv_unsigned (getr R0 19%bv) :: bv_unsigned (getr R0 20%bv) ::
  bv_unsigned (getr R0 21%bv) :: bv_unsigned (getr R0 22%bv) :: l.

(* [comment removed for export] *)
Lemma same_of_gh : forall (R0 R' : bvmap 5 word) (g : nat -> word) (j23 : nat),
  getr R' 8%bv = g 1%nat -> getr R' 9%bv = g 2%nat -> getr R' 18%bv = g 3%nat -> getr R' 19%bv = g 4%nat -> getr R' 20%bv = g 5%nat -> getr R' 21%bv = g 6%nat -> getr R' 22%bv = g 7%nat ->
  getr R' 23%bv = g j23 ->
  g 1%nat = Z_to_bv 64 (bv_unsigned (getr R0 8%bv)) -> g 2%nat = Z_to_bv 64 (bv_unsigned (getr R0 9%bv)) -> g 3%nat = Z_to_bv 64 (bv_unsigned (getr R0 18%bv)) ->
  g 4%nat = Z_to_bv 64 (bv_unsigned (getr R0 19%bv)) -> g 5%nat = Z_to_bv 64 (bv_unsigned (getr R0 20%bv)) -> g 6%nat = Z_to_bv 64 (bv_unsigned (getr R0 21%bv)) ->
  g 7%nat = Z_to_bv 64 (bv_unsigned (getr R0 22%bv)) -> g j23 = Z_to_bv 64 (bv_unsigned (getr R0 23%bv)) -> same_s06 R0 R'.
Proof.
  intros R0 R' g j23 A1 A2 A3 A4 A5 A6 A7 A8 B1 B2 B3 B4 B5 B6 B7 B8. unfold same_s06.
  rewrite A1, A2, A3, A4, A5, A6, A7, A8, B1, B2, B3, B4, B5, B6, B7, B8, !Z_to_bv_bv_unsigned. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma s_sw_loop : forall (fx : FPState) R M model K sp1 P e p b st v160 v168 v176 v200 rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> CK.spok sp1 -> sw_live R P e -> getr R 10%bv = Z_to_bv 64 p ->
  2 ^ 40 <= P <= 2 ^ 47 - 272 -> 2 ^ 12 <= p <= 2 ^ 47 -> 0 <= e < 2 ^ 64 -> 0 <= b <= 255 -> 0 <= st <= 255 ->
  0 <= v160 < 2 ^ 64 -> 0 <= v168 < 2 ^ 64 -> 0 <= v176 < 2 ^ 64 -> 0 <= v200 < 2 ^ 64 ->
  L5.u8_at RSEGS M p b -> L5.u8_at RSEGS M (P + 208) st -> L5.u64_at RSEGS M (P + 160) v160 -> L5.u64_at RSEGS M (P + 168) v168 -> L5.u64_at RSEGS M (P + 176) v176 -> L5.u64_at RSEGS M (P + 200) v200 ->
  L5.defined M (P + 160) 24 -> L5.defined M (P + 200) 8 -> sw_frame M sp1 rav R0 -> L5.ra_ok rav -> sp1 <= P -> p + 1 <= sp1 - 80 ->
  (st = 28 -> forall q' (fx' : FPState) R' M', q' = p + 1 \/ q' = v200 -> PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 1%bv = Z_to_bv 64 SWT.R_POP -> getr R' 10%bv = Z_to_bv 64 P ->
      sw_live R' P e -> TK.keepsR KO7 R R' -> L5.u64_at RSEGS M' (P + 200) q' -> TK.samem (KF P) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_POP_STATE M' model) K) ->
  (st <> 28 -> In b [9; 10; 13; 32] -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 1%bv = Z_to_bv 64 SWT.R_SPACE ->
      getr R' 10%bv = Z_to_bv 64 P -> getr R' 11%bv = Z_to_bv 64 (P + 200) ->
      sw_live R' P e -> TK.keepsR KO7 R R' -> L5.u64_at RSEGS M' (P + 200) v200 -> TK.samem (KF P) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SKIP_SPACE M' model) K) ->
  (st <> 28 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s06 R0 R' -> TK.keepsR KO7 R R' ->
      L5.u64_at RSEGS M' (P + 200) v200 -> TK.samem (KF P) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R SWT.LOOP M model) K.
Proof.
  intros fx R M model K sp1 P e p b st v160 v168 v176 v200 rav R0 Hh Hl Hfp H2 [Hsp Hal] (H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23) H10 HP Hp He Hb Hst Hv160 Hv168 Hv176 Hv200
         Cb C208 C160 C168 C176 C200 D160 D200 (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9) Hra J1 J2 Kpop Kspace Kret.
  change SWT.LOOP with (CC.cp_pc GB.cp0). unfold SWT.MASK in H23.
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20. pose proof (RG 21%bv) as G21. pose proof (RG 22%bv) as G22.
  pose proof (RG 23%bv) as G23.
  set (gl := ghf rav R0 [b; st; v160; v168; v176; v200; bv_unsigned (getr R0 23%bv)]).
  ck_open FPM GB.cp0 (GB.plans 0%nat _ eq_refl) (-80) gl (fun _ : nat => @nil byte) [(19%nat, 28); (20%nat, 10); (21%nat, -1); (22%nat, 32); (23%nat, 4294977024)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_reg E (8%bv : reg) H8. ck_reg E (10%bv : reg) H10. ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 2%nat (bv_unsigned (getr R0 9%bv)).
    ck_gh E 3%nat (bv_unsigned (getr R0 18%bv)). ck_gh E 4%nat (bv_unsigned (getr R0 19%bv)). ck_gh E 5%nat (bv_unsigned (getr R0 20%bv)). ck_gh E 6%nat (bv_unsigned (getr R0 21%bv)).
    ck_gh E 7%nat (bv_unsigned (getr R0 22%bv)). ck_gh E 8%nat b. ck_gh E 9%nat st. ck_gh E 10%nat v160. ck_gh E 11%nat v168. ck_gh E 12%nat v176. ck_gh E 13%nat v200.
    ck_gh E 14%nat (bv_unsigned (getr R0 23%bv)).
    unfold know_ok, GB.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6. + ck_kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7.
    + ck_kw64 (sp1 - 64) (bv_unsigned (getr R0 22%bv)) F8. + ck_kw64 (sp1 - 72) (bv_unsigned (getr R0 23%bv)) F9.
    + e_range. + e_range. + ck_kw8 p b Cb. + e_range. + ck_kw8 (P + 208) st C208. + e_range.
    + ck_kw64 (P + 160) v160 C160. + ck_kw64 (P + 168) v168 C168. + ck_kw64 (P + 176) v176 C176. + ck_kw64 (P + 200) v200 C200.
    + e_wr. + e_wr. + e_disj. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8. ck_reg E (9%bv : reg) H9. ck_reg E (18%bv : reg) H18. ck_reg E (10%bv : reg) H10. ck_gh E 8%nat b. ck_gh E 9%nat st. ck_gh E 13%nat v200.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 15)%nat) by (change 15%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx GB.cp0) with 79%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KF P) M M').
    { apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside. }
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    assert (LIVE : (forall r : reg, In (ridx r) [8; 9; 18]%nat -> getr R' r = getr R r) -> getr R' 19%bv = Z_to_bv 64 28 -> getr R' 20%bv = Z_to_bv 64 10 -> getr R' 21%bv = Z_to_bv 64 (-1) ->
                   getr R' 22%bv = Z_to_bv 64 32 -> getr R' 23%bv = Z_to_bv 64 4294977024 -> sw_live R' P e).
    { intros HK X19 X20 X21 X22 X23. unfold sw_live, SWT.MASK. rewrite (HK 8%bv ltac:(ck_in)), (HK 9%bv ltac:(ck_in)), (HK 18%bv ltac:(ck_in)). repeat split; assumption. }
    ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]]]]; ck_probes HLF PF.
    + (* [comment removed for export] *)
      destruct PF as (_ & PF & _). ck_w2z PF. apply RK.w_inj in PF; [|lia|lia].
      apply (Kpop PF (p + 1) fx' R' M' (or_introl eq_refl) Hfp'); [tk_lin HLF (2%bv : reg) | unfold SWT.R_POP; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | | ck_keeps HLF Hag64 KO7 | | exact FRM | exact MG].
      * apply LIVE; [ck_keeps HLF Hag64 [8; 9; 18]%nat | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | sw_reg HLF (21%bv : reg) | tk_lin HLF (22%bv : reg) | tk_lin HLF (23%bv : reg)].
      * ck_cell64 HLF (EVar 40) 200 (EAlu ALU_ADD (EVar 42) (ELit 1)). ck_vlin.
    + (* [comment removed for export] *)
      destruct PF as (_ & PF & _). ck_w2z PF. apply RK.w_inj in PF; [|lia|lia].
      apply (Kpop PF v200 fx' R' M' (or_intror eq_refl) Hfp'); [tk_lin HLF (2%bv : reg) | unfold SWT.R_POP; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | | ck_keeps HLF Hag64 KO7 | | exact FRM | exact MG].
      * apply LIVE; [ck_keeps HLF Hag64 [8; 9; 18]%nat | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | sw_reg HLF (21%bv : reg) | tk_lin HLF (22%bv : reg) | tk_lin HLF (23%bv : reg)].
      * ck_cell64 HLF (EVar 40) 200 (EVar 77). ck_atom.
    + (* [comment removed for export] *)
      destruct PF as (PF & _). ck_w2z PF. assert (NE : st <> 28) by (intros X; apply PF; rewrite X; reflexivity).
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
      apply (CK.ret_leaf fx' R' _ M' model K rav ret_sw Hh Hl R1 Hra).
      apply (Kret NE fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 KO7 | | exact FRM | exact MG].
      * apply (same_of_gh R0 R' (fun j => ev E' (64 + j)) 14%nat); [tk_reg HLF (8%bv : reg); reflexivity | tk_reg HLF (9%bv : reg); reflexivity | tk_reg HLF (18%bv : reg); reflexivity | tk_reg HLF (19%bv : reg); reflexivity
          | tk_reg HLF (20%bv : reg); reflexivity | tk_reg HLF (21%bv : reg); reflexivity | tk_reg HLF (22%bv : reg); reflexivity | tk_reg HLF (23%bv : reg); reflexivity
          | exact (GH 1%nat _ eq_refl) | exact (GH 2%nat _ eq_refl) | exact (GH 3%nat _ eq_refl) | exact (GH 4%nat _ eq_refl) | exact (GH 5%nat _ eq_refl) | exact (GH 6%nat _ eq_refl) | exact (GH 7%nat _ eq_refl) | exact (GH 14%nat _ eq_refl)].
      * ck_cell64 HLF (EVar 40) 200 (EVar 77). ck_atom.
    + (* [comment removed for export] *)
      destruct PF as (_ & PF & _). ck_w2z PF. assert (NE : st <> 28) by (intros X; apply PF; rewrite X; reflexivity).
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
      apply (CK.ret_leaf fx' R' _ M' model K rav ret_sw Hh Hl R1 Hra).
      apply (Kret NE fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 KO7 | | exact FRM | exact MG].
      * apply (same_of_gh R0 R' (fun j => ev E' (64 + j)) 14%nat); [tk_reg HLF (8%bv : reg); reflexivity | tk_reg HLF (9%bv : reg); reflexivity | tk_reg HLF (18%bv : reg); reflexivity | tk_reg HLF (19%bv : reg); reflexivity
          | tk_reg HLF (20%bv : reg); reflexivity | tk_reg HLF (21%bv : reg); reflexivity | tk_reg HLF (22%bv : reg); reflexivity | tk_reg HLF (23%bv : reg); reflexivity
          | exact (GH 1%nat _ eq_refl) | exact (GH 2%nat _ eq_refl) | exact (GH 3%nat _ eq_refl) | exact (GH 4%nat _ eq_refl) | exact (GH 5%nat _ eq_refl) | exact (GH 6%nat _ eq_refl) | exact (GH 7%nat _ eq_refl) | exact (GH 14%nat _ eq_refl)].
      * ck_cell64 HLF (EVar 40) 200 (EVar 77). ck_atom.
    + (* [comment removed for export] *)
      destruct PF as (PW & PF & _). ck_w2z PF. assert (NE : st <> 28) by (intros X; apply PF; rewrite X; reflexivity).
      ck_paths HLF RF. destruct RF as (_ & _ & RB & _). ck_rlin RB.
      assert (B32 : 0 <= b <= 32) by lia. ck_w2z PW.
      apply (Kspace NE (ws_class b B32 PW) fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold SWT.R_SPACE; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | | ck_keeps HLF Hag64 KO7 | | exact FRM | exact MG].
      * apply LIVE; [ck_keeps HLF Hag64 [8; 9; 18]%nat | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | sw_reg HLF (21%bv : reg) | tk_lin HLF (22%bv : reg) | tk_lin HLF (23%bv : reg)].
      * ck_cell64 HLF (EVar 40) 200 (EVar 77). ck_atom.
Qed.

(* [comment removed for export] *)
Lemma s_sw_r_space : forall (fx : FPState) R M model K sp1 P e q rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> CK.spok sp1 -> sw_live R P e ->
  2 ^ 40 <= P <= 2 ^ 47 - 272 -> 0 <= e < 2 ^ 64 -> 0 <= q < 2 ^ 64 -> L5.u64_at RSEGS M (P + 200) q -> sw_frame M sp1 rav R0 -> L5.ra_ok rav ->
  (q = e -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s06 R0 R' -> TK.keepsR KO7 R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M model) K) ->
  (q <> e -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> sw_live R' P e -> getr R' 10%bv = Z_to_bv 64 q -> TK.keepsR KO7 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' SWT.LOOP M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R SWT.R_SPACE M model) K.
Proof.
  intros fx R M model K sp1 P e q rav R0 Hh Hl Hfp H2 [Hsp Hal] (H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23) HP He Hq C200 (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9) Hra Kret Kloop.
  change SWT.R_SPACE with (CC.cp_pc GA.cp1). unfold SWT.MASK in H23.
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun x : reg => bv_unsigned_in_range _ (getr R0 x)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20. pose proof (RG 21%bv) as G21. pose proof (RG 22%bv) as G22.
  pose proof (RG 23%bv) as G23.
  set (gl := ghf rav R0 [q; bv_unsigned (getr R0 23%bv)]).
  ck_open FPM GA.cp1 (GA.plans 1%nat _ eq_refl) (-80) gl (fun _ : nat => @nil byte) [(19%nat, 28); (20%nat, 10); (21%nat, -1); (22%nat, 32); (23%nat, 4294977024)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_reg E (9%bv : reg) H9. ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 2%nat (bv_unsigned (getr R0 9%bv)).
    ck_gh E 3%nat (bv_unsigned (getr R0 18%bv)). ck_gh E 4%nat (bv_unsigned (getr R0 19%bv)). ck_gh E 5%nat (bv_unsigned (getr R0 20%bv)). ck_gh E 6%nat (bv_unsigned (getr R0 21%bv)).
    ck_gh E 7%nat (bv_unsigned (getr R0 22%bv)). ck_gh E 8%nat q. ck_gh E 9%nat (bv_unsigned (getr R0 23%bv)).
    unfold know_ok, GA.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6. + ck_kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7.
    + ck_kw64 (sp1 - 64) (bv_unsigned (getr R0 22%bv)) F8. + ck_kw64 (sp1 - 72) (bv_unsigned (getr R0 23%bv)) F9.
    + e_range. + ck_kw64 (P + 200) q C200.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8. ck_reg E (9%bv : reg) H9. ck_reg E (18%bv : reg) H18. ck_gh E 8%nat q.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 10)%nat) by (change 10%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx GA.cp1) with 74%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'. pose proof (TK.frame_nil _ _ _ _ _ _ HLF eq_refl) as EQ. subst M'.
    (ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]); ck_probes HLF PF.
    + destruct PF as (PF & _). ck_w2z PF. apply RK.w_inj in PF; [|lia|lia].
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
      apply (CK.ret_leaf fx' R' _ M model K rav ret_sw Hh Hl R1 Hra).
      apply (Kret PF fx' R' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 KO7].
      apply (same_of_gh R0 R' (fun j => ev E' (64 + j)) 9%nat); [tk_reg HLF (8%bv : reg); reflexivity | tk_reg HLF (9%bv : reg); reflexivity | tk_reg HLF (18%bv : reg); reflexivity | tk_reg HLF (19%bv : reg); reflexivity
          | tk_reg HLF (20%bv : reg); reflexivity | tk_reg HLF (21%bv : reg); reflexivity | tk_reg HLF (22%bv : reg); reflexivity | tk_reg HLF (23%bv : reg); reflexivity
          | exact (GH 1%nat _ eq_refl) | exact (GH 2%nat _ eq_refl) | exact (GH 3%nat _ eq_refl) | exact (GH 4%nat _ eq_refl) | exact (GH 5%nat _ eq_refl) | exact (GH 6%nat _ eq_refl) | exact (GH 7%nat _ eq_refl) | exact (GH 9%nat _ eq_refl)].
    + destruct PF as (PF & _). ck_w2z PF. assert (NE : q <> e) by (intros X; apply PF; rewrite X; reflexivity).
      apply (Kloop NE fx' R' Hfp'); [tk_lin HLF (2%bv : reg) | | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 KO7].
      unfold sw_live, SWT.MASK. repeat split; [tk_lin HLF (8%bv : reg) | tk_lin HLF (9%bv : reg) | tk_lin HLF (18%bv : reg) | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | sw_reg HLF (21%bv : reg) | tk_lin HLF (22%bv : reg) | tk_lin HLF (23%bv : reg)].
Qed.

(* [comment removed for export] *)
Lemma s_sw_r_pop : forall (fx : FPState) R M model K sp1 P e q x rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> CK.spok sp1 -> sw_live R P e -> getr R 10%bv = Z_to_bv 64 x ->
  2 ^ 40 <= P <= 2 ^ 47 - 272 -> 0 <= e < 2 ^ 64 -> 0 <= q < 2 ^ 64 -> 0 <= x < 256 -> L5.u64_at RSEGS M (P + 200) q -> L5.defined M (P + 208) 1 -> sw_frame M sp1 rav R0 -> L5.ra_ok rav -> sp1 <= P ->
  (q = e -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s06 R0 R' -> TK.keepsR KO7 R R' -> L5.u8_at RSEGS M' (P + 208) x ->
      TK.samem (fun a => ~ (P + 208 <= a < P + 209)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  (q <> e -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> sw_live R' P e -> getr R' 10%bv = Z_to_bv 64 q -> TK.keepsR KO7 R R' -> L5.u8_at RSEGS M' (P + 208) x ->
      TK.samem (fun a => ~ (P + 208 <= a < P + 209)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' SWT.LOOP M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R SWT.R_POP M model) K.
Proof.
  intros fx R M model K sp1 P e q x rav R0 Hh Hl Hfp H2 [Hsp Hal] (H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23) H10 HP He Hq Hx C200 D208 (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9) Hra J1 Kret Kloop.
  change SWT.R_POP with (CC.cp_pc GA.cp2). unfold SWT.MASK in H23.
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun y : reg => bv_unsigned_in_range _ (getr R0 y)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20. pose proof (RG 21%bv) as G21. pose proof (RG 22%bv) as G22.
  pose proof (RG 23%bv) as G23.
  set (gl := ghf rav R0 [q; bv_unsigned (getr R0 23%bv)]).
  ck_open FPM GA.cp2 (GA.plans 2%nat _ eq_refl) (-80) gl (fun _ : nat => @nil byte) [(19%nat, 28); (20%nat, 10); (21%nat, -1); (22%nat, 32); (23%nat, 4294977024)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_reg E (8%bv : reg) H8. ck_reg E (9%bv : reg) H9. ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 2%nat (bv_unsigned (getr R0 9%bv)).
    ck_gh E 3%nat (bv_unsigned (getr R0 18%bv)). ck_gh E 4%nat (bv_unsigned (getr R0 19%bv)). ck_gh E 5%nat (bv_unsigned (getr R0 20%bv)). ck_gh E 6%nat (bv_unsigned (getr R0 21%bv)).
    ck_gh E 7%nat (bv_unsigned (getr R0 22%bv)). ck_gh E 8%nat q. ck_gh E 9%nat (bv_unsigned (getr R0 23%bv)).
    unfold know_ok, GA.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6. + ck_kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7.
    + ck_kw64 (sp1 - 64) (bv_unsigned (getr R0 22%bv)) F8. + ck_kw64 (sp1 - 72) (bv_unsigned (getr R0 23%bv)) F9.
    + e_range. + e_range. + ck_kw64 (P + 200) q C200. + e_unk. + e_wr. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8. ck_reg E (9%bv : reg) H9. ck_reg E (18%bv : reg) H18. ck_reg E (10%bv : reg) H10. ck_gh E 8%nat q.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 10)%nat) by (change 10%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx GA.cp2) with 74%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (P + 208 <= a < P + 209)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk1; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    (ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]); ck_probes HLF PF;
      (assert (C208' : L5.u8_at RSEGS M' (P + 208) x) by (ck_cell8 HLF (EVar 40) 208 (EVar 42); ck_atom)).
    + destruct PF as (PF & _). ck_w2z PF. apply RK.w_inj in PF; [|lia|lia].
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
      apply (CK.ret_leaf fx' R' _ M' model K rav ret_sw Hh Hl R1 Hra).
      apply (Kret PF fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 KO7 | exact C208' | exact FRM | exact MG].
      apply (same_of_gh R0 R' (fun j => ev E' (64 + j)) 9%nat); [tk_reg HLF (8%bv : reg); reflexivity | tk_reg HLF (9%bv : reg); reflexivity | tk_reg HLF (18%bv : reg); reflexivity | tk_reg HLF (19%bv : reg); reflexivity
          | tk_reg HLF (20%bv : reg); reflexivity | tk_reg HLF (21%bv : reg); reflexivity | tk_reg HLF (22%bv : reg); reflexivity | tk_reg HLF (23%bv : reg); reflexivity
          | exact (GH 1%nat _ eq_refl) | exact (GH 2%nat _ eq_refl) | exact (GH 3%nat _ eq_refl) | exact (GH 4%nat _ eq_refl) | exact (GH 5%nat _ eq_refl) | exact (GH 6%nat _ eq_refl) | exact (GH 7%nat _ eq_refl) | exact (GH 9%nat _ eq_refl)].
    + destruct PF as (PF & _). ck_w2z PF. assert (NE : q <> e) by (intros X; apply PF; rewrite X; reflexivity).
      apply (Kloop NE fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 KO7 | exact C208' | exact FRM | exact MG].
      unfold sw_live, SWT.MASK. repeat split; [tk_lin HLF (8%bv : reg) | tk_lin HLF (9%bv : reg) | tk_lin HLF (18%bv : reg) | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | sw_reg HLF (21%bv : reg) | tk_lin HLF (22%bv : reg) | tk_lin HLF (23%bv : reg)].
Qed.
End S.
End SWS.
