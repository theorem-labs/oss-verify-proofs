(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ChunkKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_chunk_a_csrc_u Cut_chunk_b_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CKT.
Definition FB_R_XSGETN : Z := 0x3c2e8.
Definition SRC_R_FILL : Z := 0x3c144.
Definition RC_R_SRC : Z := 0x3bfb4.
Definition RC_R_DETECT : Z := 0x3bfe0.
Definition RC_R_SETEC : Z := 0x3bff8.
Definition RC_RET : Z := 0x3c020.
Definition DEPTH : Z := 96.
Definition FRAME : Z := 48.
End CKT.

Module CS.
Module GA := Cut_chunk_a_csrc_u.  Module GB := Cut_chunk_b_csrc_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ret_rc : CL.is_ret_at RSEGS CKT.RC_RET. Proof. CL.solve_is_ret. Qed.

Definition KO : list nat := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Definition rc_live (R : bvmap 5 word) (Rr E : Z) : Prop := getr R 18%bv = Z_to_bv 64 Rr /\ getr R 19%bv = Z_to_bv 64 E.
Definition rc_live2 (R : bvmap 5 word) (Rr E k p : Z) : Prop := rc_live R Rr E /\ getr R 8%bv = Z_to_bv 64 k /\ getr R 9%bv = Z_to_bv 64 p.
Definition fb_live (R : bvmap 5 word) (Rr E : Z) : Prop := getr R 8%bv = Z_to_bv 64 Rr /\ getr R 9%bv = Z_to_bv 64 16384 /\ getr R 19%bv = Z_to_bv 64 E.
Definition same_s03 (R0 R' : bvmap 5 word) : Prop :=
  getr R' 8%bv = getr R0 8%bv /\ getr R' 9%bv = getr R0 9%bv /\ getr R' 18%bv = getr R0 18%bv /\ getr R' 19%bv = getr R0 19%bv.

Definition rc_frame (M : mem) (sp1 rav : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp1 - 8) rav /\ L5.u64_at RSEGS M (sp1 - 16) (bv_unsigned (getr R0 8%bv)) /\ L5.u64_at RSEGS M (sp1 - 24) (bv_unsigned (getr R0 9%bv)) /\
  L5.u64_at RSEGS M (sp1 - 32) (bv_unsigned (getr R0 18%bv)) /\ L5.u64_at RSEGS M (sp1 - 40) (bv_unsigned (getr R0 19%bv)).

Definition fb_frames (M : mem) (sp1 rav : Z) (R0 : bvmap 5 word) (E Rr : Z) : Prop :=
  L5.u64_at RSEGS M (sp1 - 96) Rr /\ L5.u64_at RSEGS M (sp1 - 88) (bv_unsigned (getr R0 9%bv)) /\ L5.u64_at RSEGS M (sp1 - 80) Rr /\ L5.u64_at RSEGS M (sp1 - 72) CKT.SRC_R_FILL /\
  L5.u64_at RSEGS M (sp1 - 64) (bv_unsigned (getr R0 8%bv)) /\ L5.u64_at RSEGS M (sp1 - 56) CKT.RC_R_SRC /\ rc_frame M sp1 rav R0.

Definition src_cells (M : mem) (Rr IS : Z) : Prop :=
  L5.u64_at RSEGS M (Rr + 240) IS /\ L5.u64_at RSEGS M (Rr + 248) (IS + 16) /\ L5.u64_at RSEGS M IS PML.VT_ISS /\ L5.u64_at RSEGS M (IS + 16) PML.VT_STRINGBUF.

Lemma rc_frame_x : forall (K : Z -> Prop) (M M' : mem) sp1 rav R0, TK.samem K M M' -> 2 ^ 40 <= sp1 <= 2 ^ 47 -> (forall i, sp1 - 48 <= i < sp1 -> K i) ->
  rc_frame M sp1 rav R0 -> rc_frame M' sp1 rav R0.
Proof.
  intros K M M' sp1 rav R0 AG Hsp HK (F1 & F2 & F3 & F4 & F5). unfold rc_frame.
  repeat split; (eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]).
Qed.
Lemma fb_frames_x : forall (K : Z -> Prop) (M M' : mem) sp1 rav R0 E Rr, TK.samem K M M' -> 2 ^ 40 <= sp1 <= 2 ^ 47 -> (forall i, sp1 - 96 <= i < sp1 -> K i) ->
  fb_frames M sp1 rav R0 E Rr -> fb_frames M' sp1 rav R0 E Rr.
Proof.
  intros K M M' sp1 rav R0 E Rr AG Hsp HK (F1 & F2 & F3 & F4 & F5 & F6 & F7). unfold fb_frames.
  split; [eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]|].
  split; [eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]|].
  split; [eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]|].
  split; [eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]|].
  split; [eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]|].
  split; [eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]|].
  apply (rc_frame_x K M M' sp1 rav R0 AG Hsp); [intros i Hi; apply HK; lia | exact F7].
Qed.
Lemma src_cells_x : forall (K : Z -> Prop) (M M' : mem) Rr IS, TK.samem K M M' -> 2 ^ 40 <= Rr <= 2 ^ 47 -> 2 ^ 40 <= IS <= 2 ^ 47 ->
  (forall i, Rr + 240 <= i < Rr + 256 -> K i) -> (forall i, IS <= i < IS + 24 -> K i) -> src_cells M Rr IS -> src_cells M' Rr IS.
Proof.
  intros K M M' Rr IS AG HR HI K1 K2 (C1 & C2 & C3 & C4). unfold src_cells.
  split; [eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply K1; lia | assumption]|].
  split; [eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply K1; lia | assumption]|].
  split; [eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply K2; lia | assumption]|].
  eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply K2; lia | assumption].
Qed.

Lemma rc_live_rp : forall R R' Rr E, regs_preserved R R' -> rc_live R Rr E -> rc_live R' Rr E.
Proof. intros R R' Rr E RP [H1 H2]. split; [rewrite (RP 18%bv ltac:(ck_in)); exact H1 | rewrite (RP 19%bv ltac:(ck_in)); exact H2]. Qed.
Lemma rc_live2_rp : forall R R' Rr E k p, regs_preserved R R' -> rc_live2 R Rr E k p -> rc_live2 R' Rr E k p.
Proof.
  intros R R' Rr E k p RP (H1 & H2 & H3). split; [exact (rc_live_rp _ _ _ _ RP H1)|].
  split; [rewrite (RP 8%bv ltac:(ck_in)); exact H2 | rewrite (RP 9%bv ltac:(ck_in)); exact H3].
Qed.
Lemma fb_live_rp : forall R R' Rr {E}, regs_preserved R R' -> fb_live R Rr E -> fb_live R' Rr E.
Proof.
  intros R R' Rr E RP (H1 & H2 & H3).
  split; [rewrite (RP 8%bv ltac:(ck_in)); exact H1|]. split; [rewrite (RP 9%bv ltac:(ck_in)); exact H2 | rewrite (RP 19%bv ltac:(ck_in)); exact H3].
Qed.
Lemma ko_rp : forall R R', regs_preserved R R' -> TK.keepsR KO R R'.
Proof. intros R R' RP. apply TK.keepsR_preserved; [exact RP|]. intros q Hq. unfold KO in Hq. unfold callee_saved_idx. cbn [In] in *. intuition (subst; cbn; tauto). Qed.
Lemma sp_rp : forall (R R' : bvmap 5 word), regs_preserved R R' -> getr R' 2%bv = getr R 2%bv.
Proof. intros R R' RP. apply RP. ck_in. Qed.

Lemma rp_final : forall R0 R' : bvmap 5 word, getr R' 2%bv = getr R0 2%bv -> same_s03 R0 R' -> TK.keepsR KO R0 R' -> regs_preserved R0 R'.
Proof.
  intros R0 R' H2 (Q8 & Q9 & Q18 & Q19) HK. apply CK.rp_of_keeps; [exact H2|]. intros q Hq. unfold CK.CSR in Hq. cbn [In] in Hq.
  assert (QQ : forall m : nat, ridx q = m -> q = Z_to_bv 5 (Z.of_nat m)) by (intros m <-; symmetry; apply ridx_roundtrip).
  assert (HK' : In (ridx q) KO -> getr R' q = getr R0 q) by (apply HK). unfold KO in HK'. cbn [In] in HK'.
  destruct Hq as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|Hq]]]]]].
  - apply HK'. left. exact Hq.
  - apply HK'. right. left. exact Hq.
  - rewrite (QQ _ (eq_sym Hq)). exact Q8.
  - rewrite (QQ _ (eq_sym Hq)). exact Q9.
  - rewrite (QQ _ (eq_sym Hq)). exact Q18.
  - rewrite (QQ _ (eq_sym Hq)). exact Q19.
  - apply HK'. right. right. exact Hq.
Qed.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma s_rc_entry : forall (fx : FPState) R M model K sp1 Rr E IS ch rdb de bofb rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 Rr -> getr R 11%bv = Z_to_bv 64 E ->
  2 ^ 40 <= Rr <= 2 ^ 47 -> 2 ^ 40 <= IS <= 2 ^ 47 -> IS mod 8 = 0 -> 0 <= E < 2 ^ 64 -> 2 ^ 12 <= ch <= 2 ^ 47 -> (rdb = 0 \/ rdb = 2) -> 0 <= de < 2 ^ 64 -> 0 <= bofb <= 1 ->
  src_cells M Rr IS -> L5.u8_at RSEGS M (IS + 152) rdb -> PML.img_ro M ->
  L5.u64_at RSEGS M (Rr + 288) 0 -> L5.u64_at RSEGS M (Rr + 264) ch -> L5.u64_at RSEGS M (Rr + 272) 16384 -> L5.u64_at RSEGS M (Rr + 280) de -> L5.u8_at RSEGS M (Rr + 296) bofb ->
  L5.defined M (Rr + 256) 8 -> L5.defined M (Rr + 280) 16 -> L5.defined M (sp1 - 96) 96 ->
  sp1 <= Rr -> sp1 <= IS -> (Rr + 288 <= IS \/ IS + 272 <= Rr + 280) ->
  (Z.land rdb 2 <> 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 10%bv = Z_to_bv 64 0 -> getr R' 11%bv = Z_to_bv 64 0 ->
      TK.keepsR CK.CSR R R' -> L5.u64_at RSEGS M' (Rr + 280) de -> L5.u64_at RSEGS M' (Rr + 288) 0 ->
      TK.samem (fun a => ~ (sp1 - 96 <= a < sp1) /\ ~ (Rr + 256 <= a < Rr + 264) /\ ~ (Rr + 280 <= a < Rr + 296)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  (Z.land rdb 2 = 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 96) -> getr R' 1%bv = Z_to_bv 64 CKT.FB_R_XSGETN ->
      getr R' 10%bv = Z_to_bv 64 (IS + 16) -> getr R' 11%bv = Z_to_bv 64 ch -> getr R' 12%bv = Z_to_bv 64 16384 ->
      fb_live R' Rr E -> fb_frames M' sp1 rav R E Rr -> L5.u64_at RSEGS M' (Rr + 280) ch -> TK.keepsR KO R R' ->
      TK.samem (fun a => ~ (sp1 - 96 <= a < sp1) /\ ~ (Rr + 256 <= a < Rr + 264) /\ ~ (Rr + 280 <= a < Rr + 296)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_XSGETN M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_READ_CHUNK M model) K.
Proof.
  intros fx R M model K sp1 Rr E IS ch rdb de bofb rav Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 HRr HIS HISa HE Hch Hrdb Hde Hbof (C240 & C248 & Cvi & Cvs) Crd RO
         C288 C264 C272 C280 C296 D256 D280 DF J1 J2 J3 Keof Kx.
  change PML.PC_READ_CHUNK with (CC.cp_pc GA.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  ck_open FPM GA.cp0 (GA.plans 0%nat _ eq_refl) 0 [IS; rdb; ch; de; bofb] (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E0 (10%bv : reg) H10. ck_gh E0 0%nat IS. ck_gh E0 1%nat rdb. ck_gh E0 2%nat ch. ck_gh E0 3%nat de. ck_gh E0 4%nat bofb.
    unfold know_ok, GA.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range.
    + ck_kw64 (Rr + 240) IS C240. + ck_kw64 (Rr + 248) (IS + 16) C248. + unfold PML.VT_ISS in Cvi. ck_kw64 IS 792064 Cvi. + unfold PML.VT_STRINGBUF in Cvs. ck_kw64 (IS + 16) 791824 Cvs.
    + ck_kw8 (IS + 152) rdb Crd. + tk_kimg RO. + e_range. + e_align HISa. + e_range.
    + ck_kw64 (Rr + 288) 0 C288. + ck_kw64 (Rr + 264) ch C264. + e_range. + ck_kw64 (Rr + 272) 16384 C272. + ck_kw64 (Rr + 280) de C280. + e_wr. + e_unk. + e_wr.
    + ck_kw8 (Rr + 296) bofb C296. + e_range. + e_disj. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E0 (10%bv : reg) H10. ck_reg E0 (11%bv : reg) H11. ck_reg E0 (1%bv : reg) H1. ck_gh E0 0%nat IS. ck_gh E0 1%nat rdb. ck_gh E0 2%nat ch. ck_gh E0 3%nat de.
    ck_gh E0 4%nat bofb.
    ck_leaf Hag E'.
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    (ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]]); ck_probes HLF PF.
    +
      destruct PF as (PF & _). ck_w2z PF. rewrite RK.and_lit in PF by lia. apply RK.w_inj in PF; [|apply RK.land_range; lia | lia].
      apply (Kx PF fx' R' M' Hfp').
      * tk_lin HLF (2%bv : reg). * unfold CKT.FB_R_XSGETN. tk_lin HLF (1%bv : reg). * tk_lin HLF (10%bv : reg). * tk_lin HLF (11%bv : reg). * tk_lin HLF (12%bv : reg).
      * split; [tk_lin HLF (8%bv : reg)|]. split; [tk_lin HLF (9%bv : reg) | tk_lin HLF (19%bv : reg)].
      * unfold fb_frames, rc_frame, CKT.SRC_R_FILL, CKT.RC_R_SRC. repeat split.
        -- ck_cell64 HLF (EVar 2) (-96) (EVar 42). ck_atom.
        -- ck_saved HLF Hag64 (-88) 41%nat (9%bv : reg).
        -- ck_cell64 HLF (EVar 2) (-80) (EVar 42). ck_atom.
        -- ck_cell64 HLF (EVar 2) (-72) (ELit 246084). reflexivity.
        -- ck_saved HLF Hag64 (-64) 40%nat (8%bv : reg).
        -- ck_cell64 HLF (EVar 2) (-56) (ELit 245684). reflexivity.
        -- ck_cell64 HLF (EVar 2) (-8) (EVar 33). ck_atom.
        -- ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg).
        -- ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg).
        -- ck_saved HLF Hag64 (-32) 50%nat (18%bv : reg).
        -- ck_saved HLF Hag64 (-40) 51%nat (19%bv : reg).
      * ck_cell64 HLF (EVar 42) 280 (EVar 66). ck_atom.
      * ck_keeps HLF Hag64 KO.
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha (Hk1 & Hk2 & Hk3). cbn [CC.cp_F]. tk_outside.
      * exact MG.
    +
      exfalso. destruct PF as (P1 & P2 & _). ck_w2z P1. ck_w2z P2.
      destruct Hrdb as [X | X]; subst rdb.
      * apply P1. apply bv_eq. vm_compute. reflexivity.
      * apply (f_equal bv_unsigned) in P2. vm_compute in P2. discriminate P2.
    +
      destruct PF as (P1 & _). ck_w2z P1.
      assert (NE : Z.land rdb 2 <> 0).
      { destruct Hrdb as [X | X]; subst rdb.
        - exfalso. apply P1. apply bv_eq. vm_compute. reflexivity.
        - intros Y. vm_compute in Y. discriminate Y. }
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (rewrite (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ [1%nat] 1%bv HLF eq_refl Hag64 ltac:(ck_in)); exact H1).
      apply (CK.ret_leaf fx' R' _ M' model K rav ret_rc Hh Hl R1 Hra).
      apply (Keof NE fx' R' M' Hfp').
      * tk_lin HLF (2%bv : reg). * tk_lin HLF (10%bv : reg). * tk_lin HLF (11%bv : reg). * ck_keeps HLF Hag64 CK.CSR.
      * ck_cell64 HLF (EVar 42) 280 (EVar 67). ck_atom.
      * ck_cell64 HLF (EVar 42) 288 (ELit 0). reflexivity.
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha (Hk1 & Hk2 & Hk3). cbn [CC.cp_F]. tk_outside.
      * exact MG.
Qed.

Definition fb_post (M M' : mem) (sp1 Rr IS ch k0 : Z) : Prop :=
  L5.u64_at RSEGS M' (Rr + 280) (ch + k0) /\ L5.u64_at RSEGS M' (Rr + 288) 0 /\ L5.u32_at RSEGS M' (IS + 152) (if k0 <? 16384 then 2 else 0) /\
  TK.samem (fun a => ~ (sp1 - 96 <= a < sp1) /\ ~ (IS + 152 <= a < IS + 156) /\ ~ (Rr + 256 <= a < Rr + 264) /\ ~ (Rr + 280 <= a < Rr + 296)) M M' /\ mem_grows M M'.

Lemma s_fb_r_xsgetn : forall (fx : FPState) R M model K sp1 Rr E IS ch k0 bofb rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 (sp1 - 96) -> CK.spok sp1 -> getr R 10%bv = Z_to_bv 64 k0 -> 0 <= k0 <= 16384 -> fb_live R Rr E ->
  2 ^ 40 <= Rr <= 2 ^ 47 -> 2 ^ 40 <= IS <= 2 ^ 47 -> IS mod 8 = 0 -> 0 <= E < 2 ^ 64 -> 2 ^ 12 <= ch <= 2 ^ 47 -> 0 <= bofb <= 1 ->
  fb_frames M sp1 rav R0 E Rr -> L5.ra_ok rav -> L5.defined M (sp1 - 96) 96 ->
  src_cells M Rr IS -> L5.u32_at RSEGS M (IS + 152) 0 -> L5.u32_at RSEGS M (IS + 156) 0 -> L5.u64_at RSEGS M (IS + 160) (IS + 16) -> L5.defined M (IS + 152) 4 -> PML.img_ro M ->
  L5.defined M (Rr + 256) 8 -> L5.u64_at RSEGS M (Rr + 280) ch -> L5.u8_at RSEGS M (Rr + 296) bofb -> L5.defined M (Rr + 280) 16 ->
  sp1 <= Rr -> sp1 <= IS -> (Rr + 320 <= IS \/ IS + 272 <= Rr) ->
  ((k0 = 0 \/ bofb = 0) -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 10%bv = Z_to_bv 64 ch -> getr R' 11%bv = Z_to_bv 64 k0 ->
      same_s03 R0 R' -> TK.keepsR KO R R' -> fb_post M M' sp1 Rr IS ch k0 ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  (0 < k0 -> bofb = 1 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 CKT.RC_R_DETECT ->
      getr R' 10%bv = Z_to_bv 64 ch -> getr R' 11%bv = Z_to_bv 64 k0 -> rc_live2 R' Rr E k0 ch -> rc_frame M' sp1 rav R0 -> TK.keepsR KO R R' -> fb_post M M' sp1 Rr IS ch k0 ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_DETECT_JSON M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R CKT.FB_R_XSGETN M model) K.
Proof.
  intros fx R M model K sp1 Rr E IS ch k0 bofb rav R0 Hh Hl Hfp H2 [Hsp Hal] H10 Hk0 (H8 & H9 & H19) HRr HIS HISa HE Hch Hbof
         (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11) Hra DF (C240 & C248 & Cvi & Cvs) C152 C156 C160 D152 RO D256 C280 C296 D280 J1 J2 J3 Kret Kdet.
  change CKT.FB_R_XSGETN with (CC.cp_pc GA.cp1).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19.
  set (gl := [IS; bofb; ch; E; bv_unsigned (getr R0 8%bv); rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv)]).
  ck_open FPM GA.cp1 (GA.plans 1%nat _ eq_refl) (-96) gl (fun _ : nat => @nil byte) [(9%nat, 16384)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_reg E0 (8%bv : reg) H8. ck_reg E0 (10%bv : reg) H10. ck_reg E0 (19%bv : reg) H19. ck_gh E0 0%nat IS. ck_gh E0 1%nat bofb. ck_gh E0 2%nat ch. ck_gh E0 3%nat E. ck_gh E0 4%nat (bv_unsigned (getr R0 8%bv)).
    ck_gh E0 5%nat rav. ck_gh E0 6%nat (bv_unsigned (getr R0 8%bv)). ck_gh E0 7%nat (bv_unsigned (getr R0 9%bv)). ck_gh E0 8%nat (bv_unsigned (getr R0 18%bv)). ck_gh E0 9%nat (bv_unsigned (getr R0 19%bv)).
    unfold CKT.SRC_R_FILL, CKT.RC_R_SRC in *.
    unfold know_ok, GA.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_wr. + e_range. + e_range.
    + ck_kw64 (sp1 - 96) Rr F1. + ck_kw64 (sp1 - 88) (bv_unsigned (getr R0 9%bv)) F2. + ck_kw64 (sp1 - 80) Rr F3. + ck_kw64 (sp1 - 72) 246084 F4. + ck_kw64 (sp1 - 64) (bv_unsigned (getr R0 8%bv)) F5. + ck_kw64 (sp1 - 56) 245684 F6.
    + ck_kw64 (sp1 - 8) rav F7. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F8. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F9. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F10.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F11.
    + ck_kw64 (Rr + 240) IS C240. + ck_kw64 (Rr + 248) (IS + 16) C248. + unfold PML.VT_ISS in Cvi. ck_kw64 IS 792064 Cvi. + unfold PML.VT_STRINGBUF in Cvs. ck_kw64 (IS + 16) 791824 Cvs.
    + ck_kw32 (IS + 152) 0 C152. + tk_kimg RO. + e_range. + e_align HISa.
    + ck_kw32 (IS + 156) 0 C156. + ck_kw64 (IS + 160) (IS + 16) C160. + e_wr.
    + e_unk. + e_wr. + ck_kw64 (Rr + 280) ch C280. + ck_kw8 (Rr + 296) bofb C296. + e_range. + e_wr. + e_range. + e_disj. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E0 (8%bv : reg) H8. ck_reg E0 (10%bv : reg) H10. ck_reg E0 (19%bv : reg) H19. ck_gh E0 0%nat IS. ck_gh E0 1%nat bofb. ck_gh E0 2%nat ch. ck_gh E0 3%nat E.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 10)%nat) by (change 10%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx GA.cp1) with 74%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 96 <= a < sp1) /\ ~ (IS + 152 <= a < IS + 156) /\ ~ (Rr + 256 <= a < Rr + 264) /\ ~ (Rr + 280 <= a < Rr + 296)) M M').
    { apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha (Hk1 & Hk2 & Hk3 & Hk4). cbn [CC.cp_F]. tk_outside. }
    assert (RETK : forall Rx, getr Rx 1%bv = Z_to_bv 64 rav -> srealizes RSEGS SCFG (@PML.cfg fx' Rx rav M' model) K -> srealizes RSEGS SCFG (@PML.cfg fx' Rx CKT.RC_RET M' model) K).
    { intros Rx R1 HK. exact (CK.ret_leaf fx' Rx _ M' model K rav ret_rc Hh Hl R1 Hra HK). }
    (ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]]]]); ck_paths HLF PF.
    +
      destruct PF as (P1 & _). ck_rlin P1. assert (K0 : k0 = 0) by lia.
      apply RETK; [tk_reg HLF (1%bv : reg); exact (GH 5%nat _ eq_refl)|].
      apply (Kret ltac:(left; exact K0) fx' R' M' Hfp').
      * tk_lin HLF (2%bv : reg). * tk_lin HLF (10%bv : reg). * rewrite K0. tk_lin HLF (11%bv : reg).
      * unfold same_s03. repeat split.
        -- tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 6%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 7%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 8%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 9%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * ck_keeps HLF Hag64 KO.
      * unfold fb_post. replace (if k0 <? 16384 then 2 else 0) with 2 by (destruct (Z.ltb_spec k0 16384); lia).
        split; [ck_cell64 HLF (EVar 40) 280 (EAlu ALU_ADD (EVar 42) (EVar 66)); ck_vlin|]. split; [ck_cell64 HLF (EVar 40) 288 (ELit 0); reflexivity|].
        split; [ck_cell32 HLF (EVar 64) 152 (ELit 2); reflexivity|]. split; [exact FRM | exact MG].
    +
      destruct PF as (P1 & _ & P3 & _). ck_rlin P1. ck_rlin P3. assert (K0 : 1 <= k0 <= 16383 /\ bofb = 0) by lia.
      apply RETK; [tk_reg HLF (1%bv : reg); exact (GH 5%nat _ eq_refl)|].
      apply (Kret ltac:(right; lia) fx' R' M' Hfp').
      * tk_lin HLF (2%bv : reg). * tk_lin HLF (10%bv : reg). * tk_lin HLF (11%bv : reg).
      * unfold same_s03. repeat split.
        -- tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 6%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 7%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 8%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 9%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * ck_keeps HLF Hag64 KO.
      * unfold fb_post. replace (if k0 <? 16384 then 2 else 0) with 2 by (destruct (Z.ltb_spec k0 16384); lia).
        split; [ck_cell64 HLF (EVar 40) 280 (EAlu ALU_ADD (EVar 42) (EVar 66)); ck_vlin|]. split; [ck_cell64 HLF (EVar 40) 288 (ELit 0); reflexivity|].
        split; [ck_cell32 HLF (EVar 64) 152 (ELit 2); reflexivity|]. split; [exact FRM | exact MG].
    +
      destruct PF as (P1 & _ & P3 & _). ck_rlin P1. ck_rlin P3. assert (K0 : 1 <= k0 <= 16383 /\ bofb = 1) by lia.
      apply (Kdet ltac:(lia) ltac:(lia) fx' R' M' Hfp').
      * tk_lin HLF (2%bv : reg). * unfold CKT.RC_R_DETECT. tk_lin HLF (1%bv : reg). * tk_lin HLF (10%bv : reg). * tk_lin HLF (11%bv : reg).
      * unfold rc_live2, rc_live. repeat split; [tk_lin HLF (18%bv : reg) | tk_lin HLF (19%bv : reg) | tk_lin HLF (8%bv : reg) | tk_lin HLF (9%bv : reg)].
      * unfold rc_frame. repeat split.
        -- ck_cell64 HLF (EVar 2) (-8) (EVar 69). cbn [edenot]. etransitivity; [exact (f_equal bv_unsigned (GH 5%nat _ eq_refl)) | apply u64_of_Z; lia].
        -- ck_cell64 HLF (EVar 2) (-16) (EVar 70). cbn [edenot]. etransitivity; [exact (f_equal bv_unsigned (GH 6%nat _ eq_refl)) | apply u64_of_Z; lia].
        -- ck_cell64 HLF (EVar 2) (-24) (EVar 71). cbn [edenot]. etransitivity; [exact (f_equal bv_unsigned (GH 7%nat _ eq_refl)) | apply u64_of_Z; lia].
        -- ck_cell64 HLF (EVar 2) (-32) (EVar 72). cbn [edenot]. etransitivity; [exact (f_equal bv_unsigned (GH 8%nat _ eq_refl)) | apply u64_of_Z; lia].
        -- ck_cell64 HLF (EVar 2) (-40) (EVar 73). cbn [edenot]. etransitivity; [exact (f_equal bv_unsigned (GH 9%nat _ eq_refl)) | apply u64_of_Z; lia].
      * ck_keeps HLF Hag64 KO.
      * unfold fb_post. replace (if k0 <? 16384 then 2 else 0) with 2 by (destruct (Z.ltb_spec k0 16384); lia).
        split; [ck_cell64 HLF (EVar 40) 280 (EAlu ALU_ADD (EVar 42) (EVar 66)); ck_vlin|]. split; [ck_cell64 HLF (EVar 40) 288 (ELit 0); reflexivity|].
        split; [ck_cell32 HLF (EVar 64) 152 (ELit 2); reflexivity|]. split; [exact FRM | exact MG].
    +
      destruct PF as (P1 & _ & P3 & _). ck_rlin P1. ck_rlin P3. assert (K0 : k0 = 16384 /\ bofb = 0) by lia. destruct K0 as [K0 B0].
      apply RETK; [tk_reg HLF (1%bv : reg); exact (GH 5%nat _ eq_refl)|].
      apply (Kret ltac:(right; lia) fx' R' M' Hfp').
      * tk_lin HLF (2%bv : reg). * tk_lin HLF (10%bv : reg). * rewrite K0. tk_lin HLF (11%bv : reg).
      * unfold same_s03. repeat split.
        -- tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 6%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 7%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 8%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 9%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * ck_keeps HLF Hag64 KO.
      * unfold fb_post. replace (if k0 <? 16384 then 2 else 0) with 0 by (destruct (Z.ltb_spec k0 16384); lia). rewrite K0.
        split; [ck_cell64 HLF (EVar 40) 280 (EAlu ALU_ADD (EVar 66) (ELit 16384)); ck_vlin|]. split; [ck_cell64 HLF (EVar 40) 288 (ELit 0); reflexivity|].
        split; [ck_cell32 HLF (EVar 64) 152 (ELit 0); reflexivity|]. split; [exact FRM | exact MG].
    +
      destruct PF as (P1 & _ & P3 & _). ck_rlin P1. ck_rlin P3. assert (K0 : k0 = 16384 /\ bofb = 1) by lia. destruct K0 as [K0 B0].
      apply (Kdet ltac:(lia) ltac:(lia) fx' R' M' Hfp').
      * tk_lin HLF (2%bv : reg). * unfold CKT.RC_R_DETECT. tk_lin HLF (1%bv : reg). * tk_lin HLF (10%bv : reg). * rewrite K0. tk_lin HLF (11%bv : reg).
      * unfold rc_live2, rc_live. rewrite K0. repeat split; [tk_lin HLF (18%bv : reg) | tk_lin HLF (19%bv : reg) | tk_lin HLF (8%bv : reg) | tk_lin HLF (9%bv : reg)].
      * unfold rc_frame. repeat split.
        -- ck_cell64 HLF (EVar 2) (-8) (EVar 69). cbn [edenot]. etransitivity; [exact (f_equal bv_unsigned (GH 5%nat _ eq_refl)) | apply u64_of_Z; lia].
        -- ck_cell64 HLF (EVar 2) (-16) (EVar 70). cbn [edenot]. etransitivity; [exact (f_equal bv_unsigned (GH 6%nat _ eq_refl)) | apply u64_of_Z; lia].
        -- ck_cell64 HLF (EVar 2) (-24) (EVar 71). cbn [edenot]. etransitivity; [exact (f_equal bv_unsigned (GH 7%nat _ eq_refl)) | apply u64_of_Z; lia].
        -- ck_cell64 HLF (EVar 2) (-32) (EVar 72). cbn [edenot]. etransitivity; [exact (f_equal bv_unsigned (GH 8%nat _ eq_refl)) | apply u64_of_Z; lia].
        -- ck_cell64 HLF (EVar 2) (-40) (EVar 73). cbn [edenot]. etransitivity; [exact (f_equal bv_unsigned (GH 9%nat _ eq_refl)) | apply u64_of_Z; lia].
      * ck_keeps HLF Hag64 KO.
      * unfold fb_post. replace (if k0 <? 16384 then 2 else 0) with 0 by (destruct (Z.ltb_spec k0 16384); lia). rewrite K0.
        split; [ck_cell64 HLF (EVar 40) 280 (EAlu ALU_ADD (EVar 66) (ELit 16384)); ck_vlin|]. split; [ck_cell64 HLF (EVar 40) 288 (ELit 0); reflexivity|].
        split; [ck_cell32 HLF (EVar 64) 152 (ELit 0); reflexivity|]. split; [exact FRM | exact MG].
Qed.

Lemma s_rc_r_detect : forall (fx : FPState) R M model K sp1 Rr E k0 p p' kind bofb rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> getr R 10%bv = Z_to_bv 64 p' -> getr R 11%bv = Z_to_bv 64 kind -> rc_live2 R Rr E k0 p ->
  2 ^ 40 <= Rr <= 2 ^ 47 -> 0 <= E < 2 ^ 64 -> 0 <= k0 <= 16384 -> 0 <= p -> p <= p' <= p + k0 -> p + k0 < 2 ^ 63 -> 0 <= kind < 2 ^ 64 ->
  rc_frame M sp1 rav R0 -> L5.ra_ok rav -> L5.u8_at RSEGS M (Rr + 296) bofb -> 0 <= bofb <= 1 -> L5.defined M (Rr + 296) 1 -> sp1 <= Rr ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 10%bv = Z_to_bv 64 p' -> getr R' 11%bv = Z_to_bv 64 (k0 + p - p') ->
      same_s03 R0 R' -> TK.keepsR KO R R' -> L5.u8_at RSEGS M' (Rr + 296) 0 -> TK.samem (fun a => ~ (Rr + 296 <= a < Rr + 297)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 CKT.RC_R_SETEC ->
      getr R' 10%bv = Z_to_bv 64 E -> getr R' 11%bv = Z_to_bv 64 30 -> TK.keepsR KO R R' -> L5.u8_at RSEGS M' (Rr + 296) bofb -> TK.samem (fun a => ~ (Rr + 296 <= a < Rr + 297)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SET_EC M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R CKT.RC_R_DETECT M model) K.
Proof.
  intros fx R M model K sp1 Rr E k0 p p' kind bofb rav R0 Hh Hl Hfp H2 [Hsp Hal] H10 H11 ((H18 & H19) & H8 & H9) HRr HE Hk0 Hp Hp' Hpk Hkind (F1 & F2 & F3 & F4 & F5) Hra C296 Hbof D296 J1 Kok Kbad.
  change CKT.RC_R_DETECT with (CC.cp_pc GA.cp2).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19.
  set (gl := [rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bofb]).
  ck_open FPM GA.cp2 (GA.plans 2%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E0 (18%bv : reg) H18. ck_gh E0 0%nat rav. ck_gh E0 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E0 2%nat (bv_unsigned (getr R0 9%bv)). ck_gh E0 3%nat (bv_unsigned (getr R0 18%bv)).
    ck_gh E0 4%nat (bv_unsigned (getr R0 19%bv)). ck_gh E0 5%nat bofb.
    unfold know_ok, GA.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5.
    + e_range. + ck_kw8 (Rr + 296) bofb C296. + e_range. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E0 (9%bv : reg) H9. ck_reg E0 (8%bv : reg) H8. ck_reg E0 (18%bv : reg) H18. ck_reg E0 (19%bv : reg) H19. ck_reg E0 (10%bv : reg) H10. ck_gh E0 5%nat bofb.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 6)%nat) by (change 6%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx GA.cp2) with 70%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    assert (FRM : TK.samem (fun a => ~ (Rr + 296 <= a < Rr + 297)) M M').
    { apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk1. cbn [CC.cp_F]. tk_outside. }
    ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]].
    +
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
      apply (CK.ret_leaf fx' R' _ M' model K rav ret_rc Hh Hl R1 Hra).
      apply (Kok fx' R' M' Hfp').
      * tk_lin HLF (2%bv : reg).
      * rewrite (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ [10%nat] 10%bv HLF eq_refl Hag64 ltac:(ck_in)). exact H10.
      * tk_lin HLF (11%bv : reg).
      * unfold same_s03. repeat split.
        -- tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * ck_keeps HLF Hag64 KO.
      * ck_cell8 HLF (EVar 50) 296 (ELit 0). reflexivity.
      * exact FRM. * exact MG.
    +
      apply (Kbad fx' R' M' Hfp').
      * tk_lin HLF (2%bv : reg). * unfold CKT.RC_R_SETEC. tk_lin HLF (1%bv : reg). * tk_lin HLF (10%bv : reg). * tk_lin HLF (11%bv : reg).
      * ck_keeps HLF Hag64 KO. * ck_cell8 HLF (EVar 50) 296 (EVar 69). ck_atom. * exact FRM. * exact MG.
Qed.

Lemma s_rc_r_setec : forall (fx : FPState) R M model K sp1 rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> rc_frame M sp1 rav R0 -> L5.ra_ok rav ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 10%bv = Z_to_bv 64 0 -> getr R' 11%bv = Z_to_bv 64 0 -> same_s03 R0 R' -> TK.keepsR KO R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R CKT.RC_R_SETEC M model) K.
Proof.
  intros fx R M model K sp1 rav R0 Hh Hl Hfp H2 [Hsp Hal] (F1 & F2 & F3 & F4 & F5) Hra Hcont.
  change CKT.RC_R_SETEC with (CC.cp_pc GB.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19.
  set (gl := [rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv)]).
  ck_open FPM GB.cp0 (GB.plans 0%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 2%nat (bv_unsigned (getr R0 9%bv)). ck_gh E 3%nat (bv_unsigned (getr R0 18%bv)). ck_gh E 4%nat (bv_unsigned (getr R0 19%bv)).
    unfold know_ok, GB.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 5)%nat) by (change 5%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx GB.cp0) with 69%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M model K rav ret_rc Hh Hl R1 Hra).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (10%bv : reg). + tk_lin HLF (11%bv : reg).
    + unfold same_s03. repeat split.
      * tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + ck_keeps HLF Hag64 KO.
Qed.
End S.
End CS.
