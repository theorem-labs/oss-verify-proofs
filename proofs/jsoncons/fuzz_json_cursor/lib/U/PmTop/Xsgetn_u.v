(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ReadBase_u ChunkKit_u ChunkBase_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_xsgetn_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module XS.
Module G := Cut_xsgetn_csrc_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition XS_R_MOVE : Z := 0x699b8.   Definition XS_RET : Z := 0x699ec.   Definition MEMMOVE : Z := 0xb7c98.
Lemma ret_xs : CL.is_ret_at RSEGS XS_RET. Proof. CL.solve_is_ret. Qed.

Definition KS7 : list nat := [3; 4; 23; 24; 25; 26; 27]%nat.

Definition xs_frame (M : mem) (sp1 rav : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp1 - 8) rav /\ L5.u64_at RSEGS M (sp1 - 16) (bv_unsigned (getr R0 8%bv)) /\ L5.u64_at RSEGS M (sp1 - 24) (bv_unsigned (getr R0 9%bv)) /\
  L5.u64_at RSEGS M (sp1 - 32) (bv_unsigned (getr R0 18%bv)) /\ L5.u64_at RSEGS M (sp1 - 40) (bv_unsigned (getr R0 19%bv)) /\ L5.u64_at RSEGS M (sp1 - 48) (bv_unsigned (getr R0 20%bv)) /\
  L5.u64_at RSEGS M (sp1 - 56) (bv_unsigned (getr R0 21%bv)) /\ L5.u64_at RSEGS M (sp1 - 64) (bv_unsigned (getr R0 22%bv)).
Definition same_s06 (R0 R' : bvmap 5 word) : Prop :=
  getr R' 8%bv = getr R0 8%bv /\ getr R' 9%bv = getr R0 9%bv /\ getr R' 18%bv = getr R0 18%bv /\ getr R' 19%bv = getr R0 19%bv /\ getr R' 20%bv = getr R0 20%bv /\
  getr R' 21%bv = getr R0 21%bv /\ getr R' 22%bv = getr R0 22%bv.

Definition sb_cells (M : mem) (sb g eg : Z) : Prop :=
  L5.u64_at RSEGS M sb PML.VT_STRINGBUF /\ L5.u64_at RSEGS M (sb + 24) g /\ L5.u64_at RSEGS M (sb + 32) eg /\ L5.u64_at RSEGS M (sb + 48) 0 /\
  L5.u64_at RSEGS M (sb + 88) eg /\ L5.u8_at RSEGS M (sb + 96) 8.

Lemma csr_sub : forall q, In q CK.CSR -> In q (KS7 ++ [8; 9; 18; 19; 20; 21; 22])%nat.
Proof. intros q H. unfold CK.CSR, KS7 in *. cbn [In app] in *. tauto. Qed.
Lemma ks7_sub : forall q, In q KS7 -> In q [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Proof. intros q H. unfold KS7 in *. cbn [In] in *. tauto. Qed.
Lemma xs_frame_x : forall (K : Z -> Prop) (M M' : mem) sp1 rav R0, TK.samem K M M' -> 2 ^ 40 <= sp1 <= 2 ^ 47 -> (forall i, sp1 - 64 <= i < sp1 -> K i) ->
  xs_frame M sp1 rav R0 -> xs_frame M' sp1 rav R0.
Proof.
  intros K M M' sp1 rav R0 AG Hsp HK (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). unfold xs_frame.
  repeat split; (eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]).
Qed.
Lemma sb_cells_x : forall (K : Z -> Prop) (M M' : mem) sb g eg, TK.samem K M M' -> 2 ^ 40 <= sb <= 2 ^ 47 -> (forall i, sb <= i < sb + 104 -> K i) ->
  sb_cells M sb g eg -> sb_cells M' sb g eg.
Proof.
  intros K M M' sb g eg AG Hsb HK (C0 & C24 & C32 & C48 & C88 & C96). unfold sb_cells.
  split; [eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | exact C0]|].
  split; [eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | exact C24]|].
  split; [eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | exact C32]|].
  split; [eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | exact C48]|].
  split; [eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | exact C88]|].
  eapply (TK.u8_samem K M M'); [exact AG | lia | apply HK; lia | exact C96].
Qed.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma s_xs_entry : forall (fx : FPState) R M model K sp1 sb dst g av rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav ->
  getr R 10%bv = Z_to_bv 64 sb -> getr R 11%bv = Z_to_bv 64 dst -> getr R 12%bv = Z_to_bv 64 16384 ->
  2 ^ 40 <= sb <= 2 ^ 47 -> 0 <= dst < 2 ^ 64 -> 2 ^ 12 <= g <= 2 ^ 47 -> 0 <= av <= 2 ^ 26 ->
  sb_cells M sb g (g + av) -> PML.img_ro M -> L5.defined M (sp1 - 80) 80 -> (sp1 <= sb \/ sb + 104 <= sp1 - 80) ->
  (av = 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 10%bv = Z_to_bv 64 0 ->
      TK.keepsR (KS7 ++ [8; 9; 18; 19; 20; 21; 22])%nat R R' -> TK.samem (fun a => ~ (sp1 - 80 <= a < sp1)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  (0 < av -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> getr R' 1%bv = Z_to_bv 64 XS_R_MOVE ->
      getr R' 10%bv = Z_to_bv 64 dst -> getr R' 11%bv = Z_to_bv 64 g -> getr R' 12%bv = Z_to_bv 64 (Z.min 16384 av) ->
      getr R' 8%bv = Z_to_bv 64 0 -> getr R' 9%bv = Z_to_bv 64 16384 -> getr R' 19%bv = Z_to_bv 64 sb -> getr R' 20%bv = Z_to_bv 64 (Z.min 16384 av) ->
      getr R' 22%bv = Z_to_bv 64 (2 ^ 64 - 1) ->
      TK.keepsR KS7 R R' -> xs_frame M' sp1 rav R -> TK.samem (fun a => ~ (sp1 - 80 <= a < sp1)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' MEMMOVE M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_XSGETN M model) K.
Proof.
  intros fx R M model K sp1 sb dst g av rav Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 H12 Hsb Hdst Hg Hav (C0 & C24 & C32 & C48 & C88 & C96) RO DF DJ Keof Kcopy.
  change PML.PC_XSGETN with (CC.cp_pc G.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  ck_open FPM G.cp0 (G.plans 0%nat _ eq_refl) 0 [g; av] (fun _ : nat => @nil byte) [(12%nat, 16384)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_reg E (10%bv : reg) H10. ck_gh E 0%nat g. ck_gh E 1%nat av.
    unfold know_ok, G.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range.
    + unfold PML.VT_STRINGBUF in C0. ck_kw64 sb 791824 C0. + ck_kw64 (sb + 24) g C24. + ck_kw64 (sb + 32) (g + av) C32. + ck_kw64 (sb + 48) 0 C48. + ck_kw64 (sb + 88) (g + av) C88.
    + ck_kw8 (sb + 96) 8 C96. + tk_kimg RO. + e_range. + e_range. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (1%bv : reg) H1. ck_gh E 0%nat g. ck_gh E 1%nat av.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 80 <= a < sp1)) M M') by (ck_frame HLF).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    assert (FRAME : xs_frame M' sp1 rav R -> True) by (intros _; exact I).
    (ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]]); ck_paths HLF PF.
    +
      destruct PF as (PF1 & _). ck_rlin PF1. assert (AV : 16384 < av) by lia. assert (MIN : Z.min 16384 av = 16384) by lia.
      apply (Kcopy ltac:(lia) fx' R' M' Hfp'); rewrite ?MIN.
      * tk_lin HLF (2%bv : reg). * unfold XS_R_MOVE. tk_lin HLF (1%bv : reg). * tk_lin HLF (10%bv : reg). * tk_lin HLF (11%bv : reg). * tk_lin HLF (12%bv : reg).
      * tk_lin HLF (8%bv : reg). * tk_lin HLF (9%bv : reg). * tk_lin HLF (19%bv : reg). * tk_lin HLF (20%bv : reg). * tk_reg HLF (22%bv : reg). reflexivity.
      * ck_keeps HLF Hag64 KS7.
      * unfold xs_frame. repeat split.
        -- ck_cell64 HLF (EVar 2) (-8) (EVar 33). ck_atom.
        -- ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg).
        -- ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg).
        -- ck_saved HLF Hag64 (-32) 50%nat (18%bv : reg).
        -- ck_saved HLF Hag64 (-40) 51%nat (19%bv : reg).
        -- ck_saved HLF Hag64 (-48) 52%nat (20%bv : reg).
        -- ck_saved HLF Hag64 (-56) 53%nat (21%bv : reg).
        -- ck_saved HLF Hag64 (-64) 54%nat (22%bv : reg).
      * exact FRM. * exact MG.
    +
      destruct PF as (PF1 & _). ck_rlin PF1. assert (AV : 1 <= av <= 16384) by lia. assert (MIN : Z.min 16384 av = av) by lia.
      apply (Kcopy ltac:(lia) fx' R' M' Hfp'); rewrite ?MIN.
      * tk_lin HLF (2%bv : reg). * unfold XS_R_MOVE. tk_lin HLF (1%bv : reg). * tk_lin HLF (10%bv : reg). * tk_lin HLF (11%bv : reg). * tk_lin HLF (12%bv : reg).
      * tk_lin HLF (8%bv : reg). * tk_lin HLF (9%bv : reg). * tk_lin HLF (19%bv : reg). * tk_lin HLF (20%bv : reg). * tk_reg HLF (22%bv : reg). reflexivity.
      * ck_keeps HLF Hag64 KS7.
      * unfold xs_frame. repeat split.
        -- ck_cell64 HLF (EVar 2) (-8) (EVar 33). ck_atom.
        -- ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg).
        -- ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg).
        -- ck_saved HLF Hag64 (-32) 50%nat (18%bv : reg).
        -- ck_saved HLF Hag64 (-40) 51%nat (19%bv : reg).
        -- ck_saved HLF Hag64 (-48) 52%nat (20%bv : reg).
        -- ck_saved HLF Hag64 (-56) 53%nat (21%bv : reg).
        -- ck_saved HLF Hag64 (-64) 54%nat (22%bv : reg).
      * exact FRM. * exact MG.
    +
      destruct PF as (PF1 & _). ck_rlin PF1. assert (AV : av = 0) by lia.
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (rewrite (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ [1%nat] 1%bv HLF eq_refl Hag64 ltac:(ck_in)); exact H1).
      apply (CK.ret_leaf fx' R' _ M' model K rav ret_xs Hh Hl R1 Hra).
      apply (Keof AV fx' R' M' Hfp').
      * tk_lin HLF (2%bv : reg). * tk_lin HLF (10%bv : reg). * ck_keeps HLF Hag64 (KS7 ++ [8; 9; 18; 19; 20; 21; 22])%nat. * exact FRM. * exact MG.
Qed.

Lemma s_xs_r_full : forall (fx : FPState) R M model K sp1 sb g rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 64) -> CK.spok sp1 ->
  getr R 8%bv = Z_to_bv 64 0 -> getr R 9%bv = Z_to_bv 64 16384 -> getr R 20%bv = Z_to_bv 64 16384 -> getr R 22%bv = Z_to_bv 64 18446744073709551615 -> getr R 19%bv = Z_to_bv 64 sb ->
  2 ^ 40 <= sb <= 2 ^ 47 -> 2 ^ 12 <= g <= 2 ^ 47 -> xs_frame M sp1 rav R0 -> L5.ra_ok rav -> L5.defined M (sp1 - 80) 80 ->
  L5.u64_at RSEGS M (sb + 24) g -> L5.defined M (sb + 24) 8 -> (sp1 <= sb \/ sb + 104 <= sp1 - 80) ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 10%bv = Z_to_bv 64 16384 -> same_s06 R0 R' -> TK.keepsR KS7 R R' ->
      L5.u64_at RSEGS M' (sb + 24) (g + 16384) -> TK.samem (fun a => ~ (sp1 - 80 <= a < sp1) /\ ~ (sb + 24 <= a < sb + 32)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R XS_R_MOVE M model) K.
Proof.
  intros fx R M model K sp1 sb g rav R0 Hh Hl Hfp H2 [Hsp Hal] H8 H9 H20 H22 H19 Hsb Hg (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8) Hra DF C24 D24 DJ Hcont.
  change XS_R_MOVE with (CC.cp_pc G.cp1).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20. pose proof (RG 21%bv) as G21. pose proof (RG 22%bv) as G22.
  set (gl := [g; 0; rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv);
              bv_unsigned (getr R0 21%bv); bv_unsigned (getr R0 22%bv)]).
  ck_open FPM G.cp1 (G.plans 1%nat _ eq_refl) (-64) gl (fun _ : nat => @nil byte) [(8%nat, 0); (9%nat, 16384); (20%nat, 16384); (22%nat, 18446744073709551615)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_reg E (19%bv : reg) H19. ck_gh E 0%nat g. ck_gh E 2%nat rav. ck_gh E 3%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 4%nat (bv_unsigned (getr R0 9%bv)). ck_gh E 5%nat (bv_unsigned (getr R0 18%bv)).
    ck_gh E 6%nat (bv_unsigned (getr R0 19%bv)). ck_gh E 7%nat (bv_unsigned (getr R0 20%bv)). ck_gh E 8%nat (bv_unsigned (getr R0 21%bv)). ck_gh E 9%nat (bv_unsigned (getr R0 22%bv)).
    unfold know_ok, G.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_wr. + e_unk.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6. + ck_kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7. + ck_kw64 (sp1 - 64) (bv_unsigned (getr R0 22%bv)) F8.
    + e_range. + ck_kw64 (sb + 24) g C24. + e_range. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (19%bv : reg) H19. ck_gh E 0%nat g.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 10)%nat) by (change 10%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx G.cp1) with 74%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 2%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_xs Hh Hl R1 Hra).
    apply (Hcont fx' R' M' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (10%bv : reg).
    + unfold same_s06. repeat split.
      * tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 5%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 6%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (20%bv : reg). etransitivity; [exact (GH 7%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (21%bv : reg). etransitivity; [exact (GH 8%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (22%bv : reg). etransitivity; [exact (GH 9%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + ck_keeps HLF Hag64 KS7.
    + ck_cell64 HLF (EVar 51) 24 (EAlu ALU_ADD (EVar 64) (ELit 16384)). ck_vlin.
    + apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Lemma s_xs_r_part : forall (fx : FPState) R M model K sp1 sb g cnt rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 64) -> CK.spok sp1 ->
  getr R 8%bv = Z_to_bv 64 0 -> getr R 9%bv = Z_to_bv 64 16384 -> getr R 20%bv = Z_to_bv 64 cnt -> 1 <= cnt <= 16383 -> getr R 22%bv = Z_to_bv 64 18446744073709551615 -> getr R 19%bv = Z_to_bv 64 sb ->
  2 ^ 40 <= sb <= 2 ^ 47 -> 2 ^ 12 <= g <= 2 ^ 47 -> xs_frame M sp1 rav R0 -> L5.ra_ok rav -> L5.defined M (sp1 - 80) 80 ->
  sb_cells M sb g (g + cnt) -> PML.img_ro M -> L5.defined M (sb + 24) 8 -> (sp1 <= sb \/ sb + 104 <= sp1 - 80) ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 10%bv = Z_to_bv 64 cnt -> same_s06 R0 R' -> TK.keepsR KS7 R R' ->
      L5.u64_at RSEGS M' (sb + 24) (g + cnt) -> TK.samem (fun a => ~ (sp1 - 80 <= a < sp1) /\ ~ (sb + 24 <= a < sb + 32)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R XS_R_MOVE M model) K.
Proof.
  intros fx R M model K sp1 sb g cnt rav R0 Hh Hl Hfp H2 [Hsp Hal] H8 H9 H20 Hcnt H22 H19 Hsb Hg (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8) Hra DF (C0 & C24 & C32 & C48 & C88 & C96) RO D24 DJ Hcont.
  change XS_R_MOVE with (CC.cp_pc G.cp2).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20. pose proof (RG 21%bv) as G21. pose proof (RG 22%bv) as G22.
  set (gl := [g; 0; rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv);
              bv_unsigned (getr R0 21%bv); bv_unsigned (getr R0 22%bv)]).
  ck_open FPM G.cp2 (G.plans 2%nat _ eq_refl) (-64) gl (fun _ : nat => @nil byte) [(8%nat, 0); (9%nat, 16384); (22%nat, 18446744073709551615)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_reg E (19%bv : reg) H19. ck_reg E (20%bv : reg) H20. ck_gh E 0%nat g. ck_gh E 2%nat rav. ck_gh E 3%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 4%nat (bv_unsigned (getr R0 9%bv)). ck_gh E 5%nat (bv_unsigned (getr R0 18%bv)).
    ck_gh E 6%nat (bv_unsigned (getr R0 19%bv)). ck_gh E 7%nat (bv_unsigned (getr R0 20%bv)). ck_gh E 8%nat (bv_unsigned (getr R0 21%bv)). ck_gh E 9%nat (bv_unsigned (getr R0 22%bv)).
    unfold know_ok, G.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_wr. + e_unk.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6. + ck_kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7. + ck_kw64 (sp1 - 64) (bv_unsigned (getr R0 22%bv)) F8.
    + e_range. + unfold PML.VT_STRINGBUF in C0. ck_kw64 sb 791824 C0. + ck_kw64 (sb + 24) g C24. + ck_kw64 (sb + 32) (g + cnt) C32. + ck_kw64 (sb + 48) 0 C48. + ck_kw64 (sb + 88) (g + cnt) C88.
    + ck_kw8 (sb + 96) 8 C96. + tk_kimg RO. + e_range. + e_range. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (19%bv : reg) H19. ck_reg E (20%bv : reg) H20. ck_gh E 0%nat g.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 10)%nat) by (change 10%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx G.cp2) with 74%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 2%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_xs Hh Hl R1 Hra).
    apply (Hcont fx' R' M' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (10%bv : reg).
    + unfold same_s06. repeat split.
      * tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 5%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 6%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (20%bv : reg). etransitivity; [exact (GH 7%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (21%bv : reg). etransitivity; [exact (GH 8%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (22%bv : reg). etransitivity; [exact (GH 9%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + ck_keeps HLF Hag64 KS7.
    + ck_cell64 HLF (EVar 51) 24 (EAlu ALU_ADD (EVar 52) (EVar 64)). ck_vlin.
    + apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Variable L : heap_layout.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis MEMMOVE_OK : CH2.copy1_spec L MEMMOVE.

Lemma ret_ok_move : Hoare.ret_ok (Z_to_bv 64 XS_R_MOVE).
Proof. apply Hoare.ret_ok_even. reflexivity. Qed.

Theorem xsgetn_ok : TPS.xsgetn_spec L.
Proof.
  intros sp r IS dst gp rdst rep fx R M model K Hh Hl HK0 Hfp (EN & A0 & A1 & A2 & ISRC & RO & Hn & OS & BR & DD & BLK) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). destruct OS as (O1 & O2 & O3). destruct BR as (B1 & B2 & B3 & B4 & B5).
  pose proof LAY as [Y1 _ _ _ _ _ Y7 Y8 _ _ _ _ _ _]. rewrite Y7, Y8 in B2. unfold TPS.XSGETN_SCR in *. unfold hl_ceil in *.
  pose proof ISRC as ISRC0. unfold PML.isrc_at in ISRC. cbv zeta in ISRC.
  destruct ISRC as (I0 & I16 & I24 & I32 & I40 & I48 & Ig & I56 & I64 & I72 & Is & I104 & I112 & I120 & Iio & Ird & Idef).
  set (D := PML.srep_data (IS + 80) rep) in *. set (n := Z.of_nat (length (PML.srep_chars rep))) in *.

  assert (TXT : 4096 <= D /\ D + n <= 2 ^ 47 /\ (dst + 16384 <= D \/ D + n <= dst) /\ (D + n <= sp - 96 \/ sp <= D) /\ L5.bytes_at RSEGS M D (PML.srep_chars rep) /\
                TK2.str_cov (fun a => ~ (sp - 80 <= a < sp) /\ ~ (dst <= a < dst + 16384) /\ ~ (IS + 40 <= a < IS + 48)) (IS + 80) rep).
  { subst D n. destruct rep as [s | cap p s]; cbn [PML.srep_data PML.srep_chars PML.str_at PML.srep_blocks] in *.
    - destruct Is as (L22 & _ & Bs & _). split; [lia|]. split; [lia|]. split; [left; lia|]. split; [right; lia|]. split; [exact Bs|].
      split; [intros i Hi; lia | exact I].
    - destruct Is as ((_ & _ & _ & _ & Bs & _) & _ & Lc). destruct (BLK (p, cap) (or_introl eq_refl)) as ((P1 & P2 & P3 & P4 & P5) & AP). cbn [fst snd] in *. unfold PML.apart in AP.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [left; lia|]. split; [exact Bs|].
      split; [intros i Hi; lia|]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
  destruct TXT as (T1 & T2 & T3 & T4 & TB & TC).
  set (av := D + n - gp). assert (Hav : 0 <= av <= 2 ^ 26) by (unfold av; lia).
  assert (SPOK : CK.spok sp) by (split; [lia | exact S1]).
  assert (SBC : sb_cells M (IS + 16) gp (gp + av)).
  { unfold sb_cells, av. replace (gp + (D + n - gp)) with (D + n) by lia.
    replace (IS + 16 + 24) with (IS + 40) by lia. replace (IS + 16 + 32) with (IS + 48) by lia. replace (IS + 16 + 48) with (IS + 64) by lia.
    replace (IS + 16 + 88) with (IS + 104) by lia. replace (IS + 16 + 96) with (IS + 112) by lia.
    split; [exact I16|]. split; [exact I40|]. split; [exact I48|]. split; [exact I64|]. split; [exact I104|]. apply RB.u32_u8_low; [lia | lia | lia | exact I112]. }
  set (KA := fun a : Z => ~ (sp - 80 <= a < sp) /\ ~ (dst <= a < dst + 16384) /\ ~ (IS + 40 <= a < IS + 48)).
  assert (FIN : forall (fx' : FPState) R' M' k, PML.fp_ok fx' -> k = Z.min 16384 av -> getr R' 10%bv = Z_to_bv 64 k -> getr R' 2%bv = Z_to_bv 64 sp -> TK.keepsR CK.CSR R R' ->
                  TK.samem KA M M' -> mem_grows M M' -> L5.u64_at RSEGS M' (IS + 40) (gp + k) -> srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model) K).
  { intros fx' R' M' k Hfp' Hk H10' H2' KR AG MG G'.
    apply (Hcont fx' R' M' Hfp').
    - exists k. split; [exact H10'|]. split; [exact Hk|].
      apply (CB.isrc_at_setg KA M M' AG MG IS rep gp (gp + k) rdst); [lia | intros i Hi; unfold KA; lia | intros i Hi; unfold KA; lia | exact TC | exact G' | fold D n; lia | exact ISRC0].
    - apply CK.rp_of_keeps; [rewrite H2', Hsp; reflexivity | exact KR].
    - apply (CK.samem_frame_but KA _ M M' AG). intros a Ha. unfold KA.
      pose proof (Ha (sp - 96, 96) ltac:(ck_in)) as X1. pose proof (Ha (IS + 40, 8) ltac:(ck_in)) as X2. pose proof (Ha (dst, 16384) ltac:(ck_in)) as X3.
      unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    - exact MG. }
  apply (s_xs_entry fx R M model K sp (IS + 16) dst gp av r Hh Hl Hfp Hsp SPOK Hra Hrok A0 A1 A2 ltac:(lia) ltac:(lia) ltac:(lia) Hav SBC RO
           ltac:(eapply L5.defined_sub; [exact S5 | lia | lia]) ltac:(left; lia)).
  -   intros AV fx' R' M' Hfp' H2' H10' KR AG MG.
    apply (FIN fx' R' M' 0 Hfp' ltac:(lia) H10' H2').
    + apply (CK.keepsR_sub _ _ _ _ KR). exact csr_sub.
    + apply (TK.samem_weaken _ _ _ _ AG). unfold KA. tauto.
    + exact MG.
    + replace (gp + 0) with gp by lia. eapply (TK.u64_samem _ M M'); [exact AG | lia | intros i Hi; cbn beta; lia | exact I40].
  -   intros AV fx1 R1 M1 Hfp1 H2a H1a H10a H11a H12a H8a H9a H19a H20a H22a KR1 FR1 AG1 MG1.
    set (cnt := Z.min 16384 av) in *. assert (Hcnt : 1 <= cnt <= 16384 /\ cnt <= av) by (unfold cnt; lia).
    assert (TB1 : L5.bytes_at RSEGS M1 D (PML.srep_chars rep)).
    { apply (TK.bytes_samem _ M M1 D _ AG1); [lia | fold n; lia | intros i Hi; cbn beta; fold n in Hi; lia | exact TB]. }
    destruct (CK.rdn_of_bytes_sub M1 (PML.srep_chars rep) D gp (Z.to_nat cnt) ltac:(lia) ltac:(lia) ltac:(fold n; unfold av in Hcnt; lia) ltac:(fold n; lia) TB1) as (bs & Hbs & Lbs).
    assert (DD1 : L5.defined M1 dst 16384) by exact (L5.defined_grows _ _ _ _ MG1 DD).
    assert (ST1 : store_ok RSEGS M1 (Z_to_bv 64 dst) (length bs) = true).
    { pose proof (L5C.writable_of_defined RSEGS M1 dst 16384 DD1 ltac:(lia) ltac:(lia) 0 (length bs) ltac:(lia) ltac:(lia)) as W. rewrite Z.add_0_r in W. exact W. }
    destruct (MEMMOVE_OK fx1 M1 (Z_to_bv 64 dst) (Z_to_bv 64 gp) cnt bs R1 (Z_to_bv 64 XS_R_MOVE)) as (fx2 & R2 & Hms & Hkept & H10b);
      rewrite ?Y1, ?u64_of_Z by lia; try lia; try assumption; try exact ret_ok_move.
    { rewrite Lbs. exact Hbs. }
    rewrite Y1 in Hms. unfold PML.cfg. eapply L5.cps_of_msteps; [exact Hh | exact Hl | exact Hms |].
    pose proof (FPM _ _ _ _ _ _ _ _ Hms Hfp1) as Hfp2.
    set (M2 := wbytes M1 (Z_to_bv 64 dst) bs) in *.
    assert (AG2 : TK.samem (fun a => ~ (dst <= a < dst + 16384)) M1 M2).
    { apply (TK.samem_weaken _ _ _ _ (CK.wbytes_samem M1 dst bs ltac:(lia) ltac:(lia))). intros a Ha. lia. }
    assert (MG2 : mem_grows M1 M2) by apply CK.wbytes_grows.
    assert (AG02 : TK.samem (fun a => ~ (sp - 80 <= a < sp) /\ ~ (dst <= a < dst + 16384)) M M2) by (apply (CK.samem_weaken2 _ _ _ _ _ _ AG1 AG2); tauto).
    assert (KR2 : TK.keepsR [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat R1 R2) by (apply CK.keepsR_kept; [exact Hkept | reflexivity]).
    assert (H2b : getr R2 2%bv = Z_to_bv 64 (sp - 64)) by (rewrite (KR2 2%bv ltac:(ck_in)); exact H2a).
    assert (H8b : getr R2 8%bv = Z_to_bv 64 0) by (rewrite (KR2 8%bv ltac:(ck_in)); exact H8a).
    assert (H9b : getr R2 9%bv = Z_to_bv 64 16384) by (rewrite (KR2 9%bv ltac:(ck_in)); exact H9a).
    assert (H19b : getr R2 19%bv = Z_to_bv 64 (IS + 16)) by (rewrite (KR2 19%bv ltac:(ck_in)); exact H19a).
    assert (H20b : getr R2 20%bv = Z_to_bv 64 cnt) by (rewrite (KR2 20%bv ltac:(ck_in)); exact H20a).
    assert (H22b : getr R2 22%bv = Z_to_bv 64 18446744073709551615) by (rewrite (KR2 22%bv ltac:(ck_in)); exact H22a).
    assert (FR2 : xs_frame M2 sp r R) by (apply (xs_frame_x _ M1 M2 sp r R AG2); [lia | intros i Hi; lia | exact FR1]).
    assert (SBC2 : sb_cells M2 (IS + 16) gp (gp + av)) by (apply (sb_cells_x _ M M2 _ _ _ AG02); [lia | intros i Hi; lia | exact SBC]).
    assert (DF2 : L5.defined M2 (sp - 80) 80) by (apply (L5.defined_grows _ _ _ _ MG2), (L5.defined_grows _ _ _ _ MG1); eapply L5.defined_sub; [exact S5 | lia | lia]).
    assert (D24 : L5.defined M2 (IS + 16 + 24) 8) by (apply (L5.defined_grows _ _ _ _ MG2), (L5.defined_grows _ _ _ _ MG1); eapply L5.defined_sub; [exact Idef | lia | lia]).
    assert (KRF : forall R', TK.keepsR KS7 R2 R' -> same_s06 R R' -> TK.keepsR CK.CSR R R').
    { intros R' K7 (Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22) q Hq. unfold CK.CSR in Hq. cbn [In] in Hq.
      assert (QQ : forall m : nat, ridx q = m -> (m < 32)%nat -> q = Z_to_bv 5 (Z.of_nat m)) by (intros m <- _; symmetry; apply ridx_roundtrip).
      assert (K7' : In (ridx q) KS7 -> getr R' q = getr R q).
      { intros Hin. rewrite (K7 q Hin). rewrite (KR2 q (ks7_sub _ Hin)). apply KR1. exact Hin. }
      unfold KS7 in K7'. cbn [In] in K7'.
      destruct Hq as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|Hq]]]]]]]]].
      - apply K7'. left. exact Hq.
      - apply K7'. right. left. exact Hq.
      - rewrite (QQ _ (eq_sym Hq) ltac:(lia)). exact Q8.
      - rewrite (QQ _ (eq_sym Hq) ltac:(lia)). exact Q9.
      - rewrite (QQ _ (eq_sym Hq) ltac:(lia)). exact Q18.
      - rewrite (QQ _ (eq_sym Hq) ltac:(lia)). exact Q19.
      - rewrite (QQ _ (eq_sym Hq) ltac:(lia)). exact Q20.
      - rewrite (QQ _ (eq_sym Hq) ltac:(lia)). exact Q21.
      - rewrite (QQ _ (eq_sym Hq) ltac:(lia)). exact Q22.
      - apply K7'. right. right. exact Hq. }
    assert (AGF : forall M', TK.samem (fun a => ~ (sp - 80 <= a < sp) /\ ~ (IS + 16 + 24 <= a < IS + 16 + 32)) M2 M' -> TK.samem KA M M').
    { intros M' AG3. apply (CK.samem_weaken2 _ _ _ _ _ _ AG02 AG3). unfold KA. intros a Ha. lia. }
    destruct (Z_lt_le_dec av 16384) as [Hlt|Hge].
    +
      assert (Ec : cnt = av) by (unfold cnt; lia). rewrite Ec in *.
      apply (s_xs_r_part fx2 R2 M2 model K sp (IS + 16) gp av r R Hh Hl Hfp2 H2b SPOK H8b H9b H20b ltac:(lia) H22b H19b ltac:(lia) ltac:(lia) FR2 Hrok DF2 SBC2).
      * apply (TK.img_clear_samem _ M M2 _ _ AG02); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; lia | exact RO].
      * exact D24. * left; lia.
      * intros fx' R' M' Hfp' H2' H10' SS K7 G' AG3 MG3.
        apply (FIN fx' R' M' av Hfp' ltac:(lia) H10' H2' (KRF R' K7 SS) (AGF M' AG3)).
        -- intros x Hx. apply MG3, MG2, MG1. exact Hx.
        -- replace (IS + 40) with (IS + 16 + 24) by lia. exact G'.
    +
      assert (Ec : cnt = 16384) by (unfold cnt; lia). rewrite Ec in *.
      destruct SBC2 as (_ & C24 & _).
      apply (s_xs_r_full fx2 R2 M2 model K sp (IS + 16) gp r R Hh Hl Hfp2 H2b SPOK H8b H9b H20b H22b H19b ltac:(lia) ltac:(lia) FR2 Hrok DF2 C24 D24 ltac:(left; lia)).
      intros fx' R' M' Hfp' H2' H10' SS K7 G' AG3 MG3.
      apply (FIN fx' R' M' 16384 Hfp' ltac:(lia) H10' H2' (KRF R' K7 SS) (AGF M' AG3)).
      * intros x Hx. apply MG3, MG2, MG1. exact Hx.
      * replace (IS + 40) with (IS + 16 + 24) by lia. exact G'.
Qed.
End S.
End XS.

