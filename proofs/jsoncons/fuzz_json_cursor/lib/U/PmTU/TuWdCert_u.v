(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u PmFloatCSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_cwd_csrc_T_u Cut_cwd_csrc_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutDemo Require Pm10Memmove_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmGrow Require Import GrowKit_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module TWC.
Module U := Cut_cwd_csrc_u.   Module UT := Cut_cwd_csrc_T_u.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.  Definition MEMMOVE : Z := 0xb7c98.
Definition RET : Z := 0x43684.
Definition has := GK.has.

Lemma heap_ok_u : CH2.heap_chk UT.NF U.HDECL U.BLS U.CPS GK.HULL_LO GK.HULL_HI U.TAGS U.RETS MALLOC FREE [MEMMOVE] = true.
Proof. vmc_refl. Qed.

Definition isnil {A} (l : list A) : bool := match l with [] => true | _ => false end.
Definition phase (i : nat) : bool := isnil (nth i U.BLS []).

Definition lin_zero (e : expr) : bool := let l := lin_of e in (Z.eqb (fst l mod 2 ^ 64) 0 && isnil (snd l))%bool.

Definition halve_lin (l : lin) : option lin :=
  if (Z.even (fst l) && forallb (fun t : Z * expr => Z.even (fst t)) (snd l))%bool
  then Some (fst l / 2, map (fun t : Z * expr => (fst t / 2, snd t)) (snd l)) else None.

Definition cell_val (cells : list kentry) (k : Z) (w : nat) : option expr :=
  match List.find (fun X => match X with KWord (SA b k') w' _ => (expr_eqb b (EVar 8) && Z.eqb k k' && Nat.eqb w w')%bool | _ => false end) cells with
  | Some (KWord _ _ v) => Some v | _ => None end.

Definition nul_expr (nb : expr) (nk : Z) (H : expr) : expr :=
  EAlu ALU_SUB (EAlu ALU_SUB (EAlu ALU_ADD nb (ELit nk)) (EVar 8)) (EAlu ALU_ADD H (ELit 1)).

Definition pin_ok (cells : list kentry) (X : expr) : bool :=
  (lin_zero X || existsb (fun K => match K with
                                   | KRange P lo hi => (Z.eqb lo hi && (lin_zero (EAlu ALU_SUB X (EAlu ALU_SUB P (ELit lo)))
                                                                      || lin_zero (EAlu ALU_ADD X (EAlu ALU_SUB P (ELit lo)))))%bool
                                   | _ => false end) cells)%bool.

Definition lo_ok (cells : list kentry) (H : expr) : bool :=
  (AP.fact_ok cells (KRange H 1 22)
   || existsb (fun K1 => match K1 with
                         | KRange X lo hi => (Z.leb 1 lo && Z.ltb hi (2 ^ 64) &&
                              existsb (fun K2 => match K2 with
                                                 | KRange Y v v' => (Z.eqb v v' && (lin_zero (EAlu ALU_SUB (EAlu ALU_SUB H X) (EAlu ALU_SUB Y (ELit v)))
                                                                                    || lin_zero (EAlu ALU_ADD (EAlu ALU_SUB H X) (EAlu ALU_SUB Y (ELit v)))))%bool
                                                 | _ => false end) cells)%bool
                         | _ => false end) cells)%bool.
Definition short_ok (cells : list kentry) : bool :=
  match cell_val cells 0 1 with
  | Some B => match halve_lin (lin_of B) with
              | Some h => let H := unlin h in
                  (lin_zero (EAlu ALU_SUB B (EMd M_MUL (ELit 2) H)) && AP.fact_ok cells (KRange H 0 22) && lo_ok cells H
                   && existsb (fun K => match K with KWord (SA nb nk) 1 (ELit 0) => pin_ok cells (nul_expr nb nk H) | _ => false end) cells)%bool
              | None => false end
  | None => false end.
Definition long_ok (i : nat) (cells : list kentry) : bool :=
  match nth i U.BLS [], cell_val cells 0 8, cell_val cells 8 8, cell_val cells 16 8 with
  | [(P, sz)], Some w0, Some Sz, Some P' =>
      (expr_eqb sz (ELit 48) && expr_eqb w0 (ELit 49) && expr_eqb P P' && AP.fact_ok cells (KRange Sz 23 47)
       && existsb (fun K => match K with KWord (SA nb nk) 1 (ELit 0) => lin_zero (EAlu ALU_SUB (EAlu ALU_ADD nb (ELit nk)) (EAlu ALU_ADD P Sz)) | _ => false end) cells)%bool
  | _, _, _, _ => false end.

Definition KEPT : list nat := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition exit_ok (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (CL.ps_at ps [RET] && Nat.leb UT.NF (CC.cp_nx c) && CH2.blocks_vars_lt (CC.cp_nx c) (nth i U.BLS [])
   && CL.ps_reg_is ps 10 (ELit 0) && CL.ps_reg_is ps 1 (EVar 33) && CL.ps_reg_is ps 2 (EAlu ALU_ADD (EVar 2) (ELit 400))
   && CL.ps_reg_is ps 8 (EVar 34) && CL.ps_reg_is ps 9 (EVar 35) && CL.ps_keeps ps KEPT
   && (if phase i then short_ok (SR.ps_cells ps) else long_ok i (SR.ps_cells ps)))%bool.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j _ => Bool.eqb (phase i) (phase j)
  | CC.TOther pc =>
      if CH2.is_call MALLOC FREE [MEMMOVE] pc then
        match CH2.ret_of U.RETS i k with
        | Some j => if Z.eqb pc MALLOC then (phase i && negb (phase j) && expr_eqb (CA.ps_reg ps 10) (ELit 48))%bool
                    else Bool.eqb (phase i) (phase j)
        | None => false
        end
      else exit_ok i c ps
  end.
Lemma leaf_chk_ok : CH2.leaves_all U.CPS U.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.

Lemma ret_at : CL.is_ret_at GK.RSEGS RET.
Proof. CL.solve_is_ret. Qed.

Lemma isnil_true : forall {A} (l : list A), isnil l = true -> l = [].
Proof. intros A [|x l] H; [reflexivity | discriminate]. Qed.

Lemma uE_range : forall E e, 0 <= bv_unsigned (edenot E e) < 2 ^ 64.
Proof. intros E e. pose proof (bv_unsigned_in_range _ (edenot E e)) as B. unfold bv_modulus in B. cbn -[Z.pow] in B. exact B. Qed.

Lemma lin_zero_sound : forall E e, lin_zero e = true -> bv_unsigned (edenot E e) = 0.
Proof.
  intros E e H. pose proof (lin_of_sound E e) as [q Hq]. unfold lin_zero in H. destruct (lin_of e) as [c ts] eqn:Hl. cbn [fst snd] in H.
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply isnil_true in H2. subst ts.
  unfold lden in Hq. cbn [fst snd tden] in Hq. unfold uE in Hq. pose proof (uE_range E e) as Hr.
  pose proof (Z.div_mod c (2 ^ 64) ltac:(lia)) as Hd. rewrite H1 in Hd. lia.
Qed.

Lemma eqm_sub_e : forall E a b, eqm (bv_unsigned (edenot E (EAlu ALU_SUB a b))) (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)).
Proof. intros. cbn [edenot]. apply u_sub_eqm. Qed.
Lemma eqm_add_e : forall E a b, eqm (bv_unsigned (edenot E (EAlu ALU_ADD a b))) (bv_unsigned (edenot E a) + bv_unsigned (edenot E b)).
Proof. intros. cbn [edenot]. apply u_add_eqm. Qed.
Lemma eqm_mul_e : forall E a b, eqm (bv_unsigned (edenot E (EMd M_MUL a b))) (bv_unsigned (edenot E a) * bv_unsigned (edenot E b)).
Proof. intros. cbn [edenot]. apply u_mul_eqm. Qed.
Lemma eqm_lit_e : forall E z, eqm (bv_unsigned (edenot E (ELit z))) z.
Proof. intros. cbn [edenot]. apply eqm_u_lit. Qed.

Lemma cell_val_in : forall cells k w v, cell_val cells k w = Some v -> In (KWord (SA (EVar 8) k) w v) cells.
Proof.
  intros cells k w v H. unfold cell_val in H.
  destruct (List.find _ cells) as [X|] eqn:HF; [|discriminate].
  apply find_some in HF as [Hin Hb]. destruct X as [[b k'] w' v'| | | | | | | | |]; try discriminate.
  injection H as <-. repeat (apply andb_prop in Hb as [Hb ?Y]). apply expr_eqb_eq in Hb. apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y. subst. exact Hin.
Qed.

Lemma know_in : forall segs E M cells K, know_ok segs E M cells -> In K cells -> kentry_ok segs E M K.
Proof. intros segs E M cells K HK Hin. exact (proj1 (Forall_forall _ _) HK K Hin). Qed.

Lemma lo_ok_sound : forall E M cells H, know_ok GK.RSEGS E M cells -> lo_ok cells H = true -> bv_unsigned (edenot E H) <= 22 ->
  1 <= bv_unsigned (edenot E H).
Proof.
  intros E M cells H HK HL Hh. unfold lo_ok in HL. apply orb_prop in HL as [HL|HL].
  - pose proof (APS.fact_ok_sound GK.RSEGS E M cells _ HK HL) as [R1 R2]. exact R1.
  - apply existsb_exists in HL as (K1 & HK1 & HB1). destruct K1 as [| | | | |X lo hi| | | |]; try discriminate.
    apply andb_prop in HB1 as [HB1 HE2]. apply andb_prop in HB1 as [HB1 HB2]. apply Z.leb_le in HB1. apply Z.ltb_lt in HB2.
    pose proof (know_in _ _ _ _ _ HK HK1) as (X1 & X2).
    apply existsb_exists in HE2 as (K2 & HK2 & HB3). destruct K2 as [| | | | |Y v v'| | | |]; try discriminate.
    apply andb_prop in HB3 as [Hvv HB3]. apply Z.eqb_eq in Hvv. subst v'.
    pose proof (know_in _ _ _ _ _ HK HK2) as (Y1 & Y2). assert (EY : bv_unsigned (edenot E Y) = v) by lia.
    pose proof (uE_range E H) as RH. pose proof (uE_range E X) as RX.
    pose proof (eqm_sub_e E H X) as [q1 Q1]. pose proof (eqm_sub_e E Y (ELit v)) as [q2 Q2]. pose proof (eqm_lit_e E v) as [q3 Q3].
    rewrite EY in Q2. pose proof (uE_range E (EAlu ALU_SUB H X)) as R1. pose proof (uE_range E (EAlu ALU_SUB Y (ELit v))) as R2. pose proof (uE_range E (ELit v)) as R3.
    assert (E0 : bv_unsigned (edenot E (EAlu ALU_SUB Y (ELit v))) = 0) by nia.
    apply orb_prop in HB3 as [HB3|HB3].
    + pose proof (lin_zero_sound E _ HB3) as Z0. pose proof (eqm_sub_e E (EAlu ALU_SUB H X) (EAlu ALU_SUB Y (ELit v))) as [q4 Q4]. rewrite Z0, E0 in Q4. nia.
    + pose proof (lin_zero_sound E _ HB3) as Z0. pose proof (eqm_add_e E (EAlu ALU_SUB H X) (EAlu ALU_SUB Y (ELit v))) as [q4 Q4]. rewrite Z0, E0 in Q4. nia.
Qed.

Lemma short_ok_sound : forall E M cells o, short_ok cells = true -> know_ok GK.RSEGS E M cells -> bv_unsigned (ev E 8) = o -> 0 <= o -> o + 24 <= 2 ^ 64 ->
  exists h, 1 <= h <= 22 /\ L5.u8_at GK.RSEGS M o (2 * h) /\ L5.u8_at GK.RSEGS M (o + 1 + h) 0.
Proof.
  intros E M cells o H HK Ho H0 H24. unfold short_ok in H.
  destruct (cell_val cells 0 1) as [B|] eqn:HB; [|discriminate]. destruct (halve_lin (lin_of B)) as [hl|] eqn:Hh; [|discriminate].
  set (H1 := unlin hl) in *. apply andb_prop in H as [H HN]. apply andb_prop in H as [H HLO]. apply andb_prop in H as [HZ HR].
  pose proof (APS.fact_ok_sound GK.RSEGS E M cells _ HK HR) as [R0 R2]. pose proof (lo_ok_sound E M cells H1 HK HLO R2) as R1. set (h := bv_unsigned (edenot E H1)) in *.
  pose proof (lin_zero_sound E _ HZ) as Z0.
  pose proof (eqm_sub_e E B (EMd M_MUL (ELit 2) H1)) as [q1 Q1]. pose proof (eqm_mul_e E (ELit 2) H1) as [q2 Q2]. pose proof (eqm_lit_e E 2) as [q3 Q3].
  rewrite Z0 in Q1. fold h in Q2. pose proof (uE_range E B) as RB. pose proof (uE_range E (EMd M_MUL (ELit 2) H1)) as RM.
  assert (E2 : bv_unsigned (edenot E (ELit 2)) = 2) by (cbn [edenot]; apply u64_of_Z; lia). rewrite E2 in Q2.
  assert (EB : bv_unsigned (edenot E B) = 2 * h) by nia.
  exists h. split; [lia|]. split.
  - apply (GK.kword8_elim E M (SA (EVar 8) 0) B o (2 * h) (know_in _ _ _ _ _ HK (cell_val_in _ _ _ _ HB))); [unfold estart; cbn [a_base a_off edenot]; lia | exact EB].
  - apply existsb_exists in HN as (K & HKin & HKb). destruct K as [[nb nk] w v| | | | | | | | |]; try discriminate.
    destruct w as [|[|w]]; try discriminate. destruct v as [z| | | | | | |]; try discriminate. destruct z; try discriminate.
    pose proof (know_in _ _ _ _ _ HK HKin) as HC. pose proof HC as (_ & (F1 & F2 & _ & F4) & _).
    assert (X0 : bv_unsigned (edenot E (nul_expr nb nk H1)) = 0).
    { unfold pin_ok in HKb. apply orb_prop in HKb as [HKb|HKb]; [exact (lin_zero_sound E _ HKb)|].
      apply existsb_exists in HKb as (Kp & HKp & HPb). destruct Kp as [| | | | |P lo hi| | | |]; try discriminate.
      apply andb_prop in HPb as [Hlh HPb]. apply Z.eqb_eq in Hlh. subst hi.
      pose proof (know_in _ _ _ _ _ HK HKp) as (P1 & P2). assert (EP : bv_unsigned (edenot E P) = lo) by lia.
      pose proof (uE_range E (nul_expr nb nk H1)) as RX.
      pose proof (eqm_sub_e E P (ELit lo)) as [q5 Q5]. pose proof (eqm_lit_e E lo) as [q6 Q6]. rewrite EP in Q5.
      pose proof (uE_range E (EAlu ALU_SUB P (ELit lo))) as RP.
      apply orb_prop in HPb as [HPb|HPb].
      - pose proof (lin_zero_sound E _ HPb) as Z1. pose proof (eqm_sub_e E (nul_expr nb nk H1) (EAlu ALU_SUB P (ELit lo))) as [q4 Q4]. rewrite Z1 in Q4.
        assert (EP0 : bv_unsigned (edenot E (EAlu ALU_SUB P (ELit lo))) = 0) by (pose proof (uE_range E (ELit lo)); nia).
        rewrite EP0 in Q4. nia.
      - pose proof (lin_zero_sound E _ HPb) as Z1. pose proof (eqm_add_e E (nul_expr nb nk H1) (EAlu ALU_SUB P (ELit lo))) as [q4 Q4]. rewrite Z1 in Q4.
        assert (EP0 : bv_unsigned (edenot E (EAlu ALU_SUB P (ELit lo))) = 0) by (pose proof (uE_range E (ELit lo)); nia).
        rewrite EP0 in Q4. nia. }
    unfold nul_expr in X0.
    pose proof (eqm_sub_e E (EAlu ALU_SUB (EAlu ALU_ADD nb (ELit nk)) (EVar 8)) (EAlu ALU_ADD H1 (ELit 1))) as [a1 A1].
    pose proof (eqm_sub_e E (EAlu ALU_ADD nb (ELit nk)) (EVar 8)) as [a2 A2].
    pose proof (eqm_add_e E nb (ELit nk)) as [a3 A3]. pose proof (eqm_lit_e E nk) as [a4 A4].
    pose proof (eqm_add_e E H1 (ELit 1)) as [a5 A5]. pose proof (eqm_lit_e E 1) as [a6 A6].
    rewrite X0 in A1. change (edenot E (EVar 8)) with (ev E 8) in A2. rewrite Ho in A2. fold h in A5.
    assert (E1 : bv_unsigned (edenot E (ELit 1)) = 1) by (cbn [edenot]; apply u64_of_Z; lia). rewrite E1 in A5.
    pose proof (uE_range E (EAlu ALU_SUB (EAlu ALU_ADD nb (ELit nk)) (EVar 8))) as R3. pose proof (uE_range E (EAlu ALU_ADD nb (ELit nk))) as R4.
    pose proof (uE_range E (EAlu ALU_ADD H1 (ELit 1))) as R5. pose proof (uE_range E (ELit nk)) as R6.
    unfold estart in F1, F2, F4. cbn [a_base a_off] in F1, F2, F4.
    assert (EA : estart E (SA nb nk) = o + 1 + h).
    { unfold estart. cbn [a_base a_off]. change (2 ^ 64) with 18446744073709551616 in *. lia. }
    exact (CL5.kword8_zero_elim GK.RSEGS E M _ _ HC EA).
Qed.

Lemma long_ok_blk : forall i cells, long_ok i cells = true -> exists P, nth i U.BLS [] = [(P, ELit 48)].
Proof.
  intros i cells H. unfold long_ok in H. destruct (nth i U.BLS []) as [|[P sz] [|]]; try discriminate.
  destruct (cell_val cells 0 8), (cell_val cells 8 8), (cell_val cells 16 8); try discriminate.
  repeat (apply andb_prop in H as [H ?Y]). apply expr_eqb_eq in H. subst sz. exists P. reflexivity.
Qed.
Lemma long_ok_sound : forall E M i cells o P, long_ok i cells = true -> know_ok GK.RSEGS E M cells -> bv_unsigned (ev E 8) = o -> 0 <= o -> o + 24 <= 2 ^ 64 ->
  nth i U.BLS [] = [(P, ELit 48)] -> bv_unsigned (edenot E P) + 48 <= 2 ^ 64 ->
  exists S, 23 <= S <= 47 /\ L5.u64_at GK.RSEGS M o 49 /\ L5.u64_at GK.RSEGS M (o + 8) S /\ L5.u64_at GK.RSEGS M (o + 16) (bv_unsigned (edenot E P))
    /\ L5.u8_at GK.RSEGS M (bv_unsigned (edenot E P) + S) 0.
Proof.
  intros E M i cells o P H HK Ho H0 H24 HB HP. unfold long_ok in H. rewrite HB in H.
  destruct (cell_val cells 0 8) as [w0|] eqn:C0; [|discriminate]. destruct (cell_val cells 8 8) as [S|] eqn:C8; [|discriminate].
  destruct (cell_val cells 16 8) as [P'|] eqn:C16; [|discriminate].
  apply andb_prop in H as [H HN]. apply andb_prop in H as [H HR]. apply andb_prop in H as [H HPP]. apply andb_prop in H as [_ HW].
  apply expr_eqb_eq in HW, HPP. subst w0 P'.
  pose proof (APS.fact_ok_sound GK.RSEGS E M cells _ HK HR) as [R1 R2].
  exists (bv_unsigned (edenot E S)). split; [lia|].
  assert (ST : forall k, estart E (SA (EVar 8) k) = o + k) by (intros k; unfold estart; cbn [a_base a_off edenot]; lia).
  split; [apply (CL5.kword64_elim GK.RSEGS E M _ _ o 49 (know_in _ _ _ _ _ HK (cell_val_in _ _ _ _ C0))); [rewrite ST; lia | cbn [edenot]; apply u64_of_Z; lia]|].
  split; [apply (CL5.kword64_elim GK.RSEGS E M _ _ (o + 8) _ (know_in _ _ _ _ _ HK (cell_val_in _ _ _ _ C8))); [rewrite ST; lia | reflexivity]|].
  split; [apply (CL5.kword64_elim GK.RSEGS E M _ _ (o + 16) _ (know_in _ _ _ _ _ HK (cell_val_in _ _ _ _ C16))); [rewrite ST; lia | reflexivity]|].
  apply existsb_exists in HN as (K & HKin & HKb). destruct K as [[nb nk] w v| | | | | | | | |]; try discriminate.
  destruct w as [|[|w]]; try discriminate. destruct v as [z| | | | | | |]; try discriminate. destruct z; try discriminate.
  pose proof (know_in _ _ _ _ _ HK HKin) as HC. pose proof HC as (_ & (F1 & F2 & _ & F4) & _).
  pose proof (lin_zero_sound E _ HKb) as X0.
  pose proof (eqm_sub_e E (EAlu ALU_ADD nb (ELit nk)) (EAlu ALU_ADD P S)) as [a1 A1].
  pose proof (eqm_add_e E nb (ELit nk)) as [a3 A3]. pose proof (eqm_lit_e E nk) as [a4 A4].
  pose proof (eqm_add_e E P S) as [a5 A5].
  rewrite X0 in A1.
  pose proof (uE_range E (EAlu ALU_ADD nb (ELit nk))) as R4. pose proof (uE_range E (EAlu ALU_ADD P S)) as R5. pose proof (uE_range E (ELit nk)) as R6.
  pose proof (uE_range E P) as R7.
  unfold estart in F1, F2, F4. cbn [a_base a_off] in F1, F2, F4.
  assert (EA : estart E (SA nb nk) = bv_unsigned (edenot E P) + bv_unsigned (edenot E S)).
  { unfold estart. cbn [a_base a_off]. nia. }
  exact (CL5.kword8_zero_elim GK.RSEGS E M _ _ HC EA).
Qed.

Lemma bytes_of_defined : forall (M : PML.mem) (n : nat) (p : Z), 0 <= p -> p + Z.of_nat n <= 2 ^ 64 -> L5.defined M p (Z.of_nat n) ->
  exists s : list Z, length s = n /\ L5.bytes_at GK.RSEGS M p s.
Proof.
  intros M n. induction n as [|n IH]; intros p Hp Hb Hd.
  - exists []. split; [reflexivity|]. intros i Hi. cbn [length] in Hi. lia.
  - destruct (IH (p + 1) ltac:(lia) ltac:(lia)) as (s & Hl & Hs).
    { intros i Hi. replace (p + 1 + i) with (p + (i + 1)) by lia. apply Hd. lia. }
    pose proof (Hd 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 p)) as [b|] eqn:Hb0; [|contradiction].
    exists (bv_unsigned b :: s). split; [cbn [length]; rewrite Hl; reflexivity|].
    intros i Hi. destruct i as [|i].
    + cbn [nth]. rewrite Z.add_0_r. unfold L5.u8_at. cbn [rdn]. unfold rd1. rewrite Hb0. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + cbn [nth]. replace (p + Z.of_nat (S i)) with (p + 1 + Z.of_nat i) by lia. apply Hs. cbn [length] in Hi. lia.
Qed.

Section TuWdCertOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Definition Cred (cr0 : credit) (i : nat) (E : env) (cr : credit) : Prop := cr = if phase i then cr0 else debit L cr0 48.

Definition wd_post (E : env) (LB : list (Z * Z)) (cr : credit) (M : PML.mem) (R' : bvmap 5 word) (M' : PML.mem) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  PML.a0 R' 0 /\ (exists s', 1 <= Z.of_nat (length s') <= 47 /\ PMFC.num_str L LB cr M' (bv_unsigned (ev E 8)) s' LB' cr') /\
  getr R' 1%bv = ev E 33 /\ getr R' 2%bv = Z_to_bv 64 (bv_unsigned (ev E 2) + 400) /\ getr R' 8%bv = ev E 34 /\ getr R' 9%bv = ev E 35 /\
  (forall y : reg, In (ridx y) KEPT -> getr R' y = ev E (ridx y)) /\
  L5C.hpres L LB (bv_unsigned (ev E 2)) 9200 [(bv_unsigned (ev E 8), 24)] M M'.

Theorem wd_cert : forall (i : nat) (c : CC.cutpoint) (fx : FPState) (E : env) (R : bvmap 5 word) (M : PML.mem) (model : Model) (K : TSet)
    (LB : list (Z * Z)) (cr : credit),
  phase i = true -> nth_error U.CPS i = Some c -> CC.At GK.RSEGS c E R M ->
  hi_heap HI LB cr M (m_vmmaps model) -> PML.model_ok model -> K [] -> PML.fp_ok fx -> credit_ok L cr 48 ->
  bv_unsigned (ev E 2) mod 16 = 0 -> hl_sptop L - 8388608 + 9200 <= bv_unsigned (ev E 2) -> bv_unsigned (ev E 2) + 400 <= bv_unsigned (ev E 8) ->
  bv_unsigned (ev E 8) + 24 <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 ->
  ev E 4 = Z_to_bv 64 PML.TP -> L5.ra_ok (bv_unsigned (ev E 33)) ->
  L5.defined M (bv_unsigned (ev E 2) - 9200) 9200 -> L5.defined M (bv_unsigned (ev E 8)) 24 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : PML.mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
     PML.fp_ok fx' -> wd_post E LB cr M R' M' LB' cr' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
     srealizes GK.RSEGS SCFG (@PML.cfg fx' R' (bv_unsigned (ev E 33)) M' model') K) ->
  srealizes GK.RSEGS SCFG (@PML.cfg fx R (CC.cp_pc c) M model) K.
Proof.
  intros i c fx E R M model K LB cr Hph Hc HAt HH Hmo HKnil Hfp Hcr SPA SPL SPO OTOP STOP HTP HRA DSTK DOBJ Hcont.
  set (sp := bv_unsigned (ev E 2)) in *. set (o := bv_unsigned (ev E 8)) in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (SCRE : CH.hd_scr U.HDECL = 9200) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ hl_sptop L - 8388608 + CH.hd_scr U.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (rewrite SCRE; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr U.HDECL) by (rewrite SCRE; lia).
  assert (NF32 : (32 <= UT.NF)%nat) by (unfold UT.NF; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs U.HDECL) -> SGP.region_vars_lt UT.NF rg = true /\ (forall a : Z, CH2.in_reg E rg a -> CH2.sclient L LB sp a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    fold sp in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs U.HDECL) -> SGP.region_vars_lt UT.NF rg = true /\ (forall a : Z, CH2.in_reg E rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    fold o in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (BL0 : nth i U.BLS [] = []) by (apply isnil_true; exact Hph).
  unfold PML.cfg. rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := UT.NF) (E0 := E) (M0 := M) (model0 := model) (LBrest := LB) (sp0 := sp) (d := U.HDECL)
    (W := [(o, 24)]) (BLS := U.BLS) (Cred := Cred cr) (CPS := U.CPS) (TAGS := U.TAGS) (RETS := U.RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := [MEMMOVE]) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := i) (E := E) (HI := HI).
  - exact HIok.
  - exact LYI.
  - exact LYE.
  - exact (PmLayout.ly_ro L LAY).
  - rewrite LSTK. lia.
  - exact STKF.
  - exact SCRP.
  - rewrite LSTK. reflexivity.
  - exact NF32.
  - reflexivity.
  - rewrite HTP, (PmLayout.ly_tp L LAY). reflexivity.
  - exact W_OK.
  - exact CRS_OK.
  - exact WRS_OK.
  - intros rg a [].
  - exact HKnil.
  - exact ILO.
  - exact IHI.
  - rewrite LS. exact FPM.
  - rewrite LS. exact U.plans.
  - exact U.tags_ok.
  - exact heap_ok_u.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [<-|[]]. exact (Pm10Memmove_u.memmove_copy1 L LS).
  -
    intros i0 c0 kk ps j sg IL E1 E1' R1' M1 M1' cr1 HagE Hag HLF HC.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_chk_ok _ _ _ _ _ IL) as X. cbv beta iota in X. apply Bool.eqb_prop in X.
    unfold Cred in *. rewrite <- X. exact HC.
  -
    intros i0 c0 kk ps j cj IL Hret Hcj E1 E1' R1' M1 M1' cr1 HagE Hag HLF HC.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_chk_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X.
    change (CH2.is_call MALLOC FREE [MEMMOVE] MALLOC) with true in X. cbv beta iota in X. rewrite Hret in X. change (Z.eqb MALLOC MALLOC) with true in X. cbv beta iota in X.
    apply andb_prop in X as [X XA]. apply andb_prop in X as [XI XJ]. apply negb_true_iff in XJ. apply expr_eqb_eq in XA.
    assert (Hval : bv_unsigned (edenot E1' (CA.ps_reg ps 10)) = 48) by (rewrite XA; cbn [edenot]; apply u64_of_Z; lia).
    cbv zeta. rewrite Hval. unfold Cred in HC. rewrite XI in HC. subst cr1. split; [exact Hcr|].
    intros E2 Hag2. unfold Cred. rewrite XJ. reflexivity.
  -
    intros i0 c0 kk ps pc j cj IL Hcall Hnm Hret Hcj E1 E1' R1' M1 M1' cr1 HagE Hag HLF HC E2 Hag2.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_chk_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. rewrite Hcall, Hret in X.
    destruct (Z.eqb_spec pc MALLOC) as [->|_]; [contradiction|]. apply Bool.eqb_prop in X.
    unfold Cred in *. rewrite <- X. exact HC.
  -
    intros i0 c0 kk ps pc IL Hnc fx' E1 R1 M1 m1 E' R' M' HAt1 HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_chk_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. rewrite Hnc in X. unfold exit_ok in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) UT.NF E M model LB sp U.HDECL [(o, 24)] U.BLS (Cred cr) STKF SCRP NF32 eq_refl W_OK WRS_OK
                  U.CPS GK.HULL_LO GK.HULL_HI U.TAGS U.RETS MALLOC FREE [MEMMOVE] heap_ok_u i0 c0 kk ps pc IL Hnc E1 E' R1 R' M1 M' m1 HAt1 HAmb Hag HLF) as HA'.
    apply andb_prop in X as [X XSH]. apply andb_prop in X as [X XKP]. apply andb_prop in X as [X XS1]. apply andb_prop in X as [X XS0].
    apply andb_prop in X as [X XSP]. apply andb_prop in X as [X XRA]. apply andb_prop in X as [X XA0]. apply andb_prop in X as [X XBV].
    apply andb_prop in X as [X XNF].
    first [apply CL.ps_at_sound in X; destruct X as [X|[]]; symmetry in X | apply Z.eqb_eq in X | (apply orb_prop in X as [X|X]; [apply Z.eqb_eq in X | discriminate])].
    apply Nat.leb_le in XNF.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
    assert (HagE' : env_agree UT.NF E E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact XNF]]).
    assert (FV : forall n, (n < UT.NF)%nat -> ev E' n = ev E n) by (intros n Hn; symmetry; apply (proj1 HagE'); exact Hn).
    assert (F8 : bv_unsigned (ev E' 8) = o) by (rewrite FV by (unfold UT.NF; lia); reflexivity).
    rewrite LS in HLF.
    assert (HK : know_ok GK.RSEGS E' M' (SR.ps_cells ps)) by (apply Forall_forall; intros X0 HX0; exact (CC.lf_cells _ _ _ _ _ _ _ HLF X0 HX0)).
    assert (DEF : L5.defined M' o 24).
    { intros j Hj. pose proof (Hdf1 (o + j) ltac:(lia)) as D. rewrite <- (Z_to_bv_bv_unsigned _ (Z_to_bv 64 (o + j))). rewrite u64_of_Z by lia.
      apply D; [| exact (DOBJ j Hj)]. split; [right; left; split; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia]. }

    assert (RG : forall (y : reg) e, CL.ps_reg_is ps (ridx y) e = true -> getr R' y = edenot E' e).
    { intros y e Hq. rewrite <- (CC.reg_of_ridx y) at 1. exact (CL.ps_reg_is_sound GK.RSEGS c0 ps E' R' M1 M' (ridx y) e HLF Hq). }
    assert (Ha0' : PML.a0 R' 0) by (unfold PML.a0; exact (RG 10%bv (ELit 0) XA0)).
    assert (Hra' : getr R' 1%bv = ev E 33) by (rewrite (RG 1%bv (EVar 33) XRA); cbn [edenot]; apply FV; unfold UT.NF; lia).
    assert (Hsp' : getr R' 2%bv = Z_to_bv 64 (sp + 400)).
    { rewrite (RG 2%bv _ XSP). cbn [edenot]. rewrite (FV 2%nat) by (unfold UT.NF; lia). rewrite alu_add. unfold v_add. f_equal. }
    assert (Hs0' : getr R' 8%bv = ev E 34) by (rewrite (RG 8%bv (EVar 34) XS0); cbn [edenot]; apply FV; unfold UT.NF; lia).
    assert (Hs1' : getr R' 9%bv = ev E 35) by (rewrite (RG 9%bv (EVar 35) XS1); cbn [edenot]; apply FV; unfold UT.NF; lia).
    assert (KEEP : forall y : reg, In (ridx y) KEPT -> getr R' y = ev E (ridx y)).
    { intros y Hy. assert (Hy32 : (ridx y < UT.NF)%nat) by (unfold KEPT in Hy; cbn [In] in Hy; unfold UT.NF; intuition lia).
      exact (CL.ps_keeps_sound GK.RSEGS c0 ps E E' R' M1 M' KEPT UT.NF y HLF XKP HagE' Hy Hy32). }

    assert (Hds : L5.defined M (sp - CH.hd_scr U.HDECL) (CH.hd_scr U.HDECL)) by (rewrite SCRE; exact DSTK).
    pose proof (CH2.amb_hpres L HI LYI LYE UT.NF E M model LB sp U.HDECL [(o, 24)] U.BLS (Cred cr) STKF NF32 i0 E1 M' m1 HA2 Hds) as HP.
    rewrite SCRE in HP.
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct HRA as [R1' R2']. exact R2'. }
    rewrite Hra'. rewrite <- (Z_to_bv_bv_unsigned _ (ev E 33)).

    destruct (phase i0) eqn:Hph0.
    +
      assert (HB0 : nth i0 U.BLS [] = []) by (apply isnil_true; exact Hph0).
      assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite Hph0 in HC1; exact HC1). subst cr1.
      assert (HH2 : hi_heap HI LB cr M' (m_vmmaps m1)) by (unfold CH2.cur in HH1; rewrite HB0 in HH1; exact HH1).
      destruct (short_ok_sound E' M' _ o XSH HK F8 ltac:(lia) ltac:(lia)) as (h & Hh & B0 & NUL).
      destruct (bytes_of_defined M' (Z.to_nat h) (o + 1) ltac:(lia) ltac:(lia)) as (s' & Hsl & Hbs).
      { rewrite Z2Nat.id by lia. intros j Hj. replace (o + 1 + j) with (o + (1 + j)) by lia. apply DEF. lia. }
      assert (LEN : Z.of_nat (length s') = h) by (rewrite Hsl; apply Z2Nat.id; lia).
      apply (Hcont fx' R' M' m1 LB cr HFP); [| exact Hbv1 | exact HH2].
      split; [exact Ha0'|]. split.
      { exists s'. split; [lia|]. left. split; [lia|]. split; [|split; [exact DEF | split; reflexivity]].
        unfold PML.str_at, L5.lstr_short. rewrite LEN. split; [lia|]. split; [exact B0|]. split; [exact Hbs | exact NUL]. }
      split; [exact Hra'|]. split; [exact Hsp'|]. split; [exact Hs0'|]. split; [exact Hs1'|]. split; [exact KEEP | exact HP].
    +
      destruct (long_ok_blk i0 _ XSH) as (P & HBP).
      assert (Hcr1 : cr1 = debit L cr 48) by (unfold Cred in HC1; rewrite Hph0 in HC1; exact HC1). subst cr1.
      rewrite HBP in XBV. set (pX := bv_unsigned (edenot E' P)) in *.
      assert (HH2 : hi_heap HI ((pX, 48) :: LB) (debit L cr 48) M' (m_vmmaps m1)).
      { unfold CH2.cur in HH1. rewrite HBP in HH1. rewrite <- (CH2.den_agree _ E1 E' _ Hag XBV) in HH1. exact HH1. }
      destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & Hnd2 & _).
      destruct (Hwf2 (pX, 48) (or_introl eq_refl)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Qdef & Qap). cbn [fst snd lb_remove] in Q0, Q1, Q2, Q3, Q4, Qdef, Qap. rewrite Z.eqb_refl in Qap.
      destruct (long_ok_sound E' M' i0 _ o P XSH HK F8 ltac:(lia) ltac:(lia) HBP ltac:(fold pX; lia)) as (S & HS & W0 & W8 & W16 & NUL). fold pX in W16, NUL.
      destruct (bytes_of_defined M' (Z.to_nat S) pX ltac:(lia) ltac:(lia)) as (s' & Hsl & Hbs).
      { rewrite Z2Nat.id by lia. intros j Hj. apply Qdef. lia. }
      assert (LEN : Z.of_nat (length s') = S) by (rewrite Hsl; apply Z2Nat.id; lia).
      apply (Hcont fx' R' M' m1 ((pX, 48) :: LB) (debit L cr 48) HFP); [| exact Hbv1 | exact HH2].
      split; [exact Ha0'|]. split.
      { exists s'. split; [lia|]. right. exists pX. split; [lia|]. split.
        { split; [|split; [reflexivity | lia]]. unfold L5.lstr_long. rewrite LEN. split; [reflexivity|]. split; [exact W0|]. split; [exact W8|]. split; [exact W16|].
          split; [exact Hbs | exact NUL]. }
        split; [exact DEF|]. split; [|split; reflexivity].
        split; [repeat split; assumption|]. split; [|exact Qdef]. intros b0 Hb0x. destruct b0 as [bb bm]. exact (Qap (bb, bm) Hb0x). }
      split; [exact Hra'|]. split; [exact Hsp'|]. split; [exact Hs0'|]. split; [exact Hs1'|]. split; [exact KEEP | exact HP].
  - exact Hc.
  - rewrite LS. exact HAt.
  -
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|unfold Cred; rewrite Hph; reflexivity]. unfold CH2.cur. rewrite BL0. exact HH.
  - exact Hfp.
Qed.
End TuWdCertOk.
End TWC.
