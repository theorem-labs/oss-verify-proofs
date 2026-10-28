(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptExec LeptExecW LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptSelGP O23LeptMod.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptErr V23LeptStderrP8.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Ltac fdl pc F D :=
  let f := eval vm_compute in (fetch_word SEGS (Z_to_bv 64 pc)) in
  lazymatch f with
  | Some ?w =>
      let l := word_lit (Z_to_bv 64 pc) in
      assert (F : fetch_word SEGS l = Some w) by (vm_cast_no_check (eq_refl (Some w)));
      let d := eval vm_compute in (decode_any w) in
      assert (D : decode_any w = d) by (vm_cast_no_check (eq_refl d))
  end.

Local Ltac pcto q :=
  lazymatch goal with
  | |- reach _ (@mkst _ _ ?p _ _) _ => replace p with q by (apply bv_eq; reflexivity)
  | |- msteps _ (@mkst _ _ ?p _ _) _ => replace p with q by (apply bv_eq; reflexivity)
  end.

Local Ltac regz regs H :=
  repeat match goal with |- context [getr regs ?r] =>
    let E := fresh "E" in
    assert (E : getr regs r = Z_to_bv 64 0) by (first [ exact H | rewrite getr_zero; first [reflexivity | apply bv_eq; reflexivity] | rewrite <- H; first [reflexivity | f_equal; apply bv_eq; reflexivity] ]);
    rewrite E; clear E end;
  first [cond_compute | (vm_compute; reflexivity)].

Local Ltac xfstep HK ST FZ :=
  lazymatch type of ST with
  | ex_st ?segs ?E ?m ?rom ?ms0 (mkFP (fr_denot _ ?L ?fr) ?cs) ?pc ?sr ?log =>
    let F := fresh "F" in let D := fresh "D" in
    ex_fetch segs pc F D;
    lazymatch type of D with
    | decode_any ?w = Some (Fcmp ?op ?fmt ?rd ?rs1 ?rs2, _) =>
        let b := fresh "b" in let fl := fresh "fl" in let EQ := fresh "EQ" in let ST' := fresh "ST" in
        destruct (fpv_cmp op fmt (fpv_rdw fmt (reg_get (fr_denot E L fr) rs1)) (fpv_rdw fmt (reg_get (fr_denot E L fr) rs2))) as [b fl] eqn:EQ;
        pose proof (exb_fcmp segs E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 _ _ b fl ST F (eq_refl _) D eq_refl eq_refl EQ) as ST';
        clear F D EQ ST; rename ST' into ST; exb_reabs ST FZ; destruct b; exb_norm ST
    | decode_any ?w = Some (Fsgnj ?op ?fmt ?rd ?rs1 ?rs2, _) =>
        let ST' := fresh "ST" in
        pose proof (exb_fsgnj segs E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 _ _
                      (bv_unsigned (fpv_sgnj op fmt (reg_get (fr_denot E L fr) rs1) (reg_get (fr_denot E L fr) rs2)))
                      ST F (eq_refl _) D eq_refl eq_refl (eq_sym (zbv_self _))) as ST';
        clear F D ST; rename ST' into ST; exb_norm ST
    | decode_any ?w = Some (Fari ?op ?fmt ?rd ?rs1 ?rs2 ?rm, _) =>
        let mdo := eval vm_compute in (rmode_of_field (bv_unsigned rm) 0) in
        let md := lazymatch mdo with Some ?md => md end in
        let res := fresh "res" in let fl := fresh "fl" in let EQ := fresh "EQ" in let ST' := fresh "ST" in
        destruct (fpv_ari op fmt md (fpv_rdw fmt (reg_get (fr_denot E L fr) rs1)) (fpv_rdw fmt (reg_get (fr_denot E L fr) rs2))) as [res fl] eqn:EQ;
        pose proof (exb_fari segs E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 rm md _ _ res (bv_unsigned (fpv_box fmt res)) fl
                      ST F (eq_refl _) D FZ ltac:(vm_cast_no_check (eq_refl (Some md))) eq_refl eq_refl EQ (eq_sym (zbv_self _))) as ST';
        clear F D EQ ST; rename ST' into ST; exb_reabs ST FZ; exb_norm ST
    | _ => clear F D; exb_fstep (@nil (nat * nat)) HK ST FZ; exb_norm ST
    end
  end.

Local Ltac xrun stops HK ST FZ :=
  exb_cont 300%nat stops (SCR [] [] []) HK ST ltac:(fun _ => idtac);
  first [ exb_at_stop stops ST
        | (xfstep HK ST FZ; first [ exb_at_stop stops ST | xrun stops HK ST FZ ]) ].

Local Ltac xexit ST HR :=
  let R := fresh "R" in let HRx := fresh "HRx" in let Hlf := fresh "Hlf" in let Hms := fresh "Hms" in
  exb_exit ST R HRx Hlf Hms; eapply reach_msteps; [exact Hms|]; clear Hms Hlf.

Local Ltac xagree AG HR :=
  lazymatch goal with HRx : regs_ok _ _ ?R |- regs_agree _ _ ?R =>
    eapply regs_agree_trans; [exact AG | ex_agree HR HRx] end.

Local Ltac xreg regs :=
  lazymatch goal with HRx : regs_ok _ _ ?R |- getr ?R _ = _ => ex_reg regs HRx end.

Section Segs.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma mod_A : forall fr cs regs m (s po : Z) (ret : word),
  (16 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= po)%Z -> (po + 4 <= 2 ^ 64)%Z -> (po mod 4 = 0)%Z -> frm_zero cs ->
  store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true -> store_ok SEGS m (Z_to_bv 64 po) 4 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 po ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xafe34 : word) m rom)
    (fun fin => exists fr' cs' regs' (pc' : word),
       fin = @mkst (mkFP fr' cs') regs' pc' (wr4 (MFR m s ret regs) po 0) rom /\ frm_zero cs' /\
       (pc' = (0xafe64 : word) \/ pc' = (0xafee0 : word)) /\
       getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 10 = Z_to_bv 64 po /\
       regs_agree (fun r => In r [2; 12]%list) regs regs').
Proof.
  intros fr cs regs m s po ret Hs1 Hs2 Hp1 Hp2 Hp4 FZ SOK1 SOK2 H2 H1 H10.
  replace (0xafe34 : word) with (Z_to_bv 64 0xafe34) by (apply bv_eq; reflexivity).
  ex_entry regs (@nil Z) HR.
  assert (HK : know_ok SEGS (ex_env regs []) m
                 [KWr (SA (EVar 2) (-16)) 16; KWr (SA (EVar 10) 0) 4; KRange (EVar 2) 16 (2 ^ 64 - 1);
                  KRange (EVar 10) 1 (2 ^ 64 - 4); KAlign (EVar 10) 4]%Z) by ex_know regs.
  exb_open HR HK ST.
  xrun [0xafe64; 0xafee0]%Z HK ST FZ.
  all: xexit ST HR; apply reach_done; eexists _, _, _, _; split;
    [ lazymatch goal with |- @mkst _ _ _ ?M1 _ = @mkst _ _ _ ?M2 _ =>
        replace M1 with M2; [reflexivity | unfold wr4, MFR; ex_mem_eq regs] end
    | split; [assumption | split; [first [left; apply bv_eq; reflexivity | right; apply bv_eq; reflexivity] |
        split; [xreg regs | split; [xreg regs | lazymatch goal with HRx : regs_ok _ _ ?R |- _ => ex_agree HR HRx end]]]] ].
Qed.

(* [comment removed for export] *)
Lemma mod_N : forall (fx : FPState) regs m,
  rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafe64 : word) m rom) (@mkst fx regs' (0x636a4 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafe8c /\ getr regs' 10 = Z_to_bv 64 0x1b5e0 /\ getr regs' 11 = Z_to_bv 64 0x19cf1
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m G1 G2.
  replace (0xafe64 : word) with (Z_to_bv 64 0xafe64) by (apply bv_eq; reflexivity).
  replace (0x636a4 : word) with (Z_to_bv 64 0x636a4) by (apply bv_eq; reflexivity).
  ex_entry regs (@nil Z) HR.
  assert (HK : know_ok SEGS (ex_env regs []) m [KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3)]%Z)
    by ex_know regs.
  ex_run 40%nat [0x636a4]%Z (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR'); ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma mod_Z : forall (fx : FPState) regs m (s : Z) (ret v0 : word),
  (16 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) ->
  getr regs 2 = Z_to_bv 64 (s - 16) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafe8c : word) m rom) (@mkst fx regs' ret m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = v0
    /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
Proof.
  intros fx regs m s ret v0 Hs1 Hs2 Hret Cra Cs0 H2.
  replace (0xafe8c : word) with (Z_to_bv 64 0xafe8c) by (apply bv_eq; reflexivity).
  ex_entry regs [s; bv_unsigned ret; bv_unsigned v0] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bv_unsigned ret; bv_unsigned v0]) m
                 [KWord (SA (EVar 32) (-8)) 8 (EVar 33); KWord (SA (EVar 32) (-16)) 8 (EVar 34); KRange (EVar 32) 16 (2 ^ 64 - 1)]%Z).
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    - eapply ex_kword_w with (b := s) (x := ret); [reflexivity | apply zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (s + -8)%Z with (s - 8)%Z by lia. exact Cra.
    - eapply ex_kword_w with (b := s) (x := v0); [reflexivity | apply zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (s + -16)%Z with (s - 16)%Z by lia. exact Cs0.
    - eapply ex_krange with (b := s); [reflexivity | lia | lia]. }
  pose proof (ex_st_open SEGS _ m rom fx regs 0xafe8c _ HR) as ST.
  exb_cont 40%nat (@nil Z) (SCR [] [] []) HK ST ltac:(fun _ => idtac).
  assert (HRA : Z_to_bv 64 (bv_unsigned ret) = ret) by apply zbv_self.
  exb_ret ST ret HRA Hret R HR' Hlf Hms.
  exists R. split; [exact Hms|].
  repeat split; try (ex_reg regs HR'; try apply zbv_self). ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma pixDebugFlipDetect_off : forall (fx : FPState) regs m (ret : word),
  getr regs 13 = Z_to_bv 64 0 -> getr regs 1 = ret -> ret_ok ret ->
  msteps SEGS (@mkst fx regs (0xb003c : word) m rom) (@mkst fx regs ret m rom).
Proof.
  intros fx regs m ret H13 H1 Hret.
  replace (0xb003c : word) with (Z_to_bv 64 0xb003c) by (apply bv_eq; reflexivity). norm_pc.
  fdl 0xb003c%Z F1 D1.
  chain_step; [reflexivity | eapply step_beq_tk; [exact F1 | reflexivity | exact D1 | regz regs H13] | step_simpl].
  fdl 0xb00d8%Z F2 D2.
  chain_step; [reflexivity | eapply step_jalr_x0; [exact F2 | reflexivity | rewrite D2; f_equal; f_equal; f_equal; apply bv_eq; reflexivity | exact H1] | step_simpl].
  lazymatch goal with |- msteps _ (@mkst _ _ ?p _ _) _ => replace p with ret by (symmetry; etransitivity; [|exact Hret]; reflexivity) end.
  apply mst_refl.
Qed.

(* [comment removed for export] *)
Section Decision.
Variables (regs0 : bvmap 5 word) (M : word -> option byte) (po : Z).
Hypothesis Hpo : (1 <= po)%Z.
Hypothesis Hpo64 : (po + 4 <= 2 ^ 64)%Z.
Hypothesis SOK : store_ok SEGS M (Z_to_bv 64 po) 4 = true.

Definition MPOST (fin : machine_state) : Prop :=
  exists fr' cs' regs' (Mf : word -> option byte),
    fin = @mkst (mkFP fr' cs') regs' (0xaffa8 : word) Mf rom /\ frm_zero cs' /\
    regs_agree (fun r => In r [12]%list) regs0 regs' /\
    (Mf = M \/ exists o, (1 <= o <= 4)%Z /\ Mf = wr4 M po o).

Local Ltac mopen regs FZ HR HK ST :=
  ex_entry regs (@nil Z) HR;
  assert (HK : know_ok SEGS (ex_env regs []) M [KWr (SA (EVar 10) 0) 4; KRange (EVar 10) 1 (2 ^ 64 - 4)]%Z) by ex_know regs;
  exb_open HR HK ST.
Local Ltac mdone HR AG :=
  pcto (0xaffa8 : word); apply reach_done; eexists _, _, _, _; split; [reflexivity|];
  split; [assumption|]; split; [xagree AG HR | left; reflexivity].
Local Ltac mgo L q regs HR AG :=
  pcto q; apply L; [assumption | xreg regs | xagree AG HR].

(* [comment removed for export] *)
Lemma mB_st : forall (o : Z) fr cs regs, (1 <= o <= 4)%Z -> frm_zero cs -> getr regs 10 = Z_to_bv 64 po -> getr regs 12 = Z_to_bv 64 o ->
  regs_agree (fun r => In r [12]%list) regs0 regs ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xaffa4 : word) M rom) MPOST.
Proof using All.
  intros o fr cs regs Ho FZ R10 R12 AG.
  replace (0xaffa4 : word) with (Z_to_bv 64 0xaffa4) by (apply bv_eq; reflexivity).
  mopen regs FZ HR HK ST.
  xrun [0xaffa8]%Z HK ST FZ.
  xexit ST HR. pcto (0xaffa8 : word). apply reach_done. eexists _, _, _, _. split; [reflexivity|].
  split; [assumption|]. split; [xagree AG HR|].
  right. exists o. split; [lia|]. unfold wr4. ex_mem_eq regs.
Qed.

Local Ltac mgost o regs HR AG :=
  pcto (0xaffa4 : word); apply (mB_st o); [lia | assumption | xreg regs | xreg regs | xagree AG HR].

(* [comment removed for export] *)
Lemma mB_c4 : forall fr cs regs, frm_zero cs -> getr regs 10 = Z_to_bv 64 po -> regs_agree (fun r => In r [12]%list) regs0 regs ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xaff90 : word) M rom) MPOST.
Proof using All.
  intros fr cs regs FZ R10 AG.
  replace (0xaff90 : word) with (Z_to_bv 64 0xaff90) by (apply bv_eq; reflexivity).
  mopen regs FZ HR HK ST.
  xrun [0xaffa4; 0xaffa8]%Z HK ST FZ.
  all: xexit ST HR.
  all: first [ mdone HR AG | mgost 4%Z regs HR AG ].
Qed.

(* [comment removed for export] *)
Lemma mB_c3 : forall fr cs regs, frm_zero cs -> getr regs 10 = Z_to_bv 64 po -> regs_agree (fun r => In r [12]%list) regs0 regs ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xaff74 : word) M rom) MPOST.
Proof using All.
  intros fr cs regs FZ R10 AG.
  replace (0xaff74 : word) with (Z_to_bv 64 0xaff74) by (apply bv_eq; reflexivity).
  mopen regs FZ HR HK ST.
  xrun [0xaff90; 0xaffa4]%Z HK ST FZ.
  all: xexit ST HR.
  all: first [ mgo mB_c4 (0xaff90 : word) regs HR AG | mgost 3%Z regs HR AG ].
Qed.

(* [comment removed for export] *)
Lemma mB_c2 : forall fr cs regs, frm_zero cs -> getr regs 10 = Z_to_bv 64 po -> regs_agree (fun r => In r [12]%list) regs0 regs ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xaff58 : word) M rom) MPOST.
Proof using All.
  intros fr cs regs FZ R10 AG.
  replace (0xaff58 : word) with (Z_to_bv 64 0xaff58) by (apply bv_eq; reflexivity).
  mopen regs FZ HR HK ST.
  xrun [0xaff74; 0xaffa4]%Z HK ST FZ.
  all: xexit ST HR.
  all: first [ mgo mB_c3 (0xaff74 : word) regs HR AG | mgost 2%Z regs HR AG ].
Qed.

(* [comment removed for export] *)
Lemma mB_c1 : forall fr cs regs, frm_zero cs -> getr regs 10 = Z_to_bv 64 po -> regs_agree (fun r => In r [12]%list) regs0 regs ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xaff3c : word) M rom) MPOST.
Proof using All.
  intros fr cs regs FZ R10 AG.
  replace (0xaff3c : word) with (Z_to_bv 64 0xaff3c) by (apply bv_eq; reflexivity).
  mopen regs FZ HR HK ST.
  xrun [0xaff58; 0xaffa4]%Z HK ST FZ.
  all: xexit ST HR.
  all: first [ mgo mB_c2 (0xaff58 : word) regs HR AG | mgost 1%Z regs HR AG ].
Qed.

(* [comment removed for export] *)
Lemma mB_lp : forall fr cs regs, frm_zero cs -> getr regs 10 = Z_to_bv 64 po -> regs_agree (fun r => In r [12]%list) regs0 regs ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xaff38 : word) M rom) MPOST.
Proof using All.
  intros fr cs regs FZ R10 AG.
  replace (0xaff38 : word) with (Z_to_bv 64 0xaff38) by (apply bv_eq; reflexivity).
  mopen regs FZ HR HK ST.
  xrun [0xaff3c]%Z HK ST FZ.
  all: xexit ST HR.
  all: mgo mB_c1 (0xaff3c : word) regs HR AG.
Qed.

Lemma mB_ln : forall fr cs regs, frm_zero cs -> getr regs 10 = Z_to_bv 64 po -> regs_agree (fun r => In r [12]%list) regs0 regs ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xaff04 : word) M rom) MPOST.
Proof using All.
  intros fr cs regs FZ R10 AG.
  replace (0xaff04 : word) with (Z_to_bv 64 0xaff04) by (apply bv_eq; reflexivity).
  mopen regs FZ HR HK ST.
  xrun [0xaff3c]%Z HK ST FZ.
  all: xexit ST HR.
  all: mgo mB_c1 (0xaff3c : word) regs HR AG.
Qed.

(* [comment removed for export] *)
Lemma mB_up : forall fr cs regs, frm_zero cs -> getr regs 10 = Z_to_bv 64 po -> regs_agree (fun r => In r [12]%list) regs0 regs ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xafef8 : word) M rom) MPOST.
Proof using All.
  intros fr cs regs FZ R10 AG.
  replace (0xafef8 : word) with (Z_to_bv 64 0xafef8) by (apply bv_eq; reflexivity).
  mopen regs FZ HR HK ST.
  xrun [0xaff38; 0xaff04]%Z HK ST FZ.
  all: xexit ST HR.
  all: first [ mgo mB_lp (0xaff38 : word) regs HR AG | mgo mB_ln (0xaff04 : word) regs HR AG ].
Qed.

Lemma mB_un : forall fr cs regs, frm_zero cs -> getr regs 10 = Z_to_bv 64 po -> regs_agree (fun r => In r [12]%list) regs0 regs ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xaff2c : word) M rom) MPOST.
Proof using All.
  intros fr cs regs FZ R10 AG.
  replace (0xaff2c : word) with (Z_to_bv 64 0xaff2c) by (apply bv_eq; reflexivity).
  mopen regs FZ HR HK ST.
  xrun [0xaff04; 0xaff38]%Z HK ST FZ.
  all: xexit ST HR.
  all: first [ mgo mB_lp (0xaff38 : word) regs HR AG | mgo mB_ln (0xaff04 : word) regs HR AG ].
Qed.

(* [comment removed for export] *)
Lemma mB_s : forall fr cs regs, frm_zero cs -> getr regs 10 = Z_to_bv 64 po -> regs_agree (fun r => In r [12]%list) regs0 regs ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xafef0 : word) M rom) MPOST.
Proof using All.
  intros fr cs regs FZ R10 AG.
  replace (0xafef0 : word) with (Z_to_bv 64 0xafef0) by (apply bv_eq; reflexivity).
  mopen regs FZ HR HK ST.
  xrun [0xaff2c; 0xafef8]%Z HK ST FZ.
  all: xexit ST HR.
  all: first [ mgo mB_un (0xaff2c : word) regs HR AG | mgo mB_up (0xafef8 : word) regs HR AG ].
Qed.

(* [comment removed for export] *)
Lemma mB_r : forall fr cs regs, frm_zero cs -> getr regs 10 = Z_to_bv 64 po -> regs_agree (fun r => In r [12]%list) regs0 regs ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xaff1c : word) M rom) MPOST.
Proof using All.
  intros fr cs regs FZ R10 AG.
  replace (0xaff1c : word) with (Z_to_bv 64 0xaff1c) by (apply bv_eq; reflexivity).
  mopen regs FZ HR HK ST.
  xrun [0xafef8; 0xaff2c]%Z HK ST FZ.
  all: xexit ST HR.
  all: first [ mgo mB_un (0xaff2c : word) regs HR AG | mgo mB_up (0xafef8 : word) regs HR AG ].
Qed.

(* [comment removed for export] *)
Lemma mB_u : forall fr cs regs, frm_zero cs -> getr regs 10 = Z_to_bv 64 po -> regs_agree (fun r => In r [12]%list) regs0 regs ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xaff0c : word) M rom) MPOST.
Proof using All.
  intros fr cs regs FZ R10 AG.
  replace (0xaff0c : word) with (Z_to_bv 64 0xaff0c) by (apply bv_eq; reflexivity).
  mopen regs FZ HR HK ST.
  xrun [0xafef0; 0xaff1c]%Z HK ST FZ.
  all: xexit ST HR.
  all: first [ mgo mB_s (0xafef0 : word) regs HR AG | mgo mB_r (0xaff1c : word) regs HR AG ].
Qed.

(* [comment removed for export] *)
Lemma mod_M : forall fr cs regs, frm_zero cs -> getr regs 10 = Z_to_bv 64 po -> regs_agree (fun r => In r [12]%list) regs0 regs ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xafee0 : word) M rom) MPOST.
Proof using All.
  intros fr cs regs FZ R10 AG.
  replace (0xafee0 : word) with (Z_to_bv 64 0xafee0) by (apply bv_eq; reflexivity).
  mopen regs FZ HR HK ST.
  xrun [0xaff0c; 0xaff1c; 0xafef0]%Z HK ST FZ.
  all: xexit ST HR.
  all: first [ mgo mB_u (0xaff0c : word) regs HR AG | mgo mB_r (0xaff1c : word) regs HR AG | mgo mB_s (0xafef0 : word) regs HR AG ].
Qed.

End Decision.

(* [comment removed for export] *)
Lemma mod_E : forall (fx : FPState) regs m, getr regs 11 = Z_to_bv 64 0 ->
  msteps SEGS (@mkst fx regs (0xaffa8 : word) m rom) (@mkst fx regs (0xafe8c : word) m rom).
Proof.
  intros fx regs m H11.
  replace (0xaffa8 : word) with (Z_to_bv 64 0xaffa8) by (apply bv_eq; reflexivity). norm_pc.
  fdl 0xaffa8%Z F1 D1.
  chain_step; [reflexivity | eapply step_beq_tk; [exact F1 | reflexivity | exact D1 | regz regs H11] | step_simpl].
  pcto (0xafe8c : word). apply mst_refl.
Qed.

End Segs.

Lemma str_mod_fmt : str16 0x1b5e0 53.
Proof. unfold str16. split; [vm_compute; reflexivity|]. split; [lia|]. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma str_mod_proc : str16 0x19cf1 18.
Proof. unfold str16. split; [vm_compute; reflexivity|]. split; [lia|]. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition MOD_STACK : Z := 16 + LSF.

Section ModW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Instance modw_fxd : FPState | 100 := mkFP bvmap_empty (Z_to_bv 32 0).

(* [comment removed for export] *)
Lemma MFR_cells : forall m s ret regs, (16 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS (MFR m s ret regs) (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS (MFR m s ret regs) (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)).
Proof.
  intros m s ret regs Hs1 Hs2. unfold MFR. split.
  - rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; lia).
    apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
  - apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
Qed.

(* [comment removed for export] *)
Theorem makeOrientDecision_W : forall fr cs C A m md regs (s po : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + MOD_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 po -> getr regs 11 = Z_to_bv 64 0 ->
  (s <= po)%Z -> (po + 4 <= c_top C)%Z -> (po mod 4 = 0)%Z ->
  (forall fr' cs' m' regs' (o : Z), W C A m' md -> frm_zero cs' -> cs_kept regs regs' -> (0 <= o <= 4)%Z ->
     POSTM C A s (wr4 m po o) m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (0xafe34 : word) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs s po ret S CK HW FZ H2 Hs16 Hlo Hhi H1 Hret H10 H11 Hspo Hpo4 Hpo40 HC.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold MOD_STACK, LSF in Hlo.
  assert (SOK1 : store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true)
    by (apply (W_sok_win C A m md (s - 16) 16 CK HW); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  assert (SOK2 : store_ok SEGS m (Z_to_bv 64 po) 4 = true)
    by (apply (W_sok_win C A m md po 4 CK HW); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  destruct (MFR_cells m s ret regs ltac:(lia) ltac:(lia)) as [C8 C16].
  assert (OUTM : forall (o : Z) (x : word), ~ (s - 16 <= u x < s)%Z -> wr4 (MFR m s ret regs) po o x = wr4 m po o x).
  { intros o x Hx. unfold wr4, MFR. pose proof (u64_range x) as Ux.
    destruct (Z_lt_le_dec (u x) po) as [Lx|Lx]; [|destruct (Z_lt_le_dec (u x) (po + 4)) as [Lx2|Lx2]].
    - rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). reflexivity.
    - rewrite !wbytes_inside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). reflexivity.
    - rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). reflexivity. }
  assert (HWp : forall o, W C A (wr4 m po o) md).
  { intros o. unfold wr4. apply (W_store_win C A m md); [exact CK | exact HW | rewrite u_Z2bv by lia; lia |].
    rewrite length_N_to_le_bytes, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (HWq : forall o, W C A (wr4 (MFR m s ret regs) po o) md).
  { intros o. unfold wr4, MFR.
    repeat (apply W_store_win; [exact CK | | rewrite u_Z2bv by lia; lia
                               | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
    exact HW. }
  assert (PMq : forall o, POSTM C A s (wr4 m po o) (wr4 (MFR m s ret regs) po o)).
  { intros o. apply (POSTM_range C A (wr4 m po o) md (wr4 (MFR m s ret regs) po o) (s - 16) s s CK (HWp o)); [| lia | lia | lia].
    intros x Hx. apply OUTM. exact Hx. }
  assert (TAIL : forall fr' cs' rX Mx (o : Z), frm_zero cs' -> W C A Mx md -> (0 <= o <= 4)%Z -> POSTM C A s (wr4 m po o) Mx ->
            rdn SEGS Mx (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
            rdn SEGS Mx (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) ->
            getr rX 2 = Z_to_bv 64 (s - 16) ->
            (forall r, In r [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rX r = getr regs r) ->
            realizes SEGS (mkCfg (@mkst (mkFP fr' cs') rX (0xafe8c : word) Mx al_rom) md) S).
  { intros fr' cs' rX Mx o FZx HWx Ho PMx E8 E16 Y2 CSx.
    destruct (mod_Z al_rom (mkFP fr' cs') rX Mx s ret (getr regs 8) ltac:(lia) ltac:(lia) Hret E8 E16 Y2) as (r4 & RUN4 & Z2 & Z10 & Z8 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWx)) | exact (mp_lazy _ (w_pure _ _ _ _ HWx)) | exact RUN4 |].
    apply (HC fr' cs' Mx r4 o HWx FZx); [| exact Ho | exact PMx | exact Z10].
    apply cs_kept_intro; csr; reflexivity. }
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | apply (mod_A al_rom fr cs regs m s po ret); first [lia | assumption] |].
  intros fin (fr1 & cs1 & r1 & pc1 & -> & FZ1 & Hpc & R2 & R10 & AG1).
  destruct Hpc as [-> | ->].
  - destruct (mod_N al_rom (mkFP fr1 cs1) r1 (wr4 (MFR m s ret regs) po 0%Z) (W_sev_got C A _ md (HWq 0%Z)) (W_sev C A _ md (HWq 0%Z)))
      as (r2 & RUN2 & Q1 & Q10 & Q11 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ (HWq 0%Z))) | exact (mp_lazy _ (w_pure _ _ _ _ (HWq 0%Z))) | exact RUN2 |].
    apply (lept_stderr1P8_W (fx := mkFP fr1 cs1) C A (wr4 (MFR m s ret regs) po 0%Z) md r2 (s - 16) 0x1b5e0 0x19cf1 53 18 (Z_to_bv 64 0xafe8c) S CK (HWq 0%Z)).
    + csr; reflexivity.
    + rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity.
    + unfold LSF; lia.
    + lia.
    + exact Q1.
    + red; apply bv_eq; reflexivity.
    + exact Q10.
    + exact Q11.
    + vm_compute; left; reflexivity.
    + exact str_mod_fmt.
    + exact str_mod_proc.
    + intros m2 r3 HW2 FR2 GR2 CS3.
      replace (Z_to_bv 64 0xafe8c) with (0xafe8c : word) by (apply bv_eq; reflexivity).
      apply (TAIL fr1 cs1 r3 m2 0%Z FZ1 HW2 ltac:(lia)).
      * apply (POSTM_range C A (wr4 m po 0%Z) md m2 (s - 16 - LSF) s s CK (HWp 0%Z)); [| unfold LSF; lia | lia | lia].
        intros x Hx. rewrite FR2 by (unfold LSF in *; lia). apply OUTM. unfold LSF in *; lia.
      * apply (rdn_after (wr4 (MFR m s ret regs) po 0%Z) m2 _ _ (s - 8) 8 _ FR2); [lia | lia | lia |].
        unfold wr4. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; lia). exact C8.
      * apply (rdn_after (wr4 (MFR m s ret regs) po 0%Z) m2 _ _ (s - 16) 8 _ FR2); [lia | lia | lia |].
        unfold wr4. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; lia). exact C16.
      * csr; reflexivity.
      * intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx.
  - assert (SOKp : store_ok SEGS (wr4 (MFR m s ret regs) po 0%Z) (Z_to_bv 64 po) 4 = true)
      by (apply (W_sok_win C A _ md po 4 CK (HWq 0%Z)); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    eapply rz_reach; [exact (w_pure _ _ _ _ (HWq 0%Z)) | apply (mod_M al_rom r1 (wr4 (MFR m s ret regs) po 0%Z) po ltac:(lia) ltac:(lia) SOKp fr1 cs1 r1 FZ1 R10 (regs_agree_refl _ _)) |].
    intros fin (fr2 & cs2 & r5 & Mf & -> & FZ2 & AG5 & HMf).
    assert (HMf' : exists o', (0 <= o' <= 4)%Z /\ Mf = wr4 (MFR m s ret regs) po o').
    { destruct HMf as [-> | (o & Ho & ->)]; [exists 0%Z; split; [lia | reflexivity] | exists o; split; [lia |]].
      unfold wr4. apply wbytes_shadow; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; [reflexivity | lia]. }
    destruct HMf' as (o' & Ho' & ->). clear HMf.
    assert (R11 : getr r5 11 = Z_to_bv 64 0) by (csr; reflexivity).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ (HWq o'))) | exact (mp_lazy _ (w_pure _ _ _ _ (HWq o'))) | exact (mod_E al_rom (mkFP fr2 cs2) r5 _ R11) |].
    apply (TAIL fr2 cs2 r5 _ o' FZ2 (HWq o') Ho' (PMq o')).
    + unfold wr4. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; lia). exact C8.
    + unfold wr4. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; lia). exact C16.
    + csr; reflexivity.
    + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx.
Qed.

End ModW.
