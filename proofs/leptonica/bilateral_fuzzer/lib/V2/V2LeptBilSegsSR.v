(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV FPStepsB Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptArith DitherLib DitherLoop LeptExec LeptExecX LeptExecFP LeptExecB LeptFPB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpBound FpReal FpSiteB FpSiteC ExpfModelB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBilSegs V2LeptExpfV.
From stdpp.bitvector Require Import tactics.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Section BilSegsSR.
Variable rom : word -> option byte.

#[local] Ltac exB_sc_hook ::= bw_hook.

Definition spl_rofree (lo hi : Z) : bool :=
  forallb (fun sg => orb (negb (seg_writable sg))
    (orb (Z.leb hi (Z.of_N (seg_base sg))) (Z.leb (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))%Z lo))) SEGS.

Lemma spl_find_in : forall segs a sg, find_segment segs a 1%Z = Some sg ->
  In sg segs /\ (Z.of_N (seg_base sg) <= a /\ a + 1 <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg))%Z.
Proof.
  induction segs as [|sg0 segs IH]; intros a sg H; [discriminate|].
  cbn [find_segment] in H.
  lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:E end.
  - injection H as <-. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2. split; [left; reflexivity | lia].
  - destruct (IH a sg H) as (Hin & Hb). split; [right; exact Hin | exact Hb].
Qed.

Lemma spl_wview_ro : forall (m : word -> option byte) (lo hi : Z) (a : word),
  spl_rofree lo hi = true -> (lo <= bv_unsigned a < hi)%Z -> m a = None -> wview SEGS m a = None.
Proof.
  intros m lo hi a RF Ha Hm. unfold wview. rewrite Hm.
  destruct (find_segment SEGS (bv_unsigned a) 1%Z) as [sg|] eqn:FS; [|reflexivity].
  destruct (spl_find_in _ _ _ FS) as (Hin & Hb).
  unfold spl_rofree in RF. rewrite forallb_forall in RF. specialize (RF sg Hin).
  destruct (seg_writable sg) eqn:W; [|reflexivity].
  cbn [negb orb] in RF. apply orb_true_iff in RF as [RF|RF]; apply Z.leb_le in RF; lia.
Qed.

Lemma spl_ro_keep : forall (m M : word -> option byte) (R : list (Z * Z)) (lo hi : Z),
  rinv R m M -> spl_rofree lo hi = true -> (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z ->
  (forall j, (lo <= j < hi)%Z -> m (Z_to_bv 64 j) = None) ->
  Forall (fun r => store_ok SEGS m (Z_to_bv 64 (fst r)) (Z.to_nat (snd r)) = true /\
                   (0 <= fst r)%Z /\ (0 < snd r)%Z /\ (fst r + snd r <= 2 ^ 64)%Z) R ->
  forall j, (lo <= j < hi)%Z -> M (Z_to_bv 64 j) = None.
Proof.
  intros m M R lo hi (MG & RI) RF Hlo Hhi HRO HR j Hj.
  rewrite RI; [apply HRO; exact Hj|].
  intros r Hr Hin. rewrite Forall_forall in HR. destruct (HR r Hr) as (SOK & H0 & H1 & H2).
  unfold inreg in Hin. rewrite u_Z2bv in Hin by lia.
  assert (Hw : wview SEGS m (Z_to_bv 64 j) <> None).
  { apply (store_ok_all SEGS m (Z.to_nat (snd r)) (Z_to_bv 64 (fst r))); rewrite ?u_Z2bv by lia; rewrite ?Z2Nat.id by lia;
      [lia | exact SOK | lia]. }
  apply Hw. apply (spl_wview_ro m lo hi); [exact RF | rewrite u_Z2bv by lia; lia | apply HRO; exact Hj].
Qed.

Definition spl_x (k : Z) : word := fpv_box FMT_S (fst (fp_of_int (fp_format FMT_S) RNE true 32%Z (bv_unsigned (Z_to_bv 64 (k * k))))).
Definition spl_w (d k : Z) : bv 32 :=
  Z_to_bv 32 (fst (fpv_ari F_DIV FMT_S RNE (bv_unsigned (unbox_s (fpv_sgnj F_SGNJN FMT_S (spl_x k) (spl_x k))))
                          (bv_unsigned (unbox_s (Z_to_bv 64 d))))).
Definition spl_cell (d k : Z) : Z := bv_unsigned (Z_to_bv 32 (expf_model (spl_w d k))).

Definition spl_cpost (w : bv 32) (fx : FPState) (regs : bvmap 5 word) (M : word -> option byte) (s : Z) (fin : machine_state) : Prop :=
  exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 237116) M' rom /\ frm_zero cs' /\
    (forall r : reg, In (bv_unsigned r) fs_list -> reg_get fr' r = reg_get (@fp_regs fx) r) /\
    reg_get fr' (10%bv : reg) = nan_box (Z_to_bv 32 (expf_model w)) /\
    regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs' /\ getr regs' 2 = Z_to_bv 64 (s - 320) /\
    rinv [((s - 336)%Z, 16%Z)] M M'.

Definition spl_call_ok (m : word -> option byte) (spat s : Z) : Prop :=
  forall (fx : FPState) regs (M : word -> option byte) (w : bv 32),
    rinv [(spat, 44%Z); ((s - 336)%Z, 16%Z)] m M -> frm_zero (@fp_csr fx) ->
    getr regs 2 = Z_to_bv 64 (s - 320) -> reg_get (@fp_regs fx) (10%bv : reg) = nan_box w ->
    reach SEGS (@mkst fx regs (Z_to_bv 64 237112) M rom) (spl_cpost w fx regs M s).

Lemma spl_get_set : forall (fr : bvmap 5 word) (r r' : reg) v,
  reg_get (bvmap_set r v fr) r' = if bv_eqb r r' then v else reg_get fr r'.
Proof.
  intros fr r r' v. unfold bv_eqb. destruct (Z.eqb_spec (bv_unsigned r) (bv_unsigned r')) as [E|E].
  - apply bv_eq in E. subst r'. apply fpv_get_same.
  - apply fpv_get_other. intros ->. apply E. reflexivity.
Qed.
Lemma spl_reg_eq : forall (fr : bvmap 5 word) (r r' : reg), r = r' -> reg_get fr r = reg_get fr r'.
Proof. intros fr r r' ->. reflexivity. Qed.
Ltac spl_frs :=
  repeat (rewrite spl_get_set;
          lazymatch goal with |- context [bv_eqb ?a ?b] =>
            let t := eval vm_compute in (bv_eqb a b) in change (bv_eqb a b) with t; cbv beta iota end).
Ltac spl_ev :=
  lazymatch goal with |- edenot _ (sr_get ?sr ?k) = _ =>
    let e := eval vm_compute in (sr_get sr k) in change (sr_get sr k) with e end;
  ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; bw_norm; first [reflexivity | f_equal; lia].
Ltac spl_fcvt ST FZ v :=
  let F := fresh "F" in let D := fresh "D" in let ST' := fresh "ST" in
  xb_fd ST F D;
  pose proof (xb_fcvt_fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RNE FMT_S true 32%Z v ST F ltac:(xb_ec) D
                ltac:(left; split; reflexivity) ltac:(left; repeat split; reflexivity) FZ ltac:(reflexivity) ltac:(spl_ev)) as ST';
  clear ST F D; rename ST' into ST; exb_norm ST.
Ltac spl_fsgnj ST :=
  let F := fresh "F" in let D := fresh "D" in let ST' := fresh "ST" in
  xb_fd ST F D;
  pose proof (xb_fsgnj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST F ltac:(xb_ec) D) as ST';
  clear ST F D; rename ST' into ST; exb_norm ST.
Ltac spl_fari ST FZ :=
  let F := fresh "F" in let D := fresh "D" in let ST' := fresh "ST" in
  xb_fd ST F D;
  pose proof (xb_fari _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RNE ST F ltac:(xb_ec) D
                ltac:(repeat apply fpv_frm_acc; exact FZ) ltac:(reflexivity)) as ST';
  clear ST F D; rename ST' into ST; exb_norm ST.

Lemma spl_rdn_hit : forall (M : word -> option byte) (a z : Z), (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z ->
  rdn SEGS (wbytes M (Z_to_bv 64 a) (Z_to_le_bytes 4 z)) (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 z).
Proof.
  intros M a z Ha Ha4. pose proof (SeqExec.rdn_wbytes_hit SEGS (Z_to_le_bytes 4 z) M (Z_to_bv 64 a)) as H.
  rewrite length_Z_to_le_bytes in H. apply H. rewrite u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.
Ltac spl_meq regs X10 :=
  cbn [mem_denot s_log e_addr e_width e_val]; apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs |];
  rewrite <- exf_store4; f_equal; ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
  rewrite Z_to_bv_bv_unsigned, X10, fpv_low32_box; reflexivity.
Ltac spl_rinv_m RI2 a p :=
  apply (rinv_wbytes _ _ _ p 4); [exact RI2 | rewrite length_Z_to_le_bytes; reflexivity | lia | lia |];
  exists (a, 44%Z); cbn [fst snd]; split; [cbn; tauto | lia].
Ltac spl_rinv_x RI' sl p n :=
  eapply rinv_trans;
  [ eapply rinv_weaken; [exact RI'|];
    let r := fresh "r" in let Hr := fresh "Hr" in
    intros r Hr; cbn [In] in Hr; destruct Hr as [<-|[]]; exists (sl, 16%Z); cbn [fst snd]; split; [cbn; tauto | lia]
  | apply (rinv_wbytes _ _ _ p 4); [apply rinv_refl | rewrite length_Z_to_le_bytes; reflexivity | lia | lia |];
    exists (p, n); cbn [fst snd]; split; [cbn; tauto | lia] ].
Ltac spl_agree AG HR HR' AG' HR2 HR3 :=
  eapply regs_agree_trans; [exact AG|];
  eapply regs_agree_trans; [ex_agree HR HR'|];
  eapply regs_agree_trans;
  [ eapply regs_agree_mono; [|exact AG']; let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbn [In] in Hr |- *; tauto
  | ex_agree HR2 HR3 ].
Ltac spl_fs FS FS' :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; rewrite fr_kept by (cbn; tauto); rewrite FS' by exact Hr; cbn [fp_regs];
  rewrite !fpv_get_other by (let Heq := fresh in intros Heq; subst r; vm_compute in Hr; intuition discriminate);
  rewrite fr_kept by (cbn; tauto); apply FS; exact Hr.
Ltac spl_reg regs HR := solve [ ex_reg regs HR | (ex_reg regs HR; rewrite zbv_addw_small by lia; f_equal; lia) ].

Lemma spl_loop : forall (m : word -> option byte) (s spat d : Z) (fr0 regs0 : bvmap 5 word),
  spl_call_ok m spat s ->
  (4096 + 336 <= s <= 2 ^ 47)%Z -> (4096 <= spat)%Z -> (spat + 44 <= s - 336)%Z ->
  store_ok SEGS m (Z_to_bv 64 spat) 44 = true -> reg_get fr0 9 = Z_to_bv 64 d ->
  forall (j : nat) (fr : bvmap 5 word) cs regs (M : word -> option byte) (i : Z),
  Z.of_nat j = (11 - i)%Z -> (0 <= i < 11)%Z -> frm_zero cs -> rinv [(spat, 44%Z); ((s - 336)%Z, 16%Z)] m M ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 8 = Z_to_bv 64 i -> getr regs 9 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 (11 - i) -> getr regs 19 = Z_to_bv 64 (spat + 4 * i) -> getr regs 20 = Z_to_bv 64 1 ->
  getr regs 21 = Z_to_bv 64 spat -> getr regs 23 = Z_to_bv 64 (spat + 4 * i) ->
  regs_agree (fun r => In r [1; 8; 10; 11; 12; 18; 19; 23]%list) regs0 regs ->
  (forall r : reg, In (bv_unsigned r) fs_list -> reg_get fr r = reg_get fr0 r) ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 237088) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 237160) M' rom /\ frm_zero cs' /\
      rinv [(spat, 44%Z); ((s - 336)%Z, 16%Z)] m M' /\
      rinv [((spat + 4 * i)%Z, (44 - 4 * i)%Z); ((s - 336)%Z, 16%Z)] M M' /\
      (forall k, (i <= k < 11)%Z -> rdn SEGS M' (Z_to_bv 64 (spat + 4 * k)) 4 = Some (Z_to_le_bytes 4 (spl_cell d k))) /\
      getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 11 /\ getr regs' 9 = Z_to_bv 64 1 /\
      getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 (spat + 44) /\ getr regs' 20 = Z_to_bv 64 1 /\
      getr regs' 21 = Z_to_bv 64 spat /\ getr regs' 23 = Z_to_bv 64 (spat + 44) /\
      regs_agree (fun r => In r [1; 8; 10; 11; 12; 18; 19; 23]%list) regs0 regs' /\
      (forall r : reg, In (bv_unsigned r) fs_list -> reg_get fr' r = reg_get fr0 r)).
Proof.
  intros m s spat d fr0 regs0 CALL Hs Hp1 Hp2 SOKa F9.
  induction j as [|j IH]; intros fr cs regs M i Hj Hi FZ RI H2 H8 H9 H18 H19 H20 H21 H23 AG FS; [lia|].
  assert (Hii : (0 <= i * i <= 100)%Z) by nia.
  ex_entry regs [(s - 320)%Z; spat; (spat + 4 * i)%Z; i; (11 - i)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 320)%Z; spat; (spat + 4 * i)%Z; i; (11 - i)%Z]) M
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47);
      KRange (EVar 35) 0 10; KRange (EVar 36) 1 11]) by (ex_know regs).
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [237100%Z] (SCR [false] [] []) (@nil (nat * nat)) HK ST FZ.
  spl_fcvt ST FZ (i * i)%Z.
  spl_fsgnj ST.
  spl_fari ST FZ.
  exb_exit ST R HR' Hlf Hms.
  eapply reach_msteps; [exact Hms|].
  eapply reach_bind; [apply (CALL _ R _ (spl_w d i)) |].
  { exact RI. }
  { cbn [fp_csr]. repeat apply fpv_frm_acc. exact FZ. }
  { ex_reg regs HR'. }
  { cbn [fp_regs]. spl_frs. cbv beta iota delta [fpv_read]. spl_frs.
    rewrite fr_kept by (cbn; tauto). rewrite FS by (unfold fs_list; in_list).
    rewrite (spl_reg_eq fr0 _ 9) by bveq. rewrite F9. reflexivity. }
  intros fin (fr' & cs' & regs' & M' & -> & FZ' & FS' & X10 & AG' & E2' & RI').
  assert (G8 : getr regs' 8 = Z_to_bv 64 i) by (rewrite AG' by notin_list; ex_reg regs HR').
  assert (G9 : getr regs' 9 = Z_to_bv 64 1) by (rewrite AG' by notin_list; ex_reg regs HR').
  assert (G18 : getr regs' 18 = Z_to_bv 64 (11 - i)) by (rewrite AG' by notin_list; ex_reg regs HR').
  assert (G19 : getr regs' 19 = Z_to_bv 64 (spat + 4 * i)) by (rewrite AG' by notin_list; ex_reg regs HR').
  assert (G20 : getr regs' 20 = Z_to_bv 64 1) by (rewrite AG' by notin_list; ex_reg regs HR').
  assert (G21 : getr regs' 21 = Z_to_bv 64 spat) by (rewrite AG' by notin_list; ex_reg regs HR').
  assert (G23 : getr regs' 23 = Z_to_bv 64 (spat + 4 * i)) by (rewrite AG' by notin_list; ex_reg regs HR').
  assert (RI2 : rinv [(spat, 44%Z); ((s - 336)%Z, 16%Z)] m M').
  { eapply rinv_trans; [exact RI|]. eapply rinv_weaken; [exact RI'|].
    intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. exists ((s - 336)%Z, 16%Z). cbn [fst snd]. split; [cbn; tauto | lia]. }
  assert (SOKc : store_ok SEGS M' (Z_to_bv 64 (spat + 4 * i)) 4 = true)
    by (apply (reg_sok SEGS m M' spat 44 (spat + 4 * i) 4); [exact (proj1 RI2) | exact SOKa | lia | cbn; lia | lia | cbn; lia]).
  ex_entry regs' [(s - 320)%Z; spat; (spat + 4 * i)%Z; i; (11 - i)%Z; bv_unsigned (reg_get fr' 10)] HR2.
  assert (HK2 : know_ok SEGS (ex_env regs' [(s - 320)%Z; spat; (spat + 4 * i)%Z; i; (11 - i)%Z; bv_unsigned (reg_get fr' 10)]) M'
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 4096 (2 ^ 47);
      KRange (EVar 35) 0 10; KRange (EVar 36) 1 11; KWr (SA (EVar 34) 0) 4]) by (ex_know regs').
  exb_open HR2 HK2 ST.
  exb_adriveS 8%nat 400%nat [237156%Z] (SCR [false; false] [] []) [(10%nat, 37%nat)] HK2 ST FZ'.
  destruct j as [|j].
  - exb_adriveS 8%nat 400%nat [237160%Z] (SCR [false] [] []) [(10%nat, 37%nat)] HK2 ST FZ'.
    exb_exit ST R2 HR3 Hlf2 Hms2.
    assert (Ei : i = 10%Z) by lia.
    lazymatch type of Hms2 with msteps _ _ (mkst _ _ ?MD _) =>
      assert (MEQ : wbytes M' (Z_to_bv 64 (spat + 4 * i)) (Z_to_le_bytes 4 (spl_cell d i)) = MD) end.
    { spl_meq regs' X10. }
    pose proof (ex_msteps_mem SEGS _ _ _ _ _ _ Hms2 MEQ) as Hms3.
    eexists; split; [exact Hms3|].
    do 4 eexists; split; [reflexivity|].
    split; [exact FZ'|].
    split; [spl_rinv_m RI2 spat (spat + 4 * i)%Z|].
    split; [spl_rinv_x RI' (s - 336)%Z (spat + 4 * i)%Z (44 - 4 * i)%Z|].
    split.
    { intros k Hk. assert (k = i) as -> by lia. apply spl_rdn_hit; lia. }
    repeat match goal with |- _ /\ _ => split end.
    all: first [ spl_reg regs' HR3 | spl_agree AG HR HR' AG' HR2 HR3 | spl_fs FS FS' ].
  - exb_adriveS 8%nat 400%nat [237088%Z] (SCR [true] [] []) [(10%nat, 37%nat)] HK2 ST FZ'.
    exb_exit ST R2 HR3 Hlf2 Hms2.
    lazymatch type of Hms2 with msteps _ _ (mkst _ _ ?MD _) =>
      assert (MEQ : wbytes M' (Z_to_bv 64 (spat + 4 * i)) (Z_to_le_bytes 4 (spl_cell d i)) = MD) end.
    { spl_meq regs' X10. }
    pose proof (ex_msteps_mem SEGS _ _ _ _ _ _ Hms2 MEQ) as Hms3.
    eapply reach_msteps; [exact Hms3|].
    assert (RIf : rinv [(spat, 44%Z); ((s - 336)%Z, 16%Z)] m
                    (wbytes M' (Z_to_bv 64 (spat + 4 * i)) (Z_to_le_bytes 4 (spl_cell d i)))) by (spl_rinv_m RI2 spat (spat + 4 * i)%Z).
    assert (RIx : rinv [((spat + 4 * i)%Z, (44 - 4 * i)%Z); ((s - 336)%Z, 16%Z)] M
                    (wbytes M' (Z_to_bv 64 (spat + 4 * i)) (Z_to_le_bytes 4 (spl_cell d i))))
      by (spl_rinv_x RI' (s - 336)%Z (spat + 4 * i)%Z (44 - 4 * i)%Z).
    assert (Cf : rdn SEGS (wbytes M' (Z_to_bv 64 (spat + 4 * i)) (Z_to_le_bytes 4 (spl_cell d i))) (Z_to_bv 64 (spat + 4 * i)) 4 =
                 Some (Z_to_le_bytes 4 (spl_cell d i))) by (apply spl_rdn_hit; lia).
    eapply reach_weaken; [| apply (IH _ cs' R2 _ (i + 1)%Z)].
    all: try (first [ lia | exact FZ' | exact RIf | spl_reg regs' HR3 | spl_agree AG HR HR' AG' HR2 HR3 | spl_fs FS FS' ]).
    intros fin (fr2 & cs2 & regs2 & M2 & -> & FZ2 & RIm & RIy & CELLS & P2).
    do 4 eexists. split; [reflexivity|]. split; [exact FZ2|]. split; [exact RIm|].
    split.
    { eapply rinv_trans; [exact RIx|]. eapply rinv_weaken; [exact RIy|].
      intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]].
      - exists ((spat + 4 * i)%Z, (44 - 4 * i)%Z). cbn [fst snd]. split; [cbn; tauto | lia].
      - exists ((s - 336)%Z, 16%Z). cbn [fst snd]. split; [cbn; tauto | lia]. }
    split; [|exact P2].
    intros k Hk. destruct (Z.eq_dec k i) as [->|Hne].
    + rewrite (rinv_rdn SEGS _ _ M2 (spat + 4 * i) 4 RIy); [exact Cf | lia | cbn; lia |].
      intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia.
    + apply CELLS. lia.
Qed.

Lemma spl_getr_same : forall regs (r r' : reg) (v v' : word), r = r' -> r' <> 0%bv -> v = v' -> getr (regupd regs r v) r' = v'.
Proof. intros regs r r' v v' -> H ->. apply getr_same. exact H. Qed.

Lemma SpL_seg : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s spat : Z),
  frm_zero cs ->
  (4096 + 336 <= s <= 2 ^ 47)%Z ->
  (4096 <= spat)%Z -> (spat + 44 <= s - 336)%Z -> (spat mod 16 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 spat) 44 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 336)) 16 = true ->
  (forall j, (0x133a0 <= j < 0x134e8)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (0x127b4 <= j < 0x127c0)%Z -> m (Z_to_bv 64 j) = None) ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 8 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 11 ->
  getr regs 19 = Z_to_bv 64 spat -> getr regs 20 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 spat -> getr regs 23 = Z_to_bv 64 spat ->
  reg_get fr 9 = Z_to_bv 64 0xffffffff42480000 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39e20) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39e68) M' rom /\ frm_zero cs' /\
      rinv [(spat, 44%Z); ((s - 336)%Z, 16%Z)] m M' /\ kcell_ok spat 11 M' /\
      getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 11 /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 18 = Z_to_bv 64 0 /\
      getr regs' 19 = Z_to_bv 64 (spat + 44) /\ getr regs' 20 = Z_to_bv 64 1 /\ getr regs' 21 = Z_to_bv 64 spat /\
      getr regs' 23 = Z_to_bv 64 (spat + 44) /\
      regs_agree (fun r => In r [1; 8; 10; 11; 12; 18; 19; 23]%list) regs regs' /\
      (forall r : reg, In (bv_unsigned r) fs_list -> reg_get fr' r = reg_get fr r)).
Proof.
  intros fr cs regs m s spat FZ Hs Hp1 Hp2 ALp SOKa SOKs RO1 RO2 H2 H8 H9 H18 H19 H20 H21 H23 F9.
  assert (CALL : spl_call_ok m spat s).
  { intros fx R M w RI FZx HR2 H10.
    let F := fresh "F" in let D := fresh "D" in ex_fetch SEGS 237112%Z F D;
      eapply reach_step; [reflexivity | exact (step_jal_link _ _ _ _ _ _ _ _ F eq_refl D) |].
    lazymatch goal with |- context [bv_eqb ?a ?b] =>
      let t := eval vm_compute in (bv_eqb a b) in change (bv_eqb a b) with t end.
    cbv beta iota.
    lazymatch type of (expf_runV rom) with context [@mkst _ _ ?pe _ _] =>
      lazymatch goal with |- reach _ (@mkst _ _ ?pc _ _) _ => replace pc with pe by bveq end end.
    eapply reach_weaken; [| eapply (expf_runV rom fx _ M (s - 320) (Z_to_bv 64 237116) w)].
    - intros fin (fr' & cs' & regs' & M' & -> & FZ' & FS' & X10 & AG' & E2' & RI').
      unfold spl_cpost.
      exists fr', cs', regs', M'. split; [reflexivity|]. split; [exact FZ'|]. split; [exact FS'|]. split; [exact X10|].
      split; [| split; [exact E2' | replace (s - 336)%Z with (s - 320 - 16)%Z by lia; exact RI']].
      intros r Hr. destruct (decide (r = (2%bv : reg))) as [->|N2]; [rewrite E2'; symmetry; exact HR2|].
      rewrite AG'.
      + apply getr_other. intros ->. apply Hr. cbn [In]. left. bveq.
      + intros Hin. cbn [In] in Hin. destruct Hin as [Hin|[Hin|[Hin|[Hin|[]]]]];
          [exact (N2 (eq_sym Hin)) | apply Hr; cbn [In]; tauto ..].
    - exact FZx.
    - red. apply bv_eq. reflexivity.
    - apply spl_getr_same; [bveq | reg_neq_tac | bveq].
    - rewrite getr_other by reg_neq_tac. exact HR2.
    - exact H10.
    - lia.
    - replace (s - 320 - 16)%Z with (s - 336)%Z by lia.
      apply (reg_sok SEGS m M (s - 336) 16 (s - 336) 16); [exact (proj1 RI) | exact SOKs | lia | cbn; lia | lia | cbn; lia].
    - eapply (spl_ro_keep m M); [exact RI | vm_compute; reflexivity | lia | lia | first [exact RO1 | exact RO2] |].
      apply Forall_cons; [cbn [fst snd]; split; [exact SOKa | lia] |].
      apply Forall_cons; [cbn [fst snd]; split; [exact SOKs | lia] | apply Forall_nil].
    - eapply (spl_ro_keep m M); [exact RI | vm_compute; reflexivity | lia | lia | first [exact RO1 | exact RO2] |].
      apply Forall_cons; [cbn [fst snd]; split; [exact SOKa | lia] |].
      apply Forall_cons; [cbn [fst snd]; split; [exact SOKs | lia] | apply Forall_nil]. }
  eapply reach_weaken; [| apply (spl_loop m s spat _ fr regs CALL Hs Hp1 Hp2 SOKa F9 11 fr cs regs m 0%Z)].
  all: try (first [ lia | assumption | apply rinv_refl | apply regs_agree_refl | (intros; reflexivity)
                  | (lazymatch goal with |- getr ?R ?k = _ =>
                       match goal with H : getr R k = _ |- _ => rewrite H; f_equal; lia end end) ]).
  intros fin (fr' & cs' & regs' & M' & -> & FZ' & RIm & _ & CELLS & P2).
  exists fr', cs', regs', M'. split; [reflexivity|]. split; [exact FZ'|]. split; [exact RIm|].
  split; [|exact P2].
  intros k Hk. eexists. split; [apply CELLS; lia|].
  apply (FBb_forall fmt_single 1 (spl_cell _) 11); [vm_compute; reflexivity | lia].
Qed.

Lemma rgl_getr_cv : forall rs (r r' : reg) v, bv_unsigned r' = bv_unsigned r -> getr rs r = v -> getr rs r' = v.
Proof. intros rs r r' v E H. rewrite <- H. f_equal. apply bv_eq. exact E. Qed.
Ltac rgl_canon :=
  repeat match goal with
  | |- context [@BV 5 ?z ?p] =>
      let c := constr:(@BV 5 z (I <: BvWf 5 z)) in
      tryif constr_eq (@BV 5 z p) c then fail else replace (@BV 5 z p) with c by (apply bv_eq; reflexivity)
  end.
Ltac rgl_fd F D :=
  lazymatch goal with
  | |- msteps _ (@mkst _ _ ?pc _ _) _ =>
      let f := eval vm_compute in (fetch_word SEGS pc) in
      lazymatch f with
      | Some ?w =>
          assert (F : fetch_word SEGS pc = Some w) by (vm_cast_no_check (eq_refl (Some w)));
          let d := eval vm_compute in (decode_any w) in
          assert (D : decode_any w = d) by (vm_cast_no_check (eq_refl d))
      end
  end.
Ltac rgl_st tac := let F := fresh "F" in let D := fresh "D" in rgl_fd F D; tac F D; clear F D; rgl_canon.
Ltac rgl_rne := let H := fresh "H" in intro H; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H.
Ltac rgl_fpn := rgl_canon; cbn [fp_regs fp_csr]; unfold fpv_sgnj; cbn [fpv_box];
  repeat first [ rewrite fpv_read_S_box | rewrite fpv_unbox_box | rewrite fpv_read_other by rgl_rne
               | rewrite fpv_get_same | rewrite fpv_get_other by rgl_rne ].
Ltac rgl_fzero Hz := cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz.
Ltac rgl_fcvt F D Hz := chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F | reflexivity | exact D | left; split; reflexivity
  | right; left; repeat split; reflexivity | rgl_fzero Hz | reflexivity] | step_simpl ]; rgl_fpn.
Ltac rgl_fsgnj F D := chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F | reflexivity | exact D] | step_simpl ]; rgl_fpn.
Ltac rgl_fari F D Hz := chain_step; [ reflexivity | eapply fpv_step_fari; [exact F | reflexivity | exact D | rgl_fzero Hz | reflexivity] | step_simpl ]; rgl_fpn.
Ltac rgl_pin := repeat match goal with
  | H : getr ?rs ?r = ?v |- context [getr ?rs ?r'] =>
      let b := eval vm_compute in (Z.eqb (bv_unsigned r) (bv_unsigned r')) in
      lazymatch b with true => rewrite (rgl_getr_cv rs r r' v ltac:(vm_compute; reflexivity) H) end
  end.
Ltac rgl_zval := rgl_canon; gres; rgl_pin; imm_norm; rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia].
Ltac rgl_zv F D v := stepat F D v rgl_zval.
Ltac rgl_rv := gres; rgl_pin; first [reflexivity | f_equal; lia].
Ltac rgl_cond := rgl_canon; gres; rgl_pin; first [ condZ | reflexivity | (vm_compute; reflexivity) ].
Ltac rgl_fsw F D adr SOK := chain_step; [ reflexivity | eapply fp_step_fsw with (a := adr); [exact F | reflexivity | exact D | rgl_zval | exact SOK] | step_simpl ].
Ltac rgl_pc p := lazymatch goal with |- reach _ (@mkst _ _ ?q _ _) _ => replace q with p by (apply bv_eq; reflexivity) end.

Lemma rgl_sltiu0 : forall a, (1 <= a < 2 ^ 64)%Z -> v_sltiu (Z_to_bv 64 a) 1 = Z_to_bv 64 0.
Proof. intros a Ha. rewrite v_sltiu_Z by lia. replace (a <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma rgl_rdn_hit : forall (m : word -> option byte) (a z : Z), (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z ->
  rdn SEGS (wbytes m (Z_to_bv 64 a) (Z_to_le_bytes 4 z)) (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 z).
Proof.
  intros m a z Ha Ha4. pose proof (SeqExec.rdn_wbytes_hit SEGS (Z_to_le_bytes 4 z) m (Z_to_bv 64 a)) as H.
  rewrite length_Z_to_le_bytes in H. apply H. rewrite u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Lemma rgl_find_ro : forall (segs : list Segment) (lo hi j : Z) sg,
  forallb (fun g => negb (seg_writable g) || (hi <=? Z.of_N (seg_base g))%Z || (Z.of_N (seg_base g) + Z.of_N (seg_size g) <=? lo)%Z) segs = true ->
  (lo <= j < hi)%Z -> find_segment segs j 1 = Some sg -> seg_writable sg = false.
Proof.
  induction segs as [|g segs IH]; intros lo hi j sg HF Hj HS; [discriminate HS|].
  cbn [forallb] in HF. apply andb_prop in HF as [H1 H2].
  cbn [find_segment] in HS.
  match type of HS with context [if ?c then _ else _] => destruct c eqn:E end.
  - injection HS as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    apply orb_prop in H1 as [H1|H1]; [apply orb_prop in H1 as [H1|H1]|].
    + destruct (seg_writable g); [discriminate H1 | reflexivity].
    + apply Z.leb_le in H1. lia.
    + apply Z.leb_le in H1. lia.
  - exact (IH lo hi j sg H2 Hj HS).
Qed.

Lemma rgl_wv_ro : forall (m : word -> option byte) (lo hi j : Z),
  forallb (fun g => negb (seg_writable g) || (hi <=? Z.of_N (seg_base g))%Z || (Z.of_N (seg_base g) + Z.of_N (seg_size g) <=? lo)%Z) SEGS = true ->
  (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z -> (lo <= j < hi)%Z -> m (Z_to_bv 64 j) = None -> wview SEGS m (Z_to_bv 64 j) = None.
Proof.
  intros m lo hi j HF Hlo Hhi Hj Hm. unfold wview. rewrite Hm. rewrite u_Z2bv by lia.
  destruct (find_segment SEGS j 1) as [sg|] eqn:HS; [|reflexivity].
  rewrite (rgl_find_ro SEGS lo hi j sg HF Hj HS). reflexivity.
Qed.

Section rgl_Loop.
Variables (s rng f8v : Z) (M0 : word -> option byte).
Definition rgl_R : list (Z * Z) := [(rng, 1024%Z); ((s - 336)%Z, 16%Z)].
Definition rgl_CL : list reg := [1; 2; 9; 10; 11; 12; 25; 26]%bv.
Hypothesis GEO : (4096 + 336 <= s <= 2 ^ 47 /\ 4096 <= rng /\ rng + 1024 <= s - 336 /\ rng mod 16 = 0)%Z.
Hypothesis SOKr : store_ok SEGS M0 (Z_to_bv 64 rng) 1024 = true.
Hypothesis SOKs : store_ok SEGS M0 (Z_to_bv 64 (s - 336)) 16 = true.
Hypothesis RO1 : forall j, (0x133a0 <= j < 0x134e8)%Z -> M0 (Z_to_bv 64 j) = None.
Hypothesis RO2 : forall j, (0x127b4 <= j < 0x127c0)%Z -> M0 (Z_to_bv 64 j) = None.
Hypothesis HFB : forall i, (0 <= i < 256)%Z -> FB fmt_single 1 (bil_cell (bv_unsigned (unbox_s (Z_to_bv 64 f8v))) i).

Lemma rgl_ro_out : forall (lo : Z) (n : nat) (y : Z), store_ok SEGS M0 (Z_to_bv 64 lo) n = true -> (0 <= lo)%Z -> (lo + Z.of_nat n <= 2 ^ 64)%Z ->
  ((0x133a0 <= y < 0x134e8) \/ (0x127b4 <= y < 0x127c0))%Z -> ~ (lo <= y < lo + Z.of_nat n)%Z.
Proof using GEO SOKr SOKs RO1 RO2.
  intros lo n y SOK Hlo Hn Hy Hin.
  assert (Hm : M0 (Z_to_bv 64 y) = None) by (destruct Hy; [apply RO1 | apply RO2]; lia).
  assert (Hw : wview SEGS M0 (Z_to_bv 64 y) <> None).
  { apply (store_ok_all SEGS M0 n (Z_to_bv 64 lo)); rewrite ?u_Z2bv by lia; [lia | exact SOK | lia]. }
  apply Hw. destruct Hy as [Hy|Hy].
  - apply (rgl_wv_ro M0 0x133a0 0x134e8 y); [vm_compute; reflexivity | lia | lia | lia | exact Hm].
  - apply (rgl_wv_ro M0 0x127b4 0x127c0 y); [vm_compute; reflexivity | lia | lia | lia | exact Hm].
Qed.

Lemma rgl_ro : forall M, rinv rgl_R M0 M ->
  (forall j, (0x133a0 <= j < 0x134e8)%Z -> M (Z_to_bv 64 j) = None) /\ (forall j, (0x127b4 <= j < 0x127c0)%Z -> M (Z_to_bv 64 j) = None).
Proof using GEO SOKr SOKs RO1 RO2.
  intros M RI. pose proof GEO as (Gs & Gr & Grs & ALr). destruct RI as [_ RI'].
  assert (OUT : forall j, ((0x133a0 <= j < 0x134e8) \/ (0x127b4 <= j < 0x127c0))%Z -> M (Z_to_bv 64 j) = M0 (Z_to_bv 64 j)).
  { intros j Hj. apply RI'. intros r Hr. unfold rgl_R in Hr. cbn [In] in Hr. unfold inreg. rewrite u_Z2bv by lia.
    destruct Hr as [<-|[<-|[]]]; cbn [fst snd].
    - pose proof (rgl_ro_out rng 1024 j SOKr ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) Hj) as H.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H. lia.
    - pose proof (rgl_ro_out (s - 336) 16 j SOKs ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) Hj) as H.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H. lia. }
  split; intros j Hj; rewrite OUT by lia; [apply RO1 | apply RO2]; exact Hj.
Qed.

Lemma rgl_loop : forall (j : nat) fr0 regs0 fr cs regs (M : word -> option byte) (i : Z),
  Z.of_nat j = (256 - i)%Z -> (0 <= i < 256)%Z -> frm_zero cs -> rinv rgl_R M0 M ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 8 = Z_to_bv 64 256 -> getr regs 9 = Z_to_bv 64 i ->
  getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 rng ->
  getr regs 25 = Z_to_bv 64 (rng + 4 * i) -> getr regs 26 = Z_to_bv 64 (rng + 4 * i) ->
  reg_get fr 8 = Z_to_bv 64 f8v ->
  regs_agree (fun r => In r rgl_CL) regs0 regs -> (forall r : reg, In (bv_unsigned r) fs_list -> reg_get fr r = reg_get fr0 r) ->
  reach SEGS (@mkst (mkFP fr cs) regs (0x39eb0 : word) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (0x39eec : word) M' rom /\ frm_zero cs' /\
       rinv rgl_R M0 M' /\ rinv [((rng + 4 * i)%Z, (1024 - 4 * i)%Z); ((s - 336)%Z, 16%Z)] M M' /\
       getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 256 /\ getr regs' 9 = Z_to_bv 64 256 /\
       getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 rng /\
       getr regs' 25 = Z_to_bv 64 (rng + 1024) /\ getr regs' 26 = Z_to_bv 64 (rng + 1024) /\
       regs_agree (fun r => In r rgl_CL) regs0 regs' /\
       (forall r : reg, In (bv_unsigned r) fs_list -> reg_get fr' r = reg_get fr0 r) /\
       (forall jj, (i <= jj < 256)%Z -> exists x, rdn SEGS M' (Z_to_bv 64 (rng + 4 * jj)) 4 = Some (Z_to_le_bytes 4 x) /\ FB fmt_single 1 x)).
Proof using GEO SOKr SOKs RO1 RO2 HFB.
  induction j as [|j IH]; intros fr0 regs0 fr cs regs M i Hj Hi FZ RI E2 E8 E9 E18 E19 E23 E25 E26 F8 AG FS; [lia|].
  pose proof GEO as (Gs & Gr & Grs & ALr).
  destruct (rgl_ro M RI) as (ROa & ROb).
  assert (Hii : (0 <= i * i < 2 ^ 31)%Z) by nia.
  eapply reach_msteps.
  { rgl_st ltac:(fun F D => rgl_zv F D (Z_to_bv 64 (i * i))).
    rgl_st ltac:(fun F D => rgl_fcvt F D FZ).
    rgl_st ltac:(fun F D => rgl_fsgnj F D).
    rgl_st ltac:(fun F D => rgl_fari F D FZ).
    rgl_st ltac:(fun F D => stepj F D).
    apply mst_refl. }
  eapply reach_bind.
  { apply (expf_runV rom _ _ _ (s - 320) (Z_to_bv 64 0x39ec4) (Z_to_bv 32 (bil_arg (bv_unsigned (unbox_s (Z_to_bv 64 f8v))) i))).
    - rgl_fzero FZ.
    - red; apply bv_eq; reflexivity.
    - gres; reflexivity.
    - gres; rgl_pin; reflexivity.
    - cbn [fp_regs]. rewrite fpv_get_same. unfold bil_arg, fneg32, u64, ES, fpv_read, fpv_ari. rewrite F8. gres. reflexivity.
    - lia.
    - replace (s - 320 - 16)%Z with (s - 336)%Z by lia.
      apply (reg_sok SEGS M0 M (s - 336) 16 (s - 336) 16); [exact (proj1 RI) | exact SOKs | lia | lia | lia | lia].
    - exact ROa.
    - exact ROb. }
  intros fin (fr2 & cs2 & regs2 & M2 & -> & FZ2 & FS2 & XV & AG2 & E2' & RI2).
  assert (RIa : rinv rgl_R M0 M2).
  { eapply rinv_trans; [exact RI|]. eapply rinv_weaken; [exact RI2|].
    intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. exists ((s - 336)%Z, 16%Z). cbn [fst snd]. split; [unfold rgl_R; cbn; tauto | lia]. }
  assert (RIb : rinv [((rng + 4 * i)%Z, (1024 - 4 * i)%Z); ((s - 336)%Z, 16%Z)] M M2).
  { eapply rinv_weaken; [exact RI2|].
    intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. exists ((s - 336)%Z, 16%Z). cbn [fst snd]. split; [cbn; tauto | lia]. }
  assert (SOK2 : store_ok SEGS M2 (Z_to_bv 64 (rng + 4 * i)) 4 = true)
    by (apply (reg_sok SEGS M0 M2 rng 1024 (rng + 4 * i) 4); [exact (proj1 RIa) | exact SOKr | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                                             | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
  assert (G8 : getr regs2 8 = Z_to_bv 64 256) by (rewrite (AG2 8) by notin_list; gres; rgl_pin; reflexivity).
  assert (G9 : getr regs2 9 = Z_to_bv 64 i) by (rewrite (AG2 9) by notin_list; gres; rgl_pin; reflexivity).
  assert (G18 : getr regs2 18 = Z_to_bv 64 1) by (rewrite (AG2 18) by notin_list; gres; rgl_pin; reflexivity).
  assert (G19 : getr regs2 19 = Z_to_bv 64 1) by (rewrite (AG2 19) by notin_list; gres; rgl_pin; reflexivity).
  assert (G23 : getr regs2 23 = Z_to_bv 64 rng) by (rewrite (AG2 23) by notin_list; gres; rgl_pin; reflexivity).
  assert (G25 : getr regs2 25 = Z_to_bv 64 (rng + 4 * i)) by (rewrite (AG2 25) by notin_list; gres; rgl_pin; reflexivity).
  assert (G26 : getr regs2 26 = Z_to_bv 64 (rng + 4 * i)) by (rewrite (AG2 26) by notin_list; gres; rgl_pin; reflexivity).
  assert (FSr : forall r : reg, In (bv_unsigned r) fs_list -> reg_get fr2 r = reg_get fr0 r).
  { intros r Hr.
    assert (N10 : r <> (10 : reg)) by (let EQ := fresh in intros EQ; subst r; vm_compute in Hr; intuition discriminate).
    assert (N15 : r <> (15 : reg)) by (let EQ := fresh in intros EQ; subst r; vm_compute in Hr; intuition discriminate).
    rewrite FS2 by exact Hr. cbn [fp_regs]. rewrite !fpv_get_other by assumption. exact (FS r Hr). }
  assert (F8' : reg_get fr2 8 = Z_to_bv 64 f8v)
    by (rewrite FS2 by (unfold fs_list; in_list); cbn [fp_regs]; rewrite !fpv_get_other by rgl_rne; exact F8).
  replace (Z_to_bv 64 0x39ec4) with (0x39ec4 : word) by (apply bv_eq; reflexivity).
  eapply reach_msteps.
  { rgl_st ltac:(fun F D => stepb_ft F D ltac:(rgl_cond)).
    rgl_st ltac:(fun F D => stepat F D (Z_to_bv 64 0) ltac:(rgl_canon; gres; rgl_pin; imm_norm; apply rgl_sltiu0; lia)).
    rgl_st ltac:(fun F D => stepat F D (Z_to_bv 64 1) ltac:(rgl_canon; gres; rgl_pin; first [reflexivity | (apply bv_eq; vm_compute; reflexivity)])).
    rgl_st ltac:(fun F D => stepb_ft F D ltac:(rgl_cond)).
    rgl_st ltac:(fun F D => stepb_ft F D ltac:(rgl_cond)).
    rgl_st ltac:(fun F D => rgl_fsw F D (Z_to_bv 64 (rng + 4 * i)) SOK2).
    rgl_st ltac:(fun F D => rgl_zv F D (Z_to_bv 64 (i + 1))).
    rgl_st ltac:(fun F D => rgl_zv F D (Z_to_bv 64 (rng + 4 * (i + 1)))).
    rgl_st ltac:(fun F D => rgl_zv F D (Z_to_bv 64 (rng + 4 * (i + 1)))).
    apply mst_refl. }
  set (M4 := wbytes M2 _ _).
  assert (RI4 : rinv rgl_R M0 M4).
  { subst M4. apply (rinv_wbytes rgl_R M0 M2 (rng + 4 * i) 4); [exact RIa | rewrite length_Z_to_le_bytes; reflexivity | lia | lia |].
    exists (rng, 1024%Z). cbn [fst snd]. split; [unfold rgl_R; cbn; tauto | lia]. }
  assert (RIb4 : rinv [((rng + 4 * i)%Z, (1024 - 4 * i)%Z); ((s - 336)%Z, 16%Z)] M M4).
  { subst M4. apply (rinv_wbytes _ M M2 (rng + 4 * i) 4); [exact RIb | rewrite length_Z_to_le_bytes; reflexivity | lia | lia |].
    exists ((rng + 4 * i)%Z, (1024 - 4 * i)%Z). cbn [fst snd]. split; [cbn; tauto | lia]. }
  assert (VAL4 : rdn SEGS M4 (Z_to_bv 64 (rng + 4 * i)) 4 = Some (Z_to_le_bytes 4 (bil_cell (bv_unsigned (unbox_s (Z_to_bv 64 f8v))) i))).
  { subst M4. rewrite rgl_rdn_hit by lia. do 2 f_equal. cbn [fp_regs]. rewrite XV, fpv_low32_box. reflexivity. }
  destruct j as [|j].
  - eapply reach_msteps.
    { rgl_st ltac:(fun F D => stepb_ft F D ltac:(rgl_cond)). apply mst_refl. }
    rgl_pc (0x39eec : word).
    apply reach_done. do 4 eexists. split; [reflexivity|].
    split; [exact FZ2|]. split; [exact RI4|]. split; [exact RIb4|].
    do 8 (split; [rgl_rv|]).
    split; [unfold rgl_CL in AG |- *; ra_chain|].
    split; [exact FSr|].
    intros jj Hjj. assert (jj = i) as -> by lia.
    exists (bil_cell (bv_unsigned (unbox_s (Z_to_bv 64 f8v))) i). split; [exact VAL4 | apply HFB; lia].
  - eapply reach_msteps.
    { rgl_st ltac:(fun F D => stepb_tk F D ltac:(rgl_cond)). apply mst_refl. }
    rgl_pc (0x39eb0 : word).
    eapply reach_weaken; [| eapply (IH fr0 regs0 _ _ _ M4 (i + 1)%Z ltac:(lia) ltac:(lia))].
    + intros fin (fr' & cs' & regs' & M' & -> & FZ' & RI' & RIx & E2f & E8f & E9f & E18f & E19f & E23f & E25f & E26f & AGf & FSf & VALf).
      exists fr', cs', regs', M'. split; [reflexivity|]. split; [exact FZ'|]. split; [exact RI'|].
      split.
      { eapply rinv_trans; [exact RIb4|]. eapply rinv_weaken; [exact RIx|].
        intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]].
        - exists ((rng + 4 * i)%Z, (1024 - 4 * i)%Z). cbn [fst snd]. split; [cbn; tauto | lia].
        - exists ((s - 336)%Z, 16%Z). cbn [fst snd]. split; [cbn; tauto | lia]. }
      do 8 (split; [assumption|]).
      split; [exact AGf|]. split; [exact FSf|].
      intros jj Hjj. destruct (Z.eq_dec jj i) as [->|Hne].
      * exists (bil_cell (bv_unsigned (unbox_s (Z_to_bv 64 f8v))) i). split; [|apply HFB; lia].
        rewrite (rinv_rdn SEGS _ M4 M' (rng + 4 * i) 4 RIx); [exact VAL4 | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
        intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
      * apply VALf. lia.
    + exact FZ2.
    + exact RI4.
    + rgl_rv.
    + rgl_rv.
    + rgl_rv.
    + rgl_rv.
    + rgl_rv.
    + rgl_rv.
    + rgl_rv.
    + rgl_rv.
    + exact F8'.
    + unfold rgl_CL in AG |- *. ra_chain.
    + exact FSr.
Qed.
End rgl_Loop.

Lemma RgL_seg : forall (fr : bvmap 5 word) cs regs (m : word -> option byte) (s rng : Z),
  frm_zero cs ->
  (4096 + 336 <= s <= 2 ^ 47)%Z ->
  (4096 <= rng)%Z -> (rng + 1024 <= s - 336)%Z -> (rng mod 16 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 rng) 1024 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 336)) 16 = true ->
  (forall j, (0x133a0 <= j < 0x134e8)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (0x127b4 <= j < 0x127c0)%Z -> m (Z_to_bv 64 j) = None) ->
  getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 8 = Z_to_bv 64 256 -> getr regs 9 = Z_to_bv 64 0 -> getr regs 18 = Z_to_bv 64 1 ->
  getr regs 19 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 rng -> getr regs 25 = Z_to_bv 64 rng -> getr regs 26 = Z_to_bv 64 rng ->
  reg_get fr 8 = Z_to_bv 64 0xffffffff43480000 ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x39eb0) m rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x39eec) M' rom /\ frm_zero cs' /\
      rinv [(rng, 1024%Z); ((s - 336)%Z, 16%Z)] m M' /\ kcell_ok rng 256 M' /\
      getr regs' 2 = Z_to_bv 64 (s - 320) /\ getr regs' 8 = Z_to_bv 64 256 /\ getr regs' 9 = Z_to_bv 64 256 /\
      getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 rng /\
      getr regs' 25 = Z_to_bv 64 (rng + 1024) /\ getr regs' 26 = Z_to_bv 64 (rng + 1024) /\
      regs_agree (fun r => In r [1; 9; 10; 11; 12; 25; 26]%list) regs regs' /\
      (forall r : reg, In (bv_unsigned r) fs_list -> reg_get fr' r = reg_get fr r)).
Proof.
Proof.
  intros fr cs regs m s rng FZ Hs Hr1 Hr2 ALr SOKr SOKs RO1 RO2 H2 H8 H9 H18 H19 H23 H25 H26 F8.
  lazymatch type of F8 with reg_get _ _ = Z_to_bv 64 ?v =>
    assert (HFB : forall i, (0 <= i < 256)%Z -> FB fmt_single 1 (bil_cell (bv_unsigned (unbox_s (Z_to_bv 64 v))) i))
      by (intros i Hi; exact (FBb_forall fmt_single 1 (bil_cell (bv_unsigned (unbox_s (Z_to_bv 64 v)))) 256 ltac:(vm_compute; reflexivity) i
                                ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)));
    replace (Z_to_bv 64 0x39eb0) with (0x39eb0 : word) by (apply bv_eq; reflexivity);
    eapply reach_weaken;
    [| exact (rgl_loop s rng v m ltac:(lia) SOKr SOKs RO1 RO2 HFB 256%nat fr regs fr cs regs m 0%Z ltac:(reflexivity) ltac:(lia) FZ ltac:(apply rinv_refl)
                H2 H8 H9 H18 H19 H23 ltac:(rewrite H25; f_equal; lia) ltac:(rewrite H26; f_equal; lia) F8 (regs_agree_refl _ _) (fun r _ => eq_refl))]
  end.
  intros fin (fr' & cs' & regs' & M' & -> & FZ' & RI' & _ & E2f & E8f & E9f & E18f & E19f & E23f & E25f & E26f & AGf & FSf & VALf).
  exists fr', cs', regs', M'. split; [f_equal; apply bv_eq; reflexivity|].
  split; [exact FZ'|]. split; [exact RI'|].
  split; [intros jj Hjj; apply VALf; lia|].
  do 8 (split; [assumption|]).
  split; [|exact FSf].
  intros r Hr. destruct (decide (r = 2%bv)) as [->|N2]; [rewrite E2f, H2; reflexivity|].
  apply AGf. unfold rgl_CL. cbn [In]. intros X. apply Hr. cbn [In].
  destruct X as [X|[X|X]]; [left; exact X | exfalso; apply N2; symmetry; exact X | right; exact X].
Qed.

End BilSegsSR.
