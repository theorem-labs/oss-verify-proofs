(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA CutRtA CutRtB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PRK.
Definition mem := (word -> option byte).

Definition is_j_at (segs : list Segment) (pcj pc : Z) : Prop :=
  exists w rd (imm : bv 21), fetch_word segs (Z_to_bv 64 pcj) = Some w /\ is_ecall w = false /\ decode_any w = Some (Jal rd imm, 4)
    /\ bv_unsigned rd = 0 /\ bv_unsigned (btgt (Z_to_bv 64 pcj) (bv_signed imm)) = pc.
Ltac solve_is_j := unfold is_j_at; do 3 eexists; (split; [vm_compute; reflexivity|]); repeat split; vm_compute; reflexivity.

Definition ps_at (ps : SR.post_spec) (pc : Z) : SR.post_spec := SR.PS pc (SR.ps_regs ps) (SR.ps_regions ps) (SR.ps_cells ps).

Section Tail.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBrest : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable Cred : nat -> env -> credit -> Prop.
Variable D0 : Z.
Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis FFRS0 : CHA.ffrs FFrest sp0.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - SCR) SCR.
Hypothesis DEFUP : L5.defined M0 sp0 (ar_stack_top ar - sp0).
Hypothesis KNIL : K [].
Variable R0 : bvmap 5 word.
Variable ra0 : Z.
Hypothesis EV0 : forall x : reg, ev E0 (ridx x) = getr R0 x.
Hypothesis RA0 : getr R0 1%bv = Z_to_bv 64 ra0.
Hypothesis RA0ok : L5.ra_ok ra0.

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).
Abbreviation curB := (CHA.curB LBrest BLS).

Lemma tailj_leaf : forall pcj pc scr dc i c ps,
  is_j_at (hl_segs L) pcj pc -> SR.ps_pc ps = pcj -> 0 <= pcj < 2 ^ 64 ->
  CRB.tail_base_chk NF pc c (ps_at ps pc) = true -> CHA.foot_chk NF d c (nth i BLS []) (nth i FFS []) = true -> nth i FFS [] = [] -> 0 <= scr <= SCR -> dc <= D0 ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
    (forall cr LK,
        regs_preserved R0 R' -> CHA.ahpres L ar LBrest FFrest sp0 SCR W M0 M1 -> ri_inv HI (curB i E) FFrest LK cr A M1 (vml_of model1) -> incl LK LK0 -> Cred i E cr ->
        env_agree NF E0 E' -> AAMB i E A M1 model1 ->
        exists (Pre : bvmap 5 word -> mem -> Prop)
               (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> list (Z * Z) -> credit -> list (Z * Z) -> list L5.range -> Prop),
          CBA.cps_asanG L ar HI FPI pc ra0 sp0 scr (curB i E) FFrest LK cr A dc Pre Post /\ Pre R' M1 /\
          forall (fx2 : FPState) R2 M2 model2 LB' cr' LBk Wc LK2 A2, FPI fx2 -> Post R' M1 R2 M2 LB' cr' LBk Wc -> regs_preserved R0 R2 ->
            CHA.ahpres L ar LBk FFrest sp0 scr Wc M1 M2 -> model_rt model0 model2 -> incl A0 A2 -> CHA.amodel_ok A2 model2 -> incl LK2 LK0 ->
            ri_inv HI LB' FFrest LK2 cr' A2 M2 (vml_of model2) ->
            srealizes (hl_segs L) SCFG (mkCfg (@mkst fx2 R2 (Z_to_bv 64 ra0) M2 (seg_rom (hl_segs L))) model2) K) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros pcj pc scr dc i c ps (w & rd & imm & Hf & He & Hd & Hrd & Ht0) Hpc Hpcr Hchk Hfoot HFi Hscr Hdc fx' E R A M model E' R' M1 model1 HAt HA HFP Hag HLF USER.
  assert (Hrd0 : rd = 0%bv) by (apply bv_eq; rewrite Hrd; reflexivity). subst rd.
  assert (Ht : btgt (Z_to_bv 64 pcj) (bv_signed imm) = Z_to_bv 64 pc) by (rewrite <- Ht0; symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (CHA.leaf_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
                i c ps E E' R R' A M model M1 model1 Hfoot HAt HA Hag HLF) as HA1.
  destruct (CHA.aamb_model L ar C HI HIok LY_below NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i E A M1 model1 HA1) as (Hh1 & HMI1 & HAwf & Hoff1).
  set (H1 := ahid A model1).
  assert (MS : msteps (hl_segs L) (@mkst fx' R' (Z_to_bv 64 pcj) (mrestrict H1 M1) (seg_rom (hl_segs L)))
                                  (@mkst fx' R' (Z_to_bv 64 pc) (mrestrict H1 M1) (seg_rom (hl_segs L)))).
  { eapply mst_step; [reflexivity | | apply mst_refl].
    rewrite (step_jal_x0 (hl_segs L) R' (Z_to_bv 64 pcj) (mrestrict H1 M1) (seg_rom (hl_segs L)) w imm Hf He Hd). rewrite Ht. reflexivity. }
  rewrite Hpc.
  eapply (L5LZ.cps_of_msteps_lazy (hl_segs L) H1 A fx' fx' R' _ M1 R' _ (mrestrict H1 M1) model1 K Hoff1 LY_nowrap (L5LZ.lazy_cover_ahid A model1) HAwf HMI1 Hh1 MS).
  intros model2 HMI2 HS12 _.
  replace (munrestrict H1 M1 (mrestrict H1 M1)) with M1
    by (apply FunctionalExtensionality.functional_extensionality; intros x; unfold munrestrict, mrestrict; destruct (H1 x); reflexivity).
  assert (HLF2 : CCA.leaf_factsA (hl_segs L) c (ps_at ps pc) E' R' A M model M1 model2).
  { pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv. constructor.
    - rewrite (CCA.vis_sbm A model1 model2 M1 HS12). destruct HLFv as [X1 X2 X3 X4 X5 X6]. constructor; cbn [ps_at SR.ps_regs SR.ps_cells]; assumption.
    - exact (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF).
    - exact (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF).
    - exact (CCA.lfa_hid _ _ _ _ _ _ _ _ _ _ HLF).
    - exact (same_but_materialized_trans _ _ _ (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF) HS12).
    - exact HMI2. }
  change (Z_to_bv 64 pc) with (Z_to_bv 64 (SR.ps_pc (ps_at ps pc))).
  refine (CRB.tail_leaf L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0 WRS_ok
            K FPI DEF0 DEFUP KNIL R0 ra0 EV0 RA0 RA0ok pc scr dc i c (ps_at ps pc) Hchk Hfoot HFi Hscr Hdc fx' E R A M model E' R' M1 model2 HAt HA HFP Hag HLF2 _).
  intros cr LK HRP HP HH HLK HC HagE' HA2.
  assert (VML : vml_of model2 = vml_of model1) by (unfold vml_of; rewrite (L5LZ.sbm_vmmaps _ _ HS12), (L5LZ.sbm_lazy _ _ HS12); reflexivity).
  rewrite VML in HH. exact (USER cr LK HRP HP HH HLK HC HagE' HA1).
Qed.
End Tail.

Definition isnil {A} (l : list A) : bool := match l with [] => true | _ => false end.
Definition lin_zero (e : expr) : bool := let l := lin_of e in (Z.eqb (fst l mod 2 ^ 64) 0 && isnil (snd l))%bool.
Definition halve_lin (l : lin) : option lin :=
  if (Z.even (fst l) && forallb (fun t : Z * expr => Z.even (fst t)) (snd l))%bool
  then Some (fst l / 2, map (fun t : Z * expr => (fst t / 2, snd t)) (snd l)) else None.
Definition cell_val (ov : nat) (cells : list kentry) (k : Z) (w : nat) : option expr :=
  match List.find (fun X => match X with KWord (SA b k') w' _ => (expr_eqb b (EVar ov) && Z.eqb k k' && Nat.eqb w w')%bool | _ => false end) cells with
  | Some (KWord _ _ v) => Some v | _ => None end.
Definition nul_expr (ov : nat) (nb : expr) (nk : Z) (H : expr) : expr :=
  EAlu ALU_SUB (EAlu ALU_SUB (EAlu ALU_ADD nb (ELit nk)) (EVar ov)) (EAlu ALU_ADD H (ELit 1)).
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

Definition short_ok (ov : nat) (cells : list kentry) : bool :=
  match cell_val ov cells 0 1 with
  | Some B => match halve_lin (lin_of B) with
              | Some h => let H := unlin h in
                  (lin_zero (EAlu ALU_SUB B (EMd M_MUL (ELit 2) H)) && AP.fact_ok cells (KRange H 0 22) && lo_ok cells H
                   && existsb (fun K => match K with KWord (SA nb nk) 1 (ELit 0) => pin_ok cells (nul_expr ov nb nk H) | _ => false end) cells)%bool
              | None => false end
  | None => false end.

Definition short_nonul_ok (ov : nat) (cells : list kentry) : bool :=
  match cell_val ov cells 0 1 with
  | Some B => match halve_lin (lin_of B) with
              | Some h => let H := unlin h in (lin_zero (EAlu ALU_SUB B (EMd M_MUL (ELit 2) H)) && AP.fact_ok cells (KRange H 0 22))%bool
              | None => false end
  | None => false end.

Definition long_ok (ov : nat) (nul : bool) (lo hi : Z) (P : expr) (cells : list kentry) : bool :=
  match cell_val ov cells 0 8, cell_val ov cells 8 8, cell_val ov cells 16 8 with
  | Some w0, Some Sz, Some P' =>
      (expr_eqb w0 (ELit 49) && expr_eqb P P' && AP.fact_ok cells (KRange Sz lo hi)
       && (negb nul || existsb (fun K => match K with KWord (SA nb nk) 1 (ELit 0) => lin_zero (EAlu ALU_SUB (EAlu ALU_ADD nb (ELit nk)) (EAlu ALU_ADD P Sz)) | _ => false end) cells))%bool
  | _, _, _ => false end.

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
Lemma cell_val_in : forall ov cells k w v, cell_val ov cells k w = Some v -> In (KWord (SA (EVar ov) k) w v) cells.
Proof.
  intros ov cells k w v H. unfold cell_val in H.
  destruct (List.find _ cells) as [X|] eqn:HF; [|discriminate].
  apply find_some in HF as [Hin Hb]. destruct X as [[b k'] w' v'| | | | | | | | |]; try discriminate.
  injection H as <-. repeat (apply andb_prop in Hb as [Hb ?Y]). apply expr_eqb_eq in Hb. apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y. subst. exact Hin.
Qed.
Lemma know_in : forall segs E M cells K, know_ok segs E M cells -> In K cells -> kentry_ok segs E M K.
Proof. intros segs E M cells K HK Hin. exact (proj1 (Forall_forall _ _) HK K Hin). Qed.

Section Shapes.
Variable segs : list Segment.
Lemma lo_ok_sound : forall E (M : mem) cells H, know_ok segs E M cells -> lo_ok cells H = true -> bv_unsigned (edenot E H) <= 22 ->
  1 <= bv_unsigned (edenot E H).
Proof.
  intros E M cells H HK HL Hh. unfold lo_ok in HL. apply orb_prop in HL as [HL|HL].
  - pose proof (APS.fact_ok_sound segs E M cells _ HK HL) as [R1 R2]. exact R1.
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

Lemma byte0_sound : forall ov E (M : mem) cells o B hl, cell_val ov cells 0 1 = Some B -> halve_lin (lin_of B) = Some hl ->
  lin_zero (EAlu ALU_SUB B (EMd M_MUL (ELit 2) (unlin hl))) = true -> know_ok segs E M cells -> bv_unsigned (ev E ov) = o -> 0 <= o -> o + 24 <= 2 ^ 64 ->
  bv_unsigned (edenot E (unlin hl)) <= 22 ->
  L5.u8_at segs M o (2 * bv_unsigned (edenot E (unlin hl))).
Proof.
  intros ov E M cells o B hl HB Hh HZ HK Ho H0 H24 Hle. set (H1 := unlin hl) in *. set (h := bv_unsigned (edenot E H1)) in *.
  pose proof (lin_zero_sound E _ HZ) as Z0.
  pose proof (eqm_sub_e E B (EMd M_MUL (ELit 2) H1)) as [q1 Q1]. pose proof (eqm_mul_e E (ELit 2) H1) as [q2 Q2]. pose proof (eqm_lit_e E 2) as [q3 Q3].
  rewrite Z0 in Q1. fold h in Q2. pose proof (uE_range E B) as RB. pose proof (uE_range E (EMd M_MUL (ELit 2) H1)) as RM.
  assert (E2 : bv_unsigned (edenot E (ELit 2)) = 2) by (cbn [edenot]; apply u64_of_Z; lia). rewrite E2 in Q2.
  assert (EB : bv_unsigned (edenot E B) = 2 * h) by (pose proof (uE_range E H1); nia).
  pose proof (CL5A.kword8_elim segs E M (SA (EVar ov) 0) B o (know_in _ _ _ _ _ HK (cell_val_in _ _ _ _ _ HB)) ltac:(unfold estart; cbn [a_base a_off edenot]; lia)) as G.
  unfold CL5A.uv in G. rewrite EB in G. exact G.
Qed.

Lemma short_nonul_sound : forall ov E (M : mem) cells o, short_nonul_ok ov cells = true -> know_ok segs E M cells -> bv_unsigned (ev E ov) = o -> 0 <= o -> o + 24 <= 2 ^ 64 ->
  exists h, 0 <= h <= 22 /\ L5.u8_at segs M o (2 * h).
Proof.
  intros ov E M cells o H HK Ho H0 H24. unfold short_nonul_ok in H.
  destruct (cell_val ov cells 0 1) as [B|] eqn:HB; [|discriminate]. destruct (halve_lin (lin_of B)) as [hl|] eqn:Hh; [|discriminate].
  apply andb_prop in H as [HZ HR].
  pose proof (APS.fact_ok_sound segs E M cells _ HK HR) as [R0 R2].
  exists (bv_unsigned (edenot E (unlin hl))). split; [lia|]. exact (byte0_sound ov E M cells o B hl HB Hh HZ HK Ho H0 H24 R2).
Qed.

Lemma short_ok_sound : forall ov E (M : mem) cells o, short_ok ov cells = true -> know_ok segs E M cells -> bv_unsigned (ev E ov) = o -> 0 <= o -> o + 24 <= 2 ^ 64 ->
  exists h, 1 <= h <= 22 /\ L5.u8_at segs M o (2 * h) /\ L5.u8_at segs M (o + 1 + h) 0.
Proof.
  intros ov E M cells o H HK Ho H0 H24. unfold short_ok in H.
  destruct (cell_val ov cells 0 1) as [B|] eqn:HB; [|discriminate]. destruct (halve_lin (lin_of B)) as [hl|] eqn:Hh; [|discriminate].
  set (H1 := unlin hl) in *. apply andb_prop in H as [H HN]. apply andb_prop in H as [H HLO]. apply andb_prop in H as [HZ HR].
  pose proof (APS.fact_ok_sound segs E M cells _ HK HR) as [R0 R2]. pose proof (lo_ok_sound E M cells H1 HK HLO R2) as R1. set (h := bv_unsigned (edenot E H1)) in *.
  exists h. split; [lia|]. split; [exact (byte0_sound ov E M cells o B hl HB Hh HZ HK Ho H0 H24 R2)|].
  apply existsb_exists in HN as (K & HKin & HKb). destruct K as [[nb nk] w v| | | | | | | | |]; try discriminate.
  destruct w as [|[|w]]; try discriminate. destruct v as [z| | | | | | |]; try discriminate. destruct z; try discriminate.
  pose proof (know_in _ _ _ _ _ HK HKin) as HC. pose proof HC as (_ & (F1 & F2 & _ & F4) & _).
  assert (X0 : bv_unsigned (edenot E (nul_expr ov nb nk H1)) = 0).
  { unfold pin_ok in HKb. apply orb_prop in HKb as [HKb|HKb]; [exact (lin_zero_sound E _ HKb)|].
    apply existsb_exists in HKb as (Kp & HKp & HPb). destruct Kp as [| | | | |P lo hi| | | |]; try discriminate.
    apply andb_prop in HPb as [Hlh HPb]. apply Z.eqb_eq in Hlh. subst hi.
    pose proof (know_in _ _ _ _ _ HK HKp) as (P1 & P2). assert (EP : bv_unsigned (edenot E P) = lo) by lia.
    pose proof (uE_range E (nul_expr ov nb nk H1)) as RX.
    pose proof (eqm_sub_e E P (ELit lo)) as [q5 Q5]. pose proof (eqm_lit_e E lo) as [q6 Q6]. rewrite EP in Q5.
    pose proof (uE_range E (EAlu ALU_SUB P (ELit lo))) as RP.
    apply orb_prop in HPb as [HPb|HPb].
    - pose proof (lin_zero_sound E _ HPb) as Z1. pose proof (eqm_sub_e E (nul_expr ov nb nk H1) (EAlu ALU_SUB P (ELit lo))) as [q4 Q4]. rewrite Z1 in Q4.
      assert (EP0 : bv_unsigned (edenot E (EAlu ALU_SUB P (ELit lo))) = 0) by (pose proof (uE_range E (ELit lo)); nia).
      rewrite EP0 in Q4. nia.
    - pose proof (lin_zero_sound E _ HPb) as Z1. pose proof (eqm_add_e E (nul_expr ov nb nk H1) (EAlu ALU_SUB P (ELit lo))) as [q4 Q4]. rewrite Z1 in Q4.
      assert (EP0 : bv_unsigned (edenot E (EAlu ALU_SUB P (ELit lo))) = 0) by (pose proof (uE_range E (ELit lo)); nia).
      rewrite EP0 in Q4. nia. }
  unfold nul_expr in X0.
  pose proof (eqm_sub_e E (EAlu ALU_SUB (EAlu ALU_ADD nb (ELit nk)) (EVar ov)) (EAlu ALU_ADD H1 (ELit 1))) as [a1 A1].
  pose proof (eqm_sub_e E (EAlu ALU_ADD nb (ELit nk)) (EVar ov)) as [a2 A2].
  pose proof (eqm_add_e E nb (ELit nk)) as [a3 A3]. pose proof (eqm_lit_e E nk) as [a4 A4].
  pose proof (eqm_add_e E H1 (ELit 1)) as [a5 A5]. pose proof (eqm_lit_e E 1) as [a6 A6].
  rewrite X0 in A1. change (edenot E (EVar ov)) with (ev E ov) in A2. rewrite Ho in A2. fold h in A5.
  assert (E1 : bv_unsigned (edenot E (ELit 1)) = 1) by (cbn [edenot]; apply u64_of_Z; lia). rewrite E1 in A5.
  pose proof (uE_range E (EAlu ALU_SUB (EAlu ALU_ADD nb (ELit nk)) (EVar ov))) as R3. pose proof (uE_range E (EAlu ALU_ADD nb (ELit nk))) as R4.
  pose proof (uE_range E (EAlu ALU_ADD H1 (ELit 1))) as R5. pose proof (uE_range E (ELit nk)) as R6.
  unfold estart in F1, F2, F4. cbn [a_base a_off] in F1, F2, F4.
  assert (EA : estart E (SA nb nk) = o + 1 + h).
  { unfold estart. cbn [a_base a_off]. change (2 ^ 64) with 18446744073709551616 in *. lia. }
  exact (CL5.kword8_zero_elim segs E M _ _ HC EA).
Qed.

Lemma long_ok_sound : forall ov nul lo hi E (M : mem) P cells o, long_ok ov nul lo hi P cells = true -> know_ok segs E M cells -> bv_unsigned (ev E ov) = o -> 0 <= o -> o + 24 <= 2 ^ 64 ->
  bv_unsigned (edenot E P) + 48 <= 2 ^ 64 -> 0 <= lo -> hi <= 47 ->
  exists S, lo <= S <= hi /\ L5.u64_at segs M o 49 /\ L5.u64_at segs M (o + 8) S /\ L5.u64_at segs M (o + 16) (bv_unsigned (edenot E P))
    /\ (nul = true -> L5.u8_at segs M (bv_unsigned (edenot E P) + S) 0).
Proof.
  intros ov nul lo hi E M P cells o H HK Ho H0 H24 HP Hlo Hhi. unfold long_ok in H.
  destruct (cell_val ov cells 0 8) as [w0|] eqn:C0; [|discriminate]. destruct (cell_val ov cells 8 8) as [S|] eqn:C8; [|discriminate].
  destruct (cell_val ov cells 16 8) as [P'|] eqn:C16; [|discriminate].
  apply andb_prop in H as [H HN]. apply andb_prop in H as [H HR]. apply andb_prop in H as [HW HPP].
  apply expr_eqb_eq in HW, HPP. subst w0 P'.
  pose proof (APS.fact_ok_sound segs E M cells _ HK HR) as [R1 R2].
  exists (bv_unsigned (edenot E S)). split; [lia|].
  assert (ST : forall k, estart E (SA (EVar ov) k) = o + k) by (intros k; unfold estart; cbn [a_base a_off edenot]; lia).
  split; [apply (CL5.kword64_elim segs E M _ _ o 49 (know_in _ _ _ _ _ HK (cell_val_in _ _ _ _ _ C0))); [rewrite ST; lia | cbn [edenot]; apply u64_of_Z; lia]|].
  split; [apply (CL5.kword64_elim segs E M _ _ (o + 8) _ (know_in _ _ _ _ _ HK (cell_val_in _ _ _ _ _ C8))); [rewrite ST; lia | reflexivity]|].
  split; [apply (CL5.kword64_elim segs E M _ _ (o + 16) _ (know_in _ _ _ _ _ HK (cell_val_in _ _ _ _ _ C16))); [rewrite ST; lia | reflexivity]|].
  intros Hnul. subst nul. cbn [negb orb] in HN.
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
  exact (CL5.kword8_zero_elim segs E M _ _ HC EA).
Qed.

Lemma bytes_of_defined : forall (M : mem) (n : nat) (p : Z), 0 <= p -> p + Z.of_nat n <= 2 ^ 64 -> L5.defined M p (Z.of_nat n) ->
  exists s : list Z, length s = n /\ L5.bytes_at segs M p s.
Proof.
  intros M n. induction n as [|n IH]; intros p Hp Hb Hd.
  - exists []. split; [reflexivity|]. intros i Hi. cbn [length] in Hi. lia.
  - destruct (IH (p + 1) ltac:(lia) ltac:(lia)) as (s & Hl & Hs).
    { intros i Hi. replace (p + 1 + i) with (p + (i + 1)) by lia. apply Hd. lia. }
    pose proof (Hd 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 p)) as [b|] eqn:Hb0; [|contradiction].
    exists (bv_unsigned b :: s). split; [cbn [length]; rewrite Hl; reflexivity|].
    intros i Hi. destruct i as [|i].
    + cbn [nth]. rewrite Z.add_0_r. unfold L5.u8_at. cbn [rdn]. unfold rd1. rewrite Hb0. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + cbn [nth]. replace (p + Z.of_nat (Datatypes.S i)) with (p + 1 + Z.of_nat i) by lia. apply Hs. cbn [length] in Hi. lia.
Qed.
End Shapes.

Definition cur_ok (bufE cur : expr) (cells : list kentry) : bool :=
  existsb (fun X => match X with KRange e lo hi => (Z.leb 0 lo && Z.leb hi 23 && expr_eqb cur (APC.eadd bufE e))%bool | _ => false end) cells.
Lemma cur_ok_sound : forall segs E (M : mem) bufE cur cells, cur_ok bufE cur cells = true -> know_ok segs E M cells -> CL5A.uv E bufE + 23 < 2 ^ 64 ->
  CL5A.uv E bufE <= CL5A.uv E cur <= CL5A.uv E bufE + 23.
Proof.
  intros segs E M bufE cur cells H HK Hb. unfold cur_ok in H. apply existsb_exists in H as (X & HX & Hb0).
  destruct X as [| | | | |e lo hi| | | |]; try discriminate. apply andb_prop in Hb0 as [Hb0 He]. apply andb_prop in Hb0 as [Hlo Hhi].
  apply Z.leb_le in Hlo, Hhi. apply expr_eqb_eq in He. subst cur.
  pose proof (know_in _ _ _ _ _ HK HX) as (R1 & R2). cbn [kentry_ok] in R1, R2.
  unfold CL5A.uv, APC.eadd. rewrite mkAlu_denot. change (alu64 ALU_ADD (edenot E bufE) (edenot E e)) with (edenot E (EAlu ALU_ADD bufE e)).
  cbn [edenot]. rewrite u_add64. unfold CL5A.uv in Hb. rewrite Z.mod_small by (pose proof (uE_range E bufE); lia). lia.
Qed.

Definition cur_okN (mx : Z) (bufE cur : expr) (cells : list kentry) : bool :=
  existsb (fun X => match X with KRange e lo hi => (Z.leb 0 lo && Z.leb hi mx && lin_zero (EAlu ALU_SUB cur (EAlu ALU_ADD bufE e)))%bool | _ => false end) cells.
Lemma cur_okN_sound : forall segs E (M : mem) mx bufE cur cells, cur_okN mx bufE cur cells = true -> know_ok segs E M cells -> CL5A.uv E bufE + mx < 2 ^ 64 ->
  CL5A.uv E bufE <= CL5A.uv E cur <= CL5A.uv E bufE + mx.
Proof.
  intros segs E M mx bufE cur cells H HK Hb. unfold cur_okN in H. apply existsb_exists in H as (X & HX & Hb0).
  destruct X as [| | | | |e lo hi| | | |]; try discriminate. apply andb_prop in Hb0 as [Hb0 He]. apply andb_prop in Hb0 as [Hlo Hhi].
  apply Z.leb_le in Hlo, Hhi.
  pose proof (know_in _ _ _ _ _ HK HX) as (R1 & R2). cbn [kentry_ok] in R1, R2.
  pose proof (lin_zero_sound E _ He) as Z0.
  pose proof (eqm_sub_e E cur (EAlu ALU_ADD bufE e)) as [q1 Q1]. pose proof (eqm_add_e E bufE e) as [q2 Q2]. rewrite Z0 in Q1.
  pose proof (uE_range E cur) as U1. pose proof (uE_range E bufE) as U2. pose proof (uE_range E (EAlu ALU_ADD bufE e)) as U3.
  unfold CL5A.uv in *. nia.
Qed.
End PRK.
