(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutShA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FIK.
Definition mem := (word -> option byte).

Fixpoint cell_val (cells : list kentry) (b : expr) (off : Z) (w : nat) : expr :=
  match cells with
  | [] => ELit 0
  | KWord (SA b' o') w' v :: r => if (expr_eqb b' b && Z.eqb o' off && Nat.eqb w' w)%bool then v else cell_val r b off w
  | _ :: r => cell_val r b off w
  end.
Fixpoint reg_val (regs : list (nat * expr)) (r : nat) : expr :=
  match regs with [] => ELit 0 | (r', e) :: rest => if Nat.eqb r' r then e else reg_val rest r end.

Lemma u8_byte_above : forall segs (M : mem) top a v, segs_below_b segs top = true -> 0 <= top <= a -> a < 2 ^ 64 -> L5.u8_at segs M a v -> byte_at M a v.
Proof.
  intros segs M top a v Hb Ha Ha2 Hu. unfold L5.u8_at in Hu. cbn [rdn] in Hu. unfold byte_at.
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:Em.
  - injection Hu as Hb'. rewrite Hb'. reflexivity.
  - exfalso. unfold seg_rom, memory_read in Hu. change (Z.of_N 1) with 1 in Hu.
    rewrite (find_segment1_none_above segs top (bv_unsigned (Z_to_bv 64 a)) Hb ltac:(rewrite u64_of_Z by lia; lia)) in Hu. discriminate.
Qed.

Lemma resp_ok : forall segs top (M : mem) E E' Fe k F,
  segs_below_b segs top = true -> 0 <= top <= SB ->
  CL5A.uv E Fe = F -> CL5A.uv E' Fe = F -> F mod 8 = 0 -> 0 <= F -> F + k < 2 ^ 47 -> 0 <= k ->
  kentry_ok segs E' M (KWord (SA (CHA.SRL3 Fe) (SB + k / 8)) 1 (ELit 0)) ->
  kentry_ok segs E M (KZero (SA (CHA.SRL3 (EAlu Instr.ALU_ADD Fe (ELit k))) SB) (ELit 1)).
Proof.
  intros segs top M E E' Fe k F Hb Htop HF HF' F8 F0 Fk K0 HK.
  assert (GK : (F + k) / 8 = F / 8 + k / 8).
  { apply Z.mod_divide in F8; [|lia]. destruct F8 as [q Hq]. rewrite Hq. rewrite Z.div_mul by lia. replace (q * 8 + k) with (k + q * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (D0 : 0 <= F / 8) by (apply Z.div_pos; lia).
  assert (D1 : (F + k) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  pose proof (CL5A.kword8_elim segs E' M _ _ (F / 8 + (SB + k / 8)) HK ltac:(rewrite CL5A.estart_srl3, HF'; reflexivity)) as U.
  replace (CL5A.uv E' (ELit 0)) with 0 in U by (unfold CL5A.uv; cbn [edenot]; rewrite u64_of_Z by lia; reflexivity).
  assert (BZ : byte_at M (F / 8 + (SB + k / 8)) 0) by (apply (u8_byte_above segs M top); [exact Hb | unfold SB in *; lia | unfold SB in *; lia | exact U]).
  assert (UE : CL5A.uv E (EAlu Instr.ALU_ADD Fe (ELit k)) = F + k).
  { unfold CL5A.uv. cbn [edenot]. rewrite AX2S.u_add64. change (bv_unsigned (edenot E Fe)) with (CL5A.uv E Fe). rewrite HF, (u64_of_Z k) by lia. apply Z.mod_small. lia. }
  eapply CL5A.kzero_intro with (A := F / 8 + (SB + k / 8)) (N := 1); [rewrite CL5A.estart_srl3, UE, GK; lia | unfold elenZ; cbn [edenot]; apply u64_of_Z; lia | unfold SB; lia | unfold SB; lia | unfold SB; lia |].
  intros j Hj. replace (F / 8 + (SB + k / 8) + j) with (F / 8 + (SB + k / 8)) by lia. exact BZ.
Qed.

Lemma magic10 : forall xs, -2^63 <= xs <= -10 -> (xs * 7378697629483820647) / 2^64 / 4 + 1 = - ((- xs) / 10).
Proof.
  intros xs Hx. rewrite Z.div_div by lia.
  assert (Hd : - xs = 10 * ((- xs) / 10) + (- xs) mod 10) by (apply Z.div_mod; lia).
  pose proof (Z.mod_pos_bound (- xs) 10 ltac:(lia)) as Hr.
  set (k := (- xs) / 10) in *. set (r := (- xs) mod 10) in *.
  assert (Hk : 1 <= k) by lia.
  assert (Q : xs * 7378697629483820647 / (2 ^ 64 * 4) = - k - 1).
  { symmetry. apply (Z.div_unique _ _ _ (xs * 7378697629483820647 + 2 ^ 66 * (k + 1))); [left; lia | lia]. }
  rewrite Q. lia.
Qed.

Lemma swrap64_neg : forall z, -2^63 <= z < 0 -> bv_swrap 64 z = z.
Proof. intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 64 / 2) with (2 ^ 63). rewrite Z.mod_small by lia. lia. Qed.

Lemma q_den : forall (w : bv 64), 2^63 <= bv_unsigned w <= 2^64 - 10 ->
  bv_unsigned (alu64 ALU_ADD (alu64 ALU_SRL (mul_div M_MULH w (Z_to_bv 64 7378697629483820647)) (Z_to_bv 64 63))
                             (alu64 ALU_SRA (mul_div M_MULH w (Z_to_bv 64 7378697629483820647)) (Z_to_bv 64 2)))
  = 2^64 - (2^64 - bv_unsigned w) / 10.
Proof.
  intros w Hw. set (x := bv_unsigned w) in *.
  assert (Sw : bv_signed w = x - 2^64).
  { unfold bv_signed. fold x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 64 / 2) with (2 ^ 63).
    rewrite (Z.mod_eq (x + 2 ^ 63) (2 ^ 64)) by lia. replace ((x + 2 ^ 63) / 2 ^ 64) with 1; [lia|]. apply (Z.div_unique_pos _ _ _ (x + 2 ^ 63 - 2 ^ 64)); lia. }
  assert (SM : bv_signed (Z_to_bv 64 7378697629483820647) = 7378697629483820647) by (rewrite Z_to_bv_signed; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; cbn -[Z.pow]; reflexivity).
  set (xs := x - 2 ^ 64) in *.
  pose proof (magic10 xs ltac:(unfold xs; lia)) as MG.
  set (hz := xs * 7378697629483820647 / 2 ^ 64) in *.
  assert (Hh : -2^62 <= hz <= -1).
  { unfold hz. split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
  unfold alu64, alu, mul_div. unfold bv_mulhss. rewrite Sw, SM. rewrite Z.shiftr_div_pow2 by lia. change (Z.of_N 64) with 64. fold hz.
  assert (AM2 : bv_and (Z_to_bv 64 2) (Z_to_bv 64 63) = Z_to_bv 64 2) by (apply bv_eq; reflexivity).
  assert (AM63 : bv_and (Z_to_bv 64 63) (Z_to_bv 64 63) = Z_to_bv 64 63) by (apply bv_eq; reflexivity).
  rewrite AM2, AM63.
  rewrite bv_add_unsigned, bv_ashiftr_unsigned, bv_shiftr_unsigned. rewrite Z.add_comm.
  rewrite Z_to_bv_signed, swrap64_neg by lia. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 64 2) with 2. change (bv_wrap 64 63) with 63.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  assert (Uh : bv_wrap 64 hz = hz + 2 ^ 64).
  { unfold bv_wrap, bv_modulus. cbn -[Z.pow]. rewrite (Z.mod_eq hz (2 ^ 64)) by lia. replace (hz / 2 ^ 64) with (-1); [lia|]. apply (Z.div_unique_pos _ _ _ (hz + 2 ^ 64)); lia. }
  rewrite Uh.
  replace ((hz + 2 ^ 64) / 2 ^ 63) with 1 by (apply (Z.div_unique_pos _ _ _ (hz + 2 ^ 64 - 2 ^ 63)); lia).
  assert (H4 : -2^60 <= hz / 4 <= -1) by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  unfold bv_wrap, bv_modulus. cbn -[Z.pow].
  assert (E1 : (hz / 4) mod 2 ^ 64 = hz / 4 + 2 ^ 64).
  { rewrite (Z.mod_eq (hz / 4) (2 ^ 64)) by lia. replace (hz / 4 / 2 ^ 64) with (-1); [lia|]. apply (Z.div_unique_pos _ _ _ (hz / 4 + 2 ^ 64)); lia. }
  rewrite E1. change (1 mod 2 ^ 64) with 1.
  rewrite Z.mod_small by lia.
  replace (hz / 4 + 2 ^ 64 + 1) with (hz / 4 + 1 + 2 ^ 64) by lia. rewrite MG. unfold xs. replace (- (x - 2 ^ 64)) with (2 ^ 64 - x) by lia. lia.
Qed.
Lemma q_den1 : forall (w : bv 64), 2^63 <= bv_unsigned w <= 2^64 - 10 ->
  bv_unsigned (alu64 ALU_ADD (alu64 ALU_SRA (mul_div M_MULH w (Z_to_bv 64 7378697629483820647)) (Z_to_bv 64 2)) (Z_to_bv 64 1))
  = 2^64 - (2^64 - bv_unsigned w) / 10.
Proof.
  intros w Hw. set (x := bv_unsigned w) in *.
  assert (Sw : bv_signed w = x - 2^64).
  { unfold bv_signed. fold x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 64 / 2) with (2 ^ 63).
    rewrite (Z.mod_eq (x + 2 ^ 63) (2 ^ 64)) by lia. replace ((x + 2 ^ 63) / 2 ^ 64) with 1; [lia|]. apply (Z.div_unique_pos _ _ _ (x + 2 ^ 63 - 2 ^ 64)); lia. }
  assert (SM : bv_signed (Z_to_bv 64 7378697629483820647) = 7378697629483820647) by (rewrite Z_to_bv_signed; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; cbn -[Z.pow]; reflexivity).
  set (xs := x - 2 ^ 64) in *.
  pose proof (magic10 xs ltac:(unfold xs; lia)) as MG.
  set (hz := xs * 7378697629483820647 / 2 ^ 64) in *.
  assert (Hh : -2^62 <= hz <= -1).
  { unfold hz. split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
  unfold alu64, alu, mul_div. unfold bv_mulhss. rewrite Sw, SM. rewrite Z.shiftr_div_pow2 by lia. change (Z.of_N 64) with 64. fold hz.
  assert (AM2 : bv_and (Z_to_bv 64 2) (Z_to_bv 64 63) = Z_to_bv 64 2) by (apply bv_eq; reflexivity).
  rewrite AM2.
  rewrite bv_add_unsigned, bv_ashiftr_unsigned.
  rewrite Z_to_bv_signed, swrap64_neg by lia. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 64 2) with 2. change (bv_wrap 64 1) with 1.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  assert (Uh : bv_wrap 64 hz = hz + 2 ^ 64).
  { unfold bv_wrap, bv_modulus. cbn -[Z.pow]. rewrite (Z.mod_eq hz (2 ^ 64)) by lia. replace (hz / 2 ^ 64) with (-1); [lia|]. apply (Z.div_unique_pos _ _ _ (hz + 2 ^ 64)); lia. }
  assert (H4 : -2^60 <= hz / 4 <= -1) by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  unfold bv_wrap, bv_modulus. cbn -[Z.pow].
  assert (E1 : (hz / 4) mod 2 ^ 64 = hz / 4 + 2 ^ 64).
  { rewrite (Z.mod_eq (hz / 4) (2 ^ 64)) by lia. replace (hz / 4 / 2 ^ 64) with (-1); [lia|]. apply (Z.div_unique_pos _ _ _ (hz / 4 + 2 ^ 64)); lia. }
  rewrite E1. change (1 mod 2 ^ 64) with 1.
  rewrite Z.mod_small by lia.
  replace (hz / 4 + 2 ^ 64 + 1) with (hz / 4 + 1 + 2 ^ 64) by lia. rewrite MG. unfold xs. replace (- (x - 2 ^ 64)) with (2 ^ 64 - x) by lia. lia.
Qed.

Lemma kunk_sub : forall segs E E' (M : mem) b o n o' n', CL5A.uv E b = CL5A.uv E' b -> o <= o' -> o' + n' <= o + n -> 0 < n' < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  kentry_ok segs E' M (KUnk (SA b o) (ELit n)) -> kentry_ok segs E M (KUnk (SA b o') (ELit n')).
Proof.
  intros segs E E' M b o n o' n' Hb H1 H2 Hn' Hn HK. cbn [kentry_ok] in HK |- *. unfold flat, estart, elenZ in HK |- *. cbn [a_base a_off edenot] in HK |- *.
  rewrite !u64_of_Z in HK |- * by lia.
  change (bv_unsigned (edenot E b)) with (CL5A.uv E b). change (bv_unsigned (edenot E' b)) with (CL5A.uv E' b) in HK. rewrite Hb.
  destruct HK as ((F0 & F1 & F2 & F3) & HD).
  split; [lia|]. intros q Hq. replace (CL5A.uv E' b + o' + q) with (CL5A.uv E' b + o + (o' - o + q)) by lia. apply HD. lia.
Qed.

Definition reentry_chk_u (NF : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (s : CC.subst) (U : list kentry) : bool :=
  (Nat.leb NF (CC.cp_nx c)
   && forallb (fun r => CSL.reg_is (SR.ps_regs ps) r (CC.esubstL NF s (nth r (CC.cp_regs cj) (ELit 0)))) (seq 1 31)
   && forallb (fun X => let X' := CC.ksubstL NF s X in (CC.has_cell U X || CC.has_cell (SR.ps_cells ps) X' || CX.fact2_ok (SR.ps_cells ps) X')%bool) (CC.cp_know cj)
   && APC.expr_vars_lt (CC.cp_nx c) (CC.cp_meas c))%bool.

Section Leaf.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
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
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Variable XI : nat -> env -> list (Z * Z) -> mem -> Model -> Prop.

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).
Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 XI).

Theorem reentry_leaf_u : forall i c ps j cj s U,
  nth_error CPS j = Some cj ->
  SR.ps_pc ps = CC.cp_pc cj ->
  reentry_chk_u NF c ps cj s U = true ->
  CHA.goto_amb_chk NF d c (nth i BLS []) (nth j BLS []) (nth i FFS []) (nth j FFS []) s = true ->
  (forall E E' R R' A M model M1 model1,
     CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> XI i E A M model -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
     XI j (CC.env_over NF s E') A M1 model1 /\ CC.meas cj (CC.env_over NF s E') < CC.meas c E /\
     (forall X, In X U -> kentry_ok (hl_segs L) (CC.env_over NF s E') (CCA.vis A model1 M1) X)) ->
  (forall E E' R' M M' cr, env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr -> Cred j (CC.env_over NF s E') cr) ->
  CCA.leaf_ok (hl_segs L) CPS AMBX K FPI i c ps.
Proof.
  intros i c ps j cj s U Hcj Hpc Hchk Hgchk USER CRED fx' E R A M model E' R' M1 model1 HAt [HA HXI] HFP Hag HLF HIH.
  unfold reentry_chk_u in Hchk.
  apply andb_prop in Hchk as [Hchk Xmv]. apply andb_prop in Hchk as [Hchk Xkn]. apply andb_prop in Hchk as [Xnf Xregs]. apply Nat.leb_le in Xnf.
  pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
  destruct (USER E E' R R' A M model M1 model1 HAt HA HXI Hag HLF) as (HXIj & HMEAS & HUS).
  assert (X0R : getr R' 0%bv = Z_to_bv 64 0) by (exact (CC.lf_x0 _ _ _ _ _ _ _ HLFv)).
  set (E2 := CC.env_over NF s E') in *.
  rewrite Hpc.
  apply (HIH j cj fx' E2 R' A M1 model1 Hcj).
  - split.
    + intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
      * assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er). cbn [edenot]. exact X0R.
      * assert (Hr : (1 <= ridx r < 32)%nat).
        { unfold ridx. pose proof (bv_unsigned_in_range _ r) as B. change (bv_modulus 5) with 32 in B.
          unfold bv_eqb in Er. apply Z.eqb_neq in Er. change (bv_unsigned (0%bv : bv 5)) with 0 in Er. lia. }
        rewrite forallb_forall in Xregs. specialize (Xregs (ridx r) ltac:(apply in_seq; lia)).
        apply CSL.reg_is_sound in Xregs. destruct (CC.lf_regs _ _ _ _ _ _ _ HLFv _ _ Xregs) as [_ Hg]. rewrite CC.reg_of_ridx in Hg.
        rewrite Hg. unfold E2. apply CC.esubstL_denot.
    + unfold know_ok. apply Forall_forall. intros X' HX'. rewrite forallb_forall in Xkn. specialize (Xkn X' HX'). cbv zeta in Xkn.
      apply orb_prop in Xkn. destruct Xkn as [Xkn|Xkn]; [apply orb_prop in Xkn; destruct Xkn as [Xu|Xkn]|].
      * exact (HUS X' (CC.has_cell_In _ _ Xu)).
      * apply (CC.kentry_ok_ksubstL (hl_segs L) NF s E' _ X'). apply CC.has_cell_In in Xkn. exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ Xkn).
      * apply (CC.kentry_ok_ksubstL (hl_segs L) NF s E' _ X').
        exact (CX.fact2_ok_sound (hl_segs L) E' _ (SR.ps_cells ps) _ ltac:(unfold know_ok; apply Forall_forall; intros Y HY; exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HY)) Xkn).
  - split.
    + exact (CHA.goto_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
               i c ps j s Hgchk CRED E R A M model E' R' M1 model1 HAt HA Hag HLF).
    + exact HXIj.
  - exact HFP.
  - exact HMEAS.
Qed.
End Leaf.
End FIK.
