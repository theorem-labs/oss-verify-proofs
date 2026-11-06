(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_convert_casan_T Cut_convert_casan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_convert_casan.
Module GT := Cut_convert_casan_T.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.

Module CVA.
Definition PC_PUSHB : Z := 985020.
Definition RETPC : Z := 812972.
Definition SBz : Z := 2147450880.
Definition CPAE := EVar 10. Definition OE := EVar 12.

Definition bvar (i : nat) : nat := nth i [33; 33; 40; 40; 40; 40; 40; 40; 40; 40; 40; 40; 58; 58; 58; 58; 58; 58; 58; 58; 76; 76; 76; 76; 76; 76; 94; 94]%nat 0%nat.

Definition npush (i : nat) : Z := nth i [0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3; 4; 4] 0.
Definition FFS : list (list (expr * Z * Z)) := repeat [] 28.

Definition NKC : nat := 14.
Definition SHB (v : Z) : kentry := KWord (SA (EAlu Instr.ALU_SRL CPAE (ELit 3)) SBz) 1 (ELit v).
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1427896) 8 (ELit SBz)].
Definition STR_W : list SGP.region := [(OE, 0, ELit 24)].
Definition has := CC.has_cell.
Definition CPF0 : list SGP.region := [(EVar 2, -4496, ELit 4496)].

Definition a1ok (e : expr) : bool :=
  match e with
  | ELit c => (Z.leb 0 c && Z.ltb c 256)%bool
  | EAlu Instr.ALU_AND _ (ELit m) => (Z.leb 0 m && Z.ltb m 256)%bool
  | _ => false
  end.
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      ((Nat.ltb (bvar i + 1) (CC.cp_nx c) && CBA.regions_eqb (CC.cp_F c) CPF0 && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS []) && Nat.leb i 27) &&
      if Z.eqb pc PC_PUSHB then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) PC_PUSHB && Nat.leb j 27 && Z.eqb (npush j) (npush i + 1) && Z.leb (npush j) 4
                                  && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4368 2 [] (nth i FFS []) STR_W STAT None c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
                                     | Some ci => (Z.eqb (CH2.ci_csp ci) (-112) && Nat.eqb (CH2.ci_nx ci) (bvar j))%bool | None => false end
                                  && CL.ps_reg_is ps 10 OE
                                  && match find (fun ie : nat * expr => Nat.eqb (fst ie) 11) (SR.ps_regs ps) with Some (_, e) => a1ok e | None => false end)%bool
                    | None => false end
        | None => false end
      else (CBA.exit_base_chk GT.NF RETPC c ps && Z.leb (npush i) 4))%bool
  end.

Lemma kword32_intro : forall segs E (M : word -> option byte) a v A z, estart E a = A -> 0 <= A -> A + 4 <= 2 ^ 64 -> edenot E v = Z_to_bv 64 z ->
  L5.u32_at segs M A z -> kentry_ok segs E M (KWord a 4 v).
Proof.
  intros segs E M a v A z Ha H0 H4 Hv Hu. cbn [kentry_ok].
  assert (Hfl : flat E a (Z.of_nat 4)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha, Hv. exact Hu.
Qed.

Lemma regs_ok_upd : forall E sr (R : bvmap 5 word) (r0 : bv 5) e, regs_ok E sr R -> getr R r0 = edenot E e -> regs_ok E (sr_upd sr (ridx r0) e) R.
Proof.
  intros E sr R r0 e HR He r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
  - specialize (HR r). unfold sr_get in HR. rewrite Er in HR. exact HR.
  - rewrite nth_sr_upd. destruct (Nat.eqb_spec (ridx r) (ridx r0)) as [ee|ne].
    + assert (r = r0) as -> by (rewrite <- (CC.reg_of_ridx r), <- (CC.reg_of_ridx r0), ee; reflexivity). exact He.
    + specialize (HR r). unfold sr_get in HR. rewrite Er in HR. exact HR.
Qed.
Lemma regs01 : forall i, (i <= 1)%nat -> CC.cp_regs (nth i G.CPS G.cp0) = sr_upd (sr_upd sr_id 11 (ELit 1)) 13 (ELit 0).
Proof. intros i Hi. destruct i as [|[|i]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; clear - Hi; lia]. Qed.
Lemma kn_common : firstn NKC (CC.cp_know G.cp1) = firstn NKC (CC.cp_know G.cp0).
Proof. vmc_refl. Qed.
Lemma kn0_eq : CC.cp_know G.cp0 = firstn NKC (CC.cp_know G.cp0) ++ [KAlign CPAE 8; SHB 4].
Proof. vmc_refl. Qed.
Lemma kn1_eq : CC.cp_know G.cp1 = firstn NKC (CC.cp_know G.cp0) ++ [SHB 0].
Proof. vmc_refl. Qed.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma ffs_i : forall i, nth i FFS [] = [].
Proof. intros i. do 28 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma bls_i : forall i, (i <= 27)%nat -> nth i G.BLS [] = [(EVar (bvar i), EVar (bvar i + 1)%nat)].
Proof. intros i Hi. do 28 (destruct i as [|i]; [reflexivity|]). exfalso; clear - Hi; lia. Qed.
Lemma npush_rng : forall i, 0 <= npush i <= 4.
Proof. intros i. do 28 (destruct i as [|i]; [cbn; lia|]). destruct i; cbn; lia. Qed.

Lemma a1ok_sound : forall E e, a1ok e = true -> 0 <= CL5A.uv E e < 256.
Proof.
  intros E e H. destruct e as [c| |op a b| | | | |]; try discriminate H.
  - cbn [a1ok] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold CL5A.uv. cbn [edenot]. rewrite L5.unsigned_lit by lia. lia.
  - destruct op; try discriminate H. destruct b as [m| | | | | | |]; try discriminate H. cbn [a1ok] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    unfold CL5A.uv. cbn [edenot]. rewrite u_and64. rewrite L5.unsigned_lit by lia.
    pose proof (u64_range (edenot E a)) as Ra. split; [apply Z.land_nonneg; right; lia | ].
    pose proof (land_le_r (bv_unsigned (edenot E a)) m ltac:(unfold two64 in Ra; lia) H1). lia.
Qed.

Lemma find_reg11 : forall ps, match find (fun ie : nat * expr => Nat.eqb (fst ie) 11) (SR.ps_regs ps) with Some (_, e') => a1ok e' | None => false end = true ->
  exists e, CL.ps_reg_is ps 11 e = true /\ a1ok e = true.
Proof.
  intros ps H. destruct (find (fun ie : nat * expr => Nat.eqb (fst ie) 11) (SR.ps_regs ps)) as [[n e']|] eqn:Hf; [|discriminate H].
  apply find_some in Hf as [Hin Hn]. cbn [fst] in Hn.
  exists e'. split; [|exact H]. unfold CL.ps_reg_is. apply existsb_exists. exists (n, e'). split; [exact Hin|]. cbn [fst snd]. rewrite Hn, APS.expr_eqb_refl'. reflexivity.
Qed.
End CVA.

Section ConvertOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis PUSHB_OK : PMSA.str_push_back_specA L ar HI CVA.PC_PUSHB.

Definition hid (P : Prop) : Prop := P.

Lemma lor7 : forall x, 0 <= x -> Z.lor x 7 = 8 * (x / 8) + 7.
Proof.
  intros x Hx. pose proof (Z.add_lor_land x 7) as H.
  assert (L7 : Z.land x 7 = x mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  rewrite L7 in H. pose proof (Z.div_mod x 8 ltac:(lia)). lia.
Qed.
Lemma grow_cap_facts : forall cap need, 24 <= cap -> cap mod 8 = 0 -> cap <= 2 ^ 26 -> 0 <= need < 2 ^ 26 ->
  let c := PML.grow_cap cap need in 2 * cap <= c /\ need < c /\ c <= 2 ^ 27 /\ c mod 8 = 0.
Proof.
  intros cap need H24 H8 Hc Hn. cbv zeta. unfold PML.grow_cap. set (m := Z.max need (2 * (cap - 1))).
  assert (Hm : 2 * cap - 2 <= m /\ need <= m /\ m <= 2 ^ 27 - 2) by (unfold m; lia).
  rewrite lor7 by lia. pose proof (Z.div_mod m 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as B.
  assert (Hq : (2 * cap - 2) / 8 <= m / 8) by (apply Z.div_le_mono; lia).
  assert (Hc8 : (2 * cap - 2) / 8 = cap / 4 - 1).
  { pose proof (Z.div_mod cap 8 ltac:(lia)) as Dc. rewrite H8 in Dc. set (q := cap / 8) in *.
    replace (2 * cap - 2) with (6 + (2 * q - 1) * 8) by lia. rewrite Z.div_add by lia. replace cap with (0 + (2 * q) * 4) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (Hc4 : 4 * (cap / 4) = cap).
  { pose proof (Z.div_mod cap 8 ltac:(lia)) as Dc. rewrite H8 in Dc. set (q := cap / 8) in *. replace cap with (0 + (2 * q) * 4) by lia. rewrite Z.div_add by lia. change (0 / 4) with 0. lia. }
  assert (Hu : m / 8 < 2 ^ 24) by (apply Z.div_lt_upper_bound; lia).
  split; [lia|]. split; [lia|]. split; [lia|].
  replace (8 * (m / 8) + 7 + 1) with (0 + (m / 8 + 1) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma log2_halves : forall cap c, 24 <= cap -> 2 * cap <= c -> c <= 2 ^ 27 -> Z.log2 (2 ^ 27 / c) + 1 <= Z.log2 (2 ^ 27 / cap).
Proof.
  intros cap c H24 H2 Hc.
  assert (A1 : 2 ^ 27 / c <= 2 ^ 27 / (2 * cap)) by (apply Z.div_le_compat_l; lia).
  assert (B : 2 ^ 27 / (2 * cap) = 2 ^ 27 / cap / 2) by (rewrite Z.div_div by lia; f_equal; lia).
  assert (C2 : 2 <= 2 ^ 27 / cap) by (apply Z.div_le_lower_bound; lia).
  pose proof (Z.log2_le_mono _ _ A1) as M1. rewrite B in M1. set (x := 2 ^ 27 / cap) in *.
  assert (Y : 1 <= x / 2) by (apply Z.div_le_lower_bound; lia).
  pose proof (Z.log2_double (x / 2) ltac:(lia)) as Dd. pose proof (Z.mul_div_le x 2 ltac:(lia)) as Le.
  pose proof (Z.log2_le_mono _ _ Le) as M2. lia.
Qed.

Lemma bufcredA_push : forall cr cap kx bx need, PMSA.bufcredA L cr cap kx bx -> 24 <= cap -> cap mod 8 = 0 -> cap <= need -> need < 2 ^ 26 ->
  let c := PML.grow_cap cap need in
  acredit_ok L cr c /\ PMSA.bufcredA L (adebit L cr c) c kx bx /\ 2 * cap <= c /\ need < c /\ c mod 8 = 0.
Proof.
  intros cr cap kx bx need (C1 & K0 & B0 & HK & HB) H24 H8 Hn Hn2. destruct (L5A.aly_cost L C LAY) as (P1 & P2 & P3).
  destruct (grow_cap_facts cap need H24 H8 ltac:(clear - Hn Hn2; lia) ltac:(clear - Hn Hn2 H24; lia)) as (G1 & G2 & G3 & G4). cbv zeta.
  unfold acredit_ok, adebit, PMSA.bufcredA. cbn [fst snd]. set (c := PML.grow_cap cap need) in *.
  pose proof (log2_halves cap c H24 G1 G3) as LG. pose proof (Z.log2_nonneg (2 ^ 27 / c)) as L0.
  set (l' := Z.log2 (2 ^ 27 / c)) in *. set (l := Z.log2 (2 ^ 27 / cap)) in *. clearbody l l' c.
  set (kpm := hl_k_per_malloc L) in *. set (blin := hl_b_lin L) in *. set (bov := hl_b_overhead L) in *. clearbody kpm blin bov.
  change (2 ^ 28) with 268435456 in *. change (2 ^ 27) with 134217728 in *. change (2 ^ 26) with 67108864 in *.
  assert (L1 : 1 <= l) by (clear - LG L0; lia).
  assert (X1 : kpm <= l * kpm) by (clear - L1 P1; nia). assert (X2 : bov <= l * bov) by (clear - L1 P3; nia).
  assert (X3 : blin * c <= blin * (268435456 - 2 * cap)) by (apply Z.mul_le_mono_nonneg_l; clear - P2 G1 G3 H24; lia).
  assert (X4 : blin * (268435456 - 2 * c) + blin * c <= blin * (268435456 - 2 * cap)) by (rewrite <- Z.mul_add_distr_l; apply Z.mul_le_mono_nonneg_l; clear - P2 G1 G3 H24; lia).
  assert (X5 : l' * kpm + kpm <= l * kpm) by (rewrite <- Z.mul_succ_l; apply Z.mul_le_mono_nonneg_r; clear - P1 LG; lia).
  assert (X6 : l' * bov + bov <= l * bov) by (rewrite <- Z.mul_succ_l; apply Z.mul_le_mono_nonneg_r; clear - P3 LG; lia).
  split; [clear - HK HB X1 X2 X3 K0 B0; split; lia|].
  split; [|clear - G1 G2 G4; lia]. split; [exact G3|]. split; [exact K0|]. split; [exact B0|].
  clear - HK HB X4 X5 X6 K0 B0. split; lia.
Qed.

Lemma bufcredA_afford : forall cr cap kx bx n, PMSA.bufcredA L cr cap kx bx -> 24 <= cap -> cap mod 8 = 0 -> n + 1 < 2 ^ 26 -> 0 <= n ->
  cap <= n + 1 -> acredit_ok L cr (PML.grow_cap cap (n + 1)).
Proof. intros cr cap kx bx n HC H24 H8 Hn Hn0 Hle. exact (proj1 (bufcredA_push cr cap kx bx (n + 1) HC H24 H8 Hle Hn)). Qed.

Lemma nodup_notin : forall (x : Z) (l : list Z), base.NoDup (x :: l) -> ~ In x l.
Proof. intros x l H Hin. apply list_relations.list.NoDup_cons in H as [Hx _]. apply Hx. apply list_elem_of_In. exact Hin. Qed.

Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.

Theorem convert_ok : PMSA.convert_specA L ar HI 812508.
Proof.
  unfold PMSA.convert_specA. intros LB FF LK cr A o cap p cpa cp sp r kx bx s. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
         (Ha0 & Ha1 & Ha2 & Ha3 & Hcp & HCP & Cfr & HCPA & HSTR & HCAP & HinB & HSHB & OO & Hstksh & HLEN & HCR) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.a2, PMSA.a3, PMSA.CONVERT_SCR, PMSA.STR_SCR, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR, PMSA.fobj, PMSA.ainfr, PMSA.u32 in *.
  change (128 + (256 + (16 + 4096))) with 4496 in *.
  destruct OO as (Ofr & O8 & Osh). change (24 / 8) with 3 in Osh.
  pose proof HSTR as (HLS & CAP8 & SLT).
  set (slen := Z.of_nat (length s)) in *.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WFT. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFT) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  destruct (CL5A.infr_rng L ar LB FF cpa 4 RFx Cfr ltac:(clear; lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).

  assert (HI0 : exists i0 : nat, (i0 <= 1)%nat /\ ((i0 = 0%nat /\ cpa mod 8 = 0 /\ byte_at M (S cpa) 4) \/ (i0 = 1%nat /\ byte_at M (S cpa) 0))).
  { destruct HCPA as [(C8m & Csh)|Csh]; [exists 0%nat; split; [clear; lia | left; split; [reflexivity | exact (conj C8m Csh)]] | exists 1%nat; split; [clear; lia | right; split; [reflexivity | exact Csh]]]. }
  clear HCPA. destruct HI0 as (i0 & Hi01 & HV).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  change (hid (cpa + 4 <= 2147446784 \/ 17594333495296 <= cpa)) in Q5. change (hid (cpa + 4 <= hl_img_lo L \/ hl_img_hi L <= cpa)) in Q7.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  assert (SHR : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.

  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (p, cap) HinB) as ((K0 & K1 & K16 & K3 & K4 & (K5 & K6 & K7)) & Kdef & Ksha & Kbap & Kfap). cbn [fst snd] in K0, K1, K16, K3, K4, K5, K6, K7, Kdef, Ksha, Kbap, Kfap.
  change (hid (p + cap <= 2147446784 \/ 17594333495296 <= p)) in K6.

  destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ WFT) as (ND1 & ND2).
  set (LBR := lb_remove p LB).
  assert (IBR : incl LBR LB) by (intros y Hy; unfold LBR in Hy; exact (L5C.in_lb_remove p y LB Hy)).
  assert (RFr : CHA.rng_facts L ar LBR FF) by (apply (CHA.rng_incl L ar LB FF); [exact RFx | exact IBR | apply incl_refl]).

  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [cp; p; cap] 0))) (fun _ => @nil (bv 8))).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 cpa) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 o) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 cp) by reflexivity. assert (V33 : ev E0 33 = Z_to_bv 64 p) by reflexivity. assert (V34 : ev E0 34 = Z_to_bv 64 cap) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = cpa) by (rewrite V10; apply u64_of_Z; clear - Q3 Q6; lia).
  assert (U12 : bv_unsigned (ev E0 12) = o) by (rewrite V12; apply u64_of_Z; clear - O3 O6; lia).
  assert (U32 : bv_unsigned (ev E0 32) = cp) by (rewrite V32; apply u64_of_Z; clear - HCP; lia).
  assert (U33 : bv_unsigned (ev E0 33) = p) by (rewrite V33; apply u64_of_Z; clear - K0 K7 K3; lia).
  assert (U34 : bv_unsigned (ev E0 34) = cap) by (rewrite V34; apply u64_of_Z; clear - K3 K7 K0; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 4496) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := [(o, 24)] : list L5.range). set (Wo := WW).
  assert (WINC : incl Wo WW) by (apply incl_refl).
  assert (WOK : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LBR FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar LBR FF sp _ o 24 a RFr Ofr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w Wo /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U12 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LBR FF sp G.HDECL a)).
  { intros rg Hrg. exfalso. exact Hrg. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha; cbn [fst snd] in Ha; rewrite ILO, IHI; (split; [clear - Ha; lia|]); intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  assert (KSHO : forall ob n a, CL5A.ainfr FF ob n -> 0 < n -> ob + n <= 2 ^ 47 -> in_shadow_of ob n a -> CHA.akept L ar LBR FF sp (CH.hd_scr G.HDECL) WW a).
  { intros ob n a Hfr Hn Hon Ha. destruct (CL5A.infr_sh_wok L ar LBR FF sp (CH.hd_scr G.HDECL) ob n a RFr Hfr Hn Ha) as (G1 & G2 & _).
    destruct (CL5A.infr_rng L ar LBR FF ob n RFr Hfr Hn) as (_ & _ & X3 & _). pose proof (SHR ob n a X3 Hn Hon Ha) as SRa.
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin SRa O5. lia. }
  assert (AL : (sp - 4496) mod 8 = 0) by (clear - S1; pose proof (Z_div_mod_eq_full sp 16) as D; rewrite S1, Z.add_0_r in D; rewrite D; replace (16 * (sp / 16) - 4496) with ((2 * (sp / 16) - 562) * 8) by lia; apply Z_mod_mult).
  assert (KSTK : forall a, S (sp - 4496) <= a < S (sp - 4496) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 4496)) / 8 -> CHA.akept L ar LBR FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. destruct (PTA.stksh_rng ar sp 4496 a ltac:(clear - S2; lia) AL C8 (proj2 SP1) (CHA.wf_top _ _ _ _ _ _ _ _ WFT) ltac:(clear - CL; lia) Ha) as (G1 & G2).
    split; [exact G1|]. split; [do 4 right; left; exact G2|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5.
    unfold in_shadow_of, S, SB in G2. clear - Hin G2 O5 CL. lia. }

  assert (BLKW : forall LBX FFX LKX crX AX MX VX u n, ri_inv HI LBX FFX LKX crX AX MX VX -> In (u, n) LBX ->
            (4096 <= u /\ 0 < n /\ u + n <= ahl_ceil ar /\ u mod 16 = 0 /\ (u + n <= 2147446784 \/ 17594333495296 <= u) /\ u + n <= 140737488355328)
            /\ (u + n <= hl_img_lo L \/ hl_img_hi L <= u) /\ fframes_apart u n FFX /\ (u + n <= ar_fs ar \/ ar_fs ar + 11571200 <= u) /\ HeapIface.defined MX u n
            /\ base.NoDup (map fst LBX)).
  { intros LBX FFX LKX crX AX MX VX u n HHX Hun.
    destruct (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHX) as (WB & _). destruct (WB (u, n) Hun) as (B1 & B2 & _ & _ & _ & B6 & B7). cbn [fst snd] in B1, B2, B6, B7.
    destruct B1 as (R1 & R2 & R3 & R4 & R5 & (R6 & R7 & R8)). unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
    split; [clear - R1 R3 R4 R5 R7 R8; lia|]. split; [exact R2|]. split; [intros f Hf; apply B6; apply in_or_app; left; exact Hf|]. split; [exact B7|]. split; [exact B2|].
    exact (proj1 (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHX))). }

  set (STR := fun (pp cc : Z) (s' : list Z) (M1 : word -> option byte) =>
              PMLA.str_at (hl_segs L) M1 o (PML.SLong cc pp s') /\ shadow_blk M1 pp cc /\ 24 <= cc /\ cap <= cc /\ slen <= Z.of_nat (length s')).
  set (Cred := fun (i : nat) (E1 : env) (cr1 : credit) => PMSA.bufcredA L cr1 (CL5A.uv E1 (EVar (CVA.bvar i + 1)%nat)) kx bx).
  set (XI := fun (i : nat) (E1 : env) (_ : list (Z * Z)) (M1 : word -> option byte) (_ : Model) =>
               exists s', STR (CL5A.uv E1 (EVar (CVA.bvar i))) (CL5A.uv E1 (EVar (CVA.bvar i + 1)%nat)) s' M1 /\ Z.of_nat (length s') <= slen + CVA.npush i).

  assert (CUTF : forall i E1 A1 M1 m1, (i <= 27)%nat -> CHA.aamb L ar HI GT.NF E0 M model A LBR FF LK sp G.HDECL WW G.BLS CVA.FFS Cred 0 i E1 A1 M1 m1 ->
            CHA.curB LBR G.BLS i E1 = (CL5A.uv E1 (EVar (CVA.bvar i)), CL5A.uv E1 (EVar (CVA.bvar i + 1)%nat)) :: LBR /\ CHA.curF FF sp CVA.FFS i E1 = FF /\ env_agree GT.NF E0 E1 /\
            (exists crX LKX, ri_inv HI ((CL5A.uv E1 (EVar (CVA.bvar i)), CL5A.uv E1 (EVar (CVA.bvar i + 1)%nat)) :: LBR) FF LKX crX A1 M1 (vml_of m1) /\ Cred i E1 crX)).
  { intros i E1 A1 M1 m1 Hi HA. pose proof HA as (_ & _ & _ & HagE & (cra & LKa & HHa & _ & HCa & _) & _).
    assert (HcB : CHA.curB LBR G.BLS i E1 = (CL5A.uv E1 (EVar (CVA.bvar i)), CL5A.uv E1 (EVar (CVA.bvar i + 1)%nat)) :: LBR).
    { unfold CHA.curB. rewrite (CVA.bls_i i Hi). unfold CH2.den, CL5A.uv. cbn [map fst snd edenot]. reflexivity. }
    assert (HcF : CHA.curF FF sp CVA.FFS i E1 = FF) by (unfold CHA.curF; rewrite (CVA.ffs_i i); reflexivity).
    rewrite HcB, HcF in HHa. split; [exact HcB|]. split; [exact HcF|]. split; [exact HagE|]. exists cra, LKa. split; [exact HHa | exact HCa]. }

  assert (LEAFK : forall i c ps0 E1 A1 M1 m1 E' R' M' m', nth_error G.CPS i = Some c -> CHA.aamb L ar HI GT.NF E0 M model A LBR FF LK sp G.HDECL WW G.BLS CVA.FFS Cred 0 i E1 A1 M1 m1 ->
            env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> CC.cp_F c = CVA.CPF0 ->
            bv_unsigned (ev E' 2) = sp /\ bv_unsigned (ev E' 10) = cpa /\ bv_unsigned (ev E' 12) = o
            /\ (forall X0, CVA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0)
            /\ (forall (q : nat) (e0 : expr) (z : Z), CL.ps_reg_is ps0 q e0 = true -> bv_unsigned (edenot E' e0) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z)
            /\ (forall a, 0 <= a < 2 ^ 64 -> (a < sp - 4496 \/ sp <= a) -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))).
  { intros i c ps0 E1 A1 M1 m1 E' R' M' m' Hci HA Hag HLF YF.
    pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LBR FF LK sp G.HDECL WW G.BLS CVA.FFS Cred 0 i c E1 E' A1 M1 m1 HA (G.NF_le i c Hci) Hag) as HagE'.
    assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); unfold GT.NF; apply Nat.ltb_lt; exact Hn).
    assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite (FZ 2%nat eq_refl); exact U2).
    split; [exact W2|]. split; [rewrite (FZ 10%nat eq_refl); exact U10|]. split; [rewrite (FZ 12%nat eq_refl); exact U12|].
    split; [intros X0 HX0; apply CC.has_cell_In in HX0; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0)|].
    split; [intros q e0 z Hq Hz; rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq); rewrite <- Hz; symmetry; apply Z_to_bv_bv_unsigned|].
    intros a Ha Hout. apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). rewrite YF. unfold SGP.outside, CVA.CPF0. rewrite L5.unsigned_lit by exact Ha.
    repeat (apply Forall_cons); try (apply Forall_nil); cbn [fst snd]; unfold estart, elenZ; cbn [a_base a_off edenot]; rewrite ?W2; rewrite u64_of_Z by (clear; lia); clear - Hout; lia. }

  assert (STRAG : forall (M1 M2 : word -> option byte) pp cc s', (forall a, 0 <= a < 2 ^ 64 -> (a < sp - 4496 \/ sp <= a) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
            0 <= pp -> 0 < cc -> pp + cc <= ahl_ceil ar -> pp mod 16 = 0 -> STR pp cc s' M1 -> STR pp cc s' M2).
  { intros M1 M2 pp cc s' AGm P0 C0 PC P16 (X1 & X2 & X3 & X4 & X5).
    set (Sg := fun a => 0 <= a < sp - 4496).
    assert (AG' : forall a, Sg a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (intros a Ha; unfold Sg in Ha; apply AGm; [clear - Ha S3 SP1; lia | left; clear - Ha; lia]).
    split; [|split; [|split; [exact X3 | split; [exact X4 | exact X5]]]].
    - apply (PTA.str_long_ag (hl_segs L) M1 M2 Sg AG' o cc pp s'); [| | exact X1].
      + split; [clear - O3; lia|]. split; [clear - O6; lia|]. intros y Hy. unfold Sg. clear - Hy O3 O4 S2. lia.
      + split; [exact P0|]. split; [clear - PC CL SP1 S2 S3; lia|]. intros y Hy. unfold Sg. clear - Hy P0 PC S2. lia.
    - apply (PTA.shadow_blk_ag M1 M2 Sg AG' pp cc ltac:(clear - C0; lia)); [| exact (CHA.mod8_of_16 _ P16) | exact X2].
      intros a Ha. pose proof (SHR pp cc a P0 C0 ltac:(clear - PC CL SP1 S3; lia) Ha) as RG. unfold Sg. clear - RG CL S2. lia. }
  assert (NOGOTO : forall i c kk ps0 j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps0 (CC.TGoto j sg) -> False).
  { intros i c kk ps0 j sg IL. pose proof (CH2.leaves_all_sound _ _ _ CVA.leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  assert (LBRE : lb_remove p ((p, cap) :: LBR) = LBR) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
  rewrite <- LS in FPM.
  assert (Hc0 : nth_error G.CPS i0 = Some (nth i0 G.CPS G.cp0) /\ CC.cp_pc (nth i0 G.CPS G.cp0) = 812508) by (destruct i0 as [|[|i0]]; [split; reflexivity | split; reflexivity | exfalso; clear - Hi01; lia]).
  destruct Hc0 as (Hc0 & HPC0). rewrite <- HPC0.
  assert (B0 : CVA.bvar i0 = 33%nat /\ CVA.npush i0 = 0) by (destruct HV as [(-> & _)|(-> & _)]; split; reflexivity). destruct B0 as (BV0 & NP0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LBR FF LK sp G.HDECL WW Wo G.BLS CVA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := i0) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact CVA.heap_ok.
  - intros i c kk ps0 j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - intros i c kk ps0 j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  -
    intros i c kk ps0 pc IL. pose proof (CH2.leaves_all_sound _ _ _ CVA.leaf_ok _ _ _ _ _ IL) as X. unfold CVA.leaf_chk in X. cbn beta iota in X.
    assert (Hci : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hci & _); exact Hci).
    apply andb_prop in X as [X0 X]. apply andb_prop in X0 as [X0 Yi13]. apply andb_prop in X0 as [X0 Yfoot]. apply andb_prop in X0 as [Ynx YF].
    apply Nat.ltb_lt in Ynx. apply CBA.regions_eqb_eq in YF. apply Nat.leb_le in Yi13.
    destruct (Z.eqb_spec pc CVA.PC_PUSHB) as [->|Hne1].
    {
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y9]. apply andb_prop in X as [X Ynp4]. apply andb_prop in X as [X Ynp].
      apply andb_prop in X as [X Yj13]. apply andb_prop in X as [Y0 _] || rename X into Y0.
      apply Z.eqb_eq in Y0. apply Nat.leb_le in Yj13. apply Z.eqb_eq in Ynp. apply Z.leb_le in Ynp4.
      lazymatch type of Y9 with match ?t with _ => _ end = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end.
      apply andb_prop in Y9 as [Ycsp Ygx]. apply Z.eqb_eq in Ycsp. apply Nat.eqb_eq in Ygx.
      destruct (CVA.find_reg11 ps0 Y11) as (e11 & Ye11 & Yok). pose proof (npush_i := CVA.npush_rng i).
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI].
      destruct (CUTF i E1 A1 M1 m1 Yi13 HA) as (HcB & HcF & HagE & _).
      pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LBR FF LK sp G.HDECL WW Wo G.BLS CVA.FFS Cred 0 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
      refine (CALLEE CVA.PC_PUSHB 4368 2%nat [] CVA.STR_W CVA.STAT None 0 i c ps0 j cj ci Hcj Hchk Y0 _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite !CVA.ffs_i; reflexivity | rewrite CVA.ffs_i; cbn; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HVV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      destruct (LEAFK i c ps0 E1 A1 M1 m1 E' R' M' m' Hci HA Hag HLF YF) as (W2 & W10 & W12 & CELL & REG & AGR).
      pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).

      set (pp := CL5A.uv E1 (EVar (CVA.bvar i))) in *. set (cc := CL5A.uv E1 (EVar (CVA.bvar i + 1)%nat)) in *.
      destruct HXI as (s' & HS1 & HL1).
      destruct (BLKW _ _ _ _ _ _ _ pp cc HH1 (or_introl eq_refl)) as ((Rb1 & Rb4 & Rb5 & Rb16 & Rb6 & Rb7) & _ & _ & _ & _ & NDc).
      pose proof (STRAG M1 M' pp cc s' AGR ltac:(clear - Rb1; lia) Rb4 Rb5 Rb16 HS1) as HS'.
      pose proof HS' as ((HLS' & CC8 & SLT') & HSB' & C24 & CLE & SLE).
      assert (HC1' : PMSA.bufcredA L cr1 cc kx bx) by exact HC1.
      set (cb := CL5A.uv E' e11). pose proof (CVA.a1ok_sound E' e11 Yok) as CB. fold cb in CB.
      assert (LS2 : Z.of_nat (length s') + 1 < 2 ^ 26) by (clear - HL1 HLEN Ynp Ynp4 npush_i; lia).
      assert (LBRN : lb_remove pp ((pp, cc) :: LBR) = LBR) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
      eexists. eexists. split; [exact (PUSHB_OK ((pp, cc) :: LBR) FF LK1 cr1 A1 o cc pp cb (sp + CH2.ci_csp ci) (CC.cp_pc cj) s')|]. split.
      {
        unfold PMSA.a0, PMSA.a1, PMSA.str_at, PMSA.stksh, PMSA.fobj, PMLA.fobj, PMSA.STR_SCR, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR. change (256 + (16 + 4096)) with 4368.
        split; [exact (REG 10%nat _ o Y10 ltac:(unfold CVA.OE; cbn [edenot]; exact W12))|].
        split; [exact (REG 11%nat _ cb Ye11 eq_refl)|].
        split; [exact CB|]. split; [exact HLS'' || exact (conj HLS' (conj CC8 SLT'))|]. split; [exact C24|]. split; [left; reflexivity|]. split; [exact HSB'|].
        split.
        { split; [exact Ofr|]. split; [exact O8|]. change (24 / 8) with 3. intros jj Hjj. unfold byte_at.
          rewrite (Hfr1 _ (KSHO o 24 (S o + jj) Ofr ltac:(clear; lia) O6 (CL5A.shreg_in_shadow o 3 (S o + jj) O8 ltac:(clear; lia) ltac:(unfold S; clear - Hjj; lia)))). exact (Osh jj Hjj). }
        split.
        { apply (PTA.stksh_mono ar M' sp 4496 (sp + CH2.ci_csp ci) 4368); [| exact AL | | rewrite Ycsp; clear; lia].
          - apply (PTA.stksh_ag ar M M' sp 4496); [|exact Hstksh]. intros a Ha. exact (Hfr1 a (KSTK a Ha)).
          - rewrite Ycsp. clear - S1. pose proof (Z_div_mod_eq_full sp 16) as D. rewrite S1, Z.add_0_r in D. rewrite D.
            replace (16 * (sp / 16) + -112 - 4368) with ((2 * (sp / 16) - 560) * 8) by lia. apply Z_mod_mult. }
        split; [clear - LS2; lia|].
        intros Hle. exact (bufcredA_afford cr1 cc kx bx (Z.of_nat (length s')) HC1' C24 CC8 LS2 (Nat2Z.is_nonneg _) Hle). }

      intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (HGR & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
      assert (LS2' : Z.of_nat (length (s' ++ [cb])) = Z.of_nat (length s') + 1) by (rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; clear; lia).
      assert (GH : exists pn cn, 0 <= pn /\ pn + cn <= 2 ^ 47 /\ 0 < cn /\ STR pn cn (s' ++ [cb]) M2 /\ LB' = (pn, cn) :: LBR /\ LBk = LBR /\ PMSA.bufcredA L cr' cn kx bx).
      { unfold PMSA.str_grownA, PMSA.str_at, PMSA.afresh, PMLA.afresh in HGR. rewrite LBRN in HGR.
        destruct HGR as [(SA2 & SB2 & -> & -> & ->)|(p' & LE & SA2 & (AR' & _ & _ & _ & SB2) & -> & -> & ->)].
        - exists pp, cc. split; [clear - Rb1; lia|]. split; [exact Rb7|]. split; [exact Rb4|].
          split; [split; [exact SA2 | split; [exact SB2 | split; [exact C24 | split; [exact CLE | rewrite LS2'; clear - SLE; lia]]]]|].
          split; [reflexivity|]. split; [reflexivity | exact HC1'].
        - rewrite LS2' in LE, SA2, AR', SB2 |- *. destruct (bufcredA_push cr1 cc kx bx (Z.of_nat (length s') + 1) HC1' C24 CC8 LE LS2) as (_ & HCR2 & G2c & _ & _).
          set (cn := PML.grow_cap cc (Z.of_nat (length s') + 1)) in *. destruct AR' as (Qb0 & _ & _ & Qb3 & Qb4 & (_ & _ & Qb7)).
          exists p', cn. split; [clear - Qb0; lia|]. split; [exact Qb7|]. split; [exact Qb3|].
          split; [split; [exact SA2 | split; [exact SB2 | split; [clear - C24 G2c; lia | split; [clear - CLE G2c C24; lia | rewrite LS2'; clear - SLE; lia]]]]|].
          split; [reflexivity|]. split; [reflexivity | exact HCR2]. }
      clear HGR. destruct GH as (pn & cn & Pn0 & Pn47 & Cn0 & HS2 & -> & -> & HCRn).
      exists [Z_to_bv 64 pn; Z_to_bv 64 cn]. split; [reflexivity|]. cbv zeta. rewrite Ygx.
      pose proof (CH2.retEx_ghost E' (CVA.bvar j) [Z_to_bv 64 pn; Z_to_bv 64 cn] R2 0 ltac:(cbn; clear; lia)) as G56.
      pose proof (CH2.retEx_ghost E' (CVA.bvar j) [Z_to_bv 64 pn; Z_to_bv 64 cn] R2 1 ltac:(cbn; clear; lia)) as G57. cbn [nth] in G56, G57. rewrite Nat.add_0_r in G56.
      set (E2 := CH2.retEx E' (CVA.bvar j) [Z_to_bv 64 pn; Z_to_bv 64 cn] R2) in *.
      assert (T56 : CL5A.uv E2 (EVar (CVA.bvar j)) = pn) by (unfold CL5A.uv; cbn [edenot]; rewrite G56; apply u64_of_Z; clear - Pn0 Pn47 Cn0; lia).
      assert (T57 : CL5A.uv E2 (EVar (CVA.bvar j + 1)%nat) = cn) by (unfold CL5A.uv; cbn [edenot]; rewrite G57; apply u64_of_Z; clear - Pn0 Pn47 Cn0; lia).
      split; [exact I|].
      split; [cbn [CH2.den map app]; apply incl_refl|].
      split.
      { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (CVA.OE, 0, ELit 24). split; [left; reflexivity|].
        unfold CHA.in_reg, estart, elenZ, CVA.OE. cbn [a_base a_off edenot]. rewrite W12. rewrite u64_of_Z by (clear; lia). clear - Hin. lia. }
      split; [intros w a [<-|[]] Hin (_ & _ & Ko); exact (Ko (o, 24) (or_introl eq_refl) Hin)|].
      split; [unfold CHA.curB; rewrite (CVA.bls_i j Yj13); unfold CH2.den; cbn [map fst snd app edenot]; unfold CL5A.uv in T56, T57; cbn [edenot] in T56, T57; rewrite T56, T57; exact HH2|].
      split; [unfold Cred; rewrite T57; exact HCRn|].
      split; [unfold XI; exists (s' ++ [cb]); rewrite T56, T57; split; [exact HS2 | rewrite LS2', Ynp; clear - HL1; lia]|].

      intros X0 HX0 _. unfold CVA.STAT in HX0. cbn [In] in HX0.
      destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). }

    apply andb_prop in X as [Xbase Ynp4]. apply Z.leb_le in Ynp4.
    intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXI].
    destruct (CUTF i E1 A1 M1 m1 Yi13 HA) as (HcB & HcF & HagE & (crX & LKX & HHX & _)).
    refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LBR FF LK sp G.HDECL WW Wo G.BLS CVA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
              K DEF0 R r EV Hra Hraok CVA.RETPC i c ps0 _ Xbase Yfoot (CVA.ffs_i i) fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _); [rewrite LS; exact CVA.ret_at |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
    destruct (LEAFK i c ps0 E1 A1 M1 m1 E' R' M' m' Hci HA Hag HLF YF) as (W2 & W10 & W12 & CELL & REG & AGR).
    rewrite HcB in HH1. unfold Cred in HC1.
    set (pp := CL5A.uv E1 (EVar (CVA.bvar i))) in *. set (cc := CL5A.uv E1 (EVar (CVA.bvar i + 1)%nat)) in *.
    destruct HXI as (s' & HS1 & HL1).
    destruct (BLKW _ _ _ _ _ _ _ pp cc HH1 (or_introl eq_refl)) as ((Rb1 & Rb4 & Rb5 & Rb16 & Rb6 & Rb7) & _).
    pose proof (STRAG M1 M' pp cc s' AGR ltac:(clear - Rb1; lia) Rb4 Rb5 Rb16 HS1) as ((HLS' & CC8 & SLT') & HSB' & C24 & CLE & SLE).
    rewrite SCRV in HP.
    apply (Hcont fx' R' M' model2 ((pp, cc) :: LBR) cr1 LBR WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    exists cc, pp, s'. unfold PMSA.str_at.
    split; [exact (conj HLS' (conj CC8 SLT'))|]. split; [exact HSB'|]. split; [exact CLE|]. split; [clear - SLE HL1 Ynp4; lia|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HC1.
  - exact Hc0.
  -
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hcl Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hcl Hs)).
    assert (VT : CL5A.visr (ahid A model) cpa 4).
    { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 cpa 4 (cpa + k) RFx Cfr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (SHC : in_shadow_of cpa 4 (S cpa)) by (unfold in_shadow_of, S; split; [clear; lia | apply Z.add_le_mono_r; apply Z.div_le_mono; clear; lia]).
    assert (VST : ahid A model (Z_to_bv 64 (S cpa)) = false).
    { destruct (CL5A.infr_sh_wok L ar LB FF sp 0 cpa 4 (S cpa) RFx Cfr ltac:(clear; lia) SHC) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4496) 4496).
    { intros k Hk. apply CLV; [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DS : L5.defined Mv (sp - 4496) 4496) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    pose proof (CHA.shadow_range cpa 4 (S cpa) Q3 ltac:(clear; lia) Q6 SHC) as SRt.
    assert (SHBI : forall v, byte_at M (S cpa) v -> 0 <= v < 256 -> kentry_ok (hl_segs L) E0 Mv (CVA.SHB v)).
    { intros v Hb Hv. eapply CL5A.kword8_intro with (A := S cpa) (z := v); [unfold CVA.CPAE; rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U10; unfold S, SB, CVA.SBz; reflexivity | clear - SRt; lia | clear - SRt; lia | reflexivity | clear - Hv; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [clear - SRt; lia | clear - SRt; lia | intros k Hk; replace (S cpa + k) with (S cpa) by (clear - Hk; lia); exact VST |].
      unfold L5.u8_at. unfold byte_at in Hb. cbn [rdn]. rewrite Hb. reflexivity. }
    split.
    { rewrite (CVA.regs01 i0 Hi01). apply (CVA.regs_ok_upd E0 (sr_upd sr_id 11 (ELit 1)) R 13%bv (ELit 0)); [apply (CVA.regs_ok_upd E0 sr_id R 11%bv (ELit 1)); [exact (regs_ok_id R _ _) | cbn [edenot]; exact Ha1] | cbn [edenot]; exact Ha3]. }
    assert (KC : Forall (kentry_ok (hl_segs L) E0 Mv) (firstn CVA.NKC (CC.cp_know G.cp0))).
    { let l := eval vm_compute in (firstn CVA.NKC (CC.cp_know G.cp0)) in change (firstn CVA.NKC (CC.cp_know G.cp0)) with l.
      repeat (apply Forall_cons); try (apply Forall_nil).
      + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      + eapply CVA.kword32_intro with (A := cpa) (z := cp); [ev0 | clear - Q3; lia | clear - Q6; lia | exact V32 |].
        apply (CL5A.u32_vis (hl_segs L)); [clear - Q3; lia | clear - Q6; lia | exact VT | exact Hcp].
      + eapply CL5.krange_intro with (v := cp); [lin_eval; rw_atoms; clear; lia | clear - HCP; lia | clear - HCP; lia].
      + eapply CL5.krange_intro with (v := cpa); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear - Q1 Q4 FSLO CL SP1 S2 S3; lia].
      + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := cpa) (N2 := 4); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in Q5; clear - Q5; lia].
      + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO CL SP1 S2 S3; lia].
      + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact O8].
      + eapply CL5.kunk_intro with (A := sp - 4496) (N := 4496); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
      + eapply CL5.kwr_intro with (A := sp - 4496) (N := 4496); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
      + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
      + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
      + eapply CL5.kdisj_intro with (A1 := sp - 4496) (N1 := 4496) (A2 := cpa) (N2 := 4); [ev0 | reflexivity | ev0 | reflexivity | clear - Q4 S2; lia].
      + eapply CL5.kdisj_intro with (A1 := sp - 4496) (N1 := 4496) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia]. }
    unfold know_ok. destruct HV as [(-> & C8m & Csh)|(-> & Csh)].
    + change (nth 0 G.CPS G.cp0) with G.cp0. rewrite CVA.kn0_eq. apply Forall_app. split; [exact KC|].
      repeat (apply Forall_cons); try (apply Forall_nil); [| exact (SHBI 4 Csh ltac:(clear; lia))].
      eapply CL5.kalign_intro with (v := cpa); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear; lia | exact C8m].
    + change (nth 1 G.CPS G.cp0) with G.cp1. rewrite CVA.kn1_eq. apply Forall_app. split; [exact KC|].
      repeat (apply Forall_cons); try (apply Forall_nil). exact (SHBI 0 Csh ltac:(clear; lia)).
  -
    assert (HBL0 : CH2.den E0 (nth i0 G.BLS []) = [(p, cap)]).
    { rewrite (CVA.bls_i i0 ltac:(clear - Hi01; lia)), BV0. unfold CH2.den. cbn [map fst snd edenot Nat.add]. rewrite U33, U34. reflexivity. }
    assert (UV33 : CL5A.uv E0 (EVar (CVA.bvar i0)) = p) by (rewrite BV0; unfold CL5A.uv; cbn [edenot]; exact U33).
    assert (UV34 : CL5A.uv E0 (EVar (CVA.bvar i0 + 1)%nat) = cap) by (rewrite BV0; unfold CL5A.uv; cbn [edenot Nat.add]; exact U34).
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. rewrite HBL0, (CVA.ffs_i i0). cbn [CHA.denF map app length Z.of_nat Z.sub].
      split; [unfold LBR; exact (CBA.own_front L ar C HI HIok _ _ _ _ _ _ _ p cap HH HinB)|].
      split; [apply incl_refl|]. split; [unfold Cred; rewrite UV34; exact HCR | replace (0 - 0) with 0 by (clear; lia); exact Hroom].
    + unfold XI. exists s. rewrite UV33, UV34, NP0. split; [|clear; lia].
      split; [exact HSTR|]. split; [exact HSHB|]. split; [exact HCAP|]. split; clear; lia.
  - exact Hfp.
Qed.
End ConvertOk.

