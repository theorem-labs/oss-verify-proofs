(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutBridgeB CutRtCpsA CutRtA CutRtB CutRtC CutRtD CutShA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmCurDefs PmFloatCSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import FiKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_fromint_i64_casan_T Cut_fromint_i64_casan_D Cut_fromint_i64_casan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_fromint_i64_casan_D.
Module GC := Cut_fromint_i64_casan.
Module GT := Cut_fromint_i64_casan_T.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.

Module FIX.
Definition PC_SM3 : Z := 413508.
Definition PC_SETSH : Z := 535276.
Definition REENT : Z := 841704.
Definition NLOOP : Z := 841636.
Definition RETPC : Z := 842244.
Definition SBz : Z := 2147450880.
Definition IMGHI : Z := 7024640.
Definition MAGIC : Z := 7378697629483820647.
Definition VE := EVar 10. Definition OE := EVar 11. Definition FLE := EVar 40. Definition FE := EVar 45. Definition QE := EVar 68.
Definition SPX : expr := EAlu Instr.ALU_ADD (EVar 2) (ELit 16).
Definition FRM : list (expr * Z * Z) := [(FE, 3, -128)].
Definition FFS : list (list (expr * Z * Z)) := [] :: [] :: map (fun _ => FRM) (tl (tl G.CPS)).
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1427896) 8 (ELit SBz); KWord (SA (ELit 0) 1427904) 4 (ELit 1)].
Definition FLAGN : list kentry := [KWord (SA FE 504) 8 FLE; KWr (SA FLE 0) (ELit 1)].
Definition sm_ok (ps : SR.post_spec) (X : kentry) : bool :=
  (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRA.smalloc_fact_ok IMGHI G.HDECL (SR.ps_cells ps) 40 [] [] 3 45 40 X)%bool.
Definition NEWS_SM (ps : SR.post_spec) (cj : CC.cutpoint) : list kentry := List.filter (sm_ok ps) (CC.cp_know cj).
Definition has := CC.has_cell.
Definition CPF0 : list SGP.region := [(EVar 2, -4864, ELit 4864); (EVar 2, 0, ELit 16); (OE, 0, ELit 24)].
Definition CPF : list SGP.region := CPF0 ++ [(FE, 0, ELit 24); (FE, 32, ELit 472); (CHA.SRL3 FE, SBz, ELit 64)].
Definition CPFX : list SGP.region := CPF ++ [(FLE, 0, ELit 1)].

Definition HVR : list nat := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition HVN : list nat := [1; 5; 6; 7; 14; 16; 17; 28; 29; 30; 31]%nat.
Definition mk_sR (c : nat) (ps : SR.post_spec) : CC.subst :=
  [(40%nat, FLE); (45%nat, FE)] ++ map (fun ir => (57 + fst ir, FIK.reg_val (SR.ps_regs ps) (snd ir))%nat) (combine (seq 0 15) HVR)
  ++ map (fun i => (72 + i, FIK.cell_val (SR.ps_cells ps) FE (32 + Z.of_nat i) 1))%nat (seq 0 c).
Definition mk_sN (k : nat) (ps : SR.post_spec) : CC.subst :=
  [(40%nat, FLE); (45%nat, FE)] ++ map (fun ir => (57 + fst ir, FIK.reg_val (SR.ps_regs ps) (snd ir))%nat) (combine (seq 0 11) HVN)
  ++ [(68%nat, FIK.reg_val (SR.ps_regs ps) 15)]
  ++ map (fun i => (69 + i, FIK.cell_val (SR.ps_cells ps) FE (32 + Z.of_nat i) 1))%nat (seq 0 k).
Definition RESPK (i : nat) : kentry := KZero (SA (CHA.SRL3 (EAlu Instr.ALU_ADD FE (ELit (31 + Z.of_nat i)))) SBz) (ELit 1).
Definition RESP (c : nat) : list kentry := map RESPK (seq 1 c).
Definition resp_src (c : nat) (cells : list kentry) : bool :=
  forallb (fun i => has cells (KWord (SA (CHA.SRL3 FE) (SBz + (31 + Z.of_nat i) / 8)) 1 (ELit 0))) (seq 1 c).

Definition nlo (k : nat) : Z := 2 ^ 64 - 2 ^ 63 / 10 ^ Z.of_nat k.
Definition QX : expr := EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EMd Instr.M_MULH QE (ELit MAGIC)) (ELit 63)) (EAlu Instr.ALU_SRA (EMd Instr.M_MULH QE (ELit MAGIC)) (ELit 2)).
Definition QX1 : expr := EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRA (EMd Instr.M_MULH QE (ELit MAGIC)) (ELit 2)) (ELit 1).
Definition QFACT : kentry := KRange (EAlu Instr.ALU_SLTU (ELit 18446744073709551596) (EAlu Instr.ALU_ADD QE (ELit (-10)))) 0 0.
Definition KU0 : list kentry := [KUnk (SA FE 24) (ELit 8); KUnk (SA FE 32) (ELit 480)].
Definition UQ (k : nat) : list kentry := if Nat.eqb k 0 then KU0 else [KRange QE (nlo k) (2 ^ 64 - 1)].
Definition RC (ps : SR.post_spec) : nat := match FIK.reg_val (SR.ps_regs ps) 21 with ELit z => Z.to_nat z | _ => 0%nat end.

Definition exit_shape (n : nat) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (CL.ps_reg_is ps 10 (ELit (Z.of_nat n)) && has cells (KWord (SA OE 0) 1 (ELit (2 * Z.of_nat n)))
   && forallb (fun k => has cells (KWord (SA OE (1 + Z.of_nat k)) 1 (FIK.cell_val cells OE (1 + Z.of_nat k) 1))) (seq 0 n)
   && has cells (KWord (SA OE (1 + Z.of_nat n)) 1 (ELit 0)))%bool.
Definition nchars (i : nat) : nat := if Nat.leb i 79 then (i - 60)%nat else (i - 78)%nat.
Definition meas_src (i : nat) : Z := if Nat.eqb i 59 then 1048575 else if Nat.eqb i 60 then 1048575 else 524288 - (Z.of_nat i - 2).
Definition common_re (i : nat) (c : CC.cutpoint) (j : nat) (cj : CC.cutpoint) : bool :=
  (CHA.frames_eqb (nth i FFS []) FRM && CHA.frames_eqb (nth j FFS []) FRM && CH2.blocks_eqb (nth i G.BLS []) [] && CH2.blocks_eqb (nth j G.BLS []) []
   && CBA.regions_eqb (CC.cp_F c) CPF && Nat.leb 46 (CC.cp_nx c) && expr_eqb (CC.cp_meas c) (ELit (meas_src i)))%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      match CH2.ret_of G.RETS i k with
      | Some j =>
          match nth_error G.CPS j with
          | Some cj =>
              (CH2.blocks_eqb (nth i G.BLS []) [] && CH2.blocks_eqb (nth j G.BLS []) [] && CHA.frames_eqb (nth j FFS []) FRM
               && CHA.foot_chk GT.NF G.HDECL c [] (nth i FFS []) &&
              if Z.eqb pc PC_SM3 then
                (Z.eqb (SR.ps_pc ps) PC_SM3 && Nat.leb i 1 && Nat.eqb j (59 + i) && CBA.regions_eqb (CC.cp_F c) CPF0 && CHA.frames_eqb (nth i FFS []) []
                 && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 1 [] [] [] (NEWS_SM ps cj) None c ps cj [] [] [] FRM with
                    | Some ci => (Nat.eqb (CH2.ci_nx ci) 40 && Z.eqb (CH2.ci_csp ci) (-128))%bool | None => false end)%bool
              else if Z.eqb pc PC_SETSH then
                (Z.eqb (SR.ps_pc ps) PC_SETSH && Nat.leb 21 i && Nat.leb i 58 && Nat.eqb j (i + 40) && CHA.frames_eqb (nth i FFS []) FRM
                 && CBA.regions_eqb (CC.cp_F c) CPF && Nat.leb 46 (CC.cp_nx c)
                 && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 256 0 [] FRM [(CHA.SRL3 FE, SBz, ELit 64)] (STAT ++ FLAGN) None c ps cj [] FRM [] FRM with
                    | Some ci => (Z.eqb (CH2.ci_csp ci) (-128) && Nat.leb (CC.cp_nx c) (CH2.ci_nx ci))%bool | None => false end
                 && CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD (CHA.SRL3 FE) (ELit SBz)) && CL.ps_reg_is ps 11 (ELit 64) && has cells (KWord (SA FE 504) 8 FLE))%bool
              else false)%bool
          | None => false
          end
      | None =>
          if Z.eqb pc REENT then
            (let cc := RC ps in
             let j := if Nat.eqb i 59 then (20 + cc)%nat else (39 + cc)%nat in
             match nth_error G.CPS j with
             | Some cj =>
                 (Z.eqb (SR.ps_pc ps) REENT && (Nat.eqb i 59 || (Nat.leb 2 i && Nat.leb i 20 && Nat.eqb cc (i - 1))) && Nat.leb 1 cc && Nat.leb cc 19
                  && Z.eqb (CC.cp_pc cj) REENT && common_re i c j cj && expr_eqb (CC.cp_meas cj) (ELit 262144)
                  && FIK.reentry_chk_u GT.NF c ps cj (mk_sR cc ps) (RESP cc)
                  && CHA.goto_amb_chk GT.NF G.HDECL c (nth i G.BLS []) (nth j G.BLS []) (nth i FFS []) (nth j FFS []) (mk_sR cc ps)
                  && has (CC.cp_know c) (KAlign FE 64) && has (CC.cp_know c) (KRange FE 7024640 140737479966208) && resp_src cc cells)%bool
             | None => false
             end)
          else if Z.eqb pc NLOOP then
            (let kk := RC ps in
             let j := (2 + kk)%nat in
             match nth_error G.CPS j with
             | Some cj =>
                 (Z.eqb (SR.ps_pc ps) NLOOP && (Nat.eqb i 60 && Nat.eqb kk 0 || (Nat.leb 2 i && Nat.leb i 19 && Nat.eqb kk (i - 1))) && Nat.leb kk 18
                  && Z.eqb (CC.cp_pc cj) NLOOP && common_re i c j cj && expr_eqb (CC.cp_meas cj) (ELit (524288 - Z.of_nat kk))
                  && FIK.reentry_chk_u GT.NF c ps cj (mk_sN kk ps) (UQ kk)
                  && CHA.goto_amb_chk GT.NF G.HDECL c (nth i G.BLS []) (nth j G.BLS []) (nth i FFS []) (nth j FFS []) (mk_sN kk ps)
                  && (if Nat.eqb kk 0 then has cells (KUnk (SA FE 24) (ELit 488))
                      else ((expr_eqb (FIK.reg_val (SR.ps_regs ps) 15) QX || expr_eqb (FIK.reg_val (SR.ps_regs ps) 15) QX1) && has cells QFACT && has (CC.cp_know c) (KRange QE (nlo (kk - 1)) (2 ^ 64 - 1))
                            && Z.eqb (nlo kk) (2 ^ 64 - (2 ^ 64 - nlo (kk - 1)) / 10) && Nat.leb 69 (CC.cp_nx c))))%bool
             | None => false
             end)
          else
            (Z.eqb pc RETPC && CBB.exit_base_chk_sp GT.NF RETPC SPX c ps && Nat.leb 61 i && Nat.leb i 98
             && CBA.regions_eqb (CC.cp_F c) CPFX && CH2.blocks_eqb (nth i G.BLS []) [] && CHA.frames_eqb (nth i FFS []) FRM
             && match CHA.retire_chk GT.NF G.HDECL c [] FRM with Some fl => expr_eqb fl FLE | None => false end
             && has cells (KWord (SA FLE 0) 1 (ELit 0)) && Nat.leb 46 (CC.cp_nx c) && exit_shape (nchars i) ps)%bool
      end
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End FIX.

Lemma BLS_i : forall i, nth i G.BLS [] = [].
Proof.
  intros i. assert (HF : forallb (fun b : CA.blocks => match b with [] => true | _ => false end) G.BLS = true) by vmc_refl.
  destruct (Nat.lt_ge_cases i (length G.BLS)) as [Hl|Hg]; [|apply nth_overflow; exact Hg].
  pose proof (nth_In G.BLS [] Hl) as Hin. rewrite forallb_forall in HF. specialize (HF _ Hin). destruct (nth i G.BLS []); [reflexivity | discriminate].
Qed.
Lemma FFS_eq : FIX.FFS = [] :: [] :: repeat FIX.FRM 97.
Proof. vmc_refl. Qed.
Lemma FFS_i : forall i, nth i FIX.FFS [] = (if Nat.leb i 1 then [] else if Nat.leb i 98 then FIX.FRM else []).
Proof.
  intros i. rewrite FFS_eq. destruct i as [|[|i]]; [reflexivity | reflexivity |]. cbn [nth Nat.leb].
  destruct (Nat.lt_ge_cases i 97) as [Hl|Hg].
  - rewrite (nth_indep _ [] FIX.FRM) by (rewrite repeat_length; exact Hl). rewrite nth_repeat.
    destruct (Nat.leb_spec i 96); [reflexivity | lia].
  - rewrite nth_overflow by (rewrite repeat_length; exact Hg). destruct (Nat.leb_spec i 96); [lia | reflexivity].
Qed.

Section FromIntOk.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Abbreviation IC := PMLA.C_casan.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis SETSH : aset_shadow_spec L ar SCFG HI FIX.PC_SETSH 245 256.

Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.
Lemma nth_map_seq : forall (f : nat -> Z) n k d, (k < n)%nat -> nth k (map f (seq 0 n)) d = f k.
Proof. intros f n k d Hk. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hk). rewrite map_nth, seq_nth by exact Hk. reflexivity. Qed.
Lemma elit : forall E k, 0 <= k < 2 ^ 64 -> elenZ E (ELit k) = k.
Proof. intros E k Hk. unfold elenZ. cbn [edenot]. apply u64_of_Z. exact Hk. Qed.

Theorem from_integer_i64_ok : PMFCA.from_integer_i64_specA L ar HI IC 841088.
Proof.
  unfold PMFCA.from_integer_i64_specA, PMFCA.from_integer_specA.
  intros LB FF LK cr A o v sp r. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Hvr & Ha1 & Hstr & Hdef & (Ofr & O8 & Osh) & Hstksh & Hro & Hsp32) Hcont.
  assert (SCRE : PMFCA.FROMINT_SCR_A = 4880) by reflexivity. rewrite SCRE in *.
  assert (DE : PMFCA.FROMINT_D = 2) by reflexivity. rewrite DE in *.
  unfold PMSA.a0, PMSA.a1, PMSA.stksh in *. change (24 / 8) with 3 in Osh.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYH : FIX.IMGHI <= hl_img_hi L /\ hl_img_lo L < FS_BYTES) by (rewrite ILO, IHI; unfold FIX.IMGHI, FS_BYTES; clear; lia).

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8'). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (Hsp16 : (sp - 16) mod 32 = 0).
  { clear - Hsp32. pose proof (Z_div_mod_eq_full sp 32) as D. rewrite Hsp32 in D. rewrite D. replace (32 * (sp / 32) + 16 - 16) with ((sp / 32) * 32) by lia. apply Z_mod_mult. }
  assert (S1x : (sp - 16) mod 16 = 0) by (clear - Hsp16; apply Z.mod_divide in Hsp16; [|lia]; destruct Hsp16 as [q Hq]; rewrite Hq; replace (q * 32) with ((q * 2) * 16) by lia; apply Z_mod_mult).
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  assert (SHR : forall p k a, 0 <= p -> 0 < k -> p + k <= 2 ^ 47 -> in_shadow_of p k a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.

  set (RSP := regupd R 2%bv (Z_to_bv 64 (sp - 16))).
  set (E0 := Env (reg_ev RSP (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr RSP y) by (intros y; apply CL5.ev_reg).
  assert (EV' : forall y : reg, y <> 2%bv -> ev E0 (ridx y) = getr R y) by (intros y Hy; rewrite (EV y); unfold RSP; apply getr_other; exact Hy).
  assert (EVN : forall y : reg, In (ridx y) CBB.CSAVED_nosp -> ev E0 (ridx y) = getr R y).
  { intros y Hy. apply EV'. intros Heq. subst y. unfold CBB.CSAVED_nosp in Hy. cbn in Hy. clear - Hy. intuition discriminate. }
  assert (V2 : ev E0 2 = Z_to_bv 64 (sp - 16)) by (rewrite (EV 2%bv); unfold RSP; apply getr_same; discriminate).
  assert (SPE : edenot E0 FIX.SPX = getr R 2%bv).
  { rewrite Hsp. unfold FIX.SPX. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E0 _)). f_equal. cbn [edenot]. rewrite u_add64, V2, !u64_of_Z by (clear - S2 S3 SP1 CL; lia).
    rewrite Z.mod_small by (clear - S2 S3 SP1 CL; lia). clear; lia. }
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV' 4%bv ltac:(discriminate))).
  assert (REGS0 : regs_ok E0 (CC.cp_regs G.cp0) R).
  { assert (RQ : regs_ok E0 (sr_upd sr_id (ridx (2%bv : bv 5)) FIX.SPX) (regupd RSP 2%bv (getr R 2%bv))) by exact (regs_ok_upd E0 sr_id RSP 2%bv (getr R 2%bv) FIX.SPX (regs_ok_id RSP _ _) SPE).
    assert (CR : CC.cp_regs G.cp0 = sr_upd sr_id (ridx (2%bv : bv 5)) FIX.SPX) by vmc_refl. rewrite CR. intros y. pose proof (RQ y) as Ry. rewrite <- Ry.
    destruct (bv_eq_dec _ y 2%bv) as [->|Hy]; [rewrite getr_same; [reflexivity | discriminate] | rewrite (getr_other _ _ _ _ Hy); unfold RSP; rewrite (getr_other _ _ _ _ Hy); reflexivity]. }
  assert (V10 : ev E0 10 = Z_to_bv 64 v) by (rewrite <- Ha0; exact (EV' 10%bv ltac:(discriminate))).
  assert (V11 : ev E0 11 = Z_to_bv 64 o) by (rewrite <- Ha1; exact (EV' 11%bv ltac:(discriminate))).
  assert (U2 : bv_unsigned (ev E0 2) = sp - 16) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = v) by (rewrite V10; apply u64_of_Z; clear - Hvr; lia).
  assert (U11 : bv_unsigned (ev E0 11) = o) by (rewrite V11; apply u64_of_Z; clear - O3 O6; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 4864) by reflexivity.
  pose proof (CHA.ffrs_le FF sp (sp - 16) Hffrs ltac:(clear; lia)) as Hffrs16.
  assert (STKF : (sp - 16) mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp - 16 /\ sp - 16 <= ar_sptop ar) by (rewrite SCRV; split; [exact S1x | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  assert (RFr : CHA.rng_facts L ar LB FF) by exact RFx.
  set (WW := [(o, 24); (sp - 16, 16)] : list L5.range). set (Wo := WW).
  assert (WINC : incl Wo WW) by (intros y Hy; exact Hy).
  assert (WOK : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF (sp - 16) (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; [exact (CL5A.infr_wok L ar LB FF (sp - 16) _ o 24 a RFx Ofr Hin) |].
    rewrite SCRV. split; [clear - Hin S2 S3 SP1 CL; lia|]. split; [right; left; split; [clear - Hin S2 S3 SP1 CL; lia | clear - Hin; lia]|].
    intros Hs. exfalso. pose proof (CHA.shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(clear - CL; lia) ltac:(clear - SP1 S2 S3; lia) ltac:(clear; lia) Hs). clear - H Hin S2 CL. lia. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w Wo /\ L5.in_rng w a)).
  { intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha; rewrite ?U2, ?U11 in Ha; rewrite u64_of_Z in Ha by (clear; lia).
    - exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; rewrite Z.add_0_r in Ha; clear - Ha; lia].
    - exists (sp - 16, 16). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; try rewrite (Z.mod_small (sp - 16 + 0)) in Ha by (clear - S2 S3 SP1 CL; lia); clear - Ha; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF (sp - 16) G.HDECL a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U2 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
    try rewrite (Z.mod_small (sp - 16 + 0)) in Ha by (clear - S2 S3 SP1 CL; lia).
    unfold CHA.sclientA. rewrite SCRV. split; [clear - Ha S2 S3 SP1 CL; lia|]. split; [right; left; split; [clear - Ha S2 S3 SP1 CL; lia | clear - Ha; lia]|].
    intros Hs. exfalso. pose proof (CHA.shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(clear - CL; lia) ltac:(clear - SP1 S2 S3; lia) ltac:(clear; lia) Hs). clear - H Ha S2 CL. lia. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[<-|[]]] Ha; cbn [fst snd] in Ha; rewrite ILO, IHI; (split; [clear - Ha; lia|]); intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia. }
  assert (DEF0 : L5.defined M (sp - 16 - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; intros q Hq; replace (sp - 16 - 4864 + q) with (sp - 4880 + q) by (clear; lia); apply S5; clear - Hq; lia).
  assert (DEFUP : L5.defined M (sp - 16) (ar_stack_top ar - (sp - 16))).
  { intros q Hq. destruct (Z_lt_dec q 16) as [Hq16|Hq16].
    - replace (sp - 16 + q) with (sp - 4880 + (4864 + q)) by (clear; lia). apply S5. clear - Hq Hq16. lia.
    - replace (sp - 16 + q) with (sp + (q - 16)) by (clear; lia). apply S6. clear - Hq Hq16. lia. }
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[<-|[]]]; apply (L5A.aly_cells L C LAY); [left; reflexivity | right; left; reflexivity] | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (FLF := fun (E1 : env) => ar_fs ar <= CL5A.uv E1 FIX.FLE < ar_fs ar + 11571200 /\ ~ aclient L ar LB FF (sp - 16) (CH.hd_scr G.HDECL) (CL5A.uv E1 FIX.FLE)).
  set (XI := fun (i : nat) (E1 : env) (_ : list (Z * Z)) (_ : mem) (_ : Model) => (2 <= i)%nat -> FLF E1).
  assert (NOGOTO : forall i c kk ps0 j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps0 (CC.TGoto j sg) -> False).
  { intros i c kk ps0 j sg HIL. pose proof (CH2.leaves_all_sound _ _ _ FIX.leaf_ok _ _ _ _ _ HIL) as X. cbv beta iota in X. discriminate X. }

  set (i0 := if Z.ltb v (2 ^ 63) then 0%nat else 1%nat).
  assert (Hci0 : nth_error G.CPS i0 = Some (if Z.ltb v (2 ^ 63) then G.cp0 else G.cp1)) by (unfold i0; destruct (Z.ltb v (2 ^ 63)); reflexivity).
  rewrite <- LS in FPM. unfold PMSA.cfg. replace 841088 with (CC.cp_pc (if Z.ltb v (2 ^ 63) then G.cp0 else G.cp1)) by (destruct (Z.ltb v (2 ^ 63)); vm_compute; reflexivity).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW Wo G.BLS FIX.FFS Cred 2 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := i0) (E := E0).
  - exact FPM.
  - rewrite LS. exact GC.plans.
  - exact GC.tags_ok.
  - exact FIX.heap_ok.
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  -
    intros i c kl ps0 pc HIL.
    assert (Hci : nth_error G.CPS i = Some c) by (destruct HIL as (tg & Hci & _); exact Hci).
    pose proof (CH2.leaves_all_sound _ _ _ FIX.leaf_ok _ _ _ _ _ HIL) as X. unfold FIX.leaf_chk in X. cbv zeta in X.
    destruct (CH2.ret_of G.RETS i kl) as [j|] eqn:Hret.
    +
      destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X XK]. apply andb_prop in X as [X YFt]. apply andb_prop in X as [X YFj]. apply andb_prop in X as [YBi YBj].
      destruct (Z.eqb_spec pc FIX.PC_SM3) as [->|Hne0].
      *
        apply andb_prop in XK as [XK Y5]. apply andb_prop in XK as [XK YFi0]. apply andb_prop in XK as [XK YF0]. apply andb_prop in XK as [XK Yj]. apply andb_prop in XK as [Y0 Yi].
        apply Z.eqb_eq in Y0. apply Nat.leb_le in Yi. apply Nat.eqb_eq in Yj. subst j.
        lazymatch type of Y5 with match ?tm with _ => _ end = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
        apply andb_prop in Y5 as [Ynx Ycsp]. apply Nat.eqb_eq in Ynx. apply Z.eqb_eq in Ycsp.
        intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH.
        assert (HFi : nth i FIX.FFS [] = []) by (rewrite FFS_i; destruct (Nat.leb_spec i 1); [reflexivity | exfalso; clear - Yi H; lia]).
        assert (HFj : nth (59 + i) FIX.FFS [] = FIX.FRM) by (rewrite FFS_i; destruct (Nat.leb_spec (59 + i) 1); [exfalso; clear - H; lia|]; destruct (Nat.leb_spec (59 + i) 98); [reflexivity | exfalso; clear - Yi H0; lia]).
        pose proof (CRA.smalloc_leaf L ar C HI HIok LYI LYR FIX.IMGHI LYH GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW Wo G.BLS FIX.FFS Cred 2 STKF SCRP NF32 U2 V4 WINC WOK Hffrs16 CRS_OK WRS_OK IMG_OK
                      G.CPS K PMSA.fp_ok DEF0 DEFUP GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil 3 (FIX.NEWS_SM ps0 cj) i c ps0 (59 + i)%nat cj ci) as SML.
        rewrite (L5A.aly_scr_sm L C LAY), (L5A.aly_sm3 L C LAY) in SML.
        refine (SML ltac:(do 3 right; left; reflexivity) Hcj ltac:(rewrite HFi, HFj, !BLS_i; exact Hchk) Y0 _ _ _ _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _).
        -- rewrite Ynx, Ycsp, HFi, HFj. reflexivity.
        -- rewrite !BLS_i. reflexivity.
        -- apply forallb_forall. intros X0 HX0. unfold FIX.NEWS_SM in HX0. apply filter_In in HX0 as [_ HX0]. unfold FIX.sm_ok in HX0. rewrite Ynx, HFi, BLS_i. exact HX0.
        -- rewrite HFi. cbn; clear; lia.
        -- intros Ea Eb cr1 Hc _. exact Hc.
        --
           intros R2 M2 m2 F fl LK' cr1 HRP Ha0' SMF HH2. unfold CHA.curB, CHA.curF in SMF. rewrite BLS_i, HFi in SMF. cbn [Nat.eqb CH2.den CHA.denF map app] in SMF.
           destruct SMF as [Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Zp]. rewrite Ynx.
           pose proof (CH2.retEx_ghost E' 40 [Z_to_bv 64 fl] R2 0 ltac:(cbn; clear; lia)) as G40. cbn [nth Nat.add] in G40.
           set (E2 := CH2.retEx E' 40 [Z_to_bv 64 fl] R2) in *.
           destruct (CHA.rf_fs _ _ _ _ RFx) as ((FS0 & FS1 & FS2) & FS3 & _). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in Z7, FS0, FS1, FS2, FS3.
           assert (T40 : CL5A.uv E2 FIX.FLE = fl) by (unfold CL5A.uv, FIX.FLE; cbn [edenot]; rewrite G40; apply u64_of_Z; clear - Z7 FS0 FS3 CL SP1; lia).
           unfold XI, FLF. intros _. rewrite T40. split; [exact Z7|].
           intros Hc. apply Z8. eapply CHA.aclient_scr; [eapply CHA.aclient_incl; [apply incl_refl | apply incl_tl, incl_refl | exact Hc] | intros y Hy; clear - Hy; lia].
      * destruct (Z.eqb_spec pc FIX.PC_SETSH) as [->|Hne1]; [|discriminate XK].

        apply andb_prop in XK as [XK Yfl]. apply andb_prop in XK as [XK Y11]. apply andb_prop in XK as [XK Y10]. apply andb_prop in XK as [XK Y5].
        apply andb_prop in XK as [XK Ynx46]. apply andb_prop in XK as [XK YFX]. apply andb_prop in XK as [XK YFi]. apply andb_prop in XK as [XK Yj].
        apply andb_prop in XK as [XK Yi2]. apply andb_prop in XK as [Y0 Yi1].
        apply Z.eqb_eq in Y0. apply Nat.leb_le in Yi1, Yi2, Ynx46. apply Nat.eqb_eq in Yj. subst j.
        lazymatch type of Y5 with match ?tm with _ => _ end = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
        apply andb_prop in Y5 as [Ycsp Ynxc]. apply Z.eqb_eq in Ycsp. apply Nat.leb_le in Ynxc.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        assert (HFi : nth i FIX.FFS [] = FIX.FRM).
        { rewrite FFS_i. destruct (Nat.leb_spec i 1) as [He|_]; [exfalso; clear - He Yi1; lia|]. destruct (Nat.leb_spec i 98) as [_|Hgt]; [reflexivity | exfalso; clear - Yi2 Hgt; lia]. }
        assert (HFj : nth (i + 40) FIX.FFS [] = FIX.FRM).
        { rewrite FFS_i. destruct (Nat.leb_spec (i + 40) 1) as [He|_]; [exfalso; clear - He; lia|]. destruct (Nat.leb_spec (i + 40) 98) as [_|Hgt]; [reflexivity | exfalso; clear - Yi2 Hgt; lia]. }
        assert (HBi : nth i G.BLS [] = []) by apply BLS_i. assert (HBj : nth (i + 40) G.BLS [] = []) by apply BLS_i.
        assert (XF : FLF E) by (apply HXi; clear - Yi1; lia). destruct XF as (L1 & L2).
        assert (V40 : CL5A.uv E' FIX.FLE = CL5A.uv E FIX.FLE) by (unfold CL5A.uv, FIX.FLE; cbn [edenot]; rewrite <- (proj1 Hag 40%nat) by (clear - Ynx46; lia); reflexivity).
        refine (CRSH2.setsh_leaf L ar C HI HIok LYI LYR LYB GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW Wo G.BLS FIX.FFS Cred 2 STKF SCRP NF32 U2 V4 WINC WOK Hffrs16 CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 DEFUP GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil
                  FIX.PC_SETSH 245 256 SETSH 256 (FIX.STAT ++ FIX.FLAGN) i c ps0 (i + 40)%nat cj ci FIX.FE 3 (-128) FIX.FLE (EAlu Instr.ALU_ADD (CHA.SRL3 FIX.FE) (ELit FIX.SBz))
                  Hcj _ Y0 ltac:(clear; lia) HFi _ _ ltac:(clear; lia) Y10 _ Y11 _ Yfl (le_n _) _
                  fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _ _ _).
        -- rewrite HFi, HFj, HBi, HBj. exact Hchk.
        -- rewrite HFi, HFj. reflexivity.
        -- rewrite HBi, HBj. reflexivity.
        -- intros Ex. unfold CL5A.uv. cbn [edenot]. rewrite AX2S.u_add64. unfold CHA.SRL3. rewrite (CL5A.elen_srl3' Ex FIX.FE : bv_unsigned (edenot Ex (EAlu Instr.ALU_SRL FIX.FE (ELit 3))) = CL5A.uv Ex FIX.FE / 8).
           unfold FIX.SBz, SB. rewrite u64_of_Z by (clear; lia). pose proof (CL5A.uv_range Ex FIX.FE) as UR. unfold CL5A.uv in UR |- *.
           apply Z.mod_small. split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; clear - UR; lia | clear; lia]|]. pose proof (CL5A.div8_le _ _ (proj2 (conj (proj1 UR) (Z.lt_le_incl _ _ (proj2 UR))))) as D8.
           change (2 ^ 64 / 8) with 2305843009213693952 in D8. clear - D8. lia.
        -- intros X0 HX0. unfold FIX.STAT, FIX.FLAGN in HX0. cbn [In app] in HX0. destruct HX0 as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [left; reflexivity | left; reflexivity | left; reflexivity | right; left; reflexivity | right; right; reflexivity].
        -- intros Ea Eb crx Hc _. exact Hc.
        -- rewrite V40. unfold FS_BYTES. exact L1.
        -- intros Ea Eb Hg. unfold CL5A.uv, FIX.FLE. cbn [edenot]. rewrite (proj1 Hg 40%nat) by (clear - Ynx46; lia). reflexivity.
        -- cbv zeta. intros R2 M2 m2 A2 LK2 crx HRP HP1 HP3 HPOI HA2 Hmo2 Hrt2 HH2.
           unfold XI, FLF. intros _.
           assert (VV : CL5A.uv (CH2.retEx E' (CH2.ci_nx ci) [] R2) FIX.FLE = CL5A.uv E FIX.FLE).
           { rewrite <- V40. unfold CL5A.uv, FIX.FLE. cbn [edenot]. rewrite <- (proj1 (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2) 40%nat) by (clear - Ynx46 Ynxc; lia). reflexivity. }
           rewrite VV. exact (conj L1 L2).
    + destruct (Z.eqb_spec pc FIX.REENT) as [->|Hne].
      *
        set (cc := FIX.RC ps0) in *. set (jj := if Nat.eqb i 59 then (20 + cc)%nat else (39 + cc)%nat) in *.
        destruct (nth_error G.CPS jj) as [cj|] eqn:Hcj; [|discriminate].
        apply andb_prop in X as [X Ysrc]. apply andb_prop in X as [X YKR]. apply andb_prop in X as [X YKA]. apply andb_prop in X as [X Ygc]. apply andb_prop in X as [X Yre].
        apply andb_prop in X as [X Ymj]. apply andb_prop in X as [X Ycom]. apply andb_prop in X as [X Ypcj].
        apply andb_prop in X as [X Yc2]. apply andb_prop in X as [X Yc1]. apply andb_prop in X as [Y0 Ysrci].
        apply Z.eqb_eq in Y0, Ypcj. apply Nat.leb_le in Yc1, Yc2. apply expr_eqb_eq in Ymj.
        unfold FIX.common_re in Ycom. apply andb_prop in Ycom as [Ycom Ymc]. apply andb_prop in Ycom as [Ycom Ynx46]. apply Nat.leb_le in Ynx46. apply expr_eqb_eq in Ymc.
        assert (Hsrc : (i = 59 \/ 2 <= i <= 20)%nat).
        { apply orb_prop in Ysrci as [Y|Y]; [left; apply Nat.eqb_eq in Y; exact Y | right]. apply andb_prop in Y as [Y _]. apply andb_prop in Y as [Y1 Y2]. apply Nat.leb_le in Y1, Y2. lia. }
        assert (HMS : 262144 < FIX.meas_src i <= 1048575).
        { clear - Hsrc. unfold FIX.meas_src. destruct Hsrc as [->|Hi]; [cbn; lia | destruct (Nat.eqb_spec i 59); [lia|]; destruct (Nat.eqb_spec i 60); [lia|]; lia]. }
        refine (FIK.reentry_leaf_u L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW Wo G.BLS FIX.FFS Cred 2 STKF SCRP NF32 U2 WINC WOK WRS_OK
                  G.CPS K PMSA.fp_ok XI i c ps0 jj cj (FIX.mk_sR cc ps0) (FIX.RESP cc) Hcj ltac:(rewrite Y0, Ypcj; reflexivity) Yre Ygc _ _).
        -- intros E1 E' R1 R' A1 M1 m1 M' m' HAt HA HXi Hag HLF.
           assert (XF : FLF E1) by (apply HXi; destruct Hsrc as [->|Hi]; lia). destruct XF as (L1 & L2).
           assert (SV : forall v0, (v0 = 40 \/ v0 = 45)%nat -> CL5A.uv (CC.env_over GT.NF (FIX.mk_sR cc ps0) E') (EVar v0) = CL5A.uv E1 (EVar v0)).
           { intros v0 Hv0. unfold CL5A.uv. cbn [edenot CC.env_over ev]. unfold FIX.mk_sR, FIX.FLE, FIX.FE. destruct Hv0 as [->| ->]; cbn [Nat.ltb Nat.leb GT.NF CC.slook app Nat.eqb edenot];
               (rewrite <- (proj1 Hag _) by (clear - Ynx46; lia); reflexivity). }
           split; [unfold XI, FLF, FIX.FLE; intros _; rewrite (SV 40%nat ltac:(left; reflexivity)); exact (conj L1 L2)|].
           split; [unfold CC.meas; rewrite Ymc, Ymj; cbn [edenot]; rewrite !u64_of_Z by (clear - HMS; lia); clear - HMS; lia|].
           intros X0 HX0. unfold FIX.RESP in HX0. apply in_map_iff in HX0 as (ii & <- & Hii). apply in_seq in Hii.
           unfold FIX.resp_src in Ysrc. rewrite forallb_forall in Ysrc. specialize (Ysrc ii ltac:(apply in_seq; exact Hii)).
           pose proof (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ (CC.has_cell_In _ _ Ysrc)) as KC.
           pose proof (proj1 (Forall_forall _ _) (proj2 HAt) _ (CC.has_cell_In _ _ YKA)) as KAL. cbn [kentry_ok] in KAL. destruct KAL as (_ & KAL).
           pose proof (proj1 (Forall_forall _ _) (proj2 HAt) _ (CC.has_cell_In _ _ YKR)) as KRG. cbn [kentry_ok] in KRG.
           change (bv_unsigned (edenot E1 FIX.FE)) with (CL5A.uv E1 FIX.FE) in KAL, KRG.
           assert (V45 : CL5A.uv E' FIX.FE = CL5A.uv E1 FIX.FE) by (unfold CL5A.uv, FIX.FE; cbn [edenot]; rewrite <- (proj1 Hag 45%nat) by (clear - Ynx46; lia); reflexivity).
           assert (F8 : CL5A.uv E1 FIX.FE mod 8 = 0) by (apply CHA.mod8_of_64; exact KAL).
           unfold FIX.RESPK.
           refine (FIK.resp_ok (hl_segs L) (hl_img_hi L) _ _ E' FIX.FE (31 + Z.of_nat ii) (CL5A.uv E1 FIX.FE) LYB ltac:(rewrite IHI; unfold SB; clear; lia)
                     (SV 45%nat ltac:(right; reflexivity)) V45 F8 ltac:(clear - KRG; lia) ltac:(clear - KRG Hii Yc2; lia) ltac:(clear; lia) KC).
        -- intros Ea Eb R0 Ma Mb cr1 _ _ _ Hc. exact Hc.
      * destruct (Z.eqb_spec pc FIX.NLOOP) as [->|Hne2].
        --
           set (kk := FIX.RC ps0) in *.
           destruct (nth_error G.CPS (2 + kk)) as [cj|] eqn:Hcj; [|discriminate].
           apply andb_prop in X as [X Yq]. apply andb_prop in X as [X Ygc]. apply andb_prop in X as [X Yre].
           apply andb_prop in X as [X Ymj]. apply andb_prop in X as [X Ycom]. apply andb_prop in X as [X Ypcj].
           apply andb_prop in X as [X Yk2]. apply andb_prop in X as [Y0 Ysrci].
           apply Z.eqb_eq in Y0, Ypcj. apply Nat.leb_le in Yk2. apply expr_eqb_eq in Ymj.
           unfold FIX.common_re in Ycom. apply andb_prop in Ycom as [Ycom Ymc]. apply andb_prop in Ycom as [Ycom Ynx46]. apply Nat.leb_le in Ynx46. apply expr_eqb_eq in Ymc.
           assert (Hsrc : (i = 60 /\ kk = 0 \/ 2 <= i <= 19 /\ kk = i - 1)%nat).
           { apply orb_prop in Ysrci as [Y|Y]; [left; apply andb_prop in Y as [Y1 Y2]; apply Nat.eqb_eq in Y1, Y2; lia | right].
             apply andb_prop in Y as [Y Y3]. apply andb_prop in Y as [Y1 Y2]. apply Nat.leb_le in Y1, Y2. apply Nat.eqb_eq in Y3. lia. }
           refine (FIK.reentry_leaf_u L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW Wo G.BLS FIX.FFS Cred 2 STKF SCRP NF32 U2 WINC WOK WRS_OK
                     G.CPS K PMSA.fp_ok XI i c ps0 (2 + kk)%nat cj (FIX.mk_sN kk ps0) (FIX.UQ kk) Hcj ltac:(rewrite Y0, Ypcj; reflexivity) Yre Ygc _ _).
           ++ intros E1 E' R1 R' A1 M1 m1 M' m' HAt HA HXi Hag HLF.
              assert (XF : FLF E1) by (apply HXi; destruct Hsrc as [(-> & _)|(Hi & _)]; lia). destruct XF as (L1 & L2).
              assert (SV : forall v0, (v0 = 40 \/ v0 = 45)%nat -> CL5A.uv (CC.env_over GT.NF (FIX.mk_sN kk ps0) E') (EVar v0) = CL5A.uv E1 (EVar v0)).
              { intros v0 Hv0. unfold CL5A.uv. cbn [edenot CC.env_over ev]. unfold FIX.mk_sN, FIX.FLE, FIX.FE. destruct Hv0 as [->| ->]; cbn [Nat.ltb Nat.leb GT.NF CC.slook app Nat.eqb edenot];
                  (rewrite <- (proj1 Hag _) by (clear - Ynx46; lia); reflexivity). }
              split; [unfold XI, FLF, FIX.FLE; intros _; rewrite (SV 40%nat ltac:(left; reflexivity)); exact (conj L1 L2)|].
              assert (HMN : 524288 - Z.of_nat kk < FIX.meas_src i <= 1048575 /\ 0 <= 524288 - Z.of_nat kk).
              { clear - Hsrc Yk2. unfold FIX.meas_src. destruct Hsrc as [(-> & ->)|(Hi & Hk)]; [cbn; lia|].
                destruct (Nat.eqb_spec i 59); [lia|]; destruct (Nat.eqb_spec i 60); [lia|]; lia. }
              split; [unfold CC.meas; rewrite Ymc, Ymj; cbn [edenot]; rewrite !u64_of_Z by (clear - HMN; lia); clear - HMN; lia|].
              pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
              destruct (Nat.eqb_spec kk 0) as [Hk0|Hk0].
              **
                 pose proof (CC.lf_cells _ _ _ _ _ _ _ HLFv _ (CC.has_cell_In _ _ Yq)) as KU.
                 assert (V45 : CL5A.uv (CC.env_over GT.NF (FIX.mk_sN kk ps0) E') FIX.FE = CL5A.uv E' FIX.FE).
                 { change FIX.FE with (EVar 45). rewrite (SV 45%nat ltac:(right; reflexivity)). unfold CL5A.uv. cbn [edenot]. rewrite <- (proj1 Hag 45%nat) by (clear - Ynx46; lia). reflexivity. }
                 rewrite Hk0 in V45 |- *. unfold FIX.UQ, FIX.KU0. cbn [Nat.eqb].
                 intros X0 [<-|[<-|[]]].
                 --- exact (FIK.kunk_sub (hl_segs L) _ E' _ FIX.FE 24 488 24 8 V45 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) KU).
                 --- exact (FIK.kunk_sub (hl_segs L) _ E' _ FIX.FE 24 488 32 480 V45 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) KU).
              **
                 apply Nat.eqb_neq in Hk0.
                 apply andb_prop in Yq as [Yq Ynx69]. apply andb_prop in Yq as [Yq Ylo]. apply andb_prop in Yq as [Yq YKQ]. apply andb_prop in Yq as [YQX YQF].
                 apply Nat.leb_le in Ynx69. apply Z.eqb_eq in Ylo.
                 unfold FIX.UQ. rewrite Hk0. cbn [Nat.eqb]. intros X0 [<-|[]].
                 pose proof (proj1 (Forall_forall _ _) (proj2 HAt) _ (CC.has_cell_In _ _ YKQ)) as KQ. unfold FIX.QE in KQ. cbn [kentry_ok edenot] in KQ.
                 pose proof (CC.lf_cells _ _ _ _ _ _ _ HLFv _ (CC.has_cell_In _ _ YQF)) as KF. unfold FIX.QFACT, FIX.QE in KF. cbn [kentry_ok edenot] in KF.
                 assert (W68 : ev E' 68 = ev E1 68) by (rewrite <- (proj1 Hag 68%nat) by (clear - Ynx69; lia); reflexivity).
                 rewrite W68 in KF.
                 set (x := bv_unsigned (ev E1 68)) in *.
                 assert (NLO : 2 ^ 63 <= FIX.nlo (kk - 1)).
                 { clear. unfold FIX.nlo. assert (P : 0 < 10 ^ Z.of_nat (kk - 1)) by (apply Z.pow_pos_nonneg; lia).
                   pose proof (Z.div_le_compat_l (2 ^ 63) 1 (10 ^ Z.of_nat (kk - 1)) ltac:(lia) ltac:(lia)) as D. rewrite Z.div_1_r in D. lia. }
                 assert (XLE : x <= 2 ^ 64 - 10).
                 { unfold alu64, alu in KF.
                   assert (UA : bv_unsigned (ev E1 68 + Z_to_bv 64 (-10)) = x - 10)
                     by (rewrite bv_add_unsigned, Z_to_bv_unsigned; fold x; unfold bv_wrap, bv_modulus; cbn -[Z.pow]; rewrite Z.add_mod_idemp_r by (clear; lia); rewrite Z.mod_small by (clear - KQ NLO; lia); clear; lia).
                   destruct (bv_ltu (Z_to_bv 64 18446744073709551596) (ev E1 68 + Z_to_bv 64 (-10))) eqn:LT; [rewrite u64_of_Z in KF by (clear; lia); clear - KF; lia|].
                   unfold bv_ltu in LT. apply Z.ltb_ge in LT. rewrite UA, u64_of_Z in LT by (clear; lia). clear - LT KQ NLO; lia. }
                 assert (XB : FIX.nlo (kk - 1) <= x <= 2 ^ 64 - 1) by exact KQ.
                 assert (VQ : bv_unsigned (edenot E' (FIK.reg_val (SR.ps_regs ps0) 15)) = 2 ^ 64 - (2 ^ 64 - x) / 10).
                 { apply orb_prop in YQX as [YQX|YQX]; apply expr_eqb_eq in YQX; rewrite YQX; unfold FIX.QX, FIX.QX1, FIX.MAGIC, FIX.QE; cbn [edenot]; rewrite W68.
                   - exact (FIK.q_den (ev E1 68) ltac:(fold x; clear - XLE XB NLO; lia)).
                   - exact (FIK.q_den1 (ev E1 68) ltac:(fold x; clear - XLE XB NLO; lia)). }
                 unfold FIX.QE. cbn [kentry_ok edenot CC.env_over ev]. change (Nat.ltb 68 GT.NF) with false. cbn iota.
                 replace (CC.slook (FIX.mk_sN kk ps0) 68) with (FIK.reg_val (SR.ps_regs ps0) 15) by (unfold FIX.mk_sN, FIX.HVN; cbn [CC.slook app map combine seq fst snd Nat.add Nat.eqb]; reflexivity).
                 rewrite VQ, Ylo.
                 pose proof (Z.div_le_mono (2 ^ 64 - x) (2 ^ 64 - FIX.nlo (kk - 1)) 10 ltac:(clear; lia) ltac:(clear - XB; lia)) as D1.
                 pose proof (Z.div_le_lower_bound (2 ^ 64 - x) 10 1 ltac:(clear; lia) ltac:(clear - XLE; lia)) as D2. clear - D1 D2. lia.
           ++ intros Ea Eb R0 Ma Mb cr1 _ _ _ Hc. exact Hc.
        --
        apply andb_prop in X as [X Ysh]. apply andb_prop in X as [X Ynx46]. apply andb_prop in X as [X Yfl]. apply andb_prop in X as [X Yr]. apply andb_prop in X as [X YFi].
        apply andb_prop in X as [X YBi]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Yi2]. apply andb_prop in X as [X Yi1]. apply andb_prop in X as [Ypc Xbase].
        apply Z.eqb_eq in Ypc. subst pc. apply Nat.leb_le in Yi1, Yi2, Ynx46. apply CBA.regions_eqb_eq in YF.
        assert (HFi : nth i FIX.FFS [] = [(FIX.FE, 3, -128)]).
        { rewrite FFS_i. destruct (Nat.leb_spec i 1) as [He|_]; [exfalso; clear - He Yi1; lia|]. destruct (Nat.leb_spec i 98) as [_|Hgt]; [reflexivity | exfalso; clear - Yi2 Hgt; lia]. }
        destruct (CHA.retire_chk GT.NF G.HDECL c [] FIX.FRM) as [fle|] eqn:Hrc; [|discriminate]. apply expr_eqb_eq in Yr. subst fle.
        intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
        assert (XF : FLF E1) by (apply HXi; clear - Yi1; lia). destruct XF as (HFL1 & HFL2).
        refine (CBB.exit_retire_sp L ar C HI HIok LYI LYB LYN GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW Wo G.BLS FIX.FFS Cred 2 STKF SCRP NF32 U2 WINC WOK WRS_OK
                  K DEF0 R r FIX.SPX FIX.RETPC i c ps0 FIX.FLE FIX.FE 3 (-128) EVN Hra Hraok SPE _ Xbase HFi ltac:(rewrite BLS_i, HFi; exact Hrc) Yfl fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF HFL1 HFL2 _);
          [rewrite LS; exact FIX.ret_at |].
        intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE'. unfold CHA.curB in HH1. rewrite BLS_i in HH1. cbn [CH2.den map app] in HH1. unfold Cred in HC1. subst cr1.

        assert (AHM : CHA.ahpres L ar LB FF sp 4880 [(o, 24)] M M').
        { pose proof HP as (HP1 & HP2 & HP3). rewrite SCRV in HP1, HP2, HP3.
          assert (WINX : forall a, aclient L ar LB FF sp 4880 a -> ~ (sp - 16 <= a < sp)).
          { intros a Hc Ha. apply (CHA.client_high L ar LYI GT.NF (sp - 16) G.HDECL STKF SCRP NF32 LB FF sp 4880 a RFx Hc); [clear - Ha S2; lia | clear - Ha; lia]. }
          assert (SCRX : forall a, aclient L ar LB FF sp 4880 a -> aclient L ar LB FF (sp - 16) 4864 a).
          { intros a Hc. apply (CHA.aclient_scr _ _ L ar LB FF sp 4880 (sp - 16) 4864 a Hc). intros x Hx. clear - Hx. lia. }
          split; [|split].
          - intros a (Ha & Hcl & Ho). apply HP1. split; [exact Ha|]. split; [exact (SCRX a Hcl)|].
            intros w Hw Hin. destruct Hw as [<-|[<-|[]]]; [exact (Ho _ (or_introl eq_refl) Hin)|]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (WINX a Hcl ltac:(clear - Hin; lia)).
          - intros q Hq. destruct (Z_lt_dec q 4864) as [Hlt|Hge].
            + replace (sp - 4880 + q) with (sp - 16 - 4864 + q) by (clear; lia). apply HP2. clear - Hq Hlt. lia.
            + apply (HP3 (sp - 4880 + q)); [clear - Hq S2 S3 SP1 CL; lia | right; left; split; [clear - Hq Hge S2 S3 SP1 CL; lia | clear - Hq Hge; lia] | apply S5; exact Hq].
          - intros a Ha Hcl Hd. apply (HP3 a Ha); [exact (SCRX a Hcl) | exact Hd]. }
        apply (Hcont fx' R' M' model2 LB cr LB [(o, 24)] LK1 A1 HFP); [| exact HRP | exact AHM | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].

        set (cc := FIX.nchars i) in *. set (cells := SR.ps_cells ps0) in *.
        assert (Hcc : (1 <= cc <= 20)%nat) by (clear - Yi1 Yi2; unfold cc, FIX.nchars; destruct (Nat.leb_spec i 79); lia).
        unfold FIX.exit_shape in Ysh. fold cells in Ysh. apply andb_prop in Ysh as [Ysh Ynul]. apply andb_prop in Ysh as [Ysh Ydig]. apply andb_prop in Ysh as [Ya0 Ysz].
        pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
        assert (Hoff : H_off_segments (hl_segs L) (ahid A1 m')).
        { rewrite (L5LZ.sbm_ahid A1 m1 m' (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)). exact (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW G.BLS FIX.FFS Cred 2 i E1 A1 M1 m1 HA). }
        assert (CELL : forall X0, FIX.has cells X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0) by (intros X0 HX0; exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ (CC.has_cell_In _ _ HX0))).
        assert (W11 : CL5A.uv E' FIX.OE = o) by (unfold CL5A.uv, FIX.OE; cbn [edenot]; rewrite <- (proj1 HagE' 11%nat) by (unfold GT.NF; clear; lia); exact U11).
        assert (RD8 : forall k e, FIX.has cells (KWord (SA FIX.OE k) 1 e) = true -> 0 <= k < 24 -> L5.u8_at (hl_segs L) M' (o + k) (CL5A.uv E' e)).
        { intros k e Hh Hk. apply (CL5A.u8_full (hl_segs L) _ Hoff). apply (CL5A.kword8_elim (hl_segs L) E' _ _ _ (o + k) (CELL _ Hh)). unfold estart. cbn [a_base a_off].
          change (bv_unsigned (edenot E' FIX.OE)) with (CL5A.uv E' FIX.OE). rewrite W11. reflexivity. }
        exists (map (fun k => CL5A.uv E' (FIK.cell_val cells FIX.OE (1 + Z.of_nat k) 1)) (seq 0 cc)).
        rewrite length_map, length_seq.
        split; [clear - Hcc; lia|].
        split.
        { unfold PMLA.str_at, L5.lstr_short. rewrite length_map, length_seq.
          split; [clear - Hcc; lia|].
          split; [pose proof (RD8 0 _ Ysz ltac:(clear; lia)) as U; rewrite Z.add_0_r in U; replace (CL5A.uv E' (ELit (2 * Z.of_nat cc))) with (2 * Z.of_nat cc) in U
                    by (unfold CL5A.uv; cbn [edenot]; rewrite u64_of_Z by (clear - Hcc; lia); reflexivity); exact U|].
          split.
          - intros k Hk. rewrite length_map, length_seq in Hk. rewrite forallb_forall in Ydig. specialize (Ydig k ltac:(apply in_seq; clear - Hk; lia)).
            rewrite (nth_map_seq (fun k0 => CL5A.uv E' (FIK.cell_val cells FIX.OE (1 + Z.of_nat k0) 1)) cc k 0 Hk). cbv beta.
            pose proof (RD8 (1 + Z.of_nat k) _ Ydig ltac:(clear - Hk Hcc; lia)) as U.
            replace (o + 1 + Z.of_nat k) with (o + (1 + Z.of_nat k)) by (clear; lia). exact U.
          - pose proof (RD8 (1 + Z.of_nat cc) _ Ynul ltac:(clear - Hcc; lia)) as U.
            replace (CL5A.uv E' (ELit 0)) with 0 in U by (unfold CL5A.uv; cbn [edenot]; rewrite u64_of_Z by (clear; lia); reflexivity).
            replace (o + 1 + Z.of_nat cc) with (o + (1 + Z.of_nat cc)) by (clear; lia). exact U. }
        split.
        { unfold PMSA.a0. pose proof (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ 10 _ HLFv Ya0) as RA0. replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RA0. reflexivity. }
        repeat split; reflexivity.
  - exact Hci0.
  -
    assert (CLV : forall scr a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros scr a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp scr a HH Ha Hc Hs)).
    assert (VO : CL5A.visr (ahid A model) o 24).
    { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + k) RFx Ofr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VOS : forall j, 0 <= j < 3 -> ahid A model (Z_to_bv 64 (S o + j)) = false).
    { intros j Hj.
      destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o 24 (S o + j) RFx Ofr ltac:(clear; lia) (CL5A.shreg_in_shadow o 3 (S o + j) O8 ltac:(clear - Hj; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
      exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4880) 4880).
    { intros k Hk. apply (CLV 0); [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DS : L5.defined Mv (sp - 4880) 4880) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (DO : L5.defined Mv o 24) by (apply (CL5A.defined_vis _ M _ _ VO); exact Hdef).
    destruct Hstr as (_ & Hu0 & _ & _).
    assert (COMMON : Forall (kentry_ok (hl_segs L) E0 Mv) (firstn 18 (CC.cp_know G.cp0))).
    { let l := eval vm_compute in (firstn 18 (CC.cp_know G.cp0)) in change (firstn 18 (CC.cp_know G.cp0)) with l.
      repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + cbn [kentry_ok]. split; [clear; lia|]. split; [clear; lia|]. intros q Hq. unfold Mv, CCA.vis, mrestrict. destruct (ahid A model (Z_to_bv 64 q)); [reflexivity|].
      apply Hro. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_casan]. clear - Hq. lia.
    + eapply CL5A.kword8_intro with (A := o) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | clear; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 o 1 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hu0].
    + eapply CL5.kunk_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.kwr_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO S2 S3 SP1; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact O8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 3 o); [exact U11 | clear; lia | clear - O3 O6; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VOS j Hj) | exact (Osh j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 24); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.kunk_intro with (A := sp - 4880) (N := 4864); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | intros q Hq; apply DS; clear - Hq; lia].
    + eapply CL5.kunk_intro with (A := sp - 16) (N := 16); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | intros q Hq; replace (sp - 16 + q) with (sp - 4880 + (4864 + q)) by (clear; lia); apply DS; clear - Hq; lia].
    + eapply CL5.kwr_intro with (A := sp - 4880) (N := 4864); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | intros q Hq; apply DS; clear - Hq; lia].
    + eapply CL5.kwr_intro with (A := sp - 16) (N := 16); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | intros q Hq; replace (sp - 16 + q) with (sp - 4880 + (4864 + q)) by (clear; lia); apply DS; clear - Hq; lia].
    + eapply CL5.krange_intro with (v := sp - 16); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp - 16); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact Hsp16].
    + eapply CL5.kdisj_intro with (A1 := sp - 4880) (N1 := 4880) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia]. }
    assert (K01 : firstn 18 (CC.cp_know G.cp1) = firstn 18 (CC.cp_know G.cp0) /\ CC.cp_regs G.cp1 = CC.cp_regs G.cp0) by (vm_compute; split; reflexivity).
    assert (SK0 : skipn 18 (CC.cp_know G.cp0) = [KRange (EVar 10) 0 (2 ^ 63 - 1)]) by vmc_refl.
    assert (SK1 : skipn 18 (CC.cp_know G.cp1) = [KRange (EVar 10) (2 ^ 63) (2 ^ 64 - 1)]) by vmc_refl.
    destruct (Z.ltb_spec v (2 ^ 63)) as [Hlt|Hge].
    + split; [exact REGS0|]. unfold know_ok. rewrite <- (firstn_skipn 18 (CC.cp_know G.cp0)), SK0. apply Forall_app. split; [exact COMMON|].
      apply Forall_cons; [|apply Forall_nil]. eapply CL5.krange_intro with (v := v); [lin_eval; rw_atoms; clear; lia | clear - Hvr; lia | clear - Hvr Hlt; lia].
    + split; [destruct K01 as [_ ->]; exact REGS0|]. unfold know_ok. rewrite <- (firstn_skipn 18 (CC.cp_know G.cp1)), SK1, (proj1 K01). apply Forall_app. split; [exact COMMON|].
      apply Forall_cons; [|apply Forall_nil]. eapply CL5.krange_intro with (v := v); [lin_eval; rw_atoms; clear; lia | clear - Hvr; lia | clear - Hvr Hge; lia].
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      assert (HI0 : (i0 <= 1)%nat) by (unfold i0; destruct (Z.ltb v (2 ^ 63)); lia).
      exists cr, LK. unfold CHA.curB, CHA.curF. rewrite BLS_i, FFS_i. destruct (Nat.leb_spec i0 1) as [_|HG]; [|exfalso; lia]. cbn [Nat.eqb CH2.den CHA.denF map app length Z.of_nat Z.sub].
      split; [exact HH|]. split; [apply incl_refl|]. split; [unfold Cred; reflexivity | replace (2 - 0) with 2 by (clear; lia); exact Hroom].
    + unfold XI. intros H0. exfalso. unfold i0 in H0. destruct (Z.ltb v (2 ^ 63)); lia.
  - exact Hfp.
Qed.
End FromIntOk.
