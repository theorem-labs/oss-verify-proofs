(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import TopKitCB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_strinit_cboth_T Cut_strinit_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_strinit_cboth.
Module GT := Cut_strinit_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module SIA.
Definition PC_OPNEW : Z := 1363704.
Definition PC_AMEMMOVE : Z := 522512.
Definition RETPC : Z := 720384.
Definition SBz : Z := 2147450880.
Definition oE := EVar 10. Definition srcE := EVar 11. Definition nE := EVar 12. Definition nsE := EVar 32. Definition nbE := EVar 44.
Definition IA (k : Z) : expr := EAlu Instr.ALU_ADD oE (ELit k).
Definition R8 : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EAlu Instr.ALU_SRL nE (ELit 3))) (ELit 8).
Definition R9 : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EAlu Instr.ALU_SRL nE (ELit 3))) (ELit 9).
Definition SZ (ch : nat) : expr := match ch with 2%nat => ELit 26 | _ => R8 end.
Definition BLK (ch : nat) : list (expr * expr) := [(nbE, SZ ch)].

Definition chain (i : nat) : nat := match i with 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 2 | _ => 3 end%nat.
Definition stage (i : nat) : nat := match i with 4 => 2 | 5 => 1 | 6 => 1 | 7 => 2 | 8 => 2 | _ => 0 end%nat.
Definition BLKS (i : nat) : list (expr * expr) := if (i <=? 4)%nat then [] else BLK (chain i).
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz)].

Definition DST (ch : nat) : expr := match ch with 1%nat => IA 1 | _ => nbE end.
Definition NARG (ch : nat) : expr := match ch with 1%nat => nsE | 2%nat => ELit 23 | _ => nE end.
Definition TERM (ch : nat) : expr := match ch with 1%nat => EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD oE nsE) (ELit 1) | 2%nat => EAlu Instr.ALU_ADD nbE (ELit 23) | _ => EAlu Instr.ALU_ADD nE nbE end.
Definition NEWS_MM (ch : nat) : list kentry := STAT ++ [KZero (SA (CHA.SRL3 (TERM ch)) SBz) (ELit 1)].
Definition FEX (ch : nat) : list SGP.region := [(EVar 2, -4176, ELit 4176); match ch with 1%nat => (TERM 1%nat, 0, ELit 1) | 2%nat => (nbE, 23, ELit 1) | _ => (TERM 3%nat, 0, ELit 1) end].
Definition news_of (nb : nat) (cj : CC.cutpoint) : list kentry := List.filter (fun X => negb (APC.kentry_vars_lt nb X)) (CC.cp_know cj).
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition exit_cells (ch : nat) (cells : list kentry) : bool :=
  match ch with
  | 0%nat => has cells (KWord (SA oE 0) 1 (ELit 0)) && has cells (KWord (SA oE 1) 1 (ELit 0))
  | 1%nat => has cells (KWord (SA oE 0) 1 (EMd Instr.M_MUL (ELit 2) nsE)) && has cells (KWord (SA (EAlu Instr.ALU_ADD oE nsE) 1) 1 (ELit 0))
  | 2%nat => has cells (KWord (SA oE 0) 8 (ELit 27)) && has cells (KWord (SA oE 8) 8 (ELit 23)) && has cells (KWord (SA oE 16) 8 nbE) && has cells (KWord (SA nbE 23) 1 (ELit 0))
  | _ => has cells (KWord (SA oE 0) 8 R9) && has cells (KWord (SA oE 8) 8 nE) && has cells (KWord (SA oE 16) 8 nbE) && has cells (KWord (SA (EAlu Instr.ALU_ADD nE nbE) 0) 1 (ELit 0))
  end%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      match CH2.ret_of G.RETS i k with
      | Some j =>
          match nth_error G.CPS j with
          | Some cj =>
              (Nat.eqb (chain j) (chain i) && CH2.blocks_eqb (nth i G.BLS []) (BLKS i) && CH2.blocks_eqb (nth j G.BLS []) (BLKS j) &&
              if Z.eqb pc PC_OPNEW then
                let nx := (CC.cp_nx cj - APC.NCS)%nat in let news := news_of (nx + 4) cj in
                (Z.eqb (SR.ps_pc ps) PC_OPNEW && Nat.eqb (stage i) 0 && Nat.eqb (stage j) 1 && Nat.eqb nx 40 && (Nat.eqb (chain i) 2 || Nat.eqb (chain i) 3) && Nat.leb i 4 && negb (Nat.leb j 4)
                 && CH2.blocks_eqb (BLKS i) [] && CH2.blocks_eqb (BLKS j) (BLK (chain i))
                 && CHA.foot_chk GT.NF G.HDECL c [] []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4112 0 [] [] [] news None c ps cj [] [] (BLK (chain i)) [])
                 && CRB.fresh_news_ok 65536 7028736 G.HDECL GT.SCELLS GT.GLO GT.GHI cells nx [] [] (nx + 4) (SZ (chain i)) news
                 && CL.ps_reg_is ps 10 (SZ (chain i)))%bool
              else if Z.eqb pc PC_AMEMMOVE then
                (Z.eqb (SR.ps_pc ps) PC_AMEMMOVE && Nat.eqb (stage j) 2 && (if Nat.eqb (chain i) 1 then Nat.eqb (stage i) 0 else Nat.eqb (stage i) 1 && Nat.ltb 44 (CC.cp_nx c)) && Bool.eqb (Nat.leb i 4) (Nat.eqb (chain i) 1) && Bool.eqb (Nat.leb j 4) (Nat.eqb (chain i) 1)
                 && Nat.leb 1 (chain i) && CH2.blocks_eqb (BLKS j) (BLKS i)
                 && CHA.foot_chk GT.NF G.HDECL c (BLKS i) []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 2560 0 (BLKS i) [] [(DST (chain i), 0, NARG (chain i))] (NEWS_MM (chain i)) (Some (DST (chain i))) c ps cj (BLKS i) [] (BLKS i) [])
                 && CL.ps_reg_is ps 10 (DST (chain i)) && CL.ps_reg_is ps 11 srcE && CL.ps_reg_is ps 12 (NARG (chain i))
                 && has cells (KZero (SA (CHA.SRL3 oE) SBz) (ELit 3)))%bool
              else false)%bool
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c (BLKS i) [] && CH2.blocks_eqb (nth i G.BLS []) (BLKS i)
           && ((Nat.eqb i 0) || (Nat.eqb (stage i) 2 && CBA.regions_eqb (CC.cp_F c) (FEX (chain i)) && (Nat.eqb (chain i) 1 || Nat.ltb 44 (CC.cp_nx c)))) && Bool.eqb (Nat.leb i 4) (Nat.leb (chain i) 1)
           && exit_cells (chain i) cells)%bool
      end
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Definition KNC : list kentry := firstn 15 (CC.cp_know G.cp0).
Lemma knc_ok : CC.cp_know G.cp0 = KNC ++ skipn 15 (CC.cp_know G.cp0) /\ CC.cp_know G.cp1 = KNC ++ skipn 15 (CC.cp_know G.cp1) /\ CC.cp_know G.cp2 = KNC ++ skipn 15 (CC.cp_know G.cp2) /\ CC.cp_know G.cp3 = KNC ++ skipn 15 (CC.cp_know G.cp3).
Proof. vm_compute. repeat split; reflexivity. Qed.
End SIA.

Section StrInitOk.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis OPNEW_OK : PMSA.opnew_specA L ar HI SIA.PC_OPNEW.

Lemma FFSnil : forall i, nth i SIA.FFS [] = [].
Proof. intros i. unfold SIA.FFS. do 9 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.
Lemma est0 : forall E k, 0 <= k -> estart E (SA (ELit 0) k) = k.
Proof. intros E k Hk. unfold estart. cbn [a_base a_off edenot]. rewrite u64_of_Z by lia. lia. Qed.
Lemma elit : forall E k, 0 <= k < 2 ^ 64 -> elenZ E (ELit k) = k.
Proof. intros E k Hk. unfold elenZ. cbn [edenot]. apply u64_of_Z. exact Hk. Qed.

Theorem strinit_ok : PMSA.strinit_specA L ar HI 720088.
Proof.
  intros LB FF LK cr A o src sp r txt. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & Ha2 & Hn26 & Hstksh & SBY & SDEF & SACC & (Ofr & O8 & Osh) & DO & SRCB & CRD) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.a2, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR, PMSA.stksh, PMLA.apart in *. change (64 + (16 + 4096)) with 4176 in *.
  set (n := Z.of_nat (length txt)) in *. set (cap := PML.str_cap n) in *.
  assert (N0 : 0 <= n) by (unfold n; clear; lia).

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYHN : hl_img_lo L <= 65536 /\ 7028736 <= hl_img_hi L) by (rewrite ILO, IHI; clear; lia).
  pose proof (L5A.aly_scr_mem L C LAY) as SCRMEM. pose proof (L5A.aly_memmove L C LAY) as PCAMM.

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as STT.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  destruct (CL5A.infr_rng L ar _ FF o 24 RFx Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  assert (SHR : forall p k a, 0 <= p -> 0 < k -> p + k <= 2 ^ 47 -> in_shadow_of p k a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.

  assert (SRCR : 0 < n -> exists bq bm, In (bq, bm) LB /\ bq <= src /\ src + n <= bq + bm /\ 4096 <= bq /\ 0 < bm /\ bq mod 16 = 0 /\ bq + bm <= ahl_ceil ar /\
            hid (bq + bm <= 2147446784 \/ 17594333495296 <= bq) /\ bq + bm <= 2 ^ 47 /\ hid (bq + bm <= hl_img_lo L \/ hl_img_hi L <= bq) /\ hid (bq + bm <= o \/ o + 24 <= bq)).
  { intros Hn. destruct SRCB as [E|(b & Hb & B1 & B2)]; [exfalso; unfold n in Hn; rewrite E in Hn; cbn in Hn; clear - Hn; lia|]. destruct b as [bq bm]. cbn [fst snd] in B1, B2.
    destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (bq, bm) Hb) as (BR & Bdef & Bsa & Bap & Bfap). cbn [fst snd] in BR, Bfap. destruct BR as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
    destruct Ofr as (fI & HfI & FI1 & FI2). pose proof (Bfap fI (in_or_app _ _ _ (or_introl HfI))) as BFI.
    exists bq, bm. split; [exact Hb|]. split; [exact B1|]. split; [exact B2|]. split; [exact Q0|]. split; [exact Q3|]. split; [exact Q16|]. split; [exact Q4|]. split; [exact Q6|]. split; [exact Q7|]. split; [exact Q1|].
    unfold hid. clear - BFI FI1 FI2. lia. }

  set (ns := if n <=? 22 then n else 0).
  assert (NS : 0 <= ns <= 22 /\ (n <= 22 -> ns = n)) by (unfold ns; destruct (Z.leb_spec n 22); split; clear - N0 H; lia).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [ns] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 src) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 n) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 ns) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).
  assert (U12 : bv_unsigned (ev E0 12) = n) by (rewrite V12; apply u64_of_Z; clear - N0 Hn26; lia).
  assert (U32 : bv_unsigned (ev E0 32) = ns) by (rewrite V32; apply u64_of_Z; clear - NS; lia).
  assert (U11 : 0 < n -> bv_unsigned (ev E0 11) = src) by (intros Hn; destruct (SRCR Hn) as (bq & bm & _ & B1 & B2 & Q0 & _ & _ & _ & _ & Q7 & _); rewrite V11; apply u64_of_Z; clear - B1 B2 Q0 Q7 Hn; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 4176) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := [(o, 24)] : list L5.range).
  assert (RFr : CHA.rng_facts L ar LB FF) by exact RFx.
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar LB FF sp _ o 24 a RFr Ofr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (UOK : forall k, 0 <= k -> k <= 24 -> bv_unsigned (edenot E0 (EAlu Instr.ALU_ADD (EVar 10) (ELit k))) = o + k).
  { intros k K0 K1. cbn [edenot]. rewrite AX2S.u_add64, U10, (u64_of_Z k) by (clear - K0 K1; lia). apply Z.mod_small. clear - K0 K1 O3 O6; lia. }
  assert (UNS1 : bv_unsigned (edenot E0 (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 10) (EVar 32)) (ELit 1))) = o + ns + 1).
  { cbn [edenot]. rewrite !AX2S.u_add64, U10, U32. change (bv_unsigned (Z_to_bv 64 1)) with 1. rewrite (Z.mod_small (o + ns)) by (clear - NS O3 O6; lia). apply Z.mod_small. clear - NS O3 O6; lia. }
  assert (GRN : forall k, 0 <= k < 24 -> (o + k) / 8 = o / 8 + k / 8).
  { intros k Hk. clear - O8 Hk. apply Z.mod_divide in O8; [|lia]. destruct O8 as [q ->]. rewrite Z.div_mul by lia. rewrite Z.div_add_l by lia. lia. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { assert (GEN : forall a k, 0 <= k < 24 -> (o + k) / 8 + 2147450880 <= a < (o + k) / 8 + 2147450880 + 1 -> CHA.sclientA L ar LB FF sp G.HDECL a).
    { intros a k Hk Ha. rewrite (GRN k Hk) in Ha. pose proof (Z.div_lt_upper_bound k 8 3 ltac:(clear; lia) ltac:(clear - Hk; lia)) as K3. pose proof (Z.div_pos k 8 ltac:(clear - Hk; lia) ltac:(clear; lia)) as K0.
      pose proof (CL5A.shreg_in_shadow o 3 a O8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha K3 K0; lia)) as SH. change (8 * 3) with 24 in SH.
      destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFr Ofr ltac:(clear; lia) SH) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
    intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[<-|[<-|[<-|[]]]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; cbv beta iota in Ha; rewrite CL5A.estart_srl3' in Ha; unfold CL5A.uv, elenZ in Ha.
    - cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      pose proof (CL5A.shreg_in_shadow o 3 a O8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
      destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFr Ofr ltac:(clear; lia) SH) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
    - rewrite (UOK 8 ltac:(clear; lia) ltac:(clear; lia)) in Ha. cbn [edenot] in Ha. rewrite u64_of_Z in Ha by (clear; lia). exact (GEN a 8 ltac:(clear; lia) Ha).
    - rewrite (UOK 16 ltac:(clear; lia) ltac:(clear; lia)) in Ha. cbn [edenot] in Ha. rewrite u64_of_Z in Ha by (clear; lia). exact (GEN a 16 ltac:(clear; lia) Ha).
    - rewrite (UOK 1 ltac:(clear; lia) ltac:(clear; lia)) in Ha. cbn [edenot] in Ha. rewrite u64_of_Z in Ha by (clear; lia). exact (GEN a 1 ltac:(clear; lia) Ha).
    - rewrite UNS1 in Ha. cbn [edenot] in Ha. rewrite u64_of_Z in Ha by (clear; lia). replace (o + ns + 1) with (o + (ns + 1)) in Ha by (clear; lia). exact (GEN a (ns + 1) ltac:(clear - NS; lia) Ha). }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  set (Cred := fun (i : nat) (_ : env) (cr1 : credit) => if (i <=? 4)%nat then cr1 = cr else cr1 = adebit L cr cap).
  set (CHX := fun c : nat => match c with 0%nat => n = 0 | 1%nat => 1 <= n <= 22 | 2%nat => n = 23 | _ => 24 <= n end).
  set (SRCF := fun M1 : mem => 0 < n -> L5.bytes_at (hl_segs L) M1 src txt /\ L5.defined M1 src n /\ aacc M1 src n).
  set (XI := fun (i : nat) (E : env) (_ : list (Z * Z)) (M1 : mem) (_ : Model) =>
     L5.defined M1 o 24 /\ CHX (SIA.chain i) /\ (SIA.stage i <> 2%nat -> SRCF M1) /\
     ((5 <=? i)%nat = true -> PMSA.afresh L ar LB FF M1 (CL5A.uv E SIA.nbE) cap) /\
     (SIA.stage i = 2%nat -> L5.bytes_at (hl_segs L) M1 (match SIA.chain i with 1%nat => o + 1 | _ => CL5A.uv E SIA.nbE end) txt)).
  assert (NOGOTO : forall i c kk ps0 j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps0 (CC.TGoto j sg) -> False).
  { intros i c kk ps0 j sg HIL. pose proof (CH2.leaves_all_sound _ _ _ SIA.leaf_ok _ _ _ _ _ HIL) as X. cbv beta iota in X. discriminate X. }

  assert (HCH : exists i0 : nat, (i0 <= 3)%nat /\ CHX i0).
  { unfold CHX. destruct (Z.eq_dec n 0) as [Hz|Hz]; [exists 0%nat; split; [clear; lia | exact Hz]|].
    destruct (Z_le_gt_dec n 22) as [Hle|Hgt]; [exists 1%nat; split; [clear; lia | clear - Hz Hle N0; lia]|].
    destruct (Z.eq_dec n 23) as [H23|H23]; [exists 2%nat; split; [clear; lia | exact H23] | exists 3%nat; split; [clear; lia | clear - Hgt H23; lia]]. }
  destruct HCH as (i0 & Hi0 & HCH0).
  assert (ST0 : SIA.stage i0 = 0%nat /\ SIA.chain i0 = i0 /\ nth i0 G.BLS [] = [] /\ nth_error G.CPS i0 = Some (nth i0 G.CPS G.cp0) /\ CC.cp_pc (nth i0 G.CPS G.cp0) = 720088).
  { destruct i0 as [|[|[|[|i0]]]]; [repeat split; reflexivity | repeat split; reflexivity | repeat split; reflexivity | repeat split; reflexivity | exfalso; clear - Hi0; lia]. }
  destruct ST0 as (ST0 & CHN0 & BLS0 & CP0 & PC0).
  rewrite <- LS in FPM. rewrite <- PC0.
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS SIA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := i0) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact SIA.heap_ok.
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  -

    assert (UVE : forall E e z, env_agree GT.NF E0 E -> APC.expr_vars_lt GT.NF e = true -> CL5A.uv E0 e = z -> CL5A.uv E e = z).
    { intros E e z Hag Hv Hz. rewrite (CL5A.uv_agree GT.NF E0 E e Hag Hv). exact Hz. }
    assert (CAPF : 23 <= n -> cap = (if n =? 23 then 26 else 8 * (n / 8) + 8) /\ n < cap <= n + 8 /\ Z.testbit (cap + 1) 0 = true /\ 0 < cap <= 2 ^ 27) by (intros Hn; exact (TKA.str_cap_facts n Hn Hn26)).
    assert (CH23 : forall ch, (ch = 2%nat \/ ch = 3%nat) -> CHX ch -> (ch = 2%nat /\ n = 23 /\ cap = 26) \/ (ch = 3%nat /\ 24 <= n /\ cap = 8 * (n / 8) + 8)).
    { intros ch [-> | ->] HX; unfold CHX in HX; [left | right]; (split; [reflexivity|]); (split; [exact HX|]); destruct (CAPF ltac:(clear - HX; lia)) as (E & _); rewrite E;
        [rewrite (proj2 (Z.eqb_eq n 23) HX); reflexivity | destruct (Z.eqb_spec n 23) as [E23|_]; [exfalso; clear - HX E23; lia | reflexivity]]. }
    assert (USZ : forall E ch, env_agree GT.NF E0 E -> (ch = 2%nat /\ n = 23 /\ cap = 26) \/ (ch = 3%nat /\ 24 <= n /\ cap = 8 * (n / 8) + 8) -> CL5A.uv E (SIA.SZ ch) = cap).
    { intros E ch HagE Hch. assert (W12E : bv_unsigned (ev E 12) = n) by (rewrite <- (proj1 HagE 12%nat) by (apply Nat.ltb_lt; reflexivity); exact U12).
      destruct Hch as [(-> & Hn & Hc)|(-> & Hn & Hc)]; unfold SIA.SZ, SIA.R8, SIA.nE, CL5A.uv; rewrite Hc.
      - cbn [edenot]. apply u64_of_Z. clear; lia.
      - cbn [edenot]. rewrite AX2S.u_add64, AX2S.u_mul64, AX2S.u_srl64, W12E. change (bv_unsigned (Z_to_bv 64 8)) with 8. change (bv_unsigned (Z_to_bv 64 3)) with 3. change (2 ^ (3 mod 64)) with 8.
        pose proof (Z.div_pos n 8 N0 ltac:(clear; lia)) as D0. pose proof (Z.div_le_mono n (2 ^ 26) 8 ltac:(clear; lia) ltac:(clear - Hn26; lia)) as D1. change (2 ^ 26 / 8) with 8388608 in D1.
        rewrite (Z.mod_small (8 * (n / 8))) by (clear - D0 D1; lia). apply Z.mod_small. clear - D0 D1; lia. }
    assert (DENB : forall E ch, env_agree GT.NF E0 E -> (ch = 2%nat /\ n = 23 /\ cap = 26) \/ (ch = 3%nat /\ 24 <= n /\ cap = 8 * (n / 8) + 8) -> CH2.den E (SIA.BLK ch) = [(CL5A.uv E SIA.nbE, cap)]).
    { intros E ch HagE Hch. unfold CH2.den, SIA.BLK. cbn [map fst snd]. unfold CL5A.uv in USZ |- *. rewrite (USZ E ch HagE Hch). reflexivity. }

    set (PZ := fun a : Z => 0 < n /\ (src <= a < src + n \/ in_shadow_of src n a)).
    assert (PZR : forall a, PZ a -> 0 < n /\ exists bq bm, In (bq, bm) LB /\ bq <= src /\ src + n <= bq + bm /\ 4096 <= bq /\ 0 < bm /\ bq mod 16 = 0 /\ bq + bm <= ahl_ceil ar /\
            hid (bq + bm <= 2147446784 \/ 17594333495296 <= bq) /\ bq + bm <= 2 ^ 47 /\ hid (bq + bm <= hl_img_lo L \/ hl_img_hi L <= bq) /\ hid (bq + bm <= o \/ o + 24 <= bq) /\
            ((bq <= a < bq + bm /\ src <= a < src + n) \/ (in_shadow_of bq bm a /\ in_shadow_of src n a /\ 2147450880 <= a < 17594333495296))).
    { intros a (Hn & Ha). split; [exact Hn|]. destruct (SRCR Hn) as (bq & bm & PIN & B1 & B2 & Q0 & Q3 & Q16 & Q4 & Q6 & Q7 & Q1 & QO).
      exists bq, bm. do 11 (split; [assumption|]). destruct Ha as [Ha|Ha]; [left; clear - Ha B1 B2; lia | right].
      split; [exact (CL5A.in_shadow_mono src n bq bm a B1 B2 Hn Ha)|]. split; [exact Ha|]. exact (SHR src n a ltac:(clear - Q0 B1; lia) Hn ltac:(clear - B2 Q7; lia) Ha). }
    assert (NPZ_STK : forall a, sp - 4176 <= a < sp -> ~ PZ a).
    { intros a Ha Hz. apply PZR in Hz. destruct Hz as (Hn & bq & bm & _ & _ & _ & _ & _ & _ & Q4 & _ & _ & _ & _ & HX). destruct HX as [(X & _)|(_ & _ & X)]; [clear - Ha X Q4 S2; lia | clear - Ha X S2 CL; lia]. }
    assert (NPZ_O : forall a, o <= a < o + 24 -> ~ PZ a).
    { intros a Ha Hz. apply PZR in Hz. unfold hid in O5. destruct Hz as (Hn & bq & bm & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QO & HX). destruct HX as [(X & _)|(_ & _ & X)]; [unfold hid in QO; clear - Ha X QO; lia | clear - Ha X O5; lia]. }
    assert (NPZ_NB : forall (Mx : mem) u m a, PMSA.afresh L ar LB FF Mx u m -> (u <= a < u + m \/ in_shadow_of u m a) -> ~ PZ a).
    { intros Mx u m a (Hrng & Hbap & Hfap & _ & _) Ha Hz. pose proof Hrng as (R0 & R1 & R16 & R3 & R4 & (R5 & R6 & R7)). unfold BIGSHADOW_LO, BIGSHADOW_HI in R6.
      apply PZR in Hz. destruct Hz as (Hn & bq & bm & PIN & B1 & B2 & Q0 & Q3 & Q16 & Q4 & Q6 & Q7 & _ & _ & HX). pose proof (Hbap (bq, bm) PIN) as AB. cbn [fst snd] in AB. unfold hid in Q6.
      destruct Ha as [Ha|Ha]; destruct HX as [(X & _)|(X & _ & SRx)].
      - clear - Ha X AB. lia.
      - clear - Ha SRx R6. lia.
      - pose proof (SHR u m a R5 R3 R7 Ha) as SRa. clear - SRa X Q6. lia.
      - exact (CL5A.sh_apart2 u m bq bm a R5 ltac:(clear - Q0; lia) R3 Q3 (CHA.mod8_of_16 _ R16) (CHA.mod8_of_16 _ Q16) AB Ha X). }
    assert (AGS : forall (M1 M2 : mem), (forall a, PZ a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> SRCF M1 -> SRCF M2).
    { intros M1 M2 AGm XS Hn. destruct (XS Hn) as (XB & XD & XA). destruct (SRCR Hn) as (bq & bm & _ & B1 & B2 & Q0 & _ & _ & _ & _ & Q7 & _).
      split; [apply (CL5A.bytes_same (hl_segs L) M1 M2 src txt ltac:(clear - Q0 B1; lia) ltac:(fold n; clear - B2 Q7; lia)); [intros a Ha; apply AGm; split; [exact Hn | left; fold n in Ha; exact Ha] | exact XB]|].
      split; [apply (CL5A.defined_same M1 M2 src n); [intros a Ha; apply AGm; split; [exact Hn | left; exact Ha] | exact XD]|].
      intros a Ha. assert (E : M2 (Z_to_bv 64 (S a)) = M1 (Z_to_bv 64 (S a))).
      { apply AGm. split; [exact Hn|]. right. unfold in_shadow_of, S. pose proof (CL5A.div8_le src a ltac:(clear - Ha; lia)). pose proof (CL5A.div8_le a (src + n - 1) ltac:(clear - Ha; lia)). clear - H H0. lia. }
      unfold byte_at. rewrite E. exact (XA a Ha). }
    assert (HPZ : forall (M1 M2 : mem) LBx spx scrx Wc, CHA.ahpres L ar LBx FF spx scrx Wc M1 M2 -> incl LB LBx -> (forall w a, In w Wc -> L5.in_rng w a -> ~ PZ a) ->
              forall a, PZ a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros M1 M2 LBx spx scrx Wc (HP1 & _ & _) HLB HW a Ha. apply HP1. pose proof (PZR a Ha) as (Hn & bq & bm & PIN & B1 & B2 & Q0 & _ & _ & _ & _ & Q7 & _ & _ & HX).
      split; [clear - HX Q0 Q7; lia|]. split; [|intros w Hw Hin; exact (HW w a Hw Hin Ha)].
      destruct HX as [(X & _)|(X & _)]; [left; exists (bq, bm); split; [exact (HLB _ PIN) | cbn [fst snd]; exact X] | do 6 right; exists (bq, bm); split; [exact (HLB _ PIN) | exact X]]. }
    assert (KDEF : forall (M1 M2 : mem) LBx spx scrx Wc, CHA.ahpres L ar LBx FF spx scrx Wc M1 M2 -> L5.defined M1 o 24 -> L5.defined M2 o 24).
    { intros M1 M2 LBx spx scrx Wc (_ & _ & HP3) XD i Hi. apply (HP3 (o + i)); [clear - Hi O3 O6; lia | | exact (XD i Hi)].
      right; right; right; left. destruct Ofr as (f & Hf & F1 & F2). exists f. split; [exact Hf | clear - Hi F1 F2; lia]. }

    assert (KOSH : forall (M1 M2 : mem) LBx spx scrx Wc, CHA.ahpres L ar LBx FF spx scrx Wc M1 M2 ->
              (forall w a, In w Wc -> L5.in_rng w a -> a < 2147446784 \/ 17594333495296 <= a) -> forall j, 0 <= j < 3 -> M2 (Z_to_bv 64 (S o + j)) = M1 (Z_to_bv 64 (S o + j))).
    { intros M1 M2 LBx spx scrx Wc (HP1 & _ & _) HW j Hj. pose proof (CL5A.shreg_in_shadow o 3 (S o + j) O8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia)) as SH. change (8 * 3) with 24 in SH.
      pose proof (SHR o 24 (S o + j) O3 ltac:(clear; lia) O6 SH) as SRa. apply HP1. split; [clear - SRa; lia|].
      split; [do 5 right; left; destruct Ofr as (f & Hf & F1 & F2); exists f; split; [exact Hf | exact (CL5A.in_shadow_mono o 24 (ff_addr f) (ff_bytes (ff_class f)) (S o + j) ltac:(clear - F1; lia) ltac:(clear - F2; lia) ltac:(clear; lia) SH)]|].
      intros w Hw Hin. pose proof (HW w _ Hw Hin) as X. clear - X SRa. lia. }

    assert (LAG : forall i c ps0 E E' R1 R' A1 M1 m1 M' m',
              CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) [] = true ->
              CCA.AtV (hl_segs L) c E R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS SIA.FFS Cred 0 i E A1 M1 m1 ->
              env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
              (forall b, In b (CH2.den E (nth i G.BLS [])) -> PMSA.afresh L ar LB FF M1 (fst b) (snd b)) ->
              forall a, (PZ a \/ (exists b, In b (CH2.den E (nth i G.BLS [])) /\ in_shadow_of (fst b) (snd b) a)) -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros i c ps0 E E' R1 R' A1 M1 m1 M' m' Hfoot HAt HA Hag HLF HBL a Ha.
      assert (A64 : 0 <= a < 2 ^ 64).
      { destruct Ha as [Ha|(b & Hb & Hsh)]; [apply PZR in Ha; destruct Ha as (_ & bq & bm & _ & _ & _ & Q0 & _ & _ & _ & _ & Q7 & _ & _ & HX); clear - HX Q0 Q7; lia|].
        destruct (HBL b Hb) as ((R0 & _ & _ & R3 & _ & (R5 & _ & R7)) & _). pose proof (SHR _ _ a R5 R3 R7 Hsh) as SRa. clear - SRa. lia. }
      refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS SIA.FFS Cred 0 STKF SCRP NF32 U2 WRS_OK i c ps0 E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a A64 _);
        [rewrite FFSnil; exact Hfoot|].
      rewrite FFSnil. intros [X|[X|[X|[X|X]]]].
      - rewrite SCRV in X. destruct Ha as [Ha|(b & Hb & Hsh)]; [exact (NPZ_STK a X Ha)|].
        destruct (HBL b Hb) as ((R0 & _ & _ & R3 & R4 & (R5 & _ & R7)) & _). pose proof (SHR _ _ a R5 R3 R7 Hsh) as SRa. clear - SRa X S2 CL. lia.
      - destruct X as (w & [<-|[]] & Hin). unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
        destruct Ha as [Ha|(b & Hb & Hsh)]; [exact (NPZ_O a Hin Ha)|].
        destruct (HBL b Hb) as ((R0 & _ & _ & R3 & R4 & (R5 & _ & R7)) & _). pose proof (SHR _ _ a R5 R3 R7 Hsh) as SRa. unfold hid in O5. clear - SRa Hin O5. lia.
      - destruct X as (b & Hb & Hin). pose proof (HBL b Hb) as AFb.
        destruct Ha as [Ha|(b' & Hb' & Hsh)]; [exact (NPZ_NB M1 _ _ a AFb (or_introl Hin) Ha)|].
        destruct (HBL b' Hb') as ((R0 & _ & _ & R3 & R4 & (R5 & R6 & R7)) & _). pose proof (SHR _ _ a R5 R3 R7 Hsh) as SRa.
        destruct AFb as ((_ & _ & _ & _ & _ & (_ & B6 & _)) & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in B6. clear - SRa Hin B6. lia.
      - destruct X as (f & [] & _).
      - destruct X as (f & [] & _). }
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS SIA.FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.

    assert (AMM : forall dst sr nn bs LBx LKx crx Ax spx rx, CBA.cps_asanG L ar HI PMSA.fp_ok SIA.PC_AMEMMOVE rx spx 2560 LBx FF LKx crx Ax 0 (CRC.memcpy_pre L ar LBx FF spx 2560 dst sr nn bs) (CRC.memcpy_post LBx crx dst nn bs)).
    { intros dst sr nn bs LBx LKx crx Ax spx rx. unfold SIA.PC_AMEMMOVE. rewrite <- PCAMM. exact (CRC.asan_memmove_cps L ar C HI HIok PMSA.fp_ok 2560 LBx FF LKx crx Ax dst sr nn bs spx rx ltac:(rewrite SCRMEM; clear; lia)). }

    intros i c kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ SIA.leaf_ok _ _ _ _ _ HIL) as X. unfold SIA.leaf_chk in X.
    destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret.
    + destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X0 X]. apply andb_prop in X0 as [X0 YBj]. apply andb_prop in X0 as [YCH YBi]. apply Nat.eqb_eq in YCH. apply CH2.blocks_eqb_eq in YBi, YBj.
      destruct (Z.eqb_spec pc SIA.PC_OPNEW) as [->|Hne1].
      {
        cbv zeta in X. set (nx := (CC.cp_nx cj - APC.NCS)%nat) in *. set (news := SIA.news_of (nx + 4) cj) in *.
        apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y8]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X YKj]. apply andb_prop in X as [X YKi].
        apply andb_prop in X as [X YLj]. apply andb_prop in X as [X YLi]. apply andb_prop in X as [X YC]. apply andb_prop in X as [X YN]. apply andb_prop in X as [X Ysj]. apply andb_prop in X as [Y0 Ysi].
        apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Ysi, Ysj, YN. apply CH2.blocks_eqb_eq in YKi, YKj. rewrite YKi in YBi. rewrite YKj in YBj.
        assert (YC' : SIA.chain i = 2%nat \/ SIA.chain i = 3%nat) by (apply orb_prop in YC; destruct YC as [YC|YC]; apply Nat.eqb_eq in YC; [left | right]; exact YC).
        lazymatch type of Y5 with SIA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
        unfold XI in HXi. destruct HXi as (XD & XC & XS & _ & _). specialize (XS ltac:(rewrite Ysi; clear; lia)).
        pose proof (CH23 _ YC' XC) as HCH. assert (Hn23 : 23 <= n) by (destruct HCH as [(_ & Hn & _)|(_ & Hn & _)]; clear - Hn; lia). destruct (CAPF Hn23) as (_ & CAP1 & CAPB & CAP27).
        assert (HcB : CHA.curB LB G.BLS i E = LB) by (unfold CHA.curB; rewrite YBi; reflexivity).
        assert (HcF : CHA.curF FF sp SIA.FFS i E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
        refine (CALLEE SIA.PC_OPNEW 4112 0%nat [] [] news None 0 i c ps0 j cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, YBi, YBj; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite YLi in HC1; exact HC1). subst cr1.
        assert (NXeq : CH2.ci_nx ci = nx) by (destruct HV as (_ & _ & _ & _ & HV5); unfold nx; rewrite HV5; unfold APC.NCS; clear; lia).
        pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
        assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps0 q e = true -> CL5A.uv E' e = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
        { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ HLFv Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
        pose proof (LAG i c ps0 E E' R1 R' A1 M1 m1 M' m' ltac:(rewrite YBi; exact YF) HAt HA Hag HLF ltac:(rewrite YBi; intros b [])) as AGL.
        assert (XD' : L5.defined M' o 24) by exact (L5.defined_grows M1 M' o 24 (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF) XD).
        pose proof (AGS M1 M' (fun a Ha => AGL a (or_introl Ha)) XS) as XS'.
        eexists. eexists. split; [exact (OPNEW_OK LB FF LK1 cr A1 cap (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
        { unfold PMSA.a0. split; [exact (REG 10%nat (SIA.SZ (SIA.chain i)) cap Y10 (USZ E' _ HagE' HCH)) | split; [exact CAP27 | apply CRD; unfold n in Hn23; clear - Hn23; lia]]. }
        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (u & Hu & Hfresh & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        pose proof Hfresh as (Hrng & Hbap & Hfap & Hdef & Hsh). pose proof Hrng as (NQ0 & NQ1 & NQ16 & NQ3 & NQ4 & (NQ5 & NQ6 & NQ7)).
        exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
        pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
        set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
        assert (UR : 0 <= u < 2 ^ 64) by (clear - NQ5 NQ7 NQ3; lia).
        assert (Hvu : CL5A.uv E2 SIA.nbE = u).
        { unfold CL5A.uv, SIA.nbE. cbn [edenot]. pose proof (CH2.retEx_a0 E' (CH2.ci_nx ci) [] R2) as G0. cbn [length] in G0. rewrite Nat.add_0_r in G0.
          unfold E2. rewrite NXeq, YN in G0. rewrite NXeq, YN. change (40 + 4)%nat with 44%nat in G0. unfold PMSA.a0 in Hu. rewrite G0, Hu. apply u64_of_Z. exact UR. }
        assert (HagE2 : env_agree GT.NF E0 E2).
        { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
        split; [cbn [CH2.den map app]; apply incl_refl|]. split; [intros w a []|]. split; [intros w a []|].
        assert (HBj : CHA.curB LB G.BLS j E2 = (u, cap) :: LB) by (unfold CHA.curB; rewrite YBj, (DENB E2 _ HagE2 HCH), Hvu; reflexivity).
        split; [rewrite HBj; exact HH2|]. split; [unfold Cred; apply negb_true_iff in YLj; rewrite YLj; reflexivity|].
        split.
        { unfold XI. rewrite YCH, Ysj. cbv zeta. rewrite Hvu.
          pose proof (HPZ M' M2 LB _ 4112 [] HP (incl_refl _) (fun w a Hw _ => match Hw with end)) as HP1'.
          split; [exact (KDEF M' M2 LB _ 4112 _ HP XD')|]. split; [exact XC|]. split; [intros _; exact (AGS M' M2 HP1' XS')|]. split; [intros _; exact Hfresh | intros H7; exfalso; clear - H7; lia]. }

        intros X0 HX0 _.
        refine (CRB.news_sound L ar C HI HIok LYI 65536 7028736 LYHN GT.NF E0 LB FF sp G.HDECL WW STKF SCRP NF32 U2 WOK CRS_OK WRS_OK GT.SCELLS GT.GLO GT.GHI SCOK GOTOK
                  E' E2 (CH2.ci_nx ci) (SR.ps_cells ps0) [] [] 44%nat (SIA.SZ (SIA.chain i)) M' M2 A1 A2 m' m2 LB ((u, cap) :: LB) FF FF LK1 LK2 cr (adebit L cr cap) u cap news
                  HagE' Hag2 HK HH1 eq_refl eq_refl Hvu _ (USZ E' _ HagE' HCH) Hrng Hbap Hfap Hdef Hsh HH2 (or_introl eq_refl) _ X0 HX0).
        - rewrite NXeq, YN. destruct HCH as [(HQ1 & _)|(HQ1 & _)]; rewrite HQ1; reflexivity.
        - rewrite NXeq. rewrite YN in Y8 |- *. exact Y8. }
      destruct (Z.eqb_spec pc SIA.PC_AMEMMOVE) as [->|Hne2]; [|exfalso; clear - X; discriminate X].
      {
        apply andb_prop in X as [X Ysh]. apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF].
        apply andb_prop in X as [X YK]. apply andb_prop in X as [X YC1]. apply andb_prop in X as [X YLj]. apply andb_prop in X as [X YLi]. apply andb_prop in X as [X YST]. apply andb_prop in X as [Y0 Ysj].
        apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Ysj. apply CH2.blocks_eqb_eq in YK. rewrite YK in YBj.
        lazymatch type of Y5 with SIA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
        unfold XI in HXi. destruct HXi as (XD & XC & XS & XAF & _).
        assert (HcF : CHA.curF FF sp SIA.FFS i E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
        refine (CALLEE SIA.PC_AMEMMOVE 2560 0%nat (SIA.BLKS i) [(SIA.DST (SIA.chain i), 0, SIA.NARG (SIA.chain i))] (SIA.NEWS_MM (SIA.chain i)) (Some (SIA.DST (SIA.chain i))) 0 i c ps0 j cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, YBi, YBj; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
        rewrite HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
        assert (CELL : forall X0, SIA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
        { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
        pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS SIA.FFS Cred 0 i E A1 M' m' HA') as Hoff.
        assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps0 q e = true -> CL5A.uv E' e = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
        { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ HLFv Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
        assert (W10 : CL5A.uv E' (EVar 10) = o) by exact (UVE E' (EVar 10) o HagE' eq_refl U10).
        assert (SZ' : shadow_zero M' o 3).
        { intros jj Hj. apply (CL5A.byte_full (ahid A1 m') M'). exact (CL5A.shz_elim (hl_segs L) E' _ (EVar 10) 3 o (CELL _ Ysh) W10 ltac:(clear; lia) jj Hj). }
        assert (XD' : L5.defined M' o 24) by exact (L5.defined_grows M1 M' o 24 (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF) XD).
        assert (HN1 : 0 < n) by (unfold CHX in XC; apply Nat.leb_le in YC1; destruct (SIA.chain i) as [|[|[|ch]]]; [exfalso; clear - YC1; lia | clear - XC; lia | clear - XC; lia | clear - XC; lia]).
        destruct (SRCR HN1) as (bq & bm & PIN & B1 & B2 & Q0 & Q3 & Q16 & Q4 & Q6 & Q7 & Q1 & QO). pose proof (U11 HN1) as U11'.
        assert (W11 : CL5A.uv E' SIA.srcE = src) by exact (UVE E' (EVar 11) src HagE' eq_refl U11').
        pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) []) as Hag2g.

        assert (HagE2g : forall R2, env_agree GT.NF E0 (CH2.retEx E' (CH2.ci_nx ci) [] R2)).
        { intros R2. eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact (Hag2g R2)|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }

        assert (STNEWS : forall E2 A2 m2 M2 LB2 LK2 cr2, ri_inv HI LB2 FF LK2 cr2 A2 M2 (vml_of m2) -> forall X0, In X0 SIA.STAT -> kentry_ok (hl_segs L) E2 (CCA.vis A2 m2 M2) X0).
        { intros E2 A2 m2 M2 LB2 LK2 cr2 HH2 X0 HX0. unfold SIA.STAT in HX0. cbn [In] in HX0.
          destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). }
        destruct (Nat.eqb_spec (SIA.chain i) 1) as [YCH1|YCH1].
        -
          rewrite YCH1 in YCH, Y10, Y12. cbn [SIA.DST SIA.NARG] in Y10, Y12. apply Nat.eqb_eq in YST. apply eqb_prop in YLi. apply eqb_prop in YLj.
          assert (HBi : SIA.BLKS i = []) by (unfold SIA.BLKS; rewrite YLi; reflexivity).
          rewrite HBi in YBi, YBj, YF |- *.
          assert (HcB : CHA.curB LB G.BLS i E = LB) by (unfold CHA.curB; rewrite YBi; reflexivity). rewrite HcB in HH1 |- *.
          assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite YLi in HC1; exact HC1). subst cr1.
          unfold CHX in XC. rewrite YCH1 in XC. destruct NS as (NSR & NSE). specialize (NSE ltac:(clear - XC; lia)).
          assert (W32 : CL5A.uv E' SIA.nsE = n) by (rewrite <- NSE; exact (UVE E' (EVar 32) ns HagE' eq_refl U32)).
          assert (UD : CL5A.uv E' (SIA.IA 1) = o + 1) by exact (UVE E' (SIA.IA 1) (o + 1) HagE' eq_refl (UOK 1 ltac:(clear; lia) ltac:(clear; lia))).
          assert (UT : CL5A.uv E' (SIA.TERM 1%nat) = o + n + 1) by (rewrite <- NSE; exact (UVE E' (SIA.TERM 1%nat) (o + ns + 1) HagE' eq_refl UNS1)).
          pose proof (LAG i c ps0 E E' R1 R' A1 M1 m1 M' m' ltac:(rewrite YBi; exact YF) HAt HA Hag HLF ltac:(rewrite YBi; intros b [])) as AGL.
          pose proof (AGS M1 M' (fun a Ha => AGL a (or_introl Ha)) ltac:(apply XS; rewrite YST; clear; lia)) as XS'. destruct (XS' HN1) as (XB' & XDF' & XA').
          eexists. eexists. split; [exact (AMM (o + 1) src n (map (Z_to_bv 8) txt) LB LK1 cr A1 (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
          { unfold CRC.memcpy_pre. split; [exact (REG 10%nat _ (o + 1) Y10 UD)|]. split; [exact (REG 11%nat _ src Y11 W11)|]. split; [exact (REG 12%nat _ n Y12 W32)|]. split; [|split].
            -
              unfold CRC.mem_dst. split; [clear - XC; lia|]. split.
              + intros a Ha. left. replace (S a) with (S o + (a - o) / 8) by (unfold S; pose proof (GRN (a - o) ltac:(clear - Ha XC; lia)) as G; replace (o + (a - o)) with a in G by (clear; lia); rewrite G; clear; lia).
                apply SZ'. split; [apply Z.div_pos; clear - Ha; lia | apply Z.div_lt_upper_bound; clear - Ha XC; lia].
              + split; [intros k Hk; exact (CL5A.infr_clientw L ar LB FF _ 2560 o 24 (o + 1 + k) Ofr ltac:(clear - Hk XC; lia))|].
                split; [exact (L5C.writable_of_defined (hl_segs L) M' (o + 1) n (L5.defined_sub M' o 24 (o + 1) n XD' ltac:(clear; lia) ltac:(clear - XC; lia)) ltac:(clear - O3; lia) ltac:(clear - O6 XC; lia))|].
                unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. unfold hid in O5. split; [clear - O3; lia|]. split; [clear - O5 XC; lia | left; clear - O4 S2 S3 XC; lia].
            - refine (CRC.src_in_block L ar C HI HIok _ FF LK1 _ A1 M' _ (sp + CH2.ci_csp ci) 2560 bq bm src n (map (Z_to_bv 8) txt) HH1 PIN XA' B1 B2 N0 _).
              unfold n. rewrite Nat2Z.id. apply (L5C.bytes_at_rdn (hl_segs L) M' txt src ltac:(clear - Q0 B1; lia) ltac:(fold n; clear - B2 Q7; lia)). exact XB'.
            - unfold hid in QO. clear - QO B1 B2 XC. lia. }
          intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & Hnew & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          exists []. split; [reflexivity|]. cbv zeta. rewrite YCH1. cbn [SIA.DST SIA.NARG]. set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *. pose proof (HagE2g R2) as HagE2. fold E2 in HagE2.
          assert (UD2 : CL5A.uv E2 (SIA.IA 1) = o + 1) by exact (UVE E2 (SIA.IA 1) (o + 1) HagE2 eq_refl (UOK 1 ltac:(clear; lia) ltac:(clear; lia))).
          split; [rewrite Ha0'; unfold CL5A.uv in UD2; rewrite <- UD2; apply Z_to_bv_bv_unsigned|].
          split; [cbn [CH2.den map app]; apply incl_refl|].
          assert (WIN : forall w a, In w [(o + 1, n)] -> L5.in_rng w a -> o + 1 <= a < o + 1 + n) by (intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin).
          split.
          { intros w a Hw Hin. pose proof (WIN w a Hw Hin) as Ha. exists (SIA.IA 1, 0, SIA.nsE). split; [left; reflexivity|].
            unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off]. unfold CL5A.uv in UD, W32. rewrite UD, W32. clear - Ha. lia. }
          split.
          { intros w a Hw Hin (Ka & Kc & Kw). apply (Kw (o, 24)); [left; reflexivity|]. unfold L5.in_rng. cbn [fst snd]. pose proof (WIN w a Hw Hin). clear - H XC. lia. }
          split; [unfold CHA.curB; rewrite YBj; cbn [CH2.den map app]; exact HH2|]. split; [unfold Cred; rewrite YLj; reflexivity|].
          assert (KO2 : forall jj, 0 <= jj < 3 -> M2 (Z_to_bv 64 (S o + jj)) = M' (Z_to_bv 64 (S o + jj))).
          { apply (KOSH M' M2 LB _ 2560 _ HP). intros w a Hw Hin. pose proof (WIN w a Hw Hin). unfold hid in O5. clear - H O5 XC. lia. }
          split.
          { unfold XI. rewrite YCH, Ysj. cbv zeta.
            split; [exact (KDEF M' M2 LB _ 2560 _ HP XD')|]. split; [exact XC|]. split; [intros H2; exfalso; exact (H2 eq_refl)|].
            split; [intros H5; exfalso; apply Nat.leb_le in H5; apply Nat.leb_le in YLj; clear - H5 YLj; lia|].
            intros _. apply (TKA.bytes_of_copy2 (hl_segs L) M2 (o + 1) txt). intros ii Hii. apply Hnew. exact Hii. }

          intros X0 HX0 _. unfold SIA.NEWS_MM in HX0. apply in_app_or in HX0. destruct HX0 as [HX0|[<-|[]]]; [exact (STNEWS E2 A2 m2 M2 _ _ _ HH2 X0 HX0)|].
          eapply CL5A.kzero_intro with (A := (o + n + 1) / 8 + 2147450880) (N := 1);
            [rewrite CL5A.estart_srl3, (UVE E2 (SIA.TERM 1%nat) (o + n + 1) HagE2 eq_refl ltac:(rewrite <- NSE; exact UNS1)); reflexivity | apply elit; clear; lia | clear - O3 XC; lia | clear - O3 O6 XC; lia | clear - O3 O6 XC; lia |].
          intros jj Hj. replace ((o + n + 1) / 8 + 2147450880 + jj) with (S o + (n + 1) / 8) by (unfold S, SB; replace (o + n + 1) with (o + (n + 1)) by (clear; lia); rewrite (GRN (n + 1)) by (clear - XC; lia); clear - Hj; lia).
          pose proof (Z.div_pos (n + 1) 8 ltac:(clear - XC; lia) ltac:(clear; lia)) as G0. pose proof (Z.div_lt_upper_bound (n + 1) 8 3 ltac:(clear; lia) ltac:(clear - XC; lia)) as G1.
          apply CL5A.byte_vis; [| unfold byte_at; rewrite (KO2 ((n + 1) / 8) ltac:(clear - G0 G1; lia)); exact (SZ' ((n + 1) / 8) ltac:(clear - G0 G1; lia))].
          destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o 24 (S o + (n + 1) / 8) RFx Ofr ltac:(clear; lia) (CL5A.shreg_in_shadow o 3 (S o + (n + 1) / 8) O8 ltac:(clear; lia) ltac:(unfold S; clear - G0 G1; lia))) as (V1 & V2' & V3).
          exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ m2 sp 0 _ HH2 V1 (aclientw_client _ _ _ _ _ _ _ V2') V3).
        -
          apply andb_prop in YST as [YST Y44]. apply Nat.eqb_eq in YST. apply Nat.ltb_lt in Y44. apply eqb_prop in YLi. apply eqb_prop in YLj.
          assert (C3 : (SIA.chain i <= 3)%nat) by (clear; unfold SIA.chain; destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]]; cbn; lia).
          assert (YC' : SIA.chain i = 2%nat \/ SIA.chain i = 3%nat) by (apply Nat.leb_le in YC1; destruct (Nat.eq_dec (SIA.chain i) 2) as [E2|NE2]; [left; exact E2 | right; clear - C3 YC1 YCH1 NE2; lia]).
          assert (HBi : SIA.BLKS i = SIA.BLK (SIA.chain i)) by (unfold SIA.BLKS; rewrite YLi; reflexivity).
          rewrite HBi in YBi, YBj, YF |- *.
          unfold CHX in XC. pose proof (CH23 _ YC' XC) as HCH. assert (Hn23 : 23 <= n) by (destruct HCH as [(_ & Hn & _)|(_ & Hn & _)]; clear - Hn; lia). destruct (CAPF Hn23) as (_ & CAP1 & CAPB & CAP27).
          specialize (XAF ltac:(apply Nat.leb_le; apply Nat.leb_gt in YLi; clear - YLi; lia)).
          set (nb := CL5A.uv E SIA.nbE) in *.
          pose proof XAF as (Hrng & Hbap & Hfap & Hdef1 & Hsh1). pose proof Hrng as (NQ0 & NQ1 & NQ16 & NQ3 & NQ4 & (NQ5 & NQ6 & NQ7)).
          assert (HdenE : CH2.den E (SIA.BLK (SIA.chain i)) = [(nb, cap)]) by exact (DENB E _ HagE HCH).
          assert (HcB : CHA.curB LB G.BLS i E = (nb, cap) :: LB) by (unfold CHA.curB; rewrite YBi, HdenE; reflexivity). rewrite HcB in HH1 |- *.
          assert (Hcr1 : cr1 = adebit L cr cap) by (unfold Cred in HC1; rewrite YLi in HC1; exact HC1). subst cr1.
          assert (NB' : CL5A.uv E' SIA.nbE = nb) by (unfold nb; exact (CL5A.uv_var (CC.cp_nx c) E E' 44 Hag Y44)).
          assert (UD : CL5A.uv E' (SIA.DST (SIA.chain i)) = nb) by (destruct YC' as [HQ|HQ]; rewrite HQ; exact NB').
          assert (UN : CL5A.uv E' (SIA.NARG (SIA.chain i)) = n).
          { destruct HCH as [(HQ & Hn & _)|(HQ & Hn & _)]; rewrite HQ; cbn [SIA.NARG]; [rewrite Hn; unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; clear; lia | exact (UVE E' (EVar 12) n HagE' eq_refl U12)]. }
          assert (UT : forall Ex, env_agree GT.NF E0 Ex -> CL5A.uv Ex SIA.nbE = nb -> CL5A.uv Ex (SIA.TERM (SIA.chain i)) = nb + n).
          { intros Ex HagEx NBx. assert (W12x : bv_unsigned (ev Ex 12) = n) by (rewrite <- (proj1 HagEx 12%nat) by (apply Nat.ltb_lt; reflexivity); exact U12).
            unfold CL5A.uv, SIA.nbE in NBx. cbn [edenot] in NBx.
            destruct HCH as [(HQ & Hn & _)|(HQ & Hn & _)]; rewrite HQ; cbn [SIA.TERM]; unfold CL5A.uv, SIA.nbE, SIA.nE; cbn [edenot]; rewrite AX2S.u_add64, NBx; [change (bv_unsigned (Z_to_bv 64 23)) with 23; rewrite Hn | rewrite W12x, Z.add_comm];
              apply Z.mod_small; clear - NQ5 NQ7 CAP1 N0; lia. }
          pose proof (LAG i c ps0 E E' R1 R' A1 M1 m1 M' m' ltac:(rewrite YBi; exact YF) HAt HA Hag HLF ltac:(rewrite YBi, HdenE; intros b [<-|[]]; exact XAF)) as AGL.
          pose proof (AGS M1 M' (fun a Ha => AGL a (or_introl Ha)) ltac:(apply XS; rewrite YST; clear; lia)) as XS'. destruct (XS' HN1) as (XB' & XDF' & XA').
          assert (Hsh' : shadow_blk M' nb cap).
          { apply (PTA.shadow_blk_ag M1 M' (in_shadow_of nb cap)); [| clear - CAP1 N0; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ NQ16) | exact Hsh1].
            intros a Ha. apply AGL. right. exists (nb, cap). split; [rewrite YBi, HdenE; left; reflexivity | exact Ha]. }
          assert (Hdef' : L5.defined M' nb cap) by exact (L5.defined_grows M1 M' nb cap (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF) Hdef1).
          eexists. eexists. split; [exact (AMM nb src n (map (Z_to_bv 8) txt) ((nb, cap) :: LB) LK1 (adebit L cr cap) A1 (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
          { unfold CRC.memcpy_pre. split; [exact (REG 10%nat _ nb Y10 UD)|]. split; [exact (REG 11%nat _ src Y11 W11)|]. split; [exact (REG 12%nat _ n Y12 UN)|].
            split; [exact (CRC.dst_in_block L ar C HI HIok _ FF LK1 _ A1 M' _ (sp + CH2.ci_csp ci) 2560 nb cap nb n HH1 (or_introl eq_refl) Hsh' ltac:(clear; lia) ltac:(clear - CAP1; lia) ltac:(clear - N0 Hn26; lia))|].
            split.
            - refine (CRC.src_in_block L ar C HI HIok _ FF LK1 _ A1 M' _ (sp + CH2.ci_csp ci) 2560 bq bm src n (map (Z_to_bv 8) txt) HH1 (or_intror PIN) XA' B1 B2 N0 _).
              unfold n. rewrite Nat2Z.id. apply (L5C.bytes_at_rdn (hl_segs L) M' txt src ltac:(clear - Q0 B1; lia) ltac:(fold n; clear - B2 Q7; lia)). exact XB'.
            - pose proof (Hbap (bq, bm) PIN) as AB. cbn [fst snd] in AB. clear - AB B1 B2 CAP1. lia. }
          intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & Hnew & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          exists []. split; [reflexivity|]. cbv zeta. set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *. pose proof (HagE2g R2) as HagE2. fold E2 in HagE2.
          assert (NB2 : CL5A.uv E2 SIA.nbE = nb) by (rewrite <- NB'; exact (CL5A.uv_var (CH2.ci_nx ci) E' E2 44 (Hag2g R2) ltac:(destruct HV as (_ & _ & HV3 & _); clear - HV3 Y44; lia))).
          assert (UD2 : CL5A.uv E2 (SIA.DST (SIA.chain i)) = nb) by (destruct YC' as [HQ|HQ]; rewrite HQ; exact NB2).
          split; [rewrite Ha0'; unfold CL5A.uv in UD2; rewrite <- UD2; apply Z_to_bv_bv_unsigned|].
          split; [rewrite (DENB E' _ HagE' HCH), NB'; apply incl_refl|].
          assert (WIN : forall w a, In w [(nb, n)] -> L5.in_rng w a -> nb <= a < nb + n) by (intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin).
          split.
          { intros w a Hw Hin. pose proof (WIN w a Hw Hin) as Ha. exists (SIA.DST (SIA.chain i), 0, SIA.NARG (SIA.chain i)). split; [left; reflexivity|].
            unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off]. unfold CL5A.uv in UD, UN. rewrite UD, UN. clear - Ha. lia. }
          split.
          { intros w a Hw Hin (Ka & Kc & _). pose proof (WIN w a Hw Hin) as Ha.
            refine (CHA.obj_not_client L ar LYI LB FF sp (CH.hd_scr G.HDECL) nb cap a RFr (conj NQ5 (conj NQ6 NQ7)) ltac:(clear - CAP1 N0; lia) (CHA.mod8_of_16 _ NQ16) NQ4 NQ1 Hbap Hfap (or_introl _) Kc). clear - Ha CAP1. lia. }
          split; [unfold CHA.curB; rewrite YBj, (DENB E2 _ HagE2 HCH), NB2; exact HH2|]. split; [unfold Cred; rewrite YLj; reflexivity|].
          pose proof HP as (HQ1 & _ & HQ3).
          assert (KNB : forall a, in_shadow_of nb cap a -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
          { intros a Ha. pose proof (SHR nb cap a NQ5 ltac:(clear - CAP1 N0; lia) NQ7 Ha) as SRa. apply HQ1. split; [clear - SRa; lia|]. split; [do 6 right; exists (nb, cap); split; [left; reflexivity | exact Ha]|].
            intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI in NQ6. clear - Hin SRa NQ6 CAP1. lia. }
          assert (AF2 : PMSA.afresh L ar LB FF M2 nb cap).
          { split; [exact Hrng|]. split; [exact Hbap|]. split; [exact Hfap|]. split.
            - intros k Hk. apply (HQ3 (nb + k)); [clear - Hk NQ5 NQ7; lia | left; exists (nb, cap); split; [left; reflexivity | cbn [fst snd]; clear - Hk; lia] | exact (Hdef' k Hk)].
            - exact (PTA.shadow_blk_ag M' M2 (in_shadow_of nb cap) KNB nb cap ltac:(clear - CAP1 N0; lia) ltac:(intros a Ha; exact Ha) (CHA.mod8_of_16 _ NQ16) Hsh'). }
          split.
          { unfold XI. rewrite YCH, Ysj. cbv zeta. rewrite NB2.
            split; [exact (KDEF M' M2 _ _ 2560 _ HP XD')|]. split; [exact XC|]. split; [intros H2; exfalso; exact (H2 eq_refl)|]. split; [intros _; exact AF2|].
            intros _. replace (match SIA.chain i with 1%nat => o + 1 | _ => nb end) with nb by (destruct YC' as [HQ|HQ]; rewrite HQ; reflexivity).
            apply (TKA.bytes_of_copy2 (hl_segs L) M2 nb txt). intros ii Hii. apply Hnew. exact Hii. }

          intros X0 HX0 _. unfold SIA.NEWS_MM in HX0. apply in_app_or in HX0. destruct HX0 as [HX0|[<-|[]]]; [exact (STNEWS E2 A2 m2 M2 _ _ _ HH2 X0 HX0)|].
          assert (GR : exists g, 0 <= g < cap / 8 /\ (nb + n) / 8 = nb / 8 + g).
          { exists (n / 8). pose proof (CL5A.S_add_al nb n (CHA.mod8_of_16 _ NQ16)) as SA8. unfold S in SA8. split; [| clear - SA8; lia].
            pose proof (Z.div_pos n 8 N0 ltac:(clear; lia)) as D0.
            destruct HCH as [(_ & Hn & Hc)|(_ & Hn & Hc)]; rewrite Hc; [rewrite Hn; clear; split; [lia | reflexivity] |].
            replace (8 * (n / 8) + 8) with ((n / 8 + 1) * 8) by (clear; lia). rewrite Z.div_mul by (clear; lia). clear - D0. lia. }
          destruct GR as (g & Hg & Eg).
          eapply CL5A.kzero_intro with (A := (nb + n) / 8 + 2147450880) (N := 1);
            [rewrite CL5A.estart_srl3, (UT E2 HagE2 NB2); reflexivity | apply elit; clear; lia | clear - NQ5 N0; lia | clear - NQ5 NQ7 CAP1 N0; lia | clear - NQ5 NQ7 CAP1 N0; lia |].
          intros jj Hj. replace ((nb + n) / 8 + 2147450880 + jj) with (S nb + g) by (unfold S, SB; rewrite Eg; clear - Hj; lia).
          assert (SHG : in_shadow_of nb cap (S nb + g)) by (apply (CL5A.blk_shadow_in nb cap); [exact (CHA.mod8_of_16 _ NQ16) | clear - CAP1 N0; lia | pose proof (Z.div_le_mono cap (cap + 7) 8 ltac:(clear; lia) ltac:(clear; lia)); clear - Hg H; lia]).
          apply CL5A.byte_vis; [| exact (proj1 (proj2 (proj2 (proj2 (proj2 AF2)))) g Hg)].
          pose proof (SHR nb cap _ NQ5 ltac:(clear - CAP1 N0; lia) NQ7 SHG) as SRa.
          assert (A64 : 0 <= S nb + g < 2 ^ 64) by (clear - SRa; lia).
          assert (ACL : aclient L ar ((nb, cap) :: LB) FF sp 0 (S nb + g)) by (do 6 right; exists (nb, cap); split; [left; reflexivity | exact SHG]).
          exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ m2 sp 0 (S nb + g) HH2 A64 ACL (CL5A.not_stk_shadow_sh L ar LB FF nb cap (S nb + g) RFx NQ5 ltac:(clear - CAP1 N0; lia) NQ4 SHG)). }
    +
      apply andb_prop in X as [X YEX]. apply andb_prop in X as [X YL4]. apply andb_prop in X as [X YSC]. apply andb_prop in X as [X YB]. apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [Y0 Xbase].
      apply Z.eqb_eq in Y0. subst pc. apply CH2.blocks_eqb_eq in YB. apply eqb_prop in YL4.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
      assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
      unfold XI in HXi. destruct HXi as (XD & XC & XS & XAF & XBY).
      refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS SIA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                K DEF0 R r EV Hra Hraok SIA.RETPC i c ps0 _ Xbase _ (FFSnil i) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _); [rewrite LS; exact SIA.ret_at | rewrite FFSnil, YB; exact Xfoot |].
      intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
      pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
      assert (CELL : forall X0, SIA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HX0). }
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS SIA.FFS Cred 0 i E A1 M' m' HA') as Hoff.
      assert (W10 : CL5A.uv E' (EVar 10) = o) by exact (UVE E' (EVar 10) o HagE' eq_refl U10).
      assert (EST : forall k, estart E' (SA SIA.oE k) = o + k) by (intros k; unfold estart; cbn [a_base a_off]; unfold CL5A.uv in W10; unfold SIA.oE; rewrite W10; reflexivity).
      assert (XD' : L5.defined M' o 24) by exact (L5.defined_grows M1 M' o 24 (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF) XD).
      rewrite SCRV in HP.
      assert (U8C : forall a v Aa z, SIA.has (SR.ps_cells ps0) (KWord a 1 v) = true -> estart E' a = Aa -> CL5A.uv E' v = z -> L5.u8_at (hl_segs L) M' Aa z).
      { intros a v Aa z Hc Ha Hz. apply (CL5A.u8_full (hl_segs L) _ Hoff). rewrite <- Hz. exact (CL5A.kword8_elim (hl_segs L) E' _ a v Aa (CELL _ Hc) Ha). }
      assert (U64C : forall a v Aa z, SIA.has (SR.ps_cells ps0) (KWord a 8 v) = true -> estart E' a = Aa -> CL5A.uv E' v = z -> L5.u64_at (hl_segs L) M' Aa z).
      { intros a v Aa z Hc Ha Hz. apply (CL5A.u64_full (hl_segs L) _ Hoff). rewrite <- Hz. exact (CL5A.kword64_elim (hl_segs L) E' _ a v Aa (CELL _ Hc) Ha). }
      assert (ULIT : forall z, 0 <= z < 2 ^ 64 -> CL5A.uv E' (ELit z) = z) by (intros z Hz; unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; exact Hz).
      apply orb_prop in YSC. destruct YSC as [Yi0|YL].
      *
        apply Nat.eqb_eq in Yi0. subst i. cbn [SIA.chain] in XC, YEX. cbn [SIA.BLKS Nat.leb] in YB. unfold CHX in XC.
        apply andb_prop in YEX as [Yo0 Yo1].
        assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; exact HC1). subst cr1.
        assert (HB : CHA.curB LB G.BLS 0 E = LB) by (unfold CHA.curB; rewrite YB; reflexivity). rewrite HB in HH1.
        assert (TXT0 : txt = []) by (destruct txt; [reflexivity | exfalso; unfold n in XC; cbn [length] in XC; clear - XC; lia]).
        apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
        split; [reflexivity|]. split; [reflexivity|]. left. rewrite TXT0. split; [cbn; clear; lia|]. split; [| split; reflexivity].
        cbn [PMSA.str_at_w PMLA.str_at_w]. unfold L5.lstr_short. cbn [length Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r.
        split; [clear; lia|]. split; [pose proof (U8C _ _ _ 0 Yo0 (EST 0) (ULIT 0 ltac:(clear; lia))) as G; rewrite Z.add_0_r in G; exact G|].
        split; [intros k Hk; exfalso; cbn in Hk; clear - Hk; lia | exact (U8C _ _ _ 0 Yo1 (EST 1) (ULIT 0 ltac:(clear; lia)))].
      * apply andb_prop in YL as [YL YC44]. apply andb_prop in YL as [Ys2 YFX]. apply Nat.eqb_eq in Ys2. apply CBA.regions_eqb_eq in YFX.
        specialize (XBY Ys2).
        destruct (Nat.eqb_spec (SIA.chain i) 1) as [YCH1|YCH1].
        --
           rewrite YCH1 in XC, YEX, YFX, XBY, YL4. unfold CHX in XC. cbn [Nat.leb] in YL4. unfold SIA.BLKS in YB. rewrite YL4 in YB.
           apply andb_prop in YEX as [Yo0 Yt].
           destruct NS as (NSR & NSE). specialize (NSE ltac:(clear - XC; lia)).
           assert (W32 : CL5A.uv E' SIA.nsE = n) by (rewrite <- NSE; exact (UVE E' (EVar 32) ns HagE' eq_refl U32)).
           assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite YL4 in HC1; exact HC1). subst cr1.
           assert (HB : CHA.curB LB G.BLS i E = LB) by (unfold CHA.curB; rewrite YB; reflexivity). rewrite HB in HH1.

           assert (BY : L5.bytes_at (hl_segs L) M' (o + 1) txt).
           { apply (CL5A.bytes_same (hl_segs L) M1 M' (o + 1) txt ltac:(clear - O3; lia) ltac:(fold n; clear - O6 XC; lia)); [|exact XBY]. intros a Ha. fold n in Ha.
             apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF (Z_to_bv 64 a)). rewrite YFX. unfold SIA.FEX, SGP.outside. rewrite u64_of_Z by (clear - Ha O3 O6 XC; lia).
             constructor; [|constructor; [|constructor]].
             - rewrite (CL5.estart_lin E' (EVar 2) (-4176) sp ltac:(lin_eval; rewrite <- (proj1 HagE' 2%nat) by (apply Nat.ltb_lt; reflexivity); rewrite U2; clear; lia) ltac:(clear - S2 S3 CL SP1; lia)).
               left. clear - Ha O4 S2 XC. lia.
             - unfold estart. cbn [a_base a_off]. pose proof (UVE E' (SIA.TERM 1%nat) (o + ns + 1) HagE' eq_refl UNS1) as UT. unfold CL5A.uv in UT. rewrite UT, NSE. left. clear - Ha; lia. }
           apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
           split; [reflexivity|]. split; [reflexivity|]. left. split; [unfold n in XC; clear - XC; lia|]. split; [| split; reflexivity].
           cbn [PMSA.str_at_w PMLA.str_at_w]. unfold L5.lstr_short. fold n.
           split; [unfold n in XC; clear - XC; lia|].
           assert (G2 : CL5A.uv E' (EMd Instr.M_MUL (ELit 2) SIA.nsE) = 2 * n).
           { unfold CL5A.uv, SIA.nsE. cbn [edenot]. rewrite AX2S.u_mul64. unfold CL5A.uv, SIA.nsE in W32. cbn [edenot] in W32. rewrite W32. change (bv_unsigned (Z_to_bv 64 2)) with 2. apply Z.mod_small. clear - XC; lia. }
           split; [pose proof (U8C _ _ _ (2 * n) Yo0 (EST 0) G2) as G; rewrite Z.add_0_r in G; exact G|].
           split; [exact BY|].
           apply (U8C _ _ _ 0 Yt); [| exact (ULIT 0 ltac:(clear; lia))]. unfold estart. cbn [a_base a_off]. unfold SIA.oE, SIA.nsE.
           replace (bv_unsigned (edenot E' (EAlu Instr.ALU_ADD (EVar 10) (EVar 32)))) with (o + n); [clear; lia|].
           cbn [edenot]. rewrite AX2S.u_add64. unfold CL5A.uv, SIA.nsE in W10, W32. cbn [edenot] in W10, W32. rewrite W10, W32. symmetry. apply Z.mod_small. clear - O3 O6 XC; lia.
        --
           apply orb_prop in YC44. assert (Y44 : (44 < CC.cp_nx c)%nat) by (destruct YC44 as [Y|Y]; [discriminate Y | apply Nat.ltb_lt in Y; exact Y]). clear YC44.
           assert (C3 : (SIA.chain i <= 3)%nat) by (clear; unfold SIA.chain; destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]]; cbn; lia).
           assert (C0 : SIA.chain i <> 0%nat).
           { intros E0c. clear - Ys2 YL4 E0c. rewrite E0c in YL4. cbn [Nat.leb] in YL4. destruct i as [|[|[|[|[|i]]]]]; cbn in Ys2, E0c, YL4; first [discriminate YL4 | discriminate Ys2 | discriminate E0c]. }
           assert (YC' : SIA.chain i = 2%nat \/ SIA.chain i = 3%nat) by (destruct (Nat.eq_dec (SIA.chain i) 2) as [E2|NE2]; [left; exact E2 | right; clear - C3 C0 YCH1 NE2; lia]).
           assert (YLi : (i <=? 4)%nat = false) by (rewrite YL4; destruct YC' as [HQ|HQ]; rewrite HQ; reflexivity).
           unfold SIA.BLKS in YB. rewrite YLi in YB.
           unfold CHX in XC. pose proof (CH23 _ YC' XC) as HCH. assert (Hn23 : 23 <= n) by (destruct HCH as [(_ & Hn & _)|(_ & Hn & _)]; clear - Hn; lia). destruct (CAPF Hn23) as (_ & CAP1 & CAPB & CAP27).
           specialize (XAF ltac:(apply Nat.leb_le; apply Nat.leb_gt in YLi; clear - YLi; lia)).
           set (nb := CL5A.uv E SIA.nbE) in *.
           pose proof XAF as (Hrng & Hbap & Hfap & Hdef1 & Hsh1). pose proof Hrng as (NQ0 & NQ1 & NQ16 & NQ3 & NQ4 & (NQ5 & NQ6 & NQ7)).
           assert (HdenE : CH2.den E (SIA.BLK (SIA.chain i)) = [(nb, cap)]) by exact (DENB E _ HagE HCH).
           assert (Hcr1 : cr1 = adebit L cr cap) by (unfold Cred in HC1; rewrite YLi in HC1; exact HC1). subst cr1.
           assert (HB : CHA.curB LB G.BLS i E = (nb, cap) :: LB) by (unfold CHA.curB; rewrite YB, HdenE; reflexivity). rewrite HB in HH1.
           assert (NB' : CL5A.uv E' SIA.nbE = nb) by (unfold nb; exact (CL5A.uv_var (CC.cp_nx c) E E' 44 Hag Y44)).
           pose proof (LAG i c ps0 E E' R1 R' A1 M1 m1 M' m' ltac:(rewrite YB; unfold SIA.BLKS in Xfoot; rewrite YLi in Xfoot; exact Xfoot) HAt HA Hag HLF ltac:(rewrite YB, HdenE; intros b [<-|[]]; exact XAF)) as AGL.
           replace (match SIA.chain i with 1%nat => o + 1 | _ => nb end) with nb in XBY by (destruct YC' as [HQ|HQ]; rewrite HQ; reflexivity).

           assert (UTn : CL5A.uv E' (SIA.TERM (SIA.chain i)) = nb + n).
           { assert (W12x : bv_unsigned (ev E' 12) = n) by (rewrite <- (proj1 HagE' 12%nat) by (apply Nat.ltb_lt; reflexivity); exact U12).
             pose proof NB' as NBx. unfold CL5A.uv, SIA.nbE in NBx. cbn [edenot] in NBx.
             destruct HCH as [(HQ & Hn & _)|(HQ & Hn & _)]; rewrite HQ; cbn [SIA.TERM]; unfold CL5A.uv, SIA.nbE, SIA.nE; cbn [edenot]; rewrite AX2S.u_add64, NBx; [change (bv_unsigned (Z_to_bv 64 23)) with 23; rewrite Hn | rewrite W12x, Z.add_comm];
               apply Z.mod_small; clear - NQ5 NQ7 CAP1 N0; lia. }
           assert (CELLS : L5.u64_at (hl_segs L) M' o (cap + 1) /\ L5.u64_at (hl_segs L) M' (o + 8) n /\ L5.u64_at (hl_segs L) M' (o + 16) nb /\ L5.u8_at (hl_segs L) M' (nb + n) 0).
           { assert (W12 : CL5A.uv E' SIA.nE = n) by exact (UVE E' (EVar 12) n HagE' eq_refl U12).
             destruct HCH as [(HQ & Hn & Hc)|(HQ & Hn & Hc)]; rewrite HQ in YEX; cbn [SIA.exit_cells] in YEX;
               apply andb_prop in YEX as [YEX Yt]; apply andb_prop in YEX as [YEX Y16]; apply andb_prop in YEX as [Y00 Y8].
             - rewrite Hc, Hn. split; [pose proof (U64C _ _ _ 27 Y00 (EST 0) (ULIT 27 ltac:(clear; lia))) as G; rewrite Z.add_0_r in G; exact G|].
               split; [exact (U64C _ _ _ 23 Y8 (EST 8) (ULIT 23 ltac:(clear; lia)))|]. split; [exact (U64C _ _ _ nb Y16 (EST 16) NB')|].
               rewrite <- Hn. apply (U8C _ _ _ 0 Yt); [| exact (ULIT 0 ltac:(clear; lia))]. unfold estart. cbn [a_base a_off]. unfold CL5A.uv in NB'. rewrite NB', Hn. reflexivity.
             - split; [| split; [exact (U64C _ _ _ n Y8 (EST 8) W12) | split; [exact (U64C _ _ _ nb Y16 (EST 16) NB') |]]].
               + pose proof (U64C _ _ _ (cap + 1) Y00 (EST 0)) as G. rewrite Z.add_0_r in G. apply G. rewrite Hc.
                 unfold CL5A.uv, SIA.R9, SIA.nE. cbn [edenot]. rewrite AX2S.u_add64, AX2S.u_mul64, AX2S.u_srl64. rewrite <- (proj1 HagE' 12%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U12.
                 change (bv_unsigned (Z_to_bv 64 8)) with 8. change (bv_unsigned (Z_to_bv 64 3)) with 3. change (2 ^ (3 mod 64)) with 8. change (bv_unsigned (Z_to_bv 64 9)) with 9.
                 pose proof (Z.div_pos n 8 N0 ltac:(clear; lia)) as D0. pose proof (Z.div_le_mono n (2 ^ 26) 8 ltac:(clear; lia) ltac:(clear - Hn26; lia)) as D1. change (2 ^ 26 / 8) with 8388608 in D1.
                 rewrite (Z.mod_small (8 * (n / 8))) by (clear - D0 D1; lia). rewrite Z.mod_small by (clear - D0 D1; lia). clear; lia.
               + apply (U8C _ _ _ 0 Yt); [| exact (ULIT 0 ltac:(clear; lia))]. unfold estart. cbn [a_base a_off]. pose proof UTn as UT3. rewrite HQ in UT3. cbn [SIA.TERM] in UT3. unfold CL5A.uv in UT3. rewrite UT3. clear; lia. }
           destruct CELLS as (C00 & C08 & C16 & CT).

           assert (BY : L5.bytes_at (hl_segs L) M' nb txt).
           { apply (CL5A.bytes_same (hl_segs L) M1 M' nb txt NQ5 ltac:(fold n; clear - NQ7 CAP1; lia)); [|exact XBY]. intros a Ha. fold n in Ha.
             apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF (Z_to_bv 64 a)). rewrite YFX. unfold SIA.FEX, SGP.outside. rewrite u64_of_Z by (clear - Ha NQ5 NQ7 CAP1; lia).
             constructor; [|constructor; [|constructor]].
             - rewrite (CL5.estart_lin E' (EVar 2) (-4176) sp ltac:(lin_eval; rewrite <- (proj1 HagE' 2%nat) by (apply Nat.ltb_lt; reflexivity); rewrite U2; clear; lia) ltac:(clear - S2 S3 CL SP1; lia)).
               left. clear - Ha NQ4 S2 CAP1. lia.
             - destruct HCH as [(HQ & Hn & _)|(HQ & _)]; rewrite HQ; unfold estart; cbn [a_base a_off].
               + unfold CL5A.uv in NB'. rewrite NB'. left. clear - Ha Hn. lia.
               + pose proof UTn as UT3. rewrite HQ in UT3. unfold CL5A.uv in UT3. first [rewrite UT3 | cbn [SIA.TERM] in UT3; rewrite UT3]. left. clear - Ha. lia. }
           apply (Hcont fx' R' M' model2 ((nb, cap) :: LB) (adebit L cr cap) LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
           split; [reflexivity|]. split; [reflexivity|]. right. split; [unfold n in Hn23; clear - Hn23; lia|]. exists nb. cbv zeta. fold n. fold cap.
           split; [| split; [| split; reflexivity]].
           { cbn [PMSA.str_at_w PMLA.str_at_w]. fold n. split; [| exact (proj1 CAP1)]. unfold L5.lstr_long. fold n.
             split; [exact CAPB|]. split; [exact C00|]. split; [exact C08|]. split; [exact C16|]. split; [exact BY | exact CT]. }
           split; [exact Hrng|]. split; [exact Hbap|]. split; [exact Hfap|]. split; [exact (L5.defined_grows M1 M' nb cap (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF) Hdef1)|].
           apply (PTA.shadow_blk_ag M1 M' (in_shadow_of nb cap)); [| clear - CAP1 N0; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ NQ16) | exact Hsh1].
           intros a Ha. apply AGL. right. exists (nb, cap). split; [rewrite YB, HdenE; left; reflexivity | exact Ha].
  - exact CP0.
  -
    assert (CLV : forall scr a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros scr a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp scr a HH Ha Hc Hs)).
    assert (VO : CL5A.visr (ahid A model) o 24).
    { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + k) RFx Ofr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSO : forall j, 0 <= j < 3 -> ahid A model (Z_to_bv 64 (S o + j)) = false).
    { intros j Hj. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o 24 (S o + j) RFx Ofr ltac:(clear; lia) (CL5A.shreg_in_shadow o 3 (S o + j) O8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
      exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4176) 4176).
    { intros k Hk. apply (CLV 0); [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DOv : L5.defined Mv o 24) by (apply (CL5A.defined_vis _ M o 24 VO); exact DO).
    assert (DSv : L5.defined Mv (sp - 4176) 4176) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (SZv : forall k, 0 <= k < 24 -> shadow_zero Mv (o + k) 1).
    { intros k Hk j Hj. rewrite (CL5A.S_add_al o k O8). replace (S o + k / 8 + j) with (S o + k / 8) by (clear - Hj; lia).
      pose proof (Z.div_pos k 8 ltac:(clear - Hk; lia) ltac:(clear; lia)) as G0. pose proof (Z.div_lt_upper_bound k 8 3 ltac:(clear; lia) ltac:(clear - Hk; lia)) as G1.
      apply CL5A.byte_vis; [exact (VSO (k / 8) ltac:(clear - G0 G1; lia)) | exact (Osh (k / 8) ltac:(clear - G0 G1; lia))]. }
    assert (REGS : regs_ok E0 (CC.cp_regs (nth i0 G.CPS G.cp0)) R).
    { intros rr. unfold sr_get. destruct (bv_eqb rr 0) eqn:Hr0.
      - assert (rr = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; clear - Hr0; lia). subst rr. unfold getr. rewrite Hr0. destruct i0 as [|[|[|[|i0]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | exfalso; clear - Hi0; lia].
      - unfold E0, reg_ev. rewrite <- (ridx_roundtrip rr) at 1. pose proof (ridx_range rr) as Hlt. set (nn := ridx rr) in *. clearbody nn.
        unfold CHX in HCH0.
        destruct i0 as [|[|[|[|i0]]]]; [| | | | exfalso; clear - Hi0; lia];
          [ let l := eval vm_compute in (CC.cp_regs (nth 0 G.CPS G.cp0)) in change (CC.cp_regs (nth 0 G.CPS G.cp0)) with l
          | let l := eval vm_compute in (CC.cp_regs (nth 1 G.CPS G.cp0)) in change (CC.cp_regs (nth 1 G.CPS G.cp0)) with l
          | let l := eval vm_compute in (CC.cp_regs (nth 2 G.CPS G.cp0)) in change (CC.cp_regs (nth 2 G.CPS G.cp0)) with l
          | let l := eval vm_compute in (CC.cp_regs (nth 3 G.CPS G.cp0)) in change (CC.cp_regs (nth 3 G.CPS G.cp0)) with l ];
          (do 32 (destruct nn as [|nn]; [cbn [nth edenot ev Nat.ltb Nat.leb Nat.sub]; first [reflexivity | etransitivity; [exact Ha2 | f_equal; clear - HCH0 NS; lia]] |]); exfalso; clear - Hlt; lia). }
    assert (COMMON : Forall (kentry_ok (hl_segs L) E0 Mv) SIA.KNC).
    { let l := eval vm_compute in SIA.KNC in change SIA.KNC with l. repeat (apply Forall_cons); [.. | apply Forall_nil].
      + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      + eapply CL5.kunk_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DOv].
      + eapply CL5.kwr_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DOv].
      + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO S2 S3 SP1; lia].
      + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact O8].
      + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 3 o); [exact U10 | clear; lia | clear - O3 O6; lia |]. intros j Hj. apply CL5A.byte_vis; [exact (VSO j Hj) | exact (Osh j Hj)].
      + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 1 (o + 8)); [exact (UOK 8 ltac:(clear; lia) ltac:(clear; lia)) | clear; lia | clear - O3 O6; lia | exact (SZv 8 ltac:(clear; lia))].
      + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 1 (o + 16)); [exact (UOK 16 ltac:(clear; lia) ltac:(clear; lia)) | clear; lia | clear - O3 O6; lia | exact (SZv 16 ltac:(clear; lia))].
      + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 24); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
      + eapply CL5.kunk_intro with (A := sp - 4176) (N := 4176); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DSv].
      + eapply CL5.kwr_intro with (A := sp - 4176) (N := 4176); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DSv].
      + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
      + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
      + eapply CL5.kdisj_intro with (A1 := sp - 4176) (N1 := 4176) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia]. }
    split; [exact REGS|]. unfold know_ok. unfold CHX in HCH0.
    destruct i0 as [|[|[|[|i0]]]]; [| | | | exfalso; clear - Hi0; lia].
    +   change (nth 0 G.CPS G.cp0) with G.cp0. rewrite (proj1 SIA.knc_ok). apply Forall_app. split; [exact COMMON|].
      let l := eval vm_compute in (skipn 15 (CC.cp_know G.cp0)) in change (skipn 15 (CC.cp_know G.cp0)) with l. apply Forall_cons; [|apply Forall_nil].
      apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 1 (o + 1)); [exact (UOK 1 ltac:(clear; lia) ltac:(clear; lia)) | clear; lia | clear - O3 O6; lia | exact (SZv 1 ltac:(clear; lia))].
    +   change (nth 1 G.CPS G.cp0) with G.cp1. rewrite (proj1 (proj2 SIA.knc_ok)). apply Forall_app. split; [exact COMMON|].
      let l := eval vm_compute in (skipn 15 (CC.cp_know G.cp1)) in change (skipn 15 (CC.cp_know G.cp1)) with l. destruct NS as (NSR & NSE). specialize (NSE ltac:(clear - HCH0; lia)).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * eapply CL5.krange_intro with (v := ns); [lin_eval; rw_atoms; clear; lia | clear - NSR; lia | clear - NSE HCH0; lia].
      * apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 1 (o + ns + 1)); [exact UNS1 | clear; lia | clear - O3 O6 NSR; lia | replace (o + ns + 1) with (o + (ns + 1)) by (clear; lia); exact (SZv (ns + 1) ltac:(clear - NSR; lia))].
    +   change (nth 2 G.CPS G.cp0) with G.cp2. rewrite (proj1 (proj2 (proj2 SIA.knc_ok))). apply Forall_app. split; [exact COMMON|].
      let l := eval vm_compute in (skipn 15 (CC.cp_know G.cp2)) in change (skipn 15 (CC.cp_know G.cp2)) with l. apply Forall_cons; [|apply Forall_nil].
      eapply CL5.krange_intro with (v := n); [lin_eval; rw_atoms; clear; lia | clear - N0 Hn26; lia | clear - HCH0; lia].
    +   change (nth 3 G.CPS G.cp0) with G.cp3. rewrite (proj2 (proj2 (proj2 SIA.knc_ok))). apply Forall_app. split; [exact COMMON|].
      let l := eval vm_compute in (skipn 15 (CC.cp_know G.cp3)) in change (skipn 15 (CC.cp_know G.cp3)) with l. apply Forall_cons; [|apply Forall_nil].
      eapply CL5.krange_intro with (v := n); [lin_eval; rw_atoms; clear; lia | clear - N0 Hn26; lia | clear - HCH0 Hn26; lia].
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. rewrite FFSnil, BLS0. cbn [app CHA.denF CH2.den map length].
      split; [exact HH|]. split; [apply incl_refl|]. split; [unfold Cred; destruct i0 as [|[|[|[|i0]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | exfalso; clear - Hi0; lia] | exact Hroom].
    + unfold XI. rewrite ST0, CHN0. split; [exact DO|]. split; [exact HCH0|]. split; [intros _ _; split; [exact SBY | split; [exact SDEF | exact SACC]]|].
      split; [intros H5; exfalso; destruct i0 as [|[|[|[|i0]]]]; [discriminate H5 | discriminate H5 | discriminate H5 | discriminate H5 | clear - Hi0; lia] | intros H2; discriminate H2].
  - exact Hfp.
Qed.

End StrInitOk.
