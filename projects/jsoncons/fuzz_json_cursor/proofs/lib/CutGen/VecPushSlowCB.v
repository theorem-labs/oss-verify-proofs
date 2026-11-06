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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_vec_push_slow_cboth_T Cut_vec_push_slow_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_vec_push_slow_cboth.
Module GT := Cut_vec_push_slow_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module VSA.
Definition PC_OPNEW : Z := 1363704.
Definition PC_ADEL : Z := 727788.
Definition PC_MEMCPY : Z := 520756.
Definition PC_ANEW : Z := 810224.
Definition PC_OPDEL : Z := 980676.
Definition RETPC : Z := 808608.
Definition SBz : Z := 2147450880.
Definition oE := EVar 10. Definition xaE := EVar 11. Definition bE := EVar 32. Definition capE := EVar 33. Definition shvE := EVar 34. Definition xvE := EVar 35. Definition nbE := EVar 44.
Definition SIZE2 : expr := EMd Instr.M_MUL (ELit 2) capE.
Definition BOLD : list (expr * expr) := [(bE, capE)].
Definition BNEW : list (expr * expr) := [(nbE, SIZE2)].
Definition BBOTH : list (expr * expr) := [(nbE, SIZE2); (bE, capE)].
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz)].
Definition SHN (n : expr) : expr := CHA.SRL3 (APC.eaddz n 7).
Definition WSHB : list SGP.region := [(CHA.SRL3 bE, SBz, SHN capE)].
Definition WSHN : list SGP.region := [(CHA.SRL3 nbE, SBz, SHN SIZE2)].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.

Definition news_of (nb : nat) (cj : CC.cutpoint) : list kentry := List.filter (fun X => negb (APC.kentry_vars_lt nb X)) (CC.cp_know cj).
Definition HAND : list kentry :=
  [KWord (SA (CHA.SRL3 (EAlu Instr.ALU_ADD capE nbE)) SBz) 1 (ELit 0);
   KDisj (SA (CHA.SRL3 nbE) SBz) (SHN SIZE2) (SA (CHA.SRL3 oE) SBz) (ELit 3);
   KDisj (SA (CHA.SRL3 nbE) SBz) (SHN SIZE2) (SA (CHA.SRL3 xaE) SBz) (ELit 1);
   KDisj (SA (CHA.SRL3 nbE) SBz) (SHN SIZE2) (SA (CHA.SRL3 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-88)))) SBz) (ELit 5)].
Definition NEWS_MEMCPY : list kentry := STAT ++ [KBlob (SA nbE 0) capE 0].
Definition oshz (cells : list kentry) : bool := has cells (KZero (SA (CHA.SRL3 oE) SBz) (ELit 3)).
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      match CH2.ret_of G.RETS i k with
      | Some j =>
          match nth_error G.CPS j with
          | Some cj =>
              if Z.eqb pc PC_OPNEW then
                let nx := (CC.cp_nx cj - APC.NCS)%nat in let news := news_of (nx + 4) cj in
                (Z.eqb (SR.ps_pc ps) PC_OPNEW && Nat.leb i 1 && Nat.eqb j (i + 2) && Nat.eqb nx 40 && CH2.blocks_eqb (nth i G.BLS []) BOLD && CH2.blocks_eqb (nth j G.BLS []) BBOTH
                 && CHA.foot_chk GT.NF G.HDECL c BOLD []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4112 0 BOLD [] [] news None c ps cj BOLD [] BBOTH [])
                 && CRB.fresh_news_ok 65536 7028736 G.HDECL GT.SCELLS GT.GLO GT.GHI cells nx BOLD [] (nx + 4) SIZE2 (List.filter (fun X => negb (has HAND X)) news)
                 && CL.ps_reg_is ps 10 SIZE2)%bool
              else if Z.eqb pc PC_ADEL then
                (Z.eqb (SR.ps_pc ps) PC_ADEL && Nat.leb 2 i && Nat.leb i 3 && Nat.eqb j (i + 2) && Nat.ltb 44 (CC.cp_nx c) && CH2.blocks_eqb (nth i G.BLS []) BBOTH && CH2.blocks_eqb (nth j G.BLS []) BBOTH
                 && CHA.foot_chk GT.NF G.HDECL c BBOTH []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4128 0 BBOTH [] WSHB STAT None c ps cj BBOTH [] BBOTH [])
                 && CL.ps_reg_is ps 10 oE && has cells (KWord (SA oE 0) 8 bE) && has cells (KWord (SA oE 8) 8 (EAlu Instr.ALU_ADD bE capE)) && has cells (KWord (SA oE 16) 8 (EAlu Instr.ALU_ADD bE capE))
                 && oshz cells)%bool
              else if Z.eqb pc PC_MEMCPY then
                (Z.eqb (SR.ps_pc ps) PC_MEMCPY && Nat.leb 4 i && Nat.leb i 5 && Nat.eqb j (i + 2) && Nat.ltb 44 (CC.cp_nx c) && CH2.blocks_eqb (nth i G.BLS []) BBOTH && CH2.blocks_eqb (nth j G.BLS []) BBOTH
                 && CHA.foot_chk GT.NF G.HDECL c BBOTH []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 2560 0 BBOTH [] [(nbE, 0, capE)] NEWS_MEMCPY (Some nbE) c ps cj BBOTH [] BBOTH [])
                 && CL.ps_reg_is ps 10 nbE && CL.ps_reg_is ps 11 bE && CL.ps_reg_is ps 12 capE && has cells (KBlob (SA bE 0) capE 0))%bool
              else if Z.eqb pc PC_ANEW then
                (Z.eqb (SR.ps_pc ps) PC_ANEW && Nat.leb 6 i && Nat.leb i 7 && Nat.eqb j (i + 2) && Nat.ltb 44 (CC.cp_nx c) && CH2.blocks_eqb (nth i G.BLS []) BBOTH && CH2.blocks_eqb (nth j G.BLS []) BBOTH
                 && CHA.foot_chk GT.NF G.HDECL c BBOTH []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4128 0 BBOTH [] WSHN STAT None c ps cj BBOTH [] BBOTH [])
                 && CL.ps_reg_is ps 10 oE && CL.ps_reg_is ps 11 (EAlu Instr.ALU_ADD capE (ELit 1))
                 && has cells (KWord (SA oE 0) 8 nbE) && has cells (KWord (SA oE 16) 8 (EAlu Instr.ALU_ADD SIZE2 nbE)) && oshz cells)%bool
              else if Z.eqb pc PC_OPDEL then
                (Z.eqb (SR.ps_pc ps) PC_OPDEL && Nat.leb 8 i && Nat.leb i 9 && Nat.eqb j (i + 2) && Nat.ltb 44 (CC.cp_nx c) && CH2.blocks_eqb (nth i G.BLS []) BBOTH && CH2.blocks_eqb (nth j G.BLS []) BNEW
                 && CHA.foot_chk GT.NF G.HDECL c BBOTH []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4096 0 BNEW [] [] STAT None c ps cj BBOTH [] BNEW [])
                 && CL.ps_reg_is ps 10 bE)%bool
              else false
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c BNEW [] && Nat.leb 10 i && Nat.leb i 11 && CH2.blocks_eqb (nth i G.BLS []) BNEW
           && CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD capE nbE) (ELit 1))
           && has cells (KWord (SA oE 0) 8 nbE) && has cells (KWord (SA oE 8) 8 (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD capE nbE) (ELit 1))) && has cells (KWord (SA oE 16) 8 (EAlu Instr.ALU_ADD SIZE2 nbE))
           && has cells (KBlob (SA nbE 0) capE 0) && has cells (KWord (SA (EAlu Instr.ALU_ADD capE nbE) 0) 1 xvE)
           && Nat.ltb 44 (CC.cp_nx c))%bool
      end
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

End VSA.

Section VecPushSlowOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis OPNEW_OK : PMSA.opnew_specA L ar HI VSA.PC_OPNEW.
Hypothesis ADEL_OK : PMSA.annotate_delete_spec L ar HI VSA.PC_ADEL.
Hypothesis ANEW_OK : PMSA.annotate_new_spec L ar HI VSA.PC_ANEW.
Hypothesis OPDEL_OK : PMSA.opdel_specA L ar HI VSA.PC_OPDEL.

Lemma FFSnil : forall i, nth i VSA.FFS [] = [].
Proof. intros i. unfold VSA.FFS. do 13 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Definition hid (P : Prop) : Prop := P.
Definition al (x m : Z) : Prop := x mod m = 0.
Definition eqz (x y : Z) : Prop := x = y.
Definition ltm (x m v : Z) : Prop := x mod m < v.
Lemma byte_mod : forall x, Z_to_bv 8 (x mod 256) = Z_to_bv 8 x.
Proof. intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Zmod_mod. Qed.

Theorem vec_push_slow_ok : PMSA.vec_push_slow_spec L ar HI 808308.
Proof.
  intros LB FF LK cr A o b cap xa x sp r st. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & Hvec & HlenEq & Hbytes & Hx & Hxfr & Hxacc & Hxo & Hcred & Hcap2 & Hstksh & Hcap4) Hcont.
  destruct Hvec as ((Hw0 & Hw8 & Hw16) & Hofr & Ho8 & Hosh & HinLB & _ & Hcap & Hshc).
  unfold PMSA.a0, PMSA.a1, PMSA.u64, PMSA.u8, PMSA.VSLOW_SCR, PMSA.ainfr, PMSA.acobj, PMSA.stksh in *.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYH : hl_img_lo L <= 65536 /\ 7028736 <= hl_img_hi L) by (rewrite ILO, IHI; lia).

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (b, cap) HinLB) as (BR & Bdef & Bsa & Bap & Bfap). cbn [fst snd] in BR, Bdef, Bsa, Bap, Bfap.
  pose proof (PmHeapIfaceA.aio_small_high _ _ _ _ _ HIok _ _ _ _ _ _ _ HH (b, cap) HinLB ltac:(cbn [snd]; lia)) as BHI. cbn [fst] in BHI.
  destruct BR as (B0 & B1 & B16 & B3 & B4 & (B5 & B6 & B7)).
  destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ WF) as (ND1 & ND2).
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16). pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as TOP47.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  change (al sp 16) in S1. change (al o 8) in Ho8. change (al b 16) in B16. change (al (ahl_ceil ar) 8) in C8. change (al (ar_sptop ar) 16) in SP16.
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Hofr ltac:(lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  destruct (CL5A.acobj_rng L ar LB FF sp xa 1 RFx ltac:(lia) Hxfr ltac:(lia)) as (X3 & X6 & X5 & X1 & X4).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  assert (B1' : hl_img_hi L <= b) by (rewrite ILO, IHI in *; lia). clear B1 B6.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (xa + 1 <= 2147446784 \/ 17594333495296 <= xa)) in X5.
  change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7. change (hid (xa + 1 <= o \/ o + 24 <= xa)) in Hxo.
  change (hid (ar_fs ar + 32 <= xa \/ ahl_ceil ar <= xa)) in X1. change (hid (xa + 1 <= ahl_ceil ar \/ sp <= xa)) in X4.
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  assert (RFr : CHA.rng_facts L ar (lb_remove b LB) FF).
  { apply (CHA.rng_incl L ar LB FF); [exact RFx | intros y Hy; exact (L5C.in_lb_remove b y LB Hy) | apply incl_refl]. }
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.

  assert (SHV : exists shv, byte_at M (S xa) shv /\ (shv = 0 \/ (1 <= shv <= 7 /\ ltm xa 8 shv))).
  { destruct (Hxacc xa ltac:(lia)) as [H0|(v & Hv & Hr & Hl)]; [exists 0; split; [exact H0 | left; reflexivity] | exists v; split; [exact Hv | right; split; assumption]]. }
  destruct SHV as (shv & Hshv & Hshr).
  assert (SHVR : 0 <= shv <= 7) by (destruct Hshr as [->|[? _]]; lia). change (hid (shv = 0 \/ 1 <= shv <= 7 /\ ltm xa 8 shv)) in Hshr.
  pose proof (Z.mod_pos_bound x 256 ltac:(lia)) as XM.
  assert (Hxm : L5.u8_at (hl_segs L) M xa (x mod 256)) by (unfold L5.u8_at; rewrite byte_mod; exact Hx).
  remember (x mod 256) as xm eqn:Exm. change (eqz xm (x mod 256)) in Exm.

  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [b; cap; shv; xm] 0))) (fun id => nth id [map (Z_to_bv 8) st] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 xa) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 b) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 cap) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 shv) by reflexivity.
  assert (V35 : ev E0 35 = Z_to_bv 64 xm) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = xa) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = b) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = cap) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = shv) by (rewrite V34; apply u64_of_Z; lia).
  assert (U35 : bv_unsigned (ev E0 35) = xm) by (rewrite V35; apply u64_of_Z; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 8192) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  set (WW := [(o, 24)] : list L5.range).
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar (lb_remove b LB) FF sp _ o 24 a RFr Hofr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }

  assert (SP8 : (sp - 88) mod 8 = 0).
  { unfold al in S1. clear - S1. pose proof (Z_div_mod_eq_full sp 16) as D. rewrite S1, Z.add_0_r in D. rewrite D. replace (16 * (sp / 16) - 88) with ((2 * (sp / 16) - 11) * 8) by lia. apply Z_mod_mult. }
  assert (AL8192 : (sp - 8192) mod 8 = 0).
  { unfold al in S1. clear - S1. pose proof (Z_div_mod_eq_full sp 16) as D. rewrite S1, Z.add_0_r in D. rewrite D. replace (16 * (sp / 16) - 8192) with ((2 * (sp / 16) - 1024) * 8) by lia. apply Z_mod_mult. }
  assert (SHR : forall p n a, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 -> in_shadow_of p n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  assert (SSH : forall a, in_shadow_of (sp - 88) 40 a -> 0 <= a < 2 ^ 64 /\ aclientw L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros a Ha. pose proof (SHR (sp - 88) 40 a ltac:(clear - S2 CL; lia) ltac:(clear; lia) ltac:(clear - S3 SP1; lia) Ha) as SRa. destruct Ha as [A1 A2].
    split; [clear - SRa; lia|]. split.
    - right; right; right; right; left. split; [|unfold S in *; clear - A2 S3 SP1 CL; lia]. apply (Z.le_trans _ (S (sp - 88))); [|exact A1]. unfold S. apply Z.add_le_mono_r. apply Z.div_le_mono; [lia|]. clear - S2. lia.
    - intros _. unfold S, al in *. apply Z.mod_divide in SP16; [|clear; lia]. destruct SP16 as [q Hq].
      assert (E1 : ar_sptop ar / 8 = 2 * q) by (rewrite Hq; replace (q * 16) with ((2 * q) * 8) by lia; apply Z.div_mul; lia).
      assert (E2 : (sp - 88 + 40 - 1) / 8 < 2 * q) by (apply Z.div_lt_upper_bound; [lia|]; clear - S3 Hq; lia). clear - A2 E1 E2. lia. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar (lb_remove b LB) FF sp G.HDECL a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[<-|[<-|[]]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; unfold CHA.sclientA.
    - cbv beta iota in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia.
      pose proof (CL5A.shreg_in_shadow o 3 a Ho8 ltac:(lia) ltac:(unfold SB; lia)) as SH. change (8 * 3) with 24 in SH.
      destruct (CL5A.infr_sh_wok L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) o 24 a RFr Hofr ltac:(lia) SH) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
    - cbv beta iota in Ha. unfold estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U11 in Ha. rewrite u64_of_Z in Ha by lia.
      destruct (CL5A.acobj_wok L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) xa 1 a RFr CSP Hxfr ltac:(lia)) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
    - cbv beta iota in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U11 in Ha. rewrite u64_of_Z in Ha by lia.
      pose proof (CL5A.shreg1_in_shadow xa a ltac:(unfold SB; lia)) as SH.
      destruct (CL5A.acobj_sh_wok L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) xa 1 a RFr CSP Hxfr ltac:(lia) SH) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
    - cbv beta iota in Ha. rewrite CL5A.estart_srl3' in Ha. unfold elenZ in Ha.
      replace (CL5A.uv E0 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-88)))) with (sp - 88) in Ha by (symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia]).
      cbn [edenot] in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      pose proof (CL5A.shreg_in_shadow (sp - 88) 5 a SP8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 5) with 40 in SH.
      destruct (SSH a SH) as (G1 & G2 & G3). split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. lia. }

  set (Cred := fun (i : nat) (_ : env) (cr1 : credit) => if Nat.leb i 1 then cr1 = cr else cr1 = adebit L cr (2 * cap)).
  set (AFP := fun (nb : Z) => ablock_range L ar nb (2 * cap) /\ blocks_apart nb (2 * cap) ((b, cap) :: lb_remove b LB) /\ fframes_apart nb (2 * cap) FF /\ 17594333495296 <= nb).
  set (XI := fun (i : nat) (E : env) (_ : list (Z * Z)) (M1 : word -> option byte) (_ : Model) =>
               let nb := CL5A.uv E (EVar 44) in
               if Nat.leb i 1 then shadow_cont M1 b cap cap
               else if Nat.leb i 5 then AFP nb /\ L5.defined M1 nb (2 * cap) /\ shadow_blk M1 nb (2 * cap) /\ shadow_cont M1 b cap cap
               else if Nat.leb i 7 then AFP nb /\ L5.defined M1 nb (2 * cap) /\ shadow_blk M1 nb (2 * cap)
               else AFP nb /\ L5.defined M1 nb (2 * cap) /\ shadow_cont M1 nb (2 * cap) (cap + 1)).

  assert (KSH : forall p n a, CL5A.acobj ar FF sp p n -> 0 < n -> in_shadow_of p n a -> CHA.akept L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) WW a).
  { intros p n a Hp Hn Ha. destruct (CL5A.acobj_sh_wok L ar _ FF sp (CH.hd_scr G.HDECL) p n a RFr CSP Hp Hn Ha) as (G1 & G2 & _).
    destruct (CL5A.acobj_rng L ar LB FF sp p n RFx CSP Hp Hn) as (P3 & P6 & _). pose proof (SHR p n a P3 Hn P6 Ha) as SR.
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin SR O5. lia. }
  assert (KXA : CHA.akept L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) WW xa).
  { destruct (CL5A.acobj_wok L ar _ FF sp (CH.hd_scr G.HDECL) xa 1 xa RFr CSP Hxfr ltac:(clear; lia)) as (G1 & G2 & _).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in Hxo. clear - Hin Hxo. lia. }
  assert (KSTK : forall a, S (sp - 8192) <= a < S (sp - 8192) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 8192)) / 8 -> CHA.akept L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. unfold al in C8. destruct (PTA.stksh_rng ar sp 8192 a ltac:(clear - S2; lia) AL8192 C8 (proj2 S4) TOP47 ltac:(clear - CL; lia) Ha) as (G1 & G2).
    split; [exact G1|]. split; [right; right; right; right; left; exact G2|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
    unfold in_shadow_of, S, SB in G2. unfold hid in O5. clear - Hin G2 O5 CL. lia. }

  assert (NOFOOT : forall LBown a, Forall (fun bb => 17594333495296 <= fst bb) LBown -> 2147450880 <= a < 17594333495296 -> ~ CHA.afoot_sem sp G.HDECL WW LBown [] a).
  { intros LBown a HF Ha [X|[X|[X|[X|X]]]].
    - rewrite SCRV in X. clear - X Ha S2 CL. lia.
    - destruct X as (w & [<-|[]] & Hin). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin Ha O5. lia.
    - destruct X as (bb & Hbb & Hin). pose proof (proj1 (Forall_forall _ _) HF bb Hbb) as G0. cbv beta in G0. clear - Hin Ha G0. lia.
    - destruct X as (f & [] & _).
    - destruct X as (f & [] & _). }
  assert (NOGOTO : forall i c kk ps j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TGoto j sg) -> False).
  { intros i c kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ VSA.leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }

  assert (DEN1 : forall E, env_agree GT.NF E0 E -> CH2.den E VSA.BOLD = [(b, cap)]).
  { intros E HagE. unfold CH2.den, VSA.BOLD, VSA.bE, VSA.capE. cbn [map fst snd edenot]. rewrite <- (proj1 HagE 32%nat), <- (proj1 HagE 33%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U32, U33. reflexivity. }
  assert (USZ : forall E, env_agree GT.NF E0 E -> elenZ E VSA.SIZE2 = 2 * cap).
  { intros E HagE. unfold elenZ, VSA.SIZE2, VSA.capE. apply CL5.u_lin; [lin_eval; rw_atoms|]; rewrite <- ?(proj1 HagE 33%nat) by (apply Nat.ltb_lt; reflexivity); rewrite ?U33; clear - Hcap Hcap2; lia. }
  assert (DEN2 : forall E, env_agree GT.NF E0 E -> CH2.den E VSA.BBOTH = [(CL5A.uv E (EVar 44), 2 * cap); (b, cap)]).
  { intros E HagE. unfold CH2.den, VSA.BBOTH, VSA.bE, VSA.capE, VSA.nbE, CL5A.uv. cbn [map fst snd]. f_equal; [f_equal; exact (USZ E HagE)|].
    cbn [edenot]. rewrite <- (proj1 HagE 32%nat), <- (proj1 HagE 33%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U32, U33. reflexivity. }
  assert (DEN3 : forall E, env_agree GT.NF E0 E -> CH2.den E VSA.BNEW = [(CL5A.uv E (EVar 44), 2 * cap)]).
  { intros E HagE. unfold CH2.den, VSA.BNEW, VSA.nbE, CL5A.uv. cbn [map fst snd]. f_equal. f_equal. exact (USZ E HagE). }

  assert (MAIN : forall i c, nth_error G.CPS i = Some c -> (i < 2)%nat -> CC.cp_pc c = 808308 -> CCA.AtV (hl_segs L) c E0 R A M model ->
            srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 808308) M (seg_rom (hl_segs L))) model) K).
  { intros i0 c0 Hc0 Hi0 Hpc0 HAt0. rewrite <- Hpc0.
    eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW WW G.BLS VSA.FFS Cred 4 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
              G.CPS K PMSA.fp_ok XI G.TAGS) with (i := i0) (E := E0).
    - rewrite LS. exact FPM.
    - rewrite LS. exact G.plans.
    - exact G.tags_ok.
    - exact VSA.heap_ok.
    - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
    - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
    -
      intros i c kk ps pc IL. pose proof (CH2.leaves_all_sound _ _ _ VSA.leaf_ok _ _ _ _ _ IL) as X. unfold VSA.leaf_chk in X.
      pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW WW G.BLS VSA.FFS Cred 4 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                    G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.

      assert (PRO : forall i1 : nat, (2 <= i1)%nat -> forall E A1 M1 m1, CHA.aamb L ar HI GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW G.BLS VSA.FFS Cred 4 i1 E A1 M1 m1 ->
                XI i1 E A1 M1 m1 ->
                let nb := CL5A.uv E (EVar 44) in env_agree GT.NF E0 E /\ CHA.curF FF sp VSA.FFS i1 E = FF /\ AFP nb /\ L5.defined M1 nb (2 * cap)).
      { intros i1 Hi1 Ex Ax Mx mx HAx HXx. cbv zeta.
        assert (HagE : env_agree GT.NF E0 Ex) by exact (proj1 (proj2 (proj2 (proj2 HAx)))).
        split; [exact HagE|]. split; [unfold CHA.curF; rewrite FFSnil; reflexivity|].
        unfold XI in HXx. destruct (Nat.leb i1 1) eqn:L1; [apply Nat.leb_le in L1; exfalso; clear - Hi1 L1; lia|].
        destruct (Nat.leb i1 5); [exact (conj (proj1 HXx) (proj1 (proj2 HXx)))|]. destruct (Nat.leb i1 7); [exact (conj (proj1 HXx) (proj1 (proj2 HXx)))|]. exact (conj (proj1 HXx) (proj1 (proj2 HXx))). }
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret.
      +
        destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
        destruct (Z.eqb_spec pc VSA.PC_OPNEW) as [->|Hne1].
        {
          cbv zeta in X. set (nx := (CC.cp_nx cj - APC.NCS)%nat) in *. set (news := VSA.news_of (nx + 4) cj) in *.
          apply andb_prop in X as [X Y9]. apply andb_prop in X as [X Y8]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3].
          apply andb_prop in X as [X YN]. apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1].
          apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y2, YN. apply CH2.blocks_eqb_eq in Y3, Y4. subst j.
          assert (J1 : Nat.leb (i + 2) 1 = false) by (apply Nat.leb_gt; clear; lia). assert (J5 : Nat.leb (i + 2) 5 = true) by (apply Nat.leb_le; apply Nat.leb_le in Y1; clear - Y1; lia).
          lazymatch type of Y5 with VSA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
          intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
          assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
          assert (HXi' : shadow_cont M1 b cap cap) by (unfold XI in HXi; rewrite Y1 in HXi; exact HXi).
          assert (HcB : CHA.curB (lb_remove b LB) G.BLS i E = (b, cap) :: lb_remove b LB) by (unfold CHA.curB; rewrite Y3, (DEN1 E HagE); reflexivity).
          assert (HcF : CHA.curF FF sp VSA.FFS i E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
          refine (CALLEE VSA.PC_OPNEW 4112 0%nat VSA.BOLD [] news None 0 i c ps (i + 2)%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
            [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
          rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
          destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
          assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite Y1 in HC1; exact HC1). subst cr1.
          assert (NXeq : CH2.ci_nx ci = nx) by (destruct HV as (_ & _ & _ & _ & HV5); unfold nx; rewrite HV5; unfold APC.NCS; clear; lia).
          assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
          assert (W33 : bv_unsigned (ev E' 33) = cap) by (rewrite (FZ 33%nat eq_refl); exact U33).
          pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
          eexists. eexists. split; [exact (OPNEW_OK ((b, cap) :: lb_remove b LB) FF LK1 cr A1 (2 * cap) (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
          { unfold PMSA.a0. split; [|split; [clear - Hcap; lia | exact Hcred]].
            replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
            rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y9). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. exact (USZ E' HagE'). }
          {
            intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (u & Hu & Hfresh & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
            pose proof Hfresh as (Hrng & Hbap & Hfap & Hdef & Hsh). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
            exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
            pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
            set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
            assert (UR : 0 <= u < 2 ^ 64) by (clear - Q0 Q3 Q4 CL SP1; lia).
            assert (Hvu : CL5A.uv E2 (EVar 44) = u).
            { unfold CL5A.uv. cbn [edenot]. pose proof (CH2.retEx_a0 E' (CH2.ci_nx ci) [] R2) as G0. cbn [length] in G0. rewrite Nat.add_0_r in G0.
              unfold E2. rewrite NXeq, YN in G0. rewrite NXeq, YN. change (40 + 4)%nat with 44%nat in G0. unfold PMSA.a0 in Hu. rewrite G0, Hu. apply u64_of_Z. exact UR. }
            assert (HagE2 : env_agree GT.NF E0 E2).
            { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
            assert (FZ2 : forall n, (n <? 40)%nat = true -> ev E2 n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE2); apply Nat.ltb_lt; exact Hn).
            assert (T2 : bv_unsigned (ev E2 2) = sp) by (rewrite (FZ2 2%nat eq_refl); exact U2).
            assert (T10 : bv_unsigned (ev E2 10) = o) by (rewrite (FZ2 10%nat eq_refl); exact U10).
            assert (T11 : bv_unsigned (ev E2 11) = xa) by (rewrite (FZ2 11%nat eq_refl); exact U11).
            assert (T33 : bv_unsigned (ev E2 33) = cap) by (rewrite (FZ2 33%nat eq_refl); exact U33).
            assert (T44 : bv_unsigned (ev E2 44) = u) by (unfold CL5A.uv in Hvu; cbn [edenot] in Hvu; exact Hvu).
            split; [rewrite (DEN1 E' HagE'); apply incl_refl|]. split; [intros w a []|]. split; [intros w a []|].
            assert (HBj : CHA.curB (lb_remove b LB) G.BLS (i + 2) E2 = (u, 2 * cap) :: (b, cap) :: lb_remove b LB) by (unfold CHA.curB; rewrite Y4, (DEN2 E2 HagE2), Hvu; reflexivity).
            split; [rewrite HBj; exact HH2|]. split; [unfold Cred; rewrite J1; reflexivity|].
            pose proof (PmHeapIfaceA.aio_small_high _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2 (u, 2 * cap) (or_introl eq_refl) ltac:(cbn [snd]; clear - Hcap2; lia)) as UHI. cbn [fst] in UHI.
            assert (HAFP : AFP u) by (split; [exact Hrng | split; [exact Hbap | split; [exact Hfap | exact UHI]]]).
            split.
            { unfold XI. cbv zeta. rewrite J1, J5, Hvu. split; [exact HAFP|]. split; [exact Hdef|]. split; [exact Hsh|].

              apply (CL5A.shadow_cont_same M1 M2 b cap cap ltac:(clear - Hcap; lia) (CHA.mod8_of_16 _ B16)); [|exact HXi']. intros a Ha.
              pose proof (SHR b cap a ltac:(clear - B0; lia) B3 B7 Ha) as SRa. pose proof HP as (HP1 & _ & _).
              rewrite (HP1 a); [|split; [clear - SRa; lia | split; [do 6 right; exists (b, cap); split; [left; reflexivity | exact Ha] | intros w []]]].
              refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW WW G.BLS VSA.FFS Cred 4 STKF SCRP NF32 U2 WRS_OK
                        i c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil, Y3; exact YF|].
              rewrite FFSnil, Y3, (DEN1 E HagE). apply (NOFOOT [(b, cap)] a); [constructor; [cbn [fst]; exact BHI | constructor] | exact SRa]. }

            intros X0 HX0 _. destruct (VSA.has VSA.HAND X0) eqn:HH0.
            -
              apply CC.has_cell_In in HH0. unfold VSA.HAND, VSA.oE, VSA.xaE, VSA.capE, VSA.nbE, VSA.SIZE2, VSA.SHN, VSA.SBz, CHA.SRL3 in HH0. cbn [In] in HH0.
              assert (U8 : u mod 8 = 0) by exact (CHA.mod8_of_16 _ Q16).
              assert (GRAN : cap / 8 < 2 * cap / 8).
              { clear - Hcap4. pose proof (Z.div_mod (2 * cap) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (2 * cap) 8 ltac:(lia)) as M2'.
                pose proof (Z.div_mod cap 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound cap 8 ltac:(lia)) as M1'. lia. }
              pose proof (CL5A.gran_blk (2 * cap) ltac:(clear - Hcap; lia)) as GB.
              assert (VSU : forall a, in_shadow_of u (2 * cap) a -> ahid A2 m2 (Z_to_bv 64 a) = false).
              { intros a Ha. pose proof (SHR u (2 * cap) a ltac:(clear - Q0; lia) ltac:(clear - Hcap; lia) Q7 Ha) as SRa.
                apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ m2 sp 0 a HH2); [clear - SRa; lia | do 6 right; exists (u, 2 * cap); split; [left; reflexivity | exact Ha] |].
                exact (CL5A.not_stk_shadow_sh L ar LB FF u (2 * cap) a RFx ltac:(clear - Q0; lia) ltac:(clear - Hcap; lia) Q4 Ha). }
              destruct HH0 as [<-|[<-|[<-|[<-|[]]]]].
              +
                apply (CL5A.shbyte_intro (hl_segs L) E2 _ _ _ (u + cap) 0); [unfold CL5A.uv; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - UR Q0 Q4 Q7 Hcap; lia] | reflexivity | clear; lia | clear - Q0 Q7 Hcap; lia |].
                apply CL5A.byte_vis.
                * apply VSU. unfold in_shadow_of, S. pose proof (CL5A.div8_le u (u + cap) ltac:(clear - Hcap; lia)) as G1. pose proof (CL5A.div8_le (u + cap) (u + 2 * cap - 1) ltac:(clear - Hcap; lia)) as G2. clear - G1 G2. lia.
                * destruct Hsh as [Z0 _]. unfold byte_at in *. rewrite (CL5A.S_add_al u cap U8). apply Z0. split; [apply Z.div_pos; clear - Hcap; lia | exact GRAN].
              +
                pose proof Hofr as (f & Hf & F1 & F2). pose proof (Hfap f Hf) as QF. destruct (CHA.frm_align L ar LB FF LK cr A M f WF Hf) as (FA & FB & _).
                eapply CL5.kdisj_intro with (A1 := u / 8 + SB) (N1 := (2 * cap + 7) / 8) (A2 := o / 8 + SB) (N2 := 3);
                  [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite T44; reflexivity
                  | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia]
                  | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite T10; reflexivity | reflexivity |].
                destruct QF as [QF|QF].
                * left. pose proof (CL5A.gran_le u ((2 * cap + 7) / 8) (ff_addr f) (CHA.mod8_of_64 _ FA) ltac:(clear - QF GB; lia)) as G1. pose proof (CL5A.div8_le (ff_addr f) o ltac:(clear - F1; lia)) as G2. clear - G1 G2. lia.
                * right. pose proof (CL5A.gran_le o 3 (ff_addr f + ff_bytes (ff_class f)) (CL5A.al64_add8 _ _ FA FB) ltac:(clear - F2; lia)) as G1. pose proof (CL5A.div8_le _ u QF) as G2. clear - G1 G2. lia.
              +
                eapply CL5.kdisj_intro with (A1 := u / 8 + SB) (N1 := (2 * cap + 7) / 8) (A2 := xa / 8 + SB) (N2 := 1);
                  [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite T44; reflexivity
                  | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia]
                  | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite T11; reflexivity | reflexivity |].
                unfold al in C8. pose proof Hxfr as [(f & Hf & F1 & F2)|(XS1 & XS2)];
                  [|left; pose proof (CL5A.gran_le u ((2 * cap + 7) / 8) (ahl_ceil ar) C8 ltac:(clear - Q4 GB; lia)) as G1; pose proof (CL5A.div8_le (ahl_ceil ar) xa ltac:(clear - XS1 S2; lia)) as G2; clear - G1 G2; lia].
                pose proof (Hfap f Hf) as QF. destruct (CHA.frm_align L ar LB FF LK cr A M f WF Hf) as (FA & FB & _). destruct QF as [QF|QF].
                * left. pose proof (CL5A.gran_le u ((2 * cap + 7) / 8) (ff_addr f) (CHA.mod8_of_64 _ FA) ltac:(clear - QF GB; lia)) as G1. pose proof (CL5A.div8_le (ff_addr f) xa ltac:(clear - F1; lia)) as G2. clear - G1 G2. lia.
                * right. pose proof (CL5A.gran_le xa 1 (ff_addr f + ff_bytes (ff_class f)) (CL5A.al64_add8 _ _ FA FB) ltac:(clear - F2; lia)) as G1. pose proof (CL5A.div8_le _ u QF) as G2. clear - G1 G2. lia.
              +
                eapply CL5.kdisj_intro with (A1 := u / 8 + SB) (N1 := (2 * cap + 7) / 8) (A2 := (sp - 88) / 8 + SB) (N2 := 5);
                  [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite T44; reflexivity
                  | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia]
                  | rewrite CL5A.estart_srl3'; f_equal; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia] | reflexivity |].
                left. pose proof (CL5A.gran_le u ((2 * cap + 7) / 8) (sp - 88) SP8 ltac:(clear - Q4 GB S2; lia)) as G1. clear - G1. lia.
            - refine (CRB.news_sound L ar C HI HIok LYI 65536 7028736 LYH GT.NF E0 (lb_remove b LB) FF sp G.HDECL WW STKF SCRP NF32 U2 WOK CRS_OK WRS_OK GT.SCELLS GT.GLO GT.GHI SCOK GOTOK
                        E' E2 (CH2.ci_nx ci) (SR.ps_cells ps) VSA.BOLD [] 44%nat VSA.SIZE2 M' M2 A1 A2 m' m2 ((b, cap) :: lb_remove b LB) ((u, 2 * cap) :: (b, cap) :: lb_remove b LB) FF FF LK1 LK2 cr (adebit L cr (2 * cap)) u (2 * cap)
                        (List.filter (fun X => negb (VSA.has VSA.HAND X)) news)
                        HagE' Hag2 HK HH1 _ eq_refl Hvu _ (USZ E' HagE') Hrng Hbap Hfap Hdef Hsh HH2 (or_introl eq_refl) _ X0 _).
              + rewrite (DEN1 E' HagE'). reflexivity.
              + rewrite NXeq, YN. reflexivity.
              + rewrite NXeq. rewrite YN in Y8 |- *. exact Y8.
              + apply filter_In. split; [exact HX0 | rewrite HH0; reflexivity]. } }
        destruct (Z.eqb_spec pc VSA.PC_ADEL) as [->|Hne2].
        {
          apply andb_prop in X as [X Ysh]. apply andb_prop in X as [X Yc]. apply andb_prop in X as [X Yb]. apply andb_prop in X as [X Ya]. apply andb_prop in X as [X Y7].
          apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y44].
          apply andb_prop in X as [X Y2]. apply andb_prop in X as [X Y1']. apply andb_prop in X as [Y0 Y1].
          apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y2. subst j. apply CH2.blocks_eqb_eq in Y3, Y4. apply Nat.ltb_lt in Y44. apply Nat.leb_le in Y1, Y1'.
          lazymatch type of Y5 with VSA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
          intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
          destruct (PRO i ltac:(clear - Y1; lia) E A1 M1 m1 HA HXi) as (HagE & HcF & HAFP & HDF). set (nb := CL5A.uv E (EVar 44)) in *.
          assert (XI5 : Nat.leb i 1 = false /\ Nat.leb i 5 = true) by (split; [apply Nat.leb_gt | apply Nat.leb_le]; clear - Y1 Y1'; lia).
          assert (XJ5 : Nat.leb (i + 2) 1 = false /\ Nat.leb (i + 2) 5 = true) by (split; [apply Nat.leb_gt | apply Nat.leb_le]; clear - Y1 Y1'; lia).
          assert (HSB : shadow_blk M1 nb (2 * cap) /\ shadow_cont M1 b cap cap) by (unfold XI in HXi; rewrite (proj1 XI5), (proj2 XI5) in HXi; exact (proj2 (proj2 HXi))). destruct HSB as [HSB HSC].
          pose proof HAFP as (Hrng & Hbap & Hfap & NBHI). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
          assert (HcB : CHA.curB (lb_remove b LB) G.BLS i E = (nb, 2 * cap) :: (b, cap) :: lb_remove b LB) by (unfold CHA.curB; rewrite Y3, (DEN2 E HagE); reflexivity).
          refine (CALLEE VSA.PC_ADEL 4128 0%nat VSA.BBOTH VSA.WSHB VSA.STAT None 0 i c ps (i + 2)%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
            [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
          rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
          destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
          assert (Hcr1 : cr1 = adebit L cr (2 * cap)) by (unfold Cred in HC1; rewrite (proj1 XI5) in HC1; exact HC1). subst cr1.
          assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
          assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
          assert (W32 : bv_unsigned (ev E' 32) = b) by (rewrite (FZ 32%nat eq_refl); exact U32).
          assert (W33 : bv_unsigned (ev E' 33) = cap) by (rewrite (FZ 33%nat eq_refl); exact U33).
          assert (NB' : CL5A.uv E' (EVar 44) = nb) by (unfold nb, CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by exact Y44; reflexivity).
          assert (CELL : forall X0, VSA.has (SR.ps_cells ps) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
          { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
          pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW G.BLS VSA.FFS Cred 4 i E A1 M' m' HA') as Hoff.
          pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
          assert (HF2 : Forall (fun bb : Z * Z => 17594333495296 <= fst bb) [(nb, 2 * cap); (b, cap)]) by (constructor; [exact NBHI | constructor; [exact BHI | constructor]]).

          assert (FRS : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
          { intros q n a Hq Hn Hqn Ha. pose proof (SHR q n a Hq Hn Hqn Ha) as SRa.
            refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW WW G.BLS VSA.FFS Cred 4 STKF SCRP NF32 U2 WRS_OK
                      i c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil, Y3; exact YF|].
            rewrite FFSnil, Y3, (DEN2 E HagE). exact (NOFOOT _ a HF2 SRa). }
          unfold VSA.oE, VSA.bE, VSA.capE in *.
          eexists. eexists. split; [exact (ADEL_OK ((nb, 2 * cap) :: (b, cap) :: lb_remove b LB) FF LK1 (adebit L cr (2 * cap)) A1 o b cap cap (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
          { unfold PMSA.a0, PMSA.vec_at, PMSA.u64, PMSA.acobj.
            split; [replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity);
                    rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y7); cbn [edenot]; rewrite (FZ 10%nat eq_refl); exact V10|].
            split.
            { split; [|split]; apply (CL5A.u64_full (hl_segs L) _ Hoff).
              - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Ya) ltac:(ev_start)) as G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite W32 in G0. exact G0.
              - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 8) (CELL _ Yb) ltac:(ev_start)) as G0.
                replace (CL5A.uv E' (EAlu Instr.ALU_ADD (EVar 32) (EVar 33))) with (b + cap) in G0; [exact G0|]. symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hcap; lia].
              - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 16) (CELL _ Yc) ltac:(ev_start)) as G0.
                replace (CL5A.uv E' (EAlu Instr.ALU_ADD (EVar 32) (EVar 33))) with (b + cap) in G0; [exact G0|]. symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hcap; lia]. }
            split; [left; exact Hofr|]. split; [exact Ho8|].
            split; [pose proof (CL5A.shz_elim (hl_segs L) E' _ (EVar 10) 3 o (CELL _ Ysh) ltac:(unfold CL5A.uv; cbn [edenot]; exact W10) ltac:(clear; lia)) as SZ; intros jj Hj; exact (CL5A.byte_full _ _ _ _ (SZ jj Hj))|].
            split; [right; left; reflexivity|]. split; [clear - Hcap; lia|]. split; [clear - Hcap; lia|].
            split; [exact (CL5A.shadow_cont_same M1 M' b cap cap ltac:(clear - Hcap; lia) (CHA.mod8_of_16 _ B16) (fun a Ha => FRS b cap a ltac:(clear - B0; lia) B3 B7 Ha) HSC)|].
            clear - BHI; lia. }
          {
            intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (HSC2 & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
            exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
            pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
            set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
            assert (HagE2 : env_agree GT.NF E0 E2).
            { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
            assert (NB2 : CL5A.uv E2 (EVar 44) = nb) by (unfold CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag2 44%nat) by (destruct HV as (_ & _ & HV3 & _); clear - HV3 Y44; lia); exact NB').
            split; [rewrite (DEN2 E' HagE'), NB'; apply incl_refl|].
            split.
            { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (CHA.SRL3 (EVar 32), VSA.SBz, VSA.SHN (EVar 33)). split; [left; reflexivity|].
              unfold CHA.in_reg, VSA.SHN. rewrite CL5A.estart_srl3. unfold elenZ. rewrite CHA.u_srl3. unfold CL5A.uv. cbn [edenot]. rewrite W32.
              replace (bv_unsigned (edenot E' (APC.eaddz (EVar 33) 7))) with (cap + 7) by (symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia]).
              unfold S, SB, VSA.SBz in *. exact Hin. }
            split.
            { intros w a [<-|[]] Hin (Ka & Kc & _). unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
              refine (CHA.obj_not_client L ar LYI (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) b cap a RFr _ B3 (CHA.mod8_of_16 _ B16) B4 (or_intror B1') Bap _ (or_intror _) Kc).
              - unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI. clear - B0 B7 BHI. lia.
              - intros f Hf. apply Bfap. apply in_or_app. left. exact Hf.
              - exact (CL5A.blk_shadow_in b cap a (CHA.mod8_of_16 _ B16) B3 Hin). }
            split; [unfold CHA.curB; rewrite Y4, (DEN2 E2 HagE2), NB2; exact HH2|].
            split; [unfold Cred; rewrite (proj1 XJ5); reflexivity|].
            split.
            { unfold XI. cbv zeta. rewrite (proj1 XJ5), (proj2 XJ5), NB2. pose proof HP as (HP1 & HP2 & HP3).
              split; [exact HAFP|]. split; [|split; [|exact HSC2]].
              - intros k Hk. apply (HP3 (nb + k)); [clear - Hk Q0 Q7; lia | left; exists (nb, 2 * cap); split; [left; reflexivity | cbn [fst snd]; clear - Hk; lia] |].
                apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (HDF k Hk).
              -
                apply (PTA.shadow_blk_ag M1 M2 (fun a => in_shadow_of nb (2 * cap) a)); [|clear - Hcap; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ Q16) | exact HSB].
                intros a Ha. pose proof (SHR nb (2 * cap) a ltac:(clear - Q0; lia) ltac:(clear - Hcap; lia) Q7 Ha) as SRa.
                rewrite (HP1 a); [exact (FRS nb (2 * cap) a ltac:(clear - Q0; lia) ltac:(clear - Hcap; lia) Q7 Ha)|].
                split; [clear - SRa; lia|]. split; [do 6 right; exists (nb, 2 * cap); split; [left; reflexivity | exact Ha]|].
                intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
                refine (CL5A.sh_apart2 nb (2 * cap) b cap a ltac:(clear - Q0; lia) ltac:(clear - B0; lia) ltac:(clear - Hcap; lia) B3 (CHA.mod8_of_16 _ Q16) (CHA.mod8_of_16 _ B16) (Hbap (b, cap) (or_introl eq_refl)) Ha _).
                exact (CL5A.blk_shadow_in b cap a (CHA.mod8_of_16 _ B16) B3 Hin). }
            intros X0 HX0 _. unfold VSA.STAT in HX0. cbn [In] in HX0.
            destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). } }
        destruct (Z.eqb_spec pc VSA.PC_MEMCPY) as [->|Hne3].
        {
          apply andb_prop in X as [X Yblob]. apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10].
          apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y44].
          apply andb_prop in X as [X Y2]. apply andb_prop in X as [X Y1']. apply andb_prop in X as [Y0 Y1].
          apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y2. subst j. apply CH2.blocks_eqb_eq in Y3, Y4. apply Nat.ltb_lt in Y44. apply Nat.leb_le in Y1, Y1'.
          lazymatch type of Y5 with VSA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
          intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
          destruct (PRO i ltac:(clear - Y1; lia) E A1 M1 m1 HA HXi) as (HagE & HcF & HAFP & HDF). set (nb := CL5A.uv E (EVar 44)) in *.
          assert (XI5 : Nat.leb i 1 = false /\ Nat.leb i 5 = true) by (split; [apply Nat.leb_gt | apply Nat.leb_le]; clear - Y1 Y1'; lia).
          assert (XJ7 : Nat.leb (i + 2) 1 = false /\ Nat.leb (i + 2) 5 = false /\ Nat.leb (i + 2) 7 = true) by (split; [|split]; [apply Nat.leb_gt | apply Nat.leb_gt | apply Nat.leb_le]; clear - Y1 Y1'; lia).
          assert (HSB : shadow_blk M1 nb (2 * cap) /\ shadow_cont M1 b cap cap) by (unfold XI in HXi; rewrite (proj1 XI5), (proj2 XI5) in HXi; exact (proj2 (proj2 HXi))). destruct HSB as [HSB HSC].
          pose proof HAFP as (Hrng & Hbap & Hfap & NBHI). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
          assert (HcB : CHA.curB (lb_remove b LB) G.BLS i E = (nb, 2 * cap) :: (b, cap) :: lb_remove b LB) by (unfold CHA.curB; rewrite Y3, (DEN2 E HagE); reflexivity).
          refine (CALLEE VSA.PC_MEMCPY 2560 0%nat VSA.BBOTH [(VSA.nbE, 0, VSA.capE)] VSA.NEWS_MEMCPY (Some VSA.nbE) 0 i c ps (i + 2)%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
            [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
          rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
          destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
          assert (Hcr1 : cr1 = adebit L cr (2 * cap)) by (unfold Cred in HC1; rewrite (proj1 XI5) in HC1; exact HC1). subst cr1.
          assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
          assert (W32 : bv_unsigned (ev E' 32) = b) by (rewrite (FZ 32%nat eq_refl); exact U32).
          assert (W33 : bv_unsigned (ev E' 33) = cap) by (rewrite (FZ 33%nat eq_refl); exact U33).
          assert (NB' : CL5A.uv E' (EVar 44) = nb) by (unfold nb, CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by exact Y44; reflexivity).
          assert (W44 : bv_unsigned (ev E' 44) = nb) by (unfold CL5A.uv in NB'; cbn [edenot] in NB'; exact NB').
          assert (CELL : forall X0, VSA.has (SR.ps_cells ps) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
          { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
          pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW G.BLS VSA.FFS Cred 4 i E A1 M' m' HA') as Hoff.
          pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
          assert (HF2 : Forall (fun bb : Z * Z => 17594333495296 <= fst bb) [(nb, 2 * cap); (b, cap)]) by (constructor; [exact NBHI | constructor; [exact BHI | constructor]]).
          assert (FRS : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
          { intros q n a Hq Hn Hqn Ha. pose proof (SHR q n a Hq Hn Hqn Ha) as SRa.
            refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW WW G.BLS VSA.FFS Cred 4 STKF SCRP NF32 U2 WRS_OK
                      i c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil, Y3; exact YF|].
            rewrite FFSnil, Y3, (DEN2 E HagE). exact (NOFOOT _ a HF2 SRa). }
          assert (HSB' : shadow_blk M' nb (2 * cap)).
          { apply (PTA.shadow_blk_ag M1 M' (fun a => in_shadow_of nb (2 * cap) a)); [| clear - Hcap; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ Q16) | exact HSB].
            intros a Ha. exact (FRS nb (2 * cap) a ltac:(clear - Q0; lia) ltac:(clear - Hcap; lia) Q7 Ha). }
          assert (HSC' : shadow_cont M' b cap cap) by exact (CL5A.shadow_cont_same M1 M' b cap cap ltac:(clear - Hcap; lia) (CHA.mod8_of_16 _ B16) (fun a Ha => FRS b cap a ltac:(clear - B0; lia) B3 B7 Ha) HSC).
          assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps q e = true -> bv_unsigned (edenot E' e) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
          { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
          assert (LENST : length st = Z.to_nat cap) by (clear - HlenEq; lia).
          unfold VSA.nbE, VSA.bE, VSA.capE in *.
          eexists. eexists. split.
          { unfold VSA.PC_MEMCPY. rewrite <- (L5A.aly_memcpy L C LAY).
            exact (CRC.asan_memcpy_cps L ar C HI HIok PMSA.fp_ok 2560 ((nb, 2 * cap) :: (b, cap) :: lb_remove b LB) FF LK1 (adebit L cr (2 * cap)) A1 nb b cap (map (Z_to_bv 8) st) (sp + CH2.ci_csp ci) (CC.cp_pc cj)
                     ltac:(rewrite (L5A.aly_scr_mem L C LAY); clear; lia)). }
          split.
          { unfold CRC.memcpy_pre.
            split; [exact (REG 10%nat _ nb Y10 W44)|]. split; [exact (REG 11%nat _ b Y11 W32)|]. split; [exact (REG 12%nat _ cap Y12 W33)|].
            split; [exact (CRC.dst_in_block L ar C HI HIok _ FF LK1 _ A1 M' _ (sp + CH2.ci_csp ci) 2560 nb (2 * cap) nb cap HH1 (or_introl eq_refl) HSB' ltac:(clear; lia) ltac:(clear - Hcap; lia) ltac:(clear - Hcap; lia))|].
            split.
            - refine (CRC.src_in_block L ar C HI HIok _ FF LK1 _ A1 M' _ (sp + CH2.ci_csp ci) 2560 b cap b cap (map (Z_to_bv 8) st) HH1 (or_intror (or_introl eq_refl)) _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - Hcap; lia) _).
              +
                destruct HSC' as (Z0 & P0 & _). exact (CRC.aacc_blk M' b cap b cap (conj Z0 P0) (CHA.mod8_of_16 _ B16) ltac:(clear - B0; lia) ltac:(clear; lia) ltac:(clear; lia)).
              + rewrite <- LENST. apply (L5C.bytes_at_rdn (hl_segs L) M' st b ltac:(clear - B0; lia) ltac:(clear - B7 HlenEq; lia)).
                apply (CL5A.bytes_full (hl_segs L) _ Hoff). refine (proj1 (CL5.kblob_elim (hl_segs L) E' _ _ _ 0%nat b st (CELL _ Yblob) ltac:(ev_start) _)). rewrite <- (proj2 HagE'). reflexivity.
            - pose proof (Hbap (b, cap) (or_introl eq_refl)) as AP. cbn [fst snd] in AP. clear - AP Hcap. lia. }
          {
            intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & Hnew & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
            exists []. split; [reflexivity|]. cbv zeta.
            pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
            set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
            assert (HagE2 : env_agree GT.NF E0 E2).
            { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
            assert (NB2 : CL5A.uv E2 (EVar 44) = nb) by (unfold CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag2 44%nat) by (destruct HV as (_ & _ & HV3 & _); clear - HV3 Y44; lia); exact NB').
            assert (T44 : bv_unsigned (ev E2 44) = nb) by (unfold CL5A.uv in NB2; cbn [edenot] in NB2; exact NB2).
            assert (T33 : bv_unsigned (ev E2 33) = cap) by (rewrite <- (proj1 HagE2 33%nat) by (apply Nat.ltb_lt; reflexivity); exact U33).
            split; [cbn [edenot]; rewrite Ha0', <- T44; apply Z_to_bv_bv_unsigned|].
            split; [rewrite (DEN2 E' HagE'), NB'; apply incl_refl|].
            split.
            { intros w a [<-|[]] Hin. exists (EVar 44, 0, EVar 33). split; [left; reflexivity|]. unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite W44, W33.
              unfold L5.in_rng in Hin. cbn [fst snd] in Hin. clear - Hin. lia. }
            split.
            { intros w a [<-|[]] Hin (Ka & Kc & _). unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
              refine (CHA.obj_not_client L ar LYI (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) nb (2 * cap) a RFr (conj Q5 (conj Q6 Q7)) ltac:(clear - Hcap; lia) (CHA.mod8_of_16 _ Q16) Q4 Q1 _ Hfap (or_introl _) Kc).
              - intros bb Hbb. exact (Hbap bb (or_intror Hbb)).
              - clear - Hin Hcap. lia. }
            split; [unfold CHA.curB; rewrite Y4, (DEN2 E2 HagE2), NB2; exact HH2|].
            split; [unfold Cred; rewrite (proj1 XJ7); reflexivity|].
            pose proof HP as (HP1 & HP2 & HP3).

            assert (GB2 : forall k, (k < length st)%nat -> M2 (Z_to_bv 64 (nb + Z.of_nat k)) = Some (Z_to_bv 8 (nth k st 0))).
            { intros k Hk. destruct (Hnew (Z.of_nat k) ltac:(clear - Hk HlenEq; lia)) as (v & (Hnth & Hv) & Hb). rewrite Nat2Z.id, nth_error_map in Hnth.
              destruct (nth_error st k) as [z|] eqn:Ez; [|discriminate Hnth]. cbn [option_map] in Hnth. assert (Hz : Z_to_bv 8 z = Z_to_bv 8 v) by congruence. rewrite (@nth_error_nth _ st k z 0 Ez).
              unfold byte_at in Hb. rewrite Hb, <- Hz. reflexivity. }
            split.
            { unfold XI. cbv zeta. rewrite (proj1 XJ7), (proj1 (proj2 XJ7)), (proj2 (proj2 XJ7)), NB2.
              split; [exact HAFP|]. split.
              - intros k Hk. apply (HP3 (nb + k)); [clear - Hk Q0 Q7; lia | left; exists (nb, 2 * cap); split; [left; reflexivity | cbn [fst snd]; clear - Hk; lia] |].
                apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (HDF k Hk).
              - apply (PTA.shadow_blk_ag M' M2 (fun a => in_shadow_of nb (2 * cap) a)); [| clear - Hcap; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ Q16) | exact HSB'].
                intros a Ha. pose proof (SHR nb (2 * cap) a ltac:(clear - Q0; lia) ltac:(clear - Hcap; lia) Q7 Ha) as SRa.
                apply HP1. split; [clear - SRa; lia|]. split; [do 6 right; exists (nb, 2 * cap); split; [left; reflexivity | exact Ha]|].
                intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. clear - Hin SRa NBHI. lia. }

            intros X0 HX0 _. unfold VSA.NEWS_MEMCPY, VSA.STAT, VSA.nbE, VSA.capE in HX0. cbn [app In] in HX0.
            destruct HX0 as [<-|[<-|[<-|[]]]]; [apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity
                                           | apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity |].
            assert (VNB : CL5A.visr (ahid A2 m2) nb cap).
            { intros k Hk. apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ m2 sp 0 (nb + k) HH2); [clear - Hk Q0 Q7 Hcap; lia | left; exists (nb, 2 * cap); split; [left; reflexivity | cbn [fst snd]; clear - Hk Hcap; lia] |].
              apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hk NBHI. lia. }
            eapply CL5.kblob_intro with (A := nb) (bs := st); [ev_start | unfold elenZ; cbn [edenot]; rewrite T33; clear - HlenEq; lia | clear - Q0; lia | clear - Q7 HlenEq Hcap; lia | clear - Q7 Hcap; lia
                                                             | rewrite <- (proj2 HagE2); reflexivity | |].
            - apply (CL5A.bytes_vis (hl_segs L)); [clear - Q0; lia | clear - Q7 HlenEq Hcap; lia | rewrite HlenEq; exact VNB |].
              intros k Hk. unfold L5.u8_at. cbn [rdn]. rewrite (GB2 k Hk). reflexivity.
            - apply (CL5A.defined_vis _ M2 nb (Z.of_nat (length st))); [rewrite HlenEq; exact VNB|]. intros k Hk. rewrite <- (Z2Nat.id k) by (clear - Hk; lia). rewrite (GB2 (Z.to_nat k) ltac:(clear - Hk HlenEq; lia)). discriminate. } }
        destruct (Z.eqb_spec pc VSA.PC_ANEW) as [->|Hne4].
        {
          apply andb_prop in X as [X Ysh]. apply andb_prop in X as [X Yc]. apply andb_prop in X as [X Ya]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10].
          apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y44].
          apply andb_prop in X as [X Y2]. apply andb_prop in X as [X Y1']. apply andb_prop in X as [Y0 Y1].
          apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y2. subst j. apply CH2.blocks_eqb_eq in Y3, Y4. apply Nat.ltb_lt in Y44. apply Nat.leb_le in Y1, Y1'.
          lazymatch type of Y5 with VSA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
          intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
          destruct (PRO i ltac:(clear - Y1; lia) E A1 M1 m1 HA HXi) as (HagE & HcF & HAFP & HDF). set (nb := CL5A.uv E (EVar 44)) in *.
          assert (XI7 : Nat.leb i 1 = false /\ Nat.leb i 5 = false /\ Nat.leb i 7 = true) by (split; [|split]; [apply Nat.leb_gt | apply Nat.leb_gt | apply Nat.leb_le]; clear - Y1 Y1'; lia).
          assert (XJ9 : Nat.leb (i + 2) 1 = false /\ Nat.leb (i + 2) 5 = false /\ Nat.leb (i + 2) 7 = false) by (split; [|split]; apply Nat.leb_gt; clear - Y1 Y1'; lia).
          assert (HSB : shadow_blk M1 nb (2 * cap)) by (unfold XI in HXi; rewrite (proj1 XI7), (proj1 (proj2 XI7)), (proj2 (proj2 XI7)) in HXi; exact (proj2 (proj2 HXi))).
          pose proof HAFP as (Hrng & Hbap & Hfap & NBHI). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
          assert (HcB : CHA.curB (lb_remove b LB) G.BLS i E = (nb, 2 * cap) :: (b, cap) :: lb_remove b LB) by (unfold CHA.curB; rewrite Y3, (DEN2 E HagE); reflexivity).
          refine (CALLEE VSA.PC_ANEW 4128 0%nat VSA.BBOTH VSA.WSHN VSA.STAT None 0 i c ps (i + 2)%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
            [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
          rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
          destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
          assert (Hcr1 : cr1 = adebit L cr (2 * cap)) by (unfold Cred in HC1; rewrite (proj1 XI7) in HC1; exact HC1). subst cr1.
          assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
          assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
          assert (W33 : bv_unsigned (ev E' 33) = cap) by (rewrite (FZ 33%nat eq_refl); exact U33).
          assert (NB' : CL5A.uv E' (EVar 44) = nb) by (unfold nb, CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by exact Y44; reflexivity).
          assert (W44 : bv_unsigned (ev E' 44) = nb) by (unfold CL5A.uv in NB'; cbn [edenot] in NB'; exact NB').
          assert (CELL : forall X0, VSA.has (SR.ps_cells ps) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
          { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
          pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW G.BLS VSA.FFS Cred 4 i E A1 M' m' HA') as Hoff.
          pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
          assert (HF2 : Forall (fun bb : Z * Z => 17594333495296 <= fst bb) [(nb, 2 * cap); (b, cap)]) by (constructor; [exact NBHI | constructor; [exact BHI | constructor]]).
          assert (FRS : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
          { intros q n a Hq Hn Hqn Ha. pose proof (SHR q n a Hq Hn Hqn Ha) as SRa.
            refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW WW G.BLS VSA.FFS Cred 4 STKF SCRP NF32 U2 WRS_OK
                      i c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil, Y3; exact YF|].
            rewrite FFSnil, Y3, (DEN2 E HagE). exact (NOFOOT _ a HF2 SRa). }
          assert (HSB' : shadow_blk M' nb (2 * cap)).
          { apply (PTA.shadow_blk_ag M1 M' (fun a => in_shadow_of nb (2 * cap) a)); [| clear - Hcap; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ Q16) | exact HSB].
            intros a Ha. exact (FRS nb (2 * cap) a ltac:(clear - Q0; lia) ltac:(clear - Hcap; lia) Q7 Ha). }
          assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps q e = true -> bv_unsigned (edenot E' e) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
          { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
          unfold VSA.SIZE2 in *. unfold VSA.oE, VSA.nbE, VSA.bE, VSA.capE in *.
          eexists. eexists. split; [exact (ANEW_OK ((nb, 2 * cap) :: (b, cap) :: lb_remove b LB) FF LK1 (adebit L cr (2 * cap)) A1 o nb (2 * cap) (cap + 1) (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
          { unfold PMSA.a0, PMSA.a1, PMSA.u64, PMSA.acobj.
            split; [exact (REG 10%nat _ o Y10 W10)|]. split; [exact (REG 11%nat _ (cap + 1) Y11 ltac:(apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia]))|].
            split; [apply (CL5A.u64_full (hl_segs L) _ Hoff); pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Ya) ltac:(ev_start)) as G0; unfold CL5A.uv in G0; cbn [edenot] in G0; rewrite W44 in G0; exact G0|].
            split.
            { apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 16) (CELL _ Yc) ltac:(ev_start)) as G0.
              replace (CL5A.uv E' (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 33)) (EVar 44))) with (nb + 2 * cap) in G0; [exact G0|]. symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Q0 Q7 Hcap; lia]. }
            split; [left; exact Hofr|]. split; [exact Ho8|].
            split; [pose proof (CL5A.shz_elim (hl_segs L) E' _ (EVar 10) 3 o (CELL _ Ysh) ltac:(unfold CL5A.uv; cbn [edenot]; exact W10) ltac:(clear; lia)) as SZ; intros jj Hj; exact (CL5A.byte_full _ _ _ _ (SZ jj Hj))|].
            split; [left; reflexivity|]. split; [clear - Hcap; lia|]. split; [exact Hcap2|]. split; [exact (PmHeapIfaceA.shadow_blk_cont _ _ _ HSB')|]. clear - NBHI; lia. }
          {
            intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (HSC2 & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
            exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
            pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
            set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
            assert (HagE2 : env_agree GT.NF E0 E2).
            { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
            assert (NB2 : CL5A.uv E2 (EVar 44) = nb) by (unfold CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag2 44%nat) by (destruct HV as (_ & _ & HV3 & _); clear - HV3 Y44; lia); exact NB').
            split; [rewrite (DEN2 E' HagE'), NB'; apply incl_refl|].
            split.
            { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (CHA.SRL3 (EVar 44), VSA.SBz, VSA.SHN (EMd Instr.M_MUL (ELit 2) (EVar 33))). split; [left; reflexivity|].
              unfold CHA.in_reg, VSA.SHN. rewrite CL5A.estart_srl3. unfold elenZ. rewrite CHA.u_srl3. unfold CL5A.uv. cbn [edenot]. rewrite W44.
              replace (bv_unsigned (edenot E' (APC.eaddz (EMd Instr.M_MUL (ELit 2) (EVar 33)) 7))) with (2 * cap + 7) by (symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia]).
              unfold S, SB, VSA.SBz in *. exact Hin. }
            split.
            { intros w a [<-|[]] Hin (Ka & Kc & _). unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
              refine (CHA.obj_not_client L ar LYI (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) nb (2 * cap) a RFr (conj Q5 (conj Q6 Q7)) ltac:(clear - Hcap; lia) (CHA.mod8_of_16 _ Q16) Q4 Q1 _ Hfap (or_intror _) Kc).
              - intros bb Hbb. exact (Hbap bb (or_intror Hbb)).
              - exact (CL5A.blk_shadow_in nb (2 * cap) a (CHA.mod8_of_16 _ Q16) ltac:(clear - Hcap; lia) Hin). }
            split; [unfold CHA.curB; rewrite Y4, (DEN2 E2 HagE2), NB2; exact HH2|].
            split; [unfold Cred; rewrite (proj1 XJ9); reflexivity|].
            split.
            { unfold XI. cbv zeta. rewrite (proj1 XJ9), (proj1 (proj2 XJ9)), (proj2 (proj2 XJ9)), NB2. pose proof HP as (HP1 & HP2 & HP3).
              split; [exact HAFP|]. split; [|exact HSC2].
              intros k Hk. apply (HP3 (nb + k)); [clear - Hk Q0 Q7; lia | left; exists (nb, 2 * cap); split; [left; reflexivity | cbn [fst snd]; clear - Hk; lia] |].
              apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (HDF k Hk). }
            intros X0 HX0 _. unfold VSA.STAT in HX0. cbn [In] in HX0.
            destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). } }
        destruct (Z.eqb_spec pc VSA.PC_OPDEL) as [->|Hne5]; [|discriminate X].
        {
          apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y44].
          apply andb_prop in X as [X Y2]. apply andb_prop in X as [X Y1']. apply andb_prop in X as [Y0 Y1].
          apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y2. subst j. apply CH2.blocks_eqb_eq in Y3, Y4. apply Nat.ltb_lt in Y44. apply Nat.leb_le in Y1, Y1'.
          lazymatch type of Y5 with VSA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
          intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
          destruct (PRO i ltac:(clear - Y1; lia) E A1 M1 m1 HA HXi) as (HagE & HcF & HAFP & HDF). set (nb := CL5A.uv E (EVar 44)) in *.
          assert (XI9 : Nat.leb i 1 = false /\ Nat.leb i 5 = false /\ Nat.leb i 7 = false) by (split; [|split]; apply Nat.leb_gt; clear - Y1 Y1'; lia).
          assert (XJ11 : Nat.leb (i + 2) 1 = false /\ Nat.leb (i + 2) 5 = false /\ Nat.leb (i + 2) 7 = false) by (split; [|split]; apply Nat.leb_gt; clear - Y1 Y1'; lia).
          assert (HSC : shadow_cont M1 nb (2 * cap) (cap + 1)) by (unfold XI in HXi; rewrite (proj1 XI9), (proj1 (proj2 XI9)), (proj2 (proj2 XI9)) in HXi; exact (proj2 (proj2 HXi))).
          pose proof HAFP as (Hrng & Hbap & Hfap & NBHI). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
          assert (NE : nb <> b) by (pose proof (Hbap (b, cap) (or_introl eq_refl)) as AP; cbn [fst snd] in AP; clear - AP Hcap; lia).
          assert (LBR : lb_remove b ((nb, 2 * cap) :: (b, cap) :: lb_remove b LB) = (nb, 2 * cap) :: lb_remove b LB) by (cbn [lb_remove fst]; rewrite (proj2 (Z.eqb_neq nb b) NE), Z.eqb_refl; reflexivity).
          assert (HcB : CHA.curB (lb_remove b LB) G.BLS i E = (nb, 2 * cap) :: (b, cap) :: lb_remove b LB) by (unfold CHA.curB; rewrite Y3, (DEN2 E HagE); reflexivity).
          refine (CALLEE VSA.PC_OPDEL 4096 0%nat VSA.BNEW [] VSA.STAT None 0 i c ps (i + 2)%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
            [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
          rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
          destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
          assert (Hcr1 : cr1 = adebit L cr (2 * cap)) by (unfold Cred in HC1; rewrite (proj1 XI9) in HC1; exact HC1). subst cr1.
          assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
          assert (W32 : bv_unsigned (ev E' 32) = b) by (rewrite (FZ 32%nat eq_refl); exact U32).
          assert (NB' : CL5A.uv E' (EVar 44) = nb) by (unfold nb, CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by exact Y44; reflexivity).
          pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
          assert (HF2 : Forall (fun bb : Z * Z => 17594333495296 <= fst bb) [(nb, 2 * cap); (b, cap)]) by (constructor; [exact NBHI | constructor; [exact BHI | constructor]]).
          assert (FRS : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
          { intros q n a Hq Hn Hqn Ha. pose proof (SHR q n a Hq Hn Hqn Ha) as SRa.
            refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW WW G.BLS VSA.FFS Cred 4 STKF SCRP NF32 U2 WRS_OK
                      i c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil, Y3; exact YF|].
            rewrite FFSnil, Y3, (DEN2 E HagE). exact (NOFOOT _ a HF2 SRa). }
          unfold VSA.bE in *.
          eexists. eexists. split; [exact (OPDEL_OK ((nb, 2 * cap) :: (b, cap) :: lb_remove b LB) FF LK1 (adebit L cr (2 * cap)) A1 b cap (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
          { unfold PMSA.a0. split; [|right; left; reflexivity].
            replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
            rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y10). cbn [edenot]. rewrite (FZ 32%nat eq_refl). exact V32. }
          {
            intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (-> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2. rewrite LBR in HP, HH2 |- *.
            exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
            pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
            set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
            assert (HagE2 : env_agree GT.NF E0 E2).
            { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
            assert (NB2 : CL5A.uv E2 (EVar 44) = nb) by (unfold CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag2 44%nat) by (destruct HV as (_ & _ & HV3 & _); clear - HV3 Y44; lia); exact NB').
            split; [rewrite (DEN3 E' HagE'), NB'; apply incl_refl|]. split; [intros w a []|]. split; [intros w a []|].
            split; [unfold CHA.curB; rewrite Y4, (DEN3 E2 HagE2), NB2; exact HH2|].
            split; [unfold Cred; rewrite (proj1 XJ11); reflexivity|].
            split.
            { unfold XI. cbv zeta. rewrite (proj1 XJ11), (proj1 (proj2 XJ11)), (proj2 (proj2 XJ11)), NB2. pose proof HP as (HP1 & HP2 & HP3).
              split; [exact HAFP|]. split.
              - intros k Hk. apply (HP3 (nb + k)); [clear - Hk Q0 Q7; lia | left; exists (nb, 2 * cap); split; [left; reflexivity | cbn [fst snd]; clear - Hk; lia] |].
                apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (HDF k Hk).
              - apply (CL5A.shadow_cont_same M1 M2 nb (2 * cap) (cap + 1) ltac:(clear - Hcap; lia) (CHA.mod8_of_16 _ Q16)); [|exact HSC]. intros a Ha.
                pose proof (SHR nb (2 * cap) a ltac:(clear - Q0; lia) ltac:(clear - Hcap; lia) Q7 Ha) as SRa.
                rewrite (HP1 a); [exact (FRS nb (2 * cap) a ltac:(clear - Q0; lia) ltac:(clear - Hcap; lia) Q7 Ha)|].
                split; [clear - SRa; lia|]. split; [do 6 right; exists (nb, 2 * cap); split; [left; reflexivity | exact Ha] | intros w []]. }
            intros X0 HX0 _. unfold VSA.STAT in HX0. cbn [In] in HX0.
            destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). } }
      +
        apply andb_prop in X as [X Y44]. apply andb_prop in X as [X Yx]. apply andb_prop in X as [X Yblob]. apply andb_prop in X as [X Yc16]. apply andb_prop in X as [X Yc8]. apply andb_prop in X as [X Yc0].
        apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y1']. apply andb_prop in X as [X Y1]. apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [Y0 Xbase].
        apply Z.eqb_eq in Y0. subst pc. apply CH2.blocks_eqb_eq in Y3. apply Nat.ltb_lt in Y44. apply Nat.leb_le in Y1, Y1'.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
        destruct (PRO i ltac:(clear - Y1; lia) E A1 M1 m1 HA HXi) as (HagE & HcF & HAFP & HDF). set (nb := CL5A.uv E (EVar 44)) in *.
        assert (XI11 : Nat.leb i 1 = false /\ Nat.leb i 5 = false /\ Nat.leb i 7 = false) by (split; [|split]; apply Nat.leb_gt; clear - Y1 Y1'; lia).
        assert (HSC : shadow_cont M1 nb (2 * cap) (cap + 1)) by (unfold XI in HXi; rewrite (proj1 XI11), (proj1 (proj2 XI11)), (proj2 (proj2 XI11)) in HXi; exact (proj2 (proj2 HXi))).
        pose proof HAFP as (Hrng & Hbap & Hfap & NBHI). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
        refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW WW G.BLS VSA.FFS Cred 4 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                  K DEF0 R r EV Hra Hraok VSA.RETPC i c ps _ Xbase _ (FFSnil i) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
          [rewrite LS; exact VSA.ret_at | rewrite FFSnil, Y3; exact Xfoot |].
        intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
        assert (Hcr1 : cr1 = adebit L cr (2 * cap)) by (unfold Cred in HC1; rewrite (proj1 XI11) in HC1; exact HC1). subst cr1.
        assert (HB : CHA.curB (lb_remove b LB) G.BLS i E = (nb, 2 * cap) :: lb_remove b LB) by (unfold CHA.curB; rewrite Y3, (DEN3 E HagE); reflexivity). rewrite HB in HH1.
        assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
        assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
        assert (W33 : bv_unsigned (ev E' 33) = cap) by (rewrite (FZ 33%nat eq_refl); exact U33).
        assert (W35 : bv_unsigned (ev E' 35) = xm) by (rewrite (FZ 35%nat eq_refl); exact U35).
        assert (W44 : bv_unsigned (ev E' 44) = nb) by (unfold nb, CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by exact Y44; reflexivity).
        assert (CELL : forall X0, VSA.has (SR.ps_cells ps) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
        { intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0). }
        pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW G.BLS VSA.FFS Cred 4 i E A1 M' m' HA') as Hoff.
        unfold VSA.SIZE2 in *. unfold VSA.oE, VSA.nbE, VSA.capE, VSA.xvE in *. rewrite SCRV in HP.
        apply (Hcont fx' R' M' model2 ((nb, 2 * cap) :: lb_remove b LB) (adebit L cr (2 * cap)) (lb_remove b LB) WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
        exists nb. split.
        { unfold PMSA.a0. replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
          rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y10). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal.
          apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Q0 Q7 Hcap; lia]. }
        split.
        { unfold PMSA.vec_at, PMSA.u64. split; [|split]; apply (CL5A.u64_full (hl_segs L) _ Hoff).
          - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Yc0) ltac:(ev_start)) as G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite W44 in G0. exact G0.
          - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 8) (CELL _ Yc8) ltac:(ev_start)) as G0.
            replace (CL5A.uv E' (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 33) (EVar 44)) (ELit 1))) with (nb + (cap + 1)) in G0; [exact G0 | symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Q0 Q7 Hcap; lia]].
          - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 16) (CELL _ Yc16) ltac:(ev_start)) as G0.
            replace (CL5A.uv E' (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 33)) (EVar 44))) with (nb + 2 * cap) in G0; [exact G0 | symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Q0 Q7 Hcap; lia]]. }
        split.
        { apply (CL5.bytes_at_app (hl_segs L)).
          - apply (CL5A.bytes_full (hl_segs L) _ Hoff). refine (proj1 (CL5.kblob_elim (hl_segs L) E' _ _ _ 0%nat nb st (CELL _ Yblob) ltac:(ev_start) _)). rewrite <- (proj2 HagE'). reflexivity.
          - intros k Hk. cbn [length] in Hk. assert (k = 0%nat) by (clear - Hk; lia). subst k. cbn [nth]. rewrite Z.add_0_r, HlenEq.
            pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (nb + cap) (CELL _ Yx)) as G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite W35 in G0.
            apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0; [|rewrite (CL5.estart_lin E' _ 0 (nb + cap)); [clear; lia | lin_eval; rw_atoms; clear; lia | clear - Q0 Q7 Hcap; lia]].
            unfold L5.u8_at in *. unfold eqz in Exm. rewrite Exm, byte_mod in G0. exact G0. }
        split; [|split; [reflexivity | split; [reflexivity | split; reflexivity]]].
        unfold PMSA.afresh_cont. split; [exact Hrng|]. split; [intros bb Hbb; exact (Hbap bb (or_intror Hbb))|]. split; [exact Hfap|]. split.
        { intros k Hk. apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (HDF k Hk). }
        apply (CL5A.shadow_cont_same M1 M' nb (2 * cap) (cap + 1) ltac:(clear - Hcap; lia) (CHA.mod8_of_16 _ Q16)); [|exact HSC]. intros a Ha.
        pose proof (SHR nb (2 * cap) a ltac:(clear - Q0; lia) ltac:(clear - Hcap; lia) Q7 Ha) as SRa.
        refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW WW G.BLS VSA.FFS Cred 4 STKF SCRP NF32 U2 WRS_OK
                  i c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil, Y3; exact Xfoot|].
        rewrite FFSnil, Y3, (DEN3 E HagE). apply (NOFOOT _ a); [constructor; [exact NBHI | constructor] | exact SRa].
    - exact Hc0.
    - exact HAt0.
    -
      assert (Hk0 : Nat.leb i0 1 = true) by (apply Nat.leb_le; clear - Hi0; lia).
      assert (HB0 : CH2.den E0 (nth i0 G.BLS []) = [(b, cap)]).
      { assert (HBL : nth i0 G.BLS [] = VSA.BOLD) by (do 2 (destruct i0 as [|i0]; [reflexivity|]); exfalso; clear - Hi0; lia). rewrite HBL. exact (DEN1 E0 (CC.env_agree_refl _ _)). }
      split.
      + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
        split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
        exists cr, LK. unfold CHA.curB, CHA.curF. rewrite HB0, FFSnil. cbn [app CHA.denF map length]. split; [exact (CBA.own_front L ar C HI HIok _ _ _ _ _ _ _ b cap HH HinLB)|].
        split; [apply incl_refl|]. split; [unfold Cred; rewrite Hk0; reflexivity | exact Hroom].
      + unfold XI. rewrite Hk0. exact Hshc.
    - exact Hfp. }

  assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
    by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
  assert (VO : CL5A.visr (ahid A model) o 24).
  { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + k) RFx Hofr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (VX : CL5A.visr (ahid A model) xa 1).
  { intros k Hk. destruct (CL5A.acobj_wok L ar LB FF sp 0 xa 1 (xa + k) RFx CSP Hxfr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (VSO : forall j, 0 <= j < 3 -> ahid A model (Z_to_bv 64 (S o + j)) = false).
  { intros j Hj. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o 24 (S o + j) RFx Hofr ltac:(clear; lia) (CL5A.shreg_in_shadow o 3 (S o + j) Ho8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
    exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (VSX : ahid A model (Z_to_bv 64 (S xa)) = false).
  { destruct (CL5A.acobj_sh_wok L ar LB FF sp 0 xa 1 (S xa) RFx CSP Hxfr ltac:(clear; lia) (CL5A.shreg1_in_shadow xa _ eq_refl)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (VB : CL5A.visr (ahid A model) b cap).
  { intros k Hk. apply CLV; [clear - Hk B0 B7; lia | left; exists (b, cap); split; [exact HinLB | cbn [fst snd]; clear - Hk; lia] |].
    apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hk BHI. lia. }
  assert (VS : CL5A.visr (ahid A model) (sp - 8192) 8192).
  { intros k Hk. apply CLV; [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
    apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hk S2 CL. lia. }
  assert (VSS : forall j, 0 <= j < 5 -> ahid A model (Z_to_bv 64 (S (sp - 88) + j)) = false).
  { intros j Hj. pose proof (CL5A.shreg_in_shadow (sp - 88) 5 (S (sp - 88) + j) SP8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia)) as SH. change (8 * 5) with 40 in SH.
    destruct (SSH _ SH) as (G1 & G2 & G3). apply CLV; [exact G1 | | exact G3].
    eapply CHA.aclient_scr; [| intros y Hy; clear - Hy; lia].
    eapply CHA.aclient_incl; [intros z Hz; exact (L5C.in_lb_remove b z LB Hz) | apply incl_refl | exact (aclientw_client _ _ _ _ _ _ _ G2)]. }
  set (Mv := CCA.vis A model M).
  assert (DO : L5.defined Mv o 24).
  { apply (CL5A.defined_vis _ M o 24 VO). destruct Hofr as (f & Hf & F1 & F2). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WF f Hf) as (_ & _ & _ & _ & Fdef & _).
    intros k Hk. replace (o + k) with (ff_addr f + (o - ff_addr f + k)) by (clear; lia). apply Fdef. clear - Hk F1 F2. lia. }
  assert (DB : L5.defined Mv b cap) by (apply (CL5A.defined_vis _ M b cap VB); exact Bdef).
  assert (DS : L5.defined Mv (sp - 8192) 8192) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
  pose proof (CL5A.gran_blk cap ltac:(clear - Hcap; lia)) as GB.
  assert (COMMON : Forall (kentry_ok (hl_segs L) E0 Mv) (firstn 38 (CC.cp_know G.cp0))).
  { cbn [firstn CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kword64_intro with (A := o) (z := b); [ev_start | clear - O3; lia | clear - O6; lia | exact V32 |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 o 8 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hw0].
    + eapply CL5.kword64_intro with (A := o + 8) (z := b + cap); [ev_start | clear - O3; lia | clear - O6; lia | |].
      * rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hcap; lia].
      * apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 (o + 8) 8 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hw8].
    + eapply CL5.kword64_intro with (A := o + 16) (z := b + cap); [ev_start | clear - O3; lia | clear - O6; lia | |].
      * rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hcap; lia].
      * apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 (o + 16) 8 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hw16].
    + eapply CL5.kwr_intro with (A := o) (N := 24); [ev_start | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO CL SP1; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact Ho8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 3 o); [exact U10 | clear; lia | clear - O3 O6; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VSO j Hj) | exact (Hosh j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 24); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5A.kword8_intro with (A := xa) (z := xm); [ev_start | clear - X3; lia | clear - X6; lia | exact V35 | clear - XM; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [clear - X3; lia | clear - X6; lia | exact VX | exact Hxm].
    + eapply CL5.krange_intro with (v := xm); [lin_eval; rw_atoms; clear; lia | clear - XM; lia | clear - XM; lia].
    + eapply CL5.krange_intro with (v := xa); [lin_eval; rw_atoms; clear; lia | clear - X3 X6; lia | unfold hid in X1; clear - X1 X6 FSLO CL; lia].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := xa) (N2 := 1); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in X5; clear - X5; lia].
    + apply (CL5A.shbyte_intro (hl_segs L) E0 Mv _ _ xa shv); [exact U11 | exact V34 | clear - SHVR; lia | clear - X3 X6; lia | apply CL5A.byte_vis; [exact VSX | exact Hshv]].
    + eapply CL5.kblob_intro with (bs := st) (A := b); [ev_start | unfold elenZ; cbn [edenot]; rewrite U33; clear - HlenEq; lia | clear - B0; lia | clear - B7 HlenEq; lia | clear - B0 B7 B3; lia | reflexivity | |].
      * apply (CL5A.bytes_vis (hl_segs L)); [clear - B0; lia | clear - B7 HlenEq; lia | rewrite HlenEq; exact VB | exact Hbytes].
      * rewrite HlenEq. exact DB.
    + eapply CL5.kwr_intro with (A := b) (N := cap); [ev_start | unfold elenZ; cbn [edenot]; exact U33 | clear - B0; lia | clear - B7; lia | clear - B0 B7 B3; lia | exact DB].
    + eapply CL5.krange_intro with (v := b); [lin_eval; rw_atoms; clear; lia | clear - B0 B7 B3; lia | clear - BHI B4 B3 SP1; lia].
    + eapply CL5.kalign_intro with (v := b); [lin_eval; rw_atoms; clear; lia | clear - B0 B7 B3; lia | clear; lia | exact B16].
    + eapply CL5.krange_intro with (v := cap); [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia | clear - Hcap4 Hcap2; lia].
    + eapply CL5.kunk_intro with (A := sp - 8192) (N := 8192); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 8192) (N := 8192); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 5 (sp - 88)); [apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia] | clear; lia | clear - S2 S3 CL SP1; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VSS j Hj)|].
      replace (S (sp - 88) + j) with (S (sp - 8192) + (1013 + j)) by (replace (sp - 88) with (sp - 8192 + 8104) by (clear; lia); rewrite (CL5A.S_add_al (sp - 8192) 8104 AL8192); change (8104 / 8) with 1013; clear; lia).
      apply Hstksh. split; [clear - Hj; lia|]. enough (GE : 1013 + j + 1 <= (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 8192)) / 8) by (clear - GE; lia). apply Z.div_le_lower_bound; [clear; lia|]. clear - Hj S3. lia.
    + eapply CL5.kdisj_intro with (A1 := sp - 8192) (N1 := 8192) (A2 := o) (N2 := 24); [ev_start | reflexivity | ev_start | reflexivity | clear - O4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 8192) (N1 := 8192) (A2 := xa) (N2 := 1); [ev_start | reflexivity | ev_start | reflexivity | unfold hid in X4; clear - X4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 8192) (N1 := 8192) (A2 := b) (N2 := cap); [ev_start | reflexivity | ev_start | unfold elenZ; cbn [edenot]; exact U33 | clear - B4 S2; lia].
    + destruct Hofr as (f & Hf & F1 & F2). pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF.
      eapply CL5.kdisj_intro with (A1 := o) (N1 := 24) (A2 := b) (N2 := cap); [ev_start | reflexivity | ev_start | unfold elenZ; cbn [edenot]; exact U33 | clear - QF F1 F2; lia].
    + eapply CL5.kdisj_intro with (A1 := xa) (N1 := 1) (A2 := b) (N2 := cap); [ev_start | reflexivity | ev_start | unfold elenZ; cbn [edenot]; exact U33 |].
      destruct Hxfr as [(f & Hf & F1 & F2)|(XS1 & XS2)]; [pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF; clear - QF F1 F2; lia | clear - XS1 B4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := o) (N1 := 24) (A2 := xa) (N2 := 1); [ev_start | reflexivity | ev_start | reflexivity | unfold hid in Hxo; clear - Hxo; lia].
    + destruct Hofr as (f & Hf & F1 & F2). pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF. destruct (CHA.frm_align L ar LB FF LK cr A M f WF Hf) as (FA & FB & _).
      eapply CL5.kdisj_intro with (A1 := o / 8 + SB) (N1 := 3) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U10; reflexivity | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U32; reflexivity
        | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      destruct QF as [QF|QF].
      * right. pose proof (CL5A.gran_le b ((cap + 7) / 8) (ff_addr f) (CHA.mod8_of_64 _ FA) ltac:(clear - QF GB; lia)) as G1. pose proof (CL5A.div8_le (ff_addr f) o ltac:(clear - F1; lia)) as G2. clear - G1 G2. lia.
      * left. pose proof (CL5A.gran_le o 3 (ff_addr f + ff_bytes (ff_class f)) (CL5A.al64_add8 _ _ FA FB) ltac:(clear - F2; lia)) as G1. pose proof (CL5A.div8_le _ b QF) as G2. clear - G1 G2. lia.
    + eapply CL5.kdisj_intro with (A1 := xa / 8 + SB) (N1 := 1) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U11; reflexivity | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U32; reflexivity
        | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      unfold al in C8.
      destruct Hxfr as [(f & Hf & F1 & F2)|(XS1 & XS2)];
        [|right; pose proof (CL5A.gran_le b ((cap + 7) / 8) (ahl_ceil ar) C8 ltac:(clear - B4 GB; lia)) as G1; pose proof (CL5A.div8_le (ahl_ceil ar) xa ltac:(clear - XS1 S2; lia)) as G2; clear - G1 G2; lia].
      pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF. destruct (CHA.frm_align L ar LB FF LK cr A M f WF Hf) as (FA & FB & _). destruct QF as [QF|QF].
      * right. pose proof (CL5A.gran_le b ((cap + 7) / 8) (ff_addr f) (CHA.mod8_of_64 _ FA) ltac:(clear - QF GB; lia)) as G1. pose proof (CL5A.div8_le (ff_addr f) xa ltac:(clear - F1; lia)) as G2. clear - G1 G2. lia.
      * left. pose proof (CL5A.gran_le xa 1 (ff_addr f + ff_bytes (ff_class f)) (CL5A.al64_add8 _ _ FA FB) ltac:(clear - F2; lia)) as G1. pose proof (CL5A.div8_le _ b QF) as G2. clear - G1 G2. lia.
    + destruct (CL5A.shreg_bounds b cap ltac:(clear - B0; lia) ltac:(clear - Hcap; lia) B7 (CHA.mod8_of_16 _ B16)) as (G1 & G2).
      eapply CL5.kdisj_intro with (A1 := o) (N1 := 24) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [ev_start | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U32; reflexivity
        | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      unfold hid in O5. unfold SB in *. clear - O5 G1 G2. lia.
    + destruct (CL5A.shreg_bounds b cap ltac:(clear - B0; lia) ltac:(clear - Hcap; lia) B7 (CHA.mod8_of_16 _ B16)) as (G1 & G2).
      eapply CL5.kdisj_intro with (A1 := xa) (N1 := 1) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [ev_start | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U32; reflexivity
        | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      unfold hid in X5. unfold SB in *. clear - X5 G1 G2. lia.
    +
      unfold al in C8.
      eapply CL5.kdisj_intro with (A1 := (sp - 88) / 8 + SB) (N1 := 5) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [rewrite CL5A.estart_srl3'; f_equal; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia] | reflexivity
        | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U32; reflexivity
        | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      right. pose proof (CL5A.gran_le b ((cap + 7) / 8) (sp - 88) SP8 ltac:(clear - B4 GB S2; lia)) as G1. clear - G1. lia.
    + eapply CL5.kdisj_intro with (A1 := o / 8 + SB) (N1 := 3) (A2 := (sp - 88) / 8 + SB) (N2 := 5);
        [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U10; reflexivity | reflexivity
        | rewrite CL5A.estart_srl3'; f_equal; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia] | reflexivity |].
      left. pose proof (CL5A.gran_le o 3 (sp - 88) SP8 ltac:(clear - O4 S2; lia)) as G1. clear - G1. lia.
    + destruct (CL5A.shreg_bounds b cap ltac:(clear - B0; lia) ltac:(clear - Hcap; lia) B7 (CHA.mod8_of_16 _ B16)) as (G1 & G2).
      eapply CL5.kdisj_intro with (A1 := sp - 8192) (N1 := 8192) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [ev_start | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U32; reflexivity
        | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      unfold SB in *. clear - S2 CL G1 G2. lia. }

  assert (HAND : forall e v, bv_unsigned (edenot E0 e) = v -> bv_unsigned (edenot E0 (EAlu Instr.ALU_AND e (ELit 7))) = v mod 8) by (intros e v <-; apply CL5A.u_and7).
  assert (CX0 : shv = 0 -> kentry_ok (hl_segs L) E0 Mv (KRange (EVar 34) 0 0)) by (intros Hz; eapply CL5.krange_intro with (v := shv); [lin_eval; rw_atoms; clear; lia | clear - SHVR; lia | clear - Hz; lia]).
  assert (CX1 : 1 <= shv <= 7 -> kentry_ok (hl_segs L) E0 Mv (KRange (EVar 34) 1 7)) by (intros Hz; eapply CL5.krange_intro with (v := shv); [lin_eval; rw_atoms; clear; lia | clear - SHVR; lia | clear - Hz; lia]).
  assert (CX2 : 1 <= shv <= 7 -> ltm xa 8 shv -> kentry_ok (hl_segs L) E0 Mv (KRange (EAlu Instr.ALU_ADD (EVar 34) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_AND (EVar 11) (ELit 7)))) 1 7)).
  { intros Hz Hl. unfold ltm in Hl. pose proof (Z.mod_pos_bound xa 8 ltac:(clear; lia)) as MB.
    eapply CL5.krange_intro with (v := shv - xa mod 8); [lin_form; rewrite (HAND (EVar 11) xa U11); cbn [edenot]; rw_atoms; clear; lia | clear - Hz Hl MB; lia | clear - Hz Hl MB; lia]. }
  assert (ATI : forall c tl, firstn 38 (CC.cp_know c) = firstn 38 (CC.cp_know G.cp0) -> skipn 38 (CC.cp_know c) = tl -> CC.cp_regs c = CC.cp_regs G.cp0 ->
            Forall (kentry_ok (hl_segs L) E0 Mv) tl -> CCA.AtV (hl_segs L) c E0 R A M model).
  { intros c tl H1 H2 H3 HT. split; [rewrite H3; exact (regs_ok_id R _ _)|]. unfold know_ok. rewrite <- (firstn_skipn 38 (CC.cp_know c)), H1, H2. apply Forall_app. split; [exact COMMON | exact HT]. }
  unfold hid in Hshr. destruct Hshr as [Hs0|[Hs1 Hs2]].
  - apply (MAIN 0%nat G.cp0 eq_refl ltac:(clear; lia) eq_refl). apply (ATI G.cp0 [_] eq_refl eq_refl eq_refl). apply Forall_cons; [exact (CX0 Hs0) | apply Forall_nil].
  - apply (MAIN 1%nat G.cp1 eq_refl ltac:(clear; lia) eq_refl). apply (ATI G.cp1 [_; _] eq_refl eq_refl eq_refl). apply Forall_cons; [exact (CX1 Hs1) | apply Forall_cons; [exact (CX2 Hs1 Hs2) | apply Forall_nil]].
Qed.

End VecPushSlowOk.
