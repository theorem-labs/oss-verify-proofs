(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PB4.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Record pvals2 : Type := PV2 { pv_level : expr; pv_wend : expr; pv_wptr : expr; pv_st : expr; pv_sst : expr; pv_nst : expr; pv_more : expr; pv_done : expr; pv_size : expr;
                              pv_sb : expr; pv_send : expr; pv_scend : expr }.
Definition win_of (p e : Z) : option (Z * Z) := if Z.eqb e 0 then None else Some (p, e).
Definition pview2 (cells : list kentry) (Pb pe ce : expr) : option pvals2 :=
  match CAX.cell_at cells Pb 144 4, CAX.cell_at cells Pb 192 8, CAX.cell_at cells Pb 200 8, CAX.cell_at cells Pb 208 1, CAX.cell_at cells Pb 209 1,
        CAX.cell_at cells Pb 210 1, CAX.cell_at cells Pb 211 1, CAX.cell_at cells Pb 212 1, CAX.cell_at cells Pb 232 8,
        CAX.cell_at cells Pb 248 8, CAX.cell_at cells Pb 256 8, CAX.cell_at cells Pb 264 8 with
  | Some lvl, Some wend, Some wptr, Some st, Some sst, Some nst, Some more, Some done, Some se, Some csb, Some csend, Some cscend =>
      if (PB2.pconst_chk cells Pb && PB.str_pat cells Pb 224 pe ce se 264 67108864)%bool
      then Some (PV2 lvl wend wptr st sst nst more done se csb csend cscend) else None
  | _, _, _, _, _, _, _, _, _, _, _, _ => None
  end.

Lemma parser_view2 : forall E (M : mem) cells Pb pe ce pv P (bm bd : bool) (stack : list Z) scap,
  know_ok RSEGS E M cells -> pview2 cells Pb pe ce = Some pv ->
  uv E Pb = P -> 2 ^ 32 <= P -> P + 272 <= 2 ^ 63 ->
  uv E (pv_more pv) = PML.b2z bm -> uv E (pv_done pv) = PML.b2z bd ->
  L5.bytes_at RSEGS M (uv E (pv_sb pv)) stack -> uv E (pv_send pv) = uv E (pv_sb pv) + Z.of_nat (length stack) -> uv E (pv_scend pv) = uv E (pv_sb pv) + scap -> Z.of_nat (length stack) <= scap ->
  uv E (pv_wptr pv) <= uv E (pv_wend pv) ->
  L5.defined M P 272 ->
  exists buf : list Z,
    PML.parser_at M P (PML.PS (uv E (pv_st pv)) (uv E (pv_sst pv)) (uv E (pv_nst pv)) bm bd (uv E (pv_level pv)) stack (uv E (pv_sb pv)) scap (uv E ce) (uv E pe) buf
                              (win_of (uv E (pv_wptr pv)) (uv E (pv_wend pv))))
    /\ Z.of_nat (length buf) = uv E (pv_size pv) /\ 264 <= uv E ce <= 2 ^ 27 /\ uv E ce mod 8 = 0 /\ 4096 <= uv E pe <= 2 ^ 47 /\ L5.defined M (uv E pe) (uv E ce).
Proof.
  intros E M cells Pb pe ce pv P bm bd stack scap HK HV HP P0 P1 Hm Hd Hst HS1 HS2 HS3 Hwin Hdef.
  unfold pview2 in HV.
  destruct (CAX.cell_at cells Pb 144 4) as [lvl|] eqn:C144; [|discriminate]. destruct (CAX.cell_at cells Pb 192 8) as [wend|] eqn:C192; [|discriminate].
  destruct (CAX.cell_at cells Pb 200 8) as [wptr|] eqn:C200; [|discriminate]. destruct (CAX.cell_at cells Pb 208 1) as [st|] eqn:C208; [|discriminate].
  destruct (CAX.cell_at cells Pb 209 1) as [sst|] eqn:C209; [|discriminate]. destruct (CAX.cell_at cells Pb 210 1) as [nst|] eqn:C210; [|discriminate].
  destruct (CAX.cell_at cells Pb 211 1) as [more|] eqn:C211; [|discriminate]. destruct (CAX.cell_at cells Pb 212 1) as [done|] eqn:C212; [|discriminate].
  destruct (CAX.cell_at cells Pb 232 8) as [se|] eqn:C232; [|discriminate].
  destruct (CAX.cell_at cells Pb 248 8) as [csb|] eqn:C248; [|discriminate]. destruct (CAX.cell_at cells Pb 256 8) as [csend|] eqn:C256; [|discriminate].
  destruct (CAX.cell_at cells Pb 264 8) as [cscend|] eqn:C264; [|discriminate].
  lazymatch type of HV with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection HV as <-. cbn [pv_level pv_wend pv_wptr pv_st pv_sst pv_nst pv_more pv_done pv_size pv_sb pv_send pv_scend] in *.
  apply andb_prop in Hb as [B1 B2].
  assert (ES : forall k, estart E (SA Pb k) = P + k) by (intros k; unfold estart; cbn [a_base a_off]; fold (uv E Pb); rewrite HP; reflexivity).
  destruct (PB.str_view E M cells Pb 224 pe ce se 264 67108864 HK B2 ltac:(lia) ltac:(rewrite ES; lia) ltac:(rewrite ES; lia)) as (buf & Hstr & Hlen & Hcap & Hlt & Hsm & Hc8 & Hpr & Hpdef).
  rewrite ES in Hstr.
  exists buf. split; [|repeat split; try lia; try assumption].
  unfold PB2.pconst_chk, PB2.hasw in B1.
  repeat (let X := fresh "K" in apply andb_prop in B1 as [B1 X]; apply (PB.has_ok E M _ _ HK) in X).
  apply (PB.has_ok E M _ _ HK) in B1.
  pose proof (fun k w v (H : kentry_ok RSEGS E M (KWord (SA Pb k) w v)) => H) as _.
  assert (U8 : forall k v z, kentry_ok RSEGS E M (KWord (SA Pb k) 1 v) -> uv E v = z -> PML.u8 M (P + k) z).
  { intros k v z H <-. apply (PB2.kword8_elim E M _ _ _ H). apply ES. }
  assert (U32 : forall k v z, kentry_ok RSEGS E M (KWord (SA Pb k) 4 v) -> uv E v = z -> PML.u32 M (P + k) z).
  { intros k v z H <-. apply (PB2.kword32_elim E M _ _ _ H). apply ES. }
  assert (U64 : forall k v z, kentry_ok RSEGS E M (KWord (SA Pb k) 8 v) -> uv E v = z -> PML.u64 M (P + k) z).
  { intros k v z H <-. apply (PB2.kword64_elim E M _ _ _ H). apply ES. }
  assert (LIT : forall z, 0 <= z < 2 ^ 64 -> uv E (ELit z) = z) by (intros; apply PB2.uv_lit; assumption).
  assert (SHORT : forall k, kentry_ok RSEGS E M (KWord (SA Pb k) 1 (ELit 0)) -> kentry_ok RSEGS E M (KWord (SA Pb (k + 1)) 1 (ELit 0)) -> L5.lstr_short RSEGS M (P + k) []).
  { intros k H1 H2. split; [cbn; lia|]. cbn [length]. split; [exact (U8 k _ 0 H1 (LIT 0 ltac:(lia)))|]. split; [intros i Hi; cbn in Hi; lia|].
    replace (P + k + 1 + Z.of_nat 0) with (P + (k + 1)) by lia. exact (U8 (k + 1) _ 0 H2 (LIT 0 ltac:(lia))). }
  pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C144) as D144. pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C192) as D192. pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C200) as D200.
  pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C208) as D208. pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C209) as D209. pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C210) as D210.
  pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C211) as D211. pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C212) as D212.
  pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C248) as D248. pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C256) as D256. pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C264) as D264.
  unfold PML.parser_at. cbn [PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win].
  split; [replace P with (P + 0) by lia; apply (U64 0 _ _ B1); apply LIT; unfold PML.VT_PARSER; lia|].
  split; [apply (U32 8 _ _ K16); apply LIT; lia|].
  split; [apply (U8 12 _ _ K15); apply LIT; lia|]. split; [apply (U8 13 _ _ K14); apply LIT; lia|]. split; [apply (U8 14 _ _ K13); apply LIT; lia|].
  split; [apply (U8 15 _ _ K12); apply LIT; lia|]. split; [apply (U8 16 _ _ K11); apply LIT; lia|]. split; [apply (U8 17 _ _ K10); apply LIT; lia|].
  split; [apply (U8 18 _ _ K9); apply LIT; lia|].
  split; [exact (SHORT 24 K8 K7)|]. split; [exact (SHORT 48 K6 K5)|]. split; [exact (SHORT 72 K4 K3)|].
  split; [apply (U64 96 _ _ K2); apply LIT; unfold PML.VT_FUNC; lia|].
  split; [apply (U64 128 _ _ K1); rewrite PB.uv_eaddz, HP; apply Z.mod_small; lia|].
  split; [exact (U32 144 _ _ D144 eq_refl)|].
  split; [unfold win_of; destruct (Z.eqb_spec (uv E wend) 0) as [Hz|Hz]; [split; [apply (U64 192 _ _ D192); exact Hz | apply (U64 200 _ _ D200); pose proof (PB.uv_range E wptr); lia] | split; [exact (U64 200 _ _ D200 eq_refl) | split; [exact (U64 192 _ _ D192 eq_refl) | exact Hwin]]]|].
  split; [exact (U8 208 _ _ D208 eq_refl)|]. split; [exact (U8 209 _ _ D209 eq_refl)|]. split; [exact (U8 210 _ _ D210 eq_refl)|].
  split; [exact (U8 211 _ _ D211 Hm)|]. split; [exact (U8 212 _ _ D212 Hd)|].
  split; [apply (U8 213 _ _ K0); apply LIT; lia|]. split; [apply (U32 216 _ _ K); apply LIT; lia|].
  split; [exact Hstr|]. split; [lia|].
  split; [exact (U64 248 _ _ D248 eq_refl)|].
  split; [exact (U64 256 _ _ D256 HS1)|].
  split; [exact (U64 264 _ _ D264 HS2)|].
  split; [exact Hst|]. split; [lia | exact Hdef].
Qed.

Definition str_pat0 (cells : list kentry) (ob : expr) (ok : Z) (pe ce : expr) (kmin2 : Z) : bool :=
  (PB.has cells (KWord (SA ob ok) 8 (APC.eaddz ce 1)) && PB.has cells (KWord (SA ob (ok + 8)) 8 (ELit 0)) && PB.has cells (KWord (SA ob (ok + 16)) 8 pe)
   && PB.has cells (KWord (SA pe 0) 1 (ELit 0)) && PB.has cells (KAlign ce 8)
   && PB.prove cells (KRange ce kmin2 134217728) && PB.prove cells (KRange pe 4096 140737488355328))%bool.
Definition str_patx (cells : list kentry) (ob : expr) (ok : Z) (pe ce se : expr) (kmin2 smax : Z) : bool :=
  (PB.str_pat cells ob ok pe ce se kmin2 smax || (expr_eqb se (ELit 0) && Z.leb 0 smax && str_pat0 cells ob ok pe ce kmin2))%bool.
Lemma str_viewx : forall E (M : mem) cells ob ok pe ce se kmin2 smax,
  know_ok RSEGS E M cells -> str_patx cells ob ok pe ce se kmin2 smax = true -> 24 <= kmin2 ->
  0 <= estart E (SA ob ok) -> estart E (SA ob ok) + 24 <= 2 ^ 64 -> L5.defined M (uv E pe) (uv E ce) ->
  let o := estart E (SA ob ok) in let p := uv E pe in let cap := uv E ce in let size := uv E se in
  exists s : list Z, PML.str_at M o (PML.SLong cap p s) /\ Z.of_nat (length s) = size /\ kmin2 <= cap <= 2 ^ 27 /\ size < cap /\ size <= smax /\ cap mod 8 = 0
                     /\ 4096 <= p <= 2 ^ 47 /\ L5.defined M p cap.
Proof.
  intros E M cells ob ok pe ce se kmin2 smax HK HP Hk Ho0 Ho1 Hdef. cbv zeta. unfold str_patx in HP. apply orb_prop in HP as [HP|HP].
  - exact (PB.str_view E M cells ob ok pe ce se kmin2 smax HK HP Hk Ho0 Ho1).
  - apply andb_prop in HP as [HP P0]. apply andb_prop in HP as [Hse Hsm]. apply expr_eqb_eq in Hse. apply Z.leb_le in Hsm. subst se. unfold str_pat0 in P0.
    apply andb_prop in P0 as [P0 P7]. apply andb_prop in P0 as [P0 P6]. apply andb_prop in P0 as [P0 P5]. apply andb_prop in P0 as [P0 P4]. apply andb_prop in P0 as [P0 P3]. apply andb_prop in P0 as [P1 P2].
    pose proof (PB.has_ok E M _ _ HK P1) as C1. pose proof (PB.has_ok E M _ _ HK P2) as C2. pose proof (PB.has_ok E M _ _ HK P3) as C3. pose proof (PB.has_ok E M _ _ HK P4) as C4.
    pose proof (PB.has_ok E M _ _ HK P5) as C5. pose proof (PB.prove_ok E M _ _ HK P6) as C6. pose proof (PB.prove_ok E M _ _ HK P7) as C7.
    cbn [kentry_ok] in C5, C6, C7. fold (uv E ce) in C5, C6. fold (uv E pe) in C7.
    set (cap := uv E ce) in *. set (p := uv E pe) in *. set (o := estart E (SA ob ok)) in *. destruct C5 as [_ Hal].
    assert (U0 : uv E (ELit 0) = 0) by (apply PB2.uv_lit; lia). rewrite U0.
    exists []. cbn [length]. split; [|repeat split; try lia; exact Hdef].
    unfold PML.str_at. split; [|split; [exact Hal | cbn [length]; lia]].
    unfold L5.lstr_long. cbn [length].
    assert (Hev : Z.even cap = true).
    { pose proof (Z.div_mod cap 8 ltac:(lia)) as D. rewrite Hal in D. rewrite D. rewrite Z.add_0_r, Z.even_mul. reflexivity. }
    split; [rewrite Z.bit0_odd, Z.odd_add, <- Z.negb_even, Hev; reflexivity|].
    split; [apply (CL5.kword64_elim RSEGS E M _ _ o (cap + 1) C1); [reflexivity | fold (uv E (APC.eaddz ce 1)); rewrite PB.uv_eaddz; fold cap; apply Z.mod_small; lia]|].
    split; [apply (CL5.kword64_elim RSEGS E M _ _ (o + 8) 0 C2); [unfold o, estart; cbn [a_base a_off]; lia | exact U0]|].
    split; [apply (CL5.kword64_elim RSEGS E M _ _ (o + 16) p C3); [unfold o, estart; cbn [a_base a_off]; lia | reflexivity]|].
    split; [intros i Hi; cbn [length] in Hi; lia|].
    apply (CL5.kword8_zero_elim RSEGS E M _ (p + 0) C4). unfold estart. cbn [a_base a_off]. fold (uv E pe). fold p. reflexivity.
Qed.

Section Inst4.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable LBrest : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
Variable Cred : nat -> env -> credit -> Prop.
Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L LBrest sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Variable XI : nat -> env -> mem -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - CH.hd_scr d) (CH.hd_scr d).
Hypothesis HEAPCHK : CH2.heap_chk3 NF d BLS CPS TAGS = true.

Hypothesis CRED_BLK : forall i j E E2 cr, CH2.den E2 (nth j BLS []) = CH2.den E (nth i BLS []) -> Cred i E cr -> Cred j E2 cr.

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.
Abbreviation AMB3 := (CH2.amb3 L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred XI).
Abbreviation HAMB := (CH2.heap_amb L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).

Lemma reenter_leaf_ok : forall i c k ps pc j cj,
  is_leaf i c k ps (CC.TOther pc) -> nth_error CPS j = Some cj -> CC.cp_pc cj = SR.ps_pc ps ->
  (forall E E' R R' (M M' : mem) model, CC.At (hl_segs L) c E R M -> HAMB i E M' model -> XI i E M -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     exists E2, CC.At (hl_segs L) cj E2 R' M' /\ env_agree NF E0 E2 /\ CH2.cur LBrest BLS j E2 = CH2.cur LBrest BLS i E /\ (forall cr, Cred i E cr -> Cred j E2 cr) /\
                XI j E2 M' /\ CC.meas cj E2 < CC.meas c E) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros i c k ps pc j cj IL Hcj Hpc USER fx' E R M model E' R' M' HAt [HA HX] HFP Hag HLF HIH.
  pose proof (CH2.leaf_amb3 L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 W_ok WRS_ok CPS TAGS HEAPCHK i c k ps pc IL E E' R R' M M' model HAt HA Hag HLF) as HA'.
  destruct (USER E E' R R' M M' model HAt HA' HX Hag HLF) as (E2 & HAt2 & HagE2 & Hcur & HC2 & HX2 & Hm).
  rewrite <- Hpc. apply (HIH j cj fx' E2 R' M' model Hcj HAt2); [| exact HFP | exact Hm].
  split; [|exact HX2].
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  split; [exact Hmo|]. split; [exact Hbv|]. split; [exact HagE2|]. split; [exists cr; split; [rewrite Hcur; exact HH | exact (HC2 cr HC)]|]. split; assumption.
Qed.

Lemma wclient_not_private : forall LB a, CH2.wclient L sp0 a -> ~ alloc_private L LB a.
Proof.
  intros LB a (Ha & HW) HP. pose proof STK as (S1 & S2 & S3 & S4 & S5). pose proof LYI as [LI1 LI2]. unfold hl_ceil in *.
  destruct HP as [(P1 & P2 & P3)|P].
  - destruct HW as [HW|(I1 & I2 & I3 & I4)]; [lia | apply P3; split; assumption].
  - destruct HW as [HW|(I1 & I2 & I3 & I4)]; [destruct (LYR a P) as [Q|Q]; lia | exact (I3 P)].
Qed.

Lemma pure_leaf_ok : forall pc scr ng wregs news a0x (Wz : list L5.range) i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  CH2.custom_chk NF d scr ng (nth i BLS []) wregs news a0x c ps cj (nth i BLS []) = Some ci ->
  CH2.blocks_eqb (nth j BLS []) (nth i BLS []) = true ->
  (forall w a, In w Wz -> L5.in_rng w a -> exists w', In w' W /\ L5.in_rng w' a) ->
  (forall E', env_agree NF E0 E' -> forall w a, In w Wz -> L5.in_rng w a -> exists r, In r wregs /\ CH2.in_reg E' r a) ->
  (forall (fx' : FPState) E E' R' (M M' : mem) model,
      env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> regs_ok E' (CA.ps_reglist ps) R' -> HAMB i E M' model -> XI i E M ->
      PML.entry L R' M' (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) scr -> CH2.ci_csp ci <= 0 ->
      PML.fp_ok fx' -> m_halted model = None -> m_vm_lazy model = [] ->
      (forall (fx2 : FPState) R2 (M2 : mem) (ghosts : list word), length ghosts = ng -> PML.fp_ok fx2 -> regs_preserved R' R2 ->
           L5.frame_but ((sp0 + CH2.ci_csp ci - scr, scr) :: Wz) M' M2 -> mem_grows M' M2 ->
           match a0x with Some e => getr R2 10%bv = edenot (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) e | None => True end ->
           (forall X, In X news -> kentry_ok (hl_segs L) (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) M2 X) ->
           (L5C.hpres L (CH2.den E' (nth i BLS []) ++ LBrest) (sp0 + CH2.ci_csp ci) scr Wz M' M2 -> XI j (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) M2) ->
           srealizes RSEGS SCFG (@PML.cfg fx2 R2 (CC.cp_pc cj) M2 model) K) ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' pc M' model) K) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros pc scr ng wregs news a0x Wz i c k ps j cj ci IL Hret Hcj Hpc Hchk B5 WZW WZR USER fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0. apply CH2.blocks_eqb_eq in B5.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              scr ng (nth i BLS []) wregs news a0x i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  set (nx := CH2.ci_nx ci) in *.
  pose proof HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  pose proof STK as (S1 & S2 & S3 & S4 & S5). pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO. pose proof LYI as [LI1 LI2].
  destruct Hmo as (Hm1 & Hm2 & Hm3).
  rewrite Hpc, LS.
  apply (USER fx' E E' R' M M' model HagE' Hag HLF ltac:(rewrite <- Hreq; exact HR) HA' HXI0); [| exact Hc1 | exact HFP | exact Hm1 | exact Hm2 |].
  { split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]. }
  intros fx2 R2 M2 ghosts Hlen HFP2 HRP HFB HGR Ha0 HNEWS HXI2.
  set (LBk := CH2.den E' (nth i BLS []) ++ LBrest).
  assert (HHk : hi_heap HI LBk cr M' (m_vmmaps model)) by (unfold LBk; rewrite Hden; exact HH).
  pose proof (proj1 (hio_wf L SCFG HI HIok _ _ _ _ HHk)) as Hwf.
  assert (OUTF : forall a, 0 <= a < 2 ^ 64 -> L5.outside Wz a -> ~ (sp0 + CH2.ci_csp ci - scr <= a < sp0 + CH2.ci_csp ci) -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha Hout Hns. apply HFB. rewrite L5.unsigned_lit by exact Ha. intros r [<-|Hr]; [unfold L5.in_rng; cbn [fst snd]; lia | exact (Hout r Hr)]. }
  assert (HPRES : L5C.hpres L LBk (sp0 + CH2.ci_csp ci) scr Wz M' M2).
  { apply L5C.hpres_intro.
    - intros a (K1 & K2 & K3 & K4). apply (OUTF a K1 K4). destruct K2 as [(b & Hb & Hin)|[[C1 C2]|[C1 C2]]]; [|exact C2 | unfold hl_ceil in *; lia].
      destruct (Hwf b Hb) as ((R0 & R1 & R2' & R3 & R4) & _). unfold hl_ceil in *. lia.
    - intros q Hq. apply HGR. destruct Hstk as (_ & _ & _ & _ & T5). apply T5. exact Hq.
    - intros a _ _ _ Hd. apply HGR. exact Hd. }
  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model ghosts LBk Wz Hlen HFP2 (CH2.regs_preserved_kept R' R2 HRP) Ha0 HPRES).
  - intros b Hb. exact Hb.
  - exact (WZR E' HagE').
  - intros X HX _. exact (HNEWS X HX).
  - fold nx. set (E2 := CH2.retEx E' nx ghosts R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (Z3 : CH2.blocks_vars_lt nx (nth i BLS []) = true).
    { unfold CH2.custom_chk in Hchk. destruct (CH2.common_chk_x _ _ _ _ _ _ _ _) as [ci0|] eqn:Hc0; [|discriminate].
      lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb2; [|discriminate] end. injection Hchk as ->.
      apply andb_prop in Hb2 as [Hb2 _]. apply andb_prop in Hb2 as [Hb2 _]. apply andb_prop in Hb2 as [_ Hb2]. exact Hb2. }
    assert (Hden2 : CH2.den E2 (nth j BLS []) = CH2.den E (nth i BLS [])).
    { rewrite B5, (CH2.den_agree nx E' E2 _ Hag2 Z3). exact Hden. }
    split; [|exact (HXI2 HPRES)].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 (PB.FLOOR L NF sp0 d STK NF32) scr ng c ps cj ci i j E E' R' M' model E2 M2 model LBk Wz cr CF HPRES).
    + intros b Hb. unfold LBk. apply in_or_app. right. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). destruct (WZW w a Hw Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
    + apply L5C.model_but_vm_refl.
    + unfold CH2.cur. rewrite Hden2, <- Hden. fold LBk.
      apply (hio_frame L SCFG HI HIok LBk cr M' M2 _ HHk); [|intros x Hx; apply HGR; exact Hx].
      intros a Ha Hpriv. apply (OUTF a Ha).
      * intros w Hw Hin. destruct (WZW w a Hw Hin) as (w' & Hw' & Hin'). exact (wclient_not_private LBk a (W_ok w' a Hw' Hin') Hpriv).
      * intros Hin. destruct Hpriv as [(P1 & _)|P]; [unfold hl_ceil in *; lia|]. destruct (LYR a P) as [Q|Q]; unfold hl_ceil in *; lia.
    + exact Hag2.
    + exact (CRED_BLK i j E E2 cr Hden2 HC).
Qed.

Variable VB : expr.
Variable VK : Z.
Hypothesis VB_frozen : APC.expr_vars_lt NF VB = true.
Variable vaddr : Z.
Hypothesis VADDR : estart E0 (SA VB VK) = vaddr.
Hypothesis VOBJ : sp0 <= vaddr /\ vaddr + 24 <= hl_sptop L /\ vaddr mod 8 = 0 /\ forall a, vaddr <= a < vaddr + 24 -> exists w, In w W /\ L5.in_rng w a.
Hypothesis VECPUSH : PMS.vec_push_spec L HI.
Definition VEC_SCR : Z := 8368.

Definition vecpush_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in let cells := SR.ps_cells ps in
  let nx := (CC.cp_nx cj - APC.NCS - 2)%nat in
  match split_lit (nth 10 regs (ELit 0)), split_lit (nth 11 regs (ELit 0)), split_lit (nth 2 regs (ELit 0)), BLi with
  | (ob, ok), (xb, xk), (_, csp), [b1; (sbe, sce)] =>
      match CAX.cell_at cells ob ok 8, CAX.cell_at cells ob (ok + 8) 8, CAX.cell_at cells xb xk 1 with
      | Some c0, Some c8, Some xv =>
          if (expr_eqb ob VB && Z.eqb ok VK && expr_eqb xb (EVar 2) && Z.leb csp xk && Z.ltb xk 0
              && expr_eqb c0 sbe && PB.has cells (KWord (SA ob (ok + 16)) 8 (PSU.eadd sbe sce))
              && PB.prove cells (KRange xv 0 255) && PB.prove cells (KRange sce 66 1056) && PB.prove cells (KRange sbe 4096 140737488355328)
              && CH2.blocks_eqb BLj [b1; (EVar nx, EVar (nx + 1))] && CH2.blocks_vars_lt nx [b1]
              && forallb (CH2.fresh_fact_ok d 0x10000 0xf8000 cells nx [b1] nx (EVar (nx + 1))) (PSU2.vblk_facts d nx [b1]))%bool
          then CH2.custom_chk NF d VEC_SCR 2 [b1] [(ob, ok, ELit 24)] (PSU2.vec_cells ob ok (APC.eaddz (PSU2.esub c8 c0) 1) nx ++ PSU2.vblk_facts d nx [b1]) None c ps cj BLi
          else None
      | _, _, _ => None
      end
  | _, _, _, _ => None
  end.

Lemma nodup_swap : forall (a b : Z) l, base.NoDup (a :: b :: l) -> base.NoDup (b :: a :: l).
Proof.
  intros a b l H. inversion H as [|x l0 N1 N2]; subst. inversion N2 as [|y l1 N3 N4]; subst.
  constructor; [|constructor; [|exact N4]].
  - intros X. apply list_elem_of_In in X. destruct X as [->|X]; [apply N1; apply list_elem_of_In; left; reflexivity | apply N3; apply list_elem_of_In; exact X].
  - intros X. apply N1. apply list_elem_of_In. right. apply list_elem_of_In in X. exact X.
Qed.

Lemma vecpush_leaf_ok : forall i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther PML.PC_VEC_PUSH) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = PML.PC_VEC_PUSH ->
  vecpush_chk c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E E' R' (M M' : mem) model cr b1 sbe sce c8 xv xk,
      env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> HAMB i E M' model -> XI i E M ->
      nth i BLS [] = [b1; (sbe, sce)] -> CAX.cell_at (SR.ps_cells ps) VB (VK + 8) 8 = Some c8 -> CAX.cell_at (SR.ps_cells ps) (EVar 2) xk 1 = Some xv ->
      hi_heap HI (CH2.cur LBrest BLS i E) cr M' (m_vmmaps model) -> Cred i E cr ->
      exists st : list Z,
        L5.bytes_at RSEGS M' (uv E' sbe) st /\ uv E' c8 = uv E' sbe + Z.of_nat (length st) /\ (length st <= 1026)%nat /\ Z.of_nat (length st) <= uv E' sce /\
        In (uv E' sce) [66; 132; 264; 528; 1056] /\
        (Z.of_nat (length st) = uv E' sce -> credit_ok L cr (2 * uv E' sce)) /\
        forall E2 (M2 : mem) LBk spc b' cap' cr2,
          env_agree (CC.cp_nx cj - APC.NCS - 2) E' E2 -> L5C.hpres L LBk spc VEC_SCR [(vaddr, 24)] M' M2 -> incl LBrest LBk ->
          L5.bytes_at RSEGS M2 b' (st ++ [uv E' xv]) ->
          CH2.den E2 (nth j BLS []) = [(uv E' (fst b1), uv E' (snd b1)); (b', cap')] ->
          ((b' = uv E' sbe /\ cap' = uv E' sce /\ cr2 = cr /\ Z.of_nat (length st) < uv E' sce) \/
           (cap' = 2 * uv E' sce /\ cr2 = debit L cr (2 * uv E' sce) /\ Z.of_nat (length st) = uv E' sce)) ->
          XI j E2 M2 /\ Cred j E2 cr2) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros i c k ps j cj ci IL Hret Hcj Hpc Hchk USER fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0.
  unfold vecpush_chk in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [ob ok] eqn:Hsplit.
  destruct (split_lit (nth 11 (CA.ps_reglist ps) (ELit 0))) as [xb xk] eqn:Hsplitx.
  destruct (split_lit (nth 2 (CA.ps_reglist ps) (ELit 0))) as [spb csp0] eqn:Hsplits.
  destruct (nth i BLS []) as [|b1 [|[sbe sce] [|? ?]]] eqn:HBLi; try discriminate.
  destruct (CAX.cell_at (SR.ps_cells ps) ob ok 8) as [c0|] eqn:Hcell0; [|discriminate].
  destruct (CAX.cell_at (SR.ps_cells ps) ob (ok + 8) 8) as [c8|] eqn:Hcell8; [|discriminate].
  destruct (CAX.cell_at (SR.ps_cells ps) xb xk 1) as [xv|] eqn:Hcellx; [|discriminate].
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  repeat (apply andb_prop in Hb as [Hb ?B]).
  apply expr_eqb_eq in Hb, B9, B6. apply Z.eqb_eq in B10. apply Z.leb_le in B8. apply Z.ltb_lt in B7. apply CH2.blocks_eqb_eq in B1. subst ob ok xb c0.
  set (nx := (CC.cp_nx cj - APC.NCS - 2)%nat) in *. set (cells := SR.ps_cells ps) in *.
  rewrite <- HBLi in Hchk.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              VEC_SCR 2%nat [b1] _ _ None i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (Hnx : CH2.ci_nx ci = nx) by (unfold nx; lia).
  pose proof HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  pose proof HK as HK0. rewrite LS in HK.
  assert (Ho : estart E' (SA VB VK) = vaddr) by (rewrite (PB.estart_agree NF E0 E' VB VK HagE' VB_frozen); exact VADDR).
  destruct VOBJ as (O1 & O2 & O3 & O4). pose proof STK as (S1 & S2 & S3 & S4 & S5). pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.
  destruct (USER E E' R' M M' model cr b1 sbe sce c8 xv xk HagE' Hag HLF HA' HXI0 eq_refl Hcell8 Hcellx HH HC)
    as (st & Hst & Hc8v & Hl1026 & Hlcap & Hcapin & Hcred & UPOST).
  set (b := uv E' sbe) in *. set (cap := uv E' sce) in *. set (x := uv E' xv) in *.
  pose proof (PB.prove_ok E' M' cells _ HK B4) as Hx255. cbn [kentry_ok] in Hx255. fold (uv E' xv) in Hx255. fold x in Hx255.
  pose proof (PB.prove_ok E' M' cells _ HK B3) as Hcapr. cbn [kentry_ok] in Hcapr. fold (uv E' sce) in Hcapr. fold cap in Hcapr.
  pose proof (PB.prove_ok E' M' cells _ HK B2) as Hbr. cbn [kentry_ok] in Hbr. fold (uv E' sbe) in Hbr. fold b in Hbr.

  assert (Ho8 : estart E' (SA VB (VK + 8)) = vaddr + 8) by (unfold estart in *; cbn [a_base a_off] in *; lia).
  assert (Ho16 : estart E' (SA VB (VK + 16)) = vaddr + 16) by (unfold estart in *; cbn [a_base a_off] in *; lia).
  pose proof (PB2.kword64_elim E' M' _ _ vaddr (PB2.cell_at_ok E' M' cells _ _ _ _ HK Hcell0) Ho) as C0. fold b in C0.
  pose proof (PB2.kword64_elim E' M' _ _ (vaddr + 8) (PB2.cell_at_ok E' M' cells _ _ _ _ HK Hcell8) Ho8) as C8. rewrite Hc8v in C8.
  pose proof (PB2.kword64_elim E' M' _ _ (vaddr + 16) (PB.has_ok E' M' cells _ HK B5) Ho16) as C16.
  assert (U16 : uv E' (PSU.eadd sbe sce) = b + cap) by (unfold PSU.eadd; rewrite PB.uv_eadd; fold b cap; apply Z.mod_small; lia). rewrite U16 in C16.
  assert (Hxa : estart E' (SA (EVar 2) xk) = sp0 + xk).
  { unfold estart. cbn [a_base a_off edenot]. destruct HagE' as [Hev _]. rewrite <- (Hev 2%nat) by lia. rewrite SP0. reflexivity. }
  pose proof (PB2.kword8_elim E' M' _ _ (sp0 + xk) (PB2.cell_at_ok E' M' cells _ _ _ _ HK Hcellx) Hxa) as CX. fold x in CX.

  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 vaddr).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplit). f_equal. exact Ho. }
  assert (Ga1 : getr R' 11%bv = Z_to_bv 64 (sp0 + xk)).
  { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplitx). f_equal. exact Hxa. }
  assert (Hcsp : CH2.ci_csp ci = csp0).
  { unfold CH2.custom_chk in Hchk. destruct (CH2.common_chk_x _ _ _ _ _ _ _ _) as [ci0|] eqn:Hc0; [|discriminate].
    lazymatch type of Hchk with (if ?bb then _ else _) = _ => destruct bb; [|discriminate] end. injection Hchk as ->.
    unfold CH2.common_chk_x in Hc0. destruct (nth 1 (CA.ps_reglist ps) (ELit 0)); try discriminate. rewrite Hsplits in Hc0.
    destruct spb as [|[|[|[|]]]| | | | | |]; try discriminate. lazymatch type of Hc0 with (if ?bb then _ else _) = _ => destruct bb; [|discriminate] end. injection Hc0 as <-. reflexivity. }

  unfold CH2.cur in HH. rewrite <- Hden, HBLi in HH. unfold CH2.den in HH. cbn [map fst snd] in HH. fold (uv E' (fst b1)) (uv E' (snd b1)) (uv E' sbe) (uv E' sce) in HH. fold b cap in HH.
  set (b1v := (uv E' (fst b1), uv E' (snd b1))) in *. cbn [app] in HH.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & Hcr0 & Hcr1).
  assert (Nb1 : fst b1v <> b).
  { cbn [map fst] in Hnd. inversion Hnd as [|y l N1 N2]; subst. intros X. apply N1. apply list_elem_of_In. left. symmetry. exact X. }
  assert (Hrm : lb_remove b (b1v :: (b, cap) :: LBrest) = b1v :: LBrest).
  { cbn [lb_remove fst]. destruct (Z.eqb_spec (fst b1v) b) as [X|_]; [contradiction|]. rewrite Z.eqb_refl. reflexivity. }

  rewrite Hpc. rewrite LS.
  apply (VECPUSH (b1v :: (b, cap) :: LBrest) cr vaddr b cap (sp0 + xk) x (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) st fx' R' M' model K HH Hmo K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]|].
    split; [exact Ga0|]. split; [exact Ga1|]. split; [exact CX|]. split; [rewrite Hcsp; lia|]. split; [exact C0|]. split; [exact C8|]. split; [exact C16|]. split; [exact Hst|].
    split; [right; left; reflexivity|]. split; [exact Hlcap|]. split; [exact Hl1026|]. split; [unfold PML.obj_on_stack; lia | exact Hcred]. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 [HWc Hpost] HRP HPRES Hbv2 HH2.
  rewrite Hrm in Hpost.
  assert (EXP : exists b' cap', PML.u64 M2 vaddr b' /\ PML.u64 M2 (vaddr + 8) (b' + Z.of_nat (length st) + 1) /\ PML.u64 M2 (vaddr + 16) (b' + cap') /\ L5.bytes_at RSEGS M2 b' (st ++ [x]) /\
            hi_heap HI (b1v :: (b', cap') :: LBrest) cr' M2 (m_vmmaps model2) /\ LBk = b1v :: LBrest /\ 66 <= cap' <= 1056 /\ Z.of_nat (length st) + 1 <= cap' /\
            ((b' = b /\ cap' = cap /\ cr' = cr /\ Z.of_nat (length st) < cap) \/ (cap' = 2 * cap /\ cr' = debit L cr (2 * cap) /\ Z.of_nat (length st) = cap))).
  { destruct Hpost as [(G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7) | (G0 & b' & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8)].
    - exists b, cap. rewrite G5 in HH2. subst LBk. repeat split; try assumption; try lia. left. repeat split; try assumption.
    - exists b', (2 * cap). subst LBk. rewrite G6 in HH2.
      assert (Hc528 : cap <= 528) by (cbn [In] in Hcapin; lia).
      repeat split; try assumption; try lia.
      + replace (b' + Z.of_nat (length st) + 1) with (b' + cap + 1) by lia. exact G2.
      + destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (_ & Hnd2 & _).
        apply (hio_perm L SCFG HI HIok _ (b1v :: (b', 2 * cap) :: LBrest) _ _ _ HH2).
        * intros y. cbn [In]. tauto.
        * cbn [map fst] in Hnd2 |- *. apply nodup_swap. exact Hnd2.
      + right. repeat split; try assumption. }
  destruct EXP as (b' & cap' & D0 & D8 & D16 & Dst & HH3 & -> & Hcap' & Hlc' & Hcase).
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH3) as (Hwf3 & Hnd3 & _).
  destruct (Hwf3 (b', cap') ltac:(right; left; reflexivity)) as (BR & BD & BA). cbn [fst snd] in BR, BD, BA. pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4).
  assert (Nb3 : fst b1v <> b').
  { cbn [map fst] in Hnd3. inversion Hnd3 as [|y l N1 N2]; subst. intros X. apply N1. apply list_elem_of_In. left. symmetry. exact X. }
  assert (BA' : blocks_apart b' cap' (CH2.den E' [b1] ++ LBrest)).
  { cbn [lb_remove fst] in BA. destruct (Z.eqb_spec (fst b1v) b') as [X|_]; [contradiction|]. rewrite Z.eqb_refl in BA. exact BA. }

  set (ghosts := [Z_to_bv 64 b'; Z_to_bv 64 cap']).
  set (E2 := CH2.retEx E' nx ghosts R2).
  assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
  assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
  unfold hl_ceil in *.
  assert (G0 : bv_unsigned (ev E2 nx) = b') by (pose proof (PB2.ghost_val E' nx ghosts R2 0 b' eq_refl ltac:(cbn; lia) ltac:(lia)) as G; rewrite Nat.add_0_r in G; exact G).
  assert (G1 : bv_unsigned (ev E2 (nx + 1)) = cap') by (apply (PB2.ghost_val E' nx ghosts R2 1 cap' eq_refl); [cbn; lia | lia]).
  assert (Hden2 : CH2.den E2 (nth j BLS []) = [b1v; (b', cap')]).
  { rewrite B1. unfold CH2.den. cbn [map fst snd edenot]. rewrite G0, G1.
    pose proof (CH2.den_agree nx E' E2 [b1] Hag2 B0) as Dg. unfold CH2.den in Dg. cbn [map] in Dg. injection Dg as Dg1 Dg2. rewrite Dg1, Dg2. reflexivity. }
  destruct (UPOST E2 M2 (b1v :: LBrest) (sp0 + CH2.ci_csp ci) b' cap' cr' Hag2 ltac:(subst Wc; exact HPRES) ltac:(intros y Hy; right; exact Hy) Dst Hden2 Hcase) as [HXI2 HC2].
  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model2 ghosts (b1v :: LBrest) Wc eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HPRES).
  - intros y Hy. exact Hy.
  - intros w a Hw Hin. subst Wc. destruct Hw as [<-|[]]. exists (VB, VK, ELit 24). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite u64_of_Z by lia. lia.
  -
    intros X HX _. rewrite Hnx. fold E2.
    assert (Hest : estart E2 (SA VB VK) = vaddr) by (rewrite (PB.estart_agree NF E0 E2 VB VK HagE2 VB_frozen); exact VADDR).
    assert (Vc8 : APC.expr_vars_lt nx c8 = true).
    { destruct (PB.cell_at_has _ _ _ _ _ Hcell8) as (bb & Hin & ->). pose proof (PB.kn_vars_in _ _ _ V2 Hin) as Vk. cbn [APC.kentry_vars_lt] in Vk. apply andb_prop in Vk as [_ Vk]. rewrite Hnx in Vk. exact Vk. }
    assert (Vsb : APC.expr_vars_lt nx sbe = true).
    { destruct (PB.cell_at_has _ _ _ _ _ Hcell0) as (bb & Hin & ->). pose proof (PB.kn_vars_in _ _ _ V2 Hin) as Vk. cbn [APC.kentry_vars_lt] in Vk. apply andb_prop in Vk as [_ Vk]. rewrite Hnx in Vk. exact Vk. }
    assert (Usl : uv E2 (APC.eaddz (PSU2.esub c8 sbe) 1) = Z.of_nat (length st) + 1).
    { rewrite PB.uv_eaddz. unfold PSU2.esub, PSU.esub. rewrite PB.uv_esub, (PB.uv_agree nx E' E2 c8 Hag2 Vc8), (PB.uv_agree nx E' E2 sbe Hag2 Vsb), Hc8v. fold b.
      replace (b + Z.of_nat (length st) - b) with (Z.of_nat (length st)) by lia. rewrite (Z.mod_small (Z.of_nat (length st))) by lia. apply Z.mod_small. lia. }
    apply in_app_or in HX as [HX|HX].
    + rewrite LS. unfold PSU2.vec_cells in HX. cbn [In] in HX. destruct HX as [<-|[<-|[<-|[<-|[<-|[]]]]]].
      * eapply CL5.kword64_intro with (A := vaddr) (z := b'); [exact Hest | lia | lia | cbn [edenot]; rewrite <- G0; symmetry; apply Z_to_bv_bv_unsigned | exact D0].
      * eapply CL5.kword64_intro with (A := vaddr + 8) (z := b' + Z.of_nat (length st) + 1); [unfold estart in *; cbn [a_base a_off] in *; lia | lia | lia | | exact D8].
        apply PB.edenot_of_uv. unfold PSU2.eadd, PSU.eadd. rewrite PB.uv_eadd, Usl. unfold uv at 1. cbn [edenot]. rewrite G0. rewrite Z.mod_small by lia. lia.
      * eapply CL5.kword64_intro with (A := vaddr + 16) (z := b' + cap'); [unfold estart in *; cbn [a_base a_off] in *; lia | lia | lia | | exact D16].
        apply PB.edenot_of_uv. unfold PSU2.eadd, PSU.eadd. rewrite PB.uv_eadd. unfold uv. cbn [edenot]. rewrite G0, G1. rewrite Z.mod_small by lia. lia.
      * cbn [kentry_ok edenot]. rewrite G1. lia.
      * assert (Ud : uv E2 (PSU2.esub (EVar (nx + 1)) (APC.eaddz (PSU2.esub c8 sbe) 1)) = cap' - (Z.of_nat (length st) + 1)).
        { unfold PSU2.esub at 1. unfold PSU.esub. rewrite PB.uv_esub, Usl. unfold uv. cbn [edenot]. rewrite G1. apply Z.mod_small. lia. }
        cbn [kentry_ok]. fold (uv E2 (PSU2.esub (EVar (nx + 1)) (APC.eaddz (PSU2.esub c8 sbe) 1))). rewrite Ud. lia.
    + rewrite forallb_forall in B. specialize (B X HX).
      exact (CH2.ghost_block_fact L LYI LYE NF E0 LBrest sp0 d W STK SCR_pos NF32 SP0 W_ok CRS_ok WRS_ok 0x10000 0xf8000 (PmLayout.ly_img_lo L LAY) (PmLayout.ly_img_hi L LAY)
               E' E2 nx M' M2 [b1] cells nx (EVar (nx + 1)) b' cap' X HagE' HK0 Hag2 G0 ltac:(unfold elenZ; cbn [edenot]; exact G1) BR BA' BD B).
  -
    rewrite Hnx. fold E2. split; [|exact HXI2].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 (PB.FLOOR L NF sp0 d STK NF32) VEC_SCR 2%nat c ps cj ci i j E E' R' M' model E2 M2 model2 (b1v :: LBrest) Wc cr' CF HPRES).
    + intros y Hy. right. exact Hy.
    + intros w a Hw Hin (_ & _ & _ & Hout). subst Wc. destruct Hw as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      destruct (O4 a Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
    + exact Hbv2.
    + unfold CH2.cur. rewrite Hden2. exact HH3.
    + rewrite Hnx. exact Hag2.
    + exact HC2.
Qed.

Variable OB : expr.
Variable OK : Z.
Hypothesis OB_frozen : APC.expr_vars_lt NF OB = true.
Variable oaddr : Z.
Hypothesis OADDR : estart E0 (SA OB OK) = oaddr.
Hypothesis OBJ : sp0 <= oaddr /\ oaddr + 24 <= hl_sptop L /\ oaddr mod 8 = 0 /\ forall a, oaddr <= a < oaddr + 24 -> exists w, In w W /\ L5.in_rng w a.
Variables KXf BXf : list (Z * Z) -> Z.
Hypothesis CRED_EQ : forall i E cr, Cred i E cr <-> PPS.bufcred L cr (PB.cap_of BLS i E) (KXf (PB.tl_of BLS i E)) (BXf (PB.tl_of BLS i E)).
Hypothesis PUSHB : PMS.str_push_back_spec L HI.

Definition pushbc_chk (KMIN : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in let cells := SR.ps_cells ps in
  let nx := (CC.cp_nx cj - APC.NCS - 2)%nat in
  match split_lit (nth 10 regs (ELit 0)), BLi with
  | (ob, ok), (pe, ce) :: BLk =>
      match CAX.cell_at cells ob (ok + 8) 8 with
      | Some se =>
          if (expr_eqb ob OB && Z.eqb ok OK && Z.leb 12 KMIN && str_patx cells ob ok pe ce se (2 * KMIN) (2 ^ 26 - 2)
              && APC.fact_ok cells (KRange (nth 11 regs (ELit 0)) 0 255)
              && CH2.blocks_eqb BLj ((EVar nx, PSU.emul2 (EVar (nx + 1))) :: BLk) && CH2.blocks_vars_lt nx BLk
              && forallb (CH2.fresh_fact_ok d 0x10000 0xf8000 cells nx BLk nx (PSU.emul2 (EVar (nx + 1)))) (PSU.blk_facts d nx BLk))%bool
          then CH2.custom_chk NF d PB.STR_SCR 2 BLk [(ob, ok, ELit 24)] (PSU.str_news d ob ok (APC.eaddz se 1) nx KMIN BLk) None c ps cj BLi
          else None
      | None => None
      end
  | _, _ => None
  end.

Lemma pushbc_leaf_ok : forall KMIN i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther PML.PC_STR_PUSH_BACK) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj ->
  SR.ps_pc ps = PML.PC_STR_PUSH_BACK ->
  pushbc_chk KMIN c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E E' R' (M M' : mem) pe ce BLk se, env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> XI i E M ->
     nth i BLS [] = (pe, ce) :: BLk -> CAX.cell_at (SR.ps_cells ps) OB (OK + 8) 8 = Some se ->
     exists s : list Z,
       L5.bytes_at RSEGS M' (uv E' pe) s /\ Z.of_nat (length s) = uv E' se /\
       (forall E2 (M2 : mem) LBk spc cap' p', env_agree (CC.cp_nx cj - APC.NCS - 2) E' E2 -> L5C.hpres L LBk spc PB.STR_SCR [(oaddr, 24)] M' M2 -> incl LBrest LBk ->
          PML.str_at M2 oaddr (PML.SLong cap' p' (s ++ [uv E' (nth 11 (CA.ps_reglist ps) (ELit 0))])) ->
          CH2.den E2 (nth j BLS []) = (p', cap') :: CH2.den E' BLk ->
          XI j E2 M2)) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros KMIN i c k ps j cj ci IL Hret Hcj Hpc Hchk USER fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0.
  unfold pushbc_chk in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [ob ok] eqn:Hsplit.
  destruct (nth i BLS []) as [|[pe ce] BLk] eqn:HBLi; [discriminate|].
  destruct (CAX.cell_at (SR.ps_cells ps) ob (ok + 8) 8) as [se|] eqn:Hcell; [|discriminate].
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B7]. apply andb_prop in Hb as [Hb B6b]. apply andb_prop in Hb as [Hb B6]. apply andb_prop in Hb as [Hb B5]. apply andb_prop in Hb as [Hb B4].
  apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B1. apply Z.eqb_eq in B2. apply Z.leb_le in B3. subst ob ok.
  apply CH2.blocks_eqb_eq in B6.
  set (nx := (CC.cp_nx cj - APC.NCS - 2)%nat) in *. set (cells := SR.ps_cells ps) in *.
  rewrite <- HBLi in Hchk.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              PB.STR_SCR 2%nat BLk _ _ None i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (Hnx : CH2.ci_nx ci = nx) by (unfold nx; lia).
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  pose proof HK as HK0. rewrite LS in HK.

  assert (Ho : estart E' (SA OB OK) = oaddr) by (rewrite (PB.estart_agree NF E0 E' OB OK HagE' OB_frozen); exact OADDR).
  destruct OBJ as (O1 & O2 & O3 & O4). pose proof STK as (S1 & S2 & S3 & S4 & S5).
  assert (Hpd0 : L5.defined M' (uv E' pe) (uv E' ce)).
  { unfold CH2.cur in HH. rewrite <- Hden, HBLi, PB.den_cons in HH. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf0 & _). exact (proj1 (proj2 (Hwf0 _ (or_introl eq_refl)))). }
  destruct (str_viewx E' M' cells OB OK pe ce se (2 * KMIN) (2 ^ 26 - 2) HK B4 ltac:(lia) ltac:(rewrite Ho; lia) ltac:(rewrite Ho; lia) Hpd0) as (sv & Hstrv & Hlenv & Hcap & Hlt & Hsm & Hc8 & Hpr & Hpdef).
  rewrite Ho in Hstrv.
  destruct (USER E E' R' M M' pe ce BLk se HagE' Hag HLF HXI0 eq_refl Hcell) as (s & Hbs & Hlen & UCONT).
  assert (Hstr : PML.str_at M' oaddr (PML.SLong (uv E' ce) (uv E' pe) s)) by (apply (PB3.str_retext M' oaddr _ _ sv s Hstrv Hbs); apply Nat2Z.inj; rewrite Hlen, Hlenv; reflexivity). set (p := uv E' pe) in *. set (cap := uv E' ce) in *. set (size := uv E' se) in *.

  unfold CH2.cur in HH. rewrite <- Hden, HBLi, PB.den_cons in HH. fold p cap in HH. set (rest := CH2.den E' BLk ++ LBrest) in *.
  change ((p, cap) :: CH2.den E' BLk ++ LBrest) with ((p, cap) :: rest) in HH.

  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 oaddr).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplit). f_equal. exact Ho. }
  pose proof (PB.fact_ok' E' M' cells _ HK B5) as Hc255. cbn [kentry_ok] in Hc255. set (cv := bv_unsigned (edenot E' (nth 11 (CA.ps_reglist ps) (ELit 0)))) in *.
  assert (Ga1 : getr R' 11%bv = Z_to_bv 64 cv).
  { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq.
    unfold cv. symmetry. apply Z_to_bv_bv_unsigned. }

  set (kx := KXf (CH2.den E' BLk)). set (bx := BXf (CH2.den E' BLk)).
  assert (HBC : PPS.bufcred L cr cap kx bx).
  { apply CRED_EQ in HC. unfold PB.cap_of, PB.tl_of in HC. rewrite <- Hden, HBLi, PB.den_cons in HC. exact HC. }
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (_ & _ & Hcr0 & Hcr1).

  rewrite Hpc. rewrite LS.
  apply (PUSHB ((p, cap) :: rest) cr oaddr cap p cv (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) s fx' R' M' model K HH Hmo K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]|].
    split; [exact Ga0|]. split; [exact Ga1|]. split; [lia|]. split; [exact Hstr|]. split; [lia|]. split; [left; reflexivity|].
    split; [unfold PML.obj_on_stack; lia|]. split; [lia|].
    intros Hg. apply (PPS.bufcred_grow L cr cap _ kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) HBC); lia. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 [Hgrown HWc] HRP HPRES Hbv2 HH2.
  assert (Hs1 : Z.of_nat (length (s ++ [cv])) = size + 1) by (rewrite length_app, Nat2Z.inj_add; cbn [length]; lia).
  assert (EXP : exists p' cap', PML.str_at M2 oaddr (PML.SLong cap' p' (s ++ [cv])) /\ LB' = (p', cap') :: rest /\ LBk = rest /\ 2 * KMIN <= cap' <= 2 ^ 27 /\ PPS.bufcred L cr' cap' kx bx).
  { assert (Hrm : lb_remove p ((p, cap) :: rest) = rest) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
    destruct Hgrown as [(G1 & G2 & G3 & G4) | (p' & Hex)].
    - exists p, cap. rewrite G2, G3, G4, Hrm. split; [exact G1|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia | exact HBC].
    - cbv zeta in Hex. destruct Hex as (G0 & G1 & G2 & G3 & G4 & G5). rewrite Hs1 in *.
      destruct (PPS.grow_cap_facts cap (size + 1) ltac:(lia) Hc8 ltac:(lia) ltac:(lia)) as (F1 & F2 & F3 & F4).
      exists p', (PML.grow_cap cap (size + 1)). rewrite G3, G5, Hrm, G4. split; [exact G1|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
      apply (PPS.bufcred_grow L cr cap _ kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) HBC); lia. }
  destruct EXP as (p' & cap' & Hstr2 & -> & -> & Hcap' & HBC').
  destruct (CH2.first_block_facts L HI HIok p' cap' rest cr' M2 _ HH2) as (BR & BD & BA). pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4).
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.

  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model2 [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] rest Wc eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HPRES).
  - intros b Hb. exact Hb.
  - intros w a Hw Hin. subst Wc. destruct Hw as [<-|[]]. exists (OB, OK, ELit 24). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite u64_of_Z by lia. lia.
  -
    intros X HX _. rewrite Hnx. set (E2 := CH2.retEx E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
    assert (G0 : bv_unsigned (ev E2 nx) = p').
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. lia. }
    assert (Hchh : 0 <= cap' / 2 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (G1 : bv_unsigned (ev E2 (nx + 1)) = cap' / 2).
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 1 ltac:(cbn; lia)) as G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. exact Hchh. }
    destruct Hstr2 as (Hl2 & Hc8' & Hlt2).
    assert (Hcd : cap' = 2 * (cap' / 2)).
    { pose proof (Z.div_mod cap' 8 ltac:(lia)) as D. rewrite Hc8' in D. rewrite D at 2. replace (8 * (cap' / 8) + 0) with ((4 * (cap' / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
    assert (Ucap : uv E2 (PSU.emul2 (EVar (nx + 1))) = cap').
    { unfold PSU.emul2. rewrite PB.uv_escale. unfold uv. cbn [edenot]. rewrite G1, <- Hcd. apply Z.mod_small. lia. }
    unfold PSU.str_news in HX. apply in_app_or in HX as [HX|HX]; [|apply in_app_or in HX as [HX|HX]].
    + rewrite LS.
      assert (Hest : estart E2 (SA OB OK) = oaddr) by (rewrite (PB.estart_agree NF E0 E2 OB OK HagE2 OB_frozen); exact OADDR).
      assert (Hsz : uv E2 (APC.eaddz se 1) = Z.of_nat (length (s ++ [cv]))).
      { destruct (PB.cell_at_has _ _ _ _ _ Hcell) as (b' & Hin & ->).
        pose proof (PB.kn_vars_in _ _ _ V2 Hin) as Vk. cbn [APC.kentry_vars_lt] in Vk. apply andb_prop in Vk as [_ Vse]. rewrite Hnx in Vse.
        rewrite PB.uv_eaddz, (PB.uv_agree nx E' E2 se Hag2 Vse). fold size. rewrite Hs1. apply Z.mod_small. lia. }
      assert (Hpr' : 4096 <= p' <= 2 ^ 47) by (unfold hl_ceil in *; lia).
      exact (PB.str_cells_ok E2 M2 OB OK (APC.eaddz se 1) nx KMIN oaddr cap' p' (s ++ [cv]) Hest ltac:(lia) ltac:(lia) G0 G1 Hsz (conj Hl2 (conj Hc8' Hlt2)) Hcap' Hpr' X HX).
    + rewrite forallb_forall in B7. specialize (B7 X HX).
      exact (CH2.ghost_block_fact L LYI LYE NF E0 LBrest sp0 d W STK SCR_pos NF32 SP0 W_ok CRS_ok WRS_ok 0x10000 0xf8000 (PmLayout.ly_img_lo L LAY) (PmLayout.ly_img_hi L LAY)
               E' E2 nx M' M2 BLk cells nx (PSU.emul2 (EVar (nx + 1))) p' cap' X HagE' HK0 Hag2 G0 Ucap BR BA BD B7).
    + rewrite LS.
      assert (Hsz : uv E2 (APC.eaddz se 1) = size + 1).
      { destruct (PB.cell_at_has _ _ _ _ _ Hcell) as (b' & Hin & ->).
        pose proof (PB.kn_vars_in _ _ _ V2 Hin) as Vk. cbn [APC.kentry_vars_lt] in Vk. apply andb_prop in Vk as [_ Vse]. rewrite Hnx in Vse.
        rewrite PB.uv_eaddz, (PB.uv_agree nx E' E2 se Hag2 Vse). fold size. apply Z.mod_small. lia. }
      apply (PB.nul_facts_ok E2 M2 d (APC.eaddz se 1) nx BLk p' cap' (size + 1) G0 Ucap Hsz ltac:(rewrite <- Hs1; lia) ltac:(unfold hl_ceil in *; lia)); [|exact HX].
      intros Y HY. rewrite forallb_forall in B7. specialize (B7 Y HY). rewrite <- LS.
      exact (CH2.ghost_block_fact L LYI LYE NF E0 LBrest sp0 d W STK SCR_pos NF32 SP0 W_ok CRS_ok WRS_ok 0x10000 0xf8000 (PmLayout.ly_img_lo L LAY) (PmLayout.ly_img_hi L LAY)
               E' E2 nx M' M2 BLk cells nx (PSU.emul2 (EVar (nx + 1))) p' cap' Y HagE' HK0 Hag2 G0 Ucap BR BA BD B7).
  -
    rewrite Hnx. set (E2 := CH2.retEx E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (G0 : bv_unsigned (ev E2 nx) = p').
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. lia. }
    assert (Hchh : 0 <= cap' / 2 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (G1 : bv_unsigned (ev E2 (nx + 1)) = cap' / 2).
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 1 ltac:(cbn; lia)) as G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. exact Hchh. }
    pose proof Hstr2 as Hstr2'. destruct Hstr2 as (Hl2 & Hc8' & Hlt2).
    assert (Hcd : cap' = 2 * (cap' / 2)).
    { pose proof (Z.div_mod cap' 8 ltac:(lia)) as D. rewrite Hc8' in D. rewrite D at 2. replace (8 * (cap' / 8) + 0) with ((4 * (cap' / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
    assert (Ucap : uv E2 (PSU.emul2 (EVar (nx + 1))) = cap').
    { unfold PSU.emul2. rewrite PB.uv_escale. unfold uv. cbn [edenot]. rewrite G1, <- Hcd. apply Z.mod_small. lia. }
    assert (Hdenj : CH2.den E2 (nth j BLS []) = (p', cap') :: CH2.den E' BLk).
    { rewrite B6, PB.den_cons, Ucap. unfold uv at 1. cbn [edenot]. rewrite G0. rewrite (CH2.den_agree nx E' E2 BLk Hag2 B6b). reflexivity. }
    assert (Hcur : CH2.cur LBrest BLS j E2 = (p', cap') :: rest).
    { unfold CH2.cur. rewrite B6, PB.den_cons, Ucap. unfold uv at 1. cbn [edenot]. rewrite G0. unfold rest. rewrite (CH2.den_agree nx E' E2 BLk Hag2 B6b). reflexivity. }
    split; [|apply (UCONT E2 M2 rest (sp0 + CH2.ci_csp ci) cap' p' Hag2); [subst Wc; exact HPRES | intros b0 Hb0; unfold rest; apply in_or_app; right; exact Hb0 | exact Hstr2' | exact Hdenj]].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 (PB.FLOOR L NF sp0 d STK NF32) PB.STR_SCR 2%nat c ps cj ci i j E E' R' M' model E2 M2 model2 rest Wc cr' CF HPRES).
    + intros b Hb. unfold rest. apply in_or_app. right. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). subst Wc. destruct Hw as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      destruct (O4 a Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
    + exact Hbv2.
    + rewrite Hcur. exact HH2.
    + rewrite Hnx. exact Hag2.
    + apply CRED_EQ. unfold PB.cap_of, PB.tl_of. rewrite B6, PB.den_cons. cbn [hd snd tl]. rewrite Ucap. rewrite (CH2.den_agree nx E' E2 BLk Hag2 B6b). exact HBC'.
Qed.
End Inst4.
End PB4.
