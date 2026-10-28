(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncBridges_u5 EncAppendK_u5 EncBridgesU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_write_bignum_xsrc_T_u5 Cut_write_bignum_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EWBU.
Import PMES.
Module G := Cut_write_bignum_xsrc_u5.
Module GT := Cut_write_bignum_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.
Definition RETPC : Z := Eval vm_compute in hd 0 GT.ENDS.
Definition S2E : expr := EVar 32.
Definition F0 : list SGP.region := [(EVar 2, -8672, ELit 8672); (EVar 10, 296, ELit 8)].

Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition sink_j (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> CA.blocks -> option CH2.cinfo) (i k j : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (match CH2.ret_of G.RETS i k with Some j' => Nat.eqb j' j | None => false end &&
   match nth_error G.CPS j with Some cj => isSome (f c ps cj (nth i G.BLS []) (nth j G.BLS [])) | None => false end)%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  (SP.F_sub (CC.cp_F c) F0 && Nat.leb GT.NF (CC.cp_nx c)) &&
  match t with
  | CC.TGoto j s => false
  | CC.TOther pc =>
      if Z.eqb pc PML.PC_STR_APPEND then
        (Nat.eqb i 0 && Z.eqb (SR.ps_pc ps) PML.PC_STR_APPEND && sink_j (EBU.sink_chk GT.NF G.HDECL S2E 0) i k 1 c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (EVar 33) && expr_eqb (nth 12 regs (ELit 0)) (EVar 34))%bool
      else (Nat.eqb i 1 && PB.exit_base_chk GT.NF RETPC c ps)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.

Section WriteBignumOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis APPEND_OK : str_append_x_specU L HI.

(* [comment removed for export] *)
Section Stretch.
Variables (E0 : env) (sp V S2 : Z).
Hypothesis U2 : bv_unsigned (ev E0 2) = sp.
Hypothesis U10 : bv_unsigned (ev E0 10) = V.
Hypothesis SPR : hl_ceil L + 8672 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis OBJS : objs_enc L sp V S2.

Lemma out_F0 : forall (F : list SGP.region) E' a, SP.F_sub F F0 = true -> env_agree GT.NF E0 E' -> 0 <= a < 2 ^ 64 ->
  ~ (sp - 8672 <= a < sp) -> ~ (V + 296 <= a < V + 304) -> SGP.outside E' F (Z_to_bv 64 a).
Proof.
  intros F E' a HF Hag Ha N1 N2. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0. rewrite L5.unsigned_lit by lia.
  destruct OBJS as ((A1 & A2 & A3) & _). unfold ENC_SIZE in *. destruct SPR as (P1 & P2 & P3).
  unfold F0 in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|[X|[]]]; injection X as <- <- <-.
  - rewrite (PB.estart_agree GT.NF E0 E' (EVar 2) (-8672) Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U2. rewrite (u64_of_Z 8672) by lia. lia.
  - rewrite (PB.estart_agree GT.NF E0 E' (EVar 10) 296 Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U10. rewrite (u64_of_Z 8) by lia. lia.
Qed.

Lemma inv_stretch : forall (F : list SGP.region) E' (M M' : mem) g, SP.F_sub F F0 = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) -> mem_grows M M' ->
  (forall b, In b (g_lbv g) -> block_range L (fst b) (snd b)) ->
  enc_inv M V S2 g -> enc_inv M' V S2 g.
Proof.
  intros F E' M M' g HF Hag HFR HG HB HI0.
  destruct OBJS as ((A1 & A2 & A3) & (B1 & B2 & B3) & C). unfold ENC_SIZE, PML.apart in *. destruct SPR as (P1 & P2 & P3).
  assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 8672 \/ sp <= a) -> (a + n <= V + 296 \/ V + 304 <= a) -> L5C.agree_on M M' a n).
  { intros a n H0 H1 H2 H3 i Hi. apply HFR. apply (out_F0 F E' i HF Hag); lia. }
  apply (EK.enc_inv_agree M M' V S2 g); try (unfold ENC_SIZE; lia).
  - apply AG; unfold O_COLUMN; lia.
  - apply AG; unfold O_COLON, ENC_SIZE; lia.
  - destruct HI0 as (I1 & _). destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _).
    intros i Hi. apply HG. apply X. exact Hi.
  - apply AG; lia.
  - intros b Hb. destruct (HB b Hb) as (R0 & R1 & R2 & R3 & R4). split; [lia|]. split; [lia|]. apply AG; lia.
  - exact HI0.
Qed.

(* [comment removed for export] *)
Lemma blk_stretch : forall (F : list SGP.region) E' (M M' : mem) bb bm a n, SP.F_sub F F0 = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) -> block_range L bb bm -> bb <= a -> a + n <= bb + bm -> L5C.agree_on M M' a n.
Proof.
  intros F E' M M' bb bm a n HF Hag HFR (R0 & R1 & R2 & R3 & R4) Ha Hn i Hi.
  destruct OBJS as ((A1 & A2 & A3) & _). unfold ENC_SIZE in *. destruct SPR as (P1 & P2 & P3).
  apply HFR. apply (out_F0 F E' i HF Hag); lia.
Qed.
End Stretch.

(* [comment removed for export] *)
Lemma other_block : forall (LBo GB : list (Z * Z)) cr (M : mem) VM rep (b : Z * Z),
  hi_heap HI (LBo ++ GB) cr M VM -> In b LBo -> incl (PML.srep_blocks rep) GB ->
  ~ In b (PML.srep_blocks rep) /\ block_range L (fst b) (snd b) /\
  match rep with PML.SShort _ => True | PML.SLong cap p _ => block_range L p cap /\ (fst b + snd b <= p \/ p + cap <= fst b) end.
Proof.
  intros LBo GB cr M VM rep b HH Hb Hinc. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  assert (HbL : In b (LBo ++ GB)) by (apply in_or_app; left; exact Hb).
  destruct (Hwf b HbL) as (BR & _ & BA).
  destruct rep as [s|cap p s]; cbn [PML.srep_blocks] in *; [split; [intros []|split; [exact BR | exact I]]|].
  assert (HpG : In (p, cap) GB) by (apply Hinc; left; reflexivity).
  assert (Hne : fst b <> p).
  { intros E. rewrite map_app in Hnd. apply (EK.nodup_app_l' _ _ p Hnd); [apply (in_map fst _ _ HpG) | rewrite <- E; apply (in_map fst _ _ Hb)]. }
  split; [intros [X|[]]; apply Hne; rewrite <- X; reflexivity|]. split; [exact BR|].
  assert (HpL : In (p, cap) (LBo ++ GB)) by (apply in_or_app; right; exact HpG).
  split; [exact (proj1 (Hwf _ HpL))|].
  specialize (BA (p, cap) (L5C.in_lb_remove_neq (fst b) p cap _ HpL ltac:(intros X; apply Hne; symmetry; exact X))). cbn [fst snd] in BA. lia.
Qed.

Theorem write_bignum_ok : write_bignum_specU L HI.
Proof.
  intros sv bs LBo cr sp r V S2 kx bx g. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & (Ha1 & Hsv) & Hinv & _ & Hroom & Himg & Hcred & Hobjs) Hcont.
  apply sv_arg_of_U in Hsv.
  destruct Hsv as (q0 & Hq0 & Hq8 & Hbq & Hdq & Hinb & Hap1 & Hap2 & (SV1 & SV2 & SV3)).
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2' & S3 & S4 & S5).
  unfold STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  pose proof Hobjs as ((OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & OAP). unfold ENC_SIZE, PML.apart in OV2, OAP, Hap1, Hap2.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  pose proof Hinv as (I1 & I2 & I3 & I4 & I5).
  set (n := len bs) in *. assert (N0 : 0 <= n) by (unfold n, len; lia).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by (unfold hl_ceil; lia).
  assert (GLB : incl (PML.srep_blocks (g_rep g)) (g_lbv g)) by (intros b Hb; unfold g_lbv; apply in_or_app; left; exact Hb).
  (* [comment removed for export] *)
  assert (SRCQ : exists q, 0 <= q < 2 ^ 64 /\ PML.u64 M sv q /\ L5.bytes_at RSEGS M q bs /\ L5.defined M q n /\
                           (n = 0 \/ exists b, In b LBo /\ fst b <= q /\ q + n <= fst b + snd b /\ 4096 <= q /\ q + n <= hl_ceil L)).
  { destruct Hinb as [Z0|(b & Hb & B1 & B2)].
    - exists (bv_unsigned (Z_to_bv 64 q0)). pose proof (u64_range (Z_to_bv 64 q0)) as Y. unfold two64 in Y. split; [exact Y|].
      split; [unfold PML.u64, L5.u64_at in *; rewrite Z_to_bv_bv_unsigned; exact Hq0|].
      assert (BN : bs = []) by (apply length_zero_iff_nil; unfold n, len in Z0; lia).
      split; [intros i Hi; rewrite BN in Hi; cbn in Hi; lia|]. split; [intros i Hi; lia | left; exact Z0].
    - destruct (other_block LBo (g_lbv g) cr M _ (g_rep g) b HH Hb GLB) as (_ & (R0 & R1 & R2 & R3 & R4) & _).
      exists q0. split; [lia|]. split; [exact Hq0|]. split; [exact Hbq|]. split; [exact Hdq|]. right. exists b. repeat split; try assumption; lia. }
  clear Hq0 Hbq Hdq Hinb. destruct SRCQ as (q & Q64 & Hq0 & Hbq & Hdq & SRCB).
  assert (N46 : n < 2 ^ 47 - 4096).
  { destruct SRCB as [Z0|(b & _ & _ & _ & B3 & B4)]; [lia | unfold hl_ceil in B4; lia]. }
  (* [comment removed for export] *)
  assert (DCOL : L5.defined M (V + 296) 8).
  { destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  destruct (EAK.u64_of_defined M (V + 296) DCOL) as (col & Hcol0 & Hcol).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [S2; q; n; col] 0))) (fun _ => [])).
  assert (EV : forall x : reg, ev E0 (ridx x) = getr R x) by (intros x; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 V) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 sv) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 S2) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 q) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 n) by reflexivity.
  assert (V35 : ev E0 35 = Z_to_bv 64 col) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = V) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = sv) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = S2) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = q) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = n) by (rewrite V34; apply u64_of_Z; lia).
  assert (U35 : bv_unsigned (ev E0 35) = col) by (rewrite V35; apply u64_of_Z; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 8672) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (rewrite SCRV; unfold hl_ceil; repeat split; lia).
  assert (SPR : hl_ceil L + 8672 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47) by (unfold hl_ceil; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  set (W := W_h V S2).
  assert (W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng, O_COLUMN in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a)).
  { intros rg [<-|[<-|[<-|[]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha;
      rewrite ?U10, ?U11 in Ha; rewrite u64_of_Z in Ha by lia; (split; [lia | left; lia]). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (V + O_COLUMN, 8). split; [left; reflexivity | unfold L5.in_rng, O_COLUMN; cbn [fst snd]; lia].
    - rewrite U32 in Ha. rewrite u64_of_Z in Ha by lia. exists (S2, 24). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a).
  { intros rg a []. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)).
  { rewrite SCRV. intros j Hj. replace (sp - 8672 + j) with (sp - (176 + (256 + (16 + 8224))) + j) by lia. apply S5. lia. }
  assert (W_S2 : In (S2, 24) W) by (right; left; reflexivity).
  assert (OADDR : estart E0 (SA S2E 0) = S2) by (unfold estart, S2E; cbn [a_base a_off edenot]; rewrite U32; lia).
  set (GR := stack_blocks (g_sb g) (g_scap g)).
  set (off := fun (i : nat) => match i with 1%nat => n | _ => 0 end).
  set (XIv := fun (g1 : eghost) (i : nat) (E : env) (M1 : mem) =>
                enc_inv M1 V S2 g1 /\ g_es g1 = g_es g /\ g_sb g1 = g_sb g /\ g_scap g1 = g_scap g /\ g_len g1 = g_len g + off i /\
                (i = 0%nat -> L5.bytes_at RSEGS M1 q bs /\ L5.defined M1 q n)).
  set (CredV := EBU.CredV L kx bx).
  set (gB := EBU.gB GR).
  assert (GBL : forall g1, g_sb g1 = g_sb g -> g_scap g1 = g_scap g -> gB g1 = g_lbv g1).
  { intros g1 E1 E2. unfold gB, EBU.gB, g_lbv, GR. rewrite E1, E2. reflexivity. }
  assert (AGE : forall i c E E', nth_error G.CPS i = Some c -> env_agree GT.NF E0 E -> env_agree (CC.cp_nx c) E E' -> env_agree GT.NF E0 E').
  { intros i c E E' Hc H1 H2. eapply CC.env_agree_trans; [exact H1 | eapply CC.env_agree_le; [exact H2 | exact (G.NF_le i c Hc)]]. }
  assert (NILB : forall i E, CH2.den E (nth i G.BLS []) = []).
  { intros i E. destruct i as [|[|i]]; try reflexivity. destruct i; reflexivity. }
  assert (BRG : forall g1 M0c i E (M1 : mem) m1, CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS eghost gB CredV g1 M0c i E M1 m1 ->
                  (forall b, In b (gB g1) -> block_range L (fst b) (snd b)) /\ env_agree GT.NF E0 E /\ exists cr1, hi_heap HI (LBo ++ gB g1) cr1 M1 (m_vmmaps m1)).
  { intros g1 M0c i E M1 m1 (_ & _ & HagE & (cr1 & HH1 & _) & _). unfold CH2.cur, CH2V.LBr in HH1. rewrite NILB in HH1. cbn [app] in HH1.
    split; [|split; [exact HagE | exists cr1; exact HH1]]. intros b Hb.
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _). apply (Hwf b). apply in_or_app. right. exact Hb. }
  assert (STRETCH : forall g1 M0c i c k ps t E R1 (M1 : mem) m1 E' R' (M' : mem), CH2.is_leaf G.CPS G.TAGS i c k ps t -> CC.At (hl_segs L) c E R1 M1 ->
                      CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS eghost gB CredV g1 M0c i E M1 m1 -> XIv g1 i E M1 ->
                      env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M1 M' ->
                      enc_inv M' V S2 g1 /\ env_agree GT.NF E0 E' /\ (i = 0%nat -> L5.bytes_at RSEGS M' q bs /\ L5.defined M' q n)).
  { intros g1 M0c i c k ps t E R1 M1 m1 E' R' M' IL HAt HA HX Hag HLF.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [XF _]. apply andb_prop in XF as [XF _].
    destruct IL as (tags & Hc & _). destruct (BRG _ _ _ _ _ _ HA) as (HB & HagE & cr1 & HH1). pose proof (AGE i c E E' Hc HagE Hag) as HagE'.
    destruct HX as (HX1 & X2 & X3 & X4 & X5 & X6).
    split; [|split; [exact HagE'|]].
    - apply (inv_stretch E0 sp V S2 U2 U10 SPR Hobjs (CC.cp_F c) E' M1 M' g1 XF HagE' (CC.lf_frame _ _ _ _ _ _ _ HLF) (CC.lf_grows _ _ _ _ _ _ _ HLF)); [|exact HX1].
      rewrite <- (GBL g1 X3 X4). exact HB.
    - intros Hi0. destruct (X6 Hi0) as [Y1 Y2]. destruct SRCB as [Z0|(b & Hb & B1 & B2 & B3 & B4)].
      + assert (BN : bs = []) by (apply length_zero_iff_nil; unfold n, len in Z0; lia). split; [intros j Hj; rewrite BN in Hj; cbn in Hj; lia | intros j Hj; lia].
      + assert (GLB1 : incl (PML.srep_blocks (g_rep g1)) (gB g1)) by (intros b0 Hb0; unfold gB, EBU.gB; apply in_or_app; left; exact Hb0).
        destruct (other_block LBo (gB g1) cr1 M1 _ (g_rep g1) b HH1 Hb GLB1) as (_ & BR & _).
        pose proof (blk_stretch E0 sp V S2 U2 U10 SPR Hobjs (CC.cp_F c) E' M1 M' (fst b) (snd b) q n XF HagE' (CC.lf_frame _ _ _ _ _ _ _ HLF) BR B1 B2) as AGQ.
        split; [apply (L5C.bytes_at_agree RSEGS M1 M' q bs AGQ); [lia | fold (len bs); fold n; lia | exact Y1] | exact (L5C.defined_agree M1 M' q n AGQ Y2)]. }
  unfold PML.cfg. change PC_WRITE_BIGNUM with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply (CH2V.cert_sound3V L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS eghost gB CredV XIv STKF SCRP NF32 U2 W_OK WRS_OK
            G.CPS K PML.fp_ok G.TAGS) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok3.
  - (* [comment removed for export] *) intros g1 i c kk ps j sg IL E E' R' M1 M' cr1 _ _ _ HC. exact HC.
  - (* [comment removed for export] *)
    intros g1 M0c OKV i c kk ps j sg IL. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [_ X]. discriminate X.
  - (* [comment removed for export] *)
    intros i c kk ps pc IL g1 M0c OKV.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [XF X]. apply andb_prop in XF as [XF XN].
    assert (XILEAF : forall E R1 (M1 : mem) m1 E' R' (M' : mem), CC.At (hl_segs L) c E R1 M1 ->
               CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS eghost gB CredV g1 M0c i E M1 m1 -> XIv g1 i E M1 -> env_agree (CC.cp_nx c) E E' ->
               CC.leaf_facts (hl_segs L) c ps E' R' M1 M' ->
               enc_inv M' V S2 g1 /\ incl (stack_blocks (g_sb g1) (g_scap g1)) (CH2.den E' (nth i G.BLS []) ++ LBo ++ GR)).
    { intros E R1 M1 m1 E' R' M' HAt HA HX Hag HLF. destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt HA HX Hag HLF) as (HINV & _ & _).
      split; [exact HINV|]. destruct HX as (_ & _ & X3 & X4 & _). rewrite X3, X4. fold GR. intros b Hb. apply in_or_app; right; apply in_or_app; right; exact Hb. }
    destruct (Z.eqb_spec pc PML.PC_STR_APPEND) as [->|Hne1].
    + (* [comment removed for export] *)
      apply andb_prop in X as [X X5]. apply andb_prop in X as [X X4]. apply andb_prop in X as [X X3].
      apply andb_prop in X as [X1 X2]. apply Nat.eqb_eq in X1. subst i. apply Z.eqb_eq in X2. apply expr_eqb_eq in X4, X5.
      unfold sink_j in X3. apply andb_prop in X3 as [X3a X3b].
      destruct (CH2.ret_of G.RETS 0 kk) as [j|] eqn:Hret; [|discriminate]. apply Nat.eqb_eq in X3a. subst j.
      destruct (nth_error G.CPS 1) as [cj|] eqn:Hcj; [|discriminate].
      destruct (EBU.sink_chk GT.NF G.HDECL S2E 0 c ps cj (nth 0 G.BLS []) (nth 1 G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
      assert (XILEAF' : forall E R1 (M1 : mem) m1 E' R' (M' : mem), CC.At (hl_segs L) c E R1 M1 ->
                 CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS eghost gB CredV g1 M0c 0%nat E M1 m1 -> XIv g1 0%nat E M1 -> env_agree (CC.cp_nx c) E E' ->
                 CC.leaf_facts (hl_segs L) c ps E' R' M1 M' ->
                 enc_inv M' V S2 g1 /\ incl (stack_blocks (g_sb g1) (g_scap g1)) (CH2.den E' (nth 0 G.BLS []) ++ LBo ++ GR) /\ g_len g1 + n <= CLU).
      { intros E R1 M1 m1 E' R' M' HAt HA HX Hag HLF. destruct (XILEAF E R1 M1 m1 E' R' M' HAt HA HX Hag HLF) as [Y1 Y2].
        split; [exact Y1|]. split; [exact Y2|]. destruct HX as (_ & _ & _ & _ & Y5 & _). rewrite Y5. unfold off. lia. }
      apply (EBU.append_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS GR kx bx XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K HKnil DEF0
               V S2 Hobjs W_S2 S2E 0 eq_refl OADDR APPEND_OK n 0%nat c kk ps 1%nat cj ci g1 M0c OKV IL Hret Hcj X2 Hchk XILEAF').
      * intros E R1 M1 m1 E' R' M' cr1 HAt HA HX Hag HLF CF HINV HH1.
        pose proof CF as [HA' HR Hreq (V1 & V2' & V3 & V4' & V5) HK [Hra' Hraok'] (Hsp' & Hc1 & Hs0 & Hc2) Hstk' Htp' HagE' Hden Hmeas].
        destruct (STRETCH g1 M0c 0%nat c kk ps _ E R1 M1 m1 E' R' M' IL HAt HA HX Hag HLF) as (_ & _ & HSRC). destruct (HSRC eq_refl) as [Hb' Hd'].
        assert (Ga1 : getr R' 11%bv = Z_to_bv 64 q).
        { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq, X4. cbn [edenot].
          destruct HagE' as [AG _]. rewrite <- AG by (unfold GT.NF; lia). exact V33. }
        assert (Ga2 : getr R' 12%bv = Z_to_bv 64 n).
        { rewrite (HR 12%bv). unfold sr_get. change (bv_eqb (12%bv : bv 5) 0) with false. cbv iota. change (ridx 12%bv) with 12%nat. rewrite Hreq, X5. cbn [edenot].
          destruct HagE' as [AG _]. rewrite <- AG by (unfold GT.NF; lia). exact V34. }
        exists q, bs. fold n. split; [exact Ga1|]. split; [exact Ga2|]. split; [reflexivity|]. split; [exact Hb'|].
        rewrite NILB in HH1 |- *. cbn [app] in HH1 |- *.
        assert (GLB1 : incl (PML.srep_blocks (g_rep g1)) (EBU.gB GR g1)) by (intros b0 Hb0; unfold EBU.gB; apply in_or_app; left; exact Hb0).
        pose proof HINV as (_ & _ & (Hst & _ & _) & Hln & _). fold (len (PML.srep_chars (g_rep g1))).
        destruct SRCB as [Z0|(b & Hb & B1 & B2 & B3 & B4)].
        -- split; [left; exact Z0|]. rewrite Z0, Z.add_0_r.
           destruct (g_rep g1) as [s0|cap0 p0 s0] eqn:Hrep; cbn [PML.str_at PML.srep_chars] in *.
           ++ destruct Hst as (H22 & _). unfold len. lia.
           ++ destruct Hst as (_ & _ & Hlt). destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _).
              assert (Hin : In (p0, cap0) (LBo ++ EBU.gB GR g1)) by (apply in_or_app; right; unfold EBU.gB; rewrite Hrep; left; reflexivity).
              destruct (Hwf _ Hin) as ((R0 & R1' & R2 & R3 & R4) & _). cbn [fst snd] in *. unfold len. lia.
        -- destruct (other_block LBo (EBU.gB GR g1) cr1 M' _ (g_rep g1) b HH1 Hb GLB1) as (NI & (R0 & R1' & R2 & R3 & R4) & OTH).
           split.
           { right. right. right. exists b. split; [apply in_or_app; left; exact Hb|]. split; [exact NI|]. split; [exact B1|]. split; [exact B2 | exact Hd']. }
           destruct (g_rep g1) as [s0|cap0 p0 s0] eqn:Hrep; cbn [PML.str_at PML.srep_chars] in *.
           ++ destruct Hst as (H22 & _). unfold len. lia.
           ++ destruct Hst as (_ & _ & Hlt). destruct OTH as ((P0 & P1 & P2 & P3 & P4) & DJ). unfold len. lia.
      * intros E E' R' M1 M' E2 M2 g' HX HagE' Hag HLF Hag2 Hnx HINV2 G1 G2 G3 G4. destruct HX as (_ & Y2 & Y3 & Y4 & Y5 & _).
        split; [exact HINV2|]. rewrite G1, G2, G3, G4, Y5. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|]. split; [unfold off; lia | intros X0; discriminate X0].
    + (* [comment removed for export] *)
      apply andb_prop in X as [X0 X1]. apply Nat.eqb_eq in X0. subst i.
      intros fx' E R1 M1 m1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
      destruct (STRETCH g1 M0c 1%nat c kk ps _ E R1 M1 m1 E' R' M' IL HAt HAmb HX Hag HLF) as (HINV & HagE'0 & _).
      assert (DEFC : L5.defined M0c (sp - 8672) 8672) by (rewrite <- SCRV; exact (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV)).
      apply (PB.exit_ret L HI HIok LAY GT.NF E0 M0c model (CH2V.LBr LBo eghost gB g1) sp G.HDECL W G.BLS (CredV g1) STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K (XIv g1)
               (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV) (fun _ => 0) (fun _ => 0)
               8672 ltac:(rewrite SCRV; lia) ltac:(unfold hl_ceil; lia) DEFC R EV r Hra Hraok heap_ok3 RETPC 1%nat c kk ps pc ret_at IL X1 fx' E R1 M1 m1 E' R' M' HAt HAmb Hag HLF).
      intros HRP HP HA' HagE'. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & _ & _).
      destruct HX as (_ & Y2 & Y3 & Y4 & Y5 & _).
      assert (HP2 : L5C.hpres L LBo sp 8672 W M M').
      { rewrite <- SCRV. apply (CH2V.hpres_rebase L GT.NF M LBo sp G.HDECL W eghost gB NF32 g1 M0c M' OKV). rewrite SCRV. exact HP. }
      apply (Hcont fx' R' M' m1 (LBo ++ g_lbv g1) cr1 LBo W HFP); [| exact HRP | exact HP2 | exact Hbv1 |].
      * exists g1, n. split; [exact HINV|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|]. split; [reflexivity|]. split; [rewrite Y5; unfold off; reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HC1.
      * unfold CH2.cur, CH2V.LBr in HH1. rewrite <- (GBL g1 Y3 Y4). rewrite NILB in HH1. exact HH1.
  - reflexivity.
  - (* [comment removed for export] *)
    rewrite LS.
    destruct I1 as (H1 & H2 & H3 & (fl & H4 & H4') & H5 & _).
    unfold O_SINK, O_BIGNUM_FMT in *.
    assert (Hds : L5.defined M (sp - 8672) 8672) by (intros j Hj; replace (sp - 8672 + j) with (sp - (176 + (256 + (16 + 8224))) + j) by lia; apply S5; lia).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := V + 8) (z := S2); [ev_start | lia | lia | exact V32 | exact H2].
    + eapply PB2.kword8_intro with (A := V + 27) (z := 0); [ev_start | lia | lia | reflexivity | lia | exact H5].
    + eapply CL5.kword64_intro with (A := V + 296) (z := col); [ev_start | lia | lia | exact V35 | exact Hcol].
    + eapply CL5.kword64_intro with (A := sv) (z := q); [ev_start | lia | lia | exact V33 | exact Hq0].
    + eapply CL5.kword64_intro with (A := sv + 8) (z := n); [ev_start | lia | lia | exact V34 | exact Hq8].
    + e_range. + e_range.
    + e_wr. + e_range. + e_align OV3.
    + e_range. + e_align OS3.
    + e_range. + e_align SV3.
    + e_unk. + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj. + e_disj. + e_disj. + e_disj.
  - (* [comment removed for export] *)
    apply (CH2V.amb3V_intro L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS eghost gB CredV XIv g M 0%nat E0 M model
             (CH2V.okV_refl L M LBo sp G.HDECL W DEF0)).
    split; [|split; [exact Hinv | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [unfold off; lia | intros _; split; [exact Hbq | exact Hdq]]]]]]].
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [unfold CH2.cur, CH2V.LBr; cbn [nth G.BLS GT.BL0 CH2.den map app]; rewrite (GBL g eq_refl eq_refl); exact HH|].
    exact Hcred.
  - exact Hfp.
Qed.
End WriteBignumOk.
End EWBU.
Print Assumptions EWBU.write_bignum_ok.
