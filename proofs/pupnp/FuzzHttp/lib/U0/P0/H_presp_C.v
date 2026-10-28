(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF AllocSpec SReach.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_scanner_get_token H_vfmatch_A H_match H_obj H_membuffer_assign H_prep.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_presp_A H_presp_B.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Lemma NoDup_map_on : forall {X Y} (f : X -> Y) (l : list X),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros X Y f l INJ ND. induction ND as [|a l NI ND IH]; cbn; constructor.
  - rewrite list_elem_of_In. intros IN. apply in_map_iff in IN. destruct IN as (y & E & Hy).
    assert (y = a) by (apply INJ; [right; exact Hy| left; reflexivity| exact E]). subst y. apply NI. rewrite list_elem_of_In. exact Hy.
  - apply IH. intros x y Hx Hy. apply INJ; right; assumption.
Qed.

Lemma nodup_ids_eq : forall {Kt} (LB : list (block Kt)) x y, NoDup (map blk_id LB) -> In x LB -> In y LB -> blk_id x = blk_id y -> x = y.
Proof.
  intros Kt LB. induction LB as [|b LB IH]; intros x y ND Hx Hy E; [destruct Hx|].
  cbn in ND. inversion ND as [|? ? NI ND']; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| exfalso| exfalso| exact (IH x y ND' Hx Hy E)].
  - apply NI. rewrite list_elem_of_In. rewrite E. apply in_map. exact Hy.
  - apply NI. rewrite list_elem_of_In. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma bytes_at_snoc : forall m a bs b,
  bytes_at rsegs m a bs -> mrd rsegs m (wa (a + Z.of_nat (length bs))) = Some b -> (a + Z.of_nat (length bs) + 1 <= 2^64)%Z ->
  bytes_at rsegs m a (bs ++ [b]).
Proof.
  intros m a bs b (H0 & H1 & HB) RD HI. split; [exact H0|]. rewrite length_app. cbn [length]. split; [lia|].
  intros i Hi. destruct (Nat.lt_ge_cases i (length bs)).
  - rewrite nth_error_app1 by lia. apply HB. lia.
  - assert (i = length bs) by lia. subst i. rewrite nth_error_app2, Nat.sub_diag by lia. cbn. exact RD.
Qed.
Lemma bytes_at_extend : forall k m a bs,
  bytes_at rsegs m a bs ->
  (forall x, (a + Z.of_nat (length bs) <= x < a + Z.of_nat (length bs) + Z.of_nat k)%Z -> exists v, mrd rsegs m (wa x) = Some v) ->
  (a + Z.of_nat (length bs) + Z.of_nat k <= 2^64)%Z ->
  exists sl, bytes_at rsegs m a (bs ++ sl) /\ length sl = k.
Proof.
  induction k as [|k IH]; intros m a bs B RD HI.
  - exists []. rewrite app_nil_r. split; [exact B| reflexivity].
  - destruct (RD (a + Z.of_nat (length bs))%Z ltac:(lia)) as [v Hv].
    pose proof (bytes_at_snoc m a bs v B Hv ltac:(lia)) as B1.
    destruct (IH m a (bs ++ [v]) B1) as (sl & B2 & L2).
    + intros x Hx. apply RD. rewrite length_app in Hx. cbn [length] in Hx. lia.
    + rewrite length_app. cbn [length]. lia.
    + exists (v :: sl). rewrite <- app_assoc in B2. cbn [app] in B2. split; [exact B2| cbn; lia].
Qed.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L_ := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Hypothesis LOK : layout_ok AI.
  Hypothesis REALLOCPC : al_realloc_pc L_ = 0x1995c.
  Hypothesis TPV : al_tp L_ = 0x3b820.
  Hypothesis ERRNOV : al_errno L_ = 0x3b77c.
  Hypothesis CAN : canary_ok AI.

  Hypothesis ERRNC : forall lo hi, al_client_static L_ lo hi -> hi <= al_errno L_ \/ al_errno L_ + 4 <= lo.

  Hypothesis BLK4096 : blk4096_ok AI.
  Hypothesis BLKWIN : forall s LB m (b : BLK), RHEAP rsegs AI s LB m -> In b LB -> blk_addr b + blk_size b <= 0x2a000 \/ 0x5d000 <= blk_addr b.
  Notation bsub := (bsub AI).
  Notation mown := (mown AI).
  Notation okb := (okb AI).

  Definition p_smsgW (m : mem) (LB : list BLK) (P SA slen scap : Z) (sok : option K) (sbs : list byte) : Prop :=
    rw_cells rsegs m (P + 232) (mbuf_cells SA slen scap) /\ mown m LB SA scap sok sbs /\ 0 <= slen <= scap /\ scap < 2^32.

  Definition RESP_DEPTH : Z := 1176.
  Definition resp_W (P : Z) : list ivl := [(P + 224, P + 288); (P + 440, P + 452); (P + 488, P + 496)].

  Definition presp_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LBK : list BLK) (P cur A len cap : Z) (okm : option K) (bs : list byte)
      (rm isreq err hack pos entp clen csz esp lo B : Z) (m : mem) : ai_PS rsegs AI -> list BLK -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r cur' sc' maj' min' SA' slen' scap' err' pos' : Z) (sok' : option K) (sbs' : list byte),
      ms' = MS (mkR ra sp gp (wz (al_tp L_)) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ RENV rsegs AI m' B
      /\ (exists errv', rw_cells rsegs m' (al_errno L_) [C4 errv'])
      /\ hpx AI (resp_W P) LBK (bv_unsigned sp) m m'
      /\ RHEAP rsegs AI s' LB' m'
      /\ bsub (okb okm A cap ++ okb sok' SA' scap' ++ LBK) LB' /\ NoDup (map blk_id (okb okm A cap ++ okb sok' SA' scap' ++ LBK))
      /\ p_scan m' P cur' /\ p_msg AI m' LB' P A len cap okm bs /\ p_rs m' P rm sc' /\ p_ver m' P isreq maj' min'
      /\ p_smsgW m' LB' P SA' slen' scap' sok' sbs' /\ p_ctl m' P err' hack pos' entp clen csz esp
      /\ (0 <= r <= 5)%Z /\ (cur <= cur' <= len)%Z
      /\ ( (r = 4 /\ pos' = POS_HEADERS /\ err' = err /\ 0 <= maj' /\ 0 <= min' /\ 0 <= sc' /\ okm <> None)
         \/ (r <> 4 /\ pos' = pos /\ (err' = err \/ err' = 500)) ).

  #[using="AC LOK REALLOCPC TPV ERRNOV CAN ERRNC BLK4096 BLKWIN"] Theorem parser_parse_responseline_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (LBK : list BLK) (P lo B cur A len cap : Z) (okm : option K) (bs : list byte)
      (SA slen scap : Z) (sok : option K) (sbs : list byte) (rm sc isreq maj min err hack pos entp clen csz esp : Z) (errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z -> (B < 2^64)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (0x5d000 <= lo)%Z -> (lo <= bv_unsigned sp - RESP_DEPTH - al_stack L_)%Z -> (0 <= al_stack L_)%Z ->
    rw_cells rsegs m (al_errno L_) [C4 errv] -> mem_inv rsegs m ->
    p_scan m P cur -> p_msg AI m LB P A len cap okm bs -> (0 <= cur <= len)%Z ->
    p_rs m P rm sc -> p_ver m P isreq maj min -> p_smsg AI m LB P SA slen scap sok sbs -> p_ctl m P err hack pos entp clen csz esp ->
    bsub (okb okm A cap ++ okb sok SA scap ++ LBK) LB -> NoDup (map blk_id (okb okm A cap ++ okb sok SA scap ++ LBK)) ->
    (bv_unsigned sp <= P)%Z -> (P + 504 <= B)%Z -> (P + 504 < 2^62)%Z -> (P mod 8 = 0)%Z -> (bv_unsigned sp mod 8 = 0)%Z ->
    a0 = wz P ->
    SREACH AI (presp_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBK P cur A len cap okm bs rm isreq err hack pos entp clen csz esp lo B m)
      (MS (mkR ra sp gp (wz (al_tp L_)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz parse_responseline_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB BHI ST CEIL LO0 LO STK ERR MI PSC PMSG CUR PRS PVER PSM PCTL BSUB ND SPP PB P62 P8 SP8 ->.
    unfold RESP_DEPTH in LO. rewrite TPV. rewrite ERRNOV in ERR.
    pose proof (word_lt64 sp) as SPR.
    set (spv := bv_unsigned sp) in *. assert (ESP : sp = wz spv) by (subst spv; symmetry; apply Z_to_bv_bv_unsigned).
    set (q := (spv - 80)%Z). assert (Hq : spv = (q + 80)%Z) by (unfold q; lia). clearbody q spv. subst spv. rewrite ESP.
    assert (QP : (q + 80 <= P)%Z) by lia. assert (QLO : (lo + 1096 <= q)%Z) by lia.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    pose proof PSC as SC. unfold p_scan in SC.
    destruct PMSG as (MBC & OWN & HL & HC & NULM). unfold LMAX in HC.
    destruct PRS as (RSC & RMR & SCR). destruct PVER as ([pad VERC] & ISR & MJR & MNR).
    destruct PSM as (SMC & SOWN & SL1 & SCP1 & SNUL). unfold LMAX in SCP1. destruct PCTL as (CTL & ERR_R & HACK_R & POS_R & ENTP_R & CLEN_R & CSZ_R & ESP_R).
    destruct (proj1 (bsub_app AI _ _ _) BSUB) as [SUBM BSUB2]. destruct (proj1 (bsub_app AI _ _ _) BSUB2) as [SUBS SUBK].
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3. rewrite ERRNOV in WE1, WE2.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.

    assert (MF : bytes_at rsegs m A bs /\ (Z.of_nat (length bs) >= len)%Z /\ (0 < A \/ (A = 0 /\ len = 0))%Z /\ (A + Z.of_nat (length bs) <= alloc_ceiling)%Z
                 /\ (okm = None -> A = 0 /\ len = 0 /\ bs = []) /\ (forall km, okm = Some km -> In (km, A, cap + 1) LB /\ Z.of_nat (length bs) = cap + 1 /\ 4096 <= A)%Z).
    { destruct okm as [km|]; cbn in OWN.
      - destruct OWN as [HIN BLK]. destruct (ai_block_range rsegs AI _ _ _ _ HR HIN) as (R1 & R2 & R3 & R4 & _). cbn in R1, R4.
        pose proof (BLK4096 _ _ _ _ HR HIN) as R5. cbn in R5.
        pose proof (proj2 (proj1 BLK)) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
        destruct BLK as [[W _] _]. cbn in W. destruct W as [W _].
        split; [exact BY|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros; discriminate|]. intros km' E. injection E as <-. split; [exact HIN| lia].
      - destruct OWN as (-> & -> & ->). cbn in NULM. cbn. split. { split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. }
        split; [lia|]. split; [lia|]. split; [lia|]. split; [intros _; split; [reflexivity| split; [exact NULM| reflexivity]]| intros; discriminate]. }
    destruct MF as (BUF & LBS & ANZ & AHI & OKN & OKS).

    eapply sreach_evt.
    { eapply (rl_pre P q lo QLO LO0 QP P62 A len cap cur bs); try eassumption. all: lia. }
    intros ms1 PO. destruct PO as (m1 & r1 & cur1 & PO). do 14 (let x := fresh "y" in destruct PO as [x PO]).
    destruct PO as (MU1 & WM1 & MI1 & MBC1 & BUF1 & CUR1 & RR1 & SC1 & ALT).

    assert (HR1 : RHEAP rsegs AI s LB m1).
    { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
    assert (HE1 : RENV rsegs AI m1 B).
    { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
    assert (HP1 : hpx AI (resp_W P) LBK (q + 80) m m1).
    { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact SUBK| exact MU1| exact WM1|]. unfold resp_W.
      constructor; [left; cbn; lia|]. constructor; [right; right; cbn; lia| constructor]. }
    unfold mbuf_cells, MEMBUF_DEF_SIZE_INC, p_ctl_cells in *.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ RSC MU1 WM1 ltac:(cbn; lia)) as RSC1.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ VERC MU1 WM1 ltac:(cbn; lia)) as VERC1.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ SMC MU1 WM1 ltac:(cbn; lia)) as SMC1.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ CTL MU1 WM1 ltac:(cbn; lia)) as CTL1.
    assert (SOWN1 : mown m1 LB SA scap sok sbs).
    { destruct sok as [ks|]; cbn in SOWN |- *; [| exact SOWN]. destruct SOWN as [HIN BLK]. split; [exact HIN|].
      destruct (ai_block_range rsegs AI _ _ _ _ HR HIN) as (R1 & _ & _ & R4 & _). cbn in R1, R4.
      eapply (rw_cells_transport rsegs _ m m1); [exact BLK| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (OWN1 : mown m1 LB A cap okm bs).
    { destruct okm as [km|]; cbn in OWN |- *; [| exact OWN]. destruct OWN as [HIN BLK]. split; [exact HIN|].
      destruct (ai_block_range rsegs AI _ _ _ _ HR HIN) as (R1 & _ & _ & R4 & _). cbn in R1, R4.
      eapply (rw_cells_transport rsegs _ m m1); [exact BLK| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    clear MU1 WM1 ERR RSC VERC SMC CTL SOWN OWN BUF MI ST SC.
    destruct ALT as [(NR & ST1 & ->)|(o & l & bcr & j0 & tyw & -> & O1 & L1 & OL & Hbcr & CRLF & ST1 & Q0 & Q12 & Q16 & FSH & ->)].
    {
      apply sreach_ret. unfold presp_post. rewrite !(unsigned_lit (q + 80)) by lia. do 15 eexists. exists r1, cur1, sc, maj, min, SA, slen, scap, err, pos, sok, sbs.
      split; [rewrite TPV; reflexivity|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact HE1|]. split; [eexists; rewrite ERRNOV; exact ERR1|].
      split; [exact HP1|]. split; [exact HR1|]. split; [exact BSUB|]. split; [exact ND|].
      split; [exact SC1|]. split; [split; [exact MBC1| split; [exact OWN1| split; [lia| split; [unfold LMAX; lia| exact NULM]]]]|].
      split; [split; [exact RSC1| lia]|]. split; [split; [eexists; exact VERC1| lia]|].
      split; [split; [exact SMC1| split; [exact SOWN1| lia]]|]. split; [split; [exact CTL1| lia]|].
      split; [lia|]. split; [lia|]. right. split; [exact NR|]. split; [reflexivity| left; reflexivity]. }

    destruct okm as [km|]. 2:{ exfalso. destruct (OKN eq_refl) as (_ & LEN0 & _). lia. }
    destruct (OKS km eq_refl) as (HINM & LBS2 & A4096). clear OKN OKS.
    cbn in OWN1. destruct OWN1 as [_ BLK1].
    destruct (ai_block_range rsegs AI _ _ _ _ HR HINM) as (R1 & R2 & R3 & R4 & _). cbn in R1, R2, R3, R4.
    pose proof (BLKWIN _ _ _ _ HR HINM) as RW. cbn in RW.
    assert (RU : (A + (cap + 1) <= round_up8 (A + (cap + 1)) <= A + (cap + 1) + 7)%Z /\ (round_up8 (A + (cap + 1)) mod 8 = 0)%Z
                 /\ (round_up8 (A + (cap + 1)) <= alloc_ceiling)%Z /\ (A + (cap + 1) <= 0x2a000 -> round_up8 (A + (cap + 1)) <= 0x2a000)%Z).
    { unfold round_up8. Z.div_mod_to_equations. lia. }
    destruct RU as (RU1 & RU2 & RU3 & RU4).

    assert (SLX : exists sl, bytes_at rsegs m1 (A + (cap + 1)) sl /\ Z.of_nat (length sl) = (round_up8 (A + (cap + 1)) - (A + (cap + 1)))%Z).
    { destruct (bytes_at_extend (Z.to_nat (round_up8 (A + (cap + 1)) - (A + (cap + 1)))) m1 (A + (cap + 1)) []) as (sl & B2 & L2).
      - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
      - intros x Hx. cbn [length Z.of_nat] in Hx. eapply (ai_block_slack rsegs AI); [exact HR1| exact HINM| cbn; lia].
      - cbn [length Z.of_nat]. lia.
      - exists sl. cbn [app] in B2. split; [exact B2| lia]. }
    destruct SLX as (sl & SLK & LSL).
    destruct (CAN _ _ _ HR1) as [SSP1 [canary SSP2]].

    assert (NEQS : forall b0, In b0 (okb sok SA scap ++ LBK) -> In b0 LB /\ b0 <> (km, A, cap + 1)%Z).
    { intros b0 Hb0. split; [exact (BSUB2 b0 Hb0)|]. intros ->. exact (nodup_in_neq AI _ _ _ _ ND (or_introl eq_refl) Hb0 eq_refl). }

    eapply sreach_evt.
    { eapply (rl_mid P q lo QLO LO0 QP P62 A len cap o l cur1 bs sl bcr j0 tyw pad canary errv rm sc isreq maj min); try eassumption; try LiaTuning.alia. }
    intros ms2 PO. destruct PO as (m2 & sc' & maj' & min' & errv' & PO). do 14 (let x := fresh "z" in destruct PO as [x PO]).
    destruct PO as (MU2 & WM2 & MI2 & BLK2 & SLK2 & RS2 & VER2 & SCR2 & MJR2 & MNR2 & SSP1' & SSP2' & ERR2 & ALT2).
    assert (HR2 : RHEAP rsegs AI s LB m2).
    { eapply (ai_heap_frame rsegs AI); [exact HR1| exact MU2| exact WM2|].
      constructor; [left; cbn; lia|]. constructor. { right; right; right. exists (km, A, cap + 1)%Z. split; [exact HINM| cbn; lia]. }
      constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [right; right; left; rewrite ERRNOV; cbn; lia| constructor]. }
    assert (HE2 : RENV rsegs AI m2 B).
    { eapply (ai_env_frame rsegs AI); [exact HR1| exact HE1| exact MU2| exact WM2|].
      constructor; [left; cbn; lia|]. constructor. { right; right; right. exists (km, A, cap + 1)%Z. split; [exact HINM| cbn; lia]. }
      constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [right; right; left; rewrite ERRNOV; cbn; lia| constructor]. }
    assert (HP2 : hpx AI (resp_W P) LBK (q + 80) m1 m2).
    { eapply (hpx_seg rsegs AI); [exact LOK| exact HR1| exact SUBK| exact MU2| exact WM2|]. unfold resp_W.
      constructor; [left; cbn; lia|].
      constructor. { right; left. cbn. intros a Ha. eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR1| exact HINM| | lia| cbn; lia].
                     intros b0 Hb0. apply NEQS. apply in_or_app. right. exact Hb0. }
      constructor; [right; right; cbn; lia|]. constructor; [right; right; cbn; lia|].
      constructor; [| constructor]. right; left. cbn. intros a Ha [Hc|[(slo & shi & Hst & Hr)|(b0 & Hb0 & Hr0)]]; [lia| |].
      - pose proof (ERRNC slo shi Hst). rewrite ERRNOV in *. lia.
      - destruct (ai_block_range rsegs AI _ _ _ _ HR1 (SUBK b0 Hb0)) as (_ & _ & _ & _ & RF).
        pose proof (proj1 (List.Forall_forall _ _) RF we Hwe) as X. cbn in X. lia. }
    pose proof (rw_cells_transport rsegs _ m1 m2 _ _ SC1 MU2 WM2 ltac:(cbn; lia)) as SC2.
    pose proof (rw_cells_transport rsegs _ m1 m2 _ _ MBC1 MU2 WM2 ltac:(cbn; lia)) as MBC2.
    pose proof (rw_cells_transport rsegs _ m1 m2 _ _ SMC1 MU2 WM2 ltac:(cbn; lia)) as SMC2.
    pose proof (rw_cells_transport rsegs _ m1 m2 _ _ CTL1 MU2 WM2 ltac:(cbn; lia)) as CTL2.
    assert (SOWN2 : mown m2 LB SA scap sok sbs).
    { destruct sok as [ks|]; cbn in SOWN1 |- *; [| exact SOWN1]. destruct SOWN1 as [HIN BLK]. split; [exact HIN|].
      destruct (ai_block_range rsegs AI _ _ _ _ HR HIN) as (Q1 & _ & _ & Q4 & QF). cbn in Q1, Q4.
      pose proof (proj1 (List.Forall_forall _ _) QF we Hwe) as X. cbn in X.
      assert (DJ : (SA + (scap + 1) <= A \/ A + (cap + 1) <= SA)%Z).
      { pose proof (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR HIN HINM) as D. cbn in D. apply D. exact (proj2 (NEQS (ks, SA, scap + 1)%Z ltac:(cbn; left; reflexivity))). }
      eapply (rw_cells_transport rsegs _ m1 m2); [exact BLK| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    clear MU2 WM2 SC1 MBC1 SMC1 CTL1 SOWN1 BLK1 SLK ERR1 RSC1 VERC1 SSP1 SSP2 MI1 ST1.
    destruct ALT2 as [(ST2 & ->)|(t' & nv & sb & RT & -> & SC0 & MJ0 & MN0 & ST2 & Q02 & Q122 & Q162 & FSH2 & ->)].
    {
      apply sreach_ret. unfold presp_post. rewrite !(unsigned_lit (q + 80)) by lia. do 15 eexists. exists 3, cur1, sc', maj', min', SA, slen, scap, err, pos, sok, sbs.
      split; [rewrite TPV; reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact HE2|]. split; [eexists; rewrite ERRNOV; exact ERR2|].
      split; [eapply (hpx_trans rsegs AI); [exact HP1| exact HP2]|]. split; [exact HR2|]. split; [exact BSUB|]. split; [exact ND|].
      split; [exact SC2|]. split; [split; [exact MBC2| split; [cbn; split; [exact HINM| exact BLK2]| split; [lia| split; [unfold LMAX; lia| exact NULM]]]]|].
      split; [split; [exact RS2| lia]|]. split; [split; [eexists; exact VER2| lia]|].
      split; [split; [exact SMC2| split; [exact SOWN2| lia]]|]. split; [split; [exact CTL2| lia]|].
      split; [lia|]. split; [lia|]. right. split; [lia|]. split; [reflexivity| left; reflexivity]. }

    set (n := (l - (t' - o))%Z) in *. assert (Hn : n = (l - (t' - o))%Z) by reflexivity. clearbody n.
    assert (EQq : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
    rewrite <- ERRNOV in ERR2.

    pose proof (proj2 (proj1 BLK2)) as BY2. cbn [cells_bytes cbytes] in BY2. rewrite app_nil_r in BY2.
    set (src := firstn (Z.to_nat n) (skipn (Z.to_nat t') bs)).
    assert (LSRC : Z.of_nat (length src) = n). { subst src. rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia. }
    assert (BSRC : bytes_at rsegs m2 (A + t') src).
    { rewrite <- (firstn_skipn (Z.to_nat t') bs) in BY2. apply bytes_at_app in BY2. destruct BY2 as [_ BY2].
      rewrite firstn_length_le in BY2 by lia. replace (A + Z.of_nat (Z.to_nat t'))%Z with (A + t')%Z in BY2 by lia.
      rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat t') bs)) in BY2. apply bytes_at_app in BY2. destruct BY2 as [BY2 _]. exact BY2. }

    assert (KMK : In (km, A, cap + 1)%Z (lb_keep AI sok LB)).
    { destruct sok as [ks|]; cbn; [| exact HINM]. apply (in_lb_remove AI); [exact HINM|]. cbn. intros ->.
      cbn in ND. inversion ND as [|? ? NI ND']; subst. apply NI. rewrite list_elem_of_In. cbn. left. reflexivity. }
    assert (KSUB : forall b, In b LBK -> In b (lb_keep AI sok LB)).
    { intros b Hb. destruct sok as [ks|]; cbn; [| exact (SUBK b Hb)]. apply (in_lb_remove AI); [exact (SUBK b Hb)|].
      intros E.
      assert (ND'' : NoDup (map blk_id ([(ks, SA, scap + 1)%Z] ++ LBK))). { cbn in ND |- *. inversion ND; subst. assumption. }
      assert (EQB : (ks, SA, scap + 1)%Z = b).
      { symmetry. eapply (nodup_ids_eq LB); [eapply (ai_blocks_nodup rsegs AI); exact HR| exact (SUBK b Hb)| apply SUBS; cbn; left; reflexivity| exact E]. }
      exact (nodup_in_neq AI _ _ _ _ ND'' (or_introl eq_refl) Hb EQB). }
    replace (wz 0x3b820) with (wz (al_tp L_)) by (rewrite TPV; reflexivity).
    eapply sreach_bind.
    { eapply (membuffer_assign_spec AI AC LOK REALLOCPC) with (ok := sok) (MB := (P + 232)%Z) (SRC := (A + t')%Z) (n := n) (A := SA) (len := slen) (cap := scap)
             (lo := lo) (B := B) (src := src) (bs := sbs) (errv := errv'); rewrite ?EQq; try eassumption; try reflexivity; try lia.
      - apply mbloc_stack; lia.
      - eapply (client_range_block rsegs AI); [exact KMK| cbn; lia| cbn; lia]. }
    intros s3' LB3 ms3 PO3. unfold membuffer_assign_post in PO3.
    destruct PO3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3 & r3 & SA' & slen' & scap' & sok' & sbs'
                     & -> & MI3 & ST3 & HE3 & [errv3 ERR3] & HP3 & HR3 & SUB3 & SMC3 & SL3 & SCP3 & SCB3 & SOWN3 & FRESH3 & RES3).
    rewrite EQq in ST3, HP3.

    assert (TR : forall X cs, rw_cells rsegs m2 X cs -> (q <= X)%Z -> (X + Z.of_nat (cells_size cs) <= P + 232 \/ P + 264 <= X)%Z -> rw_cells rsegs m3 X cs).
    { intros X cs H H1 H2. eapply (hpx_rw_cells rsegs AI); [exact HP3| exact H| apply client_range_above; lia| cbn; lia]. }
    pose proof (TR _ _ SC2 ltac:(lia) ltac:(cbn; lia)) as SC3x.
    pose proof (TR _ _ MBC2 ltac:(lia) ltac:(cbn; lia)) as MBC3.
    pose proof (TR _ _ CTL2 ltac:(lia) ltac:(cbn; lia)) as CTL3.
    pose proof (TR _ _ RS2 ltac:(lia) ltac:(cbn; lia)) as RS3.
    pose proof (TR _ _ VER2 ltac:(lia) ltac:(cbn; lia)) as VER3.
    pose proof (TR _ _ Q02 ltac:(lia) ltac:(cbn; lia)) as Q03.
    pose proof (TR _ _ Q122 ltac:(lia) ltac:(cbn; lia)) as Q123.
    pose proof (TR _ _ Q162 ltac:(lia) ltac:(cbn; lia)) as Q163.
    pose proof (TR _ _ FSH2 ltac:(lia) ltac:(cbn; lia)) as FSH3.
    assert (BLK3 : rw_cells rsegs m3 A [CB (Z.to_nat (cap + 1)) bs]).
    { eapply (hpx_rw_cells rsegs AI); [exact HP3| exact BLK2| | cbn; lia]. eapply (client_range_block rsegs AI); [exact KMK| cbn; lia| cbn; lia]. }
    clear TR SC2 MBC2 CTL2 RS2 VER2 Q02 Q122 Q162 FSH2 BLK2 BY2 BSRC SLK2 SSP1' SSP2' ERR2 MI2 ST2 SOWN2 SMC2.
    replace (ret_pc (wz 0x14bd0)) with (wz 0x14bd0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    assert (RR3 : (r3 = 0 \/ r3 = -104)%Z) by (destruct RES3 as [(E & _)|(E & _)]; [left| right]; exact E).
    eapply sreach_evt.
    { rewrite TPV. eapply (rl_fin P q lo ltac:(lia) QP ltac:(lia) r3 err hack pos entp clen csz esp); try eassumption.
      split; [eexists; exact Q03|]. split; [eexists; exact Q123| do 2 eexists; exact Q163]. }
    intros ms4 (a0' & m4 & -> & MU4 & WM4 & MI4 & ST4 & RES4).

    assert (HR4 : RHEAP rsegs AI s3' LB3 m4).
    { eapply (ai_heap_frame rsegs AI); [exact HR3| exact MU4| exact WM4|]. constructor; [left; cbn; lia| constructor]. }
    assert (HE4 : RENV rsegs AI m4 B).
    { eapply (ai_env_frame rsegs AI); [exact HR3| exact HE3| exact MU4| exact WM4|]. constructor; [left; cbn; lia| constructor]. }
    assert (SUBK3 : forall b, In b LBK -> In b LB3) by (intros b Hb; apply SUB3; apply KSUB; exact Hb).
    assert (HP4 : hpx AI (resp_W P) LBK (q + 80) m3 m4).
    { eapply (hpx_seg rsegs AI); [exact LOK| exact HR3| exact SUBK3| exact MU4| exact WM4|]. unfold resp_W.
      constructor; [right; right; cbn; lia| constructor]. }
    assert (HP14 : hpx AI (resp_W P) LBK (q + 80) m m4).
    { eapply (hpx_trans rsegs AI); [exact HP1|]. eapply (hpx_trans rsegs AI); [exact HP2|]. eapply (hpx_trans rsegs AI); [| exact HP4].
      eapply (hpx_weaken rsegs AI); [exact HP3| unfold resp_W, sub_fp; cbn [outside]; intros; lia| lia| exact KSUB]. }
    pose proof (rw_cells_transport rsegs _ m3 m4 _ _ SC3x MU4 WM4 ltac:(cbn; lia)) as SC4.
    pose proof (rw_cells_transport rsegs _ m3 m4 _ _ MBC3 MU4 WM4 ltac:(cbn; lia)) as MBC4.
    pose proof (rw_cells_transport rsegs _ m3 m4 _ _ RS3 MU4 WM4 ltac:(cbn; lia)) as RS4.
    pose proof (rw_cells_transport rsegs _ m3 m4 _ _ VER3 MU4 WM4 ltac:(cbn; lia)) as VER4.
    pose proof (rw_cells_transport rsegs _ m3 m4 _ _ SMC3 MU4 WM4 ltac:(cbn; lia)) as SMC4.
    pose proof (rw_cells_transport rsegs _ m3 m4 _ _ ERR3 MU4 WM4 ltac:(rewrite ERRNOV; cbn; lia)) as ERR4.
    pose proof (rw_cells_transport rsegs _ m3 m4 _ _ BLK3 MU4 WM4 ltac:(cbn; lia)) as BLK4.
    assert (SOWN4 : mown m4 LB3 SA' scap' sok' sbs').
    { destruct sok' as [ks'|]; cbn in SOWN3 |- *; [| exact SOWN3]. destruct SOWN3 as [HIN BLK]. split; [exact HIN|].
      destruct (ai_block_range rsegs AI _ _ _ _ HR3 HIN) as (Q1 & _ & _ & Q4 & _). cbn in Q1, Q4.
      eapply (rw_cells_transport rsegs _ m3 m4); [exact BLK| exact MU4| exact WM4|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }

    assert (BSUB4 : bsub (okb (Some km) A cap ++ okb sok' SA' scap' ++ LBK) LB3).
    { intros b Hb. cbn in Hb. destruct Hb as [<-|Hb]; [apply SUB3; exact KMK|]. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (SUBK3 b Hb)].
      destruct sok' as [ks'|]; cbn in Hb; [| destruct Hb]. destruct Hb as [<-|[]]. cbn in SOWN3. exact (proj1 SOWN3). }
    assert (ND4 : NoDup (map blk_id (okb (Some km) A cap ++ okb sok' SA' scap' ++ LBK))).
    { apply NoDup_map_on.
      - intros bx bz Hx Hy E. eapply (nodup_ids_eq LB3); [eapply (ai_blocks_nodup rsegs AI); exact HR3| exact (BSUB4 bx Hx)| exact (BSUB4 bz Hy)| exact E].
      -
        assert (NDK : NoDup LBK).
        { cbn in ND. inversion ND as [|? ? _ ND']; subst. rewrite map_app in ND'. apply list.NoDup_app in ND'. destruct ND' as (_ & _ & NDK). exact (list.NoDup_fmap_1 blk_id LBK NDK). }
        assert (NDS : NoDup (okb sok' SA' scap' ++ LBK)).
        { destruct sok' as [ks'|]; cbn; [| exact NDK]. apply base.NoDup_cons_2; [| exact NDK]. rewrite list_elem_of_In. intros Hk.
          pose proof (FRESH3 _ (KSUB _ Hk)) as X. cbn in X. exact (X eq_refl). }
        cbn. apply base.NoDup_cons_2; [| exact NDS]. rewrite list_elem_of_In. intros Hk. apply in_app_or in Hk. destruct Hk as [Hk|Hk].
        + destruct sok' as [ks'|]; cbn in Hk; [| destruct Hk]. destruct Hk as [Hk|[]]. pose proof (FRESH3 _ KMK) as X. cbn in X. exact (X (eq_sym Hk)).
        + exact (proj2 (NEQS _ (in_or_app _ _ _ (or_intror Hk))) eq_refl). }

    apply sreach_ret. unfold presp_post. rewrite !(unsigned_lit (q + 80)) by lia.
    assert (COMMON : forall r err' pos', (err' = err \/ err' = 500)%Z -> (0 <= pos' <= 4)%Z ->
      rw_cells rsegs m4 (P + 440) (ctl9 err' hack pos' entp clen csz esp) ->
      (0 <= r <= 5)%Z -> ((r = 4 /\ pos' = POS_HEADERS /\ err' = err /\ 0 <= maj' /\ 0 <= min' /\ 0 <= sc' /\ Some km <> None) \/ (r <> 4 /\ pos' = pos /\ (err' = err \/ err' = 500)))%Z ->
      exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r0 cur' sc'0 maj'0 min'0 SA'0 slen'0 scap'0 err'0 pos'0 : Z) (sok'0 : option K) (sbs'0 : list byte),
        MS (mkR ra (wz (q + 80)) gp (wz 0x3b820) u0 u1 u2 s0 s1 (wz r) v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (ret_pc ra) fc None m4 (seg_rom rsegs)
        = MS (mkR ra (wz (q + 80)) gp (wz (al_tp L_)) t0 t1 t2 s0 s1 (wz r0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs)
        /\ mem_inv rsegs m' /\ stk rsegs m' lo (q + 80) /\ RENV rsegs AI m' B
        /\ (exists errv'0, rw_cells rsegs m' (al_errno L_) [C4 errv'0])
        /\ hpx AI (resp_W P) LBK (q + 80) m m'
        /\ RHEAP rsegs AI s3' LB3 m'
        /\ bsub (okb (Some km) A cap ++ okb sok'0 SA'0 scap'0 ++ LBK) LB3 /\ NoDup (map blk_id (okb (Some km) A cap ++ okb sok'0 SA'0 scap'0 ++ LBK))
        /\ p_scan m' P cur' /\ p_msg AI m' LB3 P A len cap (Some km) bs /\ p_rs m' P rm sc'0 /\ p_ver m' P isreq maj'0 min'0
        /\ p_smsgW m' LB3 P SA'0 slen'0 scap'0 sok'0 sbs'0 /\ p_ctl m' P err'0 hack pos'0 entp clen csz esp
        /\ (0 <= r0 <= 5)%Z /\ (cur <= cur' <= len)%Z
        /\ ((r0 = 4 /\ pos'0 = POS_HEADERS /\ err'0 = err /\ 0 <= maj'0 /\ 0 <= min'0 /\ 0 <= sc'0 /\ Some km <> None) \/ (r0 <> 4 /\ pos'0 = pos /\ (err'0 = err \/ err'0 = 500)))%Z).
    { intros r err' pos' HE' HP' CTL4 HR5 RES. do 15 eexists. exists r, cur1, sc', maj', min', SA', slen', scap', err', pos', sok', sbs'.
      split; [rewrite TPV; reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact HE4|]. split; [eexists; exact ERR4|].
      split; [exact HP14|]. split; [exact HR4|]. split; [exact BSUB4|]. split; [exact ND4|].
      split; [exact SC4|]. split; [split; [exact MBC4| split; [cbn; split; [exact (SUB3 _ KMK)| exact BLK4]| split; [lia| split; [unfold LMAX; lia| exact NULM]]]]|].
      split; [split; [exact RS4| lia]|]. split; [split; [eexists; exact VER4| lia]|].
      split; [split; [exact SMC4| split; [exact SOWN4| lia]]|]. split; [split; [unfold ctl9 in CTL4; exact CTL4| lia]|].
      split; [exact HR5|]. split; [lia|]. exact RES. }
    destruct RES4 as [(-> & -> & CTL4)|(NR3 & -> & CTL4)].
    - apply (COMMON 4 err 2); [left; reflexivity| lia| exact CTL4| lia| left; unfold POS_HEADERS; repeat split; first [lia| discriminate]].
    - apply (COMMON 3 500 pos); [right; reflexivity| lia| exact CTL4| lia| right; split; [lia| split; [reflexivity| right; reflexivity]]].
  Qed.
End W.
