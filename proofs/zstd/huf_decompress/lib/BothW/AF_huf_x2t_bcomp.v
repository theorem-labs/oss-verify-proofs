From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AFake0k_iface AProg_kit
     FsKit AF_fse_rd_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AH_huf_kit AH_huf_iface
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_tbl_iface3 AF_huf_x2t_bgeo AF_huf_x2t_bseg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_HufStats HufPure_HufStatsRT ZdHufStats.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Startup_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AHarness_bm AHarness_iface Stdio_kit AF_huf_x2t_hdefs AF_huf_x2t_bdefs
     AF_huf_x2t_bdok AF_huf_rstats_ok.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma x2c_shad_band : forall X n a, ablk X (X + n) -> 0 <= a < 2^47 -> ~ (X <= shad a < X + n).
Proof.
  intros X n a H Ha. pose proof (shad_in_band a Ha) as SB. unfold ablk in H. unfold KLS, AIMG_HI in *.
  pose proof atop_range as ATR. lia.
Qed.

Lemma x2c_shad8_disj : forall FF X n, FF mod 64 = 0 -> 0 <= FF -> FF + 64 <= 2^47 -> ablk X (X + n) ->
  X + n <= shad FF \/ shad FF + 8 <= X.
Proof.
  intros FF X n F64 F0 F47 H. pose proof (shad_in_band FF ltac:(lia)) as S1. pose proof (shad_in_band (FF + 63) ltac:(lia)) as S2.
  assert (E : shad (FF + 63) = shad FF + 7) by (rewrite !shad_div; Z.div_mod_to_equations; lia).
  unfold ablk in H. unfold KLS, AIMG_HI in *. pose proof atop_range. lia.
Qed.

Lemma x2c_shad_same : forall a x, 0 <= a -> 0 <= x -> shad a = shad x -> a / 8 = x / 8.
Proof. intros a x Ha Hx E. rewrite !shad_div in E. lia. Qed.

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Hypothesis SM0K : stack_malloc_0k_stmt AI fflag rng_fs 0.
Notation FB0 F := (mkABlock (ABFake 0) F 64).

Lemma x2c_fresh_not_client : forall LB SPV X n a,
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  ablk X (X + n) -> (forall b, In b LB -> X + n <= ab_addr b \/ ab_addr b + ab_size b <= X) ->
  ATOP <= SPV -> X <= a < X + n -> ~ aclient_addr CI LB SPV a.
Proof.
  intros LB SPV X n a LBH XH XD FS HA AC.
  pose proof (ablk_lin _ _ XH) as (XHa & XHb & XHc & XHd).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  destruct AC as [AC|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
  - lia.
  - pose proof (HCI iv Hiv). lia.
  - destruct (XD b Hb); lia.
  - assert (A47 : 0 <= a' < 2^47).
    { destruct Ha' as [H|[(iv & Hiv & Hr)|(cls & FA & fn & Hb & Hr)]].
      - lia.
      - pose proof (HCI iv Hiv). pose proof (HCI0 iv Hiv). unfold AIMG_HI in *. lia.
      - pose proof (LBH _ Hb) as BH. cbn in BH. pose proof (ablk_lin _ _ BH). lia. }
    exact (x2c_shad_band X n a' XH A47 HA).
Qed.

Lemma x2c_ff_not_client : forall LB SPV FF a,
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  FF mod 64 = 0 -> ablk FF (FF + 64) -> ATOP <= SPV ->
  (FF <= a < FF + 64 \/ shad FF <= a < shad FF + 8) -> ~ aclient_addr CI LB SPV a.
Proof.
  intros LB SPV FF a LBH FFD F64 FH FS HA AC.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof atop_range as ATR.
  assert (KA : AIMG_HI < KLS) by (unfold AIMG_HI, KLS; lia).
  assert (A47 : forall a', ((ATOP <= a' < 2^47) \/ in_ranges CI a' \/ in_fake LB a') -> 0 <= a' < 2^47).
  { intros a' [H|[(iv & Hiv & Hr)|(cls & FA & fn & Hb & Hr)]].
    - lia.
    - pose proof (HCI iv Hiv). pose proof (HCI0 iv Hiv). unfold AIMG_HI in *. lia.
    - pose proof (LBH _ Hb) as BH. cbn in BH. pose proof (ablk_lin _ _ BH). lia. }
  destruct HA as [HA|HA].
  - destruct AC as [AC|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    + lia.
    + pose proof (HCI iv Hiv). lia.
    + destruct (FFD b Hb); lia.
    + exact (x2c_shad_band FF 64 a' FH (A47 a' Ha') HA).
  - assert (SHI : exists x, FF <= x < FF + 64 /\ shad x = a).
    { exists (FF + 8 * (a - shad FF)). split; [lia|]. rewrite !shad_div in *. Z.div_mod_to_equations. lia. }
    destruct SHI as (x & Hx & <-).
    pose proof (shad_in_band x ltac:(lia)) as SB.
    destruct AC as [AC|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & E)]]].
    + unfold KLS in *. lia.
    + pose proof (HCI iv Hiv). unfold KLS, AIMG_HI in *. lia.
    + exact (x2c_shad_band _ _ x (LBH b Hb) ltac:(lia) Hr).
    + pose proof (A47 a' Ha') as B'.
      pose proof (x2c_shad_same a' x ltac:(lia) ltac:(lia) (eq_sym E)) as E8.
      assert (IN : FF <= a' < FF + 64) by (Z.div_mod_to_equations; lia).
      destruct Ha' as [H|[(iv & Hiv & Hr)|(cls & FA & fn & Hb & Hr)]].
      * lia.
      * pose proof (HCI iv Hiv). lia.
      * destruct (FFD _ Hb) as [D|D]; cbn in D; lia.
Qed.

Definition X2C_S3 : Z := 2147450880.

Lemma x2c_shad_div : forall a, shad a = ASHOFF + a / 8.
Proof. intros a. unfold shad. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma x2c_cs2 : forall w n j, Z.of_nat (cells_size [C4 w; CB n j]) = 4 + Z.of_nat n.
Proof. intros. cbn. lia. Qed.

Lemma x2c_dtu8 : forall m A w n j, rw_cells bsegs m A [C4 w; CB n j] ->
  u8arr bsegs m A (le4 w ++ j) /\ length j = n.
Proof.
  intros m A w n j ((WF & B) & W). cbn [cells_wf cell_wf] in WF. destruct WF as (_ & LJ & _).
  cbn [cells_bytes] in B. rewrite app_nil_r in B.
  split; [| exact LJ]. split; [exact B|].
  assert (E : Z.of_nat (cells_size [C4 w; CB n j]) = Z.of_nat (length (le4 w ++ j))) by (cbn; rewrite LJ; lia).
  rewrite <- E. exact W.
Qed.

Lemma x2c_le4_hd : forall mtl, 1 <= mtl <= 12 ->
  nth_error (le4 (Z_to_bv 64 (mtl * 16777217))) 0 = Some (Z_to_bv 8 mtl).
Proof.
  intros mtl HM. cbn [le4 Z_to_le_bytes nth_error]. rewrite unsigned_lit by lia. f_equal.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  Z.div_mod_to_equations. lia.
Qed.

Definition x2_frameB (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (m m3 : amem)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SPV lo FF W : Z) : Prop :=
  FF mod 64 = 0 /\ ablk FF (FF + 64) /\ FF + 64 <= ATOP /\ rng RNG FF 64 /\ rng RNG (shad FF) 8
  /\ (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF)
  /\ AHEAP AI L RNG st (FB0 FF :: LB) m3
  /\ magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (W + 624 <= a < W + 736)) m m3 /\ mem_inv bsegs m3
  /\ rw_cells bsegs m3 (SPV + -104) (X2BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
  /\ rw_cells bsegs m3 (Z.shiftr FF 3 + ASHOFF) X2BSH
  /\ stk bsegs m3 lo (SPB SPV - 16) /\ stk bsegs m3 (SPB SPV + 408) (SPV + -104).

Lemma x2_openB : forall (L : alayout) (RNG : footprint)
    (ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
    (SPV DT W S size flags lo mtl : Z) (pdt pw : aptr) (jdt : list byte) (Q : machine_state -> Prop),
  AHEAP AI L RNG st LB m -> (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  stk bsegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - HUF_RDT_STACK_A2 ->
  SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  1 <= mtl <= 12 -> In (HB pdt DT (DTABLE_BYTES mtl)) LB ->
  rw_cells bsegs m DT [C4 (Z_to_bv 64 (mtl * 16777217)); CB (Z.to_nat (4 * 2^mtl)) jdt] ->
  In (HB pw W 8704) LB ->
  (forall (FF : Z) (m3 : amem) (jA jB jC jT jD jE j3 : list byte) (hdw : Z) (y5 y6 y7 y28 y29 y30 y31 : word),
     x2_frameB L RNG st LB m m3 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF W ->
     hdw mod 256 = mtl -> 0 <= hdw < 2^32 -> hdw / 2^24 = mtl ->
     rw_cells bsegs m3 (SPB SPV - 16) [C8 (Z_to_bv 64 876); C8 (Z_to_bv 64 flags)] ->
     rw_cells bsegs m3 (SPB SPV) (X2BFRA0 FF DT W jA jB jC jT jD jE) ->
     rw_cells bsegs m3 FF (X2BFFHDR (fflag L 0 FF) j3) ->
     rw_cells bsegs m3 (W + 624) [CB 112 (repeat (Z_to_bv 8 0) 112)] ->
     evtF bsegs RNG Q
       (MS (mkR (Z_to_bv 64 0x82044) (Z_to_bv 64 (SPB SPV - 16)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPB SPV))
                (Z_to_bv 64 (W + 992)) (Z_to_bv 64 256) (Z_to_bv 64 (W + 624)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32))
                (Z_to_bv 64 S) (Z_to_bv 64 size) (Z_to_bv 64 (W + 1248))
                (Z_to_bv 64 S) (Z_to_bv 64 X2C_S3) (Z_to_bv 64 hdw) (Z_to_bv 64 size) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 W)
                (Z_to_bv 64 (W + 992)) (Z_to_bv 64 flags) (Z_to_bv 64 (W + 624)) (Z_to_bv 64 (FF + 32)) y28 y29 y30 y31)
           FR (Z_to_bv 64 AHUF_RSTATS) fc None m3 (seg_rom bsegs))) ->
  evtF bsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 S) (Z_to_bv 64 size) (Z_to_bv 64 W)
             (Z_to_bv 64 8704) (Z_to_bv 64 flags) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 AHUF_RDT_X2) fc None m (seg_rom bsegs)).
Proof.
  intros L RNG ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB
         SPV DT W S size flags lo mtl pdt pw jdt Q AH NOF LBH ST BOT LO SPT SP16 MI TP RSTK RI RFS HMTL HDT DTC HWB KC.
  pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (spb_props SPV SP16) as (SPAB & SPA32 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  assert (BB : forall b, In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP)
    by (intros b Hb; exact (AI_block_bounds AI _ _ _ _ _ b AH Hb)).
  pose proof SM0K as SMK. unfold stack_malloc_0k_stmt in SMK.
  unfold HUF_RDT_STACK_A2 in LO.
  assert (LOS : lo <= SPV - 528 - 4096 - 16) by lia.
  assert (LOC : ATOP <= lo) by lia.
  assert (SPK : SPV + 16 < KEND) by (unfold KEND; lia).
  assert (RSTK' : rng RNG lo (SPV - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
  destruct RTC as (C0 & GOT & RIC & REAL & SHB & SUA & _).
  pose proof (AI_relro AI _ _ _ _ _ AH) as REL.
  assert (GSU : rw_cells bsegs m AGOT_SUAR_R [C8 (Z_to_bv 64 X2B_SUAR)]).
  { unfold AGOT_SUAR_R. eapply relro_wordA; [exact REL| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]. }
  unfold AHUF_RDT_X2.
  eapply evtF_cut.
  { eapply x2_pro; first [exact ST| exact MI| exact GOT| exact SHB| exact GSU| exact SUA| exact SP16| exact LOS| exact LOC
                         | exact SPK| exact RSTK'| exact RI]. }
  cbv beta. intros ms' (m1 & jA & jB & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
  clear C0 GOT RIC REAL SHB SUA GSU.
  assert (AH1 : AHEAP AI L RNG st LB m1).
  { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
  assert (AP1 : aheap_pres CI LB SPV m m1).
  { eapply aheap_pres_stack_writes; [exact AH| exact BB| exact HCI| exact MU1| exact WM1| | exact LOC].
    constructor; [| constructor]. cbn. lia. }
  eapply evtF_cut.
  { eapply SMK; first [exact AH1| exact MI1| exact TP| exact RI| exact RFS| exact BOT
                       | apply fake0_lek_none; intros F n; exact (NOF F n)
                       | rewrite unsigned_lit by lia; exact STL1
                       | rewrite unsigned_lit by lia; unfold SM0K_STACK; lia
                       | rewrite unsigned_lit by lia; lia
                       | exact RSTK]. }
  intros ms' HP. unfold sm0k_post in HP.
  destruct HP as (FF & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & j0 & j1 & j2 & junk &
                  -> & MI2 & STL2 & AP2 & AH2 & F64 & FH & FC & FFC & SHF & RF & RSF).
  rewrite unsigned_lit in STL2, AP2 by lia.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd).
  assert (FFD : forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF).
  { intros b Hb. assert (NE : FB0 FF <> b) by (intro E; subst b; exact (NOF FF 64 Hb)).
    destruct (AI_blocks_disjoint AI _ _ _ _ _ (FB0 FF) b AH2 ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as [D|D];
      cbn in D; lia. }
  assert (FRB2 : rw_cells bsegs m2 (SPV + -104) (X2BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply aheap_pres_rw_cells; [exact AP2| exact FRB1|]. left; left. cbn. lia. }
  assert (FRA2 : rw_cells bsegs m2 (SPB SPV) [CB 352 jA; C8 (Z_to_bv 64 W); CB 48 jB]).
  { eapply aheap_pres_rw_cells; [exact AP2| exact FRA1|]. left; left. cbn. lia. }
  assert (STG2 : stk bsegs m2 (SPB SPV + 408) (SPV + -104)).
  { eapply aheap_pres_stk; [exact AP2| exact STG1| lia| lia]. }
  assert (APT2 : aheap_pres CI LB SPV m m2).
  { eapply aheap_pres_trans; [exact AP1|]. eapply aheap_pres_weaken; [exact AP2| lia| intros b Hb; exact Hb]. }
  clear FRB1 FRA1 STG1.
  destruct (hb_unpoisoned AI L RNG st (FB0 FF :: LB) m2 pdt DT (DTABLE_BYTES mtl) AH2 (or_intror HDT))
    as (UDT & DT16 & _ & ABD & DTA & RDT & RSDT & _).
  destruct (hb_unpoisoned AI L RNG st (FB0 FF :: LB) m2 pw W 8704 AH2 (or_intror HWB))
    as (_ & W16 & _ & ABW & WA & RW & RSW & _).
  pose proof (x2b_dtb_range mtl HMTL) as DTBR. unfold DTABLE_BYTES, HufHarness.DT_BYTES in *.
  assert (DTC2 : rw_cells bsegs m2 DT [C4 (Z_to_bv 64 (mtl * 16777217)); CB (Z.to_nat (4 * 2^mtl)) jdt]).
  { eapply aheap_pres_rw_cells; [exact APT2| exact DTC|]. rewrite x2c_cs2, Z2Nat.id by lia.
    eapply cr_block; [exact HDT| cbn [ab_addr ab_size]; lia| cbn [ab_addr ab_size]; lia]. }
  destruct (x2c_dtu8 _ _ _ _ _ DTC2) as (DTU & DTL).
  pose proof (ablk_lin _ _ ABD) as (ABDa & ABDb & ABDc & ABDd).
  pose proof (ablk_lin _ _ ABW) as (ABWa & ABWb & ABWc & ABWd).
  pose proof (FFD _ HDT) as DF. pose proof (FFD _ HWB) as WF. cbn in DF, WF.
  pose proof (AI_relro AI _ _ _ _ _ AH2) as REL2.
  assert (GPC : rw_cells bsegs m2 X2B_GOTPC [C8 (Z_to_bv 64 X2B_ENTRY)]).
  { unfold X2B_GOTPC. eapply relro_wordA; [exact REL2| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]. }
  assert (RP : ret_pc (Z_to_bv 64 0x81ecc) = Z_to_bv 64 0x81ecc) by (apply ret_pc_even; lia).
  rewrite RP.
  eapply evtF_cut; [| cbv beta; intros ms' HQ; exact HQ].
  eapply x2_hdr1 with (Q := fun ms => evtF bsegs RNG Q ms) (FLG := fflag L 0 FF) (DT := DT) (WK := W) (wksz := 8704)
    (SRC := S) (n := size) (mtl := mtl) (dtb := le4 (Z_to_bv 64 (mtl * 16777217)) ++ jdt)
    (j0 := j0) (j1 := j1) (j2 := j2) (junk := junk) (jA := jA) (jB := jB).
  all: try lazymatch goal with
       | |- zlen _ = _ => rewrite length_app, DTL; change (length (le4 _)) with 4%nat; rewrite Nat2Z.inj_add, Z2Nat.id by lia; lia
       | |- nth_error _ 0 = _ => rewrite nth_error_app1 by (change (length (le4 _)) with 4%nat; lia); exact (x2c_le4_hd mtl HMTL)
       | |- rng _ (shad _) 1 => eapply rng_sub'; [exact RSDT| unfold shlen; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia]
       | |- forall _, _ => idtac
       | |- _ => first [exact FRA2| exact STL2| exact FFC| exact SHF| exact GPC| exact MI2| exact FH| exact FC| exact F64| exact RF
                       | exact RSF| exact DTU| exact UDT| exact ABD| exact RDT| exact SP16| exact LOS| exact LOC| exact SPK| exact RSTK'
                       | exact RI| exact HMTL| unfold KEND, AIMG_HI in *; lia]
       end.
  { intros m3 j3 y12 Hc. lia. }
  intros m3 j3 jA3 jB3 jC jT jD jE hdw H2124 HHM HHR HF4 MU3 WM3 MI3 FRA3 STL3 FFH3 SH3 DTB3.
  cbv beta.
  assert (SH8 : shad FF = Z.shiftr FF 3 + ASHOFF) by (unfold shad; lia).
  assert (OUT3 : forall a, aclient_addr CI LB SPV a ->
            outside [(SPB SPV, SPB SPV + 408); (FF, FF + 24); (Z.shiftr FF 3 + ASHOFF, Z.shiftr FF 3 + ASHOFF + 8)] a).
  { intros a Ha. cbn [outside]. split; [|split; [|split; [|exact I]]].
    - intros HIN. exact (stack_not_client CI LB SPV (SPB SPV) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha).
    - intros HIN. exact (x2c_ff_not_client LB SPV FF a LBH FFD F64 FH ltac:(lia) ltac:(left; lia) Ha).
    - rewrite <- SH8. intros HIN. exact (x2c_ff_not_client LB SPV FF a LBH FFD F64 FH ltac:(lia) ltac:(right; lia) Ha). }
  assert (AP3 : aheap_pres CI LB SPV m2 m3) by (eapply aheap_pres_of_munch; [exact MU3| exact WM3| exact OUT3]).
  assert (APT : aheap_pres CI LB SPV m m3) by (eapply aheap_pres_trans; [exact APT2| exact AP3]).
  assert (MG3 : magree bsegs (fun a => outside [(SPB SPV, SPB SPV + 408); (FF, FF + 24);
                                              (Z.shiftr FF 3 + ASHOFF, Z.shiftr FF 3 + ASHOFF + 8)] a) m2 m3)
    by (apply magree_of_munch; [exact MU3| exact WM3]).
  assert (AH3 : AHEAP AI L RNG st (FB0 FF :: LB) m3).
  { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    - left; left. cbn. lia.
    - right; left. exists (FB0 FF). split; [left; reflexivity| cbn; lia].
    - right; right. right; right. exists 0, FF, 64. split; [left; reflexivity|]. cbn [fst snd].
      unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  destruct (hb_unpoisoned AI L RNG st (FB0 FF :: LB) m3 pw W 8704 AH3 (or_intror HWB))
    as (UW3 & _ & _ & _ & _ & _ & _ & WRW3).
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH3 (or_intror HWB))
    as (_ & _ & _ & _ & _ & _ & _ & (RLO & RHI & RL0 & RH0 & RLW & RHW & RSR & WSR)).
  destruct (fse_rt_of_aheap AI _ _ _ _ _ AH3) as (GOT3 & RIC3 & REAL3 & SHB3 & _ & INI3 & LAY3).
  assert (WR3 : wr_at bsegs m3 (W + 624) 112) by (eapply wr_at_sub; [exact WRW3|..]; lia).
  assert (EXJ : exists bs, length bs = Z.to_nat 112 /\ rw_cells bsegs m3 (W + 624) [CB (Z.to_nat 112) bs]).
  { eapply Shadow.rw_cells_of_wr_at; [exact WR3| apply no_image_asan; unfold AIMG_HI in *; lia| lia]. }
  destruct EXJ as (jm & JML & JMC).
  set (RL2 := (W + 624) - (W + 624) mod 64).
  assert (RL2r : W + 561 <= RL2 <= W + 624 /\ RL2 mod 64 = 0) by (subst RL2; Z.div_mod_to_equations; lia).
  assert (E24 : shad (RL2 + 192) - shad RL2 = 24) by (rewrite !x2c_shad_div; Z.div_mod_to_equations; lia).
  assert (WS2 : wr_at bsegs m3 (shad RL2) 24).
  { eapply wr_at_sub; [exact WSR|..]; unfold shlen; rewrite ?Z.shiftr_div_pow2 by lia; rewrite ?x2c_shad_div;
      Z.div_mod_to_equations; lia. }
  assert (RS2 : rng RNG (shad RL2) 24).
  { eapply rng_sub'; [exact RSR|]. unfold shlen; rewrite ?Z.shiftr_div_pow2 by lia; rewrite ?x2c_shad_div;
      Z.div_mod_to_equations; lia. }
  eapply evtF_cut.
  { eapply (amemset_specZ (W + 624) 112 0 (SPB SPV)) with (RLO2 := RL2) (RHI2 := RL2 + 192) (junk := jm) (lo := lo).
    all: first [ lazymatch goal with
                 | |- evtF _ _ _ _ => fail
                 | |- wr_at _ _ (shad _) _ => rewrite E24; exact WS2
                 | |- rng _ (shad _) _ => rewrite E24; exact RS2
                 | |- rng _ _ _ => first [exact RI| eapply rng_sub'; [exact RW| lia]| eapply rng_sub'; [exact RSTK| lia]]
                 | |- rw_cells _ _ _ _ => first [exact JMC| exact GOT3| exact RIC3| exact SHB3| exact INI3| exact LAY3| exact REAL3]
                 | |- app_blk _ _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABW| lia| lia]| lia]
                 | |- unpoisoned _ _ _ => eapply unpoisoned_sub; [exact UW3| lia| lia]
                 | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
                 | |- _ => first [exact MI3| exact STL3| exact GOT3| exact RIC3| exact SHB3| exact INI3| exact LAY3| exact REAL3
                                 | exact RI| unfold Shadow.KHIGH, KEND, AIMG_HI in *; lia]
                 end | idtac ]. }
  intros ms' HP. unfold amemsetZ_post in HP.
  destruct HP as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m4 & -> & MU4 & WM4 & MI4 & STL4 & ZC4).
  rewrite ret_pc_even by (first [lia| reflexivity]).
  pose proof (shad_in_band FF ltac:(lia)) as SBF.
  assert (SHL : Z.shiftr FF 3 + ASHOFF + 8 <= SPB SPV - 2208) by (rewrite <- SH8; unfold KLS in *; lia).
  assert (SHW : Z.shiftr FF 3 + ASHOFF + 8 <= W \/ W + 8704 <= Z.shiftr FF 3 + ASHOFF).
  { rewrite <- SH8. destruct (x2c_shad8_disj FF W 8704 F64 ltac:(lia) ltac:(lia) ABW); lia. }
  assert (FRA4 : rw_cells bsegs m4 (SPB SPV) (X2BFRA0 FF DT W jA3 jB3 jC jT jD jE)).
  { eapply rw_cells_magree; [eapply magree_of_munch; [exact MU4| exact WM4]| exact FRA3|].
    intros a Ha. unfold X2BFRA0 in Ha. cbn in Ha. cbn [outside]. lia. }
  eapply evtF_cut; [| cbv beta; intros ms' HQ; exact HQ].
  eapply x2_hdr2 with (Q := fun ms => evtF bsegs RNG Q ms) (FF := FF) (DT := DT) (WK := W) (SRC := S) (n := size)
    (hdw := hdw) (mtl := mtl) (jA := jA3) (jB := jB3) (jC := jC) (jT := jT) (jD := jD) (jE := jE).
  all: try first [exact HMTL| exact STL4| exact MI4| exact FRA4| exact SP16| exact SPK| exact LOS| exact LOC| exact RSTK'| exact RI].
  intros m5 MU5 WM5 MI5 STL5 FL5 FRA5.
  assert (FRB5 : rw_cells bsegs m5 (SPV + -104) (X2BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_magree; [eapply magree_of_munch; [exact MU5| exact WM5]| |].
    { eapply rw_cells_magree; [eapply magree_of_munch; [exact MU4| exact WM4]| |].
      { eapply rw_cells_magree; [exact MG3| exact FRB2|]. intros a Ha. unfold X2BSAVED in Ha. cbn in Ha. cbn [outside]. lia. }
      intros a Ha. unfold X2BSAVED in Ha. cbn in Ha. cbn [outside]. lia. }
    intros a Ha. unfold X2BSAVED in Ha. cbn in Ha. cbn [outside]. lia. }
  assert (SH5 : rw_cells bsegs m5 (Z.shiftr FF 3 + ASHOFF) X2BSH).
  { eapply rw_cells_magree; [eapply magree_of_munch; [exact MU5| exact WM5]| |].
    { eapply rw_cells_magree; [eapply magree_of_munch; [exact MU4| exact WM4]| exact SH3|].
      intros a Ha. unfold X2BSH in Ha. cbn in Ha. cbn [outside]. unfold ASHOFF in *. lia. }
    intros a Ha. unfold X2BSH in Ha. cbn in Ha. cbn [outside]. unfold ASHOFF in *. lia. }
  assert (FFH5 : rw_cells bsegs m5 FF (X2BFFHDR (fflag L 0 FF) j3)).
  { eapply rw_cells_magree; [eapply magree_of_munch; [exact MU5| exact WM5]| |].
    { eapply rw_cells_magree; [eapply magree_of_munch; [exact MU4| exact WM4]| exact FFH3|].
      intros a Ha. unfold X2BFFHDR in Ha. cbn in Ha. cbn [outside]. lia. }
    intros a Ha. unfold X2BFFHDR in Ha. cbn in Ha. cbn [outside]. lia. }
  assert (ZC5 : rw_cells bsegs m5 (W + 624) [CB 112 (repeat (Z_to_bv 8 0) 112)]).
  { eapply rw_cells_magree; [eapply magree_of_munch; [exact MU5| exact WM5]| exact ZC4|].
    intros a Ha. cbn in Ha. cbn [outside]. lia. }
  assert (STG5 : stk bsegs m5 (SPB SPV + 408) (SPV + -104)).
  { eapply stk_magree; [eapply magree_of_munch; [exact MU5| exact WM5]| |].
    { eapply stk_magree; [eapply magree_of_munch; [exact MU4| exact WM4]| |].
      { eapply stk_magree; [exact MG3| exact STG2|]. intros a Ha. cbn [outside]. lia. }
      intros a Ha. cbn [outside]. lia. }
    intros a Ha. cbn [outside]. lia. }
  assert (MG5 : magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (W + 624 <= a < W + 736)) m m5).
  { assert (M3 : magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (W + 624 <= a < W + 736)) m m3)
      by (intros a Ha [HP _]; exact (APT a Ha HP)).
    eapply (magree_munch_step _ m m4 m5); [eapply (magree_munch_step _ m m3 m4); [exact M3| exact MU4| exact WM4|]| exact MU5| exact WM5|].
    - intros a [HP HN]. cbn [outside]. split; [|split; [lia| exact I]].
      intros HIN. exact (stack_not_client CI LB SPV (SPB SPV - 2208) a HCI HCI0 LBH ltac:(lia) ltac:(lia) HP).
    - intros a [HP _]. cbn [outside]. split; [|exact I].
      intros HIN. exact (stack_not_client CI LB SPV (SPB SPV - 16) a HCI HCI0 LBH ltac:(lia) ltac:(lia) HP). }
  assert (AH5 : AHEAP AI L RNG st (FB0 FF :: LB) m5).
  { eapply (AI_frame AI); [| exact MU5| exact WM5|].
    { eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|].
      constructor; [|constructor; [|constructor]].
      - left; left. cbn. lia.
      - right; left. exists (HB pw W 8704). split; [right; exact HWB| cbn; lia]. }
    constructor; [|constructor]. left; left. cbn. lia. }
  assert (HDV : hdw / 2^24 = mtl).
  { rewrite firstn_app, length_le4 in HF4. cbn [Nat.sub firstn] in HF4. rewrite app_nil_r in HF4.
    rewrite firstn_all2 in HF4 by (rewrite length_le4; lia).
    apply (f_equal (fun l => bv_unsigned (le_bytes_to_word l))) in HF4. rewrite !le_bytes_to_word_le4 in HF4.
    rewrite !unsigned_lit in HF4 by lia. rewrite !(Z.mod_small _ (2^32)) in HF4 by lia.
    rewrite <- HF4. change (2^24) with 16777216. Z.div_mod_to_equations. lia. }
  cbv beta. eapply KC; [| exact HHM| exact HHR| exact HDV| exact FL5| exact FRA5| exact FFH5| exact ZC5].
  unfold x2_frameB. split; [exact F64|]. split; [exact FH|]. split; [exact FC|]. split; [exact RF|]. split; [exact RSF|].
  split; [exact FFD|]. split; [exact AH5|]. split; [exact MG5|]. split; [exact MI5|]. split; [exact FRB5|].
  split; [exact SH5|]. split; [exact STL5|]. exact STG5.
Qed.

Lemma x2c_disj_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> disjoint_from W A' n'.
Proof.
  induction W as [|[l h] W IH]; cbn; [auto|]. intros A n A' n' [H1 H2] HA HB. split; [lia| exact (IH A n A' n' H2 HA HB)].
Qed.

Lemma x2c_pow_le : forall a b, b <= a -> 0 <= a -> 2^b <= 2^a.
Proof.
  intros a b H Ha. destruct (Z_lt_le_dec b 0) as [N|N].
  - rewrite (Z.pow_neg_r 2 b N). apply Z.pow_nonneg; lia.
  - apply Z.pow_le_mono_r; lia.
Qed.

Lemma x2c_dt_okA_transport : forall W m m' DT mtl, huf_dt_okA m DT mtl -> munch W m m' -> 1 <= mtl <= 12 ->
  disjoint_from W DT (DTABLE_BYTES mtl) -> huf_dt_okA m' DT mtl.
Proof.
  intros W m m' DT mtl (tt & tl & H4 & HC) MU HM DJ. unfold DTABLE_BYTES, HufHarness.DT_BYTES in DJ.
  pose proof (Z.pow_pos_nonneg 2 mtl ltac:(lia) ltac:(lia)) as P0.
  exists tt, tl. split.
  { eapply bytes_at_transport; [exact H4| exact MU|]. eapply x2c_disj_sub; [exact DJ|..]; cbn; lia. }
  destruct HC as [(E & cells & CL & OK & TL & BA)|(E & cells & CL & OK & TL & BA)]; [left|right];
    (split; [exact E|]); exists cells; (split; [exact CL|]); (split; [exact OK|]); (split; [exact TL|]);
    (eapply bytes_at_transport; [exact BA| exact MU|]; eapply x2c_disj_sub; [exact DJ| lia|]).
  - lazymatch goal with |- context [length (firstn ?k ?l)] => pose proof (firstn_le_length k l) as FL end.
    pose proof (x2c_pow_le (mtl + 1) tl TL ltac:(lia)) as PT. rewrite Z.pow_add_r in PT by lia. change (2^1) with 2 in PT.
    pose proof (Z.pow_nonneg 2 tl ltac:(lia)) as PN. lia.
  - lazymatch goal with |- context [length (firstn ?k ?l)] => pose proof (firstn_le_length k l) as FL end.
    pose proof (x2c_pow_le mtl tl TL ltac:(lia)) as PT.
    pose proof (Z.pow_nonneg 2 tl ltac:(lia)) as PN. lia.
Qed.

Lemma x2_closeB : forall (L : alayout) (RNG : footprint)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m m4 : amem) (st : astate) (LB : list ablock) (SPV DT W mtl lo FF rv : Z) (pdt : aptr) (j0 : word)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  AHEAP AI L RNG st (FB0 FF :: LB) m4 ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (DT <= a < DT + DTABLE_BYTES mtl) /\ ~ (W <= a < W + 8704)) m m4 ->
  mem_inv bsegs m4 ->
  rw_cells bsegs m4 (Z.shiftr FF 3 + ASHOFF) X2BSH ->
  rw_cells bsegs m4 FF [C8 j0] -> rw_cells bsegs m4 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))] ->
  rw_cells bsegs m4 (SPV + -104) (X2BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells bsegs m4 (SPB SPV + 168) [C8 (Z_to_bv 64 (Z.shiftr FF 3 + ASHOFF)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] ->
  stk bsegs m4 lo (SPB SPV + 168) -> stk bsegs m4 (SPB SPV + 192) (SPV + -104) ->
  ATOP + 4096 <= lo -> lo <= SPV - HUF_RDT_STACK_A2 -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
  1 <= mtl <= 12 -> In (HB pdt DT (DTABLE_BYTES mtl)) LB ->
  0 <= rv < 2^64 -> (rv < 2^64 - 119 -> huf_dt_okA m4 DT mtl) ->
  evtF bsegs RNG (huf_rdt_postA AI huf_dt_okA L RNG ra (Z_to_bv 64 SPV) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB
                    DT W mtl lo m)
    (MS (mkR x1 (Z_to_bv 64 (SPB SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPB SPV)) (Z_to_bv 64 rv)
             x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 (X2B_ENTRY + 3732)) fc None m4 (seg_rom bsegs)).
Proof.
  intros L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m4 st LB SPV DT W mtl lo FF rv pdt j0
         x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         AH LBH F64 FH FC RF RSF FFD MG MI SHF FF0 FF56 FRB FRA STL STG BOT LO SPT SP16 RSTK RI HMTL HDT HR HOK.
  pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (spb_props SPV SP16) as (SPAB & SPA32 & _).
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd).
  unfold HUF_RDT_STACK_A2 in LO.
  assert (LOS : lo <= SPV - 528 - 4096 - 16) by lia.
  assert (LOC : ATOP <= lo) by lia.
  assert (SPK : SPV + 16 < KEND) by (unfold KEND; lia).
  assert (RSTK' : rng RNG lo (SPV - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
  destruct (FFLAG L RNG st (FB0 FF :: LB) m4 0 FF 64 AH ltac:(left; reflexivity)) as (FLC & RG & GH & GC & GD & GCI).
  assert (GF : fflag L 0 FF + 1 <= FF \/ FF + 64 <= fflag L 0 FF)
    by (destruct (GD (FB0 FF) ltac:(left; reflexivity)) as [D|D]; cbn in D; lia).
  assert (GLB : forall b, In b LB -> fflag L 0 FF + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L 0 FF)
    by (intros b Hb; exact (GD b ltac:(right; exact Hb))).
  pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd).
  assert (SH8 : shad FF = Z.shiftr FF 3 + ASHOFF) by (unfold shad; lia).
  pose proof SH8 as SH8L. unfold ASHOFF in SH8L.
  unfold X2B_ENTRY.
  eapply evtF_cut.
  { eapply x2_epi with (FLG := fflag L 0 FF); first [exact SHF| exact FF0| exact FF56| exact FLC| exact FRB| exact FRA
       | exact STL| exact STG| exact MI| exact FH| exact FC| exact F64| exact GH| exact GC| exact GF| exact RF| exact RSF
       | exact RG| exact HR| exact SP16| exact SPK| exact LOS| exact LOC| exact RSTK'| exact RI]. }
  cbv beta. intros ms' (mp & m' & x11' & x12' & x13' & -> & MU1 & WM1 & MIp & MU2 & WM2 & MI' & ST' & FL0).
  assert (AHp : AHEAP AI L RNG st (FB0 FF :: LB) mp).
  { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|].
    constructor; [|constructor; [|constructor]].
    - right; right. right; right. exists 0, FF, 64. split; [left; reflexivity|]. cbn [fst snd].
      unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
    - right; left. exists (FB0 FF). split; [left; reflexivity| cbn; lia]. }
  assert (AH' : AHEAP AI L RNG st LB m').
  { pose proof (FREL L RNG st LB mp 0 FF 64 AHp) as AR.
    eapply aheap_eqA; [exact AR|]. apply mem_eq_singleA; [lia| lia| exact MU2|].
    apply byte_of_c1A in FL0; [exact FL0| unfold AIMG_HI in *; lia]. }
  assert (OUTW : forall a, (aclient_addr CI LB SPV a /\ ~ (DT <= a < DT + DTABLE_BYTES mtl) /\ ~ (W <= a < W + 8704)) ->
            outside [(Z.shiftr FF 3 + ASHOFF, Z.shiftr FF 3 + ASHOFF + 8); (FF, FF + 8)] a
            /\ outside [(fflag L 0 FF, fflag L 0 FF + 1)] a).
  { intros a (Ha & _ & _). cbn [outside]. rewrite <- SH8. split; [split; [|split; [|exact I]]| split; [|exact I]].
    - intros HIN. exact (x2c_ff_not_client LB SPV FF a LBH FFD F64 FH ltac:(lia) ltac:(right; lia) Ha).
    - intros HIN. exact (x2c_ff_not_client LB SPV FF a LBH FFD F64 FH ltac:(lia) ltac:(left; lia) Ha).
    - intros HIN. exact (x2c_fresh_not_client LB SPV (fflag L 0 FF) 1 a LBH GH GLB ltac:(lia) ltac:(lia) Ha). }
  assert (DTH : ablk DT (DT + DTABLE_BYTES mtl)) by (exact (LBH _ HDT)).
  pose proof (x2c_shad8_disj FF DT (DTABLE_BYTES mtl) F64 ltac:(lia) ltac:(lia) DTH) as DS.
  pose proof (FFD _ HDT) as DF. pose proof (GLB _ HDT) as DG. cbn in DF, DG.
  apply evtF_done. unfold huf_rdt_postA.
  exists x5, x6, x7, x11', x12', x13', x14, x15, x16, x17, x28, x29, x30, x31, rv, m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [rewrite unsigned_lit by lia; exact ST'|].
  split.
  { rewrite unsigned_lit by lia.
    eapply magree_munch_step; [eapply magree_munch_step; [exact MG| exact MU1| exact WM1|] | exact MU2| exact WM2|].
    - intros a Ha. exact (proj1 (OUTW a Ha)).
    - intros a Ha. exact (proj2 (OUTW a Ha)). }
  split; [exact AH'|]. split; [exact HR|].
  intros HE. specialize (HOK HE).
  eapply x2c_dt_okA_transport; [eapply x2c_dt_okA_transport; [exact HOK| exact MU1| exact HMTL|] | exact MU2| exact HMTL|].
  - cbn [disjoint_from]. rewrite <- SH8L. repeat split; lia.
  - cbn [disjoint_from]. repeat split; lia.
Qed.

Definition x2_okB (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (m m5 : amem)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SPV lo FF W DT mtl hdw r tl nbs : Z) (hw rank : list Z) (j0 : word) : Prop :=
  x2B_hyps RNG SPV (SPB SPV) lo DT W 8704 FF mtl
  /\ unpoisoned m5 DT (DT + 4 * (1 + 2 ^ mtl)) /\ unpoisoned m5 W (W + 8704) /\ x2hb_art m5
  /\ 0 <= r < 2^32 /\ hdw mod 256 = mtl /\ 0 <= hdw < 2^32 /\ hdw / 2^24 = mtl
  /\ huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl /\ 2 <= nbs <= 256 /\ zlen hw = 256 /\ Forall isbyte hw
  /\ zlen rank = 13 /\ tl <= mtl
  /\ (exists (dt rs0 : list Z) (syb : list byte) (rv : list Z)
        (k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k224 k232 k240 k248 k256 k264
         k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 : word),
        XBB m5 SPV (SPB SPV) lo DT W 8704 FF mtl nbs hw rank k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136
          k144 k152 k160 k192 (Z_to_bv 64 tl) k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368
          k376 k384 k392 dt rs0 syb rv m5)
  /\ AHEAP AI L RNG st (FB0 FF :: LB) m5
  /\ (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF)
  /\ rng RNG (shad FF) 8
  /\ magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (DT <= a < DT + DTABLE_BYTES mtl) /\ ~ (W <= a < W + 8704)) m m5
  /\ rw_cells bsegs m5 (Z.shiftr FF 3 + ASHOFF) X2BSH
  /\ rw_cells bsegs m5 FF [C8 j0] /\ rw_cells bsegs m5 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))]
  /\ rw_cells bsegs m5 (SPV + -104) (X2BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
  /\ stk bsegs m5 (SPB SPV + 408) (SPV + -104).

Definition x2_postB (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (m m1 : amem)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SPV lo FF W DT mtl hdw r : Z) (src : list Z)
    (jA jB jC jT jD jE : list byte) (j0 : word) (dtb : list byte) : Prop :=
  FF mod 64 = 0 /\ ablk FF (FF + 64) /\ FF + 64 <= ATOP /\ rng RNG FF 64 /\ rng RNG (shad FF) 8
  /\ (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF)
  /\ AHEAP AI L RNG st (FB0 FF :: LB) m1 /\ mem_inv bsegs m1
  /\ magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (W <= a < W + 8704)) m m1
  /\ stk bsegs m1 lo (SPB SPV - 16) /\ stk bsegs m1 (SPB SPV + 408) (SPV + -104)
  /\ rw_cells bsegs m1 (SPB SPV) (X2BFRA0 FF DT W jA jB jC jT jD jE)
  /\ (exists w1 w2 : word, rw_cells bsegs m1 (SPB SPV - 16) [C8 w1; C8 w2])
  /\ rw_cells bsegs m1 (SPV + -104) (X2BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
  /\ rw_cells bsegs m1 (Z.shiftr FF 3 + ASHOFF) X2BSH
  /\ rw_cells bsegs m1 FF [C8 j0] /\ rw_cells bsegs m1 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))]
  /\ u8arr bsegs m1 DT dtb /\ zlen dtb = 4 * (1 + 2 ^ mtl)
  /\ rw_cells bsegs m1 (W + 676) [CB 60 (repeat (Z_to_bv 8 0) 60)]
  /\ hdw mod 256 = mtl /\ 0 <= hdw < 2^32 /\ hdw / 2^24 = mtl
  /\ 0 <= r < 2^64
  /\ match read_stats src with
     | Ok h => r = hs_ret h
               /\ (exists jrest, u8arr bsegs m1 (W + 992) (map (Z_to_bv 8) (hs_weights h) ++ jrest)
                                 /\ zlen jrest = 256 - hs_nbSymbols h)
               /\ u32arr bsegs m1 (W + 624) (map (Z_to_bv 64) (hs_rank h))
               /\ rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 (hs_nbSymbols h))]
               /\ rw_cells bsegs m1 (FF + 32) [C4 (Z_to_bv 64 (hs_tableLog h))]
     | Err e => r = 2^64 - e /\ 0 < e < 120
     | Ub | NoFuel => False
     end.

Lemma x2k_rwc_eq : forall m A cs1 cs2, rw_cells bsegs m A cs1 -> cells_bytes cs1 = cells_bytes cs2 ->
  cells_size cs1 = cells_size cs2 -> cells_wf cs2 -> rw_cells bsegs m A cs2.
Proof.
  intros m A cs1 cs2 [[_ HB] HW] EB ES WF. split; [split; [exact WF|]|].
  - rewrite <- EB. exact HB.
  - rewrite <- ES. exact HW.
Qed.

Lemma x2k_split8 : forall (j : list byte) n, length j = (8 + n)%nat -> exists w r, j = le8 w ++ r /\ length r = n.
Proof.
  intros j n HL. exists (le_bytes_to_word (firstn 8 j)), (skipn 8 j).
  rewrite Shadow.le8_of_bytes by (rewrite length_firstn; lia).
  split; [symmetry; apply firstn_skipn| rewrite length_skipn; lia].
Qed.

Lemma x2k_last8 : forall (j : list byte), length j = 8%nat -> exists w, j = le8 w.
Proof. intros j HL. exists (le_bytes_to_word j). rewrite Shadow.le8_of_bytes by exact HL. reflexivity. Qed.

Ltac x2k_chop H :=
  lazymatch type of H with
  | length ?j = 8%nat => let E := fresh "E" in destruct (x2k_last8 j H) as (?w & E); subst j
  | length ?j = ?n =>
      let E := fresh "E" in let L := fresh "L" in let r := fresh "r" in
      destruct (x2k_split8 j (n - 8) H) as (?w & r & E & L); subst j; cbn in L; x2k_chop L
  end.

Lemma x2k_frame : forall m A FF DT W jA jB jC wT jD jE,
  rw_cells bsegs m A (X2BFRA1 FF DT W jA jB jC wT jD jE) ->
  exists k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k224 k232 k240 k248 k256 k264
         k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 : word,
    rw_cells bsegs m A (X2BF FF DT W k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 wT
      k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392).
Proof.
  intros m A FF DT W jA jB jC wT jD jE H.
  pose proof H as [[WF _] _]. unfold X2BFRA1 in WF. cbn [cells_wf cell_wf] in WF.
  destruct WF as (LA & _ & LBb & _ & _ & _ & LC & _ & _ & _ & LD & _ & LE & _).
  x2k_chop LA. x2k_chop LBb. x2k_chop LC. x2k_chop LD. x2k_chop LE.
  do 42 eexists. eapply x2k_rwc_eq; [exact H| | reflexivity | cbn; tauto].
  unfold X2BFRA1, X2BF. cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma x2k_u32_of_u8 : forall m A rv, u8arr bsegs m A (u32s (map (Z_to_bv 64) rv)) -> u32arr bsegs m A (map (Z_to_bv 64) rv).
Proof. intros m A rv [HB HW]. split; [exact HB|]. rewrite u32s_length, Nat2Z.inj_mul in HW. exact HW. Qed.

Lemma x2k_chunk4 : forall n (bs : list byte), length bs = (4 * n)%nat ->
  exists rv, length rv = n /\ Forall (fun v => 0 <= v < 2^32) rv /\ u32s (map (Z_to_bv 64) rv) = bs.
Proof.
  induction n as [|n IH]; intros bs HL.
  - destruct bs; [|cbn in HL; lia]. exists []. split; [reflexivity| split; [constructor| reflexivity]].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 bs]]]]; cbn [length] in HL; try lia.
    destruct (IH bs ltac:(lia)) as (rv & RL & RF & RE).
    set (v := bv_unsigned (le_bytes_to_word [b0; b1; b2; b3]) mod 2^32).
    assert (VR : 0 <= v < 2^32) by (subst v; apply Z.mod_pos_bound; lia).
    exists (v :: rv). split; [cbn; lia|]. split; [constructor; [exact VR| exact RF]|].
    cbn [map u32s]. rewrite RE. change (b0 :: b1 :: b2 :: b3 :: bs) with ([b0; b1; b2; b3] ++ bs). f_equal.
    transitivity (le4 (le_bytes_to_word [b0; b1; b2; b3])); [| apply ABytes.le4_of_bytes; reflexivity].
    unfold le4. rewrite unsigned_lit by lia. subst v. apply Z_to_le_bytes_mod. lia.
Qed.

Lemma x2k_rwc_tr : forall a b m1 m5 A cs, munch [(a, b)] m1 m5 -> wmono bsegs m1 m5 -> rw_cells bsegs m1 A cs ->
  (A + Z.of_nat (cells_size cs) <= a \/ b <= A) -> rw_cells bsegs m5 A cs.
Proof.
  intros a b m1 m5 A cs MU WM H D. eapply rw_cells_magree; [eapply magree_of_munch; [exact MU| exact WM]| exact H|].
  intros x Hx. cbn [outside]. split; [lia| exact I].
Qed.

Lemma x2k_stk_tr : forall a b m1 m5 lo hi, munch [(a, b)] m1 m5 -> wmono bsegs m1 m5 -> stk bsegs m1 lo hi ->
  (hi <= a \/ b <= lo) -> stk bsegs m5 lo hi.
Proof.
  intros a b m1 m5 lo hi MU WM H D. eapply stk_magree; [eapply magree_of_munch; [exact MU| exact WM]| exact H|].
  intros x Hx. cbn [outside]. split; [lia| exact I].
Qed.

Lemma x2k_u8_tr : forall a b m1 m5 A bs, munch [(a, b)] m1 m5 -> wmono bsegs m1 m5 -> u8arr bsegs m1 A bs ->
  (A + zlen bs <= a \/ b <= A) -> u8arr bsegs m5 A bs.
Proof.
  intros a b m1 m5 A bs MU WM H D. eapply u8arr_transport; [exact H| exact MU| exact WM|]. cbn. split; [exact D| exact I].
Qed.

Lemma x2k_u32_tr : forall a b m1 m5 A ws, munch [(a, b)] m1 m5 -> wmono bsegs m1 m5 -> u32arr bsegs m1 A ws ->
  (A + 4 * zlen ws <= a \/ b <= A) -> u32arr bsegs m5 A ws.
Proof.
  intros a b m1 m5 A ws MU WM H D. eapply u32arr_transport; [exact H| exact MU| exact WM|]. cbn. split; [exact D| exact I].
Qed.

Lemma x2k_stats : forall src h (jrest : list byte),
  read_stats src = Ok h -> Forall (fun c => 0 <= c < 256) src -> zlen jrest = 256 - hs_nbSymbols h ->
  huf_stats_ok (firstn (Z.to_nat (hs_nbSymbols h)) (hs_weights h ++ map bv_unsigned jrest)) (hs_rank h) (hs_tableLog h)
  /\ 2 <= hs_nbSymbols h <= 256 /\ zlen (hs_weights h ++ map bv_unsigned jrest) = 256
  /\ Forall isbyte (hs_weights h ++ map bv_unsigned jrest) /\ zlen (hs_rank h) = 13 /\ 0 <= hs_ret h < 2^32
  /\ map (Z_to_bv 8) (hs_weights h ++ map bv_unsigned jrest) = map (Z_to_bv 8) (hs_weights h) ++ jrest.
Proof.
  intros src h jrest RS HF JL.
  destruct (read_stats_okB src h HF RS) as (HOK & HLEN).
  pose proof (HufPure_HufStatsRT.read_stats_ret src h (all_bytes_of_Forall src HF) RS) as RET.
  pose proof HOK as (TL & ZW & FW & ZR & _). unfold FseNCount.Zlength in ZW, ZR.
  split; [|split; [lia| split; [| split; [| split; [lia| split; [lia|]]]]]].
  - rewrite firstn_app, firstn_all2 by lia. replace (Z.to_nat (hs_nbSymbols h) - length (hs_weights h))%nat with 0%nat by lia.
    cbn [firstn]. rewrite app_nil_r. exact HOK.
  - rewrite length_app, length_map. lia.
  - apply Forall_app. split.
    + eapply Forall_impl; [| exact FW]. cbv beta. intros a Ha. lia.
    + apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (b & <- & _).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR. exact BR.
  - rewrite map_app, map_map. f_equal. erewrite map_ext; [apply map_id|]. intros b. apply definitions.Z_to_bv_bv_unsigned.
Qed.

Lemma x2k_dtne : forall pdt pw DT W mtl, 1 <= mtl <= 12 -> HB pdt DT (DTABLE_BYTES mtl) <> HB pw W 8704.
Proof.
  intros pdt pw DT W mtl HM E. apply (f_equal ab_size) in E. cbn in E. unfold DTABLE_BYTES, HufHarness.DT_BYTES in E.
  assert (MC : mtl = 1 \/ mtl = 2 \/ mtl = 3 \/ mtl = 4 \/ mtl = 5 \/ mtl = 6 \/ mtl = 7 \/ mtl = 8 \/ mtl = 9 \/ mtl = 10
               \/ mtl = 11 \/ mtl = 12) by lia.
  repeat destruct MC as [MC|MC]; subst mtl; vm_compute in E; discriminate.
Qed.

Lemma x2k_hyps : forall L RNG st LB m SPV lo FF W DT mtl pdt pw,
  AHEAP AI L RNG st (FB0 FF :: LB) m ->
  In (HB pdt DT (DTABLE_BYTES mtl)) LB -> In (HB pw W 8704) LB -> 1 <= mtl <= 12 ->
  FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  ATOP + 4096 <= lo -> lo <= SPV - HUF_RDT_STACK_A2 -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
  x2B_hyps RNG SPV (SPB SPV) lo DT W 8704 FF mtl.
Proof.
  intros L RNG st LB m SPV lo FF W DT mtl pdt pw AH HDT HWB HMTL F64 FH FC RF FFD BOT LO SPT SP16 RSTK RI.
  pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (spb_props SPV SP16) as (SPAB & SPA32 & _).
  destruct (hb_unpoisoned AI L RNG st (FB0 FF :: LB) m pdt DT (DTABLE_BYTES mtl) AH (or_intror HDT))
    as (_ & DT16 & _ & ABD & DTA & RDT & RSDT & _).
  destruct (hb_unpoisoned AI L RNG st (FB0 FF :: LB) m pw W 8704 AH (or_intror HWB))
    as (_ & W16 & _ & ABW & WA & RW & RSW & _).
  assert (DW : DT + DTABLE_BYTES mtl <= W \/ W + 8704 <= DT).
  { destruct (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH (or_intror HDT) (or_intror HWB) (x2k_dtne pdt pw DT W mtl HMTL)) as [D|D];
      cbn in D; lia. }
  pose proof (x2b_dtb_range mtl HMTL) as DTBR. unfold DTABLE_BYTES, HufHarness.DT_BYTES in *.
  pose proof (ablk_lin _ _ ABD) as (ABDa & ABDb & ABDc & ABDd).
  pose proof (ablk_lin _ _ ABW) as (ABWa & ABWb & ABWc & ABWd).
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd).
  pose proof (FFD _ HDT) as DF. pose proof (FFD _ HWB) as WF. cbn in DF, WF.
  assert (D8 : DT mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (W8 : W mod 8 = 0) by (Z.div_mod_to_equations; lia).
  unfold HUF_RDT_STACK_A2 in LO. unfold AIMG_HI in *.
  unfold x2B_hyps. rewrite D8, W8, !Z.add_0_r. unfold nshad. fold (shlen (4 * (1 + 2 ^ mtl) + 7)). fold (shlen (8704 + 7)).
  split; [exact HMTL|]. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
  split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|].
  split; [unfold Shadow.KHIGH; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact SP16|].
  split; [lia|]. split; [exact SPA32|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact F64|]. split; [lia|]. split; [exact FC|]. split; [exact FH|]. split; [lia|]. split; [lia|].
  split; [exact ABD|]. split; [exact RDT|]. split; [exact RSDT|]. split; [exact ABW|]. split; [exact RW|]. split; [exact RSW|].
  split; [exact RF|]. split; [eapply rng_sub'; [exact RSTK| lia]| exact RI].
Qed.

Lemma x2k_wr_u8 : forall m A n, wr_at bsegs m A n -> AIMG_HI <= A -> 0 <= n ->
  exists bs, length bs = Z.to_nat n /\ u8arr bsegs m A bs.
Proof.
  intros m A n WR HA HN.
  destruct (Shadow.rw_cells_of_wr_at bsegs m A n WR ltac:(apply no_image_asan; unfold AIMG_HI in *; lia) HN) as (bs & BL & BC).
  exists bs. split; [exact BL| eapply u8arr_of_rw_cells; exact BC].
Qed.

Lemma x2k_wr_stk : forall m A n, wr_at bsegs m A n -> AIMG_HI <= A -> 0 <= n -> stk bsegs m A (A + n).
Proof.
  intros m A n WR HA HN.
  destruct (Shadow.rw_cells_of_wr_at bsegs m A n WR ltac:(apply no_image_asan; unfold AIMG_HI in *; lia) HN) as (bs & BL & BC).
  pose proof (stk_of_rw_cells _ _ _ _ BC) as S. cbn [cells_size csize] in S. rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S.
Qed.

Lemma x2k_u8_u32 : forall m A n bs, u8arr bsegs m A bs -> length bs = (4 * n)%nat ->
  exists rv, length rv = n /\ Forall (fun v => 0 <= v < 2^32) rv /\ u32arr bsegs m A (map (Z_to_bv 64) rv).
Proof.
  intros m A n bs BU BL. destruct (x2k_chunk4 n bs BL) as (rv & RL & RF & RE).
  exists rv. split; [exact RL| split; [exact RF|]]. apply x2k_u32_of_u8. rewrite RE. exact BU.
Qed.

Lemma x2k_bytes : forall l : list byte, Forall isbyte (map bv_unsigned l) /\ map (Z_to_bv 8) (map bv_unsigned l) = l.
Proof.
  intros l. split.
  - apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (b & <- & _).
    pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR. exact BR.
  - rewrite map_map. erewrite map_ext; [apply map_id|]. intros b. apply definitions.Z_to_bv_bv_unsigned.
Qed.

Lemma x2_okB_mk : forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (m m1 m5 : amem)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SPV lo FF W DT mtl hdw : Z) (src : list Z)
    (jA jB jC jT jD jE : list byte) (j0 : word) (dtb : list byte) (pdt pw : aptr) (h : hstats),
  x2_postB L RNG st LB m m1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF W DT mtl hdw (hs_ret h) src jA jB jC jT jD jE j0 dtb ->
  read_stats src = Ok h -> Forall (fun c => 0 <= c < 256) src -> hs_tableLog h <= mtl ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  ATOP + 4096 <= lo -> lo <= SPV - HUF_RDT_STACK_A2 -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
  1 <= mtl <= 12 -> In (HB pdt DT (DTABLE_BYTES mtl)) LB -> In (HB pw W 8704) LB ->
  munch [(SPB SPV + 208, SPB SPV + 216)] m1 m5 -> wmono bsegs m1 m5 -> mem_inv bsegs m5 ->
  rw_cells bsegs m5 (SPB SPV) (X2BFRA1 FF DT W jA jB jC (Z_to_bv 64 (hs_tableLog h)) jD jE) ->
  exists hw : list Z,
    x2_okB L RNG st LB m m5 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF W DT mtl hdw (hs_ret h) (hs_tableLog h)
      (hs_nbSymbols h) hw (hs_rank h) j0.
Proof.
  intros L RNG st LB m m1 m5 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF W DT mtl hdw src jA jB jC jT jD jE j0 dtb pdt pw h
         PB RS HF TLM LBH BOT LO SPT SP16 RSTK RI HMTL HDT HWB MU WM MI5 FR5.
  destruct PB as (F64 & FH & FC & RF & RSF & FFD & AH1 & MI1 & MG1 & STL1 & STG1 & FRA0 & (w1 & w2 & FW12) & SAV1 & SH1 & FJ1 & F561
                  & DTU1 & DTL & RZ1 & HD1 & HD2 & HD3 & RR & MT).
  rewrite RS in MT. cbv iota beta in MT. destruct MT as (_ & (jrest & HWU1 & JL) & RKU1 & NB1 & TL1).
  pose proof (x2k_hyps L RNG st LB m1 SPV lo FF W DT mtl pdt pw AH1 HDT HWB HMTL F64 FH FC RF FFD BOT LO SPT SP16 RSTK RI) as HY.
  pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH1) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (spb_props SPV SP16) as (SPAB & SPA32 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  unfold HUF_RDT_STACK_A2 in LO.
  assert (AH5 : AHEAP AI L RNG st (FB0 FF :: LB) m5).
  { eapply (AI_frame AI); [exact AH1| exact MU| exact WM|]. constructor; [|constructor]. left; left. cbn. lia. }
  destruct (hb_unpoisoned AI L RNG st (FB0 FF :: LB) m5 pdt DT (DTABLE_BYTES mtl) AH5 (or_intror HDT))
    as (UDT & _ & _ & ABD & DTA & _ & _ & _).
  destruct (hb_unpoisoned AI L RNG st (FB0 FF :: LB) m5 pw W 8704 AH5 (or_intror HWB))
    as (UW & W16 & _ & ABW & WA & _ & _ & WRW).
  unfold DTABLE_BYTES, HufHarness.DT_BYTES in UDT, ABD, DTA.
  pose proof (x2b_dtb_range mtl HMTL) as DTBR.
  pose proof (ablk_lin _ _ ABD) as (ABDa & ABDb & ABDc & ABDd).
  pose proof (ablk_lin _ _ ABW) as (ABWa & ABWb & ABWc & ABWd).
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd).
  pose proof (shad_in_band FF ltac:(lia)) as SBF.
  assert (SH8 : shad FF = Z.shiftr FF 3 + ASHOFF) by (unfold shad; lia).
  assert (SHL : Z.shiftr FF 3 + ASHOFF + 8 <= SPB SPV - 2208) by (rewrite <- SH8; unfold KLS in *; lia).
  assert (SH5 : rw_cells bsegs m5 (Z.shiftr FF 3 + ASHOFF) X2BSH).
  { eapply x2k_rwc_tr; [exact MU| exact WM| exact SH1|]. unfold X2BSH. cbn [cells_size csize]. lia. }
  assert (FJ5 : rw_cells bsegs m5 FF [C8 j0]) by (eapply x2k_rwc_tr; [exact MU| exact WM| exact FJ1| cbn; lia]).
  assert (F565 : rw_cells bsegs m5 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))])
    by (eapply x2k_rwc_tr; [exact MU| exact WM| exact F561| cbn; lia]).
  assert (SAV5 : rw_cells bsegs m5 (SPV + -104) (X2BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply x2k_rwc_tr; [exact MU| exact WM| exact SAV1|]. unfold X2BSAVED. cbn [cells_size csize]. lia. }
  assert (STG5 : stk bsegs m5 (SPB SPV + 408) (SPV + -104)) by (eapply x2k_stk_tr; [exact MU| exact WM| exact STG1| lia]).
  assert (MG5 : magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (DT <= a < DT + DTABLE_BYTES mtl) /\ ~ (W <= a < W + 8704)) m m5).
  { eapply magree_munch_step; [eapply magree_mono; [exact MG1| intros a (HP & _ & HN); split; [exact HP| exact HN]]| exact MU| exact WM|].
    intros a (HP & _ & _). cbn [outside]. split; [|exact I]. intros HIN.
    exact (stack_not_client CI LB SPV (SPB SPV + 208) a HCI HCI0 LBH ltac:(lia) ltac:(lia) HP). }
  assert (ART : x2hb_art m5).
  { destruct (fse_rt_of_aheap AI _ _ _ _ _ AH5) as (GOT & RIC & REAL & SHB & _ & INI & LAY).
    unfold x2hb_art. tauto. }
  assert (STL5 : stk bsegs m5 lo (SPB SPV)).
  { assert (S1 : stk bsegs m5 lo (SPB SPV - 16)) by (eapply x2k_stk_tr; [exact MU| exact WM| exact STL1| lia]).
    assert (F5 : rw_cells bsegs m5 (SPB SPV - 16) [C8 w1; C8 w2]) by (eapply x2k_rwc_tr; [exact MU| exact WM| exact FW12| cbn; lia]).
    pose proof (stk_release _ _ _ _ _ S1 F5 ltac:(lia)) as S. cbn [cells_size csize] in S.
    replace (SPB SPV - 16 + Z.of_nat (8 + (8 + 0))) with (SPB SPV) in S by lia. exact S. }
  assert (DT5 : u8arr bsegs m5 DT dtb) by (eapply x2k_u8_tr; [exact MU| exact WM| exact DTU1| lia]).
  destruct (x2k_stats src h jrest RS HF JL) as (HSO & NBR & HWL & HWB8 & RKL & RETR & HWM).
  assert (HW5 : u8arr bsegs m5 (W + 992) (map (Z_to_bv 8) (hs_weights h ++ map bv_unsigned jrest))).
  { rewrite HWM. eapply x2k_u8_tr; [exact MU| exact WM| exact HWU1|]. rewrite <- HWM, length_map. lia. }
  assert (RK5 : u32arr bsegs m5 (W + 624) (map (Z_to_bv 64) (hs_rank h))).
  { eapply x2k_u32_tr; [exact MU| exact WM| exact RKU1|]. rewrite length_map. lia. }
  assert (NB5 : rw_cells bsegs m5 (FF + 48) [C4 (Z_to_bv 64 (hs_nbSymbols h))])
    by (eapply x2k_rwc_tr; [exact MU| exact WM| exact NB1| cbn; lia]).
  assert (RZ5 : rw_cells bsegs m5 (W + 676) [CB 60 (repeat (Z_to_bv 8 0) 60)]) by (eapply x2k_rwc_tr; [exact MU| exact WM| exact RZ1| cbn; lia]).
  destruct (x2k_wr_u8 m5 (W + 736) 256 ltac:(eapply Shadow.wr_at_sub; [exact WRW| lia| lia]) ltac:(lia) ltac:(lia)) as (syb & SYL & SYB5).
  destruct (x2k_wr_u8 m5 W 624 ltac:(eapply Shadow.wr_at_sub; [exact WRW| lia| lia]) ltac:(lia) ltac:(lia)) as (rvb & RVBL & RVB5).
  destruct (x2k_u8_u32 m5 W 156 rvb RVB5 ltac:(rewrite RVBL; lia)) as (rv & RVL & RVF & RV5).
  destruct (x2k_u8_u32 m5 (W + 676) 15 _ (u8arr_of_rw_cells _ _ _ _ _ RZ5) ltac:(rewrite repeat_length; reflexivity))
    as (rs0 & RSL & RSF0 & RS05).
  assert (STW5 : stk bsegs m5 (W + 1248) (W + 8704)).
  { pose proof (x2k_wr_stk m5 (W + 1248) (8704 - 1248) ltac:(eapply Shadow.wr_at_sub; [exact WRW| lia| lia]) ltac:(lia) ltac:(lia)) as S.
    replace (W + 1248 + (8704 - 1248)) with (W + 8704) in S by lia. exact S. }
  destruct (x2k_frame _ _ _ _ _ _ _ _ _ _ _ FR5) as [k0 FRK].
  repeat lazymatch type of FRK with ex _ => destruct FRK as [? FRK] end.
  pose proof (x2k_bytes dtb) as (DTF & DTM).
  exists (hs_weights h ++ map bv_unsigned jrest).
  unfold x2_okB.
  split; [exact HY|]. split; [exact UDT|]. split; [exact UW|]. split; [exact ART|]. split; [lia|].
  split; [exact HD1|]. split; [exact HD2|]. split; [exact HD3|]. split; [exact HSO|]. split; [exact NBR|].
  split; [exact HWL|]. split; [exact HWB8|]. split; [exact RKL|]. split; [exact TLM|].
  split.
  { do 46 eexists. unfold XBB.
    split; [rewrite DTM; exact DT5|]. split; [rewrite length_map; lia|]. split; [exact DTF|].
    split; [exact HW5|]. split; [exact RK5|]. split; [exact RS05|]. split; [lia|]. split; [exact RSF0|].
    split; [exact SYB5|]. split; [lia|]. split; [exact RV5|]. split; [lia|]. split; [exact RVF|].
    split; [exact STW5|]. split; [exact NB5|]. split; [exact STL5|]. split; [exact MI5|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. exact FRK. }
  split; [exact AH5|]. split; [exact FFD|]. split; [exact RSF|]. split; [exact MG5|]. split; [exact SH5|].
  split; [exact FJ5|]. split; [exact F565|]. split; [exact SAV5|]. exact STG5.
Qed.

Lemma x2c_stk_rwc : forall m A cs n hi, rw_cells bsegs m A cs -> cells_size cs = n -> hi = A + Z.of_nat n -> stk bsegs m A hi.
Proof. intros m A cs n hi H E1 E2. subst hi n. exact (stk_of_rw_cells bsegs m A cs H). Qed.

Lemma x2c_frame_close : forall m lo SPA hi (w1 w2 s8 f1 f2 a200 a216 a352 a400 a128 c208 : cell) (jA jB jC jD jE : list byte),
  stk bsegs m lo (SPA - 16) -> rw_cells bsegs m (SPA - 16) [w1; w2] -> cells_size [w1; w2] = 16%nat ->
  rw_cells bsegs m SPA [CB 128 jA; a128; CB 32 jB; s8; f1; f2; CB 8 jC; a200; c208; a216; CB 128 jD; a352; CB 40 jE; a400] ->
  cells_size [CB 128 jA; a128; CB 32 jB] = 168%nat -> cells_size [s8; f1; f2] = 24%nat ->
  cells_size [CB 8 jC; a200; c208; a216; CB 128 jD; a352; CB 40 jE; a400] = 216%nat ->
  stk bsegs m (SPA + 408) hi -> lo <= SPA - 16 -> SPA + 408 <= hi ->
  rw_cells bsegs m (SPA + 168) [s8; f1; f2] /\ stk bsegs m lo (SPA + 168) /\ stk bsegs m (SPA + 192) hi.
Proof.
  intros m lo SPA hi w1 w2 s8 f1 f2 a200 a216 a352 a400 a128 c208 jA jB jC jD jE STL W12 S12 FR Z3 Z6 ZT STG L1 L2.
  pose proof (proj1 (Startup_kit.rw_cells_app bsegs m SPA [CB 128 jA; a128; CB 32 jB] _) FR) as (H3 & R3).
  rewrite Z3 in R3. change (Z.of_nat 168) with 168 in R3.
  pose proof (proj1 (Startup_kit.rw_cells_app bsegs m (SPA + 168) [s8; f1; f2] _) R3) as (H6 & R6).
  rewrite Z6 in R6. change (Z.of_nat 24) with 24 in R6.
  split; [exact H6|]. split.
  - eapply stk_merge; [| eapply x2c_stk_rwc; [exact H3| exact Z3| reflexivity]| lia].
    eapply stk_merge; [exact STL| eapply x2c_stk_rwc; [exact W12| exact S12| cbn; lia]| lia].
  - replace (SPA + 192) with (SPA + 168 + 24) by lia.
    eapply stk_merge; [eapply x2c_stk_rwc; [exact R6| exact ZT| reflexivity]| | lia].
    replace (SPA + 168 + 24 + Z.of_nat 216) with (SPA + 408) by lia. exact STG.
Qed.

Lemma x2k_rwc_at : forall m A A' cs, rw_cells bsegs m A cs -> A = A' -> rw_cells bsegs m A' cs.
Proof. intros m A A' cs H E. subst A'. exact H. Qed.

Lemma x2k_split : forall m A n cs, rw_cells bsegs m A cs ->
  rw_cells bsegs m A (firstn n cs) /\ rw_cells bsegs m (A + Z.of_nat (cells_size (firstn n cs))) (skipn n cs).
Proof. intros m A n cs H. apply Startup_kit.rw_cells_app. rewrite firstn_skipn. exact H. Qed.

Lemma x2k_stk_cells : forall m lo A cs hi, stk bsegs m lo A -> rw_cells bsegs m A cs -> hi = A + Z.of_nat (cells_size cs) ->
  lo <= A -> stk bsegs m lo hi.
Proof.
  intros m lo A cs hi S1 H E LA. subst hi. eapply stk_merge; [exact S1| exact (stk_of_rw_cells bsegs m A cs H)| lia].
Qed.

Lemma x2k_sh_out : forall FF DT W mtl SPV SPA a, ablk FF (FF + 64) -> ablk DT (DT + 4 * (1 + 2 ^ mtl)) -> ablk W (W + 8704) ->
  KHIGH <= SPV - 640 -> SPA <= SPV - 512 ->
  Z.shiftr FF 3 + ASHOFF <= a < Z.shiftr FF 3 + ASHOFF + Z.of_nat (cells_size X2BSH) ->
  outside [(DT, DT + 4 * (1 + 2 ^ mtl)); (W, W + 8704); (SPV - 640, SPA + 408)] a.
Proof.
  intros FF DT W mtl SPV SPA a HF HD HW HK HS Ha.
  replace (Z.of_nat (cells_size X2BSH)) with 8 in Ha by reflexivity.
  pose proof atop_range as ATR. pose proof (ablk_lin _ _ HF). pose proof (ablk_lin _ _ HD). pose proof (ablk_lin _ _ HW).
  rewrite Z.shiftr_div_pow2 in Ha by lia. change (2^3) with 8 in Ha.
  unfold ablk in *. unfold ASHOFF, AIMG_HI, KLS, KHIGH in *.
  cbn [outside]. Z.div_mod_to_equations. lia.
Qed.

Lemma x2_kendB : forall (L : alayout) (RNG : footprint)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m m5 m2 : amem) (st : astate) (LB : list ablock) (SPV lo FF W DT mtl hdw r tl nbs : Z) (hw rank : list Z) (j0 : word)
    (pdt pw : aptr) (dt2 rs2 rv2 : list Z) (syb2 : list byte)
    (q0 q8 q16 q24 q32 q40 q48 q56 q64 q72 q80 q88 q96 q104 q112 q120 q136 q144 q152 q160 q192 q208 q224 q232 q240 q248 q256
     q264 q272 q280 q288 q296 q304 q312 q320 q328 q336 q344 q360 q368 q376 q384 q392 : word)
    (yra y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
  x2_okB L RNG st LB m m5 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF W DT mtl hdw r tl nbs hw rank j0 ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  lo <= SPV - HUF_RDT_STACK_A2 -> SPV + 16 < al_top L -> rng RNG lo (al_top L - lo) -> In (HB pdt DT (DTABLE_BYTES mtl)) LB ->
  In (HB pw W 8704) LB ->
  XBB m5 SPV (SPB SPV) lo DT W 8704 FF mtl nbs hw rank q0 q8 q16 q24 q32 q40 q48 q56 q64 q72 q80 q88 q96 q104 q112 q120 q136
    q144 q152 q160 q192 q208 q224 q232 q240 q248 q256 q264 q272 q280 q288 q296 q304 q312 q320 q328 q336 q344 q360 q368 q376 q384
    q392 dt2 rs2 syb2 rv2 m2 ->
  x2pref (TTB tl mtl) (2 ^ TTB tl mtl) dt2 -> Znth 0 dt2 = mtl -> Znth 1 dt2 = 1 -> Znth 2 dt2 = TTB tl mtl ->
  Znth 3 dt2 = hdw / 16777216 ->
  evtF bsegs RNG (huf_rdt_postA AI huf_dt_okA L RNG ra (Z_to_bv 64 SPV) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB
                    DT W mtl lo m)
    (MS (mkR yra (Z_to_bv 64 (SPB SPV)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPB SPV)) (Z_to_bv 64 r)
             y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
        FR (Z_to_bv 64 (X2B_ENTRY + 3732)) fc None m2 (seg_rom bsegs)).
Proof.
  intros *. intros OK LBH LO SPT RSTK HDT HBW XB PF Z0 Z1 Z2 Z3.
  destruct OK as (HY & UDT & UW & ART & HR & HM & HHW & HDV & HST & NBS & ZHW & BHW & ZRK & TLM & _ & AH5 & FFD & RSF & MG5
                  & SH5 & FF05 & FF565 & SV5 & STG5).
  destruct HY as (MTL & DTL & DTH & DT4 & WKL & WKH & WK4 & WR & KLO & BOT & LOS & SPTT & SP16 & SPAB & SPA32 & SDS & SWS
                  & DTWK & F64 & FFL & FC & ABF & DFD & DFW & ABD & RDT & RSDT & ABW & RW & RSW & RFF & RSTK' & RI).
  destruct XB as (DTC & DTLEN & DTBY & HWC & RK & RS & RSL & RSN & SYC & SYL & RVC & RVL & RVN & SKW & NBC & STL & MI2 & MU & WM
                  & FRA).
  pose proof atop_range as ATR.
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (magree_of_munch bsegs _ _ _ MU WM) as MGX.
  assert (AH2 : AHEAP AI L RNG st (FB0 FF :: LB) m2).
  { eapply (AI_frame AI); [exact AH5| exact MU| exact WM|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    - right; left. exists (HB pdt DT (DTABLE_BYTES mtl)).
      split; [right; exact HDT| cbn; unfold DTABLE_BYTES, HufHarness.DT_BYTES; lia].
    - right; left. exists (HB pw W 8704). split; [right; exact HBW| cbn; lia].
    - left; left. cbn. lia. }
  assert (MG2 : magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (DT <= a < DT + DTABLE_BYTES mtl) /\ ~ (W <= a < W + 8704))
                  m m2).
  { eapply magree_munch_step; [exact MG5| exact MU| exact WM|].
    intros a (Ha & HnD & HnW). cbn [outside]. unfold DTABLE_BYTES, HufHarness.DT_BYTES in HnD.
    split; [exact HnD|]. split; [exact HnW|]. split; [|exact I].
    intros HIN. exact (stack_not_client CI LB SPV (SPV - 640) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha). }
  assert (SH2 : rw_cells bsegs m2 (Z.shiftr FF 3 + ASHOFF) X2BSH).
  { eapply rw_cells_magree; [exact MGX| exact SH5|].
    intros a Ha. exact (x2k_sh_out FF DT W mtl SPV (SPB SPV) a ABF ABD ABW ltac:(unfold KHIGH in *; lia) ltac:(lia) Ha). }
  assert (FF02 : rw_cells bsegs m2 FF [C8 j0]).
  { eapply rw_cells_magree; [exact MGX| exact FF05|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
  assert (FF562 : rw_cells bsegs m2 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))]).
  { eapply rw_cells_magree; [exact MGX| exact FF565|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
  assert (SV2 : rw_cells bsegs m2 (SPV + -104) (X2BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_magree; [exact MGX| exact SV5|]. intros a Ha. unfold X2BSAVED in Ha. cbn in Ha. cbn [outside]. lia. }
  unfold X2BF in FRA.
  destruct (x2k_split _ _ 21 _ FRA) as (FA0 & FA1). cbn [firstn skipn] in FA0, FA1.
  destruct (x2k_split _ _ 3 _ FA1) as (FA2 & FA3). cbn [firstn skipn] in FA2, FA3.
  assert (FRA2 : rw_cells bsegs m2 (SPB SPV + 168)
                   [C8 (Z_to_bv 64 (Z.shiftr FF 3 + ASHOFF)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)]).
  { eapply x2k_rwc_at; [exact FA2| cbn; lia]. }
  assert (STL2 : stk bsegs m2 lo (SPB SPV + 168)).
  { eapply x2k_stk_cells; [exact STL| exact FA0| cbn; lia| lia]. }
  assert (STG2 : stk bsegs m2 (SPB SPV + 192) (SPV + -104)).
  { eapply (stk_merge bsegs m2 _ (SPB SPV + 408)).
    - eapply x2k_stk_cells; [apply stk_empty; lia| eapply x2k_rwc_at; [exact FA3| cbn; lia]| cbn; lia| lia].
    - eapply stk_magree; [exact MGX| exact STG5|]. intros a Ha. cbn [outside]. lia.
    - lia. }
  pose proof (proj1 HST) as TL1.
  pose proof (TTB_range tl mtl ltac:(lia) ltac:(lia)) as TTR.
  exact (x2_closeB L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m2 st LB SPV DT W mtl lo FF r
           pdt j0 yra y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
           AH2 LBH F64 ABF FC RFF RSF FFD MG2 MI2 SH2 FF02 FF562 SV2 FRA2 STL2 STG2 BOT LO SPT SP16 RSTK RI MTL HDT
           ltac:(lia)
           (fun _ => x2_dt_okB m2 DT mtl (TTB tl mtl) dt2 MTL ltac:(lia) PF Z0 Z1 Z2 ltac:(rewrite Z3; exact HDV) DTLEN DTBY DTC)).
Qed.

Lemma x2_rsretB : forall (L : alayout) (RNG : footprint)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m m1 : amem) (st : astate) (LB : list ablock) (SPV lo FF W DT mtl hdw r : Z) (src : list Z)
    (jA jB jC jT jD jE : list byte) (j0 : word) (dtb : list byte) (pdt pw : aptr)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 xs2 xs5 xs9 x28 x29 x30 x31 : word),
  x2_postB L RNG st LB m m1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF W DT mtl hdw r src jA jB jC jT jD jE j0 dtb ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  ATOP + 4096 <= lo -> lo <= SPV - HUF_RDT_STACK_A2 -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> tp = Z_to_bv 64 ATP ->
  1 <= mtl <= 12 -> In (HB pdt DT (DTABLE_BYTES mtl)) LB -> In (HB pw W 8704) LB ->
  Forall (fun c => 0 <= c < 256) src ->
  (forall (m5 : amem) (r' tl nbs : Z) (hw rank : list Z) (j0' : word) (y1 y5 y6 y7 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     x2_okB L RNG st LB m m5 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF W DT mtl hdw r' tl nbs hw rank j0' ->
     evtF bsegs RNG (huf_rdt_postA AI huf_dt_okA L RNG ra (Z_to_bv 64 SPV) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB
                       DT W mtl lo m)
       (MS (mkR y1 (Z_to_bv 64 (SPB SPV)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPB SPV))
                (Z_to_bv 64 (-44)) (Z_to_bv 64 r') (Z_to_bv 64 mtl) (Z_to_bv 64 tl) y14 y15 y16 y17
                xs2 (Z_to_bv 64 X2C_S3) (Z_to_bv 64 hdw) xs5 (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 W)
                (Z_to_bv 64 (W + 992)) xs9 (Z_to_bv 64 (W + 624)) (Z_to_bv 64 (FF + 32)) y28 y29 y30 y31)
           FR (Z_to_bv 64 (X2B_ENTRY + 544)) fc None m5 (seg_rom bsegs))) ->
  evtF bsegs RNG (huf_rdt_postA AI huf_dt_okA L RNG ra (Z_to_bv 64 SPV) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB
                    DT W mtl lo m)
    (MS (mkR x1 (Z_to_bv 64 (SPB SPV - 16)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPB SPV))
             (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
             xs2 (Z_to_bv 64 X2C_S3) (Z_to_bv 64 hdw) xs5 (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 W)
             (Z_to_bv 64 (W + 992)) xs9 (Z_to_bv 64 (W + 624)) (Z_to_bv 64 (FF + 32)) x28 x29 x30 x31)
        FR (Z_to_bv 64 (X2B_ENTRY + 508)) fc None m1 (seg_rom bsegs)).
Proof.
  intros L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m1 st LB SPV lo FF W DT mtl hdw r src jA jB jC jT jD jE j0 dtb
         pdt pw x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 xs2 xs5 xs9 x28 x29 x30 x31 PB LBH BOT LO SPT SP16 RSTK RI TP HMTL HDT HWB SRCB KOK.
  pose proof PB as (F64 & FH & FC & RF & RSF & FFD & AH1 & MI1 & MG1 & STL1 & STG1 & FRA1 & (w1 & w2 & S16) & SV1 & SH1 & FJ0 & F56
                    & DTU & DTL & ZC & HHM & HHR & HDV & HR & HRS).
  pose proof atop_range as ATR.
  pose proof (spb_props SPV SP16) as (SPAB & SPA32 & _).
  pose proof (AI_block_bounds AI _ _ _ _ _ (FB0 FF) AH1 (or_introl eq_refl)) as FBB. cbn in FBB.
  pose proof (AI_layout AI _ _ _ _ _ AH1) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  assert (RST : rng RNG lo (SPV - lo)) by (eapply rng_sub'; [exact RSTK|..]; lia).
  assert (LOS : lo <= SPV - 528 - 4096 - 16) by (unfold HUF_RDT_STACK_A2 in LO; lia).
  assert (CLOSE : forall m4 rv (c208 : cell)
            (z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
            munch [(SPB SPV + 208, SPB SPV + 216)] m1 m4 -> wmono bsegs m1 m4 -> mem_inv bsegs m4 ->
            rw_cells bsegs m4 (SPB SPV) [CB 128 jA; C8 (Z_to_bv 64 (Z.shiftr DT 3 + ASHOFF)); CB 32 jB;
              C8 (Z_to_bv 64 (Z.shiftr FF 3 + ASHOFF)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF);
              CB 8 jC; C8 (Z_to_bv 64 (W + 676)); c208; C8 (Z_to_bv 64 DT); CB 128 jD; C8 (Z_to_bv 64 W); CB 40 jE; C8 (Z_to_bv 64 FF)] ->
            cells_size [c208] = 8%nat -> 0 <= rv < 2^64 -> 2^64 - 119 <= rv ->
            evtF bsegs RNG (huf_rdt_postA AI huf_dt_okA L RNG ra (Z_to_bv 64 SPV) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB
                              DT W mtl lo m)
              (MS (mkR z1 (Z_to_bv 64 (SPB SPV)) gp tp z5 z6 z7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPB SPV)) (Z_to_bv 64 rv)
                       z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31)
                  FR (Z_to_bv 64 (X2B_ENTRY + 3732)) fc None m4 (seg_rom bsegs))).
  { intros m4 rv c208 z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31
           MU WM MI4 FR4 C208 HRV HRV2.
    assert (OUTW : forall a, (SPB SPV - 16 <= a /\ a < SPB SPV + 216 -> False) -> outside [(SPB SPV + 208, SPB SPV + 216)] a)
      by (intros a Ha; cbn [outside]; split; [lia| exact I]).
    pose proof (magree_of_munch _ _ _ _ MU WM) as MGW.
    assert (MG4 : magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (DT <= a < DT + DTABLE_BYTES mtl) /\ ~ (W <= a < W + 8704)) m m4).
    { eapply (magree_munch_step _ m m1 m4); [| exact MU| exact WM|].
      - intros a Ha [HP [_ HW]]. exact (MG1 a Ha (conj HP HW)).
      - intros a [HP _]. cbn [outside]. split; [|exact I].
        intros HIN. exact (stack_not_client CI LB SPV (SPB SPV - 16) a HCI HCI0 LBH ltac:(lia) ltac:(lia) HP). }
    assert (AH4 : AHEAP AI L RNG st (FB0 FF :: LB) m4).
    { eapply (AI_frame AI); [exact AH1| exact MU| exact WM|]. constructor; [|constructor]. left; left. cbn. split; lia. }
    assert (STL4 : stk bsegs m4 lo (SPB SPV - 16)).
    { eapply stk_magree; [exact MGW| exact STL1|]. intros a Ha. cbn [outside]. split; [lia| exact I]. }
    assert (STG4 : stk bsegs m4 (SPB SPV + 408) (SPV + -104)).
    { eapply stk_magree; [exact MGW| exact STG1|]. intros a Ha. cbn [outside]. split; [lia| exact I]. }
    assert (S164 : rw_cells bsegs m4 (SPB SPV - 16) [C8 w1; C8 w2]).
    { eapply rw_cells_magree; [exact MGW| exact S16|]. intros a Ha. cbn in Ha. cbn [outside]. split; [lia| exact I]. }
    destruct (x2c_frame_close m4 lo (SPB SPV) (SPV + -104) _ _ _ _ _ _ _ _ _ _ c208 jA jB jC jD jE STL4 S164 eq_refl FR4)
      as (FRB4 & STLB & STGB); [cbn; reflexivity| cbn; reflexivity| change [CB 8 jC; C8 (Z_to_bv 64 (W + 676)); c208; C8 (Z_to_bv 64 DT); CB 128 jD; C8 (Z_to_bv 64 W); CB 40 jE; C8 (Z_to_bv 64 FF)]
          with ([CB 8 jC; C8 (Z_to_bv 64 (W + 676))] ++ [c208] ++ [C8 (Z_to_bv 64 DT); CB 128 jD; C8 (Z_to_bv 64 W); CB 40 jE; C8 (Z_to_bv 64 FF)]);
        rewrite !cells_size_app, C208; reflexivity
      | exact STG4| lia| lia|].
    eapply x2_closeB; try eassumption.
    - eapply rw_cells_magree; [exact MGW| exact SH1|]. intros a Ha. unfold X2BSH in Ha. cbn in Ha. cbn [outside]. rewrite Z.shiftr_div_pow2 in Ha by lia. change (2^3) with 8 in Ha.
      unfold ASHOFF in *. split; [Z.div_mod_to_equations; lia| exact I].
    - eapply rw_cells_magree; [exact MGW| exact FJ0|]. intros a Ha. cbn in Ha. cbn [outside]. split; [lia| exact I].
    - eapply rw_cells_magree; [exact MGW| exact F56|]. intros a Ha. cbn in Ha. cbn [outside]. split; [lia| exact I].
    - eapply rw_cells_magree; [exact MGW| exact SV1|]. intros a Ha. unfold X2BSAVED in Ha. cbn in Ha. cbn [outside]. split; [lia| exact I].
    - intros Hlt. lia. }
  assert (E44 : Z_to_bv 64 (-44) = Z_to_bv 64 (2^64 - 44)) by (apply bv_eq; vm_compute; reflexivity).
  assert (LOC : ATOP <= lo) by lia.
  assert (F4K : 4096 <= FF) by (unfold AIMG_HI in *; lia).
  destruct (read_stats src) as [h|e| |] eqn:RS; [| | contradiction | contradiction].
  - destruct HRS as (RH & (jrest & HWA & JRL) & RKA & NSC & TLC).
    destruct (read_stats_okB src h SRCB RS) as (HSO & HNB).
    pose proof HSO as (TLR & _).
    pose proof (read_stats_ret src h (all_bytes_of_Forall src SRCB) RS) as RRB.
    subst r.
    eapply evtF_cut; [| cbv beta; intros ms' HQ; exact HQ].
    eapply (x2_rsw gp tp FR fc SPV lo SP16 LOS LOC RNG RST) with (Q := fun ms => evtF bsegs RNG
      (huf_rdt_postA AI huf_dt_okA L RNG ra (Z_to_bv 64 SPV) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DT W mtl lo m) ms)
      (tl := hs_tableLog h).
    all: try first [exact STL1 | exact MI1 | exact FRA1 | exact (fun _ => TLC) | exact HHR | exact HHM | exact HMTL | exact FC
                   | exact F64 | exact FH | exact RF | exact F4K].
    all: try (intros; lia).
    + intros m' Hr Htl MU WM MI' FR'. cbv beta. rewrite E44.
      eapply (CLOSE m' (2^64 - 44) (C8 (Z_to_bv 64 (hs_tableLog h)))); try eassumption; try (unfold X2BFRA1 in FR'; exact FR'); try reflexivity; lia.
    + intros m' Hr Htl MU WM MI' FR'. cbv beta.
      destruct (x2_okB_mk L RNG st LB m m1 m' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF W DT mtl hdw src jA jB jC jT jD jE j0 dtb
                  pdt pw h PB RS SRCB Htl LBH BOT LO SPT SP16 RSTK RI HMTL HDT HWB MU WM MI' FR') as (hw & OK).
      eapply KOK. exact OK.
  - destruct HRS as (RE & EB).
    eapply evtF_cut; [| cbv beta; intros ms' HQ; exact HQ].
    eapply (x2_rsw gp tp FR fc SPV lo SP16 LOS LOC RNG RST) with (Q := fun ms => evtF bsegs RNG
      (huf_rdt_postA AI huf_dt_okA L RNG ra (Z_to_bv 64 SPV) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DT W mtl lo m) ms)
      (tl := 0).
    all: try first [exact STL1 | exact MI1 | exact FRA1 | exact HHR | exact HHM | exact HMTL | exact FC
                   | exact F64 | exact FH | exact RF | exact F4K].
    all: try (intros; lia).
    intros Hc. cbv beta.
    eapply (CLOSE m1 r (CB 8 jT)); [exact (munch_refl _ m1) | exact (wmono_refl bsegs m1) | exact MI1 | ..];
      try (unfold X2BFRA0 in FRA1; exact FRA1); try reflexivity; lia.
Qed.

Hypothesis RSK : huf_rstats_stmtA AI rng_fs 1.

Lemma rc_cb4c4 : forall m A bs, rw_cells bsegs m A [CB 4 bs] -> exists v : word, rw_cells bsegs m A [C4 v].
Proof.
  intros m A bs H. pose proof H as ((WF & _) & _). cbn [cells_wf cell_wf] in WF. destruct WF as (LB4 & _).
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). apply (rw_cells_CB4_C4 bsegs m A _ []).
  destruct bs as [|b0 [|b1 [|b2 [|b3 [|]]]]]; cbn in LB4; try discriminate.
  set (z := bytes_le_to_Z [b0; b1; b2; b3]).
  assert (N : 0 <= z).
  { subst z. cbn [bytes_le_to_Z].
    pose proof (bv_unsigned_in_range _ b0). pose proof (bv_unsigned_in_range _ b1).
    pose proof (bv_unsigned_in_range _ b2). pose proof (bv_unsigned_in_range _ b3).
    repeat first [apply (proj2 (Z.lor_nonneg _ _)); split | apply (proj2 (Z.shiftl_nonneg _ _)) | lia]. }
  assert (E : Z_to_le_bytes 4 z = [b0; b1; b2; b3]) by exact (Z_to_le_bytes_to_Z [b0; b1; b2; b3]).
  assert (U : z < 2^32).
  { pose proof (bytes_le_to_Z_to_le_bytes 4 z N) as Q. rewrite E in Q. change (2 ^ (8 * Z.of_nat 4)) with (2^32) in Q.
    pose proof (Z.mod_pos_bound z (2^32) ltac:(lia)). lia. }
  unfold le4. rewrite unsigned_lit by lia. rewrite E. exact H.
Qed.

Local Ltac rcfix H X := match type of H with rw_cells _ _ ?Y _ => replace Y with X in H by lia end.

Lemma rc_mid : forall m A pre c post, rw_cells bsegs m A (pre ++ c :: post) ->
  rw_cells bsegs m (A + Z.of_nat (cells_size pre)) [c].
Proof.
  intros m A pre c post H. apply rw_cells_app in H. destruct H as (_ & H).
  exact (proj1 (proj1 (rw_cells_app bsegs m _ [c] post) H)).
Qed.

Lemma rc_u8 : forall m A n j, rw_cells bsegs m A [CB n j] -> u8arr bsegs m A j /\ length j = n.
Proof.
  intros m A n j ((WF & B) & W). cbn [cells_wf cell_wf] in WF. destruct WF as (LJ & _).
  cbn [cells_bytes] in B. rewrite app_nil_r in B.
  split; [| exact LJ]. split; [exact B|].
  assert (E : Z.of_nat (cells_size [CB n j]) = Z.of_nat (length j)) by (cbn; rewrite LJ; lia).
  rewrite <- E. exact W.
Qed.

Lemma rc_u8_mg : forall (P : Z -> Prop) m m' A bs, magree bsegs P m m' -> u8arr bsegs m A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> u8arr bsegs m' A bs.
Proof.
  intros P m m' A bs MG (B & W) HP. split.
  - exact (bytes_at_magree bsegs P m m' A bs MG B HP).
  - exact (wr_at_magree bsegs P m m' A _ MG W HP).
Qed.

Lemma rc_ffsplit : forall m FF w0 w1 w2 w4 j3,
  rw_cells bsegs m FF [C8 w0; C8 w1; C8 w2; CB 32 j3; C8 w4] ->
  rw_cells bsegs m FF [C8 w0] /\ rw_cells bsegs m (FF + 56) [C8 w4]
  /\ (exists v : word, rw_cells bsegs m (FF + 32) [C4 v]) /\ (exists v : word, rw_cells bsegs m (FF + 48) [C4 v]).
Proof.
  intros m FF w0 w1 w2 w4 j3 H.
  pose proof (rc_mid m FF [] (C8 w0) _ H) as H0.
  pose proof (rc_mid m FF [C8 w0; C8 w1; C8 w2; CB 32 j3] (C8 w4) [] H) as H4.
  pose proof (rc_mid m FF [C8 w0; C8 w1; C8 w2] (CB 32 j3) [C8 w4] H) as H3.
  cbn [cells_size csize] in H0, H4, H3.
  rcfix H0 FF. rcfix H4 (FF + 56). rcfix H3 (FF + 24).
  split; [exact H0|]. split; [exact H4|].
  pose proof H3 as ((WF & _) & _). cbn [cells_wf cell_wf] in WF. destruct WF as (LJ & _).
  pose proof (rw_cells_split_CB bsegs m (FF + 24) [] 32 j3 [] [8; 4; 12; 4; 4]%nat H3 eq_refl) as HS.
  cbn [mk_CB_cells app] in HS.
  pose proof (rc_mid m (FF + 24) [CB 8 _] _ _ HS) as HT.
  pose proof (rc_mid m (FF + 24) [CB 8 _; CB 4 _; CB 12 _] _ _ HS) as HN.
  cbn [cells_size csize] in HT, HN.
  rcfix HT (FF + 32). rcfix HN (FF + 48).
  split; [exact (rc_cb4c4 _ _ _ HT) | exact (rc_cb4c4 _ _ _ HN)].
Qed.

Lemma rc_zsplit : forall m A (z : byte), rw_cells bsegs m A [CB 112 (repeat z 112)] ->
  rw_cells bsegs m A [CB 52 (repeat z 52)] /\ rw_cells bsegs m (A + 52) [CB 60 (repeat z 60)].
Proof.
  intros m A z H.
  assert (H2 : rw_cells bsegs m A [CB 52 (repeat z 52); CB 60 (repeat z 60)]).
  { eapply rw_cells_recast; [exact H| | reflexivity| reflexivity].
    cbn [cells_wf cell_wf]. rewrite !repeat_length. tauto. }
  pose proof (rc_mid m A [] _ _ H2) as K1. pose proof (rc_mid m A [CB 52 (repeat z 52)] _ [] H2) as K2.
  cbn [cells_size csize] in K1, K2.
  rcfix K1 A. rcfix K2 (A + 52).
  split; assumption.
Qed.

Lemma rc_c1_at : forall m A (b0 b1 b2 b3 b4 b5 b6 b7 : byte),
  rw_cells bsegs m A [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7] ->
  rw_cells bsegs m (A + 4) [C1 b4] /\ rw_cells bsegs m (A + 6) [C1 b6].
Proof.
  intros m A b0 b1 b2 b3 b4 b5 b6 b7 H.
  pose proof (rc_mid m A [C1 b0; C1 b1; C1 b2; C1 b3] _ _ H) as K4.
  pose proof (rc_mid m A [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5] _ _ H) as K6.
  cbn [cells_size csize] in K4, K6.
  rcfix K4 (A + 4). rcfix K6 (A + 6).
  split; assumption.
Qed.

Lemma rc_c14_unp : forall m A, rw_cells bsegs m (Z.shiftr A 3 + ASHOFF) [C1 (Z_to_bv 8 4)] -> A mod 8 = 0 ->
  0 <= A -> A + 8 <= 2^47 -> unpoisoned m A (A + 4).
Proof.
  intros m A H A8 A0 AH.
  split; [lia|]. split; [lia|]. intros G H0 H1 H2.
  assert (EG : G = A / 8) by (Z.div_mod_to_equations; lia). subst G.
  exists (Z_to_bv 8 4). split.
  - rewrite Z.shiftr_div_pow2 in H by lia. change (2^3) with 8 in H.
    replace (ASHOFF + A / 8) with (A / 8 + ASHOFF) by lia.
    apply (rw_C1_high m _ _ H). unfold ASHOFF. Z.div_mod_to_equations; lia.
  - right. assert (SV : sval (Z_to_bv 8 4) = 4) by (vm_compute; reflexivity). rewrite SV.
    Z.div_mod_to_equations; lia.
Qed.

Lemma rc_srcin : forall LB S src, src_inA LB S src -> 0 < Z.of_nat (length src) ->
  exists p A n, In (HB p A n) LB /\ A <= S /\ S + Z.of_nat (length src) <= A + n.
Proof. intros LB S src H Hz. exact (H Hz). Qed.

Lemma rc_lift : forall LB SP SP' F a, SP' <= SP -> aclient_addr CI LB SP a -> aclient_addr CI (FB0 F :: LB) SP' a.
Proof.
  intros LB SP SP' F a HS [A1|[A2|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
  - left; lia.
  - right; left; exact A2.
  - right; right; left; exists b; split; [right; exact Hb| exact Hr].
  - right; right; right; exists a'; split; [|reflexivity].
    destruct Ha' as [X|[X|(cls & A & n & Hb & Hr)]]; [left; exact X| right; left; exact X|].
    right; right; exists cls, A, n; split; [right; exact Hb| exact Hr].
Qed.

Lemma rc_mgq : forall LB SC SPV FF W DT n pdt pw lo m3 m',
  FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> ablk W (W + 8704) -> W + 8704 <= ATOP ->
  (FF + 64 <= W \/ W + 8704 <= FF) -> (FF + 64 <= DT \/ DT + n <= FF) -> (DT + n <= W \/ W + 8704 <= DT) ->
  In (HB pdt DT n) LB -> In (HB pw W 8704) LB -> ATOP + 4096 <= lo -> lo <= SC -> SPV <= 2^47 ->
  magree bsegs (fun a => aclient_addr CI (FB0 FF :: LB) SC a /\ ~ (W + 992 <= a < W + 992 + 256) /\ ~ (W + 624 <= a < W + 624 + 52)
     /\ ~ (FF + 48 <= a < FF + 48 + 4) /\ ~ (FF + 32 <= a < FF + 32 + 4) /\ ~ (W + 1248 <= a < W + 1248 + 876)) m3 m' ->
  magree bsegs (fun a => (SC <= a < SPV) \/ (FF <= a < FF + 8) \/ (FF + 56 <= a < FF + 64)
                \/ (Z.shiftr FF 3 + ASHOFF <= a < Z.shiftr FF 3 + ASHOFF + 8)
                \/ (DT <= a < DT + n) \/ (W + 676 <= a < W + 736)) m3 m'.
Proof.
  intros LB SC SPV FF W DT n pdt pw lo m3 m' F64 FH FTOP ABW WTOP WFD DFD DWD HDT HWB BOT LOS SP47 MG'.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd).
  pose proof (ablk_lin _ _ ABW) as (ABWa & ABWb & ABWc & ABWd).
  assert (FFq : FF = 8 * Z.shiftr FF 3) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  pose proof (x2c_shad8_disj FF FF 64 F64 ltac:(lia) ltac:(lia) FH) as SFD. unfold shad in SFD.
  eapply magree_mono; [exact MG'|]. intros a Ha. cbv beta.
  destruct Ha as [H|[H|[H|[H|[H|H]]]]].
  - split; [left; lia|]. repeat split; intro; lia.
  - split; [right; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|]. repeat split; intro; lia.
  - split; [right; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|]. repeat split; intro; lia.
  - assert (SA : shad (8 * (a - ASHOFF)) = a) by (rewrite shad_div, Z.mul_comm, Z.div_mul by lia; lia).
    pose proof (x2c_shad_band W 8704 (8 * (a - ASHOFF)) ABW ltac:(lia)) as XB. rewrite SA in XB.
    split; [right; right; right; exists (8 * (a - ASHOFF)); split; [right; right; exists 0, FF, 64; split; [left; reflexivity| lia]| exact (eq_sym SA)]|].
    repeat split; intro; lia.
  - split; [right; right; left; exists (HB pdt DT n); split; [right; exact HDT| cbn; lia]|].
    repeat split; intro; lia.
  - split; [right; right; left; exists (HB pw W 8704); split; [right; exact HWB| cbn; lia]|]. repeat split; intro; lia.
Qed.

Lemma rc_mgm : forall LB SPV SC FF W m m3 m',
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  FF mod 64 = 0 -> ablk FF (FF + 64) -> ATOP <= SPV -> SC <= SPV ->
  magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (W + 624 <= a < W + 736)) m m3 ->
  magree bsegs (fun a => aclient_addr CI (FB0 FF :: LB) SC a /\ ~ (W + 992 <= a < W + 992 + 256) /\ ~ (W + 624 <= a < W + 624 + 52)
     /\ ~ (FF + 48 <= a < FF + 48 + 4) /\ ~ (FF + 32 <= a < FF + 32 + 4) /\ ~ (W + 1248 <= a < W + 1248 + 876)) m3 m' ->
  magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (W <= a < W + 8704)) m m'.
Proof.
  intros LB SPV SC FF W m m3 m' LBH FFD F64 FH FS SCS M1 M2.
  apply (magree_trans bsegs _ m m3 m').
  - eapply magree_mono; [exact M1|]. intros a Ha. cbv beta in Ha |- *. destruct Ha as (Ha & Hw). split; [exact Ha| lia].
  - eapply magree_mono; [exact M2|]. intros a Ha. cbv beta in Ha |- *. destruct Ha as (Ha & Hw).
    split; [exact (rc_lift LB SPV SC FF a SCS Ha)|].
    assert (NF : ~ (FF <= a < FF + 64)) by (intro HF; exact (x2c_ff_not_client LB SPV FF a LBH FFD F64 FH FS (or_introl HF) Ha)).
    repeat split; intro; lia.
Qed.

Lemma x2_rscallB : forall (L : alayout) (RNG : footprint)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m m3 : amem) (st : astate) (LB : list ablock) (SPV DT W S flags lo mtl FF hdw : Z) (pdt pw : aptr)
    (src : list Z) (rstk : region) (w : word) (jdt jA jB jC jT jD jE j3 : list byte) (y5 y6 y7 y28 y29 y30 y31 : word),
  (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  ATOP + 4096 <= lo -> lo <= SPV - HUF_RDT_STACK_A2 -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
  rclean m rstk -> r_lo rstk <= lo -> SPV <= r_hi rstk -> ATOP <= r_rlo rstk ->
  hinv_bm m -> (forall a, AHBM_LO <= a < AHBM_HI -> in_ranges CI a) ->
  1 <= mtl <= 12 -> In (HB pdt DT (DTABLE_BYTES mtl)) LB -> In (HB pw W 8704) LB ->
  rw_cells bsegs m DT [C4 w; CB (Z.to_nat (4 * 2^mtl)) jdt] ->
  bytes_at bsegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src -> zlen src < 2^26 -> 16 <= S -> src_inA LB S src ->
  (DT + DTABLE_BYTES mtl <= S \/ S + zlen src <= DT) -> (W + 8704 <= S \/ S + zlen src <= W) ->
  x2_frameB L RNG st LB m m3 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF W ->
  hdw mod 256 = mtl -> 0 <= hdw < 2^32 -> hdw / 2^24 = mtl ->
  rw_cells bsegs m3 (SPB SPV - 16) [C8 (Z_to_bv 64 876); C8 (Z_to_bv 64 flags)] ->
  rw_cells bsegs m3 (SPB SPV) (X2BFRA0 FF DT W jA jB jC jT jD jE) ->
  rw_cells bsegs m3 FF (X2BFFHDR (fflag L 0 FF) j3) ->
  rw_cells bsegs m3 (W + 624) [CB 112 (repeat (Z_to_bv 8 0) 112)] ->
  evtF bsegs RNG
    (fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : Z) (m1 : amem) (j0 : word) (dtb : list byte),
       ms' = MS (mkR (Z_to_bv 64 (X2B_ENTRY + 508)) (Z_to_bv 64 (SPB SPV - 16)) gp tp t0 t1 t2 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPB SPV))
                     (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 S) (Z_to_bv 64 X2C_S3) (Z_to_bv 64 hdw) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 W)
                     (Z_to_bv 64 (W + 992)) (Z_to_bv 64 flags) (Z_to_bv 64 (W + 624)) (Z_to_bv 64 (FF + 32)) t3 t4 t5 t6)
                FR (Z_to_bv 64 (X2B_ENTRY + 508)) fc None m1 (seg_rom bsegs)
       /\ x2_postB L RNG st LB m m1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF W DT mtl hdw r src jA jB jC jT jD jE j0 dtb)
    (MS (mkR (Z_to_bv 64 (X2B_ENTRY + 508)) (Z_to_bv 64 (SPB SPV - 16)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPB SPV))
             (Z_to_bv 64 (W + 992)) (Z_to_bv 64 256) (Z_to_bv 64 (W + 624)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32))
             (Z_to_bv 64 S) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 (W + 1248))
             (Z_to_bv 64 S) (Z_to_bv 64 X2C_S3) (Z_to_bv 64 hdw) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 W)
             (Z_to_bv 64 (W + 992)) (Z_to_bv 64 flags) (Z_to_bv 64 (W + 624)) (Z_to_bv 64 (FF + 32)) y28 y29 y30 y31)
        FR (Z_to_bv 64 AHUF_RSTATS) fc None m3 (seg_rom bsegs)).
Proof.
  intros L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m3 st LB SPV DT W S flags lo mtl FF hdw pdt pw src rstk w
    jdt jA jB jC jT jD jE j3 y5 y6 y7 y28 y29 y30 y31
    NOF LBH BOT LO SPT SP16 TP RSTK RAI RAS RFS RRS RCL RLOS RHIS RRLO HBM CIBM HMTL HDT HWB DTC SB SF SL S16 SIN DTSD WSD
    FRM HD1 HD2 HD3 STK3 FRA3 FFH3 Z3.
  destruct FRM as (F64 & FH & FTOP & RF & RSF & FFD & AH3 & MG3 & MI3 & SAV3 & SH3 & STL3 & STG3).
  pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH3) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (spb_props SPV SP16) as (SPAB & SPA32 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd).
  destruct (hb_unpoisoned AI L RNG st (FB0 FF :: LB) m3 pw W 8704 AH3 (or_intror HWB)) as (_ & W16 & _ & ABW & WTOP & _ & _ & WRW3).
  pose proof (ablk_lin _ _ ABW) as (ABWa & ABWb & ABWc & ABWd).
  pose proof (FFD _ HWB) as WFD. cbn [ab_addr ab_size] in WFD.
  unfold HUF_RDT_STACK_A2 in LO.
  destruct (rc_ffsplit m3 FF _ _ _ _ j3 FFH3) as (FC0 & FC56 & (tlv & TLC) & (nsv & NSC)).
  destruct (rc_zsplit m3 (W + 624) _ Z3) as (ZR & Z60). rcfix Z60 (W + 676).
  destruct (rc_u8 _ _ _ _ ZR) as (RKU & RKL).
  pose proof (rc_mid m3 (SPB SPV - 16) [] _ _ STK3) as STA. cbn [cells_size csize] in STA. rcfix STA (SPB SPV - 16).
  assert (WH : wr_at bsegs m3 (W + 992) 256) by (eapply wr_at_sub; [exact WRW3|..]; lia).
  assert (EXH : exists bs, length bs = Z.to_nat 256 /\ rw_cells bsegs m3 (W + 992) [CB (Z.to_nat 256) bs]).
  { eapply Shadow.rw_cells_of_wr_at; [exact WH| apply no_image_asan; unfold AIMG_HI in *; lia| lia]. }
  destruct EXH as (jh & JHL & JHC). destruct (rc_u8 _ _ _ _ JHC) as (HWU & _).
  assert (WW : wr_at bsegs m3 (W + 1248) 876) by (eapply wr_at_sub; [exact WRW3|..]; lia).
  assert (EXW : exists bs, length bs = Z.to_nat 876 /\ rw_cells bsegs m3 (W + 1248) [CB (Z.to_nat 876) bs]).
  { eapply Shadow.rw_cells_of_wr_at; [exact WW| apply no_image_asan; unfold AIMG_HI in *; lia| lia]. }
  destruct EXW as (jw & JWL & JWC). destruct (rc_u8 _ _ _ _ JWC) as (WWU & _).
  destruct (rc_c1_at _ _ _ _ _ _ _ _ _ _ SH3) as (SH4 & SH6).
  assert (E4 : Z.shiftr (FF + 32) 3 = Z.shiftr FF 3 + 4).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. replace (FF + 32) with (FF + 4 * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  assert (E6 : Z.shiftr (FF + 48) 3 = Z.shiftr FF 3 + 6).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. replace (FF + 48) with (FF + 6 * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  rcfix SH4 (Z.shiftr (FF + 32) 3 + ASHOFF). rcfix SH6 (Z.shiftr (FF + 48) 3 + ASHOFF).
  pose proof (rc_c14_unp m3 (FF + 32) SH4 ltac:(lia) ltac:(lia) ltac:(lia)) as UTL.
  pose proof (rc_c14_unp m3 (FF + 48) SH6 ltac:(lia) ltac:(lia) ltac:(lia)) as UNS.
  assert (HBM3 : hinv_bm m3).
  { eapply hinv_bm_magree; [exact MG3| |exact HBM]. intros a Ha. cbv beta.
    split; [exact (hinv_bm_client CI LB SPV a CIBM Ha)|].
    assert (AR : 0 <= (a - ASHOFF) * 8 < 2^47).
    { rewrite !shad_div in Ha. unfold AHBM_LO, AHBM_HI, ASHOFF in *. Z.div_mod_to_equations. lia. }
    pose proof (x2c_shad_band W 8704 ((a - ASHOFF) * 8) ABW AR) as XB.
    rewrite shad_div, Z.div_mul in XB by lia. lia. }
  eapply evtF_cut.
  { eapply (RSK L RNG (Z_to_bv 64 (X2B_ENTRY + 508)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPB SPV))
      (Z_to_bv 64 S) (Z_to_bv 64 X2C_S3) (Z_to_bv 64 hdw) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 W)
      (Z_to_bv 64 (W + 992)) (Z_to_bv 64 flags) (Z_to_bv 64 (W + 624)) (Z_to_bv 64 (FF + 32)) y28 y29 y30 y31 FR fc m3 st
      (FB0 FF :: LB) (SPB SPV - 16) (W + 992) (W + 624) (FF + 48) (FF + 32) S (W + 1248) src jh (repeat (Z_to_bv 8 0) 52) jw
      nsv tlv lo rstk).
    all: try assumption.
    all: try lazymatch goal with
         | |- fake0_lek _ _ => exact (fake0_lek_push0_none FF 64 LB NOF)
         | |- zlen _ = _ => unfold zlen; first [rewrite JHL | rewrite JWL | rewrite RKL]; reflexivity
         | |- AF_huf_tbl_iface.hblk8 _ _ _ => exists pw, W, 8704; split; [right; exact HWB| split; [reflexivity| lia]]
         | |- fcellA _ _ _ _ => split; [exists 0, FF, 64; split; [left; reflexivity| split; [lia| split; [lia| split; [exact FH| Z.div_mod_to_equations; lia]]]]
                                       | first [exact UNS | exact UTL]]
         | |- rng _ (shad _) _ => eapply rng_sub'; [exact RSF| unfold shad; rewrite ?E4, ?E6; lia]
         | |- rng _ _ _ => eapply rng_sub'; [exact RF| lia]
         | |- _ mod _ = 0 => Z.div_mod_to_equations; lia
         | |- forall b, In b _ -> ablk _ _ => intros b [<-|Hb]; [exact FH| exact (LBH b Hb)]
         | |- ?P ?M _ 128 => red; intros a Ha; apply (hinv_bm_zero m3 a HBM3);
                             unfold AF_huf_tbl_iface2.ABIT_MASK, AHBM_LO, AHBM_HI in *; lia
         | |- forall a, _ -> in_ranges _ _ => intros a Ha; apply CIBM; unfold AF_huf_tbl_iface2.ABIT_MASK, AHBM_LO, AHBM_HI in *; lia
         | |- bytes_at _ _ _ _ =>
             eapply bytes_at_magree; [exact MG3| exact SB|]; intros a Ha; cbv beta; rewrite length_map in Ha;
             destruct (rc_srcin _ _ _ SIN ltac:(lia)) as (p & A & n & HIn & HA1 & HA2);
             change (zlen src) with (Z.of_nat (length src)) in WSD;
             split; [right; right; left; exists (HB p A n); split; [exact HIn| cbn; lia]| lia]
         | |- _ -> bufH _ _ _ =>
             intros Hz; destruct (rc_srcin _ _ _ SIN ltac:(exact Hz)) as (p & A & n & HIn & HA1 & HA2);
             exists p, A, n; split; [right; exact HIn| exact (conj HA1 HA2)]
         | |- rclean _ _ =>
             eapply rclean_magreeA; [exact RCL| exact MG3| | exact RRLO]; intros a Ha; cbv beta;
             split; [right; right; right; exists a; split; [left; lia| reflexivity]|];
             pose proof (x2c_shad_band W 8704 a ABW ltac:(lia)); lia
         | |- _ => idtac
         end.
    all: try (unfold AHUF_RSTATS_STACK, zlen in *; lia).
    all: fail. }
  intros ms' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & r & m' & -> & MI' & STL' & MG' & AH' & RR & RS').
  apply evtF_done.
  pose proof (FFD _ HDT) as DFD. cbn [ab_addr ab_size] in DFD.
  pose proof (x2b_dtb_range mtl HMTL) as DTBR.
  assert (NE : HB pdt DT (DTABLE_BYTES mtl) <> HB pw W 8704).
  { intro E. apply (f_equal ab_size) in E. cbn [ab_size] in E. unfold DTABLE_BYTES, HufHarness.DT_BYTES in E.
    assert (P2 : 2^mtl = 2 * 2^(mtl - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia). lia. }
  pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH3 (or_intror HDT) (or_intror HWB) NE) as DWD. cbn [ab_addr ab_size] in DWD.
  unfold DTABLE_BYTES, HufHarness.DT_BYTES in DWD, DFD, DTBR.
  pose proof (rc_mgq LB (SPB SPV - 16) SPV FF W DT (4 * (1 + 2^mtl)) pdt pw lo m3 m' F64 FH FTOP ABW WTOP WFD DFD DWD HDT HWB
                BOT ltac:(lia) ltac:(lia) MG') as MGQ.
  pose proof (rc_mgm LB SPV (SPB SPV - 16) FF W m m3 m' LBH FFD F64 FH ltac:(lia) ltac:(lia) MG3 MG') as MGM.
  destruct (x2c_dtu8 _ _ _ _ _ DTC) as (DTU & DTL).
  assert (LDT : Z.of_nat (length (le4 w ++ jdt)) = 4 * (1 + 2^mtl)).
  { rewrite length_app, DTL. change (length (le4 w)) with 4%nat. rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia. }
  assert (DTU3 : u8arr bsegs m3 DT (le4 w ++ jdt)).
  { eapply rc_u8_mg; [exact MG3| exact DTU|]. rewrite LDT. intros a Ha. cbv beta.
    split; [right; right; left; exists (HB pdt DT (DTABLE_BYTES mtl)); split; [exact HDT|]|].
    - cbn [ab_addr ab_size]. unfold DTABLE_BYTES, HufHarness.DT_BYTES. lia.
    - clear - Ha DWD. lia. }
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, r, m', (Z_to_bv 64 X2B_MAGIC_LIVE), (le4 w ++ jdt).
  split.
  { rewrite ret_pc_even by (unfold X2B_ENTRY in *; lia). reflexivity. }
  unfold x2_postB.
  do 8 (split; [assumption|]).
  split; [exact MGM|].
  split; [exact STL'|].
  split. { eapply stk_magree; [exact MGQ| exact STG3|]. intros a Ha. cbv beta. clear - Ha SPAB. lia. }
  split. { eapply rw_cells_magree; [exact MGQ| exact FRA3|]. intros a Ha. unfold X2BFRA0 in Ha. cbn [cells_size csize] in Ha.
           cbv beta. clear - Ha SPAB. lia. }
  split. { exists (Z_to_bv 64 876), (Z_to_bv 64 flags). eapply rw_cells_magree; [exact MGQ| exact STK3|]. intros a Ha.
           cbn [cells_size csize] in Ha. cbv beta. clear - Ha SPAB. lia. }
  split. { eapply rw_cells_magree; [exact MGQ| exact SAV3|]. intros a Ha. unfold X2BSAVED in Ha. cbn [cells_size csize] in Ha.
           cbv beta. clear - Ha SPAB. lia. }
  split. { eapply rw_cells_magree; [exact MGQ| exact SH3|]. intros a Ha. unfold X2BSH in Ha. cbn [cells_size csize] in Ha.
           cbv beta. clear - Ha. lia. }
  split. { eapply rw_cells_magree; [exact MGQ| exact FC0|]. intros a Ha. cbn [cells_size csize] in Ha.
           cbv beta. clear - Ha. lia. }
  split. { eapply rw_cells_magree; [exact MGQ| exact FC56|]. intros a Ha. cbn [cells_size csize] in Ha.
           cbv beta. clear - Ha. lia. }
  split. { eapply rc_u8_mg; [exact MGQ| exact DTU3|]. rewrite LDT. intros a Ha. cbv beta. clear - Ha. lia. }
  split; [exact LDT|].
  split. { eapply rw_cells_magree; [exact MGQ| exact Z60|]. intros a Ha. cbn [cells_size csize] in Ha.
           cbv beta. clear - Ha. lia. }
  split; [exact HD1|]. split; [exact HD2|]. split; [exact HD3|]. split; [exact RR|]. exact RS'.
Qed.

Lemma x2_rsB : forall (L : alayout) (RNG : footprint)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m m3 : amem) (st : astate) (LB : list ablock) (SPV DT W S flags lo mtl FF hdw : Z) (pdt pw : aptr)
    (src : list Z) (rstk : region) (w : word) (jdt jA jB jC jT jD jE j3 : list byte) (y5 y6 y7 y28 y29 y30 y31 : word),
  (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  ATOP + 4096 <= lo -> lo <= SPV - HUF_RDT_STACK_A2 -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
  rclean m rstk -> r_lo rstk <= lo -> SPV <= r_hi rstk -> ATOP <= r_rlo rstk ->
  hinv_bm m -> (forall a, AHBM_LO <= a < AHBM_HI -> in_ranges CI a) ->
  1 <= mtl <= 12 -> In (HB pdt DT (DTABLE_BYTES mtl)) LB -> In (HB pw W 8704) LB ->
  rw_cells bsegs m DT [C4 w; CB (Z.to_nat (4 * 2^mtl)) jdt] ->
  bytes_at bsegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src -> zlen src < 2^26 -> 16 <= S -> src_inA LB S src ->
  (DT + DTABLE_BYTES mtl <= S \/ S + zlen src <= DT) -> (W + 8704 <= S \/ S + zlen src <= W) ->
  x2_frameB L RNG st LB m m3 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF W ->
  hdw mod 256 = mtl -> 0 <= hdw < 2^32 -> hdw / 2^24 = mtl ->
  rw_cells bsegs m3 (SPB SPV - 16) [C8 (Z_to_bv 64 876); C8 (Z_to_bv 64 flags)] ->
  rw_cells bsegs m3 (SPB SPV) (X2BFRA0 FF DT W jA jB jC jT jD jE) ->
  rw_cells bsegs m3 FF (X2BFFHDR (fflag L 0 FF) j3) ->
  rw_cells bsegs m3 (W + 624) [CB 112 (repeat (Z_to_bv 8 0) 112)] ->
  (forall (m5 : amem) (r' tl nbs : Z) (hw rank : list Z) (j0' : word) (z1 z5 z6 z7 z14 z15 z16 z17 z28 z29 z30 z31 : word),
     x2_okB L RNG st LB m m5 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF W DT mtl hdw r' tl nbs hw rank j0' ->
     evtF bsegs RNG (huf_rdt_postA AI huf_dt_okA L RNG ra (Z_to_bv 64 SPV) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB
                       DT W mtl lo m)
       (MS (mkR z1 (Z_to_bv 64 (SPB SPV)) gp tp z5 z6 z7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPB SPV))
                (Z_to_bv 64 (-44)) (Z_to_bv 64 r') (Z_to_bv 64 mtl) (Z_to_bv 64 tl) z14 z15 z16 z17
                (Z_to_bv 64 S) (Z_to_bv 64 X2C_S3) (Z_to_bv 64 hdw) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 W)
                (Z_to_bv 64 (W + 992)) (Z_to_bv 64 flags) (Z_to_bv 64 (W + 624)) (Z_to_bv 64 (FF + 32)) z28 z29 z30 z31)
           FR (Z_to_bv 64 (X2B_ENTRY + 544)) fc None m5 (seg_rom bsegs))) ->
  evtF bsegs RNG (huf_rdt_postA AI huf_dt_okA L RNG ra (Z_to_bv 64 SPV) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB
                    DT W mtl lo m)
    (MS (mkR (Z_to_bv 64 (X2B_ENTRY + 508)) (Z_to_bv 64 (SPB SPV - 16)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPB SPV))
             (Z_to_bv 64 (W + 992)) (Z_to_bv 64 256) (Z_to_bv 64 (W + 624)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32))
             (Z_to_bv 64 S) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 (W + 1248))
             (Z_to_bv 64 S) (Z_to_bv 64 X2C_S3) (Z_to_bv 64 hdw) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 W)
             (Z_to_bv 64 (W + 992)) (Z_to_bv 64 flags) (Z_to_bv 64 (W + 624)) (Z_to_bv 64 (FF + 32)) y28 y29 y30 y31)
        FR (Z_to_bv 64 AHUF_RSTATS) fc None m3 (seg_rom bsegs)).
Proof.
  intros L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m3 st LB SPV DT W S flags lo mtl FF hdw pdt pw src rstk w
         jdt jA jB jC jT jD jE j3 y5 y6 y7 y28 y29 y30 y31 NOF LBH BOT LO SPT SP16 TP RSTK RI RISH RFS RRS RCL RLO RHI RRLO HBM CIBM
         HMTL HDT HWB DTC SRC SRCB SRCL S16 SRCA SDT SW FRM HHM HHR HDV C16 FRA FFH ZC KOK.
  eapply evtF_cut.
  { eapply x2_rscallB; eassumption. }
  intros ms' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & r & m1 & j0 & dtb & EQ & PB). subst ms'.
  eapply x2_rsretB; [exact PB| exact LBH| exact BOT| exact LO| exact SPT| exact SP16| exact RSTK| exact RI| exact TP| exact HMTL
                    | exact HDT| exact HWB| exact SRCB|].
  exact KOK.
Qed.

End Asm.
End CANSEC1.
