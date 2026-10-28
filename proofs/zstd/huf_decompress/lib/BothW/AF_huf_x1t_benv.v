From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AFake0k_iface AProg_kit
     AFake_arep FsKit AF_fse_rd_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AH_huf_kit AH_huf_iface
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t_top AF_huf_x1t_bseg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma x1b_shad_band : forall X n a, ablk X (X + n) -> 0 <= a < 2^47 -> ~ (X <= shad a < X + n).
Proof.
  intros X n a H Ha. pose proof (shad_in_band a Ha) as SB. unfold ablk in H. unfold KLS, AIMG_HI in *.
  pose proof atop_range as ATR. lia.
Qed.

Lemma x1b_shad8_disj : forall FF X n, FF mod 64 = 0 -> 0 <= FF -> FF + 64 <= 2^47 -> ablk X (X + n) ->
  X + n <= shad FF \/ shad FF + 8 <= X.
Proof.
  intros FF X n F64 F0 F47 H. pose proof (shad_in_band FF ltac:(lia)) as S1. pose proof (shad_in_band (FF + 63) ltac:(lia)) as S2.
  assert (E : shad (FF + 63) = shad FF + 7) by (rewrite !shad_div; Z.div_mod_to_equations; lia).
  unfold ablk in H. unfold KLS, AIMG_HI in *. pose proof atop_range. lia.
Qed.

Lemma x1b_shad_same : forall a x, 0 <= a -> 0 <= x -> shad a = shad x -> a / 8 = x / 8.
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

Lemma x1b_fresh_not_client : forall LB SPV X n a,
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
    exact (x1b_shad_band X n a' XH A47 HA).
Qed.

Lemma x1b_ff_not_client : forall LB SPV FF a,
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
    + exact (x1b_shad_band FF 64 a' FH (A47 a' Ha') HA).
  - assert (SHI : exists x, FF <= x < FF + 64 /\ shad x = a).
    { exists (FF + 8 * (a - shad FF)). split; [lia|]. rewrite !shad_div in *. Z.div_mod_to_equations. lia. }
    destruct SHI as (x & Hx & <-).
    pose proof (shad_in_band x ltac:(lia)) as SB.
    destruct AC as [AC|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & E)]]].
    + unfold KLS in *. lia.
    + pose proof (HCI iv Hiv). unfold KLS, AIMG_HI in *. lia.
    + exact (x1b_shad_band _ _ x (LBH b Hb) ltac:(lia) Hr).
    + pose proof (A47 a' Ha') as B'.
      pose proof (x1b_shad_same a' x ltac:(lia) ltac:(lia) (eq_sym E)) as E8.
      assert (IN : FF <= a' < FF + 64) by (Z.div_mod_to_equations; lia).
      destruct Ha' as [H|[(iv & Hiv & Hr)|(cls & FA & fn & Hb & Hr)]].
      * lia.
      * pose proof (HCI iv Hiv). lia.
      * destruct (FFD _ Hb) as [D|D]; cbn in D; lia.
Qed.

Definition x1_frameB (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (m m3 : amem)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SPV lo FF : Z) : Prop :=
  FF mod 64 = 0 /\ ablk FF (FF + 64) /\ FF + 64 <= ATOP /\ rng RNG FF 64 /\ rng RNG (shad FF) 8
  /\ (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF)
  /\ AHEAP AI L RNG st (FB0 FF :: LB) m3
  /\ magree bsegs (aclient_addr CI LB SPV) m m3 /\ mem_inv bsegs m3
  /\ rw_cells bsegs m3 (SPV + -104) (X1SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
  /\ rw_cells bsegs m3 (Z.shiftr FF 3 + 2147450880) X1SH
  /\ stk bsegs m3 lo (SPA1 SPV - 16) /\ stk bsegs m3 (SPA1 SPV + 216) (SPV + -104).

Lemma x1_openB : forall (L : alayout) (RNG : footprint)
    (ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
    (SPV DT W S size flags lo : Z) (Q : machine_state -> Prop),
  AHEAP AI L RNG st LB m -> (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  stk bsegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - HUF_RDT_STACK_A2 ->
  SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  4096 <= W -> W < 2^47 -> W mod 4 = 0 -> 4096 <= DT -> DT + 4 < 2^47 ->
  (forall (FF : Z) (m3 : amem) (jA jC jD jB jE j3 j5 j6 : list byte) (y6 y7 y28 y29 y30 y31 : word),
     x1_frameB L RNG st LB m m3 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF ->
     rw_cells bsegs m3 (SPA1 SPV - 16) [C8 (Z_to_bv 64 876); C8 (Z_to_bv 64 flags)] ->
     rw_cells bsegs m3 (SPA1 SPV) (X1FRA FF DT W jA jC jD jB jE) ->
     rw_cells bsegs m3 FF (X1FFHDR (fflag L 0 FF) j3 j5 j6 (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
     evtF bsegs RNG Q
       (MS (mkR (Z_to_bv 64 0x80454) (Z_to_bv 64 (SPA1 SPV - 16)) gp tp (Z_to_bv 64 FF) y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA1 SPV))
                (Z_to_bv 64 (W + 1236)) (Z_to_bv 64 256) (Z_to_bv 64 W) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32))
                (Z_to_bv 64 S) (Z_to_bv 64 size) (Z_to_bv 64 (W + 104))
                (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) s4 (Z_to_bv 64 (W + 1236)) (Z_to_bv 64 18446744073709551572)
                (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 size) (Z_to_bv 64 S) (Z_to_bv 64 flags) (Z_to_bv 64 (FF + 48)) y28 y29 y30 y31)
           FR (Z_to_bv 64 0x9733c) fc None m3 (seg_rom bsegs))) ->
  evtF bsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 S) (Z_to_bv 64 size) (Z_to_bv 64 W)
             (Z_to_bv 64 8704) (Z_to_bv 64 flags) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 AHUF_RDT_X1) fc None m (seg_rom bsegs)).
Proof.
  intros L RNG ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB
         SPV DT W S size flags lo Q AH NOF LBH ST BOT LO SPT SP16 MI TP RSTK RI RFS WL WH W4 DTL DTH KC.
  pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (spa1_props SPV SP16) as (SPAB & SPA32 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  assert (BB : forall b, In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP)
    by (intros b Hb; exact (AI_block_bounds AI _ _ _ _ _ b AH Hb)).
  pose proof SM0K as SMK. unfold stack_malloc_0k_stmt in SMK.
  unfold HUF_RDT_STACK_A2 in LO.
  assert (LOS : lo <= SPV - 336 - 4096 - 16) by lia.
  assert (LOC : ATOP <= lo) by lia.
  assert (SPK : SPV + 16 < KEND) by (unfold KEND; lia).
  assert (RSTK' : rng RNG lo (SPV - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
  destruct RTC as (C0 & GOT & RIC & REAL & SHB & SUA & _).
  pose proof (AI_relro AI _ _ _ _ _ AH) as REL.
  assert (GSU : rw_cells bsegs m AGOT_SUAR_R [C8 (Z_to_bv 64 0xba300)]).
  { unfold AGOT_SUAR_R. eapply relro_wordA; [exact REL| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]. }
  unfold AHUF_RDT_X1.
  eapply evtF_cut.
  { eapply x1_pro; first [exact ST| exact MI| exact GOT| exact SHB| exact GSU| exact SUA| exact SP16| exact LOS| exact LOC
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
  intros ms' HP. unfold sm0k_post in HP. destruct HP as (FF & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & j0 & j1 & j2 & junk &
                        -> & MI2 & STL2 & AP2 & AH2 & F64 & FH & FC & FFC & SHF & RF & RSF).
  rewrite unsigned_lit in STL2, AP2 by lia.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd).
  assert (FFD : forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF).
  { intros b Hb. assert (NE : FB0 FF <> b) by (intro E; subst b; exact (NOF FF 64 Hb)).
    destruct (AI_blocks_disjoint AI _ _ _ _ _ (FB0 FF) b AH2 ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as [D|D];
      cbn in D; lia. }
  assert (FRB2 : rw_cells bsegs m2 (SPV + -104) (X1SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply aheap_pres_rw_cells; [exact AP2| exact FRB1|]. left; left. cbn. lia. }
  assert (FRA2 : rw_cells bsegs m2 (SPA1 SPV) [CB 96 jA; C8 (Z_to_bv 64 W); CB 112 jB]).
  { eapply aheap_pres_rw_cells; [exact AP2| exact FRA1|]. left; left. cbn. lia. }
  assert (STG2 : stk bsegs m2 (SPA1 SPV + 216) (SPV + -104)).
  { eapply aheap_pres_stk; [exact AP2| exact STG1| lia| lia]. }
  clear FRB1 FRA1 STG1.
  pose proof (AI_relro AI _ _ _ _ _ AH2) as REL2.
  assert (GPC : rw_cells bsegs m2 AGOT_X1PC [C8 (Z_to_bv 64 0x80298)]).
  { unfold AGOT_X1PC. eapply relro_wordA; [exact REL2| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]. }
  assert (RP : ret_pc (Z_to_bv 64 0x80320) = Z_to_bv 64 0x80320) by (apply ret_pc_even; lia).
  rewrite RP.
  eapply evtF_cut; [| cbv beta; intros ms' HQ; exact HQ].
  eapply x1_hdr with (Q := fun ms => evtF bsegs RNG Q ms) (FLG := fflag L 0 FF) (DT := DT) (WK := W) (wksz := 8704)
    (SRC := S) (n := size) (j0 := j0) (j1 := j1) (j2 := j2) (junk := junk) (jA := jA) (jB := jB);
    first [exact FRA2| exact STL2| exact FFC| exact SHF| exact GPC| exact MI2| exact FH| exact FC| exact F64| exact RF| exact RSF
          | exact SP16| exact LOS| exact LOC| exact SPK| exact RSTK'| exact RI| exact WL| exact WH| exact W4| exact DTL| exact DTH
          | lia| idtac].
  intros m3 jA' jC jD jB' jE j3 j5 j6 H1492 MU3 WM3 MI3 FRA3 STL3 ARG3 FFH3 SH3.
  assert (OUT3 : forall a, aclient_addr CI LB SPV a ->
            outside [(SPA1 SPV - 16, SPA1 SPV + 216); (FF, FF + 56); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] a).
  { intros a Ha. assert (SH8 : shad FF = Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
    cbn [outside]. split; [|split; [|split; [|exact I]]].
    - intros HIN. exact (stack_not_client CI LB SPV (SPA1 SPV - 16) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha).
    - intros HIN. exact (x1b_ff_not_client LB SPV FF a LBH FFD F64 FH ltac:(lia) ltac:(left; lia) Ha).
    - rewrite <- SH8. intros HIN. exact (x1b_ff_not_client LB SPV FF a LBH FFD F64 FH ltac:(lia) ltac:(right; lia) Ha). }
  assert (MG3 : magree bsegs (fun a => outside [(SPA1 SPV - 16, SPA1 SPV + 216); (FF, FF + 56);
                                              (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] a) m2 m3)
    by (apply magree_of_munch; [exact MU3| exact WM3]).
  assert (SHB8 : 2147450880 <= Z.shiftr FF 3 + 2147450880 < SPA1 SPV - 16).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold KLS, AIMG_HI in *. Z.div_mod_to_equations. lia. }
  assert (AP3 : aheap_pres CI LB SPV m2 m3) by (eapply aheap_pres_of_munch; [exact MU3| exact WM3| exact OUT3]).
  assert (APT : aheap_pres CI LB SPV m m3).
  { eapply aheap_pres_trans; [exact AP1|]. eapply aheap_pres_trans; [| exact AP3].
    eapply aheap_pres_weaken; [exact AP2| lia| intros b Hb; exact Hb]. }
  cbv beta. eapply KC.
  + unfold x1_frameB. split; [exact F64|]. split; [exact FH|]. split; [exact FC|]. split; [exact RF|]. split; [exact RSF|].
    split; [exact FFD|].
    split.
    { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      - left; left. cbn. lia.
      - right; left. exists (FB0 FF). split; [left; reflexivity| cbn; lia].
      - right; right. right; right. exists 0, FF, 64. split; [left; reflexivity|]. cbn [fst snd].
        unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
    split; [exact APT|].
    split; [exact MI3|].
    split; [eapply rw_cells_magree; [exact MG3| exact FRB2|]; intros a Ha; unfold X1SAVED in Ha; cbn in Ha; cbn [outside]; lia|].
    split; [exact SH3|].
    split; [exact STL3|].
    eapply stk_magree; [exact MG3| exact STG2|]. intros a Ha. cbn [outside]. lia.
  + exact ARG3.
  + exact FRA3.
  + exact FFH3.
Qed.

Lemma x1_closeB : forall (L : alayout) (RNG : footprint)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m m4 : amem) (st : astate) (LB : list ablock) (SPV DT W mtl lo FF rv : Z) (pdt : aptr) (j0 : word)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  AHEAP AI L RNG st (FB0 FF :: LB) m4 ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  magree bsegs (PAGx AI LB SPV DT mtl W) m m4 -> mem_inv bsegs m4 ->
  rw_cells bsegs m4 (Z.shiftr FF 3 + 2147450880) X1SH ->
  rw_cells bsegs m4 FF [C8 j0] -> rw_cells bsegs m4 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))] ->
  rw_cells bsegs m4 (SPV + -104) (X1SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells bsegs m4 (SPA1 SPV + 24) [C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF)] ->
  stk bsegs m4 lo (SPA1 SPV + 24) -> stk bsegs m4 (SPA1 SPV + 40) (SPV + -104) ->
  ATOP + 4096 <= lo -> lo <= SPV - HUF_RDT_STACK_A2 -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
  1 <= mtl <= 12 -> In (HB pdt DT (DTABLE_BYTES mtl)) LB ->
  0 <= rv < 2^64 -> (rv < 2^64 - 119 -> huf_dt_okA m4 DT mtl) ->
  evtF bsegs RNG (huf_rdt_postA AI huf_dt_okA L RNG ra (Z_to_bv 64 SPV) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB
                    DT W mtl lo m)
    (MS (mkR x1 (Z_to_bv 64 (SPA1 SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA1 SPV)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) x19 x20 x21 (Z_to_bv 64 rv) x23 x24 x25 x26 x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 0x80618) fc None m4 (seg_rom bsegs)).
Proof.
  intros L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m4 st LB SPV DT W mtl lo FF rv pdt j0
         x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31
         AH LBH F64 FH FC RF RSF FFD MG MI SHF FF0 FF56 FRB FRA STL STG BOT LO SPT SP16 RSTK RI HMTL HDT HR HOK.
  pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (spa1_props SPV SP16) as (SPAB & SPA32 & _).
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd).
  unfold HUF_RDT_STACK_A2 in LO.
  assert (LOS : lo <= SPV - 336 - 4096 - 16) by lia.
  assert (LOC : ATOP <= lo) by lia.
  assert (SPK : SPV + 16 < KEND) by (unfold KEND; lia).
  assert (RSTK' : rng RNG lo (SPV - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
  destruct (FFLAG L RNG st (FB0 FF :: LB) m4 0 FF 64 AH ltac:(left; reflexivity)) as (FLC & RG & GH & GC & GD & GCI).
  assert (GF : fflag L 0 FF + 1 <= FF \/ FF + 64 <= fflag L 0 FF)
    by (destruct (GD (FB0 FF) ltac:(left; reflexivity)) as [D|D]; cbn in D; lia).
  assert (GLB : forall b, In b LB -> fflag L 0 FF + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L 0 FF)
    by (intros b Hb; exact (GD b ltac:(right; exact Hb))).
  pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd).
  assert (SH8 : shad FF = Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  eapply evtF_cut.
  { eapply x1_epi with (FLG := fflag L 0 FF); first [exact SHF| exact FF0| exact FF56| exact FLC| exact FRB| exact FRA
       | exact STL| exact STG| exact MI| exact FH| exact FC| exact F64| exact GH| exact GC| exact GF| exact RF| exact RSF
       | exact RG| exact HR| exact SP16| exact SPK| exact LOS| exact LOC| exact RSTK'| exact RI]. }
  cbv beta. intros ms' (mp & m' & x10' & x12' & -> & MU1 & WM1 & MIp & MU2 & WM2 & MI' & ST' & FL0).
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
  assert (OUTW : forall a, PAGx AI LB SPV DT mtl W a ->
            outside [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] a
            /\ outside [(fflag L 0 FF, fflag L 0 FF + 1)] a).
  { intros a (Ha & _ & _). cbn [outside]. rewrite <- SH8. split; [split; [|split; [|exact I]]| split; [|exact I]].
    - intros HIN. exact (x1b_ff_not_client LB SPV FF a LBH FFD F64 FH ltac:(lia) ltac:(right; lia) Ha).
    - intros HIN. exact (x1b_ff_not_client LB SPV FF a LBH FFD F64 FH ltac:(lia) ltac:(left; lia) Ha).
    - intros HIN. exact (x1b_fresh_not_client LB SPV (fflag L 0 FF) 1 a LBH GH GLB ltac:(lia) ltac:(lia) Ha). }
  assert (DTH : ablk DT (DT + DTABLE_BYTES mtl)) by (exact (LBH _ HDT)).
  pose proof (x1b_shad8_disj FF DT (DTABLE_BYTES mtl) F64 ltac:(lia) ltac:(lia) DTH) as DS.
  pose proof (FFD _ HDT) as DF. pose proof (GLB _ HDT) as DG. cbn in DF, DG.
  apply evtF_done. unfold huf_rdt_postA.
  exists x5, x6, x7, x10', x12', x13, x14, x15, x16, x17, x28, x29, x30, x31, rv, m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [rewrite unsigned_lit by lia; exact ST'|].
  split.
  { rewrite unsigned_lit by lia. change (magree bsegs (PAGx AI LB SPV DT mtl W) m m').
    eapply magree_munch_step; [eapply magree_munch_step; [exact MG| exact MU1| exact WM1|] | exact MU2| exact WM2|].
    - intros a Ha. exact (proj1 (OUTW a Ha)).
    - intros a Ha. exact (proj2 (OUTW a Ha)). }
  split; [exact AH'|]. split; [exact HR|].
  intros HE. specialize (HOK HE).
  eapply huf_dt_okA_transport; [eapply huf_dt_okA_transport; [exact HOK| exact MU1| exact HMTL|] | exact MU2| exact HMTL|].
  - cbn [disjoint_from]. rewrite <- SH8. repeat split; lia.
  - cbn [disjoint_from]. repeat split; lia.
Qed.

End Asm.
End CANSEC1.
