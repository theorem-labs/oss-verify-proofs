(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree StrFun Stdio_pure.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AHarness_iface Stdio_kit AH_fi_iface AF_fi_kit
     AF_fi_gfha_iface AF_fi_ffsi_iface AF_fi_chk AF_fi_fdsC.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
#[using="Type"] Lemma buf_atA_skipn : forall m S bl k, buf_atA m S bl -> 0 <= k <= zlen bl -> buf_atA m (S + k) (skipn (Z.to_nat k) bl).
Proof.
  intros m S bl k [B F] Hk. split.
  - rewrite <- (firstn_skipn (Z.to_nat k) bl) in B. rewrite map_app in B.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in B. destruct B as [_ B].
    rewrite length_map, length_firstn in B. Local Ltac2 Set LiaHints.tbl := fun () => "0010=18147260095.8000004S2Hk".
replace (Z.of_nat (Nat.min (Z.to_nat k) (length bl))) with k in B by lia. exact B.
  - apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) F x). revert Hx. generalize (Z.to_nat k). clear.
    induction bl as [|y bl IH]; intros [|n] H; cbn in H; try exact H; [right; exact (IH n H)].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma zlen_skipnA : forall (bl : list Z) k, 0 <= k <= zlen bl -> zlen (skipn (Z.to_nat k) bl) = zlen bl - k.
Proof. intros bl k Hk. rewrite length_skipn. Local Ltac2 Set LiaHints.tbl := fun () => "0010=68659354476.4000004S2Hk".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma rclean_magreeF : forall (P : Z -> Prop) (m m' : amem), magree asegs P m m' ->
  forall r, (forall a, shad (r_rlo r) <= a < shad (r_rhi r) -> P a) -> rclean m r -> rclean m' r.
Proof.
  intros P m m' AG r HP [(U & HL & W & AB) LT]. pose proof HL as (H1 & H2 & H3 & H4 & H5 & H6). split; [| exact LT].
  split; [| split; [exact HL| split; [| exact AB]]].
  - eapply unpoisoned_agree; [exact U|].
    intros s Hs.
    assert (HPs : P s).
    { apply HP. pose proof (shad_mono (r_rlo r) (r_lo r) H1). Local Ltac2 Set LiaHints.tbl := fun () => "0050>16312776828.2218614384517.2325530187010.2347283162864.2152792927696.2000000400D00P00T00XS2H4S2H12H22H52H62HsS2Hs1H2H02H7S2H2S2Ha".
pose proof (shad_mono (r_hi r - 1) (r_rhi r - 1) ltac:(lia)).
      assert (shad (r_rhi r - 1) < shad (r_rhi r)) by (rewrite !shad_div; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia). lia. }
    destruct (AG s ltac:(rewrite !shad_div in Hs; unfold ASHOFF, KEND in *; pose proof U as (U0 & U1 & _); OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia) HPs) as [E _]. exact E.
  - eapply wr_at_magree; [exact AG| exact W|]. intros a Ha. apply HP. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Notation f1c := (C1 (Z_to_bv 8 18446744073709551601)).
Notation f3c := (C1 (Z_to_bv 8 18446744073709551603)).
Notation z1c := (C1 (Z_to_bv 8 0)).

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Hypothesis SM1 : stack_malloc_1_stmtk AI fflag rng_fs 1.
Hypothesis GFHA : gfhaA_stmt AI rng_fs.
Hypothesis FFSI : ffsiA_stmt AI rng_fs.
Hypothesis GIMG : In (0x20d40, 0x20dc0)%Z CI.
Notation FB1 F := (mkABlock (ABFake 1) F 128).

Definition FDS_STACK_A : Z := 224 + AFI_FFSI_STACK.

(* [comment removed for export] *)
Definition fdsA_post (L : alayout) (RNG : footprint)
    (ra : word) (SPV : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo SPV
    /\ magree asegs (aclient_addr CI LB SPV) m m'
    /\ AHEAP AI L RNG st LB m'.

Definition fdsA_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra : word) (SPV : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
         (S : Z) (bl : list Z) (lo : Z) (rstk : region),
  AHEAP AI L RNG st LB m ->
  fake_lek 1 1 LB -> fake_lek 0 0 LB -> fake_lek 2 0 LB ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  buf_atA m S bl -> zlen bl < 2^62 -> hcoverA LB S (zlen bl) ->
  gshA m ->
  stk asegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - FDS_STACK_A -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  rclean m rstk -> r_lo rstk <= lo -> SPV <= r_hi rstk -> ATOP <= r_rlo rstk -> rrng RNG rstk ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlen bl) ->
  evtF asegs RNG (fdsA_post L RNG ra SPV gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AFI_FDS) fc None m (seg_rom asegs)).

Section Body.
  (* [comment removed for export] *)
  Variables (L : alayout) (RNG : footprint) (ra : word) (SPV : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (S : Z) (bl : list Z) (lo : Z) (rstk : region)
            (FF : Z) (bi : ablock) (j16 : list byte).
  Notation n := (zlen bl).
  Notation SPA := (SPAf SPV).
  Notation shF := (Z.shiftr FF 3 + 2147450880).
  Notation POST := (fdsA_post L RNG ra SPV gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m).
  Hypothesis LE1 : fake_lek 1 1 LB.
  Hypothesis LE0 : fake_lek 0 0 LB.
  Hypothesis LE2 : fake_lek 2 0 LB.
  Hypothesis LBH : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
  Hypothesis BUF : buf_atA m S bl.
  Hypothesis NB : n < 2^62.
  Hypothesis HC : hcoverA LB S n.
  Hypothesis HCB : n = 0 \/ (In bi LB /\ ab_addr bi <= S /\ S + n <= ab_addr bi + ab_size bi).
  Hypothesis GSH : gshA m.
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LO : lo <= SPV - 224 - (192 + 8192).
  Hypothesis SPT : SPV + 16 < al_top L.
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis RS1 : r_lo rstk <= lo.
  Hypothesis RS2 : SPV <= r_hi rstk.
  Hypothesis RS3 : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RIS : rng_aimg_sh RNG.
  Hypothesis RFS : rng_fs L RNG.
  Hypothesis LY3 : al_top L <= 2^47.
  (* [comment removed for export] *)
  Hypothesis FH : ablk FF (FF + 128).
  Hypothesis FC : FF + 128 <= ATOP.
  Hypothesis F128 : FF mod 128 = 0.
  Hypothesis RFF : rng RNG FF 128.
  Hypothesis RSFF : rng RNG (shad FF) 16.
  Hypothesis FFD : forall b, In b LB -> FF + 128 <= ab_addr b \/ ab_addr b + ab_size b <= FF.

  (* [comment removed for export] *)
  Definition fds_invA (mk : amem) : Prop :=
    AHEAP AI L RNG st (FB1 FF :: LB) mk /\ magree asegs (aclient_addr CI LB SPV) m mk /\ mem_inv asegs mk
    /\ stk asegs mk lo SPA /\ stk asegs mk (SPA + 88) (SPV + -104)
    /\ rw_cells asegs mk (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ (exists j24, rw_cells asegs mk SPA (DFRB FF j16 j24))
    /\ (exists rcl, rw_cells asegs mk (SPA + 64) rcl /\ cells_size rcl = 24%nat)
    /\ rw_cells asegs mk shF DSH1
    /\ rw_cells asegs mk FF DHDR /\ rw_cells asegs mk (FF + 120) [C8 (Z_to_bv 64 (fflag L 1 FF))]
    /\ (exists zj, rw_cells asegs mk (FF + 32) [CB 48 zj])
    /\ rclean mk rstk.

  (* [comment removed for export] *)
  #[using="lo FF bi HCB BOT LO"] Lemma CLS : forall a, S <= a < S + n -> aclient_addr CI LB SPV a.
  Proof. intros a Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0020>23711243373.7559314873579.7300000E00US3BOT2LO2Ha3BI13BI21HS3BOT2LO2Ha2Z01H".
destruct HCB as [Z0|(BI & BI1 & BI2)]; [exfalso; lia|]. apply (cl_block CI LB SPV bi a BI). lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  #[using="SPV bl"] Lemma CLF : forall SPx a, FF <= a < FF + 128 -> aclient_addr CI (FB1 FF :: LB) SPx a.
  Proof. intros SPx a Ha. apply (cl_block CI (FB1 FF :: LB) SPx (FB1 FF) a ltac:(left; reflexivity)). cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010>50948066934.73000004S2Ha".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  Let HCI := AI_aci_img AI.
  Let HCI0 := AI_aci_lo AI.

  (* [comment removed for export] *)
  #[using="FFLAG FREL bl LBH BOT LO SPT SP16 RSTK FH FC F128 RFF RSFF FFD HCI HCI0"] Lemma fds_closeA : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r x27 x28 x29 x30 x31 : word) (mx : amem)
      (j32 : list byte) (rcl : list cell),
    AHEAP AI L RNG st (FB1 FF :: LB) mx ->
    magree asegs (aclient_addr CI LB SPV) m mx ->
    rw_cells asegs mx shF DSH1 -> rw_cells asegs mx FF DHDR -> rw_cells asegs mx (FF + 120) [C8 (Z_to_bv 64 (fflag L 1 FF))] ->
    rw_cells asegs mx (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells asegs mx SPA (DFRA FF j16 j32) -> rw_cells asegs mx (SPA + 64) rcl -> cells_size rcl = 24%nat ->
    stk asegs mx lo SPA -> stk asegs mx (SPA + 88) (SPV + -104) -> mem_inv asegs mx ->
    evtF asegs RNG POST (fds_xst gp tp FR fc SPV mx FF x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 r x27 x28 x29 x30 x31).
  Proof.
    intros until rcl. intros AHx MGx SHFx FF0x FF120x FRBx FRAx RCx LRC STLx STGx MIx. unfold fds_xst.
    pose proof atop_range as ATR. pose proof (spaf_propsA SPV SP16) as (SPAB & SPA32 & _).
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
    Local Ltac2 Set LiaHints.tbl := fun () => "00D0?14434989683.14415860008408.14017991089884.12720146148781.14421307924273.12723950408031.11629786476646.11629788559449.13829928407609.14429928407609.14536339653704.13838738239746.14044518355164.14548567891639.13849061474495.12750950165260.14452551281388.14456170236367.12763868783922.1157780033100.140 00000W00d01101Z01[02102:02C02\03503>03K03W03a03m04904B04O04X04eS3BOT2LO4SP163LRC3ATR4SPAB5SPA323FHb2HrS3LRC3FHb3GHaS3BOT3LRC3FHbS3BOT2LO4SP164F1283LRC3ATR4SPAB5SPA323FHbFS4F1283LRC3ATR3FHa3FHcS3LRC3FHbS3LRC3FHbS3BOT2LO3LRC3ATR4SPAB3FHbS3BOT2LO3LRC3ATR4SPAB3FHbS3LRC3FHbS3LRC3FHb3GHdS3LRC3FHb2HrS4F1283LRCS2LO3LRC3FHbS3LRC3FHb2HrS3LRC3FHbS3SPT3LRC3FHbS3LRC3FHbS3LRC3FHb3GHa".
assert (ESH : shad FF = Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 16 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    (* [comment removed for export] *)
    destruct (FFLAG _ _ _ _ _ _ _ _ AHx ltac:(left; reflexivity)) as (FLC & RG & GH & GC & GBL & _).
    pose proof (GBL _ ltac:(left; reflexivity)) as GF. cbn [ab_addr ab_size] in GF.
    pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa.
    (* [comment removed for export] *)
    unfold DHDR in FF0x.
    change [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1ffc2); C8 (Z_to_bv 64 0x80d14)]
      with ([C8 (Z_to_bv 64 0x41b58ab3)] ++ [C8 (Z_to_bv 64 0x1ffc2); C8 (Z_to_bv 64 0x80d14)]) in FF0x.
    apply (proj1 (rw_cells_appA _ _ _ _ _)) in FF0x. destruct FF0x as [FF0x _].
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply fds_exit with (lo := lo);
        first [exact SHFx| exact FF0x| exact FF120x| exact FLC| exact FRBx| exact FRAx| exact RCx| exact LRC| exact STLx| exact STGx| exact MIx
              | exact FH| exact FC| exact F128| exact GH| exact GC| exact GF| exact RFF| exact RSFF| exact RG| exact SP16| exact RI
              | rewrite ESH; exact RSFF | eapply rng_sub'; [exact RSTK| lia]| unfold KEND; lia | unfold AFI_STACK; lia | lia]. }
    cbv beta. intros ms' (y11 & mp & m5 & -> & MU5 & WM5 & MIp & MU6 & WM6 & MI5 & ST5 & FLC5).
    assert (AHp : AHEAP AI L RNG st (FB1 FF :: LB) mp).
    { eapply (AI_frame AI); [exact AHx| exact MU5| exact WM5|].
      constructor; [| constructor; [| constructor]]; cbn.
      - right; right. right; right. exists 1, FF, 128. split; [left; reflexivity|].
        rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      - right; left. exists (FB1 FF). split; [left; reflexivity| cbn; lia]. }
    pose proof (FREL _ _ _ _ _ _ _ _ AHp) as AHr.
    assert (AH5 : AHEAP AI L RNG st LB m5).
    { eapply aheap_eqA; [exact AHr|].
      apply (mem_eq_singleA mp m5 (fflag L 1 FF) (Z_to_bv 8 0)); [lia| lia| exact MU6| apply byte_of_c1A; [exact FLC5| lia]]. }
    apply evtF_done. unfold fdsA_post. do 15 eexists. exists m5. split; [reflexivity|].
    split; [exact MI5|]. split; [exact ST5|].
    split.
    { assert (MGp : magree asegs (aclient_addr CI LB SPV) m mp).
      { eapply magree_munch_step; [exact MGx| exact MU5| exact WM5|].
        intros a Ha. cbn.
        split; [intros Hr; refine (shadow_not_clientN CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _ Ha); rewrite ESH; lia|].
        split; [intros Hr; exact (app_not_client CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)| exact I]. }
      eapply magree_munch_step; [exact MGp| exact MU6| exact WM6|].
      intros a Ha. cbn. split; [| exact I].
      intros Hr. refine (app_not_client CI LB SPV (fflag L 1 FF) 1 a HCI HCI0 GH ltac:(lia) LBH _ ltac:(lia) Ha).
      intros b Hb. exact (GBL b (or_intror Hb)). }
    exact AH5.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  (* [comment removed for export] *)
  #[using="Type"] Lemma dfrb_dfra : forall mq j24, rw_cells asegs mq SPA (DFRB FF j16 j24) -> exists j32, rw_cells asegs mq SPA (DFRA FF j16 j32).
  Proof.
    intros mq j24 H. unfold DFRB in H.
    change [CB 16 j16; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 4294967287); CB 24 j24; C8 (Z_to_bv 64 FF)]
      with ([CB 16 j16; C8 (Z_to_bv 64 FF)] ++ [C8 (Z_to_bv 64 4294967287); CB 24 j24] ++ [C8 (Z_to_bv 64 FF)]) in H.
    apply rw_cells_merge in H. cbn [cells_size csize cells_bytes cbytes Nat.add app] in H. rewrite app_nil_r in H.
    eexists. unfold DFRA. exact H.
  Qed.

  (* [comment removed for export] *)
  #[using="rc SPV bl FH F128"] Lemma zfh_sh6 : forall mq c4 c5 c6 c7 c8 c9,
    rw_cells asegs mq shF [f1c; f1c; f1c; f1c; c4; c5; c6; c7; c8; c9; f3c; f3c; f3c; f3c; f3c; f3c] ->
    rw_cells asegs mq (Z.shiftr (FF + 32) 3 + 2147450880) [c4; c5; c6; c7; c8; c9].
  Proof.
    intros mq c4 c5 c6 c7 c8 c9 H. pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd).
    change [f1c; f1c; f1c; f1c; c4; c5; c6; c7; c8; c9; f3c; f3c; f3c; f3c; f3c; f3c]
      with ([f1c; f1c; f1c; f1c] ++ [c4; c5; c6; c7; c8; c9] ++ [f3c; f3c; f3c; f3c; f3c; f3c]) in H.
    pose proof (proj1 (rw_cells_appA _ _ _ _ _) H) as [_ X]. apply (proj1 (rw_cells_appA _ _ _ _ _)) in X. destruct X as [X _].
    cbn [cells_size csize Nat.add] in X.
    replace (Z.shiftr (FF + 32) 3 + 2147450880) with (Z.shiftr FF 3 + 2147450880 + Z.of_nat 4); [exact X|].
    Local Ltac2 Set LiaHints.tbl := fun () => "0020>29784466142.8552026834029.8400000500;S3FHbS4F128".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rng_fs FFLAG FREL GFHA FFSI GIMG bi LE0 LE2 LBH BUF NB HC HCB GSH BOT LO SPT SP16 RS1 RS2 RS3 RRS TP RSTK RI RIS RFS LY3 FH FC F128 RFF RSFF FFD HCI HCI0"] Lemma fds_stepA : forall (mk : amem) (k : Z) (tot x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    fds_invA mk -> 0 <= k -> k + 5 <= n ->
    (forall mk' k' (tot' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31 : word),
        fds_invA mk' -> k + 1 <= k' -> k' + 5 <= n ->
        evtF asegs RNG POST (fds_head gp tp FR fc SPV mk' FF S n k' tot' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31)) ->
    evtF asegs RNG POST (fds_head gp tp FR fc SPV mk FF S n k tot x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros INV K0 K5 IH.
    destruct INV as (AHk & MGk & MIk & STLk & STGk & FRBk & [j24 FRAk] & (rcl & RCk & LRC) & SHFk & FF0k & FF120k & [zj ZFk] & RCL).
    pose proof atop_range as ATR. pose proof (spaf_propsA SPV SP16) as (SPAB & SPA32 & _).
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
    Local Ltac2 Set LiaHints.tbl := fun () => "02P0?10067396400.18011797028774.17611797028776.21111801222822.17511801222824.21011801222824.21811801225000.20811801225000.21611801225126.17311801225128.20711801225128.21511803468326.17211803468328.20611803468328.21414434989683.17414434989683.20814434989683.21615091133804.20116218619485.1811687406310.162 17283273139.18017991151658.22217991430230.16317997267345.19819613269122.22219613547774.16319627838777.19820133347816.18020146148781.17420146148781.20820146148781.21621798555882.23822255217234.21522255217244.18022706556809.17922706556809.18022706556809.21422706556809.21522706556809.22122706556809.22223950408031.11927858251649.18029452305166.18029784460045.20629784460045.23229786476646.11929786661642.16129786692825.17029788740055.20429788740055.21229788741207.21529788741209.18029928407609.17429928407609.20829928407609.21529928407609.21631122784806.18132137134912.20132163650965.16132245727734.1433231020887.201 37295580274.20137621869492.20438007881225.18039473256948.18139473355253.18040575542014.18040829866818.2384221554309.181 44143292112.16345293254401.20148120193439.18048130680209.20148557109815.17048567580473.20448567580473.21248768338001.21649061543497.22249061822005.16349067593714.19849585875648.1635033780125.206 5033780125.232 50950165260.21550950167453.20750950167453.20850950167453.23350950167453.23450950167453.23551527698235.22251527944007.16351533969024.19851792315293.22251792593889.16351807236646.19851965614678.18051967548903.22651967712856.20152101693566.20652101693566.20752101693566.20852101693566.20952101693566.21052101693566.21152101693566.21252101693566.21352101693566.22952101693566.23052101693566.23152101693566.23252101693566.23352101693566.23452101693566.23552101693566.23652232296045.20152238586467.18052551281388.17452551281388.20852551281388.21652967192527.20152981871553.18056170170169.22256170415941.16357052433661.14457052433661.21757491753462.20957491753462.21757491753464.17457571066394.21657881691200.18057896370254.20159308873939.12259308873939.14559579212292.22659827795304.18059897366575.16359897612371.22259908209128.19861139191535.18061149512010.22262549407336.20163157185191.20163868783922.11868200101466.1808119804454.213 8119804454.236 8378946369.209 8378946369.210 8378946369.211 8378946369.212 8378946369.229 8378946369.230 8378946369.231 9608221839.214 9608221839.237 9686143246.198 9688267734.201 9690365912.180 9692061897.163 9692340405.222 00000\01101F01[02002E03203_04L05905f06S07@07m08h09c0:^0:o0;D0;]0<F0<[0=00=E0=F0=G0=H0>40?70@:0A=0Ai0B`0CW0DG0E70Eg0FW0GG0H70HM0I:0IO0Ic0J70J@0JQ0Jb0K30KD0KU0Kf0LO0M80Ma0NJ0N_0Om0P_0QJ0R70Rd0S50SF0T20T^0To0UX0Ui0Uj0VW0Vk0W?0Wk0XW0YC0Z00ZD0ZX0Zl0\I0]80]g0^;0^O0^c0_70_K0__0`30`G0`[0`o0aC0aW0an0bE0b\0d<0dP0dd0eT0fD0g40gd0hV0iH0i\0j00j`0kP0l@0m00n10nE0nY0nj0o;0oL0o]0on10C10X10h11<11Q11f12;12d13h14l15N16<16M17918018g19^1:31:H1;71;d1;m1<>1=41=j1>^1?G1@01@Y1AM1B61B_1C51CK1D<1Di1EV1FG1G8S4F1283LRC2K02K53BSF3AVS3BI13BI23BIu3BIF3FHuS3LRC3FHb3AVS3HU53R1bS3LRC3FHb3AVS3HU53R1bS3LRC3FHb3AVS3HU53R1bS3LRC3FHb3AVS3HU53R1bS3LRC3FHb3AVS3HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1bS3BOT2LO4SP163RS23LRC3ATR4SPAB5SPA323FHb3HU23HU43HU53R1b2HrS3BOT2LO4SP163RS23LRC3ATR4SPAB5SPA323FHb3HU23HU43HU53R1b2HrS3BOT2LO4SP163RS23LRC3ATR4SPAB5SPA323FHb3HU23HU43HU53R1b2HrS3LRC3FHb3HU53R1bS3LRC3FHa3FHb3HU53R1bS3LRC3FHb3HU53Bk13Bk23R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3HU23HU53R1bS3BOT3LRC3FHb3HU53R1bS3BOT3LRC3FHb3HU53R1bS3BOT3LRC3FHb3HU53R1bFFFS4F1283LRC2K02K53BSF3AVS3BI13BI23BIu3BIF3FHuS3BOT2LO4SP163RS24F1283LRC2K02K53ATR4SPAB5SPA323FHb3HU23HU43HU53R1bS3BOT2LO4SP163RS24F1283LRC2K02K53ATR4SPAB5SPA323FHb3HU23HU43HU53R1bS3BOT2LO4SP163RS24F1283LRC2K02K53ATR4SPAB5SPA323FHb3HU23HU43HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3HU23HU53R1b2HrS3RS33LRC2K02K53ATR3BSF3BI13BI23BIu3BIF3HU33FHu3Bk23R1cS3RS33LRC2K02K53ATR3BSF3BI13BI23BIu3BIF3HU33FHu3Bk23R1cS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1b2HxS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1b2HxS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1b2HxS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1b2HxS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1b2HxS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1b2HxS4F1283LRC3ATR3FHa3FHcS3BOT2LO3SPT3RS23LRC3ATR4SPAB3FHb3HU23HU53R1bS3LRC3FHb3FHd3HU53R1bS3LRC3FHb3HU53R1b2HaS3LRC3FHb3HU53R1b2HaS3LRC3FHbS3LRC3FHb3HU53R1bS3LRC3FHb3HU53R1bS3LRC3FHb3HU53R1bS3LRC3FHb3HU53R1bS3LRC3FHb3HU53R1bS3LRC3FHb3HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3HU23HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3HU23HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3HU23HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3HU23HU53R1bS3LRC3FHb3FHd3HU53R1bS2LO4SP163RS13RS23LRC2K02K54SPAB5SPA323BSF3AVS3BI13BI23BIu3BIF3HU13HU23HU43FHuS3LRC2K02K53BSF3AVS3BI13BI23BIu3BIF3FHu3Bk13Bk22R4S3BOT2LO3RS23LRC2K02K53ATR4SPAB3FHb3HU23HU5S3BOT2LO3SPT3RS23LRC3ATR4SPAB3FHb3HU23HU53R1bS3BOT2LO3SPT3RS23LRC3ATR4SPAB3FHb3HU23HU53R1bS3LRC3FHb3HU53R1bS3LRC3FHb3HU53R1bS4F1283LRC2K02K53BSF3AVS3BI13BI23BIu3BIF3FHuS4F1283LRC2K02K53BSF3AVS3BI13BI23BIu3BIF3FHuS3LRC3FHb3HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3HU23HU53R1bS3LRC3FHb3HU53R1bFS3BOT2LO3SPT3RS23LRC3ATR4SPAB3FHb3HU23HU53R1bS3LRC2K53FHb3HU53R1bS3LRC2K53FHb3HU53R1bS4F1283LRC2K02K53BSF3AVS3BI13BI23BIu3BIF3FHuS4F1283LRC2K02K53BSF3AVS3BI13BI23BIu3BIF3FHuS4F1283LRC2K02K53BSF3AVS3BI13BI23BIu3BIF3FHuS3BOT2LO3RS13RS23LRC3ATR4SPAB3FHb3HU23HU53R1bS2LO3LRC3FHb3HU53R1bS2LO3LRC3FHb3HU53R1bS2LO3LRC3FHb3HU53R1bS3BOT2LO4SP163RS23LRC2K02K53ATR4SPAB5SPA323FHb3BSF3AVS3BI13BI23BIu3BIF3HU23HU43HU53FHu2HN3R1bS4F1283LRC2K02K53BSF3AVS3BI13BI23BIu3BIF3FHu2HaS4F1283LRC2K02K53BSF3AVS3BI13BI23BIu3BIF3FHu2HaS3LRC3FHb3HU53R1b2HrS3LRC3FHb3HU53R1b2HaS3LRC3FHb3HU53R1b2HaS3LRC3FHb3HU53R1b2HaS3LRC3FHb3HU53R1b2HaS3LRC3FHb3HU53R1b2HaS3LRC2K53FHb3HU53R1bS3LRC2K53FHb3HU53R1bS3LRC2K53FHb3HU53R1bS3LRC2K03FHb3HU53R1bS3LRC2K03FHb3HU53R1bS3LRC2K03FHb3HU53R1bS3LRC2K02K53FHb3HU53R1bS3LRC2K02K53FHb3HU53R1bS3LRC2K02K53FHb3HU53R1bS3BOT2LO4SP163RS23LRC2K02K53ATR4SPAB5SPA323FHb3BSF3AVS3BI13BI23BIu3BIF3HU23HU43HU53FHu2HN3R1b2HaS3LRC3FHb3HU53R1b2HaS3LRC3FHb3HU53R1b2HaS3BOT2LO3RS23LRC3ATR4SPAB3FHb3FHc3HU23HU53R1b2HaS3BOT2LO3RS23LRC3ATR4SPAB3FHb3FHc3HU23HU53R1b2HaS3BOT2LO3RS23LRC3ATR4SPAB3FHb3FHc3HU23HU53R1b2HaS3BOT2LO3RS23LRC3ATR4SPAB3FHb3FHc3HU23HU53R1b2HaS3RS33LRC2K02K53ATR3BI13BI23BIu3BIF3HU33HU63FHu2HaS3BOT2LO3RS23LRC2K02K53ATR4SPAB3FHb3HU23HU53R1b2HaS3LRC3FHb3HU53R1b2HaS3LRC3FHb3HU53R1b2HaS3BOT2LO3RS23LRC3ATR4SPAB3FHb3BSF3HU23HU53R1b2HaS3BOT2LO3RS23LRC3ATR4SPAB3FHb3FHc3HU23HU53R1b2HaS3BOT2LO3RS23LRC3ATR4SPAB3FHb3FHc3HU23HU53R1b2HaS3BOT2LO3RS23LRC3ATR4SPAB3FHb3FHc3HU23HU53R1b2HaS3BOT2LO4SP163LRC2K02K53ATR4SPAB5SPA323BI13BI23BIu3BIF3HU63FHu2HaS3LRC2K03FHb3HU53R1bS3LRC2K03FHb3HU53R1bS3LRC3FHb3HU53R1bS3LRC3FHb3HU53R1bS3LRC3FHb3HU53R1bS3LRC3FHb3HU53R1bS3LRC3FHb3HU53R1bS3SPT3LRC3FHb3HU53R1bS3SPT3LRC3FHb3HU53R1bS3LRC3FHb3HU52HaS3LRC3FHb3HU53R1b2HaS3LRC3FHb3AVS3HU53R1bS3LRC3FHb3AVS3HU53R1bS3LRC3FHb3AVS3HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3HU23HU53R1bS3BOT2LO3RS23LRC2K03ATR4SPAB3FHb3BI13BI23BIa3BIc3HU23HU53Bk13R1a3R1bS3BOT2LO3RS23LRC2K03ATR4SPAB3FHb3BI13BI23BIa3BIc3HU23HU53Bk13R1a3R1bS3BOT2LO3LRC2K02K53ATR4SPAB3FHb2Z0S3BOT2LO3RS23LRC2K02K53ATR4SPAB3FHb3HU23HU52Z0S3LRC3FHb3HU53R1bS4F1283LRC2K02K53BSF3AVS3BI13BI23BIu3BIF3FHuS3BOT2LO3RS23LRC2K02K53ATR4SPAB3FHb3HU23HU53Bk23R1b3R1cS3BOT2LO3RS23LRC2K02K53ATR4SPAB3FHb3HU23HU53Bk23R1b3R1cS3BOT2LO3RS23LRC2K02K53ATR4SPAB3FHb3HU23HU53Bk23R1b3R1cS3LRC3FHa3FHb3HU53R1bS3LRC3FHa3FHb3HU53R1bS3BOT2LO3RS23LRC2K02K53ATR4SPAB3FHb3HU23HU53R1bS3LRC2K02K55SPA323BSF3AVS3BI13BI23BIu3BIF3FHuS3LRC3FHbS3LRC3FHb3HU53R1bS3RS33LRC2K02K53BSF3AVS3BI13BI23BIu3BIF3HU33HU63FHu2HaS3RS33LRC2K02K53BSF3AVS3BI13BI23BIu3BIF3HU33HU63FHu2HaS3BOT2LO3SPT3RS23LY33LRC3ATR4SPAB3FHb3HU23HU53R1b2HaS3SPT3RS23LY33LRC4SPAB3FHb3HU23HU53R1b2HaS3SPT3RS23LY33LRC4SPAB3FHb3HU23HU53R1b2HaS3SPT3RS23LY33LRC4SPAB3FHb3HU23HU53R1b2HaS3BOT2LO3SPT3RS23LY33LRC3ATR4SPAB3FHb3HU23HU53R1b2HaS3SPT3RS23LY33LRC4SPAB3FHb3HU23HU53R1b2HaS3SPT3RS23LY33LRC4SPAB3FHb3HU23HU53R1b2HaS3LRC4SPAB3FHb3HU53R1bS3LRC4SPAB3FHb3HU53R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3HU23HU53Bk13R1a3R1bS3LRC2K02K55SPA323BSF3AVS3BI13BI23BIu3BIF3FHuS3LRC2K02K55SPA323BSF3AVS3BI13BI23BIu3BIF3FHuS3BOT2LO3RS23LRC3ATR4SPAB3FHb3HU23HU53Bk13R1a3R1bS3BOT2LO3RS23LRC3ATR4SPAB3FHb3HU23HU53Bk13R1a3R1b".
assert (ESH : shad FF = Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 16 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    pose proof (app_vs_shadow FF 128 (Z.shiftr FF 3 + 2147450880) 16 FH (proj1 BSF) (proj2 BSF)) as AVS.
    destruct HCB as [Z0|(BI & BI1 & BI2)]; [exfalso; lia|].
    pose proof (LBH bi BI) as BIH. pose proof (ablk_lin _ _ BIH) as (BIa & BIb & BIc & BId). unfold AIMG_HI in BIa.
    pose proof BIH as BIu. unfold ablk, AIMG_HI, KLS in BIu.
    pose proof (FFD bi BI) as BIF.
    pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR. pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LBH' : forall b, In b (FB1 FF :: LB) -> ablk (ab_addr b) (ab_addr b + ab_size b)).
    { intros b [<-|Hb]; [exact FH| exact (LBH b Hb)]. }
    pose proof (shclean_hull _ _ _ _ _ (rclean_shclean _ _ RCL)) as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6). unfold KEND in HU6.
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    (* [comment removed for export] *)
    assert (PLk : bytes_at asegs mk S (map (Z_to_bv 8) bl)).
    { eapply bytes_at_magree; [exact MGk| exact PL|]. rewrite length_map. intros a Ha. apply CLS. lia. }
    assert (USk : unpoisoned mk S (S + n)) by (eapply hcoverA_unpoisoned; [exact AHk| apply hcoverA_cons_fake; exact HC| lia]).
    pose proof HC as HC0.
    destruct HC0 as [Z0|(p & BA & BN & Hbk & Bk1 & Bk2)]; [exfalso; lia|].
    destruct (AI_block AI _ _ _ _ _ _ _ _ AHk ltac:(right; exact Hbk)) as (HN & (R1 & R2 & R3 & R4) & RGA & RGS & _).
    pose proof (ablk_lin _ _ R1) as (R1a & R1b & R1c & R1d). unfold AIMG_HI in R1a.
    unfold shlen in RGS. rewrite Z.shiftr_div_pow2 in RGS by lia. change (2^3) with 8 in RGS.
    assert (RSS : rng RNG (Z.shiftr S 3 + 2147450880) (Z.shiftr (S + n - 1) 3 - Z.shiftr S 3 + 1)).
    { rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. eapply rng_sub'; [exact RGS|]. rewrite shad_div. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    assert (RSn : rng RNG S n) by (eapply rng_sub'; [exact RGA| lia]).
    (* [comment removed for export] *)
    eapply evtF_cut; [| intros ms' Hms; exact Hms].
    eapply fds_L1 with (lo := lo);
      first [ exact PLk | exact PLR | exact USk | exact FRAk | exact SHFk | exact MIk | exact FH | exact F128 | exact RSn | exact RSS | exact NB
            | exact SP16 | exact RI | exact RSFF | eapply rng_sub'; [exact RSTK| lia] | unfold AFI_STACK; lia | unfold KEND; lia
            | unfold KLS, KHIGH; lia | lia | idtac ].
    - (* [comment removed for export] *)
      intros x10' x11' x12' x13' x19' x20' r t11.
      destruct (dfrb_dfra _ _ FRAk) as [j32 FRA'].
      eapply fds_closeA; [exact AHk| exact MGk| exact SHFk| exact FF0k| exact FF120k| exact FRBk| exact FRA'| exact RCk| exact LRC| exact STLk| exact STGk| exact MIk].
    - (* [comment removed for export] *)
      intros k' x10' x11' x12' x13' x22' HK1 HK2.
      eapply IH; [| exact HK1| exact HK2].
      split; [exact AHk|]. split; [exact MGk|]. split; [exact MIk|]. split; [exact STLk|]. split; [exact STGk|]. split; [exact FRBk|].
      split; [exists j24; exact FRAk|]. split; [exists rcl; split; [exact RCk| exact LRC]|]. split; [exact SHFk|]. split; [exact FF0k|].
      split; [exact FF120k|]. split; [exists zj; exact ZFk| exact RCL].
    - (* [comment removed for export] *)
      intros m5 MU5 WM5 MI5 SHZ5 FRA5 PL5.
      assert (AH5 : AHEAP AI L RNG st (FB1 FF :: LB) m5).
      { eapply (AI_frame AI); [exact AHk| exact MU5| exact WM5|].
        constructor; [cbn; right; right; right; right; exists 1, FF, 128; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                      change (2 ^ 3) with 8; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]| constructor]. }
      assert (MG5 : magree asegs (aclient_addr CI LB SPV) m m5).
      { eapply magree_munch_step; [exact MGk| exact MU5| exact WM5|]. intros a Ha. cbn.
        split; [intros Hr; refine (shadow_not_clientN CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _ Ha); rewrite ESH; lia| exact I]. }
      pose proof (rw_cells_transport _ _ _ _ _ _ FRBk MU5 WM5 ltac:(cbn; lia)) as FRB5.
      pose proof (rw_cells_transport _ _ _ _ _ _ RCk MU5 WM5 ltac:(rewrite LRC; cbn; lia)) as RC5.
      pose proof (rw_cells_transport _ _ _ _ _ _ FF0k MU5 WM5 ltac:(cbn; lia)) as FF05.
      pose proof (rw_cells_transport _ _ _ _ _ _ FF120k MU5 WM5 ltac:(cbn; lia)) as FF1205.
      pose proof (rw_cells_transport _ _ _ _ _ _ ZFk MU5 WM5 ltac:(cbn; lia)) as ZF5.
      assert (STL5 : stk asegs m5 lo SPA) by (eapply stk_transport; [exact STLk| exact MU5| exact WM5| intros x Hx; left; cbn; lia]).
      assert (STG5 : stk asegs m5 (SPA + 88) (SPV + -104)) by (eapply stk_transport; [exact STGk| exact MU5| exact WM5| intros x Hx; left; cbn; lia]).
      assert (RCL5 : rclean m5 rstk).
      { destruct RCL as [SC LT]. split; [| exact LT]. eapply shclean_transport; [exact SC| exact MU5| exact WM5| | exact LT].
        cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
        split; [| exact I]. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
      unfold DSHZ in SHZ5. pose proof (zfh_sh6 _ _ _ _ _ _ _ SHZ5) as SHZ6.
      assert (UNZ5 : unpoisoned m5 (FF + 32) (FF + 32 + 48)).
      { replace (FF + 32 + 48) with ((FF + 32) + 8 * Z.of_nat 6) by lia.
        apply (c1z_cells_unpoisoned 6 m5 (FF + 32) SHZ6); [OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| lia| unfold KEND in *; lia]. }
      clear MU5 WM5.
      (* [comment removed for export] *)
      eapply evtF_cut.
      { pose proof GFHA as G. unfold gfhaA_stmt, gfhaA_stmt_at in G.
        eapply (G L RNG (Z_to_bv 64 0x80fd8) (SPAf SPV)) with (lo := lo) (S := S + k) (bl := skipn (Z.to_nat k) bl) (ZF := FF + 32); clear G;
        [ exact AH5
        | apply fake_lek_push; [intros F' n' E; discriminate E| exact LE0]
        | exact LBH'
        | apply buf_atA_skipn; [split; [exact PL5| exact PLR]| lia]
        | rewrite zlen_skipnA by lia; lia
        | apply hcoverA_cons_fake; eapply hcoverA_sub; [exact HC| lia| rewrite zlen_skipnA by lia; lia| rewrite zlen_skipnA by lia; lia]
        | exact ZF5
        | split; [ exists 1, FF, 128; split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [exact FH| OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]
                 | exact UNZ5 ]
        | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
        | exists 1, FF, 128; split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|]; split; [reflexivity|];
          split; [lia|]; split; [unfold KEND in *; lia|]; change (128 / 8) with 16; split; [rewrite ESH; exact (proj2 SHZ5)| exact RSFF]
        | eapply gshA_mg; [exact MG5| intros a Ha; exact (gsh_client CI LB SPV a GIMG Ha)| exact GSH]
        | exact STL5
        | exact BOT
        | unfold AFI_STACK; lia
        | lia
        | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
        | exact MI5
        | exact TP
        | exact RSTK
        | exact RI
        | exact RIS
        | exact RFS
        | eapply rng_sub'; [exact RFF| lia]
        | eapply rng_sub'; [exact RSFF|]; rewrite !shad_div; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
        | reflexivity
        | reflexivity
        | reflexivity
        | rewrite zlen_skipnA by lia; reflexivity ]. }
      cbv beta. intros ms' PO. unfold gfhaA_post in PO.
      destruct PO as (r & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & zj1 & hb & zj2 & m6
                      & -> & MI6 & ST6 & MG6 & AH6 & ZFH6 & _).
      retlitA.
      (* [comment removed for export] *)
      assert (SHZm6 : rw_cells asegs m6 (Z.shiftr FF 3 + 2147450880) DSHZ).
      { eapply rw_cells_magree; [exact MG6| exact SHZ5|]. cbn [cells_size csize Nat.add DSHZ length]. intros a Ha. split; [| lia].
        right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
        right; right. exists 1, FF, 128. split; [left; reflexivity|]. rewrite Z.shiftr_div_pow2 in Ha by lia. change (2^3) with 8 in Ha.
        unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
      assert (FF06 : rw_cells asegs m6 FF DHDR).
      { eapply rw_cells_magree; [exact MG6| exact FF05|]. cbn [cells_size csize Nat.add DHDR length]. intros a Ha. split; [apply CLF; lia| lia]. }
      assert (FF1206 : rw_cells asegs m6 (FF + 120) [C8 (Z_to_bv 64 (fflag L 1 FF))]).
      { eapply rw_cells_magree; [exact MG6| exact FF1205|]. cbn [cells_size csize Nat.add]. intros a Ha. split; [apply CLF; lia| lia]. }
      assert (FRB6 : rw_cells asegs m6 (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
      { eapply rw_cells_magree; [exact MG6| exact FRB5|]. cbn [cells_size csize Nat.add FDRB length]. intros a Ha. split; [apply cl_stack; lia| lia]. }
      assert (FRA6 : rw_cells asegs m6 SPA (DFRB FF j16 j24)).
      { eapply rw_cells_magree; [exact MG6| exact FRA5|]. cbn [cells_size csize Nat.add DFRB length]. intros a Ha. split; [apply cl_stack; lia| lia]. }
      assert (RC6 : rw_cells asegs m6 (SPA + 64) rcl).
      { eapply rw_cells_magree; [exact MG6| exact RC5|]. rewrite LRC. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. split; [apply cl_stack; lia| lia]. }
      assert (STG6 : stk asegs m6 (SPA + 88) (SPV + -104)).
      { eapply stk_magree; [exact MG6| exact STG5|]. intros a Ha. split; [apply cl_stack; lia| lia]. }
      assert (RCL6 : rclean m6 rstk).
      { eapply (rclean_magreeF _ _ _ MG6); [| exact RCL5]. intros a Ha. rewrite !shad_div in Ha. unfold ASHOFF in Ha. split; [| OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
        right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. left. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
      assert (MG6' : magree asegs (aclient_addr CI LB SPV) m m6).
      { eapply magree_trans; [exact MG5|]. eapply magree_mono; [exact MG6|]. intros a Ha. split.
        - eapply aca_monoA; [exact Ha| intros b Hb; right; exact Hb| lia].
        - intros Hr. exact (app_not_client CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha). }
      clear SHZ5 FF05 FF1205 FRB5 FRA5 RC5 STG5 STL5 RCL5 ZF5 MI5 AH5 MG5 SHZ6 UNZ5.
      (* [comment removed for export] *)
      eapply evtF_cut; [| intros ms' Hms; exact Hms].
      eapply fds_L2 with (lo := lo);
        first [ exact ZFH6 | exact FRA6 | exact SHZm6 | exact MI6 | exact FH | exact F128 | exact RFF | exact RSFF | exact NB
              | exact SP16 | exact RI | eapply rng_sub'; [exact RSTK| lia] | unfold AFI_STACK; lia | unfold KEND; lia | lia | idtac | idtac ].
      + (* [comment removed for export] *)
        intros m7 x1' x10' x11' x12' x13' x19' x20' r' t11 MU7 WM7 MI7 SHF7.
        assert (AH7 : AHEAP AI L RNG st (FB1 FF :: LB) m7).
        { eapply (AI_frame AI); [exact AH6| exact MU7| exact WM7|].
          constructor; [cbn; right; right; right; right; exists 1, FF, 128; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                        change (2 ^ 3) with 8; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]| constructor]. }
        assert (MG7 : magree asegs (aclient_addr CI LB SPV) m m7).
        { eapply magree_munch_step; [exact MG6'| exact MU7| exact WM7|]. intros a Ha. cbn.
          split; [intros Hr; refine (shadow_not_clientN CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _ Ha); rewrite ESH; lia| exact I]. }
        pose proof (rw_cells_transport _ _ _ _ _ _ FRB6 MU7 WM7 ltac:(cbn; lia)) as FRB7.
        pose proof (rw_cells_transport _ _ _ _ _ _ FRA6 MU7 WM7 ltac:(cbn; lia)) as FRA7.
        pose proof (rw_cells_transport _ _ _ _ _ _ RC6 MU7 WM7 ltac:(rewrite LRC; cbn; lia)) as RC7.
        pose proof (rw_cells_transport _ _ _ _ _ _ FF06 MU7 WM7 ltac:(cbn; lia)) as FF07.
        pose proof (rw_cells_transport _ _ _ _ _ _ FF1206 MU7 WM7 ltac:(cbn; lia)) as FF1207.
        assert (STL7 : stk asegs m7 lo SPA) by (eapply stk_transport; [exact ST6| exact MU7| exact WM7| intros x Hx; left; cbn; lia]).
        assert (STG7 : stk asegs m7 (SPA + 88) (SPV + -104)) by (eapply stk_transport; [exact STG6| exact MU7| exact WM7| intros x Hx; left; cbn; lia]).
        destruct (dfrb_dfra _ _ FRA7) as [j32 FRA'].
        eapply fds_closeA; [exact AH7| exact MG7| exact SHF7| exact FF07| exact FF1207| exact FRB7| exact FRA'| exact RC7| exact LRC| exact STL7| exact STG7| exact MI7].
      + (* [comment removed for export] *)
        intros m7 t11 MU7 WM7 MI7 SHF7.
        assert (AH7 : AHEAP AI L RNG st (FB1 FF :: LB) m7).
        { eapply (AI_frame AI); [exact AH6| exact MU7| exact WM7|].
          constructor; [cbn; right; right; right; right; exists 1, FF, 128; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                        change (2 ^ 3) with 8; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]| constructor]. }
        assert (MG7 : magree asegs (aclient_addr CI LB SPV) m m7).
        { eapply magree_munch_step; [exact MG6'| exact MU7| exact WM7|]. intros a Ha. cbn.
          split; [intros Hr; refine (shadow_not_clientN CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _ Ha); rewrite ESH; lia| exact I]. }
        pose proof (rw_cells_transport _ _ _ _ _ _ FRB6 MU7 WM7 ltac:(cbn; lia)) as FRB7.
        pose proof (rw_cells_transport _ _ _ _ _ _ FRA6 MU7 WM7 ltac:(cbn; lia)) as FRA7.
        pose proof (rw_cells_transport _ _ _ _ _ _ RC6 MU7 WM7 ltac:(rewrite LRC; cbn; lia)) as RC7.
        pose proof (rw_cells_transport _ _ _ _ _ _ FF06 MU7 WM7 ltac:(cbn; lia)) as FF07.
        pose proof (rw_cells_transport _ _ _ _ _ _ FF1206 MU7 WM7 ltac:(cbn; lia)) as FF1207.
        pose proof (rw_cells_transport _ _ _ _ _ _ ZFH6 MU7 WM7 ltac:(cbn; lia)) as ZFH7.
        assert (STL7 : stk asegs m7 lo SPA) by (eapply stk_transport; [exact ST6| exact MU7| exact WM7| intros x Hx; left; cbn; lia]).
        assert (STG7 : stk asegs m7 (SPA + 88) (SPV + -104)) by (eapply stk_transport; [exact STG6| exact MU7| exact WM7| intros x Hx; left; cbn; lia]).
        assert (RCL7 : rclean m7 rstk).
        { destruct RCL6 as [SC LT]. split; [| exact LT]. eapply shclean_transport; [exact SC| exact MU7| exact WM7| | exact LT].
          cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
        split; [| exact I]. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
        assert (PL7 : bytes_at asegs m7 S (map (Z_to_bv 8) bl)).
        { eapply bytes_at_magree; [exact MG7| exact PL|]. rewrite length_map. intros a Ha. apply CLS. lia. }
        assert (UR7 : unpoisoned m7 (SPA + 64) (SPA + 64 + 24)).
        { eapply unpoisoned_sub; [exact (shclean_unpoisoned _ _ _ _ _ (rclean_shclean _ _ RCL7))| lia| lia]. }
        clear MU7 WM7 FRB6 FRA6 RC6 FF06 FF1206 ZFH6 STG6 ST6 RCL6 MI6 AH6 MG6 MG6' SHZm6.
        (* [comment removed for export] *)
        eapply evtF_cut.
        { pose proof FFSI as G. unfold ffsiA_stmt in G.
          eapply (G L RNG (Z_to_bv 64 0x81050) (SPAf SPV)) with (lo := lo) (S := S + k) (bl := skipn (Z.to_nat k) bl) (R := SPAf SPV + 64) (rj := rcl); clear G;
          [ exact AH7
          | apply fake_lek_push; [intros F' n' E; discriminate E| exact LE2]
          | apply fake_lek_push; [intros F' n' E; discriminate E| exact LE0]
          | exact LBH'
          | apply buf_atA_skipn; [split; [exact PL7| exact PLR]| lia]
          | rewrite zlen_skipnA by lia; lia
          | apply hcoverA_cons_fake; eapply hcoverA_sub; [exact HC| lia| rewrite zlen_skipnA by lia; lia| rewrite zlen_skipnA by lia; lia]
          | exact RC7
          | exact LRC
          | exact UR7
          | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
          | lia
          | lia
          | eapply gshA_mg; [exact MG7| intros a Ha; exact (gsh_client CI LB SPV a GIMG Ha)| exact GSH]
          | exact STL7
          | exact BOT
          | unfold AFI_FFSI_STACK, AFI_STACK; lia
          | lia
          | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
          | exact MI7
          | exact TP
          | exact RSTK
          | exact RI
          | exact RIS
          | exact RFS
          | eapply rng_sub'; [exact RSTK| lia]
          | unfold rrng in RRS; eapply rng_sub'; [exact RRS|]; rewrite !shad_div; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
          | reflexivity
          | reflexivity
          | reflexivity
          | rewrite zlen_skipnA by lia; reflexivity ]. }
        cbv beta. intros ms' PO. unfold ffsiA_post in PO.
        destruct PO as (a0' & w0 & w1 & w2 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & w3 & w4 & w5 & w6 & nb & cs & db & m8
                        & -> & MI8 & ST8 & MG8 & AH8 & RC8 & CSF).
        retlitA. rewrite zlen_skipnA in CSF by lia.
        (* [comment removed for export] *)
        assert (CR8 : forall a, SPA <= a < 2^47 -> ~ (SPA + 64 <= a < SPA + 64 + 24) -> aclient_addr CI (FB1 FF :: LB) SPA a /\ ~ (SPA + 64 <= a < SPA + 64 + 24)).
        { intros a Ha Hn. split; [apply cl_stack; exact Ha| exact Hn]. }
        assert (FRB8 : rw_cells asegs m8 (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
        { eapply rw_cells_magree; [exact MG8| exact FRB7|]. cbn [cells_size csize Nat.add FDRB length]. intros a Ha. apply CR8; lia. }
        assert (FRA8 : rw_cells asegs m8 SPA (DFRB FF j16 j24)).
        { eapply rw_cells_magree; [exact MG8| exact FRA7|]. cbn [cells_size csize Nat.add DFRB length]. intros a Ha. apply CR8; lia. }
        assert (STG8 : stk asegs m8 (SPA + 88) (SPV + -104)).
        { eapply stk_magree; [exact MG8| exact STG7|]. intros a Ha. apply CR8; lia. }
        assert (SHF8 : rw_cells asegs m8 (Z.shiftr FF 3 + 2147450880) DSH1).
        { eapply rw_cells_magree; [exact MG8| exact SHF7|]. cbn [cells_size csize Nat.add DSH1 length]. intros a Ha. split; [| lia].
          right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
          right; right. exists 1, FF, 128. split; [left; reflexivity|]. rewrite Z.shiftr_div_pow2 in Ha by lia. change (2^3) with 8 in Ha.
          unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
        assert (FF08 : rw_cells asegs m8 FF DHDR).
        { eapply rw_cells_magree; [exact MG8| exact FF07|]. cbn [cells_size csize Nat.add DHDR length]. intros a Ha. split; [apply CLF; lia| lia]. }
        assert (FF1208 : rw_cells asegs m8 (FF + 120) [C8 (Z_to_bv 64 (fflag L 1 FF))]).
        { eapply rw_cells_magree; [exact MG8| exact FF1207|]. cbn [cells_size csize Nat.add]. intros a Ha. split; [apply CLF; lia| lia]. }
        assert (ZF8 : exists zj', rw_cells asegs m8 (FF + 32) [CB 48 zj']).
        { assert (Z7 : rw_cells asegs m8 (FF + 32) [CB 24 zj1; CB 4 hb; CB 20 zj2]).
          { eapply rw_cells_magree; [exact MG8| exact ZFH7|]. cbn [cells_size csize Nat.add]. intros a Ha. split; [apply CLF; lia| lia]. }
          destruct (rw_cells_forget asegs _ _ _ Z7) as [zj' Z8]. cbn [cells_size csize Nat.add] in Z8. exists zj'. exact Z8. }
        assert (RCL8 : rclean m8 rstk).
        { eapply (rclean_magreeF _ _ _ MG8); [| exact RCL7]. intros a Ha. rewrite !shad_div in Ha. unfold ASHOFF in Ha. split; [| OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
          right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. left. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
        assert (MG8' : magree asegs (aclient_addr CI LB SPV) m m8).
        { eapply magree_trans; [exact MG7|]. eapply magree_mono; [exact MG8|]. intros a Ha. split.
          - eapply aca_monoA; [exact Ha| intros b Hb; right; exact Hb| lia].
          - intros Hr. exact (stack_not_client CI LB SPV (SPAf SPV + 64) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha). }
        pose proof (bv_unsigned_in_range 64 cs) as CSR. unfold bv_modulus in CSR. cbn in CSR.
        rewrite <- (Z_to_bv_bv_unsigned cs) in RC8.
        clear FRB7 FRA7 RC7 FF07 FF1207 ZFH7 STG7 STL7 RCL7 PL7 UR7 MI7 AH7 MG7 SHF7.
        (* [comment removed for export] *)
        eapply evtF_cut; [| intros ms' Hms; exact Hms].
        eapply fds_L3 with (lo := lo) (c := bv_unsigned cs);
          first [ exact FRA8 | exact RC8 | exact MI8 | exact NB | exact CSF | exact CSR | exact FC | exact SP16 | exact RI
                | eapply rng_sub'; [exact RSTK| lia] | unfold AFI_STACK; lia | unfold KEND; lia | lia | idtac | idtac ].
        * (* [comment removed for export] *)
          intros x10' x19' x20' r' t11'.
          destruct (dfrb_dfra _ _ FRA8) as [j32 FRA'].
          eapply fds_closeA; [exact AH8| exact MG8'| exact SHF8| exact FF08| exact FF1208| exact FRB8| exact FRA'| exact RC8| reflexivity| exact ST8| exact STG8| exact MI8].
        * (* [comment removed for export] *)
          intros k' x10' HK1 HK2.
          destruct ZF8 as [zj' ZF8'].
          eapply IH; [| exact HK1| exact HK2].
          split; [exact AH8|]. split; [exact MG8'|]. split; [exact MI8|]. split; [exact ST8|]. split; [exact STG8|]. split; [exact FRB8|].
          split; [exists j24; exact FRA8|]. split; [eexists; split; [exact RC8| reflexivity]|]. split; [exact SHF8|]. split; [exact FF08|].
          split; [exact FF1208|]. split; [exists zj'; exact ZF8'| exact RCL8].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rng_fs FFLAG FREL GFHA FFSI GIMG bi LE0 LE2 LBH BUF NB HC HCB GSH BOT LO SPT SP16 RS1 RS2 RS3 RRS TP RSTK RI RIS RFS LY3 FH FC F128 RFF RSFF FFD HCI HCI0"] Lemma fds_loopA : forall (f : nat) (mk : amem) (k : Z) (tot x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    n - k <= Z.of_nat f -> fds_invA mk -> 0 <= k -> k + 5 <= n ->
    evtF asegs RNG POST (fds_head gp tp FR fc SPV mk FF S n k tot x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31).
  Proof.
    induction f as [|f IHf]; intros until x31; intros FUEL INV K0 K5.
    - exfalso. cbn in FUEL. Local Ltac2 Set LiaHints.tbl := fun () => "0030?44969437643.12159314873579.96 59675783702.12100000I00R00kS3BOT2LO4FUEL2K02K53HK11HS4FUEL2K5S3BOT2LO4FUEL2K02K53HK11H".
lia.
    - eapply fds_stepA; [exact INV| exact K0| exact K5|]. intros until y31. intros INV' HK1 HK2. eapply IHf; [lia| exact INV'| lia| exact HK2].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Body.
(* [comment removed for export] *)
#[using="fflag FFLAG FREL SM1 GFHA FFSI GIMG"] Theorem fdsA : fdsA_stmt.
Proof.
  unfold fdsA_stmt.
  intros L RNG ra SPV gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB S bl lo rstk
         AH LE1 LE0 LE2 LBH BUF NB HC GSH ST BOT LO SPT SP16 RCL RS1 RS2 RS3 RRS MI TP RSTK RI RIS RFS -> ->.
  pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  unfold FDS_STACK_A, AFI_FFSI_STACK, AFI_STACK in LO.
  pose proof (spaf_propsA SPV SP16) as (SPAB & SPA32 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
  pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
  pose proof (shclean_hull _ _ _ _ _ (rclean_shclean _ _ RCL)) as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6). unfold KEND in HU6.
  pose proof (rclean_lt _ _ RCL) as HULT.
  (* [comment removed for export] *)
  assert (XB : exists bi, zlen bl = 0 \/ (In bi LB /\ ab_addr bi <= S /\ S + zlen bl <= ab_addr bi + ab_size bi)).
  { destruct HC as [Z0|(p & BA & BN & Hbk & Bk1 & Bk2)]; [exists (mkABlock (ABFake 0) 0 0); left; exact Z0| exists (HB p BA BN); right; cbn; auto]. }
  destruct XB as [bi HCB].
  (* [comment removed for export] *)
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
  destruct RTC as (_ & GOT & _ & _ & SHB & SUA & _).
  destruct (fds_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [GSU _].
  (* [comment removed for export] *)
  eapply evtF_cut.
  { Local Ltac2 Set LiaHints.tbl := fun () => "01>0?10158985849.15610638381624.15511797028773.16611801222821.16511801225125.16311803323301.16711803468325.16214434989683.16015032711174.15616088010191.15316158148233.10717283160759.10617334690250.15317991086127.10017997379594.14417997724813.15319628012706.14419628224549.15320146148781.16020440531856.15520445093078.15620667555791.15321307920834.10021445009627.10621445010926.13722706556809.17022706556809.17123950408031.15024053715562.10925191441092.10627858232453.10628748943648.10029786476646.15029788740059.15529788741211.16229928407609.16030110483129.16030829781939.15633918932820.15634891932807.16034891932807.16435054702019.16235095177243.10036339867082.15539831303855.15341323351172.137436298327.153  48567580469.15549061477964.10049067767401.14449068110574.15350506967736.15550950165260.16052551281388.16052564903766.15852786605182.16256170235708.10056184917785.14456185097118.15357491753467.16458583572720.14459148144883.1455980439934.162 6006681403.156 60595102003.16060595102003.16460932994743.17061116395122.14663183206744.15363854432100.14965753062759.14667326972152.1057979291495.147 8119804454.150 8381940990.162 8806423751.161 8806423751.162 9608221839.149 00000\01M02:02g03003]03k04j05305?05d06I06J06S06`06m06n06o08008<08H08Q08R09709\09h0:40:B0:g0;00;Y0;Z0;c0;l0<50<^0=O0=X0=a0>J0?30?L0?f0?o0@80@=0@N0@`0@h0A40A@0B10B=0BF0C70CW0C`0Cm0D:0Dg0EE0Ec0FC0FD0G00G\0HE0Hc0Hl0I50I>0Ik0J60JF0J[0KO0LC0LQS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU53FHb2HnS3BOT2LO3SPT3RS23ATR3LY13LY33LY44SPAB3HU23HU53FHbS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU53FHb3FHcS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU53FHb3FHcS3HU53FHbS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU53FHb3BSFS4SPAB3HU53FHbS3BOT2LO4SP163RS23ATR3LY13LY23LY44SPAB5SPA323HU23HU43HU53FHb2HrS3HU53FHbS2NB3HU53FHbS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU5S3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU5FS3BOT3HU5S3BOT3HU53FHbS3BOT3HU53FHbFFS3BOT2LO4SP163RS23ATR3LY13LY23LY44SPAB5SPA323HU23HU43HU54F1283FHbS2LO3HU53FHbS2LO3HU53FHbS3HU53FHbFS3BOT2LO3SPT3RS23ATR3LY34SPAB3HU23HU5S3BOT2LO3SPT3RS23ATR3LY34SPAB3HU23HU5S3HU53FHb2HxS3HU53FHb2HxS3ATR4F1283FHuS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU5S3BOT3HU5S3BOT2LO3SPT3RS23ATR3LY13LY44SPAB3HU23HU5FS3HU53FHbS3HU53FHbS3HU53FHbS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU53FHbS3BOT2LO3SPT3RS23ATR3LY13LY33LY44SPAB3HU23HU53FHbS3HU53FHbS3HU53FHbS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU53FHbS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU53FHbS3RS33ATR3HU33HU63FHu3BSFS3SPT3RS23LY34SPAB3HU23HU5S3HU53FHbS3HU53FHbS3HU5S3HU53FHa3FHb3FHdS4F1283FHu3BSF3AVSS2LO3HU5S2LO3HU53FHbS2LO3HU53FHbS3BOT2LO3SPT3RS23ATR3LY13LY33LY44SPAB3HU23HU53FHbS3HU53FHb2HrS3HU53FHbS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU53FHb3FHc3BSFS3BOT2LO4SP163ATR4SPAB5SPA323HU6S3SPT3HU5S3SPT3HU53FHbS3SPT3HU53FHbS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU53FHb3FHcS3SPT3RS23LY34SPAB3HU23HU53FHbS3SPT3RS23LY34SPAB3HU23HU53FHbS3BOT2LO4SP163ATR4SPAB5SPA323HU6FS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU53FHb2HrS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU53FHb2HrS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU53FHbS3SPT3RS23LY34SPAB3HU23HU53FHbS3HU53FHbS3HU53FHbS3HU53FHbS3BOT2LO3SPT3RS23ATR3LY13LY33LY44SPAB3HU23HU5S3HU53FHb1DS3RS33HU33HU62HaS3RS33ATR3HU33FHu3BSFS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU53FHb3FHc3BSF2HxS3BOT2LO3RS23ATR3LY13LY44SPAB3HU23HU53FHb3FHc3BSF2HxS4SPAB3HU53FHb".
eapply (fds_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
      first [exact ST| exact MI| exact GOT| exact SHB| exact GSU| exact SUA| exact SP16| eapply rng_sub'; [exact RSTK| lia]
            | exact RI| unfold KEND; lia| unfold AFI_STACK; lia| lia]. }
  cbv beta. intros ms' (m1 & jA & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
  clear GOT SHB SUA GSU.
  assert (AH1 : AHEAP AI L RNG st LB m1).
  { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
  assert (MG1 : magree asegs (aclient_addr CI LB SPV) m m1).
  { eapply magree_mono; [eapply magree_of_munch; [exact MU1| exact WM1]|]. intros a Ha. cbn. split; [| exact I].
    intros Hr. exact (stack_not_client CI LB SPV (SPV - 224) a HCI HCI0 LBH ltac:(lia) Hr Ha). }
  assert (RCL1 : rclean m1 rstk).
  { eapply rclean_transport; [exact RCL| exact MU1| exact WM1|]. apply appW_cons; [unfold KLOW, KHIGH; lia| apply appW_nil]. }
  clear MU1 WM1.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { pose proof SM1 as SMC. unfold stack_malloc_1_stmtk, sm_stmtk in SMC. eapply SMC with (lo := lo); clear SMC;
      rewrite ?(unsigned_lit (SPAf SPV)) by lia;
      first [exact AH1| exact LE1| exact MI1| exact STL1| exact TP| reflexivity| exact RSTK| exact RI| exact RFS| lia]. }
  cbv beta. intros ms' PO.
  destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                  & -> & MI2 & ST2 & HPR2 & AH2 & F128 & FH & FC & FFC2 & SHF2 & RFF & RSFF).
  rewrite ?(unsigned_lit (SPAf SPV)) in ST2, HPR2 by lia.
  retlitA.
  change (Z.to_nat (128 - 32)) with 96%nat in FFC2. change (128 / 8) with 16 in RSFF.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
  assert (NFB : ~ In (FB1 FF) LB).
  { pose proof (AI_blocks_nodup AI _ _ _ _ _ AH2) as NDx. inversion NDx as [|x l NI0 N3]. exact NI0. }
  assert (FFD : forall b, In b LB -> FF + 128 <= ab_addr b \/ ab_addr b + ab_size b <= FF).
  { intros b Hb. assert (NE : FB1 FF <> b) by (intros E; apply NFB; rewrite E; exact Hb).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D. cbn in D. lia. }
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRB1 ltac:(left; left; cbn; lia)) as FRB2.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; lia)) as FRA2.
  pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
  assert (MG2 : magree asegs (aclient_addr CI LB SPV) m m2).
  { eapply magree_trans; [exact MG1|]. eapply magree_mono; [exact HPR2|]. intros a Ha. eapply aca_monoA; [exact Ha| intros b Hb; exact Hb| lia]. }
  assert (RCL2 : rclean m2 rstk).
  { eapply (rclean_magreeF _ _ _ HPR2); [| exact RCL1]. intros a Ha. rewrite !shad_div in Ha. unfold ASHOFF in Ha.
    right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. left. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (ESH : shad FF = Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 16 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  pose proof (app_vs_shadow FF 128 (Z.shiftr FF 3 + 2147450880) 16 FH (proj1 BSF) (proj2 BSF)) as AVS.
  clear MG1 HPR2 FRB1 FRA1 STG1 STL1 MI1 AH1 RCL1.
  (* [comment removed for export] *)
  destruct (fds_got_cells m2 (AI_relro AI _ _ _ _ _ AH2)) as [_ GPC2].
  eapply evtF_cut; [| intros ms' Hms; exact Hms].
  eapply fds_hdr with (lo := lo);
    first [exact FRA2| exact FFC2| exact SHF2| exact GPC2| exact MI2| exact FH| exact FC| exact F128
          | exact RFF| exact RSFF| exact SP16| exact RI| eapply rng_sub'; [exact RSTK| lia] | unfold AFI_STACK; lia | unfold KEND; lia | lia | idtac].
  intros m3 j16 j32 j24 MU3 WM3 MI3 FRA3 RC3 FFC3 SHF3. cbv beta.
  assert (AH3 : AHEAP AI L RNG st (FB1 FF :: LB) m3).
  { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
    constructor; [cbn; left; left; lia|].
    constructor; [cbn; left; left; lia|].
    constructor; [cbn; right; left; exists (FB1 FF); split; [left; reflexivity| cbn; lia]|].
    constructor; [cbn; right; right; right; right; exists 1, FF, 128; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                  change (2 ^ 3) with 8; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]| constructor]. }
  assert (LBH3 : forall b, In b (FB1 FF :: LB) -> ablk (ab_addr b) (ab_addr b + ab_size b)).
  { intros b [<-|Hb]; [exact FH| exact (LBH b Hb)]. }
  assert (MG3 : magree asegs (aclient_addr CI LB SPV) m m3).
  { eapply magree_munch_step; [exact MG2| exact MU3| exact WM3|]. intros a Ha. cbn.
    split; [intros Hr; exact (stack_not_client CI LB SPV (SPAf SPV) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha)|].
    split; [intros Hr; exact (stack_not_client CI LB SPV (SPAf SPV) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha)|].
    split; [intros Hr; exact (app_not_client CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)|].
    split; [intros Hr; refine (shadow_not_clientN CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _ Ha);
            rewrite ESH; lia| exact I]. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRB2 MU3 WM3 ltac:(cbn; lia)) as FRB3.
  assert (STL3 : stk asegs m3 lo (SPAf SPV)) by (eapply stk_transport; [exact ST2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  assert (STG3 : stk asegs m3 (SPAf SPV + 88) (SPV + -104)) by (eapply stk_transport; [exact STG2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  assert (RCL3 : rclean m3 rstk).
  { destruct RCL2 as [SC LT]. split; [| exact LT]. eapply shclean_transport; [exact SC| exact MU3| exact WM3| | exact LT].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    repeat split; try exact I; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  clear MG2 FRB2 FRA2 STG2 ST2 MI2 AH2 FFC2 SHF2 GPC2 RCL2.
  (* [comment removed for export] *)
  unfold DHDRF in FFC3.
  apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC3. destruct FFC3 as [FF03 FFC3]. cbn [cells_size csize Nat.add DHDR length] in FFC3.
  change [CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 FF))] with ([CB 96 junk] ++ [C8 (Z_to_bv 64 (fflag L 1 FF))]) in FFC3.
  apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC3. destruct FFC3 as [FJ3 FF1203]. cbn [cells_size csize Nat.add] in FF1203.
  replace (FF + Z.of_nat 24 + Z.of_nat 96) with (FF + 120) in FF1203 by lia. replace (FF + Z.of_nat 24) with (FF + 24) in FJ3 by lia.
  apply (rw_cells_split_CB asegs m3 _ [] 96 junk [] [8; 48; 40]%nat) in FJ3; [| reflexivity]. cbn [app mk_CB_cells] in FJ3.
  lazymatch type of FJ3 with rw_cells _ _ _ [?c0; ?c1; ?c2] =>
    apply (proj1 (rw_cells_appA _ m3 _ [c0] [c1; c2])) in FJ3; destruct FJ3 as [_ FZ3]; cbn [cells_size csize Nat.add] in FZ3;
    apply (proj1 (rw_cells_appA _ m3 _ [c1] [c2])) in FZ3; destruct FZ3 as [FZ3 _]; cbn [cells_size csize Nat.add] in FZ3 end.
  replace (FF + 24 + Z.of_nat 8) with (FF + 32) in FZ3 by lia.
  (* [comment removed for export] *)
  eapply evtF_cut; [| intros ms' Hms; exact Hms].
  eapply fds_disp0 with (lo := lo);
    first [exact FRA3| exact MI3| exact SP16| exact RI| eapply rng_sub'; [exact RSTK| lia] | unfold AFI_STACK; lia | unfold KEND; lia | lia | idtac | idtac].
  + (* [comment removed for export] *)
    intros r Hr.
    eapply fds_closeA; first [eassumption | reflexivity | lia].
  + (* [comment removed for export] *)
    intros m4 j24' Hn MU4 WM4 MI4 FRA4.
    assert (AH4 : AHEAP AI L RNG st (FB1 FF :: LB) m4).
    { eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|]. constructor; [cbn; left; left; lia| constructor]. }
    assert (MG4 : magree asegs (aclient_addr CI LB SPV) m m4).
    { eapply magree_munch_step; [exact MG3| exact MU4| exact WM4|]. intros a Ha. cbn.
      split; [intros Hr; exact (stack_not_client CI LB SPV (SPAf SPV) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha)| exact I]. }
    pose proof (rw_cells_transport _ _ _ _ _ _ FRB3 MU4 WM4 ltac:(cbn; lia)) as FRB4.
    pose proof (rw_cells_transport _ _ _ _ _ _ RC3 MU4 WM4 ltac:(cbn; lia)) as RC4.
    pose proof (rw_cells_transport _ _ _ _ _ _ FF03 MU4 WM4 ltac:(cbn; lia)) as FF04.
    pose proof (rw_cells_transport _ _ _ _ _ _ FF1203 MU4 WM4 ltac:(cbn; lia)) as FF1204.
    pose proof (rw_cells_transport _ _ _ _ _ _ FZ3 MU4 WM4 ltac:(cbn; lia)) as FZ4.
    pose proof (rw_cells_transport _ _ _ _ _ _ SHF3 MU4 WM4 ltac:(cbn [disjoint_from cells_size csize Nat.add DSH1 length]; lia)) as SHF4.
    assert (STL4 : stk asegs m4 lo (SPAf SPV)) by (eapply stk_transport; [exact STL3| exact MU4| exact WM4| intros x Hx; left; cbn; lia]).
    assert (STG4 : stk asegs m4 (SPAf SPV + 88) (SPV + -104)) by (eapply stk_transport; [exact STG3| exact MU4| exact WM4| intros x Hx; left; cbn; lia]).
    assert (RCL4 : rclean m4 rstk).
    { eapply rclean_transport; [exact RCL3| exact MU4| exact WM4|]. apply appW_cons; [unfold KLOW, KHIGH; lia| apply appW_nil]. }
    clear MU4 WM4 FRB3 RC3 FF03 FF1203 FZ3 SHF3 STL3 STG3 RCL3 MI3 AH3 MG3 FRA3.
    replace (Z_to_bv 64 (zlen bl)) with (Z_to_bv 64 (zlen bl - 0)) by (f_equal; lia).
    replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + 0)) by (f_equal; lia).
    eapply fds_loopA with (k := 0) (f := Z.to_nat (zlen bl)) (bi := bi) (j16 := j16).
    all: try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
    all: try lia.
    (* [comment removed for export] *)
    split; [exact AH4|]. split; [exact MG4|]. split; [exact MI4|]. split; [exact STL4|]. split; [exact STG4|]. split; [exact FRB4|].
    split; [exists j24'; exact FRA4|]. split; [exists [CB 24 j24]; split; [exact RC4| reflexivity]|]. split; [exact SHF4|]. split; [exact FF04|].
    split; [exact FF1204|]. split; [eexists; exact FZ4| exact RCL4].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Asm.
End CANSEC1.
