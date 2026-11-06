(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree StrFun.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface I_asan_memset AU_rt AH_memcpy0.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import ShadowTac APC_kit APC_kit2 APC_kit3 APC_kit4 APC_dtor APC_s12iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import A2Lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import APC_pid0 APC_pid1 APC_pid APC_fuzz0 APC_mpres APC_fuzz_t1.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import LiaTier0U.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac tlia ::= tlia_u.
Local Ltac lia3 ::= lia3_u.

Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable rng_fs : alayout -> footprint -> Prop.
Variable fflag : alayout -> Z -> Z -> Z.

(* [comment removed for export] *)
Definition afuzz_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (s : APS) (LB : list ablock) (D : Z) (payload : list Z) (lo : Z) (rstk : region),
    AHEAP AI L RNG (aps_m s) LB m ->
    (forall b, In b LB -> exists p A n, b = HB p A n) ->
    payload_atA LB D payload ->
    bytes_at bsegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
    D mod 16 = 0 -> zlength payload < 2^26 ->
    harness_invA m -> client_static s LB m ->
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK ->
    bv_unsigned sp + 208 = al_sp0 L -> bv_unsigned sp mod 16 = 0 ->
    rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
    s0 = Z_to_bv 64 (zlength payload) ->
    mem_inv bsegs m -> frm0 fc ->
    tp = Z_to_bv 64 ATP ->
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) -> ra = Z_to_bv 64 ATRUN_RET ->
    HU L ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
    aps_ok L s -> AFRESH (aps_m s) -> dk (aps_m s) <= DKF -> wr_at bsegs m (bv_unsigned sp) (al_top L - bv_unsigned sp) ->
    implMA RNG (fuzz_oneA AAllocAsan payload) s
           (fuzz_oneU_postW AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom bsegs)).

Section Proof.
  Hypothesis ONTA : opnew_nt_stmtA AI.
  Hypothesis ODA : opdelete_arr_stmtA AI.
  Hypothesis OD : opdelete_stmtA AI.
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis PARSE : parse_stmtA AI rng_fs.
  Hypothesis RFSM : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Hypothesis SM2 : stack_malloc_2_stmt AI fflag rng_fs.
  Hypothesis FAKE_FLAG : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
    rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
    /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
    /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
    /\ ~ in_ranges CI (fflag L cls F).
  Hypothesis FAKE_RELEASE : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
    AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).

  Theorem afuzz_proof : afuzz_stmt.
  Proof.
    unfold afuzz_stmt. intros until rstk.
    intros AH LBK PAY DAT DB D16 DL HINV CST ST LOA LOS SP0 SP16 RCL RCL1 RCL2 RCL3 S0E MI FZ TP A0 A1 RAE HUL RSTK RI RISH RFS RRNG AOK AFR DKF0 STKW.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof STKW as STKW0. boxm STKW0.
    unfold AHARNESS_STACK in LOS. pose proof atop_range as ATR.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    pose proof (harness_top L (bv_unsigned sp) SP0 ltac:(lia)) as HTOP.
    destruct HINV as [CI0 CSH].
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT & RIC & REAL & SHB & SUA & INI & LAY).
    pose proof CI0 as (GSUAR & _ & _ & _). unfold AGOT_SUAR, ASUAR in GSUAR. unfold rt_suar, ASUAR in SUA.
    (* [comment removed for export] *)
    apply (implMA_with_leaves RNG _ s _ (fun _ s' => DK 8 s s')); [exact (fuzz_oneA_dk payload s)|]. cbv beta.
    unfold fuzz_oneA, HarnessP.fuzz_one.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    carve_frame 128%nat ST.
    park_memA m. unfold parkedA in FR.
    subst a0 a1 s0 ra. unfold AFUZZ_ENTRY.
    do 12 zstep.
    unparkA. trmB MU WM.
    assert (FWL : Forall wfar [(lo, bv_unsigned sp)]) by (apply Forall_cons; [apply wfar_high; lia| apply Forall_nil]).
    pose proof (client_img_munch32 _ _ _ CI0 MU WM FWL) as CI00. pose proof (client_sh_munch32 _ _ _ CSH MU FWL) as CSH0.
    pose proof (client_static_munch32 _ _ _ _ _ CST MU WM FWL) as CST0.
    assert (RCL0 : rclean m0 rstk) by (eapply rclean_transport; [exact RCL| exact MU| exact WM| repeat constructor; unfold KHIGH; cbn; lia]).
    assert (PW0 : aheap_pres_W CI LB (bv_unsigned sp) client_wr m m0).
    { eapply aheap_pres_W_of_munch; [exact MU| exact WM|]. intros a Ha Hc Hx. cbn [outside].
      pose proof (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as Ha'. split; [lia| exact I]. }
    clear CI0 CSH CST RCL.
    steps_to 0x9565c.
    zstep. if_cases KU; zify_cond KU.
    { exfalso. revert KU. vm_compute. intros KU. discriminate KU. }
    clear KU. do 2 zstep.
    (* [comment removed for export] *)
    set (SA := Z.land (bv_unsigned sp + -128) 18446744073709551584) in *.
    assert (ESA : SA = bv_unsigned sp - 128 - (bv_unsigned sp - 128) mod 32)
      by (unfold SA; change 18446744073709551584 with (2^64 - 2^5); rewrite land_align_down by lia; change (2^5) with 32; lia).
    assert (SAB : bv_unsigned sp - 144 <= SA <= bv_unsigned sp - 128 /\ SA mod 32 = 0)
      by (rewrite ESA; clear - SP16 RSP LOS LOA ATR; Z.div_mod_to_equations; lia).
    clearbody SA. clear ESA.
    destruct (stk_split bsegs m0 lo SA (bv_unsigned sp + -128) ST ltac:(lia)) as [STL STM]. clear ST.
    assert (AH0 : AHEAP AI L RNG (aps_m s) LB m0)
      by (eapply (AI_frame AI); [exact AH| exact MU| exact WM| apply Forall_cons; [left; left; cbn; lia| apply Forall_nil]]).
    assert (USA : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply SM2 with (LB := LB) (lo := lo) (st := aps_m s); rewrite ?USA;
        [ exact AH0 | intros FA FN HIN; destruct (LBK _ HIN) as (p & A & n & E); discriminate E | exact MI | exact STL | exact LOA
        | unfold SM2_STACK; lia | lia | exact TP | exact RSTK | exact RI | exact RFS ]. }
    intros ms1 (FF & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & j0 & j1 & j2 & jk & -> & MI1 & STL1 & PR1 & AH1
                & F256 & FBLK & FTOP & FC & FSH & RF & RFSH & FSHB & FNC).
    retlit.
    rewrite ?USA in STL1, PR1.
    (* [comment removed for export] *)
    assert (HPX1 : aheap_pres_x CI LB SA FF 0 m0 m1) by (eapply aheap_pres_x_of_pres; [exact PR1| lia| intros b Hb; exact Hb]).
    pose proof (ablk_lin _ _ FBLK) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1. band_ind FBLK bF.
    assert (AWF : awin FF 0) by (apply awin_ablk in FBLK; unfold awin in *; lia).
    pose proof (client_img_pres_x AI IMG_CI _ _ _ _ _ _ _ _ _ _ HPX1 (awin_wfar _ _ AWF) CI00 AH1 MI1) as CI01.
    pose proof (client_sh_pres_x AI IMG_CI _ _ _ _ _ _ HPX1 (awin_wfar _ _ AWF) CSH0) as CSH1.
    pose proof (client_static_pres_x AI IMG_CI _ _ _ _ _ _ _ _ HPX1 (awin_wfar _ _ AWF) CST0) as CST1.
    pose proof (rclean_pres_x AI _ _ _ _ _ _ _ HPX1 AWF RCL3 RCL0) as RCL1'.
    pose proof (aheap_pres_x_stk CI _ _ _ _ _ _ _ _ HPX1 STM ltac:(lia) ltac:(lia) ltac:(lia)) as STM1.
    assert (PW1 : aheap_pres_W CI LB (bv_unsigned sp) client_wr m m1).
    { eapply aheap_pres_W_trans; [exact PW0|]. eapply (pres_W_of_x AI); [exact HPX1| lia| intros b Hb; exact Hb|]. intros a Hc Ho Hx. lia. }
    Time trpC PR1 (in_eq (mkABlock (ABFake 2) FF 256) LB) IMG_CI ltac:(fun _ => idtac).
    clear AH0 STM STL PW0 RCL0 CST0 CSH0 CI00 GOT RIC REAL SHB SUA INI LAY GSUAR WM MU MI STKW HPX1 PR1 FSHB.
    (* [comment removed for export] *)
    destruct (rw_cells_app_split bsegs _ _ [C8 (Z_to_bv 64 0); CB 40 _] _ FR) as [FR0 FRS]. clear FR.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRS. replace (bv_unsigned sp + -128 + 48) with (bv_unsigned sp + -80) in FRS by lia.
    pose proof (stk_release bsegs _ _ _ _ STM1 FR0 ltac:(lia)) as STF. clear STM1 FR0.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in STF. replace (bv_unsigned sp + -128 + 48) with (bv_unsigned sp + -80) in STF by lia.
    destruct (stk_split bsegs _ SA (SA + 16) _ STF ltac:(lia)) as [STG1 STX]. clear STF.
    destruct (stk_split bsegs _ (SA + 16) (SA + 24) _ STX ltac:(lia)) as [SFF STY]. clear STX.
    destruct (stk_split bsegs _ (SA + 24) (SA + 48) _ STY ltac:(lia)) as [SRR STG2]. clear STY.
    destruct (rw_cells_of_wr_at bsegs m1 (SA + 16) 8 (wr_at_of_stkF m1 (SA + 16) (SA + 24) (SA + 16) 8 SFF ltac:(lia) ltac:(lia) ltac:(lia))
                (no_image_asan (SA + 16) (SA + 16 + 8) ltac:(lia)) ltac:(lia)) as (jF & _ & FRF). clear SFF.
    destruct (rw_cells_of_wr_at bsegs m1 (SA + 24) 24 (wr_at_of_stkF m1 (SA + 24) (SA + 48) (SA + 24) 24 SRR ltac:(lia) ltac:(lia) ltac:(lia))
                (no_image_asan (SA + 24) (SA + 24 + 24) ltac:(lia)) ltac:(lia)) as (jr & _ & FRR). clear SRR.
    change (Z.to_nat 8) with 8%nat in FRF. change (Z.to_nat 24) with 24%nat in FRR.
    (* [comment removed for export] *)
    unfold shad, ASHOFF in FSH, RFSH. rewrite Z.add_comm in FSH, RFSH.
    assert (FSH' : rw_cells bsegs m1 (Z.shiftr FF 3 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)])
      by (eapply rw_cells_recast; [exact FSH| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]).
    clear FSH.
    assert (SFB : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 32 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - FB1 FB3 ATR; Z.div_mod_to_equations; lia).
    assert (FS8 : Z.shiftr FF 3 * 8 = FF) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - F256; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof (munch_refl [(SA + 16, SA + 24); (FF, FF + 256); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 32)] m1) as MU2.
    pose proof (wmono_refl bsegs m1) as WM2.
    park_memA m1. unfold parkedA in FRF, FC, FSH'.
    do 3 zstep. zstep. if_cases KF; zify_cond KF; [| exfalso; rewrite ?unsigned_lit in KF by lia; lia]. clear KF.
    Time steps_to 0x956d0.
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) _ |- _ =>
      pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK.
    Time steps_to 0x956e4.
    replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
    Time steps_to 0x65ce8.
    unparkA. Time trmB MU2 WM2.
    assert (FW2 : Forall wfar [(SA + 16, SA + 24); (FF, FF + 256); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 32)]).
    { apply Forall_cons; [apply wfar_high; lia|]. apply Forall_cons; [eapply wfar_ablk; [exact FBLK| lia| lia]|].
      apply Forall_cons; [apply wfar_shad; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - FB1; Z.div_mod_to_equations; lia| apply Forall_nil]. }
    pose proof (client_img_munch32 _ _ _ CI01 MU2 WM2 FW2) as CI4. pose proof (client_sh_munch32 _ _ _ CSH1 MU2 FW2) as CSH4.
    pose proof (client_static_munch32 _ _ _ _ _ CST1 MU2 WM2 FW2) as CST4. clear CI01 CSH1 CST1.
    assert (RCL4 : rclean m4 rstk).
    { eapply (rclean_munchF _ _ _ _ RCL1' MU2 WM2). pose proof RCL1' as ((_ & (H1 & H2 & H3 & H4 & H5 & H6) & _ & _) & _).
      rewrite !shad_div. unfold ASHOFF, KEND in *. cbn [disjoint_from].
      rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - H1 H2 H3 H4 H5 H6 RCL3 FB1 FB2 FB3 bFr bFhi bFlo ATR SAB LOA LOS RSP. Z.div_mod_to_equations. lia. }
    clear RCL1'.
    assert (AH4 : AHEAP AI L RNG (aps_m s) (mkABlock (ABFake 2) FF 256 :: LB) m4).
    { eapply (AI_frame AI); [exact AH1| exact MU2| exact WM2|].
      apply Forall_cons; [left; left; cbn; lia|].
      apply Forall_cons; [right; left; exists (mkABlock (ABFake 2) FF 256); split; [left; reflexivity| cbn; lia]|].
      apply Forall_cons; [| apply Forall_nil]. right; right. right; right. exists 2, FF, 256. split; [left; reflexivity|].
      cbn [fst snd]. unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - F256 FB1. Z.div_mod_to_equations. lia. }
    assert (PW4 : aheap_pres_W CI LB (bv_unsigned sp) client_wr m m4).
    { eapply aheap_pres_W_trans; [exact PW1|]. eapply aheap_pres_W_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc Hx. cbn [outside].
      pose proof (fresh_fake_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH1 FBLK ltac:(lia) Hc) as NF.
      pose proof (FNC a ltac:(rewrite USA; eapply aclient_addr_mono_sp; [exact Hc| lia])) as NS. unfold shad, ASHOFF in NS. rewrite Z.add_comm in NS.
      pose proof (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as Ha'.
      clear - NF NS Ha' SAB LOA LOS RSP ATR. repeat split; try exact I; lia. }
    clear AH1 MU2 WM2 PW1.
    exact (afuzz_t1 AI rng_fs fflag ONTA ODA OD IMG_CI PARSE RFSM SM2 FAKE_FLAG FAKE_RELEASE L RNG sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB D payload lo rstk m0 AH LBK PAY
       DAT DB D16 DL LOA LOS SP0 SP16 RCL1 RCL2 RCL3 FZ TP HUL RSTK RI RISH RFS RRNG AOK RSP STKW0 ATR LY1 LY2 LY3 HTOP junk FWL SA SAB USA FF u0 u1 u2 b1
       b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 j0 j1 j2 jk m3 m4 MI1 STL1 F256 FBLK FTOP RF RFSH FNC FB1 FB2 FB3 FB4 bF bFr bFhi bFlo AWF STG1 STG2 jF jr SFB FS8
       FRF FSH' FC FRR FRS FW2 CI4 CSH4 CST4 RCL4 AH4 PW4 AFR DKF0).
  Qed.
End Proof.
End S.
End CANSEC1.
