From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdFrameW ZdWalkKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_globals AZ_globalsR AZ_frame_iface AZ_dframe_iface AZ_kx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations. Import KXS.
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zland K := try (change 18446744073709551615 with (2^64-1) in K; rewrite ?zb_land_mask in K by lia; rewrite ?Z.mod_small in K by lia).
Ltac bcase K := if_cases K; zify_cond K; zland K.
Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Notation zlen l := (Z.of_nat (length l)).
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Notation SHB := 2147450880.

Section CANSEC1. Context {rc : runConstT}.

Lemma df_land_align : forall x j, 0 <= x < 2^64 -> 0 <= j <= 64 -> Z.land x (2^64 - 2^j) = x - x mod 2^j.
Proof.
  intros x j Hx Hj.
  replace (2^64 - 2^j)%Z with (Z.ldiff (Z.ones 64) (Z.ones j)).
  2:{ rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
      unfold Z.ones. rewrite Z.shiftl_mul_pow2 by lia.
      replace (2^64)%Z with (2^j * 2^(64-j))%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      replace (Z.pred (1 * (2 ^ j * 2 ^ (64 - j))))%Z with ((2^(64-j) - 1) * 2^j + (2^j - 1))%Z by lia.
      rewrite Z.div_add_l by lia. rewrite Z.div_small by (split; [lia| apply Z.lt_pred_l || lia]). lia. }
  rewrite Z.ldiff_land, Z.land_assoc. rewrite <- Z.ldiff_land.
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod x (2^j)%Z ltac:(lia)). lia.
Qed.

Notation BF1 := (Z_to_bv 8 18446744073709551601).
Notation BF8 := (Z_to_bv 8 18446744073709551608).
Notation BF3 := (Z_to_bv 8 18446744073709551603).
Notation BF5 := (Z_to_bv 8 18446744073709551605).
Notation B00 := (Z_to_bv 8 0).
Definition DFHDR (FLG : Z) (junk : list byte) : list cell :=
  [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d69); C8 (Z_to_bv 64 0x85980); CB 32 junk; C8 (Z_to_bv 64 FLG)].
Definition DFSH : list cell := [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 BF8; C1 BF3; C1 BF3; C1 BF3].
Definition DFSH5 : list cell := [C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5; C1 BF5].
Definition DSH00 : list cell := [C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00].
Lemma shadow8_c1s : forall (m : amem) s, rw_cells bsegs m s [C8 (Z_to_bv 64 0)] -> rw_cells bsegs m s DSH00.
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

Definition DSAVED (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma df_sh_rd0 : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n -> 0 <= X -> X + n <= 2^47 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr p 3 + SHB)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m X n p U H1 H2 H3 H4.
  pose proof (unp_shadow_zero m X n p U H1 H2) as B.
  assert (C : rw_cells bsegs m (shad p) [C1 (Z_to_bv 8 0)]).
  { apply rw_cells_C1_of_byte; [| | exact B]; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia. }
  pose proof (rw_cells_read bsegs m (shad p) [C1 (Z_to_bv 8 0)] 0 (C1 (Z_to_bv 8 0)) C eq_refl) as RD.
  rewrite Z.add_0_r in RD. unfold shad, ASHOFF in RD. rewrite Z.add_comm in RD. exact RD.
Qed.

Lemma df_disj_above : forall W A n K, Forall (fun iv : Z * Z => K <= fst iv) W -> A + n <= K -> disjoint_from W A n.
Proof.
  induction W as [|[lo' hi'] W IH]; intros A n K HW HA; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [lia|]. eapply IH; eassumption.
Qed.
Lemma df_art_transport : forall W m m', art m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => 0xd1740 <= fst iv) W -> art m'.
Proof.
  intros W m m' (GOT & RIC & SHBc & INI & LAY & REAL) MU WM HW.
  unfold art. repeat split.
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply df_disj_above; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply df_disj_above; [exact HW| cbn; lia]] ].
Qed.

Lemma df_relro_word : forall m A v,
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  ARELRO_LO <= A -> A + 8 <= ARELRO_HI -> rw_bytes_b bsegs A (le8 (Z_to_bv 64 v)) = true ->
  rw_cells bsegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v R LO HI RB. unfold ARELRO_LO, ARELRO_HI in *.
  eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A (le8 (Z_to_bv 64 v)));
    [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
    | exact RB | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.
Lemma df_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m 0xc7308 [C8 (Z_to_bv 64 0xcfcf8)] /\ rw_cells bsegs m 0xc7360 [C8 (Z_to_bv 64 0xcfd00)].
Proof.
  intros m R. split; (apply df_relro_word; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
Qed.

Lemma df_h5_fmt : forall (m : amem) D ws, dctx_h5 bsegs m D ws -> h5_frame_ok ws -> rw_cells bsegs m (D + 30104) [C4 (Z_to_bv 64 0)].
Proof.
  intros m D ws [HC HL] (KF & _).
  destruct ws as [|w0 [|w1 ws]]; [discriminate HL| discriminate HL|].
  change (h5_cells (w0 :: w1 :: ws)) with ([C8 w0] ++ [C4 w1] ++ mk_wcells (skipn 2 h5_sizes) ws) in HC.
  apply (proj1 (rw_cells_app bsegs _ _ [C8 w0] _)) in HC. destruct HC as [_ HC].
  apply (proj1 (rw_cells_app bsegs _ _ [C4 w1] _)) in HC. destruct HC as [HC _].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HC.
  cbv [wnth nth H5_format wz0] in KF. subst w1.
  match type of HC with rw_cells _ _ ?a _ => replace a with (D + 30104) in HC by lia end. exact HC.
Qed.

Lemma df_sh_c1 : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n -> 0 <= X -> X + n <= 2^47 ->
  rw_cells bsegs m (Z.shiftr p 3 + SHB) [C1 (Z_to_bv 8 0)].
Proof.
  intros m X n p U H1 H2 H3 H4.
  pose proof (unp_shadow_zero m X n p U H1 H2) as B.
  replace (Z.shiftr p 3 + SHB) with (shad p) by (unfold shad, ASHOFF; lia).
  apply rw_cells_C1_of_byte; [| | exact B]; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
Qed.

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (SPV lo : Z).
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPT : SPV + 16 < KEND.
  Hypothesis LOS : lo <= SPV - 208 - 4096.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.

  Definition DSPA : Z := (SPV - 192) - (SPV - 192) mod 32.
  Lemma dspa_props : SPV - 208 <= DSPA <= SPV - 192 /\ DSPA mod 32 = 0 /\ (SPV + -192) - (SPV + -192) mod 2^5 = DSPA.
  Proof. unfold DSPA. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

  Lemma df_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SPV -> mem_inv bsegs m ->
    rt_shbase m -> rw_cells bsegs m 0xc7308 [C8 (Z_to_bv 64 0xcfcf8)] -> rw_cells bsegs m 0xc7360 [C8 (Z_to_bv 64 0xcfd00)] ->
    rw_cells bsegs m 0xcfd00 [C4 (Z_to_bv 64 1)] ->
    evtF bsegs RNG (fun ms' => exists m' jA,
        ms' = MS (mkR (Z_to_bv 64 0x85a00) (Z_to_bv 64 DSPA) gp tp t0 t1 t2 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA)
                     (Z_to_bv 64 64) a1 (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     a1 (Z_to_bv 64 SHB) (Z_to_bv 64 0x7504) a0 a2 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 0x3ee8c) fc None m' (seg_rom bsegs)
        /\ munch [(SPV - 192, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
        /\ rw_cells bsegs m' DSPA [CB 88 jA]
        /\ stk bsegs m' lo DSPA /\ stk bsegs m' (DSPA + 88) (SPV + -104))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0x85980) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI SHBm GOT1 GOT2 SUA.
    unfold KEND in SPT. pose proof atop_range as ATR.
    pose proof dspa_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SPV - 192, SPV)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.
    carve_frame 104%nat ST. carve_frame 88%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    change 18446744073709551584 with (2^64 - 2^5). rewrite df_land_align by lia. rewrite ESPA'.
    release_frame FR1 ST (SPV + -104).
    destruct (stk_split bsegs _ lo (DSPA + 88) (SPV + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (DSPA + 88) 88 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 88) with 88 in STL, FRA. replace (DSPA + 88 - 88) with DSPA in STL, FRA by lia.
    zstep. zstep. zstep.
    zstep. zstep.
    zstep. zstep.
    clear GOT1 GOT2.
    zstep. rewrite (sx32_small 1) by lia.
    zstep.
    zstep. zstep.
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
    zstep. zstep. zstep.
    apply evtF_done.
    eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR0|]. split; [exact FRA|]. split; [exact STL| exact STG].
  Qed.

  Lemma df_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (FF FLG DCTX SRCo hsz : Z)
      (j0 j1 j2 : word) (junk jA : list byte),
    rw_cells bsegs m DSPA [CB 88 jA] -> stk bsegs m lo DSPA ->
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad FF) [C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m (DCTX + 30104) [C4 (Z_to_bv 64 0)] ->
    rw_cells bsegs m (Z.shiftr (DCTX + 30104) 3 + SHB) [C1 (Z_to_bv 8 0)] -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
    ablk DCTX (DCTX + 95992) -> DCTX mod 8 = 0 -> (DCTX + 95992 <= FF \/ FF + 64 <= DCTX) -> (DCTX + 95992 <= lo \/ SPV <= DCTX) ->
    rng RNG (DCTX + 30104) 4 -> rng RNG (Z.shiftr (DCTX + 30104) 3 + SHB) 1 ->
    0 <= SRCo < 2^64 -> 0 <= hsz < 2^64 ->
    evtF bsegs RNG (fun ms' => exists m' jA' y14 y15,
        ms' = MS (mkR (Z_to_bv 64 0x85acc) (Z_to_bv 64 DSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA)
                     (Z_to_bv 64 (DCTX + 29928)) (Z_to_bv 64 SRCo) (Z_to_bv 64 hsz) (Z_to_bv 64 0) y14 y15 x16 x17
                     (Z_to_bv 64 FF) (Z_to_bv 64 SHB) (Z_to_bv 64 0x7504) (Z_to_bv 64 DCTX) (Z_to_bv 64 hsz) s7
                     (Z_to_bv 64 (DCTX + 29956)) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) s11 x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x8324c) fc None m' (seg_rom bsegs)
        /\ munch [(DSPA, DSPA + 88); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' DSPA [CB 80 jA'; C8 (Z_to_bv 64 FF)] /\ stk bsegs m' lo DSPA
        /\ rw_cells bsegs m' FF (DFHDR FLG junk) /\ rw_cells bsegs m' (Z.shiftr FF 3 + SHB) DFSH)
      (MS (mkR (Z_to_bv 64 0x85a00) (Z_to_bv 64 DSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 SRCo) (Z_to_bv 64 SHB) (Z_to_bv 64 0x7504) (Z_to_bv 64 DCTX) (Z_to_bv 64 hsz) s7 s8 s9 s10 s11 x28 x29 x30 x31)
           FR (Z_to_bv 64 0x85a00) fc None m (seg_rom bsegs)).
  Proof.
    intros until jA. intros FRA STL FFC SHF FMT FMS MI FH FC F64 RF RSF DH D8 DFF DCS RFM RFMS HS HZ.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof (fk_ablk_lits _ _ DH) as DL.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof dspa_props as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    apply shadow8_c1s in SHF. unfold DSH00 in SHF. replace (shad FF) with (Z.shiftr FF 3 + SHB) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : SHB <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 8 <= 0x10007fff8000)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    assert (BSD1 : SHB <= Z.shiftr (DCTX + 30104) 3 + SHB /\ Z.shiftr (DCTX + 30104) 3 + SHB + 1 <= 0x10007fff8000)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    assert (BSD2 : Z.shiftr (DCTX + 30104) 3 + 1 <= Z.shiftr FF 3 \/ Z.shiftr FF 3 + 8 <= Z.shiftr (DCTX + 30104) 3)
      by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof (munch_refl [(DSPA, DSPA + 88); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    apply (rw_cells_split_CB bsegs _ _ [] 88 _ [] [80; 8]%nat) in FRA; [| reflexivity]. cbn [mk_CB_cells app] in FRA.
    fk_hold DL. fk_hold DFF. fk_hold DCS. fk_hold BSD1. fk_hold BSD2. fk_hold FMT. fk_hold FMS. fk_hold DH. fk_hold D8. fk_hold RFM. fk_hold RFMS.
    zstep. zstep. zstep. zstep.
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].
    do 6 zstep.
    zstep. zstep. zstep.
    zstep. zstep. zstep.
    zstep. zstep.
    replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr FF 3 + SHB) _ |- _ =>
        pose proof (rw_cells_store_ok bsegs mx _ _ 4%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep.
    zstep. replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr FF 3 + SHB) _ |- _ =>
        pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep.
    unfold fk_held in DL, DFF, DCS, BSD1, BSD2, FMT, FMS, DH, D8, RFM, RFMS.
    pose proof (rw_cells_transport bsegs _ _ _ _ _ FMT MU WM
                  ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - DFF DCS DL BSF SPAB LOS LOC ATR; lia)) as FMT'.
    pose proof (rw_cells_transport bsegs _ _ _ _ _ FMS MU WM
                  ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - BSD1 BSD2 FHu SPAB LOS LOC ATR; lia)) as FMS'.
    clear FMT FMS. fk_hold DFF. fk_hold BSD2.
    zstep. zstep. zstep.
    try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep.
    zstep. bcase K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|].
    zstep.
    zstep. zstep. zstep. zstep. zstep.
    apply evtF_done.
    eexists _, _, _, _. split; [reflexivity|]. split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [eassumption|].
    split; [exact FRA|]. split; [exact STL|]. split; [unfold DFHDR; exact FFC| unfold DFSH; exact SHF].
  Qed.

  Variable AI : AMallocIface.
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (st : astate) (LB : list ablock).
  Ltac df_sok F k := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr F 3 + SHB) _ |- _ =>
      pose proof (rw_cells_store_ok bsegs mx _ _ k _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.

  Lemma df_epi : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word) m (FF FLG : Z)
      (j0 j1 j2 : word) (junk jA : list byte),
    rw_cells bsegs m (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m DSPA [CB 88 jA] -> stk bsegs m lo DSPA -> stk bsegs m (DSPA + 88) (SPV + -104) ->
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (Z.shiftr FF 3 + SHB) DFSH -> rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
    AHEAP AI L RNG st (FB0 FF :: LB) m -> mem_inv bsegs m ->
    FLG = fflag L 0 FF -> ablk FF (FF + 64) -> FF mod 64 = 0 -> FF + 64 <= ATOP ->
    ablk FLG (FLG + 1) -> FLG + 1 <= ATOP -> (FF + 64 <= FLG \/ FLG + 1 <= FF) ->
    rng RNG FF 64 -> rng RNG (Z.shiftr FF 3 + SHB) 8 -> rng RNG FLG 1 ->
    evtF bsegs RNG (fun ms' => exists (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m',
        ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp y5 y6 y7 s0 s1 x10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ munch [(Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8); (FLG, FLG + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SPV /\ AHEAP AI L RNG st LB m')
      (MS (mkR x1 (Z_to_bv 64 DSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x85aec) fc None m (seg_rom bsegs)).
  Proof.
    intros until jA. intros SAV FRA STL STG FFC SHF FLC AH MI EFL FH F64 FC LH LC FLS RF1 RF2 RF3.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof (fk_ablk_lits _ _ FH) as FL. pose proof (fk_ablk_lits _ _ LH) as LL.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof dspa_props as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    assert (BSF : SHB <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 8 <= 0x10007fff8000)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    unfold DFSH in SHF.
    pose proof (munch_refl [(Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8); (FLG, FLG + 1)] m) as MUL.
    pose proof (munch_refl [(Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8)] m) as MUS.
    pose proof (wmono_refl bsegs m) as WML.
    fk_hold AH. fk_hold FH. fk_hold LH. fk_hold EFL.
    zstep. replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity).
    df_sok FF 4%nat. zstep. clear SOK. zstep. zstep. zstep.
    df_sok FF 0%nat. zstep. clear SOK. zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    unfold fk_held in AH, FH.
    assert (AHA : AHEAP AI L RNG st (FB0 FF :: LB) mA).
    { eapply (AI_frame AI); [exact AH| exact MUS| exact WML|].
      constructor; [cbn [fst snd] | constructor].
      replace (Z.shiftr FF 3 + SHB) with (shad FF) by (unfold shad, ASHOFF; lia).
      replace (shad FF + 8 - shad FF) with 8 by lia.
      eapply (fk_acr_fshadow AI _ 0 FF 64 FF 8); [left; reflexivity | lia | lia | Z.div_mod_to_equations; lia | lia]. }
    clear MUS AH. pose proof (munch_refl [(FLG, FLG + 1)] mA) as MU2. fk_hold AHA. fk_hold FH.
    zstep.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
    unfold fk_held in AHA, EFL, LH.
    assert (AHB : AHEAP AI L RNG st LB mB).
    { subst FLG. eapply (fk_release AI fflag L RNG st LB mA mB 0 FF 64 FRL AHA); [lia | lia | lia | exact MU2 | exact FLC]. }
    clear MU2 AHA.
    zstep. zstep.
    unfold DSAVED in SAV.
    do 13 zstep.
    zstep. zstep.
    apply evtF_done.
    do 14 eexists. exists mB. split; [reflexivity|].
    pose proof (stk_of_rw_cells bsegs _ _ _ SAV) as SAVS. cbn [cells_size csize Nat.add length] in SAVS.
    pose proof (stk_of_rw_cells bsegs _ _ _ FRA) as FRAS. cbn [cells_size csize Nat.add length] in FRAS.
    split; [eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WML|]. split; [exact MI|]. split; [| exact AHB].
    eapply stk_merge; [exact STL | | lia].
    eapply stk_merge; [| eapply stk_merge; [exact STG | | lia] | lia].
    - replace (DSPA + 88) with (DSPA + Z.of_nat 88) by lia. exact FRAS.
    - replace SPV with (SPV + -104 + Z.of_nat 104) at 2 by lia. exact SAVS.
  Qed.

  Lemma df_err : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word) m (FF FLG r : Z)
      (j0 j1 j2 : word) (junk : list byte),
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> rng RNG FF 64 -> 0 < r < 2^64 ->
    evtF bsegs RNG (fun ms' => exists m' y11,
        ms' = MS (mkR x1 (Z_to_bv 64 DSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA)
                      (Z_to_bv 64 (if 2^64 - 120 <? r then r else -72)) y11 x12 x13 x14 x15 x16 x17
                      (Z_to_bv 64 FF) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) x27 x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x85aec) fc None m' (seg_rom bsegs)
        /\ munch [(FF, FF + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' FF [C8 (Z_to_bv 64 0x45e0360e); C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)])
      (MS (mkR x1 (Z_to_bv 64 DSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x85acc) fc None m (seg_rom bsegs)).
  Proof.
    intros until junk. intros FFC MI FH RF1 HR.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof (fk_ablk_lits _ _ FH) as FL.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof (munch_refl [(FF, FF + 8)] m) as MUL. pose proof (wmono_refl bsegs m) as WML.
    fk_hold FH.
    zstep.
    zstep. bcase K0.
    - zstep. zstep. zstep. zstep. bcase K1; [exfalso; lia|].
      apply evtF_done. eexists _, _. split; [|split; [exact MUL|]; split; [exact WML|]; split; [exact MI| exact FFC]].
      match goal with |- context [if ?c then _ else _] => replace c with true by (symmetry; apply Z.ltb_lt; lia) end. reflexivity.
    - zstep. bcase K1; [exfalso; lia|].
      zstep. zstep. zstep. zstep. zstep. bcase K2; [exfalso; lia|].
      apply evtF_done. eexists _, _. split; [|split; [exact MUL|]; split; [exact WML|]; split; [exact MI| exact FFC]].
      match goal with |- context [if ?c then _ else _] => replace c with false by (symmetry; apply Z.ltb_ge; lia) end. reflexivity.
  Qed.

  Lemma df_tail : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x27 x28 x29 x30 x31 : word) m (FF FLG DCTX hsz : Z)
      (pcs dsz bt stg le fe j0 j1 j2 : word) (junk : list byte),
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe] ->
    ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr (DCTX + 29976) 3 + SHB)) 1 = Some [Z_to_bv 8 0] ->
    rng RNG (Z.shiftr (DCTX + 29976) 3 + SHB) 1 -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> rng RNG FF 64 -> ablk DCTX (DCTX + 95992) -> DCTX mod 8 = 0 -> rng RNG DCTX 95992 ->
    (DCTX + 95992 <= FF \/ FF + 64 <= DCTX) -> 0 <= hsz < 2^64 ->
    evtF bsegs RNG (fun ms' => exists m' y11,
        ms' = MS (mkR x1 (Z_to_bv 64 DSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA) (Z_to_bv 64 0) y11 x12 x13 x14 x15 x16 x17
                      (Z_to_bv 64 FF) (Z_to_bv 64 SHB) x20 (Z_to_bv 64 (DCTX + 29976)) (Z_to_bv 64 hsz) x23 (Z_to_bv 64 (DCTX + 29956))
                      (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) x27 x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x85aec) fc None m' (seg_rom bsegs)
        /\ munch [(DCTX + 29976, DCTX + 29984); (FF, FF + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (DCTX + 29976) [C8 (Z_to_bv 64 (bv_unsigned pcs + hsz)); C8 dsz; C4 bt; C4 stg; C4 le; C4 fe]
        /\ rw_cells bsegs m' FF [C8 (Z_to_bv 64 0x45e0360e); C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)])
      (MS (mkR x1 (Z_to_bv 64 DSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) (Z_to_bv 64 SHB) x20 x21 (Z_to_bv 64 hsz) x23 (Z_to_bv 64 (DCTX + 29956))
               (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x85d60) fc None m (seg_rom bsegs)).
  Proof.
    intros until junk. intros FFC H3 RDz RTz MI FH RF1 DH D8 RD DFF HS.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof (fk_ablk_lits _ _ FH) as FL. pose proof (fk_ablk_lits _ _ DH) as DL.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof (munch_refl [(DCTX + 29976, DCTX + 29984); (FF, FF + 8)] m) as MUL. pose proof (wmono_refl bsegs m) as WML.
    fk_hold FH. fk_hold DH.
    zstep. zstep. zstep. zstep.
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
    zstep. zstep. zstep.
    zstep. zstep. zstep.
    zstep. bcase K1; [| exfalso; lia].
    apply evtF_done. eexists _, _. split; [reflexivity|].
    split; [exact MUL|]. split; [exact WML|]. split; [exact MI|]. split; [exact H3| exact FFC].
  Qed.

  Lemma df_tail9 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x27 x28 x29 x30 x31 : word) m (FF FLG DCTX hsz : Z)
      (pcs dsz bt stg le fe j0 j1 j2 : word) (junk : list byte),
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe] ->
    ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr (DCTX + 29976) 3 + SHB)) 1 = Some [Z_to_bv 8 0] ->
    rng RNG (Z.shiftr (DCTX + 29976) 3 + SHB) 1 -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> rng RNG FF 64 -> ablk DCTX (DCTX + 95992) -> DCTX mod 8 = 0 -> rng RNG DCTX 95992 ->
    (DCTX + 95992 <= FF \/ FF + 64 <= DCTX) -> 0 <= hsz < 2^64 ->
    evtF bsegs RNG (fun ms' => exists m' y11,
        ms' = MS (mkR x1 (Z_to_bv 64 DSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA) (Z_to_bv 64 0) y11 x12 x13 x14 x15 x16 x17
                      (Z_to_bv 64 FF) (Z_to_bv 64 SHB) x20 (Z_to_bv 64 (DCTX + 29976)) (Z_to_bv 64 hsz) x23 (Z_to_bv 64 (DCTX + 29956))
                      (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) x27 x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x85aec) fc None m' (seg_rom bsegs)
        /\ munch [(DCTX + 29976, DCTX + 29984); (FF, FF + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (DCTX + 29976) [C8 (Z_to_bv 64 (bv_unsigned pcs + hsz)); C8 dsz; C4 bt; C4 stg; C4 le; C4 fe]
        /\ rw_cells bsegs m' FF [C8 (Z_to_bv 64 0x45e0360e); C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)])
      (MS (mkR x1 (Z_to_bv 64 DSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) (Z_to_bv 64 SHB) x20 x21 (Z_to_bv 64 hsz) x23 (Z_to_bv 64 (DCTX + 29956))
               (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x85d44) fc None m (seg_rom bsegs)).
  Proof.
    intros until junk. intros FFC H3 RDz RTz MI FH RF1 DH D8 RD DFF HS.
    zstep. eapply df_tail; eassumption.
  Qed.

  Hypothesis XXHRESET : zd_xxh_reset_stmtA.
  Ltac df_shz D D8 DL ATR UD RDS k :=
    pose proof (df_sh_rd0 _ D 95992 (D + k) UD ltac:(clear; lia) ltac:(clear - D8; Z.div_mod_to_equations; lia) ltac:(clear - DL; lia) ltac:(clear - DL ATR; lia)) as RDz;
    assert (RTz : rng RNG (Z.shiftr (D + k) 3 + SHB) 1) by
      (eapply rng_sub'; [exact RDS|]; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8;
       unfold shspan; rewrite ?shad_div; unfold ASHOFF; clear - D8; Z.div_mod_to_equations; lia).

  Lemma df_ok : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x23 x27 x28 x29 x30 x31 : word) m (FF FLG DCTX hsz : Z) (h : frame_header)
      (pcs dsz bt stg le fe j0 j1 j2 : word) (junk : list byte) (xs : list cell) (ws : list word),
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (DCTX + 29928) (zfh_cells h) -> 0 <= fh_checksum h <= 1 ->
    dctx_h3 bsegs m DCTX pcs dsz bt stg le fe -> dctx_xs bsegs m DCTX xs -> dctx_h5 bsegs m DCTX ws -> h5_frame_ok ws ->
    unpoisoned m DCTX (DCTX + 95992) -> rng RNG (shad DCTX) (shspan DCTX 95992) -> ahull RNG m DCTX 95992 ->
    stk bsegs m lo DSPA -> art m -> mem_inv bsegs m ->
    ablk FF (FF + 64) -> rng RNG FF 64 -> ablk DCTX (DCTX + 95992) -> DCTX mod 8 = 0 -> rng RNG DCTX 95992 ->
    (DCTX + 95992 <= FF \/ FF + 64 <= DCTX) -> (DCTX + 95992 <= lo \/ SPV <= DCTX) -> 0 <= hsz < 2^64 ->
    evtF bsegs RNG (fun ms' => exists (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y27 y28 y29 y30 y31 : word) m' xs',
        ms' = MS (mkR y1 (Z_to_bv 64 DSPA) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA) (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17
                      (Z_to_bv 64 FF) y19 y20 y21 y22 y23 y24 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) y27 y28 y29 y30 y31)
                 FR (Z_to_bv 64 0x85aec) fc None m' (seg_rom bsegs)
        /\ munch [(DCTX + 29976, DCTX + 29984); (DCTX + 30008, DCTX + 30116); (FF, FF + 8); (DSPA - 2240, DSPA)] m m'
        /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo DSPA
        /\ dctx_h3 bsegs m' DCTX (Z_to_bv 64 (bv_unsigned pcs + hsz)) dsz bt stg le fe
        /\ dctx_xs bsegs m' DCTX xs'
        /\ dctx_h5 bsegs m' DCTX (wupd ws H5_validateChecksum (Z_to_bv 64 (if fh_checksum h =? 0 then 0 else 1)))
        /\ (if fh_checksum h =? 0 then xs' = xs else exists i1 i2, xs' = xxh_cells i1 0 i2)
        /\ rw_cells bsegs m' FF [C8 (Z_to_bv 64 0x45e0360e); C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)])
      (MS (mkR x1 (Z_to_bv 64 DSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 DSPA) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) (Z_to_bv 64 SHB) x20 (Z_to_bv 64 DCTX) (Z_to_bv 64 hsz) x23 (Z_to_bv 64 (DCTX + 29956))
               (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x85acc) fc None m (seg_rom bsegs)).
  Proof.
    intros until ws. intros FFC FPC RCK H3 XSC H5 H5OK UD RDS AHD STL ART MI FH RF1 DH D8 RD DFF DCS HS.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof (fk_ablk_lits _ _ FH) as FL. pose proof (fk_ablk_lits _ _ DH) as DL.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof dspa_props as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    destruct XSC as [XSC XSZ]. destruct H5 as [H5C H5L]. unfold dctx_h3 in H3. unfold zfh_cells in FPC.
    destruct H5OK as (_ & KFI & KRM & _).
    h5_open ws H5L. unfold wz0 in KFI, KRM.
    lazymatch type of KFI with ?x = _ => subst x end. lazymatch type of KRM with ?x = _ => subst x end.
    pose proof (munch_refl [(DCTX + 30112, DCTX + 30116)] m) as MUL. pose proof (wmono_refl bsegs m) as WML.
    fk_hold AHD. fk_hold ART. fk_hold XSC. fk_hold XSZ. fk_hold UD. fk_hold RDS.
    zstep. zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
    zstep. bcase K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia].
    unfold fk_held in UD, RDS.
    df_shz DCTX D8 DL ATR UD RDS 30224.
    zstep. zstep. zstep. zstep. clear RDz RTz.
    zstep. if_false.
    zstep. rewrite ?(sx32w_small 0) by lia. zstep. zstep. try (bcase K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia]).
    df_shz DCTX D8 DL ATR UD RDS 29960.
    zstep. zstep. zstep. zstep. clear RDz RTz.
    zstep. if_false.
    zstep. rewrite sx32w_small by (clear - RCK; lia).
    pose proof DH as DHu. unfold ablk, AIMG_HI, KLS in DHu.
    zstep. bcase KC.
    - df_shz DCTX D8 DL ATR UD RDS 30112.
      zstep. zstep. zstep. zstep. clear RDz RTz.
      zstep. if_false.
      zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      unfold fk_held in XSC, XSZ, AHD, ART.
      assert (UD1 : unpoisoned m1 DCTX (DCTX + 95992)).
      { eapply unpoisoned_munch; [exact UD| exact MUL|]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF.
        clear - DHu DL ATR D8. split; [| exact I]. Z.div_mod_to_equations. lia. }
      df_shz DCTX D8 DL ATR UD1 RDS 29976.
      eapply evtF_cut.
      { eapply df_tail; [eassumption| exact H3| exact RDz| exact RTz| eassumption| exact FH| exact RF1| exact DH| exact D8| exact RD| exact DFF| exact HS]. }
      cbv beta. intros ms' (m2 & y11 & -> & MU2 & WM2 & MI2 & H32 & FFC2).
      apply evtF_done. do 22 eexists. exists m2, xs. split; [reflexivity|].
      split; [eapply munch_trans; [eapply munch_weaken; [| exact MUL]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia|].
      split; [exact (wmono_trans _ _ _ _ WML WM2)|]. split; [exact MI2|].
      split; [eapply stk_transport_disjoint; [eassumption| exact MU2| exact WM2| cbn [disjoint_from]; clear - DCS FHc LOC LOS SPAB; lia]|].
      split; [exact H32|]. rewrite KC. change (0 =? 0) with true. cbv beta iota.
      split; [split; [| exact XSZ]; eapply rw_cells_transport; [eapply rw_cells_transport; [exact XSC| exact MUL| exact WML| rewrite XSZ; cbn [disjoint_from]; clear; lia]
                                                               | exact MU2| exact WM2| rewrite XSZ; cbn [disjoint_from]; clear - DFF; lia]|].
      split; [split; [| reflexivity]; cbv beta iota delta [h5_cells h5_sizes mk_wcells];
              eapply rw_cells_transport; [eassumption| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - DFF; lia]|].
      split; [reflexivity| exact FFC2].
    - df_shz DCTX D8 DL ATR UD RDS 30108.
      zstep. zstep. zstep. zstep. clear RDz RTz.
      zstep. if_false.
      df_shz DCTX D8 DL ATR UD RDS 30112.
      zstep. zstep. zstep. zstep. clear RDz RTz.
      zstep. rewrite ?(sx32w_small 0) by lia.
      zstep. if_false.
      zstep. zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      zstep. if_false.
      zstep. zstep. zstep. zstep.
      unfold fk_held in XSC, XSZ, AHD, ART.
      lazymatch goal with H : rw_cells _ m1 (DCTX + 30096) _ |- _ => change (Z.b2z (0 <? 1)) with 1 in H end.
      assert (UD1 : unpoisoned m1 DCTX (DCTX + 95992)).
      { eapply unpoisoned_munch; [exact UD| exact MUL|]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF.
        clear - DHu DL ATR D8. split; [| exact I]. Z.div_mod_to_equations. lia. }
      assert (XSC1 : rw_cells bsegs m1 (DCTX + 30008) xs)
        by (eapply rw_cells_transport; [exact XSC| exact MUL| exact WML| rewrite XSZ; cbn [disjoint_from]; clear; lia]).
      assert (AH1 : ahull RNG m1 (DCTX + 30008) 88).
      { destruct AHD as (RLO & RHI & A1 & A2 & A3 & A4 & A5 & A6 & W & R). exists RLO, RHI.
        split; [clear - A1; lia|]. split; [clear - A2; lia|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
        split; [eapply wr_at_transport; [exact W| exact WML]| exact R]. }
      assert (ART1 : art m1) by (eapply df_art_transport; [exact ART| exact MUL| exact WML| repeat constructor; cbn [fst]; clear - DL; lia]).
      unfold zd_xxh_reset_stmtA, APZD_XXH_RESET in XXHRESET.
      eapply evtF_cut.
      { eapply (XXHRESET RNG) with (SPV := DSPA) (lo := lo) (STA := DCTX + 30008) (cs0 := xs);
          first [ exact XSC1 | exact XSZ | exact AH1 | exact ART1 | eassumption | reflexivity
                | lazymatch goal with
                  | |- 4096 <= _ => clear - DL; lia
                  | |- (DCTX + 30008) mod 8 = 0 => clear - D8; Z.div_mod_to_equations; lia
                  | |- DCTX + 30008 + 88 <= _ => clear - DL ATR; lia
                  | |- lo <= DSPA - _ => clear - LOS SPAB; lia
                  | |- DSPA < _ => clear - SPT SPAB; lia
                  | |- DCTX + 30008 + 88 <= lo \/ _ => clear - DCS SPAB; lia
                  | |- areg _ _ _ _ => intros _; split; [eapply ablk_sub; [exact DH| clear; lia| clear; lia]| split; [eapply unpoisoned_sub; [exact UD1| clear; lia| clear; lia]|
                                        split; [eapply rng_sub'; [exact RD| clear; lia]| eapply rng_sub'; [exact RDS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - D8; Z.div_mod_to_equations; lia]]]]
                  | |- astk _ _ _ => split; [unfold KHIGH; clear - LOC ATR; lia| split; [eapply rng_sub'; [exact RSTK| clear - SPAB LO0; lia]| exact RI]]
                  end
                | lazymatch goal with |- ?Gg => idtac "XXH-LEFT:" Gg end ]. }
      cbv beta. intros ms' PO.
      destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & -> & MU2 & WM2 & MI2 & STL2 & [i1 [i2 XS2]]).
      rd_retlit.
      assert (UD2 : unpoisoned m2 DCTX (DCTX + 95992)).
      { eapply unpoisoned_munch; [exact UD1| exact MU2|]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF.
        clear - DHu DL ATR D8 LOC LOS SPAB. split; [| split; [| exact I]]; Z.div_mod_to_equations; lia. }
      assert (FFC2 : rw_cells bsegs m2 FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)])
        by (eapply rw_cells_transport; [eassumption| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - DFF FHc LOC LOS SPAB; lia]).
      assert (H32 : rw_cells bsegs m2 (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe])
        by (eapply rw_cells_transport; [eassumption| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - DCS SPAB LOS; lia]).
      df_shz DCTX D8 DL ATR UD2 RDS 29976.
      eapply evtF_cut.
      { eapply df_tail9; [exact FFC2| exact H32| exact RDz| exact RTz| exact MI2| exact FH| exact RF1| exact DH| exact D8| exact RD| exact DFF| exact HS]. }
      cbv beta. intros ms' (m3 & y11 & -> & MU3 & WM3 & MI3 & H33 & FFC3).
      apply evtF_done. do 22 eexists. exists m3, (xxh_cells i1 0 i2). split; [reflexivity|].
      split; [eapply munch_trans; [eapply munch_weaken; [| exact MUL]| eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]];
              unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia|].
      split; [exact (wmono_trans _ _ _ _ WML (wmono_trans _ _ _ _ WM2 WM3))|]. split; [exact MI3|].
      split; [eapply stk_transport_disjoint; [exact STL2| exact MU3| exact WM3| cbn [disjoint_from]; clear - DCS FHc LOC LOS SPAB; lia]|].
      split; [exact H33|]. replace (fh_checksum h =? 0) with false by (symmetry; apply Z.eqb_neq; exact KC). cbv beta iota.
      split; [split; [| reflexivity]; eapply rw_cells_transport; [exact XS2| exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ xxh_cells]; clear - DFF; lia]|].
      split; [split; [| reflexivity]; cbv beta iota delta [h5_cells h5_sizes mk_wcells];
              eapply rw_cells_transport; [eapply rw_cells_transport; [eassumption| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - DCS SPAB LOS; lia]
                                         | exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - DFF; lia]|].
      split; [exists i1, i2; reflexivity| exact FFC3].
  Qed.
End S.

Section FC.
Variable AI : AMallocIface.
Hypothesis FHL : fake_heap_law AI.
Lemma df_disjoint_from_sub1 : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[x y] W IH]; intros a n a' n' D H1 H2; cbn [disjoint_from] in *; [exact I|].
  destruct D as [D1 D2]. split; [lia| eapply IH; [exact D2| lia| lia]].
Qed.
Lemma df_fcall_bytes_pres : forall L RNG st LB m0 (m m' : amem) W X bs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (zlen bs) -> disjoint_from W X (zlen bs) ->
  munch (W ++ fake_area L) m m' -> ffr_pres W LB m m' -> bytes_at bsegs m X bs -> bytes_at bsegs m' X bs.
Proof.
  intros L RNG st LB m0 m m' W X bs AH (b & Hb & H1 & H2) DJ MU FP B.
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [DF _].
    eapply bytes_at_transport; [exact B| exact MU|]. apply disjoint_from_app2; [exact DJ| eapply df_disjoint_from_sub1; [exact DF| lia| lia]].
  - eapply bytes_at_magree; [exact FP| exact B|]. intros a Ha. left. split.
    + exists c, A, n. split; [exact Hb| lia].
    + eapply disjoint_outside; [exact DJ| lia].
Qed.
Lemma df_fcall_cells_pres : forall L RNG st LB m0 (m m' : amem) W X cs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (Z.of_nat (cells_size cs)) -> disjoint_from W X (Z.of_nat (cells_size cs)) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> rw_cells bsegs m X cs -> rw_cells bsegs m' X cs.
Proof.
  intros L RNG st LB m0 m m' W X cs AH IB DJ MU WM FP [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
  - eapply df_fcall_bytes_pres; [exact AH| rewrite cells_bytes_length by assumption; exact IB| rewrite cells_bytes_length by assumption; exact DJ| exact MU| exact FP| exact HB].
  - eapply wr_at_transport; [exact HW| exact WM].
Qed.
Lemma df_fcall_unp_pres : forall L RNG st LB m0 (m m' : amem) W X k,
  AHEAP AI L RNG st LB m0 -> ainblk LB X k -> 0 < k -> X + k <= KEND -> aappW W ->
  munch (W ++ fake_area L) m m' -> ffr_pres W LB m m' -> unpoisoned m X (X + k) -> unpoisoned m' X (X + k).
Proof.
  intros L RNG st LB m0 m m' W X k AH (b & Hb & H1 & H2) Hk XH HW MU FP U.
  pose proof U as (U0 & U1 & _).
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [_ DSF].
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hb) as (N & (BR & _) & _). pose proof (ablk_lin _ _ BR) as (L1 & L2 & L3 & L4).
    eapply unpoisoned_munch; [exact U| exact MU|]. apply disjoint_from_app2.
    + apply aappW_shadow_disjoint; [exact HW| | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia.
    + eapply df_disjoint_from_sub1; [exact DSF| |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  - eapply unpoisoned_agree; [exact U|]. intros s Hs.
    set (a' := Z.max X (8 * (s - ASHOFF))).
    assert (Ra : X <= a' < X + k).
    { subst a'. rewrite !shad_div in Hs. unfold ASHOFF in *. destruct (Z.max_spec X (8 * (s - 2147450880))) as [[Hm ->]|[Hm ->]]; Z.div_mod_to_equations; lia. }
    assert (Ea : shad a' = s).
    { subst a'. rewrite !shad_div in Hs. rewrite shad_div. unfold ASHOFF in *. destruct (Z.max_spec X (8 * (s - 2147450880))) as [[Hm ->]|[Hm ->]]; Z.div_mod_to_equations; lia. }
    destruct (FP s ltac:(rewrite !shad_div in Hs; unfold ASHOFF in Hs; unfold KEND in XH; Z.div_mod_to_equations; lia)
                 ltac:(right; exists a'; split; [exists c, A, n; split; [exact Hb| lia]| symmetry; exact Ea])) as [E _].
    exact E.
Qed.
Lemma df_ffr_mono : forall Wa Wb LBx (m m' : amem), (forall a, outside Wb a -> outside Wa a) -> ffr_pres Wa LBx m m' -> ffr_pres Wb LBx m m'.
Proof.
  intros Wa Wb LBx m m' HW H a Ha HP. apply (H a Ha). destruct HP as [[HF HO]|HS]; [left; split; [exact HF| exact (HW a HO)]| right; exact HS].
Qed.
Lemma df_ffr_tail : forall W b LB (m m' : amem), ffr_pres W (b :: LB) m m' -> ffr_pres W LB m m'.
Proof.
  intros W b LB m m' H a Ha HP. apply (H a Ha).
  destruct HP as [[(c & A & n & Hin & Hr) HO]|(a' & (c & A & n & Hin & Hr) & E)].
  - left. split; [exists c, A, n; split; [right; exact Hin| exact Hr]| exact HO].
  - right. exists a'. split; [exists c, A, n; split; [right; exact Hin| exact Hr]| exact E].
Qed.
Lemma df_ffr_frame_cells : forall W FF LB (m m' : amem) A cs,
  ffr_pres W (FB0 FF :: LB) m m' -> rw_cells bsegs m A cs -> FF <= A -> A + Z.of_nat (cells_size cs) <= FF + 64 ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> outside W a) -> rw_cells bsegs m' A cs.
Proof.
  intros W FF LB m m' A cs FP RC H1 H2 HO. eapply rw_cells_magree; [exact FP| exact RC|].
  intros a Ha. left. split; [| exact (HO a Ha)]. exists 0, FF, 64. split; [left; reflexivity| lia].
Qed.
Lemma df_ffr_fsh_cells : forall W FF LB (m m' : amem) cs,
  ffr_pres W (FB0 FF :: LB) m m' -> rw_cells bsegs m (Z.shiftr FF 3 + SHB) cs -> FF mod 8 = 0 -> 0 <= FF ->
  Z.of_nat (cells_size cs) <= 8 -> rw_cells bsegs m' (Z.shiftr FF 3 + SHB) cs.
Proof.
  intros W FF LB m m' cs FP RC F8 F0 SZ. eapply rw_cells_magree; [exact FP| exact RC|].
  rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  intros a Ha. right. exists (FF + 8 * (a - (FF / 8 + SHB))). split.
  - exists 0, FF, 64. split; [left; reflexivity|]. clear - Ha F8 SZ. Z.div_mod_to_equations. lia.
  - rewrite shad_div. unfold ASHOFF. clear - F8. Z.div_mod_to_equations. lia.
Qed.
End FC.

Section Thm.
  Variable AI : AMallocIface.
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis SM0K : forall k, Z.of_nat k < 16384 -> stack_malloc_0k_stmt AI fflag rng_fs k.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis FREL : fake_release_law AI fflag.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis GETFH : zd_getfh_stmtA AI rng_fs.
  Hypothesis XXHRESET : zd_xxh_reset_stmtA.

  Theorem zd_decodefh_proofA : zd_decodefh_stmtA AI rng_fs.
  Proof.
    intros L RNG st LB ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV DCTX SRC src off hsz
           fp pcs dsz bt stg le fe xs ws lo
           FP0 H30 XS0 H50 H5OK DC0 DC1 SB OK OFF0 HS5 OFS SRC0 ST LO SPR SDC SSR SDS AFP TP ARO ARS AIS D8 ARD AHD AIND MI -> -> ->.
    destruct AFP as (AH & ASH & ART & (KHI & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTKT & LBH).
    pose proof atop_range as ATR.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & LY5).
    destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
    destruct RTC as (C0 & GOT & RIC & REAL & SHBc & SUA & _).
    destruct (df_got_cells m (AI_relro AI _ _ _ _ _ AH)) as (G1 & G2).
    assert (LOS : lo <= SPV - 208 - 4096) by lia.
    assert (LOC : ATOP <= lo) by lia.
    assert (SPK : SPV + 16 < KEND) by (unfold KEND; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (dspa_props SPV SP16) as (SPAB & SPA32 & _).
    destruct (ARD ltac:(lia)) as (DBK & UD0 & RD1 & RD2).
    pose proof (fk_ablk_lits _ _ DBK) as DL.
    unfold APZD_DECODEFH.
    eapply evtF_cut.
    { eapply (df_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo SP16 SPK LOS LOC RNG RSTK RI);
        [exact ST| exact MI| exact SHBc| exact G1| exact G2| exact SUA]. }
    cbv beta. intros ms' (m1 & jA & -> & MU1 & WM1 & MI1 & SAV1 & FRA1 & STL1 & STG1).
    assert (AH1 : AHEAP AI L RNG st LB m1).
    { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
    pose proof (ASH 0 ltac:(lia)) as FLE.
    eapply evtF_cut.
    { pose proof (SM0K (Z.to_nat (4096 - 2)) ltac:(lia)) as SMC. unfold stack_malloc_0k_stmt in SMC. eapply SMC with (lo := lo); clear SMC;
        rewrite ?(unsigned_lit (DSPA SPV)) by lia;
        first [exact AH1| exact FLE| exact MI1| exact STL1| exact TP| reflexivity| exact RSTKT| exact RI| exact RFS| lia| unfold SMK_STACK; lia]. }
    cbv beta. intros ms' PO.
    destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                    & -> & MI2 & ST2 & HPR2 & AH2 & F64 & FH & FC & FFC2 & SHF2 & RFF & RSFF & MUF2 & WM2 & FFA1 & FFA2).
    rewrite ?(unsigned_lit (DSPA SPV)) in ST2, HPR2, MUF2 by lia.
    rd_retlit.
    destruct (ARS ltac:(lia)) as (SBK & US0 & RS1 & RS2). pose proof (fk_ablk_lits _ _ SBK) as SL.
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
    pose proof (fk_ablk_lits _ _ FH) as FL.
    assert (AINS : forall X k, DCTX <= X -> X + k <= DCTX + 95992 -> ainblk LB X k)
      by (intros X k Q1 Q2; destruct AIND as (b & Hb & B1 & B2); exists b; split; [exact Hb| split; lia]).
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ DCTX 95992 AH2 AIND ltac:(lia)) as DFF.
    assert (SRCAP : SRC + zlen src <= FF \/ FF + 64 <= SRC).
    { destruct (AIS ltac:(lia)) as [IB|[IM1 IM2]];
        [pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ SRC (zlen src) AH2 IB ltac:(lia)); lia| unfold AIMG_HI in IM2; lia]. }
    assert (FRA2 : rw_cells bsegs m2 (DSPA SPV) [CB 88 jA]) by (eapply aheap_pres_rw_cells; [exact HPR2| exact FRA1| left; left; cbn; lia]).
    assert (SAV2 : rw_cells bsegs m2 (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      by (eapply aheap_pres_rw_cells; [exact HPR2| exact SAV1| left; left; unfold DSAVED; cbn; lia]).
    pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
    assert (DD1 : forall X n, (X + n <= lo \/ SPV <= X) -> 0 <= n -> disjoint_from [(SPV - 192, SPV)] X n)
      by (intros X nn HX Hn; cbn [disjoint_from]; split; [lia| exact I]).
    assert (DS1 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(SPV - 192, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb. cbn [disjoint_from]. split; [| exact I]. left. rewrite !shad_div. unfold ASHOFF in *. clear - X0 Hn Hb ATR BOT LO. Z.div_mod_to_equations. lia. }
    assert (UD2 : unpoisoned m2 DCTX (DCTX + 95992)).
    { eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact AIND| lia|].
      eapply unpoisoned_munch; [exact UD0| exact MU1| apply DS1; clear - DL ATR; lia]. }
    assert (FMT2 : rw_cells bsegs m2 (DCTX + 30104) [C4 (Z_to_bv 64 0)]).
    { eapply (fk_cells_pres AI); [exact HPR2| apply AINS; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
      eapply rw_cells_transport; [exact (df_h5_fmt m DCTX ws H50 H5OK)| exact MU1| exact WM1| apply DD1; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]. }
    pose proof (df_sh_c1 m2 DCTX 95992 (DCTX + 30104) UD2 ltac:(lia) ltac:(clear - D8; Z.div_mod_to_equations; lia) ltac:(clear - DL; lia) ltac:(clear - DL ATR; lia)) as FMS2.
    assert (RF4 : rng RNG (DCTX + 30104) 4) by (eapply rng_sub'; [exact RD1| lia]).
    assert (RFS4 : rng RNG (Z.shiftr (DCTX + 30104) 3 + SHB) 1)
      by (eapply rng_sub'; [exact RD2|]; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold shspan; rewrite ?shad_div; unfold ASHOFF; clear - D8; Z.div_mod_to_equations; lia).
    eapply evtF_cut.
    { eapply df_hdr; first [exact FRA2| exact ST2| exact FFC2| exact SHF2| exact FMT2| exact FMS2| exact MI2| exact FH| exact FC| exact F64| exact RFF| exact RSFF
        | exact DBK| exact D8| exact DFF| exact SDC| exact RF4| exact RFS4| exact SP16| exact LOS| exact LOC| exact RSTK| lia]. }
    cbv beta. intros ms' (m3 & jA' & y14 & y15 & -> & MU3 & WM3 & MI3 & FRA3 & STL3 & FFC3 & SHF3).
    assert (BSF : SHB <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 8 <= 0x10007fff8000) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    assert (NZ : 0 < zlen src) by lia.
    assert (AH3 : AHEAP AI L RNG st (FB0 FF :: LB) m3).
    { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
      constructor; [cbn; left; left; lia|].
      constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|].
      constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                    change (2 ^ 3) with 8; unfold ASHOFF; Z.div_mod_to_equations; lia]| constructor]. }
    assert (ART3 : art m3).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH3) as (_ & A & B & C & D & E & F & G & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F|]. split; [exact G| exact C]. }
    assert (AFP3 : afpre AI rng_fs L RNG st (FB0 FF :: LB) m3 lo (DSPA SPV) 1).
    { unfold afpre, astk. split; [exact AH3|]. split; [apply ashort_push; [exact ASH| lia]|]. split; [exact ART3|].
      split; [split; [exact KHI| split; [eapply rng_sub'; [exact RSTK| lia]| exact RI]]|].
      split; [exact RFS|]. split; [exact BOT|]. split; [lia|]. split; [clear - SPA32; Z.div_mod_to_equations; lia|].
      split; [exact RSTKT| apply ablkLB_cons; [cbn [ab_addr ab_size]; exact FH| exact LBH]]. }
    assert (ARO3 : aro_client RNG m3).
    { assert (ARO1 : aro_client RNG m1)
        by (eapply aro_client_transport; [exact ARO| exact MU1| exact WM1| constructor; [cbn [fst snd]; right; unfold KHIGH; lia| constructor]]).
      assert (ARO2 : aro_client RNG m2).
      { eapply (aro_client_transport_F RNG m1 m2 [(DSPA SPV - SMK_STACK, DSPA SPV)] L); [exact ARO1| | exact WM2| | exact FAB].
        - eapply munch_weaken; [| exact MUF2]. unfold sub_fp. intros x Hx. rewrite fk_outside_app in Hx |- *. tauto.
        - constructor; [cbn [fst snd]; right; unfold KHIGH, SMK_STACK; lia| constructor]. }
      eapply aro_client_transport_gen; [exact WM3| exact ARO2| exact MU3|]. intros A n HIn.
      destruct (aclient_bounds A n HIn) as (B1 & B2 & B3). cbn [disjoint_from]. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ASHOFF.
      clear - B1 B2 B3 FL SPAB LOC LOS ATR. repeat split; Z.div_mod_to_equations; lia. }
    assert (D3S : disjoint_from [(DSPA SPV, DSPA SPV + 88); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8)] SRC (zlen src)).
    { cbn [disjoint_from]. split; [clear - SSR SPAB LO; lia|]. split; [clear - SRCAP; lia|]. split; [clear - SL BSF ATR; lia| exact I]. }
    assert (SB3 : bytes_at bsegs m3 SRC (map (Z_to_bv 8) src)).
    { eapply bytes_at_transport; [| exact MU3| rewrite length_map; exact D3S].
      destruct (AIS NZ) as [IB|[IM1 IM2]].
      - eapply (fk_bytes_pres AI); [exact HPR2| rewrite length_map; exact IB|].
        eapply bytes_at_transport; [exact SB| exact MU1| rewrite length_map; apply DD1; [exact SSR| lia]].
      - eapply bytes_at_transport; [| exact MUF2| rewrite length_map; cbn [disjoint_from fake_area app]; rewrite ?shad_div; unfold AIMG_HI, SMK_STACK, FAKESZ, ASHOFF in *;
          destruct LY5 as (_ & _ & FA1 & FA2); repeat split; clear - IM1 IM2 FA1 FA2 SPAB LO BOT ATR; Z.div_mod_to_equations; lia].
        eapply bytes_at_transport; [exact SB| exact MU1| rewrite length_map; apply DD1; [exact SSR| lia]]. }
    assert (US3 : unpoisoned m3 SRC (SRC + zlen src)).
    { eapply unpoisoned_munch; [| exact MU3|].
      - destruct (AIS NZ) as [IB|[IM1 IM2]].
        + eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact IB| lia|].
          eapply unpoisoned_munch; [exact US0| exact MU1| apply DS1; clear - SL ATR; lia].
        + eapply unpoisoned_munch; [| exact MUF2|].
          * eapply unpoisoned_munch; [exact US0| exact MU1| apply DS1; clear - SL ATR; lia].
          * cbn [disjoint_from fake_area app]. rewrite !shad_div. unfold AIMG_HI, SMK_STACK, FAKESZ, ASHOFF in *. destruct LY5 as (_ & _ & FA1 & FA2).
            clear - IM1 IM2 FA1 FA2 FABL SPAB LO BOT ATR OFS NZ. repeat split; Z.div_mod_to_equations; lia.
      - cbn [disjoint_from]. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ASHOFF.
        clear - SL FL SRCAP F64 SPAB LO BOT ATR NZ. repeat split; Z.div_mod_to_equations; lia. }
    assert (DD3 : forall X n, DCTX <= X -> X + n <= DCTX + 95992 -> 0 <= n ->
              disjoint_from [(DSPA SPV, DSPA SPV + 88); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8)] X n).
    { intros X nn Q1 Q2 Hn. cbn [disjoint_from]. split; [clear - Q1 Q2 SDC SPAB LO Hn; lia|]. split; [clear - Q1 Q2 DFF Hn; lia|].
      split; [clear - Q1 Q2 Hn DL BSF; lia| exact I]. }
    assert (DS3 : forall X n, DCTX <= X -> X + n <= DCTX + 95992 -> 0 < n ->
              disjoint_from [(DSPA SPV, DSPA SPV + 88); (FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn Q1 Q2 Hn. cbn [disjoint_from]. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ASHOFF.
      clear - Q1 Q2 Hn DL FL DFF F64 SPAB LO BOT ATR. repeat split; Z.div_mod_to_equations; lia. }
    assert (UD3 : unpoisoned m3 DCTX (DCTX + 95992)) by (eapply unpoisoned_munch; [exact UD2| exact MU3| apply DS3; lia]).
    assert (FP3 : rw_cells bsegs m3 (DCTX + 29928) fp).
    { destruct FP0 as [FPc FPz]. eapply rw_cells_transport; [| exact MU3| exact WM3| rewrite FPz; apply DD3; lia].
      eapply (fk_cells_pres AI); [exact HPR2| rewrite FPz; apply AINS; lia|].
      eapply rw_cells_transport; [exact FPc| exact MU1| exact WM1| rewrite FPz; apply DD1; lia]. }
    assert (AHW3 : wmono bsegs m m3) by exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3)).
    unfold zd_getfh_stmtA, APZD_GETFH in GETFH.
    eapply evtF_cut.
    { eapply (GETFH L RNG st (FB0 FF :: LB)) with (lo := lo) (ZFH := DCTX + 29928) (SRC := SRC) (src := src) (off := off) (size := hsz) (cs0 := fp);
      first [ exact SB3 | exact OK | exact OFF0 | exact HS5 | exact OFS | exact SRC0 | exact FP3 | exact (proj2 FP0) | exact STL3 | exact AFP3 | exact ARO3 | exact MI3 | exact TP | reflexivity
            | lazymatch goal with
              | |- (DCTX + 29928) mod 8 = 0 => clear - D8; Z.div_mod_to_equations; lia
              | |- areg _ _ SRC _ => intros _; split; [exact SBK| split; [exact US3| split; [exact RS1| exact RS2]]]
              | |- 0 < zlen src -> ainimg _ _ _ => intros _; destruct (AIS NZ) as [(b & Hb & Hb1 & Hb2)|IM]; [left; exists b; split; [right; exact Hb| lia]| right; exact IM]
              | |- areg _ _ _ _ => intros _; split; [eapply ablk_sub; [exact DBK| lia| lia]| split; [eapply unpoisoned_sub; [exact UD3| lia| lia]|
                                     split; [eapply rng_sub'; [exact RD1| lia]| eapply rng_sub'; [exact RD2| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - D8; Z.div_mod_to_equations; lia]]]]
              | |- ahull _ _ _ _ => destruct AHD as (RLO & RHI & A1 & A2 & A3 & A4 & A5 & A6 & W & R); exists RLO, RHI;
                                     split; [lia|]; split; [lia|]; split; [exact A3|]; split; [exact A4|]; split; [exact A5|]; split; [exact A6|];
                                     split; [eapply wr_at_transport; [exact W| exact AHW3]| exact R]
              | |- ainblk _ _ _ => destruct (AINS (DCTX + 29928) 48 ltac:(lia) ltac:(lia)) as (b & Hb & Hb1); exists b; split; [right; exact Hb| exact Hb1]
              | |- _ => lia
              end
            | lazymatch goal with |- ?Gg => idtac "GETFH-LEFT:" Gg end ]. }
    cbv beta. intros ms' PO.
    destruct PO as (g5 & g6 & g7 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g28 & g29 & g30 & g31 & m5 & cs & -> & MU5 & WM5 & MI5 & ST5 & FFR5 & AH5 & ZC5 & ZSZ5 & ZOK5).
    rd_retlit.
    assert (AHW5 : wmono bsegs m m5) by exact (wmono_trans _ _ _ _ AHW3 WM5).
    destruct (FFLAG _ _ _ _ _ 0 FF 64 AH5 ltac:(left; reflexivity)) as (XL5 & RL & LBK & LTOP & LAP & _ & LFA).
    pose proof (fk_ablk_lits _ _ LBK) as LL.
    assert (QFL : FF + 64 <= fflag L 0 FF \/ fflag L 0 FF + 1 <= FF)
      by (pose proof (LAP (FB0 FF) (or_introl eq_refl)) as Q; cbn [ab_addr ab_size] in Q; clear - Q; lia).
    assert (QDL : DCTX + 95992 <= fflag L 0 FF \/ fflag L 0 FF + 1 <= DCTX)
      by (destruct AIND as (b & Hb & B1 & B2); pose proof (LAP b (or_intror Hb)) as Q; clear - Q B1 B2; lia).
    assert (ESH : Z.shiftr FF 3 + SHB = shad FF)
      by (rewrite shad_div, Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold ASHOFF; lia).
    assert (QDH : DCTX + 95992 <= Z.shiftr FF 3 + SHB \/ Z.shiftr FF 3 + SHB + 8 <= DCTX) by (clear - DL BSF; lia).
    assert (QHF : FF + 64 <= Z.shiftr FF 3 + SHB \/ Z.shiftr FF 3 + SHB + 8 <= FF) by (clear - FL BSF ATR; lia).
    assert (QHS : Z.shiftr FF 3 + SHB + 8 <= lo) by (clear - BSF KHI LOC ATR; unfold KHIGH in KHI; lia).
    assert (QFS : FF + 64 <= lo) by (clear - FC LOC; lia).
    assert (QLS : fflag L 0 FF + 1 <= lo) by (clear - LTOP LOC; lia).
    assert (QSF : shad (al_fake L) <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 8 <= shad (al_fake L) + FAKESZ / 8).
    { assert (FA8 : al_fake L mod 8 = 0) by (unfold al_fake; Z.div_mod_to_equations; lia).
      rewrite shad_div, Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      clear - FFA1 FFA2 F64 FA8. unfold ASHOFF, FAKESZ in *. Z.div_mod_to_equations. lia. }
    assert (QAS : al_fake L + FAKESZ <= lo /\ shad (al_fake L) + FAKESZ / 8 <= lo).
    { destruct LY5 as (_ & _ & FA1 & FA2). rewrite shad_div.
      clear - FA1 FA2 LOC KHI ATR. unfold FAKESZ, ASHOFF, KHIGH in *. Z.div_mod_to_equations. lia. }
    assert (SAV5 : rw_cells bsegs m5 (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { eapply rw_cells_transport; [| exact MU5| exact WM5| unfold DSAVED; cbn [disjoint_from fake_area app cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                                   clear - QAS SDC SPAB LO; lia].
      eapply rw_cells_transport; [exact SAV2| exact MU3| exact WM3| unfold DSAVED; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                                   clear - SPAB LO QFS QHS; lia]. }
    assert (FRA5 : rw_cells bsegs m5 (DSPA SPV) [CB 80 jA'; C8 (Z_to_bv 64 FF)])
      by (eapply rw_cells_transport; [exact FRA3| exact MU5| exact WM5| cbn [disjoint_from fake_area app cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                                      clear - QAS SDC SPAB LO; lia]).
    assert (STG5 : stk bsegs m5 (DSPA SPV + 88) (SPV + -104)).
    { eapply stk_transport_disjoint; [| exact MU5| exact WM5| cbn [disjoint_from fake_area app]; clear - QAS SDC SPAB LO; lia].
      eapply stk_transport_disjoint; [exact STG2| exact MU3| exact WM3| cbn [disjoint_from]; clear - SPAB LO QFS QHS; lia]. }
    assert (FFC5 : rw_cells bsegs m5 FF (DFHDR (fflag L 0 FF) junk)).
    { eapply df_ffr_frame_cells; [exact FFR5| exact FFC3| lia| unfold DFHDR; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
      intros a Ha. unfold DFHDR in Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. cbn [outside]. clear - Ha DFF. lia. }
    unfold DFHDR in FFC5.
    assert (SHF5 : rw_cells bsegs m5 (Z.shiftr FF 3 + SHB) DFSH)
      by (eapply df_ffr_fsh_cells; [exact FFR5| exact SHF3| clear - F64; Z.div_mod_to_equations; lia| clear - FL; lia|
                                     unfold DFSH; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
    assert (TR5 : forall X cs0, DCTX <= X -> X + Z.of_nat (cells_size cs0) <= DCTX + 95992 ->
                    (X + Z.of_nat (cells_size cs0) <= DCTX + 29928 \/ DCTX + 29976 <= X) ->
                    rw_cells bsegs m X cs0 -> rw_cells bsegs m5 X cs0).
    { intros X cs0 Q1 Q2 Q3 RC.
      eapply (df_fcall_cells_pres AI FHL); [exact AH5| | | exact MU5| exact WM5| |].
      - destruct (AINS X _ Q1 Q2) as (b & Hb & Hb1). exists b. split; [right; exact Hb| exact Hb1].
      - cbn [disjoint_from]. clear - Q1 Q2 Q3 SDC SPAB LO. lia.
      - eapply df_ffr_mono; [| exact FFR5]. intros a Ha. clear - Ha. cbn [outside] in *. tauto.
      - eapply rw_cells_transport; [| exact MU3| exact WM3| apply DD3; clear - Q1 Q2; lia].
        eapply (fk_cells_pres AI); [exact HPR2| apply AINS; clear - Q1 Q2; lia|].
        eapply rw_cells_transport; [exact RC| exact MU1| exact WM1| apply DD1; clear - Q1 Q2 SDC; lia]. }
    assert (H35 : dctx_h3 bsegs m5 DCTX pcs dsz bt stg le fe).
    { unfold dctx_h3 in H30 |- *. apply TR5; [lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|
                                                 cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| exact H30]. }
    assert (XS5 : dctx_xs bsegs m5 DCTX xs).
    { destruct XS0 as [XC XZ]. split; [| exact XZ]. apply TR5; [lia| rewrite XZ; lia| rewrite XZ; lia| exact XC]. }
    assert (H55 : dctx_h5 bsegs m5 DCTX ws).
    { destruct H50 as [HC HZ]. split; [| exact HZ].
      apply TR5; [lia| rewrite (h5_cells_size ws HZ); lia| rewrite (h5_cells_size ws HZ); lia| exact HC]. }
    assert (UD5 : unpoisoned m5 DCTX (DCTX + 95992)).
    { eapply (df_fcall_unp_pres AI FHL); [exact AH5| | lia| unfold KEND; lia| | exact MU5| | exact UD3].
      - destruct AIND as (b & Hb & B1 & B2). exists b. split; [right; exact Hb| lia].
      - constructor; [cbn [fst snd]; clear - DL; unfold KLOW, KHIGH; lia|
                      constructor; [cbn [fst snd]; clear - KHI LO SPAB; unfold KHIGH in *; lia| constructor]].
      - eapply df_ffr_mono; [| exact FFR5]. intros a Ha. clear - Ha. cbn [outside] in *. tauto. }
    assert (AHD5 : ahull RNG m5 DCTX 95992).
    { destruct AHD as (RLO & RHI & A1 & A2 & A3 & A4 & A5 & A6 & W & R); exists RLO, RHI.
      split; [lia|]; split; [lia|]; split; [exact A3|]; split; [exact A4|]; split; [exact A5|]; split; [exact A6|].
      split; [eapply wr_at_transport; [exact W| exact AHW5]| exact R]. }
    assert (ART5 : art m5).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH5) as (_ & A & B & C & D & E & F & G & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F|]. split; [exact G| exact C]. }
    assert (FIN : forall m6 r (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 j0' j1' j2' : word) junk' fp' pcs' xs' ws',
      munch [(DCTX + 29976, DCTX + 29984); (DCTX + 30008, DCTX + 30116); (FF, FF + 8); (DSPA SPV - 2240, DSPA SPV)] m5 m6 ->
      wmono bsegs m5 m6 -> mem_inv bsegs m6 -> stk bsegs m6 lo (DSPA SPV) ->
      rw_cells bsegs m6 FF [C8 j0'; C8 j1'; C8 j2'; CB 32 junk'; C8 (Z_to_bv 64 (fflag L 0 FF))] ->
      dctx_fp bsegs m6 DCTX fp' -> dctx_h3 bsegs m6 DCTX pcs' dsz bt stg le fe -> dctx_xs bsegs m6 DCTX xs' -> dctx_h5 bsegs m6 DCTX ws' ->
      Z_to_bv 64 r = Z_to_bv 64 (decode_frame_header src off hsz) ->
      match get_frame_header src off hsz with
      | FH_ok h => fp' = zfh_cells h
                   /\ pcs' = Z_to_bv 64 (bv_unsigned pcs + hsz)
                   /\ ws' = wupd ws H5_validateChecksum (Z_to_bv 64 (if fh_checksum h =? 0 then 0 else 1))
                   /\ (if fh_checksum h =? 0 then xs' = xs else exists i1 i2, xs' = xxh_cells i1 0 i2)
      | FH_ret _ => pcs' = pcs /\ xs' = xs /\ ws' = ws
      end ->
      evtF bsegs RNG (zd_decodefh_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DCTX src off hsz pcs dsz bt stg le fe xs ws lo m)
        (MS (mkR x1 (Z_to_bv 64 (DSPA SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (DSPA SPV)) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 FF) x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) x27 x28 x29 x30 x31)
            FR (Z_to_bv 64 0x85aec) fc None m6 (seg_rom bsegs))).
    { intros m6 r x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 j0' j1' j2' junk' fp' pcs' xs' ws'
        MU6 WM6 MI6 STL6 FFC6 FP6 H36 XS6 H56 ER CASES.
      assert (SAV6 : rw_cells bsegs m6 (SPV + -104) (DSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
        by (eapply rw_cells_transport; [exact SAV5| exact MU6| exact WM6| unfold DSAVED; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                                        clear - SDC SPAB LO QFS; lia]).
      assert (FRA6 : rw_cells bsegs m6 (DSPA SPV) [CB 80 jA'; C8 (Z_to_bv 64 FF)])
        by (eapply rw_cells_transport; [exact FRA5| exact MU6| exact WM6| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                                        clear - SDC SPAB LO QFS; lia]).
      destruct (rw_cells_forget _ _ _ _ FRA6) as [jA6 FRA6']. cbn [cells_size csize Nat.add] in FRA6'.
      assert (STG6 : stk bsegs m6 (DSPA SPV + 88) (SPV + -104))
        by (eapply stk_transport_disjoint; [exact STG5| exact MU6| exact WM6| cbn [disjoint_from]; clear - SDC SPAB LO QFS; lia]).
      assert (SHF6 : rw_cells bsegs m6 (Z.shiftr FF 3 + SHB) DFSH)
        by (eapply rw_cells_transport; [exact SHF5| exact MU6| exact WM6| unfold DFSH; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                                        clear - QDH QHF QHS SPAB LO; lia]).
      assert (XL6 : rw_cells bsegs m6 (fflag L 0 FF) [C1 (Z_to_bv 8 1)])
        by (eapply rw_cells_transport; [exact XL5| exact MU6| exact WM6| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                                        clear - QDL QFL QLS SPAB LO; lia]).
      assert (AH6 : AHEAP AI L RNG st (FB0 FF :: LB) m6).
      { eapply (AI_frame AI); [exact AH5| exact MU6| exact WM6|]. destruct AIND as (b & Hb & B1 & B2).
        constructor; [cbn; right; left; exists b; split; [right; exact Hb| cbn [fst snd]; lia]|].
        constructor; [cbn; right; left; exists b; split; [right; exact Hb| cbn [fst snd]; lia]|].
        constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|].
        constructor; [cbn; left; left; lia| constructor]. }
      eapply evtF_cut.
      { eapply df_epi; first [ exact SAV6 | exact FRA6' | exact STL6 | exact STG6 | exact FFC6 | exact SHF6 | exact XL6 | exact AH6 | exact MI6
                             | exact FH | exact F64 | exact FC | exact LBK | exact LTOP | exact QFL | exact RFF | (rewrite ESH; exact RSFF) | exact RL
                             | exact SP16 | exact SPK | exact LOS | exact LOC | exact RSTK | exact RI | exact FREL | reflexivity | exact (Z_to_bv 64 0)
                             | lazymatch goal with |- ?Gg => idtac "EPI-LEFT:" Gg; fail end ]. }
      cbv beta. intros ms' (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m7 & -> & MU7 & WM7 & MI7 & ST7 & AH7).
      apply evtF_done. unfold zd_decodefh_postA.
      do 14 eexists. exists m7, fp', pcs', xs', ws'.
      split; [rewrite ER; reflexivity|].
      split.
      { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; unfold sub_fp; intros x Hx; clear - Hx SPAB; cbn [outside app fake_area] in *; lia|].
        eapply munch_trans; [eapply munch_weaken; [| exact MUF2]; unfold sub_fp; intros x Hx; clear - Hx SPAB; cbn [outside app fake_area] in *; unfold SMK_STACK in *; lia|].
        eapply munch_trans; [eapply munch_weaken; [| exact MU3]; unfold sub_fp; intros x Hx; clear - Hx SPAB QSF FFA1 FFA2; cbn [outside app fake_area] in *; lia|].
        eapply munch_trans; [eapply munch_weaken; [| exact MU5]; unfold sub_fp; intros x Hx; clear - Hx SPAB; cbn [outside app fake_area] in *; lia|].
        eapply munch_trans; [eapply munch_weaken; [| exact MU6]; unfold sub_fp; intros x Hx; clear - Hx SPAB FFA1 FFA2; cbn [outside app fake_area] in *; lia|].
        eapply munch_weaken; [| exact MU7]; unfold sub_fp; intros x Hx; clear - Hx QSF LFA; cbn [outside app fake_area] in *; lia. }
      split; [exact (wmono_trans _ _ _ _ AHW5 (wmono_trans _ _ _ _ WM6 WM7))|].
      split; [exact MI7|].
      split; [exact ST7|].
      split.
      { assert (F02 : ffr_pres [] LB m m2).
        { eapply ffr_pres_trans; [eapply (fk_ffr_stack AI); [exact AH| exact MU1| exact WM1| constructor; [cbn; lia| constructor]]|].
          eapply fk_ffr_of_pres. exact HPR2. }
        assert (F23 : ffr_pres [] LB m2 m3).
        { eapply (fk_ffr_fin AI L RNG st LB m2 m2 m3 0 FF 64 (Z.shiftr FF 3 + SHB) 8 [] [(DSPA SPV, DSPA SPV + 88); (FF, FF + 24)]);
            [exact AH2| exact LBH| exact FH| clear - F64; Z.div_mod_to_equations; lia| exact ESH| lia| lia| | constructor| apply ffr_pres_refl| exact MU3| exact WM3].
          constructor; [cbn [fst snd]; split; [lia| left; split; [lia| clear - SPAB SPT LY3; lia]]|].
          constructor; [cbn [fst snd]; split; [lia| right; split; [intros b Hb; pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH2 b Hb) as Q; clear - Q; lia|
                                                               exists FF, (FF + 64); split; [exact FH| lia]]]| constructor]. }
        pose proof (df_ffr_tail _ _ _ _ _ FFR5) as F35.
        assert (F57 : ffr_pres [(DCTX + 29976, DCTX + 29984); (DCTX + 30008, DCTX + 30116)] LB m5 m7).
        { eapply (fk_ffr_fin AI L RNG st LB m5 m5 m7 0 FF 64 (Z.shiftr FF 3 + SHB) 8 _ [(FF, FF + 8); (DSPA SPV - 2240, DSPA SPV); (fflag L 0 FF, fflag L 0 FF + 1)]);
            [exact AH5| exact LBH| exact FH| clear - F64; Z.div_mod_to_equations; lia| exact ESH| lia| lia| | | apply ffr_pres_refl| | exact (wmono_trans _ _ _ _ WM6 WM7)].
          - constructor; [cbn [fst snd]; split; [lia| right; split; [intros b Hb; pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH5 b Hb) as Q; clear - Q; lia|
                                                                 exists FF, (FF + 64); split; [exact FH| lia]]]|].
            constructor; [cbn [fst snd]; split; [lia| left; split; [lia| clear - SPAB SPT LY3; lia]]|].
            constructor; [cbn [fst snd]; split; [lia| right; split; [intros b Hb; pose proof (LAP b (or_intror Hb)) as Q; clear - Q; lia|
                                                                 exists (fflag L 0 FF), (fflag L 0 FF + 1); split; [exact LBK| lia]]]| constructor].
          - constructor; [cbn [fst snd]; split; [exists DCTX, (DCTX + 95992); split; [exact DBK| lia]| lia]|].
            constructor; [cbn [fst snd]; split; [exists DCTX, (DCTX + 95992); split; [exact DBK| lia]| lia]| constructor].
          - eapply munch_trans; [eapply munch_weaken; [| exact MU6]| eapply munch_weaken; [| exact MU7]]; unfold sub_fp; intros x Hx; clear - Hx;
              cbn [outside app] in *; lia. }
        eapply ffr_pres_trans; [eapply df_ffr_mono; [| exact F02]; intros a _; exact I|].
        eapply ffr_pres_trans; [eapply df_ffr_mono; [| exact F23]; intros a _; exact I|].
        eapply ffr_pres_trans; [eapply df_ffr_mono; [| exact F35]; intros a Ha; clear - Ha; cbn [outside] in *; lia|].
        eapply df_ffr_mono; [| exact F57]; intros a Ha; clear - Ha; cbn [outside] in *; lia. }
      split; [exact AH7|].
      assert (TR7 : forall X cs0, DCTX <= X -> X + Z.of_nat (cells_size cs0) <= DCTX + 95992 -> rw_cells bsegs m6 X cs0 -> rw_cells bsegs m7 X cs0)
        by (intros X cs0 Q1 Q2 RC; eapply rw_cells_transport; [exact RC| exact MU7| exact WM7| cbn [disjoint_from]; clear - Q1 Q2 QDH QDL; lia]).
      split; [destruct FP6 as [FC6 FZ6]; split; [apply TR7; [lia| rewrite FZ6; lia| exact FC6]| exact FZ6]|].
      split; [unfold dctx_h3 in H36 |- *; apply TR7; [lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| exact H36]|].
      split; [destruct XS6 as [XC6 XZ6]; split; [apply TR7; [lia| rewrite XZ6; lia| exact XC6]| exact XZ6]|].
      split; [destruct H56 as [HC6 HZ6]; split; [apply TR7; [lia| rewrite (h5_cells_size ws' HZ6); lia| exact HC6]| exact HZ6]|].
      exact CASES. }
    assert (HSB : 0 <= hsz < 2^64) by (clear - DB OFS OFF0 HS5 SRC0; lia).
    destruct (get_frame_header src off hsz) as [h|v] eqn:G; cbn [fh_retval].
    - first [pose proof (ZOK5 h G) as ZE| pose proof (ZOK5 h eq_refl) as ZE]. subst cs.
      assert (CK : 0 <= fh_checksum h <= 1)
        by first [ destruct (get_frame_header_ok src OK off hsz h G) as (_ & _ & _ & _ & _ & _ & _ & X & _); exact X
                 | destruct (get_frame_header_ok src off hsz h G) as (_ & _ & _ & _ & _ & _ & _ & X & _); exact X ].
      eapply evtF_cut.
      { eapply df_ok; first [ exact FFC5 | exact ZC5 | exact CK | exact H35 | exact XS5 | exact H55 | exact H5OK | exact UD5 | exact RD2 | exact AHD5
                            | exact ST5 | exact ART5 | exact MI5 | exact FH | exact RFF | exact DBK | exact D8 | exact RD1 | exact DFF | exact SDC | exact HSB
                            | exact SP16 | exact SPK | exact LOS | exact LOC | exact RSTK | exact RI | exact FREL | exact XXHRESET | exact (Z_to_bv 64 0)
                            | lazymatch goal with |- ?Gg => idtac "OK-LEFT:" Gg; fail end ]. }
      cbv beta. intros ms' (k1 & k5 & k6 & k7 & k11 & k12 & k13 & k14 & k15 & k16 & k17 & k19 & k20 & k21 & k22 & k23 & k24 & k27 & k28 & k29 & k30 & k31
                            & m6 & xs' & -> & MU6 & WM6 & MI6 & STL6 & H36 & XS6 & H56 & XC6 & FFC6).
      eapply FIN; [ eapply munch_weaken; [| exact MU6]; unfold sub_fp; intros x Hx; clear - Hx; cbn [outside] in *; lia
                  | exact WM6 | exact MI6 | exact STL6 | exact FFC6
                  | split; [eapply rw_cells_transport; [exact ZC5| exact MU6| exact WM6| rewrite ZSZ5; cbn [disjoint_from]; clear - SDC SPAB LO DFF; lia]| exact ZSZ5]
                  | exact H36 | exact XS6 | exact H56
                  | unfold decode_frame_header; try rewrite G; reflexivity
                  | try rewrite G; cbv beta iota; split; [reflexivity| split; [reflexivity| split; [reflexivity| exact XC6]]] ].
    - assert (VR : 0 < v < 2^64).
      { assert (GR : v = ZD_FRAMEHEADERSIZE_PREFIX \/ v = ZD_SKIPPABLEHEADERSIZE \/
                     (v = frame_header_size src off ZD_FRAMEHEADERSIZE_PREFIX /\ hsz < v) \/
                     v = ZERR ZE_prefix_unknown \/ v = ZERR ZE_frameParameter_unsupported \/ v = ZERR ZE_frameParameter_windowTooLarge)
          by first [exact (get_frame_header_ret src OK off hsz v G) | exact (get_frame_header_ret src off hsz v G)].
        pose proof (frame_header_size_range src off ZD_FRAMEHEADERSIZE_PREFIX (Z.le_refl _)) as FHR.
        clear - GR FHR HS5.
        unfold ZD_FRAMEHEADERSIZE_PREFIX, ZD_SKIPPABLEHEADERSIZE, ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX, ZERR,
               ZE_prefix_unknown, ZE_frameParameter_unsupported, ZE_frameParameter_windowTooLarge in *.
        lia. }
      eapply evtF_cut.
      { eapply df_err; first [ exact FFC5 | exact MI5 | exact FH | exact RFF | exact VR
                             | exact SP16 | exact SPK | exact LOS | exact LOC | exact RSTK | exact RI | exact (Z_to_bv 64 0)
                             | lazymatch goal with |- ?Gg => idtac "ERR-LEFT:" Gg; fail end ]. }
      cbv beta. intros ms' (m6 & y11 & -> & MU6 & WM6 & MI6 & FFC6).
      assert (TR6 : forall X cs0, DCTX <= X -> X + Z.of_nat (cells_size cs0) <= DCTX + 95992 -> rw_cells bsegs m5 X cs0 -> rw_cells bsegs m6 X cs0)
        by (intros X cs0 Q1 Q2 RC; eapply rw_cells_transport; [exact RC| exact MU6| exact WM6| cbn [disjoint_from]; clear - Q1 Q2 DFF; lia]).
      eapply FIN; [ eapply munch_weaken; [| exact MU6]; unfold sub_fp; intros x Hx; clear - Hx; cbn [outside] in *; lia
                  | exact WM6 | exact MI6
                  | eapply stk_transport_disjoint; [exact ST5| exact MU6| exact WM6| cbn [disjoint_from]; clear - QFS SPAB LO; lia]
                  | exact FFC6
                  | split; [apply TR6; [lia| | exact ZC5]; rewrite ZSZ5; lia| exact ZSZ5]
                  | unfold dctx_h3 in H35 |- *; apply TR6; [lia| | exact H35]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                  | destruct XS5 as [XC XZ]; split; [apply TR6; [lia| | exact XC]; rewrite XZ; lia| exact XZ]
                  | destruct H55 as [HC HZ]; split; [apply TR6; [lia| | exact HC]; rewrite (h5_cells_size ws HZ); lia| exact HZ]
                  | unfold decode_frame_header; try rewrite G; unfold zd_is_error, ZE_maxCode, ZERR, ZE_srcSize_wrong;
                    destruct (2^64 - 120 <? v); [reflexivity| apply Z_to_bv_eqm; reflexivity]
                  | try rewrite G; cbv beta iota; split; [reflexivity| split; reflexivity] ].
  Qed.
End Thm.

End CANSEC1.
