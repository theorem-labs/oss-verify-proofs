(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_fkit AZ_fserd_iface AF_fse_rd_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_loop AF_fse_rd_hdr AF_fse_rd_seg AF_fse_rd_asm
     AZ_fserd_err.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zsize_c8 : forall c, Z.of_nat (cells_size [C8 c]) = 8. Proof. reflexivity. Qed.
Lemma zsize_c4 : forall c, Z.of_nat (cells_size [C4 c]) = 4. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bytes_at_nil : forall (m m' : amem) A, bytes_at bsegs m A [] -> bytes_at bsegs m' A [].
Proof. intros m m' A (H0 & H1 & _). split; [exact H0|]. split; [exact H1|]. intros i Hi. cbn [length] in Hi. lia. Qed.
Lemma bytes_at_len0 : forall (m m' : amem) A (bs : list byte), bytes_at bsegs m A bs -> length bs = 0%nat -> bytes_at bsegs m' A bs.
Proof. intros m m' A bs H L. destruct bs; [exact (bytes_at_nil m m' A H)| discriminate L]. Qed.

(* [comment removed for export] *)
Lemma shspan_4 : forall A, A mod 4 = 0 -> shspan A 4 = 1.
Proof. intros A H. unfold shspan. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma ainimg_apart_frame : forall LB X n FF, (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  AIMG_HI <= FF -> (0 < n -> ainimg LB X n) -> 0 <= n -> X + n <= FF \/ FF + 64 <= X \/ n = 0.
Proof.
  intros LB X n FF FFD HFF HI Hn. destruct (Z.eq_dec n 0) as [->|NZ]; [right; right; reflexivity|].
  destruct (HI ltac:(lia)) as [(b & Hb & H1 & H2)|(H1 & H2)].
  - destruct (FFD b Hb); [right; left; lia| left; lia].
  - left. lia.
Qed.

(* [comment removed for export] *)
Section S1z.
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP lo : Z).
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis LOS : lo <= SP - 176 - 4096.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Notation SPAz := (AF_fse_rd_seg.SPAz SP).

  Lemma rd_small1z : forall (x1 x10 x11 x12 x13 x14 x15 x5 x6 x7 x16 x17 x27 x28 x29 x30 x31 : word) m (FF FLG MSVP BUF NC TLP : Z)
      (buf : list Z) (junk : list byte) (RLO1 RHI1 : Z) (Q : machine_state -> Prop),
    0 <= zlen buf < 8 -> Forall (fun c => 0 <= c < 256) buf ->
    bytes_at bsegs m BUF (map (Z_to_bv 8) buf) ->
    rw_cells bsegs m FF (RFFHDR FF FLG junk) -> rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) RFFSH ->
    mem_inv bsegs m -> stk bsegs m lo SPAz ->
    rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
    app_blk BUF (BUF + zlen buf) -> unpoisoned m BUF (BUF + zlen buf) ->
    (RLO1 <= BUF /\ BUF + zlen buf <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND) ->
    wr_at bsegs m (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO1) (shad RHI1 - shad RLO1) ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> (BUF + zlen buf <= FF \/ FF + 64 <= BUF \/ zlen buf = 0) -> ablk BUF (BUF + zlen buf) ->
    rng RNG FF 64 -> rng RNG (shad FF) 8 -> rng RNG BUF (zlen buf) ->
    (forall m' rs j16 (y5 y6 y7 y16 y17 y28 y29 y30 y31 : word),
        munch [(SPAz - 2224, SPAz); (FF + 24, FF + 56); (Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] m m' ->
        wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' lo SPAz ->
        rw_cells bsegs m' FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11ba4); C8 (Z_to_bv 64 0xaaac0); CB 8 rs;
                              CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - zlen buf)))); CB 16 j16; C8 (Z_to_bv 64 FLG)] ->
        rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) RFFSH0 ->
        bytes_at bsegs m' BUF (map (Z_to_bv 8) buf) ->
        evtF bsegs RNG Q
          (MS (mkR (Z_to_bv 64 0xaac24) (Z_to_bv 64 SPAz) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                   (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 8) (Z_to_bv 64 0) y16 y17
                   (Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
                   (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 y28 y29 y30 y31)
                   F (Z_to_bv 64 0xaaac0) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xaabec) fc None m (seg_rom bsegs)).
  Proof.
    intros until Q. intros Hhb FBY HBUF FFC SHF MI ST GOT RIC SHB INI LAY REAL APPS UB HULL1 WR1 RSH1 FH FC F64 SEPB BBK RF RSF RB K.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof (ablk_lin _ _ BBK) as (BKa & BKb & BKc & BKd). unfold AIMG_HI in *.
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu. pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof (spa_propsA SP SP16) as (SPAB & SPA32 & _).
    replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    unfold RFFHDR in FFC. unfold RFFSH in SHF.
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB bsegs m FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11ba4); C8 (Z_to_bv 64 0xaaac0)] 32 junk
                  [C8 (Z_to_bv 64 FLG)] [8%nat; 8%nat; 16%nat] FFC eq_refl) as FF2.
    cbn [app mk_CB_cells] in FF2. clear FFC.
    pose proof (munch_refl [(SPAz - 2224, SPAz); (FF + 24, FF + 56); (Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof BBK as BBu. unfold ablk, AIMG_HI, KLS in BBu.
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) buf)) = zlen buf) by (rewrite length_map; reflexivity).
    set (hb := zlen buf) in *. set (hbn := Z.to_nat hb).
    (* [comment removed for export] *)
    assert (HBUFh : fk_held (bytes_at bsegs m BUF (map (Z_to_bv 8) buf))) by exact HBUF. clear HBUF.
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    assert (HBUF1 : bytes_at bsegs m1 BUF (map (Z_to_bv 8) buf)).
    { unfold fk_held in HBUFh. destruct (Z.eq_dec hb 0) as [E0|NZ].
      - eapply bytes_at_len0; [exact HBUFh|]. clear - E0 LBS. lia.
      - eapply bytes_at_transport; [exact HBUFh| exact MU|]. rewrite LBS. cbn [disjoint_from].
        rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - NZ Hhb SEPB BBu BSF LOC LOS SPAB FHu ATR.
        refine (conj _ (conj _ (conj _ I))); Z.div_mod_to_equations; lia. }
    clear HBUFh.
    (* [comment removed for export] *)
    change [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 72612); C8 (Z_to_bv 64 699072); CB 8 (firstn 8 junk);
            C8 (Z_to_bv 64 0); CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]
      with ([C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 72612); C8 (Z_to_bv 64 699072); CB 8 (firstn 8 junk)]
            ++ [C8 (Z_to_bv 64 0)] ++ [CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]) in FF2.
    apply rd_rw_cells_appA in FF2. destruct FF2 as [FA FF2]. apply rd_rw_cells_appA in FF2. destruct FF2 as [FB FCc].
    cbn [cells_size csize Nat.add] in FB, FCc. change (Z.of_nat 32) with 32 in FB, FCc. change (Z.of_nat 8) with 8 in FCc.
    pose proof (rw_cells_merge bsegs _ (FF + 32) [] [C8 (Z_to_bv 64 0)] [] FB) as FM.
    cbn [app cells_size cells_bytes csize cbytes Nat.add] in FM. clear FB.
    change (le8 (Z_to_bv 64 0) ++ []) with (repeat (Z_to_bv 8 0) 8) in FM.
    pose proof (rw_cells_split_CB bsegs _ (FF + 32) [] 8 (repeat (Z_to_bv 8 0) 8) [] [hbn; (8 - hbn)%nat] FM ltac:(cbn [sum_nat]; lia)) as FS.
    cbn [app mk_CB_cells] in FS. clear FM.
    change [CB hbn (firstn hbn (repeat (Z_to_bv 8 0) 8)); CB (8 - hbn) (firstn (8 - hbn) (skipn hbn (repeat (Z_to_bv 8 0) 8)))]
      with ([CB hbn (firstn hbn (repeat (Z_to_bv 8 0) 8))] ++ [CB (8 - hbn) (firstn (8 - hbn) (skipn hbn (repeat (Z_to_bv 8 0) 8)))]) in FS.
    apply rd_rw_cells_appA in FS. destruct FS as [R1 R2]. cbn [cells_size csize Nat.add] in R2.
    replace (FF + 32 + Z.of_nat (hbn + 0)) with (FF + 32 + hb) in R2 by lia.
    (* [comment removed for export] *)
    assert (UD : unpoisoned m1 (FF + 32) (FF + 32 + hb)).
    { change [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
              C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 18446744073709551603);
              C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)]
        with ([C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
               C1 (Z_to_bv 8 18446744073709551601)] ++ [C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 18446744073709551603);
               C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)]) in SHF.
      pose proof SHF as SH2. apply rd_rw_cells_appA in SH2. destruct SH2 as [_ SH2]. apply rd_rw_cells_appA in SH2. destruct SH2 as [SH4 _].
      cbn [cells_size csize Nat.add] in SH4.
      apply c1z_unpoisonedR; [| Z.div_mod_to_equations; lia| lia| lia| lia].
      replace (Z.shiftr (FF + 32) 3 + 2147450880) with (Z.shiftr FF 3 + 2147450880 + Z.of_nat 4); [exact SH4|].
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
    destruct HULL1 as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6).
    assert (WR2 : wr_at bsegs m1 (shad FF) (shad (FF + 64) - shad FF)).
    { destruct SHF as [_ W]. cbn [cells_size csize Nat.add] in W. replace (shad FF) with (Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
      replace (shad (FF + 64) - (Z.shiftr FF 3 + 2147450880)) with (Z.of_nat 8); [exact W|].
      unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
    assert (RSF2 : rng RNG (shad FF) (shad (FF + 64) - shad FF)).
    { replace (shad FF) with (Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
      replace (shad (FF + 64) - (Z.shiftr FF 3 + 2147450880)) with 8; [exact RSF|].
      unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
    assert (UB1 : unpoisoned m1 BUF (BUF + hb)).
    { destruct (Z.eq_dec hb 0) as [E0|NZ].
      - rewrite E0, Z.add_0_r. destruct UB as (U1 & U2 & _). split; [exact U1|]. split; [clear - U2 E0; lia|]. intros G HG. exfalso. clear - HG. lia.
      - eapply unpoisoned_munch; [exact UB| exact MU|]. rewrite !shad_div. cbn [disjoint_from]. unfold ASHOFF.
        rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. refine (conj _ (conj _ (conj _ I))); Z.div_mod_to_equations; lia. }
    clear UB.
    eapply evtF_cut; [eapply amemcpy_specZ with (A := FF + 32) (S := BUF) (n := hb) (SPz := SPAz) (RLO1 := RLO1) (RHI1 := RHI1)
                                               (RLO2 := FF) (RHI2 := FF + 64) | post_call bsegs m1 ];
      try (lazymatch goal with |- rng _ _ _ => solve_rng end).
    all: first [ lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => eassumption
         | |- bytes_at _ _ _ _ => eassumption
         | |- rw_cells _ _ _ _ => first [exact R1 | assumption]
         | |- app_blk _ _ => first [exact APPS | apply ablk_app_blk; [eapply ablk_sub; [exact FH| lia| lia]| lia]]
         | |- unpoisoned _ _ _ => first [exact UD | exact UB1]
         | |- wr_at _ _ _ _ => eassumption
         | |- rng _ _ _ => first [exact RSF2 | eassumption | eapply rng_sub'; [exact RF| lia] | eapply rng_sub'; [exact RSTK| lia]]
         | |- length _ = _ => rewrite length_map; lia
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
         | |- _ => unfold KHIGH, KEND in *; lia
         end | lazymatch goal with |- ?G => idtac "FAILED:" G end ].
    (* [comment removed for export] *)
    rewrite (pad_tailA 0 (Z_to_bv 8 0) hbn) in R2 by lia.
    lazymatch goal with P : rw_cells bsegs ?mx (FF + 32) [CB (Z.to_nat hb) (map (Z_to_bv 8) buf)] |- _ => rename P into RB1; rename mx into m2 end.
    assert (RB8 : rw_cells bsegs m2 (FF + 32) [CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - hb))))]).
    { replace (FF + 32 + hb) with (FF + 32 + Z.of_nat (cells_size [CB hbn (map (Z_to_bv 8) buf)])) in R2
        by (cbn [cells_size csize Nat.add]; lia).
      pose proof (proj2 (rd_rw_cells_appA bsegs m2 (FF + 32) [CB hbn (map (Z_to_bv 8) buf)]
                          [CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))]) (conj RB1 R2)) as RJ.
      pose proof (rw_cells_merge bsegs m2 (FF + 32) [] [CB hbn (map (Z_to_bv 8) buf); CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))] [] RJ) as RMg.
      cbn [app cells_size cells_bytes csize cbytes Nat.add] in RMg. rewrite app_nil_r in RMg.
      replace (hbn + (8 - hbn + 0))%nat with 8%nat in RMg by lia.
      rewrite map_app, map_repeat. replace (Z.to_nat (8 - hb)) with (8 - hbn)%nat by lia. exact RMg. }
    clear RB1 R2.
    assert (FRM : rw_cells bsegs m2 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11ba4); C8 (Z_to_bv 64 0xaaac0); CB 8 (firstn 8 junk);
                              CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - hb)))); CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]).
    { change [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11ba4); C8 (Z_to_bv 64 0xaaac0); CB 8 (firstn 8 junk);
              CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - hb)))); CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]
        with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11ba4); C8 (Z_to_bv 64 0xaaac0); CB 8 (firstn 8 junk)]
              ++ [CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - hb))))] ++ [CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]).
      apply rd_rw_cells_appA. split; [eassumption|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32.
      apply rd_rw_cells_appA. split; [exact RB8|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8. eassumption. }
    do 6 zstep.                                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    eapply K; eassumption.
  Qed.
End S1z.

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : AFakeK_iface.fake_flag_law AI fflag.   (* [comment removed for export] *)
Hypothesis FREL : AFakeK_iface.fake_release_law AI fflag.
Hypothesis SM0K : forall k, Z.of_nat k < 16384 -> stack_malloc_0k_stmt AI fflag rng_fs k.
Hypothesis FHL : fake_heap_law AI.
Notation FB0 F := (mkABlock (ABFake 0) F 64).

(* [comment removed for export] *)
Definition rdZ_post (SW : Z) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV NC MSVP TLP : Z) (rt0 buf : list Z) (msv0 lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r rt' (msvw tlw : word),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ([(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4); (SPV - SW, SPV)] ++ fake_area L) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ ffr_pres [(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4)] LB m m' /\ AHEAP AI L RNG st LB m'
    /\ u8arr bsegs m' NC (u16s (map (Z_to_bv 64) rt')) /\ length rt' = length rt0
    /\ rw_cells bsegs m' MSVP [C4 msvw] /\ rw_cells bsegs m' TLP [C4 tlw]
    /\ 0 <= r < 2^64
    /\ ((exists rt msv tl n, read_ncount rt0 msv0 buf = Ok (rt, msv, tl, n)
           /\ r = n /\ rt' = rt /\ msvw = Z_to_bv 64 msv /\ tlw = Z_to_bv 64 tl)
        \/ (exists e, read_ncount rt0 msv0 buf = Err e /\ r = 2^64 - e)).

Lemma rdZ_post_iface : forall SW L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 buf msv0 lo m ms,
  rdZ_post SW L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 buf msv0 lo m ms -> SW <= 4672 ->
  fse_read_any_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 buf msv0 lo m ms.
Proof.
  intros until ms. intros H HSW. unfold rdZ_post in H. unfold fse_read_any_postA.
  destruct H as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & r & rt' & msvw & tlw & E & MU & REST).
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', r, rt', msvw, tlw. split; [exact E|]. split; [| exact REST].
  eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside app fake_area] in *. clear - Hx HSW. lia.
Qed.

(* [comment removed for export] *)
Lemma rd_openZ : forall (k : nat) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem)
    (SPV NC MSVP TLP BUF hb lo : Z) (ncb bufb : list byte) (msvw tlw : word) (Q : machine_state -> Prop),
  Z.of_nat k < 16384 ->
  AHEAP AI L RNG st LB m -> fake_le 0 k LB -> ablkLB LB ->
  rng_aimg RNG -> rng RNG lo (al_top L - lo) -> rng_fs L RNG ->
  ATOP + 4096 <= lo -> lo <= SPV - 4304 -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  stk bsegs m lo SPV -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  ablk BUF (BUF + hb) -> 0 <= hb ->
  (* [comment removed for export] *)
  u8arr bsegs m NC ncb -> ainblk LB NC (Z.of_nat (length ncb)) -> unpoisoned m NC (NC + Z.of_nat (length ncb)) ->
  (NC + Z.of_nat (length ncb) <= lo \/ SPV <= NC) -> NC + Z.of_nat (length ncb) <= 2^47 ->
  rw_cells bsegs m MSVP [C4 msvw] -> ainblk LB MSVP 4 -> unpoisoned m MSVP (MSVP + 4) -> MSVP mod 4 = 0 -> rng RNG (shad MSVP) 1 ->
  (MSVP + 4 <= lo \/ SPV <= MSVP) -> MSVP + 4 <= 2^47 ->
  rw_cells bsegs m TLP [C4 tlw] -> ainblk LB TLP 4 -> unpoisoned m TLP (TLP + 4) -> (TLP + 4 <= lo \/ SPV <= TLP) -> TLP + 4 <= 2^47 ->
  bytes_at bsegs m BUF bufb -> (0 < Z.of_nat (length bufb) -> ainimg LB BUF (Z.of_nat (length bufb))) ->
  unpoisoned m BUF (BUF + Z.of_nat (length bufb)) -> 0 <= BUF -> (BUF + Z.of_nat (length bufb) <= lo \/ SPV <= BUF) ->
  BUF + Z.of_nat (length bufb) <= 2^47 ->
  (forall (FF : Z) (m3 : amem) (j48 junk : list byte) (x5 x6 x7 y10 y11 y13 y14 x15 x16 x17 x28 x29 x30 x31 : word),
     FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
     (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
     al_fake L <= FF -> FF + 64 <= al_fake L + FAKESZ ->
     AHEAP AI L RNG st (FB0 FF :: LB) m3 ->
     munch ([(SPV - 4304, SPV)] ++ fake_area L) m m3 -> wmono bsegs m m3 -> ffr_pres [] LB m m3 -> mem_inv bsegs m3 ->
     rw_cells bsegs m3 (SPV + -104) (RFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     rw_cells bsegs m3 (SPAz SPV) [CB 48 j48; C8 (Z_to_bv 64 FF)] ->
     rw_cells bsegs m3 FF (RFFHDR FF (fflag L 0 FF) junk) -> rw_cells bsegs m3 (Z.shiftr FF 3 + 2147450880) RFFSH ->
     stk bsegs m3 lo (SPAz SPV) -> stk bsegs m3 (SPAz SPV + 56) (SPV + -104) ->
     u8arr bsegs m3 NC ncb -> unpoisoned m3 NC (NC + Z.of_nat (length ncb)) ->
     rw_cells bsegs m3 MSVP [C4 msvw] -> unpoisoned m3 MSVP (MSVP + 4) ->
     rw_cells bsegs m3 TLP [C4 tlw] -> unpoisoned m3 TLP (TLP + 4) ->
     bytes_at bsegs m3 BUF bufb -> unpoisoned m3 BUF (BUF + Z.of_nat (length bufb)) ->
     Q (MS (mkR (Z_to_bv 64 0xaab40) (Z_to_bv 64 (SPAz SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAz SPV))
                y10 y11 (Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) y13 y14 x15 x16 x17
                (Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 hb)
                (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) s11 x28 x29 x30 x31)
           FR (Z_to_bv 64 (if 7 <? hb then 0xaac48 else 0xaabec)) fc None m3 (seg_rom bsegs))) ->
  evtF bsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
             (Z_to_bv 64 hb) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 AFSE_RD_BODY) fc None m (seg_rom bsegs)).
Proof.
  intros k L RNG st LB ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV NC MSVP TLP BUF hb lo
         ncb bufb msvw tlw Q HK AH FLE LBH RI RSTK RFS BOT LO SPT SP16 ST MI TP BBK Hhb
         ARR INN UN SNS NHI HMSV INM UM M4 RMS SMS MHI HTL INT UT STS THI HBUF INB UB B0 SBS BHI K.
  pose proof atop_range as ATR.
  assert (NC0 : 0 <= NC) by (destruct UN as (U & _); exact U). assert (MSVP0 : 0 <= MSVP) by (destruct UM as (U & _); exact U).
  assert (TLP0 : 0 <= TLP) by (destruct UT as (U & _); exact U).   (* [comment removed for export] *)
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (spa_props2 SPV SP16) as (SPAB & SPA32).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  assert (LOS : lo <= SPV - 176 - 4096) by lia.
  assert (LOC : ATOP <= lo) by lia.
  assert (SPK : SPV + 16 < KEND) by (unfold KEND; lia).
  (* [comment removed for export] *)
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
  destruct RTC as (C0 & GOT & RIC & REAL & SHB & SUA & INI & LAY & _).
  destruct (rd_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [GSU _].
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (rd_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
      first [exact ST| exact MI| exact GOT| exact SHB| exact GSU| exact SUA| exact SP16| eapply rng_sub'; [exact RSTK| lia]
            | exact RI| exact LOS | exact LOC | exact SPK]. }
  cbv beta. intros ms' (m1 & jA & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
  clear C0 GOT RIC REAL SHB SUA INI LAY GSU.
  assert (AH1 : AHEAP AI L RNG st LB m1).
  { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
  (* [comment removed for export] *)
  assert (D1 : forall X n, (X + n <= lo \/ SPV <= X) -> 0 <= n -> disjoint_from [(SPV - 176, SPV)] X n).
  { intros X n HX Hn. cbn [disjoint_from]. split; [lia| exact I]. }
  assert (DS1 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 ->
             disjoint_from [(SPV - 176, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
  { intros X n X0 Hn Hb. cbn [disjoint_from]. split; [| exact I]. left. rewrite !shad_div. unfold ASHOFF in *.
    clear - X0 Hn Hb ATR BOT LO. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  eapply evtF_cut.
  { pose proof (SM0K k HK) as SMC. unfold stack_malloc_0k_stmt in SMC. eapply SMC with (lo := lo); clear SMC;
      rewrite ?(unsigned_lit (SPAz SPV)) by lia;
      first [exact AH1| exact FLE| exact MI1| exact STL1| exact TP| reflexivity| exact RSTK| exact RI| exact RFS| lia| unfold SMK_STACK; lia]. }
  cbv beta. intros ms' PO.
  destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                  & -> & MI2 & ST2 & HPR2 & AH2 & F64 & FH & FC & FFC2 & SHF2 & RFF & RSFF & MUF2 & WM2 & FFA1 & FFA2).
  rewrite ?(unsigned_lit (SPAz SPV)) in ST2, HPR2, MUF2 by lia.
  rd_retlit.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH2) as FFD.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRB1 ltac:(left; left; cbn; lia)) as FRB2.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; lia)) as FRA2.
  pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
  (* [comment removed for export] *)
  destruct (fk_inblk_ablk LB MSVP 4 LBH INM ltac:(lia)) as (AM & BM & ABM0 & AM1 & AM2).
  assert (ABM : ablk MSVP (MSVP + 4)) by (eapply ablk_sub; [exact ABM0| lia| lia]).
  pose proof (ablk_lin _ _ ABM) as (ABMa & ABMb & ABMc & ABMd). unfold AIMG_HI in ABMa.
  assert (UM1 : unpoisoned m1 MSVP (MSVP + 4)) by (eapply unpoisoned_munch; [exact UM| exact MU1| apply DS1; lia]).
  assert (UM2 : unpoisoned m2 MSVP (MSVP + 4))
    by (eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact INM| lia| exact UM1]).
  pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ MSVP 4 AH2 INM ltac:(lia)) as DFM.
  destruct (rd_got_cells m2 (AI_relro AI _ _ _ _ _ AH2)) as [_ GPC2].
  assert (Hhb64 : 0 <= hb < 2^64) by (pose proof (ablk_lin _ _ BBK) as (_ & BB0 & BB1 & BB2); lia).
  eapply (rd_hdr gp tp s2 s9 s10 FR fc SPV lo); first [exact FRA2| exact FFC2| exact SHF2| exact GPC2| exact MI2| exact UM2| exact M4| exact FH| exact FC| exact F64
                       | exact RFF| exact RSFF| exact RMS| exact SP16| exact RI| eapply rng_sub'; [exact RSTK| lia]
                       | exact ABM | exact LOS | exact LOC | exact SPK | exact Hhb64 | lia | idtac].
  intros m3 j48 y10 y11 y13 y14 MU3 WM3 MI3 FRA3 FFC3 SHF3.
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (AH3 : AHEAP AI L RNG st (FB0 FF :: LB) m3).
  { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
    constructor; [cbn; left; left; lia|].
    constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|].
    constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                  change (2 ^ 3) with 8; unfold ASHOFF; Z.div_mod_to_equations; lia]| constructor]. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRB2 MU3 WM3 ltac:(cbn; lia)) as FRB3.
  assert (STL3 : stk bsegs m3 lo (SPAz SPV))
    by (eapply stk_transport; [exact ST2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  assert (STG3 : stk bsegs m3 (SPAz SPV + 56) (SPV + -104))
    by (eapply stk_transport; [exact STG2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  (* [comment removed for export] *)
  assert (MU03 : munch ([(SPV - 4304, SPV)] ++ fake_area L) m m3).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x Hx; cbn [outside app fake_area] in *; lia|].
    eapply munch_trans; [eapply munch_weaken; [| exact MUF2]; intros x Hx; cbn [outside app fake_area] in *; unfold SMK_STACK; lia|].
    eapply munch_weaken; [| exact MU3]. intros x Hx. cbn [outside app fake_area] in *.
    rewrite ?shad_div in *. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold FAKESZ, ASHOFF in *.
    clear - Hx FFA1 FFA2 SPAB LO BOT F64. Z.div_mod_to_equations. lia. }
  assert (WM03 : wmono bsegs m m3) by (eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]).
  assert (FFR02 : ffr_pres [] LB m m2).
  { eapply ffr_pres_trans; [eapply (fk_ffr_stack AI); [exact AH| exact MU1| exact WM1| constructor; [cbn; lia| constructor]]|].
    eapply (fk_ffr_of_pres AI); exact HPR2. }
  assert (FFR03 : ffr_pres [] LB m m3).
  { eapply (fk_ffr_fin AI L RNG st LB m m2 m3 0 FF 64 (shad FF) 8 [] [(SPAz SPV, SPAz SPV + 56); (FF, FF + 24)]);
      [exact AH2| exact LBH| exact FH| clear - F64; Z.div_mod_to_equations; lia| reflexivity| lia| lia| | constructor| exact FFR02| | exact WM3].
    - constructor; [cbn; split; [lia| left; lia]|].
      constructor; [cbn; split; [lia| right; split; [intros b Hb; destruct (FFD b Hb); lia| exists FF, (FF+64); split; [exact FH| lia]]]| constructor].
    - eapply munch_weaken; [| exact MU3]. intros x Hx. cbn [outside app] in *. rewrite ?shad_div in *.
      rewrite ?Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. unfold ASHOFF in *. clear - Hx. lia. }
  (* [comment removed for export] *)
  destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (ablk_disj_band _ _ FAB) as FABD. pose proof (ablk_lin _ _ FAB) as (FABa & _).
  unfold AIMG_HI in FABa. unfold FAKESZ in *.
  set (W3 := [(SPAz SPV, SPAz SPV + 56); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)]) in MU3.
  (* [comment removed for export] *)
  assert (TB : forall X n, ainblk LB X n -> 0 <= n -> (X + n <= lo \/ SPV <= X) -> X + n <= 2^47 ->
            disjoint_from W3 X n /\ (0 < n -> disjoint_from W3 (shad X) (shad (X + n - 1) + 1 - shad X))).
  { intros X n IB Hn HS HH.
    destruct (fk_inblk_ablk LB X n LBH IB Hn) as (AX & BX & ABX0 & AX1 & AX2).
    pose proof (ablk_lin _ _ ABX0) as (LX1 & LX2 & LX3 & LX4). pose proof (ablk_disj_band _ _ ABX0) as DBX. unfold AIMG_HI, KLS in LX1, DBX.
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ X n AH2 IB Hn) as DFX.
    pose proof (ablk_disj_band _ _ FH) as DBF. unfold KLS in DBF.
    subst W3. cbn [disjoint_from]. rewrite !shad_div. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ASHOFF.
    clear - Hn HS HH DFX DBX DBF LX1 AX1 AX2 SPAB LO BOT FHa FHb FHc FHd F64 ATR.
    split; [| intros Hp]; (split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]). }
  (* [comment removed for export] *)
  assert (TI : forall X n, 0 <= X -> X + n <= AIMG_HI -> 0 < n ->
            disjoint_from (fake_area L ++ [(SPAz SPV - SMK_STACK, SPAz SPV)]) X n
            /\ disjoint_from (fake_area L ++ [(SPAz SPV - SMK_STACK, SPAz SPV)]) (shad X) (shad (X + n - 1) + 1 - shad X)
            /\ disjoint_from W3 X n /\ disjoint_from W3 (shad X) (shad (X + n - 1) + 1 - shad X)).
  { intros X n X0 XH Hp. unfold AIMG_HI in XH. pose proof (ablk_disj_band _ _ FH) as DBF. unfold KLS in DBF, FABD.
    subst W3. cbn [disjoint_from fake_area app]. rewrite !shad_div. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    unfold ASHOFF, SMK_STACK, FAKESZ. clear - X0 XH Hp FABa FABD SPAB LO BOT FHa FHb FHc FHd F64 DBF ATR.
    repeat split; Z.div_mod_to_equations; lia. }
  destruct (TB NC (Z.of_nat (length ncb)) INN ltac:(lia) SNS NHI) as [DN DSN].
  destruct (TB MSVP 4 INM ltac:(lia) SMS MHI) as [DM DSM].
  destruct (TB TLP 4 INT ltac:(lia) STS THI) as [DT DST].
  assert (ARR3 : u8arr bsegs m3 NC ncb).
  { eapply u8arr_transport; [| exact MU3| exact WM3| exact DN].
    assert (ARR1 : u8arr bsegs m1 NC ncb) by (eapply u8arr_transport; [exact ARR| exact MU1| exact WM1| apply D1; rewrite ?zsize_c4; lia]).
    destruct ARR1 as [BA WA]. split; [eapply (fk_bytes_pres AI); [exact HPR2| exact INN| exact BA] | eapply wr_at_transport; [exact WA| exact WM2]]. }
  assert (HMSV3 : rw_cells bsegs m3 MSVP [C4 msvw]).
  { eapply rw_cells_transport; [| exact MU3| exact WM3| exact DM].
    eapply (fk_cells_pres AI); [exact HPR2| exact INM|].
    eapply rw_cells_transport; [exact HMSV| exact MU1| exact WM1| apply D1; rewrite ?zsize_c4; lia]. }
  assert (HTL3 : rw_cells bsegs m3 TLP [C4 tlw]).
  { eapply rw_cells_transport; [| exact MU3| exact WM3| exact DT].
    eapply (fk_cells_pres AI); [exact HPR2| exact INT|].
    eapply rw_cells_transport; [exact HTL| exact MU1| exact WM1| apply D1; rewrite ?zsize_c4; lia]. }
  assert (UN3 : unpoisoned m3 NC (NC + Z.of_nat (length ncb))).
  { destruct (Z.eq_dec (Z.of_nat (length ncb)) 0) as [E0|NZ].
    { rewrite E0 in *. destruct UN as (U1 & U2 & _). split; [lia|]. split; [lia|]. intros G HG. lia. }
    eapply unpoisoned_munch; [| exact MU3| apply DSN; lia].
    eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact INN| lia|].
    eapply unpoisoned_munch; [exact UN| exact MU1| apply DS1; lia]. }
  assert (UM3 : unpoisoned m3 MSVP (MSVP + 4)).
  { eapply unpoisoned_munch; [| exact MU3| apply DSM; lia].
    eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact INM| lia|].
    eapply unpoisoned_munch; [exact UM| exact MU1| apply DS1; lia]. }
  assert (UT3 : unpoisoned m3 TLP (TLP + 4)).
  { eapply unpoisoned_munch; [| exact MU3| apply DST; lia].
    eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact INT| lia|].
    eapply unpoisoned_munch; [exact UT| exact MU1| apply DS1; lia]. }
  (* [comment removed for export] *)
  assert (HB3 : bytes_at bsegs m3 BUF bufb /\ unpoisoned m3 BUF (BUF + Z.of_nat (length bufb))).
  { destruct (Z.eq_dec (Z.of_nat (length bufb)) 0) as [E0|NZ].
    { destruct bufb; [| cbn [length] in E0; lia]. split; [exact (bytes_at_nil _ _ _ HBUF)|].
      cbn [length]. destruct UB as (U1 & U2 & _). split; [lia|]. split; [lia|]. intros G HG. lia. }
    destruct (INB ltac:(lia)) as [IBB | [IB1 IB2]].
    - destruct (TB BUF (Z.of_nat (length bufb)) IBB ltac:(lia) SBS BHI) as [DB DSB]. split.
      + eapply bytes_at_transport; [| exact MU3| exact DB]. eapply (fk_bytes_pres AI); [exact HPR2| exact IBB|].
        eapply bytes_at_transport; [exact HBUF| exact MU1| apply D1; rewrite ?zsize_c4; lia].
      + eapply unpoisoned_munch; [| exact MU3| apply DSB; lia].
        eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact IBB| lia|].
        eapply unpoisoned_munch; [exact UB| exact MU1| apply DS1; lia].
    - destruct (TI BUF (Z.of_nat (length bufb)) B0 IB2 ltac:(lia)) as (DB2 & DSB2 & DB3 & DSB3). split.
      + eapply bytes_at_transport; [| exact MU3| exact DB3]. eapply bytes_at_transport; [| exact MUF2| exact DB2].
        eapply bytes_at_transport; [exact HBUF| exact MU1| apply D1; rewrite ?zsize_c4; lia].
      + eapply unpoisoned_munch; [| exact MU3| exact DSB3]. eapply unpoisoned_munch; [| exact MUF2| exact DSB2].
        eapply unpoisoned_munch; [exact UB| exact MU1| apply DS1; lia]. }
  destruct HB3 as [HBUF3 UB3].
  subst W3.
  eapply (K FF m3 j48 junk z5 z6 z7 y10 y11 y13 y14 e15 e16 e17 z28 z29 z30 z31);
    first [exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact FFA1| exact FFA2| exact AH3| exact MU03| exact WM03| exact FFR03
          | exact MI3| exact FRB3| exact FRA3| exact FFC3| exact SHF3| exact STL3| exact STG3
          | exact ARR3| exact UN3| exact HMSV3| exact UM3| exact HTL3| exact UT3| exact HBUF3| exact UB3].
Qed.
(* [comment removed for export] *)
Lemma ffr_pres_mono_nil : forall W LB (m m' : amem), ffr_pres [] LB m m' -> ffr_pres W LB m m'.
Proof.
  intros W LB m m' H a Ha HP. apply (H a Ha). destruct HP as [[HF _]|HS]; [left; split; [exact HF| exact I]| right; exact HS].
Qed.

(* [comment removed for export] *)
Lemma rd_closeZ : forall (SW : Z) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m m4 : amem) (SPV NC MSVP TLP lo FF r msv0 : Z) (rt0 buf rt' : list Z) (msvw tlw j0 : word) (csA : list cell)
    (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word),
  AHEAP AI L RNG st (FB0 FF :: LB) m4 -> ablkLB LB ->
  FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  al_fake L <= FF -> FF + 64 <= al_fake L + FAKESZ ->
  munch ([(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4); (SPV - SW, SPV)] ++ fake_area L) m m4 ->
  wmono bsegs m m4 -> mem_inv bsegs m4 ->
  ffr_pres [(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4)] LB m m4 ->
  rw_cells bsegs m4 (Z.shiftr FF 3 + 2147450880) RFFSH ->
  rw_cells bsegs m4 FF [C8 j0] -> rw_cells bsegs m4 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))] ->
  rw_cells bsegs m4 (SPV + -104) (RFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells bsegs m4 (SPAz SPV) csA -> cells_size csA = 56%nat ->
  stk bsegs m4 lo (SPAz SPV) -> stk bsegs m4 (SPAz SPV + 56) (SPV + -104) ->
  ATOP + 4096 <= lo -> lo <= SPV - 4304 -> SPV + 16 < al_top L -> SPV mod 16 = 0 -> rng RNG lo (al_top L - lo) ->
  ainblk LB NC (2 * zlen rt0) -> ainblk LB MSVP 4 -> ainblk LB TLP 4 ->
  NC + 2 * zlen rt0 <= 2^47 -> MSVP + 4 <= 2^47 -> TLP + 4 <= 2^47 ->
  u8arr bsegs m4 NC (u16s (map (Z_to_bv 64) rt')) -> length rt' = length rt0 ->
  rw_cells bsegs m4 MSVP [C4 msvw] -> rw_cells bsegs m4 TLP [C4 tlw] ->
  0 <= r < 2^64 ->
  ((exists rt msv tl n, read_ncount rt0 msv0 buf = Ok (rt, msv, tl, n) /\ r = n /\ rt' = rt /\ msvw = Z_to_bv 64 msv /\ tlw = Z_to_bv 64 tl)
   \/ (exists e, read_ncount rt0 msv0 buf = Err e /\ r = 2^64 - e)) ->
  evtF bsegs RNG (rdZ_post SW L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV NC MSVP TLP rt0 buf msv0 lo m)
    (MS (mkR x1 (Z_to_bv 64 (SPAz SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAz SPV)) x10 (Z_to_bv 64 r) x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 0xab14c) fc None m4 (seg_rom bsegs)).
Proof.
  intros SW L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m4 SPV NC MSVP TLP lo FF r msv0 rt0 buf rt' msvw tlw j0 csA
         x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31
         AH4 LBH F64 FH FC RFF RSFF FFD FFA1 FFA2 MU04 WM04 MI4 FFR04 SHF4 FF04 FF564 FRB4 FRA4 CSA STL4 STG4 BOT LO SPT SP16 RSTK
         INN INM INT NHI MHI THI ARR4 LRT HMSV4 HTL4 Hr RES.
  pose proof atop_range as ATR.
  pose proof (spa_props2 SPV SP16) as (SPAB & SPA32).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  destruct (FFLAG _ _ _ _ _ _ _ _ AH4 ltac:(left; reflexivity)) as (FLC & RG & GH & GC & GBL & GCI & GFA).
  pose proof (GBL _ ltac:(left; reflexivity)) as GF. cbn [ab_addr ab_size] in GF.
  pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa.
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  eapply evtF_cut.
  { eapply (rd_epi ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
      first [exact SHF4| exact FF04| exact FF564| exact FLC| exact FRB4| exact FRA4| exact CSA| exact STL4| exact STG4| exact MI4
            | exact FH| exact FC| exact F64| exact GH| exact GC| exact GF| exact RFF| exact RSFF| exact RG| exact SP16
            | eapply rng_sub'; [exact RSTK| lia]| lia]. }
  cbv beta. intros ms' (mp & m5 & -> & MU1 & WM1 & MIp & MU2 & WM2 & MI5 & ST5 & FLC5).
  assert (AHp : AHEAP AI L RNG st (FB0 FF :: LB) mp).
  { eapply (AI_frame AI); [exact AH4| exact MU1| exact WM1|].
    constructor; [| constructor; [| constructor]]; cbn.
    - right; right. right; right. exists 0, FF, 64. split; [left; reflexivity|].
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold ASHOFF. Z.div_mod_to_equations. lia.
    - right; left. exists (FB0 FF). split; [left; reflexivity| cbn; lia]. }
  assert (AH5 : AHEAP AI L RNG st LB m5).
  { eapply (fk_release AI fflag); [exact FREL| exact AHp| lia| lia| lia| exact MU2| exact FLC5]. }
  (* [comment removed for export] *)
  assert (TC : forall X n, ainblk LB X n -> 0 <= n -> X + n <= 2^47 ->
            disjoint_from [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] X n
            /\ disjoint_from [(fflag L 0 FF, fflag L 0 FF + 1)] X n).
  { intros X n (b & Hb & Hb1 & Hb2) Hn HH.
    pose proof (FFD b Hb) as D1. pose proof (GBL b ltac:(right; exact Hb)) as D2. pose proof (ablk_disj_band _ _ (LBH b Hb)) as D3.
    unfold KLS in D3. cbn [disjoint_from]. clear - Hb1 Hb2 Hn HH D1 D2 D3 BSF. repeat split; lia. }
  destruct (TC NC (2 * zlen rt0) INN ltac:(lia) NHI) as [DN1 DN2].
  destruct (TC MSVP 4 INM ltac:(lia) MHI) as [DM1 DM2].
  destruct (TC TLP 4 INT ltac:(lia) THI) as [DT1 DT2].
  assert (LNC : Z.of_nat (length (u16s (map (Z_to_bv 64) rt'))) = 2 * zlen rt0) by (rewrite u16s_length, length_map, LRT; lia).
  apply evtF_done. unfold rdZ_post. do 14 eexists. exists m5, r, rt', msvw, tlw.
  split; [reflexivity|].
  split.
  { eapply munch_trans; [exact MU04|]. eapply munch_trans.
    - eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside app fake_area] in *.
      rewrite ?shad_div in *. rewrite ?Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. unfold FAKESZ, ASHOFF in *.
      clear - Hx FFA1 FFA2 F64. Z.div_mod_to_equations. lia.
    - eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside app fake_area] in *. unfold FAKESZ in *. clear - Hx GFA. lia. }
  split; [eapply wmono_trans; [exact WM04| eapply wmono_trans; [exact WM1| exact WM2]]|].
  split; [exact MI5|]. split; [exact ST5|].
  split.
  { eapply ffr_pres_trans; [exact FFR04|]. apply ffr_pres_mono_nil.
    eapply (fk_ffr_fin AI L RNG st LB m4 m4 m5 0 FF 64 (shad FF) 8 [] [(FF, FF + 8); (fflag L 0 FF, fflag L 0 FF + 1)]);
      [exact AH4| exact LBH| exact FH| clear - F64; Z.div_mod_to_equations; lia| reflexivity| lia| lia| | constructor| apply ffr_pres_refl| |
       eapply wmono_trans; [exact WM1| exact WM2]].
    - constructor; [cbn; split; [lia| right; split; [intros b Hb; destruct (FFD b Hb); lia| exists FF, (FF + 64); split; [exact FH| lia]]]|].
      constructor; [cbn; split; [lia| right; split; [intros b Hb; exact (GBL b ltac:(right; exact Hb))| exists (fflag L 0 FF), (fflag L 0 FF + 1); split; [exact GH| lia]]]| constructor].
    - eapply munch_trans.
      + eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside app] in *. rewrite ?shad_div in *.
        rewrite ?Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. unfold ASHOFF in *. clear - Hx. lia.
      + eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside app] in *. clear - Hx. lia. }
  split; [exact AH5|].
  split.
  { eapply u8arr_transport; [eapply u8arr_transport; [exact ARR4| exact MU1| exact WM1| rewrite LNC; exact DN1]| exact MU2| exact WM2| rewrite LNC; exact DN2]. }
  split; [exact LRT|].
  split.
  { eapply rw_cells_transport; [eapply rw_cells_transport; [exact HMSV4| exact MU1| exact WM1| exact DM1]| exact MU2| exact WM2| exact DM2]. }
  split.
  { eapply rw_cells_transport; [eapply rw_cells_transport; [exact HTL4| exact MU1| exact WM1| exact DT1]| exact MU2| exact WM2| exact DT2]. }
  split; [exact Hr| exact RES].
Qed.
(* [comment removed for export] *)
Lemma rd_body8Z : forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m m3 : amem) (SPV NC MSVP TLP BUF lo FF msv0 : Z) (rt0 buf : list Z) (tl0 : word) (j48 junk : list byte)
    (x1 x5 x6 x7 y10 y11 y13 y14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
  8 <= zlen buf -> Forall (fun c => 0 <= c < 256) buf -> 0 <= msv0 <= 255 -> msv0 + 1 <= zlen rt0 -> zlen rt0 <= 65536 -> zlen buf <= 1048576 ->
  NC mod 2 = 0 -> MSVP mod 4 = 0 -> TLP mod 4 = 0 ->
  (NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC) -> (NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC) ->
  (NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC) -> (MSVP + 4 <= TLP \/ TLP + 4 <= MSVP) ->
  (MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP) -> (TLP + 4 <= BUF \/ BUF + zlen buf <= TLP) ->
  (NC + 2 * zlen rt0 <= lo \/ SPV <= NC) -> (MSVP + 4 <= lo \/ SPV <= MSVP) -> (TLP + 4 <= lo \/ SPV <= TLP) -> (BUF + zlen buf <= lo \/ SPV <= BUF) ->
  ablk NC (NC + 2 * zlen rt0) -> ablk MSVP (MSVP + 4) -> ablk TLP (TLP + 4) -> ablk BUF (BUF + zlen buf) ->
  ainblk LB NC (2 * zlen rt0) -> ainblk LB MSVP 4 -> ainblk LB TLP 4 ->
  NC + 2 * zlen rt0 <= 2^47 -> MSVP + 4 <= 2^47 -> TLP + 4 <= 2^47 ->
  rng_aimg RNG -> rng RNG lo (al_top L - lo) ->
  rng RNG NC (2 * zlen rt0) -> rng RNG (shad NC) (shspan NC (2 * zlen rt0)) -> rng RNG MSVP 4 -> rng RNG (shad MSVP) 1 ->
  rng RNG TLP 4 -> rng RNG (shad TLP) 1 -> rng RNG BUF (zlen buf) -> rng RNG (shad BUF) (shspan BUF (zlen buf)) ->
  ahull RNG m NC (2 * zlen rt0) ->
  FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  al_fake L <= FF -> FF + 64 <= al_fake L + FAKESZ ->
  ATOP + 4096 <= lo -> lo <= SPV - 4304 -> SPV + 16 < al_top L -> SPV mod 16 = 0 -> ablkLB LB ->
  AHEAP AI L RNG st (FB0 FF :: LB) m3 ->
  munch ([(SPV - 4304, SPV)] ++ fake_area L) m m3 -> wmono bsegs m m3 -> ffr_pres [] LB m m3 -> mem_inv bsegs m3 ->
  rw_cells bsegs m3 (SPV + -104) (RFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells bsegs m3 (SPAz SPV) [CB 48 j48; C8 (Z_to_bv 64 FF)] ->
  rw_cells bsegs m3 FF (RFFHDR FF (fflag L 0 FF) junk) -> rw_cells bsegs m3 (Z.shiftr FF 3 + 2147450880) RFFSH ->
  stk bsegs m3 lo (SPAz SPV) -> stk bsegs m3 (SPAz SPV + 56) (SPV + -104) ->
  u8arr bsegs m3 NC (u16s (map (Z_to_bv 64) rt0)) -> unpoisoned m3 NC (NC + 2 * zlen rt0) ->
  rw_cells bsegs m3 MSVP [C4 (Z_to_bv 64 msv0)] -> unpoisoned m3 MSVP (MSVP + 4) ->
  rw_cells bsegs m3 TLP [C4 tl0] -> unpoisoned m3 TLP (TLP + 4) ->
  bytes_at bsegs m3 BUF (map (Z_to_bv 8) buf) -> unpoisoned m3 BUF (BUF + zlen buf) ->
  evtF bsegs RNG (rdZ_post 4304 L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV NC MSVP TLP rt0 buf msv0 lo m)
    (MS (mkR x1 (Z_to_bv 64 (SPAz SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAz SPV))
             y10 y11 (Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) y13 y14 x15 x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
             (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 0xaac48) fc None m3 (seg_rom bsegs)).
Proof.
  intros L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m3 SPV NC MSVP TLP BUF lo FF msv0 rt0 buf tl0 j48 junk
         x1 x5 x6 x7 y10 y11 y13 y14 x15 x16 x17 x27 x28 x29 x30 x31
         HB8 FB HM0 HM1 HRT HBL N2 M4 T4 S1 S2 S3 S4 S5 S6 SNS SMS STS SBS BN BM BT BB INN INM INT NHI MHI THI
         RI RSTK RN RNS RM RMS RT RTS RB RBS HULL F64 FH FC RFF RSFF FFD FFA1 FFA2 BOT LO SPT SP16 LBH
         AH3 MU03 WM03 FFR03 MI3 FRB3 FRA3 FFC3 SHF3 STL3 STG3 ARR3 UN3 HMSV3 UM3 HTL3 UT3 HBUF3 UB3.
  pose proof atop_range as ATR.
  pose proof (spa_props2 SPV SP16) as (SPAB & SPA32).
  assert (SPK : SPV + 16 < KEND) by (pose proof (AI_layout AI _ _ _ _ _ AH3) as (LY1 & LY2 & LY3 & LY4 & _); unfold KEND; lia).
  set (C := mkRDA gp tp FR fc m3 SPV FF NC MSVP TLP BUF lo rt0 buf msv0).
  assert (ESPA : a_SPA C = SPAz SPV) by reflexivity.
  assert (OK : rd_okA C).
  { unfold rd_okA; cbn [a_buf a_msv0 a_rt0 a_SP a_lo a_NC a_MSVP a_TLP a_BUF a_FF C]. rewrite ESPA.
    unfold RDA_CALLEE. repeat (split; [first [assumption | lia] |]). exact I. }
  assert (SH : rd_shA C) by (unfold rd_shA; cbn; split; [exact UN3| split; [exact UM3| split; [exact UT3| exact UB3]]]).
  assert (RNGS : rd_rngA C RNG).
  { unfold rd_rngA; cbn [a_buf a_msv0 a_rt0 a_SP a_lo a_NC a_MSVP a_TLP a_BUF a_FF a_m C].
    split; [exact RI|]. split; [eapply rng_sub'; [exact RSTK| lia]|]. split; [exact RN|]. split; [exact RNS|].
    split; [exact RM|]. split; [exact RMS|]. split; [exact RT|]. split; [exact RTS|]. split; [exact RB| exact RBS]. }
  pose proof (AI_rtcells AI _ _ _ _ _ AH3) as RTC. unfold artcells in RTC.
  destruct RTC as (C0 & GOT & RIC & REAL & SHB & SUA & INI & LAY & _).
  destruct HULL as (RLO & RHI & HU1 & HU2 & HU3 & HU4 & HU5 & HU6 & WRH & RSH).
  assert (WRH3 : wr_at bsegs m3 (shad RLO) (shad RHI - shad RLO)) by (eapply wr_at_transport; [exact WRH| exact WM03]).
  pose proof (Forall_all_bytes _ FB) as AB.
  (* [comment removed for export] *)
  assert (CLOSE : forall (m' : amem) (nc : list Z) (msvw tlw : word) (r : Z)
      (z1 z5 z6 z7 z10 z12 z13 z14 z15 z16 z17 z19 z20 z21 z22 z23 z24 z27 z28 z29 z30 z31 : word),
    rd_finvA C m' nc msvw tlw -> 0 <= r < 2^64 ->
    ((exists rt msv tl n, read_ncount rt0 msv0 buf = Ok (rt, msv, tl, n) /\ r = n /\ nc = rt /\ msvw = Z_to_bv 64 msv /\ tlw = Z_to_bv 64 tl)
     \/ (exists e, read_ncount rt0 msv0 buf = Err e /\ r = 2^64 - e)) ->
    evtF bsegs RNG (rdZ_post 4304 L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV NC MSVP TLP rt0 buf msv0 lo m)
      (MS (mkR z1 (Z_to_bv 64 (a_SPA C)) gp tp z5 z6 z7 (Z_to_bv 64 SPV) (Z_to_bv 64 (a_SPA C)) z10 (Z_to_bv 64 r) z12 z13 z14 z15 z16 z17
               (Z_to_bv 64 FF) z19 z20 z21 z22 z23 z24 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) z27 z28 z29 z30 z31)
          FR (Z_to_bv 64 0xab14c) fc None m' (seg_rom bsegs))).
  { intros m' nc msvw tlw r z1 z5 z6 z7 z10 z12 z13 z14 z15 z16 z17 z19 z20 z21 z22 z23 z24 z27 z28 z29 z30 z31
           (ARR' & LNC' & HBUF' & HMSV' & HTL' & (csA & FRA' & CSA') & STL' & MU' & WM' & MI') Hr RES.
    cbn [a_NC a_rt0 a_BUF a_buf a_MSVP a_TLP a_lo a_m a_FF C] in ARR', LNC', HBUF', HMSV', HTL', FRA', STL', MU', WM', MI'.
    rewrite ESPA in *. unfold rd_WA, RDA_CALLEE in MU'. cbn [a_NC a_rt0 a_MSVP a_TLP C] in MU'. rewrite ESPA in MU'.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
    pose proof (ablk_disj_band _ _ BN) as DBN. pose proof (ablk_disj_band _ _ BM) as DBM. pose proof (ablk_disj_band _ _ BT) as DBT. unfold KLS in DBN, DBM, DBT.
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ NC (2 * zlen rt0) AH3 INN ltac:(lia)) as DFN.
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ MSVP 4 AH3 INM ltac:(lia)) as DFM.
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ TLP 4 AH3 INT ltac:(lia)) as DFT.
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; clear - FHb FHd; Z.div_mod_to_equations; lia).
    destruct (rffhdr_split _ _ _ _ FFC3) as [FF03 FF563].
    eapply (rd_closeZ 4304 L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m' SPV NC MSVP TLP lo FF r msv0 rt0 buf nc msvw tlw
              (Z_to_bv 64 0x41b58ab3) csA).
    - eapply (AI_frame AI); [exact AH3| exact MU'| exact WM'|].
      constructor; [cbn [fst snd]; replace (NC + 2 * zlen rt0 - NC) with (2 * zlen rt0) by (clear; lia); apply (fk_acr_inblk AI); destruct INN as (b & Hb & Hb1 & Hb2); exists b; split; [right; exact Hb| split; [exact Hb1| exact Hb2]]|].
      constructor; [cbn [fst snd]; replace (MSVP + 4 - MSVP) with 4 by (clear; lia); apply (fk_acr_inblk AI); destruct INM as (b & Hb & Hb1 & Hb2); exists b; split; [right; exact Hb| split; [exact Hb1| exact Hb2]]|].
      constructor; [cbn [fst snd]; replace (TLP + 4 - TLP) with 4 by (clear; lia); apply (fk_acr_inblk AI); destruct INT as (b & Hb & Hb1 & Hb2); exists b; split; [right; exact Hb| split; [exact Hb1| exact Hb2]]|].
      constructor; [cbn [fst snd]; apply (fk_acr_stack AI) with (lo := lo); clear - BOT LO SPAB SPK; unfold KEND in *; lia| constructor].
    - exact LBH.
    - exact F64. - exact FH. - exact FC. - exact RFF. - exact RSFF. - exact FFD. - exact FFA1. - exact FFA2.
    - eapply munch_trans.
      + eapply munch_weaken; [| exact MU03]. intros x Hx. cbn [outside app] in *. clear - Hx. tauto.
      + eapply munch_weaken; [| exact MU']. intros x Hx. cbn [outside app] in *. clear - Hx SPAB LO. lia.
    - eapply wmono_trans; [exact WM03| exact WM'].
    - exact MI'.
    - eapply ffr_pres_trans; [apply ffr_pres_mono_nil; exact FFR03|].
      eapply (fk_ffr_fin AI L RNG st LB m3 m3 m' 0 FF 64 (shad FF) 0
                [(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4)] [(SPAz SPV - 2224, SPAz SPV + 56)]);
        [exact AH3| exact LBH| exact FH| clear - F64; Z.div_mod_to_equations; lia| reflexivity| lia| lia| | | apply ffr_pres_refl| | exact WM'].
      + constructor; [cbn [fst snd]; split; [clear - SPAB; lia| left; clear - SPAB LO BOT SPK ATR; unfold KEND in *; lia]| constructor].
      + constructor; [split; [exists NC, (NC + 2 * zlen rt0); split; [exact BN| cbn; clear; lia]| cbn; clear - HM1 HM0; lia]|].
        constructor; [split; [exists MSVP, (MSVP + 4); split; [exact BM| cbn; clear; lia]| cbn; clear; lia]|].
        constructor; [split; [exists TLP, (TLP + 4); split; [exact BT| cbn; clear; lia]| cbn; clear; lia]| constructor].
      + eapply munch_weaken; [| exact MU']. intros x Hx. cbn [outside app] in *. clear - Hx. lia.
    - eapply rw_cells_transport; [exact SHF3| exact MU'| exact WM'|]. cbn [disjoint_from]. unfold RFFSH. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      clear - DBN DBM DBT BSF SPAB LO BOT ATR. repeat split; lia.
    - eapply rw_cells_transport; [exact FF03| exact MU'| exact WM'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - DFN DFM DFT FHc SPAB LO BOT ATR. repeat split; lia.
    - eapply rw_cells_transport; [exact FF563| exact MU'| exact WM'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - DFN DFM DFT FHc SPAB LO BOT ATR. repeat split; lia.
    - eapply rw_cells_transport; [exact FRB3| exact MU'| exact WM'|]. unfold RFRB. cbn [disjoint_from cells_size csize Nat.add]. clear - SNS SMS STS SPAB LO BOT ATR. repeat split; lia.
    - exact FRA'. - exact CSA'.
    - exact STL'.
    - eapply stk_transport; [exact STG3| exact MU'| exact WM'|]. intros x Hx. left. cbn [outside]. clear - Hx SNS SMS STS SPAB LO BOT ATR. lia.
    - exact BOT. - exact LO. - exact SPT. - exact SP16. - exact RSTK.
    - exact INN. - exact INM. - exact INT. - exact NHI. - exact MHI. - exact THI.
    - exact ARR'. - exact LNC'.
    - exact HMSV'. - exact HTL'.
    - exact Hr.
    - destruct RES as [(rt & msv & tl & n & E & -> & -> & -> & ->)|(e & E & ->)]; [left; exists rt, msv, tl, n; repeat split; try reflexivity; exact E| right; exists e; split; [exact E| reflexivity]]. }
  (* [comment removed for export] *)
  destruct (read_ncount_body8_total buf (msv0 + 1) rt0 AB ltac:(unfold FseNCount.Zlength; lia) ltac:(unfold FseNCount.Zlength; lia))
    as [(rt & msv & tlg & n & RB8 & F1 & F2 & F3 & F4 & F5 & F6 & F7) | (e & RB8)].
  - eapply evtF_cut.
    { eapply (rd_mainA C RNG OK SH RNGS rt msv tlg n tl0 j48 RLO RHI); cbn [a_m a_NC a_rt0 a_MSVP a_msv0 a_TLP a_BUF a_buf a_lo a_FF a_F a_fc a_gp a_tp a_SP C]; rewrite ?ESPA;
        first [exact ARR3| exact HMSV3| exact HTL3| exact HBUF3| exact FRA3| exact STL3| exact MI3| exact GOT| exact RIC| exact SHB| exact INI| exact LAY| exact REAL
              | exact WRH3| exact RSH| exact RB8| repeat split; lia]. }
    cbv beta. intros ms' (m' & z6 & z10 & z12 & z13 & z14 & z15 & z16 & z17 & z19 & z23 & z30 & -> & INV).
    unfold rd_lstA. rewrite ESPA. cbn [a_SP a_FF a_BUF a_NC a_msv0 a_buf a_gp a_tp a_F a_fc C].
    eapply CLOSE; [apply rd_finvA_of_inv; exact INV| clear - F5 HBL; unfold FseNCount.Zlength in F5; lia|].
    left. exists rt, msv, tlg, n. split; [| repeat split; reflexivity].
    unfold read_ncount. replace (FseNCount.Zlength buf <? 8) with false by (symmetry; apply Z.ltb_ge; unfold FseNCount.Zlength; clear - HB8; lia). exact RB8.
  - eapply evtF_cut.
    { eapply (rd_mainA_err C RNG OK SH RNGS e tl0 j48 RLO RHI); cbn [a_m a_NC a_rt0 a_MSVP a_msv0 a_TLP a_BUF a_buf a_lo a_FF a_F a_fc a_gp a_tp a_SP C]; rewrite ?ESPA;
        first [exact ARR3| exact HMSV3| exact HTL3| exact HBUF3| exact FRA3| exact STL3| exact MI3| exact GOT| exact RIC| exact SHB| exact INI| exact LAY| exact REAL
              | exact WRH3| exact RSH| exact RB8| repeat split; lia]. }
    cbv beta. intros ms' (m' & nc & msvw & tlw & z1 & z5 & z6 & z7 & z10 & z12 & z13 & z14 & z15 & z16 & z17 & z19 & z20 & z21 & z22 & z23 & z24 & z27 & z28 & z29 & z30 & z31 & -> & FINV).
    cbn [a_SP a_FF a_gp a_tp a_F a_fc C].
    pose proof (read_body8_err_invA buf (msv0 + 1) rt0 e ltac:(clear - HB8; lia) AB ltac:(clear - HM0 HM1; lia) RB8) as EE.
    eapply CLOSE; [exact FINV| destruct EE as [[_ ->]|[_ [-> _]]]; clear; lia|].
    right. exists e. split; [| reflexivity].
    unfold read_ncount. replace (FseNCount.Zlength buf <? 8) with false by (symmetry; apply Z.ltb_ge; unfold FseNCount.Zlength; clear - HB8; lia). exact RB8.
Qed.
(* [comment removed for export] *)
Lemma rd_small2Z : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP lo : Z) (RNG : footprint)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x27 x28 x29 x30 x31 : word) (m : amem) (FF r hb : Z) (Q : machine_state -> Prop),
  SP mod 16 = 0 -> SP + 16 < KEND -> rng_aimg RNG ->
  rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) RFFSH0 -> mem_inv bsegs m ->
  ablk FF (FF + 64) -> FF mod 64 = 0 -> rng RNG (shad FF) 8 ->
  0 <= r < 2^64 -> 0 <= hb < 8 ->
  (forall m' (y10 y12 : word) (r' : Z),
      ((r' = r /\ ~ (r < 2^64 - 119 /\ hb < r)) \/ (r' = 2^64 - 20 /\ r < 2^64 - 119 /\ hb < r)) ->
      munch [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
      rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) RFFSH ->
      evtF bsegs RNG Q
        (MS (mkR x1 (Z_to_bv 64 (SPAz SP)) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 (SPAz SP))
                 y10 (Z_to_bv 64 r') y12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 FF) x19 x20 x21 x22 (Z_to_bv 64 hb) x23 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0xab14c) fc None m' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
    (MS (mkR x1 (Z_to_bv 64 (SPAz SP)) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 (SPAz SP))
             (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) x19 x20 x21 x22 (Z_to_bv 64 hb) x23 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0xaac24) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros SP16 SPT RI SHF MI FH F64 RSF Hr Hhb K.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
  pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu. pose proof atop_range as ATR. unfold KEND in SPT.
  replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; clear - FHb FHd; Z.div_mod_to_equations; lia).
  unfold RFFSH0 in SHF.
  pose proof (munch_refl [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
  zstep. bcase B.
  - (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    eapply K; try eassumption. left. split; [reflexivity|].
    clear - B Hr Hhb. intros [H1 H2]. revert B. destruct (Z.ltb_spec r 18446744073709551497); destruct (Z.ltb_spec hb r); intros B; first [lia | vm_compute in B; lia].
  - (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply Z_to_bv_eqm; reflexivity).
    zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    zstep. zstep.
    eapply K; try eassumption. right. split; [reflexivity|].
    clear - B Hr Hhb. revert B. destruct (Z.ltb_spec r 18446744073709551497); destruct (Z.ltb_spec hb r); intros B; first [lia | vm_compute in B; lia].
Qed.

(* [comment removed for export] *)
Lemma rd_call8Z : forall (k : nat) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (SPV NC MSVP TLP BUF lo msv0 : Z) (rt0 buf : list Z) (tl0 : word),
  Z.of_nat k < 16384 -> zlen buf = 8 ->
  AHEAP AI L RNG st LB m -> fake_le 0 k LB -> ablkLB LB ->
  rng_aimg RNG -> rng RNG lo (al_top L - lo) -> rng_fs L RNG ->
  ATOP + 4096 <= lo -> lo <= SPV - 4304 -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  stk bsegs m lo SPV -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  Forall (fun c => 0 <= c < 256) buf -> 0 <= msv0 <= 255 -> msv0 + 1 <= zlen rt0 -> zlen rt0 <= 65536 ->
  NC mod 2 = 0 -> MSVP mod 4 = 0 -> TLP mod 4 = 0 ->
  (NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC) -> (NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC) ->
  (NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC) -> (MSVP + 4 <= TLP \/ TLP + 4 <= MSVP) ->
  (MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP) -> (TLP + 4 <= BUF \/ BUF + zlen buf <= TLP) ->
  (NC + 2 * zlen rt0 <= lo \/ SPV <= NC) -> (MSVP + 4 <= lo \/ SPV <= MSVP) -> (TLP + 4 <= lo \/ SPV <= TLP) -> (BUF + zlen buf <= lo \/ SPV <= BUF) ->
  ablk NC (NC + 2 * zlen rt0) -> ablk MSVP (MSVP + 4) -> ablk TLP (TLP + 4) -> ablk BUF (BUF + zlen buf) ->
  ainblk LB NC (2 * zlen rt0) -> ainblk LB MSVP 4 -> ainblk LB TLP 4 -> ainblk LB BUF (zlen buf) ->
  NC + 2 * zlen rt0 <= 2^47 -> MSVP + 4 <= 2^47 -> TLP + 4 <= 2^47 -> BUF + zlen buf <= 2^47 ->
  rng RNG NC (2 * zlen rt0) -> rng RNG (shad NC) (shspan NC (2 * zlen rt0)) -> rng RNG MSVP 4 -> rng RNG (shad MSVP) 1 ->
  rng RNG TLP 4 -> rng RNG (shad TLP) 1 -> rng RNG BUF (zlen buf) -> rng RNG (shad BUF) (shspan BUF (zlen buf)) ->
  ahull RNG m NC (2 * zlen rt0) ->
  u8arr bsegs m NC (u16s (map (Z_to_bv 64) rt0)) -> unpoisoned m NC (NC + 2 * zlen rt0) ->
  rw_cells bsegs m MSVP [C4 (Z_to_bv 64 msv0)] -> unpoisoned m MSVP (MSVP + 4) ->
  rw_cells bsegs m TLP [C4 tl0] -> unpoisoned m TLP (TLP + 4) ->
  bytes_at bsegs m BUF (map (Z_to_bv 8) buf) -> unpoisoned m BUF (BUF + zlen buf) ->
  evtF bsegs RNG (rdZ_post 4304 L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV NC MSVP TLP rt0 buf msv0 lo m)
    (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
             (Z_to_bv 64 (zlen buf)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 AFSE_RD_BODY) fc None m (seg_rom bsegs)).
Proof.
  intros k L RNG st LB ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV NC MSVP TLP BUF lo msv0 rt0 buf tl0
         HK HB8 AH FLE LBH RI RSTK RFS BOT LO SPT SP16 ST MI TP FB HM0 HM1 HRT N2 M4 T4 S1 S2 S3 S4 S5 S6 SNS SMS STS SBS
         BN BM BT BB INN INM INT INB NHI MHI THI BHI RN RNS RM RMS RT RTS RB RBS HULL ARR UN HMSV UM HTL UT HBUF UB.
  assert (LBS : zlen (map (Z_to_bv 8) buf) = zlen buf) by (rewrite length_map; reflexivity).
  assert (B0 : 0 <= BUF) by (destruct UB as (U & _); exact U).
  eapply evtF_cut; [| intros ms' H; exact H].
  eapply (rd_openZ k L RNG st LB ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV NC MSVP TLP BUF (zlen buf) lo
            (u16s (map (Z_to_bv 64) rt0)) (map (Z_to_bv 8) buf) (Z_to_bv 64 msv0) tl0
            (fun ms => evtF bsegs RNG (rdZ_post 4304 L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV NC MSVP TLP rt0 buf msv0 lo m) ms));
    rewrite ?u16s_length, ?length_map, ?LBS;
    first [exact HK| exact AH| exact FLE| exact LBH| exact RI| exact RSTK| exact RFS| exact BOT| exact LO| exact SPT| exact SP16| exact ST| exact MI| exact TP| exact BB
          | exact ARR| exact HMSV| exact HTL| exact HBUF| exact M4| exact RMS| exact B0 | idtac].
  all: try (clear - HB8; lia).
  all: try (replace (Z.of_nat (2 * length rt0)) with (2 * zlen rt0) by (clear; lia)). all: try assumption.
  all: try (clear - HB8 NHI MHI THI BHI SNS SMS STS SBS; lia). all: try (intros _; left; exact INB).
  cbv beta.
  intros FF m3 j48 junk x5 x6 x7 y10 y11 y13 y14 x15 x16 x17 x28 x29 x30 x31 F64 FH FC RFF RSFF FFD FFA1 FFA2 AH3 MU03 WM03 FFR03 MI3
         FRB3 FRA3 FFC3 SHF3 STL3 STG3 ARR3 UN3 HMSV3 UM3 HTL3 UT3 HBUF3 UB3.
  replace (7 <? zlen buf) with true by (symmetry; apply Z.ltb_lt; clear - HB8; lia).
  rewrite ?u16s_length, ?length_map, ?LBS in *.
  replace (Z.of_nat (2 * length rt0)) with (2 * zlen rt0) in * by (clear; lia).
  eapply (rd_body8Z L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m3 SPV NC MSVP TLP BUF lo FF msv0 rt0 buf tl0 j48 junk);
    first [eassumption | clear - HB8; lia | idtac].
Qed.


(* [comment removed for export] *)
Lemma ainblk_cons : forall b LB X n, ainblk LB X n -> ainblk (b :: LB) X n.
Proof. intros b LB X n (b' & Hb & H1 & H2). exists b'. split; [right; exact Hb| split; [exact H1| exact H2]]. Qed.

Lemma ffr_pres_tail : forall W b LB (m m' : amem), ffr_pres W (b :: LB) m m' -> ffr_pres W LB m m'.
Proof.
  intros W b LB m m' H a Ha HP. apply (H a Ha).
  destruct HP as [[(c & A & n & Hin & Hr) HO]|(a' & (c & A & n & Hin & Hr) & E)].
  - left. split; [exists c, A, n; split; [right; exact Hin| exact Hr]| exact HO].
  - right. exists a'. split; [exists c, A, n; split; [right; exact Hin| exact Hr]| exact E].
Qed.

Lemma ffr_frame_cells : forall W FF LB (m m' : amem) A cs,
  ffr_pres W (FB0 FF :: LB) m m' -> rw_cells bsegs m A cs -> FF <= A -> A + Z.of_nat (cells_size cs) <= FF + 64 ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> outside W a) -> rw_cells bsegs m' A cs.
Proof.
  intros W FF LB m m' A cs FP RC H1 H2 HO. eapply rw_cells_magree; [exact FP| exact RC|].
  intros a Ha. left. split; [| exact (HO a Ha)]. exists 0, FF, 64. split; [left; reflexivity| lia].
Qed.

Lemma ffr_fshadow_cells : forall W FF LB (m m' : amem) cs,
  ffr_pres W (FB0 FF :: LB) m m' -> rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) cs -> FF mod 8 = 0 -> 0 <= FF ->
  Z.of_nat (cells_size cs) <= 8 -> rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) cs.
Proof.
  intros W FF LB m m' cs FP RC F8 F0 SZ. eapply rw_cells_magree; [exact FP| exact RC|].
  rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  intros a Ha. right. exists (FF + 8 * (a - (FF / 8 + 2147450880))). split.
  - exists 0, FF, 64. split; [left; reflexivity|]. clear - Ha F8 SZ. Z.div_mod_to_equations. lia.
  - rewrite shad_div. unfold ASHOFF. clear - F8. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma fra10_merge : forall (m1 : amem) A FF MSVP (k0 k8 k16 k32 k40 k48 k64 : list byte),
  rw_cells bsegs m1 A [CB 8 k0; CB 8 k8; CB 8 k16; C8 (Z_to_bv 64 FF); CB 8 k32; CB 8 k40; CB 8 k48; C8 (Z_to_bv 64 MSVP); CB 16 k64; C8 (Z_to_bv 64 FF)] ->
  exists c0 c32, rw_cells bsegs m1 A [CB 24 c0; C8 (Z_to_bv 64 FF); CB 56 c32].
Proof.
  intros m1 A FF MSVP k0 k8 k16 k32 k40 k48 k64 FRM4.
  change [CB 8 k0; CB 8 k8; CB 8 k16; C8 (Z_to_bv 64 FF); CB 8 k32; CB 8 k40; CB 8 k48; C8 (Z_to_bv 64 MSVP); CB 16 k64; C8 (Z_to_bv 64 FF)]
    with ([CB 8 k0; CB 8 k8; CB 8 k16; C8 (Z_to_bv 64 FF)]
          ++ [CB 8 k32; CB 8 k40; CB 8 k48; C8 (Z_to_bv 64 MSVP); CB 16 k64; C8 (Z_to_bv 64 FF)]
          ++ []) in FRM4.
  apply rw_cells_merge in FRM4.
  lazymatch type of FRM4 with rw_cells ?sg ?mm ?AA (?l ++ ?x) =>
    change (rw_cells sg mm AA ([] ++ [CB 8 k0; CB 8 k8; CB 8 k16] ++ (C8 (Z_to_bv 64 FF) :: x))) in FRM4 end.
  apply rw_cells_merge in FRM4. cbn [app cells_size csize Nat.add] in FRM4.
  do 2 eexists. exact FRM4.
Qed.


(* [comment removed for export] *)
Lemma rd_smallZ : forall (k : nat) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m m3 : amem) (SPV NC MSVP TLP BUF lo FF msv0 : Z) (rt0 buf : list Z) (tl0 : word) (j48 junk : list byte)
    (x1 x5 x6 x7 y10 y11 y13 y14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
  Z.of_nat k < 16383 -> fake_le 0 k LB -> rng_fs L RNG -> tp = Z_to_bv 64 ATP ->
  zlen buf < 8 -> Forall (fun c => 0 <= c < 256) buf -> 0 <= msv0 <= 255 -> msv0 + 1 <= zlen rt0 -> zlen rt0 <= 65536 ->
  NC mod 2 = 0 -> MSVP mod 4 = 0 -> TLP mod 4 = 0 ->
  (NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC) -> (NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC) -> (MSVP + 4 <= TLP \/ TLP + 4 <= MSVP) ->
  (NC + 2 * zlen rt0 <= lo \/ SPV <= NC) -> (MSVP + 4 <= lo \/ SPV <= MSVP) -> (TLP + 4 <= lo \/ SPV <= TLP) ->
  ablk NC (NC + 2 * zlen rt0) -> ablk MSVP (MSVP + 4) -> ablk TLP (TLP + 4) -> ablk BUF (BUF + zlen buf) ->
  ainblk LB NC (2 * zlen rt0) -> ainblk LB MSVP 4 -> ainblk LB TLP 4 ->
  (BUF + zlen buf <= FF \/ FF + 64 <= BUF \/ zlen buf = 0) ->
  NC + 2 * zlen rt0 <= 2^47 -> MSVP + 4 <= 2^47 -> TLP + 4 <= 2^47 ->
  rng_aimg RNG -> rng RNG lo (al_top L - lo) ->
  rng RNG NC (2 * zlen rt0) -> rng RNG (shad NC) (shspan NC (2 * zlen rt0)) -> rng RNG MSVP 4 -> rng RNG (shad MSVP) 1 ->
  rng RNG TLP 4 -> rng RNG (shad TLP) 1 -> rng RNG BUF (zlen buf) ->
  ahull RNG m NC (2 * zlen rt0) -> ahull RNG m BUF (zlen buf) ->
  FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  al_fake L <= FF -> FF + 64 <= al_fake L + FAKESZ ->
  ATOP + 4096 <= lo -> lo <= SPV - 4512 -> SPV + 16 < al_top L -> SPV mod 16 = 0 -> ablkLB LB ->
  AHEAP AI L RNG st (FB0 FF :: LB) m3 ->
  munch ([(SPV - 4304, SPV)] ++ fake_area L) m m3 -> wmono bsegs m m3 -> ffr_pres [] LB m m3 -> mem_inv bsegs m3 ->
  rw_cells bsegs m3 (SPV + -104) (RFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells bsegs m3 (SPAz SPV) [CB 48 j48; C8 (Z_to_bv 64 FF)] ->
  rw_cells bsegs m3 FF (RFFHDR FF (fflag L 0 FF) junk) -> rw_cells bsegs m3 (Z.shiftr FF 3 + 2147450880) RFFSH ->
  stk bsegs m3 lo (SPAz SPV) -> stk bsegs m3 (SPAz SPV + 56) (SPV + -104) ->
  u8arr bsegs m3 NC (u16s (map (Z_to_bv 64) rt0)) -> unpoisoned m3 NC (NC + 2 * zlen rt0) ->
  rw_cells bsegs m3 MSVP [C4 (Z_to_bv 64 msv0)] -> unpoisoned m3 MSVP (MSVP + 4) ->
  rw_cells bsegs m3 TLP [C4 tl0] -> unpoisoned m3 TLP (TLP + 4) ->
  bytes_at bsegs m3 BUF (map (Z_to_bv 8) buf) -> unpoisoned m3 BUF (BUF + zlen buf) ->
  evtF bsegs RNG (rdZ_post 4512 L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV NC MSVP TLP rt0 buf msv0 lo m)
    (MS (mkR x1 (Z_to_bv 64 (SPAz SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAz SPV))
             y10 y11 (Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) y13 y14 x15 x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
             (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 0xaabec) fc None m3 (seg_rom bsegs)).
Proof.
  intros k L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m3 SPV NC MSVP TLP BUF lo FF msv0 rt0 buf tl0 j48 junk
         x1 x5 x6 x7 y10 y11 y13 y14 x15 x16 x17 x27 x28 x29 x30 x31
         HK FLE RFS TP HB8 FB HM0 HM1 HRT N2 M4 T4 S1 S2 S4 SNS SMS STS BN BM BT BB INN INM INT SEPB NHI MHI THI
         RI RSTK RN RNS RM RMS RT RTS RB HULL HULLB F64 FH FC RFF RSFF FFD FFA1 FFA2 BOT LO SPT SP16 LBH
         AH3 MU03 WM03 FFR03 MI3 FRB3 FRA3 FFC3 SHF3 STL3 STG3 ARR3 UN3 HMSV3 UM3 HTL3 UT3 HBUF3 UB3.
  pose proof atop_range as ATR.
  pose proof (spa_props2 SPV SP16) as (SPAB & SPA32).
  pose proof (AI_layout AI _ _ _ _ _ AH3) as (LY1 & LY2 & LY3 & LY4 & _).
  assert (SPK : SPV + 16 < KEND) by (unfold KEND; clear - SPT LY3; lia).
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  pose proof (ablk_lin _ _ BB) as (BBa & BBb & BBc & BBd). unfold AIMG_HI in BBa.
  assert (HB0 : 0 <= zlen buf) by (clear; lia).
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; clear - FHb FHd; Z.div_mod_to_equations; lia).
  assert (BSF8 : 2147450880 <= FF / 8 + 2147450880 /\ FF / 8 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 in BSF by (clear; lia); exact BSF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH3) as RTC. unfold artcells in RTC.
  destruct RTC as (C0 & GOT & RIC & REAL & SHB & SUA & INI & LAY & _).
  destruct (fk_ahull_pres RNG m m3 BUF (zlen buf) WM03 HULLB) as (RLO1 & RHI1 & HL1 & HL2 & HL3 & HL4 & HL5 & HL6 & WR1 & RSH1).
  (* [comment removed for export] *)
  eapply (rd_small1z gp tp FR fc SPV lo SP16 SPK ltac:(clear - LO; lia) ltac:(clear - BOT; lia) RNG ltac:(eapply rng_sub'; [exact RSTK| clear - SPT; lia]) RI
            x1 y10 y11 (Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) y13 y14 x15 x5 x6 x7 x16 x17 x27 x28 x29 x30 x31
            m3 FF (fflag L 0 FF) MSVP BUF NC TLP buf junk RLO1 RHI1);
    first [exact HBUF3| exact FFC3| exact SHF3| exact MI3| exact STL3| exact GOT| exact RIC| exact SHB| exact INI| exact LAY| exact REAL
          | exact UB3| exact WR1| exact RSH1| exact FH| exact FC| exact F64| exact SEPB| exact BB| exact RFF| exact RSFF| exact RB| exact FB
          | apply ablk_app_blk; [exact BB| clear - HB0; lia]
          | clear - HB8 HB0; lia
          | split; [exact HL1|]; split; [exact HL2|]; split; [exact HL3|]; split; [exact HL4|]; split; [exact HL5| exact HL6]
          | idtac].
  intros m5 rs j16 y5 y6 y7 y16 y17 y28 y29 y30 y31 MU5 WM5 MI5 STL5 FFC5 SHF5 HBUF5.
  clear C0 GOT RIC REAL SHB SUA INI LAY WR1 RSH1.
  set (W5 := [(SPAz SPV - 2224, SPAz SPV); (FF + 24, FF + 56); (Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)]) in MU5.
  set (hb := zlen buf) in *. set (buf' := buf ++ repeat 0 (Z.to_nat (8 - hb))) in *.
  assert (LB' : zlen buf' = 8) by (subst buf' hb; rewrite length_app, repeat_length; clear - HB8; lia).
  assert (FB' : Forall (fun c => 0 <= c < 256) buf').
  { subst buf'. apply Forall_app. split; [exact FB|]. apply Forall_forall. intros c Hc. apply repeat_spec in Hc. subst c. clear. lia. }
  (* [comment removed for export] *)
  assert (AH5 : AHEAP AI L RNG st (FB0 FF :: LB) m5).
  { eapply (AI_frame AI); [exact AH3| exact MU5| exact WM5|]. subst W5.
    constructor; [cbn [fst snd]; replace (SPAz SPV - (SPAz SPV - 2224)) with 2224 by (clear; lia); apply (fk_acr_stack AI) with (lo := lo); clear - BOT LO SPAB SPK; unfold KEND in *; lia|].
    constructor; [cbn [fst snd]; replace (FF + 56 - (FF + 24)) with 32 by (clear; lia); apply (fk_acr_frame AI) with (c := 0) (F := FF) (N := 64); [left; reflexivity| clear; lia| clear; lia]|].
    constructor; [| constructor]. cbn [fst snd].
    replace (Z.shiftr FF 3 + 2147450880 + 5 - (Z.shiftr FF 3 + 2147450880 + 4)) with 1 by (clear; lia).
    replace (Z.shiftr FF 3 + 2147450880 + 4) with (shad (FF + 32)) by (rewrite shad_div, Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold ASHOFF; clear - F64; Z.div_mod_to_equations; lia).
    apply (fk_acr_fshadow AI) with (c := 0) (F := FF) (N := 64); [left; reflexivity| clear; lia| clear; lia| clear - F64; Z.div_mod_to_equations; lia| clear - FHb; lia]. }
  (* [comment removed for export] *)
  pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ NC (2 * zlen rt0) AH3 INN ltac:(clear - HM0 HM1; lia)) as DNF.
  pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ MSVP 4 AH3 INM ltac:(clear; lia)) as DMF.
  pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ TLP 4 AH3 INT ltac:(clear; lia)) as DTF.
  pose proof (ablk_disj_band _ _ BN) as DBN. pose proof (ablk_disj_band _ _ BM) as DBM. pose proof (ablk_disj_band _ _ BT) as DBT. unfold KLS in DBN, DBM, DBT.
  pose proof (ablk_lin _ _ BN) as (BNa & BNb & BNc & BNd). pose proof (ablk_lin _ _ BM) as (BMa & BMb & BMc & BMd). pose proof (ablk_lin _ _ BT) as (BTa & BTb & BTc & BTd).
  unfold AIMG_HI in BNa, BMa, BTa.
  assert (D5 : forall X n, (X + n <= FF \/ FF + 64 <= X) -> (X + n <= lo \/ SPV <= X) -> (X + n <= 0x7fff7000 \/ 0x10007fff8000 <= X) -> 0 <= n ->
             disjoint_from W5 X n /\ (0 < n -> 0 <= X -> X + n <= 2^47 -> disjoint_from W5 (shad X) (shad (X + n - 1) + 1 - shad X))).
  { intros X n HXF HXS HXB Hn. subst W5. cbn [disjoint_from]. rewrite !shad_div. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ASHOFF.
    pose proof (ablk_disj_band _ _ FH) as DBF. unfold KLS in DBF.
    clear - HXF HXS HXB Hn SPAB LO BOT FHa FHb FHc FHd F64 ATR BSF8 DBF.
    split; [| intros Hp X0 XH]; (split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]). }
  destruct (D5 NC (2 * zlen rt0) DNF SNS DBN ltac:(clear - HM0 HM1; lia)) as [DN DSN].
  destruct (D5 MSVP 4 DMF SMS DBM ltac:(clear; lia)) as [DM DSM].
  destruct (D5 TLP 4 DTF STS DBT ltac:(clear; lia)) as [DT DST].
  assert (LNC : Z.of_nat (length (u16s (map (Z_to_bv 64) rt0))) = 2 * zlen rt0) by (rewrite u16s_length, length_map; clear; lia).
  assert (ARR5 : u8arr bsegs m5 NC (u16s (map (Z_to_bv 64) rt0))) by (eapply u8arr_transport; [exact ARR3| exact MU5| exact WM5| rewrite LNC; exact DN]).
  assert (HMSV5 : rw_cells bsegs m5 MSVP [C4 (Z_to_bv 64 msv0)]) by (eapply rw_cells_transport; [exact HMSV3| exact MU5| exact WM5| exact DM]).
  assert (HTL5 : rw_cells bsegs m5 TLP [C4 tl0]) by (eapply rw_cells_transport; [exact HTL3| exact MU5| exact WM5| exact DT]).
  assert (UN5 : unpoisoned m5 NC (NC + 2 * zlen rt0)) by (eapply unpoisoned_munch; [exact UN3| exact MU5| apply DSN; clear - HM0 HM1 BNb NHI; lia]).
  assert (UM5 : unpoisoned m5 MSVP (MSVP + 4)) by (eapply unpoisoned_munch; [exact UM3| exact MU5| apply DSM; clear - BMb MHI; lia]).
  assert (UT5 : unpoisoned m5 TLP (TLP + 4)) by (eapply unpoisoned_munch; [exact UT3| exact MU5| apply DST; clear - BTb THI; lia]).
  (* [comment removed for export] *)
  assert (FRB5 : rw_cells bsegs m5 (SPV + -104) (RFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_transport; [exact FRB3| exact MU5| exact WM5|]. subst W5. unfold RFRB. cbn [disjoint_from cells_size csize Nat.add].
    clear - SPAB FHc BOT LO ATR BSF. repeat split; lia. }
  assert (STG5 : stk bsegs m5 (SPAz SPV + 56) (SPV + -104)).
  { eapply stk_transport; [exact STG3| exact MU5| exact WM5|]. subst W5. intros x Hx. left. cbn [outside]. clear - Hx SPAB FHc BOT LO ATR BSF. lia. }
  assert (FRA5 : rw_cells bsegs m5 (SPAz SPV) [CB 48 j48; C8 (Z_to_bv 64 FF)]).
  { eapply rw_cells_transport; [exact FRA3| exact MU5| exact WM5|]. subst W5. cbn [disjoint_from cells_size csize Nat.add].
    clear - SPAB FHc BOT LO ATR BSF. repeat split; lia. }
  (* [comment removed for export] *)
  destruct (rffhdr5_split m5 FF rs _ j16 (fflag L 0 FF) FFC5) as (FF05 & FB5 & FF565).
  assert (IHBUF : bytes_at bsegs m5 (FF + 32) (map (Z_to_bv 8) buf')).
  { destruct FB5 as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. exact BA. }
  assert (IUB : unpoisoned m5 (FF + 32) (FF + 32 + zlen buf')).
  { rewrite LB'. apply c1z_unpoisonedR; [| clear - F64; Z.div_mod_to_equations; lia| clear - FHb; lia| clear; lia| clear - FHd; lia].
    replace (Z.shiftr (FF + 32) 3 + 2147450880) with (Z.shiftr FF 3 + 2147450880 + 4); [exact (rffsh0_byte4 _ _ SHF5)|].
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - F64. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (ILBH : ablkLB (FB0 FF :: LB)) by (apply ablkLB_cons; [exact FH| exact LBH]).
  assert (IFLE : fake_le 0 (S k) (FB0 FF :: LB)) by (apply fake_le_push_any; exact FLE).
  assert (IHK : Z.of_nat (S k) < 16384) by (clear - HK; lia).
  assert (ILO : lo <= SPAz SPV - 4304) by (clear - LO SPAB; lia).
  assert (ISPT : SPAz SPV + 16 < al_top L) by (clear - SPT SPAB; lia).
  assert (ISP16 : SPAz SPV mod 16 = 0) by (clear - SPA32; Z.div_mod_to_equations; lia).
  assert (IBB : ablk (FF + 32) (FF + 32 + zlen buf')) by (rewrite LB'; eapply ablk_sub; [exact FH| clear; lia| clear; lia]).
  assert (IINB : ainblk (FB0 FF :: LB) (FF + 32) (zlen buf')) by (rewrite LB'; exists (FB0 FF); split; [left; reflexivity| cbn; clear; lia]).
  assert (IRBf : rng RNG (FF + 32) (zlen buf')) by (rewrite LB'; eapply rng_sub'; [exact RFF| clear; lia]).
  assert (IRBS : rng RNG (shad (FF + 32)) (shspan (FF + 32) (zlen buf'))).
  { rewrite LB'. eapply rng_sub'; [exact RSFF|]. unfold shspan. rewrite !shad_div. unfold ASHOFF. clear - F64 FHb. Z.div_mod_to_equations. lia. }
  assert (IHULL : ahull RNG m5 NC (2 * zlen rt0)) by (eapply fk_ahull_pres; [eapply wmono_trans; [exact WM03| exact WM5]| exact HULL]).
  replace (Z_to_bv 64 8) with (Z_to_bv 64 (zlen buf')) by (rewrite LB'; reflexivity).
  eapply evtF_cut.
  { eapply (rd_call8Z (S k) L RNG st (FB0 FF :: LB) (Z_to_bv 64 0xaac24) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAz SPV)) (Z_to_bv 64 0) y16 y17
              (Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 hb) (Z_to_bv 64 (FF + 32))
              (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 y28 y29 y30 y31 FR fc m5 (SPAz SPV) NC MSVP TLP (FF + 32) lo msv0 rt0 buf' tl0);
      first [exact IHK| exact LB'| exact AH5| exact IFLE| exact ILBH| exact RI| exact RSTK| exact RFS| exact BOT| exact ILO| exact ISPT| exact ISP16| exact STL5| exact MI5| exact TP
            | exact FB'| exact HM0| exact HM1| exact HRT| exact N2| exact M4| exact T4| exact S1| exact S2| exact S4
            | exact BN| exact BM| exact BT| exact IBB| exact IINB| apply ainblk_cons; assumption
            | exact NHI| exact MHI| exact THI| exact RN| exact RNS| exact RM| exact RMS| exact RT| exact RTS| exact IRBf| exact IRBS| exact IHULL
            | exact ARR5| exact UN5| exact HMSV5| exact UM5| exact HTL5| exact UT5| exact IHBUF| exact IUB
            | rewrite ?LB'; clear - DNF DMF DTF SNS SMS STS FHc FHd BOT LO SPAB; lia
            | idtac]. }
  cbv beta. intros ms' PO. unfold rdZ_post in PO.
  destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & m7 & r & rt' & msvw & tlw
                  & -> & MU7 & WM7 & MI7 & ST7 & FFR7 & AH7 & ARR7 & LRT & HMSV7 & HTL7 & Hr & RES).
  rd_retlit.
  clear ARR5 HMSV5 HTL5 UN5 UM5 UT5 IHBUF IUB IRBf IRBS IHULL ARR3 HMSV3 HTL3 UN3 UM3 UT3 HBUF3 UB3.
  (* [comment removed for export] *)
  assert (SHF7 : rw_cells bsegs m7 (Z.shiftr FF 3 + 2147450880) RFFSH0)
    by (eapply ffr_fshadow_cells; [exact FFR7| exact SHF5| clear - F64; Z.div_mod_to_equations; lia| exact FHb| cbn; clear; lia]).
  (* [comment removed for export] *)
  assert (RB8 : read_ncount rt0 msv0 buf' = read_ncount_body8 buf' (msv0 + 1) rt0).
  { unfold read_ncount. unfold FseNCount.Zlength. rewrite LB'. reflexivity. }
  assert (RSZ : r < 2^64 - 119 -> exists rt msv tl n, read_ncount_body8 buf' (msv0 + 1) rt0 = Ok (rt, msv, tl, n) /\ r = n /\ 1 <= n <= 8
                                    /\ rt' = rt /\ msvw = Z_to_bv 64 msv /\ tlw = Z_to_bv 64 tl).
  { intros HR. destruct RES as [(rt & msv & tl & n & E & -> & -> & -> & ->)|(e & E & ->)].
    - rewrite RB8 in E. exists rt, msv, tl, n. split; [exact E|]. split; [reflexivity|]. split; [| repeat split; reflexivity].
      destruct (read_ncount_body8_total buf' (msv0 + 1) rt0 (Forall_all_bytes _ FB') ltac:(unfold FseNCount.Zlength; clear - LB'; lia)
                  ltac:(unfold FseNCount.Zlength; clear - HM1 HM0; lia)) as [(nc2 & msv2 & tl2 & n2 & E2 & _ & _ & _ & _ & NN2 & _) | (ee2 & E2)];
        rewrite E in E2; [injection E2 as <- <- <- <-; unfold FseNCount.Zlength in NN2; rewrite LB' in NN2; exact NN2| discriminate E2].
    - exfalso. rewrite RB8 in E.
      pose proof (read_body8_err_invA buf' (msv0 + 1) rt0 e ltac:(clear - LB'; lia) (Forall_all_bytes _ FB') ltac:(clear - HM0 HM1; lia) E) as EE.
      clear - EE HR. destruct EE as [[_ ->]|[_ [-> _]]]; lia. }
  assert (RER : 2^64 - 119 <= r -> exists e, read_ncount_body8 buf' (msv0 + 1) rt0 = Err e /\ r = 2^64 - e).
  { intros HR. destruct RES as [(rt & msv & tl & n & E & -> & _)|(e & E & ->)].
    - exfalso. rewrite RB8 in E.
      destruct (read_ncount_body8_total buf' (msv0 + 1) rt0 (Forall_all_bytes _ FB') ltac:(unfold FseNCount.Zlength; clear - LB'; lia)
                  ltac:(unfold FseNCount.Zlength; clear - HM1 HM0; lia)) as [(nc2 & msv2 & tl2 & n2 & E2 & _ & _ & _ & _ & NN2 & _) | (ee2 & E2)];
        rewrite E in E2; [injection E2 as <- <- <- <-; unfold FseNCount.Zlength in NN2; rewrite LB' in NN2; clear - NN2 HR; lia| discriminate E2].
    - rewrite RB8 in E. exists e. split; [exact E| reflexivity]. }
  clear RES.
  (* [comment removed for export] *)
  eapply (rd_small2Z (Z_to_bv 64 0xaac24) gp tp (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAz SPV)) (Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF)
            (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 hb) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27
            FR fc SPV lo RNG);
    first [exact SP16| exact SPK| exact RI| exact SHF7| exact MI7| exact FH| exact F64| exact RSFF| exact Hr| clear - HB8 HB0; subst hb; lia| idtac].
  intros m6 z10 z11 r' Hr' MU6 WM6 MI6 SHF6.
  (* [comment removed for export] *)
  destruct (FHL _ _ _ _ _ AH3) as [FAB _]. pose proof (ablk_lin _ _ FAB) as (FABa & FABb & FABc & FABd).
  assert (AH6 : AHEAP AI L RNG st (FB0 FF :: LB) m6).
  { eapply (AI_frame AI); [exact AH7| exact MU6| exact WM6|]. constructor; [| constructor]. cbn [fst snd].
    replace (Z.shiftr FF 3 + 2147450880 + 5 - (Z.shiftr FF 3 + 2147450880 + 4)) with 1 by (clear; lia).
    replace (Z.shiftr FF 3 + 2147450880 + 4) with (shad (FF + 32)) by (rewrite shad_div, Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold ASHOFF; clear - F64; Z.div_mod_to_equations; lia).
    apply (fk_acr_fshadow AI) with (c := 0) (F := FF) (N := 64); [left; reflexivity| clear; lia| clear; lia| clear - F64; Z.div_mod_to_equations; lia| clear - FHb; lia]. }
  (* [comment removed for export] *)
  assert (DW6 : forall A n, (A + n <= 0x7fff7000 \/ 0x10007fff8000 <= A) -> disjoint_from [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] A n).
  { intros A n HA. cbn [disjoint_from]. split; [| exact I]. clear - HA BSF. lia. }
  assert (DW6s : forall A n, ATOP <= A -> disjoint_from [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] A n).
  { intros A n HA. cbn [disjoint_from]. split; [| exact I]. clear - HA BSF ATR. lia. }
  (* [comment removed for export] *)
  assert (DS7 : forall A n, SPAz SPV <= A -> A + n <= SPV -> 0 <= n ->
             disjoint_from ([(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4); (SPAz SPV - 4304, SPAz SPV)] ++ fake_area L) A n).
  { intros A n HA HB Hn. cbn [disjoint_from fake_area app]. rewrite shad_div.
    clear - HA HB Hn SNS SMS STS SPAB FABc FABb BOT LO ATR HM0 HM1. unfold ASHOFF, FAKESZ in *. repeat split; Z.div_mod_to_equations; lia. }
  pose proof (ablk_disj_band _ _ FH) as DBF. unfold KLS in DBF.
  assert (FF06 : rw_cells bsegs m6 FF [C8 (Z_to_bv 64 0x41b58ab3)]).
  { eapply rw_cells_transport; [| exact MU6| exact WM6| rewrite zsize_c8; apply DW6; clear - DBF; lia].
    eapply ffr_frame_cells; [exact FFR7| exact FF05| clear; lia| rewrite zsize_c8; clear; lia|].
    rewrite zsize_c8. intros a Ha. cbn [outside]. clear - Ha DNF DMF DTF HM0 HM1. repeat split; lia. }
  assert (FF566 : rw_cells bsegs m6 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))]).
  { eapply rw_cells_transport; [| exact MU6| exact WM6| rewrite zsize_c8; apply DW6; clear - DBF; lia].
    eapply ffr_frame_cells; [exact FFR7| exact FF565| clear; lia| rewrite zsize_c8; clear; lia|].
    rewrite zsize_c8. intros a Ha. cbn [outside]. clear - Ha DNF DMF DTF HM0 HM1. repeat split; lia. }
  assert (FRB6 : rw_cells bsegs m6 (SPV + -104) (RFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_transport; [| exact MU6| exact WM6| apply DW6s; clear - SPAB BOT LO ATR; lia].
    eapply rw_cells_transport; [exact FRB5| exact MU7| exact WM7|]. unfold RFRB. cbn [cells_size csize Nat.add]. apply DS7; clear - SPAB; lia. }
  assert (FRA6 : rw_cells bsegs m6 (SPAz SPV) [CB 48 j48; C8 (Z_to_bv 64 FF)]).
  { eapply rw_cells_transport; [| exact MU6| exact WM6| apply DW6s; clear - SPAB BOT LO ATR; lia].
    eapply rw_cells_transport; [exact FRA5| exact MU7| exact WM7|]. cbn [cells_size csize Nat.add]. apply DS7; clear - SPAB; lia. }
  assert (STG6 : stk bsegs m6 (SPAz SPV + 56) (SPV + -104)).
  { eapply stk_transport; [| exact MU6| exact WM6| intros x Hx; left; cbn [outside]; clear - Hx SPAB BOT LO BSF ATR; lia].
    eapply stk_transport; [exact STG5| exact MU7| exact WM7|]. intros x Hx.
    pose proof (DS7 x 1 ltac:(clear - Hx; lia) ltac:(clear - Hx; lia) ltac:(clear; lia)) as D. left.
    clear - D. cbn [disjoint_from outside fake_area app] in *. repeat split; lia. }
  assert (STL6 : stk bsegs m6 lo (SPAz SPV)).
  { eapply stk_transport; [exact ST7| exact MU6| exact WM6| intros x Hx; left; cbn [outside]; clear - Hx BOT BSF ATR; lia]. }
  assert (LNC' : Z.of_nat (length (u16s (map (Z_to_bv 64) rt'))) = 2 * zlen rt0) by (rewrite u16s_length, length_map, LRT; clear; lia).
  assert (ARR6 : u8arr bsegs m6 NC (u16s (map (Z_to_bv 64) rt'))) by (eapply u8arr_transport; [exact ARR7| exact MU6| exact WM6| rewrite LNC'; apply DW6; exact DBN]).
  assert (HMSV6 : rw_cells bsegs m6 MSVP [C4 msvw]) by (eapply rw_cells_transport; [exact HMSV7| exact MU6| exact WM6| rewrite zsize_c4; apply DW6; exact DBM]).
  assert (HTL6 : rw_cells bsegs m6 TLP [C4 tlw]) by (eapply rw_cells_transport; [exact HTL7| exact MU6| exact WM6| rewrite zsize_c4; apply DW6; exact DBT]).
  (* [comment removed for export] *)
  assert (MU06 : munch ([(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4); (SPV - 4512, SPV)] ++ fake_area L) m m6).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU03]; intros x Hx; cbn [outside app fake_area] in *; clear - Hx; lia|].
    eapply munch_trans.
    { eapply munch_weaken; [| exact MU5]. subst W5. intros x Hx. cbn [outside app fake_area] in *.
      rewrite ?shad_div in *. rewrite ?Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. unfold FAKESZ, ASHOFF in *.
      clear - Hx FFA1 FFA2 SPAB F64. Z.div_mod_to_equations. lia. }
    eapply munch_trans.
    { eapply munch_weaken; [| exact MU7]. intros x Hx. cbn [outside app fake_area] in *. clear - Hx SPAB. lia. }
    eapply munch_weaken; [| exact MU6]. intros x Hx. cbn [outside app fake_area] in *.
    rewrite ?shad_div in *. rewrite ?Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. unfold FAKESZ, ASHOFF in *.
    clear - Hx FFA1 FFA2 F64. Z.div_mod_to_equations. lia. }
  assert (WM06 : wmono bsegs m m6) by (eapply wmono_trans; [exact WM03| eapply wmono_trans; [exact WM5| eapply wmono_trans; [exact WM7| exact WM6]]]).
  (* [comment removed for export] *)
  assert (FFR06 : ffr_pres [(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4)] LB m m6).
  { eapply ffr_pres_trans.
    { apply ffr_pres_mono_nil.
      eapply (fk_ffr_fin AI L RNG st LB m m3 m5 0 FF 64 (shad FF) 5 [] [(SPAz SPV - 2224, SPAz SPV); (FF + 24, FF + 56)]);
        [exact AH3| exact LBH| exact FH| clear - F64; Z.div_mod_to_equations; lia| reflexivity| clear; lia| clear; lia| | constructor| exact FFR03| | exact WM5].
      - constructor; [cbn [fst snd]; split; [clear; lia| left; clear - SPAB LO BOT SPK ATR; unfold KEND in *; lia]|].
        constructor; [cbn [fst snd]; split; [clear; lia| right; split; [intros b Hb; destruct (FFD b Hb); lia| exists FF, (FF + 64); split; [exact FH| clear; lia]]]| constructor].
      - eapply munch_weaken; [| exact MU5]. subst W5. intros x Hx. cbn [outside app] in *. rewrite ?shad_div in *.
        rewrite ?Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. unfold ASHOFF in *. clear - Hx. lia. }
    eapply ffr_pres_trans; [eapply ffr_pres_tail; exact FFR7|].
    eapply (fk_ffr_fin AI L RNG st LB m7 m7 m6 0 FF 64 (shad FF) 5 [(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4)] []);
      [exact AH7| exact LBH| exact FH| clear - F64; Z.div_mod_to_equations; lia| reflexivity| clear; lia| clear; lia| constructor| | apply ffr_pres_refl| | exact WM6].
    - constructor; [split; [exists NC, (NC + 2 * zlen rt0); split; [exact BN| cbn; clear; lia]| cbn; clear - HM1 HM0; lia]|].
      constructor; [split; [exists MSVP, (MSVP + 4); split; [exact BM| cbn; clear; lia]| cbn; clear; lia]|].
      constructor; [split; [exists TLP, (TLP + 4); split; [exact BT| cbn; clear; lia]| cbn; clear; lia]| constructor].
    - eapply munch_weaken; [| exact MU6]. intros x Hx. cbn [outside app] in *. rewrite ?shad_div in *.
      rewrite ?Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. unfold ASHOFF in *. clear - Hx. lia. }
  (* [comment removed for export] *)
  eapply (rd_closeZ 4512 L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m6 SPV NC MSVP TLP lo FF r' msv0 rt0 buf rt' msvw tlw
            (Z_to_bv 64 0x41b58ab3) [CB 48 j48; C8 (Z_to_bv 64 FF)]);
    first [exact AH6| exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact FFA1| exact FFA2| exact MU06| exact WM06| exact MI6| exact FFR06
          | exact SHF6| exact FF06| exact FF566| exact FRB6| exact FRA6| exact STL6| exact STG6| exact BOT| exact SPT| exact SP16| exact RSTK
          | exact INN| exact INM| exact INT| exact NHI| exact MHI| exact THI| exact ARR6| exact LRT| exact HMSV6| exact HTL6
          | lazymatch goal with |- lo <= SPV - 4304 => clear - LO; lia end
          | lazymatch goal with |- 0 <= r' < 2 ^ 64 => clear - Hr Hr'; lia end
          | lazymatch goal with |- cells_size _ = _ => reflexivity end
          | idtac].
  (* [comment removed for export] *)
  unfold read_ncount. unfold FseNCount.Zlength. fold hb. replace (hb <? 8) with true by (symmetry; apply Z.ltb_lt; clear - HB8; subst hb; lia). fold buf'.
  destruct (Z.lt_ge_cases r (2^64 - 119)) as [HR|HR].
  - destruct (RSZ HR) as (rt & msv & tl & n & E & -> & N8 & -> & -> & ->). rewrite E. cbn [bind].
    destruct (Z.ltb_spec hb n) as [LT|GE].
    + right. exists ZSTD_error_corruption_detected. split; [reflexivity|]. unfold ZSTD_error_corruption_detected. clear - Hr' HR LT. lia.
    + left. exists rt, msv, tl, n. split; [reflexivity|]. split; [clear - Hr' GE; lia| repeat split; reflexivity].
  - destruct (RER HR) as (e & E & ->). rewrite E. cbn [bind]. right. exists e. split; [reflexivity| clear - Hr' HR; lia].
Qed.

Lemma rdZ_post_monoSW : forall SW SW' L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 buf msv0 lo m ms,
  rdZ_post SW L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 buf msv0 lo m ms -> SW <= SW' ->
  rdZ_post SW' L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 buf msv0 lo m ms.
Proof.
  intros until ms. intros H HSW. unfold rdZ_post in H |- *.
  destruct H as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & r & rt' & msvw & tlw & E & MU & REST).
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', r, rt', msvw, tlw. split; [exact E|]. split; [| exact REST].
  eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside app fake_area] in *. clear - Hx HSW. lia.
Qed.

(* [comment removed for export] *)
Theorem fse_read_any_proofA : fse_read_any_stmtA AI rng_fs.
Proof.
  unfold fse_read_any_stmtA.
  intros L RNG st LB ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV NC MSVP TLP BUF rt0 buf msv0 lo tl0
         AFP TP AN INN HULL AM INM AT INT AB HULLB INB MI ARR HMSV HTL HBUF FB HM0 HM1 HRT HBL
         N0 NHI N2 M0 MHI M4 T0 THI T4 B0 BHI ST LO0 LO SNS SMS STS SBS S1 S2 S3 S4 S5 S6 -> -> -> -> ->.
  destruct AFP as (AH & ASH & ART & (KLO & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTK2 & LBH).
  pose proof (ashort_fake_le LB 2 0 ASH ltac:(clear; lia)) as FLE. change (Z.to_nat (4096 - 2)) with 4094%nat in FLE.
  (* [comment removed for export] *)
  destruct (AN ltac:(clear - HM0 HM1; lia)) as (BN & UN & RN & RNS). destruct (AM ltac:(clear; lia)) as (BM & UM & RM & RMS).
  destruct (AT ltac:(clear; lia)) as (BT & UT & RT & RTS). destruct AB as (BB & UB & RB & RBS).
  rewrite (shspan_4 MSVP M4) in RMS. rewrite (shspan_4 TLP T4) in RTS.
  assert (LBS : zlen (map (Z_to_bv 8) buf) = zlen buf) by (rewrite length_map; reflexivity).
  assert (LNC : Z.of_nat (length (u16s (map (Z_to_bv 64) rt0))) = 2 * zlen rt0) by (rewrite u16s_length, length_map; clear; lia).
  eapply evtF_mono; [| intros ms' H; eapply (rdZ_post_iface 4512); [exact H| clear; lia]].
  eapply evtF_cut; [| intros ms' H; exact H].
  unfold APFSE_READ_BODY. change 0xaaac0 with AFSE_RD_BODY.
  eapply (rd_openZ 4094%nat L RNG st LB ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV NC MSVP TLP BUF (zlen buf) lo
            (u16s (map (Z_to_bv 64) rt0)) (map (Z_to_bv 8) buf) (Z_to_bv 64 msv0) tl0
            (fun ms => evtF bsegs RNG (rdZ_post 4512 L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV NC MSVP TLP rt0 buf msv0 lo m) ms));
    rewrite ?LNC, ?LBS;
    first [exact AH| exact FLE| exact LBH| exact RI| exact RSTK2| exact RFS| exact BOT| exact SPT| exact SP16| exact ST| exact MI| exact TP| exact BB
          | exact ARR| exact INN| exact UN| exact SNS| exact HMSV| exact INM| exact UM| exact M4| exact RMS| exact SMS| exact HTL| exact INT| exact UT| exact STS
          | exact HBUF| exact INB| exact UB| exact SBS
          | clear - LO; lia | clear - HBL; lia | clear - NHI; lia | clear - MHI; lia | clear - THI; lia | clear - B0; lia | clear - BHI; lia | clear; cbn; lia
          | idtac].
  cbv beta.
  intros FF m3 j48 junk x5 x6 x7 y10 y11 y13 y14 x15 x16 x17 x28 x29 x30 x31 F64 FH FC RFF RSFF FFD FFA1 FFA2 AH3 MU03 WM03 FFR03 MI3
         FRB3 FRA3 FFC3 SHF3 STL3 STG3 ARR3 UN3 HMSV3 UM3 HTL3 UT3 HBUF3 UB3.
  rewrite ?LNC, ?LBS in *.
  pose proof (ainimg_apart_frame LB BUF (zlen buf) FF FFD ltac:(pose proof (ablk_lin _ _ FH) as (X & _); exact X) INB ltac:(clear; lia)) as SEPB.
  destruct (Z.ltb_spec 7 (zlen buf)) as [HB8|HB8].
  - (* [comment removed for export] *)
    eapply evtF_mono; [| intros ms' H; eapply (rdZ_post_monoSW 4304 4512); [exact H| clear; lia]].
    eapply (rd_body8Z L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m3 SPV NC MSVP TLP BUF lo FF msv0 rt0 buf tl0 j48 junk);
      first [eassumption | clear - HB8 NHI MHI THI LO; lia | idtac].
  - (* [comment removed for export] *)
    eapply (rd_smallZ 4094%nat L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m3 SPV NC MSVP TLP BUF lo FF msv0 rt0 buf tl0 j48 junk);
      first [eassumption | clear - HB8 NHI MHI THI LO; lia | clear; cbn; lia | idtac].
Qed.

End Asm.
End CANSEC1.
