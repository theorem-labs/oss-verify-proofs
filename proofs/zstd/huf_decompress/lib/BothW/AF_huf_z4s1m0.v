From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s2_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_tbl_iface2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3b.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s1_iface AF_huf_z4s1mk.

Notation amem := (word -> option byte).
Notation Zw z := (Z_to_bv 64 z) (only parsing).

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_bitd AF_huf_z4d_iface AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_x4s04.
Section CANSEC1. Context {rc : runConstT}.

Section Z4S1M0.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
            (SBL SBH : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis NFK : forall F k, ~ In (mkABlock (ABFake 0) F k) LB.
  Hypothesis ABL : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis DSTF : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis NSM : n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis SRCB : 0 < n -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= SS /\ SS + n <= SBH.
  Hypothesis DJ1 : DT + DTL <= SS \/ SS + n <= DT.
  Hypothesis DJ2 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis DJ3 : DT + DTL <= DST \/ DST + dcap <= DT.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TPA : tp = Z_to_bv 64 ATP.
  Hypothesis HINV : harness_invA m0.
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : SP <= r_hi rstk.
  Hypothesis RRL : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WIS : rng_aimg_sh RNG.
  Hypothesis WFS : rng_fs L RNG.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation Z4SF' := (Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs).
  Notation ZS pc m r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 :=
    (MS (mkR r1 (Z_to_bv 64 (SP + -384)) gp tp r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
             r26 r27 r28 r29 r30 r31) FR (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

  Ltac atstop := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
    let b := eval vm_compute in (orb (orb (p =? ABIT_INIT_D) (p =? AZ4_DEPI)) (orb (p =? AZ4_D + 704) (p =? AZ4_C0))) in
    lazymatch b with true => idtac end end.
  Ltac w4run := repeat (tryif atstop then fail else
    lazymatch goal with |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail | _ => zstep end).

  Lemma z4c_lay : al_top L <= 2^47 /\ ATOP + 4096 <= lo /\ lo <= SP - 4096 /\ SP + 16 < al_top L.
  Proof using AH LOA LOS SPT. pose proof (AI_layout AI _ _ _ _ _ AH) as LY. clear - LY LOS LOA SPT. lia. Qed.

  Lemma z4c_d0 : 0 <= DST /\ DST + dcap <= ATOP.
  Proof using All.
    pose proof (@ATOP_lo rc) as HA.
    destruct DSTF as [[-> ->]|(pb & HB)]; [lia|].
    pose proof (AI_block AI L RNG st LB m0 pb DST dcap AH HB) as (D1 & (C2 & C3 & C4 & C5) & _).
    unfold ablk, AIMG_HI, KLS in C2. lia.
  Qed.

  Lemma z4c_appW : appW DW.
  Proof using All.
    pose proof (@ATOP_lo rc) as HA. pose proof z4c_lay as LY.
    unfold appW, KLOW, KHIGH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    - lia.
    - destruct DSTF as [[-> ->]|(pb & HB)]; [lia|].
      pose proof (AI_block AI L RNG st LB m0 pb DST dcap AH HB) as (D1 & (C2 & C3 & C4 & C5) & _).
      unfold ablk, AIMG_HI, KLS in C2. lia.
  Qed.

  Lemma z4c_aheap : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> AHEAP AI L RNG st LB mm.
  Proof using All.
    intros mm MU WM. pose proof z4c_lay as LY. pose proof (@ATOP_lo rc) as HA.
    destruct DSTF as [[E1 E2] | [pb HBo]].
    - eapply (AI_frame AI _ _ _ _ m0 mm [(lo, SP)]); [exact AH | eapply munch_weaken; [|exact MU] | exact WM |].
      + intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [exact Hx | split; [lia | exact I]].
      + apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; unfold aclient_range, aclient_app_range.
        left. left. lia.
    - eapply (AI_frame AI); [exact AH | exact MU | exact WM |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; unfold aclient_range, aclient_app_range.
      + left. left. lia.
      + right. left. exists (HB pb DST dcap). split; [exact HBo|]. cbn. lia.
  Qed.

  Lemma z4c_rcl : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> rclean mm rstk.
  Proof using All. intros mm MU WM. eapply rclean_transport; [exact RCL|exact MU|exact WM|exact z4c_appW]. Qed.
  Lemma z4c_art : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> artcells mm.
  Proof using All. intros mm MU WM. exact (AI_rtcells AI _ _ _ _ _ (z4c_aheap mm MU WM)). Qed.

  Lemma z4c_unpS : forall mm, munch DW m0 mm -> 0 < n -> unpoisoned mm SS (SS + n).
  Proof using All.
    intros mm MU NP. destruct (SRCB NP) as (p & HS & L1 & L2).
    pose proof (fun p A n H => hb_unpoisoned AI L RNG st LB m0 p A n AH H) as HU.
    destruct (HU _ _ _ HS) as (U & _ & N1 & AB & _).
    apply (unpoisoned_sub mm SBL (SBL + (SBH - SBL))); [|exact L1|lia].
    eapply unpoisoned_appW; [exact U|exact MU|exact z4c_appW|lia|].
    pose proof (ablk_lin _ _ AB) as A. lia.
  Qed.

  Lemma z4c_shar : forall a l b h, b mod 16 = 0 -> b <= a -> 0 <= l -> a + l <= h ->
    shad a + nshad (l + a mod 8) <= shad b + shlen (h - b + 7).
  Proof.
    intros a l b h B16 BA L0 AHh. rewrite !shad_div, nshad_div. unfold shlen. rewrite Z.shiftr_div_pow2 by lia.
    change (2^3) with 8. Z.div_mod_to_equations. lia.
  Qed.

  Lemma z4c_sh5 : forall A, A mod 8 = 0 -> shad (A + 40 - 1) + 1 - shad A = 5.
  Proof. intros A HA. rewrite !shad_div. Z.div_mod_to_equations. lia. Qed.

  Lemma z4c_m64 : forall x, x mod 64 = 0 -> x mod 8 = 0.
  Proof. intros x HX. Z.div_mod_to_equations. lia. Qed.

  Lemma z4c_rng : forall o len, 0 <= o -> 0 <= len -> o + len <= n -> 0 < n ->
    ablk (SS + o) (SS + o + len) /\ SS + o + 8 <= 2^47 /\ rng RNG (SS + o) len /\
    rng RNG (shad (SS + o)) (nshad (len + (SS + o) mod 8)).
  Proof using All.
    intros o len O1 O2 O3 NP. destruct (SRCB NP) as (p & HS & L1 & L2).
    pose proof (fun p A n H => hb_unpoisoned AI L RNG st LB m0 p A n AH H) as HU.
    destruct (HU _ _ _ HS) as (_ & A16 & N1 & AB & AT & R1 & R2 & _).
    pose proof (ablk_lin _ _ AB) as A.
    split; [eapply ablk_sub; [exact AB|lia|lia]|]. split; [lia|]. split; [eapply rng_sub; [exact R1|lia|lia]|].
    eapply rng_sub; [exact R2| |].
    - unfold shad. rewrite !Z.shiftr_div_pow2 by lia. apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
    - apply z4c_shar; lia.
  Qed.

  Lemma z4c_call : forall (Q : machine_state -> Prop) mm (A o len : Z) (j : list byte)
      (xra t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    6 <= dcap -> 0 < n -> munch DW m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm lo (SP + -384) -> rw_cells bsegs mm A [CB 40 j] ->
    SP + -384 <= A -> A + 40 <= SP + -104 -> A mod 8 = 0 ->
    bytes_at bsegs mm SS (map (Z_to_bv 8) src) -> 0 <= o -> 0 <= len -> o + len <= n ->
    x10 = Z_to_bv 64 A -> x11 = Z_to_bv 64 (SS + o) -> x12 = Z_to_bv 64 len ->
    (forall m' (ret : Z) (u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 : word),
       munch [(SP + -384 - ABIT_INIT_STACK, SP + -384); (A, A + 40)] mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' ->
       stk bsegs m' lo (SP + -384) ->
       match init_dstream (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) with
       | Ok d => ret = len /\ bd_zero d = false /\ exists jp, rw_cells bsegs m' A (bitdz_cellsA (SS + o) d jp)
       | Err e => ret = - e /\ exists j', rw_cells bsegs m' A [CB 40 j']
       | Ub | NoFuel => False
       end ->
       evtF bsegs RNG Q (MS (mkR xra (Z_to_bv 64 (SP + -384)) gp tp u5 u6 u7 x8 x9 (Z_to_bv 64 ret) u11 u12 u13 u14 u15 u16
                                 u17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u28 u29 u30 u31)
                            FR (ret_pc xra) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR xra (Z_to_bv 64 (SP + -384)) gp tp t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16
                              x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                         FR (Z_to_bv 64 ABIT_INIT_D) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros Q mm A o len j xra t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
      t3 t4 t5 t6 D6 NP MU WM MI STK RWA A1 A2 A3 BYT O1 O2 O3 E10 E11 E12 K.
    pose proof z4c_lay as LY. pose proof (z4c_rcl mm MU WM) as RC. pose proof (z4c_art mm MU WM) as ART.
    pose proof (z4c_unpS mm MU NP) as UNP. destruct (z4c_rng o len O1 O2 O3 NP) as (ABS & S8 & RS & RSS).
    pose proof bit_init_proofAD as BI. unfold bit_init_stmtA in BI.
    assert (LENB : zlen (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) = len).
    { rewrite firstn_length, skipn_length. lia. }
    pose proof (rclean_shclean _ _ RC) as SHC. pose proof (shclean_hull _ _ _ _ _ SHC) as HU.
    eapply evtF_cut.
    - eapply (BI RNG xra (Z_to_bv 64 (SP + -384))) with (D := A) (S := SS + o)
        (bs := firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) (j := j) (lo := lo) (RLO := r_rlo rstk) (RHI := r_rhi rstk).
      + exact RWA.
      + exact A3.
      + rewrite <- (firstn_skipn (Z.to_nat o) src), map_app in BYT. apply bytes_at_app in BYT. destruct BYT as [_ BYT].
        rewrite map_length, firstn_length_le, Z2Nat.id in BYT by lia.
        rewrite <- (firstn_skipn (Z.to_nat len) (skipn (Z.to_nat o) src)), map_app in BYT.
        apply bytes_at_app in BYT. exact (proj1 BYT).
      + apply Forall_take, Forall_drop, BYS.
      + rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; lia.
      + lia.
      + intros _. rewrite LENB. exact (conj ABS S8).
      + rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; exact STK.
      + exact LOA.
      + rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; unfold ABIT_INIT_STACK; lia.
      + exact MI.
      + exact ART.
      + eapply shclean_sub; [exact SHC|lia|lia|lia].
      + rewrite LENB. eapply unpoisoned_sub; [exact UNP|lia|lia].
      + eapply rng_sub; [exact WSK|lia|lia].
      + destruct HU as (U1 & U2 & U3 & U4 & U5 & _). rewrite <- (z4c_sh5 A A3).
        apply (rng_shad_sub RNG (r_rlo rstk) (r_rhi rstk)); [exact RRS|lia|lia|lia|exact U5|apply z4c_m64, U4].
      + intros _. rewrite LENB. exact (conj RS RSS).
      + rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia. eapply rng_sub; [exact WSK|lia|lia].
      + exact RRS.
      + exact WIM.
      + exact E10.
      + exact E11.
      + rewrite LENB. exact E12.
    - intros ms' (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & ret & m' & EQ & MU' & WM' & MI' & STK' & BY' & RES).
      subst ms'. rewrite Z_to_bv_unsigned in MU', STK'. unfold bv_wrap, bv_modulus in MU', STK'.
      rewrite Z.mod_small in MU', STK' by lia.
      rewrite LENB in RES. apply K; [exact MU'|exact WM'|exact MI'|exact STK'|exact RES].
  Qed.

  Notation BIW A := [(SP + -384 - ABIT_INIT_STACK, SP + -384); (A, A + 40)].

  Lemma z4c_keep : forall mm m' A B bd, rw_cells bsegs mm B bd ->
      munch (BIW A) mm m' -> wmono bsegs mm m' -> SP + -384 <= B -> (B + Z.of_nat (cells_size bd) <= A \/ A + 40 <= B) ->
      rw_cells bsegs m' B bd.
  Proof.
    intros mm m' A B bd RW MU WM B1 B2.
    eapply rw_cells_transport; [exact RW|exact MU|exact WM|]. cbn [disjoint_from]. unfold ABIT_INIT_STACK. lia.
  Qed.

  Lemma z4c_far : 0 < n -> SS + n <= ATOP /\ DT + 4 + zlen cbs <= ATOP /\ DST + dcap <= ATOP /\ 0 <= SS /\ 0 <= DT.
  Proof using All.
    intros NZ0.
    destruct (SRCB NZ0) as (psb & HSB & SB1 & SB2).
    pose proof (ablk_lin _ _ (ABL _ HSB)) as AA. cbn [ab_addr ab_size] in AA.
    pose proof (ablk_lin _ _ (ABL _ HDT)) as HTL. cbn [ab_addr ab_size] in HTL.
    pose proof z4c_d0 as (DA & DB).
    rewrite LCB. cbv [DTABLE_BYTES HufHarness.DT_BYTES] in HTL.
    assert (P2 : 2 ^ tl <= 2 ^ mtl).
    { destruct (Z_lt_le_dec tl 0) as [Hn|Hn].
      - rewrite (Z.pow_neg_r 2 tl Hn). pose proof (Z.pow_pos_nonneg 2 mtl ltac:(lia) ltac:(lia)). lia.
      - apply Z.pow_le_mono_r; lia. }
    lia.
  Qed.

  Lemma z4c_rebuild : forall mm m' A spl bd4 bd3 bd2 bd1 bd4' bd3' bd2' bd1',
      0 < n -> SP + -264 <= A -> A + 40 <= SP + -104 ->
      Z4SF' mm spl bd4 bd3 bd2 bd1 ->
      munch (BIW A) mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' -> stk bsegs m' lo (SP + -384) ->
      rw_cells bsegs m' (SP + -264) bd4' -> cells_size bd4' = 40%nat ->
      rw_cells bsegs m' (SP + -224) bd3' -> cells_size bd3' = 40%nat ->
      rw_cells bsegs m' (SP + -184) bd2' -> cells_size bd2' = 40%nat ->
      rw_cells bsegs m' (SP + -144) bd1' -> cells_size bd1' = 40%nat ->
      Z4SF' m' spl bd4' bd3' bd2' bd1'.
  Proof using All.
    intros mm m' A spl bd4 bd3 bd2 bd1 bd4' bd3' bd2' bd1' NZ0 A1 A2 WF MU' WM' MI' STK' N4 N4S N3 N3S N2 N2S N1 N1S.
    pose proof z4c_lay as LY. unfold ABIT_INIT_STACK in *.
    destruct (z4c_far NZ0) as (FA1 & FA2 & FA3 & FA4 & FA5).
    destruct WF as (BUF & BSS & BDT4 & BDT & STK & FRC & FRCS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
    unfold Z4SF.
    destruct BUF as (buf & BU & BL).
    split; [exists buf; split; [eapply u8arr_transport; [exact BU | exact MU' | exact WM' |] | exact BL] |].
    { rewrite length_map, BL. cbn [disjoint_from]. lia. }
    split; [eapply bytes_at_transport; [exact BSS | exact MU' |]; rewrite length_map; cbn [disjoint_from]; lia |].
    split; [eapply bytes_at_transport; [exact BDT4 | exact MU' |]; cbn [disjoint_from]; lia |].
    split; [eapply bytes_at_transport; [exact BDT | exact MU' |]; cbn [disjoint_from length]; lia |].
    split; [exact STK' |].
    split; [eapply rw_cells_transport; [exact FRC | exact MU' | exact WM' |]; rewrite FRCS; cbn [disjoint_from]; lia |].
    split; [exact FRCS |].
    split; [exact N4 |]. split; [exact N4S |]. split; [exact N3 |]. split; [exact N3S |].
    split; [exact N2 |]. split; [exact N2S |]. split; [exact N1 |]. split; [exact N1S |].
    split; [eapply rw_cells_transport; [exact FRM | exact MU' | exact WM' |]; cbn [disjoint_from cells_size csize]; lia |].
    split; [exact MI' |].
    split.
    - eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU']].
      intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia.
    - eapply wmono_trans; [exact WM | exact WM'].
  Qed.

  Lemma z4c_neg : forall e, Z_to_bv 64 (- e) = Z_to_bv 64 (2^64 - e).
  Proof.
    intros e. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    replace (2^64 - e) with (- e + 1 * 2 ^ Z.of_N 64) by (cbn; lia). rewrite Z.mod_add by (cbn; lia). reflexivity.
  Qed.

  Lemma z4c_cl : forall (Q : machine_state -> Prop) mm (A o len R : Z) j spl bd4 bd3 bd2 bd1
      (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word),
    6 <= dcap -> 0 < n -> Z4SF' mm spl bd4 bd3 bd2 bd1 -> rw_cells bsegs mm A [CB 40 j] ->
    SP + -264 <= A -> A + 40 <= SP + -104 -> A mod 8 = 0 -> 0 <= o -> 0 <= len -> o + len <= n ->
    r1 = Z_to_bv 64 R -> 0 <= R < 2^64 -> R mod 2 = 0 ->
    r10 = Z_to_bv 64 A -> r11 = Z_to_bv 64 (SS + o) -> r12 = Z_to_bv 64 len ->
    (forall m' d jp (u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 : word),
       init_dstream (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) = Ok d -> bd_zero d = false ->
       munch (BIW A) mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' -> stk bsegs m' lo (SP + -384) ->
       rw_cells bsegs m' A (bitdz_cellsA (SS + o) d jp) ->
       evtF bsegs RNG Q (ZS R m' r1 u5 u6 u7 r8 r9 (Z_to_bv 64 len) u11 u12 u13 u14 u15 u16 u17 r18 r19 r20 r21 r22 r23
                           r24 r25 r26 r27 u28 u29 u30 u31)) ->
    (forall m' e j' (u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 : word),
       init_dstream (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) = Err e ->
       munch (BIW A) mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' -> stk bsegs m' lo (SP + -384) ->
       rw_cells bsegs m' A [CB 40 j'] ->
       evtF bsegs RNG Q (ZS R m' r1 u5 u6 u7 r8 r9 (Z_to_bv 64 (2^64 - e)) u11 u12 u13 u14 u15 u16 u17 r18 r19 r20 r21
                           r22 r23 r24 r25 r26 r27 u28 u29 u30 u31)) ->
    evtF bsegs RNG Q (ZS ABIT_INIT_D mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
                         r27 r28 r29 r30 r31).
  Proof using All.
    intros Q mm A o len R j spl bd4 bd3 bd2 bd1 r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
      r24 r25 r26 r27 r28 r29 r30 r31 D6 NP WF RWA A1 A2 A3 O1 O2 O3 E1 R1 R2 E10 E11 E12 KO KE.
    destruct WF as (BUF & BSS & BDT4 & BDT & STK & FRC & FRCS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
    eapply (z4c_call Q mm A o len j); try eassumption; try lia.
    intros m' ret u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 MU' WM' MI' STK' RES.
    subst r1. rewrite (ret_pc_even R R1 R2).
    destruct (init_dstream _) as [d|e| |] eqn:EQ; try contradiction.
    - destruct RES as (-> & BZ & jp & RW). eapply KO; [reflexivity|exact BZ|exact MU'|exact WM'|exact MI'|exact STK'|exact RW].
    - destruct RES as (-> & j' & RW). rewrite z4c_neg. eapply KE; [reflexivity|exact MU'|exact WM'|exact MI'|exact STK'|exact RW].
  Qed.

  Lemma z4c_bslen : forall o len, 0 <= o -> 0 <= len -> o + len <= n ->
    zlen (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) = len.
  Proof. intros o len O1 O2 O3. rewrite firstn_length, skipn_length. lia. Qed.

  Lemma z4c_bsbytes : forall o len, Forall (fun c => 0 <= c < 256) (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)).
  Proof using All. intros o len. apply Forall_take, Forall_drop, BYS. Qed.

  Lemma z4c_hinv : forall o len d, 0 <= o -> 0 <= len -> o + len <= n ->
    init_dstream (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) = Ok d ->
    z4H len (bd_ptr d) (bd_bits d) /\ 1 <= len /\ 0 <= bd_bits d <= 64.
  Proof using All.
    intros o len d O1 O2 O3 ID.
    pose proof (init_dstream_shape _ _ (z4c_bsbytes o len) ID) as SH. rewrite (z4c_bslen o len O1 O2 O3) in SH.
    unfold z4H. lia.
  Qed.

  Lemma z4c_eerr : forall o len e, init_dstream (firstn (Z.to_nat len) (skipn (Z.to_nat o) src)) = Err e -> 1 <= e <= 119.
  Proof using All. intros o len e ID. exact (init_dstream_err_range _ _ (z4c_bsbytes o len) ID). Qed.

  Lemma z4c_bd : forall S d jp, bd_zero d = false ->
    bitdz_cellsA S d jp = BD4A (Z_to_bv 64 (bd_cont d)) (Z_to_bv 64 (bd_bits d)) jp (Z_to_bv 64 (S + bd_ptr d))
                               (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)).
  Proof. intros S d jp BZ. unfold bitdz_cellsA, BD4A. rewrite BZ. reflexivity. Qed.

  Notation Zw z := (Z_to_bv 64 z) (only parsing).
  Notation BDS k b jp O o := (BD4A k (Zw b) jp (Zw (SS + O + o)) (Zw (SS + O)) (Zw (SS + O + 8))) (only parsing).

  Lemma z4c_sx32 : forall e, 0 <= e < 2^31 -> Mem.sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
  Proof.
    intros e He. unfold Mem.sx32. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with 18446744073709551616. rewrite Z.mod_small by lia.
    unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
    rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma z4c_x7 : forall d, 0 <= d + 4 < 2^64 ->
    Z_to_bv 64 (Z.lxor (d + 4) 18446744073709551615) = Z_to_bv 64 (- d - 5).
  Proof.
    intros d Hd. rewrite zb_lxor_ones by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with 18446744073709551616.
    replace (- d - 5) with (18446744073709551615 - (d + 4) + (-1) * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  Qed.

  Lemma z4c_x6 : forall t m, 1 <= t <= 12 -> 0 <= m <= 255 ->
    Z_to_bv 64 (Z.land (Z.land (bv_swrap 32 (0 - Z.land (t + 256 * m) 18446744073709551615)) 18446744073709551615) 63)
    = Z_to_bv 64 (64 - t).
  Proof.
    intros t m T M. f_equal.
    pose proof (neg_desc_shift2 t m T M) as N.
    change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by lia.
    change (2 ^ 64) with 18446744073709551616. exact N.
  Qed.

  Lemma z4c_x6b : forall t m, 1 <= t <= 12 -> 0 <= m <= 255 ->
    Z_to_bv 64 (Z.land (Z.land (bv_swrap 32 (0 - (t + 256 * m))) 18446744073709551615) 63) = Z_to_bv 64 (64 - t).
  Proof.
    intros t m T M. f_equal.
    pose proof (neg_desc_shift2 t m T M) as N.
    change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
    change (2 ^ 64) with 18446744073709551616.
    rewrite (Z.mod_small (t + 256 * m) 18446744073709551616) in N by lia. exact N.
  Qed.

  Lemma z4c_strm : forall Lk o b, z4H Lk o b -> z4strm Lk o b.
  Proof. intros Lk o b H. unfold z4H, z4strm in *. lia. Qed.

  Lemma z4c_ops : z1ops seg 0 seg (2 * seg) (3 * seg).
  Proof using All. unfold z1ops. Z.div_mod_to_equations. lia. Qed.

  Lemma z4c_loop : forall (Q : machine_state -> Prop) mm (l1 l2 l3 o1 o2 o3 o4 b1 b2 b3 b4 : Z) (k1 k2 k3 k4 : word)
      (jp1 jp2 jp3 jp4 : list byte) (w0 w4 w5 w7 a1 a2 a3 a6 a8 a9 a10 a11 a12 a13 a14 : word)
      (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word),
    z4I_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q ->
    z4s2_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q ->
    z4R_epi RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q ->
    Z4SF' mm (SPD w0 a1 a2 a3 w4 w5 a6 w7 a8 a9 a10 a11 a12 a13 a14)
      (BDS k4 b4 jp4 (6 + l1 + l2 + l3) o4) (BDS k3 b3 jp3 (6 + l1 + l2) o3)
      (BDS k2 b2 jp2 (6 + l1) o2) (BDS k1 b1 jp1 6 o1) ->
    a1 = Zw (DST + 3 * seg) -> a2 = Zw (tl + 256 * mtl) -> a3 = Zw (DST + dcap - 7) -> a6 = Zw (DST + dcap) ->
    a8 = k2 -> a9 = Zw (DST + seg) -> a10 = Zw (DST + 2 * seg) -> a11 = k4 -> a12 = k3 -> a13 = Zw (DT + 4) -> a14 = Zw dcap ->
    1 <= l1 -> 1 <= l2 -> 1 <= l3 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg + 8 <= dcap ->
    z4H l1 o1 b1 -> z4H l2 o2 b2 -> z4H l3 o3 b3 -> z4H (n - (6 + l1 + l2 + l3)) o4 b4 ->
    r1 = Zw b2 -> r5 = Zw (2^61) -> r6 = Zw (64 - tl) -> r7 = Zw (- DT - 5) -> r9 = Zw (DST + 3 * seg) -> r12 = Zw DST ->
    r14 = Zw (SS + 6 + o1) -> r15 = Zw (SS + 6 + l1 + o2) -> r16 = Zw (SS + 6 + l1 + l2 + o3) ->
    r18 = Zw (DST + 2 * seg) -> r19 = Zw (DST + seg) -> r20 = Zw b3 -> r21 = Zw AZ4_SB -> r23 = k1 -> r24 = Zw b4 ->
    r26 = Zw b1 -> r30 = Zw (DT + 4) -> r31 = Zw (SS + 6 + l1 + l2 + l3 + o4) ->
    evtF bsegs RNG Q (ZS (AZ4_D + 856) mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
                         r24 r25 r26 r27 r28 r29 r30 r31).
  Proof using All.
    intros Q mm l1 l2 l3 o1 o2 o3 o4 b1 b2 b3 b4 k1 k2 k3 k4 jp1 jp2 jp3 jp4 w0 w4 w5 w7 a1 a2 a3 a6 a8 a9 a10 a11 a12 a13 a14
      r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31
      ZI S2 EPR WF A1 A2 A3 A6 A8 A9 A10 A11 A12 A13 A14 L1 L2 L3 LN D6 D8 H1 H2 H3 H4.
    intros. subst a1 a2 a3 a6 a8 a9 a10 a11 a12 a13 a14 r1 r5 r6 r7 r9 r12 r14 r15 r16 r18 r19 r20 r21 r23 r24 r26 r30 r31.
    pose proof (ZI S2 EPR mm l1 l2 l3 0 seg (2 * seg) (3 * seg) o1 o2 o3 o4 b1 b2 b3 b4 k1 k2 k3 k4 jp1 jp2 jp3 jp4
                  w0 w4 w5 w7 r8 r10 r11 r13 r17 r22 r25 r27 r28 r29 WF L1 L2 L3 LN D6 ltac:(lia) H1 H2 H3 H4 z4c_ops D8) as G.
    rewrite Z.add_0_r in G. exact G.
  Qed.

  Lemma z4c_s2 : forall (Q : machine_state -> Prop) mm (l1 l2 l3 o1 o2 o3 o4 b1 b2 b3 b4 : Z) (k1 k2 k3 k4 : word)
      (jp1 jp2 jp3 jp4 : list byte) (w0 w4 w5 w7 a1 a2 a3 a6 a8 a9 a10 a11 a12 a13 a14 : word)
      (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word),
    z4s2_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q ->
    z4R_epi RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q ->
    Z4SF' mm (SPD w0 a1 a2 a3 w4 w5 a6 w7 a8 a9 a10 a11 a12 a13 a14)
      (BDS k4 b4 jp4 (6 + l1 + l2 + l3) o4) (BDS k3 b3 jp3 (6 + l1 + l2) o3)
      (BDS k2 b2 jp2 (6 + l1) o2) (BDS k1 b1 jp1 6 o1) ->
    a1 = Zw (DST + 3 * seg) -> a2 = Zw (tl + 256 * mtl) -> a3 = Zw (DST + dcap - 7) -> a6 = Zw (DST + dcap) ->
    a9 = Zw (DST + seg) -> a10 = Zw (DST + 2 * seg) -> a13 = Zw (DT + 4) -> a14 = Zw dcap ->
    1 <= l1 -> 1 <= l2 -> 1 <= l3 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg <= dcap ->
    z4H l1 o1 b1 -> z4H l2 o2 b2 -> z4H l3 o3 b3 -> z4H (n - (6 + l1 + l2 + l3)) o4 b4 ->
    r9 = Zw (DST + 3 * seg) -> r12 = Zw DST -> r17 = Zw (DST + seg) -> r18 = Zw (DST + 2 * seg) -> r19 = Zw (DST + seg) ->
    r21 = Zw AZ4_SB -> r30 = Zw (DT + 4) ->
    evtF bsegs RNG Q (ZS AZ4_C0 mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
                         r24 r25 r26 r27 r28 r29 r30 r31).
  Proof using All.
    intros Q mm l1 l2 l3 o1 o2 o3 o4 b1 b2 b3 b4 k1 k2 k3 k4 jp1 jp2 jp3 jp4 w0 w4 w5 w7 a1 a2 a3 a6 a8 a9 a10 a11 a12 a13 a14
      r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31
      S2 EPR WF A1 A2 A3 A6 A9 A10 A13 A14 L1 L2 L3 LN D6 D3 H1 H2 H3 H4.
    intros. subst a1 a2 a3 a6 a9 a10 a13 a14 r9 r12 r17 r18 r19 r21 r30.
    replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in WF by lia.
    replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in WF by lia.
    replace (SS + (6 + l1)) with (SS + 6 + l1) in WF by lia.
    assert (Q4 : 0 <= 3 * seg <= dcap) by (Z.div_mod_to_equations; lia).
    pose proof (S2 l1 l2 l3 0 seg (2 * seg) (3 * seg) o1 o2 o3 o4 b1 b2 b3 b4 k1 k2 k3 k4 jp1 jp2 jp3 jp4
                  w0 w4 w5 w7 a8 a11 a12 mm r1 r5 r6 r7 r8 r10 r11 r13 r14 r15 r16 r20 r22 r23 r24 r25 r26 r27 r28 r29 r31)
      as G.
    rewrite !Z.add_0_r in G.
    exact (G WF L1 L2 L3 LN D6 D3 ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) Q4
             (z4c_strm _ _ _ H1) (z4c_strm _ _ _ H2) (z4c_strm _ _ _ H3) (z4c_strm _ _ _ H4) EPR).
  Qed.

  Ltac z4eq := first [ reflexivity | f_equal; lia
                     | apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity
                     | Z.div_mod_to_equations; lia ].
  Ltac z4eq2 := first [ z4eq | rewrite z4c_sx32 by lia; reflexivity | apply z4c_x7; lia | apply z4c_x6; lia
                      | apply z4c_x6b; lia ].
  Ltac z4no K := exfalso; zify_cond K; Z.div_mod_to_equations; lia.
  Ltac z4br := lazymatch goal with |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
    let K := fresh "K" in if_cases K; [ try z4no K | try z4no K ] end.
  Ltac z4kp H MU WM N := pose proof (z4c_keep _ _ _ _ _ H MU WM) as N;
    specialize (N ltac:(lia) ltac:(cbv [bitdz_cellsA BD4A cells_size csize Nat.add app Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
  Ltac z4m8 := clear - SP16; Z.div_mod_to_equations; lia.
  Ltac atstop2 := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
    let b := eval vm_compute in (orb (p =? AZ4_D + 856) (p =? AZ4_C0)) in
    lazymatch b with true => idtac end end.
  Ltac w4run2 := repeat (tryif atstop2 then fail else
    lazymatch goal with |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail | _ => zstep end).
  Ltac z4pack := unfold Z4SF, SPD; split; [eexists; split; eassumption|];
    do 17 (split; [first [eassumption | reflexivity]|]); eassumption.

  Lemma z4m0_main : forall Q,
    z4I_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q ->
    z4i1_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  Proof using All.

    intros Q ZI. unfold z4i1_goal. intros S2 EPI mm l1 l2 l3 w0 w1 w2 w3 w4 w5 w7 w8 w11 w12 j4 j3 j2 j1
      x1 x5 x6 x7 x10 x12 x13 x14 x16 x17 x24 x27 x28 x29 x30 x31 WF L1 L2 L3 LN D6 N10.
    unfold z4epi_hyp in EPI.
    pose proof z4c_lay as LY.
    pose proof WF as WF0.
    destruct WF0 as (_ & _ & _ & _ & _ & _ & _ & B4 & _ & B3 & _ & B2 & _ & B1 & _ & _ & _ & _ & _).
    unfold AZ4_I1. w4run.
    (* [comment removed for export] *)
    eapply (z4c_cl _ mm (SP + -144) 6 l1 _ j1);
      [ lia | lia | exact WF | exact B1 | lia | lia | z4m8 | lia | lia | lia
      | reflexivity | lia | reflexivity | z4eq | z4eq | z4eq | | ].
    2: { intros m1 e1 j1' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID1 MU1 WM1 MI1 STK1 RW1.
         pose proof (z4c_eerr _ _ _ ID1) as E1.
         z4kp B4 MU1 WM1 B41. z4kp B3 MU1 WM1 B31. z4kp B2 MU1 WM1 B21.
         pose proof (z4c_rebuild mm m1 (SP + -144) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF MU1 WM1 MI1 STK1
                       B41 eq_refl B31 eq_refl B21 eq_refl RW1 eq_refl) as WF1.
         w4run. z4br. w4run. eapply EPI; exact WF1. }
    intros m1 d1 jp1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID1 BZ1 MU1 WM1 MI1 STK1 RW1.
    destruct (z4c_hinv 6 l1 d1 ltac:(lia) ltac:(lia) ltac:(lia) ID1) as (HV1 & LL1 & BB1).
    z4kp B4 MU1 WM1 B41. z4kp B3 MU1 WM1 B31. z4kp B2 MU1 WM1 B21.
    pose proof (z4c_rebuild mm m1 (SP + -144) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF MU1 WM1 MI1 STK1
                  B41 eq_refl B31 eq_refl B21 eq_refl RW1 eq_refl) as WF1.
    clear B4 B3 B2 B1 MU1 WM1 MI1 STK1 WF.
    w4run. z4br. w4run.
    (* [comment removed for export] *)
    eapply (z4c_cl _ m1 (SP + -184) (6 + l1) l2 _ j2);
      [ lia | lia | exact WF1 | exact B21 | lia | lia | z4m8 | lia | lia | lia
      | reflexivity | lia | reflexivity | z4eq | z4eq | z4eq | | ].
    2: { intros m2 e2 j2' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID2 MU2 WM2 MI2 STK2 RW2.
         pose proof (z4c_eerr _ _ _ ID2) as E2.
         z4kp B41 MU2 WM2 B42. z4kp B31 MU2 WM2 B32. z4kp RW1 MU2 WM2 C12.
         pose proof (z4c_rebuild m1 m2 (SP + -184) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF1 MU2 WM2 MI2 STK2
                       B42 eq_refl B32 eq_refl RW2 eq_refl C12 eq_refl) as WF2.
         w4run. z4br. w4run. eapply EPI; exact WF2. }
    intros m2 d2 jp2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID2 BZ2 MU2 WM2 MI2 STK2 RW2.
    destruct (z4c_hinv (6 + l1) l2 d2 ltac:(lia) ltac:(lia) ltac:(lia) ID2) as (HV2 & LL2 & BB2).
    z4kp B41 MU2 WM2 B42. z4kp B31 MU2 WM2 B32. z4kp RW1 MU2 WM2 C12.
    pose proof (z4c_rebuild m1 m2 (SP + -184) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF1 MU2 WM2 MI2 STK2
                  B42 eq_refl B32 eq_refl RW2 eq_refl C12 eq_refl) as WF2.
    clear B41 B31 B21 RW1 MU2 WM2 MI2 STK2 WF1.
    w4run. z4br. w4run.
    (* [comment removed for export] *)
    eapply (z4c_cl _ m2 (SP + -224) (6 + l1 + l2) l3 _ j3);
      [ lia | lia | exact WF2 | exact B32 | lia | lia | z4m8 | lia | lia | lia
      | reflexivity | lia | reflexivity | z4eq | z4eq | z4eq | | ].
    2: { intros m3 e3 j3' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID3 MU3 WM3 MI3 STK3 RW3.
         pose proof (z4c_eerr _ _ _ ID3) as E3.
         z4kp B42 MU3 WM3 B43. z4kp RW2 MU3 WM3 C23. z4kp C12 MU3 WM3 C13.
         pose proof (z4c_rebuild m2 m3 (SP + -224) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF2 MU3 WM3 MI3 STK3
                       B43 eq_refl RW3 eq_refl C23 eq_refl C13 eq_refl) as WF3.
         w4run. z4br. w4run. eapply EPI; exact WF3. }
    intros m3 d3 jp3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID3 BZ3 MU3 WM3 MI3 STK3 RW3.
    destruct (z4c_hinv (6 + l1 + l2) l3 d3 ltac:(lia) ltac:(lia) ltac:(lia) ID3) as (HV3 & LL3 & BB3).
    z4kp B42 MU3 WM3 B43. z4kp RW2 MU3 WM3 C23. z4kp C12 MU3 WM3 C13.
    pose proof (z4c_rebuild m2 m3 (SP + -224) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF2 MU3 WM3 MI3 STK3
                  B43 eq_refl RW3 eq_refl C23 eq_refl C13 eq_refl) as WF3.
    clear B42 B32 RW2 C12 MU3 WM3 MI3 STK3 WF2.
    w4run. z4br. w4run.
    (* [comment removed for export] *)
    eapply (z4c_cl _ m3 (SP + -264) (6 + l1 + l2 + l3) (n - (6 + l1 + l2 + l3)) _ j4);
      [ lia | lia | exact WF3 | exact B43 | lia | lia | z4m8 | lia | lia | lia
      | reflexivity | lia | reflexivity | z4eq | z4eq | z4eq | | ].
    2: { intros m4 e4 j4' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID4 MU4 WM4 MI4 STK4 RW4.
         pose proof (z4c_eerr _ _ _ ID4) as E4.
         z4kp RW3 MU4 WM4 C34. z4kp C23 MU4 WM4 C24. z4kp C13 MU4 WM4 C14.
         pose proof (z4c_rebuild m3 m4 (SP + -264) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF3 MU4 WM4 MI4 STK4
                       RW4 eq_refl C34 eq_refl C24 eq_refl C14 eq_refl) as WF4.
         w4run. z4br. w4run. eapply EPI; exact WF4. }
    intros m4 d4 jp4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ID4 BZ4 MU4 WM4 MI4 STK4 RW4.
    destruct (z4c_hinv (6 + l1 + l2 + l3) (n - (6 + l1 + l2 + l3)) d4 ltac:(lia) ltac:(lia) ltac:(lia) ID4)
      as (HV4 & LL4 & BB4).
    z4kp RW3 MU4 WM4 C34. z4kp C23 MU4 WM4 C24. z4kp C13 MU4 WM4 C14.
    pose proof (z4c_rebuild m3 m4 (SP + -264) _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) WF3 MU4 WM4 MI4 STK4
                  RW4 eq_refl C34 eq_refl C24 eq_refl C14 eq_refl) as WF4.
    clear B43 RW3 C23 C13 MU4 WM4 MI4 STK4 WF3 RW4 C34 C24 C14.
    rewrite (z4c_bd _ d1 jp1 BZ1), (z4c_bd _ d2 jp2 BZ2), (z4c_bd _ d3 jp3 BZ3), (z4c_bd _ d4 jp4 BZ4) in WF4.
    w4run. z4br. w4run.

    destruct WF4 as (BUF & BSS & BDT4 & BDT & STK & FRC & FRCS & L264 & L264S & L224 & L224S & L184 & L184S & L144 & L144S
                     & FRM & MI & MU & WM).
    destruct BUF as (buf & BU & BL).
    unfold SPD in FRC. unfold BD4A in L264, L224, L184, L144.
    destruct (z4c_far ltac:(lia)) as (FA1 & FA2 & FA3 & FA4 & FA5).
    pose proof TOK as (TL1 & _). unfold HUF_TABLELOG_MAX in TL1.
    assert (EPR : z4R_epi RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q).
    { unfold z4R_epi. intros mm' spl bd4 bd3 bd2 bd1 r z1 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22
        z23 z24 z25 z26 z27 z28 z29 z30 z31 HF _. eapply EPI; exact HF. }
    Ltac z4s2t Q l1 l2 l3 d1 d2 d3 d4 jp1 jp2 jp3 jp4 S2 EPR :=
      w4run2;
      eapply (z4c_s2 Q _ l1 l2 l3 (bd_ptr d1) (bd_ptr d2) (bd_ptr d3) (bd_ptr d4) (bd_bits d1) (bd_bits d2)
                (bd_bits d3) (bd_bits d4) (Zw (bd_cont d1)) (Zw (bd_cont d2)) (Zw (bd_cont d3))
                (Zw (bd_cont d4)) jp1 jp2 jp3 jp4); [exact S2 | exact EPR | z4pack | ..];
      first [assumption | lia | z4eq2].
    w4run2. if_cases KA; [| z4s2t Q l1 l2 l3 d1 d2 d3 d4 jp1 jp2 jp3 jp4 S2 EPR].
    zify_cond KA. w4run2. if_cases KB; [| z4s2t Q l1 l2 l3 d1 d2 d3 d4 jp1 jp2 jp3 jp4 S2 EPR].
    assert (D8 : 3 * seg + 8 <= dcap).
    { pose proof z4c_d0 as (DA & DB). pose proof (@ATOP_hi rc) as AH2. clear - KA DA DB AH2 D6 DC.
      change 18446744073709551615 with (Z.ones 64) in KA. rewrite !Z.land_ones in KA by lia.
      Z.div_mod_to_equations. lia. }
    w4run2.
    eapply (z4c_loop Q _ l1 l2 l3 (bd_ptr d1) (bd_ptr d2) (bd_ptr d3) (bd_ptr d4) (bd_bits d1) (bd_bits d2)
              (bd_bits d3) (bd_bits d4) (Zw (bd_cont d1)) (Zw (bd_cont d2)) (Zw (bd_cont d3))
              (Zw (bd_cont d4)) jp1 jp2 jp3 jp4); [exact ZI | exact S2 | exact EPR | z4pack | ..];
      try first [assumption | lia | z4eq2].

  Qed.
End Z4S1M0.

Lemma z4s1_m0 : z4F_case.
Proof.
  unfold z4F_case.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src
    cells cbs pdt SBL SBH rstk CTX ZI.
  destruct CTX as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                   & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  exact (z4m0_main AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
           src cells cbs pdt SBL SBH rstk AH NFK ABL MTL TLM HDT TOK ECB LCB DSTF DC BYS NSM S16 SRCB DJ1 DJ2 DJ3 LOA LOS SPT
           SP16 TPA HINV RCL RLO RHI RRL RRS WSK WIM WIS WFS Q ZI).
Qed.


End CANSEC1.
