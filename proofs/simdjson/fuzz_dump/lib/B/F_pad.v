(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import R_m2s I_consts F_achk I_memsetw F_fwritex_sn.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim FmtFp.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import F_memcpy F_fwritex.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import ImageA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition pad_entry := 0x1591b0%Z.

Definition got_ssp := 0x16ef68%Z.
Definition ssp_guard := 0x6cb3a8%Z.

Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  ro_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ ro_cells bsegs m ssp_guard [C8 canary].

Definition pad_n (w l fl : Z) : Z :=
  if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z || (w <=? l)%Z then 0 else w - l.

Lemma pad_model : forall o c w l fl, (w - l < 256)%Z ->
  pad o c w l fl = Some (o ++ zrepeat c (pad_n w l fl)).
Proof.
  intros o c w l fl H. unfold pad, pad_n.
  destruct (negb _ || _); [cbn; now rewrite app_nil_r|].
  change PAD_FUEL with (S 63). cbn [pad_loop].
  destruct (Z.leb_spec0 256 (w - l)); [lia|]. reflexivity.
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Definition memset_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D C N lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(D, D + N); (q - IMEMSET_DEPTH, q)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo q
    /\ rw_cells bsegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].
Lemma memset_callZ : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q D C N : Z) (junk : list byte) (lo : Z),
  rw_cells bsegs m D [CB (Z.to_nat N) junk] ->
  mem_inv bsegs m ->
  (0 <= q < 2^63)%Z -> (0 <= D)%Z -> (0 <= C < 2^64)%Z -> (0 <= N)%Z ->
  stk bsegs m lo q -> (lo <= q - IMEMSET_DEPTH)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (N = 0 \/ D + N <= lo \/ q <= D)%Z ->
  chkr m D N -> ictx m ->
  evt bsegs (memset_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x7e86c) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until lo. intros DST MI Hq HD HC HN ST LO HSH SEPD CK IC.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  pose proof (chkr_chk_ok m D N CK) as CHK. pose proof (chkr_bound m D N CK) as HDN. pose proof IC as (_ & ICM & _ & M2S).
  unfold kHighShadowEnd, kHighMemEnd in *.
  zstep.
  eapply evt_mono.
  { eapply (imemset_spec RIP ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D C N junk lo);
      rewrite ?Eq.
    all: first [reflexivity | exact ST | exact DST | exact MI | exact ICM | exact M2S | exact CHK | unfold kHighShadowEnd; lia | lia]. }
  cbv beta. intros ms' PS. unfold imemset_post in PS. rewrite !Eq in PS.
  destruct PS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & ST' & DC).
  unfold memset_postZ. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'| exact DC].
Qed.

Definition fwritex_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
    (S : Z) (bs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length bs))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(q - 2304, q);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + Z.of_nat (length bs));
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo q
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ bs) (skipn (length bs) junk)
    /\ bytes_at bsegs m' S bs.

Lemma fwritex_call : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q S L Fp : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk bs : list byte) (lo : Z),
  wfile m Fp fl0 j1 j2 lbfw B content junk ->
  bytes_at bsegs m S bs ->
  Z.of_nat (length bs) = L ->
  (length bs <= length junk)%nat ->
  stk bsegs m lo q ->
  mem_inv bsegs m ->
  (64 <= q < 2^63)%Z -> (0 <= S)%Z -> (S + L < 2^64)%Z -> (0 <= Fp)%Z ->
  (Fp + 148 <= lo \/ q <= Fp)%Z ->
  (B + Z.of_nat (length content) + Z.of_nat (length junk) <= lo \/ q <= B)%Z ->
  (S + L <= lo \/ q <= S)%Z ->
  (S + L <= B + Z.of_nat (length content) \/ B + Z.of_nat (length content) + L <= S)%Z ->
  (S + L <= Fp \/ Fp + 148 <= S)%Z ->

  (lo <= q - 2304)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  chkr m S L -> chkr m (B + Z.of_nat (length content)) L -> ictx m ->
  evt bsegs (fwritex_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp fl0 j1 j2 lbfw B content junk S bs lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) (Z_to_bv 64 Fp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x157b4c) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until lo. intros WF SRC LEN LE ST MI Hq HS HSL HFp SEP1 SEP2 SEP3 SEP4 SEP5 LO HSH CKS CKD IC.
  assert (HF : (Fp + 148 <= 2^64)%Z).
  { destruct WF as (FC & _). pose proof (rw_cells_bound _ _ _ _ FC) as BF. unfold FILE_cells in BF. cbn [cells_size csize Nat.add length] in BF.
    lia. }
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Es : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (El : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (Ef : bv_unsigned (Z_to_bv 64 Fp) = Fp) by (apply unsigned_lit; lia).
  subst L.
  eapply evt_mono.
  { eapply (fwritex_spec_A RIP ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length bs))) (Z_to_bv 64 Fp));
      rewrite ?Eq, ?Es, ?El, ?Ef; eauto; lia. }
  intros ms' P. unfold fwritex_postA in P. rewrite !Eq, !Es, !Ef in P. exact P.
Qed.

Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

Definition pad_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
    (C n lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2608, bv_unsigned sp);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + n);
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk)
    /\ ssp_cells m' canary.

Ltac hyp := lazymatch goal with |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end end.

Lemma pad_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (C W L FL : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word) (lo : Z),
  wfile m (bv_unsigned a0) fl0 j1 j2 lbfw B content junk ->
  ssp_cells m canary ->
  stk bsegs m lo (bv_unsigned sp) ->
  mem_inv bsegs m ->
  (0 <= C < 256)%Z -> (-2^31 <= W < 2^31)%Z -> (0 <= L < 2^31)%Z -> (0 <= FL < 2^32)%Z ->
  (W - L < 256)%Z ->
  (pad_n W L FL <= Z.of_nat (length junk))%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 2608)%Z ->
  (bv_unsigned sp <= bv_unsigned a0)%Z -> (bv_unsigned sp <= B)%Z ->

  (lo <= bv_unsigned sp - 2608)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (bv_unsigned sp < 2^63)%Z ->
  (forall p n, lo <= p -> p + n <= bv_unsigned sp -> chkr m p n)%Z ->
  chkr m (B + Z.of_nat (length content)) (Z.of_nat (length junk)) -> ictx m ->
  evt bsegs (pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1591b0) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until lo. intros WF (GOT & SSP) ST MI HC HW HL HFL HWL ROOM GLO AF AB LO HSH SPH CK0 CKB0 IC0.
  unfold kHighShadowEnd in *.
  pose proof WF as WF0. destruct WF as (FC & BUF & FLG & LBF & Bpos & Bhi & SEPfb).
  pose_word_ranges.
  set (Fp := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size csize Nat.add length] in BF.
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Nat2Z.inj_add in BB.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 2608, bv_unsigned sp);
                          (B + Z.of_nat (length content), B + Z.of_nat (length content) + pad_n W L FL);
                          (Fp + 40, Fp + 48)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.

  set (m0 := m) in CK0, CKB0, IC0.
  assert (Em0 : m0 = m) by reflexivity. clearbody m0.
  assert (AW : forall mm, munch [(bv_unsigned sp - 2608, bv_unsigned sp);
                          (B + Z.of_nat (length content), B + Z.of_nat (length content) + pad_n W L FL);
                          (Fp + 40, Fp + 48)]%Z m mm -> wmono bsegs m mm ->
            ictx mm /\ (forall p n, lo <= p -> p + n <= bv_unsigned sp -> chkr mm p n)%Z
            /\ chkr mm (B + Z.of_nat (length content)) (Z.of_nat (length junk))).
  { subst m0. intros mm MUm WMm. split; [| split].
    - apply (ictx_munch _ m mm IC0 MUm WMm). unfold ICR. cbn [in_rl outside]. intros x Hx. lia.
    - intros p n Hp Hn. apply (chkr_munch _ m mm p n (CK0 p n Hp Hn) MUm). unfold SHADOW_LO, SHADOW_HI. cbn [outside]. intros x Hx. lia.
    - apply (chkr_munch _ m mm _ _ CKB0 MUm). unfold SHADOW_LO, SHADOW_HI. cbn [outside]. intros x Hx. lia. }
  clear CK0 CKB0 IC0 Em0 m0.
  unfold FILE_cells in FC.
  carve_frame 304%nat ST.
  do 6 zstep. zstep. zstep. zstep. zstep. zstep.

  assert (EXIT : forall m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (n : Z) pad256,
    n = pad_n W L FL ->
    mem_inv bsegs m1 ->
    rw_cells bsegs m1 (bv_unsigned sp + -304) [CB 256 pad256; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk bsegs m1 lo (bv_unsigned sp + -304) ->
    munch [(bv_unsigned sp - 2608, bv_unsigned sp); (B + Z.of_nat (length content), B + Z.of_nat (length content) + pad_n W L FL); (Fp + 40, Fp + 48)]%Z m m1 ->
    wmono bsegs m m1 ->
    wfile m1 Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk) ->
    ro_cells bsegs m1 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> ro_cells bsegs m1 ssp_guard [C8 canary] ->
    evt bsegs (pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) lo m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 7123880) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x159258) fc None m1 (seg_rom bsegs))).
  { intros until pad256. intros Hn MI1 FR1 ST1 MU1 WM1 WF1 GOT1 SSP1. unfold got_ssp, ssp_guard in GOT1, SSP1.
    zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
    { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 6 zstep. zstep. release_frame FR1 ST1 (bv_unsigned sp).
    apply evt_done. unfold pad_post.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [ ms_eq | ].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
    split; [rewrite <- Hn; exact WF1 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT1 | exact SSP1]]. }

  Ltac mk_wfile FC BUF FLG LBF := split; [exact FC|]; split; [exact BUF|]; split; [exact FLG|]; split; [exact LBF|]; split; [lia|]; split; lia.
  assert (PN0 : (W <= L \/ Z.land FL 73728 <> 0)%Z -> pad_n W L FL = 0%Z).
  { intros HH. unfold pad_n, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
    destruct (Z.eqb_spec (Z.land FL 73728) 0); destruct (Z.leb_spec0 W L); cbn; lia. }
  zstep. if_cases Kw; zify_cond Kw; rewrite !signed_of_Z in Kw by lia.
  -
    eapply EXIT; [ reflexivity | exact MI | exact FR | exact ST | exact MU | exact WM | | exact GOT | exact SSP ].
    rewrite PN0 by lia. rewrite !Z2Nat.inj_0. cbn [repeat]. rewrite skipn_O, app_nil_r. mk_wfile FC BUF FLG LBF.
  - zstep. zstep. zstep. if_cases Kf; zify_cond Kf.
    +
      eapply EXIT; [ reflexivity | exact MI | exact FR | exact ST | exact MU | exact WM | | exact GOT | exact SSP ].
      rewrite PN0 by lia. rewrite !Z2Nat.inj_0. cbn [repeat]. rewrite skipn_O, app_nil_r. mk_wfile FC BUF FLG LBF.
    + assert (PN : pad_n W L FL = (W - L)%Z).
      { unfold pad_n, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
        destruct (Z.eqb_spec (Z.land FL 73728) 0); destruct (Z.leb_spec0 W L); cbn; lia. }
      rewrite PN in *. set (N := (W - L)%Z) in *.
      zstep. rewrite Z_to_bv_swrap32, (sext32_small (W - L)) by lia. fold N.
      zstep. zstep. zstep. if_cases Kn; zify_cond Kn.
      2:{ exfalso. revert Kn. rewrite ?unsigned_lit by lia. lia. }

      apply (rw_cells_split_CB bsegs _ _ [] 256 _ [C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [Z.to_nat N; 256 - Z.to_nat N]%nat) in FR; [ | cbn; lia ].
      cbn [mk_CB_cells app] in FR.
      apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FR. destruct FR as [FRa FRb].
      cbn [cells_size csize] in FRb. rewrite Nat.add_0_r, Z2Nat.id in FRb by lia.
      zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        destruct (AW mm ltac:(hyp) ltac:(hyp)) as (ICm & CKm & CKBm) end.
      call memset_callZ.
      1:{ exact FRa. } 1:{ hyp. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
      1:{ exact ST. } 1:{ lia. } 1:{ unfold kHighShadowEnd in *; lia. } 1:{ lia. }
      1:{ apply CKm; lia. } 1:{ exact ICm. }
      clear ICm CKm CKBm.
      rewrite (Z.mod_small C 256) in * by lia.
      match goal with MSC : rw_cells _ _ (bv_unsigned sp + -304)%Z [CB (Z.to_nat N) _] |- _ => rename MSC into FRa end.
      zstep. if_cases Kn2; zify_cond Kn2.
      2:{ exfalso. revert Kn2. rewrite ?unsigned_lit by lia. lia. }
      zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
      { exfalso. exact (Ke FLG). }
      zstep. zstep. zstep. zstep.
      pose proof (rw_cells_bytes_at' _ _ _ _ FRa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.

      set (bsP := repeat (Z_to_bv 8 C) (Z.to_nat N)) in *.
      assert (LbsP : length bsP = Z.to_nat N) by (subst bsP; apply repeat_length).
      set (nc := length content) in *. set (nj := length junk) in *.

      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
        destruct (AW m ltac:(hyp) ltac:(hyp)) as (ICm & CKm & CKBm);
        eapply evt_cut;
        [ eapply fwritex_call;
          [ mk_wfile FC BUF FLG LBF
          | exact SRC
          | rewrite LbsP, Z2Nat.id by lia; reflexivity
          | rewrite LbsP; lia
          | match goal with H : stk _ _ _ _ |- _ => exact H end
          | hyp
          | lia | lia | lia | lia | lia | lia | lia | lia | lia
          | lia | unfold kHighShadowEnd in *; lia
          | apply CKm; lia
          | apply (chkr_sub _ _ _ _ _ CKBm); rewrite ?LbsP; lia
          | exact ICm ]
        | clear ICm CKm CKBm FC BUF; post_call segs m ]
      end.
      match goal with X : wfile _ _ _ _ _ _ _ _ (skipn (length _) _) |- _ => rewrite LbsP in X end.
      match goal with X : rw_cells _ _ (bv_unsigned sp + -304)%Z [CB (Z.to_nat N) _] |- _ => rename X into FRa' end.

      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FRb with rw_cells _ _ _ (?c2 :: ?rest) =>
        assert (FR : rw_cells bsegs mm (bv_unsigned sp + -304) ([] ++ [CB (Z.to_nat N) bsP; c2] ++ rest));
        [ cbn [app]; apply (proj2 (rw_cells_app bsegs _ _ [_] _)); split; [ exact FRa' |];
          cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact FRb
        | apply rw_cells_merge in FR; cbn [cells_size cells_bytes csize cbytes app Nat.add] in FR;
          rewrite app_nil_r in FR; replace (Z.to_nat N + (256 - Z.to_nat N + 0))%nat with 256%nat in FR by lia ]
      end end.
      unfold bsP in *. eapply EXIT; [ reflexivity | hyp | exact FR | hyp | hyp | hyp | hyp | unfold got_ssp, ssp_guard; hyp | unfold ssp_guard; hyp ].
Qed.

Definition pad_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
    (C n lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(q - 2608, q);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + n);
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo q
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk)
    /\ ssp_cells m' canary.

Lemma pad_call : forall ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q Fp C W L FL : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word) (lo : Z),
  wfile m Fp fl0 j1 j2 lbfw B content junk ->
  ssp_cells m canary ->
  stk bsegs m lo q ->
  mem_inv bsegs m ->
  (0 <= C < 256)%Z -> (-2^31 <= W < 2^31)%Z -> (0 <= L < 2^31)%Z -> (0 <= FL < 2^32)%Z ->
  (W - L < 256)%Z ->
  (pad_n W L FL <= Z.of_nat (length junk))%Z ->
  (ssp_guard + 8 <= q - 2608)%Z -> (q < 2^63)%Z ->
  (q <= Fp < 2^64)%Z -> (q <= B)%Z ->
  (lo <= q - 2608)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (forall p n, lo <= p -> p + n <= q -> chkr m p n)%Z ->
  chkr m (B + Z.of_nat (length content)) (Z.of_nat (length junk)) -> ictx m ->
  evt bsegs (pad_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1591b0) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until lo. intros WF SSP ST MI HC HW HL HFL HWL ROOM GLO Hq HF HB LO HSH CK CKB IC.
  unfold ssp_guard, kHighShadowEnd in GLO, LO, HSH.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Ef : bv_unsigned (Z_to_bv 64 Fp) = Fp) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (pad_spec ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp)); rewrite ?Eq, ?Ef; eauto; unfold ssp_guard, kHighShadowEnd; try lia. }
  intros ms' P. unfold pad_post in P. rewrite !Eq, !Ef in P. exact P.
Qed.
End WithRIP.
