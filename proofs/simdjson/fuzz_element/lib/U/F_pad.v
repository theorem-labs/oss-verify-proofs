(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim FmtFp.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memset F_memcpy F_fwritex.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition pad_entry := 0xc6e58%Z.

Definition got_ssp := 0xdc448%Z.
Definition ssp_guard := 0x10f7f8%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].

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

Definition memset_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D C N : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(D, D + N)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].
Lemma memset_callZ : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q D C N : Z) (junk : list byte),
  rw_cells usegs m D [CB (Z.to_nat N) junk] ->
  mem_inv usegs m ->
  (0 <= q < 2^64)%Z -> (0 <= D < 2^64)%Z -> (0 <= C < 2^64)%Z -> (0 <= N < 2^64)%Z ->
  evt usegs (memset_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xd0c68) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros DST MI Hq HD HC HN.
  assert (Ed : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (Ec : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memset_spec ra (Z_to_bv 64 q)); rewrite ?Ed, ?En; eauto. }
  intros ms' P. unfold memset_post in P. rewrite !Ed, !Ec, !En in P. exact P.
Qed.

Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

Definition pad_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
    (C n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 368, bv_unsigned sp);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + n);
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' (bv_unsigned sp - 368) (bv_unsigned sp)
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk)
    /\ ssp_cells m' canary.

Ltac hyp := lazymatch goal with |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end end.

Lemma pad_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (C W L FL : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word),
  wfile m (bv_unsigned a0) fl0 j1 j2 lbfw B content junk ->
  ssp_cells m canary ->
  stk usegs m (bv_unsigned sp - 368) (bv_unsigned sp) ->
  mem_inv usegs m ->
  (0 <= C < 256)%Z -> (-2^31 <= W < 2^31)%Z -> (0 <= L < 2^31)%Z -> (0 <= FL < 2^32)%Z ->
  (W - L < 256)%Z ->
  (pad_n W L FL <= Z.of_nat (length junk))%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 368)%Z ->
  (bv_unsigned sp <= bv_unsigned a0)%Z -> (bv_unsigned sp <= B)%Z ->
  evt usegs (pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xc6e58) fc None m (seg_rom usegs)).
Proof.
  intros until canary. intros WF (GOT & SSP) ST MI HC HW HL HFL HWL ROOM GLO AF AB.
  pose proof WF as WF0. destruct WF as (FC & BUF & FLG & LBF & Bpos & Bhi & SEPfb).
  pose_word_ranges.
  set (Fp := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size csize Nat.add length] in BF.
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Nat2Z.inj_add in BB.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp);
                          (B + Z.of_nat (length content), B + Z.of_nat (length content) + pad_n W L FL);
                          (Fp + 40, Fp + 48)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold FILE_cells in FC.
  carve_frame 304%nat ST.
  do 6 zstep. zstep. zstep. zstep. zstep. zstep.

  assert (EXIT : forall m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (n : Z) pad256,
    n = pad_n W L FL ->
    mem_inv usegs m1 ->
    rw_cells usegs m1 (bv_unsigned sp + -304) [CB 256 pad256; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 (bv_unsigned sp - 368) (bv_unsigned sp + -304) ->
    munch [(bv_unsigned sp - 368, bv_unsigned sp); (B + Z.of_nat (length content), B + Z.of_nat (length content) + pad_n W L FL); (Fp + 40, Fp + 48)]%Z m m1 ->
    wmono usegs m m1 ->
    wfile m1 Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk) ->
    rw_cells usegs m1 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells usegs m1 ssp_guard [C8 canary] ->
    evt usegs (pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1112056) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xc6f00) fc None m1 (seg_rom usegs))).
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

      apply (rw_cells_split_CB usegs _ _ [] 256 _ [C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [Z.to_nat N; 256 - Z.to_nat N]%nat) in FR; [ | cbn; lia ].
      cbn [mk_CB_cells app] in FR.
      apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FR. destruct FR as [FRa FRb].
      cbn [cells_size csize] in FRb. rewrite Nat.add_0_r, Z2Nat.id in FRb by lia.
      zstep. zstep. call memset_callZ.
      1:{ exact FRa. } 1:{ hyp. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
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
        eapply evt_cut;
        [ eapply fwritex_call;
          [ mk_wfile FC BUF FLG LBF
          | exact SRC
          | rewrite LbsP, Z2Nat.id by lia; reflexivity
          | rewrite LbsP; lia
          | replace (bv_unsigned sp + -304 - 64)%Z with (bv_unsigned sp - 368)%Z by lia; exact ST
          | hyp
          | lia | lia | lia | lia | lia | lia | lia | lia | lia ]
        | post_call segs m ]
      end.
      match goal with X : stk _ _ (bv_unsigned sp + -304 - 64)%Z _ |- _ =>
        replace (bv_unsigned sp + -304 - 64)%Z with (bv_unsigned sp - 368)%Z in X by lia end.
      match goal with X : wfile _ _ _ _ _ _ _ _ (skipn (length _) _) |- _ => rewrite LbsP in X end.
      match goal with X : rw_cells _ _ (bv_unsigned sp + -304)%Z [CB (Z.to_nat N) _] |- _ => rename X into FRa' end.

      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FRb with rw_cells _ _ _ (?c2 :: ?rest) =>
        assert (FR : rw_cells usegs mm (bv_unsigned sp + -304) ([] ++ [CB (Z.to_nat N) bsP; c2] ++ rest));
        [ cbn [app]; apply (proj2 (rw_cells_app usegs _ _ [_] _)); split; [ exact FRa' |];
          cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact FRb
        | apply rw_cells_merge in FR; cbn [cells_size cells_bytes csize cbytes app Nat.add] in FR;
          rewrite app_nil_r in FR; replace (Z.to_nat N + (256 - Z.to_nat N + 0))%nat with 256%nat in FR by lia ]
      end end.
      unfold bsP in *. eapply EXIT; [ reflexivity | hyp | exact FR | hyp | hyp | hyp | hyp | unfold got_ssp, ssp_guard; hyp | unfold ssp_guard; hyp ].
Qed.

Definition pad_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
    (C n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 368, q);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + n);
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' (q - 368) q
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk)
    /\ ssp_cells m' canary.

Lemma pad_call : forall ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q Fp C W L FL : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word),
  wfile m Fp fl0 j1 j2 lbfw B content junk ->
  ssp_cells m canary ->
  stk usegs m (q - 368) q ->
  mem_inv usegs m ->
  (0 <= C < 256)%Z -> (-2^31 <= W < 2^31)%Z -> (0 <= L < 2^31)%Z -> (0 <= FL < 2^32)%Z ->
  (W - L < 256)%Z ->
  (pad_n W L FL <= Z.of_nat (length junk))%Z ->
  (ssp_guard + 8 <= q - 368)%Z -> (q < 2^64)%Z ->
  (q <= Fp < 2^64)%Z -> (q <= B)%Z ->
  evt usegs (pad_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xc6e58) fc None m (seg_rom usegs)).
Proof.
  intros until canary. intros WF SSP ST MI HC HW HL HFL HWL ROOM GLO Hq HF HB.
  unfold ssp_guard in GLO.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Ef : bv_unsigned (Z_to_bv 64 Fp) = Fp) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (pad_spec ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp)); rewrite ?Eq, ?Ef; eauto; unfold ssp_guard; lia. }
  intros ms' P. unfold pad_post in P. rewrite !Eq, !Ef in P. exact P.
Qed.
