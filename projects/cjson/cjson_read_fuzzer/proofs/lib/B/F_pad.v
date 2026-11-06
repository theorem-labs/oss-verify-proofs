(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_defs CJ_iface AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_memset F_memcpy F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition pad_entry := 0x94ef8%Z.

(* [comment removed for export] *)
Definition got_ssp := 0xa2388%Z.
Definition ssp_guard := 0x5fc9b0%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells bsegs m ssp_guard [C8 canary].

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition PAD_DEPTH : Z := 2672.   (* [comment removed for export] *)

Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

Definition pad_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
    (C n : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2672, bv_unsigned sp);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + n);
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk)
    /\ ssp_cells m' canary.

(* [comment removed for export] *)
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
  (ssp_guard + 8 <= bv_unsigned sp - 368)%Z ->
  (bv_unsigned sp <= bv_unsigned a0)%Z -> (bv_unsigned sp <= B)%Z ->
  (* [comment removed for export] *)
  MRT m -> (alloc_ceiling <= lo)%Z -> (lo + PAD_DEPTH <= bv_unsigned sp)%Z -> (bv_unsigned sp + 64 <= KHIGHMEM_END)%Z ->
  app_range (B + Z.of_nat (length content)) (pad_n W L FL) -> wr_range_ok (B + Z.of_nat (length content)) (pad_n W L FL) ->
  ((0 < pad_n W L FL)%Z -> shadow_ok m (B + Z.of_nat (length content)) (pad_n W L FL)) ->
  evt bsegs (pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x94ef8) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros WF (GOT & SSP) ST MI HC HW HL HFL HWL ROOM GLO AF AB.
  intros MR CEIL SPB SPHI ARd WRd SOd.
  unfold PAD_DEPTH in SPB. pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  pose proof SPHI as SPH. unfold KHIGHMEM_END in SPH. pose proof AINTRIN_STACK_val as AIS.
  pose proof WF as WF0. (nelim WF 7%nat; intros FC BUF FLG LBF Bpos Bhi SEPfb).
  pose_word_ranges.
  set (Fp := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size csize Nat.add length] in BF.
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Nat2Z.inj_add in BB.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 2672, bv_unsigned sp);
                          (B + Z.of_nat (length content), B + Z.of_nat (length content) + pad_n W L FL);
                          (Fp + 40, Fp + 48)]%Z m) as MU.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUs.   (* [comment removed for export] *)
  pose proof (wmono_refl bsegs m) as WM.
  unfold FILE_cells in FC.
  carve_frame 304%nat ST.
  do 6 zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  assert (EXIT : forall m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (n : Z) pad256,
    n = pad_n W L FL ->
    mem_inv bsegs m1 ->
    rw_cells bsegs m1 (bv_unsigned sp + -304) [CB 256 pad256; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk bsegs m1 lo (bv_unsigned sp + -304) ->
    munch [(bv_unsigned sp - 2672, bv_unsigned sp); (B + Z.of_nat (length content), B + Z.of_nat (length content) + pad_n W L FL); (Fp + 40, Fp + 48)]%Z m m1 ->
    wmono bsegs m m1 ->
    wfile m1 Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk) ->
    rw_cells bsegs m1 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m1 ssp_guard [C8 canary] ->
    evt bsegs (pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) lo m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 6277552) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x94fa0) fc None m1 (seg_rom bsegs))).
  { intros until pad256. intros Hn MI1 FR1 ST1 MU1 WM1 WF1 GOT1 SSP1. unfold got_ssp, ssp_guard in GOT1, SSP1.
    zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
    { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 6 zstep. zstep. release_frame FR1 ST1 (bv_unsigned sp).
    apply evt_done. unfold pad_post.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [ ms_eq | ].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
    split; [rewrite <- Hn; exact WF1 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT1 | exact SSP1]]. }
  (* [comment removed for export] *)
  Ltac mk_wfile FC BUF FLG LBF := split; [exact FC|]; split; [exact BUF|]; split; [exact FLG|]; split; [exact LBF|]; split; [lia|]; split; lia.
  assert (PN0 : (W <= L \/ Z.land FL 73728 <> 0)%Z -> pad_n W L FL = 0%Z).
  { intros HH. unfold pad_n, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
    destruct (Z.eqb_spec (Z.land FL 73728) 0); destruct (Z.leb_spec0 W L); cbn; lia. }
  zstep. if_cases Kw; zify_cond Kw; rewrite !signed_of_Z in Kw by lia.
  - (* [comment removed for export] *)
    eapply EXIT; [ reflexivity | exact MI | exact FR | exact ST | exact MU | exact WM | | exact GOT | exact SSP ].
    rewrite PN0 by lia. rewrite !Z2Nat.inj_0. cbn [repeat]. rewrite skipn_O, app_nil_r. mk_wfile FC BUF FLG LBF.
  - zstep. zstep. zstep. if_cases Kf; zify_cond Kf.
    + (* [comment removed for export] *)
      eapply EXIT; [ reflexivity | exact MI | exact FR | exact ST | exact MU | exact WM | | exact GOT | exact SSP ].
      rewrite PN0 by lia. rewrite !Z2Nat.inj_0. cbn [repeat]. rewrite skipn_O, app_nil_r. mk_wfile FC BUF FLG LBF.
    + assert (PN : pad_n W L FL = (W - L)%Z).
      { unfold pad_n, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
        destruct (Z.eqb_spec (Z.land FL 73728) 0); destruct (Z.leb_spec0 W L); cbn; lia. }
      rewrite PN in *. set (N := (W - L)%Z) in *.
      zstep. rewrite Z_to_bv_swrap32, (sext32_small (W - L)) by lia. fold N.
      zstep. zstep. zstep. if_cases Kn; zify_cond Kn.
      2:{ exfalso. revert Kn. rewrite ?unsigned_lit by lia. lia. }
      (* [comment removed for export] *)
      apply (rw_cells_split_CB bsegs _ _ [] 256 _ [C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [Z.to_nat N; 256 - Z.to_nat N]%nat) in FR; [ | cbn; lia ].
      cbn [mk_CB_cells app] in FR.
      apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FR. destruct FR as [FRa FRb].
      cbn [cells_size csize] in FRb. rewrite Nat.add_0_r, Z2Nat.id in FRb by lia.
      zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MR1 : MRT mm)
          by (eapply (MRT_munch _ m mm); [exact MR| exact MUs|];
              apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil])
      end.
      call memset_icpt_callZ.
      1:{ exact FRa. } 1:{ hyp. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
      1:{ exact (MRT_icpt _ MR1). } 1:{ exact ST. } 1:{ exact CEIL. } 1:{ lia. } 1:{ lia. }
      1:{ apply app_range_stack; lia. } 1:{ apply wr_range_ok_stack; lia. }
      1:{ intros Hl. apply (MRT_shadow_ok_stack _ _ _ MR1); lia. } 1:{ lia. }
      clear MR1. match goal with H : stk bsegs _ lo _ |- _ => rename H into ST end.
      rewrite (unsigned_lit C) in * by lia. rewrite (Z.mod_small C 256) in * by lia.
      match goal with MSC : rw_cells _ _ (bv_unsigned sp + -304)%Z [CB (Z.to_nat N) _] |- _ => rename MSC into FRa end.
      zstep. if_cases Kn2; zify_cond Kn2.
      2:{ exfalso. revert Kn2. rewrite ?unsigned_lit by lia. lia. }
      zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
      { exfalso. exact (Ke FLG). }
      zstep. zstep. zstep. zstep.
      pose proof (rw_cells_bytes_at' _ _ _ _ FRa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
      (* [comment removed for export] *)
      set (bsP := repeat (Z_to_bv 8 C) (Z.to_nat N)) in *.
      assert (LbsP : length bsP = Z.to_nat N) by (subst bsP; apply repeat_length).
      set (nc := length content) in *. set (nj := length junk) in *.
      (* [comment removed for export] *)
      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m' _) =>
        assert (MR2 : MRT m')
          by (eapply (MRT_munch _ m m'); [exact MR| exact MUs|];
              apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil]);
        assert (SOd2 : (0 < N)%Z -> shadow_ok m' (B + Z.of_nat nc) N)
          by (intros Hl; eapply shadow_ok_munch_app; [apply SOd; exact Hl| exact MUs| exact Hl| exact ARd|];
              apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil]);
        clear MUs;
        eapply evt_cut;
        [ eapply fwritex_call;
          [ mk_wfile FC BUF FLG LBF
          | exact SRC
          | rewrite LbsP, Z2Nat.id by lia; reflexivity
          | rewrite LbsP; lia
          | exact ST
          | hyp
          | lia | lia | lia | lia | lia | lia | lia | lia | lia
          | exact MR2 | exact CEIL | unfold FWX_DEPTH; lia
          | apply app_range_stack; lia | exact ARd | exact WRd
          | intros Hl; apply (MRT_shadow_ok_stack _ _ _ MR2); lia | exact SOd2
          | lia | lia | lia | lia ]
        | post_call segs m' ]
      end.
      match goal with X : wfile _ _ _ _ _ _ _ _ (skipn (length _) _) |- _ => rewrite LbsP in X end.
      match goal with X : rw_cells _ _ (bv_unsigned sp + -304)%Z [CB (Z.to_nat N) _] |- _ => rename X into FRa' end.
      (* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition pad_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
    (C n : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(q - 2672, q);
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
  (ssp_guard + 8 <= q - 368)%Z -> (q < 2^64)%Z ->
  (q <= Fp < 2^64)%Z -> (q <= B)%Z ->
  (* [comment removed for export] *)
  MRT m -> (alloc_ceiling <= lo)%Z -> (lo + PAD_DEPTH <= q)%Z -> (q + 64 <= KHIGHMEM_END)%Z ->
  app_range (B + Z.of_nat (length content)) (pad_n W L FL) -> wr_range_ok (B + Z.of_nat (length content)) (pad_n W L FL) ->
  ((0 < pad_n W L FL)%Z -> shadow_ok m (B + Z.of_nat (length content)) (pad_n W L FL)) ->
  evt bsegs (pad_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x94ef8) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros WF SSP ST MI HC HW HL HFL HWL ROOM GLO Hq HF HB.
  intros MR CEIL SPB SPHI ARd WRd SOd.
  unfold ssp_guard in GLO.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Ef : bv_unsigned (Z_to_bv 64 Fp) = Fp) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (pad_spec ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp)); rewrite ?Eq, ?Ef; eauto; unfold ssp_guard; lia. }
  intros ms' P. unfold pad_post in P. rewrite !Eq, !Ef in P. exact P.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac hyp := lazymatch goal with |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end end.
