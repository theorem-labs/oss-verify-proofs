(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_ctype F_syscalls F_errno_location F_strtol F_atoi F_htons F_memset F_stpncpy F_strncasecmp
     F_inet_pton_A F_inet_pton_C H_parse_uric.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import HU_list_kit.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition parse_uri_entry := 0x16ba4%Z.
Definition PURI_FRAME : Z := 400.
Definition PURI_DEPTH : Z := 928.
Notation GOT_GIF := 0x2a118%Z.
Notation GIF := 0x2b468%Z.

Definition parse_uri_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (U O : Z) (ustr slack : list byte) (canary gifv : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z) (junk' : list byte) (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - PURI_DEPTH, bv_unsigned sp); (O, O + 216); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - PURI_DEPTH) (bv_unsigned sp)
    /\ rw_cells rsegs m' O [CB 216 junk']
    /\ bytes_at rsegs m' U (ustr ++ Z_to_bv 8 0 :: slack)
    /\ rw_cells rsegs m' (bv_unsigned tp - 164) [C4 errv']
    /\ rw_cells rsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m' ssp_guard [C8 canary]
    /\ bytes_at rsegs m' GOT_GIF (le8 (Z_to_bv 64 GIF)) /\ bytes_at rsegs m' GIF (le4 gifv).

Definition parse_uri_stmt : Prop :=
  forall (U O ulen : Z) (ustr slack junk : list byte) (errv canary gifv : word)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bytes_at rsegs m U (ustr ++ Z_to_bv 8 0 :: slack) -> Z.of_nat (length ustr) = ulen -> (0 <= ulen < 2^31)%Z ->
  ((- (U + ulen + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  rw_cells rsegs m O [CB 216 junk] ->
  rw_cells rsegs m (bv_unsigned tp - 164) [C4 errv] ->
  rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
  bytes_at rsegs m GOT_GIF (le8 (Z_to_bv 64 GIF)) -> bytes_at rsegs m GIF (le4 gifv) ->
  stk rsegs m (bv_unsigned sp - PURI_DEPTH) (bv_unsigned sp) -> mem_inv rsegs m ->

  (4096 <= U)%Z -> (U + ulen + 1 + Z.of_nat (length slack) <= bv_unsigned sp - PURI_DEPTH)%Z ->
  (bv_unsigned sp <= O)%Z -> (O + 216 <= 2^62)%Z -> (O mod 8 = 0)%Z -> (bv_unsigned sp + 2^41 <= 2^63)%Z ->
  (4096 + 164 <= bv_unsigned tp)%Z -> (bv_unsigned tp - 164 + 4 <= bv_unsigned sp - PURI_DEPTH)%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - PURI_DEPTH)%Z -> (got_ssp + 8 <= bv_unsigned sp - PURI_DEPTH)%Z ->
  (GIF + 4 <= bv_unsigned sp - PURI_DEPTH)%Z ->
  (bv_unsigned tp - 164 + 4 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164)%Z ->
  (bv_unsigned tp - 164 + 4 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164)%Z ->
  (bv_unsigned tp - 164 + 4 <= GOT_GIF \/ GOT_GIF + 8 <= bv_unsigned tp - 164)%Z ->
  (bv_unsigned tp - 164 + 4 <= GIF \/ GIF + 4 <= bv_unsigned tp - 164)%Z ->
  (bv_unsigned tp - 164 + 4 <= U \/ U + ulen + 1 + Z.of_nat (length slack) <= bv_unsigned tp - 164)%Z ->
  a0 = Z_to_bv 64 U -> a1 = Z_to_bv 64 ulen -> a2 = Z_to_bv 64 O ->
  evt rsegs (parse_uri_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc U O ustr slack canary gifv m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 parse_uri_entry) fc None m (seg_rom rsegs)).

Ltac sstep := step; fix_lit_store.
Ltac pg := match goal with |- ?G => idtac G end.
Ltac ph := try (match goal with H : ?T |- _ => idtac H ":" T; fail end).

Ltac post_callq segs m :=
  let ms' := fresh "ms'" in let PO := fresh "PC" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  lazymatch goal with QSP : bv_unsigned (Z_to_bv 64 _) = _ |- _ => try rewrite !QSP in MUc; try rewrite !QSP in PO end;
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Tactic Notation "callq" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callq segs m ]
  end.

Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

Lemma rw_CB_len : forall m A n bs, rw_cells rsegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[W _] _]. cbn in W. LiaTuning.ctauto. Qed.

Lemma out_split : forall m O junk, rw_cells rsegs m O [CB 216 junk] ->
  exists j0 a b c d j4,
    rw_cells rsegs m O [CB 32 j0] /\ rw_cells rsegs m (O + 32) [C8 a; C8 b] /\ rw_cells rsegs m (O + 48) [C8 c; C8 d]
    /\ rw_cells rsegs m (O + 64) [CB 152 j4].
Proof.
  intros m O junk H.
  pose proof (rw_cells_split_CB rsegs m O [] 216 junk [] [32; 8; 8; 8; 8; 152]%nat H eq_refl) as S. cbn [mk_CB_cells app] in S.
  change (rw_cells rsegs m O ([CB 32 (firstn 32 junk)] ++ [CB 8 (firstn 8 (skipn 32 junk)); CB 8 (firstn 8 (skipn 8 (skipn 32 junk)))] ++
     [CB 8 (firstn 8 (skipn 8 (skipn 8 (skipn 32 junk)))); CB 8 (firstn 8 (skipn 8 (skipn 8 (skipn 8 (skipn 32 junk))))); CB 152 (firstn 152 (skipn 8 (skipn 8 (skipn 8 (skipn 8 (skipn 32 junk))))))])) in S.
  apply rw_cells_take3 in S. destruct S as (S1 & S2 & S3). cbn [cells_size csize Nat.add] in S2, S3.
  change (Z.of_nat 32) with 32%Z in *. change (Z.of_nat 16) with 16%Z in *.
  replace (O + 32 + 16)%Z with (O + 48)%Z in S3 by lia.
  lazymatch type of S3 with rw_cells _ _ _ [?a; ?b; ?c] => change (rw_cells rsegs m (O + 48) ([a; b] ++ [c])) in S3 end.
  apply rw_cells_app in S3. destruct S3 as [S3 S4].
  cbn [cells_size csize Nat.add] in S4. change (Z.of_nat 16) with 16%Z in *. replace (O + 48 + 16)%Z with (O + 64)%Z in S4 by lia.
  pose proof (rw_cells_CB_C8 rsegs m _ [] _ _ S2) as S2'. cbn [app] in S2'. pose proof (rw_cells_CB_C8 rsegs m _ [_] _ [] S2') as S2''. cbn [app] in S2''.
  pose proof (rw_cells_CB_C8 rsegs m _ [] _ _ S3) as S3'. cbn [app] in S3'. pose proof (rw_cells_CB_C8 rsegs m _ [_] _ [] S3') as S3''. cbn [app] in S3''.
  do 6 eexists. split; [exact S1|]. split; [exact S2''|]. split; [exact S3''| exact S4].
Qed.

Lemma out_join : forall m O cs0 cs1 cs2 cs3,
  rw_cells rsegs m O cs0 -> cells_size cs0 = 32%nat ->
  rw_cells rsegs m (O + 32) cs1 -> cells_size cs1 = 16%nat ->
  rw_cells rsegs m (O + 48) cs2 -> cells_size cs2 = 16%nat ->
  rw_cells rsegs m (O + 64) cs3 -> cells_size cs3 = 152%nat ->
  exists junk, rw_cells rsegs m O [CB 216 junk].
Proof.
  intros m O cs0 cs1 cs2 cs3 H0 L0 H1 L1 H2 L2 H3 L3.
  assert (H23 : rw_cells rsegs m (O + 48) (cs2 ++ cs3)). { apply rw_cells_app. rewrite L2. split; [exact H2|]. change (Z.of_nat 16) with 16%Z. replace (O+48+16)%Z with (O+64)%Z by lia. exact H3. }
  assert (H123 : rw_cells rsegs m (O + 32) (cs1 ++ cs2 ++ cs3)). { apply rw_cells_app. rewrite L1. split; [exact H1|]. change (Z.of_nat 16) with 16%Z. replace (O+32+16)%Z with (O+48)%Z by lia. exact H23. }
  assert (H : rw_cells rsegs m O (cs0 ++ cs1 ++ cs2 ++ cs3)). { apply rw_cells_app. rewrite L0. split; [exact H0|]. change (Z.of_nat 32) with 32%Z. exact H123. }
  destruct (rw_cells_forget rsegs m O _ H) as [junk J]. rewrite !cells_size_app, L0, L1, L2, L3 in J. cbn in J. exists junk. exact J.
Qed.

Lemma frame_join : forall m q csA csB,
  rw_cells rsegs m q csA -> cells_size csA = 296%nat -> rw_cells rsegs m (q + 296) csB ->
  rw_cells rsegs m q (csA ++ csB).
Proof. intros m q csA csB HA LA HB. apply rw_cells_app. rewrite LA. split; [exact HA| exact HB]. Qed.

Lemma bytes_at_drop : forall m a l k, bytes_at rsegs m a l -> (k <= length l)%nat -> bytes_at rsegs m (a + Z.of_nat k) (skipn k l).
Proof.
  intros m a l k H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length, Nat.min_l in H by lia. exact H.
Qed.

Definition oal (O : Z) : Prop := (O mod 8 = 0)%Z.

Lemma puri_slti0 : forall x, (0 <= x < 2^63)%Z -> (Z.lxor x 9223372036854775808 <? 9223372036854775808)%Z = false.
Proof. intros x Hx. change 9223372036854775808%Z with (2^63)%Z. rewrite zb_lxor_pow2_small by lia. apply Z.ltb_ge. lia. Qed.

Ltac pwalk_to p :=
  repeat first [ (uis_ms; tryif uat_pc p then fail else ucstep)
               | (uhas_b2z_if; rewrite ?puri_slti0 by lia; uub_b2z; ulit_branch_safe)
               | (uis_if; first [ ubr_auto | ubr2 | ubr3 ]) ].

Section WALK.
Context {HCEIL : HasCeiling}.
  Variables (U O ulen : Z) (ustr slack : list byte) (canary gifv : word).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis USL : Z.of_nat (length ustr) = ulen.
  Hypothesis ULR : (0 <= ulen < 2^31)%Z.
  Hypothesis PAD : ((- (U + ulen + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis U4K : (4096 <= U)%Z.
  Hypothesis ULO : (U + ulen + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 928)%Z.
  Hypothesis OSP : (bv_unsigned sp <= O)%Z.
  Hypothesis OHI : (O + 216 <= 2^62)%Z.
  Hypothesis OAL : oal O.
  Hypothesis SPH : (bv_unsigned sp + 2^41 <= 2^63)%Z.
  Hypothesis TP1 : (4096 + 164 <= bv_unsigned tp)%Z.
  Hypothesis TP2 : (bv_unsigned tp - 164 + 4 <= bv_unsigned sp - 928)%Z.
  Hypothesis SGLO : (ssp_guard + 8 <= bv_unsigned sp - 928)%Z.
  Hypothesis GSLO : (got_ssp + 8 <= bv_unsigned sp - 928)%Z.
  Hypothesis GFLO : (GIF + 4 <= bv_unsigned sp - 928)%Z.
  Hypothesis DE1 : (bv_unsigned tp - 164 + 4 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE2 : (bv_unsigned tp - 164 + 4 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE3 : (bv_unsigned tp - 164 + 4 <= GOT_GIF \/ GOT_GIF + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE4 : (bv_unsigned tp - 164 + 4 <= GIF \/ GIF + 4 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE5 : (bv_unsigned tp - 164 + 4 <= U \/ U + ulen + 1 + Z.of_nat (length slack) <= bv_unsigned tp - 164)%Z.

  Notation SP := (bv_unsigned sp).
  Notation q := (bv_unsigned sp + -400)%Z.
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -400)).
  Notation lo := (bv_unsigned sp - 928)%Z.
  Notation TPE := (bv_unsigned tp - 164)%Z.
  Notation W := [(bv_unsigned sp - 928, bv_unsigned sp); (O, O + 216); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z.
  Notation POST := (parse_uri_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc U O ustr slack canary gifv m0).
  Notation USTR m := (bytes_at rsegs m U (ustr ++ Z_to_bv 8 0 :: slack)).

  Definition base (m : mem) : Prop :=
    USTR m
    /\ (exists errv, rw_cells rsegs m TPE [C4 errv])
    /\ rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 canary]
    /\ ro_cells rsegs m GOT_GIF [C8 (Z_to_bv 64 GIF)] /\ ro_cells rsegs m GIF [C4 gifv]
    /\ mem_inv rsegs m /\ munch W m0 m /\ wmono rsegs m0 m.

  Notation FRB m := (rw_cells rsegs m (q + 296) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Ltac open_base B :=
    let errv := fresh "errv" in
    destruct B as (USTR & [errv ERR] & GOT & CAN & GIFP & GIFV & MI & MU & WM).
  Ltac close_base :=
    lazymatch goal with |- base ?m =>
      split; [assumption|]; split; [eexists; eassumption|]; repeat (split; [assumption|]); assumption end.

  #[using="U ulen slack ULR U4K ULO SPH"] Lemma sp_range : (928 <= SP /\ SP + 2^41 <= 2^63)%Z.
  Proof. clear -ULR U4K ULO SPH. pose proof (word_lt64 sp). lia. Qed.
  #[using="U ulen ustr slack ULR U4K ULO SPH GFLO"] Lemma q_sp : bv_unsigned spw = q.
  Proof. pose proof sp_range. apply unsigned_lit. lia. Qed.

  #[using="ulen ULR U4K ULO SPH"] Lemma epilogue : forall (r : Z) x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      m jA junk,
    base m -> rw_cells rsegs m q [CB 296 jA] -> FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O [CB 216 junk] ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16e04) fc None m (seg_rom rsegs)).
  Proof.
    intros until junk. intros B FRA FRBm ST OUT. open_base B. pose proof sp_range as SR.
    pose proof (frame_join m q _ _ FRA eq_refl FRBm) as FR. clear FRA FRBm. cbn [app] in FR.
    do 15 step.
    release_frame FR ST (bv_unsigned sp).
    unfold parse_uri_post, PURI_DEPTH. finish.
    all: try exact OUT. all: try exact ERR.
    - destruct GIFP as [_ B1]. exact B1.
    - destruct GIFV as [_ B1]. exact B1.
  Qed.

  #[using="Type"] Lemma frameA_forget : forall m cs, rw_cells rsegs m q cs -> cells_size cs = 296%nat -> exists j, rw_cells rsegs m q [CB 296 j].
  Proof. intros m cs H L. destruct (rw_cells_forget rsegs m q cs H) as [j J]. rewrite L in J. exists j. exact J. Qed.

  #[using="USL"] Lemma nth_U : forall i, (0 <= i <= ulen)%Z -> exists b, nth_error (ustr ++ Z_to_bv 8 0 :: slack) (Z.to_nat i) = Some b.
  Proof.
    clear -USL. intros i Hi. destruct (nth_error _ (Z.to_nat i)) as [b|] eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. rewrite app_length in E. cbn [length] in E. lia.
  Qed.

  #[using="USL"] Lemma USTR_len : Z.of_nat (length (ustr ++ Z_to_bv 8 0 :: slack)) = (ulen + 1 + Z.of_nat (length slack))%Z.
  Proof. clear -USL. rewrite app_length. cbn [length]. lia. Qed.

  #[using="ulen ULR U4K ULO SPH"] Lemma fin : forall x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      m jA cs0 cs1 cs2 cs3,
    base m -> rw_cells rsegs m q [CB 296 jA] -> FRB m -> stk rsegs m lo (q - 112) -> stk rsegs m (q - 112) q ->
    rw_cells rsegs m O cs0 -> cells_size cs0 = 32%nat -> rw_cells rsegs m (O + 32) cs1 -> cells_size cs1 = 16%nat ->
    rw_cells rsegs m (O + 48) cs2 -> cells_size cs2 = 16%nat -> rw_cells rsegs m (O + 64) cs3 -> cells_size cs3 = 152%nat ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16e00) fc None m (seg_rom rsegs)).
  Proof.
    intros until cs3. intros B FRA FRBm ST1 ST2 O0 L0 O1 L1 O2 L2 O3 L3. pose proof sp_range as SR.
    destruct (out_join m O cs0 cs1 cs2 cs3 O0 L0 O1 L1 O2 L2 O3 L3) as [junk OUT].
    pose proof (stk_merge rsegs m lo (q - 112) q ST1 ST2 ltac:(lia)) as ST.
    open_base B. zstep. eapply epilogue; try eassumption. close_base.
  Qed.

  #[using="ulen USL ULR PAD U4K ULO OSP OHI SPH TP2 SGLO GSLO GFLO DE4"] Lemma frag_null : forall x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      m jA cs0 cs1 (oc od : word) cs3,
    base m -> rw_cells rsegs m q [CB 296 jA] -> FRB m -> stk rsegs m lo (q - 112) -> stk rsegs m (q - 112) q ->
    rw_cells rsegs m O cs0 -> cells_size cs0 = 32%nat -> rw_cells rsegs m (O + 32) cs1 -> cells_size cs1 = 16%nat ->
    rw_cells rsegs m (O + 48) [C8 oc; C8 od] -> rw_cells rsegs m (O + 64) cs3 -> cells_size cs3 = 152%nat ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16df8) fc None m (seg_rom rsegs)).
  Proof.
    intros until cs3. intros B FRA FRBm ST1 ST2 O0 L0 O1 L1 O2 O3 L3. pose proof sp_range as SR. open_base B.
    sstep. sstep.
    eapply fin; try eassumption; try reflexivity. close_base.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE3 DE4"] Lemma tail : forall (bp : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31
      m jA junk,
    base m -> rw_cells rsegs m q [CB 296 jA] -> FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O [CB 216 junk] -> (0 <= bp <= ulen)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 1) (Z_to_bv 64 bp) x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16d58) fc None m (seg_rom rsegs)).
  Proof.
    intros until junk. intros B FRA FRBm ST OUT BP. open_base B. pose proof sp_range as SR.
    pose proof USTR_len as UL. pose proof OAL as OA. unfold oal in OA.
    destruct (out_split m O junk OUT) as (j0 & oa & ob & oc & od & j4 & OUT0 & PQ & FRG & HP). clear OUT junk.
    pwalk_to 0x16d88%Z. step.
    pose proof (bytes_at_drop m U _ (Z.to_nat bp) USTR ltac:(rewrite app_length; cbn [length]; lia)) as SUF. rewrite Z2Nat.id in SUF by lia.
    pose proof q_sp as QSP. destruct (stk_split rsegs m lo (q - 112) q ST ltac:(lia)) as [ST1 ST2]. clear ST.
    callq (parse_uric_spec (U + bp)%Z (O + 32)%Z (ulen - bp)%Z (skipn (Z.to_nat bp) (ustr ++ Z_to_bv 8 0 :: slack)) oa ob).
    all: side (rewrite ?QSP, ?skipn_length, ?UL; first [exact SUF | exact PQ | exact ST2 | exact MI | reflexivity | lia]).
    match goal with H : stk _ _ _ q |- _ => rename H into ST2 end.
    match goal with H : rw_cells _ _ (O + 32)%Z _ |- _ => rename H into PQ end.
    match goal with H : bytes_at _ _ (U + bp)%Z _ |- _ => clear H end.
    match goal with H : (0 <= ?i)%Z, H2 : (?i <= ulen - bp)%Z |- _ => rename i into ii; rename H into Ii0; rename H2 into Ii1 end. rename ii into i.

    assert (CONT : forall r1 r5 r6 r7 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r23 r24 r27 r28 r29 r30 r31 m' cs0,
      base m' -> rw_cells rsegs m' q [CB 296 jA] -> FRB m' -> stk rsegs m' lo (q - 112) -> stk rsegs m' (q - 112) q ->
      rw_cells rsegs m' O cs0 -> cells_size cs0 = 32%nat ->
      rw_cells rsegs m' (O + 32) [C8 (Z_to_bv 64 (U + bp)); C8 (Z_to_bv 64 i)] -> rw_cells rsegs m' (O + 48) [C8 oc; C8 od] -> rw_cells rsegs m' (O + 64) [CB 152 j4] ->
      evt rsegs POST (MS (mkR r1 spw gp tp r5 r6 r7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 i) r11 r12 r13 r14 r15 r16 r17
                              (Z_to_bv 64 U) r19 r20 r21 r22 r23 r24 (Z_to_bv 64 1) (Z_to_bv 64 bp) r27 r28 r29 r30 r31) F (Z_to_bv 64 0x16dac) fc None m' (seg_rom rsegs))).
    { intros until cs0. intros B' FRA' FRB' ST1' ST2' O0 L0 O1 O2 O3. clear USTR ERR GOT CAN GIFP GIFV MU WM FRA FRBm OUT0 FRG HP ST1 ST2 PQ. open_base B'.
      pwalk_to 0x16df0%Z. if_cases K0; zify_cond K0.
      {   pwalk_to 0x16df8%Z. eapply frag_null; try eassumption; try reflexivity. close_base. }
      destruct (nth_U (bp + i) ltac:(lia)) as [b Hb]. pose proof (byte_range b) as BR.
      pose proof (u8ro_read rsegs m' U _ (bp + i) b (Z_to_bv 64 (U + (bp + i))) USTR Hb ltac:(lia) eq_refl) as RD.
      pwalk_to 0x16df0%Z. if_cases K1; zify_cond K1.
      {   pwalk_to 0x16df8%Z. eapply frag_null; try eassumption; try reflexivity. close_base. }
      pwalk_to 0x16df0%Z. step.
      pose proof (bytes_at_drop m' U _ (Z.to_nat (bp + i + 1)) USTR ltac:(rewrite app_length; cbn [length]; lia)) as SUF. rewrite Z2Nat.id in SUF by lia.
      callq (parse_uric_spec (U + (bp + i + 1))%Z (O + 48)%Z (ulen - (bp + i + 1))%Z (skipn (Z.to_nat (bp + i + 1)) (ustr ++ Z_to_bv 8 0 :: slack)) oc od).
      all: side (rewrite ?QSP, ?skipn_length, ?UL; first [exact SUF | exact O2 | exact ST2' | exact MI | reflexivity | (f_equal; lia) | lia]).
      match goal with H : stk _ _ _ q |- _ => rename H into ST3 end.
      match goal with H : rw_cells _ _ (O + 48)%Z _ |- _ => rename H into FRG end.
      pwalk_to 0x16e00%Z. eapply fin; try eassumption; try reflexivity. close_base. }
    pwalk_to 0x16dac%Z. if_cases K0; zify_cond K0.
    {   eapply CONT; try eassumption; try reflexivity. close_base. }
    destruct (nth_U bp ltac:(lia)) as [b Hb]. pose proof (byte_range b) as BR.
    pose proof (u8ro_read rsegs _ U _ bp b (Z_to_bv 64 (U + bp)) USTR Hb ltac:(lia) eq_refl) as RD.
    pwalk_to 0x16dac%Z. if_cases K1; zify_cond K1.
    {   eapply CONT; try eassumption; try reflexivity. close_base. }
    pwalk_to 0x16dac%Z. eapply CONT; try eassumption; try reflexivity. close_base.
  Qed.
End WALK.
