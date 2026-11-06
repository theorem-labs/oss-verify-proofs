From Stdlib Require Import ZArith List Lia Bool Arith Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar PsDecStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjIn PjStruct ReaderRes ReaderKB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import parse_string_loops ps_seg_utail put_utf8_c ps_loop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require hex4_c.
Import ListNotations.
Open Scope Z_scope.

Lemma pss_split : forall m A n j cs, rw_cells rsegs m A (CB n j :: cs) ->
  rw_cells rsegs m A [CB n j] /\ rw_cells rsegs m (A + Z.of_nat n) cs.
Proof.
  intros m A n j cs [[[Hj Hwf] Hb] (W0 & W1 & W)].
  cbn [cells_bytes cbytes cells_size csize] in Hb, W1, W.
  apply bytes_at_app in Hb as [Hb1 Hb2]. rewrite Hj in Hb2.
  pose proof (cells_bytes_length cs Hwf) as HL.
  split.
  - split; [split; [split; [exact Hj | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb1]|].
    cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
  - split; [split; [exact Hwf | exact Hb2]|]. split; [lia|]. split; [lia|].
    intros i Hi. replace (A + Z.of_nat n + i) with (A + (Z.of_nat n + i)) by lia. apply W. lia.
Qed.

Lemma pss_epi : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z)
    (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
  0 <= S -> S + 144 < 2 ^ 64 ->
  rw_cells rsegs m (S + 40)
    [C8 v27; C8 v26; C8 v25; C8 v24; C8 v23; C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 v1] ->
  evt rsegs (fun ms' => ms' = MS (mkR v1 (Z_to_bv 64 (S + 144)) gp tp t0 t1 t2 v8 v9 s1 a1 a2 a3 a4 a5 a6 a7
                                   v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 t3 t4 t5 t6) F (ret_pc v1) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x168dc) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S
    v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 HS0 HS1 FR.
  do 16 step. apply evt_done. reflexivity.
Qed.

Lemma pss_tail : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z)
    (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
  0 <= S -> S + 144 < 2 ^ 64 ->
  rw_cells rsegs m (S + 40)
    [C8 v27; C8 v26; C8 v25; C8 v24; C8 v23; C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 v1] ->
  evt rsegs (fun ms' => ms' = MS (mkR v1 (Z_to_bv 64 (S + 144)) gp tp t0 t1 t2 v8 v9 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                   v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 t3 t4 t5 t6) F (ret_pc v1) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x168d8) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S
    v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 HS0 HS1 FR.
  step. apply pss_epi; assumption.
Qed.

Definition pss_pro_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q text p : Z) (tb : list byte) (ms' : machine_state) : Prop :=
  exists (m' : word -> option byte) (junk : list byte),
    munch [(bv_unsigned sp + -144, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    rw_cells rsegs m' (bv_unsigned sp + -144) [CB 40 junk] /\
    rw_cells rsegs m' (bv_unsigned sp + -144 + 40)
      [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    match scan (rest_at tb text (p + 1)) with
    | None => exists a1' a2' a3' : word,
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -144 + 144)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3'
                      a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs)
    | Some Q => exists a2' a3' : word,
        ms' = MS (mkR (Z_to_bv 64 0x16668) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1
                      (Z_to_bv 64 (Z.of_nat Q + 1)) (Z_to_bv 64 34) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                      (Z_to_bv 64 (p + 1)) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15454) fc None m' (seg_rom rsegs)
    end.

Local Ltac weq := first [ reflexivity | f_equal; rewrite ?unsigned_lit by lia; lia ].

Lemma pss_pro : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q text len p d : Z) (tb : list byte),
  a0 = Z_to_bv 64 q -> pj_in_ok rsegs m q text len p d tb -> p < text + len ->
  stk rsegs m (bv_unsigned sp + -144) (bv_unsigned sp) -> 144 <= bv_unsigned sp ->
  (q + 24 <= bv_unsigned sp + -144 \/ bv_unsigned sp <= q) ->
  (text + len <= bv_unsigned sp + -144 \/ bv_unsigned sp <= text) ->
  evt rsegs (pss_pro_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q text p tb)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x165e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q text len p d tb
    E0 PJ HP ST SP DQ DT.
  pose proof (pj_in_ok_bounds rsegs _ _ _ _ _ _ _ PJ) as (B1 & B2 & B3 & B4 & B5 & B6 & TL & B8 & B9).
  destruct PJ as (BQ & BE & _ & _ & _ & _ & _ & _ & _ & TB & _ & _).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2 ^ 64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  subst a0.
  carve_frame 144%nat ST. clear ST.
  do 14 step.
  pose proof (psu_rd8 _ _ _ BQ) as RQ. pose proof (psu_rd8 _ _ _ BE) as RE.
  do 4 step.
  eapply evt_cut.
  { apply ps_scan with (text := text) (len := len) (s := p + 1) (tb := tb); [weq | weq | exact TB | exact TL | lia | lia]. }
  intros ms' Hms. cbv beta in Hms.
  destruct (pss_split _ _ _ _ _ FR) as [FR1 FR2]. change (Z.of_nat 40) with 40 in FR2.
  destruct (scan (rest_at tb text (p + 1))) as [Q|] eqn:HQ.
  - destruct Hms as [a3' ->].
    pose proof (pslp_lt tb text len (p + 1) Q TL ltac:(lia) HQ) as HQL.
    pose proof (scan_quote _ _ HQ) as [HQ1 _].
    pose proof (pslp_rest_len tb text len (p + 1) TL ltac:(lia)) as HRL.
    do 3 step.
    apply evt_done. unfold pss_pro_post. do 2 eexists.
    split; [exact MU|]. split; [exact WM|]. split; [exact FR1|]. split; [exact FR2|].
    rewrite HQ. do 2 eexists.
    rewrite (unsigned_lit (p + 1 + Z.of_nat Q)), (unsigned_lit (p + 1)) by lia.
    replace (p + 1 + Z.of_nat Q - (p + 1) + 1) with (Z.of_nat Q + 1) by lia. reflexivity.
  - destruct Hms as (a1' & a2' & a3' & ->).
    step.
    eapply evt_mono; [apply pss_epi; [lia | lia | exact FR2]|].
    intros ms' ->. unfold pss_pro_post. do 2 eexists.
    split; [exact MU|]. split; [exact WM|]. split; [exact FR1|]. split; [exact FR2|].
    rewrite HQ. do 3 eexists. reflexivity.
Qed.

Local Ltac cf H := zify_cond H; rewrite ?unsigned_lit_wrap in H; rewrite ?Z.mod_small in H by lia.

Lemma pss_null : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z)
    (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
  a0 = Z_to_bv 64 0 -> 0 <= S -> S + 144 < 2 ^ 64 ->
  rw_cells rsegs m (S + 40)
    [C8 v27; C8 v26; C8 v25; C8 v24; C8 v23; C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 v1] ->
  evt rsegs (fun ms' => ms' = MS (mkR v1 (Z_to_bv 64 (S + 144)) gp tp t0 t1 t2 v8 v9 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                   v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 t3 t4 t5 t6) F (ret_pc v1) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16668) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S
    v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 E0 HS0 HS1 FR.
  subst a0. step. if_true. apply pss_tail; assumption.
Qed.

Lemma pss_cells5 : forall m A j0 j1 x y z, rw_cells rsegs m A [CB 8 j0; C8 x; C8 y; C8 z; CB 8 j1] ->
  bytes_at rsegs m (A + 8) (le8 x) /\ bytes_at rsegs m (A + 16) (le8 y) /\ bytes_at rsegs m (A + 24) (le8 z) /\
  wr_at rsegs m (A + 36) 4.
Proof.
  intros m A j0 j1 x y z [[Hwf Hb] (W1 & W2 & W3)].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (Hj & _ & _ & _ & Hj1 & _).
  cbn [cells_bytes cbytes cells_size csize] in Hb, W2, W3.
  apply bytes_at_app in Hb as [_ Hb]. rewrite Hj in Hb.
  apply bytes_at_app in Hb as [Hx Hb]. rewrite length_le8 in Hb.
  apply bytes_at_app in Hb as [Hy Hb]. rewrite length_le8 in Hb.
  apply bytes_at_app in Hb as [Hz _].
  split; [exact Hx|]. split; [replace (A + 16) with (A + Z.of_nat 8 + Z.of_nat 8) by lia; exact Hy|].
  split; [replace (A + 24) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia; exact Hz|].
  split; [lia|]. split; [lia|]. intros i Hi. replace (A + 36 + i) with (A + (36 + i)) by lia. apply W3. lia.
Qed.

Definition pss_body_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (q text p S a : Z) (Q : nat) (tb : list byte)
    (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word) (ms' : machine_state) : Prop :=
  (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (ws : list byte) (m' : word -> option byte),
     ms' = MS (mkR v1 (Z_to_bv 64 (S + 144)) gp tp t0' t1' t2' v8 v9 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7'
                   v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 t3' t4' t5' t6') F (ret_pc v1) fc None m' (seg_rom rsegs) /\
     decode (rest_at tb text (p + 1)) = Some (zb ws, rest_at tb text (p + 1 + Z.of_nat Q + 1)) /\
     (length ws <= Q)%nat /\
     bytes_at rsegs m' a (ws ++ [Z_to_bv 8 0]) /\
     bytes_at rsegs m' q (le8 (Z_to_bv 64 (p + 1 + Z.of_nat Q + 1))) /\
     munch [(S, S + 40); (a, a + Z.of_nat Q + 1); (q, q + 8)] m m' /\ wmono rsegs m m')
  \/
  (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
          (m' : word -> option byte),
     ms' = MS (mkR (Z_to_bv 64 0x168d8) (Z_to_bv 64 S) gp tp t0' t1' t2' (Z_to_bv 64 q) (Z_to_bv 64 a) (Z_to_bv 64 a)
                   a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
              F (Z_to_bv 64 0x157f8) fc None m' (seg_rom rsegs) /\
     decode (rest_at tb text (p + 1)) = None /\
     munch [(S, S + 40); (a, a + Z.of_nat Q + 1)] m m' /\ wmono rsegs m m').

Lemma pss_body : put_utf8_contract -> hex4_c.hex4_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q text len p d S a : Z) (Q : nat) (tb junk : list byte)
    (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
  sp = Z_to_bv 64 S -> s0 = Z_to_bv 64 q -> s8 = Z_to_bv 64 (p + 1) -> a0 = Z_to_bv 64 a ->
  pj_in_ok rsegs m q text len p d tb -> p < text + len -> scan (rest_at tb text (p + 1)) = Some Q ->
  rw_cells rsegs m S [CB 40 junk] ->
  rw_cells rsegs m (S + 40)
    [C8 v27; C8 v26; C8 v25; C8 v24; C8 v23; C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 v1] ->
  wr_at rsegs m a (Z.of_nat Q + 1) ->
  0 <= S -> S mod 16 = 0 -> S + 144 <= q -> 0 < a -> a + Z.of_nat Q + 1 <= S ->
  (a + Z.of_nat Q + 1 <= text \/ text + len <= a) -> (S + 144 <= text \/ text + len <= S) ->
  evt rsegs (pss_body_post gp tp F fc m q text p S a Q tb v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16668) fc None m (seg_rom rsegs)).
Proof.
  intros PU HX ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    q text len p d S a Q tb junk v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27
    Esp Es0 Es8 Ea0 PJ HP HQ FRL FRS HWA HS0 HS16 HSQ Ha0 HaS DAT DST.
  pose proof (pj_in_ok_bounds rsegs _ _ _ _ _ _ _ PJ) as (B1 & B2 & B3 & B4 & B5 & B6 & TL & B8 & B9).
  destruct PJ as (BQ & BE & BD & WQ & _ & _ & _ & _ & _ & TB & _ & _).
  pose proof (scan_quote _ _ HQ) as [HQ1 _].
  pose proof (pslp_rest_len tb text len (p + 1) TL ltac:(lia)) as HRL.
  pose proof (munch_refl [(S, S + 40); (a, a + Z.of_nat Q + 1)] m) as MU2.
  pose proof (munch_refl [(S, S + 40); (a, a + Z.of_nat Q + 1); (q, q + 8)] m) as MU3.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (psu_rd8 _ _ _ BE) as RE.
  subst sp s0 s8 a0.
  step. if_cases HC; [exfalso; cf HC; lia|].
  step. step. clear RE. step. if_cases HC2; [exfalso; cf HC2; lia|].
  do 29 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mL end.
  destruct (pss_cells5 _ _ _ _ _ _ _ FRL) as (C8a & C16a & C24a & W36).
  lazymatch type of C8a with bytes_at _ _ _ (le8 ?w) =>
    replace w with (Z_to_bv 64 0xFFFFFFFFFCA02400) in C8a by (apply bv_eq; vm_compute; reflexivity) end.
  lazymatch type of C16a with bytes_at _ _ _ (le8 ?w) =>
    replace w with (Z_to_bv 64 0xDC00) in C16a by (apply bv_eq; vm_compute; reflexivity) end.
  lazymatch type of C24a with bytes_at _ _ _ (le8 ?w) =>
    replace w with (Z_to_bv 64 0xD800) in C24a by (apply bv_eq; vm_compute; reflexivity) end.
  eapply evt_cut.
  { eapply ps_loop with (m0 := mL) (tb := tb) (text := text) (len := len) (s := p + 1) (st := q) (S := S) (O0 := a)
      (P := p + 1) (O := a) (Q := Q).
    all: try first [exact PU | exact HX | reflexivity].
    unfold ps_inv.
    split; [exact TL|]. split; [lia|]. split; [lia|].
    split; [exact TB|]. split; [exact BE|].
    split; [exact C8a|]. split; [exact C16a|]. split; [exact C24a|].
    split; [exact HWA|]. split; [exact W36|].
    split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [lia|].
    split; [rewrite HQ; f_equal; lia|].
    split; [apply munch_refl|]. split; [apply wmono_refl|].
    exists []. split; [apply bytes_at_nil; lia|]. split; [cbn [length Z.of_nat]; lia|].
    split; [cbn [length Z.of_nat]; lia|].
    unfold zb. cbn [map]. rewrite psd_emit_nil. reflexivity. }
  intros ms' [(a2' & a3' & s10' & ws & m' & -> & HD & HLw & HBw & MU' & WM') |
              (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s8' & s10' &
               t3' & t4' & t5' & t6' & m' & -> & HD & MU' & WM')].
  - assert (HWA' : wr_at rsegs m' a (Z.of_nat Q + 1)) by exact (wr_at_transport rsegs mL m' _ _ HWA WM').
    assert (WQ' : wr_at rsegs m' q 24) by exact (wr_at_transport rsegs mL m' _ _ WQ WM').
    assert (BQ' : bytes_at rsegs m' q (le8 (Z_to_bv 64 p)))
      by (apply (bytes_at_transport rsegs _ mL m' _ _ BQ MU'); cbn [disjoint_from]; rewrite length_le8; lia).
    assert (FRS' : rw_cells rsegs m' (S + 40)
      [C8 v27; C8 v26; C8 v25; C8 v24; C8 v23; C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 v1])
      by (apply (rw_cells_transport rsegs _ mL m' _ _ FRS MU' WM'); cbn [disjoint_from cells_size csize]; lia).
    pose proof (wr_at_store_ok rsegs m' a (Z.of_nat Q + 1) (Z.of_nat (length ws)) 1 HWA' ltac:(lia) ltac:(lia)) as HS1.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      replace bs with [Z_to_bv 8 0] by (vm_compute; reflexivity) end.
    lazymatch goal with |- evt ?sg ?Qp (MS ?R ?F0 ?pc ?fc0 ?rv (write_to_mem ?m0 _ ?bs) ?ro) =>
      change (evt sg Qp (MS R F0 pc fc0 rv (write_to_mem m0 (wa (a + Z.of_nat (length ws))) bs) ro)) end.
    assert (WQ1 : wr_at rsegs (write_to_mem m' (wa (a + Z.of_nat (length ws))) [Z_to_bv 8 0]) q 24)
      by (apply wr_at_write; exact WQ').
    pose proof (wr_at_store_ok rsegs _ q 24 0 8 WQ1 ltac:(lia) ltac:(lia)) as HS2. rewrite Z.add_0_r in HS2.
    step. step.
    try rewrite (unsigned_lit (p + 1 + Z.of_nat Q + 1)) by lia. try rewrite le8_lit by lia.
    lazymatch goal with |- evt ?sg ?Qp (MS ?R ?F0 ?pc ?fc0 ?rv (write_to_mem ?m0 _ ?bs) ?ro) =>
      change (evt sg Qp (MS R F0 pc fc0 rv (write_to_mem m0 (wa q) bs) ro)) end.
    step.
    set (mF := write_to_mem (write_to_mem m' (wa (a + Z.of_nat (length ws))) [Z_to_bv 8 0]) (wa q)
                 (le8 (Z_to_bv 64 (p + 1 + Z.of_nat Q + 1)))).
    assert (FRF : rw_cells rsegs mF (S + 40)
      [C8 v27; C8 v26; C8 v25; C8 v24; C8 v23; C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 v1]).
    { unfold mF. apply rw_cells_frame; [apply rw_cells_frame; [exact FRS' | lia | simpl_sizes; lia | simpl_sizes; lia]
        | lia | simpl_sizes; lia | simpl_sizes; lia]. }
    eapply evt_mono; [apply pss_epi; [lia | lia | exact FRF] |].
    intros ms' ->. left. do 14 eexists. exists ws, mF. split; [reflexivity|].
    split; [exact HD|]. split; [exact HLw|].
    split.
    { unfold mF. apply bytes_at_write_other; [apply pslp_push1; [exact HBw | lia | lia] | lia | rewrite length_le8; lia |].
      rewrite length_app, length_le8. cbn [length]. lia. }
    split; [unfold mF; apply bytes_at_write_same; [lia | rewrite length_le8; lia]|].
    split; [|unfold mF; apply wmono_write, wmono_write; exact (wmono_trans rsegs _ _ _ WM WM')].
    unfold mF. apply munch_write; [apply munch_write | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; lia].
    + apply (munch_trans _ m mL m' MU3). eapply munch_weaken; [|exact MU']. intros x Hx; cbn [outside] in Hx |- *; lia.
    + lia.
    + cbn [length Z.of_nat Pos.of_succ_nat]. lia.
    + cbn [inside length Z.of_nat Pos.of_succ_nat]. lia.
  - step. step.
    apply evt_done. right. do 24 eexists. exists m'. split; [reflexivity|]. split; [exact HD|].
    split; [|exact (wmono_trans rsegs _ _ _ WM WM')].
    apply (munch_trans _ m mL m' MU2). eapply munch_weaken; [|exact MU']. intros x Hx; cbn [outside] in Hx |- *; lia.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK14 YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger fuzz_malloc_c fuzz_free_c parse_string_c.
Local Open Scope Z_scope.

Definition ps_e0 (a n x : Z) : Prop := 0 < n /\ (alloc_statics x \/ (a <> 0 /\ a - 16 <= x < a + n)).

Lemma ps_e0_sub : forall q a n x, ps_e0 a n x -> parse_string_writes q a n x.
Proof. intros q a n x (H1 & H2). unfold parse_string_writes. split; [exact H1 | tauto]. Qed.

Lemma ps_pw_app : forall (R : Z * Z -> Z * Z -> Prop) b1 y b2 x, pairwise R (b1 ++ y :: b2) -> In x (b1 ++ b2) ->
  R x y \/ R y x.
Proof.
  induction b1 as [|z b1 IH]; intros y b2 x H Hx; cbn in H, Hx.
  - destruct H as [H _]. right. apply H. exact Hx.
  - destruct H as [Hz H]. destruct Hx as [<- | Hx].
    + left. apply Hz. apply in_or_app. right. left. reflexivity.
    + exact (IH y b2 x H Hx).
Qed.

Lemma ps_zb_rng : forall l : list byte, Forall (fun b => 0 <= b < 256) (zb l).
Proof.
  intros l. unfold zb. rewrite Forall_forall. intros c Hc. apply in_map_iff in Hc as (bt & <- & _).
  pose proof (bv_unsigned_in_range 8 bt) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma ps_zb_map : forall l : list byte, map (Z_to_bv 8) (zb l) = l.
Proof.
  intros l. unfold zb. rewrite map_map.
  rewrite (map_ext _ (fun b => b)) by (intros bt; apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small;
    apply bv_unsigned_in_range).
  apply map_id.
Qed.

Lemma ps_bytes_keep : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (E (Z.of_nat i) ltac:(lia)) as Ei.
  transitivity (mbyte rsegs m' (a + Z.of_nat i)); [reflexivity|]. rewrite Ei. exact (H i Hi).
Qed.

Lemma ps_pin_keep : forall m m' q text len p d tb, pj_in_ok rsegs m q text len p d tb ->
  (forall i, 0 <= i < 24 ->
     mbyte rsegs m' (q + i) = mbyte rsegs m (q + i) /\ (writable_at rsegs m (q + i) -> writable_at rsegs m' (q + i))) ->
  (forall i, 0 <= i < len -> mbyte rsegs m' (text + i) = mbyte rsegs m (text + i)) ->
  pj_in_ok rsegs m' q text len p d tb.
Proof.
  intros m m' q text len p d tb (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) KQ KT.
  refine (conj _ (conj _ (conj _ (conj _ (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj _ (conj H11 H12))))))))))).
  - apply (ps_bytes_keep m); [exact H1|]. intros i Hi. rewrite length_le8 in Hi. exact (proj1 (KQ i ltac:(lia))).
  - apply (ps_bytes_keep m); [exact H2|]. intros i Hi. rewrite length_le8 in Hi.
    replace (q + 8 + i) with (q + (8 + i)) by lia. exact (proj1 (KQ (8 + i) ltac:(lia))).
  - apply (ps_bytes_keep m); [exact H3|]. intros i Hi. rewrite length_le4 in Hi.
    replace (q + 16 + i) with (q + (16 + i)) by lia. exact (proj1 (KQ (16 + i) ltac:(lia))).
  - destruct H4 as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi.
    exact (proj2 (KQ i Hi) (W3 i Hi)).
  - apply (ps_bytes_keep m); [exact H10|]. intros i Hi. rewrite H9 in Hi. exact (KT i Hi).
Qed.

Lemma ps_ro_munch : forall W m m', MemNorm.ro_agree rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> find_segment rsegs x 1 = None) -> MemNorm.ro_agree rsegs m'.
Proof.
  intros W m m' H MU HW a E.
  destruct (rk_outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite <- (H a E). unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.mrd. rewrite (MU a O). reflexivity.
  - exfalso. pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
    unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.ro_addr in E. rewrite (HW _ R O) in E. discriminate.
Qed.

Lemma ps_mb : forall segs W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  mbyte segs m' a = mbyte segs m a /\ (writable_at segs m a <-> writable_at segs m' a).
Proof.
  intros segs W m m' a MU Ha Ho. split; [exact (MemNorm.mbyte_munch segs W m m' a MU Ha Ho) | exact (rk_writable_munch segs W m m' a MU Ha Ho)].
Qed.

Lemma ps_final_regs : forall {regs R' : bvmap 5 word}
    {gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word} {sb v : Z},
  xregs_eqv (mkR (reg_get regs 1) (Z_to_bv 64 (sb + 144)) gp tp x5 x6 x7 (reg_get regs 8) (reg_get regs 9) (Z_to_bv 64 v)
     x11 x12 x13 x14 x15 x16 x17 (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
     (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) x28 x29 x30 x31) R' ->
  sb + 144 = spZ regs -> gp = reg_get regs 3 -> tp = reg_get regs 4 ->
  regs_preserved regs R' /\ getr R' 10 = Z_to_bv 64 v.
Proof.
  intros regs R' gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 sb v XR HS -> ->.
  split; [|rewrite (rk_getr_eqv _ _ XR); reflexivity].
  intros r Hr. rewrite (rk_getr_eqv _ _ XR). unfold callee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
               r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    try reflexivity.
  change (Z_to_bv 64 (sb + 144) = getr regs 2). rewrite HS. exact (Z_to_bv_lit_self (getr regs 2)).
Qed.

Local Ltac outs := cbn [outside]; repeat split; lia.
Local Ltac djs := cbn [disjoint_from]; repeat split; lia.

Section PSH.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis PSAX : YL01.AllocExtra B (aa_MR API).
Hypothesis PSCTX : ctx_owned B API.
Hypothesis PSMAL : fuzz_malloc_contract B API RF.
Hypothesis PSFREE : fuzz_free_contract B API RF.
Hypothesis PSPU : put_utf8_contract.
Hypothesis PSHX : hex4_c.hex4_contract.

Lemma ps_call : forall K2 L A regs mem md (E2 : Z -> Prop) L' A' regs' mem' md' (g : Z * Z),
  aa_MR API L A mem md ->
  call_post_k B (aa_MR API) K2 L A regs mem md E2 L' A' regs' mem' md' ->
  (st_init_done A = true -> st_init_done A' = true) ->
  (st_init_done A' = false -> forall i, 0 <= i < 8 ->
     mbyte (ms_segs B) mem' (ms_libc B + 8 + i) = mbyte (ms_segs B) mem (ms_libc B + 8 + i)) ->
  (length (st_regions A) <= length (st_regions A'))%nat ->
  ublocks_kept L A A' g ->
  rpost B API K2 L A regs mem md E2 (fun a k => (a, k) = g) L' A' regs' mem' md'.
Proof.
  intros K2 L A regs mem md E2 L' A' regs' mem' md' g HM0 (M & W & Bd & Y & PA & RP & D & FR & KB & SC) HI X G U.
  split; [exact M|]. split; [exact W|]. split; [exact Bd|]. split; [exact Y|]. split; [exact HI|]. split; [exact X|].
  split; [exact G|].
  split; [intros p n Hp Hg; exact (U p n Hp Hg)|].
  split; [exact PA|]. split; [exact RP|]. split; [exact D|].
  split.
  { intros a Ha Hs He. apply FR; [left; exact Ha | | | exact Hs | exact He].
    - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ HM0 Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ M Ho). lia. }
  split.
  { intros a Ha NO Hs He. apply FR; [right; exact Ha | exact (NO _ _ _ _ HM0) | exact (NO _ _ _ _ M) | exact Hs | exact He]. }
  split; [intros p n i Hp Hp' Hi _; exact (KB p n i Hp Hp' Hi)|].
  exact SC.
Qed.

Lemma ps_rp_mono : forall K L A regs mem md (E E' : Z -> Prop) gone L' A' regs' mem' md',
  rpost B API K L A regs mem md E gone L' A' regs' mem' md' -> (forall x, E x -> E' x) ->
  rpost B API K L A regs mem md E' gone L' A' regs' mem' md'.
Proof.
  intros K L A regs mem md E E' gone L' A' regs' mem' md' (M & W & Bd & Y & HI & X & G & UB & PA & RP & D & H & IM & Kb & C) HE.
  refine (conj M (conj W (conj Bd (conj Y (conj HI (conj X (conj G (conj UB (conj PA (conj RP (conj D
    (conj _ (conj _ (conj _ C)))))))))))))).
  - intros a Ha Hs He. apply H; [exact Ha | exact Hs | intros E1; apply He, HE, E1].
  - intros a Ha Hn Hs He. apply IM; [exact Ha | exact Hn | exact Hs | intros E1; apply He, HE, E1].
  - intros p n i Hp Hp' Hi He. apply (Kb p n i); [exact Hp | exact Hp' | exact Hi | intros E1; apply He, HE, E1].
Qed.

Lemma ps_txt_rp : forall K L A regs mem md (E : Z -> Prop) L' A' regs' mem' md' text len,
  rpost B API K L A regs mem md E (fun _ _ => False) L' A' regs' mem' md' ->
  (YM05.alloc_ceiling <= text \/
   (forall i, 0 <= i < len -> in_img B (text + i) /\
      (forall L0 A0 mem0 md0, aa_MR API L0 A0 mem0 md0 -> ~ owned B L0 A0 (text + i))) \/
   (exists p0 k0, In (p0, k0) (user_blocks A) /\ ptr_addr L p0 <= text /\ text + len <= ptr_addr L p0 + k0)) ->
  (forall i, 0 <= i < len -> ~ scratch_k B K regs (text + i) /\ ~ E (text + i)) ->
  0 <= text -> text + len <= 2 ^ 64 ->
  forall i, 0 <= i < len -> mbyte (ms_segs B) mem' (text + i) = mbyte (ms_segs B) mem (text + i).
Proof.
  intros K L A regs mem md E L' A' regs' mem' md' text len
    (M & W & Bd & Y & HI & X & G & UB & PA & RP & D & H & IM & Kb & C) TXL OK T0 T1 i Hi.
  destruct (OK i Hi) as [Ns Ne].
  destruct TXL as [Hs | [Him | (p0 & k0 & Hp & Ha & Hk)]].
  - exact (proj1 (H (text + i) ltac:(lia) Ns Ne)).
  - destruct (Him i Hi) as [Hm NO]. exact (proj1 (IM (text + i) Hm NO Ns Ne)).
  - assert (Hp' : In (p0, k0) (user_blocks A')) by (apply UB; [exact Hp | intros F; exact F]).
    replace (text + i) with (ptr_addr L p0 + (text + i - ptr_addr L p0)) by lia.
    apply (Kb p0 k0 (text + i - ptr_addr L p0)); [exact Hp | exact Hp' | lia |].
    replace (ptr_addr L p0 + (text + i - ptr_addr L p0)) with (text + i) by lia. exact Ne.
Qed.

Lemma ps_main : parse_string_contract B API RF.
Proof using All.
  unfold parse_string_contract.
  intros L A regs mem md Lam peak cnt fail b q text len p d tb ENV LED RES R10 PIN HP HQT SPQ AUXQ TXT DJ CNT ROOM.
  pose proof ENV as (_ & TP & ERR & GG & GD & PRE & SP47 & GTOP & FRM & RDC).
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & HAUX).
  destruct (mr_model B _ (aa_laws API) L A mem md HM) as (Hh & Hl & _).
  pose proof RDC as (RO & RGG & RGD).
  pose proof rk_ceil as HCEIL.
  pose proof (zr_word (getr regs 2)) as Rsp. unfold inr64 in Rsp. change (bv_unsigned (getr regs 2)) with (spZ regs) in Rsp.
  assert (KV : PARSE_STRING_K = 8368) by (vm_compute; reflexivity).
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ PIN) as (QB0 & QB1 & TX0 & TXP & TXE & QTX & TL & Q8 & D32).
  cbn [Frame.disjoint_from] in DJ.
  pose proof LED as (_ & _ & (CN0 & CN1) & _).
  destruct TXT as (TXL0 & TXN).
  assert (STL : forall a, alloc_statics a -> 0 <= a < 2 ^ 33)
    by (intros a Ha; unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha; lia).
  assert (OWL : forall L0 A0 mem0 md0 x, aa_MR API L0 A0 mem0 md0 -> owned B L0 A0 x -> 0 <= x < YM05.alloc_ceiling)
    by (intros L0 A0 mem0 md0 x HM0 Ho; exact (mr_owned_low B _ (aa_laws API) L0 A0 mem0 md0 x HM0 Ho)).
  assert (ERRL : 0 <= errno_addr B /\ errno_addr B + 4 <= 2 ^ 33) by (rewrite ERR; unfold strtod_c.STRTOD_ERRNO; lia).
  assert (LB0 : 0 <= ms_libc B + 8 /\ ms_libc B + 16 <= YM05.alloc_ceiling).
  { pose proof (OWL _ _ _ _ (ms_libc B + 8) HM ltac:(right; unfold static_owned; right; right; left; lia)).
    pose proof (OWL _ _ _ _ (ms_libc B + 15) HM ltac:(right; unfold static_owned; right; right; left; lia)). lia. }
  assert (TXL : YM05.alloc_ceiling <= text \/
                (forall i, 0 <= i < len -> in_img B (text + i) /\
                   (forall L0 A0 mem0 md0, aa_MR API L0 A0 mem0 md0 -> ~ owned B L0 A0 (text + i))) \/
                (exists p0 k0, In (p0, k0) (user_blocks A) /\ ptr_addr L p0 <= text /\ text + len <= ptr_addr L p0 + k0)).
  { destruct TXL0 as [Hs | [Him | [(a0 & k0 & Hb & _ & Ha & Hk) | (a0 & k0 & Hl0 & Ha & Hk)]]].
    - left. lia.
    - right; left. intros i Hi. split; [exact (Him i Hi)|].
      intros L0 A0 mem0 md0 HM0 [Ho|Ho].
      + pose proof (YL01.ax_img PSAX L0 A0 mem0 md0 (text + i) HM0 (Him i Hi) Ho) as HC.
        apply (proj1 (TXN i Hi)). exact (PSCTX L A mem md (text + i) HM HC).
      + apply (proj1 (TXN i Hi)). right. exact Ho.
    - right; right. destruct (rk_blk_user L A a0 k0 Hb) as (p0 & Hp0 & Ep0). exists p0, k0. rewrite Ep0. auto.
    - right; right. pose proof LED as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF. unfold lin in Hl0.
      destruct (LF _ Hl0) as (LK & LIn & _). cbn [fst snd] in LK, LIn.
      destruct (rk_blk_user L A _ _ LIn) as (p0 & Hp0 & Ep0). exists p0, (k0 + 16). rewrite Ep0. split; [exact Hp0 | lia]. }
  assert (ES : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  rewrite SEG in PIN, RO, HWS.
  rewrite SEG.
  eapply rk_kA; [exact Hh | exact Hl | |].
  { unfold mkR_of, PARSE_STRING.
    eapply pss_pro with (q := q) (text := text) (len := len) (p := p) (d := d) (tb := tb).
    - exact R10.
    - exact PIN.
    - exact HP.
    - rewrite ES. apply rk_stk_of_wr; [lia | lia |]. intros a Ha. apply HWS. lia.
    - rewrite ES. lia.
    - rewrite ES. right. exact SPQ.
    - rewrite ES. lia. }
  intros ms1 (can1 & PP1 & EQV1). unfold pss_pro_post in PP1.
  destruct PP1 as (m1 & junk & MU1 & WM1 & FRJ & FRS & ARM1).
  rewrite ES in MU1, FRJ, FRS, ARM1.
  assert (WM1' : wmono (ms_segs B) mem m1) by (rewrite SEG; exact WM1).
  assert (KEEP1 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs + -144 <= x < spZ regs) ->
                    mbyte (ms_segs B) m1 x = mbyte (ms_segs B) mem x).
  { intros x Hx Ho. apply (MemNorm.mbyte_munch _ _ _ _ _ MU1); [exact Hx|]. cbn [outside]. split; [exact Ho | exact I]. }
  assert (HM1 : aa_MR API L A m1 md).
  { apply (rk_MR_A SEG L A mem m1 md _ HM MU1 WM1').
    - intros x Ho. pose proof (OWL _ _ _ _ x HM Ho). outs.
    - intros x Hx Ho. cbn [outside] in Ho. intros Hi. pose proof (rk_img_bound SEG x Hi). lia. }
  assert (LED1 : ledger B L A m1 Lam peak cnt fail).
  { apply (rk_ledger_keep L A mem m1 Lam peak cnt fail LED).
    - intros a Ha. pose proof (STL a Ha). apply KEEP1; lia.
    - intros a k i HI Hi. pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HM LED HI) as (Ra & Rb & _).
      pose proof LED as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF. destruct (LF _ HI) as (Lk & _).
      cbn [fst snd] in Lk. apply KEEP1; lia. }
  assert (RO1 : MemNorm.ro_agree rsegs m1).
  { apply (ps_ro_munch _ mem m1 RO MU1). intros x Hx Ho. apply rk_high_nofs. cbn [outside] in Ho. lia. }
  assert (R1G : forall (E : Z -> Prop) regsF, regs_preserved regs regsF ->
            rpost B API PARSE_STRING_K L A regs mem md E (fun _ _ => False) L A regsF m1 md).
  { intros E regsF RPF.
    apply (rk_of_A SEG PARSE_STRING_K L A regs mem md E m1 [(spZ regs + -144, spZ regs)] regsF HM1 HWF HBD RPF MU1 WM1').
    - intros a [Ha|Ha]; [rewrite SEG; apply HWS; exact Ha | apply HER; exact Ha].
    - intros x Hx Hs He. unfold scratch_k in Hs. outs.
    - intros i Hi. outs.
    - lia.
    - lia.
    - intros p0 n0 i Hp Hi He. destruct (mr_blocks B _ (aa_laws API) L A mem md p0 n0 i HM Hp Hi) as (_ & Bl & Bh & _).
      split; [lia|]. outs. }
  destruct (scan (rest_at tb text (p + 1))) as [Q|] eqn:HQ.
  2: {
    try rewrite HQ in ARM1. destruct ARM1 as (a1' & a2' & a3' & ->).
    destruct (rk_eqv_shape _ _ _ _ _ _ EQV1) as (Ems & XR).
    destruct (ps_final_regs XR ltac:(lia) eq_refl eq_refl) as (RPF & R10F).
    rewrite Ems. apply SR_ret. cbv beta.
    exists L, A, (ms_regs ms1), m1, md, Lam, peak, cnt, fail, b, 0, 0, 0.
    split; [change (reg_get regs 1) with (getr regs 1); rewrite (rk_ret_pc _ HRA); reflexivity|].
    split; [exact (R1G _ _ RPF)|].
    split.
    { split; [rewrite SEG; exact RO1|].
      destruct (YL01.ax_statics PSAX L A m1 md HM1) as (GOT & (g & _ & GW) & _). split; [exact GOT | exists g; exact GW]. }
    split; [exact R10F|]. split; [exact LED1|]. split; [exact RES|].
    do 10 (split; [reflexivity|]).
    apply (pj_in_ok_transport rsegs _ mem m1 q text len p d tb PIN MU1 WM1); djs. }
  try rewrite HQ in ARM1. destruct ARM1 as (a2' & a3' & ->).
  destruct (rk_eqv_shape _ _ _ _ _ _ EQV1) as (Ems & XR1).
  pose proof (scan_quote _ _ HQ) as [HQ1 _].
  pose proof (pslp_rest_len tb text len (p + 1) TL ltac:(lia)) as HRL.
  destruct (ROOM Q eq_refl) as [ROOMQ QB].
  assert (G1 : getr (ms_regs ms1) 1 = Z_to_bv 64 0x16668) by (rewrite (rk_getr_eqv _ _ XR1); reflexivity).
  assert (SP1 : spZ (ms_regs ms1) = spZ regs - 144).
  { change (spZ (ms_regs ms1)) with (bv_unsigned (getr (ms_regs ms1) 2)). rewrite (rk_getr_eqv _ _ XR1).
    change (bv_unsigned (Z_to_bv 64 (spZ regs + -144)) = spZ regs - 144). rewrite unsigned_lit by lia. lia. }
  assert (G10 : getr (ms_regs ms1) 10 = Z_to_bv 64 (Z.of_nat Q + 1)) by (rewrite (rk_getr_eqv _ _ XR1); reflexivity).
  rewrite Ems. rewrite <- SEG.
  change (Z_to_bv 64 0x15454) with (Z_to_bv 64 FUZZ_MALLOC).
  eapply SR_bind.
  { apply (PSMAL L A (ms_regs ms1) m1 md (Z.of_nat Q + 1) b Lam peak cnt fail).
    - apply (KindBGlue.kb_pre_A B API PARSE_STRING_K 144 (ALLOC_STACK + 32) L A regs mem md (ms_regs ms1) m1
               [(spZ regs + -144, spZ regs)] PRE).
      + lia.
      + unfold ALLOC_STACK. lia.
      + unfold ALLOC_STACK. lia.
      + exact SP1.
      + rewrite SP1. replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia. rewrite Z_mod_plus_full. exact H16.
      + rewrite (rk_getr_eqv _ _ XR1). reflexivity.
      + rewrite G1. apply ret_ok_even. vm_compute. reflexivity.
      + exact MU1.
      + exact WM1'.
      + intros x Hx Hs. outs.
      + intros x Hx _. outs.
    - exact G10.
    - lia.
    - exact LED1.
    - rewrite SEG. exact RO1.
    - exact RES.
    - replace (Z.of_nat Q + 1 + 16) with (Z.of_nat Q + 17) by lia. exact ROOMQ.
    - lia. }
  intros c2 (L2 & A2 & regs2 & mem2 & md2 & res & -> & ROA2 & GK2 & INIT2 & AUX2 & CP2 & LEN2 & R102 & KEEP2 & UK2 & _ & ARM2).
  rewrite G1.
  pose proof CP2 as (M2 & WF2 & B2 & Y2 & P2 & RP2r & D2 & FR2 & KB2 & SC2).
  destruct (mr_model B _ (aa_laws API) L2 A2 mem2 md2 M2) as (Hh2 & Hl2 & _).
  assert (RESB : res = 0 \/ (res <> 0 /\ In (res - 16, Z.of_nat Q + 1 + 16) (blocks L2 A2) /\ 4096 <= res - 16 /\
            res - 16 + (Z.of_nat Q + 1 + 16) <= YM05.alloc_ceiling /\
            (forall i, 0 <= i < Z.of_nat Q + 1 + 16 -> ~ in_img B (res - 16 + i)))).
  { destruct ARM2 as [(_ & R0 & _) | (_ & RNZ & _ & _ & _ & RNI & _ & (bb1 & bb2 & EB2 & _) & _)]; [left; exact R0|].
    right. assert (Hin : In (res - 16, Z.of_nat Q + 1 + 16) (blocks L2 A2))
      by (rewrite EB2; apply in_or_app; right; left; reflexivity).
    destruct (rk_blk_facts L2 A2 mem2 md2 _ _ M2 Hin) as (Lo & Hi & _).
    split; [exact RNZ|]. split; [exact Hin|]. split; [lia|]. split; [lia | exact RNI]. }
  assert (RESH : res = 0 \/ res + (Z.of_nat Q + 1) <= YM05.alloc_ceiling) by (destruct RESB as [R0|(_ & _ & _ & Hc & _)]; lia).
  assert (TXNB : forall i, 0 <= i < len -> ~ (res <> 0 /\ res - 16 <= text + i < res + (Z.of_nat Q + 1))).
  { intros i Hi [RNZ Hr].
    destruct ARM2 as [(_ & R0 & _) | (_ & _ & _ & _ & _ & RNI & _ & (bb1 & bb2 & EB2 & EB) & _)]; [lia|].
    destruct TXL as [Hs | [Him | (p0 & k0 & Hp0 & Ha0 & Hk0)]].
    - lia.
    - apply (RNI (text + i - (res - 16))); [lia|]. replace (res - 16 + (text + i - (res - 16))) with (text + i) by lia.
      exact (proj1 (Him i Hi)).
    - pose proof (mr_blocks_disjoint B _ (aa_laws API) _ _ _ _ M2) as PW. rewrite EB2 in PW.
      assert (Hin : In (ptr_addr L p0, k0) (bb1 ++ bb2)) by (rewrite <- EB; exact (rk_blk_of_user L A p0 k0 Hp0)).
      destruct (ps_pw_app _ bb1 _ bb2 _ PW Hin) as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
  assert (TXOK : forall i, 0 <= i < len ->
            ~ scratch_k B PARSE_STRING_K regs (text + i) /\ ~ ps_e0 res (Z.of_nat Q + 1) (text + i)).
  { intros i Hi. destruct (TXN i Hi) as (_ & NS & NE). split.
    - unfold scratch_k. intros [Hs|Hs]; [lia | exact (NE Hs)].
    - unfold ps_e0. intros (_ & [Hs|Hb]); [exact (NS Hs) | exact (TXNB i Hi Hb)]. }
  assert (QOK : forall i, 0 <= i < 24 -> YM05.alloc_ceiling <= q + i < 2 ^ 64 /\
            ~ scratch_k B PARSE_STRING_K regs (q + i) /\ ~ ps_e0 res (Z.of_nat Q + 1) (q + i)).
  { intros i Hi. split; [lia|]. split.
    - unfold scratch_k. lia.
    - unfold ps_e0. intros (_ & [Hs|(Hz & Hr)]); [pose proof (STL _ Hs); lia | lia]. }
  assert (RP2 : rpost B API (ALLOC_STACK + 32) L A (ms_regs ms1) m1 md (alloc_writes res) (fun a k => (a, k) = (0, 0))
                  L2 A2 regs2 mem2 md2)
    by exact (ps_call _ _ _ _ _ _ _ _ _ _ _ _ _ HM1 CP2 INIT2 AUX2 LEN2 UK2).
  assert (RP12 : rpost B API PARSE_STRING_K L A regs mem md (ps_e0 res (Z.of_nat Q + 1)) (fun _ _ => False)
                   L2 A2 regs mem2 md2).
  { apply (rk_seq PARSE_STRING_K L A regs mem md _ L A regs m1 md (ALLOC_STACK + 32) (ms_regs ms1) _ _ L2 A2 regs2 mem2 md2
      regs (R1G _ regs (fun r _ => eq_refl)) RP2).
    - intros r _. reflexivity.
    - rewrite SP1. unfold ALLOC_STACK. lia.
    - rewrite SP1. lia.
    - exact HAC.
    - unfold ALLOC_STACK. lia.
    - intros a Ha _ _. unfold alloc_writes. intros [Hs|(Hz & Hr)]; [pose proof (STL a Hs); lia | lia].
    - intros a _ _ He. unfold alloc_writes. intros [Hs|(Hz & Hr)]; apply He; (split; [lia|]);
        [left; exact Hs | right; split; [exact Hz | lia]].
    - intros p0 n0 i _ _ _ He. unfold alloc_writes. intros [Hs|(Hz & Hr)]; apply He; (split; [lia|]);
        [left; exact Hs | right; split; [exact Hz | lia]].
    - intros p0 n0 Hp _ E. cbv beta in E. injection E as E1 E2.
      pose proof (mr_blocks_range B _ (aa_laws API) _ _ _ _ p0 n0 HM Hp). lia.
    - intros a Ha Hd. left. unfold scratch_k in Ha, Hd. rewrite SP1 in Hd. unfold alloc_writes.
      intros [Hs|(Hz & Hr)]; [pose proof (STL a Hs); lia | lia]. }
  pose proof RP12 as (_ & _ & _ & Y12 & I12 & X12 & _ & UB12 & PA12 & _ & _ & H12 & _ & _ & C12).
  assert (TXK2 : forall i, 0 <= i < len -> mbyte (ms_segs B) mem2 (text + i) = mbyte (ms_segs B) mem (text + i))
    by exact (ps_txt_rp _ _ _ _ _ _ _ _ _ _ _ _ text len RP12 TXL TXOK ltac:(lia) ltac:(lia)).
  assert (PIN2 : pj_in_ok rsegs mem2 q text len p d tb).
  { apply (ps_pin_keep mem); [exact PIN | |].
    - intros i Hi. destruct (QOK i Hi) as (Hr & Ns & Ne). destruct (H12 (q + i) Hr Ns Ne) as [E1 E2].
      rewrite SEG in E1, E2. split; [exact E1 | apply E2].
    - intros i Hi. rewrite <- SEG. exact (TXK2 i Hi). }
  assert (FK2 : forall x, spZ regs + -144 <= x < spZ regs ->
            mbyte rsegs mem2 x = mbyte rsegs m1 x /\ (writable_at rsegs m1 x -> writable_at rsegs mem2 x)).
  { intros x Hx. pose proof RP2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H2 & _).
    destruct (H2 x) as [E1 E2].
    - lia.
    - unfold scratch_k. rewrite SP1. unfold ALLOC_STACK. lia.
    - unfold alloc_writes. intros [Hs|(Hz & Hr)]; [pose proof (STL _ Hs); lia | lia].
    - rewrite SEG in E1, E2. split; [exact E1 | apply E2]. }
  assert (FRJ2 : rw_cells rsegs mem2 (spZ regs + -144) [CB 40 junk]).
  { apply (rk_rw_cells_keep m1 mem2 _ _ FRJ). intros i Hi. cbn [cells_size csize] in Hi. apply FK2. lia. }
  pose proof (rk_rw_cells_keep m1 mem2 _ _ FRS
    ltac:(intros i Hi; cbn [cells_size csize Nat.add] in Hi; apply FK2; lia)) as FRS2.
  assert (S2 : reg_get regs2 2 = Z_to_bv 64 (spZ regs + -144)).
  { transitivity (getr regs2 (Z_to_bv 5 2)); [reflexivity|]. rewrite (RP2r 2) by (unfold callee_saved; lia).
    rewrite (rk_getr_eqv _ _ XR1). reflexivity. }
  assert (GP2 : reg_get regs2 3 = reg_get regs 3).
  { transitivity (getr regs2 (Z_to_bv 5 3)); [reflexivity|]. rewrite (RP2r 3) by (unfold callee_saved; lia).
    rewrite (rk_getr_eqv _ _ XR1). reflexivity. }
  assert (TP2 : reg_get regs2 4 = reg_get regs 4).
  { transitivity (getr regs2 (Z_to_bv 5 4)); [reflexivity|]. rewrite (RP2r 4) by (unfold callee_saved; lia).
    rewrite (rk_getr_eqv _ _ XR1). reflexivity. }
  rewrite SEG.
  destruct ARM2 as [(CF & R0 & EL2 & EA2 & EMD2 & RF2 & WO2 & EB2 & LED2) |
                    (CNF & RNZ & RM16 & RF2 & RNS & RNI & RNL & (bb1 & bb2 & EB2 & EB) & LED2)].
  - subst res L2 A2 md2.
    rewrite Z.mod_small in LED2 by lia.
    eapply rk_kA; [exact Hh2 | exact Hl2 | |].
    { unfold mkR_of. rewrite S2. eapply pss_null with (S := spZ regs + -144); [exact R102 | lia | lia | exact FRS2]. }
    intros ms' (can & -> & EQV).
    destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems' & XR).
    destruct (ps_final_regs XR ltac:(lia) GP2 TP2) as (RPF & R10F).
    rewrite Ems'. apply SR_ret. cbv beta.
    exists L, A, (ms_regs ms'), mem2, md, Lam, peak, (cnt + 1), (2 ^ 64 - 1), b, 0, 0, (Z.of_nat Q + 1).
    split; [change (reg_get regs 1) with (getr regs 1); rewrite (rk_ret_pc _ HRA); reflexivity|].
    split; [eapply ps_rp_mono; [eapply rk_regs; [exact RP12 | exact RPF] | intros x Hx; exact (ps_e0_sub q _ _ x Hx)]|].
    split.
    { split; [exact ROA2|].
      destruct (YL01.ax_statics PSAX L A mem2 md M2) as (GOT & (g & _ & GW) & _). split; [exact GOT | exists g; exact GW]. }
    split; [exact R10F|]. split; [exact LED2|]. split; [exact RF2|].
    split; [reflexivity|]. split; [reflexivity|].
    left. split; [exact CF|]. do 6 (split; [reflexivity|]). exact PIN2.
  - assert (CNE : (cnt + 1) mod 2 ^ 64 = cnt + 1) by (apply Z.mod_small; lia).
    rewrite CNE in LED2.
    destruct RESB as [R0|(_ & HIN2 & RLO & RHI & _)]; [lia|].
    assert (NEWB : new_blks L A [(res, Z.of_nat Q + 1)]).
    { intros a0 k0 [E1|[]] Hin. injection E1 as <- <-. rewrite EB in Hin.
      pose proof (mr_blocks_disjoint B _ (aa_laws API) _ _ _ _ M2) as PW. rewrite EB2 in PW.
      destruct (ps_pw_app _ bb1 _ bb2 _ PW Hin) as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
    assert (TXD : res + Z.of_nat Q + 1 <= text \/ text + len <= res).
    { destruct (Z_le_gt_dec (res + Z.of_nat Q + 1) text) as [H1|H1]; [left; exact H1|].
      destruct (Z_le_gt_dec (text + len) res) as [H2|H2]; [right; exact H2|].
      exfalso. apply (TXNB (Z.max res text - text)); [lia|]. split; [exact RNZ | lia]. }
    assert (BNO : forall x, res <= x < res + Z.of_nat Q + 1 -> ~ owned B L2 A2 x /\ ~ in_img B x /\ ~ alloc_statics x).
    { intros x Hx. destruct (rk_blk_facts L2 A2 mem2 md2 _ _ M2 HIN2) as (_ & _ & BF).
      destruct (BF (x - (res - 16)) ltac:(lia)) as (_ & NO). replace (res - 16 + (x - (res - 16))) with x in NO by lia.
      split; [exact NO|]. split.
      - replace x with (res - 16 + (x - (res - 16))) by lia. apply RNI. lia.
      - replace x with (res - 16 + (x - (res - 16))) by lia. apply RNS. lia. }
    assert (BODY : forall W m3, munch W mem2 m3 -> wmono rsegs mem2 m3 ->
              (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x ->
                 (spZ regs + -144 <= x < spZ regs + -144 + 40) \/ (res <= x < res + Z.of_nat Q + 1) \/ (q <= x < q + 8)) ->
              aa_MR API L2 A2 m3 md2 /\ MemNorm.ro_agree rsegs m3 /\
              ledger B L2 A2 m3 ((res, Z.of_nat Q + 1) :: Lam) (Z.max peak (lsum Lam + (Z.of_nat Q + 1))) (cnt + 1) fail /\
              (forall E : Z -> Prop, (forall x, q <= x < q + 8 -> ~ outside W x -> E x) ->
                 (forall x, ps_e0 res (Z.of_nat Q + 1) x -> E x) ->
                 rpost B API PARSE_STRING_K L2 A2 regs mem2 md2 E (fun _ _ => False) L2 A2 regs m3 md2)).
    { intros W m3 MU3 WM3 HW.
      assert (WM3' : wmono (ms_segs B) mem2 m3) by (rewrite SEG; exact WM3).
      assert (KEEP3 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs + -144 <= x < spZ regs + -144 + 40) ->
                        ~ (res <= x < res + Z.of_nat Q + 1) -> ~ (q <= x < q + 8) ->
                        mbyte (ms_segs B) m3 x = mbyte (ms_segs B) mem2 x).
      { intros x Hx N1 N2 N3. apply (MemNorm.mbyte_munch _ _ _ _ _ MU3); [exact Hx|].
        destruct (rk_outside_dec W x) as [O|O]; [exact O|]. exfalso. destruct (HW x Hx O) as [Hw|[Hw|Hw]]; contradiction. }
      assert (HM3 : aa_MR API L2 A2 m3 md2).
      { apply (rk_MR_A SEG L2 A2 mem2 m3 md2 W M2 MU3 WM3').
        - intros x Ho. pose proof (OWL _ _ _ _ x M2 Ho) as Hlo. destruct (rk_outside_dec W x) as [O|O]; [exact O|].
          exfalso. destruct (HW x ltac:(lia) O) as [Hw|[Hw|Hw]]; [lia | exact (proj1 (BNO x Hw) Ho) | lia].
        - intros x Hx O. destruct (HW x Hx O) as [Hw|[Hw|Hw]].
          + intros Hi. pose proof (rk_img_bound SEG x Hi). lia.
          + exact (proj1 (proj2 (BNO x Hw))).
          + intros Hi. pose proof (rk_img_bound SEG x Hi). lia. }
      split; [exact HM3|].
      split.
      { apply (ps_ro_munch W mem2 m3); [rewrite <- SEG; exact ROA2 | exact MU3 |]. intros x Hx O.
        destruct (HW x Hx O) as [Hw|[Hw|Hw]];
          [apply rk_high_nofs; lia | apply (rk_noimg_fs SEG); exact (proj1 (proj2 (BNO x Hw))) | apply rk_high_nofs; lia]. }
      split.
      { apply (rk_ledger_keep L2 A2 mem2 m3 _ _ _ _ LED2).
        - intros x Hx. pose proof (STL x Hx) as Hlo. apply KEEP3; [lia | lia | intros Hw; exact (proj2 (proj2 (BNO x Hw)) Hx) | lia].
        - intros a0 k0 i HI Hi.
          pose proof LED2 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
          destruct (LF _ HI) as (Lk & LIn & _). cbn [fst snd] in Lk, LIn.
          pose proof (ledger_block_range B API L2 A2 mem2 md2 _ _ _ _ a0 k0 M2 LED2 HI) as (Ra & Rb & _).
          apply KEEP3; [lia | lia | | lia].
          destruct HI as [E1|HI].
          + injection E1 as <- <-. lia.
          + pose proof (mr_blocks_disjoint B _ (aa_laws API) _ _ _ _ M2) as PW.
            assert (NE : (a0 - 16, k0 + 16) <> (res - 16, Z.of_nat Q + 1 + 16)).
            { intros E1. injection E1 as E2 E3. apply RNL. replace res with a0 by lia. apply in_map_iff.
              exists (a0, k0). split; [reflexivity | exact HI]. }
            destruct (rk_pairwise_in _ _ _ _ PW LIn HIN2 NE) as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
      intros E HEq HE0.
      apply (rk_of_A SEG PARSE_STRING_K L2 A2 regs mem2 md2 E m3 W regs HM3 WF2 B2 (fun r _ => eq_refl) MU3 WM3').
      - exact C12.
      - intros x Hx Hs He. destruct (rk_outside_dec W x) as [O|O]; [exact O|]. exfalso.
        destruct (HW x Hx O) as [Hw|[Hw|Hw]].
        + apply Hs. unfold scratch_k. left. lia.
        + apply He. apply HE0. unfold ps_e0. split; [lia|]. right. split; [exact RNZ | lia].
        + apply He. exact (HEq x Hw O).
      - intros i Hi. destruct (rk_outside_dec W (ms_libc B + 8 + i)) as [O|O]; [exact O|]. exfalso.
        assert (Ho : owned B L2 A2 (ms_libc B + 8 + i)) by (right; unfold static_owned; right; right; left; lia).
        pose proof (OWL _ _ _ _ _ M2 Ho) as Hlo.
        destruct (HW (ms_libc B + 8 + i) ltac:(lia) O) as [Hw|[Hw|Hw]]; [lia | exact (proj1 (BNO _ Hw) Ho) | lia].
      - lia.
      - lia.
      - intros p0 n0 i Hp Hi He. destruct (mr_blocks B _ (aa_laws API) L2 A2 mem2 md2 p0 n0 i M2 Hp Hi) as (_ & Bl & Bh & _).
        split; [lia|]. destruct (rk_outside_dec W (ptr_addr L2 p0 + i)) as [O|O]; [exact O|]. exfalso.
        destruct (HW (ptr_addr L2 p0 + i) ltac:(lia) O) as [Hw|[Hw|Hw]]; [lia | | lia].
        apply He. apply HE0. unfold ps_e0. split; [lia|]. right. split; [exact RNZ | lia]. }
    eapply rk_kA; [exact Hh2 | exact Hl2 | |].
    { unfold mkR_of.
      eapply (pss_body PSPU PSHX) with (q := q) (text := text) (len := len) (p := p) (d := d) (S := spZ regs + -144)
        (a := res) (Q := Q) (tb := tb) (junk := junk).
      - exact S2.
      - transitivity (getr regs2 (Z_to_bv 5 8)); [reflexivity|]. rewrite (RP2r 8) by (unfold callee_saved; lia).
        rewrite (rk_getr_eqv _ _ XR1). reflexivity.
      - transitivity (getr regs2 (Z_to_bv 5 24)); [reflexivity|]. rewrite (RP2r 24) by (unfold callee_saved; lia).
        rewrite (rk_getr_eqv _ _ XR1). reflexivity.
      - exact R102.
      - exact PIN2.
      - exact HP.
      - exact HQ.
      - exact FRJ2.
      - exact FRS2.
      - split; [lia|]. split; [lia|]. intros i Hi.
        destruct (rk_blk_facts L2 A2 mem2 md2 _ _ M2 HIN2) as (_ & _ & BF).
        destruct (BF (16 + i) ltac:(lia)) as (Pr & _). replace (res - 16 + (16 + i)) with (res + i) in Pr by lia.
        pose proof (present_writable B mem2 (res + i) Pr) as Wr. rewrite SEG in Wr. exact Wr.
      - lia.
      - replace (spZ regs + -144) with (spZ regs + (-9) * 16) by lia. rewrite Z_mod_plus_full. exact H16.
      - lia.
      - lia.
      - lia.
      - exact TXD.
      - lia. }
    intros ms3 (can3 & BP & EQV3). unfold pss_body_post in BP.
    destruct BP as [(t0' & t1' & t2' & a1' & a2'' & a3'' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ws & m3 & -> &
                     HD & HLw & HBw & HBq & MU3 & WM3) |
                    (t0' & t1' & t2' & a1' & a2'' & a3'' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' &
                     s9' & s10' & s11' & t3' & t4' & t5' & t6' & m3 & -> & HD & MU3 & WM3)].
    + destruct (BODY _ m3 MU3 WM3 ltac:(intros x Hx O; cbn [outside] in O; lia)) as (HM3 & RO3 & LED3 & R3G).
      assert (RP3 : rpost B API PARSE_STRING_K L2 A2 regs mem2 md2 (parse_string_writes q res (Z.of_nat Q + 1))
                      (fun _ _ => False) L2 A2 regs m3 md2).
      { apply R3G; [intros x Hx _; unfold parse_string_writes; split; [lia | left; exact Hx] | apply ps_e0_sub]. }
      destruct (rk_eqv_shape _ _ _ _ _ _ EQV3) as (Ems3 & XR3).
      destruct (ps_final_regs XR3 ltac:(lia) GP2 TP2) as (RPF & R10F).
      rewrite Ems3. apply SR_ret. cbv beta.
      exists L2, A2, (ms_regs ms3), m3, md2, ((res, Z.of_nat Q + 1) :: Lam), (Z.max peak (lsum Lam + (Z.of_nat Q + 1))),
        (cnt + 1), fail, (rf_malloc RF b (Z.of_nat Q + 1 + 16)), res, res, (Z.of_nat Q + 1).
      split; [change (reg_get regs 1) with (getr regs 1); rewrite (rk_ret_pc _ HRA); reflexivity|].
      split.
      { apply (rk_seq PARSE_STRING_K L A regs mem md _ L2 A2 regs mem2 md2 PARSE_STRING_K regs _ _ L2 A2 regs m3 md2
          (ms_regs ms3) (ps_rp_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP12 (ps_e0_sub q res (Z.of_nat Q + 1))) RP3 RPF).
        - lia.
        - lia.
        - exact HAC.
        - lia.
        - intros a0 _ _ He. exact He.
        - intros a0 _ _ He. exact He.
        - intros p0 n0 i _ _ _ He. exact He.
        - intros p0 n0 _ _ F. exact F.
        - intros a0 Ha Hd. contradiction. }
      split.
      { split; [rewrite SEG; exact RO3|].
        destruct (YL01.ax_statics PSAX L2 A2 m3 md2 HM3) as (GOT & (g & _ & GW) & _). split; [exact GOT | exists g; exact GW]. }
      split; [exact R10F|]. split; [exact LED3|]. split; [exact RF2|].
      split; [reflexivity|]. split; [reflexivity|].
      right; right.
      split; [exact CNF|]. split; [reflexivity|]. split; [exact RNZ|].
      exists (zb ws), (rest_at tb text (p + 1 + Z.of_nat Q + 1)).
      split; [exact HD|]. split; [reflexivity|]. split; [exact NEWB|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      split.
      { split; [exact (G1_4_bytes _ _ _ (ps_zb_rng _) HD)|].
        rewrite map_app, ps_zb_map. cbn [map]. exact HBw. }
      pose proof PIN2 as (P1 & P2' & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
      split; [replace (p + (Z.of_nat Q + 1) + 1) with (p + 1 + Z.of_nat Q + 1) by lia; exact HBq|].
      split; [apply (bytes_at_transport rsegs _ mem2 m3 _ _ P2' MU3); rewrite length_le8; djs|].
      split; [apply (bytes_at_transport rsegs _ mem2 m3 _ _ P3 MU3); rewrite length_le4; djs|].
      split; [exact (wr_at_transport rsegs _ _ _ _ P4 WM3)|].
      split; [exact P5|]. split; [exact P6|]. split; [exact P7|].
      split; [lia|]. split; [exact P9|].
      split; [apply (bytes_at_transport rsegs _ mem2 m3 _ _ P10 MU3); rewrite P9; djs|].
      split; [exact P11 | exact P12].
    + destruct (BODY _ m3 MU3 WM3 ltac:(intros x Hx O; cbn [outside] in O; lia)) as (HM3 & RO3 & LED3 & R3G).
      assert (RP3 : rpost B API PARSE_STRING_K L2 A2 regs mem2 md2 (ps_e0 res (Z.of_nat Q + 1))
                      (fun _ _ => False) L2 A2 regs m3 md2).
      { apply R3G; [intros x Hx O; exfalso; apply O; outs | intros x Hx; exact Hx]. }
      assert (RP123 : rpost B API PARSE_STRING_K L A regs mem md (ps_e0 res (Z.of_nat Q + 1)) (fun _ _ => False)
                        L2 A2 regs m3 md2).
      { apply (rk_seq PARSE_STRING_K L A regs mem md _ L2 A2 regs mem2 md2 PARSE_STRING_K regs _ _ L2 A2 regs m3 md2
          regs RP12 RP3).
        - intros r _. reflexivity.
        - lia.
        - lia.
        - exact HAC.
        - lia.
        - intros a0 _ _ He. exact He.
        - intros a0 _ _ He. exact He.
        - intros p0 n0 i _ _ _ He. exact He.
        - intros p0 n0 _ _ F. exact F.
        - intros a0 Ha Hd. contradiction. }
      pose proof RP123 as (_ & _ & _ & Y3 & I3 & X3 & _ & _ & _ & _ & _ & H3 & _ & _ & C3).
      destruct (rk_eqv_shape _ _ _ _ _ _ EQV3) as (Ems3 & XR3).
      assert (G31 : getr (ms_regs ms3) 1 = Z_to_bv 64 0x168d8) by (rewrite (rk_getr_eqv _ _ XR3); reflexivity).
      assert (SP3 : spZ (ms_regs ms3) = spZ regs + -144).
      { change (spZ (ms_regs ms3)) with (bv_unsigned (getr (ms_regs ms3) 2)). rewrite (rk_getr_eqv _ _ XR3).
        change (bv_unsigned (Z_to_bv 64 (spZ regs + -144)) = spZ regs + -144). rewrite unsigned_lit by lia. reflexivity. }
      assert (G310 : getr (ms_regs ms3) 10 = Z_to_bv 64 res) by (rewrite (rk_getr_eqv _ _ XR3); reflexivity).
      assert (G34 : getr (ms_regs ms3) 4 = getr regs 4).
      { transitivity (reg_get regs2 4); [rewrite (rk_getr_eqv _ _ XR3); reflexivity | exact TP2]. }
      rewrite Ems3. rewrite <- SEG.
      change (Z_to_bv 64 0x157f8) with (Z_to_bv 64 FUZZ_FREE).
      eapply SR_bind.
      { apply (PSFREE L2 A2 (ms_regs ms3) m3 md2 res (Z.of_nat Q + 1) (rf_malloc RF b (Z.of_nat Q + 1 + 16))
                 ((res, Z.of_nat Q + 1) :: Lam) (Z.max peak (lsum Lam + (Z.of_nat Q + 1))) (cnt + 1) fail).
        - split; [exact HM3|]. split; [exact WF2|]. split; [exact B2|].
          split; [rewrite G31; apply ret_ok_even; vm_compute; reflexivity|].
          split; [rewrite SP3; replace (spZ regs + -144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact H16|].
          split; [rewrite SP3; unfold ALLOC_STACK; lia|].
          split; [rewrite SP3; lia|].
          split; [intros a0 Ha0; rewrite SP3 in Ha0; apply C3; unfold scratch_k; left; unfold ALLOC_STACK in Ha0; lia|].
          split; [rewrite G34; exact HTP|].
          split; [intros a0 Ha0; apply C3; right; exact Ha0|].
          intros HI2. rewrite SP3. destruct Y3 as (_ & YS & _). rewrite YS.
          assert (HI : st_init_done A = false)
            by (case_eq (st_init_done A); intros E1; [rewrite (I3 E1) in HI2; discriminate HI2 | reflexivity]).
          apply (auxv_pre_mono B (ly_sec L) (spZ regs) (spZ regs + -144) m3); [lia|].
          apply (rk_auxv_keep _ _ mem m3 (HAUX HI) (X3 HI2)).
          intros a0 Ha0. refine (proj1 (H3 a0 _ _ _)); [lia | unfold scratch_k; lia |].
          unfold ps_e0. intros (_ & [Hs|(Hz & Hr)]); [pose proof (STL _ Hs); lia | lia].
        - exact G310.
        - exact LED3.
        - rewrite SEG. exact RO3.
        - right. left. reflexivity.
        - exact RF2. }
      intros c4 (L4 & A4 & regs4 & mem4 & md4 & -> & ROA4 & GK4 & INIT4 & AUX4 & CP4 & LEN4 & KEEP4 & UK4 & ARM4).
      rewrite G31.
      pose proof CP4 as (M4 & WF4 & B4 & Y4 & P4 & RP4r & D4 & FR4 & KB4 & SC4).
      destruct (mr_model B _ (aa_laws API) L4 A4 mem4 md4 M4) as (Hh4 & Hl4 & _).
      destruct ARM4 as [(P0 & _) | (_ & _ & (l1 & l2 & EL & LED4) & RF4)]; [exfalso; exact (RNZ P0)|].
      assert (EL' : l1 ++ l2 = Lam).
      { destruct l1 as [|x l1]; apply (f_equal (@tl _)) in EL; cbn [tl app] in EL |- *.
        - symmetry. exact EL.
        - exfalso. apply RNL. rewrite EL, map_app. apply in_or_app. right. cbn [map fst]. left. reflexivity. }
      assert (RP4 := ps_call _ _ _ _ _ _ _ _ _ _ _ _ _ HM3 CP4 INIT4 AUX4 LEN4 UK4).
      assert (RP1234 : rpost B API PARSE_STRING_K L A regs mem md (ps_e0 res (Z.of_nat Q + 1)) (fun _ _ => False)
                         L4 A4 regs mem4 md4).
      { apply (rk_seq PARSE_STRING_K L A regs mem md _ L2 A2 regs m3 md2 ALLOC_STACK (ms_regs ms3) _ _ L4 A4 regs4 mem4 md4
          regs RP123 RP4).
        - intros r _. reflexivity.
        - rewrite SP3. unfold ALLOC_STACK. lia.
        - rewrite SP3. lia.
        - exact HAC.
        - unfold ALLOC_STACK. lia.
        - intros a0 Ha0 _ _. unfold free_writes. intros [Hg|(Hz & Hr)]; [unfold G_LIVE in Hg; lia | lia].
        - intros a0 _ _ He. unfold free_writes. intros [Hg|(Hz & Hr)]; apply He; (split; [lia|]);
            [left; unfold alloc_statics; left; exact Hg | right; split; [exact Hz | lia]].
        - intros p0 n0 i _ _ _ He. unfold free_writes. intros [Hg|(Hz & Hr)]; apply He; (split; [lia|]);
            [left; unfold alloc_statics; left; exact Hg | right; split; [exact Hz | lia]].
        - intros p0 n0 Hp _ E1. cbv beta in E1. injection E1 as E2 E3.
          apply (NEWB res (Z.of_nat Q + 1) (or_introl eq_refl)). rewrite <- E2, <- E3. exact (rk_blk_of_user L A p0 n0 Hp).
        - intros a0 Ha0 Hd. left. unfold free_writes. unfold scratch_k in Ha0, Hd.
          intros [Hg|(Hz & Hr)]; [unfold G_LIVE in Hg; lia | lia]. }
      pose proof RP1234 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H4 & _ & _ & _).
      pose proof (rk_rw_cells_keep mem2 mem4 _ _ FRS2
        ltac:(intros i Hi; cbn [cells_size csize Nat.add] in Hi;
              pose proof RP4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H44 & _);
              destruct (H44 (spZ regs + -144 + 40 + i)) as [E4 W4];
              [lia | unfold scratch_k; rewrite SP3; unfold ALLOC_STACK; lia | unfold free_writes, G_LIVE; lia |];
              destruct (ps_mb (ms_segs B) _ mem2 m3 (spZ regs + -144 + 40 + i) MU3 ltac:(lia) ltac:(outs)) as [E3 W3];
              rewrite SEG in E4, W4, E3, W3; split; [rewrite E4, E3; reflexivity | intros Wx; apply W4, W3, Wx])) as FRS4.
      rewrite SEG.
      eapply rk_kA; [exact Hh4 | exact Hl4 | |].
      { unfold mkR_of.
        assert (S4 : reg_get regs4 2 = Z_to_bv 64 (spZ regs + -144)).
        { transitivity (getr regs4 (Z_to_bv 5 2)); [reflexivity|]. rewrite (RP4r 2) by (unfold callee_saved; lia).
          rewrite (rk_getr_eqv _ _ XR3). reflexivity. }
        rewrite S4. eapply pss_tail; [lia | lia | exact FRS4]. }
      intros ms5 (can5 & -> & EQV5).
      destruct (rk_eqv_shape _ _ _ _ _ _ EQV5) as (Ems5 & XR5).
      assert (GP4 : reg_get regs4 3 = reg_get regs 3).
      { transitivity (getr regs4 (Z_to_bv 5 3)); [reflexivity|]. rewrite (RP4r 3) by (unfold callee_saved; lia).
        rewrite (rk_getr_eqv _ _ XR3). exact GP2. }
      assert (TP4 : reg_get regs4 4 = reg_get regs 4).
      { transitivity (getr regs4 (Z_to_bv 5 4)); [reflexivity|]. rewrite (RP4r 4) by (unfold callee_saved; lia).
        rewrite (rk_getr_eqv _ _ XR3). exact TP2. }
      destruct (ps_final_regs XR5 ltac:(lia) GP4 TP4) as (RPF & R10F).
      rewrite Ems5. apply SR_ret. cbv beta.
      exists L4, A4, (ms_regs ms5), mem4, md4, Lam, (Z.max peak (lsum Lam + (Z.of_nat Q + 1))), (cnt + 1), fail,
        (rf_free RF (rf_malloc RF b (Z.of_nat Q + 1 + 16)) (Z.of_nat Q + 1 + 16)), 0, res, (Z.of_nat Q + 1).
      split; [change (reg_get regs 1) with (getr regs 1); rewrite (rk_ret_pc _ HRA); reflexivity|].
      split; [eapply ps_rp_mono; [eapply rk_regs; [exact RP1234 | exact RPF] | intros x Hx; exact (ps_e0_sub q _ _ x Hx)]|].
      split.
      { split; [exact ROA4|].
        destruct (YL01.ax_statics PSAX L4 A4 mem4 md4 M4) as (GOT & (g & _ & GW) & _). split; [exact GOT | exists g; exact GW]. }
      split; [exact R10F|]. split; [rewrite EL' in LED4; exact LED4|]. split; [exact RF4|].
      split; [reflexivity|]. split; [reflexivity|].
      right; left.
      split; [exact CNF|]. split; [exact HD|]. split; [reflexivity|]. split; [exact RNZ|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split.
      { intros x Hx. split.
        - replace x with (res - 16 + (x - (res - 16))) by lia. apply RNI. lia.
        - intros p0 k0 Hin Hr. rewrite EB in Hin.
          pose proof (mr_blocks_disjoint B _ (aa_laws API) _ _ _ _ M2) as PW. rewrite EB2 in PW.
          destruct (ps_pw_app _ bb1 _ bb2 _ PW Hin) as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
      split; [lia|]. split; [reflexivity|].
      apply (ps_pin_keep mem); [exact PIN | |].
      * intros i Hi. destruct (QOK i Hi) as (Hr & Ns & Ne). destruct (H4 (q + i) Hr Ns Ne) as [E1 E2].
        rewrite SEG in E1, E2. split; [exact E1 | apply E2].
      * intros i Hi. rewrite <- SEG.
        exact (ps_txt_rp _ _ _ _ _ _ _ _ _ _ _ _ text len RP1234 TXL TXOK ltac:(lia) ltac:(lia) i Hi).
Qed.

End PSH.

Section PSF.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.

Theorem parse_string_holds : YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  fuzz_malloc_contract B API RF -> fuzz_free_contract B API RF -> put_utf8_contract -> hex4_c.hex4_contract ->
  parse_string_contract B API RF.
Proof.
  intros AX CT HMA HFR PU HX. unfold parse_string_contract.
  intros L A regs mem md Lam peak cnt fail b q text len p d tb ENV.
  exact (ps_main B API RF (proj1 ENV) AX CT HMA HFR PU HX L A regs mem md Lam peak cnt fail b q text len p d tb ENV).
Qed.

End PSF.
