From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import slot_steps_c memchr_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require slot_glue.
Import ListNotations.
Open Scope Z_scope.

Lemma sl_s8 : sl_s8_stmt.
Proof.
  unfold sl_s8_stmt, sl_frame.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    j v5 v4 v3 v2 v1 v0 vra FR.
  do 10 zstep.
  apply evt_done. reflexivity.
Qed.

Definition sl_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo p : Z) (pl : list byte) : machine_state -> Prop :=
  fun ms' =>
       (0x400000 < sl_tn pl /\
        exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom rsegs) /\
          munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
          stk rsegs m' lo (bv_unsigned sp)) \/
       (sl_tn pl <= 0x400000 /\
        exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (j : list byte) (m' : word -> option byte),
          ms' = MS (mkR (Z_to_bv 64 0x12fb4) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2'
                        (Z_to_bv 64 (sl_un pl)) (Z_to_bv 64 (Z.of_nat (length pl) - sl_s pl))
                        (Z_to_bv 64 (sl_uri p pl)) (Z_to_bv 64 (sl_un pl))
                        (Z_to_bv 64 (sl_text p pl)) (Z_to_bv 64 (sl_tn pl)) a4' a5' a6' a7'
                        (Z_to_bv 64 (sl_text p pl)) (Z_to_bv 64 (sl_tn pl)) (Z_to_bv 64 (sl_uri p pl))
                        (Z_to_bv 64 (- sl_s pl)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 0x130d0) fc None m' (seg_rom rsegs) /\
          rw_cells rsegs m' (bv_unsigned sp + -64) (sl_frame j s5 s4 s3 s2 s1 s0 ra) /\
          munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
          stk rsegs m' lo (bv_unsigned sp + -64)).

Ltac br b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; unfold bv_ltu, bv_eqb; rewrite ?unsigned_lit by lia;
        first [apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq]; lia]
  end.

Ltac nt := first
  [ br false
  | let K := fresh "K" in if_cases K; zify_cond K; [exfalso; mlia | cbv iota] ].

Ltac dec_b2z := decide_tests; try change (Z.b2z true) with 1; try change (Z.b2z false) with 0.

Lemma sl_t3 :
  forall (xra sp gp tp t0 t1 t2 x9 a0 xa1 a2 a3 a4 a5 a6 a7 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (ra s0 s1 s2 s3 s4 s5 : word) (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte)
         (lo p : Z) (pl j : list byte),
    x9 = Z_to_bv 64 (Z.of_nat (length pl) - sl_s pl) -> x21 = Z_to_bv 64 (- sl_s pl) ->
    0 <= sl_tn pl < 2 ^ 62 -> 0 <= lo -> lo + 64 <= bv_unsigned sp ->
    rw_cells rsegs m1 (bv_unsigned sp + -64) (sl_frame j s5 s4 s3 s2 s1 s0 ra) ->
    munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -64) ->
    evt rsegs (sl_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p pl)
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (sl_un pl)) x9 a0 xa1 a2 a3 a4
               a5 a6 a7 (Z_to_bv 64 (sl_text p pl)) (Z_to_bv 64 (sl_tn pl)) (Z_to_bv 64 (sl_uri p pl))
               x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f98) fc None m1 (seg_rom rsegs)).
Proof.
  intros xra sp gp tp t0 t1 t2 x9 a0 xa1 a2 a3 a4 a5 a6 a7 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5
    F fc m m1 lo p pl j -> -> HT HLO HSP FR MU WM MI ST.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  assert (US : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  zstep. zstep.
  destruct (Z_lt_le_dec 0x400000 (sl_tn pl)) as [C|C].
  - br true.
    eapply evt_cut; [eapply sl_s8; rewrite US; exact FR|].
    intros ms' ->. apply evt_done. left. split; [lia|].
    rewrite US. replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    do 15 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    pose proof (stk_release rsegs m1 lo _ _ ST FR ltac:(lia)) as STf.
    unfold sl_frame in STf. cbn [cells_size csize Nat.add] in STf.
    replace (bv_unsigned sp + -64 + Z.of_nat 64) with (bv_unsigned sp) in STf by lia. exact STf.
  - br false.
    do 5 zstep.
    apply evt_done. right. split; [exact C|].
    do 13 eexists. split; [reflexivity|].
    split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST].
Qed.

Lemma sl_t2 : memchr_contract ->
  forall (xra sp gp tp t0 t1 t2 x8 a0 xa1 a2 a3 a4 a5 a6 a7 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (ra s0 s1 s2 s3 s4 s5 a1 : word) (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte)
         (lo p : Z) (pl j : list byte),
    x8 = Z_to_bv 64 (sl_un pl) -> a1 = Z_to_bv 64 (Z.of_nat (length pl)) -> x21 = Z_to_bv 64 (- sl_s pl) ->
    4096 <= p -> p + Z.of_nat (length pl) < 2 ^ 62 -> 0 <= lo -> lo + 64 <= bv_unsigned sp ->
    bytes_at rsegs m1 (sl_text p pl) (sl_tbuf pl) ->
    rw_cells rsegs m1 (bv_unsigned sp + -64) (sl_frame j s5 s4 s3 s2 s1 s0 ra) ->
    munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -64) ->
    evt rsegs (sl_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p pl)
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 x8 a1 a0 xa1 a2 a3 a4
               a5 a6 a7 (Z_to_bv 64 (sl_text p pl)) (Z_to_bv 64 (sl_k pl)) (Z_to_bv 64 (sl_uri p pl))
               x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f78) fc None m1 (seg_rom rsegs)).
Proof.
  intros MEMCHR xra sp gp tp t0 t1 t2 x8 a0 xa1 a2 a3 a4 a5 a6 a7 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 a1
    F fc m m1 lo p pl j -> -> -> HP HPN HLO HSP BT FR MU WM MI ST.
  pose proof (slot_glue.sl_k_range pl) as (K0 & K1 & K2).
  pose proof (slot_glue.sl_s_range pl) as SR.
  pose proof (slot_glue.sl_tbuf_len pl) as TL.
  pose proof (slot_glue.sl_tn_range pl) as TNR.
  do 6 zstep.
  lazymatch goal with
  | |- context [Z_to_bv 64 (?e - sl_k pl)] =>
      replace (e - sl_k pl) with (Z.of_nat (length (sl_tbuf pl))) by mlia
  end.
  assert (TX : 4096 <= sl_text p pl /\ sl_text p pl + Z.of_nat (length (sl_tbuf pl)) <= p + Z.of_nat (length pl)).
  { unfold sl_text. lia. }
  eapply evt_cut.
  { eapply MEMCHR.
    - rewrite unsigned_lit by lia. exact BT.
    - rewrite !unsigned_lit by lia. change (0 mod 256) with 0. unfold memchr_ok.
      destruct (find_byte 0 (firstn (Z.to_nat (Z.of_nat (length (sl_tbuf pl)))) (sl_tbuf pl))); [left|]; lia.
    - exact MI. }
  post_call rsegs m1.
  rewrite !unsigned_lit by lia. change (0 mod 256) with 0.
  unfold memchr_res.
  destruct (find_byte 0 (firstn (Z.to_nat (Z.of_nat (length (sl_tbuf pl)))) (sl_tbuf pl))) as [i|] eqn:FB.
  - pose proof (find_byte_Some _ _ _ FB) as (FL & _). rewrite length_firstn in FL.
    zstep. br false.
    zstep.
    assert (ESN : sl_tn pl = Z.of_nat i) by (unfold sl_tn, strnlen_res; rewrite FB; reflexivity).
    first [replace (sl_text p pl + Z.of_nat i - sl_text p pl) with (sl_tn pl) by lia | rewrite <- ESN].
    eapply sl_t3; first [eassumption | lia | reflexivity | f_equal; lia].
  - zstep. br true.
    assert (ESN : sl_tn pl = Z.of_nat (length (sl_tbuf pl))) by (unfold sl_tn, strnlen_res; rewrite FB; reflexivity).
    rewrite <- ESN.
    eapply sl_t3; first [eassumption | lia | reflexivity | f_equal; lia].
Qed.

Lemma sl_t1 : memchr_contract ->
  forall (xra sp gp tp t0 t1 t2 x8 a0 xa1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (ra s0 s1 s2 s3 s4 s5 a1 : word) (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte)
         (lo p : Z) (pl j : list byte),
    x19 = Z_to_bv 64 (sl_k pl) -> a1 = Z_to_bv 64 (Z.of_nat (length pl)) -> a0 = Z_to_bv 64 p ->
    4096 <= p -> p + Z.of_nat (length pl) < 2 ^ 62 -> 0 <= lo -> lo + 64 <= bv_unsigned sp ->
    bytes_at rsegs m1 p pl ->
    rw_cells rsegs m1 (bv_unsigned sp + -64) (sl_frame j s5 s4 s3 s2 s1 s0 ra) ->
    munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -64) ->
    evt rsegs (sl_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p pl)
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 x8 a1 a0 xa1 a2 a3 a4
               a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f28) fc None m1 (seg_rom rsegs)).
Proof.
  intros MEMCHR xra sp gp tp t0 t1 t2 x8 a0 xa1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra s0 s1 s2 s3 s4 s5 a1 F fc m m1 lo p pl j -> -> -> HP HPN HLO HSP BP FR MU WM MI ST.
  pose proof (slot_glue.sl_k_range pl) as (K0 & K1 & K2).
  pose proof (slot_glue.sl_s_range pl) as SR.
  pose proof (slot_glue.sl_tbuf_len pl) as TL.
  pose proof (slot_glue.sl_ubuf_len pl) as UL.
  pose proof (slot_glue.sl_un_range pl) as UNR.
  assert (S01 : 0 <= sl_s pl <= 1) by (destruct SR as [[-> _] | [-> _]]; lia).
  assert (BU : bytes_at rsegs m1 (sl_uri p pl) (sl_ubuf pl)).
  { unfold sl_uri, sl_ubuf.
    pose proof (slot_glue.bytes_at_skip_first rsegs m1 p pl (Z.to_nat (sl_s pl)) (Z.to_nat (sl_k pl)) BP ltac:(lia)) as H.
    rewrite Z2Nat.id in H by lia. exact H. }
  assert (BT : bytes_at rsegs m1 (sl_text p pl) (sl_tbuf pl)).
  { unfold sl_text, sl_tbuf.
    pose proof (slot_glue.bytes_at_skip_first rsegs m1 p pl (Z.to_nat (sl_s pl + sl_k pl))
                  (length (skipn (Z.to_nat (sl_s pl + sl_k pl)) pl)) BP ltac:(rewrite length_skipn; lia)) as H.
    rewrite Z2Nat.id in H by lia. rewrite firstn_all in H. replace (p + sl_s pl + sl_k pl) with (p + (sl_s pl + sl_k pl)) by lia.
    exact H. }
  clear BP.
  assert (ES : Z.b2z (0 <? Z.of_nat (length pl)) = sl_s pl) by (destruct pl; reflexivity).
  zstep. rewrite ES.
  zstep.
  zstep. nt.
  zstep. zstep. dec_b2z.
  zstep.
  zstep. nt.
  zstep.
  zstep. nt.
  zstep. dec_b2z.
  zstep.
  zstep. nt.
  do 5 zstep.
  eapply evt_cut.
  { eapply MEMCHR.
    - rewrite unsigned_lit by (unfold sl_uri in *; lia). exact BU.
    - rewrite !unsigned_lit by (unfold sl_uri in *; lia). change (0 mod 256) with 0. unfold memchr_ok.
      destruct (find_byte 0 (firstn (Z.to_nat (sl_k pl)) (sl_ubuf pl))); [left|]; lia.
    - exact MI. }
  post_call rsegs m1.
  rewrite !unsigned_lit by (unfold sl_uri in *; lia). change (0 mod 256) with 0.
  unfold memchr_res.
  destruct (find_byte 0 (firstn (Z.to_nat (sl_k pl)) (sl_ubuf pl))) as [i|] eqn:FB.
  - pose proof (find_byte_Some _ _ _ FB) as (FL & _). rewrite length_firstn in FL.
    assert (ESN : sl_un pl = Z.of_nat i) by (unfold sl_un, strnlen_res; rewrite FB; reflexivity).
    zstep. zstep. br false. zstep.
    eapply sl_t2; try eassumption; try lia; try reflexivity.
    all: f_equal; lia.
  - assert (ESN : sl_un pl = sl_k pl) by (unfold sl_un, strnlen_res; rewrite FB; reflexivity).
    zstep. zstep. br true.
    eapply sl_t2; try eassumption; try lia; try reflexivity.
    all: f_equal; lia.
Qed.

Lemma sl_s0 : memchr_contract -> sl_s0_stmt.
Proof.
  intros MEMCHR. unfold sl_s0_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo p pl -> -> HP HPN BP DJ HMI ST LO.
  enough (G : evt rsegs (sl_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p pl)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat (length pl))) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x12ee4) fc None m (seg_rom rsegs)))
    by exact G.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (proj1 ST) as LO0.
  pose proof (slot_glue.sl_k_range pl) as (K0 & K1 & K2).
  carve_frame 64%nat ST.
  do 9 zstep.
  assert (PLC : pl = [] \/ exists b rest, pl = b :: rest) by (destruct pl; [left | right; eauto]; reflexivity).
  destruct PLC as [E0 | (b & rest & E1)].
  - assert (HN0 : Z.of_nat (length pl) = 0) by (rewrite E0; reflexivity).
    zstep. br true. zstep.
    eapply sl_t1; try eassumption; try lia; try reflexivity.
    all: rewrite E0; reflexivity.
  - assert (HN1 : 1 <= Z.of_nat (length pl)) by (rewrite E1; cbn [length]; lia).
    pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
    zstep. br false.
    zstep. nt.
    match goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RD : ov_read_bytes rsegs mm (wa p) 1 = Some [b])
    end.
    { pose proof (bytes_at_read rsegs _ p pl 0 1 BP ltac:(lia) ltac:(lia)) as R. rewrite Z.add_0_r in R.
      rewrite E1 in R. exact R. }
    zstep. zstep. zstep.
    destruct (Z_lt_le_dec (Z.of_nat (length pl) - 1) (bv_unsigned b)) as [C|C].
    + br true.
      eapply sl_t1; try eassumption; try lia; try reflexivity.
      all: rewrite E1 in *; cbn [sl_k]; f_equal; lia.
    + br false. zstep. zstep.
      eapply sl_t1; try eassumption; try lia; try reflexivity.
      all: rewrite E1 in *; cbn [sl_k]; f_equal; lia.
Qed.
