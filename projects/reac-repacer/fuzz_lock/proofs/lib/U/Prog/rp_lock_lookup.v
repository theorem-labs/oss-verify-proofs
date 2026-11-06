(* Walk of reac-repacer's rp_lock_lookup (src/repace_conf.c:114-145 at 3ac1cf10) in fuzz_lock.ubsan, 0x13258.
   The walk is split over RpLib.v (facts, exit at 0x132ec, the digits tests at 0x13444), RpDec.v (the name tests
   at 0x13408), RpMid.v (memchr '\0' and the three fields at 0x133a4), RpLoop.v (memchr '\n' at 0x13384 and the
   loop) and this file (prologue, std_period, strlen and the setup before the loop).
   UBSan checks of rp_lock_lookup (trap [unimp] at 0x1348c), none taken:
   - 0x1333c [bltu s10,s2]: stop = text + n does not wrap (tx + |T| < 2^64);
   - 0x13350 [beqz a0], a0 = (text <> 0) xor (stop = 0): 0 < tx and tx + |T| < 2^64 (ptr_ok);
   - 0x13400 [beq s7,s1], s1 = -1: lf + 1 does not wrap, lf = tx + o + j < tx + |T| (RpMid.v);
   - 0x13414 [beqz a0], a0 = name: name = tx + o + o1 > 0 (RpDec.v).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import StrFun LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import DigitsMach field_c digits_c
  strlen_c memchr_c bcmp_c rp_lock_lookup_c RpLib RpDec RpMid RpLoop.
Import ListNotations.
Open Scope Z_scope.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.
Lemma ptr_ok : forall x e, 0 < x < 2^64 -> 0 < e < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 x))) (bv_unsigned (v_sltiu (Z_to_bv 64 e) 1))))
         (Z_to_bv 64 0) = false.
Proof.
  intros x e Hx He. rewrite (snez_ok x) by lia. unfold v_sltiu. rewrite (unsigned_lit e) by lia.
  change (bv_wrap 64 1) with 1. destruct (Z.ltb_spec e 1); [lia|]. vm_compute. reflexivity.
Qed.

Section R.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (tx pa rate lo b std : Z) (T P SL : list byte).
Hypothesis Htx : 0 < tx.
Hypothesis HtxE : tx + Z.of_nat (length T) < 2^64.
Hypothesis Hpa : 0 < pa.
Hypothesis HPb : pa + Z.of_nat (length P + 1 + length SL) <= 2^64.
Hypothesis Hrate : rate = 44100 \/ rate = 48000 \/ rate = 96000.
Hypothesis HSTD : std_period rate = std.
Hypothesis Hstd : std = 272109 \/ std = 250000 \/ std = 125000.
Hypothesis Hb : b + 160 = bv_unsigned sp.
Hypothesis Hb8 : b mod 8 = 0.
Hypothesis Hlo : 0 <= lo <= b.
Hypothesis DT : tx + Z.of_nat (length T) <= b \/ b + 160 <= tx.
Hypothesis DP : pa + Z.of_nat (length P + 1 + length SL) <= b \/ b + 160 <= pa.

Local Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Local Notation Q := (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (lock_lookup T P rate)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_FRAME, bv_unsigned sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp)).

(* the registers in the loop: s0 rate, s1 -1, s2 the line, s3 strlen(port), s4 found, s10 stop, s11 '#' *)
Local Notation LS pc mm xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 vs2 vs4 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 :=
  (MS (mkR xra (Z_to_bv 64 b) gp tp xt0 xt1 xt2 (Z_to_bv 64 rate) (Z_to_bv 64 (-1)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           vs2 (Z_to_bv 64 (Z.of_nat (length P))) vs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (tx + Z.of_nat (length T)))
           (Z_to_bv 64 35) xt3 xt4 xt5 xt6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Local Notation INV0 m := (RpLib.INV0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 tx pa lo b std T P SL m).
Local Notation INV m := (RpLib.INV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 tx pa lo b std T P SL m).

Ltac slot := first [ eapply c8_cb; eassumption | eapply cb_ex; eassumption ].
Ltac mk_inv0 := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); assumption.
Ltac mk_inv := refine (conj _ (conj _ (conj _ (conj _ _)))); [mk_inv0 | slot | slot | slot | slot].
Hypothesis BC : bcmp_contract.
Hypothesis MC : memchr_contract.
Hypothesis SLc : strlen_contract.
Hypothesis NZ : ~ In (Z_to_bv 8 0) P.
Hypothesis PAD : (- (pa + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length SL).

(* 0x132e0: n > RP_LOCK_MAX returns 0; strlen(port); stop = text + n; n = 0 returns 0; the bounds std -+ std/20 *)
Lemma rp_start : forall (m : word -> option byte) (J : list byte) (vs0 vs2 vs4 va2 : Z)
    (xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  vs0 = rate -> vs2 = tx -> vs4 = Z.of_nat (length T) -> va2 = pa ->
  rw_cells rsegs m b (CB 56 J :: SAVED) -> stk rsegs m lo b -> munch [(b, b + 160)] m0 m -> wmono rsegs m0 m ->
  mem_inv rsegs m -> bytes_at rsegs m tx T -> bytes_at rsegs m pa (P ++ Z_to_bv 8 0 :: SL) ->
  evt rsegs Q (MS (mkR xra (Z_to_bv 64 b) gp tp xt0 xt1 xt2 (Z_to_bv 64 vs0) (Z_to_bv 64 std) xa0 xa1 (Z_to_bv 64 va2)
                       xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 vs2) xs3 (Z_to_bv 64 vs4) xs5 xs6 xs7 xs8 xs9 xs10 xs11
                       xt3 xt4 xt5 xt6)
                  F (Z_to_bv 64 0x132e0) fc None m (seg_rom rsegs)).
Proof using All.
  intros m J vs0 vs2 vs4 va2 xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11
    xt3 xt4 xt5 xt6 -> -> -> -> FR ST MU WM MI BT BP.
  pose proof SLc as SLu. unfold strlen_contract in SLu.
  pose proof (bytes_at_bound _ _ _ _ BT) as BTb.
  pose proof (bytes_at_bound _ _ _ _ BP) as BPb. rewrite length_app in BPb; cbn [length] in BPb.
  pose proof (bnd_sp sp) as Rsp.
  (* 0x132e0 lui a0,0x10; bgeu a0,s4 *)
  step. step.
  destruct (Z_le_gt_dec (Z.of_nat (length T)) 65536) as [HN|HN].
  2: { br false.
       (* 0x132e8 mv s4,zero *)
       step.
       destruct (rw_split2 m b [CB 56 J] SAVED (b + 56) FR ltac:(cbn; lia)) as [F1 F2].
       eapply (rp_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 tx pa rate lo b T P SL
                 Htx Hpa HPb Hb Hlo DP);
         [ | exact F1 | reflexivity | exact F2 | exact ST | exact MU | exact WM | exact MI ].
       unfold lock_lookup. replace (65536 <? Z.of_nat (length T)) with true by (symmetry; apply Z.ltb_lt; lia).
       rewrite orb_true_r. reflexivity. }
  br true.
  (* 0x1332c sd a2,0x10(sp); mv a0,a2; jal strlen *)
  step. step. step.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply SLu with (str := P) (slack := SL);
      [ rewrite unsigned_lit by lia; rewrite ?Z.add_0_r; exact BP | exact NZ
      | rewrite unsigned_lit by lia; rewrite ?Z.add_0_r; exact PAD | exact MI ]
    | post_call segs mm ] end.
  repeat match goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.
  (* 0x13338 add s10,s2,s4; bltu s10,s2 (UBSan overflow check of text + n, trap at 0x1348c) *)
  step. step. br false.
  (* 0x13340 mv s3,a0; snez a0,s2; seqz a1,s10; xor a0,a0,a1; beqz a0 (UBSan check, trap at 0x1348c) *)
  step. step. step. step. step.
  if_false_by (ptr_ok tx (tx + Z.of_nat (length T)) ltac:(lia) ltac:(lia)).
  (* 0x13354 beqz s4: n = 0 *)
  step.
  destruct (Nat.eq_dec (length T) 0) as [N0|N0].
  { br true.
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?rest) =>
      destruct (rw_split2 _ _ [c1; c2; c3] rest (b + 56) FR ltac:(cbn; lia)) as [F1 F2] end.
    eapply (rp_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 tx pa rate lo b T P SL
              Htx Hpa HPb Hb Hlo DP);
      [ | exact F1 | reflexivity | exact F2 | eassumption | eassumption | eassumption | eassumption ].
    destruct T; [|cbn in N0; lia]. unfold lock_lookup. cbn [length Z.of_nat].
    destruct (_ || _); reflexivity. }
  br false.
  (* 0x13358 mv s4,zero; lui a0; li s11,35; addiw a0; mul a0,s1,a0; srli a0,a0,32; sub a1,s1,a0; sd a1,8(sp);
     add a0,s1,a0; sd a0,0(sp); li s1,-1 *)
  do 11 step.
  rewrite (unsigned_lit std) in FR by lia. rewrite (div20 std Hstd) in FR.
  rewrite (unsigned_lit (std / 20)) in FR by lia.
  lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?rest) =>
    destruct (rw_split2 _ _ [c1; c2; c3] rest (b + 24) FR ltac:(cbn; lia)) as [FHL FR2] end.
  lazymatch type of FR2 with rw_cells _ _ _ (?c1 :: ?rest) =>
    destruct (rw_split2 _ _ [c1] rest (b + 56) FR2 ltac:(cbn; lia)) as [F32 FS] end.
  apply (rw_cells_split_CB rsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in F32; [|reflexivity].
  cbn [app mk_CB_cells] in F32.
  lazymatch type of F32 with rw_cells _ _ _ (?c1 :: ?rest) =>
    destruct (rw_split2 _ _ [c1] rest (b + 24 + 8) F32 ltac:(cbn; lia)) as [C18 F32b] end.
  lazymatch type of F32b with rw_cells _ _ _ (?c1 :: ?rest) =>
    destruct (rw_split2 _ _ [c1] rest (b + 24 + 8 + 8) F32b ltac:(cbn; lia)) as [C20 F32c] end.
  lazymatch type of F32c with rw_cells _ _ _ (?c1 :: ?rest) =>
    destruct (rw_split2 _ _ [c1] rest (b + 24 + 8 + 8 + 8) F32c ltac:(cbn; lia)) as [C28 C30] end.
  replace (b + 24 + 8) with (b + 32) in C20 by lia.
  replace (b + 24 + 8 + 8) with (b + 40) in C28 by lia.
  replace (b + 24 + 8 + 8 + 8) with (b + 48) in C30 by lia.
  replace (b + 24 + 8) with (b + 32) in C20 by lia.
  rewrite ?Z.add_0_r.
  replace (Z_to_bv 64 tx) with (Z_to_bv 64 (tx + Z.of_nat 0)) by (f_equal; lia).
  eapply (rp_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 tx pa rate lo b std T P SL
            Htx HtxE Hpa HPb Hrate HSTD Hstd Hb Hb8 Hlo DT DP BC MC (length T) 0 0 (length T));
    [lia | lia | apply Nat.le_refl | | ].
  - unfold lock_lookup. rewrite HSTD. replace (std =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (65536 <? Z.of_nat (length T)) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - mk_inv.
Qed.

End R.

Theorem rp_lock_lookup_holds : strlen_contract -> memchr_contract -> bcmp_contract -> rp_lock_lookup_contract.
Proof.
  intros SLc MCc BCc. unfold rp_lock_lookup_contract, RP_LOCK_LOOKUP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m tx pa rate lo T P SL
    Htx HtxE BT Hpa BP NZ PAD Hrate ST HLO HSP8 DT DP MI.
  unfold RP_FRAME in HLO, DT, DP.
  pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp + -160 + 160)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ BP) as BPb. rewrite length_app in BPb; cbn [length] in BPb.
  pose proof (bytes_at_bound _ _ _ _ BT) as BTb.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (Hb : bv_unsigned sp + -160 + 160 = bv_unsigned sp) by lia.
  assert (Hb8 : (bv_unsigned sp + -160) mod 8 = 0) by lia.
  assert (Hlo : 0 <= lo <= bv_unsigned sp + -160) by lia.
  assert (DTb : tx + Z.of_nat (length T) <= bv_unsigned sp + -160 \/ bv_unsigned sp + -160 + 160 <= tx) by lia.
  assert (DPb : pa + Z.of_nat (length P + 1 + length SL) <= bv_unsigned sp + -160
                \/ bv_unsigned sp + -160 + 160 <= pa) by lia.
  assert (HPb : pa + Z.of_nat (length P + 1 + length SL) <= 2^64) by lia.
  carve_frame 160%nat ST.
  (* 0x13258 addi sp,sp,-160; sd ra, s0-s11 *)
  do 14 step.
  (* 0x13290 mv s0,a3; mv s4,a1; li a1,44100; mv s2,a0; beq a3,a1 *)
  do 6 step.
  destruct (Z.eqb_spec rate 44100) as [E1|E1].
  { subst rate. br true.
    (* 0x132d8 li s1,272109 *)
    step. step.
    eapply (rp_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m tx pa 44100 lo (bv_unsigned sp + -160)
              272109 T P SL Htx HtxE Hpa HPb (or_introl eq_refl) eq_refl (or_introl eq_refl) Hb Hb8 Hlo DTb DPb
              BCc MCc SLc NZ PAD);
      [ lia | lia | lia | lia | eassumption | eassumption | eassumption | eassumption | eassumption
      | eassumption | eassumption ]. }
  br false.
  (* 0x132a8 li a0,96000; beq s0,a0 *)
  step. step. step.
  destruct (Z.eqb_spec rate 96000) as [E2|E2].
  { subst rate. br true.
    (* 0x132cc li s1,125000; j 0x132e0 *)
    step. step. step.
    eapply (rp_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m tx pa 96000 lo (bv_unsigned sp + -160)
              125000 T P SL Htx HtxE Hpa HPb (or_intror (or_intror eq_refl)) eq_refl (or_intror (or_intror eq_refl))
              Hb Hb8 Hlo DTb DPb BCc MCc SLc NZ PAD);
      [ lia | lia | lia | lia | eassumption | eassumption | eassumption | eassumption | eassumption
      | eassumption | eassumption ]. }
  br false.
  (* 0x132b4 li a0,48000; bne s0,a0 *)
  step. step. step.
  destruct (Z.eqb_spec rate 48000) as [E3|E3].
  { subst rate. br false.
    (* 0x132c0 li s1,250000; j 0x132e0 *)
    step. step. step.
    eapply (rp_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m tx pa 48000 lo (bv_unsigned sp + -160)
              250000 T P SL Htx HtxE Hpa HPb (or_intror (or_introl eq_refl)) eq_refl (or_intror (or_introl eq_refl))
              Hb Hb8 Hlo DTb DPb BCc MCc SLc NZ PAD);
      [ lia | lia | lia | lia | eassumption | eassumption | eassumption | eassumption | eassumption
      | eassumption | eassumption ]. }
  br true.
  (* 0x132e8 mv s4,zero: std_period(rate) = 0 *)
  step.
  lazymatch goal with FR : rw_cells _ _ _ (?c1 :: ?rest) |- _ =>
    destruct (rw_split2 _ _ [c1] rest (bv_unsigned sp + -160 + 56) FR ltac:(cbn; lia)) as [F1 F2] end.
  eapply (rp_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m tx pa rate lo (bv_unsigned sp + -160) T P SL
            Htx Hpa HPb Hb Hlo DPb);
    [ | exact F1 | reflexivity | exact F2 | eassumption | eassumption | eassumption | eassumption ].
  unfold lock_lookup, std_period.
  rewrite (proj2 (Z.eqb_neq _ _) E1), (proj2 (Z.eqb_neq _ _) E3), (proj2 (Z.eqb_neq _ _) E2). reflexivity.
Qed.
