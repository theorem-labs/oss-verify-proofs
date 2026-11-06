(** The walk of musl strcasecmp in the ubsan image (U/Prog/strcasecmp_c.v), written new for reac-pw/fuzz_segconf on the
    pattern of omx-clap-core/fuzz_manifest's strncasecmp walk (lib/Prog/strncasecmp.v at 25e3d17bdb50): the same
    loop without the counter. tolower is a premise (tolower_contract, U/Prog/tolower_c.v).

    Code (plain addresses; this ubsan copy is the same 160 bytes at 0x1f3c4 = plain + 0x99c, tolower at 0x1f464):
      0x1ea28-0x1ea38  frame of 32: ra s0 s1 s2 at sp+24 .. sp+0
      0x1ea3c lbu a2,0(a0); 0x1ea40 mv s0,a1; 0x1ea44 beqz a2 -> 0x1ea94; 0x1ea48 addi s2,a0,1; 0x1ea4c j 0x1ea60
      NEXT 0x1ea50 lbu a2,0(s2); s0++; s2++; 0x1ea5c beqz a2 -> 0x1ea8c
      LOOP 0x1ea60 lbu a0,0(s0); 0x1ea64 beqz a0 -> 0x1ea8c; 0x1ea68 beq a2,a0 -> NEXT;
           0x1ea6c-0x1ea80 s1 = tolower(a2), a0 = tolower(r[i]); 0x1ea84 beq s1,a0 -> NEXT; 0x1ea88 lbu a2,-1(s2)
      0x1ea8c andi a0,a2,0xff; 0x1ea90 j 0x1ea98; 0x1ea94 mv a0,zero
      FIN  0x1ea98 tolower(a0) -> s0, tolower(r[i]); 0x1eaac subw a0,s0,a0; restore; ret *)
From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import tolower_c strcasecmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_word_eq_tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require StepFast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.zstep ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.StepFast.sf_zstep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_word_eq_tac ].
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Stor0fe.sb_mem_after_store.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require AndN.
Import ListNotations.
Open Scope Z_scope.

Lemma zlower_zero : forall x, 0 <= x < 256 -> (zlower x = 0 <-> x = 0).
Proof. intros x Hx. unfold zlower. destruct (65 <=? x) eqn:E1; destruct (x <=? 90) eqn:E2; cbn; lia. Qed.

Lemma zlower_range : forall x, 0 <= x < 256 -> 0 <= zlower x < 256.
Proof. intros x Hx. unfold zlower. destruct (65 <=? x) eqn:E1; destruct (x <=? 90) eqn:E2; cbn;
  rewrite ?Z.leb_le, ?Z.leb_gt in *; lia. Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R. Qed.

Lemma u_byte : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intros b. apply unsigned_lit. pose proof (byte_range b). lia. Qed.

Lemma u_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. exact u_byte. Qed.

Lemma land255 : forall b : byte, Z.land (bv_unsigned b) 255 = bv_unsigned b.
Proof.
  intros b. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small.
  pose proof (byte_range b). change (2 ^ 8) with 256. lia.
Qed.

Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

Lemma list_ext_nth : forall {A} (l l' : list A), (forall n, nth_error l n = nth_error l' n) -> l = l'.
Proof.
  induction l as [|x l IH]; intros [|y l'] H.
  - reflexivity.
  - specialize (H 0%nat). discriminate.
  - specialize (H 0%nat). discriminate.
  - pose proof (H 0%nat) as H0. cbn in H0. inversion H0; subst. f_equal. apply IH. intros n. exact (H (S n)).
Qed.

Lemma nth_full : forall (s : list byte) i, (i <= length s)%nat -> exists b, nth_error (s ++ [Z_to_bv 8 0]) i = Some b.
Proof.
  intros s i H. destruct (nth_error (s ++ [Z_to_bv 8 0]) i) as [b|] eqn:E; [eauto|].
  apply nth_error_None in E. rewrite length_app in E. cbn in E. lia.
Qed.

Lemma nth_full_zero : forall (s : list byte) i b, ~ In (Z_to_bv 8 0) s ->
  nth_error (s ++ [Z_to_bv 8 0]) i = Some b -> (bv_unsigned b = 0 <-> i = length s).
Proof.
  intros s i b NZ E. pose proof (nth_error_lt _ _ _ E) as Hl. rewrite length_app in Hl. cbn in Hl.
  destruct (Nat.eq_dec i (length s)) as [->|NE].
  - rewrite nth_error_app2, Nat.sub_diag in E by lia. cbn in E. inversion E; subst. split; reflexivity.
  - rewrite nth_error_app1 in E by lia. split; [|intros; lia]. intros Hb. exfalso. apply NZ.
    replace (Z_to_bv 8 0) with b; [eapply nth_error_In; eauto|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.

Lemma map_u_app0 : forall (s : list byte), map bv_unsigned (s ++ [Z_to_bv 8 0]) = map bv_unsigned s ++ [0].
Proof. intros s. rewrite map_app. reflexivity. Qed.

(** [lower_eq] on the strings is equality after tolower of the strings with their NUL. *)
Lemma lower_eq_full : forall ls rs,
  lower_eq ls rs <-> map zlower (map bv_unsigned ls ++ [0]) = map zlower (map bv_unsigned rs ++ [0]).
Proof.
  intros ls rs. unfold lower_eq. rewrite !map_app. cbn [map]. split; intros H.
  - rewrite H. reflexivity.
  - apply app_inj_tail in H. destruct H as [H _]. exact H.
Qed.

Lemma nth_case : forall (s : list byte) j,
  nth_error (map zlower (map bv_unsigned s ++ [0])) j =
  option_map (fun b => zlower (bv_unsigned b)) (nth_error (s ++ [Z_to_bv 8 0]) j).
Proof.
  intros s j. rewrite <- map_u_app0, nth_error_map, nth_error_map. destruct (nth_error _ j); reflexivity.
Qed.

(** The loop stops at index k (a NUL on either side, or lowered bytes that differ) after agreeing below k: the
    lowered bytes at k agree exactly when the strings agree after tolower. *)
Lemma case_stop : forall (ls rs : list byte) (k : nat) (b1 b2 : byte),
  ~ In (Z_to_bv 8 0) ls -> ~ In (Z_to_bv 8 0) rs ->
  nth_error (ls ++ [Z_to_bv 8 0]) k = Some b1 -> nth_error (rs ++ [Z_to_bv 8 0]) k = Some b2 ->
  (forall j, (j < k)%nat -> exists x y, nth_error ls j = Some x /\ nth_error rs j = Some y /\
                                  zlower (bv_unsigned x) = zlower (bv_unsigned y)) ->
  (bv_unsigned b1 = 0 \/ bv_unsigned b2 = 0 \/ zlower (bv_unsigned b1) <> zlower (bv_unsigned b2)) ->
  (zlower (bv_unsigned b1) = zlower (bv_unsigned b2) <-> lower_eq ls rs).
Proof.
  intros ls rs k b1 b2 NL NR E1 E2 P D. rewrite lower_eq_full.
  pose proof (byte_range b1) as R1. pose proof (byte_range b2) as R2.
  split.
  - intros Heq. apply list_ext_nth. intros j. rewrite !nth_case.
    destruct (Nat.lt_trichotomy j k) as [Jk|[->|Jk]].
    + destruct (P j Jk) as (x & y & Ex & Ey & Exy).
      rewrite nth_error_app1 by (eapply nth_error_lt; eauto). rewrite (nth_error_app1 rs) by (eapply nth_error_lt; eauto).
      rewrite Ex, Ey. cbn. rewrite Exy. reflexivity.
    + rewrite E1, E2. cbn. rewrite Heq. reflexivity.
    + destruct D as [Z1|[Z2|Dif]].
      * assert (Z2 : bv_unsigned b2 = 0).
        { apply zlower_zero; [exact R2|]. rewrite <- Heq. apply zlower_zero; [exact R1| exact Z1]. }
        apply (nth_full_zero ls k b1 NL E1) in Z1. apply (nth_full_zero rs k b2 NR E2) in Z2.
        rewrite !(proj2 (nth_error_None _ _)) by (rewrite length_app; cbn; lia). reflexivity.
      * assert (Z1 : bv_unsigned b1 = 0).
        { apply zlower_zero; [exact R1|]. rewrite Heq. apply zlower_zero; [exact R2| exact Z2]. }
        apply (nth_full_zero ls k b1 NL E1) in Z1. apply (nth_full_zero rs k b2 NR E2) in Z2.
        rewrite !(proj2 (nth_error_None _ _)) by (rewrite length_app; cbn; lia). reflexivity.
      * contradiction.
  - intros Heq. apply (f_equal (fun l => nth_error l k)) in Heq. rewrite !nth_case in Heq.
    rewrite E1, E2 in Heq. cbn in Heq. inversion Heq. reflexivity.
Qed.

Lemma sub_lower_zero : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  (Z_to_bv 64 (bv_swrap 32 (zlower x - zlower y)) = Z_to_bv 64 0 <-> zlower x = zlower y).
Proof.
  intros x y Hx Hy. pose proof (zlower_range x Hx) as Lx. pose proof (zlower_range y Hy) as Ly.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia).
  split; intros Heq.
  - apply (f_equal bv_unsigned) in Heq. rewrite !unsigned_lit_wrap in Heq. rewrite Z.mod_0_l in Heq by lia.
    Z.div_mod_to_equations. nia.
  - rewrite Heq, Z.sub_diag. reflexivity.
Qed.

Theorem strcasecmp_holds : tolower_contract -> strcasecmp_contract.
Proof.
  intros TL. unfold tolower_contract, TOLOWER in TL.
  unfold strcasecmp_contract, STRCASECMP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs lo
         ST HL NL HR NR MI LO SL SR.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ HL) as BL. pose proof (bytes_at_bound _ _ _ _ HR) as BR.
  rewrite length_app in BL, BR. cbn [length] in BL, BR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  carve_frame 32%nat ST.
  zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into M1 end.
  (* FIN 0x1f434: a0 = l[k], s0 = r + k; two tolower calls, subw, return. *)
  assert (FIN : forall (k : nat) (b1 b2 : byte) (x1 x8 x9 x11 x12 x18 : word),
    nth_error (ls ++ [Z_to_bv 8 0]) k = Some b1 -> nth_error (rs ++ [Z_to_bv 8 0]) k = Some b2 ->
    (forall j, (j < k)%nat -> exists x y, nth_error ls j = Some x /\ nth_error rs j = Some y /\
                                    zlower (bv_unsigned x) = zlower (bv_unsigned y)) ->
    (bv_unsigned b1 = 0 \/ bv_unsigned b2 = 0 \/ zlower (bv_unsigned b1) <> zlower (bv_unsigned b2)) ->
    bv_unsigned x8 = bv_unsigned a1 + Z.of_nat k ->
    evt rsegs (strcasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs lo m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (bv_unsigned b1))
               x11 x12 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1f434) fc None M1 (seg_rom rsegs))).
  { intros k b1 b2 x1 x8 x9 x11 x12 x18 E1 E2 P D H8.
    pose proof (byte_range b1) as R1. pose proof (byte_range b2) as R2.
    pose proof (nth_error_lt _ _ _ E2) as Lk2. rewrite length_app in Lk2. cbn [length] in Lk2.
    assert (RD2 : ov_read_bytes rsegs M1 x8 1 = Some [b2]).
    { apply (u8ro_read rsegs M1 (bv_unsigned a1) (rs ++ [Z_to_bv 8 0]) (Z.of_nat k) b2 x8 HR);
        [rewrite Nat2Z.id; exact E2 | lia | unfold wa; rewrite <- H8; symmetry; apply Z_to_bv_lit_self]. }
    zstep.
    eapply evt_cut. { eapply TL. rewrite ?u_zxb, ?u_byte. exact R1. }
    intros ms' [y11 ->]. fix_ret. rewrite ?u_zxb, ?u_byte.
    zstep. zstep. zstep. zstep.
    eapply evt_cut. { eapply TL. rewrite ?u_zxb, ?u_byte. exact R2. }
    intros ms' [y11' ->]. fix_ret. rewrite ?u_zxb, ?u_byte.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    pose proof (zlower_range _ R1) as ZR1. pose proof (zlower_range _ R2) as ZR2.
    rewrite (Z.mod_small (zlower (bv_unsigned b1)) 18446744073709551616) by lia.
    rewrite (Z.mod_small (zlower (bv_unsigned b2)) 18446744073709551616) by lia.
    apply evt_done. unfold strcasecmp_post.
    repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact HL|].
    split; [exact HR|].
    rewrite (sub_lower_zero _ _ R1 R2).
    exact (case_stop ls rs k b1 b2 NL NR E1 E2 P D). }
  (* LOOP 0x1f3fc: a2 = l[i] (not NUL), s0 = r + i, s2 = l + i + 1; well-founded on length ls - i. *)
  assert (LOOP : forall (k i : nat) (b1 : byte) (x1 x8 x9 x10 x11 x18 : word),
    (length ls - i = k)%nat -> (i < length ls)%nat ->
    nth_error ls i = Some b1 ->
    (forall j, (j < i)%nat -> exists x y, nth_error ls j = Some x /\ nth_error rs j = Some y /\
                                    zlower (bv_unsigned x) = zlower (bv_unsigned y)) ->
    bv_unsigned x8 = bv_unsigned a1 + Z.of_nat i ->
    bv_unsigned x18 = bv_unsigned a0 + Z.of_nat i + 1 ->
    evt rsegs (strcasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs lo m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 x8 x9 x10 x11 (Z_to_bv 64 (bv_unsigned b1))
               a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1f3fc) fc None M1 (seg_rom rsegs))).
  { induction k as [k IH] using lt_wf_ind.
    intros i b1 x1 x8 x9 x10 x11 x18 Hk Hil E1 P H8 H18.
    pose proof (byte_range b1) as R1.
    assert (NZ1 : bv_unsigned b1 <> 0).
    { intros Zb. apply NL. replace (Z_to_bv 8 0) with b1; [eapply nth_error_In; eauto|].
      apply bv_eq. rewrite Zb. reflexivity. }
    assert (E1f : nth_error (ls ++ [Z_to_bv 8 0]) i = Some b1) by (rewrite nth_error_app1 by lia; exact E1).
    assert (Iy : (i <= length rs)%nat).
    { destruct i as [|i']; [lia|]. destruct (P i' ltac:(lia)) as (x & y & _ & Ey & _).
      apply nth_error_lt in Ey. lia. }
    destruct (nth_full rs i Iy) as [b2 E2]. pose proof (byte_range b2) as R2.
    pose proof (zlower_range _ R1) as ZR1. pose proof (zlower_range _ R2) as ZR2.
    assert (RD2 : ov_read_bytes rsegs M1 x8 1 = Some [b2]).
    { apply (u8ro_read rsegs M1 (bv_unsigned a1) (rs ++ [Z_to_bv 8 0]) (Z.of_nat i) b2 x8 HR);
        [rewrite Nat2Z.id; exact E2 | lia | unfold wa; rewrite <- H8; symmetry; apply Z_to_bv_lit_self]. }
    (* NEXT 0x1f3ec: index i agreed (r[i] not NUL); read l[i+1], step both pointers. *)
    assert (NEXT : zlower (bv_unsigned b1) = zlower (bv_unsigned b2) -> bv_unsigned b2 <> 0 ->
        forall (y1 y9 y10 y11 y12 : word),
        evt rsegs (strcasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs lo m)
          (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 x8 y9 y10 y11
                   y12 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1f3ec) fc None M1 (seg_rom rsegs))).
    { intros Heq NZ2 y1 y9 y10 y11 y12.
      assert (Iy' : (S i <= length rs)%nat).
      { destruct (Nat.eq_dec i (length rs)) as [Ei|]; [|lia]. exfalso. apply NZ2.
        apply (nth_full_zero rs i b2 NR E2). exact Ei. }
      destruct (nth_full ls (S i) ltac:(lia)) as [b1' E1']. destruct (nth_full rs (S i) Iy') as [b2' E2'].
      pose proof (byte_range b1') as R1'.
      assert (P' : forall j, (j < S i)%nat -> exists x y, nth_error ls j = Some x /\ nth_error rs j = Some y /\
                                    zlower (bv_unsigned x) = zlower (bv_unsigned y)).
      { intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [|apply P; lia].
        exists b1, b2. split; [exact E1|]. split; [|exact Heq].
        rewrite nth_error_app1 in E2; [exact E2|]. destruct (Nat.eq_dec i (length rs)) as [Ei|]; [|lia].
        exfalso. apply NZ2. apply (nth_full_zero rs i b2 NR E2). exact Ei. }
      assert (RD1 : ov_read_bytes rsegs M1 x18 1 = Some [b1']).
      { apply (u8ro_read rsegs M1 (bv_unsigned a0) (ls ++ [Z_to_bv 8 0]) (Z.of_nat (S i)) b1' x18 HL);
          [rewrite Nat2Z.id; exact E1' | lia | unfold wa; rewrite <- (Z_to_bv_lit_self x18); f_equal; lia]. }
      zstep. zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?u_zxb, ?u_byte in K; cbv iota.
      - zstep. zstep. rewrite ?u_zxb, ?u_byte, ?land255.
        eapply FIN with (k := S i); [exact E1' | exact E2' | exact P' | left; exact K | ].
        rewrite unsigned_lit by lia. lia.
      - assert (Il : (S i < length ls)%nat).
        { destruct (Nat.eq_dec (S i) (length ls)) as [Ei|]; [|lia]. exfalso. apply K.
          apply (nth_full_zero ls (S i) b1' NL E1'). exact Ei. }
        rewrite nth_error_app1 in E1' by lia.
        eapply (IH (length ls - S i)%nat); [lia | reflexivity | exact Il | exact E1' | exact P' | | ];
          rewrite unsigned_lit by lia; lia. }
    step. step. if_cases K1; zify_cond K1; rewrite ?u_zxb, ?u_byte in K1; cbv iota.
    - zstep. zstep. rewrite ?u_zxb, ?u_byte, ?land255.
      eapply FIN with (k := i); [exact E1f | exact E2 | exact P | right; left; exact K1 | exact H8].
    - zstep. if_cases K3; zify_cond K3; rewrite ?u_zxb, ?u_byte in K3; cbv iota.
      + apply NEXT; [rewrite K3; reflexivity | lia].
      + zstep. rewrite ?u_zxb, ?u_byte, ?land255.
        zstep.
        eapply evt_cut. { eapply TL. rewrite ?u_zxb, ?u_byte. exact R1. }
        intros ms' [y11 ->]. fix_ret. rewrite ?u_zxb, ?u_byte.
        zstep. zstep. zstep. zstep.
        eapply evt_cut. { eapply TL. rewrite ?u_zxb, ?u_byte. exact R2. }
        intros ms' [y11' ->]. fix_ret. rewrite ?u_zxb, ?u_byte.
        zstep. if_cases K4; zify_cond K4; rewrite ?Z.mod_small in K4 by lia; cbv iota.
        * apply NEXT; [exact K4 | lia].
        * assert (RD1b : ov_read_bytes rsegs M1 (Z_to_bv 64 (bv_unsigned x18 + -1)) 1 = Some [b1]).
          { apply (u8ro_read rsegs M1 (bv_unsigned a0) (ls ++ [Z_to_bv 8 0]) (Z.of_nat i) b1 _ HL);
              [rewrite Nat2Z.id; exact E1f | lia | unfold wa; f_equal; lia]. }
          zstep. zstep. zstep. rewrite ?u_zxb, ?u_byte, ?land255.
          eapply FIN with (k := i); [exact E1f | exact E2 | exact P | right; right; exact K4 | exact H8]. }
  (* Entry: l[0]; NUL goes to FIN with a0 = 0, else LOOP at i = 0. *)
  destruct (nth_full ls 0 ltac:(lia)) as [b10 E10]. pose proof (byte_range b10) as R10.
  assert (RD0 : ov_read_bytes rsegs M1 a0 1 = Some [b10]).
  { apply (u8ro_read rsegs M1 (bv_unsigned a0) (ls ++ [Z_to_bv 8 0]) 0 b10 a0 HL);
      [exact E10 | lia | unfold wa; rewrite Z.add_0_r; symmetry; apply Z_to_bv_lit_self]. }
  zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?u_zxb, ?u_byte in K; cbv iota.
  - zstep.
    destruct (nth_full rs 0 ltac:(lia)) as [b20 E20].
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (bv_unsigned b10)) by (rewrite K; reflexivity).
    eapply FIN with (k := 0%nat); [exact E10 | exact E20 | intros j Hj; lia | left; exact K | lia].
  - zstep. zstep.
    assert (Il : (0 < length ls)%nat).
    { destruct (Nat.eq_dec 0 (length ls)) as [Ei|]; [|lia]. exfalso. apply K.
      apply (nth_full_zero ls 0 b10 NL E10). exact Ei. }
    rewrite nth_error_app1 in E10 by lia.
    eapply (LOOP (length ls - 0)%nat 0%nat); [reflexivity | exact Il | exact E10 | intros j Hj; lia | | ];
      rewrite ?unsigned_lit by lia; lia.
Qed.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Image.
Open Scope Z_scope.

(** ** Satisfiability of the premises

    A closed instance of every premise of strcasecmp_contract in the shape of parse_file's first call (ubsan 0x15628,
    `strcasecmp(key, "role")`: a1 = 0x10298, the read-only .rodata bytes "role" NUL of the image; a0 = the key, a
    writable NUL-terminated string above the callee's frame, as parse_file's line buffer is): the key "Role" at KEY_W,
    a 4096-byte stack below SP_W, no other byte in the memory. The two strings agree after tolower. *)
Definition SP_W : Z := 0x7ffff000.
Definition LO_W : Z := 0x7fffe000.
Definition KEY_W : Z := 0x7ffff100.
Definition ROLE : Z := 0x10298.
Definition key_w : list byte := map (Z_to_bv 8) [82; 111; 108; 101].
Definition role_w : list byte := map (Z_to_bv 8) [114; 111; 108; 101].

Definition m_w (x : word) : option byte :=
  if (LO_W <=? bv_unsigned x) && (bv_unsigned x <? SP_W) then Some (Z_to_bv 8 0)
  else if (KEY_W <=? bv_unsigned x) && (bv_unsigned x <? KEY_W + 5)
  then nth_error (key_w ++ [Z_to_bv 8 0]) (Z.to_nat (bv_unsigned x - KEY_W))
  else None.

Lemma find_segment_above_w : forall (sl : list Segment) top a n,
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sl = true ->
  top <= a -> 0 < n -> find_segment sl a n = None.
Proof.
  induction sl as [|sg rest IH]; intros top a n Hall Ha Hn; cbn [find_segment]; [reflexivity|].
  cbn [forallb] in Hall. apply andb_prop in Hall as [H1 H2]. apply Z.leb_le in H1.
  destruct (Z.leb_spec (Z.of_N (seg_base sg)) a); cbn [andb];
    [ destruct (Z.leb_spec (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))); [lia|] |];
    eapply IH; eauto.
Qed.

Lemma rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x100000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma m_w_inv : mem_inv rsegs m_w.
Proof.
  intros x b Hx. unfold m_w in Hx.
  assert (Hhi : 0x100000 <= bv_unsigned x).
  { destruct ((LO_W <=? bv_unsigned x) && (bv_unsigned x <? SP_W)) eqn:E1.
    - apply andb_prop in E1 as [E1 _]. apply Z.leb_le in E1. unfold LO_W in E1. lia.
    - destruct ((KEY_W <=? bv_unsigned x) && (bv_unsigned x <? KEY_W + 5)) eqn:E2; [|discriminate].
      apply andb_prop in E2 as [E2 _]. apply Z.leb_le in E2. unfold KEY_W in E2. lia. }
  unfold ro_addr. rewrite (find_segment_above_w rsegs 0x100000) by first [exact rsegs_top | lia]. reflexivity.
Qed.

Lemma m_w_stk : stk rsegs m_w LO_W SP_W.
Proof.
  split; [unfold LO_W; lia|]. split; [unfold SP_W; lia|].
  intros a Ha. unfold LO_W, SP_W in Ha.
  assert (E : m_w (wa a) = Some (Z_to_bv 8 0)).
  { unfold m_w. rewrite wa_unsigned by lia.
    replace ((LO_W <=? a) && (a <? SP_W)) with true; [reflexivity|].
    symmetry. apply andb_true_intro. unfold LO_W, SP_W. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  split.
  - unfold wview. rewrite E. cbv iota. discriminate.
  - exists (Z_to_bv 8 0). unfold mrd. rewrite E. reflexivity.
Qed.

Lemma m_w_key : bytes_at rsegs m_w KEY_W (key_w ++ [Z_to_bv 8 0]).
Proof.
  split; [cbv [KEY_W]; lia|]. split; [cbv [KEY_W]; cbn; lia|].
  intros i Hi. cbn in Hi.
  destruct i as [|[|[|[|[|i]]]]]; try lia; vm_compute; reflexivity.
Qed.

Lemma role_at : bytes_at rsegs m_w ROLE (role_w ++ [Z_to_bv 8 0]).
Proof.
  apply (ro_bytes_at rsegs m_w); [exact m_w_inv | cbv [ROLE]; lia | cbv [ROLE]; cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma strcasecmp_sat :
  let sp := Z_to_bv 64 SP_W in let a0 := Z_to_bv 64 KEY_W in let a1 := Z_to_bv 64 ROLE in
  stk rsegs m_w LO_W (bv_unsigned sp) /\
  bytes_at rsegs m_w (bv_unsigned a0) (key_w ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) key_w /\
  bytes_at rsegs m_w (bv_unsigned a1) (role_w ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) role_w /\
  mem_inv rsegs m_w /\
  LO_W <= bv_unsigned sp - 32 /\
  (bv_unsigned a0 + Z.of_nat (length key_w) + 1 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0) /\
  (bv_unsigned a1 + Z.of_nat (length role_w) + 1 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a1) /\
  lower_eq key_w role_w.
Proof.
  cbv zeta. rewrite !unsigned_lit by (cbv [SP_W KEY_W ROLE]; lia).
  split; [exact m_w_stk|]. split; [exact m_w_key|].
  split; [unfold key_w; cbn [map In]; intros [H|[H|[H|[H|[]]]]]; apply (f_equal bv_unsigned) in H;
          vm_compute in H; discriminate|].
  split; [exact role_at|].
  split; [unfold role_w; cbn [map In]; intros [H|[H|[H|[H|[]]]]]; apply (f_equal bv_unsigned) in H;
          vm_compute in H; discriminate|].
  split; [exact m_w_inv|].
  split; [cbv [LO_W SP_W]; lia|].
  split; [right; cbv [SP_W KEY_W]; lia|].
  split; [left; change (length role_w) with 4%nat; cbv [ROLE SP_W]; lia|].
  unfold lower_eq. vm_compute. reflexivity.
Qed.
