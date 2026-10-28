(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require W_sub_part_words.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop AsLeaf. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import AW_sub_words.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2411172 => 1
  | 2411176 => 1
  | 2411180 => 2
  | 2411184 => 1
  | 2411188 => 1
  | 2411192 => 1
  | 2411196 => 1
  | 2411200 => 2
  | 2411204 => 1
  | 2411208 => 1
  | 2411212 => 1
  | 2411216 => 2
  | 2411220 => 1
  | 2411224 => 1
  | 2411228 => 1
  | 2411232 => 2
  | 2411236 => 1
  | 2411240 => 1
  | 2411244 => 1
  | 2411248 => 2
  | 2411252 => 1
  | 2411256 => 1
  | 2411260 => 1
  | 2411264 => 2
  | 2411280 => 1
  | 2411284 => 1
  | 2411332 => 1
  | 2411336 => 1
  | 2411340 => 1
  | 2411360 => 1
  | 2411368 => 2
  | 2411372 => 2
  | 2411380 => 2
  | 2411384 => 2
  | 2411432 => 2
  | 2411436 => 2
  | 2411508 => 2
  | 2411512 => 2
  | 2411588 => 2
  | 2411592 => 2
  | 2411668 => 2
  | 2411672 => 2
  | 2411748 => 1
  | 2411752 => 2
  | 2411756 => 2
  | 2411760 => 2
  | 2411768 => 2
  | 2411800 => 1
  | 2411804 => 1
  | 2411812 => 1
  | 2411828 => 1
  | 2411888 => 2
  | 2411892 => 2
  | 2411968 => 2
  | 2411972 => 2
  | 2412044 => 2
  | 2412048 => 2
  | 2412124 => 2
  | 2412128 => 2
  | 2412180 => 2
  | 2412184 => 1
  | 2412188 => 2
  | 2412192 => 2
  | 2412200 => 2
  | 2412216 => 1
  | 2412224 => 1
  | 2412232 => 1
  | 2412244 => 1
  | 2412288 => 2
  | 2412292 => 2
  | 2412348 => 2
  | 2412352 => 2
  | 2412408 => 2
  | 2412412 => 2
  | 2412472 => 2
  | 2412476 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Definition bn_sub_part_words_aentry := 0x24ca34%Z.

(* [comment removed for export] *)
Notation pos_fl := W_sub_part_words.pos_fl.
Notation pos_fc := W_sub_part_words.pos_fc.
Notation neg_fl := W_sub_part_words.neg_fl.
Notation neg_fc := W_sub_part_words.neg_fc.
Notation sub_part_pos_gen := W_sub_part_words.sub_part_pos_gen.
Notation sub_part_neg_gen := W_sub_part_words.sub_part_neg_gen.
Notation pos_fc_range := W_sub_part_words.pos_fc_range.
Notation neg_fc_range := W_sub_part_words.neg_fc_range.

Definition spw_apost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp : Z) (a b : list Z) (cl : nat) (N : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  wl_post bsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp N 224%Z
          (fst (sub_part_words a b cl)) (snd (sub_part_words a b cl)) lo m.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (cl da db : nat) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation bp := (bv_unsigned a2).
  Notation SP := (bv_unsigned sp).
  Notation N := (Z.of_nat (cl + da + db)).
  Hypothesis LA : limbs a.
  Hypothesis LB : limbs b.
  Hypothesis HLA : length a = (cl + da)%nat.
  Hypothesis HLB : length b = (cl + db)%nat.
  Hypothesis DAB : (da = 0 \/ db = 0)%nat.
  Hypothesis N31 : (N < 2147483648)%Z.
  Hypothesis A3 : bv_unsigned a3 = Z.of_nat cl.
  Hypothesis A4 : a4 = Z_to_bv 64 (Z.of_nat da - Z.of_nat db).
  Hypothesis RA : limbs_at bsegs m ap a.
  Hypothesis RB : limbs_at bsegs m bp b.
  Hypothesis WR : wr_at bsegs m rp (8 * N).
  Hypothesis ALA : (rp = ap \/ rp + 8 * N <= ap \/ ap + 8 * Z.of_nat (length a) <= rp)%Z.
  Hypothesis ALB : (rp = bp \/ rp + 8 * N <= bp \/ bp + 8 * Z.of_nat (length b) <= rp)%Z.
  Hypothesis STK : stk bsegs m lo SP.
  Hypothesis LO : (lo <= SP - 224)%Z.
  Hypothesis SEPR : (rp + 8 * N <= SP - 224 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * Z.of_nat (length a) <= SP - 224 \/ SP <= ap)%Z.
  Hypothesis SEPB : (bp + 8 * Z.of_nat (length b) <= SP - 224 \/ SP <= bp)%Z.
  Hypothesis MI0 : mem_inv bsegs m.
  (* [comment removed for export] *)
  Hypothesis SHBC : shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
  Hypothesis ACR : acc bsegs m rp (8 * N).
  Hypothesis ACA : acc bsegs m ap (8 * Z.of_nat (length a)).
  Hypothesis ACB : acc bsegs m bp (8 * Z.of_nat (length b)).
  Hypothesis APT : aptrs3 rp ap bp N lo.

  Hypothesis UBR : ub_ptr_ok 1 (bv_unsigned a0).
  Hypothesis UBA : ub_ptr_ok 1 (bv_unsigned a1).
  Hypothesis UBB : ub_ptr_ok 1 (bv_unsigned a2).

  Notation POST := (spw_apost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) a b cl N lo m).
  Notation Wfin := [(bv_unsigned a0, bv_unsigned a0 + 8 * Z.of_nat (cl + da + db)); (bv_unsigned sp - 224, bv_unsigned sp)]%Z.
  Notation r1 := (fst (sub_words (firstn cl a) (firstn cl b))).
  Notation c1 := (snd (sub_words (firstn cl a) (firstn cl b))).

  (* [comment removed for export] *)
  Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation FCELLS jb := [CB 8 jb; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation CL8 := (8 * Z.of_nat cl)%Z.

  Lemma FBE : (bv_unsigned sp + -112 = bv_unsigned sp - 112)%Z. Proof. lia. Qed.
  Lemma LENa : length (skipn cl a) = length (skipn cl a). Proof. reflexivity. Qed.
  Lemma LENb : length (skipn cl b) = length (skipn cl b). Proof. reflexivity. Qed.
  Lemma Hska : length (skipn cl a) = da. Proof. rewrite length_skipn. lia. Qed.
  Lemma Hskb : length (skipn cl b) = db. Proof. rewrite length_skipn. lia. Qed.
  Lemma ALAt : alias_ok (rp + CL8) (ap + CL8) (Z.of_nat (length (skipn cl a))).
  Proof. unfold alias_ok. rewrite Hska. clear - ALA HLA. lia. Qed.
  Lemma ALBt : alias_ok (rp + CL8) (bp + CL8) (Z.of_nat (length (skipn cl b))).
  Proof. unfold alias_ok. rewrite Hskb. clear - ALB HLB. lia. Qed.
  Lemma SEPRa : (rp + CL8 + 8 * Z.of_nat (length (skipn cl a)) <= SP - 112 \/ SP <= rp + CL8)%Z.
  Proof. rewrite Hska. clear - SEPR. lia. Qed.
  Lemma SEPRb : (rp + CL8 + 8 * Z.of_nat (length (skipn cl b)) <= SP - 112 \/ SP <= rp + CL8)%Z.
  Proof. rewrite Hskb. clear - SEPR. lia. Qed.
  Lemma SEPAt : (ap + CL8 + 8 * Z.of_nat (length (skipn cl a)) <= SP - 112 \/ SP <= ap + CL8)%Z.
  Proof. rewrite Hska. clear - SEPA HLA. lia. Qed.
  Lemma SEPBt : (bp + CL8 + 8 * Z.of_nat (length (skipn cl b)) <= SP - 112 \/ SP <= bp + CL8)%Z.
  Proof. rewrite Hskb. clear - SEPB HLB. lia. Qed.

  (* [comment removed for export] *)
  Notation PINV m2 jb := (INV bsegs pos_fl pos_fc 1 m2 (bv_unsigned a0 + CL8) (bv_unsigned a1 + CL8) (bv_unsigned a1 + CL8) (bv_unsigned sp) lo (skipn cl a)
                        112%Z (bv_unsigned sp + -112)%Z (FCELLS jb) (fst (sub_part_pos (skipn cl a) c1)) (snd (sub_part_pos (skipn cl a) c1))).
  Notation PKIT m2 jb L := (L bsegs pos_fl pos_fc 1%Z pos_fc_range m2 (bv_unsigned a0 + CL8)%Z (bv_unsigned a1 + CL8)%Z (bv_unsigned a1 + CL8)%Z (bv_unsigned sp) lo
                        (skipn cl a) (skipn cl a) 112%Z (bv_unsigned sp + -112)%Z (FCELLS jb) eq_refl FBE LENa ALAt ALAt SEPRa SEPAt SEPAt
                        (fst (sub_part_pos (skipn cl a) c1)) (snd (sub_part_pos (skipn cl a) c1))).
  Notation NINV m2 jb := (INV bsegs neg_fl neg_fc 1 m2 (bv_unsigned a0 + CL8) (bv_unsigned a2 + CL8) (bv_unsigned a2 + CL8) (bv_unsigned sp) lo (skipn cl b)
                        112%Z (bv_unsigned sp + -112)%Z (FCELLS jb) (fst (sub_part_neg (skipn cl b) c1)) (snd (sub_part_neg (skipn cl b) c1))).
  Notation NKIT m2 jb L := (L bsegs neg_fl neg_fc 1%Z neg_fc_range m2 (bv_unsigned a0 + CL8)%Z (bv_unsigned a2 + CL8)%Z (bv_unsigned a2 + CL8)%Z (bv_unsigned sp) lo
                        (skipn cl b) (skipn cl b) 112%Z (bv_unsigned sp + -112)%Z (FCELLS jb) eq_refl FBE LENb ALBt ALBt SEPRb SEPBt SEPBt
                        (fst (sub_part_neg (skipn cl b) c1)) (snd (sub_part_neg (skipn cl b) c1))).
  (* [comment removed for export] *)
  Notation PPB := (apure (bv_unsigned a0 + CL8) (bv_unsigned a1 + CL8) (bv_unsigned a1 + CL8) (Z.of_nat (length (skipn cl a))) (bv_unsigned sp) 112%Z).
  Notation NPB := (apure (bv_unsigned a0 + CL8) (bv_unsigned a2 + CL8) (bv_unsigned a2 + CL8) (Z.of_nat (length (skipn cl b))) (bv_unsigned sp) 112%Z).
  Notation PSH m2 jb L := (L bsegs pos_fl pos_fc 1%Z m2 (bv_unsigned a0 + CL8)%Z (bv_unsigned a1 + CL8)%Z (bv_unsigned a1 + CL8)%Z (bv_unsigned sp) lo
                        (skipn cl a) 112%Z (bv_unsigned sp + -112)%Z (FCELLS jb) (fst (sub_part_pos (skipn cl a) c1)) (snd (sub_part_pos (skipn cl a) c1))).
  Notation NSH m2 jb L := (L bsegs neg_fl neg_fc 1%Z m2 (bv_unsigned a0 + CL8)%Z (bv_unsigned a2 + CL8)%Z (bv_unsigned a2 + CL8)%Z (bv_unsigned sp) lo
                        (skipn cl b) 112%Z (bv_unsigned sp + -112)%Z (FCELLS jb) (fst (sub_part_neg (skipn cl b) c1)) (snd (sub_part_neg (skipn cl b) c1))).

  (* [comment removed for export] *)
  Definition OUTER (m2 : word -> option byte) : Prop :=
    limbs_at bsegs m2 rp r1 /\ munch Wfin m m2 /\ wmono bsegs m m2.
  Definition ACCP (m2 : word -> option byte) : Prop :=
    acc bsegs m2 (ap + CL8) (8 * Z.of_nat (length (skipn cl a))) /\ acc bsegs m2 (rp + CL8) (8 * Z.of_nat (length (skipn cl a))).
  Definition ACCN (m2 : word -> option byte) : Prop :=
    acc bsegs m2 (bp + CL8) (8 * Z.of_nat (length (skipn cl b))) /\ acc bsegs m2 (rp + CL8) (8 * Z.of_nat (length (skipn cl b))).

  Lemma r1_len : length r1 = cl.
  Proof. rewrite sub_words_length, !length_firstn. lia. Qed.

  (* [comment removed for export] *)
  Lemma spw_ret : forall jb m3 cfin x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    limbs_at bsegs m3 rp (fst (sub_part_words a b cl)) -> cfin = snd (sub_part_words a b cl) ->
    rw_cells bsegs m3 (SP + -112) (FCELLS jb) -> stk bsegs m3 lo (SP + -112) -> mem_inv bsegs m3 ->
    munch Wfin m m3 -> wmono bsegs m m3 ->
    evt bsegs POST (ST 0x24cfd8 m3 x1 x5 x6 x7 x9 (Z_to_bv 64 cfin) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros HP CY FR ST MI MU WM.
    do 15 zstep.
    release_frame FR ST (bv_unsigned sp).
    rewrite CY.
    unfold spw_apost. finish.
  Qed.

  Lemma model_pos : db = 0%nat ->
    sub_part_words a b cl = (r1 ++ fst (sub_part_pos (skipn cl a) c1), snd (sub_part_pos (skipn cl a) c1)).
  Proof.
    intros Hdb. unfold sub_part_words. destruct (sub_words (firstn cl a) (firstn cl b)) as [r c0]. cbn [fst snd].
    assert (E : skipn cl b = []) by (apply length_zero_iff_nil; rewrite Hskb; exact Hdb). rewrite E.
    destruct (sub_part_pos (skipn cl a) c0); reflexivity.
  Qed.
  Lemma model_neg : (1 <= db)%nat ->
    sub_part_words a b cl = (r1 ++ fst (sub_part_neg (skipn cl b) c1), snd (sub_part_neg (skipn cl b) c1)).
  Proof.
    intros Hdb. unfold sub_part_words. destruct (sub_words (firstn cl a) (firstn cl b)) as [r c0]. cbn [fst snd].
    destruct (skipn cl b) as [|y0 tb] eqn:E; [exfalso; pose proof Hskb as H; rewrite E in H; cbn in H; lia|].
    destruct (sub_part_neg (y0 :: tb) c0); reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma spw_ret_pos : forall jb m2 m3 pre c pa pb pr x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    OUTER m2 -> db = 0%nat -> PINV m2 jb m3 pre [] [] c pa pb pr ->
    evt bsegs POST (ST 0x24cfd8 m3 x1 x5 x6 x7 x9 (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros (HR & MUo & WMo) Hdb I.
    pose proof (PKIT m2 jb INV_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU' & WM').
    pose proof (model_pos Hdb) as E.
    eapply spw_ret; [ | | exact FR | exact ST | exact MI | | ].
    - rewrite E. cbn [fst]. apply limbs_at_app. split.
      + eapply limbs_at_transport; [exact HR | exact MU' | cbn [disjoint_from]; rewrite r1_len; clear - SEPR; lia].
      + rewrite r1_len. exact HP.
    - rewrite E. cbn [snd]. symmetry. exact CY.
    - eapply munch_trans; [exact MUo|]. eapply munch_weaken; [|exact MU'].
      unfold sub_fp. cbn [outside]. rewrite Hska. intros x Hx. clear - Hx Hdb. lia.
    - eapply wmono_trans; [exact WMo | exact WM'].
  Qed.

  Lemma spw_ret_neg : forall jb m2 m3 pre c pa pb pr x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    OUTER m2 -> (1 <= db)%nat -> NINV m2 jb m3 pre [] [] c pa pb pr ->
    evt bsegs POST (ST 0x24cfd8 m3 x1 x5 x6 x7 x9 (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros (HR & MUo & WMo) Hdb I.
    pose proof (NKIT m2 jb INV_done _ _ _ _ _ _ I) as (HP & CY & FR & ST & MI & MU' & WM').
    pose proof (model_neg Hdb) as E.
    eapply spw_ret; [ | | exact FR | exact ST | exact MI | | ].
    - rewrite E. cbn [fst]. apply limbs_at_app. split.
      + eapply limbs_at_transport; [exact HR | exact MU' | cbn [disjoint_from]; rewrite r1_len; clear - SEPR; lia].
      + rewrite r1_len. exact HP.
    - rewrite E. cbn [snd]. symmetry. exact CY.
    - eapply munch_trans; [exact MUo|]. eapply munch_weaken; [|exact MU'].
      unfold sub_fp. cbn [outside]. rewrite Hskb. intros x Hx. clear - Hx DAB Hdb. lia.
    - eapply wmono_trans; [exact WMo | exact WM'].
  Qed.

  Ltac pw64eq := unfold W_sub_part_words.pos_fl; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia.
  Ltac nw64eq := unfold W_sub_part_words.neg_fl; clear; apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite ?BW_lit; Z.div_mod_to_equations; lia.
  Ltac pldA m2 jb I := let L := constr:(PKIT m2 jb INV_rdA) in ldA_with L I.
  Ltac nldA m2 jb I := let L := constr:(NKIT m2 jb INV_rdA) in ldA_with L I.
  Ltac pst m2 jb I l cn Ecn := let L1 := constr:(PKIT m2 jb INV_store_ok) in let L2 := constr:(PKIT m2 jb INV_store) in st_limb_with L1 L2 pw64eq I l cn Ecn.
  Ltac nst m2 jb I l cn Ecn := let L1 := constr:(NKIT m2 jb INV_store_ok) in let L2 := constr:(NKIT m2 jb INV_store) in st_limb_with L1 L2 nw64eq I l cn Ecn.
  (* [comment removed for export] *)
  Ltac pshA' m2 jb P AC I k := let L := constr:(PSH m2 jb INV_shA P) in ld_sh_with L I AC k.
  Ltac pshR' m2 jb P AC I k := let L := constr:(PSH m2 jb INV_shR P) in ld_sh_with L I AC k.
  Ltac pshA m2 jb P AC I k := pshA' m2 jb P AC I k; chk0.
  Ltac pshR m2 jb P AC I k := pshR' m2 jb P AC I k; chk0.
  Ltac nshA m2 jb P AC I k := let L := constr:(NSH m2 jb INV_shA P) in ld_sh_with L I AC k; chk0.
  Ltac nshR m2 jb P AC I k := let L := constr:(NSH m2 jb INV_shR P) in ld_sh_with L I AC k; chk0.
  (* [comment removed for export] *)
  Ltac cn0 x cn Ecn := let E0 := fresh "E0" in
    assert (E0 : cn = 0%Z) by (rewrite Ecn; unfold W_sub_part_words.pos_fc; destruct (x =? 0)%Z; reflexivity); clear Ecn; subst cn.

  Lemma PFP : forall jb m2 m3 pre la c pa pr, PINV m2 jb m3 pre la la c pa pa pr ->
    (0 < pa /\ pa mod 8 = 0 /\ pa + 8 * Z.of_nat (length la) <= 18446744073709551616 /\
     0 < pr /\ pr mod 8 = 0 /\ pr + 8 * Z.of_nat (length la) <= 140737488355328)%Z.
  Proof.
    intros jb m2 m3 pre la c pa pr I.
    pose proof (PKIT m2 jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (PKIT m2 jb INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & _ & TA).
    destruct (UBR ltac:(lia)) as (NZR & ALR). destruct (UBA ltac:(lia)) as (NZA & ALA').
    clear - El En Epr TOP R0 Epa TA NZR ALR NZA ALA'. Z.div_mod_to_equations. lia.
  Qed.
  Lemma PFN : forall jb m2 m3 pre la c pa pr, NINV m2 jb m3 pre la la c pa pa pr ->
    (0 < pa /\ pa mod 8 = 0 /\ pa + 8 * Z.of_nat (length la) <= 18446744073709551616 /\
     0 < pr /\ pr mod 8 = 0 /\ pr + 8 * Z.of_nat (length la) <= 140737488355328)%Z.
  Proof.
    intros jb m2 m3 pre la c pa pr I.
    pose proof (NKIT m2 jb INV_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (NKIT m2 jb INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & _ & TA).
    destruct (UBR ltac:(lia)) as (NZR & ALR). destruct (UBB ltac:(lia)) as (NZB & ALB').
    clear - El En Epr TOP R0 Epa TA NZR ALR NZB ALB'. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma spw_ret0 : forall jb m2 m3 pre pa pb pr x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    OUTER m2 -> db = 0%nat -> PINV m2 jb m3 pre [] [] 0 pa pb pr ->
    evt bsegs POST (ST 0x24cfd4 m3 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros O Hdb I.
    zstep. eapply spw_ret_pos; [exact O | exact Hdb | exact I].
  Qed.

  Lemma spw_ret1 : forall jb m2 m3 pre c pa pb pr x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    OUTER m2 -> db = 0%nat -> PINV m2 jb m3 pre [] [] c pa pb pr ->
    evt bsegs POST (ST 0x24d014 m3 x1 x5 x6 x7 x9 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros O Hdb I.
    do 2 zstep. eapply spw_ret_pos; [exact O | exact Hdb | exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma spw_copy_loop : forall (K : nat) la jb m2 m3 pre pa pr off x1 x10 x11 x12 x18 x19 x21 x23 x24 x25 x26 x27 x31,
    length la = K -> la <> [] -> OUTER m2 -> ACCP m2 -> PPB -> db = 0%nat -> (0 <= pa)%Z -> (0 <= pr)%Z -> (0 <= off)%Z ->
    PINV m2 jb m3 pre la la 0 (pa + off) (pa + off) (pr + off) ->
    evt bsegs POST (ST 0x24ced8 m3 x1 (Z_to_bv 64 (-17)) (Z_to_bv 64 3) (Z_to_bv 64 (-25)) (Z_to_bv 64 (Z.of_nat (length la))) x10 x11 x12
                       (Z_to_bv 64 pr) (Z_to_bv 64 0) (Z_to_bv 64 off) (Z_to_bv 64 (-9)) (Z_to_bv 64 2) x18 x19 (Z_to_bv 64 pa) x21 (Z_to_bv 64 SHB)
                       x23 x24 x25 x26 x27 (Z_to_bv 64 (shad (pr + off))) (Z_to_bv 64 (shad (pa + off))) (Z_to_bv 64 (-33)) x31).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros la jb m2 m3 pre pa pr off x1 x10 x11 x12 x18 x19 x21 x23 x24 x25 x26 x27 x31 HK NE O AC P Hdb Hpa Hpr Hoff I.
    pose proof AC as (ACA2 & ACR2).
    pose proof (PKIT m2 jb INV_len _ _ _ _ _ _ _ _ I) as (_ & En & Epr & _).
    pose proof (PKIT m2 jb INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & _).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & _).
    assert (R31 : (Z.of_nat (length la) < 2147483648)%Z) by (rewrite Hska in En; clear - En N31; lia).
    assert (BND : (pa + off + 8 * Z.of_nat (length la) <= 140737488355328 /\ pr + off + 8 * Z.of_nat (length la) <= 140737488355328)%Z)
      by (clear - En Epr Epa BR BA; lia).
    clear En Epr Epa BR BA.
    pose proof (PFP _ _ _ _ _ _ _ _ I) as PF.
    destruct la as [|y1 la]; [congruence|]. clear NE. cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    (* [comment removed for export] *)
    pshA' m2 jb P ACA2 I 0%nat. zstep. chk0.
    pshR' m2 jb P ACR2 I 0%nat. zstep. chk0.
    pldA m2 jb I. zstep. rewrite bn_swrap32_small by (clear - R31; lia).
    pst m2 jb I l1 cn1 Ec1. cn0 y1 cn1 Ec1.
    zstep. rewrite lts_signed by (clear - R31; lia).
    if_cases K1; zify_cond K1.
    { destruct la as [|? ?]; [|exfalso; clear - K1; cbn [length] in K1; lia].
      eapply spw_ret0; [exact O | exact Hdb | exact I]. }
    destruct la as [|y2 la]; [exfalso; clear - K1; cbn [length] in K1; lia|]. clear K1. cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    (* [comment removed for export] *)
    ub. do 3 zstep. pshA m2 jb P ACA2 I 0%nat.
    do 3 zstep. pshR m2 jb P ACR2 I 0%nat.
    pldA m2 jb I. pst m2 jb I l2 cn2 Ec2. cn0 y2 cn2 Ec2.
    zstep. if_cases K2; zify_cond K2.
    { destruct la as [|? ?]; [|exfalso; clear - K2; cbn [length] in K2; lia].
      eapply spw_ret0; [exact O | exact Hdb | exact I]. }
    destruct la as [|y3 la]; [exfalso; clear - K2; cbn [length] in K2; lia|]. clear K2. cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    (* [comment removed for export] *)
    ub. do 3 zstep. pshA m2 jb P ACA2 I 0%nat.
    do 3 zstep. pshR m2 jb P ACR2 I 0%nat.
    pldA m2 jb I. pst m2 jb I l3 cn3 Ec3. cn0 y3 cn3 Ec3.
    zstep. if_cases K3; zify_cond K3.
    { destruct la as [|? ?]; [|exfalso; clear - K3; cbn [length] in K3; lia].
      eapply spw_ret0; [exact O | exact Hdb | exact I]. }
    destruct la as [|y4 la]; [exfalso; clear - K3; cbn [length] in K3; lia|]. clear K3. cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    (* [comment removed for export] *)
    ub. do 3 zstep. pshA m2 jb P ACA2 I 0%nat.
    do 3 zstep. pshR m2 jb P ACR2 I 0%nat.
    pldA m2 jb I. zstep. rewrite bn_swrap32_small by (clear - R31; lia).
    pst m2 jb I l4 cn4 Ec4. cn0 y4 cn4 Ec4.
    zstep. if_cases K4; zify_cond K4.
    { destruct la as [|? ?]; [|exfalso; clear - K4; cbn [length] in K4; lia]. (* [comment removed for export] *)
      eapply spw_ret0; [exact O | exact Hdb | exact I]. }
    assert (NEl : la <> []) by (destruct la; [exfalso; apply K4; cbn [length]; clear; lia | discriminate]).
    assert (Hl1 : (1 <= Z.of_nat (length la))%Z) by (destruct la; [congruence | cbn [length]; clear; lia]).
    ub. do 3 zstep.
    zstep. try if_true.
    setreg 9%Z (Z_to_bv 64 (Z.of_nat (length la))) ltac:(f_equal; clear; lia).
    setreg 29%Z (Z_to_bv 64 (shad (pa + (off + 32)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    setreg 28%Z (Z_to_bv 64 (shad (pr + (off + 32)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    replace (pa + off + 32)%Z with (pa + (off + 32))%Z in I by (clear; lia).
    replace (pr + off + 32)%Z with (pr + (off + 32))%Z in I by (clear; lia).
    eapply (IH (length la)); [ clear - HK; lia | reflexivity | exact NEl | exact O | exact AC | exact P | exact Hdb | exact Hpa | exact Hpr | clear - Hoff; lia | exact I ].
  Qed.

  (* [comment removed for export] *)
  Lemma spw_copy_entry : forall la jb m2 m3 pre pa pr x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    la <> [] -> OUTER m2 -> ACCP m2 -> PPB -> db = 0%nat -> PINV m2 jb m3 pre la la 0 pa pa pr ->
    evt bsegs POST (ST 0x24ce94 m3 x1 x5 x6 x7 (Z_to_bv 64 (Z.of_nat (length la))) x10 x11 x12 (Z_to_bv 64 pr) x14 x15 x16 x17
                       x18 x19 (Z_to_bv 64 pa) x21 (Z_to_bv 64 SHB) x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros NE O AC P Hdb I.
    pose proof AC as (ACA2 & ACR2).
    pose proof (PKIT m2 jb INV_len _ _ _ _ _ _ _ _ I) as (_ & En & Epr & _).
    pose proof (PKIT m2 jb INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & _).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & _).
    assert (R31 : (Z.of_nat (length la) < 2147483648)%Z) by (rewrite Hska in En; clear - En N31; lia).
    assert (BND : (0 <= pa /\ 0 <= pr /\ pa + 8 * Z.of_nat (length la) <= 140737488355328 /\ pr + 8 * Z.of_nat (length la) <= 140737488355328)%Z)
      by (clear - En Epr Epa BR BA; lia).
    clear En Epr Epa BR BA.
    pose proof (PFP _ _ _ _ _ _ _ _ I) as PF.
    assert (Hl1 : (1 <= Z.of_nat (length la))%Z) by (destruct la; [congruence | cbn [length]; clear; lia]).
    ub.
    zstep. rewrite (land7 pr) by (clear - PF; tauto).
    ub.
    do 3 zstep. ub. zstep. ub. zstep. ub. do 2 zstep. ub.
    setreg 28%Z (Z_to_bv 64 (shad (pr + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
    setreg 29%Z (Z_to_bv 64 (shad (pa + 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.add_0_r; clear; lia).
    eapply (spw_copy_loop (length la) la _ m2 _ pre pa pr 0);
      [ reflexivity | exact NE | exact O | exact AC | exact P | exact Hdb | clear - BND; lia | clear - BND; lia | clear; lia | rewrite !Z.add_0_r; exact I ].
  Qed.

  (* [comment removed for export] *)
  Ltac pcarry r x c Rx Hc cn Ecn H :=
    let v := reg_val r in
    lazymatch v with
    | Z_to_bv 64 ?e =>
        let E := fresh "E" in
        assert (E : e = cn)
          by (clear - Rx Hc Ecn; subst cn; unfold W_sub_part_words.pos_fc;
              assert (c = 0 \/ c = 1)%Z as [-> | ->] by lia;
              (destruct (Z.eqb_spec x 0) as [-> | NZ];
               [ reflexivity | rewrite (proj2 (Z.ltb_lt 0 x)) by lia; reflexivity ]));
        rewrite E; clear E
    end;
    assert (H : (0 <= cn <= 1)%Z) by (clear - Rx Hc Ecn; subst cn; apply pos_fc_range; assumption).

  (* [comment removed for export] *)
  Lemma spw_loopP : forall (K : nat) la jb m2 m3 pre c qa qr x1 x11 x14 x17 x18 x19,
    length la = K -> la <> [] -> OUTER m2 -> ACCP m2 -> PPB -> db = 0%nat -> (0 <= qa)%Z -> (0 <= qr)%Z ->
    PINV m2 jb m3 pre la la c (qa + CL8) (qa + CL8) (qr + CL8) ->
    evt bsegs POST (ST 0x24cb64 m3 x1 (Z_to_bv 64 (qa + 24)) (Z_to_bv 64 (qr + 8)) (Z_to_bv 64 (qr + 16)) (Z_to_bv 64 (Z.of_nat (length la))) (Z_to_bv 64 c)
                       x11 (Z_to_bv 64 0) (Z_to_bv 64 0) x14 (Z_to_bv 64 (qa + 8)) (Z_to_bv 64 (qa + 16)) x17
                       x18 x19 (Z_to_bv 64 qa) (Z_to_bv 64 CL8) (Z_to_bv 64 SHB) (Z_to_bv 64 (-25)) (Z_to_bv 64 (-33))
                       (Z_to_bv 64 (shad (qa + CL8))) (Z_to_bv 64 (shad (qr + CL8))) (Z_to_bv 64 qr)
                       (Z_to_bv 64 (qr + 24)) (Z_to_bv 64 2) (Z_to_bv 64 (-9)) (Z_to_bv 64 (-17))).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros la jb m2 m3 pre c qa qr x1 x11 x14 x17 x18 x19 HK NE O AC P Hdb Hqa Hqr I.
    pose proof AC as (ACA2 & ACR2).
    pose proof (PKIT m2 jb INV_len _ _ _ _ _ _ _ _ I) as (_ & En & Epr & _).
    pose proof (PKIT m2 jb INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & _).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & _).
    assert (R31 : (Z.of_nat (length la) < 2147483648)%Z) by (rewrite Hska in En; clear - En N31; lia).
    assert (CL31 : (0 <= CL8 /\ CL8 < 17179869184)%Z) by (clear - N31; lia).
    assert (BND : (qa + CL8 + 8 * Z.of_nat (length la) <= 140737488355328 /\ qr + CL8 + 8 * Z.of_nat (length la) <= 140737488355328)%Z)
      by (clear - En Epr Epa BR BA; lia).
    clear En Epr Epa BR BA.
    pose proof (PKIT m2 jb INV_carry _ _ _ _ _ _ _ _ I) as Hc.
    pose proof (PFP _ _ _ _ _ _ _ _ I) as PF.
    destruct la as [|y0 la]; [congruence|]. clear NE. cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    pose proof (PKIT m2 jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Ry0.
    (* [comment removed for export] *)
    zstep. ub. zstep. ub.
    pshA m2 jb P ACA2 I 0%nat. pshR m2 jb P ACR2 I 0%nat.
    pldA m2 jb I. do 2 zstep. pst m2 jb I l0 cn1 Ec1.
    do 2 zstep.
    pcarry 10%Z y0 c Ry0 Hc cn1 Ec1 Hc1. clear Ec1.
    zstep. rewrite lts_signed by (clear - R31; lia).
    if_cases K1; zify_cond K1.
    { destruct la as [|? ?]; [|exfalso; clear - K1; cbn [length] in K1; lia].
      eapply spw_ret_pos; [exact O | exact Hdb | exact I]. }
    destruct la as [|y1 la]; [exfalso; clear - K1; cbn [length] in K1; lia|]. clear K1. cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    pose proof (PKIT m2 jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Ry1.
    (* [comment removed for export] *)
    ub. do 3 zstep. pshA m2 jb P ACA2 I 0%nat.
    do 3 zstep. pshR m2 jb P ACR2 I 0%nat.
    pldA m2 jb I. do 2 zstep. pst m2 jb I l1 cn2 Ec2.
    do 2 zstep.
    pcarry 10%Z y1 cn1 Ry1 Hc1 cn2 Ec2 Hc2. clear Ec2.
    zstep. if_cases K2; zify_cond K2.
    { destruct la as [|? ?]; [|exfalso; clear - K2; cbn [length] in K2; lia].
      eapply spw_ret_pos; [exact O | exact Hdb | exact I]. }
    destruct la as [|y2 la]; [exfalso; clear - K2; cbn [length] in K2; lia|]. clear K2. cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    pose proof (PKIT m2 jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Ry2.
    (* [comment removed for export] *)
    ub. do 3 zstep. pshA m2 jb P ACA2 I 0%nat.
    do 3 zstep. pshR m2 jb P ACR2 I 0%nat.
    pldA m2 jb I. do 2 zstep. pst m2 jb I l2 cn3 Ec3.
    do 2 zstep.
    pcarry 10%Z y2 cn2 Ry2 Hc2 cn3 Ec3 Hc3. clear Ec3.
    zstep. zstep. if_cases K3; zify_cond K3.
    { destruct la as [|? ?]; [|exfalso; clear - K3; cbn [length] in K3; lia].
      eapply spw_ret_pos; [exact O | exact Hdb | exact I]. }
    destruct la as [|y3 la]; [exfalso; clear - K3; cbn [length] in K3; lia|]. clear K3. cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    pose proof (PKIT m2 jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Ry3.
    (* [comment removed for export] *)
    ub. do 3 zstep. pshA m2 jb P ACA2 I 0%nat.
    do 3 zstep. pshR m2 jb P ACR2 I 0%nat.
    pldA m2 jb I. do 2 zstep. pst m2 jb I l3 cn4 Ec4.
    do 2 zstep.
    pcarry 11%Z y3 cn3 Ry3 Hc3 cn4 Ec4 Hc4.
    assert (H43 : (cn4 = 0 \/ cn4 = cn3)%Z) by (clear - Ec4; subst cn4; unfold W_sub_part_words.pos_fc; destruct (y3 =? 0)%Z; auto).
    clear Ec4.
    zstep. zstep. if_cases K4; zify_cond K4.
    { (* [comment removed for export] *)
      destruct la as [|? ?]; [|exfalso; clear - K4; cbn [length] in K4; lia].
      eapply spw_ret1; [exact O | exact Hdb | exact I]. }
    assert (NEl : la <> []) by (destruct la; [exfalso; apply K4; cbn [length]; clear; lia | discriminate]).
    assert (Hl1 : (1 <= Z.of_nat (length la))%Z) by (destruct la; [congruence | cbn [length]; clear; lia]).
    ub. do 12 zstep.
    zstep. rewrite bn_swrap32_small by (clear - R31; lia).
    setreg 9%Z (Z_to_bv 64 (Z.of_nat (length la))) ltac:(f_equal; clear; lia).
    replace (qa + CL8 + 32)%Z with (qa + 32 + CL8)%Z in I by (clear; lia).
    replace (qr + CL8 + 32)%Z with (qr + 32 + CL8)%Z in I by (clear; lia).
    zstep. if_cases K5; zify_cond K5.
    - (* [comment removed for export] *)
      assert (E43 : cn4 = cn3) by (clear - H43 K5 Hc4; destruct H43 as [H|H]; [exfalso; apply K5; rewrite H; reflexivity | exact H]).
      rewrite <- E43.
      setreg 5%Z (Z_to_bv 64 (qa + 32 + 24)) ltac:(f_equal; clear; lia).
      setreg 6%Z (Z_to_bv 64 (qr + 32 + 8)) ltac:(f_equal; clear; lia).
      setreg 7%Z (Z_to_bv 64 (qr + 32 + 16)) ltac:(f_equal; clear; lia).
      setreg 15%Z (Z_to_bv 64 (qa + 32 + 8)) ltac:(f_equal; clear; lia).
      setreg 16%Z (Z_to_bv 64 (qa + 32 + 16)) ltac:(f_equal; clear; lia).
      setreg 28%Z (Z_to_bv 64 (qr + 32 + 24)) ltac:(f_equal; clear; lia).
      setreg 25%Z (Z_to_bv 64 (shad (qa + 32 + CL8))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
      setreg 26%Z (Z_to_bv 64 (shad (qr + 32 + CL8))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
      eapply (IH (length la)); [ clear - HK; lia | reflexivity | exact NEl | exact O | exact AC | exact P | exact Hdb | clear - Hqa; lia | clear - Hqr; lia | exact I ].
    - (* [comment removed for export] *)
      assert (E0 : cn4 = 0%Z) by (clear - K5 Hc4; lia). subst cn4.
      do 3 zstep.
      eapply spw_copy_entry; [exact NEl | exact O | exact AC | exact P | exact Hdb | exact I].
  Qed.

  (* [comment removed for export] *)
  Ltac ncmov y cn Ecn :=
    let CONT := fresh "CONT" in let KZ := fresh "KZ" in
    eassert (CONT : _);
    [ | zstep; if_cases KZ; zify_cond KZ;
        [ setreg 10%Z (Z_to_bv 64 cn) ltac:(f_equal; rewrite Ecn; unfold W_sub_part_words.neg_fc; rewrite (proj2 (Z.eqb_eq y 0) KZ); reflexivity); exact CONT
        | zstep;
          setreg 10%Z (Z_to_bv 64 cn) ltac:(f_equal; rewrite Ecn; unfold W_sub_part_words.neg_fc; rewrite (proj2 (Z.eqb_neq y 0) KZ); reflexivity); exact CONT ] ].

  (* [comment removed for export] *)
  Lemma spw_loopN : forall (K : nat) la jb m2 m3 pre c qb qr x1 x11 x13 x18 x23 x24 x25 x26,
    length la = K -> la <> [] -> OUTER m2 -> ACCN m2 -> NPB -> (1 <= db)%nat -> (0 <= qb)%Z -> (0 <= qr)%Z ->
    NINV m2 jb m3 pre la la c (qb + CL8) (qb + CL8) (qr + CL8) ->
    evt bsegs POST (ST 0x24cd3c m3 x1 (Z_to_bv 64 (-9)) (Z_to_bv 64 (-17)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (- Z.of_nat (length la))) (Z_to_bv 64 c)
                       x11 (Z_to_bv 64 0) x13 (Z_to_bv 64 (qb + 24)) (Z_to_bv 64 (qb + 16)) (Z_to_bv 64 (qb + 8)) (Z_to_bv 64 (-2))
                       x18 (Z_to_bv 64 qb) (Z_to_bv 64 qr) (Z_to_bv 64 CL8) (Z_to_bv 64 SHB) x23 x24 x25 x26 (Z_to_bv 64 qr)
                       (Z_to_bv 64 (-25)) (Z_to_bv 64 (shad (qb + CL8))) (Z_to_bv 64 (shad (qr + CL8))) (Z_to_bv 64 (-33))).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros la jb m2 m3 pre c qb qr x1 x11 x13 x18 x23 x24 x25 x26 HK NE O AC P Hdb Hqb Hqr I.
    pose proof AC as (ACB2 & ACR2).
    pose proof (NKIT m2 jb INV_len _ _ _ _ _ _ _ _ I) as (_ & En & Epr & _).
    pose proof (NKIT m2 jb INV_ptrs _ _ _ _ _ _ _ _ I) as (Epa & _).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & _).
    assert (R31 : (Z.of_nat (length la) < 2147483648)%Z) by (rewrite Hskb in En; clear - En N31; lia).
    assert (CL31 : (0 <= CL8 /\ CL8 < 17179869184)%Z) by (clear - N31; lia).
    assert (BND : (qb + CL8 + 8 * Z.of_nat (length la) <= 140737488355328 /\ qr + CL8 + 8 * Z.of_nat (length la) <= 140737488355328)%Z)
      by (clear - En Epr Epa BR BA; lia).
    clear En Epr Epa BR BA.
    pose proof (NKIT m2 jb INV_carry _ _ _ _ _ _ _ _ I) as Hc.
    pose proof (PFN _ _ _ _ _ _ _ _ I) as PF.
    destruct la as [|y1 la]; [congruence|]. clear NE. cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    pose proof (NKIT m2 jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Ry1.
    (* [comment removed for export] *)
    nshA m2 jb P ACB2 I 0%nat. nshR m2 jb P ACR2 I 0%nat.
    zstep. nldA m2 jb I. zstep. do 2 zstep. nst m2 jb I l1 cn1 Ec1.
    ncmov y1 cn1 Ec1.
    assert (Hc1 : (0 <= cn1 <= 1)%Z) by (clear - Ry1 Hc Ec1; subst cn1; apply neg_fc_range; assumption). clear Ec1.
    zstep. rewrite lts_signed by (clear - R31; lia).
    if_cases K1; zify_cond K1.
    { destruct la as [|? ?]; [|exfalso; clear - K1; cbn [length] in K1; lia].
      eapply spw_ret_neg; [exact O | exact Hdb | exact I]. }
    destruct la as [|y2 la]; [exfalso; clear - K1; cbn [length] in K1; lia|]. clear K1. cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    pose proof (NKIT m2 jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Ry2.
    (* [comment removed for export] *)
    ub. do 3 zstep. nshA m2 jb P ACB2 I 0%nat.
    do 4 zstep. nshR m2 jb P ACR2 I 0%nat.
    nldA m2 jb I. do 2 zstep. nst m2 jb I l2 cn2 Ec2.
    ncmov y2 cn2 Ec2.
    assert (Hc2 : (0 <= cn2 <= 1)%Z) by (clear - Ry2 Hc1 Ec2; subst cn2; apply neg_fc_range; assumption). clear Ec2.
    zstep. if_cases K2; zify_cond K2.
    { destruct la as [|? ?]; [|exfalso; clear - K2 R31; cbn [length] in *; rewrite Nat2Z.inj_succ in *; Z.div_mod_to_equations; lia].
      eapply spw_ret_neg; [exact O | exact Hdb | exact I]. }
    destruct la as [|y3 la]; [exfalso; apply K2; reflexivity|]. clear K2. cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    pose proof (NKIT m2 jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Ry3.
    (* [comment removed for export] *)
    ub. do 3 zstep. nshA m2 jb P ACB2 I 0%nat.
    do 3 zstep. nshR m2 jb P ACR2 I 0%nat.
    nldA m2 jb I. do 2 zstep. nst m2 jb I l3 cn3 Ec3.
    ncmov y3 cn3 Ec3.
    assert (Hc3 : (0 <= cn3 <= 1)%Z) by (clear - Ry3 Hc2 Ec3; subst cn3; apply neg_fc_range; assumption). clear Ec3.
    zstep. if_cases K3; zify_cond K3.
    { destruct la as [|? ?]; [|exfalso; clear - K3 R31; cbn [length] in *; rewrite Nat2Z.inj_succ in *; Z.div_mod_to_equations; lia].
      eapply spw_ret_neg; [exact O | exact Hdb | exact I]. }
    destruct la as [|y4 la].
    { exfalso. clear - K3. cbn [length] in K3. change (- Z.succ (Z.succ (Z.succ (Z.of_nat 0))))%Z with (-3)%Z in K3. lia. }
    clear K3. cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    pose proof (NKIT m2 jb INV_rangeA _ _ _ _ _ _ _ _ _ I) as Ry4.
    (* [comment removed for export] *)
    ub. do 3 zstep. nshA m2 jb P ACB2 I 0%nat.
    do 3 zstep. nshR m2 jb P ACR2 I 0%nat.
    nldA m2 jb I. do 2 zstep. nst m2 jb I l4 cn4 Ec4.
    ncmov y4 cn4 Ec4.
    assert (Hc4 : (0 <= cn4 <= 1)%Z) by (clear - Ry4 Hc3 Ec4; subst cn4; apply neg_fc_range; assumption). clear Ec4.
    zstep. rewrite bn_swrap32_mod by (clear - R31; lia).
    setreg 9%Z (Z_to_bv 64 (- Z.of_nat (length la))) ltac:(f_equal; clear; lia).
    zstep. if_cases K4; zify_cond K4.
    { destruct la as [|? ?]; [|exfalso; clear - K4 R31; cbn [length] in *; rewrite Nat2Z.inj_succ in *; Z.div_mod_to_equations; lia]. (* [comment removed for export] *)
      eapply spw_ret_neg; [exact O | exact Hdb | exact I]. }
    assert (NEl : la <> []) by (destruct la; [exfalso; apply K4; reflexivity | discriminate]).
    assert (Hl1 : (1 <= Z.of_nat (length la))%Z) by (destruct la; [congruence | cbn [length]; clear; lia]).
    ub. do 9 zstep.
    zstep. try if_true.
    setreg 14%Z (Z_to_bv 64 (qb + 32 + 24)) ltac:(f_equal; clear; lia).
    setreg 15%Z (Z_to_bv 64 (qb + 32 + 16)) ltac:(f_equal; clear; lia).
    setreg 16%Z (Z_to_bv 64 (qb + 32 + 8)) ltac:(f_equal; clear; lia).
    setreg 29%Z (Z_to_bv 64 (shad (qb + 32 + CL8))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    setreg 30%Z (Z_to_bv 64 (shad (qr + 32 + CL8))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    replace (qb + CL8 + 32)%Z with (qb + 32 + CL8)%Z in I by (clear; lia).
    replace (qr + CL8 + 32)%Z with (qr + 32 + CL8)%Z in I by (clear; lia).
    eapply (IH (length la)); [ clear - HK; lia | reflexivity | exact NEl | exact O | exact AC | exact P | exact Hdb | clear - Hqb; lia | clear - Hqr; lia | exact I ].
  Qed.
  (* [comment removed for export] *)
  Lemma spw_neg_entry : forall jb m2 m3 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x25 x26 x28 x29 x30 x31,
    OUTER m2 -> ACCN m2 -> NPB -> (1 <= db)%nat -> NINV m2 jb m3 [] (skipn cl b) (skipn cl b) c1 (bp + CL8) (bp + CL8) (rp + CL8) ->
    evt bsegs POST (ST 0x24cce0 m3 x1 x5 x6 x7 (Z_to_bv 64 (- Z.of_nat db)) (Z_to_bv 64 c1) x11 x12 x13 x14 x15 x16 x17
                       x18 a2 a1 (Z_to_bv 64 CL8) (Z_to_bv 64 SHB) x23 x24 x25 x26 a0 x28 x29 x30 x31).
  Proof.
    intros until x31. intros OU AC P Hdb I.
    pose proof (PFN _ _ _ _ _ _ _ _ I) as PF.
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & BA & _).
    pose proof Hskb as HL. rewrite HL in BR, BA, PF.
    destruct (UBR ltac:(lia)) as (NZR & ALR). destruct (UBB ltac:(lia)) as (NZB & ALB').
    assert (NEb : skipn cl b <> []) by (intros E; pose proof Hskb as H; rewrite E in H; cbn in H; clear - H Hdb; lia).
    assert (CL31 : (0 <= CL8 /\ CL8 < 17179869184)%Z) by (clear - N31; lia).
    pose proof (zr_word a0) as Z0. pose proof (zr_word a2) as Z2. unfold inr64 in Z0, Z2.
    zstep. ub.
    zstep. rewrite (land7 _ ALR).
    ub. do 7 zstep. ub. zstep. ub. do 3 zstep. ub. zstep.
    setreg 29%Z (Z_to_bv 64 (shad (bp + CL8))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    setreg 30%Z (Z_to_bv 64 (shad (rp + CL8))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    replace (Z_to_bv 64 (- Z.of_nat db)) with (Z_to_bv 64 (- Z.of_nat (length (skipn cl b)))) by (rewrite Hskb; reflexivity).
    eapply evt_eq; [ | eapply (spw_loopN (length (skipn cl b)) (skipn cl b) _ m2 _ [] c1 bp rp);
                       [ reflexivity | exact NEb | exact OU | exact AC | exact P | exact Hdb | clear - Z2; lia | clear - Z0; lia | exact I ] ].
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
  Qed.

  Lemma c1_range : (0 <= c1 <= 1)%Z.
  Proof.
    pose proof (sub_words_spec (firstn cl a) (firstn cl b) (limbs_firstn _ _ LA) (limbs_firstn _ _ LB)
                  ltac:(rewrite !length_firstn; lia)) as H.
    destruct (sub_words (firstn cl a) (firstn cl b)) as [r c]. cbn [snd]. tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma bn_sub_part_words_aspec :
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24ca34) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl Wfin m) as MU. pose proof (munch_refl [(SP - 112, SP)]%Z m) as MUF. pose proof (wmono_refl bsegs m) as WM.
    pose proof (zr_word sp) as RSP. unfold inr64 in RSP. change (2 ^ 64)%Z with 18446744073709551616%Z in RSP.
    pose proof (proj1 STK) as LO0.
    assert (La : length (firstn cl a) = cl) by (rewrite length_firstn; lia).
    assert (Lb : length (firstn cl b) = cl) by (rewrite length_firstn; lia).
    pose proof c1_range as Hc1.
    (* [comment removed for export] *)
    assert (LOHI : (17594333495296 <= lo)%Z) by (clear - APT; unfold aptrs3, SHHI in APT; tauto).
    assert (BNA : (0 < Z.of_nat (length a) -> 0 <= ap /\ ap + 8 * Z.of_nat (length a) <= 140737488355328)%Z) by (apply (limbs_at_b47 bsegs m); assumption).
    assert (BNB : (0 < Z.of_nat (length b) -> 0 <= bp /\ bp + 8 * Z.of_nat (length b) <= 140737488355328)%Z) by (apply (limbs_at_b47 bsegs m); assumption).
    assert (BNR : (0 < 8 * N -> 0 <= rp /\ rp + 8 * N <= 140737488355328)%Z) by (apply (wr_at_b47 bsegs m); assumption).
    assert (OFFfin : offshW Wfin).
    { cbn [offshW]. destruct APT as (_ & _ & _ & A4' & A5'). unfold SHHI in *. split; [exact A4'|]. split; [right; clear - A5' LO; lia | exact I]. }
    assert (OFFfr : offshW [(SP - 112, SP)]%Z).
    { cbn [offshW]. destruct APT as (_ & _ & _ & _ & A5'). unfold SHHI in *. split; [right; clear - A5' LO; lia | exact I]. }

    assert (PT : (0 < N -> rp + 8 * N <= 140737488355328)%Z /\ (ap + CL8 < 18446744073709551616)%Z /\ (bp + CL8 < 18446744073709551616)%Z).
    { split; [|split].
      - intros HN. pose proof (wr_at_below bsegs m rp (8 * N) MI0 WR ltac:(lia)) as T. unfold UTOP in T. exact T.
      - destruct (Nat.eq_dec (cl + da) 0) as [E0|NE0].
        + pose proof (zr_word a1) as R1. unfold inr64 in R1. change (2 ^ 64)%Z with 18446744073709551616%Z in R1. clear - E0 R1. lia.
        + assert (NEa : lbytes a <> []) by (destruct a; [cbn [length] in HLA; lia | cbn; discriminate]).
          pose proof (bytes_at_below bsegs m ap (lbytes a) MI0 RA NEa) as TA. rewrite lbytes_lengthZ in TA. unfold UTOP in TA.
          clear - TA HLA. lia.
      - destruct (Nat.eq_dec (cl + db) 0) as [E0|NE0].
        + pose proof (zr_word a2) as R2. unfold inr64 in R2. change (2 ^ 64)%Z with 18446744073709551616%Z in R2. clear - E0 R2. lia.
        + assert (NEb : lbytes b <> []) by (destruct b; [cbn [length] in HLB; lia | cbn; discriminate]).
          pose proof (bytes_at_below bsegs m bp (lbytes b) MI0 RB NEb) as TB. rewrite lbytes_lengthZ in TB. unfold UTOP in TB.
          clear - TB HLB. lia. }
    destruct PT as (PTR & PTA & PTB).
    destruct SHBC as [G1 G2]. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in G1, G2.
    carve_frame 112%nat STK.
    do 25 zstep.
    assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -112)) = (SP + -112)%Z)
      by (apply inr64_unsigned_lit; unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - LO LO0 RSP; lia).
    assert (RA0 : limbs_at bsegs m0 ap a) by (eapply limbs_at_transport; [exact RA | exact MUF | cbn [disjoint_from]; clear - SEPA; lia]).
    assert (RB0 : limbs_at bsegs m0 bp b) by (eapply limbs_at_transport; [exact RB | exact MUF | cbn [disjoint_from]; clear - SEPB; lia]).
    rewrite <- (firstn_skipn cl a) in RA0. apply limbs_at_app in RA0. destruct RA0 as [RAl RAh]. rewrite La in RAh.
    rewrite <- (firstn_skipn cl b) in RB0. apply limbs_at_app in RB0. destruct RB0 as [RBl RBh]. rewrite Lb in RBh.
    eapply evt_cut.
    { eapply bn_sub_words_aspec with (a := firstn cl a) (b := firstn cl b) (lo := lo) (m := m0).
      - apply limbs_firstn. exact LA.
      - apply limbs_firstn. exact LB.
      - rewrite La, Lb. reflexivity.
      - rewrite La. clear - N31. lia.
      - rewrite La. exact A3.
      - exact RAl.
      - exact RBl.
      - rewrite La. pose proof (wr_at_sub bsegs m0 rp (8 * N) 0 (8 * Z.of_nat cl) WR ltac:(lia) ltac:(lia) ltac:(lia)) as X.
        rewrite Z.add_0_r in X. exact X.
      - rewrite La. unfold alias_ok. clear - ALA HLA. lia.
      - rewrite La. unfold alias_ok. clear - ALB HLB. lia.
      - rewrite ESP. exact STK.
      - rewrite ESP. clear - LO. lia.
      - rewrite La, ESP. clear - SEPR. lia.
      - rewrite La, ESP. clear - SEPA HLA. lia.
      - rewrite La, ESP. clear - SEPB HLB. lia.
      - exact MI0.
      - split; [exact G1 | exact G2].
      - rewrite La. pose proof (acc_tr bsegs _ m m0 rp (8 * N) 0 (8 * Z.of_nat cl) ACR MUF OFFfr) as X. rewrite Z.add_0_r in X.
        apply X; [intros Hp; pose proof (BNR ltac:(clear - Hp; lia)); clear - H Hp; lia | lia | clear; lia].
      - rewrite La. pose proof (acc_tr bsegs _ m m0 ap (8 * Z.of_nat (length a)) 0 (8 * Z.of_nat cl) ACA MUF OFFfr) as X. rewrite Z.add_0_r in X.
        apply X; [intros Hp; pose proof (BNA ltac:(clear - Hp HLA; lia)); clear - H Hp HLA; lia | lia | clear - HLA; lia].
      - rewrite La. pose proof (acc_tr bsegs _ m m0 bp (8 * Z.of_nat (length b)) 0 (8 * Z.of_nat cl) ACB MUF OFFfr) as X. rewrite Z.add_0_r in X.
        apply X; [intros Hp; pose proof (BNB ltac:(clear - Hp HLB; lia)); clear - H Hp HLB; lia | lia | clear - HLB; lia].
      - rewrite La. pose proof (aptrs3_sub rp ap bp N lo 0 (Z.of_nat cl) APT ltac:(lia) ltac:(lia) ltac:(lia)) as X.
        rewrite !Z.mul_0_r, !Z.add_0_r in X. exact X.
      - intros _. apply UBR. lia.
      - intros _. apply UBA. lia.
      - intros _. apply UBB. lia. }
    clear MUF.
    intros ms' PO. unfold sw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite La, ESP in *.
    replace (ret_pc (Z_to_bv 64 2411160)) with (Z_to_bv 64 2411160) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    assert (RAh2 : limbs_at bsegs m2 (ap + CL8) (skipn cl a)).
    { eapply limbs_at_transport; [exact RAh | exact MUc | cbn [disjoint_from]; rewrite Hska; clear - ALA SEPA HLA; lia]. }
    assert (RBh2 : limbs_at bsegs m2 (bp + CL8) (skipn cl b)).
    { eapply limbs_at_transport; [exact RBh | exact MUc | cbn [disjoint_from]; rewrite Hskb; clear - ALB SEPB HLB; lia]. }
    clear RAl RAh RBl RBh STK G1 G2.
    transport_after_call bsegs m0 m2 MUc WMc.
    clear MUc WMc MI0. try clear m0.
    assert (OU : OUTER m2) by (split; [exact HR | split; [exact MU | exact WM]]).
    rewrite A4.
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (Hd0 : (da = 0 /\ db = 0)%nat).
      { clear - K0 DAB N31. Z.div_mod_to_equations. lia. }
      destruct Hd0 as (Hda & Hdb).
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jb :: _) => eapply (spw_ret jb) end;
        [ | | exact FR | exact STc | exact MIc | exact MU | exact WM ].
      - rewrite (model_pos Hdb). cbn [fst].
        assert (Esk : skipn cl a = []) by (apply length_zero_iff_nil; rewrite Hska; exact Hda).
        rewrite Esk. cbn [sub_part_pos fst]. rewrite app_nil_r. exact HR.
      - rewrite (model_pos Hdb). cbn [snd].
        assert (Esk : skipn cl a = []) by (apply length_zero_iff_nil; rewrite Hska; exact Hda).
        rewrite Esk. reflexivity. }
    assert (Hd1 : (da <> 0 \/ db <> 0)%nat) by (clear - K0; destruct da, db; [exfalso; apply K0; reflexivity | lia..]).
    clear K0.
    assert (HN1 : (1 <= N)%Z) by (clear - Hd1; lia).
    specialize (PTR ltac:(clear - HN1; lia)).
    destruct (UBR ltac:(lia)) as (NZR & ALR). destruct (UBA ltac:(lia)) as (NZA & ALA'). destruct (UBB ltac:(lia)) as (NZB & ALB').
    assert (CL31 : (0 <= CL8 /\ CL8 < 17179869184)%Z) by (clear - N31; lia).
    pose proof (zr_word a0) as Z0. pose proof (zr_word a1) as Z1. pose proof (zr_word a2) as Z2. unfold inr64 in Z0, Z1, Z2.
    setreg 21%Z (Z_to_bv 64 (Z.of_nat cl)) ltac:(rewrite <- A3; apply Z_to_bv_bv_unsigned).
    zstep. replace (Z.of_nat cl ≪ 3)%Z with CL8 by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.

    ub.
    zstep. replace (Z.of_nat cl ≪ 3)%Z with CL8 by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. rewrite lts_signed by (clear - N31; lia).
    if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      assert (Hdb : (1 <= db)%nat /\ da = 0%nat) by (clear - K1 DAB; lia). destruct Hdb as (Hdb & Hda).
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jb :: _) =>
        assert (I : NINV m2 jb m2 [] (skipn cl b) (skipn cl b) c1 (bp + CL8) (bp + CL8) (rp + CL8));
        [ apply (NKIT m2 jb INV_init);
          [ apply limbs_skipn; exact LB | apply limbs_skipn; exact LB | rewrite Hskb; clear - Hdb; lia | exact Hc1
          | exact RBh2 | exact RBh2
          | rewrite Hskb; apply (wr_at_sub bsegs m2 rp (8 * N) CL8 (8 * Z.of_nat db) WR); clear; lia
          | exact FR | exact STc | exact MIc | apply munch_refl | apply munch_refl | apply wmono_refl
          | rewrite sub_part_neg_gen; reflexivity | rewrite sub_part_neg_gen; reflexivity ] | ]
      end.
      assert (P : NPB).
      { eapply (apure_intro bsegs m2) with (a := skipn cl b) (b := skipn cl b) (lo := lo);
          [ | reflexivity | rewrite Hskb; clear - Hdb; lia | exact RBh2 | exact RBh2
            | rewrite Hskb; apply (wr_at_sub bsegs m2 rp (8 * N) CL8 (8 * Z.of_nat db) WR); clear; lia | exact MIc | clear - LO; lia | clear; lia ].
        rewrite Hskb. pose proof (aptrs3_sub rp bp bp N lo (Z.of_nat cl) (Z.of_nat db)) as X. apply X; [ | clear; lia | clear; lia | clear; lia].
        clear - APT. unfold aptrs3 in *. tauto. }
      assert (AC : ACCN m2).
      { unfold ACCN. rewrite Hskb. split.
        - apply (acc_tr bsegs _ m m2 bp (8 * Z.of_nat (length b)) CL8 (8 * Z.of_nat db) ACB MU OFFfin);
            [intros Hp; pose proof (BNB ltac:(clear - Hp HLB; lia)) as H; clear - H HLB; lia | clear; lia | clear - HLB; lia].
        - apply (acc_tr bsegs _ m m2 rp (8 * N) CL8 (8 * Z.of_nat db) ACR MU OFFfin);
            [intros Hp; pose proof (BNR ltac:(clear - Hp; lia)) as H; clear - H; lia | clear; lia | clear; lia]. }
      replace (Z.of_nat da - Z.of_nat db)%Z with (- Z.of_nat db)%Z by (clear - Hda; lia).
      eapply spw_neg_entry; [exact OU | exact AC | exact P | exact Hdb | exact I].
    - (* [comment removed for export] *)
      assert (Hda : (1 <= da)%nat /\ db = 0%nat) by (clear - K1 DAB Hd1; lia). destruct Hda as (Hda & Hdb).
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jb :: _) =>
        assert (I : PINV m2 jb m2 [] (skipn cl a) (skipn cl a) c1 (ap + CL8) (ap + CL8) (rp + CL8));
        [ apply (PKIT m2 jb INV_init);
          [ apply limbs_skipn; exact LA | apply limbs_skipn; exact LA | rewrite Hska; clear - Hda; lia | exact Hc1
          | exact RAh2 | exact RAh2
          | rewrite Hska; apply (wr_at_sub bsegs m2 rp (8 * N) CL8 (8 * Z.of_nat da) WR); clear; lia
          | exact FR | exact STc | exact MIc | apply munch_refl | apply munch_refl | apply wmono_refl
          | rewrite sub_part_pos_gen; reflexivity | rewrite sub_part_pos_gen; reflexivity ] | ]
      end.
      assert (P : PPB).
      { eapply (apure_intro bsegs m2) with (a := skipn cl a) (b := skipn cl a) (lo := lo);
          [ | reflexivity | rewrite Hska; clear - Hda; lia | exact RAh2 | exact RAh2
            | rewrite Hska; apply (wr_at_sub bsegs m2 rp (8 * N) CL8 (8 * Z.of_nat da) WR); clear; lia | exact MIc | clear - LO; lia | clear; lia ].
        rewrite Hska. pose proof (aptrs3_sub rp ap ap N lo (Z.of_nat cl) (Z.of_nat da)) as X. apply X; [ | clear; lia | clear; lia | clear; lia].
        clear - APT. unfold aptrs3 in *. tauto. }
      assert (AC : ACCP m2).
      { unfold ACCP. rewrite Hska. split.
        - apply (acc_tr bsegs _ m m2 ap (8 * Z.of_nat (length a)) CL8 (8 * Z.of_nat da) ACA MU OFFfin);
            [intros Hp; pose proof (BNA ltac:(clear - Hp HLA; lia)) as H; clear - H HLA; lia | clear; lia | clear - HLA; lia].
        - apply (acc_tr bsegs _ m m2 rp (8 * N) CL8 (8 * Z.of_nat da) ACR MU OFFfin);
            [intros Hp; pose proof (BNR ltac:(clear - Hp; lia)) as H; clear - H; lia | clear; lia | clear; lia]. }
      assert (NEa : skipn cl a <> []) by (intros E; pose proof Hska as H; rewrite E in H; cbn in H; clear - H Hda; lia).
      replace (Z.of_nat da - Z.of_nat db)%Z with (Z.of_nat (length (skipn cl a))) by (rewrite Hska; clear - Hdb; lia).
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        lazymatch type of I with
        | INV ?s ?fl ?fc' ?cb ?mm ?r ?a1' ?b1 ?spz ?l ?aa ?fs ?fb ?fcells ?res ?cy ?m1 ?pre ?la ?lb ?c ?pa ?pb ?pr =>
            assert (I0 : INV s fl fc' cb mm r a1' b1 spz l aa fs fb fcells res cy m1 pre la lb 0%Z pa pb pr)
              by (replace 0%Z with c by exact K2; exact I)
        end.
        clear I.
        zstep.
        eapply evt_eq; [ | eapply (spw_copy_entry (skipn cl a)); [exact NEa | exact OU | exact AC | exact P | exact Hdb | exact I0] ].
        rewrite ?Z_to_bv_bv_unsigned. reflexivity.
      + (* [comment removed for export] *)
        ub. rewrite (land7 _ ALR), (land7 _ ALA').
        do 11 zstep. ub. do 4 zstep. ub.
        setreg 25%Z (Z_to_bv 64 (shad (ap + CL8))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
        setreg 26%Z (Z_to_bv 64 (shad (rp + CL8))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
        eapply evt_eq; [ | eapply (spw_loopP (length (skipn cl a)) (skipn cl a) _ m2 m2 [] c1 ap rp);
                           [reflexivity | exact NEa | exact OU | exact AC | exact P | exact Hdb | clear - Z1; lia | clear - Z0; lia | exact I] ].
        rewrite !Z_to_bv_bv_unsigned. reflexivity.
  Qed.

End Proofs.
