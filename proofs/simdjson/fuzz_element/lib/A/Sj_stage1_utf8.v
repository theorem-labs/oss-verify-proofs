(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_stage1_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section UTF8.
  Variable E : s1env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a1_shz E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Local Ltac chk x := a1_shz_buf SHZ x; zstep; rewrite shr3_div; zstep; zstep; rewrite sxb_z8; zstep; if_false.

  Lemma a1_utf8 : forall (Q : machine_state -> Prop) (i err : Z) (out : list Z) xra xa0 xa2 xa3 xs10 xs11 xt3 (m1 : mem),
    A1INV E m1 out -> (0 <= i < len)%Z -> (128 <= B bs i)%Z ->
    (forall xt1' xa0' xa1' xs9' xt3' m1', A1INV E m1' out ->
       evt asegs Q (A1ST E 0xba5b4 (Z_to_bv 64 (snd (utf8_step bs i err))) xt1' (Z_to_bv 64 len) xa0' xa1' xa2 xa3 xs9' xs10
                         (Z_to_bv 64 (fst (utf8_step bs i err))) xt3' (Z_to_bv 64 (e_BUF E)) m1')) ->
    evt asegs Q (A1ST E 0xba564 xra (Z_to_bv 64 err) (Z_to_bv 64 len) xa0 (Z_to_bv 64 (B bs i)) xa2 xa3 (Z_to_bv 64 i) xs10 xs11 xt3
                      (Z_to_bv 64 (e_BUF E)) m1).
  Proof using OK SHZ.
    intros Q i err out xra xa0 xa2 xa3 xs10 xs11 xt3 m1 INV Hi Hb HK.
    destruct OK as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, A1_STACK, A1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (B_range bs i BOK) as CR. set (b := B bs i) in *.
    unfold utf8_step in HK. fold b in HK.
    zstep. zstep.
    if_cases K64; zify_cond K64.
    -
      rewrite (proj2 (Z.eqb_eq _ _) K64) in HK. cbn [fst snd] in HK.
      zstep. s1norm. zstep. zstep. apply HK. exact INV.
    - rewrite (proj2 (Z.eqb_neq _ _) K64) in HK.
      zstep. zstep.
      if_cases K32; zify_cond K32.
      +
        rewrite (proj2 (Z.eqb_neq _ _) K32) in HK.
        pose proof (B_range bs (i + 1) BOK) as CR1. set (b1 := B bs (i + 1)) in *.
        pose proof (B_range bs (i + 2) BOK) as CR2. set (b2 := B bs (i + 2)) in *.
        a1_open_inv INV.
        zstep. zstep.
        if_cases K16; zify_cond K16.
        *
          rewrite (proj2 (Z.eqb_neq _ _) K16) in HK.
          pose proof (B_range bs (i + 3) BOK) as CR3. set (b3 := B bs (i + 3)) in *.
          zstep. s1norm. zstep. s1norm. zstep. zstep. s1norm. zstep. zstep.
          set (cond4 := ((len <? i + 3)%Z || negb (is_cont b1) || negb (is_cont b2) || negb (is_cont b3))%bool) in *.

          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
            assert (ERR4 : cond4 = true -> forall xra' xa0' xs11' xt3',
              evt asegs Q (A1ST E 0xba740 xra' (Z_to_bv 64 err) (Z_to_bv 64 len) xa0' (Z_to_bv 64 b) xa2 xa3 (Z_to_bv 64 i) xs10 xs11' xt3'
                                (Z_to_bv 64 (e_BUF E)) mc))
          end.
          { intros C4 xra' xa0' xs11' xt3'. rewrite C4 in HK. cbn [fst snd] in HK.
            zstep. zstep. zstep. zstep.
            change (0 <? 0)%Z with false. cbn [Z.b2z]. rewrite Z.land_0_l.
            zstep. zstep. if_false. zstep. zstep. zstep. zstep. apply HK. a1_close_inv. }
          zstep.
          if_cases KL3; zify_cond KL3.
          { apply ERR4. subst cond4. rewrite (proj2 (Z.ltb_lt _ _) KL3). reflexivity. }
          s1_cur_mem ltac:(fun m => pose proof (buf_read m (e_BUF E) bs (i + 1) BUFRO ltac:(lia)) as RD1). fold b1 in RD1.
          zstep. zstep. zstep. s1norm. zstep. chk (e_BUF E + (i + 1))%Z.
          zstep. s1norm. zstep. zstep.
          if_cases KC1; zify_cond KC1; rewrite (sbyte_signed _ CR1) in KC1.
          { apply ERR4. subst cond4. rewrite (not_cont_of_gt b1 CR1 KC1). rewrite orb_true_r. reflexivity. }
          s1_cur_mem ltac:(fun m => pose proof (buf_read m (e_BUF E) bs (i + 2) BUFRO ltac:(lia)) as RD2). fold b2 in RD2.
          zstep. zstep. zstep. s1norm. zstep. chk (e_BUF E + (i + 2))%Z.
          zstep. s1norm. zstep. zstep.
          if_cases KC2; zify_cond KC2; rewrite (sbyte_signed _ CR2) in KC2.
          { apply ERR4. subst cond4. rewrite (not_cont_of_gt b2 CR2 KC2). rewrite orb_true_r. reflexivity. }
          s1_cur_mem ltac:(fun m => pose proof (buf_read m (e_BUF E) bs (i + 3) BUFRO ltac:(lia)) as RD3). fold b3 in RD3.
          zstep. zstep. zstep. s1norm. zstep. chk (e_BUF E + (i + 3))%Z.
          zstep. s1norm. zstep.
          if_cases KC3; zify_cond KC3; rewrite (sbyte_signed _ CR3) in KC3.
          { apply ERR4. subst cond4. rewrite (not_cont_of_gt b3 CR3 ltac:(lia)). rewrite orb_true_r. reflexivity. }
          assert (C4 : cond4 = false).
          { subst cond4. rewrite (proj2 (Z.ltb_ge _ _) KL3), (cont_of_le b1 CR1 KC1), (cont_of_le b2 CR2 KC2), (cont_of_le b3 CR3 ltac:(lia)). reflexivity. }
          rewrite C4 in HK. cbn [fst snd] in HK. clear ERR4.
          step. rewrite (spill_byte_land b1 CR1).
          zstep.
          if_cases K244; zify_cond K244.
          --
             assert (E240 : (b =? 240)%Z = false) by (apply Z.eqb_neq; lia).
             assert (G244 : (244 <? b)%Z = false) by (apply Z.ltb_ge; lia).
             rewrite E240, G244, (proj2 (Z.eqb_eq _ _) K244) in HK. cbn [andb orb] in HK. rewrite orb_false_r in HK.
             zstep. zstep. zstep. zstep.
             destruct (Z.ltb_spec b1 144) as [L144|L144]; cbn [Z.b2z Z.lxor Pos.lxor].
             ++ assert (X : (143 <? b1)%Z = false) by (apply Z.ltb_ge; lia). rewrite X in HK.
                if_true. zstep. s1norm. zstep. zstep. apply HK. a1_close_inv.
             ++ assert (X : (143 <? b1)%Z = true) by (apply Z.ltb_lt; lia). rewrite X in HK.
                if_false. zstep. zstep. s1norm. zstep. zstep. apply HK. a1_close_inv.
          -- rewrite (proj2 (Z.eqb_neq _ _) K244) in HK. cbn [andb] in HK. rewrite orb_false_r in HK.
             zstep.
             if_cases K240; zify_cond K240.
             ++
                rewrite (proj2 (Z.eqb_neq _ _) K240) in HK. cbn [andb orb] in HK.
                zstep. zstep.
                destruct (Z.ltb_spec b 245) as [L245|L245]; cbn [Z.b2z Z.lxor Pos.lxor].
                ** assert (X : (244 <? b)%Z = false) by (apply Z.ltb_ge; lia). rewrite X in HK.
                   zstep. if_true. zstep. s1norm. zstep. zstep. apply HK. a1_close_inv.
                ** assert (X : (244 <? b)%Z = true) by (apply Z.ltb_lt; lia). rewrite X in HK.
                   zstep. if_false. zstep. zstep. s1norm. zstep. zstep. apply HK. a1_close_inv.
             ++
                assert (G244 : (244 <? b)%Z = false) by (apply Z.ltb_ge; lia).
                rewrite G244, (proj2 (Z.eqb_eq _ _) K240) in HK. cbn [andb] in HK. rewrite orb_false_r in HK.
                zstep. zstep. zstep.
                destruct (Z.ltb_spec b1 144) as [L144|L144]; cbn [Z.b2z].
                ** if_false. zstep. zstep. s1norm. zstep. zstep. apply HK. a1_close_inv.
                ** if_true. zstep. s1norm. zstep. zstep. apply HK. a1_close_inv.
        *
          rewrite (proj2 (Z.eqb_eq _ _) K16) in HK.
          zstep. s1norm. zstep. zstep.
          if_cases KL2; zify_cond KL2.
          --
             rewrite (proj2 (Z.ltb_lt _ _) KL2) in HK. cbn [orb fst snd] in HK.
             zstep. if_false. zstep. s1norm. zstep. zstep. apply HK. a1_close_inv.
          -- rewrite (proj2 (Z.ltb_ge _ _) KL2) in HK. cbn [orb] in HK.
             s1_cur_mem ltac:(fun m => pose proof (buf_read m (e_BUF E) bs (i + 1) BUFRO ltac:(lia)) as RD1). fold b1 in RD1.
             zstep. s1norm. zstep. zstep. s1norm. zstep. chk (e_BUF E + (i + 1))%Z.
             zstep. s1norm. zstep. zstep. zstep. zstep.
             if_cases KC1; zify_cond KC1; rewrite (sbyte_signed _ CR1) in KC1.
             ++ rewrite (not_cont_of_gt b1 CR1 KC1) in HK. cbn [orb fst snd] in HK.
                apply HK. a1_close_inv.
             ++ rewrite (cont_of_le b1 CR1 KC1) in HK. cbn [orb] in HK.
                zstep. zstep. zstep. s1norm. zstep. zstep.
                s1_cur_mem ltac:(fun m => pose proof (buf_read m (e_BUF E) bs (i + 2) BUFRO ltac:(lia)) as RD2). fold b2 in RD2.
                chk (e_BUF E + (i + 2))%Z.
                zstep. zstep. s1norm. zstep. zstep.
                if_cases KC2; zify_cond KC2; rewrite (sbyte_signed _ CR2) in KC2.
                ** rewrite (not_cont_of_gt b2 CR2 KC2) in HK. cbn [fst snd] in HK.
                   apply HK. a1_close_inv.
                ** rewrite (cont_of_le b2 CR2 KC2) in HK. cbn [fst snd] in HK.
                   pose proof (rw_cells_C8_read1_at asegs _ _ [_; _] _ _ FRlo) as RDS.
                   cbn [cells_size csize Nat.add] in RDS. change (Z.of_nat 16) with 16%Z in RDS.
                   step. rewrite (spill_byte b1 CR1). s1norm.
                   zstep. zstep.
                   if_cases K237; zify_cond K237.
                   ---
                       assert (E224 : (b =? 224)%Z = false) by (apply Z.eqb_neq; lia).
                       rewrite E224, (proj2 (Z.eqb_eq _ _) K237) in HK. cbn [andb orb] in HK.
                       zstep. zstep.
                       if_cases K159; zify_cond K159.
                       +++ rewrite (proj2 (Z.ltb_ge _ _) K159) in HK.
                           zstep. s1norm. zstep. zstep. apply HK. a1_close_inv.
                       +++ rewrite (proj2 (Z.ltb_lt _ _) K159) in HK.
                           zstep. zstep. s1norm. zstep. zstep. apply HK. a1_close_inv.
                   --- rewrite (proj2 (Z.eqb_neq _ _) K237) in HK. cbn [andb] in HK. rewrite orb_false_r in HK.
                       zstep.
                       if_cases K224; zify_cond K224.
                       +++
                           rewrite (proj2 (Z.eqb_neq _ _) K224) in HK. cbn [andb] in HK.
                           zstep. s1norm. zstep. zstep. apply HK. a1_close_inv.
                       +++ rewrite (proj2 (Z.eqb_eq _ _) K224) in HK. cbn [andb] in HK.
                           zstep.
                           if_cases K160; zify_cond K160.
                           *** rewrite (proj2 (Z.ltb_lt _ _) K160) in HK.
                               zstep. zstep. s1norm. zstep. zstep. apply HK. a1_close_inv.
                           *** rewrite (proj2 (Z.ltb_ge _ _) K160) in HK.
                               zstep. zstep. s1norm. zstep. zstep. apply HK. a1_close_inv.
      +
        rewrite (proj2 (Z.eqb_eq _ _) K32) in HK.
        pose proof (B_range bs (i + 1) BOK) as CR1. set (b1 := B bs (i + 1)) in *.
        pose proof INV as INV'. a1_open_inv INV'.
        pose proof (buf_read m1 (e_BUF E) bs (i + 1) BUFRO ltac:(lia)) as RD1. fold b1 in RD1.
        zstep. s1norm. zstep. zstep. s1norm. zstep. chk (e_BUF E + (i + 1))%Z.
        zstep. s1norm. zstep. zstep.
        if_cases KC; zify_cond KC; rewrite (sbyte_signed _ CR1) in KC.
        * rewrite (not_cont_of_gt b1 CR1 KC) in HK. cbn [fst snd] in HK.
          zstep. zstep. apply HK. exact INV.
        * rewrite (cont_of_le b1 CR1 KC) in HK. cbn [fst snd] in HK.
          zstep. zstep.
          if_cases K194; zify_cond K194.
          -- rewrite (proj2 (Z.ltb_ge _ _) K194) in HK.
             zstep. s1norm. zstep. apply HK. exact INV.
          -- rewrite (proj2 (Z.ltb_lt _ _) K194) in HK.
             zstep. zstep. s1norm. zstep. apply HK. exact INV.
  Qed.
End UTF8.
