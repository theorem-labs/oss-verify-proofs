(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage1_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section UTF8.
  Variable E : s1env.
  Hypothesis OK : env_ok_u E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma u1_utf8 : forall (Q : machine_state -> Prop) (i err : Z) (out : list Z) (idxc : Z) xa0 xa5 xt3 xt5 (m1 : mem),
    U1INV E m1 out idxc err -> (0 <= i < len)%Z -> (128 <= B bs i)%Z ->
    (forall xa5' xt5' m1', U1INV E m1' out idxc (snd (utf8_step bs i err)) ->
       evt usegs Q (U1ST E 0x41a18 (Z_to_bv 64 (fst (utf8_step bs i err))) xa0 (Z_to_bv 64 1) xa5' (Z_to_bv 64 i) (Z_to_bv 64 len)
                         xt3 xt5' (Z_to_bv 64 (B bs i)) m1')) ->
    evt usegs Q (U1ST E 0x41a9c (Z_to_bv 64 (i + e_BUF E)) xa0 (Z_to_bv 64 1) xa5 (Z_to_bv 64 i) (Z_to_bv 64 len)
                      xt3 xt5 (Z_to_bv 64 (B bs i)) m1).
  Proof using OK.
    intros Q i err out idxc xa0 xa5 xt3 xt5 m1 INV Hi Hb HK.
    destruct OK as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, U1_STACK, U1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (B_range bs i BOK) as CR. set (b := B bs i) in *.
    pose proof (B_range bs (i + 1) BOK) as CR1. set (b1 := B bs (i + 1)) in *.
    pose proof (B_range bs (i + 2) BOK) as CR2. set (b2 := B bs (i + 2)) in *.
    pose proof (B_range bs (i + 3) BOK) as CR3. set (b3 := B bs (i + 3)) in *.
    unfold utf8_step in HK. fold b b1 b2 b3 in HK. unfold UTF8_ERROR in HK.
    u1_open_inv INV.

    zstep. if_cases G0; zify_cond G0; [|exfalso; lia].
    zstep. zstep.
    if_cases K64; zify_cond K64.
    -
      rewrite (proj2 (Z.eqb_eq _ _) K64) in HK. cbn [fst snd] in HK.
      zstep. zstep. zstep. zstep. s1norm. zstep. apply HK. u1_close_inv.
    - rewrite (proj2 (Z.eqb_neq _ _) K64) in HK.
      zstep. zstep.
      if_cases K32; zify_cond K32.
      +
        rewrite (proj2 (Z.eqb_neq _ _) K32) in HK.
        zstep. zstep. s1norm. zstep. zstep.
        if_cases K16; zify_cond K16.
        *
          rewrite (proj2 (Z.eqb_neq _ _) K16) in HK.
          set (cond4 := ((len <? i + 3)%Z || negb (is_cont b1) || negb (is_cont b2) || negb (is_cont b3))%bool) in *.
          assert (ERR : cond4 = true -> forall xa5' xt5' m', U1INV E m' out idxc err ->
                    evt usegs Q (U1ST E 0x41c24 (Z_to_bv 64 (i + 1)) xa0 (Z_to_bv 64 1) xa5' (Z_to_bv 64 i) (Z_to_bv 64 len) xt3 xt5' (Z_to_bv 64 b) m')).
          { intros C4 xa5' xt5' m' INV2. rewrite C4 in HK. cbn [fst snd] in HK.
            clear FRlo FRtb FRhi PARSER IDXA IDXL IDXF BUFRO MI MU WM ST PBL. u1_open_inv INV2.
            zstep. if_true. zstep. zstep. zstep. apply HK. u1_close_inv. }
          zstep. s1norm. zstep. s1norm. zstep. zstep.
          if_cases KL3; zify_cond KL3.
          { apply ERR; [subst cond4; rewrite (proj2 (Z.ltb_lt _ _) KL3); reflexivity| u1_close_inv]. }
          s1_cur_mem ltac:(fun m => pose proof (ubuf_read m (e_BUF E) bs (i + 1) BUFRO ltac:(lia)) as RD1). fold b1 in RD1.
          zstep. zstep. s1norm. zstep. if_cases G1; zify_cond G1; [|exfalso; lia].
          zstep. zstep. s1norm. zstep. zstep.
          if_cases KC1; zify_cond KC1; rewrite (sbyte_signed _ CR1) in KC1.
          { apply ERR; [subst cond4; rewrite (not_cont_of_gt b1 CR1 KC1); rewrite orb_true_r; reflexivity| u1_close_inv]. }
          s1_cur_mem ltac:(fun m => pose proof (ubuf_read m (e_BUF E) bs (i + 2) BUFRO ltac:(lia)) as RD2). fold b2 in RD2.
          zstep. zstep. zstep. s1norm. zstep. if_cases G2; zify_cond G2; [|exfalso; lia].
          zstep. zstep. s1norm. zstep.
          if_cases KC2; zify_cond KC2; rewrite (sbyte_signed _ CR2) in KC2.
          { apply ERR; [subst cond4; rewrite (not_cont_of_gt b2 CR2 KC2); rewrite orb_true_r; reflexivity| u1_close_inv]. }
          s1_cur_mem ltac:(fun m => pose proof (ubuf_read m (e_BUF E) bs (i + 3) BUFRO ltac:(lia)) as RD3). fold b3 in RD3.
          zstep. zstep. zstep. s1norm. zstep. if_cases G3; zify_cond G3; [|exfalso; lia].
          zstep. zstep. s1norm. zstep.
          if_cases KC3; zify_cond KC3; rewrite (sbyte_signed _ CR3) in KC3.
          { apply ERR; [subst cond4; rewrite (not_cont_of_gt b3 CR3 KC3); rewrite orb_true_r; reflexivity| u1_close_inv]. }
          assert (C4 : cond4 = false).
          { subst cond4. rewrite (proj2 (Z.ltb_ge _ _) KL3), (cont_of_le b1 CR1 KC1), (cont_of_le b2 CR2 KC2), (cont_of_le b3 CR3 KC3). reflexivity. }
          rewrite C4 in HK. cbn [fst snd] in HK. clear ERR.
          pose proof (rw_cells_C8_read1_at usegs _ _ [CB 8 j0] _ _ FRlo) as RDS.
          cbn [cells_size csize Nat.add] in RDS. change (Z.of_nat 8) with 8%Z in RDS.
          step. rewrite (spill_byte b1 CR1). s1norm.
          set (ec := (((b =? 240)%Z && (b1 <? 144)%Z) || ((b =? 244)%Z && (143 <? b1)%Z) || (244 <? b)%Z)%bool) in *.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
            assert (KOK : ec = false -> forall xa5' xra', evt usegs Q (U1ST E 0x41bf4 xra' xa0 (Z_to_bv 64 1) xa5' (Z_to_bv 64 i) (Z_to_bv 64 len) xt3 (Z_to_bv 64 b1) (Z_to_bv 64 b) mc));
            [| assert (KER : ec = true -> forall xa5' xra', evt usegs Q (U1ST E 0x41bec xra' xa0 (Z_to_bv 64 1) xa5' (Z_to_bv 64 i) (Z_to_bv 64 len) xt3 (Z_to_bv 64 b1) (Z_to_bv 64 b) mc))]
          end.
          { intros EC xa5' xra'. rewrite EC in HK. zstep. s1norm. zstep. apply HK. u1_close_inv. }
          { intros EC xa5' xra'. rewrite EC in HK. zstep. zstep. zstep. s1norm. zstep. apply HK. u1_close_inv. }
          zstep.
          if_cases K240; zify_cond K240.
          --
             zstep. if_cases K144; zify_cond K144.
             ++ apply KER. subst ec. rewrite (proj2 (Z.eqb_eq _ _) K240), (proj2 (Z.ltb_lt _ _) K144). reflexivity.
             ++ zstep. apply KOK. subst ec. rewrite (proj2 (Z.eqb_eq _ _) K240), (proj2 (Z.ltb_ge _ _) K144).
                replace (b =? 244)%Z with false by (symmetry; apply Z.eqb_neq; lia).
                replace (244 <? b)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
          -- zstep. if_cases K244; zify_cond K244.
             ++
                zstep. if_cases K245; zify_cond K245.
                ** apply KER. subst ec. replace (244 <? b)%Z with true by (symmetry; apply Z.ltb_lt; lia). rewrite !orb_true_r. reflexivity.
                ** zstep. apply KOK. subst ec. rewrite (proj2 (Z.eqb_neq _ _) K240), (proj2 (Z.eqb_neq _ _) K244).
                   replace (244 <? b)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
             ++
                zstep. if_cases K143; zify_cond K143.
                ** apply KOK. subst ec. rewrite (proj2 (Z.eqb_neq _ _) K240), (proj2 (Z.eqb_eq _ _) K244).
                   replace (143 <? b1)%Z with false by (symmetry; apply Z.ltb_ge; lia).
                   replace (244 <? b)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
                ** apply KER. subst ec. rewrite (proj2 (Z.eqb_neq _ _) K240), (proj2 (Z.eqb_eq _ _) K244).
                   replace (143 <? b1)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
        *
          rewrite (proj2 (Z.eqb_eq _ _) K16) in HK.
          set (cond3 := ((len <? i + 2)%Z || negb (is_cont b1) || negb (is_cont b2))%bool) in *.
          assert (ERR : cond3 = true -> forall xa5' xt5' m', U1INV E m' out idxc err ->
                    evt usegs Q (U1ST E 0x41c3c (Z_to_bv 64 (i + 1)) xa0 (Z_to_bv 64 1) xa5' (Z_to_bv 64 i) (Z_to_bv 64 len) xt3 xt5' (Z_to_bv 64 b) m')).
          { intros C3 xa5' xt5' m' INV2. rewrite C3 in HK. cbn [fst snd] in HK.
            clear FRlo FRtb FRhi PARSER IDXA IDXL IDXF BUFRO MI MU WM ST PBL. u1_open_inv INV2.
            zstep. zstep. zstep. apply HK. u1_close_inv. }
          zstep.
          if_cases KL2; zify_cond KL2.
          { zstep. if_false. zstep. s1norm.
            apply ERR; [subst cond3; rewrite (proj2 (Z.ltb_lt _ _) KL2); reflexivity| u1_close_inv]. }
          s1_cur_mem ltac:(fun m => pose proof (ubuf_read m (e_BUF E) bs (i + 1) BUFRO ltac:(lia)) as RD1). fold b1 in RD1.
          zstep. s1norm. zstep. zstep. s1norm. zstep. if_cases G1; zify_cond G1; [|exfalso; lia].
          zstep. zstep. s1norm. zstep. zstep.
          if_cases KC1; zify_cond KC1; rewrite (sbyte_signed _ CR1) in KC1.
          { apply ERR; [subst cond3; rewrite (not_cont_of_gt b1 CR1 KC1); rewrite orb_true_r; reflexivity| u1_close_inv]. }
          s1_cur_mem ltac:(fun m => pose proof (ubuf_read m (e_BUF E) bs (i + 2) BUFRO ltac:(lia)) as RD2). fold b2 in RD2.
          zstep. zstep. zstep. s1norm. zstep. if_cases G2; zify_cond G2; [|exfalso; lia].
          zstep. zstep. s1norm. zstep.
          if_cases KC2; zify_cond KC2; rewrite (sbyte_signed _ CR2) in KC2.
          { apply ERR; [subst cond3; rewrite (not_cont_of_gt b2 CR2 KC2); rewrite orb_true_r; reflexivity| u1_close_inv]. }
          assert (C3 : cond3 = false).
          { subst cond3. rewrite (proj2 (Z.ltb_ge _ _) KL2), (cont_of_le b1 CR1 KC1), (cont_of_le b2 CR2 KC2). reflexivity. }
          rewrite C3 in HK. cbn [fst snd] in HK. clear ERR.
          pose proof (rw_cells_C8_read1_at usegs _ _ [CB 8 j0; CB 8 j8] _ _ FRlo) as RDS.
          cbn [cells_size csize Nat.add] in RDS. change (Z.of_nat 16) with 16%Z in RDS.
          step. rewrite (spill_byte b1 CR1). s1norm.
          set (ec := (((b =? 224)%Z && (b1 <? 160)%Z) || ((b =? 237)%Z && (159 <? b1)%Z))%bool) in *.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
            assert (KOK : ec = false -> forall xa5' xra', evt usegs Q (U1ST E 0x41b64 xra' xa0 (Z_to_bv 64 1) xa5' (Z_to_bv 64 i) (Z_to_bv 64 len) xt3 (Z_to_bv 64 b1) (Z_to_bv 64 b) mc));
            [| assert (KER : ec = true -> forall xa5' xra', evt usegs Q (U1ST E 0x41b5c xra' xa0 (Z_to_bv 64 1) xa5' (Z_to_bv 64 i) (Z_to_bv 64 len) xt3 (Z_to_bv 64 b1) (Z_to_bv 64 b) mc))]
          end.
          { intros EC xa5' xra'. rewrite EC in HK. zstep. s1norm. zstep. apply HK. u1_close_inv. }
          { intros EC xa5' xra'. rewrite EC in HK. zstep. zstep. zstep. s1norm. zstep. apply HK. u1_close_inv. }
          zstep. zstep.
          if_cases K224; zify_cond K224.
          --
             zstep. zstep. if_cases K159; zify_cond K159.
             ++ apply KER. subst ec. rewrite (proj2 (Z.eqb_eq _ _) K224).
                replace (b1 <? 160)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
             ++ zstep. apply KOK. subst ec. rewrite (proj2 (Z.eqb_eq _ _) K224).
                replace (b1 <? 160)%Z with false by (symmetry; apply Z.ltb_ge; lia).
                replace (b =? 237)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
          -- zstep. zstep. if_cases K237; zify_cond K237.
             ++ apply KOK. subst ec. rewrite (proj2 (Z.eqb_neq _ _) K224), (proj2 (Z.eqb_neq _ _) K237). reflexivity.
             ++
                zstep. zstep. if_cases K159; zify_cond K159.
                ** apply KOK. subst ec. rewrite (proj2 (Z.eqb_neq _ _) K224), (proj2 (Z.eqb_eq _ _) K237).
                   replace (159 <? b1)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
                ** apply KER. subst ec. rewrite (proj2 (Z.eqb_neq _ _) K224), (proj2 (Z.eqb_eq _ _) K237).
                   replace (159 <? b1)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      +
        rewrite (proj2 (Z.eqb_eq _ _) K32) in HK.
        s1_cur_mem ltac:(fun m => pose proof (ubuf_read m (e_BUF E) bs (i + 1) BUFRO ltac:(lia)) as RD1). fold b1 in RD1.
        zstep. s1norm. zstep. zstep. s1norm. zstep.
        if_cases G1; zify_cond G1; [|exfalso; lia].
        zstep. zstep. s1norm. zstep.
        if_cases KC; zify_cond KC; rewrite (sbyte_signed _ CR1) in KC.
        * rewrite (not_cont_of_gt b1 CR1 KC) in HK. cbn [fst snd] in HK.
          zstep. zstep. zstep. apply HK. u1_close_inv.
        * rewrite (cont_of_le b1 CR1 KC) in HK. cbn [fst snd] in HK.
          zstep. zstep.
          if_cases K194; zify_cond K194.
          -- assert (X : (b <? 194)%Z = false) by (apply Z.ltb_ge; lia). rewrite X in HK.
             zstep. s1norm. apply HK. u1_close_inv.
          -- assert (X : (b <? 194)%Z = true) by (apply Z.ltb_lt; lia). rewrite X in HK.
             zstep. zstep. zstep. zstep. s1norm. apply HK. u1_close_inv.
  Qed.
End UTF8.
