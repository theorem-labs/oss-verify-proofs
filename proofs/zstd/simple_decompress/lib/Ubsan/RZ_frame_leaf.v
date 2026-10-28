(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_frame_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import frame_kit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma zd_iserror_proof : zd_iserror_stmt.
Proof.
  intros until c. intros Hc ->. unfold PZD_ISERROR.
  zstep. zstep. zstep. rewrite zd_is_error_sltiu.
  apply evt_done. reflexivity.
Qed.

Lemma zd_errcode_proof : zd_errcode_stmt.
Proof.
  intros until c. intros Hc ->. unfold PZD_ERRCODE.
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. unfold zd_errcode_post. eexists.
  replace (Z.land ((Z.b2z (c <? 18446744073709551497) + -1) mod 18446744073709551616) (bv_swrap 32 (0 - c) mod 18446744073709551616))
    with (zd_error_code c); [reflexivity|].
  unfold zd_error_code. rewrite zd_is_error_lit. change (2^64) with 18446744073709551616 in *.
  destruct (Z.ltb_spec c 18446744073709551497); destruct (Z.ltb_spec 18446744073709551496 c); try lia; cbn [Z.b2z].
  - reflexivity.
  - sw32 (18446744073709551616 - c).
    change ((1 + -1) mod 18446744073709551616) with 0. change ((0 + -1) mod 18446744073709551616) with (Z.ones 64).
    rewrite Z.mod_small by lia. rewrite Z.land_comm, Z.land_ones by lia. change (2^64) with 18446744073709551616.
    rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma bt_form : forall b x, 0 <= b < 65536 -> 0 <= x ->
  ((b * 2305843009213693952) mod 18446744073709551616) ≫ 62 = ((b + 65536 * x) / 2) mod 4.
Proof. intros b x Hb Hx. rewrite Z.shiftr_div_pow2 by lia. change (2^62) with 4611686018427387904. Z.div_mod_to_equations. lia. Qed.
Lemma last_form : forall x b, 0 <= b < 256 -> Z.land (x * 256 + b) 1 = b mod 2.
Proof. intros x b Hb. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2. Z.div_mod_to_equations. lia. Qed.

Section GETCBLOCK.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SRC BP : Z) (src : list Z) (ip size : Z) (cs0 : list cell).
  Hypothesis SB : bytes_at usegs m SRC (map (Z_to_bv 8) src).
  Hypothesis OK : all_bytes src.
  Hypothesis IP0 : 0 <= ip.
  Hypothesis SZ0 : 0 <= size.
  Hypothesis IPS : ip + size <= zlen src.
  Hypothesis BPC0 : rw_cells usegs m BP cs0.
  Hypothesis BPSZ : cells_size cs0 = 12%nat.
  Hypothesis MI : mem_inv usegs m.
  Hypothesis SRC0 : 0 < SRC.
  Hypothesis BP0 : 0 < BP.
  Hypothesis BPA : BP mod 4 = 0.

  Lemma zd_getcblock_walk :
    evt usegs (zd_getcblock_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BP src ip size m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SRC + ip)) (Z_to_bv 64 size) (Z_to_bv 64 BP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_GETCBLOCK) fc None m (seg_rom usegs)).
  Proof.
    unfold PZD_GETCBLOCK.
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    destruct (rw_cells_forget _ _ _ _ BPC0) as [junk BPC]. rewrite BPSZ in BPC.
    pose proof (rw_cells_bound _ _ _ _ BPC0) as DBP. rewrite BPSZ in DBP. change (Z.of_nat 12) with 12 in DBP.
    assert (MU : munch [(BP, BP + 12)] m m) by apply munch_refl.
    assert (WM : wmono usegs m m) by apply wmono_refl.
    zs. zs. if_cases K; zify_cond K.
    - zs. fck. zs. zs. fck. zs. fck. zs. zs. fck.
      zlb SB OK (ip + 1). zlb SB OK (ip + 2). zlb SB OK ip.
      do 9 zs.
      set (bp := cblock_props (le24 src ip)).
      pose proof (le24_range src OK ip) as RH. change (2^24) with 16777216 in RH.
      assert (EH : Znth (ip + 2) src * 65536 + (Znth (ip + 1) src * 256 + Znth ip src) = le24 src ip) by (rewrite le24_bytes; lia).
      rewrite (bt_form (Znth (ip + 1) src * 256 + Znth ip src) (Znth (ip + 2) src)) by lia.
      replace (Znth (ip + 1) src * 256 + Znth ip src + 65536 * Znth (ip + 2) src) with (le24 src ip) by (rewrite le24_bytes; lia).
      rewrite last_form by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite EH.
      replace (Znth ip src mod 2) with (le24 src ip mod 2) by (rewrite le24_bytes; Z.div_mod_to_equations; lia).
      change ((le24 src ip / 2) mod 4) with (bp_type bp). change (le24 src ip mod 2) with (bp_last bp). change (le24 src ip / 8) with (bp_orig bp).
      assert (RBT : 0 <= bp_type bp < 4) by (unfold bp, cblock_props, bp_type; Z.div_mod_to_equations; lia).
      assert (RLA : 0 <= bp_last bp < 2) by (unfold bp, cblock_props, bp_last; Z.div_mod_to_equations; lia).
      assert (RCS : 0 <= bp_orig bp < 2097152) by (unfold bp, cblock_props, bp_orig; Z.div_mod_to_equations; lia).
      zs. zs. zs.
      assert (RES : get_cblock_size src ip size = Some (if bp_type bp =? bt_rle then 1 else if bp_type bp =? bt_reserved then ZERR ZE_corruption_detected else bp_orig bp, bp)).
      { unfold get_cblock_size, ZD_blockHeaderSize. replace (size <? 3) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      assert (FIN : forall (x11 x12 x13 x14 x15 : word),
        evt usegs (zd_getcblock_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BP src ip size m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cblock_ret (get_cblock_size src ip size))) x11 x12 x13 x14 x15 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m0 (seg_rom usegs))).
      { intros. apply evt_done. unfold zd_getcblock_post. do 5 eexists. exists m0. eexists.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BPC|]. split; [reflexivity|].
        intros v bp' E. rewrite RES in E. injection E as _ <-. reflexivity. }
      zs. if_cases B1; zify_cond B1.
      + zs. replace (Z_to_bv 64 (bp_type bp)) with (Z_to_bv 64 (cblock_ret (get_cblock_size src ip size)))
          by (rewrite RES; cbn [cblock_ret]; unfold bt_rle; rewrite B1; reflexivity). apply FIN.
      + zs. zs. if_cases B3; zify_cond B3.
        * zs. zs. replace (Z_to_bv 64 (bp_orig bp)) with (Z_to_bv 64 (cblock_ret (get_cblock_size src ip size))).
          { apply FIN. }
          rewrite RES. cbn [cblock_ret]. unfold bt_rle, bt_reserved. replace (bp_type bp =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
          replace (bp_type bp =? 3) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
        * zs. zs. replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (cblock_ret (get_cblock_size src ip size))).
          { apply FIN. }
          rewrite RES. cbn [cblock_ret]. unfold bt_rle, bt_reserved. replace (bp_type bp =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
          rewrite B3. change (3 =? 3) with true. cbv iota. apply Z_to_bv_eqm. reflexivity.
    - assert (RES : get_cblock_size src ip size = None).
      { unfold get_cblock_size, ZD_blockHeaderSize. replace (size <? 3) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
      zs. zs. replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (cblock_ret (get_cblock_size src ip size)))
        by (rewrite RES; apply Z_to_bv_eqm; reflexivity).
      apply evt_done. unfold zd_getcblock_post. do 5 eexists. exists m. eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BPC|]. split; [reflexivity|].
      intros v bp E. rewrite RES in E. discriminate E.
  Qed.
End GETCBLOCK.

Lemma zd_getcblock_proof : zd_getcblock_stmt.
Proof.
  intros until cs0. intros SB OK IP0 SZ0 IPS SRC0 BPC BPSZ BP0 BPA MI -> -> ->.
  eapply zd_getcblock_walk; eassumption.
Qed.

Print Assumptions zd_getcblock_proof.
