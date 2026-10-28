(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C7 ECH_AKit ECH_AsKit ECH_AsKitK AsWalk ECH_AC8_blockA ECH_AC14_bio2buf_seg ECH_AC14_ladder_seg ECH_AC14_fmt_seg ECH_AC14_b64arm_seg.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ADF_DEC : Z := 0x553768.    (* [comment removed for export] *)
Definition ADF_HDR : Z := 0x553834.
Definition ADF_LOOP0 : Z := 0x51a9c0.
Definition ADF_HEAD : Z := 0x553908.   (* [comment removed for export] *)
Definition ADF_ADV : Z := 0x5540c0.
Definition ADF_DONE : Z := 0x554184.   Definition ADF_R_DONE : Z := 0x55418c.
Definition ADF_TA : Z := 0x5541b0.     Definition ADF_TA_R1 : Z := 0x5541b8.   Definition ADF_TA_R2 : Z := 0x5541d4.   (* [comment removed for export] *)
Definition ADF_TZ : Z := 0x5541e8.     Definition ADF_TZ_R1 : Z := 0x5541f0.   Definition ADF_TZ_R2 : Z := 0x554200.   (* [comment removed for export] *)
Definition ADF_TY : Z := 0x554230.     Definition ADF_TY_R1 : Z := 0x554238.   Definition ADF_TY_R2 : Z := 0x554254.   (* [comment removed for export] *)
Definition ADF_TX : Z := 0x554268.     Definition ADF_TX_R0 : Z := 0x554270.   Definition ADF_TX_R1 : Z := 0x554278.   Definition ADF_TX_R2 : Z := 0x554294.
Definition ADF_TX_R3 : Z := 0x5542ac.
Definition AERRL_R2 : Z := 0x5536b8.   Definition AERRL_R3 : Z := 0x5536cc.   (* [comment removed for export] *)
Definition AEXIT : Z := 0x5532c8.      Definition AEXIT_R : Z := 0x5532ec.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AFUNC_D1 : Z := 0x112560.   (* [comment removed for export] *)
Definition AFUNC_DF : Z := 0x112520.   (* [comment removed for export] *)
Definition AR_ECH_DECODE_ERROR : Z := 426.
Definition AECH_VERSION : Z := 0xfe0d.

(* [comment removed for export] *)
Definition olen_of (bs : list byte) : Z := match bs with b0 :: b1 :: _ => 256 * bv_unsigned b0 + bv_unsigned b1 | _ => 0 end.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  Local Ltac rw_join H1 H2 J :=
    lazymatch type of H1 with rw_cells ?sg ?mx ?A ?cs1 =>
    lazymatch type of H2 with rw_cells _ _ ?B ?cs2 =>
      let n := eval lazy in (Z.of_nat (cells_size cs1)) in
      assert (J : rw_cells sg mx A (cs1 ++ cs2));
      [ apply (proj2 (rw_cells_app sg mx A cs1 cs2)); split;
        [ exact H1 | change (A + Z.of_nat (cells_size cs1)) with (A + n); replace (A + n) with B by lia; exact H2 ]
      | cbn [app] in J; clear H1 H2 ] end end.

  (* [comment removed for export] *)
  Lemma afs_dec :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (T Bb : Z),
      0 <= T < 2^31 -> 0 < Bb -> Bb + 2 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists a0' a1',
          ms' = if (32 <=? T) && (T <? 1500)
                then MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Bb + 1)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 T) (Z_to_bv 64 Bb) s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 ADF_HDR) fc None m (seg_rom asegs)
                else MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 AR_PASSED_NULL_PARAMETER) (Z_to_bv 64 509) (Z_to_bv 64 T) (Z_to_bv 64 Bb) s8 (Z_to_bv 64 0) s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 ADF_TY) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 T) (Z_to_bv 64 Bb) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADF_DEC) fc None m (seg_rom asegs)).
  Proof.
    intros until Bb. intros TR BP BH MI. unfold ADF_DEC, ADF_HDR, ADF_TY, AR_PASSED_NULL_PARAMETER.
    zstep. step.
    destruct (andb (32 <=? T) (T <? 1500)) eqn:G.
    - apply andb_prop in G. destruct G as [G1 G2]. apply Z.leb_le in G1. apply Z.ltb_lt in G2.
      step. if_cases K2; zify_cond K2.
      2: { exfalso. try (change 18446744073709551615 with (Z.ones 64) in K2; rewrite ?Z.land_ones in K2 by lia). revert K2. clear - G1 G2 TR. Z.div_mod_to_equations. lia. }
      clear K2. go_to ADF_HDR. apply evt_done. exists a0. eexists. reflexivity.
    - step. if_cases K2; zify_cond K2.
      { exfalso. apply Bool.andb_false_iff in G. rewrite Z.leb_gt, Z.ltb_ge in G. try (change 18446744073709551615 with (Z.ones 64) in K2; rewrite ?Z.land_ones in K2 by lia).
        revert K2. clear - G TR. Z.div_mod_to_equations. lia. }
      clear K2. go_to ADF_TY. apply evt_done. do 2 eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afs_hdr :
    forall (rax s0w gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s8 s9 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q T Bb A bt st shf : Z) (bs : list byte)
           (w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w136 w144 w152 w160 w168 w176 w192 w200 w208 w216 w224 w232 : word),
      32 <= T < 1500 -> zlength bs = T -> bytes_at asegs m Bb bs -> 0 < Bb -> Bb + T < 2^63 -> Bb mod 8 = 0 -> accessible m Bb 8 ->
      0 <= q -> q + 464 <= 2^64 -> 0 <= A < 2^64 -> 0 <= bt < 2^64 -> 0 <= st < 2^64 -> st mod 8 = 0 ->
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 (wz st) w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 w168 w176 (wz A) w192 w200 w208 w216 w224 w232) ->
      mem_inv asegs m ->
      evt asegs (fun ms' => exists a0' a1' a2',
           (T - 2 < olen_of bs /\
              ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3 a4 a5 a6 a7
                            (Z_to_bv 64 A) (Z_to_bv 64 shf) (Z_to_bv 64 AR_INTERNAL_ERROR) (Z_to_bv 64 514) (Z_to_bv 64 (T - 2)) (Z_to_bv 64 Bb) s8 (Z_to_bv 64 0) s10 (Z_to_bv 64 bt) t3 t4 t5 t6)
                       F (Z_to_bv 64 ADF_TY) fc None m (seg_rom asegs))
        \/ (olen_of bs = 0 /\ exists m1,
              ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3 a4 a5 a6 a7
                            s2 (Z_to_bv 64 shf) (Z_to_bv 64 ASHB) s5 (Z_to_bv 64 (T - 2)) (Z_to_bv 64 0) (Z_to_bv 64 (Bb + 2)) s9 s10 (Z_to_bv 64 bt) t3 t4 t5 t6)
                       F (Z_to_bv 64 ADF_DONE) fc None m1 (seg_rom asegs)
              /\ munch [(q + 16, q + 144)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
              /\ rw_cells asegs m1 (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 (wz bt) (wz Bb) w96 w104 w112 w120 (wz st) w136))
        \/ (1 <= olen_of bs <= T - 2 /\ exists m1,
              ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3 a4 a5 a6 a7
                            (Z_to_bv 64 2) (Z_to_bv 64 shf) (Z_to_bv 64 ASHB) s5 (Z_to_bv 64 (T - 2)) (Z_to_bv 64 (olen_of bs)) (Z_to_bv 64 (Bb + 2)) s9 s10 (Z_to_bv 64 bt) t3 t4 t5 t6)
                       F (Z_to_bv 64 ADF_HEAD) fc None m1 (seg_rom asegs)
              /\ munch [(q + 16, q + 144)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
              /\ rw_cells asegs m1 (q + 16) (arp_sg1 w16 (wz AR_INTERNAL_ERROR) w32 w40 w48 (wz 0) (wz AECH_VERSION) (wz ARP_FILE) (wz bt) (wz Bb) w96 w104 w112 w120 (wz st) w136)))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 (Bb + 1)) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 shf) (Z_to_bv 64 ASHB) s5 (Z_to_bv 64 T) (Z_to_bv 64 Bb) s8 s9 s10 (Z_to_bv 64 bt) t3 t4 t5 t6)
            F (Z_to_bv 64 ADF_HDR) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros TR BSL BS BP BH B8 ACC Q1 Q2 AR BTR STR S8 SG1 SG2 MI.
    unfold ADF_HDR, ADF_TY, ADF_DONE, ADF_HEAD, AR_INTERNAL_ERROR, AECH_VERSION, ARP_FILE. unfold arp_sg1, arp_sg2, ASHB, wz in *.
    unfold zlength in BSL.
    pose proof (munch_refl [(q + 16, q + 144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct bs as [|b0 [|b1 bs2]]; try (cbn in BSL; exfalso; lia).
    pose proof (abyte_range b0) as B0. pose proof (abyte_range b1) as B1.
    pose proof (rd_raw _ _ _ 0 b0 BS eq_refl ltac:(lia)) as RD0. replace (Bb + 0) with Bb in RD0 by lia.
    pose proof (rd_raw _ _ _ 1 b1 BS eq_refl ltac:(lia)) as RD1.
    pose proof ACC as (_ & AHI' & _).
    cbn [olen_of].
    (* [comment removed for export] *)
    go. ck1f_load ACC Bb. step. if_lit.
    (* [comment removed for export] *)
    go. ck1f_load ACC (Bb + 1). go.
    (* [comment removed for export] *)
    unfold zxb in *. rewrite (unsigned_lit (bv_unsigned b0)) by lia. rewrite (unsigned_lit (bv_unsigned b1)) by lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (unsigned_lit (bv_unsigned b0 * 2 ^ 8)) by (change (2 ^ 8) with 256; lia).
    rewrite (Z.lor_comm (bv_unsigned b0 * 2 ^ 8) (bv_unsigned b1)). rewrite (lor_add_disjoint _ _ 8) by lia. change (2 ^ 8) with 256.
    replace (bv_unsigned b1 + bv_unsigned b0 * 256) with (256 * bv_unsigned b0 + bv_unsigned b1) by lia.
    set (olen := 256 * bv_unsigned b0 + bv_unsigned b1). assert (OR : 0 <= olen < 65536) by (subst olen; lia).
    replace (T + -2) with (T - 2) by lia.
    (* [comment removed for export] *)
    destruct (Z_lt_ge_dec (T - 2) olen) as [LT|GE].
    - if_cases K2; zify_cond K2; [kill K2|]. clear K2. go_to ADF_TY. apply evt_done. do 3 eexists. left. split; [exact LT| reflexivity].
    - if_cases K2; zify_cond K2; [| kill K2]. clear K2.
      (* [comment removed for export] *)
      go. rewrite zb_lxor_ones by lia. ub_dead. go.
      destruct (Z.eq_dec olen 0) as [Z0|NZ].
      + rewrite Z0 in *. if_lit. go_to ADF_DONE. apply evt_done. do 3 eexists. right; left. split; [reflexivity|]. eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
      + br.
        (* [comment removed for export] *)
        go_to ADF_HEAD.
        try rewrite (al8u st) in * by (first [exact S8| lia]). try rewrite (al8 st) in * by exact S8.
        apply evt_done. do 3 eexists. right; right. split; [lia|]. eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  Lemma afs_adv :
    forall (rax s0w gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q cur rem elen : Z),
      0 <= elen -> 4 + elen <= rem -> rem < 2^31 -> 0 <= cur -> cur + rem < 2^63 -> 0 <= q -> q + 464 <= 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 (Z_to_bv 64 (cur + 4 + elen)) s5 s6 (Z_to_bv 64 (rem - 4 - elen)) (Z_to_bv 64 (cur + 4 + elen)) s9 (Z_to_bv 64 elen) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (if rem - 4 - elen =? 0 then ADF_DONE else ADF_HEAD)) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 (Z_to_bv 64 (cur + 4 + elen)) s5 s6 (Z_to_bv 64 (rem - 4)) s8 s9 (Z_to_bv 64 elen) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADF_ADV) fc None m (seg_rom asegs)).
  Proof.
    intros until elen. intros ER EL RR CR CH Q1 Q2 MI. unfold ADF_ADV, ADF_DONE, ADF_HEAD.
    zstep. zstep.
    destruct (Z.eqb_spec (rem - 4 - elen) 0) as [E0|NE].
    - step. if_cases K2; zify_cond K2; [kill K2|]. clear K2. step. apply evt_done.
      replace (rem - 4 - elen =? 0) with true by (symmetry; apply Z.eqb_eq; exact E0). reflexivity.
    - step. if_cases K2; zify_cond K2; [| kill K2]. clear K2. apply evt_done.
      replace (rem - 4 - elen =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afs_done :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 ADF_R_DONE) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ADF_DONE) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold ADF_DONE, ADF_R_DONE, P_ossl_echstore_entry_free. step. step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma afs_done2 :
    forall (s0w gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (q ff A bt Bb : Z) (w16 w24 w32 w40 w48 w56 w64 w72 w96 w104 w112 w128 w136 w144 w168 w176 w192 w200 w208 w216 w224 w232 : word),
      0 <= q -> q + 464 <= 2^64 ->
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 (wz bt) (wz Bb) w96 w104 w112 (wz 0) w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 (wz ff) (wz ff) w168 w176 (wz A) w192 w200 w208 w216 w224 w232) ->
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFM_ERRL_R1) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 bt) a1 a2 a3 a4 a5 a6 a7
                                          (Z_to_bv 64 A) s3 s4 (Z_to_bv 64 1) s6 (Z_to_bv 64 Bb) (Z_to_bv 64 ff) s9 (Z_to_bv 64 ff) (Z_to_bv 64 bt) t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_free_all) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADF_R_DONE) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADF_R_DONE)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros Q1 Q2 SG1 SG2 MI. unfold ADF_R_DONE in *. retpc. unfold AFM_ERRL_R1, P_BIO_free_all. unfold arp_sg1, arp_sg2, wz in SG1, SG2.
    go. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition arglue (raA raB target : Z) (a0v a1v a2v : word) (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) : Prop :=
    forall (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem), mem_inv asegs m1 ->
      evt asegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                   ms' = MS (mkR (Z_to_bv 64 raB) sp gp tp v0 v1 v2 s0 s1 a0v a1v a2v c3 c4 c5 c6 c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 target) fc None m1 (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 raA) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (ret_pc (Z_to_bv 64 raA)) fc None m1 (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma aft_a1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 ADF_TA_R1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ADF_TA) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold ADF_TA, ADF_TA_R1, P_ERR_new. step. step. apply evt_done. reflexivity. Qed.
  Lemma aft_a2 : forall (line : Z) (sp gp tp s0 s1 s2 s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32),
      arglue ADF_TA_R1 ADF_TA_R2 P_ERR_set_debug (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 line) (Z_to_bv 64 AFUNC_D1) sp gp tp s0 s1 s2 s3 (Z_to_bv 64 line) s5 s6 s7 s8 s9 s10 s11 F fc.
  Proof.
    unfold arglue. intros. unfold ADF_TA_R1 in *. retpc. unfold ADF_TA_R2, P_ERR_set_debug, ARP_FILE, AFUNC_D1.
    do 7 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.
  Lemma aft_a3 : forall (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32),
      arglue ADF_TA_R2 ADF_TZ P_ERR_set_error (Z_to_bv 64 AERR_LIB_SSL) (Z_to_bv 64 AR_ECH_DECODE_ERROR) (Z_to_bv 64 0) sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc.
  Proof.
    unfold arglue. intros. unfold ADF_TA_R2 in *. retpc. unfold ADF_TZ, P_ERR_set_error, AERR_LIB_SSL, AR_ECH_DECODE_ERROR.
    do 5 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma aft_z1 :
    forall (rax s0w gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)   (* [comment removed for export] *)
           (q ee : Z) (w144 w152 w160 w176 w184 w192 w200 w208 w216 w224 w232 : word),
      0 <= q -> q + 432 <= 2^64 ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 (wz ee) w176 w184 w192 w200 w208 w216 w224 w232) -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 ADF_TZ_R1) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 ee) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADF_TZ) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros Q1 Q2 SG2 MI. unfold ADF_TZ, ADF_TZ_R1, P_ossl_echstore_entry_free. unfold arp_sg2, wz in SG2.
    st1. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma aft_z2 :
    forall (s0w gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (q ff lbuf btmp binbuf : Z) (sa : list byte) (sb : byte) (sc : list byte) (sb2 sc2 : byte) (sd se : list byte) (sr : byte) (sg : list byte)
           (w16 w24 w32 w40 w48 w56 w64 w72 w96 w104 w112 w120 w128 w136 w168 w176 w192 w200 w208 w216 w224 w232 : word),
      set_shadow_f8_stmt ->
      0 <= q -> q + 432 <= 2^64 -> AIMG_TOP <= ff -> ff + 4096 <= aceil -> aapp ff 4096 -> aceil <= q ->
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 (wz btmp) (wz binbuf) w96 w104 w112 w120 w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 (wz (Z.shiftr ff 3 + ASHB + 10)) (wz ff) (wz ff) w168 w176 (wz lbuf) w192 w200 w208 w216 w224 w232) ->
      rw_cells asegs m (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sb2 sc2 sd se sr sg) ->
      mem_inv asegs m -> ACONST m ->
      evt asegs (fun ms' => exists m1 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          ms' = MS (mkR (Z_to_bv 64 ADF_TY_R1) (Z_to_bv 64 q) gp tp t0' t1' t2' s0w (Z_to_bv 64 q) (Z_to_bv 64 0xc0000) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 lbuf) (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (Z_to_bv 64 AR_INTERNAL_ERROR) (Z_to_bv 64 520) s6 (Z_to_bv 64 binbuf)
                       (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 ff) (Z_to_bv 64 btmp) t3' t4' t5' t6')
                   F (Z_to_bv 64 P_ERR_new) fc None m1 (seg_rom asegs)
          /\ munch [(Z.shiftr ff 3 + ASHB + 4, Z.shiftr ff 3 + ASHB + 5); (Z.shiftr ff 3 + ASHB + 8, Z.shiftr ff 3 + ASHB + 266)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 (wz btmp) (wz binbuf) w96 w104 w112 w120 w128 w136)
          /\ rw_cells asegs m1 (q + 144) (arp_sg2 (wz (Z.shiftr ff 3 + ASHB + 10)) (wz ff) (wz ff) w168 w176 (wz lbuf) w192 w200 w208 w216 w224 w232)
          /\ rw_cells asegs m1 (Z.shiftr ff 3 + ASHB) (arp_fshadow sa (b8 0xf8) sc (b8 0xf8) sc2 (poison_bytes 256 0xf8) se sr sg)
          /\ ACONST m1)
        (MS (mkR (Z_to_bv 64 ADF_TZ_R1) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADF_TZ_R1)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros SF8 Q1 Q2 FF1 FF2 AAP CQ SG1 SG2 SHC MI AC. unfold ADF_TZ_R1 in *. retpc.
    unfold ADF_TY_R1, P_ERR_new, AR_INTERNAL_ERROR. unfold arp_sg1, arp_sg2, arp_fshadow, ASHB, wz in *.
    acb. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO, ALOWSH_LO in *.
    assert (SHR : Z.shiftr ff 3 = ff / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    pose proof (munch_refl [(Z.shiftr ff 3 + 2147450880 + 4, Z.shiftr ff 3 + 2147450880 + 5); (Z.shiftr ff 3 + 2147450880 + 8, Z.shiftr ff 3 + 2147450880 + 266)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    step. st1. step. step.
    match type of SHC with rw_cells _ ?mx ?ax (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
      change (rw_cells asegs mx ax ([c1; c2; c3; c4; c5] ++ ([c6] ++ rest))) in SHC end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHC. destruct SHC as [SH10 SHR5]. cbn [cells_size csize Nat.add length] in SHR5. change (Z.of_nat 10) with 10 in SHR5.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHR5. destruct SHR5 as [SH256 SHT]. cbn [cells_size csize Nat.add length] in SHT. change (Z.of_nat 256) with 256 in SHT.
    eapply evt_cut.
    { unfold set_shadow_f8_stmt, set_shadow_stmt in SF8. eapply SF8 with (sa := Z.shiftr ff 3 + 2147450880 + 10) (n := 256);
        [first [reflexivity| f_equal; lia]| reflexivity| lia| change (Z.to_nat 256) with 256%nat; exact SH256| assumption| exact AC]. }
    intros ms2 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & SHP).
    retpc. change (Z.to_nat 256) with 256%nat in SHP.
    eapply rw_cells_transport in SG1; [| exact MU2| exact WM2| cbn [cells_size csize Nat.add length disjoint_from fst snd]; lia].
    eapply rw_cells_transport in SG2; [| exact MU2| exact WM2| cbn [cells_size csize Nat.add length disjoint_from fst snd]; lia].
    eapply rw_cells_transport in SH10; [| exact MU2| exact WM2| cbn [cells_size csize Nat.add length disjoint_from fst snd]; lia].
    eapply rw_cells_transport in SHT; [| exact MU2| exact WM2| cbn [cells_size csize Nat.add length disjoint_from fst snd]; lia].
    assert (MU02 : munch [(Z.shiftr ff 3 + 2147450880 + 4, Z.shiftr ff 3 + 2147450880 + 5); (Z.shiftr ff 3 + 2147450880 + 8, Z.shiftr ff 3 + 2147450880 + 266)] m m2).
    { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]]. intros z Hz; cbn in Hz |- *; lia. }
    pose proof (wmono_trans asegs _ _ _ WM WM2) as WM02.
    assert (AC2 : ACONST m2).
    { eapply ACONST_frame; [exact AC| exact MU02| exact WM02|].
      apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
      apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil]. }
    clear MU WM MI MU2 WM2 AC2. rename MI2 into MI. rename MU02 into MU. rename WM02 into WM.
    (* [comment removed for export] *)
    step. step. step. st1. st1. st1. st1. st1. st1. st1. st1. st1. step. step.
    (* [comment removed for export] *)
    rw_join SH10 SHP SHQ. rw_join SHQ SHT SHALL.
    apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside fst snd]; intros z Hz; lia|].
    split; [exact WM|]. split; [exact MI|]. split; [exact SG1|].
    split; [first [exact SG2| let v := eval vm_compute in (2147450880 + 10) in (replace (Z.shiftr ff 3 + 2147450880 + 10) with (Z.shiftr ff 3 + v) in SG2 by lia; exact SG2)]|]. split; [exact SHALL|].
    eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma aft_y1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 ADF_TY_R1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ADF_TY) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold ADF_TY, ADF_TY_R1, P_ERR_new. step. step. apply evt_done. reflexivity. Qed.
  Lemma aft_y2 : forall (line : Z) (sp gp tp s0 s1 s2 s3 s4 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32),
      arglue ADF_TY_R1 ADF_TY_R2 P_ERR_set_debug (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 line) (Z_to_bv 64 AFUNC_DF) sp gp tp s0 s1 s2 s3 s4 (Z_to_bv 64 line) s6 s7 s8 s9 s10 s11 F fc.
  Proof.
    unfold arglue. intros. unfold ADF_TY_R1 in *. retpc. unfold ADF_TY_R2, P_ERR_set_debug, ARP_FILE, AFUNC_DF.
    do 7 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.
  Lemma aft_y3 : forall (reason : Z) (sp gp tp s0 s1 s2 s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32),
      arglue ADF_TY_R2 ADF_TX P_ERR_set_error (Z_to_bv 64 AERR_LIB_SSL) (Z_to_bv 64 reason) (Z_to_bv 64 0) sp gp tp s0 s1 s2 s3 (Z_to_bv 64 reason) s5 s6 s7 s8 s9 s10 s11 F fc.
  Proof.
    unfold arglue. intros. unfold ADF_TY_R2 in *. retpc. unfold ADF_TX, P_ERR_set_error, AERR_LIB_SSL.
    do 5 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma aft_x1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),   (* [comment removed for export] *)
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 ADF_TX_R0) sp gp tp t0 t1 t2 s0 s1 s9 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ADF_TX) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold ADF_TX, ADF_TX_R0, P_ossl_echstore_entry_free. step. step. apply evt_done. reflexivity. Qed.
  Lemma aft_x2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 ADF_TX_R1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADF_TX_R0) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 ADF_TX_R0)) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold ADF_TX_R0 in *. retpc. unfold ADF_TX_R1, P_ERR_new. step. step. apply evt_done. reflexivity. Qed.
  Lemma aft_x3 : arp_glue ADF_TX_R1 ADF_TX_R2 P_ERR_set_debug ARP_FILE 637 ARP_FUNC.
  Proof.
    unfold arp_glue. intros. unfold ADF_TX_R1 in *. retpc. unfold ADF_TX_R2, P_ERR_set_debug, ARP_FILE, ARP_FUNC.
    do 7 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.
  Lemma aft_x4 : arp_glue ADF_TX_R2 ADF_TX_R3 P_ERR_set_error AERR_LIB_SSL AR_INTERNAL_ERROR 0.
  Proof.
    unfold arp_glue. intros. unfold ADF_TX_R2 in *. retpc. unfold ADF_TX_R3, P_ERR_set_error, AERR_LIB_SSL, AR_INTERNAL_ERROR.
    do 6 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.
  Lemma aft_x5 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFM_ERRL_R1) sp gp tp t0 t1 t2 s0 s1 s11 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_BIO_free_all) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ADF_TX_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 ADF_TX_R3)) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold ADF_TX_R3 in *. retpc. unfold AFM_ERRL_R1, P_BIO_free_all. do 5 step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma aerrl2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AERRL_R2) sp gp tp t0 t1 t2 s0 s1 s7 (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 645) a3 a4 a5 a6 a7
                                          s2 s3 (Z_to_bv 64 ARP_FILE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFM_ERRL_R1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 AFM_ERRL_R1)) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold AFM_ERRL_R1 in *. retpc. unfold AERRL_R2, P_CRYPTO_free, ARP_FILE. do 7 step. apply evt_done. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma aerrl3 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AERRL_R3) sp gp tp t0 t1 t2 s0 s1 s2 (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 646) a3 a4 a5 a6 a7
                                          s2 s3 (Z_to_bv 64 ARP_FILE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AERRL_R2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 ARP_FILE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 AERRL_R2)) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold AERRL_R2 in *. retpc. unfold AERRL_R3, P_CRYPTO_free, ARP_FILE. do 5 step. apply evt_done. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma aerrl4 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AERRL_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AEXIT) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AERRL_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 AERRL_R3)) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold AERRL_R3 in *. retpc. unfold AEXIT. step. apply evt_done. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma a595c :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 A595_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AEXIT) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 A595_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 A595_R3)) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold A595_R3 in *. retpc. unfold AEXIT. step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma aexit :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (ff q fp rb : Z) (fj1 fj2 : list byte),
      0 < ff -> ff + 4096 < 2^64 ->
      rw_cells asegs m ff (arp_fframe q fj1 rb fj2 fp) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 AEXIT_R) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ff) (Z_to_bv 64 ARP_FFREQ) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 ff) s9 (Z_to_bv 64 ff) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AFS_FREE_6) fc None m1 (seg_rom asegs)
          /\ munch [(ff, ff + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ff [CB 24 (le8 (wz AFRAME_RETIRED) ++ le8 (wz ARP_DESCR) ++ le8 (wz P_ech_read_priv_echconfiglist)); C8 (wz q);
                                 CB 4056 (fj1 ++ le8 (wz rb) ++ fj2); C8 (wz fp)])
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 ff) s9 (Z_to_bv 64 ff) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AEXIT) fc None m (seg_rom asegs)).
  Proof.
    intros until fj2. intros FF1 FF2 FRM MI. unfold AEXIT, AEXIT_R, AFS_FREE_6, ARP_FFREQ. unfold arp_fframe, wz in FRM.
    pose proof FRM as [[WF _] _]. cbn [cells_wf cell_wf csize length] in WF. destruct WF as (_ & _ & _ & _ & L1 & _ & L2 & _).
    pose proof (munch_refl [(ff, ff + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    zstep. zstep. st1. step. br. zstep. zstep. step. step. step.
    apply evt_done. eexists _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    match goal with X : rw_cells asegs ?mx ff (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: nil) |- _ =>
      apply (rw_cells_merge asegs mx ff [] [c1; c2; c3] [c4; c5; c6; c7; c8]) in X;
      apply (rw_cells_merge asegs mx ff [CB (cells_size [c1; c2; c3]) (cells_bytes [c1; c2; c3]); c4] [c5; c6; c7] [c8]) in X;
      cbn [cells_size csize cells_bytes cbytes app Nat.add length] in X; rewrite ?app_nil_r in X
    end.
    match goal with X : rw_cells asegs _ ff _ |- _ => eapply arw_cells_recut; [exact X| | ] end.
    - cbn [cells_wf cell_wf csize length]. rewrite ?length_app, ?L1, ?L2. cbn [length Nat.add]. repeat split; reflexivity || lia.
    - cbn [cells_bytes cbytes app]. rewrite <- ?app_assoc. cbn [app]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma aepi :
    forall (rax spx gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (esp S11 S10 S9 S8 S7 S6 S5 S4 S3 S2 S1 S0 RA : word),
      464 <= bv_unsigned esp ->
      rw_cells asegs m (bv_unsigned esp + -104) (arp_saves S11 S10 S9 S8 S7 S6 S5 S4 S3 S2 S1 S0 RA) -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR RA esp gp tp t0 t1 t2 S0 S1 s5 a1 a2 a3 a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                                 F (ret_pc RA) fc None m (seg_rom asegs))
        (MS (mkR rax spx gp tp t0 t1 t2 esp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AEXIT_R)) fc None m (seg_rom asegs)).
  Proof.
    intros until RA. intros SPL SV MI. unfold AEXIT_R in *. retpc. pose proof (aword_range esp) as SPR. unfold arp_saves in SV.
    step. step. zstep. do 13 st1. zstep. try (replace (bv_unsigned esp + -448 + 448) with (bv_unsigned esp) by lia; rewrite Z_to_bv_bv_unsigned).
    step. apply evt_done. reflexivity.
  Qed.
End S.
