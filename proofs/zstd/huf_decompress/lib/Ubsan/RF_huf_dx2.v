(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac showpc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC" pc end.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Lemma x2_init_err : forall bs e, init_dstream bs = Err e -> 1 <= e <= 119.
Proof.
  intros bs e H. unfold init_dstream, add_byte, readLE64, highbit32, load in H. cbv zeta in H.
  repeat (first [ discriminate H
                | injection H as <-; split; apply Z.leb_le; reflexivity
                | match type of H with context [if ?c then _ else _] => destruct c end; cbn [bind] in H ]).
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section DX2.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).     (* [comment removed for export] *)
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 4 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 4 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation C61 := 2305843009213693952.
  Notation M64 := 18446744073709551615.

  Definition XTL : list cell := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition XM (mm : fmem) (bd : list cell) : Prop :=
    (exists buf, u8arr usegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at usegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at usegs mm (DT + 4) cbs
    /\ stk usegs mm lo (SP + -112)
    /\ rw_cells usegs mm (SP + -112) (bd ++ XTL)
    /\ mem_inv usegs mm /\ munch DW m0 mm /\ wmono usegs m0 mm.

  Definition BDC (c b p : word) (jp : list byte) : list cell :=
    [C8 c; C4 b; CB 4 jp; C8 p; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 (SS + 8))].

  Lemma xm_forget : forall mm c b p jp, XM mm (BDC c b p jp) -> exists j, XM mm [CB 40 j].
  Proof.
    intros mm c b p jp (ARR & SRC & CBR & ST & FR & MI & MU & WM).
    apply (rw_cells_merge usegs mm _ [] (BDC c b p jp) XTL) in FR.
    eexists. split; [exact ARR|]. split; [exact SRC|]. split; [exact CBR|]. split; [exact ST|].
    split; [exact FR|]. split; [exact MI|]. split; [exact MU|exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_idx_bound : forall c b sh, 0 <= c < 2^64 -> sh = 64 - tl -> 0 <= ((c ≪ b) mod 2^64) ≫ sh < 2^tl.
  Proof using All.
    intros c b sh _ ->. destruct TOK as (TL & _). unfold HUF_TABLELOG_MAX in TL.
    pose proof (Z.mod_pos_bound (c ≪ b) (2^64) ltac:(lia)) as MB.
    rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia.
    replace (64 - tl + tl) with 64 by lia. lia.
  Qed.

  Lemma x2_tl_bound : 1 <= tl <= 12.
  Proof using All. destruct TOK as (TL & _). unfold HUF_TABLELOG_MAX in TL. lia. Qed.

  Lemma x2_pow_tl : 2 <= 2^tl <= 4096.
  Proof using All.
    destruct TOK as (TL & _). unfold HUF_TABLELOG_MAX in TL. split.
    - change 2 with (2^1). apply Z.pow_le_mono_r; lia.
    - change 4096 with (2^12). apply Z.pow_le_mono_r; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac xidx v :=
    rewrite ?(Z.mod_small (tl + 256 * mtl)) by (pose proof x2_tl_bound; lia);
    rewrite ?neg_desc_mod64 by (pose proof x2_tl_bound; lia);
    lazymatch goal with |- context [Z_to_bv 64 ((?x mod ?M) ≫ (64 - tl))] =>
      let EV := fresh "EV" in let VR := fresh "VR" in
      remember ((x mod M) ≫ (64 - tl)) as v eqn:EV;
      assert (VR : 0 <= v < 2^tl) by (subst v; apply x2_idx_bound; [apply bv_unsigned_in_range | reflexivity]);
      clear EV
    end.

  Lemma x2_cells_len : 2^tl <= Z.of_nat (length cells).
  Proof using All. destruct TOK as (_ & TLN & _). unfold FseNCount.Zlength in TLN. lia. Qed.

  Lemma x2_cbs_rd : forall mm, bytes_at usegs mm (DT + 4) cbs ->
    bytes_at usegs mm (DT + 4) (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells)).
  Proof using All. intros mm H. rewrite <- ECB. exact H. Qed.

  Ltac xrd v c EC :=
    repeat match goal with H : ov_read_bytes usegs _ (Z_to_bv 64 (DT + 4 + 4 * v + _)) _ = _ |- _ => clear H end;
    repeat match goal with H : ov_read_bytes usegs _ (Z_to_bv 64 (DT + 4 + 4 * v)) _ = _ |- _ => clear H end;
    lazymatch goal with
    | VR : 0 <= v < 2^tl, SQ : 0 <= x2_seq c < _, CE : bytes_at usegs ?mm (DT + 4) cbs |- _ =>
      let RC0 := fresh "RC" in let RC2 := fresh "RC" in let RC3 := fresh "RC" in let RCB := fresh "RC" in
      pose proof x2_pow_tl; pose proof x2_cells_len;
      destruct (x2_cell_rd usegs mm (DT + 4) cells (Z.to_nat (4 * 2^tl)) v c (x2_cbs_rd mm CE)
                  ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) EC SQ)
        as (RC0 & RC2 & RC3 & RCB)
    end.

  (* [comment removed for export] *)
  Ltac xcell v c EC :=
    lazymatch goal with
    | VR : 0 <= v < 2^tl |- _ =>
      remember (nth (Z.to_nat v) cells x2_default) as c eqn:EC;
      let SQ := fresh "SQ" in let NB := fresh "NB" in let LN := fresh "LN" in
      destruct (proj2 (proj2 TOK) v VR) as (SQ & NB & LN); rewrite <- EC in SQ, NB, LN;
      xrd v c EC
    end.

  Ltac xgen :=
    lazymatch goal with ARR : u8arr usegs ?m DST (map (Z_to_bv 8) (Zupd ?i ?x ?b0)) |- _ =>
      let LB' := fresh "LB" in
      assert (LB' : zlen (Zupd i x b0) = dcap) by (rewrite Zupd_length; lia);
      let nb := fresh "buf" in let ENB := fresh "ENB" in
      remember (Zupd i x b0) as nb eqn:ENB; clear ENB
    end.

  Ltac xst k := lazymatch goal with ARR : u8arr usegs _ DST _ |- _ => u8_sok ARR k; zstep; u8_store_same ARR k; xgen end.

  Ltac xm_close :=
    unfold XM, BDC, XTL; cbn [app];
    lazymatch goal with ARR : u8arr usegs ?m DST (map (Z_to_bv 8) ?bf), LB : zlen ?bf = dcap |- _ =>
      split; [exists bf; split; [exact ARR | exact LB] |] end;
    repeat (split; [eassumption|]); eassumption.

  Lemma x2_nullchk : forall p q, 0 < p -> 0 <= q -> p <> q ->
    Z.lxor (Z.b2z (0 <? p)) (Z.b2z (Z.lxor p q <? 1)) <> 0.
  Proof using All.
    intros p q P Q N. replace (0 <? p) with true by (symmetry; apply Z.ltb_lt; lia).
    assert (NZ : Z.lxor p q <> 0) by (intro H; apply N; apply Z.lxor_eq; exact H).
    assert (NN : 0 <= Z.lxor p q) by (apply Z.lxor_nonneg; split; intros; lia).
    replace (Z.lxor p q <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    intro H. vm_compute in H. discriminate H.
  Qed.

  Lemma x2_zext32 : forall x, 0 <= x < 4294967296 -> (x * 4294967296) mod 18446744073709551616 / 4294967296 = x.
  Proof using All. intros x Hx. rewrite Z.mod_small by lia. apply Z.div_mul. lia. Qed.

  Ltac xpow_in U :=
    try change (2^2) with 4 in U; try change (2^3) with 8 in U; try change (2^32) with 4294967296 in U;
    try change (2^62) with 4611686018427387904 in U.
  Ltac xpow :=
    try change (2^2) with 4; try change (2^3) with 8; try change (2^32) with 4294967296;
    try change (2^62) with 4611686018427387904.

  Ltac xsim_in U :=
    rewrite ?bv_wrap_small in U by (change (bv_modulus 32) with 4294967296; lia);
    rewrite ?Z.shiftl_mul_pow2 in U by lia; rewrite ?Z.shiftr_div_pow2 in U by lia; xpow_in U;
    rewrite ?swrap32_small in U by lia;
    rewrite ?unsigned_lit in U by lia; rewrite ?Z.mod_small in U by lia.
  Ltac xsim :=
    rewrite ?bv_wrap_small by (change (bv_modulus 32) with 4294967296; lia);
    rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?Z.shiftr_div_pow2 by lia; xpow;
    rewrite ?swrap32_small by lia;
    rewrite ?(Z.mod_small (_ / 8)) by lia; rewrite ?(Z.mod_small (_ - _)) by lia;
    rewrite ?x2_zext32 by lia.

  Ltac xchk U :=
    exfalso; pose proof x2_tl_bound; pose proof x2_pow_tl;
    pose proof (bv_unsigned_in_range 64 sp) as RSP'; unfold bv_modulus in RSP'; cbn in RSP';
    try (pose proof (DP ltac:(lia)));
    rewrite ?zb_lxor_ones in U by lia;
    xsim_in U;
    rewrite ?(Z.mod_small (_ * 4)) in U by lia; rewrite ?(Z.mod_small (4 * _)) in U by lia;
    rewrite ?Z.div_small in U by lia;
    first [ lia | eapply x2_nullchk; [ | | | exact U ]; lia ].

  Lemma x2_land_not_b2z : forall b, Z.land (Z.lxor (Z.b2z b) M64) 1 = Z.b2z (negb b).
  Proof using All. intros []; reflexivity. Qed.
  Lemma x2_b2z_nz : forall b, Z.b2z b <> 0 -> b = true.
  Proof using All. intros [] H; [reflexivity | cbn in H; lia]. Qed.
  Lemma x2_b2z_z : forall b, Z.b2z b = 0 -> b = false.
  Proof using All. intros [] H; [cbn in H; lia | reflexivity]. Qed.
  Lemma x2_land_b2z : forall b, Z.land (Z.b2z b) 1 = Z.b2z b.
  Proof using All. intros []; reflexivity. Qed.

  Ltac xz U := zify_cond U; rewrite ?byte_lit in U by lia; rewrite ?unsigned_lit in U by lia;
    rewrite ?Z.mod_small in U by lia;
    rewrite ?x2_land_not_b2z, ?x2_land_b2z, ?Z.land_0_r, ?Z.land_0_l in U;
    try (apply x2_b2z_nz in U; zify_bool U); try (apply x2_b2z_z in U; zify_bool U).

  Ltac xdrive pc := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x154b0) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let U := fresh "U" in if_cases U; xz U; try (xchk U)
    | _ => zstep end).

  Ltac xdrive2 pc1 pc2 := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 pc1) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 pc2) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x154b0) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let U := fresh "U" in if_cases U; xz U; try (xchk U)
    | _ => zstep end).

  Ltac xsrc :=
    lazymatch goal with SRC : bytes_at usegs ?m SS (map (Z_to_bv 8) src) |- _ =>
      let a := OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.STRW_tac.cur_mem_addr in
      lazymatch a with Z_to_bv 64 ?e =>
        let RS := fresh "RS" in
        pose proof (src_rd usegs m SS src (e - SS) SRC ltac:(lia)) as RS;
        replace (SS + (e - SS)) with e in RS by ring
      end
    end.

  Ltac xsrc8 :=
    lazymatch goal with SRC : bytes_at usegs ?m SS (map (Z_to_bv 8) src) |- _ =>
      let a := OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.STRW_tac.cur_mem_addr in
      lazymatch a with Z_to_bv 64 ?e =>
        let RS := fresh "RS" in
        pose proof (bytes_at_read usegs m SS (map (Z_to_bv 8) src) (e - SS) 8 SRC ltac:(lia)
                      ltac:(rewrite length_map; lia)) as RS;
        replace (SS + (e - SS)) with e in RS by ring
      end
    end.

  Ltac xdriveS pc := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x154b0) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let U := fresh "U" in if_cases U; xz U; try (xsim_in U); try (xchk U)
    | _ => first [zstep | xsim; xsrc; zstep | xsim; xsrc8; zstep] end).

  (* [comment removed for export] *)
  Lemma x2_ret : forall mm j (ra' t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
    XM mm [CB 40 j] ->
    evt usegs POST (MS (mkR ra' (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15484) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros (ARR & SRC & CBR & ST & FR & MI & MU & WM).
    unfold XTL in FR. cbn [app] in FR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    do 10 zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_end : forall mm c b p jp (ra' t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
    XM mm (BDC c b p jp) ->
    evt usegs POST (MS (mkR ra' (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15460) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros XMM.
    pose proof XMM as (ARR & SRC & CBR & ST & FR & MI & MU & WM).
    unfold BDC, XTL in FR. cbn [app] in FR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (xm_forget _ _ _ _ _ XMM) as (j & XMJ).
    do 7 zstep. if_cases K.
    - zstep. eapply x2_ret; exact XMJ.
    - zstep. zstep. eapply x2_ret; exact XMJ.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_last : forall k mm c b p jp (ra' t0 t1 t2 x8 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
    XM mm (BDC c b p jp) -> 0 <= k <= dcap ->
    evt usegs POST (MS (mkR ra' (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 x8 (Z_to_bv 64 (DST + k)) (Z_to_bv 64 (DT + 4))
                           (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 C61) (Z_to_bv 64 (tl + 256 * mtl)) a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x153d8) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros XMM KR.
    pose proof XMM as ((buf & ARR & LB) & SRC & CBR & ST & FR & MI & MU & WM).
    unfold BDC, XTL in FR. cbn [app] in FR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof TOK as (TL & TLEN & TCK).
    zstep. if_cases K; zify_cond K.
    - eapply x2_end; exact XMM.
    - do 4 zstep.
      xidx v.
      zstep. zstep. zstep. if_cases U1; zify_cond U1; [xchk U1|].
      zstep. zstep. zstep. if_cases U2; zify_cond U2; [xchk U2|].
      xcell v cc EC.
      rewrite ?(Z.shiftl_mul_pow2 v 2) by lia; try change (2^2) with 4; rewrite ?(Z.mul_comm v 4).
      zstep. zstep.
      xst k.
      xrd v cc EC.
      xdrive 0x15460.
      all: eapply x2_end; xm_close.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_loop2r : forall (fuel : nat) k mm c b p jp (ra' t0 t1 t2 x8 a4 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
    XM mm (BDC c b p jp) -> 0 <= k -> k + 2 <= dcap -> dcap - k < Z.of_nat fuel ->
    evt usegs POST (MS (mkR ra' (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 x8 (Z_to_bv 64 (DST + k)) (Z_to_bv 64 (DT + 4))
                           (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 C61) (Z_to_bv 64 (tl + 256 * mtl)) a4
                           (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 (Z.lxor (DT + 4) M64)) (Z_to_bv 64 (64 - tl))
                           x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15380) fc None mm (seg_rom usegs)).
  Proof using All.
    induction fuel as [|fuel IH]; intros until t6; intros XMM K0 K2 KF; [lia|].
    pose proof XMM as ((buf & ARR & LB) & SRC & CBR & ST & FR & MI & MU & WM).
    unfold BDC, XTL in FR. cbn [app] in FR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof x2_tl_bound.
    do 3 zstep. rewrite ?(Z.mod_small (64 - tl)) by lia. xidx v.
    zstep. zstep. if_cases U1; zify_cond U1; [xchk U1|].
    zstep. zstep. zstep. if_cases U2; zify_cond U2; [xchk U2|].
    xcell v cc EC.
    rewrite ?(Z.shiftl_mul_pow2 v 2) by lia; try change (2^2) with 4; rewrite ?(Z.mul_comm v 4).
    zstep. zstep. zstep. unfold sx16.
    xst k. xst (k + 1).
    xrd v cc EC.
    xdrive2 0x15380 0x153d8.
    all: rewrite ?byte_lit by lia; replace (DST + k + x2_len cc) with (DST + (k + x2_len cc)) by ring.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x15380) _ _ _ _) => eapply IH; [xm_close | lia | lia | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x153d8) _ _ _ _) => eapply x2_last; [xm_close | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_l2r_entry : forall k mm c b p jp (ra' t0 t1 t2 x8 a4 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
    XM mm (BDC c b p jp) -> 0 <= k <= dcap -> 2 <= dcap ->
    evt usegs POST (MS (mkR ra' (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 x8 (Z_to_bv 64 (DST + k)) (Z_to_bv 64 (DT + 4))
                           (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 C61) (Z_to_bv 64 (tl + 256 * mtl)) a4
                           (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 (Z.lxor (DT + 4) M64)) (Z_to_bv 64 (64 - tl))
                           x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1537c) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros XMM KR D2.
    pose proof (DP ltac:(lia)).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    zstep. if_cases K; xz K.
    - eapply x2_last; [exact XMM | lia].
    - eapply (x2_loop2r (Z.to_nat (dcap - k + 1))); [exact XMM | lia | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_l2x : forall k mm c b p jp (ra' t0 t1 x8 a4 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
    XM mm (BDC c b p jp) -> 0 <= k <= dcap -> 2 <= dcap ->
    evt usegs POST (MS (mkR ra' (Z_to_bv 64 (SP + -112)) gp tp t0 t1 (Z_to_bv 64 3) x8 (Z_to_bv 64 (DST + k)) (Z_to_bv 64 (DT + 4))
                           (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 C61) (Z_to_bv 64 (tl + 256 * mtl)) a4
                           (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 (Z.lxor (DT + 4) M64)) (Z_to_bv 64 (64 - tl))
                           x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1536c) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros XMM KR D2.
    pose proof XMM as ((buf & ARR & LB) & SRC & CBR & ST & FR & MI & MU & WM).
    unfold BDC, XTL in FR. cbn [app] in FR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (DP ltac:(lia)).
    xdrive 0x1537c.
    eapply x2_l2r_entry; [xm_close | lia | lia].
  Qed.

  Lemma x2_land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
  Proof using All. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

  Lemma x2_st01 : forall c : bool, Z.lxor (Z.b2z c) 1 = 0 \/ Z.lxor (Z.b2z c) 1 = 1.
  Proof using All. intros []; [left | right]; reflexivity. Qed.

  Ltac xbwr := lazymatch goal with BW : bv_swrap 32 (bv_unsigned ?b) = ?x |- context [sx32 ?b] =>
    replace (sx32 b) with (Z_to_bv 64 x) by (unfold sx32; rewrite BW; reflexivity) end.

  Ltac xatstop pcs := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
    let t := eval vm_compute in (existsb (Z.eqb p) (0x154b0 :: pcs)) in lazymatch t with true => idtac end end.

  Ltac xidxA :=
    lazymatch goal with |- context [Z_to_bv 64 (Z.shiftr (Z.modulo (Z.shiftl _ _) _) _)] => idtac end;
    rewrite ?(Z.mod_small (64 - tl)) by (pose proof x2_tl_bound; lia);
    let v := fresh "v" in xidx v.

  Ltac xcellA :=
    rewrite ?(Z.shiftl_mul_pow2 _ 2) by lia; xpow;
    lazymatch goal with VR : 0 <= ?v < 2^tl |- _ =>
      rewrite ?(Z.mul_comm v 4);
      first [ lazymatch goal with EC : ?c = nth (Z.to_nat v) cells x2_default |- _ => xrd v c EC end
            | let c := fresh "cc" in let EC := fresh "EC" in xcell v c EC ]
    end.

  Ltac xstA :=
    let a := OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.STRW_tac.cur_mem_addr in
    lazymatch a with Z_to_bv 64 ?e => xst (e - DST) end.

  Ltac xone :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let U := fresh "U" in if_cases U; xz U; try (xsim_in U); try (xchk U)
    | _ => first [ zstep | xsim; xsrc; zstep | xsim; xsrc8; zstep | xcellA; zstep | xstA
                 | rewrite ?byte_lit by lia; xstA ]; try unfold sx16; try xbwr; try xidxA
    end.

  Ltac xwalkn n pcs := lazymatch n with
    | O => idtac "BUDGET"
    | S ?m => tryif xatstop pcs then idtac else first [ xone; xwalkn m pcs | idtac ]
    end.

  Ltac xbw :=
    rewrite ?x2_land7 by lia;
    rewrite ?unsigned_lit_wrap, ?swrap32_eq; unfold bv_wrap; try change (bv_modulus 32) with (2^32);
    rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia; xpow;
    rewrite ?unsigned_lit_wrap, ?swrap32_eq; lia.

  Ltac xside :=
    first [ assumption | apply x2_st01 | lia
          | rewrite ?byte_lit by lia; rewrite ?unsigned_lit by lia; rewrite ?swrap32_small by lia; lia
          | xsim; rewrite ?Z.mod_small by lia; rewrite ?x2_land7 by lia; lia
          | xbw ].

  Ltac xjoin :=
    lazymatch goal with FR : rw_cells usegs ?m (SP + -112) (C8 ?w0 :: C4 ?w1 :: CB 4 ?j :: C8 (Z_to_bv 64 ?e) :: ?rest) |- _ =>
      let cw := fresh "cw" in
      set (cw := w0) in FR; clearbody cw;
      replace e with (SS + (e - SS)) in FR by ring
    end.

  Ltac xpc := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
    let o := eval vm_compute in (p - 0x14900) in idtac "PCO" o end.

  Definition L2H (fuel : nat) : Prop :=
    forall k pt bits mm c b jp (ra' t1 x8 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
    XM mm (BDC c b (Z_to_bv 64 (SS + pt)) jp) -> 0 <= pt -> (pt = 0 \/ pt + 8 <= n) -> 0 <= bits <= 64 ->
    bv_swrap 32 (bv_unsigned b) = bits -> 0 <= k <= dcap -> 2 <= dcap -> dcap - k < Z.of_nat fuel ->
    evt usegs POST (MS (mkR ra' (Z_to_bv 64 (SP + -112)) gp tp (Z_to_bv 64 65) t1 (Z_to_bv 64 3) x8 (Z_to_bv 64 (DST + k))
                           (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 C61) (Z_to_bv 64 (tl + 256 * mtl))
                           (Z_to_bv 64 bits) (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 (Z.lxor (DT + 4) M64)) (Z_to_bv 64 (64 - tl))
                           x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15184) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Lemma x2_l2j : forall fuel, L2H fuel ->
    forall k pt bits st mm c b jp (ra' t1 x8 x18 x19 x20 x21 x22 x23 t4 t5 t6 : word),
    XM mm (BDC c b (Z_to_bv 64 (SS + pt)) jp) -> 0 <= pt -> (pt = 0 \/ pt + 8 <= n) -> 0 <= bits <= 64 ->
    bv_swrap 32 (bv_unsigned b) = bits -> (st = 0 \/ st = 1) -> 0 <= k <= dcap -> 2 <= dcap -> dcap - k <= Z.of_nat fuel ->
    evt usegs POST (MS (mkR ra' (Z_to_bv 64 (SP + -112)) gp tp (Z_to_bv 64 65) t1 (Z_to_bv 64 3) x8 (Z_to_bv 64 (DST + k))
                           (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 C61) (Z_to_bv 64 (tl + 256 * mtl))
                           (Z_to_bv 64 bits) (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 (Z.lxor (DT + 4) M64)) (Z_to_bv 64 (64 - tl))
                           x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 (Z_to_bv 64 st) t4 t5 t6) F (Z_to_bv 64 0x15300) fc None mm (seg_rom usegs)).
  Proof using All.
    intros fuel HL k pt bits st mm c b jp ra' t1 x8 x18 x19 x20 x21 x22 x23 t4 t5 t6 XMM P0 PV BB BW STS K0 D2 KF.
    pose proof XMM as ((buf & ARR & LB) & SRC & CBR & ST & FR & MI & MU & WM).
    unfold BDC, XTL in FR. cbn [app] in FR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (DP ltac:(lia)). pose proof x2_tl_bound.
    unfold L2H in HL. destruct STS as [-> | ->].
    all: xwalkn 200%nat [0x15184; 0x1536c; 0x1537c].
    all: rewrite ?byte_lit by lia;
         try (lazymatch goal with |- context [Z_to_bv 64 (DST + ?k0 + ?l)] =>
                replace (DST + k0 + l) with (DST + (k0 + l)) by ring end).
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x15184) _ _ _ _) => eapply HL; [xm_close | xside ..]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1537c) _ _ _ _) => eapply x2_l2r_entry; [xm_close | lia | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1536c) _ _ _ _) => eapply x2_l2x; [xm_close | lia | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_loop2 : forall (fuel : nat) k pt bits mm c b jp (ra' t1 x8 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
    XM mm (BDC c b (Z_to_bv 64 (SS + pt)) jp) -> 0 <= pt -> (pt = 0 \/ pt + 8 <= n) -> 0 <= bits <= 64 ->
    bv_swrap 32 (bv_unsigned b) = bits -> 0 <= k <= dcap -> 2 <= dcap -> dcap - k < Z.of_nat fuel ->
    evt usegs POST (MS (mkR ra' (Z_to_bv 64 (SP + -112)) gp tp (Z_to_bv 64 65) t1 (Z_to_bv 64 3) x8 (Z_to_bv 64 (DST + k))
                           (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 C61) (Z_to_bv 64 (tl + 256 * mtl))
                           (Z_to_bv 64 bits) (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 (Z.lxor (DT + 4) M64)) (Z_to_bv 64 (64 - tl))
                           x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15184) fc None mm (seg_rom usegs)).
  Proof using All.
    induction fuel as [|fuel IH]; intros until t6; intros XMM P0 PV BB BW K0 D2 KF; [lia|].
    pose proof XMM as ((buf & ARR & LB) & SRC & CBR & ST & FR & MI & MU & WM).
    unfold BDC, XTL in FR. cbn [app] in FR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (DP ltac:(lia)). pose proof x2_tl_bound.
    xdriveS 0x15300.
    all: xjoin; eapply (x2_l2j fuel IH); [xm_close | xside ..].
  Qed.

  Lemma x2_land63 : forall x, 0 <= x -> Z.land x 63 = x mod 64.
  Proof using All. intros x Hx. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.

  Ltac xregs :=
    try (replace (DST + dcap + -2) with (DST + dcap - 2) by ring);
    rewrite ?x2_land63 by lia; rewrite ?neg_desc_mod64 by (pose proof x2_tl_bound; lia).

  (* [comment removed for export] *)
  Lemma x2_mid : forall k bits mm c b p jp (ra' t0 t1 t2 x8 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
    XM mm (BDC c b p jp) -> 0 <= bits < 2^31 ->
    (bits < 65 -> bv_swrap 32 (bv_unsigned b) = bits /\
                  exists pt, p = Z_to_bv 64 (SS + pt) /\ 0 <= pt /\ (pt = 0 \/ pt + 8 <= n)) ->
    0 <= k <= dcap ->
    evt usegs POST (MS (mkR ra' (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 x8 (Z_to_bv 64 (DST + k)) (Z_to_bv 64 (DT + 4))
                           (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 C61) (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 bits) a5 a6 a7
                           x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15150) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros XMM BB HB K0.
    pose proof XMM as ((buf & ARR & LB) & SRC & CBR & ST & FR & MI & MU & WM).
    unfold BDC, XTL in FR. cbn [app] in FR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof x2_tl_bound.
    xwalkn 60%nat [0x15184; 0x153d8; 0x1536c; 0x1537c].
    all: xregs.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x153d8) _ _ _ _) => eapply x2_last; [exact XMM | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1536c) _ _ _ _) => eapply x2_l2x; [exact XMM | lia | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x15184) _ _ _ _) =>
             destruct (HB ltac:(lia)) as (BW & pt & EP & P0 & PV); subst p;
             eapply (x2_loop2 (Z.to_nat (dcap - k + 1))); [exact XMM | xside .. | rewrite Z2Nat.id by lia; lia]
         end.
  Qed.

End DX2.
End CANSEC1.
