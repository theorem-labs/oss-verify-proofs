(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_fargs RF_huf_y4s_iface RF_huf_y4fin.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac y4wsrd A i :=
  lazymatch goal with W : u64arr usegs ?mm A ?ws |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u64arr_read usegs mm A ws i _ _ W eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) end.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).
Ltac xo o := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
      let d := eval vm_compute in ((z =? PHUF_DX2_4X + o) || (z =? PHUF_DX2_4X + 4868) || (z =? PY4_BODY)) in
      lazymatch d with true => fail | false => zstep end
  | _ => zstep end).
Ltac ckfin U := exfalso; first [ discriminate U | congruence |
  repeat (first [ rewrite signed_lit in U by lia | rewrite unsigned_lit in U by lia ]); lia ].
Ltac autobr := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let U := fresh "CK" in
  first [ if_cases U; zify_cond U; [ ckfin U | ] | if_cases U; zify_cond U; [ | ckfin U ] ] end.
Ltac b2zsplit := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  match c with context [Z.b2z (?a <? ?b)] => destruct (Z.ltb_spec a b); simpl Z.b2z; simpl Z.lxor end end.
Ltac aw o := xo o; repeat (first [ autobr | b2zsplit; try (exfalso; lia) ]; xo o).
Ltac fixret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?z)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z)
    by (symmetry; apply ret_pc_even; unfold PHUF_DX2_4X; [lia | vm_compute; reflexivity]) end.

Ltac andsplit := repeat match goal with |- _ /\ _ => split end.
Ltac y4m_close :=
  andsplit;
  lazymatch goal with
  | |- u64arr _ ?m ?A _ => apply y4_u64arr_of_C8; match goal with H : rw_cells _ m A _ |- _ => exact H end
  | |- exists jo, rw_cells _ ?m ?A [CB 32 jo] =>
      match goal with H : rw_cells _ m A _ |- _ => destruct (rw_cells_forget _ _ _ _ H) as (jo & HJ); exists jo; exact HJ end
  | |- length _ = _ => reflexivity
  | |- _ => assumption
  end.

Section CANSEC1. Context {rc : runConstT}.
Section Y4E.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis DTA : DT mod 4 = 0.
  Hypothesis CBL : DT + 4 + 4 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 4 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation Y4M := (RF_huf_y4s_iface.Y4M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs).
  Notation SPS4 := (RF_huf_y4s_iface.SPS4 DST dcap SS DT src).
  Notation SPSL w0 w8 := (SPS4 w0 w8 14757395258967641293 2635249153387078803 (DST + dcap) SS (DST + 3 * ((dcap + 3) / 4)) (DST + 2 * ((dcap + 3) / 4)) (DST + ((dcap + 3) / 4))).
  Notation W4 a b c d := [Z_to_bv 64 a; Z_to_bv 64 b; Z_to_bv 64 c; Z_to_bv 64 d].
  Notation HO mm b0 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31 :=
    (MS (mkR (Z_to_bv 64 (-25)) (Z_to_bv 64 (SP + -512)) gp tp x5 (Z_to_bv 64 OP3) x7 x8 (Z_to_bv 64 IP2) x10
             (Z_to_bv 64 IP3) x12 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 IP0) (Z_to_bv 64 OP1) (Z_to_bv 64 OP2)
             (Z_to_bv 64 (SP + -168)) (Z_to_bv 64 OP0) (Z_to_bv 64 IP1) x20 x21 b0 (Z_to_bv 64 (SP + -136)) x24
             (Z_to_bv 64 (-16)) x26 x27 x28 x29 (Z_to_bv 64 (- (DT + 4) - 1)) x31)
        F (Z_to_bv 64 0x15cbc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Hypothesis SLOW : y4_slow_goal ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs.

  Hypothesis OUTER : tl = 11 -> 0 < dcap -> 3 * ((dcap + 3) / 4) < dcap ->
    forall (fuel : nat) mm ws (w0 w8 : Z) (b0 b1 b2 b3 : word) IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3
           IE0 IE1 IE2 IE3 (x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31 : word),
    Y4M mm (SPSL w0 w8) ws (W4 OP0 OP1 OP2 OP3) (W4 IP0 IP1 IP2 IP3) [b0; b1; b2; b3] ->
    nth_error ws 13 = Some (Z_to_bv 64 SS) ->
    nth_error ws 15 = Some (Z_to_bv 64 IE0) -> nth_error ws 16 = Some (Z_to_bv 64 IE1) ->
    nth_error ws 17 = Some (Z_to_bv 64 IE2) -> nth_error ws 18 = Some (Z_to_bv 64 IE3) ->
    SS <= IE0 <= SS + n -> SS <= IE1 <= SS + n -> SS <= IE2 <= SS + n -> SS <= IE3 <= SS + n ->
    DST + dcap - OP3 < 5 * Z.of_nat fuel ->
    SS <= IP0 -> IP0 + 8 <= SS + n -> SS <= IP1 -> IP1 + 8 <= SS + n ->
    SS <= IP2 -> IP2 + 8 <= SS + n -> SS <= IP3 -> IP3 + 8 <= SS + n ->
    DST <= OP0 <= DST + ((dcap + 3) / 4) -> DST <= OP1 <= DST + 2 * ((dcap + 3) / 4) -> DST <= OP2 <= DST + 3 * ((dcap + 3) / 4) -> DST <= OP3 <= DST + dcap ->
    bv_unsigned b0 mod 512 <> 0 -> bv_unsigned b1 mod 512 <> 0 -> bv_unsigned b2 mod 512 <> 0 -> bv_unsigned b3 mod 512 <> 0 ->
    evt usegs POST (HO mm b0 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31).

  (* [comment removed for export] *)
  Lemma y4e_epi : forall mm (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    stk usegs mm lo (SP + -104) -> rw_cells usegs mm (SP + -104) FRS ->
    mem_inv usegs mm -> munch DW m0 mm -> wmono usegs m0 mm ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x16d70) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until xra. intros ST FR MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    do 14 zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma y4_m7_rd : forall m1, mem_inv usegs m1 ->
    ov_read_bytes usegs m1 (Z_to_bv 64 0x10470) 8 = Some (le8 (Z_to_bv 64 2635249153387078803)).
  Proof using All.
    intros m1 MI.
    assert (RC : ro_cells usegs m1 0x10470 [CB (length (le8 (Z_to_bv 64 2635249153387078803))) (le8 (Z_to_bv 64 2635249153387078803))])
      by (apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | cbn; lia]).
    exact (ro_cells_read_at usegs m1 _ _ 0 _ 8 _ RC eq_refl eq_refl eq_refl).
  Qed.

  (* [comment removed for export] *)
  Definition FAW (b0 b1 b2 b3 : Z) : list word :=
    let l1 := jt_len src 0 in let l2 := jt_len src 2 in let l3 := jt_len src 4 in
    let seg := (dcap + 3) / 4 in
    [ Z_to_bv 64 (SS + 6 + l1 - 8); Z_to_bv 64 (SS + 6 + l1 + l2 - 8); Z_to_bv 64 (SS + 6 + l1 + l2 + l3 - 8);
      Z_to_bv 64 (SS + n - 8);
      Z_to_bv 64 DST; Z_to_bv 64 (DST + seg); Z_to_bv 64 (DST + 2 * seg); Z_to_bv 64 (DST + 3 * seg);
      Z_to_bv 64 b0; Z_to_bv 64 b1; Z_to_bv 64 b2; Z_to_bv 64 b3;
      Z_to_bv 64 (DT + 4); Z_to_bv 64 SS; Z_to_bv 64 (DST + dcap);
      Z_to_bv 64 (SS + 6); Z_to_bv 64 (SS + 6 + l1); Z_to_bv 64 (SS + 6 + l1 + l2); Z_to_bv 64 (SS + 6 + l1 + l2 + l3) ].

  (* [comment removed for export] *)
  Lemma y4_stk4 : forall mm cs cw ce co ci cb, stk usegs mm lo (SP + -512) ->
    rw_cells usegs mm (SP + -512) cs -> cells_size cs = 128%nat ->
    rw_cells usegs mm (SP + -384) cw -> cells_size cw = 152%nat ->
    rw_cells usegs mm (SP + -232) ce -> cells_size ce = 32%nat ->
    rw_cells usegs mm (SP + -200) co -> cells_size co = 32%nat ->
    rw_cells usegs mm (SP + -168) ci -> cells_size ci = 32%nat ->
    rw_cells usegs mm (SP + -136) cb -> cells_size cb = 32%nat ->
    stk usegs mm lo (SP + -104).
  Proof using All.
    intros mm cs cw ce co ci cb ST C LC W LW E LE O LO I LI B LB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    eapply stk_release in C; [ | exact ST | lia ]. rewrite LC in C.
    eapply stk_release in W; [ | replace (SP + -384) with (SP + -512 + Z.of_nat 128) by lia; exact C | lia ]. rewrite LW in W.
    eapply stk_release in E; [ | replace (SP + -232) with (SP + -384 + Z.of_nat 152) by lia; exact W | lia ]. rewrite LE in E.
    eapply stk_release in O; [ | replace (SP + -200) with (SP + -232 + Z.of_nat 32) by lia; exact E | lia ]. rewrite LO in O.
    eapply stk_release in I; [ | replace (SP + -168) with (SP + -200 + Z.of_nat 32) by lia; exact O | lia ]. rewrite LI in I.
    eapply stk_release in B; [ | replace (SP + -136) with (SP + -168 + Z.of_nat 32) by lia; exact I | lia ]. rewrite LB in B.
    replace (SP + -104) with (SP + -136 + Z.of_nat 32) by lia. exact B.
  Qed.

  (* [comment removed for export] *)
  Lemma y4_entry : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (flags : Z) (buf : list Z),
    u8arr usegs m0 DST (map (Z_to_bv 8) buf) -> zlen buf = dcap ->
    bytes_at usegs m0 SS (map (Z_to_bv 8) src) -> bytes_at usegs m0 (DT + 4) cbs ->
    bytes_at usegs m0 DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl] ->
    stk usegs m0 lo SP -> mem_inv usegs m0 -> 0 <= flags < 64 ->
    evt usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SS) (Z_to_bv 64 n)
                           (Z_to_bv 64 DT) (Z_to_bv 64 flags) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 PHUF_DX2_4X) fc None m0 (seg_rom usegs)).
  Proof using All.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 flags buf OUT LB SRCB CBSB DTB ST MI FL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl DW m0) as MU. pose proof (wmono_refl usegs m0) as WM.
    carve_frame 104%nat ST. rename FR into FRa.
    xo 72.
    if_cases K; zify_cond K.
    - carve_frame 32%nat ST. rename FR into FRb.
      carve_frame 32%nat ST. rename FR into FRi.
      carve_frame 32%nat ST. rename FR into FRo.
      carve_frame 32%nat ST. rename FR into FRe.
      carve_frame 152%nat ST. rename FR into FRw.
      carve_frame 128%nat ST. rename FR into FRs.
      pose proof TOK as (TL & _). unfold HUF_TABLELOG_MAX in TL.
      assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity).
      assert (P0 : 0 < 2^tl) by (apply Z.pow_pos_nonneg; lia).
      aw 204.
      if_cases K2; zify_cond K2.
      all: aw 204.
      all: zstep.
      all: assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -512)) = SP + -512) by (apply unsigned_lit; lia).
      all: call (fast_args_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -384) DST dcap SS DT mtl 1 tl mtl src _ lo).
      all: rewrite ?ESP.
      all: try first [eassumption | exact BYS | lia | reflexivity | (f_equal; lia) | (intros HD; pose proof (DP HD); lia)].
      all: fixret; rewrite ?ESP in *.
      all: lazymatch goal with H : _ = 0 \/ _ |- _ => destruct H as [-> | [-> | (-> & FOK)]] end.
      all: try (exfalso; lia).
      all: try (destruct FOK as (TL11 & N10 & JL0 & JL1 & JL2 & JLS & DCP & SG & b0 & b1 & b2 & b3 &
                                 B0 & B1 & B2 & B3 & M0 & M1 & M2 & M3 & FW); try (exfalso; lia)).
      all: lazymatch goal with H : exists ja, rw_cells _ _ (SP + -384) [CB 152 ja] |- _ => destruct H as (ja' & FWj) end.
      all: try (unfold fast_args_cells in FW; cbv zeta in FW; clear FWj).
      all: aw 592.
      all: try (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
             lazymatch goal with
             | STq : stk _ mm lo (SP + -512), Cs : rw_cells _ mm (SP + -512) _, Cw : rw_cells _ mm (SP + -384) [CB 152 _],
               Ce : rw_cells _ mm (SP + -232) _, Co : rw_cells _ mm (SP + -200) _, Ci : rw_cells _ mm (SP + -168) _,
               Cb : rw_cells _ mm (SP + -136) _ |- _ =>
                 pose proof (y4_stk4 mm _ _ _ _ _ _ STq Cs eq_refl Cw eq_refl Ce eq_refl Co eq_refl Ci eq_refl Cb eq_refl) as STK
             end end).
      all: try (eapply y4e_epi; eassumption).
      all: try (eapply SLOW; unfold Y4S; split; [exists buf; split; assumption |]; andsplit; assumption).
      all: try (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => match goal with H : mem_inv _ mm |- _ => pose proof (y4_m7_rd mm H) as M7R end end; aw 592).
      all: lazymatch goal with |- context [Z_to_bv 64 (Z.lxor (DT + 4) ?c)] =>
             replace (Z_to_bv 64 (Z.lxor (DT + 4) c)) with (Z_to_bv 64 (- (DT + 4) - 1))
               by (rewrite zb_lxor_ones by lia; rewrite <- (Z_to_bv_mod64 (- (DT + 4) - 1)); f_equal;
                   first [ apply (Z.mod_unique _ _ (-1)) | symmetry; apply (Z.mod_unique _ _ (-1)) ]; lia) end.
      all: eapply (OUTER TL11 DCP SG (Z.to_nat dcap) _ (FAW b0 b1 b2 b3) DST b0 (Z_to_bv 64 b0) (Z_to_bv 64 b1) (Z_to_bv 64 b2) (Z_to_bv 64 b3)
                     _ _ _ _ _ _ _ _ (SS + 6) (SS + 6 + jt_len src 0) (SS + 6 + jt_len src 0 + jt_len src 2)
                     (SS + 6 + jt_len src 0 + jt_len src 2 + jt_len src 4)).
      all: try reflexivity.
      all: try (rewrite unsigned_lit by lia; assumption).
      all: try (rewrite Z2Nat.id by lia; lia).
      all: try lia.
      all: try (unfold RF_huf_y4s_iface.Y4M; split; [exists buf; split; assumption |]).
      all: try y4m_close.
    - xo 19916.
      eapply SLOW.
      refine (conj _ (conj SRCB (conj CBSB (conj DTB (conj ST (conj FRa (conj MI (conj MU WM)))))))).
      exists buf; split; assumption.
  Qed.

End Y4E.
End CANSEC1.
