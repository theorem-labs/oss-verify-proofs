(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require PropExec InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_x4s
  RF_huf_fa_iface RF_huf_y4s RF_huf_y4s_iface RF_huf_y4s0 RF_huf_bitinit RF_huf_y4s01.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Section CANSEC1. Context {rc : runConstT}.
Section Y4S02.
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
  Hypothesis CBL : DT + 4 + 4 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 4 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.
  Hypothesis DT4 : DT mod 4 = 0.

  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation YB l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).
  Notation Y4F' mm spl b4 b3 b2 b1 :=
    (Y4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl b4 b3 b2 b1).
  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation Y4S' mm := (Y4S ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm).
  Notation L1 := (jt_len src 0). Notation L2 := (jt_len src 2). Notation L3 := (jt_len src 4).
  Notation O2 := (6 + L1). Notation O3 := (6 + L1 + L2). Notation O4 := (6 + L1 + L2 + L3).
  Notation SEG := ((dcap + 3) / 4).
  Notation desc := (tl + 256 * mtl).
  (* [comment removed for export] *)
  Notation SPL436 j0 j112 :=
    [CB 96 j0; C8 (Z_to_bv 64 (DST + SEG)); C8 (Z_to_bv 64 (DST + 2 * SEG)); CB 8 j112;
     C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 (DT + 4))].
  Notation BS1 := (firstn (Z.to_nat L1) (skipn (Z.to_nat 6) src)).
  Notation BS2 := (firstn (Z.to_nat L2) (skipn (Z.to_nat O2) src)).

(* [comment removed for export] *)
  Hypothesis HC488 : forall mm j0 j112 jb4 jb3 d1 jp1 d2 jp2
      (xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    Y4F' mm (SPL436 j0 j112) [CB 40 jb4] [CB 40 jb3] (bitd_cells (SS + O2) d2 jp2) (bitd_cells (SS + 6) d1 jp1) ->
    init_dstream BS1 = Ok d1 -> init_dstream BS2 = Ok d2 ->
    6 <= dcap -> 10 <= n -> O4 <= n ->
    t1 = Z_to_bv 64 (DST + dcap) -> x8 = Z_to_bv 64 DST -> x9 = Z_to_bv 64 (SS + O3) ->
    a0 = Z_to_bv 64 (SP + -736) -> a1 = Z_to_bv 64 (SS + O3) -> a2 = Z_to_bv 64 L3 ->
    x18 = Z_to_bv 64 L3 -> x19 = Z_to_bv 64 (SS + O2) -> x20 = Z_to_bv 64 L2 -> x21 = Z_to_bv 64 O4 ->
    x22 = Z_to_bv 64 n -> x23 = Z_to_bv 64 (-120) -> x24 = Z_to_bv 64 desc -> x25 = Z_to_bv 64 (DST + 2 * SEG) ->
    x26 = Z_to_bv 64 dcap -> x27 = Z_to_bv 64 (DST + 3 * SEG) ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 109088) fc None mm (seg_rom usegs)).

  Ltac y4s02_y4f :=
    unfold Y4F; repeat match goal with |- _ /\ _ => split end;
    first [ eassumption | reflexivity | (eexists; split; eassumption) | (eexists; eassumption)
          | (do 12 eexists; unfold PY4_RET; eassumption) ].
  Ltac y4s02_call D S BS L :=
    assert (ZLB : Z.of_nat (length BS) = L) by (apply y4_sub_len; lia);
    assert (LMB : Z.of_nat (length (map (Z_to_bv 8) BS)) = L) by (rewrite length_map; exact ZLB);
    call (bit_init_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D S BS _ lo);
    repeat match goal with E : bv_unsigned (Z_to_bv 64 _) = _ |- _ => rewrite E end;
    try (first [eassumption | lia | reflexivity | (rewrite ZLB; reflexivity) | (rewrite ZLB; lia) | (apply y4_bytes_sub; exact BYS) | (f_equal; lia)]).
  Ltac y4s02_after BS :=
    let INI0 := fresh "INI0" in let INI := fresh "INI" in
    pose proof (init_dstream_ok BS) as INI0;
    first [pose proof (INI0 (Forall_all_bytes _ ltac:(apply y4_bytes_sub; exact BYS))) as INI | pose proof INI0 as INI]; clear INI0;
    let e := fresh "e" in let EE := fresh "EE" in let d := fresh "d" in let ED := fresh "ED" in
    destruct INI as [(e & EE) | (d & ED & ? & ? & ?)];
    [ lazymatch goal with H : context [match init_dstream BS with _ => _ end] |- _ =>
        rewrite EE in H; cbn iota in H; let RET := fresh "RET" in destruct H as (RET & ? & ?);
        lazymatch type of RET with ?r = _ => subst r end end;
      pose proof (y4_init_err _ e EE)
    | lazymatch goal with H : context [match init_dstream BS with _ => _ end] |- _ =>
        rewrite ED in H; cbn iota in H; let RET := fresh "RET" in destruct H as (RET & ? & ? & ?);
        lazymatch type of RET with ?r = _ => subst r end end ];
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end).

(* [comment removed for export] *)
  Lemma y4s02_call2 : forall mm j0 j112 jb4 jb3 jb2 d1 jp1
      (xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    Y4F' mm (SPL436 j0 j112) [CB 40 jb4] [CB 40 jb3] [CB 40 jb2] (bitd_cells (SS + 6) d1 jp1) ->
    init_dstream BS1 = Ok d1 ->
    6 <= dcap -> 10 <= n -> O4 <= n ->
    t1 = Z_to_bv 64 (DST + dcap) -> x8 = Z_to_bv 64 DST -> x9 = Z_to_bv 64 (SS + O3) ->
    a0 = Z_to_bv 64 (SP + -696) -> a1 = Z_to_bv 64 (SS + O2) -> a2 = Z_to_bv 64 L2 ->
    x18 = Z_to_bv 64 L3 -> x19 = Z_to_bv 64 (SS + O2) -> x20 = Z_to_bv 64 L2 -> x21 = Z_to_bv 64 O4 ->
    x22 = Z_to_bv 64 n -> x23 = Z_to_bv 64 (-120) -> x24 = Z_to_bv 64 desc -> x25 = Z_to_bv 64 (DST + 2 * SEG) ->
    x26 = Z_to_bv 64 dcap -> x27 = Z_to_bv 64 (DST + 3 * SEG) ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 109064) fc None mm (seg_rom usegs)).
  Proof using All.
    intros mm j0 j112 jb4 jb3 jb2 d1 jp1 xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6
      XF ED1 D6 N10 NO4 E6 E8 E9 E10 E11 E12 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27.
    subst t1 x8 x9 a0 a1 a2 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27.
    destruct XF as (BUF & SRC & CBS & ST & SPC & LS0 & B4 & LB4 & B3 & LB3 & B2 & LB2 & B1 & LB1 & SV & (jl & JL) & FR & MI & MU & WM).
    destruct SV as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & SV). unfold PY4_RET in SV.
    destruct BUF as (buf & OUT & LBUF).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof TOK as (TL1 & _). unfold HUF_TABLELOG_MAX in TL1.
    assert (Y0 : 0 <= Znth 0 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y1 : 0 <= Znth 1 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y2 : 0 <= Znth 2 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y3 : 0 <= Znth 3 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y4 : 0 <= Znth 4 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y5 : 0 <= Znth 5 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (HL1 : 0 <= L1 < 2^16) by (unfold jt_len; change (0 + 1) with 1; lia).
    assert (HL2 : 0 <= L2 < 2^16) by (unfold jt_len; change (2 + 1) with 3; lia).
    assert (HL3 : 0 <= L3 < 2^16) by (unfold jt_len; change (4 + 1) with 5; lia).
    assert (LMS : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity).
    pose proof (y4_src_sub usegs mm SS src O2 L2 SRC ltac:(lia) ltac:(lia) ltac:(lia)) as SB2.
    assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -912)) = SP + -912)
      by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
    zstep.
    y4s02_call constr:(SP + -696) constr:(SS + O2) constr:(firstn (Z.to_nat L2) (skipn (Z.to_nat O2) src)) constr:(L2).
    y4s02_after constr:(firstn (Z.to_nat L2) (skipn (Z.to_nat O2) src)).
    all: y4z_walk 109088 121940 SS src SRC.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 121940) _ _ _ _) => eapply (YB y4s_epi); y4s02_y4f
         | |- evt _ _ (MS _ _ (Z_to_bv 64 109088) _ _ _ _) =>
             first [ solve [exfalso; first [lia | (Z.div_mod_to_equations; lia)]]
                   | (eapply HC488; first [ y4s02_y4f | eassumption | lia | reflexivity | (f_equal; lia) ]) ]
         end.
  Qed.
End Y4S02.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
