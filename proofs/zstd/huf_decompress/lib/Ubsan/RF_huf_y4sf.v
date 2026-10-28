(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require PropExec InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_x4s
  RF_huf_fa_iface RF_huf_y4s RF_huf_y4s_iface RF_huf_y4s1 RF_huf_y4s1d RF_huf_y4s1k RF_huf_y4s04 RF_huf_y4s33_kit
  RF_huf_y4s3 RF_huf_y4s0 RF_huf_y4s01 RF_huf_y4s02 RF_huf_y4s03 RF_huf_y4s04m.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Section Y4SF.
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
  Notation Y4F' mm spl b4 b3 b2 b1 :=
    (Y4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl b4 b3 b2 b1).
  Notation L1 := (jt_len src 0). Notation L2 := (jt_len src 2). Notation L3 := (jt_len src 4).
  Notation L4 := (n - (6 + L1 + L2 + L3)).
  Notation O2 := (6 + L1). Notation O3 := (6 + L1 + L2). Notation O4 := (6 + L1 + L2 + L3).
  Notation SEG := ((dcap + 3) / 4).
  Notation desc := (tl + 256 * mtl).
  Notation SPLL w64 k4 k2 p2 k1 j0 :=
    (SPLB desc (DST + 3 * SEG) dcap (SS + O4 + 8) (SS + O3 + 8) (SS + O2 + 8) (DST + dcap - 7) w64 k4 k2
          (SS + O2 + p2) (DST + SEG) (DST + 2 * SEG) k1 (DST + dcap) (DT + 4) j0).
  Notation SPLX v24 v32 v40 v48 v64 v72 v80 v88 v112 j0 :=
    (SPLB desc (DST + 3 * SEG) v24 v32 v40 v48 (DST + dcap - 7) v64 v72 v80 v88
          (DST + SEG) (DST + 2 * SEG) v112 (DST + dcap) (DT + 4) j0).
  Notation BDS c b p O jp := (BD4 c b (SS + O + p) (SS + O) jp).

  Definition Y4LOOP : Prop := (1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n) -> (0 < SEG /\ 3 * SEG <= dcap /\ dcap <= 4 * SEG) -> 2 <= SEG ->
    forall q1 q2 q3 q4 b1 b2 b3 b4 p1 p2 p3 p4 c1 c2 c3 c4 w64 mm j0 jp1 jp2 jp3 jp4
                           (xt2 xs0 xa0 xa2 xa3 xa4 xs5 xs6 xs8 xs10 xt5 : word),
    Y4F' mm (SPLL w64 c4 c2 p2 c1 j0) (BDS c4 b4 p4 O4 jp4) (BDS c3 b3 p3 O3 jp3) (BDS c2 b2 p2 O2 jp2) (BDS c1 b1 p1 6 jp1) ->
    Y1OPS SEG q1 q2 q3 q4 -> q4 + 8 <= dcap ->
    Y1HDI L1 p1 b1 -> Y1HDI L2 p2 b2 -> Y1HDI L3 p3 b3 -> Y1HDI L4 p4 b4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 -> 0 <= w64 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -912)) gp tp (Z_to_bv 64 (SS + O3 + p3)) (Z_to_bv 64 (DT + 4))
                            xt2 xs0 (Z_to_bv 64 b1) xa0 (Z_to_bv 64 (DST + q1)) xa2 xa3 xa4 (Z_to_bv 64 (2^61))
                            (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 (DST + q4)) (Z_to_bv 64 c3)
                            (Z_to_bv 64 (DST + q3)) xs5 xs6 (Z_to_bv 64 b3) xs8 (Z_to_bv 64 b4) xs10 (Z_to_bv 64 (DST + q2))
                            (Z_to_bv 64 (SS + O4 + p4)) (Z_to_bv 64 (SS + 6 + p1)) xt5 (Z_to_bv 64 (DST + dcap)))
                        F (Z_to_bv 64 0x1aaf4) fc None mm (seg_rom usegs)).

  Definition Y4EXIT : Prop := (1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n) -> (0 < SEG /\ 3 * SEG <= dcap /\ dcap <= 4 * SEG) -> 2 <= SEG ->
    forall q1 q2 q3 q4 b1 b2 b3 b4 p1 p2 p3 p4 st1 st2 st3 st4 c1 c2 c3 c4
                           v24 v32 v40 v48 v64 v72 v80 v88 v112 mm j0 jp1 jp2 jp3 jp4
                           (xra xt0 xt2 xs0 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 : word),
    Y4F' mm (SPLX v24 v32 v40 v48 v64 v72 v80 v88 v112 j0)
         (BDS c4 b4 p4 O4 jp4) (BDS c3 b3 p3 O3 jp3) (BDS c2 b2 p2 O2 jp2) (BDS c1 b1 p1 6 jp1) ->
    0 <= q1 <= dcap -> 0 <= q2 <= dcap -> 0 <= q3 <= dcap -> 0 <= q4 <= dcap ->
    Y1AFT L1 p1 b1 st1 -> Y1AFT L2 p2 b2 st2 -> Y1AFT L3 p3 b3 st3 -> Y1AFT L4 p4 b4 st4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp xt0 (Z_to_bv 64 (DT + 4)) xt2 xs0 xs1 xa0
                            (Z_to_bv 64 (DST + q1)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (DST + q4)) xs3 (Z_to_bv 64 (DST + q3))
                            xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + q2)) xt3 xt4 xt5 (Z_to_bv 64 (DST + dcap)))
                        F (Z_to_bv 64 0x1b41c) fc None mm (seg_rom usegs)).


  Lemma y4_main : Y4EXIT -> Y4LOOP.
  Proof using All.
    unfold Y4EXIT, Y4LOOP. intros EX HLp HQp SG2.
    exact (y4s1_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47 DT4 L1 L2 L3 L4 SEG HLp HQp SG2  (EX HLp HQp SG2)).
  Qed.

  Notation YB l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).

  Ltac xo3 := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
        let d := eval vm_compute in ((z =? PY4_BODY + 3076) || (z =? PY4_BODY + 13332) || (z =? PY4_BODY + 13336)
                                     || (z =? PY4_BODY + 13340)) in
        lazymatch d with true => fail | false => zstep end
    | _ => zstep end).
  Ltac w3 := xo3; repeat (lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
    let K := fresh "K" in if_cases K; zify_cond K end; xo3).

  Lemma y4_exit : Y4EXIT.
  Proof using All.
    unfold Y4EXIT. intros HLp HQp SG2. intros until xt5. intros XF Q1 Q2 Q3 Q4 A1 A2 A3 A4 C1 C2 C3 C4.
    pose proof XF as XF0.
    destruct XF as ((buf & BUFA & BUFL) & SRC & CBS & ST & SPC & L0 & B4 & LB4 & B3 & LB3 & B2 & LB2 & B1 & LB1 &
                    (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & SV) & (jl & JL) & FR & MI & MU & WM).
    unfold BD4 in B1, B2, B3, B4. unfold SPLB in SPC.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof TOK as (TL & _). unfold HUF_TABLELOG_MAX in TL.
    pose proof A1 as A1u; pose proof A2 as A2u; pose proof A3 as A3u; pose proof A4 as A4u.
    unfold Y1AFT in A1u, A2u, A3u, A4u.
    w3.
    all: try (exfalso; lia).
    all: first
      [ eapply (YB y4s_epi); exact XF0
      | eapply (YB y4s_err); exact XF0
      | eapply (YB y4s_m1); exact XF0
      | eapply ((YB y4s3_all) L1 L2 L3 L4 SEG (2 * SEG) (3 * SEG) HLp ltac:(lia));
        first [ exact XF0 | lia ]
      | showpc; fail ].
  Qed.

  Notation YC l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47 DT4) (only parsing).
  Lemma y4_slow_sec : y4_slow_goal ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs.
  Proof using All.
    exact (YC y4s0_entry (YC y4s01_call1 (YC y4s02_call2 (YC y4s03_call3 (YC y4s04_call4 (y4_main y4_exit) y4_exit))))).
  Qed.
End Y4SF.

Theorem y4_slow_proof : y4_slow_stmt.
Proof.
  unfold y4_slow_stmt. intros. eapply y4_slow_sec; eassumption.
Qed.

End CANSEC1.
