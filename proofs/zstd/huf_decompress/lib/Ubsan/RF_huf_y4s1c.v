From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require PropExec InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_x4s
  RF_huf_y4s_iface RF_huf_y4s1.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Section Y4S1.
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

  Variables (L1 L2 L3 L4 SEG : Z).
  Notation O2 := (6 + L1). Notation O3 := (6 + L1 + L2). Notation O4 := (6 + L1 + L2 + L3).
  Hypothesis HL : 1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n.
  Hypothesis HQ : 0 < SEG /\ 3 * SEG <= dcap /\ dcap <= 4 * SEG.
  Hypothesis HQ2 : 2 <= SEG.
  Notation desc := (tl + 256 * mtl).
  Lemma HQ3 : 0 < SEG <= 2 * SEG /\ 2 * SEG <= 3 * SEG /\ 3 * SEG <= dcap.
  Proof using All. destruct HQ as (? & ? & ?). lia. Qed.

  Notation SPLL w64 k4 k2 p2 k1 j0 :=
    (SPLB desc (DST + 3 * SEG) dcap (SS + O4 + 8) (SS + O3 + 8) (SS + O2 + 8) (DST + dcap - 7) w64 k4 k2
          (SS + O2 + p2) (DST + SEG) (DST + 2 * SEG) k1 (DST + dcap) (DT + 4) j0).
  Notation SPLX v24 v32 v40 v48 v64 v72 v80 v88 v112 j0 :=
    (SPLB desc (DST + 3 * SEG) v24 v32 v40 v48 (DST + dcap - 7) v64 v72 v80 v88
          (DST + SEG) (DST + 2 * SEG) v112 (DST + dcap) (DT + 4) j0).

  Notation BDS c b p O jp := (BD4 c b (SS + O + p) (SS + O) jp).

  (* [comment removed for export] *)
  Definition Y1C1B (Q0 : Z) : Prop :=
    forall o1 o2 o3 o4 l1 l2 l3 l4 b1 b2 b3 b4 p1 p2 p3 p4 c1 c2 c3 c4 w64 mm j0 jp1 jp2 jp3 jp4
           (xr8 xt5 xr19 xs10 : word),
    Q0 < o4 + l4 - DST ->
    Y4F' mm (SPLL w64 c4 c2 p2 c1 j0) (BDS c4 b4 p4 O4 jp4) (BDS c3 b3 p3 O3 jp3) (BDS c2 b2 p2 O2 jp2)
         (BDS c1 (Z.land b1 7) (p1 - b1 / 8) 6 jp1) ->
    Y1BEF L1 p1 b1 -> 8 <= p1 -> Y1BEF L2 p2 b2 -> Y1BEF L3 p3 b3 -> Y1BEF L4 p4 b4 ->
    1 <= l1 <= 2 -> 1 <= l2 <= 2 -> 1 <= l3 <= 2 -> 1 <= l4 <= 2 ->
    DST <= o1 -> DST <= o2 -> DST <= o3 -> DST <= o4 ->
    Y1OPS SEG (o1 + l1 - DST) (o2 + l2 - DST) (o3 + l3 - DST) (o4 + l4 - DST) -> o4 + l4 <= DST + dcap ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 -> 0 <= w64 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -912)) gp tp (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SS + O3 + p3)) (Z_to_bv 64 (b1 / 8)) xr8 (Z_to_bv 64 (Z.land b1 7)) (Z_to_bv 64 l1) (Z_to_bv 64 o1) (Z_to_bv 64 l2) (Z_to_bv 64 l3) (Z_to_bv 64 3) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 o4) xr19 (Z_to_bv 64 o3) (Z_to_bv 64 (SS + 6 + p1 - b1 / 8)) (Z_to_bv 64 l4) (Z_to_bv 64 b3) (Z_to_bv 64 (SS + O4 + p4)) (Z_to_bv 64 b4) xs10 (Z_to_bv 64 o2) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SS + 6 + p1)) xt5 (Z_to_bv 64 c3))
                        F (Z_to_bv 64 (PY4_BODY + 2208)) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition Y1C2 (Q0 : Z) : Prop :=
    forall o1 o2 o3 o4 l1 l2 l3 l4 b1 b2 b3 b4 p1 p2 p3 p4 st1 c1 c2 c3 c4 mm j0 jp1 jp2 jp3 jp4
           (xs0 xs8 xs10 xt5 : word),
    Y4F' mm (SPLL st1 c4 c2 p2 c1 j0) (BDS c4 b4 p4 O4 jp4) (BDS c3 b3 p3 O3 jp3) (BDS c2 b2 p2 O2 jp2) (BDS c1 b1 p1 6 jp1) ->
    Y1AFT L1 p1 b1 st1 -> Y1BEF L2 p2 b2 -> Y1BEF L3 p3 b3 -> Y1BEF L4 p4 b4 -> 8 <= p2 ->
    Q0 < o4 + l4 - DST ->
    1 <= l1 <= 2 -> 1 <= l2 <= 2 -> 1 <= l3 <= 2 -> 1 <= l4 <= 2 ->
    DST <= o1 -> DST <= o2 -> DST <= o3 -> DST <= o4 ->
    Y1OPS SEG (o1 + l1 - DST) (o2 + l2 - DST) (o3 + l3 - DST) (o4 + l4 - DST) -> o4 + l4 <= DST + dcap ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -912)) gp tp (Z_to_bv 64 (SS + O3 + p3)) (Z_to_bv 64 (DT + 4))
                            (Z_to_bv 64 (SS + O2 + 8)) xs0 (Z_to_bv 64 b1) (Z_to_bv 64 l1) (Z_to_bv 64 o1) (Z_to_bv 64 l2) (Z_to_bv 64 l3) (Z_to_bv 64 3)
                            (Z_to_bv 64 (2^61)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 o4) (Z_to_bv 64 c3)
                            (Z_to_bv 64 o3) (Z_to_bv 64 (SS + O2 + p2)) (Z_to_bv 64 l4) (Z_to_bv 64 b3) xs8 (Z_to_bv 64 b4) xs10 (Z_to_bv 64 o2)
                            (Z_to_bv 64 (SS + O4 + p4)) (Z_to_bv 64 (SS + 6 + p1)) xt5 (Z_to_bv 64 (DST + dcap)))
                        F (Z_to_bv 64 (PY4_BODY + 2344)) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition Y1C3 (Q0 : Z) : Prop :=
    forall o1 o2 o3 o4 l1 l2 l3 l4 b1 b2 b3 b4 p1 p2 p3 p4 st1 st2 c1 c2 c3 c4 p2s mm j0 jp1 jp2 jp3 jp4
           (xt2 xs0 xs8 xs10 xt5 : word),
    Y4F' mm (SPLL st1 c4 c2 p2s c1 j0) (BDS c4 b4 p4 O4 jp4) (BDS c3 b3 p3 O3 jp3) (BDS c2 b2 p2 O2 jp2) (BDS c1 b1 p1 6 jp1) ->
    Y1AFT L1 p1 b1 st1 -> Y1AFT L2 p2 b2 st2 -> Y1BEF L3 p3 b3 -> Y1BEF L4 p4 b4 ->
    0 <= p2s ->
    Q0 < o4 + l4 - DST ->
    1 <= l1 <= 2 -> 1 <= l2 <= 2 -> 1 <= l3 <= 2 -> 1 <= l4 <= 2 ->
    DST <= o1 -> DST <= o2 -> DST <= o3 -> DST <= o4 ->
    Y1OPS SEG (o1 + l1 - DST) (o2 + l2 - DST) (o3 + l3 - DST) (o4 + l4 - DST) -> o4 + l4 <= DST + dcap ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -912)) gp tp (Z_to_bv 64 (SS + O3 + p3)) (Z_to_bv 64 (DT + 4))
                            xt2 xs0 (Z_to_bv 64 b1) (Z_to_bv 64 l1) (Z_to_bv 64 o1) (Z_to_bv 64 l2) (Z_to_bv 64 l3) (Z_to_bv 64 st2)
                            (Z_to_bv 64 (2^61)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 o4) (Z_to_bv 64 c3)
                            (Z_to_bv 64 o3) (Z_to_bv 64 (SS + O2 + p2)) (Z_to_bv 64 l4) (Z_to_bv 64 b3) xs8 (Z_to_bv 64 b4) xs10 (Z_to_bv 64 o2)
                            (Z_to_bv 64 (SS + O4 + p4)) (Z_to_bv 64 (SS + 6 + p1)) xt5 (Z_to_bv 64 (DST + dcap)))
                        F (Z_to_bv 64 (PY4_BODY + 2516)) fc None mm (seg_rom usegs)).

End Y4S1.
End CANSEC1.
