From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_x4s
  RF_huf_y4s_iface RF_huf_y4s31_kit RF_huf_y4s1.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition Y1H (P : Prop) : Prop := P.

Section CANSEC1. Context {rc : runConstT}.
Section Y4S1D.
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

  Notation SPLL w64 k4 k2 p2 k1 j0 :=
    (SPLB desc (DST + 3 * SEG) dcap (SS + O4 + 8) (SS + O3 + 8) (SS + O2 + 8) (DST + dcap - 7) w64 k4 k2
          (SS + O2 + p2) (DST + SEG) (DST + 2 * SEG) k1 (DST + dcap) (DT + 4) j0).
  Notation SPLX v24 v32 v40 v48 v64 v72 v80 v88 v112 j0 :=
    (SPLB desc (DST + 3 * SEG) v24 v32 v40 v48 (DST + dcap - 7) v64 v72 v80 v88
          (DST + SEG) (DST + 2 * SEG) v112 (DST + dcap) (DT + 4) j0).
  Notation BDS c b p O jp := (BD4 c b (SS + O + p) (SS + O) jp).

  Ltac y4open H :=
    destruct H as (OUTX & SRC & TB & STK & FL & FLS & F4 & F4S & F3 & F3S & F2 & F2S & F1 & F1S & SAV & JL & FR & MI & MU & WM);
    destruct OUTX as (buf & OUT & LB); change (zlen buf) with (Z.of_nat (length buf)) in LB;
    destruct SAV as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & SAV); destruct JL as (jl & JL);
    pose proof TOK as (TL1 & TLN & TCK); cbv [HUF_TABLELOG_MAX] in TL1; cbv [FseNCount.Zlength] in TLN;
    unfold SPLB, BD4 in *.

  Ltac ustep1 stops TCK OUT LB :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
        lazymatch eval vm_compute in (orb (existsb (Z.eqb pc) stops) (u_is_chk usegs pc)) with
        | true => fail
        | false =>
            try (let v := fresh "v" in uidx tl v);
            try rewrite u_shl2;
            try unfold sx16;
            try (rewrite ?u_srl3 by lia);
            try (rewrite u_shamt by lia);
            repeat (match goal with |- context [sx32 (Z_to_bv 64 ?z)] => rewrite (sx32_small z) by lia end);
            repeat (match goal with
                    | |- context [bv_unsigned (Z_to_bv 8 (x2_len ?c))] => rewrite (byte_lit (x2_len c)) by lia
                    | |- context [bv_unsigned (Z_to_bv 8 (x2_nbBits ?c))] => rewrite (byte_lit (x2_nbBits c)) by lia
                    | |- context [bv_unsigned (Z_to_bv 8 (x2_seq ?c))] => rewrite (byte_lit (x2_seq c)) by lia end);
            repeat (ucell tl cells TCK);
            first [ zstep | ustore OUT LB | urd_new DT cells cbs ECB; zstep | urd_all DT cells cbs ECB; zstep ]
        end
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let H := fresh "B" in if_cases H; zify_cond H;
        try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
               lazymatch eval vm_compute in (u_is_chk usegs pc) with
               | true => unorm H; solve [zrefute H]
               end end)
    end.

  Notation YR2 Q0 := (Y1R2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG Q0).
  Notation YREL Q0 := (Y1REL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG Q0).

  Ltac ybef Pb Bc := unfold Y1BEF; split; [lia|]; split; [exact Pb|]; split; [lia|];
    let HP8 := fresh "HP8" in intro HP8; unfold Y1H in Bc; specialize (Bc HP8); lia.

  Lemma y4s1_r34 : forall Q0, YREL (Q0 + 2) -> YR2 Q0.
  Proof using All.
    intros Q0 K. unfold Y1R2.
    intros r1 r2 r3 r4 l1 l2 l3 l4 b1 b2 b3 b4 bb1 bb2 bb3 bb4 p1 p2 p3 p4 c1 c2 c3 c4 w64 mm j0 jp1 jp2 jp3 jp4
           xra xt2 xa0 xs7 xs8 QR FR0 H1 H2 H3 H4 L1r L2r L3r L4r R1 R2 R3 R4 OPS R4D C1 C2 C3 C4 W64.
    y4open FR0.
    assert (D8 : 8 <= DST) by (apply DP; lia).
    destruct H1 as (P1a & P1b & B1r & B1c), H2 as (P2a & P2b & B2r & B2c), H3 as (P3a & P3b & B3r & B3c),
             H4 as (P4a & P4b & B4r & B4c).
    change (Y1H (p1 = 0 \/ p1 + 8 <= L1)) in P1b; change (Y1H (p2 = 0 \/ p2 + 8 <= L2)) in P2b;
    change (Y1H (p3 = 0 \/ p3 + 8 <= L3)) in P3b; change (Y1H (p4 = 0 \/ p4 + 8 <= L4)) in P4b;
    change (Y1H (8 <= p1 -> b1 <= 32)) in B1c; change (Y1H (8 <= p2 -> b2 <= 32)) in B2c;
    change (Y1H (8 <= p3 -> b3 <= 32)) in B3c; change (Y1H (8 <= p4 -> b4 <= 32)) in B4c.
    unfold Y1OPS in OPS.
    do 120 (try ustep1 [110360] TCK OUT LB).
    do 120 (try ustep1 [110716] TCK OUT LB).
    ubdnorm F1; ubdnorm F2; ubdnorm F3; ubdnorm F4.
    eapply K.
    all: try (lazymatch goal with |- Y4F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold Y4F, SPLB, BD4; upack end).
    all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => lia end).
    all: try (lazymatch goal with |- 1 <= _ <= 2 => lia end).
    all: try (lazymatch goal with |- DST <= _ => lia end).
    all: try (lazymatch goal with
      | |- Y1BEF L1 _ _ => ybef P1b B1c | |- Y1BEF L2 _ _ => ybef P2b B2c
      | |- Y1BEF L3 _ _ => ybef P3b B3c | |- Y1BEF L4 _ _ => ybef P4b B4c end).
    all: try (lazymatch goal with |- Y1OPS _ _ _ _ _ => unfold Y1OPS in *; lia end).
    all: lia.
  Qed.
End Y4S1D.
End CANSEC1.
