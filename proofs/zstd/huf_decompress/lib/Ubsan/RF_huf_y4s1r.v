From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require PropExec InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_x4s
  RF_huf_y4s_iface RF_huf_y4s1 RF_huf_y4s31_kit RF_huf_y4s1c RF_huf_x2t_top_kit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma u_lx1 : forall a b, 0 <= a -> 0 <= b -> Z.lxor (Z.b2z true) (Z.b2z (Z.lxor a b <? 1)) = 0 -> a = b.
Proof.
  intros a b A B H. destruct (Z.lxor a b <? 1) eqn:E; cbn in H; [| discriminate H].
  apply Z.ltb_lt in E. assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  apply Z.lxor_eq_0_iff. lia.
Qed.

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

  Definition Y1H (P : Prop) : Prop := P.
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
               | true => unorm H; try (apply u_lx1 in H; [ | lia | apply Z.div_pos; lia ]); solve [zrefute H | unfold Y1H in *; zrefute H]
               end end)
    end.

  Ltac showregs3 := showreg 1%Z; showreg 5%Z; showreg 6%Z; showreg 7%Z; showreg 8%Z; showreg 9%Z; showreg 10%Z; showreg 11%Z; showreg 12%Z; showreg 13%Z; showreg 14%Z; showreg 15%Z; showreg 16%Z; showreg 17%Z; showreg 18%Z; showreg 19%Z; showreg 20%Z; showreg 21%Z; showreg 22%Z; showreg 23%Z; showreg 24%Z; showreg 25%Z; showreg 26%Z; showreg 27%Z; showreg 28%Z; showreg 29%Z; showreg 30%Z; showreg 31%Z.


  Ltac srd8 SRC :=
    lazymatch type of SRC with bytes_at usegs ?mm ?S ?bs =>
      let E := u_mem_addr in
      let R := fresh "R8" in
      pose proof (bytes_at_read usegs mm S bs (E - S) 8 SRC ltac:(lia) ltac:(rewrite ?length_map; lia)) as R;
      replace (S + (E - S)) with E in R by lia end.

  Ltac srd1 SRC :=
    lazymatch type of SRC with bytes_at usegs ?mm ?S ?bs =>
      let E := u_mem_addr in
      let R := fresh "R1" in
      pose proof (bytes_at_read usegs mm S bs (E - S) 1 SRC ltac:(lia) ltac:(rewrite ?length_map; lia)) as R;
      replace (S + (E - S)) with E in R by lia end.

  Lemma u_srl3z : forall x, 0 <= x < 2^32 -> bv_swrap 32 (bv_wrap 32 x ≫ 3) = x / 8.
  Proof. intros x H. rewrite srliw_val by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
  Ltac unorm2 :=
    repeat (match goal with |- context [bv_swrap 32 (bv_wrap 32 ?x ≫ 3)] =>
              rewrite (u_srl3z x) by (unfold Y1H in *; lia) end);
    repeat (match goal with |- context [(?a) mod 18446744073709551616] =>
              lazymatch a with context [SS] => rewrite (Z.mod_small a 18446744073709551616) by (unfold Y1H in *; lia) end end).
  Ltac unorm3 :=
    repeat (match goal with |- context [(?a) mod 18446744073709551616] =>
              lazymatch a with context [SS] => rewrite (Z.mod_small a 18446744073709551616) by lia end end);
    repeat (match goal with |- context [0 <? ?a] =>
              lazymatch a with context [SS] => replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia) end end).
  Ltac pfacts :=
    repeat match goal with
    | PB : 8 <= ?p -> ?b / 8 <= 7, PL : Y1H (?p = 0 \/ ?p + 8 <= ?L) |- _ =>
        lazymatch goal with _ : ?p + 8 <= L |- _ => fail | _ =>
          let G := fresh "G8" in assert (G : 8 <= p) by lia;
          let H1 := fresh "PQ" in let H2 := fresh "PQ" in
          assert (H1 : p + 8 <= L) by (unfold Y1H in PL; destruct PL; lia);
          assert (H2 : b / 8 <= 7) by (apply PB; exact G) end
    end.
  Ltac srcfirst stops SRC :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch eval vm_compute in (orb (existsb (Z.eqb pc) stops) (u_is_chk usegs pc)) with
      | false => let E := u_mem_addr in
                 lazymatch E with context [SS] => try pfacts;
                   let w := eval vm_compute in (match fetch_word usegs (Z_to_bv 64 pc) with
                                                | Some w => match decode_any w with Some (Load SZ1 _ _ _ _, _) => true | _ => false end
                                                | None => false end) in
                   lazymatch w with true => srd1 SRC; zstep | false => srd8 SRC; zstep end end
      end end.
  Ltac ustep2 stops TCK OUT LB SRC :=
    first [ srcfirst stops SRC | try unorm3; try unorm2;
    first [ srcfirst stops SRC
          | ustep1 stops TCK OUT LB
          | lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              lazymatch eval vm_compute in (orb (existsb (Z.eqb pc) stops) (u_is_chk usegs pc)) with
              | false => first [ srd8 SRC; zstep | srd1 SRC; zstep ] end end ] ].

  Ltac ybef Pb Bc := unfold Y1BEF; split; [lia|]; split; [exact Pb|]; split; [lia|];
    let HP8 := fresh "HP8" in intro HP8; unfold Y1H in Bc; specialize (Bc HP8); lia.

  Lemma y4s1_r1 : forall Q0,
    Y1C1B ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG Q0 -> Y1C2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG Q0 -> Y1C3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG Q0 -> Y1REL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG Q0.
  Proof using All.
    intros Q0 HC1 HC2 HC3. unfold Y1REL.
    intros o1 o2 o3 o4 l1 l2 l3 l4 B1 B2 B3 B4 p1 p2 p3 p4 c1 c2 c3 c4 w64 mm j0 jp1 jp2 jp3 jp4 xt2 xs0 xa4 xs5 xs8 xs10 xt5
      QQ FR0 H1 H2 H3 H4 L1r L2r L3r L4r O1a O2a O3a O4a OPS OLIM C1 C2 C3 C4 W64.
    y4open FR0.
    assert (D8 : 8 <= DST) by (apply DP; lia).
    destruct H1 as (P1a & P1b & B1r & B1c), H2 as (P2a & P2b & B2r & B2c), H3 as (P3a & P3b & B3r & B3c),
             H4 as (P4a & P4b & B4r & B4c).
    assert (P1n : 0 <= p1 <= L1) by (destruct P1b; lia). assert (P2n : 0 <= p2 <= L2) by (destruct P2b; lia).
    assert (P3n : 0 <= p3 <= L3) by (destruct P3b; lia). assert (P4n : 0 <= p4 <= L4) by (destruct P4b; lia).
    assert (PB1 : 8 <= p1 -> B1 / 8 <= 7) by (intro; apply Z.div_le_upper_bound; lia).
    assert (PB2 : 8 <= p2 -> B2 / 8 <= 7) by (intro; apply Z.div_le_upper_bound; lia).
    assert (PB3 : 8 <= p3 -> B3 / 8 <= 7) by (intro; apply Z.div_le_upper_bound; lia).
    assert (PB4 : 8 <= p4 -> B4 / 8 <= 7) by (intro; apply Z.div_le_upper_bound; lia).
    change (Y1H (p1 = 0 \/ p1 + 8 <= L1)) in P1b; change (Y1H (p2 = 0 \/ p2 + 8 <= L2)) in P2b;
    change (Y1H (p3 = 0 \/ p3 + 8 <= L3)) in P3b; change (Y1H (p4 = 0 \/ p4 + 8 <= L4)) in P4b;
    change (Y1H (8 <= p1 -> B1 <= 56)) in B1c; change (Y1H (8 <= p2 -> B2 <= 56)) in B2c;
    change (Y1H (8 <= p3 -> B3 <= 56)) in B3c; change (Y1H (8 <= p4 -> B4 <= 56)) in B4c.
    unfold PY4_BODY.
    all: repeat (ustep2 [PY4_BODY + 700; PY4_BODY + 2208; PY4_BODY + 2344; PY4_BODY + 2516; PY4_BODY + 2708; PY4_BODY + 2904; PY4_BODY + 3044] TCK OUT LB SRC).
    1: { ubdnorm F1; ubdnorm F2; ubdnorm F3; ubdnorm F4.
         eapply HC2.
         all: try (lazymatch goal with |- Y4F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold Y4F, SPLB, BD4; upack end).
         all: try (lazymatch goal with |- Y4F' _ _ _ _ _ _ => unfold Y4F', Y4F, SPLB, BD4; upack end).
         all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => lia end).
         all: try (lazymatch goal with |- 1 <= _ <= 2 => lia end).
         all: try (lazymatch goal with |- DST <= _ => lia end).
         all: try (lazymatch goal with
           | |- Y1BEF L1 _ _ => ybef P1b B1c | |- Y1BEF L2 _ _ => ybef P2b B2c
           | |- Y1BEF L3 _ _ => ybef P3b B3c | |- Y1BEF L4 _ _ => ybef P4b B4c end).
         all: try (lazymatch goal with |- Y1OPS _ _ _ _ _ => exact OPS end).
         all: try (lazymatch goal with |- Y1AFT L1 _ _ _ => unfold Y1AFT; unfold Y1H in P1b; intuition lia end).
         all: try (lazymatch goal with |- Y1AFT L2 _ _ _ => unfold Y1AFT; unfold Y1H in P2b; intuition lia end).
         all: try lia. }
    1: { ubdnorm F1; ubdnorm F2; ubdnorm F3; ubdnorm F4.
         eapply HC3.
         all: try (lazymatch goal with |- Y4F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold Y4F, SPLB, BD4; upack end).
         all: try (lazymatch goal with |- Y4F' _ _ _ _ _ _ => unfold Y4F', Y4F, SPLB, BD4; upack end).
         all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => lia end).
         all: try (lazymatch goal with |- 1 <= _ <= 2 => lia end).
         all: try (lazymatch goal with |- DST <= _ => lia end).
         all: try (lazymatch goal with
           | |- Y1BEF L1 _ _ => ybef P1b B1c | |- Y1BEF L2 _ _ => ybef P2b B2c
           | |- Y1BEF L3 _ _ => ybef P3b B3c | |- Y1BEF L4 _ _ => ybef P4b B4c end).
         all: try (lazymatch goal with |- Y1OPS _ _ _ _ _ => exact OPS end).
         all: try (lazymatch goal with |- Y1AFT L1 _ _ _ => unfold Y1AFT; unfold Y1H in P1b; intuition lia end).
         all: try (lazymatch goal with |- Y1AFT L2 _ _ _ => unfold Y1AFT; unfold Y1H in P2b; intuition lia end).
         all: try lia. }
    1: { replace (SS + 6 + p1 - B1 / 8) with (SS + 6 + (p1 - B1 / 8)) in F1 by lia; ubdnorm F1; ubdnorm F2; ubdnorm F3; ubdnorm F4.
         eapply HC1.
         all: try (lazymatch goal with |- Y4F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold Y4F, SPLB, BD4; upack end).
         all: try (lazymatch goal with |- Y4F' _ _ _ _ _ _ => unfold Y4F', Y4F, SPLB, BD4; upack end).
         all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => lia end).
         all: try (lazymatch goal with |- 1 <= _ <= 2 => lia end).
         all: try (lazymatch goal with |- DST <= _ => lia end).
         all: try (lazymatch goal with
           | |- Y1BEF L1 _ _ => ybef P1b B1c | |- Y1BEF L2 _ _ => ybef P2b B2c
           | |- Y1BEF L3 _ _ => ybef P3b B3c | |- Y1BEF L4 _ _ => ybef P4b B4c end).
         all: try (lazymatch goal with |- Y1OPS _ _ _ _ _ => exact OPS end).
         all: try lia. }
  Qed.

End Y4S1.
End CANSEC1.
