From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require PropExec InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_x4s
  RF_huf_y4s_iface RF_huf_y4s31_kit RF_huf_y4s1 RF_huf_x2t_top_kit.
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

  (* [comment removed for export] *)
  Notation SPLL w64 k4 k2 p2 k1 j0 :=
    (SPLB desc (DST + 3 * SEG) dcap (SS + O4 + 8) (SS + O3 + 8) (SS + O2 + 8) (DST + dcap - 7) w64 k4 k2
          (SS + O2 + p2) (DST + SEG) (DST + 2 * SEG) k1 (DST + dcap) (DT + 4) j0).
  Notation SPLX v24 v32 v40 v48 v64 v72 v80 v88 v112 j0 :=
    (SPLB desc (DST + 3 * SEG) v24 v32 v40 v48 (DST + dcap - 7) v64 v72 v80 v88
          (DST + SEG) (DST + 2 * SEG) v112 (DST + dcap) (DT + 4) j0).

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
        lazymatch goal with |- evt _ _ (MS _ _ (if ?c then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
          let oa := eval vm_compute in (a - PY4_BODY) in let ob := eval vm_compute in (b - PY4_BODY) in
          idtac
        | |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) => idtac
        end;
        let H := fresh "B" in if_cases H; zify_cond H;
        try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
               lazymatch eval vm_compute in (u_is_chk usegs pc) with
               | true => unorm H; try (apply u_lx1 in H; [ | lia | apply Z.div_pos; lia ]); solve [zrefute H | unfold Y1H in *; zrefute H]
               end end)
    end.



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
  Ltac srcfirst stops SRC :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch eval vm_compute in (orb (existsb (Z.eqb pc) stops) (u_is_chk usegs pc)) with
      | false => let E := u_mem_addr in
                 lazymatch E with context [SS] => first [ srd8 SRC; zstep | srd1 SRC; zstep ] end
      end end.
  Ltac ustep2 stops TCK OUT LB SRC :=
    try unorm3; try unorm2;
    first [ srcfirst stops SRC
          | ustep1 stops TCK OUT LB
          | lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              lazymatch eval vm_compute in (orb (existsb (Z.eqb pc) stops) (u_is_chk usegs pc)) with
              | false => first [ srd8 SRC; zstep | srd1 SRC; zstep ] end end ].


  Notation BDS c b p O jp := (BD4 c b (SS + O + p) (SS + O) jp).
  Notation ARGS l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG) (only parsing).
  Notation Y1HEAD' Q0 := (ARGS Y1HEAD Q0).
  Notation Y1EXIT' := (ARGS Y1EXIT).

  Definition Y1C9 (Q0 : Z) : Prop :=
    forall o1 o2 o3 o4 l1 l2 l3 l4 b1 b2 b3 b4 p1 p2 p3 p4 st1 st2 st3 st4 c1 c2 c3 c4 mm j0 jp1 jp2 jp3 jp4
           (xt2 xs0 xs8 xt5 : word),
    Q0 < o4 + l4 - DST ->
    Y4F' mm (SPLL st1 c4 c2 p2 c1 j0) (BDS c4 b4 p4 O4 jp4) (BDS c3 b3 p3 O3 jp3) (BDS c2 b2 p2 O2 jp2) (BDS c1 b1 p1 6 jp1) ->
    Y1AFT L1 p1 b1 st1 -> Y1AFT L2 p2 b2 st2 -> Y1AFT L3 p3 b3 st3 -> Y1AFT L4 p4 b4 st4 ->
    DST <= o1 -> DST <= o2 -> DST <= o3 -> DST <= o4 ->
    Y1OPS SEG (o1 + l1 - DST) (o2 + l2 - DST) (o3 + l3 - DST) (o4 + l4 - DST) -> o4 + l4 <= DST + dcap ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -912)) gp tp (Z_to_bv 64 (SS + O3 + p3)) (Z_to_bv 64 (DT + 4))
                            xt2 xs0 (Z_to_bv 64 b1) (Z_to_bv 64 l1) (Z_to_bv 64 o1) (Z_to_bv 64 l2) (Z_to_bv 64 l3) (Z_to_bv 64 st2)
                            (Z_to_bv 64 (2^61)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 o4) (Z_to_bv 64 c3)
                            (Z_to_bv 64 o3) (Z_to_bv 64 st3) (Z_to_bv 64 l4) (Z_to_bv 64 b3) xs8 (Z_to_bv 64 b4) (Z_to_bv 64 st4) (Z_to_bv 64 o2)
                            (Z_to_bv 64 (SS + O4 + p4)) (Z_to_bv 64 (SS + 6 + p1)) xt5 (Z_to_bv 64 (DST + dcap)))
                        F (Z_to_bv 64 (PY4_BODY + 2904)) fc None mm (seg_rom usegs)).

  Ltac c9pack := unfold Y4F, SPLB, BD4; upack.
  Ltac c9head HD :=
    lazymatch goal with B : Z.lor (Z.lor ?s1 ?s2) (Z.lor ?s3 ?s4) = 0 |- _ =>
      apply Z.lor_eq_0_iff in B; destruct B as (B12 & B34);
      apply Z.lor_eq_0_iff in B12; apply Z.lor_eq_0_iff in B34;
      destruct B12 as (E1 & E2); destruct B34 as (E3 & E4); subst s1 s2 s3 s4 end;
    unfold Y1HEAD in HD; eapply HD;
    [ lia | c9pack | eassumption | lia
    | apply y1_aft_hdi; eassumption | apply y1_aft_hdi; eassumption | apply y1_aft_hdi; eassumption | apply y1_aft_hdi; eassumption
    | lia | lia | lia | lia | lia ].
  Ltac c9exit EX :=
    unfold Y1EXIT in EX; eapply EX;
    [ c9pack | lia | lia | lia | lia | eassumption | eassumption | eassumption | eassumption | lia | lia | lia | lia ].

  Lemma y4s1_c9 : forall Q0, Y1HEAD' Q0 -> Y1EXIT' -> Y1C9 Q0.
  Proof using All.
    intros Q0 HD EX. unfold Y1C9.
    intros o1 o2 o3 o4 l1 l2 l3 l4 b1 b2 b3 b4 p1 p2 p3 p4 st1 st2 st3 st4 c1 c2 c3 c4 mm j0 jp1 jp2 jp3 jp4 xt2 xs0 xs8 xt5
      QQ FR0 A1 A2 A3 A4 O1a O2a O3a O4a OPS OLIM C1 C2 C3 C4.
    assert (S1 : st1 = 0 \/ st1 = 3) by (unfold Y1AFT in A1; lia).
    assert (S2 : st2 = 0 \/ st2 = 3) by (unfold Y1AFT in A2; lia).
    assert (S3 : st3 = 0 \/ st3 = 3) by (unfold Y1AFT in A3; lia).
    assert (S4 : st4 = 0 \/ st4 = 3) by (unfold Y1AFT in A4; lia).
    assert (S1r : 0 <= st1 <= 3) by lia. assert (S2r : 0 <= st2 <= 3) by lia.
    assert (S3r : 0 <= st3 <= 3) by lia. assert (S4r : 0 <= st4 <= 3) by lia.
    change (Y1H (st1 = 0 \/ st1 = 3)) in S1. change (Y1H (st2 = 0 \/ st2 = 3)) in S2.
    change (Y1H (st3 = 0 \/ st3 = 3)) in S3. change (Y1H (st4 = 0 \/ st4 = 3)) in S4.
    assert (OL : 0 <= o1 + l1 - DST <= dcap /\ 0 <= o2 + l2 - DST <= dcap /\ 0 <= o3 + l3 - DST <= dcap /\ 3 * SEG <= o4 + l4 - DST)
      by (unfold Y1OPS in OPS; destruct HQ as (? & ? & ?); lia).
    y4open FR0.
    assert (D8 : 8 <= DST) by (apply DP; lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    unfold PY4_BODY.
    all: do 15 (try (ustep2 [PY4_BODY + 700; PY4_BODY + 3044] TCK OUT LB SRC)).
    all: replace (o1 + l1) with (DST + (o1 + l1 - DST)) by lia; replace (o2 + l2) with (DST + (o2 + l2 - DST)) by lia;
         replace (o3 + l3) with (DST + (o3 + l3 - DST)) by lia; replace (o4 + l4) with (DST + (o4 + l4 - DST)) by lia.
    all: first [ c9head HD | c9exit EX ].
  Qed.

  Definition Y1C4 (Q0 : Z) : Prop :=
    forall o1 o2 o3 o4 l1 l2 l3 l4 b1 b2 b3 b4 p1 p2 p3 p4 st1 st2 st3 c1 c2 c3 c4 mm j0 jp1 jp2 jp3 jp4
           (xt2 xs0 xs8 xs10 xt5 : word),
    Q0 < o4 + l4 - DST ->
    Y4F' mm (SPLL st1 c4 c2 p2 c1 j0) (BDS c4 b4 p4 O4 jp4) (BDS c3 b3 p3 O3 jp3) (BDS c2 b2 p2 O2 jp2) (BDS c1 b1 p1 6 jp1) ->
    Y1AFT L1 p1 b1 st1 -> Y1AFT L2 p2 b2 st2 -> Y1AFT L3 p3 b3 st3 -> Y1BEF L4 p4 b4 -> 8 <= p4 ->
    DST <= o1 -> DST <= o2 -> DST <= o3 -> DST <= o4 ->
    Y1OPS SEG (o1 + l1 - DST) (o2 + l2 - DST) (o3 + l3 - DST) (o4 + l4 - DST) -> o4 + l4 <= DST + dcap ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -912)) gp tp (Z_to_bv 64 (SS + O3 + p3)) (Z_to_bv 64 (DT + 4))
                            xt2 xs0 (Z_to_bv 64 b1) (Z_to_bv 64 l1) (Z_to_bv 64 o1) (Z_to_bv 64 l2) (Z_to_bv 64 l3) (Z_to_bv 64 st2)
                            (Z_to_bv 64 (2^61)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 o4) (Z_to_bv 64 c3)
                            (Z_to_bv 64 o3) (Z_to_bv 64 st3) (Z_to_bv 64 l4) (Z_to_bv 64 b3) xs8 (Z_to_bv 64 b4) xs10 (Z_to_bv 64 o2)
                            (Z_to_bv 64 (SS + O4 + p4)) (Z_to_bv 64 (SS + 6 + p1)) xt5 (Z_to_bv 64 (DST + dcap)))
                        F (Z_to_bv 64 (PY4_BODY + 2708)) fc None mm (seg_rom usegs)).

  Ltac srdx n SRC :=
    lazymatch type of SRC with bytes_at usegs ?mm ?S ?bs =>
      let E := u_mem_addr in
      let K1 := fresh "K" in let K2 := fresh "K" in let R := fresh "R" in
      assert (K1 : 0 <= E - S) by (unfold Y1H in *; lia);
      assert (K2 : (Z.to_nat (E - S) + n <= length bs)%nat) by (rewrite ?length_map; unfold Y1H in *; lia);
      pose proof (bytes_at_read usegs mm S bs (E - S) n SRC K1 K2) as R;
      replace (S + (E - S)) with E in R by lia; clear K1 K2 end.
  Ltac ustep2x stops TCK OUT LB SRC :=
    try unorm3; try unorm2;
    first [ lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              lazymatch eval vm_compute in (orb (existsb (Z.eqb pc) stops) (u_is_chk usegs pc)) with
              | false => let E := u_mem_addr in
                         lazymatch E with context [SS] => first [ srdx 8%nat SRC; zstep | srdx 1%nat SRC; zstep ] end
              end end
          | ustep1 stops TCK OUT LB ].
  Ltac c4gen := repeat match goal with |- context [Z_to_bv 64 ?E] =>
      lazymatch E with context [le_bytes_to_word] =>
        let w := fresh "cw" in let EW := fresh "EW" in remember (Z_to_bv 64 E) as w eqn:EW; clear EW end end.

  Lemma y4s1_c4 : forall Q0, Y1HEAD' Q0 -> Y1EXIT' -> Y1C4 Q0.
  Proof using All.
    intros Q0 HD EX. unfold Y1C4.
    intros o1 o2 o3 o4 l1 l2 l3 l4 b1 b2 b3 b4 p1 p2 p3 p4 st1 st2 st3 c1 c2 c3 c4 mm j0 jp1 jp2 jp3 jp4 xt2 xs0 xs8 xs10 xt5
      QQ FR0 A1 A2 A3 E4 P48 O1a O2a O3a O4a OPS OLIM C1 C2 C3 C4.
    y4open FR0.
    assert (D8 : 8 <= DST) by (apply DP; lia).
    destruct E4 as (P4a & P4b & B4r & B4c).
    assert (P4c : p4 + 8 <= L4) by (destruct P4b; lia). clear P4b.
    assert (B4u : b4 <= 56) by (apply B4c; lia). clear B4c.
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    unfold PY4_BODY.
    all: repeat (ustep2x [PY4_BODY + 2904; PY4_BODY + 700; PY4_BODY + 3044] TCK OUT LB SRC; try c4gen).
    all: assert (EB : Z.land b4 7 = b4 mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity);
         rewrite ?EB in *; clear EB.
    all: assert (EP : SS + O4 + p4 - b4 / 8 = SS + O4 + (p4 - b4 / 8)) by lia; rewrite ?EP in *; clear EP.
    all: lazymatch goal with H : rw_cells _ _ (SP + -776) (C8 ?w :: _) |- _ =>
           rewrite <- (Z_to_bv_lit_self w) in *;
           pose proof (bv_unsigned_in_range 64 w) as RW; unfold bv_modulus in RW; cbn in RW;
           eapply (y4s1_c9 Q0 HD EX o1 o2 o3 o4 l1 l2 l3 l4 b1 b2 b3 (b4 mod 8) p1 p2 p3 (p4 - b4 / 8) st1 st2 st3 0
                     c1 c2 c3 (bv_unsigned w)) end.
    all: first [ eassumption | solve [unfold Y4F, SPLB, BD4; upack] | solve [unfold Y1AFT, Y1BEF in *; lia] | lia ].
  Qed.
End Y4S1.
End CANSEC1.
