From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require PropExec InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_x4s
  RF_huf_y4s_iface RF_huf_y4s31_kit RF_huf_y4s1 RF_huf_x2t_top_kit RF_huf_y4s1c.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Section Y4S1T.
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
        lazymatch goal with |- evt _ _ (MS _ _ (if ?c then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
          let oa := eval vm_compute in (a - PY4_BODY) in let ob := eval vm_compute in (b - PY4_BODY) in
          idtac
        | |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) => idtac
        end;
        let H := fresh "B" in if_cases H; zify_cond H;
        try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
               lazymatch eval vm_compute in (u_is_chk usegs pc) with
               | true => unorm H; solve [zrefute H | unfold Y1H in *; zrefute H]
               end end)
    end.


  Ltac srd8 SRC :=
    lazymatch type of SRC with bytes_at usegs ?mm ?S ?bs =>
      let E := u_mem_addr in
      let R := fresh "R8" in
      pose proof (bytes_at_read usegs mm S bs (E - S) 8 SRC ltac:(unfold Y1H in *; lia) ltac:(rewrite ?length_map; unfold zlen, Y1H in *; lia)) as R;
      replace (S + (E - S)) with E in R by lia end.

  Ltac srd1 SRC :=
    lazymatch type of SRC with bytes_at usegs ?mm ?S ?bs =>
      let E := u_mem_addr in
      let R := fresh "R1" in
      pose proof (bytes_at_read usegs mm S bs (E - S) 1 SRC ltac:(unfold Y1H in *; lia) ltac:(rewrite ?length_map; unfold zlen, Y1H in *; lia)) as R;
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
  Ltac ustep2 stops TCK OUT LB SRC :=
    try unorm3; try unorm2;
    first [ ustep1 stops TCK OUT LB
          | lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              lazymatch eval vm_compute in (orb (existsb (Z.eqb pc) stops) (u_is_chk usegs pc)) with
              | false => first [ srd8 SRC; zstep | srd1 SRC; zstep ] end end ].


  Lemma u_nn1 : forall a b, 0 <= a -> 0 <= b -> a <> b ->
    Z.lxor (Z.b2z true) (Z.b2z (Z.lxor a b <? 1)) = 1.
  Proof.
    intros a b A B N.
    assert (X0 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
    assert (X1 : Z.lxor a b <> 0) by (intro E; apply Z.lxor_eq in E; lia).
    replace (Z.lxor a b <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.

  Ltac srd1p SRC :=
    lazymatch type of SRC with bytes_at usegs ?mm ?S ?bs =>
      let E := u_mem_addr in
      let R := fresh "R1" in
      let NB := fresh "NB" in
      assert (NB : (Z.to_nat (E - S) + 1 <= length bs)%nat)
        by (apply Nat2Z.inj_le; rewrite Nat2Z.inj_add, Z2Nat.id by lia; rewrite ?length_map; unfold zlen in *; lia);
      pose proof (bytes_at_read usegs mm S bs (E - S) 1 SRC ltac:(lia) NB) as R; clear NB;
      replace (S + (E - S)) with E in R by lia end.

  Ltac r2gen :=
    repeat (match goal with |- context [Z.lor ?a ?b] =>
              lazymatch a with context [Znth] =>
                let cw := fresh "cw" in set (cw := Z.lor a b) in *; clearbody cw end end).

  Ltac r2step stops TCK OUT LB SRC :=
    try unorm3; try unorm2; r2gen;
    first [ ustep1 stops TCK OUT LB
          | lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              lazymatch eval vm_compute in (orb (existsb (Z.eqb pc) stops) (u_is_chk usegs pc)) with
              | false => first [ usrc SRC; zstep | srd1p SRC; zstep | srd8 SRC; zstep ] end end ].

  Ltac r2chk := try (lazymatch goal with B : Z.lxor (Z.b2z true) (Z.b2z (Z.lxor ?a ?b <? 1)) = 0 |- _ =>
           solve [exfalso; rewrite u_nn1 in B by (first [lia | apply Z.div_pos; lia | intro; lia]); lia] end).

  Notation Y1C2' Q0 := (Y1C2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG Q0).
  Notation Y1C3' Q0 := (Y1C3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG Q0).


  Lemma y4s1_r2 : forall Q0, Y1C3' Q0 -> Y1C2' Q0.
  Proof using All.
    intros Q0 K3. unfold Y1C2.
    intros o1 o2 o3 o4 l1 l2 l3 l4 b1 b2 b3 b4 p1 p2 p3 p4 st1 c1 c2 c3 c4 mm j0 jp1 jp2 jp3 jp4 xs0 xs8 xs10 xt5
      FR0 A1 E2 E3 E4 P28 QQ L1r L2r L3r L4r O1a O2a O3a O4a OPS OLIM C1 C2 C3 C4.
    y4open FR0.
    assert (D8 : 8 <= DST) by (apply DP; lia).
    destruct E2 as (P2a & P2b & B2r & B2c).
    assert (P2c : p2 + 8 <= L2) by (destruct P2b; lia). clear P2b.
    assert (B2u : b2 <= 56) by (apply B2c; lia). clear B2c.
    unfold PY4_BODY.
    all: do 48 (try (r2step [PY4_BODY + 2516; PY4_BODY + 700; PY4_BODY + 2708; PY4_BODY + 2904; PY4_BODY + 3044] TCK OUT LB SRC); r2chk).
    all: assert (EB : Z.land b2 7 = b2 mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity);
         rewrite ?EB in *; clear EB.
    all: assert (EP : SS + O2 + p2 - b2 / 8 = SS + O2 + (p2 - b2 / 8)) by lia; rewrite ?EP in *; clear EP.
    all: lazymatch goal with H : rw_cells _ _ (SP + -696) (C8 (Z_to_bv 64 ?c) :: _) |- _ =>
           rewrite <- (Z_to_bv_mod64 c) in *;
           eapply (K3 o1 o2 o3 o4 l1 l2 l3 l4 b1 (b2 mod 8) b3 b4 p1 (p2 - b2 / 8) p3 p4 st1 0 c1 (c mod 2^64) c3 c4 p2) end.
    all: first [ solve [unfold Y4F, SPLB, BD4; upack] | solve [unfold Y1AFT, Y1BEF in *; lia]
               | solve [apply Z.mod_pos_bound; lia] | lia ].
  Qed.
End Y4S1T.
End CANSEC1.
