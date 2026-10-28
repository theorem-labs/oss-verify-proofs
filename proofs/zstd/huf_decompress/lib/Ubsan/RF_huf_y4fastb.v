From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface RF_huf_y4s_iface RF_huf_y4body_kit RF_huf_y4fastt.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation Y4_M10 := 14757395258967641293 (only parsing).
Notation Y4_M7 := 2635249153387078803 (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Section Y4FASTB.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Hypothesis TOK : x2_table_ok cells 11.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^11)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 8192.
  Hypothesis D8 : 8 <= DST.
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis SG : 3 * seg < dcap.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 8192 <= lo.
  Hypothesis DJ1 : DT + 4 + 8192 <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.
  Hypothesis DTA : DT mod 4 = 0.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation Y4M := (RF_huf_y4s_iface.Y4M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs).
  Notation SPS4 := (RF_huf_y4s_iface.SPS4 DST dcap SS DT src).
  Notation SPSL w0 w8 := (SPS4 w0 w8 Y4_M10 Y4_M7 (DST + dcap) SS (DST + 3 * seg) (DST + 2 * seg) (DST + seg)).
  Notation W4 a b c d := [Z_to_bv 64 a; Z_to_bv 64 b; Z_to_bv 64 c; Z_to_bv 64 d].

  Notation HO mm b0 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31 :=
    (MS (mkR (Z_to_bv 64 (-25)) (Z_to_bv 64 (SP + -512)) gp tp x5 (Z_to_bv 64 OP3) x7 x8 (Z_to_bv 64 IP2) x10
             (Z_to_bv 64 IP3) x12 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 IP0) (Z_to_bv 64 OP1) (Z_to_bv 64 OP2)
             (Z_to_bv 64 (SP + -168)) (Z_to_bv 64 OP0) (Z_to_bv 64 IP1) x20 x21 b0 (Z_to_bv 64 (SP + -136)) x24
             (Z_to_bv 64 (-16)) x26 x27 x28 x29 (Z_to_bv 64 (- (DT + 4) - 1)) x31)
        F (Z_to_bv 64 0x15cbc) fc None mm (seg_rom usegs)).

  Notation HI mm b0 b1 b2 b3 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 OL x9 x11 x14 x19 x21 x24 x28 :=
    (MS (mkR (Z_to_bv 64 (-25)) (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 Y4_FT0) (Z_to_bv 64 OP3) (Z_to_bv 64 IP0) b1 x9
             (Z_to_bv 64 OL) x11 (Z_to_bv 64 Y4_FA2) (Z_to_bv 64 (DT + 4)) x14 (Z_to_bv 64 OP1) (Z_to_bv 64 OP2)
             (Z_to_bv 64 (SP + -168)) (Z_to_bv 64 OP0) x19 (Z_to_bv 64 IP1) x21 b0 (Z_to_bv 64 (SP + -136)) x24
             (Z_to_bv 64 (-16)) b3 (Z_to_bv 64 IP2) x28 b2 (Z_to_bv 64 (- (DT + 4) - 1)) (Z_to_bv 64 IP3))
        F (Z_to_bv 64 Y4_IH) fc None mm (seg_rom usegs)).

  Hypothesis WB : forall mm ws (w0 w8 w64 w72 w80 w88 w96 w104 w112 : Z) (b0 b1 b2 b3 : word)
                         IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 IE0 IE1 IE2 IE3
                         (x1 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    Y4M mm (SPS4 w0 w8 w64 w72 w80 w88 w96 w104 w112) ws (W4 OP0 OP1 OP2 OP3) (W4 IP0 IP1 IP2 IP3) [b0; b1; b2; b3] ->
    nth_error ws 13 = Some (Z_to_bv 64 SS) ->
    nth_error ws 15 = Some (Z_to_bv 64 IE0) -> nth_error ws 16 = Some (Z_to_bv 64 IE1) ->
    nth_error ws 17 = Some (Z_to_bv 64 IE2) -> nth_error ws 18 = Some (Z_to_bv 64 IE3) ->
    SS <= IE0 <= SS + n -> SS <= IE1 <= SS + n -> SS <= IE2 <= SS + n -> SS <= IE3 <= SS + n ->
    SS <= IP0 -> IP0 + 8 <= SS + n -> SS <= IP1 -> IP1 + 8 <= SS + n ->
    SS <= IP2 -> IP2 + 8 <= SS + n -> SS <= IP3 -> IP3 + 8 <= SS + n ->
    DST <= OP0 <= DST + seg -> DST <= OP1 <= DST + 2 * seg -> DST <= OP2 <= DST + 3 * seg -> DST <= OP3 <= DST + dcap ->
    bv_unsigned b0 <> 0 -> bv_unsigned b1 <> 0 -> bv_unsigned b2 <> 0 -> bv_unsigned b3 <> 0 ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 Y4_FT0) x6 x7 x8 x9 x10 x11 (Z_to_bv 64 Y4_FA2)
                           x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1667c) fc None mm (seg_rom usegs)).

  Hypothesis MH10 : forall x, 0 <= x < 2^64 ->
  ((x * 14757395258967641293) ≫ 64 mod 18446744073709551616) ≫ 3 = x / 10.
  Hypothesis MH7 : forall x, 0 <= x < 2^64 ->
  ((((x - (x * 2635249153387078803) ≫ 64 mod 18446744073709551616) mod 18446744073709551616) ≫ 1
     + (x * 2635249153387078803) ≫ 64) mod 18446744073709551616) ≫ 2 = x / 7.

  Hypothesis INNER : forall (r : nat) mm ws (w0 w8 : Z) (b0 b1 b2 b3 : word) IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 OL
                          (ops ips bts : list word) (x9 x11 x14 x19 x21 x24 x28 : word),
    Y4M mm (SPSL w0 w8) ws ops ips bts ->
    (1 <= r)%nat -> OL <= OP3 + 5 * Z.of_nat r -> OP3 < OL ->
    OP0 + 10 * Z.of_nat r <= DST + seg -> OP1 + 10 * Z.of_nat r <= DST + 2 * seg ->
    OP2 + 10 * Z.of_nat r <= DST + 3 * seg -> OP3 + 10 * Z.of_nat r <= DST + dcap ->
    DST <= OP0 -> DST <= OP1 -> DST <= OP2 -> DST <= OP3 ->
    SS + 7 * Z.of_nat r <= IP0 -> IP0 + 8 <= SS + n -> SS + 7 * Z.of_nat r <= IP1 -> IP1 + 8 <= SS + n ->
    SS + 7 * Z.of_nat r <= IP2 -> IP2 + 8 <= SS + n -> SS + 7 * Z.of_nat r <= IP3 -> IP3 + 8 <= SS + n ->
    bv_unsigned b0 mod 512 <> 0 -> bv_unsigned b1 mod 512 <> 0 -> bv_unsigned b2 mod 512 <> 0 -> bv_unsigned b3 mod 512 <> 0 ->
    (forall mm' (b0' b1' b2' b3' : word) IP0' IP1' IP2' IP3' OP0' OP1' OP2' OP3'
            (x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31 : word),
       Y4M mm' (SPSL w0 w8) ws (W4 OP0' OP1' OP2' OP3') (W4 IP0' IP1' IP2' IP3') [b0'; b1'; b2'; b3'] ->
       SS <= IP0' -> IP0' + 8 <= SS + n -> SS <= IP1' -> IP1' + 8 <= SS + n ->
       SS <= IP2' -> IP2' + 8 <= SS + n -> SS <= IP3' -> IP3' + 8 <= SS + n ->
       DST <= OP0' <= DST + seg -> DST <= OP1' <= DST + 2 * seg -> DST <= OP2' <= DST + 3 * seg ->
       OL <= OP3' <= DST + dcap ->
       bv_unsigned b0' mod 512 <> 0 -> bv_unsigned b1' mod 512 <> 0 ->
       bv_unsigned b2' mod 512 <> 0 -> bv_unsigned b3' mod 512 <> 0 ->
       evt usegs POST (HO mm' b0' IP0' IP1' IP2' IP3' OP0' OP1' OP2' OP3' x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31)) ->
    evt usegs POST (HI mm b0 b1 b2 b3 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 OL x9 x11 x14 x19 x21 x24 x28).


  Notation XT l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT lo src cells cbs
                     TOK ECB LCB D8 DC SG DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47 DTA WB MH10 MH7 INNER)
                     (only parsing).

  Ltac y4b_zl := repeat match goal with |- context [Z.of_nat (length ?l)] => change (Z.of_nat (length l)) with (zlen l) end.
  Ltac y4b_ltb := repeat match goal with |- context [Z.ltb ?a ?b] =>
    first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; lia)
          | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; lia) ] end.
  Ltac y4b_lit := repeat match goal with
    | |- context [Z.b2z ?x] => let v := eval vm_compute in (Z.b2z x) in is_Zlit v; change (Z.b2z x) with v
    | |- context [Z.lxor ?x ?y] => let v := eval vm_compute in (Z.lxor x y) in is_Zlit v; change (Z.lxor x y) with v
    end.
  Ltac y4b_csolve :=
    unfold bv_ltu, bv_leu, bv_eqb; rewrite ?Z.shiftl_mul_pow2 by lia; y4b_ltb; y4b_lit;
    rewrite ?unsigned_lit by lia; solve_cond_rec.
  Ltac y4b_cond :=
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
      let C := fresh "C" in
      first [ assert (C : c = true) by y4b_csolve; replace (if c then a else b) with a by (rewrite C; reflexivity)
            | assert (C : c = false) by y4b_csolve; replace (if c then a else b) with b by (rewrite C; reflexivity) ];
      clear C
    end.
  Ltac y4b_ucond C := unfold bv_ltu, bv_leu, bv_eqb in C; rewrite ?Z.shiftl_mul_pow2 in C by lia;
    rewrite ?unsigned_lit in C by lia; zify_bool C.
  Tactic Notation "y4b_split" ident(C) :=
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
      destruct (Bool.bool_dec c true) as [C|C];
      [ replace (if c then a else b) with a by (rewrite C; reflexivity)
      | apply Bool.not_true_is_false in C; replace (if c then a else b) with b by (rewrite C; reflexivity) ]
    end.
  Ltac y4b_lim A :=
    lazymatch A with
    | (bv_unsigned sp + -512) => constr:(128) | (bv_unsigned sp + -384) => constr:(152)
    | (bv_unsigned sp + -200) => constr:(32) | (bv_unsigned sp + -168) => constr:(32)
    | (bv_unsigned sp + -136) => constr:(32) | _ => constr:(0) end.
  Ltac y4b_rd :=
    let E0 := cur_mem_addr in let E := addr_expr E0 in
    match goal with W : u64arr usegs ?mm ?A ?ws |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let k := addr_diff E A in let lim := y4b_lim A in
      let ok := eval vm_compute in (Z.leb 0 k && Z.ltb k lim && Z.eqb (Z.modulo k 8) 0)%bool in
      lazymatch ok with true =>
        let i := eval vm_compute in (k / 8) in
        pose proof (u64arr_read usegs mm A ws i _ _ W ltac:(first [reflexivity | eassumption]) ltac:(lia) ltac:(unfold wa; f_equal; lia))
      end end.
  Ltac y4b_go stop :=
    repeat (lazymatch goal with
            | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
            | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                let b := eval vm_compute in (orb (Z.eqb pc stop) (orb (Z.eqb pc 0x1667c) (orb (Z.eqb pc Y4_IH)
                                               (RF_huf_y4body_kit.y4k_is_chk usegs pc)))) in
                lazymatch b with true => fail | false => first [zstep | (y4b_rd; zstep)] end
            end).
  Ltac y4b_mh := repeat match goal with
    | |- context [((?x * ?m) ≫ 64 mod ?p) ≫ 3] => rewrite (MH10 x) by lia
    | |- context [(?x * ?m) ≫ 64] => rewrite (MH7 x) by lia
    end.
  Ltac y4b_show := lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let o := eval vm_compute in (pc - 0x15a6c) in idtac "PC_UPLUS" o
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => idtac "COND" c
    | |- _ => idtac "OTHER" end.

  Lemma y4_outer_b : forall (fuel : nat) mm ws (w0 w8 : Z) (b0 b1 b2 b3 : word) IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3
                          IE0 IE1 IE2 IE3 (x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31 : word),
    Y4M mm (SPSL w0 w8) ws (W4 OP0 OP1 OP2 OP3) (W4 IP0 IP1 IP2 IP3) [b0; b1; b2; b3] ->
    nth_error ws 13 = Some (Z_to_bv 64 SS) ->
    nth_error ws 15 = Some (Z_to_bv 64 IE0) -> nth_error ws 16 = Some (Z_to_bv 64 IE1) ->
    nth_error ws 17 = Some (Z_to_bv 64 IE2) -> nth_error ws 18 = Some (Z_to_bv 64 IE3) ->
    SS <= IE0 <= SS + n -> SS <= IE1 <= SS + n -> SS <= IE2 <= SS + n -> SS <= IE3 <= SS + n ->
    DST + dcap - OP3 < 5 * Z.of_nat fuel ->
    SS <= IP0 -> IP0 + 8 <= SS + n -> SS <= IP1 -> IP1 + 8 <= SS + n ->
    SS <= IP2 -> IP2 + 8 <= SS + n -> SS <= IP3 -> IP3 + 8 <= SS + n ->
    DST <= OP0 <= DST + seg -> DST <= OP1 <= DST + 2 * seg -> DST <= OP2 <= DST + 3 * seg -> DST <= OP3 <= DST + dcap ->
    bv_unsigned b0 mod 512 <> 0 -> bv_unsigned b1 mod 512 <> 0 -> bv_unsigned b2 mod 512 <> 0 -> bv_unsigned b3 mod 512 <> 0 ->
    evt usegs POST (HO mm b0 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31).
  Proof using All.
    induction fuel as [|fuel IH];
      intros mm ws w0 w8 b0 b1 b2 b3 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 IE0 IE1 IE2 IE3
        x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31
        Y W13 E15 E16 E17 E18 IB0 IB1 IB2 IB3 FU I0 I0' I1 I1' I2 I2' I3 I3' O0 O1 O2 O3 M0 M1 M2 M3; [lia|].
    pose proof Y as Y0.
    destruct Y as ([buf [BUFA LBUF]] & SRCB & CBSB & STK & SPSA & LSPS & WSA & LWS & [jo JO]
                   & OPA & LOP & IPA & LIP & BTA & LBT & FR & MI & MU & WM).
    unfold RF_huf_y4s_iface.SPS4 in SPSA. cbn [map] in SPSA.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (SEG0 : 0 <= seg) by (apply Z.div_pos; lia).
    y4b_go 0x15da4. y4b_mh.
    all: repeat (y4b_go 0x15da4; y4b_mh; first [y4b_cond | let C := fresh "C" in y4b_split C; y4b_ucond C]).
    all: lazymatch goal with |- context [Z_to_bv 64 (?o + ?q + ?q ≪ 2)] =>
           replace (o + q + q ≪ 2) with (o + 5 * q) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 2) with 4; lia);
           eapply ((XT RF_huf_y4fastt.y4_tail824) q mm ws w0 w8 b0 b1 b2 b3 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 IE0 IE1 IE2 IE3)
         end.
    all: first [exact Y0 | eassumption | lia | idtac].
    all: intros; eapply IH; try eassumption; lia.
  Qed.

End Y4FASTB.
End CANSEC1.

