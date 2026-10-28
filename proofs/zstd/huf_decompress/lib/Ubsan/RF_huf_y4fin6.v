From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image PropExec.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_y4s_iface RF_huf_y4fin.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Section Y4F6.
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
  Hypothesis DTA : DT mod 4 = 0.
  Hypothesis CBL : DT + 4 + 8192 <= lo.
  Hypothesis DJ1 : DT + 4 + 8192 <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation Y4M := (RF_huf_y4s_iface.Y4M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs).
  Notation SPS4 := (RF_huf_y4s_iface.SPS4 DST dcap SS DT src).

  Notation YF l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT lo src cells cbs
                      TOK ECB LCB D8 DC SG DL S0 SL NSM BYS DT0 DTA CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).

  Notation NDT := (Z.lxor (DT + 4) 18446744073709551615).
  Notation KH pc mm k prev x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 prev) x9 (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 64)
             (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation W4 a b c d := [Z_to_bv 64 a; Z_to_bv 64 b; Z_to_bv 64 c; Z_to_bv 64 d].

  Lemma y4f_pre : forall mm ws (w0 w8 w64 w72 w80 w88 w96 w104 w112 : Z) (b0 b1 b2 b3 : word)
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
    (forall mm' (y1 y7 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31 : word),
       Y4M mm' (SPS4 w0 w8 w64 w72 w80 w88 w96 w104 w112)
         (W4 IP0 IP1 IP2 IP3 ++ W4 OP0 OP1 OP2 OP3 ++ [b0; b1; b2; b3] ++ skipn 12 ws)
         (W4 OP0 OP1 OP2 OP3) (W4 IP0 IP1 IP2 IP3) [b0; b1; b2; b3] ->
       evt usegs POST (KH 0x16720 mm' 0 DST y1 y7 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31)) ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 0xfdb8) x6 x7 x8 x9 x10 x11 (Z_to_bv 64 0x104a0)
                           x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1667c) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until x31. intros YM WS13 WS15 WS16 WS17 WS18 IE0B IE1B IE2B IE3B
      P0a P0b P1a P1b P2a P2b P3a P3b O0 O1 O2 O3 B0 B1 B2 B3 CONT.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct YM as ((buf & ARR & LB) & SRC & CBR & ST & SPA & SPL & WSA & WSL & (jo & JO) & OPA & OPL & IPA & IPL & BTA & BTL & FR & MI & MU & WM).
    apply y4_C8_of_u64arr in SPA, WSA, OPA, IPA, BTA.
    destruct ws as [|w_0 [|w_1 [|w_2 [|w_3 [|w_4 [|w_5 [|w_6 [|w_7 [|w_8 [|w_9 [|w_10 [|w_11 [|w_12 [|w_13 [|w_14 [|w_15 [|w_16 [|w_17 [|w_18 [|? ?]]]]]]]]]]]]]]]]]]]];
      cbn in WSL; try discriminate WSL.
    cbn in WS13, WS15, WS16, WS17, WS18. injection WS13 as ->. injection WS15 as ->. injection WS16 as ->.
    injection WS17 as ->. injection WS18 as ->.
    unfold RF_huf_y4s_iface.SPS4 in SPA. cbn [map] in SPA, WSA, OPA, IPA, BTA.
    repeat (lazymatch goal with
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
          let d := eval vm_compute in (z =? PHUF_DX2_4X + 3252) in lazymatch d with true => fail | false => zstep end
      | _ => zstep end).
    eapply CONT.
    unfold RF_huf_y4s_iface.Y4M, RF_huf_y4s_iface.SPS4. cbn [map app skipn].
    split; [exists buf; split; eassumption |].
    repeat (split; [first [ eassumption | reflexivity | (apply y4_u64arr_of_C8; cbn [map]; eassumption) | eexists; eassumption ] |]).
    eassumption.
Qed.

  Lemma y4f_be : forall mm k prev sps ws ops ips bts (x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 : word),
    0 <= k < 4 -> DST <= prev <= DST + dcap ->
    Y4M mm sps ws ops ips bts ->
    nth_error sps 6 = Some (Z_to_bv 64 dcap) ->
    (k + 1 < 4 -> forall mm' (y1 y7 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31 : word),
       Y4M mm' sps ws ops ips bts ->
       evt usegs POST (KH 0x16720 mm' (k + 1) prev y1 y7 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31)) ->
    evt usegs POST (KH 0x16d28 mm k prev x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31).
  Proof using All.
    intros until x31. intros KB PB YM SP6 CONT.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (SGP : 0 < seg) by (apply Z.div_str_pos; lia).
    pose proof (YF RF_huf_y4fin.y4m_stk mm sps ws ops ips bts YM) as STK.
    pose proof YM as YM0.
    destruct YM as (BUF & SRC & CBR & ST & SPA & SPL & WSA & WSL & (jo & JO) & OPA & OPL & IPA & IPL & BTA & BTL & FR & MI & MU & WM).
    apply y4_C8_of_u64arr in SPA, WSA, OPA, IPA, BTA.
    destruct sps as [|v_0 [|v_8 [|v_16 [|v_24 [|v_32 [|v_40 [|v_48 [|v_56 [|v_64 [|v_72 [|v_80 [|v_88 [|v_96 [|v_104 [|v_112 [|v_120 [|? ?]]]]]]]]]]]]]]]]];
      cbn in SPL; try discriminate SPL.
    destruct ws as [|w_0 [|w_1 [|w_2 [|w_3 [|w_4 [|w_5 [|w_6 [|w_7 [|w_8 [|w_9 [|w_10 [|w_11 [|w_12 [|w_13 [|w_14 [|w_15 [|w_16 [|w_17 [|w_18 [|? ?]]]]]]]]]]]]]]]]]]]];
      cbn in WSL; try discriminate WSL.
    destruct ops as [|o_0 [|o_1 [|o_2 [|o_3 [|? ?]]]]]; cbn in OPL; try discriminate OPL.
    destruct ips as [|i_0 [|i_1 [|i_2 [|i_3 [|? ?]]]]]; cbn in IPL; try discriminate IPL.
    destruct bts as [|t_0 [|t_1 [|t_2 [|t_3 [|? ?]]]]]; cbn in BTL; try discriminate BTL.
    cbn [map] in SPA, WSA, OPA, IPA, BTA.
    cbn in SP6. injection SP6 as ->.
    repeat (lazymatch goal with
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => let U := fresh "U" in if_cases U; y4br U
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
          let d := eval vm_compute in (orb (z =? PHUF_DX2_4X + 3252) (z =? PHUF_DX2_4X + 4868)) in
          lazymatch d with true => fail | false => zstep end
      | _ => zstep end).
    all: repeat match goal with
      | U : context [Z.eqb _ _] |- _ => y4pbU U
      | U : context [Z.ltb _ _] |- _ => y4pbU U
      | U : context [Z.leb _ _] |- _ => y4pbU U end.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
          let d := eval vm_compute in (z =? PHUF_DX2_4X + 4868) in
          lazymatch d with
          | true => eapply (YF RF_huf_y4fin.y4_epi); eassumption
          | false => eapply CONT; [lia | exact YM0]
          end
      end.
  Qed.

End Y4F6.
End CANSEC1.
