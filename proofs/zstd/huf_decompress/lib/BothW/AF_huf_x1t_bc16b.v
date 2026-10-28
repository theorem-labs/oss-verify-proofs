(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import ZdHufStats ZdHufX1.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AFake0k_iface AProg_kit
     AFake_arep FsKit AF_fse_rd_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AH_huf_kit AH_huf_iface
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t_top AF_huf_x1t_bseg AF_huf_x1t_bdefs AF_huf_x1t_bfk AF_huf_x1t_bpure AF_huf_x1t_bc16.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section SHD. Context {rc : runConstT}.
Lemma x1_shd_ap : forall E X B k L H, ablk L H -> L <= H ->
  L <= bv_unsigned (edenot E X) <= H + 7 -> L <= bv_unsigned (edenot E B) + k < H ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) ASHOFF) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit 1)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) ASHOFF) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit 1) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) ASHOFF)).
Proof.
  intros E X B k L H AB LH XR BR.
  pose proof (ablk_lin L H AB) as (L1 & L2 & L3 & L4).
  pose proof (ablk_shad_disj L H AB LH) as SD.
  pose proof (shad_mono L (bv_unsigned (edenot E X)) ltac:(lia)) as M1.
  pose proof (shad_mono (bv_unsigned (edenot E X)) (H + 7) ltac:(lia)) as M2.
  assert (SH : forall a, shad a = ASHOFF + a / 8) by (intro a; rewrite shad_div; lia).
  rewrite SH in M1, M2, SD. rewrite (SH (H + 7)) in SD.
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  change (2 ^ (3 mod 64)) with 8.
  assert (HD0 : 0 <= bv_unsigned (edenot E X) / 8) by (apply Z.div_pos; lia).
  unfold ASHOFF in *. repeat split; lia.
Qed.
End SHD.
Ltac x1shd DT DTB :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) _ /\ _ =>
      apply (x1_shd_ap E X B k DT (DT + DTB)); [ assumption | lia | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia
                                           | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia ]
  end.
Ltac prf_chain c PRE :=
  lazymatch goal with
  | |- x1prf ?mtl ?tl c ?ks (Zupd ?i ?v ?D) =>
      let j := lazymatch i with _ + ?j - _ => j end in
      let jv := eval vm_compute in (j - 4) in
      let kk := eval vm_compute in (Z.div jv 2) in
      let par := eval vm_compute in (Z.modulo jv 2) in
      lazymatch par with
      | 0 => eapply (prf_st_nb mtl tl c _ D kk i v); [ prf_chain c PRE | lia | lia | lia | rewrite ?Zupd_length2; lia | lia ]
      | 1 => eapply (prf_st_sy mtl tl c _ D kk i v); [ prf_chain c PRE | lia | lia | lia ]
      end
  | |- x1prf _ _ c _ _ => apply prf_open; exact PRE
  end.
Section CANSEC1. Context {rc : runConstT}.
Section X1B.
  Variables (RNG : footprint) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m5 : amem) (SPV SPA lo DT DTB WK wksz FF r : Z).
  Hypothesis HY : x1A_hyps RNG SPV SPA lo DT DTB WK wksz FF.
  Hypothesis UDT : unpoisoned m5 DT (DT + DTB).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : artcells m5.
  Hypothesis Hr : 0 <= r < 2^32.
  Variable POST : machine_state -> Prop.
  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 0x7fff8000) xs4
             xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Section C16.
  Variables (hw rank : list Z) (nbs tl mtl : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis TLR : 1 <= tl <= 12.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Notation XFm := (XF m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl).
  Notation XCm := (XC m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl).
  Notation SF pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5
             (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation STC pc mm nb len xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (SF pc mm xra x5 x6 x7 xa0 (Z_to_bv 64 nb) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 (Z_to_bv 64 len) xs10 xs11 x28 x29 x30 x31).
  Notation STL mm len xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (SF 0x81964 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 (Z_to_bv 64 len) xs10 xs11 x28 x29 x30 x31).
  Notation XDm j0 j192 dt rst syb w cur sym cnt nb len :=
    (XCm j0 j192 dt rst syb w cur sym cnt (Z_to_bv 64 (2 * len)) (Z_to_bv 64 cnt) (Z_to_bv 64 nb) (Z_to_bv 64 sym) (Z_to_bv 64 (256 - sym))).
  Notation STO mm s q len x5 x6 x7 xa0 xa1 xa2 xa5 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 (DT + 2 * q)) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             xa0 xa1 xa2 (Z_to_bv 64 s) (Z_to_bv 64 (DT + 2 * q)) xa5 (Z_to_bv 64 q) xa7
             xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5 (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) (Z_to_bv 64 len) xs10 xs11
             x28 x29 x30 x31)
        F (Z_to_bv 64 0x81460) fc None mm (seg_rom bsegs)).
  Notation STI mm u s q len d x5 x6 x7 xa0 xa2 xa5 xa7 xs4 xs5 xs10 xs11 x29 x30 :=
    (MS (mkR (Z_to_bv 64 (DT + 2 * q)) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             xa0 (Z_to_bv 64 d) xa2 (Z_to_bv 64 s) (Z_to_bv 64 (DT + 2 * q)) xa5 (Z_to_bv 64 q) xa7
             (Z_to_bv 64 (32 * u)) (Z_to_bv 64 0x7fff8000) xs4 xs5 (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) (Z_to_bv 64 len) xs10 xs11
             (Z_to_bv 64 (16 * u)) x29 x30 (Z_to_bv 64 (18446744073709551615 - (DT + 4 + 2 * q))))
        F (Z_to_bv 64 0x814dc) fc None mm (seg_rom bsegs)).
  Notation STI2 mm u s q len d x5 x6 xa0 :=
    (MS (mkR (Z_to_bv 64 (DT + 2 * q)) (Z_to_bv 64 SPA) gp tp x5 x6 (Z_to_bv 64 (d / 256)) (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             xa0 (Z_to_bv 64 d) (Z_to_bv 64 (DT + 2 * q + 32 * u)) (Z_to_bv 64 s) (Z_to_bv 64 (DT + 2 * q)) (Z_to_bv 64 (DT + 2 * q + 32 * u + 4)) (Z_to_bv 64 q)
             (Z_to_bv 64 (DT + 2 * q + 32 * u))
             (Z_to_bv 64 (32 * u)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (d / 4294967296)) (Z_to_bv 64 (d / 72057594037927936))
             (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) (Z_to_bv 64 len)
             (Z_to_bv 64 (d / 65536)) (Z_to_bv 64 (d / 16777216))
             (Z_to_bv 64 (16 * u)) (Z_to_bv 64 (d / 1099511627776)) (Z_to_bv 64 (d / 281474976710656)) (Z_to_bv 64 (18446744073709551615 - (DT + 4 + 2 * q))))
        F (Z_to_bv 64 0x815a0) fc None mm (seg_rom bsegs)).
  Notation STDL mm s q len x5 x6 x7 xa0 xa1 xa2 xa5 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 (DT + 2 * q)) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA)
             xa0 xa1 xa2 (Z_to_bv 64 s) (Z_to_bv 64 (DT + 2 * q)) xa5 (Z_to_bv 64 q) xa7
             xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5 (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 18446744073709551591) (Z_to_bv 64 len) xs10 xs11
             x28 x29 x30 x31)
        F (Z_to_bv 64 0x816a4) fc None mm (seg_rom bsegs)).
  Definition x1_cd_in1A_stmt : Prop := forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb len s q u sv d : Z)
      x5 x6 x7 xa0 xa2 xa5 xa7 xs4 xs5 xs10 xs11 x29 x30,
    XDm j0 j192 dt rst syb w cur sym cnt nb len m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> 5 <= w ->
    len = hw_cells w -> nb = tl + 1 - w -> 0 <= s < cnt -> 0 <= q -> q + len <= 2 ^ tl -> 0 <= u -> 16 * u + 16 <= len ->
    0 <= sv < 256 -> d4f d sv nb -> x1pref mtl tl (q + 16 * u) dt ->
    (forall m2 (dt' : list Z) (y5 y6 ya0 : word),
       XDm j0 j192 dt' rst syb w cur sym cnt nb len m2 -> x1pref mtl tl (q + 16 * u + 8) dt' ->
       evtF bsegs RNG POST (STI2 m2 u s q len d y5 y6 ya0)) ->
    evtF bsegs RNG POST (STI m1 u s q len d x5 x6 x7 xa0 xa2 xa5 xa7 xs4 xs5 xs10 xs11 x29 x30).
  Lemma XC_sbw : forall j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 a x b,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> DT <= a < DT + DTB -> x mod 256 = b mod 256 -> 0 <= b < 256 ->
    XCm j0 j192 (Zupd (a - DT) b dt) rst syb w cur sym cnt k112 k120 k128 k136 k144 (CatExec.wbytes m1 (wa a) (word_to_le_bytes 1 (Z_to_bv 64 x))).
  Proof.
    intros until b. intros I AR XV BR.
    exact (XC_sb RNG m5 SPV SPA lo DT DTB WK wksz FF r HY hw rank tl TLR LHW LRK j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 a x b I AR XV BR).
  Qed.
  Ltac xd_bv DM B0 B1 B2 B3 B4 B5 B6 B7 nb sv :=
    rewrite ?DM;
    repeat match goal with |- context [2 ^ (?a mod 64)] => let v := eval vm_compute in (2 ^ (a mod 64)) in change (2 ^ (a mod 64)) with v end;
    rewrite ?Z.div_1_r, ?(Z.mod_small nb 256), ?(Z.mod_small sv 256) by lia;
    first [exact B0 | exact B1 | exact B2 | exact B3 | exact B4 | exact B5 | exact B6 | exact B7].
  Ltac xd_mem I2 DM B0 B1 B2 B3 B4 B5 B6 B7 nb sv M :=
    lazymatch M with
    | CatExec.wbytes ?m (wa ?a) (word_to_le_bytes 1 (Z_to_bv 64 ?x)) =>
        xd_mem I2 DM B0 B1 B2 B3 B4 B5 B6 B7 nb sv m;
        first [ eapply (XC_sbw _ _ _ _ _ _ _ _ _ _ _ _ _ _ m a x nb) in I2; [ | lia | xd_bv DM B0 B1 B2 B3 B4 B5 B6 B7 nb sv | lia ]
              | eapply (XC_sbw _ _ _ _ _ _ _ _ _ _ _ _ _ _ m a x sv) in I2; [ | lia | xd_bv DM B0 B1 B2 B3 B4 B5 B6 B7 nb sv | lia ] ]
    | _ => idtac
    end.
  Lemma x1_cd_in1A : x1_cd_in1A_stmt.
  Proof.
    unfold x1_cd_in1A_stmt. intros until x30. intros I HW HC HS HCN W5 HL HNB SR Q0 QH U0 UL SVR DF PRE K.
    pose proof (fill_facts hw rank nbs tl STATS TLR NBSR LHW w HW) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR).
    rewrite <- HC, <- HS, <- HCN in *. rewrite <- HL in CL0, CLH, LENR.
    pose proof (proj1 (len16 w ltac:(lia))) as LEN16. rewrite <- HL in LEN16.
    pose proof I as I0. open_xc I0. x1_hy HY.
    pose proof (x1_unp_dtM RNG m5 SPV SPA lo DT DTB WK wksz FF HY UDT m1 MU) as UD1.
    assert (QR : 0 <= q <= 4080) by lia. assert (UR : 0 <= u <= 127) by lia.
    assert (LDT : zlen (map (Z_to_bv 8) dt) = DTB) by (rewrite length_map; exact DTLEN).
    assert (D0 : 0 <= d < 2^64) by (destruct DF as (D0 & DM & _); rewrite <- DM; apply Z.mod_pos_bound; lia).
    unfold shspan in RSDT, RSWK.
    kx_runFm [529824] 60%nat
      [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange q 0 4080; KZRange u 0 127; KZRange d 0 (2^64 - 1);
       KZWr (DT + 2 * q + 32 * u + 4) 16]
      (@nil (Z * Z)) [(SPA, 216); (DT + 2 * q + 32 * u + 4, 16)] [(DT + 2 * q + 32 * u + 4, 16)].
    all: try x1shd DT DTB.
    kx_post_regs.
    lazymatch goal with |- context [mem_denot ?E _ _] => cbn [mem_denot]; xa_norm E end.
    pose proof DF as (DD0 & DM & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof I as I2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?M _) => xd_mem I2 DM B0 B1 B2 B3 B4 B5 B6 B7 nb sv M end.
    rewrite ?DM in I2 |- *.
    repeat match goal with |- context [2 ^ (?a mod 64)] => let v := eval vm_compute in (2 ^ (a mod 64)) in change (2 ^ (a mod 64)) with v end.
    repeat match type of I2 with context [2 ^ (?a mod 64)] => let v := eval vm_compute in (2 ^ (a mod 64)) in change (2 ^ (a mod 64)) with v in I2 end.
    replace (DT + (2 * q + 32 * u)) with (DT + 2 * q + 32 * u) in I2 |- * by lia.
    negfix.
    replace (Z_to_bv 64 (- DT + -2 * q + -5)) with (Z_to_bv 64 (18446744073709551615 - (DT + 4 + 2 * q)))
      by (apply Z_to_bv_eqm; replace (18446744073709551615 - (DT + 4 + 2 * q)) with ((- DT + -2 * q + -5) + 1 * 2^64) by lia;
          rewrite Z_mod_plus_full; reflexivity).
    eapply K; [exact I2 |].
    change (q + 16 * u + 8) with (q + 16 * u + Z.of_nat 8).
    eapply (prf_close_c mtl tl (q + 16 * u) _ _ 8%nat); [ prf_chain (q + 16 * u) PRE | lia | vm_compute; reflexivity ].
  Qed.
  End C16.
End X1B.
End CANSEC1.
