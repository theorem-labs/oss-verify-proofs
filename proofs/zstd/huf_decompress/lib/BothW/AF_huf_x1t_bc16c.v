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
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t_top AF_huf_x1t_bseg AF_huf_x1t_bdefs AF_huf_x1t_bfk AF_huf_x1t_bpure AF_huf_x1t_bc16 AF_huf_x1t_bc16b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
  Definition x1_cd_in2A_stmt : Prop := forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb len s q u sv d : Z) x5 x6 xa0,
    XDm j0 j192 dt rst syb w cur sym cnt nb len m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> 5 <= w ->
    len = hw_cells w -> nb = tl + 1 - w -> 0 <= s < cnt -> 0 <= q -> q + len <= 2 ^ tl -> 0 <= u -> 16 * u + 16 <= len ->
    0 <= sv < 256 -> d4f d sv nb -> x1pref mtl tl (q + 16 * u + 8) dt ->
    (forall m2 (dt' : list Z) (y5 y6 y7 ya0 ya2 ya5 ya7 ys4 ys5 ys10 ys11 y29 y30 : word), 16 * u + 32 <= len ->
       XDm j0 j192 dt' rst syb w cur sym cnt nb len m2 -> x1pref mtl tl (q + 16 * (u + 1)) dt' ->
       evtF bsegs RNG POST (STI m2 (u + 1) s q len d y5 y6 y7 ya0 ya2 ya5 ya7 ys4 ys5 ys10 ys11 y29 y30)) ->
    (forall m2 (dt' : list Z) (y5 y6 y7 ya0 ya1 ya2 ya5 ya7 ys2 ys4 ys5 ys10 ys11 y28 y29 y30 y31 : word), 16 * u + 16 = len ->
       XDm j0 j192 dt' rst syb w cur sym cnt nb len m2 -> x1pref mtl tl (q + len) dt' ->
       evtF bsegs RNG POST (STDL m2 s q len y5 y6 y7 ya0 ya1 ya2 ya5 ya7 ys2 ys4 ys5 ys10 ys11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STI2 m1 u s q len d x5 x6 xa0).
  Ltac xd_bv2 DM B0 B1 B2 B3 B4 B5 B6 B7 nb sv :=
    rewrite ?DM;
    repeat match goal with |- context [2 ^ (?a mod 64)] => let v := eval vm_compute in (2 ^ (a mod 64)) in change (2 ^ (a mod 64)) with v end;
    rewrite ?Z.div_1_r, ?(Z.mod_small nb 256), ?(Z.mod_small sv 256) by lia;
    first [exact B0 | exact B1 | exact B2 | exact B3 | exact B4 | exact B5 | exact B6 | exact B7].
  Ltac xd_mem2 I2 DM B0 B1 B2 B3 B4 B5 B6 B7 nb sv M :=
    lazymatch M with
    | CatExec.wbytes ?m (wa ?a) (word_to_le_bytes 1 (Z_to_bv 64 ?x)) =>
        xd_mem2 I2 DM B0 B1 B2 B3 B4 B5 B6 B7 nb sv m;
        first [ eapply (XC_sbw RNG m5 SPV SPA lo DT DTB WK wksz FF r HY hw rank tl TLR LHW LRK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m a x nb) in I2; [ | lia | xd_bv2 DM B0 B1 B2 B3 B4 B5 B6 B7 nb sv | lia ]
              | eapply (XC_sbw RNG m5 SPV SPA lo DT DTB WK wksz FF r HY hw rank tl TLR LHW LRK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m a x sv) in I2; [ | lia | xd_bv2 DM B0 B1 B2 B3 B4 B5 B6 B7 nb sv | lia ] ]
    | _ => idtac
    end.
  Ltac prf_chain20 c PRE :=
    lazymatch goal with
    | |- x1prf ?mtl ?tl c ?ks (Zupd ?i ?v ?D) =>
        let j := lazymatch i with _ + ?j - _ => j end in
        let jv := eval vm_compute in (j - 20) in
        let kk := eval vm_compute in (Z.div jv 2) in
        let par := eval vm_compute in (Z.modulo jv 2) in
        lazymatch par with
        | 0 => eapply (prf_st_nb mtl tl c _ D kk i v); [ prf_chain20 c PRE | lia | lia | lia | rewrite ?Zupd_length2; lia | lia ]
        | 1 => eapply (prf_st_sy mtl tl c _ D kk i v); [ prf_chain20 c PRE | lia | lia | lia ]
        end
    | |- x1prf _ _ c _ _ => apply prf_open; exact PRE
    end.
  Lemma x1_cd_in2A : x1_cd_in2A_stmt.
  Proof.
    unfold x1_cd_in2A_stmt. intros until xa0. intros I HW HC HS HCN W5 HL HNB SR Q0 QH U0 UL SVR DF PRE KL KE.
    pose proof (fill_facts hw rank nbs tl STATS TLR NBSR LHW w HW) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR).
    rewrite <- HC, <- HS, <- HCN in *. rewrite <- HL in CL0, CLH, LENR.
    pose proof (len16 w ltac:(lia)) as (LEN16 & LD16). rewrite <- HL in LEN16, LD16.
    pose proof I as I0. open_xc I0. x1_hy HY.
    pose proof (x1_unp_dtM RNG m5 SPV SPA lo DT DTB WK wksz FF HY UDT m1 MU) as UD1.
    assert (QR : 0 <= q <= 4080) by lia. assert (UR : 0 <= u <= 127) by lia.
    assert (LDT : zlen (map (Z_to_bv 8) dt) = DTB) by (rewrite length_map; exact DTLEN).
    assert (D0 : 0 <= d < 2^64) by (destruct DF as (D0 & DM & _); rewrite <- DM; apply Z.mod_pos_bound; lia).
    unfold shspan in RSDT, RSWK.
    destruct (Z_lt_ge_dec (16 * u + 16) len) as [LT|GE].
    - kx_runFmd [529628; 530084] 60%nat [true]
        [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange q 0 4080; KZRange u 0 127; KZRange len 16 2048;
         KZRange d 0 (2^64 - 1); KZWr (DT + 2 * q + 32 * u + 20) 16]
        (@nil (Z * Z)) [(SPA, 216); (DT + 2 * q + 32 * u + 20, 16)] [(DT + 2 * q + 32 * u + 20, 16)].
      all: try x1shd DT DTB.
      all: try w4br.
      kx_post_regs.
      lazymatch goal with |- context [mem_denot ?E _ _] => cbn [mem_denot]; xa_norm E end.
      pose proof DF as (DD0 & DM & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
      pose proof I as I2.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?M _) => xd_mem2 I2 DM B0 B1 B2 B3 B4 B5 B6 B7 nb sv M end.
      rewrite ?DM in I2 |- *.
      repeat match goal with |- context [2 ^ (?a mod 64)] => let v := eval vm_compute in (2 ^ (a mod 64)) in change (2 ^ (a mod 64)) with v end.
      repeat match type of I2 with context [2 ^ (?a mod 64)] => let v := eval vm_compute in (2 ^ (a mod 64)) in change (2 ^ (a mod 64)) with v in I2 end.
      replace (DT + (2 * q + 32 * u)) with (DT + 2 * q + 32 * u) in I2 |- * by lia.
      negfix.
      try replace (Z_to_bv 64 (- DT + -2 * q + -5)) with (Z_to_bv 64 (18446744073709551615 - (DT + 4 + 2 * q)))
        by (apply Z_to_bv_eqm; replace (18446744073709551615 - (DT + 4 + 2 * q)) with ((- DT + -2 * q + -5) + 1 * 2^64) by lia;
            rewrite Z_mod_plus_full; reflexivity).
      replace (q + 16 * (u + 1)) with (q + 16 * u + 8 + Z.of_nat 8) in KL by lia.
      replace (32 * u + 32) with (32 * (u + 1)) by lia.
      replace (16 * u + 16) with (16 * (u + 1)) by lia.
      eapply KL; [lia | exact I2 | ].
      eapply (prf_close_c mtl tl (q + 16 * u + 8) _ _ 8%nat); [ prf_chain20 (q + 16 * u + 8) PRE | lia | vm_compute; reflexivity ].
    - assert (EQ : 16 * u + 16 = len) by (destruct LD16 as (kq & KQ); nia).
      kx_runFmd [529628; 530084] 60%nat [false]
        [KZRange SPA 4096 (2^47); KZRange DT 4096 (2^47); KZRange q 0 4080; KZRange u 0 127; KZRange len 16 2048;
         KZRange d 0 (2^64 - 1); KZWr (DT + 2 * q + 32 * u + 20) 16]
        (@nil (Z * Z)) [(SPA, 216); (DT + 2 * q + 32 * u + 20, 16)] [(DT + 2 * q + 32 * u + 20, 16)].
      all: try x1shd DT DTB.
      all: try w4br.
      kx_post_regs.
      lazymatch goal with |- context [mem_denot ?E _ _] => cbn [mem_denot]; xa_norm E end.
      pose proof DF as (DD0 & DM & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
      pose proof I as I2.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?M _) => xd_mem2 I2 DM B0 B1 B2 B3 B4 B5 B6 B7 nb sv M end.
      rewrite ?DM in I2 |- *.
      repeat match goal with |- context [2 ^ (?a mod 64)] => let v := eval vm_compute in (2 ^ (a mod 64)) in change (2 ^ (a mod 64)) with v end.
      repeat match type of I2 with context [2 ^ (?a mod 64)] => let v := eval vm_compute in (2 ^ (a mod 64)) in change (2 ^ (a mod 64)) with v in I2 end.
      replace (DT + (2 * q + 32 * u)) with (DT + 2 * q + 32 * u) in I2 |- * by lia.
      negfix.
      replace (q + len) with (q + 16 * u + 8 + Z.of_nat 8) in KE by lia.
      eapply KE; [lia | exact I2 | ].
      eapply (prf_close_c mtl tl (q + 16 * u + 8) _ _ 8%nat); [ prf_chain20 (q + 16 * u + 8) PRE | lia | vm_compute; reflexivity ].
  Qed.
  Definition x1_cd_inloopA_stmt : Prop := forall (f : nat) m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb len s q u sv d : Z)
      x5 x6 x7 xa0 xa2 xa5 xa7 xs4 xs5 xs10 xs11 x29 x30,
    XDm j0 j192 dt rst syb w cur sym cnt nb len m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> 5 <= w ->
    len = hw_cells w -> nb = tl + 1 - w -> 0 <= s < cnt -> 0 <= q -> q + len <= 2 ^ tl -> 0 <= u -> 16 * u + 16 * Z.of_nat (S f) = len ->
    0 <= sv < 256 -> d4f d sv nb -> x1pref mtl tl (q + 16 * u) dt ->
    (forall m2 (dt' : list Z) (y5 y6 y7 ya0 ya1 ya2 ya5 ya7 ys2 ys4 ys5 ys10 ys11 y28 y29 y30 y31 : word),
       XDm j0 j192 dt' rst syb w cur sym cnt nb len m2 -> x1pref mtl tl (q + len) dt' ->
       evtF bsegs RNG POST (STDL m2 s q len y5 y6 y7 ya0 ya1 ya2 ya5 ya7 ys2 ys4 ys5 ys10 ys11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STI m1 u s q len d x5 x6 x7 xa0 xa2 xa5 xa7 xs4 xs5 xs10 xs11 x29 x30).
  Lemma x1_cd_inloopA : x1_cd_inloopA_stmt.
  Proof.
    pose proof (x1_cd_in1A RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r HY UDT POST hw rank nbs tl mtl STATS TLR NBSR LHW LRK) as IN1.
    pose proof x1_cd_in2A as IN2. unfold x1_cd_in1A_stmt in IN1. unfold x1_cd_in2A_stmt in IN2.
    unfold x1_cd_inloopA_stmt. induction f as [|f IH]; intros until x30; intros I HW HC HS HCN W5 HL HNB HSR Q0 QH U0 UF SVR D4F PF KE.
    - eapply (IN1 m1 j0 j192 dt rst syb w cur sym cnt nb len s q u sv d); [exact I| exact HW| exact HC| exact HS| exact HCN| exact W5| exact HL| exact HNB| exact HSR| exact Q0| exact QH| exact U0| lia| exact SVR| exact D4F| exact PF|].
      intros m2 dt' y5 y6 ya0 I2 PF2.
      eapply (IN2 m2 j0 j192 dt' rst syb w cur sym cnt nb len s q u sv d); [exact I2| exact HW| exact HC| exact HS| exact HCN| exact W5| exact HL| exact HNB| exact HSR| exact Q0| exact QH| exact U0| lia| exact SVR| exact D4F| exact PF2| intros; exfalso; lia|].
      intros m3 dt3 z5 z6 y7 za0 ya1 ya2 ya5 ya7 ys2 ys4 ys5 ys10 ys11 y28 y29 y30 y31 _ I3 PF3. eapply KE; [exact I3| exact PF3].
    - eapply (IN1 m1 j0 j192 dt rst syb w cur sym cnt nb len s q u sv d); [exact I| exact HW| exact HC| exact HS| exact HCN| exact W5| exact HL| exact HNB| exact HSR| exact Q0| exact QH| exact U0| lia| exact SVR| exact D4F| exact PF|].
      intros m2 dt' y5 y6 ya0 I2 PF2.
      eapply (IN2 m2 j0 j192 dt' rst syb w cur sym cnt nb len s q u sv d); [exact I2| exact HW| exact HC| exact HS| exact HCN| exact W5| exact HL| exact HNB| exact HSR| exact Q0| exact QH| exact U0| lia| exact SVR| exact D4F| exact PF2| | intros; exfalso; lia].
      intros m3 dt3 z5 z6 y7 za0 ya2 ya5 ya7 ys4 ys5 ys10 ys11 y29 y30 HU I3 PF3.
      eapply (IH m3 j0 j192 dt3 rst syb w cur sym cnt nb len s q (u + 1) sv d);
        [exact I3| exact HW| exact HC| exact HS| exact HCN| exact W5| exact HL| exact HNB| exact HSR| exact Q0| exact QH| lia| lia| exact SVR| exact D4F| exact PF3| exact KE].
  Qed.
  Definition x1_cd_symloopA_stmt : Prop := forall (g : nat) m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb len s q : Z)
      x5 x6 x7 xa0 xa1 xa2 xa5 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31,
    XDm j0 j192 dt rst syb w cur sym cnt nb len m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> 5 <= w ->
    len = hw_cells w -> nb = tl + 1 - w -> 0 <= s -> s + Z.of_nat (S g) = cnt -> q = cur + len * s -> x1pref mtl tl q dt ->
    (forall m2 (dt' : list Z) (yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 ys11 y28 y29 y30 y31 : word),
       XDm j0 j192 dt' rst syb w cur sym cnt nb len m2 -> x1pref mtl tl (cur + cnt * len) dt' ->
       evtF bsegs RNG POST (STL m2 len yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 ys11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STO m1 s q len x5 x6 x7 xa0 xa1 xa2 xa5 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31).
  Lemma x1_cd_symloopA : x1_cd_symloopA_stmt.
  Proof.
    pose proof (@x1_cd_headA _ RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r) as HDA; repeat lazymatch type of HDA with | forall (_ : machine_state -> Prop), _ => specialize (HDA POST) | forall (_ : list Z) (_ : list Z) (_ : Z) (_ : Z) (_ : Z), _ => specialize (HDA hw rank nbs tl mtl) | forall (_ : list Z) (_ : list Z) (_ : Z) (_ : Z), _ => specialize (HDA hw rank nbs tl) | ?A -> _ => specialize (HDA ltac:(assumption)) end. pose proof (@x1_cd_slA _ RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r) as SLA; repeat lazymatch type of SLA with | forall (_ : machine_state -> Prop), _ => specialize (SLA POST) | forall (_ : list Z) (_ : list Z) (_ : Z) (_ : Z) (_ : Z), _ => specialize (SLA hw rank nbs tl mtl) | forall (_ : list Z) (_ : list Z) (_ : Z) (_ : Z), _ => specialize (SLA hw rank nbs tl) | ?A -> _ => specialize (SLA ltac:(assumption)) end. pose proof x1_cd_inloopA as ILA.
    unfold x1_cd_headA_stmt in HDA. unfold x1_cd_slA_stmt in SLA. unfold x1_cd_inloopA_stmt in ILA.
    unfold x1_cd_symloopA_stmt. induction g as [|g IH]; intros until x31; intros I HW HC HS HCN W5 HL HNB S0 SG HQ PF KE.
    all: pose proof (fill_facts hw rank nbs tl STATS TLR NBSR LHW w HW) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR);
      rewrite <- HL in CL0, CLH, LENR; rewrite <- HC, <- HS, <- HCN in *.
    all: assert (Q0 : 0 <= q) by (rewrite HQ; nia).
    all: assert (QH : q + len <= 2 ^ tl) by (rewrite HQ; assert (len * s + len <= cnt * len) by nia; lia).
    all: assert (QH4 : q + len <= 4096) by lia.
    all: pose proof (len16 w ltac:(lia)) as (L16 & l16 & HL16); rewrite <- HL in L16, HL16.
    all: eapply (HDA m1 j0 j192 dt rst syb w cur sym cnt nb len s q);
      [exact I| exact HW| exact HC| exact HS| exact HCN| exact W5| exact HL| exact HNB| lia| exact HQ| exact Q0| exact QH4|].
    all: intros m2 sv d ya0 ya2 ya5 SVR D4F I2.
    all: eapply (ILA (Z.to_nat (l16 - 1)) m2 j0 j192 dt rst syb w cur sym cnt nb len s q 0 sv d);
      [exact I2| exact HW| exact HC| exact HS| exact HCN| exact W5| exact HL| exact HNB| lia| exact Q0| exact QH| lia| lia| exact SVR| exact D4F| replace (q + 16 * 0) with q by lia; exact PF|].
    all: intros m3 dt3 y5 y6 y7 za0 ya1 za2 za5 ya7 ys2 ys4 ys5 ys10 ys11 y28 y29 y30 y31 I3 PF3.
    - eapply (SLA m3 j0 j192 dt3 rst syb w cur sym cnt nb len s q); [exact I3| exact HW| exact HC| exact HS| exact HCN| exact W5| exact HL| exact HNB| lia| exact HQ| exact Q0| exact QH4| intros; exfalso; lia|].
      intros yra wa0 wa1 wa3 wa4 wa6 HS1. eapply KE; [exact I3|].
      replace (cur + cnt * len) with (q + len) by (rewrite HQ, <- HS1; lia). exact PF3.
    - eapply (SLA m3 j0 j192 dt3 rst syb w cur sym cnt nb len s q); [exact I3| exact HW| exact HC| exact HS| exact HCN| exact W5| exact HL| exact HNB| lia| exact HQ| exact Q0| exact QH4| | intros; exfalso; lia].
      intros wa0 wa1 HS1.
      eapply (IH m3 j0 j192 dt3 rst syb w cur sym cnt nb len (s + 1) (q + len));
        [exact I3| exact HW| exact HC| exact HS| exact HCN| exact W5| exact HL| exact HNB| lia| lia| rewrite HQ; lia| exact PF3| exact KE].
  Qed.
  Definition x1_cdA_stmt : Prop := forall m1 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (w cur sym cnt nb len : Z) (k112 k120 k128 k136 k144 : word)
      xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31,
    XCm j0 j192 dt rst syb w cur sym cnt k112 k120 k128 k136 k144 m1 -> 1 <= w <= tl -> cur = xcur rank w -> sym = xsym rank w -> cnt = Znth w rank -> 5 <= w ->
    len = hw_cells w -> nb = tl + 1 - w -> x1pref mtl tl cur dt ->
    (forall m2 (dt' : list Z) (k112' k120' k128' k136' k144' : word) (yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 ys11 y28 y29 y30 y31 : word),
       XCm j0 j192 dt' rst syb w cur sym cnt k112' k120' k128' k136' k144' m2 -> x1pref mtl tl (cur + cnt * len) dt' ->
       evtF bsegs RNG POST (STL m2 len yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 ys11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STC 0x813f8 m1 nb len xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs10 xs11 x28 x29 x30 x31).
  Lemma x1_cdA : x1_cdA_stmt.
  Proof.
    pose proof (@x1_cd_setA _ RNG gp tp F fc m5 SPV SPA lo DT DTB WK wksz FF r) as STA; repeat lazymatch type of STA with | forall (_ : machine_state -> Prop), _ => specialize (STA POST) | forall (_ : list Z) (_ : list Z) (_ : Z) (_ : Z) (_ : Z), _ => specialize (STA hw rank nbs tl mtl) | forall (_ : list Z) (_ : list Z) (_ : Z) (_ : Z), _ => specialize (STA hw rank nbs tl) | ?A -> _ => specialize (STA ltac:(assumption)) end. pose proof x1_cd_symloopA as SYL.
    unfold x1_cd_setA_stmt in STA. unfold x1_cd_symloopA_stmt in SYL.
    unfold x1_cdA_stmt. intros until x31; intros I HW HC HS HCN W5 HL HNB PF KE.
    eapply (STA m1 j0 j192 dt rst syb w cur sym cnt nb len k112 k120 k128 k136 k144);
      [exact I| exact HW| exact HC| exact HS| exact HCN| exact W5| exact HL| exact HNB| |].
    - intros m2 ya0 ya1 ya2 HCNT I2.
      eapply (SYL (Z.to_nat (cnt - 1)) m2 j0 j192 dt rst syb w cur sym cnt nb len 0 cur);
        [exact I2| exact HW| exact HC| exact HS| exact HCN| exact W5| exact HL| exact HNB| lia| lia| lia| exact PF|].
      intros m3 dt3 yra y5 y6 y7 za0 za1 za2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys10 ys11 y28 y29 y30 y31 I3 PF3.
      eapply KE; [exact I3| exact PF3].
    - intros ya0 HC0. eapply KE; [exact I| rewrite HC0; replace (cur + 0 * len) with cur by lia; exact PF].
  Qed.
  End C16.
End X1B.
End CANSEC1.
