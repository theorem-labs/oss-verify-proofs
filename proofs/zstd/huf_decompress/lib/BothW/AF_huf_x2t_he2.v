From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AF_huf_x2t_hdefs AF_huf_w4s3b AF_huf_x2t_h1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x2t_he1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Definition x2hb_cd_stmt : Prop :=
  forall (RNG : footprint) (x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : amem) (SPF DT SYM pos cnt bg nb T bs lvl mtl : Z) (syb j0 : list byte) (dt : list Z),
  x2hb_hyps RNG SPF DT SYM mtl -> unpoisoned m0 DT (DT + (4 * (1 + 2 ^ mtl))) -> unpoisoned m0 SYM (SYM + 256) -> x2hb_art m0 ->
  0 <= pos -> 0 <= bg -> 0 <= cnt -> bg + cnt <= 256 -> 0 <= nb <= T -> 1 <= T <= 12 -> 1 <= mtl <= 12 -> T <= mtl ->
  4 <= T - nb -> pos + 2 ^ (T - nb) * cnt <= 2 ^ mtl -> (lvl = 1 \/ lvl = 2) -> 0 <= bs < 256 ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG (x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 (pos + 2 ^ (T - nb) * cnt))
    (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
       SPF DT SYM pos bg cnt nb bs lvl (2 ^ (T - nb)) 8 0x8d5dc).

Section CD2.
Variables (RNG : footprint) (x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : amem) (SPF DT SYM pos cnt bg nb T mtl bs : Z) (syb j0 : list byte).
Hypothesis HY : x2hb_hyps RNG SPF DT SYM mtl.
Hypothesis UDT : unpoisoned m0 DT (DT + (4 * (1 + 2 ^ mtl))).
Hypothesis USY : unpoisoned m0 SYM (SYM + 256).
Hypothesis ART0 : x2hb_art m0.
Hypothesis HP : 0 <= pos.
Hypothesis HB : 0 <= bg.
Hypothesis HBC : bg + cnt <= 256.
Hypothesis HC : 1 <= cnt.
Hypothesis HNB : 0 <= nb <= T.
Hypothesis HT : 1 <= T <= 12.
Hypothesis HM : 1 <= mtl <= 12.
Hypothesis HTM : T <= mtl.
Hypothesis HL4 : 4 <= T - nb.
Hypothesis HROOM : pos + 2 ^ (T - nb) * cnt <= 2 ^ mtl.
Hypothesis HBS : 0 <= bs < 256.

Notation CDOh := (CDO x1 gp tp F fc SPF DT SYM cnt bg nb T bs).
Notation CDPh := (CDPOST x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m0 SPF DT pos cnt nb T mtl).

Lemma cd_lenb : 16 <= 2 ^ (T - nb) <= 4096.
Proof.
  split; [replace 16 with (2 ^ 4) by reflexivity | replace 4096 with (2 ^ 12) by reflexivity];
    apply Z.pow_le_mono_r; lia.
Qed.

Ltac cd_vals := repeat (match goal with |- context [2 ^ (?a mod 64)] =>
                          let v := eval vm_compute in (2 ^ (a mod 64)) in change (2 ^ (a mod 64)) with v end);
  let w := eval vm_compute in (2 ^ 64) in change (2 ^ 64) with w; Z.div_mod_to_equations; lia.

Lemma cdo_body : forall k c m dt y13 y14 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 lvl,
  (lvl = 1 \/ lvl = 2) -> 0 <= k < cnt -> c = pos + 2 ^ (T - nb) * k ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T c dt ->
  (k + 1 < cnt -> forall m' dt' z13 z14 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27,
     XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt' m' -> x2pref T (c + 2 ^ (T - nb)) dt' ->
     evtF bsegs RNG CDPh (CDOh (k + 1) (c + 2 ^ (T - nb)) m' z13 z14 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 lvl)) ->
  evtF bsegs RNG CDPh (CDOh k c m y13 y14 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 lvl).
Proof.
  intros k c m dt y13 y14 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 lvl HL HK HCK I PRE KN.
  pose proof cd_lenb as LB.
  assert (LD : 2 ^ (T - nb) = 16 * 2 ^ (T - nb - 4))
    by (replace 16 with (2 ^ 4) by reflexivity; rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (PK0 : 0 <= 2 ^ (T - nb) * k) by (apply Z.mul_nonneg_nonneg; lia).
  assert (PK1 : 2 ^ (T - nb) * (k + 1) <= 2 ^ (T - nb) * cnt) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (HC0 : pos <= c) by lia.
  assert (HCR : c + 2 ^ (T - nb) <= 2 ^ mtl) by lia.
  pose proof I as I0.
  pose proof HY as HY'. open_hyhb HY'. open_xhb I.
  assert (UDTm : unpoisoned m DT (DT + (4 * (1 + 2 ^ mtl)))) by (eapply x2hb_unp_dtM; eassumption).
  assert (USYm : unpoisoned m SYM (SYM + 256)) by (eapply x2hb_unp_syM; eassumption).
  unfold KHIGH in KLO. unfold shspan in RSDT, RSSY.
  assert (P2 : 2 <= 2 ^ mtl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
  assert (LDT : Z.of_nat (length (map (Z_to_bv 8) dt)) = 4 * (1 + 2 ^ mtl)) by (rewrite length_map; exact DTLEN).
  assert (LSY : Z.of_nat (length syb) = 256) by exact SYLEN.
  pose proof (proj2 DTC) as WDT. rewrite LDT in WDT.
  assert (RS1 : rng RNG (SYM + bg + k) 1) by (eapply rng_sub; [exact RSY | lia | lia]).
  unfold CDO, ASHOFF. let v := eval vm_compute in (APX2HB + 952) in change (APX2HB + 952) with v.
  destruct HL as [HL|HL]; subst lvl.
  all: let p2 := eval vm_compute in (APX2HB + 1048) in
       let p3 := eval vm_compute in (APX2HB + 2428) in
       kx_runFm [p2; p3] 80%nat
       [KZRange SPF (KHIGH + 112) (2^47 - 16); KZRange DT 4096 (2^47 - 12); KZRange SYM 4096 (2^47 - 257);
        KZRange (2 ^ mtl) 2 4096; KZRange c 0 4096; KZRange k 0 255; KZRange bg 0 256; KZRange cnt 1 256;
        KZRange (bg + k) 0 255; KZRange nb 0 12; KZRange (2 ^ (T - nb)) 16 4096; KZRange bs 0 255]
       [(SYM + bg + k, 1)] [(SYM + bg + k, 1)] [(SYM + bg + k, 1)].
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => (unfold KHIGH; lia) end).
  all: kx_post_regs; cbn [mem_denot].
  all: lazymatch goal with |- context [bv_unsigned (ev ?E ?j)] => kx_range (EVar j) HSYM end.
  all: let A := eval cbv [ASHOFF] in ASHOFF in
       lazymatch goal with
       |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?a10) (Z_to_bv 64 ?a11) _ _ _ _ (Z_to_bv 64 ?L) _ _
                          (Z_to_bv 64 ?a19) ?a20 (Z_to_bv 64 ?a21) _ _ _ _ _ _ _ _ (Z_to_bv 64 ?a30) _) _ _ _ _ _ _) =>
         replace a21 with (A + (DT + 4 + 4 * (c + 8 * 0)) / 8)
           by (change (2 ^ (3 mod 64)) with 8; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia);
         replace a19 with (DT + 4 + 4 * (c + 2 ^ (T - nb)))
           by (rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; rewrite ?Z.mod_small by lia; lia);
         replace a10 with (DT + 4 + 4 * c) by lia;
         replace a11 with (SYM + bg + k) by lia;
         (* [comment removed for export] *)
         replace a20 with (Z_to_bv 64 0)
           by (apply bv_eq; cbn [edenot]; unfold KXE; cbn [ev kx_env nth map app]; unfold alu64, alu; cbv beta iota;
               rewrite ?bv_and_unsigned, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
               rewrite (Z.mod_small DT), (Z.mod_small 1) by lia;
               change (Z.land DT 1) with (Z.land DT (Z.ones 1)); rewrite (Z.land_ones DT 1) by lia;
               Z.div_mod_to_equations; lia);
         replace a30 with (65536 * nb + 16777216 * L) by lia;
         eapply cdi_loop with (n := Z.to_nat (2 * 2 ^ (T - nb - 4) - 1)) (c0 := c) (i := 0) (E := c + 2 ^ (T - nb))
           (lvl := L) (dt := dt)
       end.
  all: try eassumption.
  all: try lia.
  all: try (replace (c + 8 * 0) with c by lia; exact PRE).
  all: cd_vals.
Qed.

Lemma cdo_loop : forall n k m dt y13 y14 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 lvl,
  Z.of_nat n = cnt - k -> (lvl = 1 \/ lvl = 2) -> 0 <= k -> k < cnt ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T (pos + 2 ^ (T - nb) * k) dt ->
  evtF bsegs RNG CDPh (CDOh k (pos + 2 ^ (T - nb) * k) m y13 y14 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 lvl).
Proof.
  induction n as [|n IH]; intros k m dt y13 y14 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 lvl HN HL HK0 HKC I PRE.
  - lia.
  - eapply cdo_body; [exact HL | lia | reflexivity | exact I | exact PRE | ].
    intros HK1 m' dt' z13 z14 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 I' PRE'.
    replace (pos + 2 ^ (T - nb) * k + 2 ^ (T - nb)) with (pos + 2 ^ (T - nb) * (k + 1)) in * by lia.
    apply IH with dt'; [lia | exact HL | lia | exact HK1 | exact I' | exact PRE'].
Qed.

Lemma cd_pos : forall m dt x7 x28 x29 x30 x31 lvl, (lvl = 1 \/ lvl = 2) ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG CDPh (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                         SPF DT SYM pos bg cnt nb bs lvl (2 ^ (T - nb)) 8 0x8d5dc).
Proof.
  intros m dt x7 x28 x29 x30 x31 lvl HL I PRE.
  pose proof HY as HY'. open_hyhb HY'. unfold KHIGH in KLO. unfold x2hb_hs, ASHOFF.
  pose proof cd_lenb as LB.
  destruct HL as [HL|HL]; subst lvl.
  all: let p1 := eval vm_compute in (APX2HB + 952) in let p2 := eval vm_compute in (APX2HB + 1048) in
       let p3 := eval vm_compute in (APX2HB + 2428) in
       kx_runFm [p1; p2; p3] 40%nat [KZRange (SYM + bg) 4096 (2^47 - 1); KZRange cnt 1 256; KZRange (2 ^ (T - nb)) 16 4096]
         (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => lia end).
  all: kx_post_regs; cbn [mem_denot].
  all: lazymatch goal with
       |- evtF _ _ _ (MS (mkR _ _ _ _ _ (Z_to_bv 64 ?a6) (Z_to_bv 64 ?a7) _ (Z_to_bv 64 ?a9) (Z_to_bv 64 ?a10)
                          (Z_to_bv 64 ?a11) _ _ _ _ (Z_to_bv 64 ?L) _ _ _ _ _ _ _ _ _ _ _
                          (Z_to_bv 64 ?a28) (Z_to_bv 64 ?a29) (Z_to_bv 64 ?a30) _) _ (Z_to_bv 64 ?pc) _ _ _ _) =>
         replace a10 with (DT + 4 + 4 * (pos + 2 ^ (T - nb) * 0)) by lia;
         replace a11 with (SYM + bg + 0) by lia;
         replace a30 with (65536 * nb + 16777216 * L) by lia;
         replace (Z_to_bv 64 a6) with (Z_to_bv 64 (-9)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity);
         replace (Z_to_bv 64 a7) with (Z_to_bv 64 (-17)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity);
         replace (Z_to_bv 64 a9) with (Z_to_bv 64 (-1)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity);
         replace (Z_to_bv 64 a28) with (Z_to_bv 64 (-25)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity);
         replace (Z_to_bv 64 a29) with (Z_to_bv 64 (-33)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity);
         change (Z_to_bv 64 pc) with (Z_to_bv 64 (APX2HB + 952));
         eapply cdo_loop with (n := Z.to_nat cnt) (k := 0) (lvl := L) (dt := dt)
       end.
  all: try lia.
  all: try exact I.
  all: replace (pos + 2 ^ (T - nb) * 0) with pos by lia; exact PRE.
Qed.
End CD2.

Section CD0.
Variables (RNG : footprint) (x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : amem) (SPF DT SYM pos cnt bg nb T mtl bs : Z) (syb j0 : list byte).
Hypothesis HY : x2hb_hyps RNG SPF DT SYM mtl.
Hypothesis HP : 0 <= pos.
Hypothesis HB : 0 <= bg.
Hypothesis HBC : bg + cnt <= 256.
Hypothesis HC : cnt = 0.
Hypothesis HNB : 0 <= nb <= T.
Hypothesis HT : 1 <= T <= 12.
Hypothesis HM : 1 <= mtl <= 12.
Hypothesis HTM : T <= mtl.
Hypothesis HL4 : 4 <= T - nb.
Hypothesis HBS : 0 <= bs < 256.

Lemma cd_lenb0 : 16 <= 2 ^ (T - nb) <= 4096.
Proof.
  split; [replace 16 with (2 ^ 4) by reflexivity | replace 4096 with (2 ^ 12) by reflexivity];
    apply Z.pow_le_mono_r; lia.
Qed.

Lemma cd_zero : forall m dt x7 x28 x29 x30 x31 lvl, (lvl = 1 \/ lvl = 2) ->
  XHb SPF DT SYM mtl m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m -> x2pref T pos dt ->
  evtF bsegs RNG (x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m0 (pos + 2 ^ (T - nb) * cnt))
    (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
       SPF DT SYM pos bg cnt nb bs lvl (2 ^ (T - nb)) 8 0x8d5dc).
Proof.
  intros m dt x7 x28 x29 x30 x31 lvl HL I PRE.
  pose proof HY as HY'. open_hyhb HY'. open_xhb I. unfold KHIGH in KLO. unfold x2hb_hs, ASHOFF.
  pose proof cd_lenb0 as LB.
  destruct HL as [HL|HL]; subst lvl.
  all: let p1 := eval vm_compute in (APX2HB + 952) in let p2 := eval vm_compute in (APX2HB + 1048) in
       let p3 := eval vm_compute in (APX2HB + 2428) in
       kx_runFm [p1; p2; p3] 40%nat [KZRange (SYM + bg) 4096 (2^47 - 1); KZRange cnt 0 0; KZRange (2 ^ (T - nb)) 16 4096]
         (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => lia end).
  all: kx_post_regs; cbn [mem_denot].
  all: rewrite HC, Z.mul_0_r, Z.add_0_r.
  all: eapply x2hb_ret; [exact RSTF | unfold KHIGH; lia | lia | exact FR | eassumption ..].
Qed.
End CD0.

Lemma x2hb_cd : x2hb_cd_stmt.
Proof.
  unfold x2hb_cd_stmt.
  intros RNG x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m0 m SPF DT SYM pos cnt bg nb T bs
    lvl mtl syb j0 dt HY UDT USY ART0 HP HB HC0 HBC HNB HT HM HTM HL4 HROOM HL HBS I PRE.
  assert (CZ : cnt = 0 \/ 1 <= cnt) by lia. destruct CZ as [CZ|CZ].
  - eapply cd_zero. all: eassumption.
  - eapply cd_pos. all: eassumption.
Qed.
End CANSEC1.
