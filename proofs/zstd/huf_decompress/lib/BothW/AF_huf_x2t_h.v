From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AF_huf_x2t_hdefs AF_huf_w4s3b AF_huf_x2t_h1 AFrameD AKit AF_huf_x2t_hd AF_huf_x2t_ha AF_huf_x2t_hb AF_huf_x2t_hc AF_huf_x2t_he2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Lemma x2hb_enter : forall (RNG : footprint) (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (m m1 : amem)
    (SPF DT SYM mtl : Z) (syb j0 : list byte) (dt : list Z),
  x2hb_hyps RNG SPF DT SYM mtl -> u8arr bsegs m DT (map (Z_to_bv 8) dt) -> zlen dt = (4 * (1 + 2 ^ mtl)) -> Forall isbyte dt ->
  bytes_at bsegs m SYM syb -> zlen syb = 256 -> x2hb_art m ->
  rw_cells bsegs m1 (SPF + -112) (X2HBFR x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 j0) -> mem_inv bsegs m1 ->
  munch [(SPF - 112, SPF)] m m1 -> wmono bsegs m m1 ->
  XHb SPF DT SYM mtl m x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt m1 /\ x2hb_art m1.
Proof.
  intros until dt. intros HY DTC DTLEN DTBY SYB SYLEN ART FR MI MU WM.
  open_hyhb HY. unfold KHIGH in KLO.
  split.
  - eapply XHb_close; try eassumption.
    + eapply u8arr_transportD; [exact DTC | exact MU |]. cbn [disjoint_from]. rewrite length_map. split; [lia | exact I].
    + eapply bytes_at_agree; [exact SYB |]. intros i Hi. apply MU. cbn [outside]. unfold wa. rewrite Z_to_bv_unsigned.
      unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. split; [lia | exact I].
    + intros x Hx. apply MU. cbn [outside] in Hx |- *. tauto.
  - eapply x2hb_art_transport; [exact ART | exact MU | exact WM |]. repeat constructor. cbn [fst]. lia.
Qed.

Ltac x2hb_case lem L :=
  let C := fresh "C" in intros C;
  lazymatch type of C with ?d = _ =>
    let P := fresh "P" in assert (P : 2 ^ d = L) by (rewrite C; reflexivity);
    rewrite P in *
  end;
  eapply lem; first [ eassumption | lia ].

Theorem x2hb_proof : x2hb_stmt.
Proof.
  unfold x2hb_stmt. intros until syb.
  intros HY MI DTC DTLEN DTBY SYB SYLEN STK ART UDT USY TP HP HB HC HBC HNB HT HM HTM HROOM HL HBS PRE.
  eapply x2hb_pro; [exact HY | exact MI | exact STK | exact ART | exact TP |].
  intros m1 j0 FR MI1 MU WM.
  destruct (x2hb_enter RNG x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 m m1 SPF DT SYM mtl syb j0 dt
              HY DTC DTLEN DTBY SYB SYLEN ART FR MI1 MU WM) as [I ART1].
  pose proof HY as HY'. open_hyhb HY'.
  eapply x2hb_disp; [exact HNB | exact HT | exact RI | exact MI1 | exact ART1 | ..].
  - let C := fresh "C" in intros C;
    let P := fresh "P" in assert (P : 2 ^ (T - nb) = 1) by (rewrite C; reflexivity);
    rewrite P in *; rewrite Z.mul_1_l in *;
    eapply x2hb_c1; first [ eassumption | lia ].
  - x2hb_case x2hb_c2 2.
  - x2hb_case x2hb_c4 4.
  - x2hb_case x2hb_c8 8.
  - intros C. pose proof x2hb_cd as CD. unfold x2hb_cd_stmt in CD. eapply CD; first [ eassumption | lia ].
Qed.
End CANSEC1.
