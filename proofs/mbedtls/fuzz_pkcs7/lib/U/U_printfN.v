(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame RegsExt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemcpyLib BBFrame PrintfLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_defs U_exit_base U_fwrite_err U_printf1 U_stdio_printfbuf_base U_stdio_printfbuf.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_printfN () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "pn_post"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"].


(* [comment removed for export] *)
Record pn_mem (sp0 : word) (w : Z) (canw : word) (M : word -> option byte) : Prop := PN_MEM {
  pn_win : forall a : word, (bv_unsigned sp0 - 8388608 <= bv_unsigned a < bv_unsigned sp0)%Z -> wview RSEGS M a <> None;
  pn_ro  : forall a : Z, (0x10000 <= a < 0x4bcd8)%Z -> M (Z_to_bv 64 a) = None;
  pn_got : rdn RSEGS M (Z_to_bv 64 0x4bcd8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7d330));
  pn_rest : forall a : Z, (0x4bce0 <= a < 0x4c000)%Z -> M (Z_to_bv 64 a) = None;
  pn_canary : rdn RSEGS M (Z_to_bv 64 0x7d330) 8 = Some (word_to_le_bytes 8 canw);
  pn_file : stdout_buffered M w;
  pn_w : (0x7d798 <= w <= 0x7db96)%Z
}.

Record pn_post (sp0 : word) (w : Z) (M M' : word -> option byte) : Prop := PN_POST {
  pnp_agree : forall x : word,
      ~ (bv_unsigned sp0 - 1264 <= bv_unsigned x < bv_unsigned sp0 - 208)%Z ->
      ~ (0x4ce20 <= bv_unsigned x < 0x4ce24)%Z ->
      ~ (0x4ce48 <= bv_unsigned x < 0x4ce50)%Z ->
      ~ (w <= bv_unsigned x < w + 2)%Z -> M' x = M x;
  pnp_munch : munch [((bv_unsigned sp0 - 1264)%Z, (bv_unsigned sp0 - 208)%Z); (0x4ce20%Z, 0x4ce24%Z); (0x4ce48%Z, 0x4ce50%Z); (w, (w + 2)%Z)] M M';
  pnp_grows : mem_grows M M';
  pnp_wmono : wmono RSEGS M M';
  pnp_file  : stdout_buffered M' (w + 2);
  pnp_bytes : rdn RSEGS M' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 48; Z_to_bv 8 10]
}.

Section PN.
  Variable sp0 : word.
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Variables (w : Z) (R : bvmap 5 word) (M : word -> option byte) (canw : word).
  Hypothesis G1 : getr R 1 = Z_to_bv 64 0x1d5f8.
  Hypothesis G2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 208).
  Hypothesis G3 : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis G4 : getr R 4 = Z_to_bv 64 0x5d0c8.
  Hypothesis G11 : getr R 11 = Z_to_bv 64 0.
  Hypothesis PM : pn_mem sp0 w canw M.

  #[using="Hvsp SPlo SPhi SPal PM"] Lemma pn_pfH : pfH M (Z_to_bv 64 (bv_unsigned sp0 - 208)) w (bv_unsigned canw).
  Proof.
    pose proof SPlo. pose proof SPhi. pose proof SPal. pose proof (u64_range canw). destruct PM as [Wn RO GOT RE CA FB Hw]. destruct FB.
    split; rewrite ?u_small by lia; try lia.
    - rewrite <- Zminus_mod_idemp_l, SPal. reflexivity.
    - intros a n Ha Hn. rewrite ?u_small in Ha by lia. rewrite ?u_small in Hn by lia. unfold PF_FR in Ha.
      apply store_ok_of_all; [lia|]. intros x Hx. apply Wn. lia.
    - exact RO.
    - exact GOT.
    - exact RE.
    - exact sob_flags.
    - exact sob_wend.
    - exact sob_wpos.
    - exact sob_bsz.
    - exact sob_lock.
    - exact sob_lbf.
    - rewrite Z_to_bv_bv_unsigned. exact CA.
  Qed.

  #[using="Hvsp Hh Hlazy SPlo SPhi SPal canw G1 G2 G3 G4 G11 PM"] Theorem printfN : ltac2:(CDefT.buildp (gd_tbl_P_printfN ()) "PK,$0.P,Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PM',P,(1.&40.)(2.(1.&8.))P,(3.Vsp0,Vw,VM,R1.)(4.$5.(6.(7.(8.(9.&40.+1=5?8.)(9.&40.(:.(;.&40.Vsp0,)+=0.))(9.&40.+10800.)(9.&40.+5=0<8.)R11.R10.R?.(<.VR,(=.&5.+8.$>.))(<.VR,(=.&5.+9.$>.))R>.R=.R<.R;.R:.R9.R8.R7.(<.VR,(=.&5.+12.$>.))(<.VR,(=.&5.+13.$>.))(<.VR,(=.&5.+14.$>.))(<.VR,(=.&5.+15.$>.))(<.VR,(=.&5.+16.$>.))(<.VR,(=.&5.+17.$>.))(<.VR,(=.&5.+18.$>.))(<.VR,(=.&5.+19.$>.))(<.VR,(=.&5.+1:.$>.))(<.VR,(=.&5.+1;.$>.))R6.R5.R4.R3.)(?.&5.(1.&40.))(9.&40.+1=5?8.)(9.&20.=)(10.(1.&40.))R2.(11.$5.))Vmodel,)R12.)(4.$5.(6.(12.$13.VR,(9.&40.+1=6:4.)VM,(11.$5.))Vmodel,)R2.)")
(* [comment removed for export] *).
  Proof.
    intros K HC. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    ddestruct (printf0_buffered R M (seg_rom RSEGS) (Z_to_bv 64 (bv_unsigned sp0 - 208)) w (bv_unsigned canw) pn_pfH G1 G2 G11)
      as (R' & M' & RUN & KEEP & FRM & Bw & Bwpos & Bflags).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |].
    apply (realizes_getr_ext RSEGS
             (mkR (Z_to_bv 64 0x1d5f8) (Z_to_bv 64 (bv_unsigned sp0 - 208)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8)
                  (getr R' (Z_to_bv 5 5)) (getr R' (Z_to_bv 5 6)) (getr R' (Z_to_bv 5 7)) (getr R 8) (getr R 9)
                  (getr R' (Z_to_bv 5 10)) (getr R' (Z_to_bv 5 11)) (getr R' (Z_to_bv 5 12)) (getr R' (Z_to_bv 5 13))
                  (getr R' (Z_to_bv 5 14)) (getr R' (Z_to_bv 5 15)) (getr R' (Z_to_bv 5 16)) (getr R' (Z_to_bv 5 17))
                  (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                  (getr R 25) (getr R 26) (getr R 27)
                  (getr R' (Z_to_bv 5 28)) (getr R' (Z_to_bv 5 29)) (getr R' (Z_to_bv 5 30)) (getr R' (Z_to_bv 5 31))) R').
    { intros r. pose proof (ridx_range r) as Hi.
      rewrite <- (ridx_roundtrip r). set (i := ridx r) in *. clearbody i.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
        [ .. | lia];
        lazymatch goal with |- _ = getr R' (Z_to_bv 5 (Z.of_nat ?k)) =>
          first
            [ (transitivity (getr R' (Z_to_bv 5 (Z.of_nat k))); [reflexivity|reflexivity])
            | (rewrite (KEEP (Z_to_bv 5 (Z.of_nat k))) by (unfold callee_saved; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]));
               first [ (etransitivity; [reflexivity|]; symmetry; first [exact G1 | exact G2 | exact G3 | exact G4])
                     | (transitivity (getr R (Z_to_bv 5 (Z.of_nat k))); [reflexivity|reflexivity]) ])
            | (unfold getr; cbn; reflexivity) ]
        end. }
    change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
    replace (0x1d5f8 : word) with (Z_to_bv 64 0x1d5f8) by (apply bv_eq; reflexivity).
    apply HC.
    destruct PM as [Wn RO GOT RE CA FB Hw]. destruct FRM as [AG GR].
    assert (AG' : forall x : word,
               ~ (bv_unsigned sp0 - 1264 <= bv_unsigned x < bv_unsigned sp0 - 208)%Z ->
               ~ (0x4ce20 <= bv_unsigned x < 0x4ce24)%Z ->
               ~ (0x4ce48 <= bv_unsigned x < 0x4ce50)%Z ->
               ~ (w <= bv_unsigned x < w + 2)%Z -> M' x = M x).
    { intros x N1 N2 N3 N4. pose proof (u64_range x). apply AG. cbn [outside BBFrame.outside]. unfold in_rng.
      rewrite (u_small (bv_unsigned sp0 - 208)) by lia. rewrite !u_small by lia. repeat split; lia. }
    assert (RD : forall (a : Z) (n : nat), (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
               (a + Z.of_nat n <= bv_unsigned sp0 - 1264 \/ bv_unsigned sp0 - 208 <= a)%Z ->
               (a + Z.of_nat n <= 0x4ce20 \/ 0x4ce24 <= a)%Z ->
               (a + Z.of_nat n <= 0x4ce48 \/ 0x4ce50 <= a)%Z ->
               (a + Z.of_nat n <= w \/ w + 2 <= a)%Z ->
               rdn RSEGS M' (Z_to_bv 64 a) n = rdn RSEGS M (Z_to_bv 64 a) n).
    { intros a n H0 H1 D1 D2 D3 D4. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply AG'; rewrite u_small by lia; lia. }
    destruct FB.
    split.
    - exact AG'.
    - intros x Hout. cbn [outside] in Hout. ddestruct Hout as (O1 & O2 & O3 & O4 & _). apply AG'; lia.
    - exact GR.
    - apply mem_grows_wmono. exact GR.
    - split; try (rewrite RD by lia; assumption).
      all: first [ exact Bflags
                 | (replace (0x4ce20 + 40)%Z with 0x4ce48%Z by reflexivity; rewrite Bwpos; reflexivity) ].
    - exact Bw.
  Qed.
End PN.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
