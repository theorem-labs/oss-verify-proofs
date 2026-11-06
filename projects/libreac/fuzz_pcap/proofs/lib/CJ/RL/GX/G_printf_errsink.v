From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.Lib Require Import SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.RL.G Require Import G_memcpy G_fwritex G_pad G_fmt_fp_lib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.RL.Reloc.RProgAt.RTac.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma es_zb_len : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma es_zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.

Lemma es_out_of : forall (W : list (Z * Z)) A N x,
  Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= x < A + N -> outside W x.
Proof.
  intros W A N x H Hx. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

Lemma es_disj : forall (W : list (Z * Z)) A N a n,
  Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
Proof.
  intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

Lemma es_implM_get_k : forall segs {S B} (k : S -> M S B) s Q ms, implM segs (k s) s Q ms -> implM segs (mbind mget k) s Q ms.
Proof. intros. exact H. Qed.

Section Img.
  Context {IMG : RImg}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)%Z}.
  Context {RL0_1 : ZFact (sym 0x34288 + 8 <= sym 0x35000)%Z}.
  Context {SPEC_fwritex : fwritex_contract}.

  Definition err_keep (Fp B : Z) (m0 m : mem) (o : list Z) : Prop :=
    forall x : word, (Fp <= bv_unsigned x < Fp + 40 \/ Fp + 48 <= bv_unsigned x < Fp + 232
                      \/ B + zlength o <= bv_unsigned x < B + SNF_CAP) -> m x = m0 x.

  Definition SINK_err (Fp : Z) (fl0 : byte) (j1 j2 j3 : list byte) (lbfw : word) (B : Z) (m0 : mem)
      (m : mem) (o : list Z) : Prop :=
    exists junk : list byte,
      wfile m Fp fl0 j1 j2 lbfw B (zb o) junk
      /\ rw_cells img_segs m (Fp + 148) [CB 84 j3]
      /\ zlength o + Z.of_nat (length junk) = SNF_CAP
      /\ (sym 0x22e18 + 8 <= Fp /\ Fp + 232 <= sym 0x34288)
      /\ GLOBALS_TOP <= B
      /\ err_keep Fp B m0 m o.

  Definition TOPOK_err (sp : Z) : Prop := True.

  Lemma err_sink_frame : forall Fp fl0 j1 j2 j3 lbfw B m0 RC RCS RE RES,
    sink_frame_stmt Fp B SNF_CAP RC RCS RE RES (SINK_err Fp fl0 j1 j2 j3 lbfw B m0).
  Proof.
    intros Fp fl0 j1 j2 j3 lbfw B m0 RC RCS RE RES.
    unfold sink_frame_stmt. intros W m m' o (junk & WF & R3 & LEN & SEPG & SEPB & KEEP) MU WM DF DB DRC DRE.
    pose proof WF as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
    pose proof (proj2 FC) as (F0 & F1 & _). cbn [cells_size csize FILE_cells Nat.add] in F0, F1.
    pose proof (es_zb_len o) as LZ. unfold zlength, SNF_CAP in *.
    exists junk. split; [|split; [|split; [exact LEN|split; [exact SEPG|split; [exact SEPB|]]]]].
    - unfold wfile. split; [|split; [|split; [exact FL|split; [exact LBF|split; [exact Bpos|split; [exact Bhi|exact SEPfb]]]]]].
      + eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
        eapply es_disj; [exact DF | lia | cbn [cells_size csize FILE_cells Nat.add]; lia | lia].
      + eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
        eapply es_disj; [exact DB | lia | cbn [cells_size csize Nat.add]; lia | lia].
    - eapply rw_cells_transport; [exact R3 | exact MU | exact WM |].
      eapply es_disj; [exact DF | lia | cbn [cells_size csize Nat.add]; lia | lia].
    - intros x Hx. rewrite (MU x); [apply KEEP; exact Hx|].
      unfold zlength, SNF_CAP in Hx. destruct Hx as [Hx|[Hx|Hx]].
      + apply (es_out_of W Fp 232); [exact DF | lia].
      + apply (es_out_of W Fp 232); [exact DF | lia].
      + apply (es_out_of W B 80); [exact DB | lia].
  Qed.

  Lemma err_sink_flags : forall Fp fl0 j1 j2 j3 lbfw B m0,
    sink_flags_stmt Fp (SINK_err Fp fl0 j1 j2 j3 lbfw B m0).
  Proof.
    intros Fp fl0 j1 j2 j3 lbfw B m0. unfold sink_flags_stmt. intros m o (junk & WF & _).
    destruct WF as (FC & _ & FL & _). exists fl0. split; [|exact FL].
    unfold FILE_cells in FC. apply (proj1 (rw_cells_app img_segs m Fp [CB 1 [fl0]] _)) in FC. exact (proj1 FC).
  Qed.

  Lemma err_topok : topok_stmt TOPOK_err.
  Proof. unfold topok_stmt, TOPOK_err. intros. exact I. Qed.

  Lemma err_out : forall Fp fl0 j1 j2 j3 lbfw B m0 RC RCS RE RES,
    out_stmt Fp B SNF_CAP RC RCS RE RES (SINK_err Fp fl0 j1 j2 j3 lbfw B m0) TOPOK_err (OUT_snf SNF_CAP).
  Proof.
    intros Fp fl0 j1 j2 j3 lbfw B m0 RC RCS RE RES.
    unfold out_stmt. intros until canary.
    intros HS SRC RNG LB Ha1 Ha2 ST LO GLO SPHI TQ SSP MI D1 D2 D3 D4 E1 E2 E3 E4 E5. rename st into o.
    pose proof (@zfact_pf _ RL0_0) as G0. pose proof (@zfact_pf _ RL0_1) as G1.
    unfold OUT_snf. apply es_implM_get_k.
    destruct (Z.leb_spec0 (zlength o + zlength bs) SNF_CAP) as [FIT|NOFIT]; [ | apply implM_unr ].
    apply implM_put.
    destruct HS as (junk & WF & R3 & LEN & SEPG & SEPB & KEEP).
    unfold OUT_DEPTH, GLOBALS_TOP in *.
    pose proof WF as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
    pose proof (proj2 FC) as (F0 & F1 & _). cbn [cells_size csize FILE_cells Nat.add] in F0, F1.
    pose proof (es_zb_len bs) as LZb. pose proof (es_zb_len o) as LZo.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
    pose proof (proj1 ST) as L0.
    assert (EFp : bv_unsigned a2 = Fp) by (subst a2; apply unsigned_lit; lia).
    destruct SSP as [SS1 SS2]. unfold got_ssp, ssp_guard in SS1, SS2.
    destruct (stk_split _ _ _ (bv_unsigned sp - 64) _ ST ltac:(lia)) as [ST1 ST2].
    unfold zlength, SNF_CAP in *. rewrite LZb in SB.
    eapply evt_mono.
    { eapply (SPEC_fwritex ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m fl0 j1 j2 lbfw B (zb o) junk (zb bs));
        rewrite ?EFp, ?LZo, ?LZb.
      - exact WF. - exact SRC. - subst a1. rewrite unsigned_lit by lia. reflexivity. - lia. - exact ST2. - exact MI.
      - lia. - destruct D1; [left|right]; lia. - destruct D2; [left|right]; lia.
      - destruct E1; [left|right]; lia. - destruct E3; [left|right]; lia.
      - destruct E2; [left|right]; lia. }
    cbv beta. intros ms' P. unfold fwritex_post in P. rewrite ?EFp, ?LZo, ?LZb in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & WF2 & SRC').
    assert (TR : forall A cs, rw_cells img_segs m A cs ->
              disjoint_from [(bv_unsigned sp - 64, bv_unsigned sp);
                             (B + Z.of_nat (length o), B + Z.of_nat (length o) + Z.of_nat (length bs));
                             (Fp + 40, Fp + 48)] A (Z.of_nat (cells_size cs)) -> rw_cells img_segs m' A cs)
      by (intros; eapply rw_cells_transport; eauto).
    unfold out_post, SR. eexists x5, x6, x7, _, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
    split; [reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. lia. }
    split; [exact WM|]. split; [exact MI'|].
    split.
    { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia]
                        | exact ST' | lia ]. }
    split.
    { rewrite <- es_zb_app in WF2.
      exists (skipn (length bs) junk).
      split; [exact WF2|].
      split; [apply TR; [exact R3|]; cbn [disjoint_from cells_size csize Nat.add]; lia|].
      split; [unfold zlength, SNF_CAP; rewrite length_app, length_skipn; lia|].
      split; [exact SEPG|]. split; [unfold GLOBALS_TOP; exact SEPB|].
      intros x Hx. unfold zlength, SNF_CAP in Hx. rewrite length_app in Hx.
      pose proof (bv_unsigned_in_range _ x) as Rx.
      rewrite (MU x); [apply KEEP; unfold zlength, SNF_CAP; lia|].
      cbn [outside]. lia. }
    split.
    { unfold ssp_cells, got_ssp, ssp_guard. split.
      - apply TR; [exact SS1|]. cbn [disjoint_from cells_size csize Nat.add]. lia.
      - apply TR; [exact SS2|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    exact SRC'.
  Qed.

End Img.
