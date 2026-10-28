(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt HeapIface CellsX Cells Mem Step Frame Tac AStep Asn1Aux Asn1AuxA X509Aux X509AuxB MState.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import H3Tac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.
Set Printing Width 200.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma land64_zero : forall r, -2^63 <= r < 2^63 -> Z.land r 18446744073709551615 = 0 -> r = 0.
Proof.
  intros r Hr H. change 18446744073709551615 with (Z.ones 64) in H. rewrite Z.land_ones in H by lia.
  destruct (Z.lt_ge_cases r 0); [| rewrite Z.mod_small in H by lia; exact H].
  rewrite <- (Z.mod_add r 1 (2^64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
Qed.
Lemma land64_nonzero : forall r, -2^63 <= r < 2^63 -> Z.land r 18446744073709551615 <> 0 -> r <> 0.
Proof. intros r Hr H ->. apply H. reflexivity. Qed.
Lemma mod64_zero : forall r, -2^63 <= r < 2^63 -> r mod 18446744073709551616 = 0 -> r = 0.
Proof.
  intros r Hr H. destruct (Z.lt_ge_cases r 0); [| rewrite Z.mod_small in H by lia; exact H].
  rewrite <- (Z.mod_add r 1 18446744073709551616) in H by lia. rewrite Z.mod_small in H by lia. lia.
Qed.
Lemma mod64_nonzero : forall r, -2^63 <= r < 2^63 -> r mod 18446744073709551616 <> 0 -> r <> 0.
Proof. intros r Hr H ->. apply H. reflexivity. Qed.
(* [comment removed for export] *)
Ltac kzero K := first [apply land64_zero in K; [| lia] | apply mod64_zero in K; [| lia] | idtac].
Ltac knz K := first [apply land64_nonzero in K; [| lia] | apply mod64_nonzero in K; [| lia] | idtac].
Ltac b2z_close k :=
  exfalso;
  repeat match type of k with context [Z.ltb ?a ?b] =>
    first [ let H := fresh in assert (H : a < b) by lia; apply Z.ltb_lt in H; rewrite H in k; clear H
          | let H := fresh in assert (H : b <= a) by lia; apply Z.ltb_ge in H; rewrite H in k; clear H ] end;
  cbn in k; first [discriminate k | lia].
Ltac al8_close k := exfalso; rewrite ?unsigned_lit in k by lia; change 7 with (Z.ones 3) in k; rewrite Z.land_ones in k by lia; change (2 ^ 3) with 8 in k; lia.
(* [comment removed for export] *)
Lemma swrap32_land_errsum : forall r c, -0x10000 < r <= 0 -> 2^64 - 0x10000 <= c < 2^64 ->
  bv_swrap 32 (Z.land r 18446744073709551615 + c) = r + (c - 2^64).
Proof.
  intros r c Hr Hc. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply swrap32_errsum; lia.
Qed.

Lemma rw_cells_blob segs m A0 cs : rw_cells segs m A0 cs -> rw_cells segs m A0 [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros H. pose proof H as H'. destruct H' as [[Hwf _] _].
  eapply rw_cells_reshape; [exact H| cbn; split; [apply cells_bytes_length; exact Hwf| exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
Qed.

Definition U_PKCS7_GETCERTS : Z := 0x1deb8.
Definition U_X509_CRT_PARSE_DER : Z := 0x26a28.

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variable PK : pk_class usegs.
  Variable SI : sinv L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis CRTPARSE : x509_crt_parse_der_stmt usegs L HI PK SI U_X509_CRT_PARSE_DER.

  Section Body.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
              (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (PP P END BUF CRT lo : Z) (bs : list byte).
    Hypothesis HH : HEAP usegs L HI h LB m mo.
    Hypothesis HPP : rw_cells usegs m PP [C8 (Z_to_bv 64 P)].
    Hypothesis ALP : PP mod 8 = 0.
    Hypothesis BY : bytes_at usegs m BUF bs.
    Hypothesis BIN : In (BUF, Z.of_nat (length bs)) LB.
    Hypothesis B1 : BUF <= P.  Hypothesis B2 : P <= END.  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
    Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.  Hypothesis B5 : 0 < BUF.
    Hypothesis B6 : Z.of_nat (length bs) < 2^30.
    Hypothesis CZ : crt_zero usegs m CRT.
    Hypothesis ALC : CRT mod 8 = 0.
    Hypothesis PP1 : bv_unsigned sp <= PP.  Hypothesis PP2 : PP + 8 <= heap_top usegs L HI h.
    Hypothesis CR1 : bv_unsigned sp <= CRT. Hypothesis CR2 : CRT + CRT_SIZE <= heap_top usegs L HI h.
    Hypothesis D1 : PP + 8 <= CRT \/ CRT + CRT_SIZE <= PP.
    Hypothesis ST : stk usegs m lo (bv_unsigned sp).
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis SLO : lo <= bv_unsigned sp - PKCS7_GETCERTS_STACK - hl_stack L.
    Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
    Hypothesis SPTOP : bv_unsigned sp <= heap_top usegs L HI h.
    Hypothesis MI : mem_inv usegs m.
    Hypothesis SO : statics_ok usegs L m.
    Hypothesis SIP : si_P SI m.
    Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
    Hypothesis SPR : 0 <= bv_unsigned sp < 2 ^ 64.

    Let LOSP : lo <= bv_unsigned sp + -80. Proof. unfold PKCS7_GETCERTS_STACK in SLO. lia. Qed.
    Let BCE : BUF + Z.of_nat (length bs) <= alloc_ceiling.
    Proof.
      destruct (heap_blocks usegs L HI _ _ _ _ HH) as [BR _]. rewrite Forall_forall in BR.
      destruct (BR _ BIN) as (_ & _ & _ & Bce & _). exact Bce.
    Qed.

    Notation POST := (pkcs7_get_certs_post usegs L HI PK SI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP P END CRT lo m mo).
    Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -80)).
    Notation X00 := [(PP, PP + 8); (CRT, CRT + 744)].
    Notation X0 := ([(PP, PP + 8); (CRT, CRT + 744)] ++ si_fp SI).
    Definition SAVED : list cell := [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

    Ltac zofnat H := cbn [cells_size csize Nat.add length] in H;
      repeat match type of H with context [Z.of_nat (Datatypes.S ?k)] => let v := eval vm_compute in (Z.of_nat (Datatypes.S k)) in change (Z.of_nat (Datatypes.S k)) with v in H end;
      repeat match type of H with context [Z.add (Z.add ?a ?b) ?c] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (Z.add b c) in replace (Z.add (Z.add a b) c) with (Z.add a v) in H by lia end.
    Ltac fix_ret pc := replace (ret_pc (Z_to_bv 64 pc)) with (Z_to_bv 64 pc : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    Ltac kz K := unfold CRT_SIZE in *; first [ rewrite Z.mod_small in K by lia
                       | change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by lia; rewrite Z.mod_small in K by lia
                       | apply land64_zero in K; [| lia] | apply mod64_zero in K; [| lia]
                       | apply land64_nonzero in K; [| lia] | apply mod64_nonzero in K; [| lia] | idtac ].
    Ltac joinr H1 H2 :=
      lazymatch type of H1 with rw_cells ?sg ?mm ?A1 ?cs1 =>
      lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
        replace A2 with (A1 + Z.of_nat (cells_size cs1)) in H2 by (cbn; lia);
        let Hj := fresh "J" in
        pose proof (proj2 (rw_cells_app sg mm A1 cs1 cs2) (conj H1 H2)) as Hj; clear H1 H2; rename Hj into H1;
        cbn [app] in H1
      end end.
    (* [comment removed for export] *)
    Ltac spine_firstn k cs :=
      let k := eval cbv in k in
      lazymatch k with
      | Datatypes.O => eval lazy beta iota delta [firstn] in (firstn Datatypes.O cs)
      | Datatypes.S ?k' => lazymatch cs with
                 | ?c :: ?cs' => let r := spine_firstn k' cs' in constr:(c :: r)
                 | _ => eval cbv beta iota delta [firstn] in (firstn k cs)
                 end
      end.
    Ltac spine_skipn k cs :=
      let k := eval cbv in k in
      lazymatch k with
      | Datatypes.O => cs
      | Datatypes.S ?k' => lazymatch cs with
                 | _ :: ?cs' => spine_skipn k' cs'
                 | _ => eval cbv beta iota delta [skipn] in (skipn k cs)
                 end
      end.
    Ltac splitat H k H2 :=
      lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
        let l1 := spine_firstn k cs in
        let l2 := spine_skipn k cs in
        change (rw_cells sg mm A0 (l1 ++ l2)) in H;
        let H1 := fresh "SP" in
        destruct (proj1 (rw_cells_app sg mm A0 l1 l2) H) as [H1 H2]; clear H; rename H1 into H; zofnat H2
      end.

    (* [comment removed for export] *)
    Definition wfp (W : list ivl) : Prop := forall a, ~ outside W a -> (PP <= a < PP + 8) \/ (lo <= a < bv_unsigned sp).

    #[using="HLS m mo BUF CRT bs HH BIN B5 PP1 PP2 CR1 CEIL SLO SPR LOSP BCE"] Lemma HEAPm : forall W Lc hc mA mB moc,
      HEAP usegs L HI hc (Lc ++ LB) mA moc -> heap_top usegs L HI hc = heap_top usegs L HI h ->
      munch W mA mB -> wmono usegs mA mB -> wfp W -> HEAP usegs L HI hc (Lc ++ LB) mB moc.
    Proof.
      intros W Lc hc mA mB moc HHc HTc MU WM HW.
      eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HHc | exact CEIL | exact MU | exact WM |].
      intros a Ha Hna. destruct (HW a Hna) as [H1|H3]; left; rewrite HTc; lia.
    Qed.

    #[using="HLS DHI bs PP1 CR1 CEIL SLO SPR LOSP"] Lemma HPXm : forall W Lx hc mA mB moc,
      HEAP usegs L HI hc Lx mA moc -> munch W mA mB -> wmono usegs mA mB -> wfp W ->
      heap_presx usegs L Lx (bv_unsigned sp) X0 mA mB.
    Proof.
      intros W Lx hc mA mB moc HHc MU WM HW a Ha Hc Ho. split; [| apply WM].
      destruct (outside_dec W a) as [O|NO]; [apply MU; rewrite wa_unsigned by lia; exact O|]. exfalso.
      destruct (heap_blocks usegs L HI _ _ _ _ HHc) as [BR AP]. rewrite Forall_forall in BR.
      destruct (HW a NO) as [H1|H3]; cbn [outside app] in Ho; ddestruct Ho as (HoA & HoB & _); [lia|].
      destruct Hc as [C|[[C1 C2]|(b & Hb & Hr)]]; [lia| pose proof alloc_ceiling_pos; lia|].
      ddestruct (BR b Hb) as (_ & _ & _ & Bce & _). lia.
    Qed.

    #[using="bs"] Lemma HPXsub : forall Lc mA mB, heap_presx usegs L (Lc ++ LB) (bv_unsigned sp) X0 mA mB -> heap_presx usegs L LB (bv_unsigned sp) X0 mA mB.
    Proof. intros Lc mA mB HP. eapply heap_presx_weaken; [exact HP| intros b Hb; apply in_or_app; right; exact Hb| lia| intros x Hx; exact Hx]. Qed.

    #[using="HI HLS sp m mo h LB BUF lo bs HH BIN B5 PP1 CR1 D1 CEIL SLO SPR LOSP BCE"] Lemma X0_above : fp_above X00 alloc_ceiling.
    Proof. pose proof LOSP. unfold fp_above. repeat constructor; cbn; unfold CRT_SIZE in *; lia. Qed.
    #[using="DIMG"] Lemma XAV : forall X hc Lx mA moc, HEAP usegs L HI hc Lx mA moc -> fp_above X alloc_ceiling -> fp_avoids (X ++ si_fp SI) Lx.
    Proof. intros X hc Lx mA moc HHc HX. eapply (fp_avoids_above_si usegs L SI HI); [exact HHc| exact HX| exact (proj1 DIMG)| exact (proj2 DIMG)]. Qed.
    Ltac si_md MU := lazymatch goal with H : si_P SI _ |- _ =>
      eapply (si_munch_offdata L SI) in H; [| exact MU| intros a Da Wa; cbn [outside]; unfold CRT_SIZE in *; lia] end.

    #[using="HLS DHI CRT bs PP1 CR1 CEIL SLO SPR LOSP"] Lemma SOm : forall W mA mB, statics_ok usegs L mA -> munch W mA mB -> wfp W -> statics_ok usegs L mB.
    Proof.
      intros W mA mB SO0 MU HW. eapply statics_ok_munch; [exact SO0| exact MU|].
      intros a Ha Hnw. destruct (outside_dec W a) as [Ho|Hno]; [exact Ho|]. exfalso. pose proof alloc_ceiling_pos.
      destruct (HW a Hno) as [H1|H3]; lia.
    Qed.

    (* [comment removed for export] *)
    #[using="HLS bs SLO SPR LOSP"] Lemma L_RET : forall (fr : list cell) Lc mc moc hc (r p : Z) (f : crt_own) (j : crt_junk)
        (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
      rw_cells usegs mc (bv_unsigned sp + -80) (fr ++ SAVED) -> Z.of_nat (cells_size fr) = 24 ->
      HEAP usegs L HI hc (Lc ++ LB) mc moc -> heap_top usegs L HI hc = heap_top usegs L HI h -> mo_frame mo moc ->
      heap_presx usegs L LB (bv_unsigned sp) X0 m mc ->
      rw_cells usegs mc PP [C8 (Z_to_bv 64 p)] -> P <= p <= END ->
      crt_at usegs PK mc (Lc ++ LB) CRT f j -> Permutation Lc (crt_blocks f) ->
      mem_inv usegs mc -> statics_ok usegs L mc -> si_P SI mc -> stk usegs mc lo (bv_unsigned sp + -80) ->
      -2^31 < r <= 1 ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1df68) fc None mc (seg_rom usegs)).
    Proof.
      intros fr Lc mc moc hc r p f j x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31
             FR SZ HHc HTc MFc HPXc PPc Hp CA PERM MIc SOc SIc STc Hr.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof LOSP as LOSP'.
      destruct (proj1 (rw_cells_app usegs mc _ fr SAVED) FR) as [FRj SV]. unfold SAVED in SV. rewrite SZ in SV.
      replace (bv_unsigned sp + -80 + 24) with (bv_unsigned sp + -56) in SV by lia.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.  (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      pose proof (stk_release usegs _ _ _ _ STc FR ltac:(lia)) as STf. rewrite cells_size_app in STf. unfold SAVED in STf.
      cbn [cells_size csize Nat.add] in STf. rewrite Nat2Z.inj_add, SZ in STf.
      replace (bv_unsigned sp + -80 + (24 + Z.of_nat 56)) with (bv_unsigned sp) in STf by lia.
      apply aevtM_done. unfold pkcs7_get_certs_post.
      deexists 15. dexists mc, moc, hc, r, p, f, j, Lc.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact Hr|]. split; [exact MIc|]. split; [exact SOc|].
      split; [exact SIc|]. split; [exact STf|].
      split; [exact MFc|]. split; [exact HTc|]. split; [exact PPc|]. split; [exact Hp|].
      split; [exact CA|]. split; [exact PERM|]. split; [exact HHc|]. unfold CRT_SIZE. exact HPXc.
    Qed.

    (* [comment removed for export] *)
    #[using="HLS DIMG DHI CRTPARSE BUF bs HH HPP ALP BY BIN B1 B2 B3 B4 B5 B6 CZ ALC PP1 PP2 CR1 CR2 D1 ST CEIL SLO SP16 SPTOP MI SO SIP TP SPR LOSP BCE"] Lemma ENTRY : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      aevtM usegs mo POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 CRT) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1deb8) fc None m (seg_rom usegs)).
    Proof.
      intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
      pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof LOSP as LOSP'. pose proof alloc_ceiling_pos as ACP. pose proof BCE as BCE'.
      pose proof (unsigned_lit (bv_unsigned sp + -80) ltac:(lia)) as USP.
      pose proof (rw_cells_bound usegs m PP _ HPP) as PPB. cbn [cells_size csize Nat.add] in PPB.
      pose proof (rw_cells_bound usegs m CRT _ CZ) as CRB. cbn [cells_size csize Nat.add] in CRB.
      pose proof BY as BY0. pose proof CZ as CZ0. pose proof HPP as HPP0. pose proof SO as SO0. pose proof ST as ST0. pose proof MI as MI0. pose proof HH as HH0. pose proof SIP as SI0.
      set (m_entry := m) in BY, CZ, HPP, SO, ST, MI, HH, SIP.   (* [comment removed for export] *)
      pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl usegs m) as WM0.
      pose proof (conj CZ0 (conj HPP0 (conj BY0 (conj HH0 I)))) as CBOX. clear CZ0 HPP0 BY0 HH0.
      zstep. carve_frame 80%nat ST0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
      zstep. zstep.                            (* [comment removed for export] *)
      zstep. zstep.                            (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
      ddestruct CBOX as (CZ0 & HPP0 & BY0 & HH0 & _).
      assert (WF0 : wfp [(bv_unsigned sp - 80, bv_unsigned sp)]) by (intros a Hna; cbn [outside] in Hna; first [clear_disj; lia | lia]).
      pose proof (HEAPm _ [] _ _ _ _ HH0 eq_refl MU0 WM0 WF0) as HHm0.
      pose proof (HPXm _ _ _ _ _ _ HH0 MU0 WM0 WF0) as HPX0'.
      lazymatch type of SO0 with statics_ok _ _ m0 => rename SO0 into SO1 | _ => pose proof (SOm _ _ _ SO0 MU0 WF0) as SO1; clear SO0 end.
      lazymatch type of SI0 with si_P _ m0 => idtac | _ => si_md MU0 end.
      pose proof (rw_cells_transport usegs _ m m0 _ _ CZ0 MU0 WM0 ltac:(cbn; unfold CRT_SIZE in *; lia)) as CZ1.
      pose proof (rw_cells_transport usegs _ m m0 _ _ HPP0 MU0 WM0 ltac:(cbn; lia)) as HPP1.
      pose proof (bytes_at_transport usegs _ m m0 _ _ BY0 MU0 ltac:(cbn; lia)) as BY1.
      clear CZ0 HPP0 BY0 MU0 WM0 MK HH0. pose proof (heap_mok _ _ HI _ _ _ _ HHm0) as MK.
      (* [comment removed for export] *)
      zstep. zstep. zstep.                     (* [comment removed for export] *)
      lazymatch goal with H : rw_cells usegs m0 (bv_unsigned sp + -80) _ |- _ => rename H into FR end.
      splitat FR 1%nat L2. splitat L2 1%nat L1. splitat L1 1%nat SV.   (* [comment removed for export] *)
      pose proof U_asn1_get_tag_spec as SPT. unfold asn1_get_tag_stmt, U_ASN1_GET_TAG in SPT.
      eapply aevtM_cut_evt; [exact MK | |].
      { eapply SPT with (PP := PP) (LENP := bv_unsigned sp + -64) (P := P) (END := END) (BUF := BUF) (bs := bs) (tag := 160);
          try eassumption; try reflexivity; rewrite ?USP; try eassumption; try (unfold CRT_SIZE in *; plia);
          try (clear - SP16 SPR LOSP' CEIL ACP; Z.div_mod_to_equations; lia). }
      intros ms' PO. ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m1 & r & p1 & Lw
                                 & -> & MU1 & WM1 & MI1 & -> & Hr & PPc1 & LEN1 & Hp1' & HOK).
      rewrite ?USP in MU1. fix_ret 0x1def4. clear SPT.
      assert (WF1 : wfp [(PP, PP + 8); (bv_unsigned sp + -64, bv_unsigned sp + -64 + 8)]) by (intros a Hna; cbn [outside] in Hna; first [clear_disj; lia | lia]).
      pose proof (HEAPm _ [] _ _ _ _ HHm0 eq_refl MU1 WM1 WF1) as HH1.
      pose proof (HPXm _ _ _ _ _ _ HHm0 MU1 WM1 WF1) as HPX01. cbn [app] in HPX01.
      assert (HPX1 : heap_presx usegs L LB (bv_unsigned sp) X0 m m1) by (eapply heap_presx_trans; [exact HPX0'| exact HPX01]).
      pose proof (SOm _ _ _ SO1 MU1 WF1) as SO2. si_md MU1.
      pose proof (rw_cells_transport usegs _ m0 m1 _ _ CZ1 MU1 WM1 ltac:(cbn; unfold CRT_SIZE in *; lia)) as CZ2.
      pose proof (rw_cells_transport usegs _ m0 m1 _ _ SV MU1 WM1 ltac:(cbn; lia)) as SV2.
      pose proof (rw_cells_transport usegs _ m0 m1 _ _ FR MU1 WM1 ltac:(cbn; lia)) as FJ2.
      pose proof (rw_cells_transport usegs _ m0 m1 _ _ L2 MU1 WM1 ltac:(cbn; lia)) as L22.
      pose proof (bytes_at_transport usegs _ m0 m1 _ _ BY1 MU1 ltac:(cbn; lia)) as BY2.
      lazymatch goal with H : stk usegs m0 _ _ |- _ => pose proof (stk_transport_disjoint usegs _ m0 m1 _ _ H MU1 WM1 ltac:(cbn; lia)) as ST2; clear H end.
      clear HHm0 HPX0' HPX01 SO1 MU1 WM1 MK CZ1 HPP1 BY1 SV FR L2 L1. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
      pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn in LR.
      cbn [app] in HH1.
      pose proof (crt_at_of_zero usegs PK m1 LB CRT CZ2 ALC ltac:(lia)) as CA2.
      zstep. zstep. if_cases KU; zify_cond KU.
      { (* [comment removed for export] *)
        zstep. zstep.
        eapply (L_RET [CB 8 _; C8 _; C8 _] [] m1 mo h 0 p1 crt_own_zero crt_junk_zero);
          [unfold SAVED; joinr FJ2 L22; joinr FJ2 LEN1; joinr FJ2 SV2; exact FJ2| reflexivity| exact HH1| reflexivity| apply mo_frame_refl| exact HPX1
          | exact PPc1| lia| exact CA2| rewrite crt_blocks_zero; apply Permutation_refl| exact MI1| exact SO2| exact SI0| exact ST2| lia]. }
      zstep. if_cases KT; zify_cond KT.
      { (* [comment removed for export] *)
        kz KT. zstep. zstep. zstep. zstep.     (* [comment removed for export] *)
        try match goal with |- context [Some (Z_to_bv 64 (bv_swrap 32 ?e))] =>
          replace (bv_swrap 32 e) with (r - 21248)
            by (unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
                change (2 ^ Z.of_N 32) with 4294967296; change (4294967296 `div` 2) with 2147483648;
                clear - Hr KT KU; Z.div_mod_to_equations; lia) end.
        zstep; if_cases KC1; zify_cond KC1; [exfalso; rewrite ?signed_lit64 in KC1 by lia; lia|].
        eapply (L_RET [CB 8 _; C8 _; C8 _] [] m1 mo h _ p1 crt_own_zero crt_junk_zero);
          [unfold SAVED; joinr FJ2 L22; joinr FJ2 LEN1; joinr FJ2 SV2; exact FJ2| reflexivity| exact HH1| reflexivity| apply mo_frame_refl| exact HPX1
          | exact PPc1| lia| exact CA2| rewrite crt_blocks_zero; apply Permutation_refl| exact MI1| exact SO2| exact SI0| exact ST2| lia]. }
      (* [comment removed for export] *)
      kz KT. subst r. destruct (HOK eq_refl) as [Hp1a HLw].
      zstep. zstep; if_cases KA0; zify_cond KA0; [al8_close KA0|].
      zstep. zstep. zstep.                     (* [comment removed for export] *)
      zstep; if_cases KW0; zify_cond KW0; [exfalso; lia|].
      zstep. zstep. zstep. zstep; if_cases KN0; zify_cond KN0; [b2z_close KN0|].
      zstep. zstep. zstep. zstep. zstep.       (* [comment removed for export] *)
      pose proof U_asn1_get_tag_spec as SPT. unfold asn1_get_tag_stmt, U_ASN1_GET_TAG in SPT.
      eapply aevtM_cut_evt; [exact MK | |].
      { eapply SPT with (PP := PP) (LENP := bv_unsigned sp + -72) (P := p1) (END := p1 + bv_unsigned Lw) (BUF := BUF) (bs := bs) (tag := 48);
          try eassumption; try reflexivity; rewrite ?USP; try eassumption; try (unfold CRT_SIZE in *; plia);
          try (clear - SP16 SPR LOSP' CEIL ACP; Z.div_mod_to_equations; lia). }
      intros ms' PO. ddestruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m2 & r2 & p2 & Lw2
                                 & -> & MU2 & WM2 & MI2 & -> & Hr2 & PPc2 & LEN2 & Hp2' & HOK2).
      rewrite ?USP in MU2. fix_ret 0x1df3c. clear SPT.
      assert (WF2 : wfp [(PP, PP + 8); (bv_unsigned sp + -72, bv_unsigned sp + -72 + 8)]) by (intros a Hna; cbn [outside] in Hna; first [clear_disj; lia | lia]).
      pose proof (HEAPm _ [] _ _ _ _ HH1 eq_refl MU2 WM2 WF2) as HH2. cbn [app] in HH2.
      pose proof (HPXm _ _ _ _ _ _ HH1 MU2 WM2 WF2) as HPX12. cbn [app] in HPX12.
      assert (HPX2 : heap_presx usegs L LB (bv_unsigned sp) X0 m m2) by (eapply heap_presx_trans; [exact HPX1| exact HPX12]).
      pose proof (SOm _ _ _ SO2 MU2 WF2) as SO3. si_md MU2.
      pose proof (rw_cells_transport usegs _ m1 m2 _ _ CZ2 MU2 WM2 ltac:(cbn; unfold CRT_SIZE in *; lia)) as CZ3.
      pose proof (rw_cells_transport usegs _ m1 m2 _ _ SV2 MU2 WM2 ltac:(cbn; lia)) as SV3.
      pose proof (rw_cells_transport usegs _ m1 m2 _ _ FJ2 MU2 WM2 ltac:(cbn; lia)) as FJ3.
      pose proof (rw_cells_transport usegs _ m1 m2 _ _ LEN1 MU2 WM2 ltac:(cbn; lia)) as L13.
      pose proof (bytes_at_transport usegs _ m1 m2 _ _ BY2 MU2 ltac:(cbn; lia)) as BY3.
      pose proof (stk_transport_disjoint usegs _ m1 m2 _ _ ST2 MU2 WM2 ltac:(cbn; lia)) as ST3.
      clear HH1 HPX1 HPX12 SO2 MU2 WM2 MK CZ2 SV2 FJ2 LEN1 BY2 ST2 PPc1 CA2. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
      pose proof (bv_unsigned_in_range 64 Lw2) as LR2. unfold bv_modulus in LR2. cbn in LR2.
      pose proof (crt_at_of_zero usegs PK m2 LB CRT CZ3 ALC ltac:(lia)) as CA3.
      zstep. if_cases KT2; zify_cond KT2.
      2:{ (* [comment removed for export] *)
        kz KT2. zstep. zstep. zstep.           (* [comment removed for export] *)
        zstep. zstep.
        first [rewrite swrap32_land_errsum by lia | rewrite swrap32_errsum by lia].
        zstep; if_cases KC2; zify_cond KC2; [exfalso; rewrite ?signed_lit64 in KC2 by lia; lia|].  (* [comment removed for export] *)
        eapply (L_RET [CB 8 _; C8 _; C8 _] [] m2 mo h _ p2 crt_own_zero crt_junk_zero);
          [unfold SAVED; joinr FJ3 LEN2; joinr FJ3 L13; joinr FJ3 SV3; exact FJ3| reflexivity| exact HH2| reflexivity| apply mo_frame_refl| exact HPX2
          | exact PPc2| lia| exact CA3| rewrite crt_blocks_zero; apply Permutation_refl| exact MI2| exact SO3| exact SI0| exact ST3| lia]. }
      kz KT2. subst r2. destruct (HOK2 eq_refl) as [Hp2a HLw2].
      zstep. zstep. zstep. zstep; if_cases KW1; zify_cond KW1; [exfalso; lia|].
      zstep. zstep. zstep. zstep; if_cases KN1; zify_cond KN1; [b2z_close KN1|].
      zstep.              (* [comment removed for export] *)
      zstep. if_cases KE; zify_cond KE; rewrite ?unsigned_lit in KE by lia.
      2:{ (* [comment removed for export] *)
        zstep. zstep.                          (* [comment removed for export] *)
        try match goal with |- context [Some (Z_to_bv 64 (bv_swrap 32 ?e))] =>
          replace (Z_to_bv 64 (bv_swrap 32 e) : word) with (Z_to_bv 64 (-21376) : word) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (L_RET [CB 8 _; C8 _; C8 _] [] m2 mo h _ p2 crt_own_zero crt_junk_zero);
          [unfold SAVED; joinr FJ3 LEN2; joinr FJ3 L13; joinr FJ3 SV3; exact FJ3| reflexivity| exact HH2| reflexivity| apply mo_frame_refl| exact HPX2
          | exact PPc2| lia| exact CA3| rewrite crt_blocks_zero; apply Permutation_refl| exact MI2| exact SO3| exact SI0| exact ST3| lia]. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.              (* [comment removed for export] *)
      pose proof CRTPARSE as SPC. unfold x509_crt_parse_der_stmt, U_X509_CRT_PARSE_DER in SPC.
      eapply aevtM_cut.
      { eapply SPC with (Q := p1) (blen := bv_unsigned Lw) (BUF := BUF) (bs := bs) (CRT := CRT) (lo := lo) (h := h) (LB := LB);
          try reflexivity; rewrite ?USP; try eassumption; try (unfold CRT_SIZE in *; plia);
          try (clear - SP16 SPR LOSP' CEIL ACP; Z.div_mod_to_equations; lia).
        - unfold PKCS7_GETCERTS_STACK in SLO. unfold X509_CRT_PARSE_STACK. lia.
        - symmetry. apply Z_to_bv_bv_unsigned. }
      intros ms' mo'x PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m3 & mo3 & h3 & r3 & f3 & j3 & LBc
                      & E0 & -> & Hr3 & MI3 & SO4 & SI4 & ST4 & MF3 & HT3 & CA4 & PERM3 & HH3 & HPX3).
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite ?USP in ST4. rewrite ?USP in HPX3. fix_ret 0x1dfcc. clear SPC.
      assert (XD : forall A0 kk, (A0 + kk <= CRT \/ CRT + 744 <= A0) -> alloc_ceiling <= A0 -> disjoint_from ([(CRT, CRT + CRT_SIZE)] ++ si_fp SI) A0 kk)
        by (intros A0 kk Y1 Y2; apply disjoint_from_app_intro; [cbn; unfold CRT_SIZE; lia| apply (si_fp_disjoint_hi L SI); lia]).
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX3 FJ3 ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn; lia)) as FJ4.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX3 LEN2 ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn; lia)) as LEN24.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX3 L13 ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn; lia)) as L14.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX3 SV3 ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn; lia)) as SV4.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX3 PPc2 ltac:(apply client_range_stack; lia) ltac:(apply XD; unfold CRT_SIZE in *; cbn; lia)) as PPc4.
      assert (HPX4 : heap_presx usegs L LB (bv_unsigned sp) X0 m m3).
      { eapply heap_presx_trans; [exact HPX2|]. eapply heap_presx_weaken; [exact HPX3| intros b Hb; exact Hb| lia| unfold CRT_SIZE; intros x Hx; cbn [outside app] in Hx |- *; ddestruct Hx as (HxA & HxB & HxS); split; [lia| exact HxS]]. }
      clear HH2 HPX2 HPX3 SO3 CZ3 SV3 FJ3 LEN2 L13 BY3 ST3 PPc2 CA3 MK. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK.
      zstep. if_cases KR; zify_cond KR; rewrite ?signed_lit64 in KR by lia.
      { (* [comment removed for export] *)
        zstep. zstep.                          (* [comment removed for export] *)
        try match goal with |- context [Some (Z_to_bv 64 (bv_swrap 32 ?e))] =>
          replace (Z_to_bv 64 (bv_swrap 32 e) : word) with (Z_to_bv 64 (-21888) : word) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (L_RET [CB 8 _; C8 _; C8 _] LBc m3 mo3 h3 _ p2 f3 j3);
          [unfold SAVED; joinr FJ4 LEN24; joinr FJ4 L14; joinr FJ4 SV4; exact FJ4| reflexivity| exact HH3| exact HT3| exact MF3| exact HPX4
          | exact PPc4| lia| exact CA4| exact PERM3| exact MI3| exact SO4| exact SI4| exact ST4| lia]. }
      (* [comment removed for export] *)
      pose proof (conj HH3 (conj FJ4 (conj LEN24 (conj L14 (conj SV4 (conj CA4 I)))))) as CBOX. clear HH3 FJ4 LEN24 L14 SV4 CA4.
      pose proof (munch_refl [(PP, PP + 8)] m3) as MU5. pose proof (wmono_refl usegs m3) as WM5.
      zstep.                                   (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
      ddestruct CBOX as (HH3 & FJ4 & LEN24 & L14 & SV4 & CA4 & _).
      assert (WF5 : wfp [(PP, PP + 8)]) by (intros a Hna; cbn [outside] in Hna; first [clear_disj; lia | lia]).
      pose proof (HEAPm _ _ _ _ _ _ HH3 HT3 MU5 WM5 WF5) as HH5.
      pose proof (HPXm _ _ _ _ _ _ HH3 MU5 WM5 WF5) as HPX35.
      assert (HPX5 : heap_presx usegs L LB (bv_unsigned sp) X0 m m4) by (eapply heap_presx_trans; [exact HPX4| apply (HPXsub LBc); exact HPX35]).
      lazymatch type of SO4 with statics_ok _ _ m4 => rename SO4 into SO5 | _ => pose proof (SOm _ _ _ SO4 MU5 WF5) as SO5; clear SO4 end.
      lazymatch type of SI4 with si_P _ m4 => idtac | _ => si_md MU5 end.
      pose proof (rw_cells_transport usegs _ m3 m4 _ _ FJ4 MU5 WM5 ltac:(cbn; lia)) as FJ5.
      pose proof (rw_cells_transport usegs _ m3 m4 _ _ LEN24 MU5 WM5 ltac:(cbn; lia)) as LEN25.
      pose proof (rw_cells_transport usegs _ m3 m4 _ _ L14 MU5 WM5 ltac:(cbn; lia)) as L15.
      pose proof (rw_cells_transport usegs _ m3 m4 _ _ SV4 MU5 WM5 ltac:(cbn; lia)) as SV5.
      lazymatch type of ST4 with stk _ m4 _ _ => rename ST4 into ST5 | _ => pose proof (stk_transport_disjoint usegs _ m3 m4 _ _ ST4 MU5 WM5 ltac:(cbn; lia)) as ST5; clear ST4 end.
      assert (CA5 : crt_at usegs PK m4 (LBc ++ LB) CRT f3 j3).
      { ddestruct CA4 as (CC4 & AL4 & POS4 & BND4 & OWN4). split; [| split; [exact AL4| split; [exact POS4| split; [exact BND4|]]]].
        - eapply rw_cells_transport; [exact CC4| exact MU5| exact WM5| ].
          change (Z.of_nat (cells_size (crt_cells f3 j3))) with 744. cbn [disjoint_from]. unfold CRT_SIZE in *. lia.
        - eapply (crt_own_ok_presx3' usegs L PK); [exact OWN4| | eapply heap_presx_weaken; [exact HPX35| intros b Hb; exact Hb| apply Z.le_refl| intros x Hx; exact Hx]
                                    | eapply blocks_below_of_HEAP; exact HH3| eapply XAV; [exact HH3| exact X0_above] | lia| assumption].
          intros b Hb. apply in_or_app. left. eapply Permutation_in; [apply Permutation_sym; exact PERM3| exact Hb]. }
      lazymatch goal with H : mem_inv usegs m4 |- _ => rename H into MI5 | _ => idtac end.
      zstep. zstep.                            (* [comment removed for export] *)
      eapply (L_RET [CB 8 _; C8 _; C8 _] LBc m4 mo3 h3 1 _ f3 j3);
        [unfold SAVED; joinr FJ5 LEN25; joinr FJ5 L15; joinr FJ5 SV5; exact FJ5| reflexivity| exact HH5| exact HT3| exact MF3| exact HPX5
        | exact PPc4| lia| exact CA5| exact PERM3| first [exact MI5| eassumption]| exact SO5| exact SI4| exact ST5| lia].
    Qed.
  End Body.

  #[using="HLS DIMG DHI CRTPARSE"] Theorem U_pkcs7_getcerts_spec : pkcs7_get_certs_stmt usegs L HI PK SI U_PKCS7_GETCERTS.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB PP P END BUF CRT lo bs
           HH HPP ALP BY BIN B1 B2 B3 B4 B5 B6 CZ ALC PP1 PP2 CR1 CR2 D1 ST CEIL SLO SP16 SPTOP DHI' MI SO SIP TP -> -> ->.
    unfold U_PKCS7_GETCERTS.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2 ^ 64) in SPR.
    eapply ENTRY; try eassumption.
  Qed.
End Walk.
