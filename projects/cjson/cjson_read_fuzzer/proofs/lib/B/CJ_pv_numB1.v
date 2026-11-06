(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pwlopts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pwlopts_A.CJ_band3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_conv ICPT_iface ICPT_musl ICPT_pcdefs ICPT_fmt_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fmt_glue.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fmt_glue.ICPT_fmt_iface2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_printf_iface.NumFacts_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_ctx.CJ_fp_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.CJ_print_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.CJ_print_lemmas2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pv_ctx CJ_pv_common CJ_pv_cases CJ_pv_calls CJ_pv_lits CJ_pv_numK.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gch_numch : forall o, Forall num_gch o -> Forall (fun c => is_numch c = true) o.
Proof.
  intros o H. eapply Forall_impl; [| exact H]. intros c Hc. unfold num_gch in Hc. unfold is_numch.
  destruct Hc as [Hc|[->|[->|[->|[->| ->]]]]]; try reflexivity.
  replace (48 <=? c) with true by (symmetry; apply Z.leb_le; lia).
  replace (c <=? 57) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma gch_bytes : forall o, Forall num_gch o -> Forall (fun c => 0 <= c < 256) o.
Proof. intros o H. eapply Forall_impl; [| exact H]. intros c Hc. unfold num_gch in Hc. lia. Qed.

Lemma gch_nox : forall o, Forall num_gch o -> Forall (fun c => c <> 120 /\ c <> 88) o.
Proof. intros o H. eapply Forall_impl; [| exact H]. intros c Hc. unfold num_gch in Hc. lia. Qed.

Lemma Forall_range_unsigned : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof. induction bs as [|b bs IH]; cbn; constructor; [| exact IH]. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia. Qed.

Lemma map_zb_unsigned : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite IH. f_equal. apply (@definitions.Z_to_bv_bv_unsigned 8). Qed.

(* [comment removed for export] *)
Lemma word_int_arg : forall w : word, exists i, bv_unsigned w mod 2^32 = i mod 2^32 /\ -2^31 <= i < 2^31.
Proof.
  intros w. exists ((bv_unsigned w + 2^31) mod 2^32 - 2^31).
  pose proof (bv_unsigned_in_range 64 w) as R. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition fmt_facts_stmt (AI : art_iface) : Prop :=
  forall sp0 SPB LB LF TRS BB m mo g, ART AI sp0 SPB LB LF TRS BB m mo g -> sh_zero m alloc_ceiling (2^47) ->
    fmt_cells m /\ MRT m /\ lowsh_at m /\ exists canary : word, assp_cells m canary.
Definition fmt_lits_stmt (AI : art_iface) : Prop :=
  forall sp0 SPB LB LF TRS BB m mo g, ART AI sp0 SPB LB LF TRS BB m mo g ->
    shadow_ok m A_FMT_d 3 /\ shadow_ok m A_FMT_g15 7 /\ shadow_ok m A_FMT_lg 4 /\ shadow_ok m A_FMT_g17 7
    /\ shadow_ok m 0x212c0 3 /\ shadow_ok m A_FMT_u04x 6.

Section NUMB1.
  Variable Q : pvi.
  Local Notation AI := (q_ai Q).    Local Notation TI := (q_ti Q).
  Local Notation ra := (q_ra Q).    Local Notation sp := (q_sp Q).    Local Notation gp := (q_gp Q).    Local Notation tp := (q_tp Q).
  Local Notation s0 := (q_s0 Q).    Local Notation s1 := (q_s1 Q).    Local Notation s2 := (q_s2 Q).    Local Notation s3 := (q_s3 Q).
  Local Notation s4 := (q_s4 Q).    Local Notation s5 := (q_s5 Q).    Local Notation s6 := (q_s6 Q).    Local Notation s7 := (q_s7 Q).
  Local Notation s8 := (q_s8 Q).    Local Notation s9 := (q_s9 Q).    Local Notation s10 := (q_s10 Q).  Local Notation s11 := (q_s11 Q).
  Local Notation F := (q_F Q).      Local Notation m := (q_m Q).      Local Notation g := (q_g Q).
  Local Notation sp0 := (q_sp0 Q).  Local Notation SPB := (q_SPB Q).  Local Notation LR := (q_LR Q).    Local Notation B := (q_B Q).
  Local Notation LF := (q_LF Q).    Local Notation np0 := (q_np0 Q).  Local Notation BB := (q_BB Q).    Local Notation CH := (q_CH Q).
  Local Notation n := (q_n Q).      Local Notation p := (q_p Q).      Local Notation PB := (q_PB Q).    Local Notation len0 := (q_len0 Q).
  Local Notation dep := (q_dep Q).  Local Notation fw := (q_fw Q).    Local Notation lo := (q_lo Q).
  Local Notation SA := (q_SA Q).    Local Notation Fr := (q_Fr Q).
  Hypothesis PVL : pvl Q.
  Local Notation SP := (bv_unsigned sp).
  Ltac lits := pose proof (pvl_lits Q PVL)
                 as ((PL1 & PL2 & PL3) & PB8 & AL & S47 & TOP & BOT & PB80 & CEIL & LO & TP & N1 & BLR & DEPN & DEP0 & PNZ
                     & CHOK & CHL & CHB & RA1 & RA2 & NPM & BBA & LEN0 & LFR & (GSA1 & GSA2) & (FAL & FLO & FHI & FNEW)
                     & SPR & RAR & S0R & (TOPR & BOTE) & CHN0);
               pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR; change (2^3) with 8 in SHFR;
               pose proof alloc_ceiling_eq as ACE; pose proof KHIGH_eqs as KHE.
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length map]; rewrite ?cells_size_mapC8, ?cells_size_mapC1, ?length_map; unfold AERRNO, ATP; lia.
  Hypothesis FMTF : fmt_facts_stmt AI.
  Hypothesis FMTL : fmt_lits_stmt AI.
  Hypothesis SPRD : asprintf_d_stmt_b.
  Hypothesis SPRG15 : asprintf_g_stmt_b 15.
  Hypothesis SPRG17 : asprintf_g_stmt_b 17.
  Hypothesis SSC : asscanf_lg_stmt_b.
  Hypothesis GRET : F_printf_iface.FMT_G_RET.
  Hypothesis GLEN25 : F_printf_iface.FMT_G_LEN25.
  Hypothesis GFACTS : NUM_FMT_G_FACTS.
  Hypothesis GTOT : NUM_FMT_G_TOTAL.
  Hypothesis DTOT : NUM_FMT_D_TOTAL.
  Hypothesis SJUNK : NUM_SSCANF_JUNK.

  (* [comment removed for export] *)
  Definition spr_post (depc : Z) (mo1 : Model) (g1 : lghost) (LB1 : list cblock) (TRS1 : list (list Z)) (B1 np1 : Z) (errv1 : word)
      (buf len off : Z) (bs : list byte) (loc : list word) (j0 nb j1 j2 : list byte) (t : word) (j3 : list byte) (Fx : bvmap 5 word)
      (x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) : machine_state -> Prop :=
    fun ms' => exists (o : list Z) (r : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
      ms' = MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               Ft (ret_pc x1) fc' None m' (seg_rom bsegs)
      /\ NUMX Q depc m' mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 (map (Z_to_bv 8) o ++ Z_to_bv 8 0 :: skipn (S (length o)) nb) j1 j2 t j3 SHP_NUM Ft fc'
      /\ r = zlength o /\ 0 <= r <= 25 /\ Forall num_gch o
      /\ (forall k : bv 5, bv_unsigned k <> 10 -> reg_get Ft k = reg_get Fx k).

  (* [comment removed for export] *)
  Lemma num_call_g : forall (prec : Z) depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc j0 nb j1 j2 t j3 Fx fcx (vd : word)
      (x1 t0 t1 t2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    NUMX Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 nb j1 j2 t j3 SHP_NUM Fx fcx ->
    (prec = 15 \/ prec = 17) -> ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047 ->
    evt bsegs (spr_post depc mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc j0 nb j1 j2 t j3 Fx x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27)
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 (if prec =? 15 then A_FMT_g15 else A_FMT_g17)) vd a3 a4 a5 a6 a7
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fx (Z_to_bv 64 ASPRINTF_T) fcx None mm (seg_rom bsegs)).
  Proof.
    intros until t6. intros [CTX FRX] HP15 DFIN. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    (nelimp CTX 13%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ _).
    (nelimp FRX 16%nat; intros SAVW LOC LL9 PAD ST HDR P0 P1 P2 P3 P4 P5 SHC L16 FRM FA).
    assert (E1 : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; lia).
    pose proof (num_shadow_ok26 Q PVL mm SHP_NUM SHC L16 eq_refl) as SOK.
    (nelim (FMTF _ _ _ _ _ _ _ _ _ HL SSZ) 4%nat; intros FC MR LOW [canary ASSP]).
    (nelimp (FMTL _ _ _ _ _ _ _ _ _ HL) 5%nat; intros _ SO15 _ SO17 _).
    pose proof (bv_unsigned_in_range 64 vd) as VR. change (bv_modulus 64) with (2^64) in VR.
    (nelim (GTOT (bv_unsigned vd) prec DFIN HP15) 4%nat; intros o EG OG OL).
    pose proof (GFACTS _ _ _ _ HP15 EG) as GF.
    assert (L26 : length nb = 26%nat) by (destruct P1 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    eapply evt_cut.
    { assert (SPRG : asprintf_g_stmt_b prec) by (destruct HP15 as [-> | ->]; [exact SPRG15| exact SPRG17]).
      unfold asprintf_g_stmt_b in SPRG.
      eapply SPRG with (dn := 26%nat) (lo := lo) (canary := canary) (o := o) (r := zlength o); clear SPRG; rewrite ?E1;
        first [ exact GRET | exact GLEN25 | exact P1 | reflexivity | exact HP15 | exact EG | exact GF
              | unfold zlength in OL |- *; (cut_to HP15 DFIN PL1 PB8 CEIL LO N1 GSA1 GSA2 FLO SPR VR OL; (cut_to HP15 DFIN PL1 PB8 CEIL LO N1 GSA1 GSA2 VR OL; lia))
              | destruct HP15 as [-> | ->]; cbn; assumption
              | idtac ].
      unfold asprintf_pre_b. rewrite E1. split; [exact FC|]. split; [exact MR|]. split; [exact LOW|]. split; [exact MI|]. split; [exact FRM|].
      split; [exact ASSP|]. split; [exact ST|]. split; [try rewrite alloc_ceiling_eq; lia|]. split; [unfold AFMT_STACK; lia|]. split; [lia|].
      split; [left; lia|]. sepM. split; [split; [unfold AIMG_HI; lia| app_rng0]|]. exact SOK. }
    cbv beta. intros ms' PO.
    (nelim PO 26%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' -> MU WM MI' FRM' HF ST' SSP' OUTC).
    rewrite E1 in MU, ST'. change (Z.of_nat 26) with 26 in MU.
    apply evt_done. unfold spr_post. exists o, (zlength o). nexists 14%nat. exists Ft, fc', m'. split; [reflexivity|].
    split; [| split; [reflexivity| split; [unfold zlength in OL |- *; (lia_on HP15 DFIN PL1 PB8 CEIL LO N1 GSA1 GSA2 FLO SPR VR OL)| split; [exact OG| exact HF]]]].
    split.
    - eapply (pvm_wext0 Q PVL); [exact CTX| exact MU| exact WM| exact MI'|].
      constructor; [unfold pv_wiv0; cbn [fst snd]; lia|]. constructor; [unfold pv_wiv0; cbn [fst snd]; lia| constructor].
    - eapply (nfr_wext Q PVL); [exact FRX| exact MU| exact WM| | exact ST'| exact OUTC| | exact FRM'| eapply FAG18_but10; [exact FA| exact HF]].
      + constructor; [unfold nf_wiv; cbn [fst snd]; lia|]. constructor; [unfold nf_wiv; cbn [fst snd]; lia| constructor].
      + eapply (rw_cells_transport bsegs); [exact P4| exact MU| exact WM| dj].
  Qed.

  (* [comment removed for export] *)
  Lemma num_call_d : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc j0 nb j1 j2 t j3 Fx fcx (w : word)
      (x1 t0 t1 t2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    NUMX Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 nb j1 j2 t j3 SHP_NUM Fx fcx ->
    evt bsegs (spr_post depc mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc j0 nb j1 j2 t j3 Fx x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27)
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 A_FMT_d) w a3 a4 a5 a6 a7
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fx (Z_to_bv 64 ASPRINTF_T) fcx None mm (seg_rom bsegs)).
  Proof.
    intros until t6. intros [CTX FRX]. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    (nelimp CTX 13%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ _).
    (nelimp FRX 16%nat; intros SAVW LOC LL9 PAD ST HDR P0 P1 P2 P3 P4 P5 SHC L16 FRM FA).
    assert (E1 : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; lia).
    pose proof (num_shadow_ok26 Q PVL mm SHP_NUM SHC L16 eq_refl) as SOK.
    (nelim (FMTF _ _ _ _ _ _ _ _ _ HL SSZ) 4%nat; intros FC MR LOW [canary ASSP]).
    pose proof (FMTL _ _ _ _ _ _ _ _ _ HL) as (SOD & _).
    (nelim (word_int_arg w) 3%nat; intros i Ei Ri).
    (nelim (DTOT i) 5%nat; intros o ED OG _ OL). specialize (OL Ri).
    assert (L26 : length nb = 26%nat) by (destruct P1 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    eapply evt_cut.
    { pose proof SPRD as SP0. unfold asprintf_d_stmt_b in SP0.
      eapply SP0 with (dn := 26%nat) (lo := lo) (canary := canary) (o := o) (r := zlength o) (i := i); clear SP0; rewrite ?E1;
        first [ exact P1 | reflexivity | exact Ei | exact Ri | exact ED | exact SOD
              | unfold zlength in OL |- *; lia
              | idtac ].
      unfold asprintf_pre_b. rewrite E1. split; [exact FC|]. split; [exact MR|]. split; [exact LOW|]. split; [exact MI|]. split; [exact FRM|].
      split; [exact ASSP|]. split; [exact ST|]. split; [try rewrite alloc_ceiling_eq; lia|]. split; [unfold AFMT_STACK; lia|]. split; [lia|].
      split; [left; lia|]. split; [split; [unfold AIMG_HI; lia| app_rng0]|]. exact SOK. }
    cbv beta. intros ms' PO.
    (nelim PO 26%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' -> MU WM MI' FRM' HF ST' SSP' OUTC).
    rewrite E1 in MU, ST'. change (Z.of_nat 26) with 26 in MU.
    apply evt_done. unfold spr_post. exists o, (zlength o). nexists 14%nat. exists Ft, fc', m'. split; [reflexivity|].
    split; [| split; [reflexivity| split; [unfold zlength in OL |- *; lia| split; [exact OG| exact HF]]]].
    split.
    - eapply (pvm_wext0 Q PVL); [exact CTX| exact MU| exact WM| exact MI'|].
      constructor; [unfold pv_wiv0; cbn [fst snd]; lia|]. constructor; [unfold pv_wiv0; cbn [fst snd]; lia| constructor].
    - eapply (nfr_wext Q PVL); [exact FRX| exact MU| exact WM| | exact ST'| exact OUTC| | exact FRM'| eapply FAG18_but10; [exact FA| exact HF]].
      + constructor; [unfold nf_wiv; cbn [fst snd]; lia|]. constructor; [unfold nf_wiv; cbn [fst snd]; lia| constructor].
      + eapply (rw_cells_transport bsegs); [exact P4| exact MU| exact WM| dj].
  Qed.

  (* [comment removed for export] *)
  Definition scan_post (depc : Z) (mo1 : Model) (g1 : lghost) (LB1 : list cblock) (TRS1 : list (list Z)) (B1 np1 : Z)
      (buf len off : Z) (bs : list byte) (loc : list word) (j0 nb j1 j2 : list byte) (j3 : list byte) (Fx : bvmap 5 word)
      (x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) : machine_state -> Prop :=
    fun ms' => exists (r : Z) (tw errv' : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
      ms' = MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               F' (ret_pc x1) fc' None m' (seg_rom bsegs)
      /\ NUMX Q depc m' mo1 g1 LB1 TRS1 B1 np1 errv' buf len buf len off bs loc j0 nb j1 j2 tw j3 SHP_NUM F' fc'
      /\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get Fx k).

  (* [comment removed for export] *)
  Lemma num_call_scan : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc j0 (o : list Z) (rest : list byte) j1 j2 t j3 Fx fcx
      (x1 t0 t1 t2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    NUMX Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 (map (Z_to_bv 8) o ++ Z_to_bv 8 0 :: rest) j1 j2 t j3 SHP_NUM Fx fcx ->
    Forall num_gch o -> x1 = Z_to_bv 64 0x84a48 ->
    evt bsegs (scan_post depc mo1 g1 LB1 TRS1 B1 np1 buf len off bs loc j0 (map (Z_to_bv 8) o ++ Z_to_bv 8 0 :: rest) j1 j2 j3 Fx x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27)
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 A_FMT_lg) (Z_to_bv 64 (Fr + 96)) a3 a4 a5 a6 a7
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fx (Z_to_bv 64 ASSCANF_T) fcx None mm (seg_rom bsegs)).
  Proof.
    intros until t6. intros [CTX FRX] OG ->. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    (nelimp CTX 13%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ _).
    (nelimp FRX 16%nat; intros SAVW LOC LL9 PAD ST HDR P0 P1 P2 P3 P4 P5 SHC L16 FRM FA).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 _ _ R4). pose_perm_blk_band HL HP. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) 8%nat; intros _ _ _ _ _ _ _ FD). change (fsz 1) with 128 in FD.
    pose proof (FD buf len (perm_in_head _ _ _ HP)) as FDB.
    assert (E1 : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; lia).
    pose proof (num_shadow_ok26 Q PVL mm SHP_NUM SHC L16 eq_refl) as SOK.
    pose proof (num_shadow_ok_pd Q PVL mm SHP_NUM SHC L16 eq_refl) as SOKD.
    (nelim (FMTF _ _ _ _ _ _ _ _ _ HL SSZ) 4%nat; intros FC MR LOW [canary ASSP]).
    (nelimp (FMTL _ _ _ _ _ _ _ _ _ HL) 4%nat; intros _ _ SOLG _).
    assert (L26 : length (map (Z_to_bv 8) o ++ Z_to_bv 8 0 :: rest) = 26%nat) by (destruct P1 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    assert (L6 : length j1 = 6%nat) by (destruct P2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    pose proof L26 as LO26. rewrite length_app, length_map in LO26. cbn [length] in LO26.
    (* [comment removed for export] *)
    set (txt := o ++ 0 :: map bv_unsigned (rest ++ j1)).
    assert (LT : zlength txt = 32) by (subst txt; unfold zlength; rewrite length_app; cbn [length]; rewrite length_map, length_app; lia).
    destruct (scan_sscanf_lg (o ++ [0])) as [[rr res]|] eqn:ES.
    2:{ exfalso. exact (scan_sscanf_lg_total_gen o (gch_bytes o OG) (gch_nox o OG) ES). }
    assert (ES' : scan_sscanf_lg txt = Some (rr, res)) by (subst txt; rewrite (SJUNK o _ (gch_numch o OG)); exact ES).
    assert (TXTB : bytes_at bsegs mm (Fr + 32) (map (Z_to_bv 8) txt)).
    { subst txt. rewrite map_app. cbn [map]. rewrite map_zb_unsigned.
      assert (J : rw_cells bsegs mm (Fr + 32) [CB 26 (map (Z_to_bv 8) o ++ Z_to_bv 8 0 :: rest); CB 6 j1]).
      { apply rw_cells_app1. split; [exact P1|]. cbn [Cells.csize]. replace (Fr + 32 + Z.of_nat 26) with (Fr + 58) by lia. exact P2. }
      destruct J as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r, <- app_assoc in BY. cbn [app] in BY. exact BY. }
    assert (AL8 : (Fr + 32 + zlength txt) mod 8 = 0) by (rewrite LT; Z.div_mod_to_equations; lia).
    eapply evt_cut.
    { pose proof SSC as SS0. unfold asscanf_lg_stmt_b in SS0.
      sepM. eapply SS0 with (T := Fr + 32) (PD := Fr + 96) (txt := txt) (pre := o) (post := map bv_unsigned (rest ++ j1)) (r := rr) (res := res) (djunk := t) (lo := lo) (canary := canary) (ev := errv1);
        clear SS0; rewrite ?E1; rewrite ?LT;
        first [ exact FC | exact MR | exact LOW | exact MI | exact FRM | exact ASSP | exact ERR | exact TXTB | exact P4 | exact ES' | exact ST | exact AL8 | exact SOKD
              | reflexivity
              | unfold wz, ATP in TP; exact TP
              | subst txt; apply Forall_app; split; [exact (gch_bytes o OG)| constructor; [lia| apply Forall_range_unsigned]]
              | exact (gch_numch o OG)
              | lazymatch goal with   (* [comment removed for export] *)
                | |- app_range _ _ =>
                    first [ lazymatch goal with HL : ART ?AI _ _ _ ((?Fr0, ?k0) :: _) _ _ _ _ _ |- _ =>   (* [comment removed for export] *)
                              eapply (art_frame_app_range AI _ _ _ _ _ _ _ _ _ Fr0 k0); [exact HL| left; reflexivity| lia| lia| try (change (fsz 1) with 128); try (change (fsz 2) with 256); lia] end
                          | app_rng0 ]
                | |- shadow_ok _ _ _ => eapply shadow_ok_sub; [exact SOK| lia| unfold zlength; lia| unfold zlength; lia]
                | |- _ /\ sclr _ _ => unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia
                | |- _ + AFMT_STACK <= _ => unfold AFMT_STACK; lia
                end
              | unfold zlength; (cut_to PL1 CEIL GSA1 FLO LO26 FAL PB80 FHI; lia)
              | try rewrite alloc_ceiling_eq; lia
              | unfold AFMT_STACK; (cut_to LO GSA1; lia)
              | app_rng0
              | eapply shadow_ok_sub; [exact SOK| lia| unfold zlength; lia| unfold zlength; lia]
              | unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia
              | lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 29%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' ev' -> MU WM MI' FRM' HF ST' PD' TXT' SSP' ERR').
    rewrite ?E1 in MU, ST'.
    apply evt_done. unfold scan_post.
    exists rr, (match res with Some bits => Z_to_bv 64 bits | None => t end), ev'. nexists 14%nat. exists F', fc', m'. split; [reflexivity|].
    split; [| exact HF].
    split.
    - eapply (pvm_wext Q PVL); [exact CTX| exact MU| exact WM| exact MI'| | exact ERR'| | reflexivity].
      + constructor; [unfold pv_wiv; cbn [fst snd]; lia|]. constructor; [unfold pv_wiv; cbn [fst snd]; lia|].
        constructor; [unfold pv_wiv; cbn [fst snd]; lia| constructor].
      + eapply u8arr_transport; [exact ARR| exact MU| exact WM| rewrite LEN; (cut_on [PL1 PB8 CEIL LO N1 GSA1 GSA2 FAL FLO FHI SPR R1 BR FDB LT] dj)].
    - eapply (nfr_wext Q PVL); [exact FRX| exact MU| exact WM| | exact ST'| | exact PD'| exact FRM'| eapply FAG18_call3; [exact FA| exact HF]].
      + constructor; [unfold nf_wiv; cbn [fst snd]; lia|]. constructor; [unfold nf_wiv; cbn [fst snd]; lia|].
        constructor; [unfold nf_wiv; cbn [fst snd]; lia| constructor].
      + eapply (rw_cells_transport bsegs); [exact P1| exact MU| exact WM| dj].
  Qed.
End NUMB1.


End CeilWrap.
(* [comment removed for export] *)
Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.
