(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pv_ctx ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition art_flag_low_stmt (AI : art_iface) : Prop :=
  forall sp0 SPB LB LF TRS B m mo g Fr k fl F' k',
    ART AI sp0 SPB LB LF TRS B m mo g -> In (Fr, k) LF -> cells_at asegs m (Fr + fsz k - 8) [C8 (wz fl)] -> 0 <= fl < 2^64 ->
    In (F', k') LF -> fl + 1 <= F'.

(* [comment removed for export] *)
Lemma pvh_head_CB : forall m PB b l cs,
  rw_cells asegs m PB (C8 b :: C8 l :: cs) -> rw_cells asegs m PB [CB 16 (le8 b ++ le8 l)] /\ rw_cells asegs m (PB + 16) cs.
Proof.
  intros m PB b l cs H.
  destruct (rw_cells_app_split m PB [C8 b; C8 l] cs H) as [H1 H2]. cbn [cells_size csize Nat.add] in H2.
  split; [| exact H2].
  pose proof (rw_cells_merge asegs m PB [] [C8 b; C8 l] [] ltac:(rewrite app_nil_r; exact H1)) as M.
  cbn [app cells_size cells_bytes csize cbytes Nat.add] in M. rewrite app_nil_r in M. exact M.
Qed.

Lemma pvh_head_zero : forall m PB cs,
  rw_cells asegs m PB [CB (Z.to_nat 16) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 16))] -> rw_cells asegs m (PB + 16) cs ->
  rw_cells asegs m PB (C8 (wz 0) :: C8 (wz 0) :: cs).
Proof.
  intros m PB cs H1 H2.
  assert (H1' : rw_cells asegs m PB [C8 (wz 0); C8 (wz 0)]) by (eapply rw_cells_recast; [exact H1| cbn; repeat split; exact I| reflexivity]).
  exact (rw_cells_app_join m PB [C8 (wz 0); C8 (wz 0)] cs H1' H2).
Qed.

Lemma cells_size_mapC8 : forall ws : list word, cells_size (map C8 ws) = (length ws * 8)%nat.
Proof. induction ws as [|x ws IH]; cbn; [reflexivity|]. rewrite IH. lia. Qed.

Section PVC.
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
  Local Notation POST := (pvalue_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR B LF np0 BB CH n p PB len0 dep fw lo m g).
  Ltac lits := pose proof (pvl_lits Q PVL)
                 as ((PL1 & PL2 & PL3) & PB8 & AL & S47 & TOP & BOT & PB80 & CEIL & LO & TP & N1 & BLR & DEPN & DEP0 & PNZ
                     & CHOK & CHL & CHB & RA1 & RA2 & NPM & BBA & LEN0 & LFR & (GSA1 & GSA2) & (FAL & FLO & FHI & FNEW)
                     & SPR & RAR & S0R & (TOPR & BOTE) & CHN0);
               pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR; change (2^3) with 8 in SHFR;
               pose proof alloc_ceiling_eq as ACE; pose proof KHIGH_eqs as KHE.
  Hypothesis FLAGLOW : art_flag_low_stmt AI.
  Ltac alia := first [ rewrite ?alloc_ceiling_eq; unfold sclr, AMALLOC_STACK, AINTRIN_STACK, ASTRFN_STACK, AENSURE_STACK, ASTKMALLOC_STACK, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_END in *; lia | sclr_tac ].
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length map]; rewrite ?cells_size_mapC8, ?cells_size_mapC1, ?length_map; unfold AERRNO, ATP; lia.

  (* [comment removed for export] *)
  Definition pv_out (r : Z) (mm : word -> option byte) (LB1 : list cblock) (B1 np1 : Z) : Prop :=
    exists buf' len' off',
      (r = 0 /\ (exists dep', PBS Q mm buf' len' off' dep')
         /\ ((buf' = 0 /\ Permutation LR LB1) \/ (buf' <> 0 /\ Permutation ((buf', len') :: LR) LB1))
         /\ BB - pb_allow len0 <= B1 /\ np1 <= np0 + pb_npallow len0)
      \/ (r = 1 /\ (exists bs', Permutation ((buf', len') :: LR) LB1 /\ PBS Q mm buf' len' off' dep /\ pb_data mm buf' len' bs'
                              /\ pb_nums len' off' dep /\ pb_nul bs' len' off')
         /\ len0 <= len' /\ BB - (pb_pot len' - pb_pot len0) <= B1 /\ np1 <= np0 + (pb_npot len' - pb_npot len0)).

  Lemma pv_out_LR : forall r mm LB1 B1 np1, pv_out r mm LB1 B1 np1 -> forall b, In b LR -> In b LB1.
  Proof.
    intros r mm LB1 B1 np1 (buf' & len' & off' & [(_ & _ & HB & _)|(_ & (bs' & HP & _) & _)]) b Hb.
    - destruct HB as [[_ HP]|[_ HP]]; (eapply Permutation_in; [exact HP|]); [exact Hb| right; exact Hb].
    - eapply Permutation_in; [exact HP| right; exact Hb].
  Qed.

  (* [comment removed for export] *)
  Lemma pv_out_ext : forall r mm mm' LB1 B1 np1 W,
    pv_out r mm LB1 B1 np1 -> munch W mm mm' -> wmono asegs mm mm' ->
    disjoint_from W PB 64 -> (forall A k, In (A, k) LB1 -> disjoint_from W A k) ->
    pv_out r mm' LB1 B1 np1.
  Proof.
    intros r mm mm' LB1 B1 np1 W OUT MU WM DPB DLB.
    destruct OUT as (buf' & len' & off' & [(Hr & (dep' & PS) & HB & H1 & H2)|(Hr & (bs' & HP & PS & (ARR & LEN) & PN & NUL) & H1 & H2 & H3)]);
      exists buf', len', off'.
    - left. split; [exact Hr|]. split; [| split; [exact HB| split; [exact H1| exact H2]]].
      exists dep'. eapply rw_cells_transport; [exact PS| exact MU| exact WM| exact DPB].
    - right. split; [exact Hr|]. split; [| split; [exact H1| split; [exact H2| exact H3]]].
      exists bs'. split; [exact HP|]. split; [eapply rw_cells_transport; [exact PS| exact MU| exact WM| exact DPB]|].
      split; [| split; [exact PN| exact NUL]]. split; [| exact LEN].
      eapply u8arr_transport; [exact ARR| exact MU| exact WM|]. rewrite LEN. apply DLB. eapply perm_in_head; exact HP.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_epi : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx (r : Z)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x27 x28 x29 x30 x31 : word),
    PVFR Q mm loc jb shp Fx fcx ->
    ART AI sp0 SPB LB1 ((Fr, 1) :: LF) TRS1 B1 mm mo1 g1 -> rw_cells asegs mm AERRNO [C4 errv1] -> mem_inv asegs mm ->
    pv_agree sp0 LR LF SP PB m mm -> cj_chain CJ_PRINTABLE mm n p B -> chain_cells mm CH -> gmono g g1 -> TINV TI np1 TRS1 ->
    pv_out r mm LB1 B1 np1 ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
              x18 x19 x20 x21 x22 x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) x27 x28 x29 x30 x31)
          Fx (Z_to_bv 64 PV_EPI) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros (SAVW & LOC & LL & PAD & ST & HDR & BODY & SHC & L16 & FRM & FA) HL ERR MI PVA CHN CC GM TV OUT.
    lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    pose proof (pv_out_LR _ _ _ _ _ OUT) as HLR.
    unfold AERRNO, ATP in ERR. unfold SAVEDV in SAVW. unfold FHDR in HDR. unfold FBODY in BODY. unfold SHCV, SHCW in SHC. unfold SHR, PV_EPI.
    destruct shp as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 [|b12 [|b13 [|b14 [|b15 [|? ?]]]]]]]]]]]]]]]]]; try (cbn in L16; lia).
    cbn [map] in SHC. clear L16.
    (* [comment removed for export] *)
    assert (INF : In (Fr, 1) ((Fr, 1) :: LF)) by (left; reflexivity).
    destruct (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL INF) as (_ & _ & _ & _ & _ & _ & (fl & FLP & FLB & FLK & FLT) & FD).
    change (fsz 1) with 128 in FLP, FLT, FD. replace (Fr + 128 - 8) with (Fr + 120) in FLP by lia.
    pose proof (rw_cells_bound asegs _ _ _ FLB) as FLBB. cbn [cells_size Cells.csize Nat.add] in FLBB.
    pose proof (art_flag_high AI _ _ _ _ _ _ _ _ _ Fr 1 fl HL INF ltac:(change (fsz 1) with 128; replace (Fr + 128 - 8) with (Fr + 120) by lia; exact FLP) ltac:(lia)) as FLHI.
    (* [comment removed for export] *)
    pose proof (ablk_img _ _ FLHI) as FLHIi. pose proof (ablk_top _ _ FLHI) as FLHIt. apply ablk_disj_band in FLHI. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLHIi, FLHI. bandM. sepM.
    assert (FLF : forall F' k', In (F', k') LF -> fl + 1 <= F').
    { intros F' k' Hin. eapply (FLAGLOW _ _ _ _ _ _ _ _ _ Fr 1 fl F' k' HL INF); [| lia| right; exact Hin].
      change (fsz 1) with 128. replace (Fr + 128 - 8) with (Fr + 120) by lia. exact FLP. }
    pose proof FLP as FLR. change (cells_at asegs mm (Fr + 120) [C8 (wz fl)]) with (ro_cells asegs mm (Fr + 120) [C8 (wz fl)]) in FLR.
    (* [comment removed for export] *)
    pose proof (conj OUT I) as OUTB. clear OUT.
    eapply lscps_step_evt. cbv beta delta [mkR].
    pose proof (munch_refl [(Fr, Fr + 8); (Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 16)] mm) as MU.
    pose proof (wmono_refl asegs mm) as WM.
    zstep. zstep. zstep. fix_lit_store.
    zstep. if_cases Kf; zify_cond Kf; [exfalso; lia|].
    zstep. do 16 sbstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (OWN1 : Forall (pv_own_iv Q) [(Fr, Fr + 8); (Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 16)]).
    { constructor; [| constructor; [| constructor]]; unfold pv_own_iv; cbn [fst snd]; lia. }
    assert (HL2 : ART AI sp0 SPB LB1 ((Fr, 1) :: LF) TRS1 B1 m2 mo1 g1) by (eapply (pvm_art_store Q PVL); [exact HL| exact MU| exact WM| exact OWN1]).
    assert (PVA2 : pv_agree sp0 LR LF SP PB m m2) by (eapply (pvm_agree_store Q PVL); [exact HL| exact HLR| exact MU| exact WM| exact OWN1| exact PVA]).
    assert (CC2 : chain_cells m2 CH) by (eapply (pvm_chain_cells_store Q PVL); [exact CC| exact MU| exact OWN1]).
    assert (CHN2 : cj_chain CJ_PRINTABLE m2 n p B).
    { eapply cj_chain_frame; [exact CHN| exact MU| exact WM|]. intros A k Hin. cbn.
      destruct (FD A k (HLR _ (BLR _ Hin))). all: split; [lia| split; [| exact I]].
      (* [comment removed for export] *)
      all: (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ (BLR _ Hin))) 4%nat; intros R1 _ R3 R4);
           pose proof (art_block_sclr AI _ _ _ _ _ _ _ _ _ A k A (Z.max k 1) HL (HLR _ (BLR _ Hin)) ltac:(lia) ltac:(lia)) as SC;
           pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2);
           unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1, SC; clear - R3 SC FB1 FB2; lia. }
    assert (FLP2 : cells_at asegs m2 (Fr + 120) [C8 (wz fl)]) by exact FLR.
    destruct OUTB as [OUT _].
    assert (OUT2 : pv_out r m2 LB1 B1 np1).
    { eapply pv_out_ext; [exact OUT| exact MU| exact WM| cbn; lia|].
      intros A k Hin. cbn. (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 4%nat; intros R1 _ _ R4).
      unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4. (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 4%nat; intros _ _ R3 _).
      pose proof (art_block_sclr AI _ _ _ _ _ _ _ _ _ A k A (Z.max k 1) HL Hin ltac:(lia) ltac:(lia)) as SC. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in SC. bandM. sepM.
      pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2).   (* [comment removed for export] *)
      destruct (FD A k Hin); (split; [lia| split; [clear - R3 SC FB1 FB2; unfold Band in SC; lia| exact I]]). }
    pose proof (conj OUT2 I) as OUTB. clear OUT OUT2.
    clear MU WM HL PVA CC CHN OWN1.
    (* [comment removed for export] *)
    zstep. unfold wz.
    pose proof (munch_refl [(fl, fl + 1)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    sbstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : ART AI sp0 SPB LB1 LF TRS1 B1 m3 mo1 g1).
    { replace LF with (lf_remove Fr ((Fr, 1) :: LF)) by (cbn; rewrite Z.eqb_refl; reflexivity).
      eapply (art_ff_release AI); [exact HL2| exact INF| | exact MU| exact WM|].
      - change (fsz 1) with 128. replace (Fr + 128 - 8) with (Fr + 120) by lia. exact FLP2.
      - lazymatch goal with H : rw_cells asegs m3 fl _ |- _ => exact H end. }
    assert (PVA3 : pv_agree sp0 LR LF SP PB m m3).
    { eapply pv_agree_trans; [exact PVA2|]. eapply magree_of_munch; [exact MU| exact WM|].
      intros a Ha [Hc Hn]. cbn. split; [| exact I].
      destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(F' & k & Hin & Hr)|Hsh]]]].
      - lia.
      - pose proof (aclient_image_lt a Hi). lia.
      - destruct (FLK A' n' (HLR _ Hin)); lia.
      - pose proof (FLF F' k Hin). (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL3 Hin) 5%nat; intros Hk _ HF1 HF2 _).
        try rewrite alloc_ceiling_eq in HF2. assert (fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
        unfold sclr, SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. Z.div_mod_to_equations. lia.
      - unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia. }
    assert (CC3 : chain_cells m3 CH).
    { eapply (chain_cells_ext_below Q m2 m3 (SP + 16) CH (ASTACK_TOP sp0)); [exact CC2| exact CHOK| exact CHB|].
      intros a Ha. apply MU. rewrite wa_unsigned by lia. cbn. split; [lia| exact I]. }
    assert (CHN3 : cj_chain CJ_PRINTABLE m3 n p B).
    { eapply cj_chain_frame; [exact CHN2| exact MU| exact WM|]. intros A k Hin. cbn. split; [| exact I].
      destruct (FLK A k (HLR _ (BLR _ Hin))); lia. }
    (* [comment removed for export] *)
    destruct OUTB as [OUT2 _].
    assert (OUT3 : pv_out r m3 LB1 B1 np1).
    { eapply pv_out_ext; [exact OUT2| exact MU| exact WM| cbn; lia|].
      intros A k Hin. cbn. split; [| exact I]. destruct (FLK A k Hin); lia. }
    clear OUT2 MU WM HL2 PVA2 CC2 CHN2 FLP2.
    (* [comment removed for export] *)
    zstep. zstep. do 15 zstep. zstep. zstep.
    (* [comment removed for export] *)
    eapply stk_release in LOC; [| exact ST| lia]. rewrite cells_size_mapC8, LL in LOC. change (Z.of_nat (9 * 8)) with 72 in LOC.
    pose proof (stk_merge asegs m3 lo (SA + 72) (SP + -120) LOC PAD ltac:(lia)) as ST2.
    release_frame SAVW ST2 (bv_unsigned sp).
    apply evt_done. apply lscps_done. unfold pvalue_post.
    (nelim OUT3 4%nat; intros buf' len' off' OUT3).
    nexists 17%nat. exists m3, errv1. split; [reflexivity|].
    split; [exact MI|]. split; [exact FRM|]. split; [apply (FAG18_restore F Fx FA)|].
    split; [exact ST2|]. split; [exact ERR|]. split; [exact PVA3|]. split; [exact CHN3|]. split; [exact GM|]. split; [exact CC3|].
    exists LB1, TRS1, B1, np1, buf', len', off'. split; [exact HL3|]. split; [exact TV|].
    destruct OUT3 as [(-> & HPS & HB & H1 & H2)|(-> & HX & H1 & H2 & H3)]; [left| right].
    - split; [reflexivity|]. split; [exact HPS|]. split; [exact HB|]. split; [exact H1| exact H2].
    - split; [reflexivity|]. split; [exact HX|]. split; [exact H1|]. split; [exact H2| exact H3].
  Qed.

  (* [comment removed for export] *)
  Definition pv_exit (mm : word -> option byte) (mo1 : Model) (g1 : lghost) (LB1 : list cblock) (TRS1 : list (list Z)) (B1 np1 : Z)
      (errv1 : word) (loc : list word) (jb : list byte) (shp : list Z) (Fx : bvmap 5 word) (fcx : bv 32) (r : Z) : Prop :=
    PVFR Q mm loc jb shp Fx fcx
    /\ ART AI sp0 SPB LB1 ((Fr, 1) :: LF) TRS1 B1 mm mo1 g1 /\ rw_cells asegs mm AERRNO [C4 errv1] /\ mem_inv asegs mm
    /\ pv_agree sp0 LR LF SP PB m mm /\ cj_chain CJ_PRINTABLE mm n p B /\ chain_cells mm CH /\ gmono g g1 /\ TINV TI np1 TRS1
    /\ pv_out r mm LB1 B1 np1.

  Lemma pv_epi' : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx (r : Z)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x27 x28 x29 x30 x31 : word),
    pv_exit mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx r ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
              x18 x19 x20 x21 x22 x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) x27 x28 x29 x30 x31)
          Fx (Z_to_bv 64 PV_EPI) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros nelH_; (nelim nelH_ 10%nat; intros FRX HL ERR MI PVA CHN CC GM TV OUT).
    eapply pv_epi; eassumption.
  Qed.

  Lemma loc9 : forall loc : list word, length loc = 9%nat ->
    exists w0 w1 w2 w3 w4 w5 w6 w7 w8, loc = [w0; w1; w2; w3; w4; w5; w6; w7; w8].
  Proof.
    intros loc L. destruct loc as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|? ?]]]]]]]]]]; try (cbn in L; lia).
    exists w0, w1, w2, w3, w4, w5, w6, w7, w8. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_ret1 : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x27 x28 x29 x30 x31 : word),
    pv_exit mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx 1 ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
              x18 x19 x20 x21 x22 x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) x27 x28 x29 x30 x31)
          Fx (Z_to_bv 64 PV_RET1) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros EX. lits. bandM. sepM. unfold PV_RET1, SHR.
    (nelimp EX 5%nat; intros _ _ _ MI _).
    eapply lscps_step_evt. cbv beta delta [mkR]. zstep. zstep. apply evt_done. cbv beta.
    eapply pv_epi'. exact EX.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_ret0_930 : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x27 x28 x29 x30 x31 : word),
    pv_exit mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx 0 ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
              x18 x19 x20 x21 x22 x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) x27 x28 x29 x30 x31)
          Fx (Z_to_bv 64 PV_RET0_930) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros EX. lits. bandM. sepM. unfold PV_RET0_930, SHR.
    (nelimp EX 5%nat; intros _ _ _ MI _).
    eapply lscps_step_evt. cbv beta delta [mkR]. zstep. apply evt_done. cbv beta.
    eapply pv_epi'. exact EX.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_ret0_924 : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word),
    pv_exit mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx 0 -> nth_error loc 4 = Some (Z_to_bv 64 Fr) ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
              x18 x19 x20 x21 x22 x23 x24 (SHR Fr) (Z_to_bv 64 Fr) x27 x28 x29 x30 x31)
          Fx (Z_to_bv 64 PV_RET0_924) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros EX L4. lits. bandM. sepM. unfold PV_RET0_924, SHR.
    pose proof EX as ((SAVW & LOC & LL & _) & _ & _ & MI & _).
    (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 EL). rewrite EL in LOC, L4. cbn in L4.
    injection L4 as E4. subst w4. cbn [map] in LOC.
    eapply lscps_step_evt. cbv beta delta [mkR]. zstep. zstep. zstep. apply evt_done. cbv beta.
    eapply pv_epi'. exact EX.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_ret0_2c8 : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word),
    pv_exit mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx 0 -> nth_error loc 4 = Some (Z_to_bv 64 Fr) ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
              x18 x19 x20 x21 x22 x23 x24 (SHR Fr) (Z_to_bv 64 Fr) x27 x28 x29 x30 x31)
          Fx (Z_to_bv 64 PV_RET0_2C8) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros EX L4. lits. bandM. sepM. unfold PV_RET0_2C8, SHR.
    pose proof EX as ((SAVW & LOC & LL & _) & _ & _ & MI & _).
    (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 EL). rewrite EL in LOC, L4. cbn in L4.
    injection L4 as E4. subst w4. cbn [map] in LOC.
    eapply lscps_step_evt. cbv beta delta [mkR]. zstep. zstep. apply evt_done. cbv beta.
    eapply pv_epi'. exact EX.
  Qed.
  (* [comment removed for export] *)
  Hypothesis MEMSET : asan_memset_spec.

  Lemma pv_fail_free : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx buf len off depc
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x27 x28 x29 x30 x31 : word),
    PVFR Q mm loc jb shp Fx fcx ->
    ART AI sp0 SPB LB1 ((Fr, 1) :: LF) TRS1 B1 mm mo1 g1 -> rw_cells asegs mm AERRNO [C4 errv1] -> mem_inv asegs mm ->
    pv_agree sp0 LR LF SP PB m mm -> cj_chain CJ_PRINTABLE mm n p B -> chain_cells mm CH -> gmono g g1 -> TINV TI np1 TRS1 ->
    sh_zero mm alloc_ceiling (2^47) ->
    Permutation ((buf, len) :: LR) LB1 -> PBS Q mm buf len off depc ->
    BB - pb_allow len0 + cost_free <= B1 -> np1 + 1 <= np0 + pb_npallow len0 -> np1 < NPMAX TI ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
              x18 (Z_to_bv 64 PB) x20 x21 x22 x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) x27 x28 x29 x30 x31)
          Fx (Z_to_bv 64 PV_FAIL_FREE) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros FRX HL ERR MI PVA CHN CC GM TV SSZ HP PBS1 HB HNP NPX.
    (nelimp FRX 11%nat; intros SAVW LOC LL PAD ST HDR BODY SHC L16 FRM FA).
    lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. unfold PV_FAIL_FREE, SHR.
    assert (HLR : forall b, In b LR -> In b LB1) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    (nelimp (art_binv AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros _ _ BXR _).
    unfold AERRNO, ATP in ERR. unfold PBS in PBS1. unfold SAVEDV in SAVW.
    assert (E1 : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    assert (CCX : chain_cells mm ((SP, bv_unsigned ra, bv_unsigned s0) :: CH)).
    { split; [| exact CC].
      destruct (rw_cells_app_split mm (SP + -120) [C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7;
                 C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] SAVW) as [_ T2].
      cbn [cells_size Cells.csize Nat.add] in T2. replace (SP + -120 + Z.of_nat 104) with (SP + -16) in T2 by lia.
      exact (proj1 (chain_cells_frame1 mm SP s0 ra T2)). }
    assert (CHOK2 : chain_ok SP ((SP, bv_unsigned ra, bv_unsigned s0) :: CH) (ASTACK_TOP sp0)).
    { apply chain_ok_cons; [lia| Z.div_mod_to_equations; lia| lia| lia| exact RA2| lia| eapply chain_ok_mono; [exact CHOK| lia]|].
      unfold chain_link in CHL. destruct CH as [|[[f1 r1] sv1] CH']; [exact CHL| exact CHL]. }
    pose proof (uwt_hook_fp mm SA (ASTACK_TOP sp0) PC0_FREE SP (bv_unsigned ra) (bv_unsigned s0) CH
                  ltac:(right; left; reflexivity) CCX CHOK2 ltac:(lia)) as UW.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    replace (ret_pc (wz AFREE)) with (wz AFREE) by (unfold wz, AFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (art_free_ok AI) with (lo := lo) (A := buf) (n := len) (tl := chain_trace 2 ((SP, bv_unsigned ra, bv_unsigned s0) :: CH));
        rewrite ?E1; rewrite ?unsigned_lit by lia;
        try (first [ exact HL | eapply perm_in_head; exact HP | exact ST | exact ERR | exact MI | exact TP | reflexivity
              | exact UW
              | eapply (tinv_room_paid TI); [exact TV| exact NPX]
              | split; [lia| unfold PC0_FREE; lia]
              | rewrite cost_free_eq in *; lia
              | alia ]). all: match goal with |- ?G => idtac "REMAINING"; idtac G end. all: fail. }
    cbv beta. intros ms3 mo3 g3 PO.
    (nelim PO 25%nat; intros t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c m3 TRS3 -> MI3 ST3 ERR3 PR3 GM3 TP3 HL3)
.
    rewrite ?E1 in ST3, PR3. unfold AERRNO, ATP in ERR3.
    replace (ret_pc (Z_to_bv 64 0x85174)) with (Z_to_bv 64 0x85174) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (perm_cb_remove _ _ _ _ HP (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL))) as HPr.
    assert (TV3 : TINV TI (np1 + 1) TRS3) by (eapply (tinv_put_paid_or TI); [exact TV| exact NPX| left; exact TP3]).
    assert (GM3' : gmono g g3) by (eapply gmono_trans; [exact GM| exact GM3]).
    (* [comment removed for export] *)
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in SAVW; [| left; cbn; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in LOC; [| left; rewrite cells_size_mapC8, LL; cbn; lia].
    apply (cj_pres_stk _ _ _ _ _ _ _ _ PR3) in PAD; [| lia| lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in PBS1; [| left; cbn; lia].
    unfold FHDR in HDR. apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in HDR; [| do 4 right; left; exists Fr, 1; split; [left; reflexivity| cbn; change (fsz 1) with 128; lia]].
    unfold FBODY in BODY. apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in BODY; [| do 4 right; left; exists Fr, 1; split; [left; reflexivity| cbn; change (fsz 1) with 128; lia]].
    unfold SHCV, SHCW in SHC. apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR3) in SHC;
      [| do 5 right; left; exists Fr, 1; split; [left; reflexivity| rewrite cells_size_mapC1, length_map, L16, SH_shiftr; cbn; change (fsz 1) with 128; lia]].
    assert (PVA3 : pv_agree sp0 LR LF SP PB m m3).
    { eapply pv_agree_trans; [exact PVA|]. eapply (pv_agree_weaken_lf sp0 LR ((Fr, 1) :: LF) LF); [| intros f Hf; right; exact Hf].
      eapply pv_agree_of_cj_pres; [exact PR3| lia| intros b Hb; eapply Permutation_in; [exact HPr| exact Hb]]. }
    assert (SSZ3 : sh_zero m3 alloc_ceiling (2^47)) by (eapply sh_zero_stack_cj_pres; [exact PR3| exact SSZ]).
    assert (CC3 : chain_cells m3 CH).
    { eapply (chain_cells_cj_pres sp0 _ _ SA mm m3 (SP + 16)); [exact CC| exact CHOK| exact PR3| lia| lia| lia]. }
    assert (CHN3 : cj_chain CJ_PRINTABLE m3 n p B).
    { eapply cj_chain_pres; [exact CHN| exact PR3|]. intros b Hb. eapply Permutation_in; [exact HPr| apply BLR; exact Hb]. }
    clear PVA PR3 MI ST ERR HL SSZ CC CHN UW CCX CHOK2.
    (* [comment removed for export] *)
    destruct (pvh_head_CB _ _ _ _ _ PBS1) as [HD TL].
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { pose proof MEMSET as MSX. unfold asan_memset_spec, memset_contract in MSX.
      eapply MSX with (lo := lo) (d := PB) (c := 0) (n := 16); clear MSX; rewrite ?unsigned_lit by lia;
        first [ lazymatch goal with |- icpt_cells _ => eapply (art_icpt_cells AI); exact HL3 end | exact MI3 | exact ST3 | exact HD | reflexivity
              | lazymatch goal with |- app_range _ _ => app_rng0 end
              | apply wr_range_ok_high; lia
              | intros _; eapply sh_zero_shadow_ok; [exact SSZ3| alia| lia| lia]
              | alia ]. }
    cbv beta. intros ms4 PO4.
    (nelim PO4 21%nat; intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m4 -> MU4 WM4 MI4 ZB ST4).
    rewrite ?unsigned_lit in MU4, ST4 by lia. unfold AINTRIN_STACK in MU4.
    replace (ret_pc (Z_to_bv 64 0x85184)) with (Z_to_bv 64 0x85184) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply (rw_cells_transport asegs) in SAVW; [| exact MU4| exact WM4| dj].
    eapply (rw_cells_transport asegs) in LOC; [| exact MU4| exact WM4| dj].
    eapply stk_transport_disjoint in PAD; [| exact MU4| exact WM4| dj].
    eapply (rw_cells_transport asegs) in ERR3; [| exact MU4| exact WM4| dj].
    eapply (rw_cells_transport asegs) in TL; [| exact MU4| exact WM4| dj].
    eapply (rw_cells_transport asegs) in HDR; [| exact MU4| exact WM4| dj].
    eapply (rw_cells_transport asegs) in BODY; [| exact MU4| exact WM4| dj].
    eapply (rw_cells_transport asegs) in SHC; [| exact MU4| exact WM4| dj].
    pose proof (pvh_head_zero _ _ _ ZB TL) as PBS4.
    assert (OWN4 : Forall (pv_own_iv Q) [(PB, PB + 16); (SA - 2304, SA)]).
    { constructor; [| constructor; [| constructor]]; unfold pv_own_iv; cbn [fst snd]; lia. }
    assert (HL4 : ART AI sp0 SPB (cb_remove buf LB1) ((Fr, 1) :: LF) TRS3 (B1 - cost_free) m4 mo3 g3)
      by (eapply (pvm_art_store Q PVL); [exact HL3| exact MU4| exact WM4| exact OWN4]).
    assert (HLR4 : forall b, In b LR -> In b (cb_remove buf LB1)) by (intros b Hb; eapply Permutation_in; [exact HPr| exact Hb]).
    assert (PVA4 : pv_agree sp0 LR LF SP PB m m4) by (eapply (pvm_agree_store Q PVL); [exact HL3| exact HLR4| exact MU4| exact WM4| exact OWN4| exact PVA3]).
    assert (CC4 : chain_cells m4 CH) by (eapply (pvm_chain_cells_store Q PVL); [exact CC3| exact MU4| exact OWN4]).
    assert (CHN4 : cj_chain CJ_PRINTABLE m4 n p B).
    { eapply cj_chain_frame; [exact CHN3| exact MU4| exact WM4|]. intros A k Hin. cbn.
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL3 (HLR4 _ (BLR _ Hin))) 4%nat; intros Q1 _ _ Q4).
      unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Q1. bandM. sepM. try rewrite alloc_ceiling_eq in Q4. lia. }
    clear MU4 WM4 HL3 PVA3 CC3 CHN3 ZB TL HD OWN4.
    zstep. zstep. apply evt_done. cbv beta.
    eapply pv_epi'. split.
    { split; [exact SAVW|]. split; [exact LOC|]. split; [exact LL|]. split; [exact PAD|]. split; [exact ST4|].
      split; [exact HDR|]. split; [exact BODY|]. split; [exact SHC|]. split; [exact L16|]. split; [exact FRM| exact FA]. }
    split; [exact HL4|]. split; [exact ERR3|]. split; [exact MI4|]. split; [exact PVA4|]. split; [exact CHN4|].
    split; [exact CC4|]. split; [exact GM3'|]. split; [exact TV3|].
    exists 0, 0, off. left. split; [reflexivity|]. split; [exists depc; exact PBS4|]. split; [left; split; [reflexivity| exact HPr]|].
    rewrite cost_free_eq in *. split; lia.
  Qed.
End PVC.


End CeilWrap.
