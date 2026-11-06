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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pv_ctx CJ_pv_common CJ_pv_cases CJ_pv_calls ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma u8arr_mid : forall m A l1 l2 l3,
  u8arr asegs m A (l1 ++ l2 ++ l3) -> u8arr asegs m (A + Z.of_nat (length l1)) l2.
Proof.
  intros m A l1 l2 l3 [BY (W0 & W1 & WR)]. rewrite !length_app in W1, WR.
  apply bytes_at_app in BY. destruct BY as [_ BY]. apply bytes_at_app in BY. destruct BY as [BY _].
  split; [exact BY|]. split; [lia|]. split; [lia|]. intros i Hi.
  replace (A + Z.of_nat (length l1) + i) with (A + (Z.of_nat (length l1) + i)) by lia. apply WR. lia.
Qed.

(* [comment removed for export] *)
Lemma u8arr_put_mid : forall m m' A l1 l2 l2' l3 u v,
  u8arr asegs m A (l1 ++ l2 ++ l3) ->
  munch [(A + Z.of_nat (length l1), A + Z.of_nat (length l1) + Z.of_nat (length l2)); (u, v)] m m' -> wmono asegs m m' ->
  bytes_at asegs m' (A + Z.of_nat (length l1)) l2' -> length l2' = length l2 ->
  A + Z.of_nat (length (l1 ++ l2 ++ l3)) <= u ->
  u8arr asegs m' A (l1 ++ l2' ++ l3).
Proof.
  intros m m' A l1 l2 l2' l3 u v [BY WR] MU WM BY2 L2 HU. rewrite !length_app in HU, WR. split.
  - apply bytes_at_app in BY. destruct BY as [BY1 BY]. apply bytes_at_app in BY. destruct BY as [_ BY3].
    apply bytes_at_app. split.
    + eapply bytes_at_transport; [exact BY1| exact MU| cbn; lia].
    + apply bytes_at_app. split; [exact BY2|]. rewrite L2. eapply bytes_at_transport; [exact BY3| exact MU| cbn; lia].
  - rewrite !length_app, L2. (nelim WR 3%nat; intros W0 W1 W). split; [exact W0|]. split; [exact W1|]. intros i Hi. apply WM. apply W. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma split3 : forall (bs : list byte) (i k : Z), 0 <= i -> 0 <= k -> i + k <= Z.of_nat (length bs) ->
  exists l1 l2 l3, bs = l1 ++ l2 ++ l3 /\ Z.of_nat (length l1) = i /\ Z.of_nat (length l2) = k.
Proof.
  intros bs i k Hi Hk H. exists (firstn (Z.to_nat i) bs), (firstn (Z.to_nat k) (skipn (Z.to_nat i) bs)), (skipn (Z.to_nat k) (skipn (Z.to_nat i) bs)).
  split; [| split; [rewrite length_firstn; lia| rewrite length_firstn, length_skipn; lia]].
  rewrite (firstn_skipn (Z.to_nat k)). symmetry. apply firstn_skipn.
Qed.

Section LITS.
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
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length map]; rewrite ?cells_size_mapC8, ?cells_size_mapC1, ?length_map; unfold AERRNO, ATP; lia.
  Hypothesis MEMCPY : asan_memcpy_spec.

  (* [comment removed for export] *)
  Definition litcpy_post (depc : Z) (mo1 : Model) (g1 : lghost) (LB1 : list cblock) (TRS1 : list (list Z)) (B1 np1 : Z) (errv1 : word)
      (buf len off : Z) (loc : list word) (jb : list byte) (shp : list Z) (Fx : bvmap 5 word) (fcx : bv 32)
      (x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (bs' : list byte),
      ms' = MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf + off)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               Fx (ret_pc x1) fcx None m' (seg_rom asegs)
      /\ PVX Q depc m' mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs' loc jb shp Fx fcx
      /\ pb_nul bs' len off.

  Lemma pvx_memcpy_lit : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx (L : Z) (lit : list byte) (k : Z)
      (x1 t0 t1 t2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    PVX Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx ->
    In (L, k) AGLOB_STRS -> bytes_at asegs mm L lit -> Z.of_nat (length lit) = k -> 1 <= k -> 0 <= L -> L + k <= 0x25000 ->
    nth_error lit (Z.to_nat (k - 1)) = Some (wb 0) ->
    off + k < len ->
    evt asegs (litcpy_post depc mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off loc jb shp Fx fcx x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27)
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf + off)) (Z_to_bv 64 L) (Z_to_bv 64 k) a3 a4 a5 a6 a7
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fx (Z_to_bv 64 AASANMEMCPY) fcx None mm (seg_rom asegs)).
  Proof.
    intros until t6. intros [CTX FRX] INL BYL LL K1 L0' LHI NULL ROOM. lits. bandM. sepM.
    (nelimp CTX 19%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ HB16 HB8 GM TV L0 HB HNP).
    (nelimp FRX 11%nat; intros SAVW LOC LL9 PAD ST HDR BODY SHC L16 FRM FA).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    assert (E1 : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; lia).
    (nelim (split3 bs off k ltac:(lia) ltac:(lia) ltac:(lia)) 6%nat; intros l1 l2 l3 EBS EL1 EL2).
    pose proof ARR as ARR0. rewrite EBS in ARR0. pose proof (u8arr_mid _ _ _ _ _ ARR0) as MID. rewrite EL1 in MID.
    apply rw_cells_of_u8arr in MID.
    assert (GSO : shadow_ok mm L k).
    { pose proof (art_global_shadow AI _ _ _ _ _ _ _ _ _ HL) as [GS _]. apply (proj1 (Forall_forall _ _) GS) in INL. exact INL. }
    pose proof (perm_in_head _ _ _ HP) as BIN.   (* [comment removed for export] *)
    eapply evt_cut.
    { pose proof MEMCPY as MC. unfold asan_memcpy_spec, memcpy_contract in MC.
      sepM. eapply MC with (lo := lo) (d := buf + off) (s := L) (n := k) (src := lit) (junk := l2); clear MC; rewrite ?E1; rewrite ?unsigned_lit by lia;
        first [ lazymatch goal with |- icpt_cells _ => eapply (art_icpt_cells AI); exact HL end | exact MI | exact ST | exact BYL | exact LL | reflexivity
              | lazymatch goal with |- context [(Z.to_nat k)] => replace (Z.to_nat k) with (length l2) by lia; exact MID end
              | left; unfold lowmem_range, KLOWSHADOW_BEG; (cut_to LHI CEIL R1 EL1 K1 L0' ROOM R4; lia)
              | lazymatch goal with |- app_range _ _ => app_rng0 end
              | apply wr_range_ok_high; lia
              | intros _; exact GSO
              | intros _; eapply shadow_ok_sub; [eapply (art_block_shadow_ok AI); [exact HL| eapply perm_in_head; exact HP]| (cut_to PN1; (cut_to PN1; lia))| lia| lia]
              | unfold AINTRIN_STACK; lia
              | lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 22%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MU WM MI' BLK' BY' ST').
    rewrite ?E1 in MU, ST'. rewrite ?unsigned_lit in MU, ST' by lia. unfold AINTRIN_STACK in MU.
    (* [comment removed for export] *)
    assert (ARR' : u8arr asegs m' buf (l1 ++ lit ++ l3)).
    { eapply (u8arr_put_mid mm m' buf l1 l2 lit l3 (SA - 2304) SA); [rewrite <- EBS; exact ARR| | exact WM| | lia| rewrite <- EBS; lia].
      - rewrite ?EL1, ?EL2, ?LL. replace (Z.of_nat (length lit)) with k by lia. exact MU.
      - rewrite EL1. exact (proj1 (u8arr_of_rw_cells _ _ _ _ _ BLK')). }
    apply evt_done. unfold litcpy_post. nexists 14%nat. exists m', (l1 ++ lit ++ l3). split; [reflexivity|].
    assert (OWN : Forall (pv_own_iv Q) [(SA - 2304, SA)]) by (constructor; [unfold pv_own_iv; cbn [fst snd]; lia| constructor]).
    assert (HLR : forall b, In b LR -> In b LB1) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    (* [comment removed for export] *)
    assert (HL' : ART AI sp0 SPB LB1 ((Fr, 1) :: LF) TRS1 B1 m' mo1 g1).
    { eapply (art_frame AI); [exact HL| exact MU| exact WM|]. constructor; [| constructor; [| constructor]].
      - do 7 right. left. exists buf, len. cbn. split; [eapply perm_in_head; exact HP| lia].
      - right; left. cbn. lia. }
    pose_blk_band HL BIN.   (* [comment removed for export] *)
    assert (PVA' : pv_agree sp0 LR LF SP PB m m').
    { eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha [Hc Hn]. cbn. split; [| split; [| exact I]].
      - destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(F' & kk & Hin & Hr)|Hsh]]]].
        + lia.
        + pose proof (aclient_image_lt a Hi). lia.
        + destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D]. (lia_on ROOM PL1 PB8 CEIL LO N1 GSA1 GSA2 FLO SPR R1 EL1 BR BSC Hr Hn D).
        + (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(right; exact Hin)) 8%nat; intros Hk _ HF1 HF2 _ _ _ FD).
          destruct (FD buf len (perm_in_head _ _ _ HP)). all: assert (fsz kk = 128 \/ fsz kk = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
          sepM. all: unfold sclr, SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in HF2; Z.div_mod_to_equations; (lia_on ROOM PL1 CEIL LO N1 EL1 Hr HF2 H H0 SMf H1 H2 H6 H7 BR BSC HF1 H16).
        + unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia.
      - eapply (pv_own_not_client Q PVL); [exact HL| exact HLR| unfold pv_own_iv; cbn [fst snd]; lia| exact Hc| exact Hn]. }
    split.
    - split.
      + split; [exact HL'|]. split; [exact HP|].
        split; [eapply (rw_cells_transport asegs); [exact PBS1| exact MU| exact WM| dj]|].
        split; [exact ARR'|]. split; [rewrite !length_app in *; rewrite <- LEN, EBS, !length_app; cbn; lia|]. split; [exact PN|].
        split; [eapply (rw_cells_transport asegs); [unfold AERRNO, ATP in ERR |- *; exact ERR| exact MU| exact WM| dj]|]. split; [exact MI'|].
        split; [exact PVA'|].
        split. { eapply cj_chain_frame; [exact CHN| exact MU| exact WM|]. intros A' n' Hin. cbn.
                 (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ (BLR _ Hin))) 4%nat; intros Q1 _ _ Q4). try rewrite alloc_ceiling_eq in Q4.
                 destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HP A' n' (BLR _ Hin)) as [_ D]. sepM. lia. }
        split. { eapply (chain_cells_ext_below Q mm m' (SP + 16) CH (ASTACK_TOP sp0)); [exact CC| exact CHOK| exact CHB|].
                 intros a Ha. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
        split. { eapply sh_zero_stack_munch; [exact SSZ| exact MU|]. sepM. constructor; [cbn [fst snd]; sclr_tac2| constructor; [cbn [fst snd]; sclr_tac2| constructor]]. }
        split. { intros H16. eapply pb_below_munch; [exact (HB16 H16)| exact MU| cbn; lia]. }
        split. { intros H8. destruct (HB8 H8) as [w BW]. exists w. eapply bytes_at_transport; [exact BW| exact MU| rewrite length_le8; cbn; lia]. }
        split; [exact GM|]. split; [exact TV|]. split; [exact L0|]. split; [exact HB| exact HNP].
      + unfold PVFR. unfold SAVEDV, FHDR, FBODY, SHCV, SHCW in *.
        pose proof (proj1 (pvm_frame_apart Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) buf len (perm_in_head _ _ _ HP)) as FDB.
        split; [eapply (rw_cells_transport asegs); [exact SAVW| exact MU| exact WM| dj]|].
        split; [eapply (rw_cells_transport asegs); [exact LOC| exact MU| exact WM| dj]|]. split; [exact LL9|].
        split; [eapply stk_transport_disjoint; [exact PAD| exact MU| exact WM| dj]|]. split; [exact ST'|].
        split; [eapply (rw_cells_transport asegs); [exact HDR| exact MU| exact WM| (cut_on [K1 ROOM PL1 PB8 CEIL LO N1 GSA1 GSA2 FAL FLO FHI SPR R1 EL1 BR BSC FDB] dj)]|].
        split; [eapply (rw_cells_transport asegs); [exact BODY| exact MU| exact WM| (cut_on [K1 ROOM PL1 PB8 CEIL LO N1 GSA1 GSA2 FAL FLO FHI SPR R1 EL1 BR BSC FDB] dj)]|].
        split; [eapply (rw_cells_transport asegs); [exact SHC| exact MU| exact WM| rewrite ?SHFR; (cut_on [K1 ROOM PL1 PB8 CEIL LO N1 GSA1 GSA2 FAL FLO FHI SPR SHFR L16 R1 EL1 BR BSC FDB] dj)]|].
        split; [exact L16|]. split; [exact FRM| exact FA].
    - exists (k - 1). split; [lia|]. split; [lia|].
      rewrite nth_error_app2 by lia. rewrite nth_error_app1 by lia.
      replace (Z.to_nat (off + (k - 1)) - length l1)%nat with (Z.to_nat (k - 1)) by (lia_on K1 ROOM PL1 CEIL LO N1 GSA1 FLO SPR R1 EL1). exact NULL.
  Qed.
  (* [comment removed for export] *)
  Lemma pvx_commit : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs loc jb shp Fx fcx mm',
    PVMs Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs -> PVFR Q mm loc jb shp Fx fcx ->
    munch [(PB, PB + 16)] mm mm' -> wmono asegs mm mm' -> mem_inv asegs mm' ->
    PBS Q mm' buf len off depc ->
    PVX Q depc mm' mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx.
  Proof.
    intros until mm'. intros CTX FRX MU WM MI' PBS2. lits. bandM. sepM.
    (nelimp CTX 19%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ HB16 HB8 GM TV L0 HB HNP).
    (nelimp FRX 11%nat; intros SAVW LOC LL9 PAD ST HDR BODY SHC L16 FRM FA).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    assert (HLR : forall b, In b LR -> In b LB1) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    assert (OWN : Forall (pv_own_iv Q) [(PB, PB + 16)]) by (constructor; [unfold pv_own_iv; cbn [fst snd]; lia| constructor]).
    unfold SAVEDV, FHDR, FBODY, SHCV, SHCW in *. unfold AERRNO, ATP in ERR.
    split.
    - split; [eapply (pvm_art_store Q PVL); [exact HL| exact MU| exact WM| exact OWN]|]. split; [exact HP|]. split; [exact PBS2|].
      split; [eapply u8arr_transport; [exact ARR| exact MU| exact WM| rewrite LEN; dj]|]. split; [exact LEN|]. split; [exact PN|].
      split; [eapply (rw_cells_transport asegs); [exact ERR| exact MU| exact WM| dj]|]. split; [exact MI'|].
      split; [eapply (pvm_agree_store Q PVL); [exact HL| exact HLR| exact MU| exact WM| exact OWN| exact PVA]|].
      split. { eapply cj_chain_frame; [exact CHN| exact MU| exact WM|]. intros A' n' Hin. cbn.
               (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ (BLR _ Hin))) 4%nat; intros Q1 _ _ Q4). try rewrite alloc_ceiling_eq in Q4. lia. }
      split; [eapply (pvm_chain_cells_store Q PVL); [exact CC| exact MU| exact OWN]|].
      split; [eapply (pvm_sh_zero_store Q PVL); [exact SSZ| exact MU| exact OWN]|].
      destruct (pvm_below_store Q PVL _ _ _ HB16 HB8 MU OWN) as [HB16' HB8'].
      split; [exact HB16'|]. split; [exact HB8'|]. split; [exact GM|]. split; [exact TV|]. split; [exact L0|]. split; [exact HB| exact HNP].
    - unfold PVFR. unfold SAVEDV, FHDR, FBODY, SHCV, SHCW.
      split; [eapply (rw_cells_transport asegs); [exact SAVW| exact MU| exact WM| dj]|].
      split; [eapply (rw_cells_transport asegs); [exact LOC| exact MU| exact WM| dj]|]. split; [exact LL9|].
      split; [eapply stk_transport_disjoint; [exact PAD| exact MU| exact WM| dj]|].
      split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| dj]|].
      split; [eapply (rw_cells_transport asegs); [exact HDR| exact MU| exact WM| dj]|].
      split; [eapply (rw_cells_transport asegs); [exact BODY| exact MU| exact WM| dj]|].
      split; [eapply (rw_cells_transport asegs); [exact SHC| exact MU| exact WM| rewrite ?SHFR; dj]|].
      split; [exact L16|]. split; [exact FRM| exact FA].
  Qed.
  (* [comment removed for export] *)
  Lemma pvx_exit0 : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx,
    PVX Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx ->
    pv_exit Q mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx 0.
  Proof.
    intros until fcx. intros [CTX FRX]. lits. bandM. sepM.
    (nelimp CTX 19%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ HB16 HB8 GM TV L0 HB HNP).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as (R1 & _). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM.
    split; [exact FRX|]. split; [exact HL|]. split; [exact ERR|]. split; [exact MI|]. split; [exact PVA|]. split; [exact CHN|].
    split; [exact CC|]. split; [exact GM|]. split; [exact TV|].
    exists buf, len, off. left. split; [reflexivity|]. split; [exists depc; exact PBS1|]. split; [right; split; [lia| exact HP]|].
    pose proof (pb_pot_mono len INT_MAX ltac:(unfold INT_MAX; lia) ltac:(lia)). pose proof (pb_npot_mono len INT_MAX ltac:(unfold INT_MAX; lia) ltac:(lia)).
    pose proof PB_FAIL_eq as PFE. unfold pb_allow, pb_npallow in *. lia.
  Qed.

  Lemma pvx_exit1 : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx,
    PVX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx -> pb_nul bs len off ->
    pv_exit Q mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx 1.
  Proof.
    intros until fcx. intros [CTX FRX] NUL. lits. bandM. sepM.
    (nelimp CTX 19%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ HB16 HB8 GM TV L0 HB HNP).
    split; [exact FRX|]. split; [exact HL|]. split; [exact ERR|]. split; [exact MI|]. split; [exact PVA|]. split; [exact CHN|].
    split; [exact CC|]. split; [exact GM|]. split; [exact TV|].
    exists buf, len, off. right. split; [reflexivity|]. split; [| split; [exact L0| split; [exact HB| exact HNP]]].
    exists bs. split; [exact HP|]. split; [exact PBS1|]. split; [split; [exact ARR| exact LEN]|]. split; [exact PN| exact NUL].
  Qed.
  (* [comment removed for export] *)
  Lemma pvx_loc_store : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs loc jb shp Fx fcx mm' loc',
    PVMs Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs -> PVFR Q mm loc jb shp Fx fcx ->
    munch [(SA, SA + 72)] mm mm' -> wmono asegs mm mm' -> mem_inv asegs mm' ->
    rw_cells asegs mm' SA (map C8 loc') -> length loc' = 9%nat ->
    PVMs Q depc mm' mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs /\ PVFR Q mm' loc' jb shp Fx fcx.
  Proof.
    intros until loc'. intros CTX FRX MU WM MI' LOC' LL'. lits. bandM. sepM.
    (nelimp CTX 19%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ HB16 HB8 GM TV L0 HB HNP).
    (nelimp FRX 11%nat; intros SAVW LOC LL9 PAD ST HDR BODY SHC L16 FRM FA).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    assert (HLR : forall b, In b LR -> In b LB1) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    assert (OWN : Forall (pv_own_iv Q) [(SA, SA + 72)]) by (constructor; [unfold pv_own_iv; cbn [fst snd]; lia| constructor]).
    unfold SAVEDV, FHDR, FBODY, SHCV, SHCW, PBS in *. unfold AERRNO, ATP in ERR.
    split.
    - split; [eapply (pvm_art_store Q PVL); [exact HL| exact MU| exact WM| exact OWN]|]. split; [exact HP|].
      split; [eapply (rw_cells_transport asegs); [exact PBS1| exact MU| exact WM| dj]|].
      split; [eapply u8arr_transport; [exact ARR| exact MU| exact WM| rewrite LEN; dj]|]. split; [exact LEN|]. split; [exact PN|].
      split; [eapply (rw_cells_transport asegs); [exact ERR| exact MU| exact WM| dj]|]. split; [exact MI'|].
      split; [eapply (pvm_agree_store Q PVL); [exact HL| exact HLR| exact MU| exact WM| exact OWN| exact PVA]|].
      split. { eapply cj_chain_frame; [exact CHN| exact MU| exact WM|]. intros A' n' Hin. cbn.
               (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ (BLR _ Hin))) 4%nat; intros Q1 _ _ Q4). try rewrite alloc_ceiling_eq in Q4. lia. }
      split; [eapply (pvm_chain_cells_store Q PVL); [exact CC| exact MU| exact OWN]|].
      split; [eapply (pvm_sh_zero_store Q PVL); [exact SSZ| exact MU| exact OWN]|].
      destruct (pvm_below_store Q PVL _ _ _ HB16 HB8 MU OWN) as [HB16' HB8'].
      split; [exact HB16'|]. split; [exact HB8'|]. split; [exact GM|]. split; [exact TV|]. split; [exact L0|]. split; [exact HB| exact HNP].
    - unfold PVFR. unfold SAVEDV, FHDR, FBODY, SHCV, SHCW.
      split; [eapply (rw_cells_transport asegs); [exact SAVW| exact MU| exact WM| dj]|].
      split; [exact LOC'|]. split; [exact LL'|].
      split; [eapply stk_transport_disjoint; [exact PAD| exact MU| exact WM| dj]|].
      split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| dj]|].
      split; [eapply (rw_cells_transport asegs); [exact HDR| exact MU| exact WM| dj]|].
      split; [eapply (rw_cells_transport asegs); [exact BODY| exact MU| exact WM| dj]|].
      split; [eapply (rw_cells_transport asegs); [exact SHC| exact MU| exact WM| rewrite ?SHFR; dj]|].
      split; [exact L16|]. split; [exact FRM| exact FA].
  Qed.
End LITS.


End CeilWrap.
