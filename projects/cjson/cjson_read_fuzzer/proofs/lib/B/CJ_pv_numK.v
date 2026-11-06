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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_conv.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pv_ctx CJ_pv_common CJ_pv_cases CJ_pv_calls CJ_pv_lits ICPT_iface.
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
(* [comment removed for export] *)

Lemma FAG18_set : forall F Fc (k : bv 5) v, FAG18 F Fc -> bv_unsigned k < 18 -> FAG18 F (bvmap_set k v Fc).
Proof.
  intros F Fc k v FA Hk r Hr. rewrite freg_get_other; [apply FA; exact Hr|]. unfold bv_eqb. apply Z.eqb_neq. lia.
Qed.

Lemma FAG18_call3 : forall F Fc Ft, FAG18 F Fc ->
  (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get Ft k = reg_get Fc k) -> FAG18 F Ft.
Proof. intros F Fc Ft FA H r Hr. rewrite (H r) by lia. apply FA. exact Hr. Qed.

(* [comment removed for export] *)
Definition SHP_NUM0 : list Z := [-15; -15; -15; -15; 0; 0; 0; 2; -14; -14; -14; -14; -8; -13; -13; -13].
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_app' : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)). rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma rw_cells_app1 : forall m A c cs,
  rw_cells bsegs m A (c :: cs) <-> rw_cells bsegs m A [c] /\ rw_cells bsegs m (A + Z.of_nat (Cells.csize c)) cs.
Proof.
  intros m A c cs. change (c :: cs) with ([c] ++ cs). rewrite (rw_cells_app' bsegs m A [c] cs).
  cbn [cells_size]. rewrite Nat.add_0_r. tauto.
Qed.

(* [comment removed for export] *)
Lemma nd_shb0 : forall (AI : art_iface) sp0 SPB LB LF TRS BB m mo g p off,
  ART AI sp0 SPB LB LF TRS BB m mo g -> In (p, 64) LB -> 0 <= off -> off + 8 <= 64 -> off mod 8 = 0 -> shb m (p + off) 0.
Proof.
  intros AI sp0 SPB LB LF TRS BB m mo g p off HL HIN H0 H1 H2.
  (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL HIN) 3%nat; intros _ AL _).
  pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL HIN) as SO.
  destruct (shadow_ok_shchk m p 64 (p + off) 8 SO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (v & SHB & [->|[C1 C2]]); [exact SHB|].
  exfalso. Z.div_mod_to_equations. lia.
Qed.

Lemma disjoint_from_forall : forall (W : list (Z * Z)) A k,
  Forall (fun iv => A + k <= fst iv \/ snd iv <= A) W -> disjoint_from W A k.
Proof.
  induction W as [|[lo1 hi1] W IH]; intros A k HW; cbn; [exact I|].
  apply Forall_cons_iff in HW as [H1 H2]. cbn [fst snd] in H1. split; [exact H1| apply IH; exact H2].
Qed.

Lemma outside_forall : forall (W : list (Z * Z)) a,
  Forall (fun iv => ~ (fst iv <= a < snd iv)) W -> outside W a.
Proof.
  induction W as [|[lo1 hi1] W IH]; intros a HW; cbn; [exact I|].
  apply Forall_cons_iff in HW as [H1 H2]. cbn [fst snd] in H1. split; [exact H1| apply IH; exact H2].
Qed.

Section NUMK.
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
  Hypothesis MEMSET : asan_memset_spec.
  Hypothesis MEMCPY : asan_memcpy_spec.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition NFR (mm : word -> option byte) (loc : list word) (j0 nb j1 j2 : list byte) (t : word) (j3 : list byte)
      (shp : list Z) (Fx : bvmap 5 word) (fcx : bv 32) : Prop :=
    rw_cells bsegs mm (SP + -120) (SAVEDV Q) /\ rw_cells bsegs mm SA (map C8 loc) /\ length loc = 9%nat
    /\ stk bsegs mm (SA + 72) (SP + -120) /\ stk bsegs mm lo SA
    /\ FHDR Q mm
    /\ rw_cells bsegs mm (Fr + 24) [CB 8 j0] /\ rw_cells bsegs mm (Fr + 32) [CB 26 nb] /\ rw_cells bsegs mm (Fr + 58) [CB 6 j1]
    /\ rw_cells bsegs mm (Fr + 64) [CB 32 j2] /\ rw_cells bsegs mm (Fr + 96) [C8 t] /\ rw_cells bsegs mm (Fr + 104) [CB 16 j3]
    /\ SHCV Q mm shp /\ length shp = 16%nat /\ frm0 fcx /\ FAG18 F Fx.

  Lemma nfr_of_pvfr : forall mm loc jb shp Fx fcx, PVFR Q mm loc jb shp Fx fcx ->
    exists j0 nb j1 j2 t j3, NFR mm loc j0 nb j1 j2 t j3 shp Fx fcx /\ jb = j0 ++ nb ++ j1 ++ j2 ++ le8 t ++ j3.
  Proof.
    intros mm loc jb shp Fx fcx nelH_; (nelim nelH_ 11%nat; intros SAVW LOC LL PAD ST HDR BODY SHC L16 FRM FA).
    unfold FBODY in BODY.
    assert (L96 : length jb = 96%nat) by (destruct BODY as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    pose proof (rw_cells_split_CB bsegs mm (Fr + 24) [] 96 jb [] [8; 26; 6; 32; 8; 16]%nat BODY eq_refl) as SPL.
    cbn [mk_CB_cells app] in SPL.
    set (j0 := firstn 8 jb) in SPL. set (r0 := skipn 8 jb) in SPL.
    set (nb := firstn 26 r0) in SPL. set (r1 := skipn 26 r0) in SPL.
    set (j1 := firstn 6 r1) in SPL. set (r2 := skipn 6 r1) in SPL.
    set (j2 := firstn 32 r2) in SPL. set (r3 := skipn 32 r2) in SPL.
    set (tb := firstn 8 r3) in SPL. set (r4 := skipn 8 r3) in SPL.
    set (j3 := firstn 16 r4) in SPL.
    assert (LTB : length tb = 8%nat) by (subst tb r3 r2 r1 r0; rewrite firstn_length_le; [reflexivity|]; rewrite !length_skipn; lia).
    assert (SPL' : rw_cells bsegs mm (Fr + 24) [CB 8 j0; CB 26 nb; CB 6 j1; CB 32 j2; C8 (le_bytes_to_word tb); CB 16 j3]).
    { pose proof SPL as [[W _] _]. cbn in W. decompose [and] W.
      eapply rw_cells_recast; [exact SPL| cbn; repeat split; first [assumption| exact I]| cbn [cells_bytes cbytes app]; rewrite (le8_of_bytes8 tb LTB); reflexivity]. }
    apply rw_cells_app1 in SPL' as [P0 SPL']. cbn [Cells.csize] in SPL'.
    apply rw_cells_app1 in SPL' as [P1 SPL']. cbn [Cells.csize] in SPL'.
    apply rw_cells_app1 in SPL' as [P2 SPL']. cbn [Cells.csize] in SPL'.
    apply rw_cells_app1 in SPL' as [P3 SPL']. cbn [Cells.csize] in SPL'.
    apply rw_cells_app1 in SPL' as [P4 P5]. cbn [Cells.csize] in P5.
    replace (Fr + 24 + Z.of_nat 8) with (Fr + 32) in P1 by lia.
    replace (Fr + 24 + Z.of_nat 8 + Z.of_nat 26) with (Fr + 58) in P2 by lia.
    replace (Fr + 24 + Z.of_nat 8 + Z.of_nat 26 + Z.of_nat 6) with (Fr + 64) in P3 by lia.
    replace (Fr + 24 + Z.of_nat 8 + Z.of_nat 26 + Z.of_nat 6 + Z.of_nat 32) with (Fr + 96) in P4 by lia.
    replace (Fr + 24 + Z.of_nat 8 + Z.of_nat 26 + Z.of_nat 6 + Z.of_nat 32 + Z.of_nat 8) with (Fr + 104) in P5 by lia.
    exists j0, nb, j1, j2, (le_bytes_to_word tb), j3. split.
    - unfold NFR. repeat (split; [assumption|]). assumption.
    - rewrite (le8_of_bytes8 tb LTB). subst j0 nb j1 j2 tb j3 r0 r1 r2 r3 r4.
      assert (L4' : length (skipn 8 (skipn 32 (skipn 6 (skipn 26 (skipn 8 jb))))) = 16%nat) by (rewrite !length_skipn; lia).
      rewrite (firstn_all2 (n := 16%nat)) by lia.
      rewrite <- (firstn_skipn 8 jb) at 1. f_equal.
      rewrite <- (firstn_skipn 26 (skipn 8 jb)) at 1. f_equal.
      rewrite <- (firstn_skipn 6 (skipn 26 (skipn 8 jb))) at 1. f_equal.
      rewrite <- (firstn_skipn 32 (skipn 6 (skipn 26 (skipn 8 jb)))) at 1. f_equal.
      rewrite <- (firstn_skipn 8 (skipn 32 (skipn 6 (skipn 26 (skipn 8 jb))))) at 1. reflexivity.
  Qed.

  Lemma pvfr_of_nfr : forall mm loc j0 nb j1 j2 t j3 shp Fx fcx, NFR mm loc j0 nb j1 j2 t j3 shp Fx fcx ->
    PVFR Q mm loc (j0 ++ nb ++ j1 ++ j2 ++ le8 t ++ j3) shp Fx fcx.
  Proof.
    intros until fcx. intros nelH_; (nelim nelH_ 16%nat; intros SAVW LOC LL PAD ST HDR P0 P1 P2 P3 P4 P5 SHC L16 FRM FA). lits. bandM. sepM.
    assert (BODY : rw_cells bsegs mm (Fr + 24) [CB 8 j0; CB 26 nb; CB 6 j1; CB 32 j2; C8 t; CB 16 j3]).
    { apply rw_cells_app1. split; [exact P0|]. cbn [Cells.csize]. replace (Fr + 24 + Z.of_nat 8) with (Fr + 32) by lia.
      apply rw_cells_app1. split; [exact P1|]. cbn [Cells.csize]. replace (Fr + 32 + Z.of_nat 26) with (Fr + 58) by lia.
      apply rw_cells_app1. split; [exact P2|]. cbn [Cells.csize]. replace (Fr + 58 + Z.of_nat 6) with (Fr + 64) by lia.
      apply rw_cells_app1. split; [exact P3|]. cbn [Cells.csize]. replace (Fr + 64 + Z.of_nat 32) with (Fr + 96) by lia.
      apply rw_cells_app1. split; [exact P4|]. cbn [Cells.csize]. replace (Fr + 96 + Z.of_nat 8) with (Fr + 104) by lia. exact P5. }
    pose proof (rw_cells_merge bsegs mm (Fr + 24) [] [CB 8 j0; CB 26 nb; CB 6 j1; CB 32 j2; C8 t; CB 16 j3] [] ltac:(rewrite app_nil_r; exact BODY)) as M.
    cbn [cells_size cells_bytes Cells.csize cbytes app Nat.add] in M. rewrite !app_nil_r in M.
    unfold PVFR, FBODY. repeat (split; [assumption|]). exact FA.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pv_wiv (buf len : Z) (iv : Z * Z) : Prop :=
    (lo <= fst iv /\ snd iv <= SP)
    \/ (Fr <= fst iv /\ snd iv <= Fr + 120)
    \/ (Z.shiftr Fr 3 + 2147450880 <= fst iv /\ snd iv <= Z.shiftr Fr 3 + 2147450880 + 16)
    \/ (fst iv = AERRNO /\ snd iv = AERRNO + 4)
    \/ (buf <= fst iv /\ snd iv <= buf + len).

  Lemma pvm_wext : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs W mm' errv' bs',
    PVMs Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs ->
    munch W mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' -> Forall (pv_wiv buf len) W ->
    rw_cells bsegs mm' AERRNO [C4 errv'] -> u8arr bsegs mm' buf bs' -> length bs' = length bs ->
    PVMs Q depc mm' mo1 g1 LB1 TRS1 B1 np1 errv' sbuf slen buf len off bs'.
  Proof.
    intros until bs'. intros CTX MU WM MI' HW ERR' ARR' LBS. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    (nelimp CTX 19%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ HB16 HB8 GM TV L0 HB HNP).
    assert (HLR : forall b, In b LR -> In b LB1) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 _ _ R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (* [comment removed for export] *)
    assert (NUMW : Forall (fun iv => (lo <= fst iv /\ snd iv <= SP)
                                     \/ (0x5ff000 <= fst iv /\ snd iv <= alloc_ceiling /\ Fr <= fst iv /\ snd iv <= Fr + 120)
                                     \/ (0x7fff7000 <= fst iv /\ snd iv <= 0x10007fff8000 /\ snd iv <= 2147450880 + alloc_ceiling / 8)   (* [comment removed for export] *)
                                     \/ (fst iv = 0x5dc8cc /\ snd iv = 0x5dc8d0)
                                     \/ (buf <= fst iv /\ snd iv <= buf + len /\ 0x5ff000 <= fst iv /\ snd iv <= alloc_ceiling)) W).
    { pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2).
      assert (FB3 : Z.shiftr Fr 3 + 2147450880 + 16 <= 2147450880 + alloc_ceiling / 8) by (rewrite SHFR; clear - FAL FHI; Z.div_mod_to_equations; lia).
      eapply Forall_impl; [| exact HW]. intros [u v] Hiv. unfold pv_wiv in Hiv. cbn [fst snd] in Hiv |- *.
      unfold AERRNO, ATP in Hiv. destruct Hiv as [H|[H|[H|[H|H]]]]; [left| right; left| right; right; left| right; right; right; left| right; right; right; right]; (lia_on H PL1 CEIL LO N1 GSA1 FLO FHI SPR SHFR FB2 FB3 R1 R4). }
    pose proof (perm_in_head _ _ _ HP) as BIN. pose_blk_band HL BIN.   (* [comment removed for export] *)
    unfold PVMs. unfold PBS in PBS1 |- *.
    split.
    { eapply (art_frame AI); [exact HL| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. intros iv Hiv.
      unfold pv_wiv in Hiv. destruct Hiv as [H|[H|[H|[H|H]]]].
      - apply (pv_own_write_ok Q PVL). right; left. exact H.
      - apply (pv_own_write_ok Q PVL). right; right; right; left. exact H.
      - apply (pv_own_write_ok Q PVL). right; right; right; right. exact H.
      - unfold cj_write_ok. right; right; right; left. lia.
      - unfold cj_write_ok. do 7 right. left. exists buf, len. split; [eapply perm_in_head; exact HP| lia]. }
    split; [exact HP|].
    split. { eapply (rw_cells_transport bsegs); [exact PBS1| exact MU| exact WM|]. apply disjoint_from_forall.
             eapply Forall_impl; [| exact NUMW]. intros [u v] H. cbn [fst snd cells_size Cells.csize Nat.add] in H |- *. (lia_on PL1 PB8 CEIL LO N1 GSA1 GSA2 FLO FHI SPR R1 H). }
    split; [exact ARR'|]. split; [rewrite <- LEN, LBS; reflexivity|]. split; [exact PN|]. split; [exact ERR'|]. split; [exact MI'|].
    split.
    { eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha [Hc Hn].
      apply outside_forall. apply Forall_forall. intros [u v] Hin. cbn [fst snd].
      pose proof (proj1 (Forall_forall _ _) HW _ Hin) as Hiv. pose proof (proj1 (Forall_forall _ _) NUMW _ Hin) as Hnum. cbn [fst snd] in Hnum.
      unfold pv_wiv in Hiv. cbn [fst snd] in Hiv.
      destruct Hiv as [H|[H|[H|[H|H]]]].
      - eapply (pv_own_not_client Q PVL); [exact HL| exact HLR| right; left; exact H| exact Hc| exact Hn].
      - eapply (pv_own_not_client Q PVL); [exact HL| exact HLR| right; right; right; left; exact H| exact Hc| exact Hn].
      - eapply (pv_own_not_client Q PVL); [exact HL| exact HLR| right; right; right; right; exact H| exact Hc| exact Hn].
      - (* [comment removed for export] *)
        unfold AERRNO, ATP in H.
        destruct Hc as [Hs|[Hi|[(A' & n' & Hin' & Hr)|[(F' & kk & Hin' & Hr)|Hsh]]]].
        + lia.
        + unfold aclient_image, AERRNO, ATP, AGERROR0, AGERROR1 in Hi. sepM. (lia_on PL1 PB8 CEIL LO N1 GSA1 GSA2 FLO SPR R1 Hi H Hnum).
        + pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ Hin')) as (Q1 & _). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Q1. bandM. sepM. lia.
        + (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(right; exact Hin')) 5%nat; intros Hk _ HF1 HF2 _).
          unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in HF1. bandM. sepM. assert (K : fsz kk = 128 \/ fsz kk = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
          unfold SH, SHADOW_OFFSET in Hr. Z.div_mod_to_equations. (lia_on PL1 CEIL LO N1 Hr H Hnum HF1 H5 H6).
        + unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. (lia_on CEIL Hsh H Hnum H0 H1).
      - (* [comment removed for export] *)
        destruct Hc as [Hs|[Hi|[(A' & n' & Hin' & Hr)|[(F' & kk & Hin' & Hr)|Hsh]]]].
        + lia.
        + pose proof (aclient_image_lt a Hi). lia.
        + destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HP A' n' Hin') as [_ D]. sepM. (lia_on Hr H D).
        + (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(right; exact Hin')) 8%nat; intros Hk _ HF1 HF2 _ _ _ FD).
          destruct (FD buf len (perm_in_head _ _ _ HP)). all: assert (K : fsz kk = 128 \/ fsz kk = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
          sepM. all: unfold sclr, SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in HF2; Z.div_mod_to_equations; (lia_on Hr H HF1 HF2 H0 H6 H7 H11 H12 BSC).
        + unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. (lia_on PL1 CEIL LO N1 BR BSC Hsh H H0 H1 H5 H6 H15). }
    split.
    { eapply cj_chain_frame; [exact CHN| exact MU| exact WM|]. intros A' n' Hin. apply disjoint_from_forall.
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ (BLR _ Hin))) 4%nat; intros Q1 _ _ Q4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Q1. bandM. sepM. try rewrite alloc_ceiling_eq in Q4.
      destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HP A' n' (BLR _ Hin)) as [_ D].
      (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) 8%nat; intros _ _ _ _ _ _ _ FD). change (fsz 1) with 128 in FD.
      pose proof (FD A' n' (HLR _ (BLR _ Hin))) as FDB.
      pose proof (HLR _ (BLR _ Hin)) as INA'. pose_blk_band HL INA'.   (* [comment removed for export] *)
      eapply Forall_impl; [| exact NUMW]. intros [u v] H. cbn [fst snd] in H |- *. sepM. (lia_on LBS PL1 PB8 CEIL LO N1 GSA1 GSA2 FLO SPR LEN R1 BR Q1 BR0 H SMf SMf0 SMf1). }
    split.
    { eapply (chain_cells_ext_below Q mm mm' (SP + 16) CH (ASTACK_TOP sp0)); [exact CC| exact CHOK| exact CHB|].
      intros a Ha. apply MU. rewrite wa_unsigned by lia. apply outside_forall.
      eapply Forall_impl; [| exact NUMW]. intros [u v] H. cbn [fst snd] in H |- *. (lia_on PL1 PB8 CEIL LO N1 GSA1 GSA2 FLO FHI SPR R1 BR Ha H). }
    split.
    { eapply sh_zero_ext; [exact SSZ|]. intros j Hj. apply MU.
      assert (Rb : SH (2^47 - 1) = 0x10007fff7fff) by reflexivity. rewrite Rb in Hj. unfold SH, SHADOW_OFFSET in Hj.   (* [comment removed for export] *)
      pose proof alloc_ceiling_range as ACR. rewrite wa_unsigned by lia. apply outside_forall.
      eapply Forall_impl; [| exact NUMW]. intros [u v] H. cbn [fst snd] in H |- *. (lia_on PL1 PB8 CEIL LO N1 GSA1 GSA2 FAL FLO SPR BMf R1 BR BSC Hj ACR H). }
    assert (AG : forall a, SP <= a < PB -> mm' (wa a) = mm (wa a)).
    { intros a Ha. apply MU. rewrite wa_unsigned by lia. apply outside_forall.
      eapply Forall_impl; [| exact NUMW]. intros [u v] H. cbn [fst snd] in H |- *. lia. }
    split.
    { intros H16. (nelim (HB16 H16) 4%nat; intros w1 w2 BY LE). exists w1, w2. split; [| exact LE].
      (nelim BY 3%nat; intros B0 B1' B2). split; [exact B0|]. split; [exact B1'|]. intros i Hi.
      rewrite <- (B2 i Hi). unfold mrd. rewrite AG; [reflexivity|].
      rewrite length_app, !length_le8 in Hi. cbn in Hi. lia. }
    split.
    { intros H8. destruct (HB8 H8) as [w BW]. exists w. (nelim BW 3%nat; intros B0 B1' B2). split; [exact B0|]. split; [exact B1'|]. intros i Hi.
      rewrite <- (B2 i Hi). unfold mrd. rewrite AG; [reflexivity|]. rewrite length_le8 in Hi. cbn in Hi. lia. }
    split; [exact GM|]. split; [exact TV|]. split; [exact L0|]. split; [exact HB| exact HNP].
  Qed.

  (* [comment removed for export] *)
  Definition pv_wiv0 (iv : Z * Z) : Prop :=
    (lo <= fst iv /\ snd iv <= SP)
    \/ (Fr <= fst iv /\ snd iv <= Fr + 120)
    \/ (Z.shiftr Fr 3 + 2147450880 <= fst iv /\ snd iv <= Z.shiftr Fr 3 + 2147450880 + 16).

  Lemma pvm_wext0 : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs W mm',
    PVMs Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs ->
    munch W mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' -> Forall pv_wiv0 W ->
    PVMs Q depc mm' mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs.
  Proof.
    intros until mm'. intros CTX MU WM MI' HW. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    (nelimp CTX 9%nat; intros HL HP PBS1 ARR LEN PN ERR MI _).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 _ _ R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) 8%nat; intros _ _ _ _ _ _ _ FD). change (fsz 1) with 128 in FD.
    pose proof (FD buf len (perm_in_head _ _ _ HP)) as FDB.
    eapply pvm_wext; [exact CTX| exact MU| exact WM| exact MI'| | | | reflexivity].
    - eapply Forall_impl; [| exact HW]. intros iv Hiv. unfold pv_wiv0 in Hiv. unfold pv_wiv. tauto.
    - eapply (rw_cells_transport bsegs); [exact ERR| exact MU| exact WM|]. apply disjoint_from_forall.
      eapply Forall_impl; [| exact HW]. intros [u v] H. unfold pv_wiv0 in H. cbn [fst snd cells_size Cells.csize Nat.add] in H |- *.
      unfold AERRNO, ATP. rewrite ?SHFR in H. Z.div_mod_to_equations. lia.
    - eapply u8arr_transport; [exact ARR| exact MU| exact WM|]. rewrite LEN. apply disjoint_from_forall.
      eapply Forall_impl; [| exact HW]. intros [u v] H. unfold pv_wiv0 in H. cbn [fst snd] in H |- *.
      (* [comment removed for export] *)
      pose proof (perm_in_head _ _ _ HP) as BIN. pose_blk_band HL BIN. pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2). (lia_on PL1 PB8 CEIL LO N1 GSA1 GSA2 FAL FLO FHI SPR SHFR R1 FDB H BR BSC).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition nf_wiv (iv : Z * Z) : Prop :=
    (lo <= fst iv /\ snd iv <= SA)
    \/ (SP <= fst iv)
    \/ (Fr + 32 <= fst iv /\ snd iv <= Fr + 58)
    \/ (Fr + 96 <= fst iv /\ snd iv <= Fr + 104)
    \/ (fst iv = AERRNO /\ snd iv = AERRNO + 4)
    \/ (AIMG_HI <= fst iv /\ snd iv <= alloc_ceiling /\ (snd iv + 16 <= Fr \/ Fr + 128 <= fst iv - 16)
        /\ (snd iv <= 0x7fff7000 \/ 0x10007fff8000 <= fst iv)).      (* [comment removed for export] *)

  Lemma nfr_wext : forall mm loc j0 nb j1 j2 t j3 shp Fx fcx W mm' nb' t' Fx' fcx',
    NFR mm loc j0 nb j1 j2 t j3 shp Fx fcx ->
    munch W mm mm' -> wmono bsegs mm mm' -> Forall nf_wiv W ->
    stk bsegs mm' lo SA -> rw_cells bsegs mm' (Fr + 32) [CB 26 nb'] -> rw_cells bsegs mm' (Fr + 96) [C8 t'] ->
    frm0 fcx' -> FAG18 F Fx' ->
    NFR mm' loc j0 nb' j1 j2 t' j3 shp Fx' fcx'.
  Proof.
    intros until fcx'. intros (SAVW & LOC & LL & PAD & ST & HDR & P0 & P1 & P2 & P3 & P4 & P5 & SHC & L16 & FRM & FA) MU WM HW ST' P1' P4' FRM' FA'.
    lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    assert (NUMW : Forall (fun iv => (lo <= fst iv /\ snd iv <= SA)
                                     \/ (SP <= fst iv)
                                     \/ (Fr + 32 <= fst iv /\ snd iv <= Fr + 58)
                                     \/ (Fr + 96 <= fst iv /\ snd iv <= Fr + 104)
                                     \/ (fst iv = 0x5dc8cc /\ snd iv = 0x5dc8d0)
                                     \/ (0x5ff000 <= fst iv /\ snd iv <= alloc_ceiling /\ (snd iv + 16 <= Fr \/ Fr + 128 <= fst iv - 16)
                                         /\ (snd iv <= 0x7fff7000 \/ 0x10007fff8000 <= fst iv))) W).
    { eapply Forall_impl; [| exact HW]. intros [u v] Hiv. unfold nf_wiv in Hiv. cbn [fst snd] in Hiv |- *.
      unfold sclr, AERRNO, ATP, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Hiv. try rewrite alloc_ceiling_eq in Hiv. sepM. (lia_on Hiv). }
    unfold NFR. unfold SAVEDV in SAVW |- *. unfold FHDR in HDR |- *. unfold SHCV, SHCW in SHC |- *.
    Ltac tr H MU WM NUMW := eapply (rw_cells_transport bsegs); [exact H| exact MU| exact WM|]; apply disjoint_from_forall;
      eapply Forall_impl; [| exact NUMW]; intros [u v] HH; cbn [fst snd cells_size Cells.csize Nat.add length map] in HH |- *;
      rewrite ?cells_size_mapC8, ?cells_size_mapC1, ?length_map; lia.
    split; [tr SAVW MU WM NUMW|].
    split; [tr LOC MU WM NUMW|]. split; [exact LL|].
    split. { eapply stk_transport_disjoint; [exact PAD| exact MU| exact WM|]. apply disjoint_from_forall.
             eapply Forall_impl; [| exact NUMW]; intros [u v] HH; cbn [fst snd] in HH |- *. lia. }
    split; [exact ST'|].
    split; [tr HDR MU WM NUMW|].
    split; [tr P0 MU WM NUMW|]. split; [exact P1'|]. split; [tr P2 MU WM NUMW|]. split; [tr P3 MU WM NUMW|]. split; [exact P4'|]. split; [tr P5 MU WM NUMW|].
    split. { eapply (rw_cells_transport bsegs); [exact SHC| exact MU| exact WM|]; apply disjoint_from_forall.
             eapply Forall_impl; [| exact NUMW]; intros [u v] HH; cbn [fst snd] in HH |- *.
             rewrite cells_size_mapC1, length_map, L16. pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2). lia. }   (* [comment removed for export] *)
    split; [exact L16|]. split; [exact FRM'| exact FA'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma shcv_vis : forall mm shp j, SHCV Q mm shp -> length shp = 16%nat ->
    Z.shiftr Fr 3 + 2147450880 <= j < Z.shiftr Fr 3 + 2147450880 + 16 -> mm (wa j) <> None.
  Proof.
    intros mm shp j SHC L16 Hj. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. unfold SHCV, SHCW in SHC.
    destruct SHC as [[_ BY] _]. (nelim BY 3%nat; intros _ _ BY).
    specialize (BY (Z.to_nat (j - (Z.shiftr Fr 3 + 2147450880)))).
    rewrite cells_bytes_length in BY by (clear; induction shp; cbn; [exact I| split; [reflexivity| assumption]]).
    rewrite cells_size_mapC1, !length_map, L16 in BY. specialize (BY ltac:(lia)).
    replace (Z.shiftr Fr 3 + 2147450880 + Z.of_nat (Z.to_nat (j - (Z.shiftr Fr 3 + 2147450880)))) with j in BY by lia.
    destruct (nth_error (cells_bytes (map C1 (map zb shp)))) as [b|] eqn:E.
    - replace j with (SH (Fr + 8 * (j - SH Fr))) in BY |- * by (unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia).
      apply mrd_shadow in BY; [congruence|]. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia.
    - exfalso. apply nth_error_None in E. rewrite cells_bytes_length in E by (clear; induction shp; cbn; [exact I| split; [reflexivity| assumption]]).
      rewrite cells_size_mapC1, !length_map, L16 in E. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma shcv_enc26 : forall mm shp, SHCV Q mm shp -> length shp = 16%nat ->
    firstn 4 (skipn 4 shp) = [0; 0; 0; 2] -> sh_bytes mm (Fr + 32) (shadow_enc 26).
  Proof.
    intros mm shp SHC L16 E. lits. bandM. sepM. unfold SHCV, SHCW in SHC.
    rewrite <- (firstn_skipn 4 shp) in SHC. rewrite <- (firstn_skipn 4 (skipn 4 shp)) in SHC. rewrite E in SHC.
    rewrite !map_app in SHC.
    apply (proj1 (rw_cells_app' _ _ _ _ _)) in SHC as [_ SHC].
    apply (proj1 (rw_cells_app' _ _ _ _ _)) in SHC as [SHC _].
    rewrite cells_size_mapC1, !length_map, firstn_length_le in SHC by lia.
    replace (Z.shiftr Fr 3 + 2147450880 + Z.of_nat 4) with (SH (Fr + 32)) in SHC by (unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia).
    change (shadow_enc 26) with [0; 0; 0; 2]. unfold sh_bytes, shcells. cbn [map] in SHC |- *. exact (proj1 SHC).
  Qed.

  Lemma num_shadow_ok26 : forall mm shp, SHCV Q mm shp -> length shp = 16%nat ->
    firstn 4 (skipn 4 shp) = [0; 0; 0; 2] -> shadow_ok mm (Fr + 32) 26.
  Proof.
    intros mm shp SHC L16 E. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. pose proof (shcv_enc26 mm shp SHC L16 E) as SB. split.
    - intros i Hi. eapply shadow_enc_addressable; [exact SB| Z.div_mod_to_equations; lia| lia| lia| exact Hi].
    - intros j Hj. eapply (shcv_vis mm shp j SHC L16). unfold SH, SHADOW_OFFSET in Hj. rewrite SHFR. Z.div_mod_to_equations. lia.
  Qed.

  Lemma num_shchk1 : forall mm shp a, SHCV Q mm shp -> length shp = 16%nat ->
    firstn 4 (skipn 4 shp) = [0; 0; 0; 2] -> Fr + 32 <= a < Fr + 58 -> shchk mm a 1.
  Proof.
    intros mm shp a SHC L16 E Ha. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. pose proof (shcv_enc26 mm shp SHC L16 E) as SB.
    eapply shadow_enc_shchk; [exact SB| Z.div_mod_to_equations; lia| lia| lia| lia| lia| left; reflexivity| apply Z.mod_1_r].
  Qed.

  (* [comment removed for export] *)
  Lemma num_shadow_ok_pd : forall mm shp, SHCV Q mm shp -> length shp = 16%nat ->
    nth_error shp 12 = Some 0 -> shadow_ok mm (Fr + 96) 8.
  Proof.
    intros mm shp SHC L16 E. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. pose proof SHC as SHC0. unfold SHCV in SHC. apply SHCW_sh_bytes in SHC. split.
    - intros i Hi. exists 0. split; [| left; reflexivity].
      eapply (sh_bytes_shb mm Fr shp 12 0 (Fr + 96 + i) SHC); [Z.div_mod_to_equations; lia| exact E| cbn; lia| lia].
    - intros j Hj. eapply (shcv_vis mm shp j SHC0 L16). unfold SH, SHADOW_OFFSET in Hj. rewrite SHFR. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition NUMX depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs loc j0 nb j1 j2 t j3 shp Fx fcx : Prop :=
    PVMs Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs /\ NFR mm loc j0 nb j1 j2 t j3 shp Fx fcx.

  Definition ncall_post (depc : Z) (mo1 : Model) (g1 : lghost) (LB1 : list cblock) (TRS1 : list (list Z)) (B1 np1 : Z) (errv1 : word)
      (sbuf slen buf len off : Z) (bs : list byte) (loc : list word) (j0 nb' j1 j2 : list byte) (t : word) (j3 : list byte) (shp : list Z)
      (Fx : bvmap 5 word) (fcx : bv 32) (x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 (Fr + 32)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               Fx (ret_pc x1) fcx None m' (seg_rom bsegs)
      /\ NUMX depc m' mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs loc j0 nb' j1 j2 t j3 shp Fx fcx.

  (* [comment removed for export] *)
  Lemma num_memset26 : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs loc j0 nb j1 j2 t j3 shp Fx fcx
      (x1 t0 t1 t2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    NUMX depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs loc j0 nb j1 j2 t j3 shp Fx fcx ->
    firstn 4 (skipn 4 shp) = [0; 0; 0; 2] ->
    evt bsegs (ncall_post depc mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs loc j0 (repeat (Z_to_bv 8 0) 26) j1 j2 t j3 shp Fx fcx
                          x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27)
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 0) (Z_to_bv 64 26) a3 a4 a5 a6 a7
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fx (Z_to_bv 64 AASANMEMSET) fcx None mm (seg_rom bsegs)).
  Proof.
    intros until t6. intros [CTX FRX] E47. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    (nelimp CTX 9%nat; intros HL HP PBS1 ARR LEN PN ERR MI _).
    (nelimp FRX 16%nat; intros SAVW LOC LL9 PAD ST HDR P0 P1 P2 P3 P4 P5 SHC L16 FRM FA).
    assert (E1 : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; lia).
    pose proof (num_shadow_ok26 mm shp SHC L16 E47) as SOK.
    eapply evt_cut.
    { pose proof MEMSET as MS0. unfold asan_memset_spec, memset_contract in MS0.
      eapply MS0 with (lo := lo) (d := Fr + 32) (c := 0) (n := 26) (junk := nb); clear MS0; rewrite ?E1; rewrite ?unsigned_lit by lia;
        first [ eapply (art_icpt_cells AI); exact HL | exact MI | exact ST | exact P1 | reflexivity
              | app_rng0
              | apply wr_range_ok_high; lia
              | intros _; exact SOK
              | unfold AINTRIN_STACK; lia
              | lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 21%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MU WM MI' BLK' ST').
    rewrite ?E1 in MU, ST'. unfold AINTRIN_STACK in MU.
    apply evt_done. unfold ncall_post. nexists 14%nat. exists m'. split; [reflexivity|]. split.
    - eapply pvm_wext0; [exact CTX| exact MU| exact WM| exact MI'|].
      constructor; [unfold pv_wiv0; cbn [fst snd]; lia|]. constructor; [unfold pv_wiv0; cbn [fst snd]; lia| constructor].
    - eapply nfr_wext; [exact FRX| exact MU| exact WM| | exact ST'| exact BLK'| | exact FRM| exact FA].
      + constructor; [unfold nf_wiv; cbn [fst snd]; lia|]. constructor; [unfold nf_wiv; cbn [fst snd]; (lia_on PL1 CEIL LO N1 GSA1 FLO FHI SPR KHE)| constructor].
      + eapply (rw_cells_transport bsegs); [exact P4| exact MU| exact WM| dj].
  Qed.

  (* [comment removed for export] *)
  Lemma num_memcpy_null : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs loc j0 nb j1 j2 t j3 shp Fx fcx
      (x1 t0 t1 t2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    NUMX depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs loc j0 nb j1 j2 t j3 shp Fx fcx ->
    firstn 4 (skipn 4 shp) = [0; 0; 0; 2] ->
    evt bsegs (ncall_post depc mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs loc j0 (lit_null ++ skipn 5 nb) j1 j2 t j3 shp Fx fcx
                          x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27)
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 LIT_NULL) (Z_to_bv 64 5) a3 a4 a5 a6 a7
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fx (Z_to_bv 64 AASANMEMCPY) fcx None mm (seg_rom bsegs)).
  Proof.
    intros until t6. intros [CTX FRX] E47. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    (nelimp CTX 9%nat; intros HL HP PBS1 ARR LEN PN ERR MI _).
    (nelimp FRX 16%nat; intros SAVW LOC LL9 PAD ST HDR P0 P1 P2 P3 P4 P5 SHC L16 FRM FA).
    assert (E1 : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; lia).
    pose proof (num_shadow_ok26 mm shp SHC L16 E47) as SOK.
    assert (GSO : shadow_ok mm LIT_NULL 5).
    { pose proof (art_global_shadow AI _ _ _ _ _ _ _ _ _ HL) as [GS _]. exact (proj1 (Forall_forall _ _) GS _ (proj1 lit_slots)). }
    assert (L26 : length nb = 26%nat) by (destruct P1 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB bsegs mm (Fr + 32) [] 26 nb [] [5; 21]%nat P1 eq_refl) as P1s. cbn [mk_CB_cells app] in P1s.
    apply rw_cells_app1 in P1s as [P1a P1b]. cbn [Cells.csize] in P1b.
    eapply evt_cut.
    { pose proof MEMCPY as MC. unfold asan_memcpy_spec, memcpy_contract in MC.
      sepM. eapply MC with (lo := lo) (d := Fr + 32) (s := LIT_NULL) (n := 5) (src := lit_null) (junk := firstn 5 nb); clear MC; rewrite ?E1; rewrite ?unsigned_lit by lia;
        first [ eapply (art_icpt_cells AI); exact HL | exact MI | exact ST | apply lit_null_at; exact MI | exact P1a | reflexivity
              | unfold LIT_NULL; (cut_to CEIL LO GSA1 FLO KHE FHI; lia)
              | left; unfold lowmem_range, LIT_NULL, KLOWSHADOW_BEG; lia
              | app_rng0
              | apply wr_range_ok_high; lia
              | intros _; exact GSO
              | intros _; eapply shadow_ok_sub; [exact SOK| lia| lia| lia]
              | unfold AINTRIN_STACK; lia
              | unfold LIT_NULL; lia
              | lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 22%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MU WM MI' BLK' BY' ST').
    rewrite ?E1 in MU, ST'. unfold AINTRIN_STACK in MU.
    apply evt_done. unfold ncall_post. nexists 14%nat. exists m'. split; [reflexivity|].
    assert (P1' : rw_cells bsegs m' (Fr + 32) [CB 26 (lit_null ++ skipn 5 nb)]).
    { pose proof (rw_cells_transport bsegs _ mm m' _ _ P1b MU WM ltac:(dj)) as P1b'.
      assert (J : rw_cells bsegs m' (Fr + 32) [CB 5 lit_null; CB 21 (skipn 5 nb)]).
      { apply rw_cells_app1. split; [exact BLK'|]. cbn [Cells.csize]. replace (Z.to_nat 5) with 5%nat by reflexivity.
        replace (firstn 21 (skipn 5 nb)) with (skipn 5 nb) in P1b' by (symmetry; apply firstn_all2; rewrite length_skipn; lia). exact P1b'. }
      pose proof (rw_cells_merge bsegs m' (Fr + 32) [] [CB 5 lit_null; CB 21 (skipn 5 nb)] [] ltac:(rewrite app_nil_r; exact J)) as M.
      cbn [cells_size cells_bytes Cells.csize cbytes app Nat.add] in M. rewrite !app_nil_r in M. exact M. }
    split.
    - eapply pvm_wext0; [exact CTX| exact MU| exact WM| exact MI'|].
      constructor; [unfold pv_wiv0; cbn [fst snd]; lia|]. constructor; [unfold pv_wiv0; cbn [fst snd]; lia| constructor].
    - eapply nfr_wext; [exact FRX| exact MU| exact WM| | exact ST'| exact P1'| | exact FRM| exact FA].
      + constructor; [unfold nf_wiv; cbn [fst snd]; lia|]. constructor; [unfold nf_wiv; cbn [fst snd]; (lia_on PL1 CEIL LO N1 GSA1 FLO FHI SPR KHE)| constructor].
      + eapply (rw_cells_transport bsegs); [exact P4| exact MU| exact WM| dj].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pvm_off_store : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs mm' off',
    PVM Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs ->
    munch [(PB, PB + 32)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
    PBS Q mm' buf len off' depc -> 0 <= off' <= len ->
    PVM Q depc mm' mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off' bs.
  Proof.
    intros until off'. intros CTX MU WM MI' PBS2 HO. lits. bandM. sepM.
    (nelimp CTX 19%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ HB16 HB8 GM TV L0 HB HNP).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    assert (HLR : forall b, In b LR -> In b LB1) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    assert (OWN : Forall (pv_own_iv Q) [(PB, PB + 32)]) by (constructor; [unfold pv_own_iv; cbn [fst snd]; lia| constructor]).
    unfold AERRNO, ATP in ERR. unfold PVM, PVMs.
    split; [eapply (pvm_art_store Q PVL); [exact HL| exact MU| exact WM| exact OWN]|]. split; [exact HP|]. split; [exact PBS2|].
    split; [eapply u8arr_transport; [exact ARR| exact MU| exact WM| rewrite LEN; dj]|]. split; [exact LEN|]. split; [unfold pb_nums; lia|].
    split; [eapply (rw_cells_transport bsegs); [exact ERR| exact MU| exact WM| dj]|]. split; [exact MI'|].
    split; [eapply (pvm_agree_store Q PVL); [exact HL| exact HLR| exact MU| exact WM| exact OWN| exact PVA]|].
    split. { eapply cj_chain_frame; [exact CHN| exact MU| exact WM|]. intros A' n' Hin. cbn.
             (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ (BLR _ Hin))) 4%nat; intros Q1 _ _ Q4). try rewrite alloc_ceiling_eq in Q4. lia. }
    split; [eapply (pvm_chain_cells_store Q PVL); [exact CC| exact MU| exact OWN]|].
    split; [eapply (pvm_sh_zero_store Q PVL); [exact SSZ| exact MU| exact OWN]|].
    destruct (pvm_below_store Q PVL _ _ _ HB16 HB8 MU OWN) as [HB16' HB8'].
    split; [exact HB16'|]. split; [exact HB8'|]. split; [exact GM|]. split; [exact TV|]. split; [exact L0|]. split; [exact HB| exact HNP].
  Qed.
End NUMK.


End CeilWrap.
