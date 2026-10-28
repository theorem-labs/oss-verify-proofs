From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_Conv LbB_MILB LbB_PrsStmt LbB_HKit LbB_HStKit LbB_PmExit LbB_PiStmt LbB_PiInit LbB_PmTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt LbB_RwStm LbB_PmHTK LbB_PmMagRS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma wadd1 : forall a, 0 <= a -> a + 1 < 2 ^ 64 -> Z_to_bv 64 (a + 1) = (Z_to_bv 64 a + 1)%bv.
Proof.
  intros a Ha Hb. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change (bv_unsigned (1%bv : bv 64)) with 1.
  rewrite (Z.mod_small a) by lia. reflexivity.
Qed.

Lemma rdn4_join : forall segs m (x : word) b0 b1 b2 b3, PropExec.rdn segs m x 1 = Some [b0] ->
  PropExec.rdn segs m (x + 1)%bv 1 = Some [b1] -> PropExec.rdn segs m (x + 1 + 1)%bv 1 = Some [b2] ->
  PropExec.rdn segs m (x + 1 + 1 + 1)%bv 1 = Some [b3] -> PropExec.rdn segs m x 4 = Some [b0; b1; b2; b3].
Proof.
  intros segs m x b0 b1 b2 b3 R0 R1 R2 R3. cbn [PropExec.rdn] in *.
  destruct (match m x with Some b => Some b | None => PropExec.seg_rom segs x end) as [c0|]; [|discriminate].
  destruct (match m (x + 1)%bv with Some b => Some b | None => PropExec.seg_rom segs (x + 1)%bv end) as [c1|]; [|discriminate].
  destruct (match m (x + 1 + 1)%bv with Some b => Some b | None => PropExec.seg_rom segs (x + 1 + 1)%bv end) as [c2|]; [|discriminate].
  destruct (match m (x + 1 + 1 + 1)%bv with Some b => Some b | None => PropExec.seg_rom segs (x + 1 + 1 + 1)%bv end) as [c3|]; [|discriminate].
  injection R0 as ->. injection R1 as ->. injection R2 as ->. injection R3 as ->. reflexivity.
Qed.

Lemma rdn4_fld : forall m a (b0 b1 b2 b3 : byte), 0 <= a -> a + 4 < 2 ^ 64 ->
  PropExec.rdn asegs m (Z_to_bv 64 (a + 0)) 1 = Some [b0] -> PropExec.rdn asegs m (Z_to_bv 64 (a + 1)) 1 = Some [b1] ->
  PropExec.rdn asegs m (Z_to_bv 64 (a + 2)) 1 = Some [b2] -> PropExec.rdn asegs m (Z_to_bv 64 (a + 3)) 1 = Some [b3] ->
  fldA m a 4 (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
Proof.
  intros m a b0 b1 b2 b3 Ha Hb R0 R1 R2 R3.
  rewrite (wadd1 a) in R1 by lia.
  replace (a + 2) with ((a + 1) + 1) in R2 by lia. rewrite (wadd1 (a + 1)), (wadd1 a) in R2 by lia.
  replace (a + 3) with (((a + 1) + 1) + 1) in R3 by lia.
  rewrite (wadd1 ((a + 1) + 1)), (wadd1 (a + 1)), (wadd1 a) in R3 by lia.
  rewrite Z.add_0_r in R0.
  pose proof (bv_unsigned_in_range _ b0) as B0. pose proof (bv_unsigned_in_range _ b1) as B1.
  pose proof (bv_unsigned_in_range _ b2) as B2. pose proof (bv_unsigned_in_range _ b3) as B3.
  unfold bv_modulus in B0, B1, B2, B3. change (2 ^ Z.of_N 8) with 256 in B0, B1, B2, B3.
  unfold fldA, fld.
  replace (word_to_le_bytes 4 (Z_to_bv 64 _)) with [b0; b1; b2; b3].
  - exact (rdn4_join _ _ _ _ _ _ _ R0 R1 R2 R3).
  - apply TablRep.map_unsigned_inj. rewrite TablRep.le4_bytes by lia. unfold TablRep.le4. cbn [map].
    f_equal; [| f_equal; [| f_equal; [| f_equal]]]; Z.div_mod_to_equations; lia.
Qed.

Definition st_e (c : stateC) (e : Z) : stateC :=
  {| st_words := st_words c; st_nwords := st_nwords c; st_diag := st_diag c; st_widx := st_widx c;
     st_icount := st_icount c; st_endian := e; st_flags := e;
     st_m1 := st_m1 c; st_m2 := st_m2 c; st_m3 := st_m3 c; st_v1 := st_v1 c; st_v2 := st_v2 c; st_v3 := st_v3 c |}.
Definition pc_e (c : parserC) (e : Z) : parserC :=
  {| pc_cons := pc_cons c; pc_user := pc_user c; pc_state := st_e (pc_state c) e |}.

Lemma state_rep_endianA : forall LB m m' st c e,
  @state_rep AC_A ASEGS LY_A MI_A (lbl LB) m st c -> AIMG_TOP <= st -> st + 240 <= 2 ^ 47 ->
  (st_flags c = 0 \/ st_flags c = 1) -> (e = 0 \/ e = 1) ->
  (forall a, st <= a < st + 240 -> ~ (st + 40 <= a < st + 45) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall a b, In b (state_blocks c) -> fst b <= a < fst b + snd b -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  fld ASEGS m' (st + 40) 4 e -> fld ASEGS m' (st + 44) 1 e ->
  @state_rep AC_A ASEGS LY_A MI_A (lbl LB) m' st (st_e c e).
Proof.
  intros LB m m' st c e SR Hlo Hhi HF He HMo HMb F5 F6.
  pose proof Hlo as Hlo'. unfold AIMG_TOP in Hlo'.
  destruct SR as [W0 W1 W2 W3 W4 W5 W6 Sm1 Sm2 Sm3 Sv1 Sv2 Sv3 Sdef Sal Snd].
  assert (AGO : forall o k, 0 <= o -> o + k <= 240 -> (o + k <= 40 \/ 45 <= o) -> HRepFacts.agree_on m m' (st + o) k).
  { intros o k Ho Hk Hx i Hi. apply HMo; lia. }
  assert (CW : forall o (wd : N) v, cellw ASEGS m (st + o) wd v -> 0 <= o -> o + Z.of_N wd <= 240 ->
                 (o + Z.of_N wd <= 40 \/ 45 <= o) -> cellw ASEGS m' (st + o) wd v).
  { intros o wd v C Ho Hk Hx. eapply cellw_agree; [exact C | apply AGO; lia | lia | lia]. }
  assert (UF : forall NS (V : Type) (o bl bc : Z) (ents : list (Z * (Z * V))) a,
            (forall x, In x (umap_blocks NS bl bc ents) -> In x (state_blocks c)) -> 48 <= o -> o + 40 <= 240 ->
            umap_foot NS (st + o) bl bc ents a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros NS V o bl bc ents a Hs Ho Hk Hf.
    destruct (umap_foot_cases NS (st + o) bl bc ents a Hf) as [H0|(b & Hb & Hab)]; [apply HMo; lia |].
    exact (HMb a b (Hs b Hb) Hab). }
  assert (C5 : cell4 ASEGS m' (st + 40) e) by (apply cell4_of_fld; [lia | exact F5]).
  assert (F7 : fld ASEGS m' (st + 44 + 1) 1 0).
  { assert (F6o : fld ASEGS m (st + 44) 2 (st_flags c)) by exact (proj2 W6).
    destruct (fld2_split01 m (st + 44) (st_flags c) ltac:(lia) ltac:(lia) HF F6o) as [_ F7o].
    eapply fld_agree; [lia | cbn; lia | exact F7o |]. intros a Ha. unfold zwin in Ha. cbn in Ha. apply HMo; lia. }
  assert (C6 : cellw ASEGS m' (st + 44) 2 e) by exact (cellw2_of_flds m' (st + 44) e ltac:(lia) ltac:(lia) He F6 F7).
  assert (D5 : HRep.defined m' (st + 40) 4).
  { pose proof (defined_of_rw_cells_hi _ _ _ (rw_cells_of_cellw4 m' (st + 40) e C5 ltac:(lia) ltac:(lia)) ltac:(lia)) as D.
    exact D. }
  assert (D6 : HRep.defined m' (st + 44) 2).
  { pose proof (defined_of_rw_cells_hi _ _ _ (rw_cells_of_cellw2 m' (st + 44) e C6 ltac:(lia) ltac:(lia)) ltac:(lia)) as D.
    exact D. }
  unfold state_blocks in *.
  constructor; cbn [st_e st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
  - replace st with (st + 0) by lia. apply CW; [rewrite Z.add_0_r; exact W0 | lia | cbn; lia | cbn; lia].
  - apply CW; [exact W1 | lia | cbn; lia | cbn; lia].
  - apply CW; [exact W2 | lia | cbn; lia | cbn; lia].
  - apply CW; [exact W3 | lia | cbn; lia | cbn; lia].
  - apply CW; [exact W4 | lia | cbn; lia | cbn; lia].
  - exact C5.
  - exact C6.
  - eapply (umapx_agree ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (nval24_agree ASEGS) ltac:(lia));
      [exact Sm1 | intros a Hf; refine (UF _ _ _ _ _ _ _ _ _ _ Hf); [intros x Hx; rewrite !in_app_iff; tauto | lia | lia] | intros p n Hp Hl; exact Hl].
  - eapply (umapx_agree ASEGS LY_A MI_A 32 (Z * Z * Z)%type (nval32 ASEGS) (nval32_agree ASEGS) ltac:(lia));
      [exact Sm2 | intros a Hf; refine (UF _ _ _ _ _ _ _ _ _ _ Hf); [intros x Hx; rewrite !in_app_iff; tauto | lia | lia] | intros p n Hp Hl; exact Hl].
  - eapply (umapx_agree ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (nval24_agree ASEGS) ltac:(lia));
      [exact Sm3 | intros a Hf; refine (UF _ _ _ _ _ _ _ _ _ _ Hf); [intros x Hx; rewrite !in_app_iff; tauto | lia | lia] | intros p n Hp Hl; exact Hl].
  - destruct Sv1 as [B E C BLK]. constructor; [apply CW; [exact B | lia | cbn; lia | cbn; lia] | replace (st + 168 + 8) with (st + 176) by lia; apply CW; [replace (st + 176) with (st + 168 + 8) by lia; exact E | lia | cbn; lia | cbn; lia]
      | replace (st + 168 + 16) with (st + 184) by lia; apply CW; [replace (st + 184) with (st + 168 + 16) by lia; exact C | lia | cbn; lia | cbn; lia] | exact BLK].
  - destruct Sv2 as [B E C BLK]. constructor; [apply CW; [exact B | lia | cbn; lia | cbn; lia] | replace (st + 192 + 8) with (st + 200) by lia; apply CW; [replace (st + 200) with (st + 192 + 8) by lia; exact E | lia | cbn; lia | cbn; lia]
      | replace (st + 192 + 16) with (st + 208) by lia; apply CW; [replace (st + 208) with (st + 192 + 16) by lia; exact C | lia | cbn; lia | cbn; lia] | exact BLK].
  - destruct Sv3 as [B E C BLK]. constructor; [apply CW; [exact B | lia | cbn; lia | cbn; lia] | replace (st + 216 + 8) with (st + 224) by lia; apply CW; [replace (st + 224) with (st + 216 + 8) by lia; exact E | lia | cbn; lia | cbn; lia]
      | replace (st + 216 + 16) with (st + 232) by lia; apply CW; [replace (st + 232) with (st + 216 + 16) by lia; exact C | lia | cbn; lia | cbn; lia] | exact BLK].
  - intros i Hi.
    destruct (Z_lt_le_dec i 40) as [L1|L1]; [rewrite (HMo (st + i)) by lia; apply Sdef; lia |].
    destruct (Z_lt_le_dec i 44) as [L2|L2]; [replace (st + i) with (st + 40 + (i - 40)) by lia; apply D5; lia |].
    destruct (Z_lt_le_dec i 46) as [L3|L3]; [replace (st + i) with (st + 44 + (i - 44)) by lia; apply D6; lia |].
    rewrite (HMo (st + i)) by lia. apply Sdef. lia.
  - exact Sal.
  - exact Snd.
Qed.

Lemma parser_repA_endian : forall LB m m' p c e,
  parser_repA LB m p c -> AIMG_TOP <= p -> 0 <= pc_cons c -> pc_cons c + 48 < 2 ^ 64 ->
  (st_flags (pc_state c) = 0 \/ st_flags (pc_state c) = 1) -> (e = 0 \/ e = 1) ->
  (forall a, p <= a < p + PARSER_SIZE -> ~ (p + 88 <= a < p + 93) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall a b, In b (state_blocks (pc_state c)) -> fst b <= a < fst b + snd b -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall a, pc_cons c + 32 <= a < pc_cons c + 40 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  fld ASEGS m' (p + 88) 4 e -> fld ASEGS m' (p + 92) 1 e ->
  parser_repA LB m' p (pc_e c e).
Proof.
  intros LB m m' p c e PR Hlo Hc0 Hc1 HF He HMo HMb HC F5 F6.
  pose proof Hlo as Hlo'. unfold AIMG_TOP in Hlo'.
  destruct PR as [Pcons Puser Phdr Pins Phunk Pst Pdef Pal Prange Pconsf Pconsm Pconsd]. unfold PARSER_SIZE in *.
  assert (FP : forall k (w : nat) v, 0 <= k -> k + Z.of_nat w <= 48 -> fld ASEGS m (p + k) w v -> fld ASEGS m' (p + k) w v).
  { intros k w v Hk Hkw F. eapply fld_agree; [lia | lia | exact F |]. intros a Ha. unfold zwin in Ha. apply HMo; lia. }
  constructor; cbn [pc_e pc_cons pc_user pc_state].
  - apply (FP 8 8%nat); [lia | cbn; lia | exact Pcons].
  - apply (FP 16 8%nat); [lia | cbn; lia | exact Puser].
  - apply (FP 24 8%nat); [lia | cbn; lia | exact Phdr].
  - apply (FP 32 8%nat); [lia | cbn; lia | exact Pins].
  - apply (FP 40 1%nat); [lia | cbn; lia | exact Phunk].
  - unfold ST_OFF in *. eapply state_rep_endianA; [exact Pst | unfold AIMG_TOP; lia | lia | exact HF | exact He | | | |].
    + intros a Ha Hn. apply HMo; lia.
    + exact HMb.
    + replace (p + 48 + 40) with (p + 88) by lia. exact F5.
    + replace (p + 48 + 44) with (p + 92) by lia. exact F6.
  - intros i Hi. unfold ST_OFF in Hi. rewrite (HMo (p + i)) by lia. apply Pdef. exact Hi.
  - exact Pal.
  - exact Prange.
  - eapply fld_agree; [lia | cbn; lia | exact Pconsf |]. intros a Ha. unfold zwin in Ha. cbn in Ha. apply HC. lia.
  - intros i Hi. rewrite (HC (pc_cons c + 32 + i)) by lia. apply Pconsm. exact Hi.
  - exact Pconsd.
Qed.

Lemma words_sh0A : forall LB0 m words n, words_okA LB0 m words n -> 2 <= n -> sh0 m words.
Proof.
  intros LB0 m words n (pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh) Hn.
  assert (Hl : Z.of_nat (length (LbB_PrsStmt.cc_gen k (4 * n))) = nsh k).
  { unfold LbB_PrsStmt.cc_gen, poison_bytes. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length by lia.
    assert (nsh (4 * n) <= nsh k) by (unfold nsh; apply Z.div_le_mono; lia). lia. }
  assert (Hx : words <= words + 0 < words + 8 * Z.of_nat (length (LbB_PrsStmt.cc_gen k (4 * n)))).
  { rewrite Hl. unfold nsh. assert (1 <= (k + 7) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
  destruct (shk_of_SHAD m _ _ _ Wsh Hx) as (b & Hb & K).
  rewrite Z.add_0_r in K. replace (words + 0 - words) with 0 in Hb by lia.
  change (Z.to_nat (0 / 8)) with 0%nat in Hb.
  assert (H8 : (0 < Z.to_nat (4 * n / 8))%nat) by (assert (1 <= 4 * n / 8) by (apply Z.div_le_lower_bound; lia); lia).
  rewrite (cc_gen_nth0 k (4 * n) 0%nat ltac:(lia) H8) in Hb.
  injection Hb as <-. exact K.
Qed.

Lemma bytes4_x : forall b0 b1 b2 b3 : byte,
  let x := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3 in
  0 <= x < 2 ^ 32 /\ x mod 256 = bv_unsigned b0 /\ (x / 256) mod 256 = bv_unsigned b1 /\
  (x / 65536) mod 256 = bv_unsigned b2 /\ x / 16777216 = bv_unsigned b3.
Proof.
  intros b0 b1 b2 b3 x.
  pose proof (bv_unsigned_in_range _ b0) as B0. pose proof (bv_unsigned_in_range _ b1) as B1.
  pose proof (bv_unsigned_in_range _ b2) as B2. pose proof (bv_unsigned_in_range _ b3) as B3.
  unfold bv_modulus in B0, B1, B2, B3. change (2 ^ Z.of_N 8) with 256 in B0, B1, B2, B3.
  subst x. repeat split; Z.div_mod_to_equations; lia.
Qed.

Lemma rdn1_keep : forall m m' a (b : byte), m (Z_to_bv 64 a) = Some b -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  PropExec.rdn asegs m' (Z_to_bv 64 a) 1 = Some [b].
Proof. intros m m' a b E1 E2. cbn [PropExec.rdn]. rewrite E2, E1. reflexivity. Qed.

Section Words.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma hdr_words : forall e ff fp XSc sk LBk m,
    wpre H e -> winv H e ff fp XSc sk LBk m -> w_words e <> 0 -> 5 <= w_n e ->
    16 <= w_words e /\ w_words e mod 16 = 0 /\ w_words e + 4 * w_n e <= 2 ^ 47 /\ sh0 m (w_words e)
    /\ exists b0 b1 b2 b3 : byte,
         PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 0)) 1 = Some [b0] /\ PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 1)) 1 = Some [b1]
      /\ PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 2)) 1 = Some [b2] /\ PropExec.rdn asegs m (Z_to_bv 64 (w_words e + 3)) 1 = Some [b3].
  Proof.
    intros e ff fp XSc sk LBk m HP HI HW HN.
    pose proof HP as HP'. destruct HP' as (_ & _ & HN24 & WOK & _).
    destruct WOK as [[E0 _] | WOK]; [contradiction |].
    pose proof WOK as (pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh).
    assert (KEEP : forall a, w_words e <= a < w_words e + k -> m (Z_to_bv 64 a) = w_m e (Z_to_bv 64 a)).
    { intros a Ha. destruct (wkeep H HH e ff fp XSc sk LBk m a HP HI ltac:(lia)) as [K _].
      - left. exists pw, (w_words e), k. split; [exact Hin | left; lia].
      - exact K. }
    assert (BYTE : forall i, 0 <= i < 4 -> exists b : byte, PropExec.rdn asegs m (Z_to_bv 64 (w_words e + i)) 1 = Some [b]).
    { intros i Hi. pose proof (Wdef i ltac:(lia)) as D.
      destruct (w_m e (Z_to_bv 64 (w_words e + i))) as [b|] eqn:EB; [| contradiction].
      exists b. apply (rdn1_keep (w_m e) m); [exact EB | apply KEEP; lia]. }
    destruct (BYTE 0 ltac:(lia)) as (b0 & R0). destruct (BYTE 1 ltac:(lia)) as (b1 & R1).
    destruct (BYTE 2 ltac:(lia)) as (b2 & R2). destruct (BYTE 3 ltac:(lia)) as (b3 & R3).
    assert (SH0 : sh0 (w_m e) (w_words e)) by exact (words_sh0A _ _ _ _ WOK ltac:(lia)).
    assert (SHM : sh0 m (w_words e)).
    { unfold sh0, shk in SH0 |- *. set (x := w_words e / 8 + SHBASE) in *.
      cbn [PropExec.rdn] in SH0 |- *.
      destruct (wkeep H HH e ff fp XSc sk LBk m x HP HI) as [K _].
      - subst x. unfold SHBASE. pose proof (Z.div_pos (w_words e) 8 ltac:(lia) ltac:(lia)).
        assert (w_words e / 8 <= w_words e) by (apply Z.div_le_upper_bound; lia). lia.
      - left. exists pw, (w_words e), k. split; [exact Hin | right]. subst x. unfold sh, nsh, SHBASE. rewrite ASHADOW_BASE_val. split; [lia |].
        assert (1 <= (k + 7) / 8) by (apply Z.div_le_lower_bound; lia). lia.
      - unfold wa in K. rewrite K. exact SH0. }
    split; [clear - W0 W16; Z.div_mod_to_equations; lia |]. split; [exact W16 |]. split; [lia |]. split; [exact SHM |].
    exists b0, b1, b2, b3. auto.
  Qed.
End Words.

Section Glue.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma hdr_a2_sr : forall s msF mo R F fc m q sp words n fp (Q : config -> Prop),
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (wz (0xea7c4 + 3384)) fc None m (seg_rom asegs) -> rfull R ->
    hdrR_a2_pre R m q sp words n fp ->
    (forall msF1 mo1 R' M', as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
       as_VIS H s msF1 = MS R' F (wz (0xea7c4 + 4784)) fc None M' (seg_rom asegs) -> rfull R' ->
       hdrR_a2_post 0xea7c4 R F fc m q sp words n fp R' M' -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros s msF mo R F fc m q sp words n fp Q KR VIS RF P K.
    destruct (hdrR_a2_bp R F fc m q sp words n fp P) as (R' & M' & PST).
    pose proof PST as PST'. unfold hdrR_a2_post in PST'. destruct PST' as [MS _].
    eapply (sr_msteps H HH s msF mo R F _ fc m R' _ M' Q KR VIS RF MS).
    intros msF1 mo1 KR1 MP1 VIS1 RF1. exact (K msF1 mo1 R' M' KR1 MP1 VIS1 RF1 PST).
  Qed.

  Lemma hdr_mgL_sr : forall s msF mo R F fc m q sp words n x (Q : config -> Prop),
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (wz (0xea7c4 + 4784)) fc None m (seg_rom asegs) -> rfull R ->
    hdrR_mg_pre R m q sp words n x ->
    x mod 256 = 3 -> (x / 256) mod 256 = 2 -> (x / 65536) mod 256 = 35 -> x / 16777216 = 7 ->
    (forall msF1 mo1 R' M', as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
       as_VIS H s msF1 = MS R' F (wz (0xea7c4 + 5632)) fc None M' (seg_rom asegs) -> rfull R' ->
       hdrR_mgL_post 0xea7c4 R F fc m q sp words n x R' M' -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros s msF mo R F fc m q sp words n x Q KR VIS RF P B0 B1 B2 B3 K.
    destruct (hdrR_mgL_bp R F fc m q sp words n x P B0 B1 B2 B3) as (R' & M' & PST).
    pose proof PST as PST'. unfold hdrR_mgL_post in PST'. destruct PST' as [MS _].
    eapply (sr_msteps H HH s msF mo R F _ fc m R' _ M' Q KR VIS RF MS).
    intros msF1 mo1 KR1 MP1 VIS1 RF1. exact (K msF1 mo1 R' M' KR1 MP1 VIS1 RF1 PST).
  Qed.

  Lemma hdr_mgB_sr : forall s msF mo R F fc m q sp words n x (Q : config -> Prop),
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (wz (0xea7c4 + 4784)) fc None m (seg_rom asegs) -> rfull R ->
    hdrR_mg_pre R m q sp words n x ->
    x mod 256 = 7 -> (x / 256) mod 256 = 35 -> (x / 65536) mod 256 = 2 -> x / 16777216 = 3 ->
    (forall msF1 mo1 R' M', as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
       as_VIS H s msF1 = MS R' F (wz (0xea7c4 + 5632)) fc None M' (seg_rom asegs) -> rfull R' ->
       hdrR_mgB_post 0xea7c4 R F fc m q sp words n x R' M' -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros s msF mo R F fc m q sp words n x Q KR VIS RF P B0 B1 B2 B3 K.
    destruct (hdrR_mgB_bp R F fc m q sp words n x P B0 B1 B2 B3) as (R' & M' & PST).
    pose proof PST as PST'. unfold hdrR_mgB_post in PST'. destruct PST' as [MS _].
    eapply (sr_msteps H HH s msF mo R F _ fc m R' _ M' Q KR VIS RF MS).
    intros msF1 mo1 KR1 MP1 VIS1 RF1. exact (K msF1 mo1 R' M' KR1 MP1 VIS1 RF1 PST).
  Qed.
End Glue.
