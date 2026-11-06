(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA L5OpmodSpecsA L5DivSpecsA L5UnwindSpecsA L5AUnwK.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AUK2.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5AUK.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Lemma defined_bytes M : forall (n : nat) (a : Z), L5.defined M a (Z.of_nat n) ->
  exists bs : list byte, length bs = n /\ forall i, (i < n)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros a D. exists []. split. reflexivity. intros i Hi. lia.
  destruct (IH (a + 1)) as (bs & Lb & Hb). { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply D. lia. }
  pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0. destruct (M (Z_to_bv 64 a)) as [b|] eqn:E. 2: contradiction.
  exists (b :: bs). split. cbn; lia. intros i Hi. destruct i as [|i]. cbn [nth_error]. rewrite Z.add_0_r. exact E.
  cbn [nth_error]. replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply Hb. lia.
Qed.
(* [comment removed for export] *)
Lemma apart_of_pointwise a n b m : 0 < n -> 0 < m -> (forall x, a <= x < a + n -> ~ (b <= x < b + m)) -> a + n <= b \/ b + m <= a.
Proof. intros Hn Hm H. destruct (Z_lt_le_dec a b) as [X|X]. destruct (Z_le_gt_dec (a + n) b) as [Y|Y]. left; exact Y. exfalso. apply (H b); lia. destruct (Z_le_gt_dec (b + m) a) as [Y|Y]. right; exact Y. exfalso. apply (H a); lia. Qed.
Lemma u32_of_zeros M a : L5KA.zeros_at M a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M a 0.
Proof.
  intros Z0 Ha Hn. unfold L5.u32_at. change (word_to_le_bytes 4 (Z_to_bv 64 0)) with [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
  apply (rdn_overlay_list M [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] a Ha). cbn [length]. lia.
  intros i Hi. cbn [length] in Hi. rewrite (Z0 (Z.of_nat i)) by lia. do 4 (destruct i as [|i]; [reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_img M lo hi : L5.img_clear M lo hi -> forall (k : nat) a, lo <= a -> a + Z.of_nat k <= hi -> 0 <= a -> hi <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) k = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) k.
Proof.
  intros IC. induction k as [|k IH]; intros a H1 H2 H3 H4. reflexivity.
  cbn [rdn]. rewrite (IC a) by lia. rewrite (L5C.add1_lit a). rewrite (IH (a + 1)) by lia. reflexivity.
Qed.
Lemma rdn_head M a (k : nat) b rest : rdn RSEGS M a (Datatypes.S k) = Some (b :: rest) -> rdn RSEGS M a 1 = Some [b].
Proof.
  cbn [rdn]. destruct (match M a with Some b0 => Some b0 | None => seg_rom RSEGS a end) as [b0|]; [|discriminate].
  destruct (rdn RSEGS M (a + 1) k) as [r|]; [|discriminate]. intros E. injection E as -> _. reflexivity.
Qed.
Lemma addn_lit a (n : nat) : (Z_to_bv 64 a + BvBase.nat_to_word n)%bv = Z_to_bv 64 (a + Z.of_nat n).
Proof.
  apply bv_eq. unfold BvBase.nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite <- Z.add_mod by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rdn_snoc0 M a (bs : list byte) : rdn RSEGS M (Z_to_bv 64 a) (length bs) = Some bs -> L5.u8_at RSEGS M (a + Z.of_nat (length bs)) 0 ->
  rdn RSEGS M (Z_to_bv 64 a) (length bs + 1) = Some (bs ++ [Z_to_bv 8 0]).
Proof. intros RB NUL. apply (SeqExec.rdn_app RSEGS M (length bs) 1 (Z_to_bv 64 a) bs [Z_to_bv 8 0] RB). rewrite addn_lit. exact NUL. Qed.
(* [comment removed for export] *)
Lemma rdn_ext M a (known : list byte) (m : nat) :
  rdn RSEGS M (Z_to_bv 64 a) (length known) = Some known -> L5.defined M (a + Z.of_nat (length known)) (Z.of_nat m) ->
  0 <= a -> a + Z.of_nat (length known) + Z.of_nat m <= 2 ^ 64 ->
  exists rest : list byte, length rest = m /\ rdn RSEGS M (Z_to_bv 64 a) (length known + m) = Some (known ++ rest).
Proof.
  intros RK D Ha Hn. destruct (defined_bytes M m (a + Z.of_nat (length known)) D) as (rest & Lr & Hr). exists rest. split. exact Lr.
  apply (SeqExec.rdn_app RSEGS M (length known) m (Z_to_bv 64 a) known rest RK).
  replace (Z_to_bv 64 a + BvBase.nat_to_word (length known))%bv with (Z_to_bv 64 (a + Z.of_nat (length known))).
  2:{ apply bv_eq. unfold BvBase.nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite <- Z.add_mod by lia. reflexivity. }
  rewrite <- Lr. apply rdn_overlay_list. lia. rewrite Lr. lia. intros i Hi. apply Hr. rewrite <- Lr. exact Hi.
Qed.

Lemma rdn_firstn M : forall (k n : nat) a bs, rdn RSEGS M a n = Some bs -> (k <= n)%nat -> rdn RSEGS M a k = Some (firstn k bs).
Proof.
  induction k as [|k IH]; intros n a bs H Hk. reflexivity.
  destruct n as [|n]. lia. cbn [rdn] in H |- *.
  destruct (match M a with Some b0 => Some b0 | None => seg_rom RSEGS a end) as [b0|]; [|discriminate].
  destruct (rdn RSEGS M (a + 1) n) as [r|] eqn:E; [|discriminate]. injection H as <-. cbn [firstn]. rewrite (IH n (a + 1)%bv r E) by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rdn_of_copied M dst (bs : list byte) :
  (forall i, 0 <= i < Z.of_nat (length bs) -> exists v, (nth_error bs (Z.to_nat i) = Some (Z_to_bv 8 v) /\ 0 <= v < 256) /\ byte_at M (dst + i) v) ->
  0 <= dst -> dst + Z.of_nat (length bs) <= 2 ^ 64 -> rdn RSEGS M (Z_to_bv 64 dst) (length bs) = Some bs.
Proof.
  intros HB Hd Hn. apply rdn_overlay_list. exact Hd. exact Hn. intros i Hi.
  destruct (HB (Z.of_nat i) ltac:(lia)) as (v & (E & _) & B). rewrite Nat2Z.id in E. rewrite E. exact B.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod16_sub x k : x mod 16 = 0 -> k mod 16 = 0 -> (x - k) mod 16 = 0. Proof. intros; lia. Qed.
Lemma mod16_add x k : x mod 16 = 0 -> k mod 16 = 0 -> (x + k) mod 16 = 0. Proof. intros; lia. Qed.
Lemma mod8_of_16 x : x mod 16 = 0 -> x mod 8 = 0. Proof. intros; lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis UNWL : L5USA.as0_unw_layout L.

Section CHAIN.
Variables (M0 : word -> option byte) (model0 : Model) (A0 : list (Z * Z)) (LB : list (Z * Z)) (FF : list fframe) (Sp Scr : Z) (W : list L5.range).
Local Abbreviation cinv := (L5AUK.cinv L ar HI M0 model0 A0 LB FF Sp Scr W).
Local Abbreviation cinv_num := (L5AUK.cinv_num L ar HI M0 model0 A0 LB FF Sp Scr W).
Local Abbreviation cinv_top := (L5AUK.cinv_top L ar C HI HIok M0 model0 A0 LB FF Sp Scr W).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ccl (XB : list (Z * Z)) (sp' a k : Z) : Prop :=
  (sp' <= a /\ a + k <= 2 ^ 47)
  \/ (0x10000 <= a /\ a + k <= 0xd7000)
  \/ (exists r, In r (L5USA.UNW_STATICS ++ L5USA.UNW_CONSTS) /\ fst r <= a /\ a + k <= fst r + snd r)
  \/ (exists q n, In (q, n) XB /\ q <= a /\ a + k <= q + n).

Lemma unw_client LBx FFx spx scrx r i : In r (L5USA.UNW_STATICS ++ L5USA.UNW_CONSTS) -> fst r <= i < fst r + snd r -> aclient L ar LBx FFx spx scrx i.
Proof.
  intros Hr Hi. right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). apply in_app_or in Hr. destruct Hr as [Hr|Hr].
  - split. { pose proof L5USA.unw_statics_img as F. rewrite Forall_forall in F. specialize (F r Hr). clear - F Hi. lia. }
    exact (proj1 (proj1 UNWL r i Hr Hi)).
  - split. { unfold L5USA.UNW_CONSTS in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hi; clear - Hi; lia. }
    exact (proj1 (proj2 UNWL) r i Hr Hi).
Qed.
Lemma ccl_client XB sp' scr a k i : ahl_ceil ar <= sp' - scr -> 0 <= scr -> ccl XB sp' a k -> a <= i < a + k -> aclient L ar (XB ++ LB) FF sp' scr i.
Proof.
  intros HC HS [X|[X|[(r & Hr & X1 & X2)|(q & n & Hin & X1 & X2)]]] Hi.
  - apply stack_client. clear - HC HS X Hi; lia. clear - HS X Hi; lia.
  - apply (img_client L ar C LY (as0_layout2_of L C LY)). clear - X Hi; lia.
  - apply (unw_client _ _ _ _ r i Hr). clear - X1 X2 Hi; lia.
  - apply (block_client L ar (XB ++ LB) FF sp' scr q n i). apply in_or_app. left. exact Hin. clear - X1 X2 Hi; lia.
Qed.

(* [comment removed for export] *)
Lemma ag_of_pres XB sp' scr (D : Z -> Prop) Mc M' :
  ahl_ceil ar <= sp' - scr -> 0 <= scr ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (XB ++ LB) FF sp' scr a -> ~ D a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  forall a k, 0 <= a -> a + k <= 2 ^ 64 -> ccl XB sp' a k -> (forall i, a <= i < a + k -> ~ D i) -> L5C.agree_on Mc M' a k.
Proof. intros HC HS PRES a k Ha Hk CL ND i Hi. apply PRES. clear - Ha Hk Hi; lia. exact (ccl_client XB sp' scr a k i HC HS CL Hi). exact (ND i Hi). Qed.

(* [comment removed for export] *)
Lemma cinv_after_call XB XB' Mc modelc LKc crc Ac M' model' cr' A' sp' scr (D : Z -> Prop) :
  cinv XB Mc modelc LKc crc Ac -> 0 <= Scr -> 0 <= scr -> Sp - Scr <= sp' - scr -> sp' <= Sp ->
  ri_inv HI (XB' ++ LB) FF LKc cr' A' M' (vml_of model') -> amodel_ok A' model' -> model_rt modelc model' -> incl Ac A' ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (XB ++ LB) FF sp' scr a -> ~ D a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  (forall a, sp' - scr <= a < sp' -> M' (Z_to_bv 64 a) <> None) ->
  (forall a, D a -> M' (Z_to_bv 64 a) <> None) -> (forall a, D a \/ ~ D a) ->
  (forall a, D a -> (Sp - Scr <= a < Sp) \/ in_block XB a) ->
  cinv XB' M' model' LKc cr' A'.
Proof.
  intros CI HS0 Hscr HLO HHI HH' AM' RT' IA' PRES SDEF DDEF DDEC DIN. pose proof CI as (HH & AM & RT & IA & STK & SH & EK & DK).
  pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT). pose proof (cinv_top _ _ _ _ _ _ CI) as TOP47.
  unfold L5AUK.cinv. split. exact HH'. split. exact AM'. split. eapply L5LZ.model_rt_trans. exact RT. exact RT'.
  split. { intros x Hx. apply IA'. apply IA. exact Hx. }
  split. { destruct STK as (_ & _ & _ & _ & DSCR & DUP).
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
    assert (DD : forall x, (Sp - Scr <= x < Sp \/ Sp <= x < ar_stack_top ar) -> M' (Z_to_bv 64 x) <> None).
    { intros x Hx. destruct (rng_dec x (sp' - scr) sp') as [I|O]. apply SDEF; exact I. destruct (DDEC x) as [Dx|Dx]. apply DDEF; exact Dx.
      rewrite PRES. destruct (Z_lt_le_dec x Sp).
      + replace x with (Sp - Scr + (x - (Sp - Scr))) by lia. apply DSCR. lia.
      + replace x with (Sp + (x - Sp)) by lia. apply DUP. lia.
      + clear - Hx SLO SHI SPT HS0 TOP. destruct Hx; lia. + apply stack_client. clear - Hx SLO SHI SPT HS0 TOP. destruct Hx; lia. exact O. + exact Dx. }
    split. exact A16. split. exact SLO. split. exact SHI. split. exact SPT. split.
    - intros j Hj. apply DD. lia.
    - intros j Hj. apply DD. lia. }
  split. { intros j Hj. unfold byte_at. rewrite PRES. apply SH. exact Hj.
           pose proof (stksh_range ar (Sp - Scr) j ltac:(clear - SLO SPT; lia) Hj ltac:(clear - SPT; lia) TOP47) as RG. clear - RG; lia.
           apply stksh_client. clear - SLO HS0; lia. exact Hj. clear - SPT; lia. exact TOP47.
           intros Dx. pose proof (stksh_range ar (Sp - Scr) j ltac:(clear - SLO SPT; lia) Hj ltac:(clear - SPT; lia) TOP47) as RG.
           destruct (DIN _ Dx) as [X|X]. clear - X RG SLO SPT; lia.
           destruct X as (b & Hb & X). destruct b as [q n]. cbn [fst snd] in X.
           pose proof (blk_facts L ar C HI LY HIok _ _ _ _ _ _ _ q n HH ltac:(apply in_or_app; left; exact Hb)) as (BR & _). clear - BR X RG; lia. }
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF Sp Scr a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hc. apply PRES. exact Ha. apply aclient_appb. eapply aclient_mono. exact Hc. intros x Hx. clear - Hx HLO HHI Hscr; lia.
    intros Da. destruct (DIN a Da) as [X|X].
    - destruct (aclient_cases L ar C HI LY HIok (XB ++ LB) FF LKc crc Ac Mc _ Sp Scr a HH SPT (aclient_appb L ar LB XB FF Sp Scr a Hc)) as [Y|Y]. clear - X Y; lia. clear - X Y SLO; lia.
    - destruct X as (b & Hb & X). destruct b as [q n]. cbn [fst snd] in X. exact (xblock_not_client L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac q n a Sp Scr CI Hb X Hc). }
  split. { eapply ek_trans. exact EK. intros a (Ha & Hc & _). apply KEEP. exact Ha. exact Hc. }
  eapply dk_trans. exact DK. intros a Ha Hc HM. rewrite KEEP. exact HM. exact Ha. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cinv_aligned XB Mc modelc LKc crc Ac (fx : FPState) R n sp' r K :
  cinv XB Mc modelc LKc crc Ac -> K [] -> 0 <= Scr ->
  getr R (reg 10) = Z_to_bv 64 16 -> getr R (reg 11) = Z_to_bv 64 n -> 0 < n <= 4096 -> n mod 16 = 0 -> acredit_ok L crc n ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  sp' mod 16 = 0 -> Sp - Scr <= sp' - 4096 -> sp' <= Sp ->
  (forall (fx' : FPState) R' M' model' A' u,
      getr R' (reg 10) = Z_to_bv 64 u -> regs_preserved R R' ->
      cinv ((u, n) :: XB) M' model' LKc (adebit L crc n) A' ->
      (forall a k, 0 <= a -> a + k <= 2 ^ 64 -> ccl XB sp' a k -> L5C.agree_on Mc M' a k) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R 0x5fc60 Mc modelc) K.
Proof.
  intros CI HK HS0 G10 G11 Hn Hn16 CR G1 RA G2 G4 A16' HLO HHI KONT. pose proof CI as (HH & AM & RT & IA & STK & SH & EK & DK).
  pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT).
  pose proof (aio_aligned _ _ _ _ _ HIok) as HF. unfold aaligned16_spec in HF. rewrite (aly_segs L C LY), (aly_aligned L C LY), (aly_scr_aligned L C LY) in HF.
  assert (U2 : bv_unsigned (getr R 2%bv) = sp'). { rewrite r2, G2. apply L5.unsigned_lit. clear - SLO SHI SPT HLO HHI HS0; lia. }
  unfold cfg.
  eapply (HF fx R Mc modelc (XB ++ LB) FF LKc crc Ac n K HH (proj1 AM) (proj2 AM)); clear HF.
  - rewrite r10. exact G10.
  - rewrite r11. exact G11.
  - exact Hn.
  - exact Hn16.
  - exact CR.
  - rewrite r4. exact G4.
  - rewrite r1, G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (destruct RA as [X _]; clear - X; lia). exact (proj2 RA).
  - rewrite U2. pose proof (astack_ok_of_astk L ar C LY Mc Mc Sp Scr (Sp - sp') 4096 STK (mem_grows_refl Mc)) as X.
    replace (Sp - (Sp - sp')) with sp' in X by (clear; lia). apply X. clear - HHI; lia. clear; lia. clear - HLO; lia. exact A16'.
  - exact HK.
  - intros R' M' model' A' u mR10 RP BR BA FA DEF SHB PRES RT2 IA2 MI2 HH2. rewrite U2 in PRES. rewrite r1, G1.
    assert (HC : ahl_ceil ar <= sp' - 4096) by (clear - SLO HLO HS0; lia).
    apply (KONT fx R' M' model' A' u). rewrite <- r10. exact mR10. exact RP.
    + apply (cinv_after_call XB ((u, n) :: XB) Mc modelc LKc crc Ac M' model' (adebit L crc n) A' sp' 4096 (fun _ => False) CI HS0 ltac:(clear; lia) HLO HHI).
      * exact HH2.
      * split. rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM). exact MI2.
      * exact RT2. * exact IA2.
      * intros a Ha Hc _. apply (proj1 PRES). exact Ha. exact Hc.
      * exact (proj2 PRES).
      * intros a []. * intros a. right. intros [].
      * intros a [].
    + intros a k Ha Hk CL. apply (ag_of_pres XB sp' 4096 (fun _ => False) Mc M' HC ltac:(clear; lia)). intros x Hx Hc _. apply (proj1 PRES). exact Hx. exact Hc.
      exact Ha. exact Hk. exact CL. intros i _ [].
Qed.

Lemma cinv_malloc XB Mc modelc LKc crc Ac (fx : FPState) R n sp' r K :
  cinv XB Mc modelc LKc crc Ac -> K [] -> 0 <= Scr ->
  getr R (reg 10) = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 -> acredit_ok L crc n ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  sp' mod 16 = 0 -> Sp - Scr <= sp' - 4096 -> sp' <= Sp ->
  (forall (fx' : FPState) R' M' model' A' u,
      getr R' (reg 10) = Z_to_bv 64 u -> regs_preserved R R' ->
      cinv ((u, n) :: XB) M' model' LKc (adebit L crc n) A' ->
      (forall a k, 0 <= a -> a + k <= 2 ^ 64 -> ccl XB sp' a k -> L5C.agree_on Mc M' a k) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R 0x5fc58 Mc modelc) K.
Proof.
  intros CI HK HS0 G10 Hn CR G1 RA G2 G4 A16' HLO HHI KONT. pose proof CI as (HH & AM & RT & IA & STK & SH & EK & DK).
  pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT).
  pose proof (aio_malloc _ _ _ _ _ HIok) as HF. unfold amalloc_spec, amalloc_post in HF. rewrite (aly_segs L C LY), (aly_malloc L C LY), (aly_scr_malloc L C LY) in HF.
  assert (U2 : bv_unsigned (getr R 2%bv) = sp'). { rewrite r2, G2. apply L5.unsigned_lit. clear - SLO SHI SPT HLO HHI HS0; lia. }
  unfold cfg.
  eapply (HF fx R Mc modelc (XB ++ LB) FF LKc crc Ac n K HH (proj1 AM) (proj2 AM)); clear HF.
  - rewrite r10. exact G10.
  - exact Hn.
  - exact CR.
  - rewrite r4. exact G4.
  - rewrite r1, G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (destruct RA as [X _]; clear - X; lia). exact (proj2 RA).
  - rewrite U2. pose proof (astack_ok_of_astk L ar C LY Mc Mc Sp Scr (Sp - sp') 4096 STK (mem_grows_refl Mc)) as X.
    replace (Sp - (Sp - sp')) with sp' in X by (clear; lia). apply X. clear - HHI; lia. clear; lia. clear - HLO; lia. exact A16'.
  - exact HK.
  - intros R' M' model' A' u mR10 RP BR BA FA DEF SHB PRES RT2 IA2 MI2 HH2. rewrite U2 in PRES. rewrite r1, G1.
    assert (HC : ahl_ceil ar <= sp' - 4096) by (clear - SLO HLO HS0; lia).
    apply (KONT fx R' M' model' A' u). rewrite <- r10. exact mR10. exact RP.
    + apply (cinv_after_call XB ((u, n) :: XB) Mc modelc LKc crc Ac M' model' (adebit L crc n) A' sp' 4096 (fun _ => False) CI HS0 ltac:(clear; lia) HLO HHI).
      * exact HH2.
      * split. rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM). exact MI2.
      * exact RT2. * exact IA2.
      * intros a Ha Hc _. apply (proj1 PRES). exact Ha. exact Hc.
      * exact (proj2 PRES).
      * intros a []. * intros a. right. intros [].
      * intros a [].
    + intros a k Ha Hk CL. apply (ag_of_pres XB sp' 4096 (fun _ => False) Mc M' HC ltac:(clear; lia)). intros x Hx Hc _. apply (proj1 PRES). exact Hx. exact Hc.
      exact Ha. exact Hk. exact CL. intros i _ [].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cinv_strlen XB Mc modelc LKc crc Ac (fx : FPState) R s Kn (buf : list byte) sp' r K :
  cinv XB Mc modelc LKc crc Ac -> K [] -> 0 <= Scr ->
  getr R (reg 10) = Z_to_bv 64 s ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  sp' mod 16 = 0 -> Sp - Scr <= sp' - 2304 -> sp' <= Sp ->
  0 <= s -> s + Z.of_nat (length buf) <= 2 ^ 47 -> 0 <= Kn < 2 ^ 27 ->
  rdn RSEGS Mc (Z_to_bv 64 s) (length buf) = Some buf ->
  (s + Kn) / 8 * 8 + 8 <= s + Z.of_nat (length buf) ->
  nth (Z.to_nat Kn) buf (Z_to_bv 8 0) = Z_to_bv 8 0 ->
  (forall j, (j < Z.to_nat Kn)%nat -> nth j buf (Z_to_bv 8 0) <> Z_to_bv 8 0) ->
  ccl XB sp' s (Z.of_nat (length buf)) ->
  L5.img_clear Mc 0x10000 0xd7000 ->
  aacc Mc s (Kn + 1) -> app_rng ar s (Kn + 1) ->
  (forall (fx' : FPState) R' M' model',
      getr R' (reg 10) = Z_to_bv 64 Kn -> regs_preserved R R' ->
      cinv XB M' model' LKc crc Ac ->
      (forall a k, 0 <= a -> a + k <= 2 ^ 64 -> ccl XB sp' a k -> L5C.agree_on Mc M' a k) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R 0x4dbb0 Mc modelc) K.
Proof.
  intros CI HK HS0 G10 G1 RA G2 G4 A16' HLO HHI Hs Hlen HKn RDN OVR NUL NZ CL IMG ACC APR KONT. pose proof CI as (HH & AM & RT & IA & STK & SH & EK & DK).
  pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT).
  pose proof (aic_strlen _ _ _ _ _ ICok) as HF. unfold astrlen_spec in HF. cbv zeta in HF.
  rewrite (aly_segs L C LY), (aicl_strlen IL ILY), (aicl_scr_strlen IL ILY), (aicl_ro_lo IL ILY), (aicl_ro_hi IL ILY) in HF.
  assert (U2 : bv_unsigned (getr R 2%bv) = sp'). { rewrite r2, G2. apply L5.unsigned_lit. clear - SLO SHI SPT HLO HHI HS0; lia. }
  assert (HC : ahl_ceil ar <= sp' - 2304) by (clear - SLO HLO HS0; lia).
  unfold cfg.
  eapply (HF fx R Mc modelc (XB ++ LB) FF LKc crc Ac s Kn buf K HH (proj1 AM) (proj2 AM)); clear HF.
  - rewrite r10. exact G10.
  - rewrite r4. exact G4.
  - rewrite r1, G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (destruct RA as [X _]; clear - X; lia). exact (proj2 RA).
  - rewrite U2. pose proof (astack_ok_of_astk L ar C LY Mc Mc Sp Scr (Sp - sp') 2304 STK (mem_grows_refl Mc)) as X.
    replace (Sp - (Sp - sp')) with sp' in X by (clear; lia). apply X. clear - HHI; lia. clear; lia. clear - HLO; lia. exact A16'.
  - exact Hs. - exact Hlen. - exact HKn. - exact RDN. - exact OVR. - exact NUL. - exact NZ.
  - intros i Hi. right. rewrite U2. apply (ccl_client XB sp' 2304 s (Z.of_nat (length buf)) (s + i) HC ltac:(clear; lia) CL). clear - Hi; lia.
  - intros a Ha. apply IMG. clear - Ha; lia.
  - exact ACC.
  - exact APR.
  - exact HK.
  - intros R' M' model' mR10 RP PRES SDEF GROW RT2 MI2 HH2. rewrite U2 in PRES, SDEF. rewrite r1, G1.
    apply (KONT fx R' M' model'). rewrite <- r10. exact mR10. exact RP.
    + apply (cinv_after_call XB XB Mc modelc LKc crc Ac M' model' crc Ac sp' 2304 (fun _ => False) CI HS0 ltac:(clear; lia) HLO HHI).
      * exact HH2.
      * split. rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM). exact MI2.
      * exact RT2. * apply incl_refl.
      * intros a Ha Hc _. apply PRES. exact Ha. exact Hc.
      * exact SDEF.
      * intros a []. * intros a. right. intros [].
      * intros a [].
    + intros a k Ha Hk CL'. apply (ag_of_pres XB sp' 2304 (fun _ => False) Mc M' HC ltac:(clear; lia)). intros x Hx Hc _. apply PRES. exact Hx. exact Hc.
      exact Ha. exact Hk. exact CL'. intros i _ [].
Qed.

(* [comment removed for export] *)
Lemma cinv_memcpy_at (pc : Z) (ov : bool) XB Mc modelc LKc crc Ac (fx : FPState) R dst src n (bs : list byte) sp' r K :
  amemcpy_spec_at L ar SCFG HI pc ov ->
  cinv XB Mc modelc LKc crc Ac -> K [] -> 0 <= Scr ->
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 src -> getr R (reg 12) = Z_to_bv 64 n -> 0 <= n <= 2 ^ 27 ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  sp' mod 16 = 0 -> Sp - Scr <= sp' - 2560 -> sp' <= Sp ->
  ((sp' <= dst /\ dst + n <= Sp) \/ (exists q m, In (q, m) XB /\ q <= dst /\ dst + n <= q + m)) ->
  aacc Mc dst n -> app_rng ar dst n ->
  aacc Mc src n -> 0 <= src /\ src + n <= 2 ^ 47 -> app_rng ar src n -> ccl XB sp' src n ->        (* [comment removed for export] *)
  rdn RSEGS Mc (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
  (ov = false -> dst + n <= src \/ src + n <= dst) ->
  (forall (fx' : FPState) R' M' model',
      getr R' (reg 10) = Z_to_bv 64 dst -> regs_preserved R R' ->
      cinv XB M' model' LKc crc Ac ->
      (forall i, 0 <= i < n -> exists v, (nth_error bs (Z.to_nat i) = Some (Z_to_bv 8 v) /\ 0 <= v < 256) /\ byte_at M' (dst + i) v) ->
      (forall a k, 0 <= a -> a + k <= 2 ^ 64 -> ccl XB sp' a k -> (a + k <= dst \/ dst + n <= a) -> L5C.agree_on Mc M' a k) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R pc Mc modelc) K.
Proof.
  intros HF CI HK HS0 G10 G11 G12 Hn G1 RA G2 G4 A16' HLO HHI DST ACD APD ACS SRG APS SCLS RDN NOV KONT. pose proof CI as (HH & AM & RT & IA & STK & SH & EK & DK).
  pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT).
  unfold amemcpy_spec_at, amem_pre, amem_post in HF. rewrite (aly_segs L C LY), (aly_scr_mem L C LY) in HF.
  assert (U2 : bv_unsigned (getr R 2%bv) = sp'). { rewrite r2, G2. apply L5.unsigned_lit. clear - SLO SHI SPT HLO HHI HS0; lia. }
  assert (HC : ahl_ceil ar <= sp' - 2560) by (clear - SLO HLO HS0; lia).
  assert (DCL : ccl XB sp' dst n).
  { destruct DST as [X|(q & m & Hin & X1 & X2)]. left. clear - X SHI SPT; lia. right; right; right. exists q, m. split. exact Hin. split. exact X1. exact X2. }
  assert (DDEF : L5.defined Mc dst n).
  { destruct DST as [X|(q & m & Hin & X1 & X2)].
    - apply (astk_defined ar Mc Sp Scr dst n STK). clear - X HLO; lia. clear - X; lia.
    - pose proof (blk_facts L ar C HI LY HIok _ _ _ _ _ _ _ q m HH ltac:(apply in_or_app; left; exact Hin)) as (_ & DEF & _).
      eapply L5.defined_sub. exact DEF. exact X1. exact X2. }
  assert (DRG : 0 <= dst /\ dst + n <= 2 ^ 64).
  { destruct DST as [X|(q & m & Hin & X1 & X2)]. clear - X SLO SHI SPT HLO HS0; lia.
    pose proof (blk_facts L ar C HI LY HIok _ _ _ _ _ _ _ q m HH ltac:(apply in_or_app; left; exact Hin)) as (BR & _). clear - BR X1 X2; lia. }
  unfold cfg.
  eapply (HF fx R Mc modelc (XB ++ LB) FF LKc crc Ac dst src n bs K); clear HF.
  - split. exact HH. split. exact (proj1 AM). split. exact (proj2 AM).
    split. rewrite r10. exact G10. split. rewrite r12. exact G12. split. exact Hn.
    split. rewrite r4. exact G4.
    split. rewrite r1, G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (destruct RA as [X _]; clear - X; lia). exact (proj2 RA).
    split. { rewrite U2. pose proof (astack_ok_of_astk L ar C LY Mc Mc Sp Scr (Sp - sp') 2560 STK (mem_grows_refl Mc)) as X.
             replace (Sp - (Sp - sp')) with sp' in X by (clear; lia). apply X. clear - HHI; lia. clear; lia. clear - HLO; lia. exact A16'. }
    split. exact ACD.
    split. { intros i Hi. rewrite U2. destruct DST as [X|(q & m & Hin & X1 & X2)].              (* [comment removed for export] *)
             - apply stack_client. clear - X Hi HC SHI SPT; lia. clear - X Hi; lia.
             - apply (block_client L ar (XB ++ LB) FF sp' 2560 q m). apply in_or_app. left. exact Hin. clear - X1 X2 Hi; lia. }
    split. { intros i m0 Hi Hm. apply (L5C.writable_of_defined RSEGS Mc dst n DDEF (proj1 DRG) (proj2 DRG)). exact Hi. exact Hm. }
    split. exact HK. exact APD.
  - rewrite r11. exact G11.
  - exact ACS.
  - exact SRG.
  - exact APS.
  - intros i Hi. right. rewrite U2. apply (ccl_client XB sp' 2560 src n (src + i) HC ltac:(clear; lia) SCLS). clear - Hi; lia.
  - exact RDN.
  - exact NOV.
  - intros R' M' model' mR10 RP BYTES PRES SDEF RT2 MI2 HH2. rewrite U2 in PRES, SDEF. rewrite r1, G1.
    apply (KONT fx R' M' model'). rewrite <- r10. exact mR10. exact RP.
    + apply (cinv_after_call XB XB Mc modelc LKc crc Ac M' model' crc Ac sp' 2560 (fun a => dst <= a < dst + n) CI HS0 ltac:(clear; lia) HLO HHI).
      * exact HH2.
      * split. rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM). exact MI2.
      * exact RT2. * apply incl_refl.
      * exact PRES.
      * exact SDEF.
      * intros a Da. destruct (BYTES (a - dst) ltac:(clear - Da; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (dst + (a - dst)) with a in Bv by (clear; lia). rewrite Bv. discriminate.
      * intros a. destruct (rng_dec a dst (dst + n)); [left|right]; assumption.
      * intros a Da. destruct DST as [X|(q & m & Hin & X1 & X2)]. left. clear - X Da HLO; lia. right. exists (q, m). split. exact Hin. cbn [fst snd]. clear - X1 X2 Da; lia.
    + exact BYTES.
    + intros a k Ha Hk CL' AV. apply (ag_of_pres XB sp' 2560 (fun x => dst <= x < dst + n) Mc M' HC ltac:(clear; lia) PRES a k Ha Hk CL'). intros i Hi. clear - Hi AV. lia.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma cinv_al XB Mc modelc LKc crc Ac : cinv XB Mc modelc LKc crc Ac -> Scr mod 8 = 0 ->
  (Sp - Scr) mod 8 = 0 /\ ar_sptop ar mod 8 = 0 /\ ar_stack_top ar mod 4096 = 0 /\ ar_stack_top ar <= 2 ^ 47 /\ ar_sptop ar - 4096 <= ar_stack_top ar <= ar_sptop ar + 4096.
Proof.
  intros CI S8. pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & _). destruct CI as (HH & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & (B1 & B2) & (B3 & B4 & _ & B5) & TOP & _).
  clear - A16 S8 B1 B2 B3 B4 B5 TOP. lia.
Qed.
(* [comment removed for export] *)
Lemma aacc_stack XB Mc modelc LKc crc Ac p m : cinv XB Mc modelc LKc crc Ac -> Scr mod 8 = 0 -> Sp - Scr <= p -> p + m <= ar_sptop ar -> aacc Mc p m.
Proof.
  intros CI S8 H1 H2. pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT). pose proof (cinv_al _ _ _ _ _ _ CI S8) as (L8 & T8 & T4096 & _).
  destruct CI as (_ & _ & _ & _ & _ & SH & _).
  apply (aacc_of_zero Mc (Sp - Scr) ((Z.max (ar_sptop ar) (ar_stack_top ar) - (Sp - Scr)) / 8) p m SH L8). clear - SLO SPT; lia. exact H1.
  clear - H2 L8 T8 T4096. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Lemma aacc_xblk XB Mc modelc LKc crc Ac q n p m : cinv XB Mc modelc LKc crc Ac -> In (q, n) (XB ++ LB) -> q <= p -> p + m <= q + n -> aacc Mc p m.
Proof.
  intros (HH & _) Hin H1 H2. pose proof (blk_facts L ar C HI LY HIok _ _ _ _ _ _ _ q n HH Hin) as (BR & _ & SHB & _).
  apply (aacc_of_blk Mc q n p m SHB). Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - BR; lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). clear - BR; lia. exact H1. exact H2.
Qed.

(* [comment removed for export] *)
Lemma cinv_strerror XB Mc modelc LKc crc Ac (fx : FPState) R sp' r K :
  cinv XB Mc modelc LKc crc Ac -> K [] -> 0 <= Scr -> Scr mod 8 = 0 ->
  getr R (reg 10) = Z_to_bv 64 22 -> getr R (reg 11) = Z_to_bv 64 (sp' + 16) -> getr R (reg 12) = Z_to_bv 64 1024 ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  sp' mod 16 = 0 -> Sp - Scr <= sp' - 4320 -> sp' + 128 <= Sp ->
  L5.u64_at RSEGS Mc 0x610cd8 0x630fd0 -> L5.u64_at RSEGS Mc 0x630ff8 0 ->
  L5.img_clear Mc 0x10000 0xd7000 ->                                   (* [comment removed for export] *)
  (forall (fx' : FPState) R' M' model',
      getr R' (reg 10) = Z_to_bv 64 0 -> regs_preserved R R' ->
      cinv XB M' model' LKc crc Ac ->
      rdn RSEGS M' (Z_to_bv 64 (sp' + 16)) 17 = Some (map (Z_to_bv 8) EINVAL_MSG) ->
      (forall a k, 0 <= a -> a + k <= 2 ^ 64 -> ccl XB sp' a k -> (a + k <= sp' + 16 \/ sp' + 33 <= a) -> L5C.agree_on Mc M' a k) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R 0x4dc04 Mc modelc) K.
Proof.
  intros CI HK HS0 S8 G10 G11 G12 G1 RA G2 G4 A16' HLO HHI LC1 LC2 IMC KONT. pose proof CI as (HH & AM & RT & IA & STK & SH & EK & DK).
  pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT). pose proof (cinv_al _ _ _ _ _ _ CI S8) as (L8 & T8 & T4096 & _).
  pose proof (aic_strerror_r22 _ _ _ _ _ ICok) as HF. unfold astrerror_r22_spec in HF. cbv zeta in HF.
  rewrite (aly_segs L C LY), (aicl_strerror_r IL ILY), (aicl_scr_strerror IL ILY), (aicl_strerror_cells IL ILY), (aicl_sro_lo IL ILY), (aicl_sro_hi IL ILY) in HF.
  assert (U2 : bv_unsigned (getr R 2%bv) = sp'). { rewrite r2, G2. apply L5.unsigned_lit. clear - SLO SHI SPT HLO HHI HS0; lia. }
  assert (HC : ahl_ceil ar <= sp' - 4320) by (clear - SLO HLO HS0; lia).
  assert (BDEF : L5.defined Mc (sp' + 16) 17). { apply (astk_defined ar Mc Sp Scr (sp' + 16) 17 STK). clear - HLO; lia. clear - HHI; lia. }
  unfold cfg.
  eapply (HF fx R Mc modelc (XB ++ LB) FF LKc crc Ac K HH (proj1 AM) (proj2 AM)); clear HF.
  - rewrite r10. exact G10.
  - rewrite r11, U2. exact G11.
  - rewrite r12. exact G12.
  - rewrite r4. exact G4.
  - rewrite r1, G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (destruct RA as [X _]; clear - X; lia). exact (proj2 RA).
  - rewrite U2. pose proof (astack_ok_of_astk L ar C LY Mc Mc Sp Scr (Sp - sp') 4320 STK (mem_grows_refl Mc)) as X.
    replace (Sp - (Sp - sp')) with sp' in X by (clear; lia). apply X. clear - HHI; lia. clear; lia. clear - HLO; lia. exact A16'.
  - rewrite U2. clear - HHI SHI; lia.
  - rewrite U2. apply app_rng_stack. clear - SPT; lia. clear - HC; lia. clear - HHI SHI; lia.
  - rewrite U2. intros d m0 Hd Hm. apply (L5C.writable_of_defined RSEGS Mc (sp' + 16) 17 BDEF). clear - HC SPT; lia. clear - HHI SHI SPT; lia. exact Hd. exact Hm.
  - rewrite U2. intros x Hx. unfold in_shadow_of, S in Hx.
    replace x with (S (Sp - Scr) + (x - S (Sp - Scr))) by (clear; lia). apply SH. unfold S.
    clear - Hx HLO HHI SHI A16' L8 T8 T4096. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply Forall_cons. exact LC1. apply Forall_cons. exact LC2. apply Forall_nil.
  - intros a Ha. apply IMC. exact Ha.
  - exact HK.
  - intros fx' R' M' model' mR10 RP RDN PRES SDEF GROW RT2 MI2 HH2. rewrite U2 in PRES, SDEF, RDN. rewrite r1, G1.
    apply (KONT fx' R' M' model'). rewrite <- r10. exact mR10. exact RP.
    + apply (cinv_after_call XB XB Mc modelc LKc crc Ac M' model' crc Ac sp' 4320 (fun a => sp' + 16 <= a < sp' + 33) CI HS0 ltac:(clear; lia) HLO ltac:(clear - HHI; lia)).
      * exact HH2.
      * split. rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM). exact MI2.
      * exact RT2. * apply incl_refl.
      * exact PRES.
      * exact SDEF.
      * intros a Da. apply GROW. replace a with (sp' + 16 + (a - (sp' + 16))) by (clear; lia). apply BDEF. clear - Da; lia.
      * intros a. destruct (rng_dec a (sp' + 16) (sp' + 33)); [left|right]; assumption.
      * intros a Da. left. clear - Da HLO HHI; lia.
    + exact RDN.
    + intros a k Ha Hk CL' AV. apply (ag_of_pres XB sp' 4320 (fun x => sp' + 16 <= x < sp' + 33) Mc M' HC ltac:(clear; lia) PRES a k Ha Hk CL'). intros i Hi. clear - Hi AV. lia.
Qed.

(* [comment removed for export] *)
Lemma cinv_hnr XB Mc modelc LKc crc Ac (fx : FPState) R sp' r K :
  cinv XB Mc modelc LKc crc Ac -> K [] -> 0 <= Scr -> Scr mod 8 = 0 ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  sp' mod 16 = 0 -> Sp - Scr <= sp' - 8256 -> sp' <= Sp ->
  (forall (fx' : FPState) R' M' model',
      regs_preserved R R' ->
      cinv XB M' model' LKc crc Ac ->
      (forall a k, 0 <= a -> a + k <= 2 ^ 64 -> ccl XB sp' a k -> L5C.agree_on Mc M' a k) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R 0x670e8 Mc modelc) K.
Proof.
  intros CI HK HS0 S8 G1 RA G2 G4 A16' HLO HHI KONT. pose proof CI as (HH & AM & RT & IA & STK & SH & EK & DK).
  pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT). pose proof (cinv_al _ _ _ _ _ _ CI S8) as (L8 & T8 & T4096 & TOP47 & TNEAR).
  pose proof (aio_no_return _ _ _ _ _ HIok) as HF. unfold ahandle_no_return_spec in HF. cbv zeta in HF.
  rewrite (aly_segs L C LY), (aly_nr L C LY), (aly_scr_nr L C LY) in HF.
  assert (U2 : bv_unsigned (getr R 2%bv) = sp'). { rewrite r2, G2. apply L5.unsigned_lit. clear - SLO SHI SPT HLO HHI HS0; lia. }
  assert (HC : ahl_ceil ar <= sp' - 4160) by (clear - SLO HLO HS0; lia).
  unfold cfg.
  eapply (HF fx R Mc modelc (XB ++ LB) FF LKc crc Ac K HH (proj1 AM) (proj2 AM)); clear HF.
  - rewrite r4. exact G4.
  - rewrite r1, G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (destruct RA as [X _]; clear - X; lia). exact (proj2 RA).
  - rewrite U2. pose proof (astack_ok_of_astk L ar C LY Mc Mc Sp Scr (Sp - sp') 4160 STK (mem_grows_refl Mc)) as X.
    replace (Sp - (Sp - sp')) with sp' in X by (clear; lia). apply X. clear - HHI; lia. clear; lia. clear - HLO; lia. exact A16'.
  - exact HK.
  - intros R' M' model' lo RP LOR LO4096 SZ' PRES SDEF RT2 MI2 HH2. rewrite U2 in LOR, PRES, SDEF. rewrite r1, G1.
    (* [comment removed for export] *)
    assert (PRESF : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (XB ++ LB) FF sp' 4160 a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
    { intros a Ha Hc.
      destruct (Z_lt_le_dec a (S lo)) as [X|X]. { apply PRES. exact Ha. exact Hc. unfold in_shadow_of. clear - X; lia. }
      destruct (Z_lt_le_dec (S (lo + (ar_stack_top ar - lo) - 1)) a) as [Y|Y]. { apply PRES. exact Ha. exact Hc. unfold in_shadow_of. clear - Y; lia. }
      assert (E1 : a = S lo + (a - S lo)) by (clear; lia).
      assert (E2 : a = S (Sp - Scr) + (a - S (Sp - Scr))) by (clear; lia).
      unfold shadow_zero, byte_at in SZ'. rewrite E1 at 1. rewrite SZ'.
      2:{ unfold S in *. clear - X Y LO4096 T4096 LOR. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      rewrite E2. symmetry. apply SH. unfold S in *. clear - X Y LO4096 T4096 LOR HLO L8 T8. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (KONT fx R' M' model'). exact RP.
    + apply (cinv_after_call XB XB Mc modelc LKc crc Ac M' model' crc Ac sp' 4160 (fun _ => False) CI HS0 ltac:(clear; lia) ltac:(clear - HLO; lia) HHI).
      * exact HH2.
      * split. rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM). exact MI2.
      * exact RT2. * apply incl_refl.
      * intros a Ha Hc _. apply PRESF. exact Ha. exact Hc.
      * exact SDEF.
      * intros a []. * intros a. right. intros [].
      * intros a [].
    + intros a k Ha Hk CL'. apply (ag_of_pres XB sp' 4160 (fun _ => False) Mc M' HC ltac:(clear; lia)). intros x Hx Hc _. apply PRESF. exact Hx. exact Hc.
      exact Ha. exact Hk. exact CL'. intros i _ [].
Qed.

(* [comment removed for export] *)
Lemma cv_d4 XB Mc modelc LKc crc Ac a n v : cinv XB Mc modelc LKc crc Ac -> In (a, n, v) AS0_ALY_CELLS_D4 ->
  cell_is RSEGS (mrestrict (ahid Ac modelc) Mc) a (Z.to_nat n) v.
Proof.
  intros (HH & _) Hin. pose proof (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (aly_segs L C LY) in CS. rewrite Forall_forall in CS.
  pose proof (CS _ (aly_cells L C LY _ Hin)) as X. cbn [fst snd] in X.
  pose proof AS0_ALY_CELLS_D4_img as IMG. rewrite Forall_forall in IMG. specialize (IMG _ Hin). cbn [fst snd] in IMG.
  pose proof (vis_pack L ar C HI LY HIok _ _ _ _ _ _ _ HH) as (_ & _ & VIMG & _).
  unfold cell_is in *. rewrite (rdn_mrestrict_eq RSEGS (ahid Ac modelc) (Z.to_nat n) Mc). exact X.
  assert (N0 : 0 <= n). { unfold AS0_ALY_CELLS_D4 in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; clear; lia|]). destruct Hin. }
  apply range_avoids_of_avis. rewrite Z2Nat.id by exact N0. apply VIMG. clear - IMG; lia. clear - IMG; lia. clear - IMG; lia. rewrite Z2Nat.id by exact N0. clear - IMG; lia.
Qed.

(* [comment removed for export] *)
Lemma cv_tls XB Mc modelc LKc crc Ac : cinv XB Mc modelc LKc crc Ac ->
  exists ctx th tbv tev blk : Z,
    let MV := mrestrict (ahid Ac modelc) Mc in
    (L5.u64_at RSEGS MV 0x6320b0 ctx /\ L5.u64_at RSEGS MV (ctx + 152) th /\ L5.u64_at RSEGS MV (th + 48) tbv /\ L5.u64_at RSEGS MV (th + 56) tev
     /\ L5.u64_at RSEGS MV (hl_tp L + 8) blk /\ L5.u64_at RSEGS MV (blk + 24) (hl_tp L))
    /\ (4096 <= ctx /\ ctx + 160 <= ahl_ceil ar /\ 4096 <= th /\ th + 64 <= ahl_ceil ar /\ 4096 <= blk /\ blk + 4096 <= ahl_ceil ar /\ 0 <= tbv < 2 ^ 64 /\ 0 <= tev < 2 ^ 64)
    /\ ((ctx + 160 <= 0x10000 \/ 0x633000 <= ctx) /\ (th + 64 <= 0x10000 \/ 0x633000 <= th) /\ (blk + 4096 <= 0x10000 \/ 0x633000 <= blk))
    /\ ((ctx + 160 <= th \/ th + 64 <= ctx) /\ (ctx + 160 <= blk \/ blk + 4096 <= ctx) /\ (th + 64 <= blk \/ blk + 4096 <= th))
    /\ (forall q n, In (q, n) (XB ++ LB) -> (q + n <= ctx \/ ctx + 160 <= q) /\ (q + n <= th \/ th + 64 <= q) /\ (q + n <= blk \/ blk + 4096 <= q)).
Proof.
  intros CI. pose proof CI as (HH & _). pose proof (cinv_num _ _ _ _ _ _ CI) as (_ & _ & _ & SPT).
  destruct (aic_tls _ _ _ _ _ ICok _ _ _ _ _ _ _ HH) as (ctx & th & tbv & tev & blk & C1 & C2 & C3 & C4 & C5 & C6 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & I1 & I2 & I3 & P1 & P2 & P3 & NC).
  rewrite (aly_segs L C LY) in C1, C2, C3, C4, C5, C6. rewrite (aicl_ctxslot IL ILY) in C1. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in I1, I2, I3.
  pose proof (vis_pack L ar C HI LY HIok _ _ _ _ _ _ _ HH) as (_ & _ & VIMG & _).
  assert (VO : forall a n, (ctx <= a /\ a + n <= ctx + 160) \/ (th <= a /\ a + n <= th + 64) \/ (blk <= a /\ a + n <= blk + 4096) -> avis (ahid Ac modelc) a n).
  { intros a n Hr i Hi. apply ahid_not_lazy. apply (proj2 (NC (a + i) ltac:(clear - Hr Hi; lia))). }
  assert (TPR : 0x10000 <= hl_tp L /\ hl_tp L + 16 <= 0x633000). { rewrite (proj2 (proj2 UNWL)). unfold L5USA.TPV. clear; lia. }
  exists ctx, th, tbv, tev, blk. cbv zeta.
  split. { split. apply (proj2 (u64_at_vis _ Mc _ _ (VIMG 0x6320b0 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) ltac:(clear; lia))). exact C1.
           split. apply (proj2 (u64_at_vis _ Mc _ _ (VO (ctx + 152) 8 ltac:(left; clear; lia)) ltac:(clear - R1; lia) ltac:(clear - R2 SPT; lia))). exact C2.
           split. apply (proj2 (u64_at_vis _ Mc _ _ (VO (th + 48) 8 ltac:(right; left; clear; lia)) ltac:(clear - R3; lia) ltac:(clear - R4 SPT; lia))). exact C3.
           split. apply (proj2 (u64_at_vis _ Mc _ _ (VO (th + 56) 8 ltac:(right; left; clear; lia)) ltac:(clear - R3; lia) ltac:(clear - R4 SPT; lia))). exact C4.
           split. apply (proj2 (u64_at_vis _ Mc _ _ (VIMG (hl_tp L + 8) 8 ltac:(clear - TPR; lia) ltac:(clear - TPR; lia)) ltac:(clear - TPR; lia) ltac:(clear - TPR; lia))). exact C5.
           apply (proj2 (u64_at_vis _ Mc _ _ (VO (blk + 24) 8 ltac:(right; right; clear; lia)) ltac:(clear - R5; lia) ltac:(clear - R6 SPT; lia))). exact C6. }
  split. { clear - R1 R2 R3 R4 R5 R6 R7 R8. lia. }
  split. { clear - I1 I2 I3. lia. }
  split. { clear - P1 P2 P3. lia. }
  intros q n Hin. pose proof (blk_facts L ar C HI LY HIok _ _ _ _ _ _ _ q n HH Hin) as (BR & _).
  assert (CLI : forall a, q <= a < q + n -> aclient L ar (XB ++ LB) FF 0 0 a) by (intros a Ha; apply (block_client L ar (XB ++ LB) FF 0 0 q n a Hin Ha)).
  split. 2: split.
  - destruct (apart_of_pointwise ctx 160 q n ltac:(clear; lia) ltac:(clear - BR; lia)) as [X|X]. intros x Hx Hq. apply (proj1 (NC x ltac:(left; exact Hx)) 0 0). apply CLI. exact Hq.
    right; exact X. left; exact X.
  - destruct (apart_of_pointwise th 64 q n ltac:(clear; lia) ltac:(clear - BR; lia)) as [X|X]. intros x Hx Hq. apply (proj1 (NC x ltac:(right; left; exact Hx)) 0 0). apply CLI. exact Hq.
    right; exact X. left; exact X.
  - destruct (apart_of_pointwise blk 4096 q n ltac:(clear; lia) ltac:(clear - BR; lia)) as [X|X]. intros x Hx Hq. apply (proj1 (NC x ltac:(right; right; exact Hx)) 0 0). apply CLI. exact Hq.
    right; exact X. left; exact X.
Qed.

(* [comment removed for export] *)
Lemma agree_of_frm (Wp : Z -> Prop) (Mc M1 : word -> option byte) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  forall a k, 0 <= a -> a + k <= 2 ^ 64 -> (forall i, a <= i < a + k -> ~ Wp i) -> L5C.agree_on Mc M1 a k.
Proof. intros FRM a k Ha Hk ND i Hi. apply FRM. clear - Ha Hk Hi; lia. exact (ND i Hi). Qed.
(* [comment removed for export] *)
Lemma cu_zeros XB Mc modelc LKc crc Ac a n : cinv XB Mc modelc LKc crc Ac -> L5AUK.cvis ar LB XB a n ->
  L5KA.zeros_at (mrestrict (ahid Ac modelc) Mc) a n -> L5KA.zeros_at Mc a n.
Proof. intros CI Hv X. apply (proj1 (zeros_at_vis _ Mc a n (cvis_avis L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac CI a n Hv))). exact X. Qed.
Lemma cv_zeros XB Mc modelc LKc crc Ac a n : cinv XB Mc modelc LKc crc Ac -> L5AUK.cvis ar LB XB a n ->
  L5KA.zeros_at Mc a n -> L5KA.zeros_at (mrestrict (ahid Ac modelc) Mc) a n.
Proof. intros CI Hv X. apply (proj2 (zeros_at_vis _ Mc a n (cvis_avis L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac CI a n Hv))). exact X. Qed.

End CHAIN.
End WithIface.
End SCFG_1.

(* [comment removed for export] *)
Lemma auxv_cell (M : word -> option byte) (av uid rnd hw : Z) :
  (forall j : nat, (j < 20)%nat -> L5.u64_at RSEGS M (av + 8 * Z.of_nat j) (nth j (L5USA.auxv20A uid rnd hw) 0)) ->
  forall (j : nat) (a v : Z), (j < 20)%nat -> a = av + 8 * Z.of_nat j -> v = nth j (L5USA.auxv20A uid rnd hw) 0 -> L5.u64_at RSEGS M a v.
Proof. intros H j a v Hj -> ->. apply H. exact Hj. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition numf (P : Prop) : Prop := P.
Ltac nlia :=
  lazymatch goal with
  | NUM : numf _ |- _ =>
      repeat match goal with H : (_ < _)%nat |- _ => revert H end;
      repeat match goal with H : (_ <= ?i < _) |- _ => is_var i; revert H end;
      clear - NUM; unfold numf in NUM; intros; Lia.lia
  | |- _ => lia          (* [comment removed for export] *)
  end.
(* [comment removed for export] *)
Ltac dlia :=
  lazymatch goal with
  | NUM : numf _ |- _ =>
      match goal with D : (_ \/ _) |- _ =>
        solve [ repeat match goal with H : (_ < _)%nat |- _ => revert H end;
                repeat match goal with H : (_ <= ?i < _) |- _ => is_var i; revert H end;
                clear - NUM D; unfold numf in NUM; intros; Lia.lia ]
      end
  end.
Ltac ndlia := first [ nlia | dlia ].

(* [comment removed for export] *)
Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Ltac in_tac := solve [ repeat first [ left; reflexivity | right ] ].
(* [comment removed for export] *)
Ltac try_blocks XB k :=
  lazymatch XB with
  | (?q, ?n) :: ?rest => first [ k q n | try_blocks rest k ]
  | _ => fail "no block fits"
  end.
Ltac with_ci CI k :=
  lazymatch type of CI with
  | L5AUK.cinv ?L ?ar ?HI ?M0 ?model0 ?A0 ?LB ?FF ?Sp ?Scr ?W ?XB ?Mc ?modelc ?LKc ?crc ?Ac =>
      lazymatch goal with
      | LY : as0_layout L ?C, HIok : asan_iface_ok L ar ?C _ HI |- _ => k L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac
      end
  end.
(* [comment removed for export] *)
Ltac cvis_tac XB :=
  first [ lazymatch goal with |- L5AUK.cvis _ _ _ (Zpos _) _ => solve [right; left; clear; lia] end
        | solve [left; nlia] | solve [right; left; nlia]
        | right; right; try_blocks XB ltac:(fun q n => solve [exists q, n; split; [apply in_or_app; left; in_tac | nlia]]) ].
(* [comment removed for export] *)
Ltac fd_mem CI :=
  with_ci CI ltac:(fun L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac =>
    lazymatch goal with
    | |- L5.writable _ (mrestrict _ _) ?a ?n =>
        first [ lazymatch a with Zpos _ => apply (L5AUK.writable_img _ a n); [ vm_compute; reflexivity | clear; lia | clear; lia | clear; lia ] end
              | apply (proj1 (L5AUK.cv_stack L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac CI a n ltac:(nlia) ltac:(nlia) ltac:(nlia)))
              | try_blocks XB ltac:(fun q m => solve [ eapply L5.writable_sub; [ apply (proj1 (proj2 (L5AUK.cv_blk L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac CI q m ltac:(apply in_or_app; left; in_tac)))) | nlia | nlia ] ]) ]
    | |- L5.defined (mrestrict _ _) ?a ?n =>
        first [ apply (proj2 (L5AUK.cv_stack L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac CI a n ltac:(nlia) ltac:(nlia) ltac:(nlia)))
              | try_blocks XB ltac:(fun q m => solve [ eapply L5.defined_sub; [ apply (proj2 (proj2 (L5AUK.cv_blk L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac CI q m ltac:(apply in_or_app; left; in_tac)))) | nlia | nlia ] ]) ]
    | |- L5KA.zeros_at (mrestrict _ _) (?v / 8 + ?off) ?k =>
        lazymatch goal with SCR8 : Scr mod 8 = 0 |- _ =>
          first [ solve [ apply (L5AUK.cv_stksh L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W SCR8 XB Mc modelc LKc crc Ac CI v off k); [ assumption | unfold SB; nlia | unfold SB; nlia ] ]
                | try_blocks XB ltac:(fun q m => solve [ apply (L5AUK.cv_blksh L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac CI q m v off k); [ apply in_or_app; left; in_tac | assumption | unfold SB; nlia | unfold SB; nlia ] ]) ]
        end
    | |- L5KA.zeros_at (mrestrict _ _) ?a ?n =>
        apply (cv_zeros L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac a n CI); [ cvis_tac XB | gmem ]
    | |- L5.u64_at _ (mrestrict _ _) ?a ?v =>
        first [ lazymatch a with Zpos _ => exact (cv_d4 L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac a 8 v CI ltac:(unfold AS0_ALY_CELLS_D4, SB; in_tac)) end
              | solve [ apply (L5AUK.cv_u64 L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac CI a v); [ cvis_tac XB | nlia | nlia | first [asm | gmem] ] ] ]
    | |- L5.u32_at _ (mrestrict _ _) ?a ?v =>
        first [ lazymatch a with Zpos _ => exact (cv_d4 L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac a 4 v CI ltac:(unfold AS0_ALY_CELLS_D4, SB; in_tac)) end
              | solve [ apply (L5AUK.cv_u32 L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac CI a v); [ cvis_tac XB | nlia | nlia | first [asm | gmem] ] ] ]
    | |- L5.u8_at _ (mrestrict _ _) ?a ?v =>
        first [ lazymatch a with Zpos _ => exact (cv_d4 L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac a 1 v CI ltac:(unfold AS0_ALY_CELLS_D4, SB; in_tac)) end
              | solve [ apply (L5AUK.cv_u8 L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac CI a v); [ cvis_tac XB | nlia | nlia | first [asm | gmem] ] ] ]
    | |- L5.img_clear (mrestrict _ _) _ _ => apply img_clear_mrestrict; gmem
    end).
(* [comment removed for export] *)
Ltac lift_cells CI :=
  with_ci CI ltac:(fun L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac =>
    repeat match goal with H : ?A /\ ?B |- _ => lazymatch A with context [mrestrict _ Mc] => destruct H as [? ?] end end;
    repeat match goal with
    | H : L5.u64_at _ (mrestrict _ Mc) ?a ?v |- _ =>
        first [ apply (L5AUK.cu_u64 L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac CI a v ltac:(cvis_tac XB) ltac:(nlia) ltac:(nlia)) in H | clear H ]
    | H : L5.u32_at _ (mrestrict _ Mc) ?a ?v |- _ =>
        first [ apply (L5AUK.cu_u32 L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac CI a v ltac:(cvis_tac XB) ltac:(nlia) ltac:(nlia)) in H | clear H ]
    | H : L5.u8_at _ (mrestrict _ Mc) ?a ?v |- _ =>
        first [ apply (L5AUK.cu_u8 L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac CI a v ltac:(cvis_tac XB) ltac:(nlia) ltac:(nlia)) in H | clear H ]
    | H : L5KA.zeros_at (mrestrict _ Mc) ?a ?n |- _ =>
        first [ apply (cu_zeros L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac a n CI ltac:(cvis_tac XB)) in H | clear H ]
    | H : L5.defined (mrestrict _ Mc) _ _ |- _ => clear H
    end).
(* [comment removed for export] *)
Ltac carry Mo Mn AG sd :=
  repeat match goal with
  | H : L5.u64_at _ Mo ?a ?v |- _ =>
      first [ apply (L5C.u64_at_agree RSEGS Mo Mn a v ltac:(apply AG; [nlia | nlia | sd ..]) ltac:(nlia) ltac:(nlia)) in H | clear H ]
  | H : L5.u32_at _ Mo ?a ?v |- _ =>
      first [ apply (L5AUK.u32_at_agree Mo Mn a v ltac:(apply AG; [nlia | nlia | sd ..]) ltac:(nlia) ltac:(nlia)) in H | clear H ]
  | H : L5.u8_at _ Mo ?a ?v |- _ =>
      first [ apply (L5C.u8_at_agree RSEGS Mo Mn a v ltac:(apply AG; [nlia | nlia | sd ..]) ltac:(nlia) ltac:(nlia)) in H | clear H ]
  | H : L5KA.zeros_at Mo ?a ?n |- _ =>
      first [ apply (L5KA.zeros_at_agree1 Mo Mn a n ltac:(apply AG; [nlia | nlia | sd ..])) in H | clear H ]
  | H : ?P -> L5.u8_at _ Mo ?a ?v |- _ =>        (* [comment removed for export] *)
      first [ (let Y := fresh "CC" in
               assert (Y : P -> L5.u8_at RSEGS Mn a v) by (let p := fresh "p" in intros p; apply (L5C.u8_at_agree RSEGS Mo Mn a v ltac:(apply AG; [nlia | nlia | sd ..]) ltac:(nlia) ltac:(nlia) (H p)));
               clear H; rename Y into H)
            | clear H ]
  | H : forall j : nat, (j < ?n)%nat -> L5.u64_at _ Mo (@?a j) (@?v j) |- _ =>      (* [comment removed for export] *)
      first [ (let Y := fresh "CA" in
               assert (Y : forall j : nat, (j < n)%nat -> L5.u64_at RSEGS Mn (a j) (v j))
                 by (let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; cbv beta;
                     let aj := eval cbv beta in (a j) in let vj := eval cbv beta in (v j) in
                     apply (L5C.u64_at_agree RSEGS Mo Mn aj vj ltac:(apply AG; [nlia | nlia | sd ..]) ltac:(nlia) ltac:(nlia) (H j Hj)));
               clear H; rename Y into H; cbv beta in H)
            | clear H ]
  | H : rdn _ Mo (Z_to_bv 64 ?a) ?n = Some ?bs |- _ =>       (* [comment removed for export] *)
      first [ (let Y := fresh "RD" in
               assert (Y : rdn RSEGS Mn (Z_to_bv 64 a) n = Some bs)
                 by (rewrite (L5C.rdn_agree RSEGS Mo Mn n a ltac:(nlia) ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; nlia)
                                ltac:(apply AG; [nlia | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; nlia | sd ..])); exact H);
               clear H; rename Y into H)
            | clear H ]
  | H : L5.img_clear Mo ?lo ?hi |- _ =>
      first [ (let Y := fresh "IM" in
               assert (Y : L5.img_clear Mn lo hi)
                 by (let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
                     rewrite (AG i 1 ltac:(nlia) ltac:(nlia)); [ apply H; exact Hi | sd .. | nlia ]);
               clear H; rename Y into H)
            | clear H ]
  end.
(* [comment removed for export] *)
Ltac sd_piece := intros ?i ?Hi; cbv beta; ndlia.
(* [comment removed for export] *)
Ltac try_ranges W k :=
  lazymatch W with
  | ?r :: ?rest => first [ k r | try_ranges rest k ]
  | _ => fail "no range fits"
  end.
Ltac cfoot_tac :=
  let a := fresh "a" in let Wa := fresh "Wa" in
  intros a Wa; cbv beta in Wa; repeat (destruct Wa as [Wa|Wa]);
  lazymatch goal with
  | |- L5AUK.cfoot _ _ ?W ?XB _ =>
      first [ solve [left; nlia]
            | solve [right; left; try_blocks XB ltac:(fun q n => solve [exists (q, n); split; [in_tac | cbn [fst snd]; nlia]])]
            | solve [right; right; try_ranges W ltac:(fun r => solve [exists r; split; [in_tac | unfold L5.in_rng; cbn [fst snd]; nlia]])] ]
  end.
(* [comment removed for export] *)
Ltac ccl_lit XB :=
  first [ solve [right; left; clear; lia]
        | solve [right; right; left;
                 let l := eval unfold L5USA.UNW_STATICS, L5USA.UNW_CONSTS, L5USA.EH_CAUGHT, L5USA.SYSCAT_GUARD, L5USA.UW_FLAGS, L5USA.ERRNO, app in (L5USA.UNW_STATICS ++ L5USA.UNW_CONSTS) in
                 try_ranges l ltac:(fun r => solve [exists r; split; [ (unfold L5USA.UNW_STATICS, L5USA.UNW_CONSTS, L5USA.EH_CAUGHT, L5USA.SYSCAT_GUARD, L5USA.UW_FLAGS, L5USA.ERRNO; cbn [app]; in_tac) | cbn [fst snd]; clear; lia]])] ].
Ltac ccl_var XB :=
  first [ solve [right; left; nlia]
        | solve [right; right; left;
                 let l := eval unfold L5USA.UNW_STATICS, L5USA.UNW_CONSTS, L5USA.EH_CAUGHT, L5USA.SYSCAT_GUARD, L5USA.UW_FLAGS, L5USA.ERRNO, app in (L5USA.UNW_STATICS ++ L5USA.UNW_CONSTS) in
                 try_ranges l ltac:(fun r => solve [exists r; split; [ (unfold L5USA.UNW_STATICS, L5USA.UNW_CONSTS, L5USA.EH_CAUGHT, L5USA.SYSCAT_GUARD, L5USA.UW_FLAGS, L5USA.ERRNO; cbn [app]; in_tac) | cbn [fst snd]; nlia]])] ].
Ltac ccl_sym XB :=
  first [ solve [left; nlia]
        | solve [right; right; right; try_blocks XB ltac:(fun q n => solve [exists q, n; split; [in_tac | nlia]])] ].
Ltac ccl_tac :=
  idtac; lazymatch goal with
  | |- ccl ?XB _ ?a _ =>
      lazymatch a with
      | Zpos _ => ccl_lit XB
      | Zpos _ + Zpos _ => ccl_lit XB
      | _ => first [ ccl_sym XB | ccl_var XB ]
      end
  end.

(* [comment removed for export] *)
Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                               | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Ltac scx := first [ asm | rk | gmem | (arith_goal; first [asm | nlia | dlia | blia]) ].
Ltac fdp CI := first [ apply L5AUK.UR | apply L5AUK.U_to | apply BL.bvu_range | scx | fd_mem CI ].
(* [comment removed for export] *)
Tactic Notation "piece_step" constr(CI) constr(WIMG) ident(P) constr(Wp) ident(fxn) ident(Rn) ident(Mn) ident(modeln) ident(CIn) :=
  feed P ltac:(fdp CI);
  let Mv := fresh "Mv" in let MG := fresh "MG" in let FZ := fresh "FZ" in let MS := fresh "MS" in let EX := fresh "EX" in
  destruct P as (fxn & Rn & Mv & MG & _ & FZ & (MS & EX));
  with_ci CI ltac:(fun L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac =>
    lazymatch goal with HS0 : 0 <= Scr |- srealizes _ _ _ ?K =>
      apply (L5AUK.cinv_piece L ar C HI LY HIok M0 model0 A0 LB FF Sp Scr W WIMG XB Mc modelc LKc crc Ac _ fxn _ _ Rn _ Mv Wp K CI HS0 MS MG);
      [ (let a := fresh "a" in let Ha := fresh "Ha" in let Hna := fresh "Hna" in intros a Ha Hna; apply FZ; [exact Ha | cbv beta in Hna; clear - Hna; lia ..])
      | cfoot_tac
      | (let AH := fresh "AH" in let VIS := fresh "VIS" in let FRM := fresh "FRM" in let AG := fresh "AG" in
         intros Mn modeln CIn AH VIS FRM; subst Mv; clear MS MG FZ;
         repeat (lazymatch type of EX with _ /\ _ => let X := fresh "EX" in destruct EX as [X EX] end);
         pose proof (agree_of_frm Wp Mc Mn FRM) as AG; cbv beta in AG;
         lift_cells CIn; carry Mc Mn AG sd_piece; clear AG FRM) ]
    end).
(* [comment removed for export] *)
Ltac clear_regs Rd := repeat match goal with H : getr Rd _ = Z_to_bv 64 _ |- _ => clear H end.
(* [comment removed for export] *)
Tactic Notation "norm_ks" constr(Rn) constr(Ro) ident(KSn) :=
  match goal with H : forall x, In x ?ks -> getr Rn (reg x) = getr Ro (reg x) |- _ =>
    assert (KSn : forall x, In x L5SA.cs_all -> getr Rn (reg x) = getr Ro (reg x))
      by (let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; apply H; revert x Hx; apply L5K.incl_b; vm_compute; reflexivity);
    clear H end.
(* [comment removed for export] *)
Ltac tidy CIk :=
  repeat match goal with H : L5AUK.cinv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => tryif constr_eq H CIk then fail else clear H end;
  repeat match goal with H : ahid _ _ = ahid _ _ |- _ => clear H end;
  repeat match goal with M : word -> option byte |- _ => clear M end;
  repeat match goal with M : Model |- _ => clear M end;
  repeat match goal with M : FPState |- _ => clear M end.
(* [comment removed for export] *)
Ltac sd_call := idtac; lazymatch goal with |- ccl _ _ _ _ => ccl_tac | |- _ => nlia end.
End L5AUK2.
