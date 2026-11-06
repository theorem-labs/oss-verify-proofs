(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value: proofs of three Props of the shared call kit
   lib/B/Prog/ExvB_Loop_kit.v (owner ExvLoop; shared with ExvOpen / ExvDisp):
   - exv_kit_chain  : KIT_CALL_CHAIN. ex_value keeps s0 = its entry sp, so a call's frame chain is ex_value's own record
     (exv_sp E - 8: the entry ra, EXB's saved slot (280, 1); exv_sp E - 16: the entry s0, slot (272, 8)) followed by
     the entry chain e_ch E. The entry chain is read through EXV_PRE's prhex_ch_apart at the reader "current view at
     or above exv_sp E, entry view below": the two views agree at or above exv_sp E outside the cursor [q, q + 40)
     (EXB's caller-window clause up to exv_sp E + e_d E, the journal's >= alloc_ceiling clause above it), and
     fpchain reads only words at or above the sp it is stated at. Both records' words lie below exv_sp E <= q, so
     any reader agreeing with the current view outside [q, q + 40) reads the same chain (prhex_ch_apart at the call).
   - exv_kit_rodata : KIT_RODATA. arodata_okP is kept by the journal's image clause (a read-only byte is no PST byte,
     S1ImgB.v pst_not_ro_B; exv_FP E does not open the sink); rom_view from it by EXV_HYP's eh_rom_own and the
     errno word's place in B's writable image (by computation at eh_errno_B).
   - exv_kit_wdest  : KIT_WDEST. EXB's wdest_ok at width 0 plus the window: the scratch ends below alloc_ceiling,
     the callee's window [exv_s1 E - STK1, exv_s1 E) starts at or above exv_sp E - exv_STK E >= ly_stk_lo >=
     alloc_ceiling (astk_ok of EXV_PRE's fpre).
   Rule 24: proves no function (kind: segment lemma).
   Numerals: 1, 2, 8 (WORD: register numbers ra, sp, s0); 8, 16 (LENGTH: frame-record word offsets); 280, 272, 288
   (LENGTH: B's saved-slot offsets, ExvB_Stmt.v exv_saved); 40 (LENGTH: struct ex); 4 (LENGTH: errno word);
   2 ^ 64, 2 ^ 47 (LENGTH: word range, stack ceiling of astk_ok). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0s YP08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_kit ExvB_Open_kt.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Existing Instance prh_img_B.

(* ---- image-free helpers ---- *)
Lemma exvq_w64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

Lemma exvq_bvr : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H. Qed.

(* a word val_mem holds is the word rdword reads (YCem.v rdword_of_val_mem, restated: YCem's dependency YCeh does
   not build on this base) *)
Lemma exvq_rdword : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply YG0s.le_bytes8. exact Hr.
Qed.

(* fpchain reads only the words at fp - 8 and fp - 16 of its records and at bp - 8 of its end, all in [lo, top) when
   the chain starts at bp >= lo + 16 below top - 16 *)
Lemma exvq_fpchain_ext : forall (load load' : Z -> option Z) lo top ch bp,
  (forall a, lo <= a -> a + 8 <= top -> load' a = load a) -> lo + 16 <= bp -> bp <= top - 16 ->
  fpchain load bp top ch -> fpchain load' bp top ch.
Proof.
intros load load' lo top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hag Hlo Hhi H; cbn [fpchain] in *.
- destruct H as (r & Hr & Hb). exists r. rewrite Hag by lia. split; [exact Hr | exact Hb].
- destruct H as (Efp & Hm & Hra & Hn & H4 & Hrest). subst fp.
  split; [reflexivity|]. split; [exact Hm|]. rewrite (Hag (bp - 8)) by lia. rewrite (Hag (bp - 16)) by lia.
  split; [exact Hra|]. split; [exact Hn|]. split; [exact H4|].
  destruct (bad_next bp top nfp) eqn:Hb; [exact Hrest|].
  unfold bad_next in Hb. apply orb_false_iff in Hb as [Hb12 Hb3]. apply orb_false_iff in Hb12 as [Hb1 Hb2].
  apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
  exact (IH nfp Hag ltac:(lia) ltac:(lia) Hrest).
Qed.

Section q. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.

(* the entry sp: in the stack, at or above alloc_ceiling + the entry's stack need, below 2 ^ 47 *)
Lemma exvq_sp_rng : forall E, EXV_PRE B ARx E ->
  0 <= exv_STK E /\ alloc_ceiling <= ly_stk_lo (e_ly E) /\ ly_stk_lo (e_ly E) + exv_STK E <= exv_sp E /\
  exv_sp E <= ly_top (e_ly E) /\ ly_top (e_ly E) <= ly_stk_hi (e_ly E) /\ ly_stk_hi (e_ly E) <= 2 ^ 47 /\
  exv_sp E mod 16 = 0.
Proof.
intros E HPRE. destruct HPRE as (HFP & _). destruct HFP as (HAF & _ & _).
destruct HAF as (_ & _ & _ & _ & _ & HASK & _). destruct HASK as (Hm16 & HS0 & Hclo & Hlosp & _ & Hhi47 & _ & Hsptop & Htophi).
unfold exv_sp. repeat split; assumption.
Qed.

(* the chain a call from ex_value takes: ex_value's own record, then the entry chain *)
Definition exvq_ch1 (E : exv_e) (lyc : alayout) : list (Z * Z * Z) :=
  if ly_top lyc - 16 <=? exv_sp E then []
  else (exv_sp E, raZ (e_regs E), s0Z (e_regs E)) ::
       (if bad_next (exv_sp E) (ly_top lyc) (s0Z (e_regs E)) then [] else e_ch E).

Lemma exvq_chain_rd : forall (fx : YK11.FPState) E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos
    (rd : reader),
  EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  (forall a, ~ (e_q E <= a < e_q E + 40) -> rd a = aview rsegs (w_H Wc) memc a) ->
  achain lyc rd (exv_s1 E) (exv_sp E) (exvq_ch1 E lyc).
Proof.
intros fx E lyc Sc Hpc Wc regs memc mdc k pos rd HPRE HEXB Hrd.
pose proof (exv_s1_le E) as [Hs1 _].
pose proof (exvq_sp_rng E HPRE) as (HS0 & Hclo & Hlosp & Hsptop & Htophi & Hhi47 & Hm16).
destruct HPRE as (HFP & _ & _ & _ & _ & _ & _ & HAP & Hspq & Hqd & _ & _ & _ & _ & _ & _ & _ & _ & HWD & _ & _ & _ & _ & _).
destruct HFP as (HAF & _ & _). destruct HAF as (_ & _ & Hra4 & _).
destruct HWD as (Hsc0 & Hscn & _).
destruct HEXB as (HJ & HWIN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSAV & _).
destruct HJ as (_ & HLE & _ & _ & _ & _ & _ & _ & HCEIL & _).
destruct HLE as (_ & _ & _ & _ & _ & _ & _ & _ & Htop & _).
change (spZ (e_regs E)) with (exv_sp E) in Hspq, Hqd.
(* the current view is the entry's at or above exv_sp E, outside the cursor *)
assert (AG : forall a, exv_sp E <= a < 2 ^ 64 -> ~ (e_q E <= a < e_q E + 40) ->
  aview rsegs (w_H Wc) memc a = aview rsegs (w_H (e_W E)) (e_mem E) a).
{ intros a Ha Hq. destruct (Z_lt_le_dec a (exv_sp E + e_d E)) as [Hlt|Hge].
  - apply HWIN; [lia|]. intros (r & Hr & Hra). unfold exv_FP in Hr. cbn [In] in Hr.
    destruct Hr as [Hr|[Hr|[Hr|[Hr|[]]]]]; subst r; cbn [fst snd] in Hra; lia.
  - apply HCEIL; lia. }
(* the record's two words: below exv_sp E <= q, EXB's saved slots *)
assert (Hsav1 : rdword rd (exv_sp E - 8) = Some (raZ (e_regs E))).
{ rewrite (rdword_ext (aview rsegs (w_H Wc) memc) rd (exv_sp E - 8)) by (intros kk Hk; apply Hrd; lia).
  replace (exv_sp E - 8) with (exv_sp E - 288 + 280) by lia.
  apply exvq_rdword;
    [exact (HSAV 280 1 ltac:(cbn [exv_saved In]; left; reflexivity)) | unfold raZ; apply exvq_bvr]. }
assert (Hsav2 : rdword rd (exv_sp E - 16) = Some (s0Z (e_regs E))).
{ rewrite (rdword_ext (aview rsegs (w_H Wc) memc) rd (exv_sp E - 16)) by (intros kk Hk; apply Hrd; lia).
  replace (exv_sp E - 16) with (exv_sp E - 288 + 272) by lia.
  apply exvq_rdword;
    [exact (HSAV 272 8 ltac:(cbn [exv_saved In]; right; left; reflexivity)) | unfold s0Z; apply exvq_bvr]. }
assert (Hm8 : exv_sp E mod 8 = 0) by lia.
unfold exvq_ch1, achain. rewrite Htop.
destruct (Z.leb_spec (ly_top (e_ly E) - 16) (exv_sp E)) as [Hle|Hgt].
- left. split; [right; left; exact Hle | reflexivity].
- right. destruct (bad_next (exv_sp E) (ly_top (e_ly E)) (s0Z (e_regs E))) eqn:Hbn; cbv iota.
  + split; [lia|]. split; [lia|]. split; [exact Hm8|]. split.
    * cbn [fpchain]. split; [reflexivity|]. split; [exact Hm8|]. split; [exact Hsav1|]. split; [exact Hsav2|].
      split; [exact Hra4|]. rewrite Hbn. exact eq_refl.
    * constructor; [cbn [fst]; lia | constructor].
  + pose proof Hbn as Hb. unfold bad_next in Hb. apply orb_false_iff in Hb as [Hb12 Hb3].
    apply orb_false_iff in Hb12 as [Hb1 Hb2]. apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
    apply negb_false_iff in Hb3. apply Z.eqb_eq in Hb3.
    (* the entry chain, read at the reader: rd at or above exv_sp E, the entry view below *)
    set (rd2 := fun a => if (exv_sp E <=? a) && (a <? 2 ^ 64) then rd a else aview rsegs (w_H (e_W E)) (e_mem E) a).
    assert (Hrd2 : forall a, ~ (e_q E <= a < e_q E + 40) -> rd2 a = aview rsegs (w_H (e_W E)) (e_mem E) a).
    { intros a Ha. unfold rd2. cbv beta. destruct ((exv_sp E <=? a) && (a <? 2 ^ 64)) eqn:Hc; [|reflexivity].
      apply andb_true_iff in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2.
      rewrite (Hrd a Ha). apply AG; [lia | exact Ha]. }
    pose proof (HAP rd2 Hrd2) as HCH. change (spZ (e_regs E)) with (exv_sp E) in HCH. unfold achain in HCH.
    destruct HCH as [(Hc & _) | (Hs16 & _ & _ & Hfp & HFa)]; [exfalso; lia|].
    split; [lia|]. split; [lia|]. split; [exact Hm8|]. split.
    * cbn [fpchain]. split; [reflexivity|]. split; [exact Hm8|]. split; [exact Hsav1|]. split; [exact Hsav2|].
      split; [exact Hra4|]. rewrite Hbn. cbv iota.
      apply (exvq_fpchain_ext (rdword rd2) (rdword rd) (exv_sp E) (ly_top (e_ly E)) (e_ch E) (s0Z (e_regs E)));
        [| lia | lia | exact Hfp].
      intros a Ha1 Ha2. apply rdword_ext. intros kk Hk. unfold rd2. cbv beta.
      destruct ((exv_sp E <=? a + kk) && (a + kk <? 2 ^ 64)) eqn:Hc; [reflexivity|].
      exfalso. apply andb_false_iff in Hc as [Hc|Hc]; [apply Z.leb_gt in Hc | apply Z.ltb_ge in Hc]; lia.
    * constructor; [cbn [fst]; lia|].
      rewrite Forall_forall in HFa |- *. intros [[f1 r1] n1] Hin. specialize (HFa _ Hin). cbn [fst] in *. lia.
Qed.

(* (b) KIT_CALL_CHAIN *)
Lemma exv_kit_chain : forall fx : YK11.FPState, KIT_CALL_CHAIN (fx := fx) B ARx SK.
Proof.
intros fx E lyc Sc Hpc Wc regs memc mdc k pos regsc HPRE HEXB Hsp Hs0.
pose proof (exv_s1_le E) as [Hs1 _].
pose proof (exvq_sp_rng E HPRE) as (HS0 & Hclo & Hlosp & Hsptop & Htophi & Hhi47 & _).
pose proof alloc_ceiling_value as [[Hcm _] _].
exists (exvq_ch1 E lyc). split.
- apply (exvq_chain_rd fx E lyc Sc Hpc Wc regs memc mdc k pos); [exact HPRE | exact HEXB | intros; reflexivity].
- unfold prhex_ch_apart. intros rd' Hrd'.
  assert (E1 : spZ regsc = exv_s1 E) by (unfold spZ; rewrite Hsp; apply exvq_w64; lia).
  assert (E2 : s0Z regsc = exv_sp E) by (unfold s0Z; rewrite Hs0; apply exvq_w64; lia).
  rewrite E1, E2. exact (exvq_chain_rd fx E lyc Sc Hpc Wc regs memc mdc k pos rd' HPRE HEXB Hrd').
Qed.

(* the errno word is not read-only (B's errno sits in its writable image) *)
Lemma exvq_errno_rw : forall a, as_errno B <= a < as_errno B + 4 ->
  ~ in_roP rsegs B_prog_relro_lo B_prog_relro_hi a.
Proof.
intros a Ha Hro. rewrite (eh_errno_B B ARx SK HYP) in Ha.
assert (HC : YP08.zallb (fun x => negb (S1ImgCheck.in_ro_b rsegs B_prog_relro_lo B_prog_relro_hi x)) YF0m.TFIB_ERRNO 4%nat = true)
  by (vm_compute; reflexivity).
pose proof (YP08.zallb_sound _ 4%nat YF0m.TFIB_ERRNO a HC ltac:(change (Z.of_nat 4) with 4; lia)) as H.
cbv beta in H. rewrite (S1ImgCheck.in_ro_b_complete _ _ _ _ Hro) in H. discriminate.
Qed.

(* (c) KIT_RODATA *)
Lemma exv_kit_rodata : forall fx : YK11.FPState, KIT_RODATA (fx := fx) B ARx SK.
Proof.
intros fx E lyc Sc Hpc Wc regs memc mdc k pos HPRE HEXB.
pose proof (exvq_sp_rng E HPRE) as (HS0 & Hclo & Hlosp & _).
pose proof alloc_ceiling_value as [[Hcm _] _].
destruct HPRE as (HFP & _ & _ & _ & _ & _ & _ & _ & Hspq & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIBS & _ & _ & _ & _).
destruct HFP as (HAF & HROD & _). destruct HAF as (HAR & _).
change (spZ (e_regs E)) with (exv_sp E) in Hspq.
destruct HEXB as (HJ & _). destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIMG & _).
(* exv_FP E does not open the sink: the scratch is in a live block (>= 4096), the cursor cells on the stack *)
assert (HSP : ~ YI16.sink_open_fp (exv_FP E)).
{ destruct HIBS as (b & m & Hin & Hb & _).
  pose proof (alx_blocks rsegs B ARx (eh_laws B ARx SK HYP) _ _ _ _ _ _ b m HAR Hin) as (_ & Hb4 & _).
  intros (r & Hr & Hr0). unfold exv_FP in Hr. cbn [In] in Hr.
  destruct Hr as [Hr|[Hr|[Hr|[Hr|[]]]]]; subst r; cbn [fst snd] in Hr0; lia. }
assert (ARO : arodata_okP rsegs B_prog_relro_lo B_prog_relro_hi B (aview rsegs (w_H Wc) memc)).
{ intros a Hro Hno Her. rewrite HIMG; [exact (HROD a Hro Hno Her) | | exact Hno | exact Her | | ].
  - destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (B_prog_relro a Hr)].
  - intros Hp. exact (S1ImgB.pst_not_ro_B a Hp Hro).
  - apply fp_spares_closed. exact HSP. }
split; [exact ARO|]. unfold arodata_okP in ARO.
intros a Ha Hno. apply ARO; [left; exact Ha | exact Hno |].
intros Her. exact (exvq_errno_rw a Her (or_introl Ha)).
Qed.

(* (d) KIT_WDEST *)
Lemma exv_kit_wdest : forall fx : YK11.FPState, KIT_WDEST (fx := fx) B ARx SK.
Proof.
intros fx E lyc Sc Hpc Wc regs memc mdc k pos regsc STK1 HPRE HEXB Hsp HS1 HSTK.
pose proof (exv_s1_le E) as [Hs1 _].
pose proof (exvq_sp_rng E HPRE) as (HS0 & Hclo & Hlosp & Hsptop & Htophi & Hhi47 & _).
pose proof alloc_ceiling_value as [[Hcm _] _].
destruct HEXB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWD & _).
destruct HWD as (Hd0 & Hdn & Ham & Hall & Hra & Hhull).
assert (E1 : spZ regsc = exv_s1 E) by (unfold spZ; rewrite Hsp; apply exvq_w64; lia).
split; [exact Hd0|]. split; [exact Hdn|]. split; [exact Ham|]. split; [|split; [exact Hra | exact Hhull]].
intros a Ha. destruct (Hall a Ha) as (Hw & Hno & _). split; [exact Hw|]. split; [exact Hno|].
rewrite E1. lia.
Qed.
End q.

Print Assumptions exv_kit_chain.
Print Assumptions exv_kit_rodata.
Print Assumptions exv_kit_wdest.
