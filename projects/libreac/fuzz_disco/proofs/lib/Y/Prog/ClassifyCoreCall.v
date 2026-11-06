(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:86-90
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 332-335, 358-363, 460-463 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1593-1596, 1605-1615 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:2082-2086 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:393-396. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue_defect.v, with its module paths, module names and numbers changed; 282 of its 366 lines of code are new or changed and 575 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacRivalKindOf.v; 586 of its 636 lines of code are new or changed and 316 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YP03.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacPortsParse ClassifyCore ClassifyCoreSeg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed RcParse RcLeaf disco_classify_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma cc_stk : CLS_STK = 176 + CLS_PARSE_NEED /\ CLS_PARSE_NEED = 144 + 2 * ESTACK /\
  CLS_CHK_NEED = 16 + ESTACK /\ REAC_PORTS_PARSE_STK = 16 + ESTACK /\ 0 <= ESTACK.
Proof.
unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, CLS_CHK_NEED, REAC_PORTS_PARSE_STK, ESTACK. lia.
Qed.

Lemma cc_lyF : forall n ly ly', layout_le n ly ly' -> ly_F ly' = ly_F ly.
Proof. intros n ly ly' H. destruct H as (_ & _ & _ & _ & _ & HF & _). exact HF. Qed.

Lemma cc_top : forall n ly ly', layout_le n ly ly' -> ly_top ly' = ly_top ly.
Proof. intros n ly ly' H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & HT & _). exact HT. Qed.

Lemma cc_frame_addr : forall ly ly' c p, ly_F ly' = ly_F ly -> frame_addr ly' c p = frame_addr ly c p.
Proof. intros ly ly' c p H. unfold frame_addr. rewrite H. reflexivity. Qed.

Lemma cc_flag_addr : forall ly ly' c p, ly_F ly' = ly_F ly -> flag_addr ly' c p = flag_addr ly c p.
Proof. intros ly ly' c p H. unfold flag_addr. rewrite H. reflexivity. Qed.

Lemma cc_rv : forall (regs : bvmap 5 word) RV r v,
  Forall (fun rv => getr regs (Z_to_bv 5 (fst rv)) = w64 (snd rv)) RV -> In (r, v) RV ->
  getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs RV r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.

Lemma cc_pres : forall (regs3 regs2 : bvmap 5 word) r v,
  aregs_preserved regs3 regs2 -> acallee_saved r -> getr regs3 (Z_to_bv 5 r) = v -> getr regs2 (Z_to_bv 5 r) = v.
Proof. intros regs3 regs2 r v HP Hr E. rewrite (HP r Hr). exact E. Qed.

Lemma cc_qaddr {rc : YM05.RunCeil} : forall F c n, in_app F 256 -> zone2 F 256 -> F + 256 <= alloc_ceiling ->
  0 <= c -> 0 <= n -> c + n <= 256 ->
  F + c + n <= 2 ^ 47 /\ amem_range (F + c) n /\ off_img (F + c) n /\
  (F + c + n <= kLowShadowBeg \/ kHighMemBeg <= F + c).
Proof.
intros F c n Happ Hz HFc Hc Hn Hcn. pose proof alloc_ceiling_value as Hac. destruct Hz as (Hoi & _).
unfold in_app, amem_range, off_img, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. lia.
Qed.

Lemma cc_patA : forall F x, F mod 32 = 0 -> F + 32 <= x < F + 32 + 36 ->
  saddr_ok x (nth (Z.to_nat ((x - F) / 8)) PAT_A 0).
Proof.
intros F x HF Hx.
assert (Hq : (x - F) / 8 = 4 \/ (x - F) / 8 = 5 \/ (x - F) / 8 = 6 \/ (x - F) / 8 = 7 \/ (x - F) / 8 = 8) by lia.
unfold saddr_ok. destruct Hq as [E | [E | [E | [E | E]]]]; rewrite E.
- left. reflexivity.
- left. reflexivity.
- left. reflexivity.
- left. reflexivity.
- right. change (nth (Z.to_nat 8) PAT_A 0) with 4. lia.
Qed.

Lemma cc_patB : forall F x, F mod 32 = 0 -> F + 112 <= x < F + 112 + 12 ->
  saddr_ok x (nth (Z.to_nat ((x - F) / 8)) PAT_B 0).
Proof.
intros F x HF Hx.
assert (Hq : (x - F) / 8 = 14 \/ (x - F) / 8 = 15) by lia.
unfold saddr_ok. destruct Hq as [E | E]; rewrite E.
- left. reflexivity.
- right. change (nth (Z.to_nat 15) PAT_B 0) with 4. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma cc_ra : forall (regs : bvmap 5 word) k, getr regs 1 = w64 (BASE + k) -> 0 <= k < 2 ^ 40 -> k mod 2 = 0 ->
  YK0s.ret_ok (getr regs 1) /\ raZ regs = BASE + k.
Proof.
intros regs k H Hk Hk2. pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _). split.
- rewrite H. exact (ret_ok_codeptr_v k Hk Hk2).
- unfold raZ. rewrite H. unfold w64. apply YP03.unsigned_lit_small. lia.
Qed.

Lemma cc_shrd : forall (W3 : world SEGS) mem3 F SHP,
  garr8 SEGS (mrestrict (w_H W3) mem3) (SHADOW_OFF + F / 8) SHP ->
  forall i, (i < length SHP)%nat -> aview SEGS (w_H W3) mem3 (SHADOW_OFF + F / 8 + Z.of_nat i) = Some (nth i SHP 0).
Proof.
intros W3 mem3 F SHP G i Hi. destruct (G i Hi) as [Hv Hr]. exact (aview_of_val_mem1 _ _ _ _ _ Hv Hr).
Qed.

Lemma cc_ra_sh : forall (W3 : world SEGS) mem3 F SHP c n,
  F mod 32 = 0 -> length SHP = 32%nat -> garr8 SEGS (mrestrict (w_H W3) mem3) (SHADOW_OFF + F / 8) SHP ->
  0 <= c -> 0 <= n -> c + n <= 256 ->
  (forall x, F + c <= x < F + c + n -> saddr_ok x (nth (Z.to_nat ((x - F) / 8)) SHP 0)) ->
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (F + c) n.
Proof.
intros W3 mem3 F SHP c n HF HL G Hc Hn Hcn Hok x Hx.
exists (nth (Z.to_nat ((x - F) / 8)) SHP 0). split; [|exact (Hok x Hx)].
assert (E : shadow_of_addr SHADOW_OFF x = SHADOW_OFF + F / 8 + Z.of_nat (Z.to_nat ((x - F) / 8))).
{ rewrite Z2Nat.id by (apply Z.div_pos; lia). unfold shadow_of_addr. lia. }
rewrite E. apply (cc_shrd W3 mem3 F SHP G). rewrite HL. lia.
Qed.

Lemma cc_hull : forall (W3 : world SEGS) mem3 F SHP c n,
  F mod 32 = 0 -> length SHP = 32%nat -> garr8 SEGS (mrestrict (w_H W3) mem3) (SHADOW_OFF + F / 8) SHP ->
  32 <= c -> 0 < n -> c + n <= 192 ->
  shadow_hull_vis (aview SEGS (w_H W3) mem3) (F + c) n.
Proof.
intros W3 mem3 F SHP c n HF HL G Hc Hn Hcn s Hs. unfold shadow_addr in Hs.
assert (Hj : 0 <= s - (SHADOW_OFF + F / 8) < 32) by (unfold SHADOW_OFF in *; lia).
replace s with (SHADOW_OFF + F / 8 + Z.of_nat (Z.to_nat (s - (SHADOW_OFF + F / 8)))) by lia.
rewrite (cc_shrd W3 mem3 F SHP G) by (rewrite HL; lia). discriminate.
Qed.

Lemma cc_rod : forall B (W W2 : world SEGS) memc mem2,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
intros B W W2 memc mem2 HR HK a Hro Ho He. rewrite (HK a); [exact (HR a Hro Ho He) | | exact Ho | exact He].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hgot)].
Qed.

Definition cls_setfq (cx : ccx) (fx : YK11.FPState) : ccx :=
  mkCCX fx (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) (x_k cx) (x_regs cx) (x_ch cx)
  (x_lk cx) (x_f cx) (x_len cx) (x_u cx) (x_o cx) (x_FB cx) (x_U cx) (x_OB cx) (x_L cx).

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis NOW : cls_now_ok B.
Hypothesis ACH : cls_achain_ok B.

Ltac cc_in := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma tcls_post_fp : forall cx (fx : YK11.FPState) (W2 : world SEGS) c2,
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx) k = Sem.reg_get (@YK11.fp_regs (x_fq cx)) k) ->
  (@YK11.fp_csr fx = @YK11.fp_csr (x_fq cx) \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx)) 5) 7 = 0) ->
  cls_Q B (cls_setfq cx fx) W2 c2 -> cls_Q B cx W2 c2.
Proof.
intros cx fx W2 c2 HR HC (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hc & HR' & HC' & H).
exists fx', ly2, S2, regs2, mem2, md2.
split; [exact Hc|].
split; [intros k Hk; exact (eq_trans (HR' k Hk) (HR k Hk))|].
split; [|exact H].
destruct HC' as [E | E]; [rewrite E; exact HC | right; exact E].
Qed.

Ltac cc_open cx Hpre Hcut :=
  unfold cls_pre in Hpre; cbv zeta in Hpre;
  destruct Hpre as (HJc & HROD & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & H14 & Hch & Hal & Hstk & Hsp & Htop &
    Hdep & Hlen & LFB & LU & LOB & HF & HUr & HUs & HUg & Ho & Ho4 & HOr & HOg & HOw & HOst & HL & HOU & HOF & HLsep);
  unfold cls_cut in Hcut; cbv zeta in Hcut;
  destruct Hcut as (J3 & Hfr3 & Hnin & Hperm3 & EF3 & EFL3 & HK3 & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R27 &
    HRV & HSp & Vo & Vf & VF & VLS & LSHP & GSHP & VFL & HPS & LO3 & GO3 & HL3);
  change (spZ (x_regs cx)) with (cSP cx) in *.

Lemma cc_S1 : forall cx, cSP cx mod 16 = 0 -> (cSP cx - 176 <= cS1 cx <= cSP cx - 160) /\ cS1 cx mod 32 = 0.
Proof.
intros cx H. unfold cS1, cls_S1.
pose proof (Z.div_mod (cSP cx - 160) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (cSP cx - 160) 32 ltac:(lia)) as M.
split; [lia | rewrite Z.mul_comm; apply Z_mod_mult].
Qed.

Lemma cc_awr_keep : forall STK sp0 FP ly S W0 mem0 md0 own ly3 S3 (W3 : world SEGS) mem3 md3 k (W2 : world SEGS) mem2 slo shi
  (Er : Z -> Prop) a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 mem3 md3 k ->
  tcallee_kept B ly3 S3 W3 mem3 W2 mem2 slo shi Er ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly3 S3) ly3 own a ->
  ~ (slo <= a < shi) -> ~ Er a ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 mem3 md3 k W2 mem2 slo shi Er a HJ HK Hw Hs He.
destruct HK as (K1 & K2 & _ & K4 & _).
destruct HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hlo & Hlo2 & Hhi & Hhi2 & _).
destruct Hw as [Hw | [(_ & b & n & Hin & Hr) | [(b & n & Hin & _ & Hr) | (cid & pos & Hin & Hr)]]].
- apply K1; [lia | exact Hs | exact He].
- replace a with (b + (a - b)) by lia.
  apply (K2 b n (a - b)); [exact Hin | lia | replace (b + (a - b)) with a by lia; exact He].
- replace a with (b + (a - b)) by lia.
  apply (K2 b n (a - b)); [exact Hin | lia | replace (b + (a - b)) with a by lia; exact He].
- apply (K4 cid pos a); [rewrite Hfrs; apply in_or_app; left; exact Hin | exact Hr | exact He].
Qed.

Lemma cc_kept : forall cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 (W2 : world SEGS) mem2 slo shi
  (Er : Z -> Prop),
  cls_pre B cx -> cls_cut B cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 ->
  cSP cx - CLS_STK <= slo -> shi <= cSP cx ->
  (forall a, Er a -> cF cx fpos <= a < cF cx fpos + 256) ->
  tcallee_kept B ly3 S3 W3 mem3 W2 mem2 slo shi Er ->
  tcls_kept B (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) W2 mem2 (cSP cx) (x_lk cx) (x_o cx) (x_L cx).
Proof.
intros cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 W2 mem2 slo shi Er Hpre Hcut Hslo Hshi HEr HKc.
pose proof (NOW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre Hcut) as HN. cbv zeta in HN.
destruct HN as ((HF0 & HFc & _ & _ & HFapp & _ & _ & _ & _ & _ & _ & _ & _ & Hbsep & Hfsep) & _).
cc_open cx Hpre Hcut.
pose proof HJc as (_ & HLc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstc & _).
pose proof J3 as (HAR3 & HL3y & _).
assert (EFA : forall c p, frame_addr (x_lyc cx) c p = frame_addr ly3 c p)
  by (intros c p; rewrite (cc_frame_addr _ _ c p (cc_lyF _ _ _ HLc)), (cc_frame_addr _ _ c p (cc_lyF _ _ _ HL3y)); reflexivity).
destruct Hstc as (_ & _ & Hlo & Hlo2 & Hhi & Hhi2 & _).
destruct HKc as (K1 & K2 & K3 & K4 & K5 & K6). destruct HK3 as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof alloc_ceiling_value as Hac.
unfold tcls_kept.
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw Hc. rewrite (K1 a Ha); [exact (C1 a Ha Hw Hc) | lia | intros He; apply HEr in He; lia].
- intros b m i Hin Hi Hc.
  assert (Hin3 : In (b, m) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm3 | exact Hin]).
  rewrite (K2 b m i Hin3 Hi); [exact (C2 b m i Hin Hi Hc) |].
  intros He. apply HEr in He. pose proof (Hbsep b m Hin3). lia.
- intros a Hi Hos Hes. rewrite (K3 a Hi Hos Hes). exact (C3 a Hi Hos Hes).
- intros cid pos a Hin Hr Hc.
  assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite Hfr3; right; exact Hin).
  assert (Hr3 : in_zr a (frame_rng ly3 (cid, pos)) \/
    in_zr a (shadow_addr (frame_addr ly3 cid pos), fs_frame_bytes cid / 8)).
  { unfold frame_rng in Hr |- *. cbn [fst snd] in Hr |- *. rewrite !EFA in Hr. exact Hr. }
  rewrite (K4 cid pos a Hin3 Hr3); [exact (C4 cid pos a Hin Hr Hc) |].
  intros He. apply HEr in He. unfold frame_rng in Hr3. cbn [fst snd] in Hr3.
  destruct Hr3 as [Hr3 | Hr3]; unfold in_zr in Hr3; cbn [fst snd] in Hr3.
  + pose proof (Hfsep cid pos Hin) as Hd. lia.
  + destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR3 Hin3) as (Hb0 & Hb1 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    clear - Hr3 He HFapp Hb0 Hb1 Hfs Hac.
    unfold shadow_addr, in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- intros a Ha Hw Hp. apply K5; [exact Ha | lia | exact (C5 a Ha Hw Hp)].
- intros a Ha. destruct (Z_le_gt_dec slo a) as [H1 | H1]; [destruct (Z_lt_ge_dec a shi) as [H2 | H2] |].
  + apply K6. lia.
  + apply K5; [lia | lia | exact (C6 a Ha)].
  + apply K5; [lia | lia | exact (C6 a Ha)].
Qed.

Lemma cc_keep : forall cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 (W2 : world SEGS) mem2 slo shi
  (Er : Z -> Prop) a,
  cls_pre B cx -> cls_cut B cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 ->
  tcallee_kept B ly3 S3 W3 mem3 W2 mem2 slo shi Er ->
  cSP cx - CLS_STK <= slo -> shi <= cS1 cx ->
  (forall x, Er x -> cF cx fpos <= x < cF cx fpos + 256) ->
  (cS1 cx <= a < cSP cx \/ (cF cx fpos <= a < cF cx fpos + 256 /\ ~ Er a) \/
   (SHADOW_OFF + cF cx fpos / 8 <= a < SHADOW_OFF + cF cx fpos / 8 + 32) \/
   cls_wr (x_lk cx) (x_o cx) (x_L cx) a) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a.
Proof.
intros cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 W2 mem2 slo shi Er a Hpre Hcut HKc Hslo Hshi HEr Ha.
pose proof (NOW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre Hcut) as HN. cbv zeta in HN.
destruct HN as ((HF0 & HFc & HFal & _ & HFapp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) & _ & _ & _ & HNo & HNo0 & HNoc & HNoaw & HNl).
cc_open cx Hpre Hcut.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstc & _).
destruct Hstc as (_ & _ & Hlo & Hlo2 & Hhi & Hhi2 & _).
pose proof alloc_ceiling_value as Hac.
pose proof (cc_S1 cx Hal) as ((HS1lo & HS1hi) & _).
pose proof cc_stk as (Est & Epn & _ & _ & HE0).
pose proof HKc as (K1 & K2 & _ & K4 & _).
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite Hfr3; left; reflexivity).
destruct Ha as [Ha | [[Ha He] | [Ha | Ha]]].
- apply K1; [lia | lia | intros He; apply HEr in He; lia].
- apply (K4 2 fpos a Hfin); [| exact He].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF3. change (fs_frame_bytes 2) with 256. lia.
- apply (K4 2 fpos a Hfin).
  + right. unfold in_zr. cbn [fst snd]. rewrite EF3. unfold shadow_addr. change (fs_frame_bytes 2 / 8) with 32. lia.
  + intros He. apply HEr in He. clear - Ha He HFapp HF0 Hac.
    unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- unfold cls_wr in Ha. destruct Ha as [Ha | Ha].
  + destruct HNo as (_ & _ & HoF & HoS).
    eapply cc_awr_keep; [exact J3 | exact HKc | exact (HNoaw a Ha) | lia | intros He; apply HEr in He; lia].
  + revert Ha HNl. destruct (x_L cx) as [Lb|]; intros Ha HNl; [|destruct Ha].
    destruct HNl as ((_ & _ & HlF & HlS) & _ & _ & HNlaw).
    eapply cc_awr_keep; [exact J3 | exact HKc | exact (HNlaw a Ha) | lia | intros He; apply HEr in He; lia].
Qed.

Lemma cc_cut : forall cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 pc' RV' PS' (W2 : world SEGS) ly2 S2 regs2
  mem2 md2 slo shi (Er : Z -> Prop),
  cls_pre B cx -> cls_cut B cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 ->
  ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) ->
  aregs_preserved regs3 regs2 -> frames S2 = frames S3 -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  tcallee_kept B ly3 S3 W3 mem3 W2 mem2 slo shi Er ->
  cSP cx - CLS_STK <= slo -> shi <= cS1 cx ->
  (forall x, Er x -> cF cx fpos <= x < cF cx fpos + 248) ->
  Forall (fun rv => getr regs2 (Z_to_bv 5 (fst rv)) = w64 (snd rv)) RV' ->
  (match PS' with
   | Some P => length P = 36%nat /\ garr8 SEGS (mrestrict (w_H W2) mem2) (cF cx fpos + 32) (cls_bytes P)
   | None => True end) ->
  cls_cut B cx fpos pc' RV' O3 L3 SHP PS' LS W2 ly2 S2 regs2 mem2 md2.
Proof.
intros cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 pc' RV' PS' W2 ly2 S2 regs2 mem2 md2 slo shi Er
  Hpre Hcut HJ2 HPR Hfr2 Hperm2 HKc Hslo Hshi HEr HRV' HPS'.
assert (HEr' : forall x, Er x -> cF cx fpos <= x < cF cx fpos + 256) by (intros x Hx; apply HEr in Hx; lia).
assert (HS1 : cS1 cx <= cSP cx).
{ pose proof Hpre as Hp'. unfold cls_pre in Hp'. cbv zeta in Hp'.
  destruct Hp' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal' & _).
  pose proof (cc_S1 cx Hal') as ((_ & Hh) & _). lia. }
assert (Hshi' : shi <= cSP cx) by lia.
pose proof (cc_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Er Hpre Hcut Hslo Hshi' HEr' HKc) as HKn.
assert (KP : forall a, (cS1 cx <= a < cSP cx \/ (cF cx fpos <= a < cF cx fpos + 256 /\ ~ Er a) \/
   (SHADOW_OFF + cF cx fpos / 8 <= a < SHADOW_OFF + cF cx fpos / 8 + 32) \/
   cls_wr (x_lk cx) (x_o cx) (x_L cx) a) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a)
  by (intros a Ha; exact (cc_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Er a Hpre Hcut HKc Hslo Hshi HEr' Ha)).
cc_open cx Hpre Hcut.
pose proof (cc_S1 cx Hal) as ((HS1lo & HS1hi) & _).
pose proof J3 as (_ & HL3y & _).
pose proof HJ2 as (_ & HL2y & _).
assert (EF23 : ly_F ly2 = ly_F ly3) by (rewrite (cc_lyF _ _ _ HL2y), (cc_lyF _ _ _ HL3y); reflexivity).
unfold cls_cut. cbv zeta.
split; [exact HJ2|].
split; [rewrite Hfr2; exact Hfr3|].
split; [exact Hnin|].
split; [eapply Permutation_trans; [exact Hperm2 | exact Hperm3]|].
split; [rewrite <- EF3; apply cc_frame_addr; exact EF23|].
split; [rewrite <- EFL3; apply cc_flag_addr; exact EF23|].
split; [exact HKn|].
split; [exact (cc_pres regs3 regs2 2 _ HPR ltac:(unfold acallee_saved; lia) R2)|].
split; [exact (cc_pres regs3 regs2 3 _ HPR ltac:(unfold acallee_saved; lia) R3)|].
split; [exact (cc_pres regs3 regs2 4 _ HPR ltac:(unfold acallee_saved; lia) R4)|].
split; [exact (cc_pres regs3 regs2 8 _ HPR ltac:(unfold acallee_saved; lia) R8)|].
split; [exact (cc_pres regs3 regs2 9 _ HPR ltac:(unfold acallee_saved; lia) R9)|].
split; [exact (cc_pres regs3 regs2 18 _ HPR ltac:(unfold acallee_saved; lia) R18)|].
split; [exact (cc_pres regs3 regs2 19 _ HPR ltac:(unfold acallee_saved; lia) R19)|].
split; [exact (cc_pres regs3 regs2 20 _ HPR ltac:(unfold acallee_saved; lia) R20)|].
split; [exact (cc_pres regs3 regs2 27 _ HPR ltac:(unfold acallee_saved; lia) R27)|].
split; [exact HRV'|].
split.
{ apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) HSp p Hp) as Hv. cbv beta in Hv |- *.
  assert (Hb : -104 <= snd p <= -8)
    by (unfold cls_spills in Hp; cbn [In] in Hp; repeat (destruct Hp as [<- | Hp]; [cbn [snd]; lia|]); destruct Hp).
  eapply YC88.val_mem_aview_kept_x; [|exact Hv]. intros x Hx. apply KP. left.
  change (Z.of_nat 8) with 8 in Hx. lia. }
split; [eapply YC88.val_mem_aview_kept_x; [|exact Vo]; intros x Hx; apply KP; left; change (Z.of_nat 8) with 8 in Hx; lia|].
split; [eapply YC88.val_mem_aview_kept_x; [|exact Vf]; intros x Hx; apply KP; left; change (Z.of_nat 8) with 8 in Hx; lia|].
split; [eapply YC88.val_mem_aview_kept_x; [|exact VF]; intros x Hx; apply KP; left; change (Z.of_nat 8) with 8 in Hx; lia|].
split; [intros HLS; eapply YC88.val_mem_aview_kept_x; [|exact (VLS HLS)]; intros x Hx; apply KP; left;
  change (Z.of_nat 8) with 8 in Hx; lia|].
split; [exact LSHP|].
split.
{ eapply YC88.garr8_aview_kept; [|exact GSHP]. intros x Hx. apply KP. right. right. left.
  rewrite LSHP in Hx. change (Z.of_nat 32) with 32 in Hx. exact Hx. }
split.
{ eapply YC88.val_mem_aview_kept_x; [|exact VFL]. intros x Hx. apply KP. right. left.
  change (Z.of_nat 8) with 8 in Hx. split; [lia | intros He; apply HEr in He; lia]. }
split; [exact HPS'|].
split; [exact LO3|].
split.
{ eapply YC88.garr8_aview_kept; [|exact GO3]. intros x Hx. apply KP. right. right. right. unfold cls_wr. left.
  unfold cls_bytes in Hx. rewrite length_map, LO3 in Hx. change (Z.of_nat 24) with 24 in Hx. exact Hx. }
revert HL3. destruct (x_L cx) as [Lb|] eqn:EL; destruct L3 as [L3b|]; intros HL3; try exact I; try contradiction.
destruct HL3 as (HL3l & HL3g). split; [exact HL3l|].
eapply YC88.garr8_aview_kept; [|exact HL3g]. intros x Hx. apply KP. right. right. right. unfold cls_wr. right. try rewrite EL.
unfold cls_bytes in Hx. rewrite length_map, HL3l in Hx. change (Z.of_nat 12) with 12 in Hx. exact Hx.
Qed.

Lemma cc_common : forall cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3,
  cls_pre B cx -> cls_cut B cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 ->
  ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 mem3 md3 (x_k cx) /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem3) /\
  getr regs3 3 = w64 (as_gp B) /\ getr regs3 4 = w64 (as_tp B) /\
  spZ regs3 = cS1 cx /\ s0Z regs3 = cSP cx /\
  cS1 cx mod 32 = 0 /\ cSP cx - 176 <= cS1 cx /\ cS1 cx <= cSP cx - 160 /\
  x_sp0 cx - x_STK cx <= cSP cx - CLS_STK /\ cSP cx <= x_sp0 cx /\
  alloc_ceiling <= x_sp0 cx - x_STK cx /\ x_sp0 cx <= 2 ^ 47 /\
  cS1 cx + 32 <= ly_top ly3 /\
  Z.of_nat (length (frames S3)) <= CLS_DEPTH + 1 /\
  (exists ch, achain ly3 (aview SEGS (w_H W3) mem3) (spZ regs3) (s0Z regs3) ch) /\
  0 <= x_len cx < 2 ^ 64 /\ length (x_FB cx) = 50%nat /\
  (50 <= x_len cx -> 0 < x_f cx) /\
  Forall (fun rv => getr regs3 (Z_to_bv 5 (fst rv)) = w64 (snd rv)) RV /\
  frame_addr ly3 2 fpos = cF cx fpos /\
  garr8 SEGS (mrestrict (w_H W3) mem3) (SHADOW_OFF + cF cx fpos / 8) SHP /\ length SHP = 32%nat /\
  (match PS with
   | Some P => length P = 36%nat /\ garr8 SEGS (mrestrict (w_H W3) mem3) (cF cx fpos + 32) (cls_bytes P)
   | None => True end).
Proof.
intros cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 Hpre Hcut.
destruct (ACH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre Hcut) as (ch & Hch3).
cc_open cx Hpre Hcut.
pose proof (cc_S1 cx Hal) as ((HS1lo & HS1hi) & HS1a).
pose proof HJc as (_ & HLc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstc & _).
pose proof J3 as (_ & HL3y & _).
destruct Hstc as (_ & _ & Hlo & Hlo2 & Hhi & Hhi2 & _).
pose proof cc_stk as (Est & Epn & _ & _ & HE0).
pose proof alloc_ceiling_value as Hac.
assert (Esp : spZ regs3 = cS1 cx) by (unfold spZ; rewrite R2; unfold w64; apply YP03.unsigned_lit_small; lia).
assert (Es0 : s0Z regs3 = cSP cx) by (unfold s0Z; rewrite R8; unfold w64; apply YP03.unsigned_lit_small; lia).
split; [exact J3|].
split; [exact (cc_rod B _ _ _ _ HROD (proj1 (proj2 (proj2 HK3))))|].
split; [rewrite R3; exact Hgp|].
split; [rewrite R4; exact Htp|].
split; [exact Esp|]. split; [exact Es0|].
split; [exact HS1a|]. split; [lia|]. split; [lia|].
split; [exact Hstk|]. split; [exact Hsp|].
split; [lia|]. split; [lia|].
split; [rewrite (cc_top _ _ _ HL3y), <- (cc_top _ _ _ HLc); lia|].
split; [rewrite Hfr3; cbn [length]; lia|].
split; [exists ch; rewrite Esp, Es0; exact Hch3|].
split; [exact Hlen|]. split; [exact LFB|].
split; [intros H50; exact (proj1 (HF H50))|].
split; [exact HRV|]. split; [exact EF3|]. split; [exact GSHP|]. split; [exact LSHP|]. exact HPS.
Qed.

Lemma cc_awrF : forall cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3,
  cls_pre B cx -> cls_cut B cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 ->
  forall a, cF cx fpos <= a < cF cx fpos + 256 ->
  awr_byte (x_STK cx) (x_sp0 cx) (x_FP cx) (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly3 S3) ly3 ((2, fpos) :: x_own cx) a /\
  apresent (w_H W3) mem3 a.
Proof.
intros cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 Hpre Hcut a Ha.
pose proof (NOW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre Hcut) as HN. cbv zeta in HN.
destruct HN as ((_ & _ & _ & _ & _ & HFpres & _) & _).
split; [|exact (HFpres a Ha)].
unfold cls_cut in Hcut. cbv zeta in Hcut. destruct Hcut as (_ & _ & _ & _ & EF3 & _).
right. right. right. exists 2, fpos. split; [left; reflexivity|]. left.
unfold in_zr. cbn [fst snd]. rewrite EF3. change (fs_frame_bytes 2) with 256. exact Ha.
Qed.

Lemma cc_f_sep : forall cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3,
  cls_pre B cx -> cls_cut B cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 ->
  50 <= x_len cx -> cls_sep B ly3 S3 (x_f cx) 50.
Proof.
intros cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 Hpre Hcut H50.
cc_open cx Hpre Hcut.
pose proof HJc as (_ & HLc & _). pose proof J3 as (_ & HL3y & _).
destruct HLc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eloc & Ehic & _).
destruct HL3y as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo3 & Ehi3 & _).
destruct (HF H50) as (_ & _ & Hsep & _).
unfold cls_sep.
destruct Hsep as [(cid & pos & Hin & H1 & H2) | [(b & m & Hin & H1 & H2) | (H1 & H2)]].
- assert (EF : frame_addr ly3 cid pos = frame_addr (x_lyc cx) cid pos) by (unfold cF, frame_addr in EF3 |- *; lia).
  left. exists cid, pos. rewrite EF.
  split; [rewrite Hfr3; right; exact Hin|]. split; lia.
- right; left. exists b, m.
  split; [eapply Permutation_in; [apply Permutation_sym; exact Hperm3 | exact Hin]|]. split; lia.
- right; right. split; lia.
Qed.

Theorem cls_call_P : tparse_need B -> cls_from_R1 B -> cls_from_P B.
Proof.
intros TP HR1. unfold cls_from_P, cls_from. intros cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre HP.
unfold cls_at_P in HP. cbv zeta in HP.
pose proof (NOW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre HP) as HN. cbv zeta in HN.
destruct HN as ((HF0 & HFc & HFal & HFz & HFapp & _) & HNf & _).
destruct (cc_common _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre HP) as (J3 & HROD3 & Hgp3 & Htp3 & Esp & Es0 & HS1a & HS1lo &
  HS1hi & Hstk & Hsp & Hlo & Hhi & Htop3 & Hdep3 & (ch & Hch3) & Hlen & LFB & Hf0 & HRV & EF3 & GSHP & LSHP & HPS).
pose proof cc_stk as (Est & Epn & _ & _ & HE0).
pose proof alloc_ceiling_lt as Hac47.
pose proof (cc_awrF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre HP) as HFw.
assert (Hr1 : getr regs3 1 = w64 (BASE + PC_R1)) by exact (cc_rv regs3 _ 1 (BASE + PC_R1) HRV ltac:(cc_in)).
destruct (cc_ra regs3 PC_R1 Hr1 ltac:(unfold PC_R1, AF_both3_classify_core; lia) ltac:(reflexivity)) as (Hret & Era).
destruct (cc_qaddr (cF cx fpos) 32 36 HFapp HFz HFc ltac:(lia) ltac:(lia) ltac:(lia)) as (Hq47 & Hqam & Hqoi & Hqband).
eapply SRr_bind.
{ apply (TP (x_fq cx) (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 mem3 md3 (x_k cx) regs3 ch (x_f cx) (x_len cx) (cF cx fpos + 32) (x_FB cx)).
  - exact J3.
  - exact HROD3.
  - exact Hret.
  - rewrite Era. pose proof (@pa_B_ok _ _ PI) as (HB0 & _). unfold PC_R1, AF_both3_classify_core. lia.
  - exact Hgp3.
  - exact Htp3.
  - exact (cc_rv regs3 _ 10 (x_f cx) HRV ltac:(cc_in)).
  - exact (cc_rv regs3 _ 11 (x_len cx) HRV ltac:(cc_in)).
  - exact (cc_rv regs3 _ 12 (cF cx fpos + 32) HRV ltac:(cc_in)).
  - exact Hch3.
  - rewrite Esp. lia.
  - rewrite Esp. lia.
  - rewrite Esp. lia.
  - rewrite Esp. exact Htop3.
  - exact Hdep3.
  - exact Hlen.
  - exact LFB.
  - intros H50. destruct (HNf H50) as (Gf & (Hfa0 & Hfa1 & Hfam & Hfoi & Hfband) & (Hfpr & Hfra & Hfhv) & HfF & HfS).
    rewrite Esp.
    split; [exact (Hf0 H50)|]. split; [exact Hfa1|]. split; [exact Hfam|]. split; [exact Hfoi|].
    split; [exact Hfband|]. split; [lia|]. split; [exact Hfpr|].
    split; [exact (cc_f_sep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre HP H50)|].
    split; [exact Hfra|]. split; [exact Hfhv|].
    split; [exact Gf|]. lia.
  - lia.
  - lia.
  - exact Hq47.
  - exact Hqam.
  - exact Hqoi.
  - exact Hqband.
  - lia.
  - apply (cc_ra_sh W3 mem3 (cF cx fpos) PAT_A 32 36 HFal LSHP GSHP ltac:(lia) ltac:(lia) ltac:(lia)).
    intros x Hx. exact (cc_patA (cF cx fpos) x HFal Hx).
  - exact (cc_hull W3 mem3 (cF cx fpos) PAT_A 32 36 HFal LSHP GSHP ltac:(lia) ltac:(lia) ltac:(lia)).
  - intros a Ha. exact (HFw a ltac:(lia)). }
intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hc & Hfxr & Hfxc & HJ2 & HPR & Hfr2 & Hperm2 & Ha0 & Hq & HKc).
subst c2. rewrite Hr1.
eapply SRr_mono; [|intros W4 c4 _ HQ4; exact (tcls_post_fp cx fx' W4 c4 Hfxr Hfxc HQ4)].
change (SRr SEGS W2 (cfg_at (fx := fx') SEGS (BASE + PC_R1) regs2 mem2 md2) (cls_Q B (cls_setfq cx fx'))).
apply (HR1 (cls_setfq cx fx') fpos W2 ly2 S2 regs2 mem2 md2 Hpre).
change (cls_at_R1 B cx fpos W2 ly2 S2 regs2 mem2 md2).
unfold cls_at_R1. cbv zeta.
eapply cc_cut; [exact Hpre | exact HP | exact HJ2 | exact HPR | exact Hfr2 | exact Hperm2 | exact HKc | | | | | ].
- rewrite Esp. lia.
- rewrite Esp. lia.
- intros x Hx. cbv beta in Hx. lia.
- apply Forall_cons; [exact Ha0|].
  repeat (apply Forall_cons; [cbn [fst snd]; eapply cc_pres;
    [exact HPR | unfold acallee_saved; lia | apply (cc_rv regs3 _ _ _ HRV); cc_in] |]).
  apply Forall_nil.
- split; [exact (RcParse.ctrlparse_length (x_len cx) (x_FB cx)) | exact Hq].
Qed.

Theorem cls_call_K : tchk_need B -> cls_from_R2 B -> cls_from_K B.
Proof.
intros TC HR2. unfold cls_from_K, cls_from. intros cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre HK.
unfold cls_at_K in HK. cbv zeta in HK. destruct HK as (HK0 & HK1 & HKe & HP).
pose proof (NOW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre HP) as HN. cbv zeta in HN.
destruct HN as ((HF0 & HFc & HFal & HFz & HFapp & _) & HNf & _).
destruct (cc_common _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre HP) as (J3 & HROD3 & Hgp3 & Htp3 & Esp & Es0 & HS1a & HS1lo &
  HS1hi & Hstk & Hsp & Hlo & Hhi & Htop3 & Hdep3 & (ch & Hch3) & Hlen & LFB & Hf0 & HRV & EF3 & GSHP & LSHP & HPS).
pose proof cc_stk as (Est & Epn & Ecn & _ & HE0).
assert (H50 : 50 <= x_len cx).
{ destruct (Z_le_gt_dec 50 (x_len cx)) as [H | H]; [exact H|]. exfalso. apply HK0.
  unfold cK, disco_classify_c.dkind. apply (proj2 (RcParse.ctrlparse_none _ _)). intros (Hc & _). lia. }
destruct (HNf H50) as (Gf & (Hfa0 & Hfa1 & Hfam & Hfoi & Hfband) & (Hfpr & Hfra & Hfhv) & HfF & HfS).
assert (Hr1 : getr regs3 1 = w64 (BASE + PC_R2)) by exact (cc_rv regs3 _ 1 (BASE + PC_R2) HRV ltac:(cc_in)).
destruct (cc_ra regs3 PC_R2 Hr1 ltac:(unfold PC_R2, AF_both3_classify_core; lia) ltac:(reflexivity)) as (Hret & Era).
eapply SRr_bind.
{ apply (TC (x_fq cx) (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 mem3 md3 (x_k cx) regs3 ch (x_f cx) (x_FB cx)).
  - exact J3.
  - exact HROD3.
  - exact Hret.
  - rewrite Era. pose proof (@pa_B_ok _ _ PI) as (HB0 & _). unfold PC_R2, AF_both3_classify_core. lia.
  - exact Hgp3.
  - exact Htp3.
  - exact (cc_rv regs3 _ 10 (x_f cx) HRV ltac:(cc_in)).
  - exact Hch3.
  - rewrite Esp. lia.
  - rewrite Esp. lia.
  - rewrite Esp. lia.
  - exact LFB.
  - exact (Hf0 H50).
  - exact Hfa1.
  - exact Hfam.
  - exact Hfoi.
  - exact Hfband.
  - rewrite Esp. lia.
  - exact Hfpr.
  - exact Hfra.
  - exact Hfhv.
  - exact Gf. }
intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hc & Hfxr & Hfxc & HJ2 & HPR & Hfr2 & Hperm2 & Ha0 & HKc).
subst c2. rewrite Hr1.
eapply SRr_mono; [|intros W4 c4 _ HQ4; exact (tcls_post_fp cx fx' W4 c4 Hfxr Hfxc HQ4)].
change (SRr SEGS W2 (cfg_at (fx := fx') SEGS (BASE + PC_R2) regs2 mem2 md2) (cls_Q B (cls_setfq cx fx'))).
apply (HR2 (cls_setfq cx fx') fpos W2 ly2 S2 regs2 mem2 md2 Hpre).
change (cls_at_R2 B cx fpos W2 ly2 S2 regs2 mem2 md2).
unfold cls_at_R2. cbv zeta.
split; [exact HK0|]. split; [exact HK1|]. split; [exact HKe|].
destruct HPS as (LPS & GPS).
eapply cc_cut; [exact Hpre | exact HP | exact HJ2 | exact HPR | exact Hfr2 | exact Hperm2 | exact HKc | | | | | ].
- rewrite Esp. lia.
- rewrite Esp. lia.
- intros x Hx. destruct Hx.
- apply Forall_cons; [exact Ha0|].
  repeat (apply Forall_cons; [cbn [fst snd]; eapply cc_pres;
    [exact HPR | unfold acallee_saved; lia | apply (cc_rv regs3 _ _ _ HRV); cc_in] |]).
  apply Forall_nil.
- split; [exact LPS|].
  eapply YC88.garr8_aview_kept; [|exact GPS]. intros a Ha.
  unfold cls_bytes in Ha. rewrite length_map, LPS in Ha. change (Z.of_nat 36) with 36 in Ha.
  eapply cc_keep; [exact Hpre | exact HP | exact HKc | rewrite Esp; lia | rewrite Esp; lia | intros x Hx; destruct Hx |].
  right. left. split; [lia | intros Hx; destruct Hx].
Qed.

Theorem cls_call_Q : treac_ports_parse_spec B -> cls_from_R3 B -> cls_from_Q B.
Proof.
intros TQ HR3. unfold cls_from_Q, cls_from. intros cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre HQ.
unfold cls_at_Q in HQ. cbv zeta in HQ. destruct HQ as (Hret0 & HP).
pose proof (NOW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre HP) as HN. cbv zeta in HN.
destruct HN as ((HF0 & HFc & HFal & HFz & HFapp & _) & HNf & _).
destruct (cc_common _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre HP) as (J3 & HROD3 & Hgp3 & Htp3 & Esp & Es0 & HS1a & HS1lo &
  HS1hi & Hstk & Hsp & Hlo & Hhi & Htop3 & Hdep3 & (ch & Hch3) & Hlen & LFB & Hf0 & HRV & EF3 & GSHP & LSHP & HPS).
pose proof cc_stk as (Est & Epn & _ & Epp & HE0).
pose proof alloc_ceiling_lt as Hac47.
pose proof (cc_awrF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre HP) as HFw.
assert (HK0 : cK cx <> 0).
{ intros E. unfold cRet, disco_classify_c.cm_ret, disco_classify_c.classify_model in Hret0. cbv zeta in Hret0.
  unfold cK in E. rewrite E in Hret0. cbn [Z.eqb fst] in Hret0. discriminate Hret0. }
assert (H50 : 50 <= x_len cx).
{ destruct (Z_le_gt_dec 50 (x_len cx)) as [H | H]; [exact H|]. exfalso. apply HK0.
  unfold cK, disco_classify_c.dkind. apply (proj2 (RcParse.ctrlparse_none _ _)). intros (Hc & _). lia. }
destruct (HNf H50) as (Gf & (Hfa0 & Hfa1 & Hfam & Hfoi & Hfband) & (Hfpr & Hfra & Hfhv) & HfF & HfS).
assert (Gp : garr8 SEGS (mrestrict (w_H W3) mem3) (x_f cx + 18) (map (fun b : byte => bv_unsigned b) (cBS cx))).
{ pose proof (YC88.garr8_sub_x SEGS _ _ _ 18 20 Gf ltac:(unfold cls_bytes; rewrite length_map, LFB; lia)) as G.
  unfold cls_bytes in G. rewrite skipn_map, firstn_map in G. exact G. }
assert (Hr1 : getr regs3 1 = w64 (BASE + PC_R3)) by exact (cc_rv regs3 _ 1 (BASE + PC_R3) HRV ltac:(cc_in)).
destruct (cc_ra regs3 PC_R3 Hr1 ltac:(unfold PC_R3, AF_both3_classify_core; lia) ltac:(reflexivity)) as (Hret & Era).
destruct (cc_qaddr (cF cx fpos) 112 12 HFapp HFz HFc ltac:(lia) ltac:(lia) ltac:(lia)) as (Hq47 & _ & _ & Hqband).
eapply SRr_bind.
{ apply (TQ (x_fq cx) (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 mem3 md3 (x_k cx) regs3 ch (x_f cx + 18) (cF cx fpos + 112) (cBS cx)).
  - exact J3.
  - exact HROD3.
  - exact Hret.
  - rewrite Era. pose proof (@pa_B_ok _ _ PI) as (HB0 & _). unfold PC_R3, AF_both3_classify_core. lia.
  - exact Hgp3.
  - exact Htp3.
  - exact (cc_rv regs3 _ 10 (x_f cx + 18) HRV ltac:(cc_in)).
  - exact (cc_rv regs3 _ 11 (cF cx fpos + 112) HRV ltac:(cc_in)).
  - lia.
  - lia.
  - exact Hch3.
  - rewrite Esp. lia.
  - rewrite Esp. lia.
  - rewrite Esp. lia.
  - lia.
  - rewrite Esp. right. lia.
  - intros _ _.
    split; [unfold cBS, CtrlParsed.fld; rewrite length_firstn, length_skipn, LFB; reflexivity|].
    split; [lia|].
    split; [unfold off_img in *; lia|].
    split; [lia|].
    split; [rewrite Esp; lia|].
    split; [eapply range_addressable_sub; [exact Hfra | lia | lia]|].
    split; [intros a Ha; apply Hfpr; lia|].
    split; [exact Gp|].
    split; [lia|].
    split; [lia|].
    split; [exact Hqband|].
    split; [apply (cc_ra_sh W3 mem3 (cF cx fpos) PAT_B 112 12 HFal LSHP GSHP ltac:(lia) ltac:(lia) ltac:(lia));
      intros x Hx; exact (cc_patB (cF cx fpos) x HFal Hx)|].
    intros a Ha. exact (HFw a ltac:(lia)). }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & HPR & Hfr2 & Hperm2 & Ha0 & P1 & P2 & P3 & P4 & P5 & P6 & Pok).
assert (HKc : tcallee_kept B ly3 S3 W3 mem3 W2 mem2 (spZ regs3 - REAC_PORTS_PARSE_STK) (spZ regs3)
  (fun a => cF cx fpos + 112 <= a < cF cx fpos + 112 + 12))
  by exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 P6))))).
subst c2. rewrite Hr1.
change (SRr SEGS W2 (cfg_at (fx := x_fq cx) SEGS (BASE + PC_R3) regs2 mem2 md2) (cls_Q B cx)).
apply (HR3 cx fpos W2 ly2 S2 regs2 mem2 md2 Hpre).
unfold cls_at_R3. cbv zeta.
split; [exact Hret0|]. split.
- eapply cc_cut; [exact Hpre | exact HP | exact HJ2 | exact HPR | exact Hfr2 | exact Hperm2 | exact HKc | | | | | ].
  + rewrite Esp. lia.
  + rewrite Esp. lia.
  + intros x Hx. cbv beta in Hx. lia.
  + apply Forall_cons; [exact Ha0|].
    repeat (apply Forall_cons; [cbn [fst snd]; eapply cc_pres;
      [exact HPR | unfold acallee_saved; lia | apply (cc_rv regs3 _ _ _ HRV); cc_in] |]).
    apply Forall_nil.
  + exact I.
- intros Hok. rewrite Hok in Pok. destruct Pok as (V1 & V2 & _). split; [exact V1|].
  replace (cF cx fpos + 116) with (cF cx fpos + 112 + 4) by lia. exact V2.
Qed.

End h.
End f.
End d.
