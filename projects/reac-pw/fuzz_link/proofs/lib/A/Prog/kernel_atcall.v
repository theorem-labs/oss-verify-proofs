(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v; 294 of its 360 lines of code are new or changed and 420 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: kernel's call of attr_text (0x86b18 = kernel 0x83d30 + 0x2de8) from a cut of the
   walk: at +0xb40 (the attribute cases a % 6 in {0, 1, 4} and the empty cursor's, kernel_a014.v) and at +0xdc8 (the
   nest of cases 2, 3). Listing (internal path) (internal record, sha256 7bc02d6772b3).
   - `kn_atcall`: kernel_ocall.v's kn_ocall at attr_text's aleaf_rd contract (ATEXT), from a cut at attr_text's
     entry (KP_ATEXT, after the `jal`): attr_text's Pre from the cut (w2 from kw_at and F's shadow, as
     kernel_k12_call.v builds nl_error's) and from `katstr` (the string a2 at the current state, its slack, its
     shadow facts, its separation from kernel's frame, and its bytes in kernel's read set); the Pre's read set (the
     string) is akb at attr_text's window [s1 - 4160, s1) by kbase's read-set premise and LinkWalkCall.v akb_sub.
   - `katstr_img`: katstr of a string of kernel_img.v's ki_strs (.str.1, .str.8, the eleven texts' strings) from
     ktext (kernel_str at the call) and the read set's coverage: the bytes at the cut from KernImg (kkept's
     arodata_okP), the slack visible (ki_vis), the shadow facts moved from the call (LinkWalkShadow.v
     shadow_transport_akb over kkept's akept).
   Section hypotheses: LAWS : AR_laws pa_segs B; LV : LinkVals; KI : KernImg pa_segs B (kernel_img_tfib.v
   kernel_img_syms); TB : PcapSyms B (AF0m.v; AD2l.PcapB_syms); ATEXT : attr_text_acontract SK pa_segs PCAP_RLO
   PCAP_RHI B (discharged by attr_text.v attr_text_aproof).
   Released proofs (rule 24): this proves no function (kind: segment lemma of kernel's walk); the walk of kernel had
   its search (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by the rule-24 walk check at 14:56Z).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
PcapRelro kernel_c kernel_img kernel_defs kernel_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import attr_text_c LinkWalkCall kernel_ocall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* attr_text's entry as a kernel offset: 0x86b18 - 0x83d30 *)
Definition KP_ATEXT : Z := 0x2de8.

(* ---- bytes ---- *)
Lemma kac_zb_unsigned : forall b : byte, zb (bv_unsigned b) = b.
Proof.
  intros b. unfold zb. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma kac_zb0 : forall x, 0 <= x < 256 -> zb x = zb 0 -> x = 0.
Proof.
  intros x Hx H. unfold zb in H. apply (f_equal bv_unsigned) in H.
  rewrite !Z_to_bv_unsigned in H. unfold bv_wrap, bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. rewrite (Z.mod_small x 256 Hx) in H. exact H.
Qed.

(* the strings of ki_strs: their bytes and NUL, and where they lie *)
Lemma ki_strs_shape : forall p bs, In (p, bs) ki_strs ->
  bs = removelast bs ++ [0] /\ Forall (fun z => 0 < z < 256) (removelast bs) /\
  0x20fc0 <= p /\ p + Z.of_nat (length bs) <= 0x21230.
Proof.
  intros p bs H. unfold ki_strs in H. cbn [In] in H.
  repeat (destruct H as [H|H];
    [injection H as <- <-; cbn [removelast length];
     split; [reflexivity|]; split; [repeat (apply Forall_cons; [lia|]); apply Forall_nil | lia] |]).
  destruct H.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis KI : KernImg pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis ATEXT : attr_text_acontract SK pa_segs PCAP_RLO PCAP_RHI B.

(* a string kernel hands attr_text as a2, at the cut of the call *)
Definition katstr (cx : kcx) (W3 : world SEGS) (ms3 : machine_state) (p : Z) (s : list byte) : Prop :=
  0 < p /\ acstr_at SEGS (rdW W3 (ms_mem ms3)) p s /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\
  (exists slack, abytes SEGS (rdW W3 (ms_mem ms3)) (p + Z.of_nat (length s) + 1) slack /\
     (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)) /\
  amem_range p (Z.of_nat (length s) + 1) /\
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF p (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms3)) p (Z.of_nat (length s) + 1) /\
  apart_frame (k_regs cx) KERNEL_AK p (Z.of_nat (length s) + 1) /\
  (forall a, p <= a <= p + Z.of_nat (length s) -> kernel_ard SEGS (k_regs cx) (km0 cx) a).

(* two C strings at one address have one length *)
Lemma kac_cstr_len : forall m p s s', acstr_at SEGS m p s -> acstr_at SEGS m p s' -> length s = length s'.
Proof.
  intros m p s s' ((_ & _ & H1) & N1) ((_ & _ & H2) & N2).
  destruct (Nat.lt_trichotomy (length s) (length s')) as [Hl | [Hl | Hl]]; [exfalso | exact Hl | exfalso].
  - pose proof (H1 (length s) ltac:(rewrite length_app; cbn [length]; lia)) as A.
    pose proof (H2 (length s) ltac:(rewrite length_app; cbn [length]; lia)) as Bq.
    rewrite A in Bq. rewrite nth_error_app2 in Bq by lia. rewrite Nat.sub_diag in Bq. cbn [nth_error] in Bq.
    rewrite nth_error_app1 in Bq by lia. symmetry in Bq. apply nth_error_In in Bq. exact (N2 Bq).
  - pose proof (H1 (length s') ltac:(rewrite length_app; cbn [length]; lia)) as A.
    pose proof (H2 (length s') ltac:(rewrite length_app; cbn [length]; lia)) as Bq.
    rewrite Bq in A. rewrite nth_error_app2 in A by lia. rewrite Nat.sub_diag in A. cbn [nth_error] in A.
    rewrite nth_error_app1 in A by lia. symmetry in A. apply nth_error_In in A. exact (N1 A).
Qed.

Lemma kac_mbyte_of_view : forall H m a v, aview SEGS H m a = Some v -> mbyte SEGS (mrestrict H m) a = Some (zb v).
Proof.
  intros H m a v E. unfold aview in E.
  destruct (mbyte SEGS (mrestrict H m) a) as [b|]; cbn [option_map] in E; [|discriminate].
  injection E as <-. rewrite kac_zb_unsigned. reflexivity.
Qed.

(* the string of a ki_strs entry, at any state whose read-only view is the image's *)
Lemma kac_cstr_ro : forall H m p bs, arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS H m) ->
  In (p, bs) ki_strs -> acstr_at SEGS (mrestrict H m) p (map zb (removelast bs)).
Proof.
  intros H m p bs HRO Hin. destruct (ki_strs_shape p bs Hin) as (Ebs & Hz & Hp1 & Hp2).
  pose proof (ki_str_rd SEGS PCAP_RLO PCAP_RHI B KI H m HRO p bs Hin) as R.
  remember (removelast bs) as zs eqn:Ezs. clear Ezs. rewrite Ebs in R, Hp2. clear Ebs Hin.
  rewrite length_app in Hp2. cbn [length] in Hp2.
  split.
  - split; [lia|]. split; [rewrite length_app, length_map; cbn [length]; lia|].
    intros i Hi. rewrite length_app, length_map in Hi. cbn [length] in Hi.
    rewrite (kac_mbyte_of_view H m _ _ (R i ltac:(rewrite length_app; cbn [length]; lia))).
    replace (map zb zs ++ [zb 0]) with (map zb (zs ++ [0])) by (rewrite map_app; reflexivity).
    rewrite nth_error_map, (nth_error_nth' (zs ++ [0]) 0) by (rewrite length_app; cbn [length]; lia).
    reflexivity.
  - intros Hc. apply in_map_iff in Hc as (z & Hzb & Hzi).
    rewrite Forall_forall in Hz. pose proof (Hz z Hzi) as Hzr.
    pose proof (kac_zb0 z ltac:(lia) Hzb). lia.
Qed.

(* the stack rows, the frames' addresses and the blocks of a cut, against the call's *)
Lemma kac_row : forall cx fpos k2 ly3 S3 W3 mm md3,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mm md3 k2 ->
  ly_stk_lo ly3 = ly_stk_lo (k_lyc cx) /\ ly_stk_hi ly3 = ly_stk_hi (k_lyc cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 mm md3 HB HJ. pose proof HB as ((HJ0 & _) & _).
  destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (A1 & A2).
  destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as (B1 & B2).
  split; congruence.
Qed.

Lemma kac_fa : forall cx fpos k2 ly3 S3 W3 mm md3,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mm md3 k2 ->
  forall c q, frame_addr ly3 c q = frame_addr (k_lyc cx) c q.
Proof.
  intros cx fpos k2 ly3 S3 W3 mm md3 HB HJ c q. pose proof HB as ((HJ0 & _) & _).
  rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ)).
  rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ0)).
  reflexivity.
Qed.

(* a range of kernel's read set: its shadow facts at the call hold at a cut *)
Lemma kac_sh_now : forall cx fpos k2 ly3 S3 W3 ms3 md3 x n,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 -> kkept B cx fpos W3 ms3 -> 0 < n ->
  (forall a, x <= a < x + n -> kernel_ard SEGS (k_regs cx) (km0 cx) a) ->
  range_addressable (ard SEGS (km0 cx)) SHADOW_OFF x n -> shadow_hull_vis (ard SEGS (km0 cx)) x n ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF x n /\
  shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms3)) x n.
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 x n HB HJ Hjb Hkk Hn Hcov HR HH.
  pose proof HB as (HPRE & HRD & _). pose proof HPRE as (HJ0 & _).
  pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (HAR0 & _).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR3 & _).
  destruct (kac_row cx fpos k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ) as (Elo & Ehi).
  pose proof Hjb as (_ & _ & Hperm & Hnin & (S1 & W1 & mem1 & md1 & HAR1 & HF1 & _) & _).
  assert (Hin1 : In (KN_CID, fpos) (frames S1)) by (rewrite HF1; left; reflexivity).
  pose proof HAR1 as (M1 & _).
  destruct (frame_facts B _ _ _ KN_CID fpos M1 Hin1) as (_ & Hpos & _).
  destruct Hkk as (Hak & _).
  apply (shadow_transport_akb SEGS B LAWS TB (ki_segs_img SEGS B KI) (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx)
    (k_mdc cx) ly3 S3 W3 (ms_mem ms3) md3 (ksp cx - KERNEL_AK) (ksp cx)
    (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a) x n HAR0 HAR3 Elo Ehi);
    [ | exact Hak | | exact Hn | | exact HR | exact HH].
  - intros b m Hbm. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hbm.
  - apply fmiss_or.
    + apply (fmiss_app SEGS B LAWS _ _ _ _ _ _ HAR0). intros a Ha.
      destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 a HB Hjb (kn_kE_ard cx a Ha)) as (_ & Happ & _).
      exact Happ.
    + apply (fmiss_side SEGS B _ _ _ _ _ KN_CID fpos HAR0); [unfold KN_CID; lia | exact Hpos | exact Hnin].
  - intros a Ha. exact (HRD a (Hcov a Ha)).
Qed.

(* katstr of a string of ki_strs, from kernel_str at the call and the read set's coverage *)
Lemma katstr_img : forall cx fpos k2 ly3 S3 W3 ms3 md3 p bs,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 -> kkept B cx fpos W3 ms3 ->
  In (p, bs) ki_strs -> ktext cx p ->
  (forall s, acstr_at SEGS (km0 cx) p s -> forall a, p <= a <= p + Z.of_nat (length s) ->
     kernel_ard SEGS (k_regs cx) (km0 cx) a) ->
  katstr cx W3 ms3 p (map zb (removelast bs)).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 p bs HB HJ Hjb Hkk Hin HT Hcov.
  destruct (ki_strs_shape p bs Hin) as (Ebs & _ & Hp1 & Hp2).
  pose proof HB as ((_ & _ & HRO0 & _) & _). pose proof Hkk as (_ & HRO3).
  pose proof (kac_cstr_ro _ _ p bs HRO3 Hin) as CS3.
  pose proof (kac_cstr_ro _ _ p bs HRO0 Hin) as CS0.
  destruct HT as (s & slack & Hp0 & Hcs & Hlen & Hsl & Hslk & Hamr & Hra & Hhv & Hkap).
  assert (EL : length s = length (map zb (removelast bs))) by exact (kac_cstr_len _ _ _ _ Hcs CS0).
  assert (LB : Z.of_nat (length s) + 1 = Z.of_nat (length bs)).
  { rewrite EL, length_map. rewrite Ebs at 2. rewrite length_app. cbn [length]. lia. }
  assert (Hend : 0x21300 <= PcapImgEnd.pcap_img_end) by (vm_compute; discriminate).
  unfold katstr. rewrite <- EL.
  split; [lia|]. split; [exact CS3|]. split; [exact Hlen|].
  split.
  { set (q := p + Z.of_nat (length s) + 1).
    pose proof (Z.mod_pos_bound (- q) 8 ltac:(lia)) as Hm.
    exists (abytes_of SEGS (rdW W3 (ms_mem ms3)) q (Z.to_nat ((- q) mod 8))).
    split; [|rewrite abytes_of_length; lia].
    apply abytes_of_abytes; [unfold q; lia | unfold q; lia |].
    intros i Hi.
    pose proof (ki_vis SEGS B KI (w_H W3) (ms_mem ms3) (q + Z.of_nat i) ltac:(unfold q; lia)) as V.
    unfold aview in V. destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (q + Z.of_nat i)) as [b|].
    - exists b. reflexivity.
    - cbn [option_map] in V. congruence. }
  split; [exact Hamr|].
  destruct (kac_sh_now cx fpos k2 ly3 S3 W3 ms3 md3 p (Z.of_nat (length s) + 1) HB HJ Hjb Hkk ltac:(lia)
              (fun a Ha => Hcov s Hcs a ltac:(lia)) Hra Hhv) as (R1 & R2).
  split; [exact R1|]. split; [exact R2|].
  split; [exact (proj1 Hkap)|].
  intros a Ha. exact (Hcov s Hcs a Ha).
Qed.

(* the eleven texts words are strings of ki_strs *)
Lemma ki_tx_in_strs : forall i, (i < 11)%nat -> exists bs, In (nth i ki_tx_words 0, bs) ki_strs.
Proof.
  intros i Hi.
  do 11 (destruct i as [|i];
    [eexists; unfold ki_strs; cbn [nth ki_tx_words]; repeat (first [left; reflexivity | right]) |]).
  lia.
Qed.

(* the text kernel hands for attribute byte a (ka_text: texts[(a >> 3) % 11] at the call) is a string of ki_strs *)
Lemma kac_tx_in : forall cx a p, kbase SK B cx -> 0 <= a < 256 -> ka_text cx a p -> ktext cx p ->
  exists bs, In (p, bs) ki_strs.
Proof.
  intros cx a p HB Ha Htx HT.
  pose proof HB as ((_ & _ & HRO0 & _) & _).
  pose proof (Z.mod_pos_bound (a / 8) 11 ltac:(lia)) as Hm.
  set (i := Z.to_nat ((a / 8) mod 11)).
  assert (Hi : (i < 11)%nat) by (unfold i; lia).
  pose proof (ki_tx_val_mem SEGS PCAP_RLO PCAP_RHI B KI (w_H (k_W cx)) (k_memc cx) HRO0 i Hi eq_refl eq_refl) as V.
  unfold ka_text, au64_at, km0 in Htx.
  replace (LA_TEXTS + 8 * ((a / 8) mod 11)) with (KI_TX + 8 * Z.of_nat i) in Htx
    by (unfold i, KI_TX, LA_TEXTS; rewrite Z2Nat.id by lia; reflexivity).
  destruct HT as (s & slack & Hp0 & ((Hpa & Hpb & _) & _) & _).
  rewrite length_app in Hpb. cbn [length] in Hpb.
  destruct (ki_tx_in_strs i Hi) as (bs & Hin).
  assert (Hw : 0 <= nth i ki_tx_words 0 < 2 ^ 64).
  { destruct (ki_strs_shape _ bs Hin) as (_ & _ & H1 & H2). lia. }
  pose proof (rdword_of_val_mem SEGS _ _ _ _ Htx ltac:(lia)) as R1.
  pose proof (rdword_of_val_mem SEGS _ _ _ _ V Hw) as R2.
  rewrite R1 in R2. injection R2 as Ep. rewrite Ep. exists bs. exact Hin.
Qed.

(* THE CALL: attr_text from a cut at its entry, the walk continuing at the return address *)
Theorem kn_atcall : forall POST cx fpos k2 ly3 S3 W3 ms3 md3 ret rl rl' sl s1v r adv g n f p s,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  kat B cx fpos KP_ATEXT rl sl (kfsh s1v 0 r) true adv g k2 ly3 S3 W3 ms3 md3 ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  getr (ms_regs ms3) 1 = w64 (BASE + kpc ret) -> 0 <= kpc ret < 2 ^ 40 -> kpc ret mod 2 = 0 ->
  getr (ms_regs ms3) 10 = w64 (kW2 cx fpos) -> getr (ms_regs ms3) 12 = w64 p ->
  katstr cx W3 ms3 p s ->
  incl rl' rl -> Forall (fun rv => acallee_saved (Z.of_nat (fst rv))) rl' -> kslots_okb sl = true ->
  (forall ly4 S4 W4 ms4 md4 n' f',
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx)
       (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly4 S4 W4 (ms_mem ms4) md4 k2 ->
     frames S4 = (KN_CID, fpos) :: frames (k_Sc cx) ->
     kat B cx fpos ret rl' sl (kfsh s1v 0 r) true adv g k2 ly4 S4 W4 ms4 md4 ->
     kw_at W4 ms4 (kW2 cx fpos) n' f' -> n <= n' ->
     SRr SEGS W4 (mkCfg ms4 md4) (POST cx)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms3 md3 ret rl rl' sl s1v r adv g n f p s
    HB HJ HFR HAT HW Hra Hret1 Hret2 Ha0r Ha2r HST Hrl Hcs Hsl HCONT.
  pose proof HAT as (_ & HR0 & _ & _ & _ & HSH & _ & HJB & _).
  pose proof HR0 as (R2 & _).
  pose proof (kn_sp1 SK B cx HB) as (Hs1a & _ & Hlo & _ & _ & Hsp47 & _).
  pose proof (kn_sp SK B cx HB) as (G1 & G2 & _ & G4 & _).
  assert (HKA : kernel_c.KERNEL_AK = 4640) by reflexivity.
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & F4 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity. rewrite Hfb in F2, F3.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  pose proof HST as (Hp0 & Hcs3 & Hlen & Hslack & Hamr & Hra3 & Hhv3 & Hapf & Hcov).
  pose proof Hcs3 as ((Hpa & Hpb & _) & _). rewrite length_app in Hpb. cbn [length] in Hpb.
  assert (Ha0 : aarg (ms_regs ms3) 0 = kW2 cx fpos).
  { unfold aarg, argZ. transitivity (bv_unsigned (getr (ms_regs ms3) 10)); [reflexivity|].
    rewrite Ha0r. unfold w64. apply unsigned_lit_small. unfold kW2, KN_W2. lia. }
  assert (Ha2 : aarg (ms_regs ms3) 2 = p).
  { unfold aarg, argZ. transitivity (bv_unsigned (getr (ms_regs ms3) 12)); [reflexivity|].
    rewrite Ha2r. unfold w64. apply unsigned_lit_small. lia. }
  assert (Hsp : spZ (ms_regs ms3) = ksp1 cx).
  { unfold spZ. transitivity (bv_unsigned (w64 (ksp1 cx))); [f_equal; exact R2|].
    unfold w64. apply unsigned_lit_small. lia. }
  eapply kn_ocall with (pcE := ATTR_TEXT_A) (K := ATTR_TEXT_AK) (SIDE := [])
                       (Pre := attr_text_apre SEGS) (Rd := attr_text_ard SEGS)
                       (pc := KP_ATEXT) (ret := ret) (rl' := rl') (n := n) (f := f).
  - exact LAWS.
  - exact LV.
  - exact KI.
  - exact ATEXT.
  - exact HB.
  - exact HJ.
  - exact HFR.
  - exact HAT.
  - exact HW.
  - rewrite (lv_text LV). unfold link_text, kpc, AF_kernel, KP_ATEXT, ATTR_TEXT_A. lia.
  - rewrite ATTR_TEXT_AK_val. lia.
  - apply Forall_nil.
  - exact Hra.
  - exact Hret1.
  - exact Hret2.
  - exact Ha0r.
  - (* attr_text's Pre at the cut *)
    destruct (anlw_of_nlw_fields SEGS _ _ _ _ HW) as (bs & Hbs & Hwf & _ & _).
    pose proof (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 s1v r HJB HSH) as HRA.
    assert (HFS : kFSH cx fpos = SHADOW_OFF + kF cx fpos / 8) by reflexivity.
    assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
    unfold attr_text_apre. exists bs, s. rewrite Ha0, Ha2.
    split; [exact Hbs|]. split; [exact Hwf|].
    split; [lia|]. split; [exact Hcs3|]. split; [exact Hlen|]. split; [exact Hslack|].
    split.
    { (* w2 is in F, the string is in kernel's read set: apart *)
      unfold apart.
      destruct (Z_le_gt_dec (kW2 cx fpos + NW_SIZE) p) as [H1|H1]; [left; exact H1|].
      destruct (Z_le_gt_dec (p + (Z.of_nat (length s) + 1)) (kW2 cx fpos)) as [H2|H2]; [right; exact H2|].
      exfalso.
      apply (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 (Z.max p (kW2 cx fpos)) HB HJB
               (Hcov (Z.max p (kW2 cx fpos)) ltac:(unfold NW_SIZE in *; lia))).
      rewrite Hfb. unfold NW_SIZE in *. lia. }
    split.
    { unfold apart_frame. rewrite Hsp, ATTR_TEXT_AK_val. left. unfold NW_SIZE. lia. }
    split.
    { unfold apart_frame in Hapf |- *. rewrite Hsp, ATTR_TEXT_AK_val.
      change (spZ (k_regs cx)) with (ksp cx) in Hapf. rewrite HKA in Hapf. lia. }
    split.
    { unfold amem_range, kLowMemEnd, kHighMemEnd, NW_SIZE. unfold kHighMemBeg in *. lia. }
    split; [rewrite ard_aview; exact HRA|].
    split.
    { (* the hull of w2's shadow is inside F's 0x448 shadow bytes *)
      assert (HSA : forall x, kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE ->
                kFSH cx fpos + 0x226 <= shadow_addr x <= kFSH cx fpos + 0x427).
      { intros x Hx. rewrite HFS. unfold shadow_addr. unfold NW_SIZE in Hx. lia. }
      intros sa Hs.
      change (ard SEGS (mrestrict (w_H W3) (ms_mem ms3)) sa) with (aview SEGS (w_H W3) (ms_mem ms3) sa).
      pose proof (HSA (kW2 cx fpos) ltac:(unfold NW_SIZE; lia)) as Q1.
      pose proof (HSA (kW2 cx fpos + NW_SIZE - 1) ltac:(unfold NW_SIZE; lia)) as Q2.
      assert (HF8 : kFSH cx fpos mod 8 = 0) by (rewrite HFS; unfold SHADOW_OFF; lia).
      assert (Hi : 0x220 <= sa - kFSH cx fpos < 0x428) by lia.
      unfold kshadow in HSH.
      replace sa with (kFSH cx fpos + Z.of_nat (Z.to_nat (sa - kFSH cx fpos))) by (rewrite Z2Nat.id; lia).
      rewrite (HSH (Z.to_nat (sa - kFSH cx fpos))) by (rewrite kfsh_length; lia). discriminate. }
    split; [exact Hamr|].
    split; [rewrite ard_aview; exact Hra3 | rewrite ard_aview; exact Hhv3].
  - (* the read set: the string, in kernel's read set, so akb at attr_text's window *)
    intros a (s' & Hs' & Ha). rewrite Ha2 in Hs', Ha.
    assert (EL : length s' = length s) by exact (kac_cstr_len _ _ _ _ Hs' Hcs3).
    rewrite EL in Ha.
    pose proof HB as (_ & HRD & _).
    pose proof (HRD a (Hcov a Ha)) as Hakb.
    destruct (kac_row cx fpos k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ) as (Elo & Ehi).
    pose proof HJB as (_ & _ & Hperm & _).
    rewrite ATTR_TEXT_AK_val.
    apply (akb_sub SEGS B (k_lyc cx) (k_Sc cx) ly3 S3 (ksp cx - KERNEL_AK) (ksp cx) (ksp1 cx - 4160) (ksp1 cx) a
             Hakb); [lia | lia | exact Elo | exact Ehi | | | exact (kac_fa cx fpos k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ)].
    + intros b mm Hbm. exact (Permutation_in _ (Permutation_sym Hperm) Hbm).
    + intros c q Hcq. rewrite HFR. right. exact Hcq.
  - exact Hrl.
  - exact Hcs.
  - exact Hsl.
  - rewrite kfsh_length. lia.
  - exact HCONT.
Qed.

End b.
End a.

Print Assumptions kn_atcall.
Print Assumptions katstr_img.
Print Assumptions kac_tx_in.
