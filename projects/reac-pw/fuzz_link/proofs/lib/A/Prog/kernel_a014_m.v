(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v; 482 of its 536 lines of code are new or changed and 432 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel's attribute case a % 6 = 1 (kernel_defs.v kin_txt at +0xa74):
   +0xa74 .. +0xaf8 (one run to the `jal checked_memset` with a0 = s3 = long_alias, a1 = 0x61, a2 = 300),
   checked_memset (link_ajkit.v aj_gx_intrin_at over AMEMSET: the 300 bytes of long_alias become 0x61), then
   +0xafc .. +0xb40 (one run to the `jal attr_text` with a0 = w2, a1 = 20, a2 = long_alias, a3 = 0, s3 reloaded from
   slot 0xb0), and kernel_a014.v tx_call to kin_alat. The string attr_text gets is long_alias's 300 bytes 0x61 and
   its NUL at long_alias + 300 (kla_at: the memset does not reach it), with 3 visible slack bytes (KernImg ki_vis).
   - `tx_ms_la`: the checked_memset step (kernel_a5.v a5_call_ms's shape, with long_alias's writability from
     KernImg ki_la_wseg and its shadow facts at the call memory as premises).
   - `tx_kat_frame_la`: kernel_kit.v kat_frame for a step that also writes long_alias's 300 bytes, given kla_at
     at the new state.
   - `katstr_la`: kernel_atcall.v katstr of long_alias at a state where its 300 bytes are 0x61.
   Section hypotheses: LAWS, LV, KI, TB, AMEMSET (aintrin_realizes pa_segs B OSet 0x53214, discharged by
   AE2r.v asan_memset_realizes), ATEXT.
   Released proofs (rule 24): this proves no function (kind: segment lemma of kernel's walk); the walk of kernel had
   its search (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by the rule-24 walk check at 14:56Z).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
attr_text_c LinkWalkCall kernel_entry kernel_next kernel_ocall kernel_msg0_kit kernel_atcall kernel_a014_base kernel_a014 kernel_a5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Definition tx_la : list byte := repeat (zb 97) 300.
(* the state at +0xafc, after checked_memset: s3 = long_alias (atom 19), the slots *)
Definition tx_atoms2 : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
Definition tx_ss2 : sstate := mkSS (kpc 0xafc) sr_atoms [tx_rg] None (mkFacts tx_atoms2 [] []).

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
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet 0x53214.
Hypothesis ATEXT : attr_text_acontract SK pa_segs PCAP_RLO PCAP_RHI B.

Definition tx_X (cx : kcx) (a : Z) : Prop :=
  (LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 300) \/ (ksp1 cx - ESTACK <= a < ksp1 cx).
Definition tx_rl0 (cx : kcx) (fpos left : Z) : list (nat * Z) :=
  [(21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (22%nat, left)].

Lemma tx_la_w : forall (m : word -> option byte) a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + LONG_ALIAS_SIZE ->
  writable_at SEGS m a.
Proof.
  intros m a Ha. apply (writable_at_of_wseg SEGS m LA_LONG_ALIAS LONG_ALIAS_SIZE);
    [unfold LA_LONG_ALIAS; lia | unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE; lia | exact (ki_la_wseg _ _ KI) | exact Ha].
Qed.

(* ---- the checked_memset call at +0xaf8 ---- *)
Lemma tx_ms_la : forall cx fpos k2 ly3 S3 W3 mm md md0 (rg : bvmap 5 word) raw (Q : world SEGS -> config -> Prop),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mm md k2 ->
  kjbk B cx fpos k2 ly3 S3 md0 ->
  range_addressable (aview SEGS (w_H W3) mm) SHADOW_OFF LA_LONG_ALIAS 300 ->
  shadow_hull_vis (aview SEGS (w_H W3) mm) LA_LONG_ALIAS 300 ->
  getr rg 10 = w64 LA_LONG_ALIAS -> getr rg 11 = w64 97 -> getr rg 12 = w64 300 -> getr rg 2 = w64 (ksp1 cx) ->
  getr rg 3 = getr (k_regs cx) 3 -> getr rg 4 = getr (k_regs cx) 4 -> getr rg 1 = raw -> YK0s.ret_ok raw ->
  (forall regs2 mem2 md2,
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
       (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mem2 md2 k2 ->
     aregs_preserved rg regs2 ->
     (forall i, 0 <= i < 300 -> aview SEGS (w_H W3) mem2 (LA_LONG_ALIAS + i) = Some 97) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ tx_X cx a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mm a) ->
     (forall a, apresent (w_H W3) mm a -> apresent (w_H W3) mem2 a) ->
     same_but_materialized md md2 ->
     SRr SEGS W3 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst rg (Z_to_bv 64 0x53214) mm (seg_rom SEGS)) md) Q.
Proof.
  intros cx fpos k2 ly3 S3 W3 mm md md0 rg raw Q HB HJ HJB HRA HHV R10 R11 R12 R2 R3 R4 R1 Hraw CONT.
  pose proof HB as (HPRE & _). pose proof HPRE as (HJ0 & HGok & _ & _ & _ & Hgp & Htp & _).
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _) & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & S1c & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp : spZ rg = ksp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  pose proof HJB as (_ & _ & Hperm & _).
  eapply SRr_bind.
  - eapply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OSet 0x53214 AMEMSET (k_G cx) (k_XO cx) (k_OUT cx) W3 rg
      mm (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) _ ly3 S3 md k2
      LA_LONG_ALIAS 97 300 raw HGok HJ R10 R11 R12);
    [ lia | unfold LA_LONG_ALIAS; lia | unfold LA_LONG_ALIAS; lia
    | rewrite Hsp; lia | rewrite Hsp, HES; rewrite HK8 in S6; lia | rewrite Hsp; lia
    | rewrite R3; exact Hgp | rewrite R4; exact Htp | exact R1 | exact Hraw
    | | | exact HRA | intros _; exact HHV | exact I ].
    + intros a Ha.
      assert (HE : inFP (kernel_awr (k_regs cx) (km0 cx)) a).
      { exists (LA_LONG_ALIAS, LA_LONG_ALIAS + LONG_ALIAS_SIZE). split; [unfold kernel_awr; kn_in|].
        cbn [fst snd]. unfold LONG_ALIAS_SIZE. lia. }
      destruct (Hajw a HE) as [[Haw Hnout] | [HGa | Hout]].
      * left. split; [|split; [exact Hnout | rewrite Hsp, HES; unfold LA_LONG_ALIAS in Ha; lia]].
        destruct Haw as [Hw | [(Hfp & b0 & n0 & Hbn & Hr) | [(b0 & n0 & Hbn & Hnb & Hr) | (cid & pos & Hown & Hr)]]].
        -- left. exact Hw.
        -- right; left. split; [exact Hfp|]. exists b0, n0. split; [|exact Hr].
           exact (Permutation_in _ (Permutation_sym Hperm) Hbn).
        -- right; right; left. exists b0, n0. split; [exact (Permutation_in _ (Permutation_sym Hperm) Hbn)|].
           split; [exact Hnb | exact Hr].
        -- right; right; right. exists cid, pos. split; [right; exact Hown|].
           rewrite (kac_fa SK B LAWS cx fpos k2 ly3 S3 W3 mm md HB HJ). exact Hr.
      * right; left. split; [exact HGa|]. apply tx_la_w. unfold LONG_ALIAS_SIZE. lia.
      * right; right. exact Hout.
    + unfold amem_range, kLowMemEnd, LA_LONG_ALIAS. left. lia.
  - cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset & Hfr & Hpres & Hsbm).
    apply (CONT regs2 mem2 md2 HJ2 HP2); [| | exact Hpres | exact Hsbm].
    + intros i Hi. rewrite (Hset i Hi). reflexivity.
    + intros a Ha Hx. apply Hfr; [exact Ha | intros Hc; apply Hx; left; exact Hc |].
      rewrite Hsp. intros Hc; apply Hx; right; exact Hc.
Qed.

Print Assumptions tx_ms_la.


(* ---- kernel_kit.v kat_frame for a step that also writes long_alias's 300 bytes: kla_at at the new state given ---- *)
Lemma tx_kat_frame_la : forall (X : Z -> Prop) cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4
    md4,
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms4 -> kregs0 cx ms4 -> kregs_eq ms4 rl' -> incl sl' sl -> (length sh <= 2048)%nat ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  (forall a, X a -> kX_in cx fpos a) ->
  (forall a, ksp cx - 104 <= a < ksp cx -> ~ X a) ->
  (forall ov, In ov sl' -> 0 <= fst ov <= 0xf0 /\ (forall a, ksp1 cx + fst ov <= a < ksp1 cx + fst ov + 8 -> ~ X a)) ->
  (forall a, kF cx fpos <= a < kF cx fpos + 24 -> ~ X a) ->
  (forall a, kF cx fpos + fs_frame_bytes KN_CID - 8 <= a < kF cx fpos + fs_frame_bytes KN_CID -> ~ X a) ->
  (forall a, kFSH cx fpos <= a < kFSH cx fpos + Z.of_nat (length sh) -> ~ X a) ->
  (forall a, ka0 cx <= a < ka0 cx + 16 -> ~ X a) ->
  (forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ X a) ->
  kla_at W4 ms4 ->
  kat B cx fpos pc' rl' sl' sh live adv g k2 ly3 S3 W4 ms4 md4.
Proof.
  intros X cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4
    HB HK HMS HR0 HRL Hsl Hsh Hfds Hfs UN HP HXin Msv Msl Mhd Mfl Msh Mcu Mgn HLA4.
  destruct HK as (_ & _ & _ & HSAV & HFR & HSH & HSL & HJB & HKEPT & HCUR & HGNL & HLA).
  unfold kat.
  refine (conj HMS (conj HR0 (conj HRL (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ HLA4))))))))))).
  - eapply ksaved_frame; eassumption.
  - eapply kframe_frame; eassumption.
  - eapply kshadow_frame; eassumption.
  - eapply kslots_frame; eassumption.
  - eapply kjbk_md; eassumption.
  - eapply kkept_frame; eassumption.
  - eapply kcursor_frame; eassumption.
  - eapply kgnl_frame; eassumption.
Qed.

(* ---- katstr of long_alias at a state where its 300 bytes are 0x61 ---- *)
Lemma katstr_la : forall cx fpos k2 ly3 S3 W3 ms3 md3,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 -> kkept B cx fpos W3 ms3 ->
  (forall i, 0 <= i < 300 -> aview SEGS (w_H W3) (ms_mem ms3) (LA_LONG_ALIAS + i) = Some 97) ->
  kla_at W3 ms3 ->
  katstr cx W3 ms3 LA_LONG_ALIAS tx_la.
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HJB HKK Hset HLA.
  destruct (tx_apre_x SK B cx HB) as (_ & _ & HRA0 & HHV0 & HAF).
  destruct HLA as (la3 & (HLAb & _) & Hl3).
  assert (Hlen : length tx_la = 300%nat) by (unfold tx_la; apply repeat_length).
  assert (Hl3' : length la3 = 300%nat) by lia.
  assert (Hend : 0x630000 <= PcapImgEnd.pcap_img_end) by (vm_compute; discriminate).
  unfold katstr. rewrite Hlen.
  split; [unfold LA_LONG_ALIAS; lia|].
  split.
  { split.
    - split; [unfold LA_LONG_ALIAS; lia|]. split; [rewrite length_app, Hlen; cbn [length]; unfold LA_LONG_ALIAS; lia|].
      intros i Hi. rewrite length_app, Hlen in Hi. cbn [length] in Hi.
      destruct (Nat.lt_ge_cases i 300) as [Hi3|Hi3].
      + rewrite nth_error_app1 by (rewrite Hlen; exact Hi3). unfold tx_la. rewrite nth_error_repeat by exact Hi3.
        apply kac_mbyte_of_view. exact (Hset (Z.of_nat i) ltac:(lia)).
      + assert (Ei : i = 300%nat) by lia. subst i.
        rewrite nth_error_app2 by (rewrite Hlen; lia). rewrite Hlen, Nat.sub_diag. cbn [nth_error].
        destruct HLAb as (_ & _ & HB3).
        pose proof (HB3 300%nat ltac:(rewrite length_app; cbn [length]; lia)) as N.
        rewrite nth_error_app2 in N by lia. rewrite Hl3', Nat.sub_diag in N. cbn [nth_error] in N. exact N.
    - unfold tx_la. intros Hc. apply repeat_spec in Hc.
      pose proof (kac_zb0 97 ltac:(lia) (eq_sym Hc)). lia. }
  split; [lia|].
  split.
  { set (q := LA_LONG_ALIAS + Z.of_nat 300 + 1).
    pose proof (Z.mod_pos_bound (- q) 8 ltac:(lia)) as Hm.
    exists (abytes_of SEGS (rdW W3 (ms_mem ms3)) q (Z.to_nat ((- q) mod 8))).
    split; [|rewrite abytes_of_length; lia].
    apply abytes_of_abytes; [unfold q, LA_LONG_ALIAS; lia | unfold q, LA_LONG_ALIAS; lia |].
    intros i Hi.
    pose proof (ki_vis SEGS B KI (w_H W3) (ms_mem ms3) (q + Z.of_nat i) ltac:(unfold q, LA_LONG_ALIAS; lia)) as V.
    unfold aview in V. destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (q + Z.of_nat i)) as [b|].
    - exists b. reflexivity.
    - cbn [option_map] in V. congruence. }
  split; [unfold amem_range, kLowMemEnd, LA_LONG_ALIAS; left; lia|].
  assert (HCOV : forall x, LA_LONG_ALIAS <= x < LA_LONG_ALIAS + LONG_ALIAS_SIZE ->
            kernel_ard SEGS (k_regs cx) (km0 cx) x).
  { intros x Hx. unfold kernel_ard. do 9 right. left. exact Hx. }
  destruct (kac_sh_now SK B LAWS KI TB cx fpos k2 ly3 S3 W3 ms3 md3 LA_LONG_ALIAS LONG_ALIAS_SIZE HB HJ HJB HKK
              ltac:(unfold LONG_ALIAS_SIZE; lia) HCOV HRA0 HHV0) as (R1 & R2).
  unfold LONG_ALIAS_SIZE in R1, R2. change (Z.of_nat 300 + 1) with 301.
  split; [exact R1|]. split; [exact R2|].
  split.
  { unfold apart_frame in HAF |- *. unfold LONG_ALIAS_SIZE in HAF. lia. }
  intros x Hx. apply HCOV. unfold LONG_ALIAS_SIZE. lia.
Qed.

Print Assumptions katstr_la.


(* ---- the state at +0xafc, after checked_memset ---- *)
Lemma tx_seat2 : forall cx fpos k2 ly3 S3 md3 W3 ms3 sl,
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  kms 0xafc ms3 -> kregs0 cx ms3 -> kslots_eq cx W3 ms3 sl ->
  In (KS_CN, ka0 cx + 8) sl -> In (KS_M6, KI_M6_V) sl ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) [])) tx_ss2 (restrict (w_H W3) ms3).
Proof.
  intros cx fpos k2 ly3 S3 md3 W3 ms3 sl HB HJB HMS HR0 HSL Hcn Hm6.
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof (kn_sp1 SK B cx HB) as (S1a & S1b & S1c & _ & _ & S1f & _).
  destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 (ka0 cx + 15) HB HJB (kn_ard_cur cx (ka0 cx + 15) ltac:(lia)))
    as (CL & _).
  destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 (ka0 cx) HB HJB (kn_ard_cur cx (ka0 cx) ltac:(lia)))
    as (CL0 & _).
  set (E := Eimg (Ereg (ms_regs ms3) [])).
  assert (ER : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E jn = getr (ms_regs ms3) r)
    by (intros jn r Hjr; exact (ew_Eimg_Ereg_nat _ _ jn r Hjr)).
  assert (E18 : ew E 18%nat = w64 (ka0 cx)) by (rewrite (ER 18%nat 18%bv eq_refl); exact A18).
  assert (E9 : ew E 9%nat = w64 (ksp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact A9).
  assert (E20 : ew E 20%nat = w64 SHADOW_OFF) by (rewrite (ER 20%nat 20%bv eq_refl); exact A20).
  assert (BV18 : bv_unsigned (ew E 18%nat) = ka0 cx) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
  pose proof (kn_slot_of cx W3 ms3 sl KS_CN (ka0 cx + 8) HSL Hcn) as SL_CN.
  pose proof (kn_slot_of cx W3 ms3 sl KS_M6 KI_M6_V HSL Hm6) as SL_M6.
  rewrite (kn_ms_shape ms3 (BASE + kpc 0xafc) Hpc Hrv Hsvc Hrom Hfrg Hfcs), restrict_mkst_fx.
  unfold tx_ss2. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold tx_rg, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite BV9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xb0 (SOff 18 8) (ka0 cx + 8)); [|exact SL_CN].
      cbn [sv_denot]. rewrite BV18. reflexivity.
    + exact (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xb8 (SLit KI_M6_V) KI_M6_V eq_refl SL_M6).
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; [exact I | exact I]].
    unfold tx_atoms2. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E20. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; first [lia | exact I | exact S1b].
Qed.


(* ---- a % 6 = 1: +0xa74 -> checked_memset(long_alias, 0x61, 300) -> +0xafc -> the attr_text call at +0xb40 ---- *)
Lemma tx_c1_ph : forall POST Rc Rm Ra,
  kfrom SK B POST (kin_alat B Rc Rm Ra) ->
  kfrom SK B POST (kin_txtc B Rc Rm Ra (fun x => x = 1)).
Proof.
  intros POST Rc Rm Ra HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (a & p & Ha & Hc & Htx & HT & HAT0).
  destruct HAT0 as (c & ci & j & m & k & n & f & adv & hd & kd & left & HRc & HRm & HRa & Hc1 & Hci & Hj & Hm & Hk &
    Hkd & Hl & Hhd & HW & _ & HAT).
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & _ & HSL & HJB & HKK & _ & _ & HLA).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof (kn_sp1 SK B cx HB) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e & Hsp47 & _).
  pose proof (kn_sp SK B cx HB) as (G1 & G2 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity. rewrite Hfb in F2.
  destruct (tx_apre_x SK B cx HB) as (_ & _ & HRA0 & HHV0 & HAF).
  destruct (kn_apre SK B cx HB) as (_ & HAPL & _).
  assert (HCOV : forall x, LA_LONG_ALIAS <= x < LA_LONG_ALIAS + LONG_ALIAS_SIZE ->
            kernel_ard SEGS (k_regs cx) (km0 cx) x)
    by (intros x Hx; unfold kernel_ard; do 9 right; left; exact Hx).
  assert (LANF : forall x, LA_LONG_ALIAS <= x < LA_LONG_ALIAS + LONG_ALIAS_SIZE -> ~ (kF cx fpos <= x < kF cx fpos + 16384)).
  { intros x Hx. rewrite <- Hfb. exact (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 x HB HJB (HCOV x Hx)). }
  destruct (kac_sh_now SK B LAWS KI TB cx fpos k2 ly3 S3 W3 ms3 md3 LA_LONG_ALIAS LONG_ALIAS_SIZE HB HJ HJB HKK
              ltac:(unfold LONG_ALIAS_SIZE; lia) (fun x Hx => HCOV x ltac:(lia)) HRA0 HHV0) as (HRA3 & HHV3).
  assert (HRA300 : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF LA_LONG_ALIAS 300)
    by (intros x Hx; apply HRA3; unfold LONG_ALIAS_SIZE; lia).
  assert (HHV300 : shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms3)) LA_LONG_ALIAS 300)
    by (intros sa Hs; apply HHV3; unfold shadow_addr, SHADOW_OFF, LA_LONG_ALIAS, LONG_ALIAS_SIZE in *; lia).
  assert (O20 : pa_val (A_OBJ 20) = LA_LONG_ALIAS) by (rewrite (lv_obj LV) by (vm_compute; lia); reflexivity).
  (* ---- run 1: +0xa74 -> the jal checked_memset ---- *)
  remember (Eimg (Ereg (ms_regs ms3) (@nil word))) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (@nil word)) E)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (ER : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E jn = getr (ms_regs ms3) r)
    by (intros jn r Hjr; rewrite HEdef; exact (ew_Eimg_Ereg_nat _ _ jn r Hjr)).
  assert (R23 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 23)) = w64 a) by (apply (kn_reg_in ms3 _ _ _ HRL); kn_in).
  assert (D261 : sv_denot E (SOff 261 0) = w64 LA_LONG_ALIAS).
  { cbn [sv_denot]. rewrite HEdef, (Eimg_img _ 261) by (unfold A_TEXT, A_LIM; lia).
    change (pa_val 261) with (pa_val (A_OBJ 20)). rewrite O20, unsigned_lit_small by (unfold LA_LONG_ALIAS; lia).
    rewrite Z.add_0_r. reflexivity. }
  assert (HCS : conds_ok E tx_c1).
  { pose proof (tx_conds E a ltac:(rewrite (ER 23%nat (Z_to_bv 5 (Z.of_nat 23)) eq_refl), R23; reflexivity) Ha) as Q.
    rewrite Hc in Q. exact Q. }
  assert (HS : st_ok_pi SEGS pa_val E (tx_ss tx_c1) (restrict (w_H W3) ms3)).
  { rewrite HEdef in HCS |- *.
    exact (tx_seat SK B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 _ a tx_c1 HB HJB HMS HR0 HSL
             ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)
             ltac:(apply in_or_app; left; unfold kslots_setup; kn_in) R23 Ha HCS). }
  pose proof HS as HS0.
  assert (SHOK : sh_ok SEGS tx_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK tx_span.
  { cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros x Hx. unfold tx_rg in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia. }
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?mm) |- _ => rename mm into ms1; rename HSx into HS1 end.
  lazymatch goal with HFx : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ => rename HFx into HFr1 end.
  lazymatch goal with HJx : ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ms1) _ _ |- _ => rename HJx into HJ1 end.
  assert (Hmem1 : ms_mem ms1 = ms_mem ms3)
    by (apply functional_extensionality; intros x; apply HFr1;
        intros (rr & Hin' & Hw); cbn [ss_mem In] in Hin'; destruct Hin' as [<-|[]];
        unfold tx_rg in Hw; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; lia).
  pose proof (a5_reg_same E _ _ (w_H W3) ms3 ms1 [2; 3; 4] HS0 HS1 ltac:(vm_compute; reflexivity)) as KEEP.
  assert (HK0 : forall r, In r nx_keep0 -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) ms1) (ms_regs ms3) (@nil word) nx_keep0 HS1 HAG
                ltac:(vm_compute; reflexivity)).
  assert (HR01 : kregs0 cx ms1) by exact (kregs0_keep cx ms3 ms1 HK0 HR0).
  assert (HKN1 : forall r, In r [21; 22; 24; 25]%nat ->
            getr (ms_regs ms1) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
    by (intros r Hr;
        exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) ms1) (ms_regs ms3) (@nil word)
                 (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 22; 24; 25]%nat) HS1 HAG
                 ltac:(vm_compute; reflexivity) _ (kn_in_map5 r _ Hr))).
  assert (HRL01 : kregs_eq ms1 (tx_rl0 cx fpos left)).
  { unfold kregs_eq, tx_rl0. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      rewrite HKN1 by kn_in; apply (kn_reg_in ms3 _ _ _ HRL); kn_in. }
  sreg HS1 (10%bv : bv 5) R10. sreg HS1 (11%bv : bv 5) R11. sreg HS1 (12%bv : bv 5) R12.
  sreg HS1 (Z_to_bv 5 19) R19. sreg HS1 (1%bv : bv 5) R1.
  cbn [ms_regs restrict mkst] in R10, R11, R12, R19, R1.
  assert (R10' : getr (ms_regs ms1) 10%bv = w64 LA_LONG_ALIAS) by (rewrite R10; exact D261).
  assert (R19' : getr (ms_regs ms1) (Z_to_bv 5 19) = w64 LA_LONG_ALIAS) by (rewrite R19; exact D261).
  assert (R11' : getr (ms_regs ms1) 11%bv = w64 97) by (rewrite R11; reflexivity).
  assert (R12' : getr (ms_regs ms1) 12%bv = w64 300) by (rewrite R12; reflexivity).
  assert (Rr1 : getr (ms_regs ms1) 1%bv = w64 (BASE + kpc 0xafc)).
  { rewrite R1. cbn [sv_denot]. rewrite (img_env_codeptr E HEI 9824). unfold w64.
    f_equal; try (unfold kpc, AF_kernel; lia). }
  assert (R2' : getr (ms_regs ms1) 2%bv = w64 (ksp1 cx)) by (rewrite (KEEP 2%bv) by reflexivity; exact (proj1 HR0)).
  assert (R3' : getr (ms_regs ms1) 3%bv = getr (k_regs cx) 3)
    by (rewrite (KEEP 3%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 HR0))))).
  assert (R4' : getr (ms_regs ms1) 4%bv = getr (k_regs cx) 4)
    by (rewrite (KEEP 4%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 (proj2 HR0)))))).
  pmkst HS1.
  rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_memset) with 0x53214.
  (* ---- the memset ---- *)
  apply (tx_ms_la cx fpos k2 ly3 S3 W3 (ms_mem ms1) _ md3 (ms_regs ms1) (w64 (BASE + kpc 0xafc)) (POST cx) HB HJ1 HJB
           ltac:(rewrite Hmem1; exact HRA300) ltac:(rewrite Hmem1; exact HHV300) R10' R11' R12' R2' R3' R4' Rr1
           ltac:(apply ret_ok_codeptr_v; [unfold kpc, AF_kernel; lia | unfold kpc, AF_kernel; reflexivity])).
  intros regs2 mem2 md2 HJ2 HP2 Hset Hfr2 Hpres2 Hsbm.
  set (ms2 := mkst regs2 (w64 (BASE + kpc 0xafc)) mem2 (seg_rom SEGS)).
  change (SRr SEGS W3 (mkCfg ms2 md2) (POST cx)).
  change mem2 with (ms_mem ms2) in HJ2, Hset, Hfr2, Hpres2.
  (* ---- the cut at +0xafc ---- *)
  assert (HKMS2 : kms 0xafc ms2).
  { unfold kms, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    do 5 (split; [reflexivity|]). reflexivity. }
  assert (HR02 : kregs0 cx ms2) by exact (ko_regs0 cx ms1 ms2 HP2 HR01).
  assert (HRL02 : kregs_eq ms2 (tx_rl0 cx fpos left)).
  { apply (ko_regs_eq ms1 ms2 (tx_rl0 cx fpos left) (tx_rl0 cx fpos left) HP2 (incl_refl _)); [|exact HRL01].
    unfold tx_rl0. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      unfold acallee_saved; do 5 right; lia. }
  assert (Hfds2 : m_fds md2 = m_fds md3)
    by (rewrite (proj1 (kn_sbm_fds_fs _ _ Hsbm)); exact (proj1 (wvb_fds_fs _ _ _))).
  assert (Hfs2 : m_fs md2 = m_fs md3)
    by (rewrite (proj2 (kn_sbm_fds_fs _ _ Hsbm)); exact (proj2 (wvb_fds_fs _ _ _))).
  assert (UN2 : forall x, 0 <= x < 2 ^ 64 -> ~ tx_X cx x ->
            aview SEGS (w_H W3) (ms_mem ms2) x = aview SEGS (w_H W3) (ms_mem ms3) x)
    by (intros x Hx Hn; rewrite <- Hmem1; exact (Hfr2 x Hx Hn)).
  assert (HP2' : forall x, apresent (w_H W3) (ms_mem ms3) x -> apresent (w_H W3) (ms_mem ms2) x)
    by (intros x Hp; apply Hpres2; rewrite Hmem1; exact Hp).
  assert (CUR : forall x, ka0 cx <= x < ka0 cx + 16 -> ~ (ksp cx - KERNEL_AK <= x < ksp cx)).
  { intros x Hx. destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 x HB HJB (kn_ard_cur cx x Hx))
      as (_ & _ & _ & H4). exact H4. }
  assert (FSHb : SHADOW_OFF <= kFSH cx fpos /\ kFSH cx fpos + 0x448 <= 0x10007fff8000)
    by (unfold kFSH, shadow_of_addr; unfold SHADOW_OFF; lia).
  unfold apart in HAPL.
  assert (HLA2 : kla_at W3 ms2).
  { destruct HLA as (la3 & (HLAb & _) & Hl3).
    exists tx_la. split; [split|].
    - split; [unfold LA_LONG_ALIAS; lia|]. split; [unfold tx_la; rewrite length_app, repeat_length; cbn [length];
        unfold LA_LONG_ALIAS; lia|].
      intros i Hi. unfold tx_la in Hi |- *. rewrite length_app, repeat_length in Hi. cbn [length] in Hi.
      destruct (Nat.lt_ge_cases i 300) as [Hi3|Hi3].
      + rewrite nth_error_app1 by (rewrite repeat_length; exact Hi3). rewrite nth_error_repeat by exact Hi3.
        apply kac_mbyte_of_view. exact (Hset (Z.of_nat i) ltac:(lia)).
      + assert (Ei : i = 300%nat) by lia. subst i.
        rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length, Nat.sub_diag. cbn [nth_error].
        destruct HLAb as (_ & _ & HB3).
        pose proof (HB3 300%nat ltac:(rewrite length_app; cbn [length]; lia)) as N.
        rewrite nth_error_app2 in N by lia. replace (300 - length la3)%nat with 0%nat in N by lia.
        cbn [nth_error] in N. rewrite <- N.
        apply kn_mbyte_of_aview. apply UN2; [unfold LA_LONG_ALIAS; lia|].
        intros [Hx|Hx]; [lia | unfold LA_LONG_ALIAS in Hx; lia].
    - unfold tx_la. rewrite length_app, repeat_length. cbn [length].
      intros i Hi. apply tx_la_w. unfold LONG_ALIAS_SIZE. lia.
    - unfold tx_la. rewrite repeat_length. reflexivity. }
  assert (HAT2 : kat B cx fpos 0xafc (tx_rl0 cx fpos left)
            (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
            (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms2 md2).
  { pose proof (kslots_okb_spec (kslots_setup cx fpos c ++
      [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)]) eq_refl) as SOK.
    apply (tx_kat_frame_la (tx_X cx) cx fpos KP_TXT _ _ (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3
             0xafc (tx_rl0 cx fpos left) _ W3 ms2 md2 HB HAT HKMS2 HR02 HRL02 (incl_refl _)
             ltac:(rewrite kfsh_length; lia) Hfds2 Hfs2 UN2 HP2'); [ | | | | | | | | exact HLA2].
    - intros x [Hx|Hx].
      + left. exists (LA_LONG_ALIAS, LA_LONG_ALIAS + LONG_ALIAS_SIZE). split; [unfold kernel_awr; kn_in|].
        cbn [fst snd]. unfold LONG_ALIAS_SIZE. lia.
      + right; right; right. rewrite HK8, HES in *. lia.
    - intros x Hx [Hq|Hq]; [unfold LA_LONG_ALIAS in Hq; lia | rewrite HES in Hq; lia].
    - intros ov Hov. split; [exact (SOK ov Hov)|]. pose proof (SOK ov Hov).
      intros x Hx [Hq|Hq]; [unfold LA_LONG_ALIAS in Hq; lia | rewrite HES in Hq; lia].
    - intros x Hx [Hq|Hq]; [apply (LANF x ltac:(unfold LONG_ALIAS_SIZE; lia)); lia | rewrite HES in Hq; lia].
    - rewrite Hfb. intros x Hx [Hq|Hq]; [apply (LANF x ltac:(unfold LONG_ALIAS_SIZE; lia)); lia | rewrite HES in Hq; lia].
    - rewrite kfsh_length. intros x Hx [Hq|Hq]; [unfold LA_LONG_ALIAS, SHADOW_OFF in *; lia |
        rewrite HES in Hq; unfold SHADOW_OFF in *; lia].
    - intros x Hx [Hq|Hq]; [unfold LONG_ALIAS_SIZE in HAPL; lia |].
      apply (CUR x Hx). rewrite HK8, HES in *. lia.
    - intros x Hx [Hq|Hq]; [unfold LA_G_NL, NK_SIZE, LA_LONG_ALIAS in *; lia | rewrite HES in Hq;
        unfold LA_G_NL, NK_SIZE in *; lia]. }
  (* ---- run 2: +0xafc -> the jal attr_text ---- *)
  pose proof HAT2 as (_ & _ & _ & _ & _ & _ & HSL2 & HJB2 & HKK2 & _).
  assert (HW2 : kw_at W3 ms2 (kW2 cx fpos) n f).
  { pose proof HW as HW'. destruct HW' as (_ & _ & _ & Hn & Hf & Hnr & Hfr).
    assert (W2F : forall x, kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE -> ~ tx_X cx x).
    { intros x Hx [Hq|Hq]; [apply (LANF x ltac:(unfold LONG_ALIAS_SIZE; lia)); unfold kW2, KN_W2, NW_SIZE in Hx; lia |
        rewrite HES in Hq; unfold kW2, KN_W2, NW_SIZE in Hx; lia]. }
    apply (kw_move W3 ms3 W3 ms2 (kW2 cx fpos) n f n f HW HP2'); [| | exact Hnr | exact Hfr].
    - apply (val_mem_moved SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms2)
        (kW2 cx fpos + NW_N) (kW2 cx fpos + NW_N) 8 n); [|exact Hn].
      intros q Hq. apply UN2; [unfold kW2, KN_W2, NW_N in *; lia|]. apply W2F. unfold NW_N, NW_SIZE. cbn in Hq. lia.
    - apply (val_mem_moved SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms2)
        (kW2 cx fpos + NW_FULL) (kW2 cx fpos + NW_FULL) 4 f); [|exact Hf].
      intros q Hq. apply UN2; [unfold kW2, KN_W2, NW_FULL in *; lia|]. apply W2F. unfold NW_FULL, NW_SIZE. cbn in Hq. lia. }
  remember (Eimg (Ereg (ms_regs ms2) (@nil word))) as E2 eqn:HE2def.
  assert (HEI2 : img_env pa_val A_LIM E2) by (rewrite HE2def; apply Eimg_env).
  assert (HAG2 : env_agree 32 (Ereg (ms_regs ms2) (@nil word)) E2)
    by (rewrite HE2def; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (ER2 : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E2 jn = getr (ms_regs ms2) r)
    by (intros jn r Hjr; rewrite HE2def; exact (ew_Eimg_Ereg_nat _ _ jn r Hjr)).
  pose proof HR02 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  assert (B18 : bv_unsigned (ew E2 18%nat) = ka0 cx).
  { rewrite (ER2 18%nat 18%bv eq_refl), A18. apply unsigned_lit_small.
    destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 (ka0 cx) HB HJB (kn_ard_cur cx (ka0 cx) ltac:(lia)))
      as (CL0 & _). lia. }
  assert (B21 : bv_unsigned (ew E2 21%nat) = kW2 cx fpos).
  { rewrite (ER2 21%nat (Z_to_bv 5 (Z.of_nat 21)) eq_refl), (kn_reg_in ms2 _ _ _ HRL02 ltac:(unfold tx_rl0; kn_in)).
    apply unsigned_lit_small. unfold kW2, KN_W2. lia. }
  assert (B19 : bv_unsigned (ew E2 19%nat) = LA_LONG_ALIAS).
  { rewrite (ER2 19%nat (Z_to_bv 5 19) eq_refl).
    change (getr (ms_regs ms2) (Z_to_bv 5 19)) with (getr regs2 (Z_to_bv 5 19)).
    rewrite (HP2 19 ltac:(unfold acallee_saved; do 5 right; lia)).
    rewrite R19'. apply unsigned_lit_small. unfold LA_LONG_ALIAS. lia. }
  assert (HS2 : st_ok_pi SEGS pa_val E2 tx_ss2 (restrict (w_H W3) ms2)).
  { rewrite HE2def. exact (tx_seat2 cx fpos k2 ly3 S3 md2 W3 ms2 _ HB HJB2 HKMS2 HR02 HSL2
             ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)
             ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)). }
  assert (SHOK2 : sh_ok SEGS tx_Bx (@nil shent) E2 (mrestrict (w_H W3) (ms_mem ms2))) by apply Forall_nil.
  pose proof HJ2 as HJ2s.
  paj_run_tok RUN HS2 HJ2 SHOK2 tx_span.
  { cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros x Hx. unfold tx_rg in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia. }
  lazymatch goal with
  | HS' : st_ok _ _ ?ssx (restrict _ ?msn), HF' : frame_of _ _ (ms_mem ms2) (ms_mem ?msn)
    |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    assert (Hmem : ms_mem msn = ms_mem ms2)
      by (apply functional_extensionality; intros x; apply HF';
          intros (rr & Hin' & Hw); cbn [ss_mem In] in Hin'; destruct Hin' as [<-|[]];
          unfold tx_rg in Hw; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; lia);
    assert (HMS' : kms KP_ATEXT msn)
      by (apply (tx_kms_of _ E2 ssx msn KP_ATEXT HS');
          [vm_compute; reflexivity | cbn [ss_pc setpc]; exact tx_sigma_atext]);
    assert (HR0' : kregs0 cx msn)
      by (apply (kregs0_keep cx ms2 msn); [|exact HR02];
          exact (regs_kept_of_st_ok SEGS E2 ssx (restrict (w_H W3) msn) (ms_regs ms2) (@nil word) nx_keep0 HS'
                   HAG2 ltac:(vm_compute; reflexivity)));
    assert (HKN : forall r, In r [21; 22; 24; 25]%nat ->
              getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms2) (Z_to_bv 5 (Z.of_nat r)))
      by (intros r Hr;
          exact (regs_kept_of_st_ok SEGS E2 ssx (restrict (w_H W3) msn) (ms_regs ms2) (@nil word)
                   (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 22; 24; 25]%nat) HS' HAG2
                   ltac:(vm_compute; reflexivity) _ (kn_in_map5 r _ Hr)));
    assert (Rr19 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 19)) = w64 (ka0 cx + 8))
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E2 ssx msn (Z_to_bv 5 (Z.of_nat 19)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 19))) with (SOff 18 8) by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite B18; reflexivity);
    assert (Hrl' : kregs_eq msn (tx_rl' cx fpos left))
      by (unfold kregs_eq, tx_rl'; apply Forall_cons; [exact Rr19|];
          unfold kregs_eq, tx_rl0 in HRL02; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          rewrite HKN by kn_in; apply (kn_reg_in ms2 _ _ _ HRL02); kn_in);
    assert (Rr1b : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 1)) = w64 (BASE + kpc KP_ALAT))
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E2 ssx msn (Z_to_bv 5 (Z.of_nat 1)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 1))) with (SOff 240 9896)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite (img_env_codeptr E2 HEI2 9896); unfold w64;
          f_equal; try (unfold kpc, AF_kernel, KP_ALAT; lia));
    assert (Rr10 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 10)) = w64 (kW2 cx fpos))
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E2 ssx msn (Z_to_bv 5 (Z.of_nat 10)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 10))) with (SOff 21 0)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite B21, Z.add_0_r; reflexivity);
    assert (Rr12 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 12)) = w64 LA_LONG_ALIAS)
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E2 ssx msn (Z_to_bv 5 (Z.of_nat 12)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 12))) with (SOff 19 0)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite B19, Z.add_0_r; reflexivity);
    assert (Hfds : m_fds mdn = m_fds md2) by exact (proj1 (wvb_fds_fs _ _ _));
    assert (Hfs : m_fs mdn = m_fs md2) by exact (proj2 (wvb_fds_fs _ _ _));
    pose proof (katstr_la cx fpos k2 ly3 S3 W3 ms2 md2 HB HJ2s HJB2 HKK2 Hset HLA2) as HST;
    exact (tx_call SK B LAWS LV KI ATEXT POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms2 msn md2 mdn 0xafc _ _
             c ci j m k n f adv hd kd left LA_LONG_ALIAS tx_la HN HB ltac:(assumption) HFR HRc HRm HRa Hc1 Hci Hj
             Hm Hk Hkd Hl Hhd HW2 eq_refl HAT2 HMS' HR0' Hrl' Rr1b Rr10 Rr12 Hmem Hfds Hfs HST)
  end.
Qed.


(* ---- THE PHASE: kin_txt (+0xa74) -> the six cases of a % 6 ---- *)
Theorem kn_txt : forall POST Rc Rm Ra,
  kfrom SK B POST (kin_alat B Rc Rm Ra) -> kfrom SK B POST (kin_acase B Rc Rm Ra KP_A23 ka_23) ->
  kfrom SK B POST (kin_acase B Rc Rm Ra KP_A5 ka_5) -> kfrom SK B POST (kin_txt B Rc Rm Ra).
Proof.
  intros POST Rc Rm Ra HN H23 H5 cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (a & p & Ha & Htx & HT & HAT).
  pose proof (Z.mod_pos_bound a 6 ltac:(lia)) as Hm.
  assert (Hc : a mod 6 = 0 \/ a mod 6 = 1 \/ (a mod 6 = 2 \/ a mod 6 = 3) \/ a mod 6 = 4 \/ a mod 6 = 5) by lia.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|Hc]]]].
  - assert (K : kfrom SK B POST (kin_txtc B Rc Rm Ra (fun x => x = 0))) by (eapply tx_c0_ph; eassumption).
    apply (K cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR). exists a, p. tauto.
  - assert (K : kfrom SK B POST (kin_txtc B Rc Rm Ra (fun x => x = 1))) by (eapply tx_c1_ph; eassumption).
    apply (K cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR). exists a, p. tauto.
  - assert (K : kfrom SK B POST (kin_txtc B Rc Rm Ra (fun x => x = 2 \/ x = 3))) by (eapply tx_c23_ph; eassumption).
    apply (K cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR). exists a, p. tauto.
  - assert (K : kfrom SK B POST (kin_txtc B Rc Rm Ra (fun x => x = 4))) by (eapply tx_c4_ph; eassumption).
    apply (K cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR). exists a, p. tauto.
  - assert (K : kfrom SK B POST (kin_txtc B Rc Rm Ra (fun x => x = 5))) by (eapply tx_c5_ph; eassumption).
    apply (K cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR). exists a, p. tauto.
Qed.

End b.
End a.

Print Assumptions kn_txt.
