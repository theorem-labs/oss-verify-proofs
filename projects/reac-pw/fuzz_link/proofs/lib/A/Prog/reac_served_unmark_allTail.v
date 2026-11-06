(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v; 2133 of its 2182 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/nl_talk_sock.v, with its module paths and module names changed; 331 of its 411 lines of code are new or changed and 2102 lines of the source are left out. *)
(* reac_served_unmark_all (fuzz_link.asan 0x89ed4, listing offset AF_reac_served_unmark_all = 0x7d08) on image A, THE
   TAIL PIECE: from the TAIL cut (+0x340) to the RELEASE cut (+0x350). It proves reac_served_unmark_allDefs.v's
   obligation `um_tail_obl` from `um_rel_obl`.

   The code (listing (internal path) (internal record, sha256 9bc7ee7c887a)):
     +0x340  addi a2, zero, 0x204        516 = MK_SIZE, the whole marks block
     +0x344  mv   a0, s4                 m
     +0x348  mv   a1, zero
     +0x34c  jal  checked_memset         (0x53214), returning at +0x350
   The four instructions are one token run (LinkWalk.v paj_run_x) seated at the cut with no memory region; it stops
   at the call. checked_memset is link_ajkit.v `aj_gx_intrin_at` (op OSet) over HMS. At the RELEASE cut the body is
   done: the marks block is 516 zeros (marks_wf, n = 0), the fake kernel is um_kinv's at c = n, which is the
   whole loop's `unmark` result, and um_base still holds (the fill touched only the block, which is in the
   contract's write set, and frame_alloc's scratch window below s1).

   HSEGS (pa_segs = tfibsegs) gives: a byte of G that the write set holds is writable at every memory (it lies in a
   writable segment, LinkWalkWseg.v wseg_writable_tfib).

   Proves no function (kind: segment lemma of reac_served_unmark_all's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_unmark_all_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LinkWalk LinkWalkPi LinkWalkSide LinkWalkCall LinkWalkShadow LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_unmark_allDefs reac_served_unmark_allWriteKit reac_served_unmark_allWrite.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkWseg.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* No global sink_head instance is in scope: every journal below is the Section's SK. *)
Fail Definition sink_head_probe_um_tail : YI16.sink_head := _.

(* the symbolic state seated at the TAIL cut: the registers as atoms, no memory region *)
Definition ut_ss : sstate := mkSS (AF_reac_served_unmark_all + 0x340) sr_atoms [] None (mkFacts [] [] []).

(* an image byte off the read-only set is writable at every memory (its segment is writable: LinkWalkWseg.v) *)
Lemma ut_img_rw_writable : forall segs rlo rhi a (m : word -> option byte), segs = AB1v.tfibsegs ->
  in_img segs a -> ~ in_roP segs rlo rhi a -> writable_at segs m a.
Proof.
  intros segs rlo rhi a m -> (s & Hs & Hr) Hro. apply wseg_writable_tfib.
  exists s. split; [exact Hs|]. split; [|exact Hr].
  destruct (seg_writable s) eqn:Hw; [reflexivity|].
  exfalso. apply Hro. left. exists s. split; [exact Hs|]. split; [exact Hw | exact Hr].
Qed.

Lemma ut_mk_names_length : forall gbs, length (mk_names gbs) = Z.to_nat (mk_n gbs).
Proof. intros gbs. unfold mk_names. rewrite length_map, length_seq. reflexivity. Qed.

Lemma ut_zeros_n : mk_n (repeat (zb 0) 516) = 0.
Proof. vm_compute. reflexivity. Qed.

Section s.
Variable segs : list Segment.

(* the interface table read off a memory that agrees with it on g_nl and on each table string *)
Lemma ut_aiftab_move : forall (m m' : word -> option byte) bs tab, aiftab_at segs m LA_G_NL bs tab ->
  (forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> mbyte segs m' x = mbyte segs m x) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) -> au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
     acstr_at segs m p n2 -> forall x, p <= x <= p + Z.of_nat (length n2) -> mbyte segs m' x = mbyte segs m x) ->
  aiftab_at segs m' LA_G_NL bs tab.
Proof.
  intros m m' bs tab (L & L80 & H) HG HS. split; [exact L|]. split; [exact L80|].
  intros i nm ix E. destruct (H i nm ix E) as (R & p & P & Pn & C & X).
  assert (Hi : (i < length tab)%nat) by (apply nth_error_Some; congruence).
  split; [exact R|]. exists p.
  split; [apply (uw_vm_move segs _ _ _ _ _ P); intros x Hx; apply HG; unfold NK_IF_NAME, NK_SIZE in *;
          change (Z.of_nat 8) with 8 in Hx; lia|].
  split; [exact Pn|].
  split; [apply (uw_acstr_move segs _ _ _ _ C); exact (HS i nm ix p E P C)|].
  apply (uw_vm_move segs _ _ _ _ _ X). intros x Hx. apply HG. unfold NK_IF_INDEX, NK_SIZE in *.
  change (Z.of_nat 4) with 4 in Hx. lia.
Qed.

End s.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : AF0m.PcapSyms B.
Hypothesis HSEGS : SEGS = AB1v.tfibsegs.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
(* checked_memset (0x53214): lib/A/AE2r.v asan_memset_realizes *)
Hypothesis HMS : aintrin_realizes SEGS B OSet (pa_sigma LS___asan_memset).

Section c.
Variable cx : umcx.
Variable fpos : Z.
Variables (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model).
Variable kbs : list byte.
Hypothesis HPRE : um_pre SK B cx.
Hypothesis HM : um_mk cx <> 0.
Hypothesis HKI : um_kinv cx (rdW W3 (ms_mem ms3)) kbs (Z.to_nat (um_n cx)).
Hypothesis HB : um_base SK B cx fpos ly3 S3 W3 ms3 md3.

#[local] Notation own' := ((UM_CID, fpos) :: um_own cx).
#[local] Notation AJ ly S W m md :=
  (ajournal_gx SEGS B (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx)
     (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) ((UM_CID, fpos) :: um_own cx) ly S W m md (um_k cx)).
#[local] Notation Ec := (fun a => um_E cx a \/ aside_rng (um_lyc cx) UM_CID fpos a).
#[local] Notation m3 := (ms_mem ms3).
#[local] Notation R3 := (ms_regs ms3).

Lemma ut_n32 : 0 <= um_n cx <= 32.
Proof.
  pose proof (uw_mkf SK B cx HPRE HM) as (_ & _ & _ & _ & _ & _ & _ & _ & (Hn & _)).
  unfold um_n, MARKS_MAX in *. lia.
Qed.

(* a byte of the contract's write set off the read-only set is writable at every later state of the journal *)
Lemma ut_ajw_w : forall a ly4 S4 (W4 : world SEGS) m4 md4,
  inFP (um_wr cx) a -> AJ ly4 S4 W4 m4 md4 ->
  Permutation (ablocks B ly4 S4) (ablocks B (um_lyc cx) (um_Sc cx)) ->
  (forall c' q, frame_addr ly4 c' q = frame_addr (um_lyc cx) c' q) ->
  writable_at SEGS (rdW W4 m4) a.
Proof.
  intros a ly4 S4 W4 m4 md4 Ha HJ4 Hperm Hfa.
  pose proof (uw_pajw SK B cx HPRE a Ha) as Hw. pose proof (uw_pnro SK B cx HPRE a Ha) as Hro.
  pose proof (uw_pg SK B cx HPRE) as HGX.
  pose proof HJ4 as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  assert (Hbl : forall b m, In (b, m) (ablocks B (um_lyc cx) (um_Sc cx)) -> In (b, m) (ablocks B ly4 S4))
    by (intros b m Hin; apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
  destruct Hw as [(Haw & Hno) | [HGa | (HO & Hout)]].
  - destruct Haw as [Hs | Haw].
    + apply (apresent_writable SEGS). apply Hpres. lia.
    + apply (apresent_writable SEGS).
      refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi _)).
      destruct Haw as [(Hf & b & n & Hin & Hr) | [(b & n & Hin & Hn0 & Hr) | (c & q & Hin & Hr)]].
      * right; left. split; [exact Hf|]. exists b, n. split; [exact (Hbl b n Hin) | exact Hr].
      * right; right; left. exists b, n. split; [exact (Hbl b n Hin)|]. split; [exact Hn0 | exact Hr].
      * right; right; right. exists c, q. split; [right; exact Hin|]. rewrite !Hfa. exact Hr.
  - destruct (HGX a HGa) as (Hi & _). exact (ut_img_rw_writable SEGS PCAP_RLO PCAP_RHI a _ HSEGS Hi Hro).
  - apply (apresent_writable SEGS). apply Hpres. lia.
Qed.

(* the strings of the table at the cut, read off as at the call: apart from the block and from the stack *)
Lemma ut_tab_str : forall i n2 ix p, nth_error (um_tab cx) i = Some (n2, ix) ->
  au64_at SEGS (rdW W3 m3) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  acstr_at SEGS (rdW W3 m3) p n2 ->
  (p + Z.of_nat (length n2) + 1 <= um_mk cx \/ um_mk cx + MK_SIZE <= p) /\
  (p + Z.of_nat (length n2) + 1 <= um_sp cx - 8768 \/ um_sp cx <= p).
Proof.
  intros i n2 ix p Hn Hp Hc.
  destruct (uw_tab_entry SK B cx fpos ly3 S3 W3 ms3 md3 HPRE HM HB i n2 ix p Hn Hp)
    as (p0 & Ep & H0 & Hr0 & _ & _ & _ & Hrt & _ & _ & Hm).
  pose proof (uw_acstr_range SEGS _ _ _ Hc) as Hrp. rewrite Z.mod_small in Ep by lia. subst p0.
  destruct Hrt as (_ & _ & T3 & _ & _ & _ & T7). unfold apart_frame, apart, amem_range in T3, T7, Hm.
  fold (um_sp cx) in T7. pose proof (uw_sp_rng cx) as Hsp.
  pose proof asan_consts as ((AC1 & AC2) & _ & C3 & C4 & C5).
  split; [lia|]. lia.
Qed.

(* ---- the memset and the RELEASE cut ---- *)
Section d.
Variable R' : bvmap 5 word.
Variable md' : Model.
Hypothesis RC10 : getr R' 10 = w64 (um_mk cx).
Hypothesis RC11 : getr R' 11 = w64 0.
Hypothesis RC12 : getr R' 12 = w64 MK_SIZE.
Hypothesis RC1 : getr R' 1 = w64 (BASE + UM_CUT_REL).
Hypothesis RCP : aregs_preserved R3 R'.
Hypothesis HJ' : AJ ly3 S3 W3 m3 md'.
Hypothesis Hfd' : m_fds md' = m_fds md3.
Hypothesis Hfs' : m_fs md' = m_fs md3.

Lemma ut_spc : spZ R' = um_sp1 cx.
Proof.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & _).
  pose proof (uw_geo SK B cx HPRE) as (_ & G2 & _ & G4 & _ & G6 & _ & _ & _ & _ & G11).
  pose proof (uw_sp_rng cx).
  unfold spZ. transitivity (bv_unsigned (getr R3 2)).
  - f_equal. uw_pr RCP 2.
  - rewrite R2. unfold w64. apply unsigned_lit_small. lia.
Qed.

Lemma ut_rel : forall (regs2 : bvmap 5 word) mem2 md2,
  AJ ly3 S3 W3 mem2 md2 -> aregs_preserved R' regs2 ->
  (forall i, 0 <= i < MK_SIZE -> aview SEGS (w_H W3) mem2 (um_mk cx + i) = Some (0 mod 256)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (um_mk cx <= a < um_mk cx + MK_SIZE) -> ~ (spZ R' - ESTACK <= a < spZ R') ->
     aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) m3 a) ->
  (forall a, apresent (w_H W3) m3 a -> apresent (w_H W3) mem2 a) ->
  same_but_materialized md' md2 ->
  um_gi_rel SK B cx fpos ly3 S3 W3 (mkst regs2 (w64 (BASE + UM_CUT_REL)) mem2 (seg_rom SEGS)) md2.
Proof.
  intros regs2 mem2 md2 HJ2 HPR2 HEFF HFR HPRES HSBM.
  rewrite ut_spc in HFR. assert (Hes : ESTACK = 4096) by reflexivity. rewrite Hes in HFR.
  pose proof (uw_geo SK B cx HPRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (uw_sp_rng cx) as Hsp.
  pose proof (uw_mkf SK B cx HPRE HM) as (Mk0 & Mkr & MkR & MkH & Mkf & Mkg & Mke & Mka & Mkw).
  pose proof (uw_mk_rng SK B cx HPRE HM) as (Mk1 & Mk2).
  pose proof uw_consts as (_ & _ & _ & _ & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & _ & _ & C16 & C17 & C18 & _).
  pose proof asan_consts as ((AC1 & AC2) & _ & _ & AC5 & _).
  unfold apart_frame, apart_gnl, apart, amem_range in Mkr, Mkf, Mkg, Mke. fold (um_sp cx) in Mkf.
  (* the bytes the fill kept: off the block, above s1 - 4096 *)
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (um_mk cx <= a < um_mk cx + MK_SIZE) ->
    ~ (um_sp1 cx - 4096 <= a < um_sp1 cx) -> mbyte SEGS (rdW W3 mem2) a = mbyte SEGS (rdW W3 m3) a).
  { intros a Ha H1 H2. apply uw_mbyte_eq. exact (HFR a Ha H1 H2). }
  assert (HIE : PcapImgEnd.pcap_img_end = 0x654000) by reflexivity.
  unfold um_gi_rel. cbn [ms_regs ms_mem mkst].
  split; [reflexivity|].
  split.
  { (* the contract's Post at the memory after the fill *)
    split; [intros H0; exfalso; exact (HM H0)|].
    intros _ kbs1 tab1 gbs1 Hnl1 Hif1 Hmk1. cbv zeta. change (aarg (um_regs cx) 0) with (um_mk cx) in Hmk1 |- *.
    pose proof (uw_pnl SK B cx HPRE) as (HNL0 & HWF0 & HOP0 & HO0 & HC0 & HIF0 & _).
    rewrite (uw_anlk_unique SEGS _ _ _ _ Hnl1 HNL0) in Hif1 |- *.
    rewrite (uw_aiftab_unique SEGS _ _ _ _ Hif1 HIF0).
    assert (Eg : gbs1 = um_gbs cx).
    { destruct Hmk1 as ((B1 & _) & L1). destruct Mka as ((B2 & _) & L2).
      apply (uw_abytes_unique SEGS _ _ _ _ B1 B2). lia. }
    subst gbs1. clear Hnl1 Hif1 Hmk1.
    change (unmark (um_tab cx) (mk_names (um_gbs cx)) (nk_sent (um_kbs cx)) (nk_kstate (um_kbs cx))) with (um_U cx).
    pose proof HKI as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
    assert (Esk : skipn (Z.to_nat (um_n cx)) (um_names cx) = []).
    { apply skipn_all2. unfold um_names, um_n. rewrite ut_mk_names_length. lia. }
    rewrite Esk in K7. cbn [unmark_walk] in K7.
    split.
    - (* the block: 516 zeros *)
      exists (repeat (zb 0) 516).
      split; [|split; [unfold marks_wf; rewrite ut_zeros_n; split; [unfold MARKS_MAX; lia | intros i Hi; lia] | exact ut_zeros_n]].
      split; [|rewrite repeat_length; exact (eq_sym C10)].
      split.
      + split; [lia|]. split; [rewrite repeat_length; lia|].
        intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi.
        destruct (aview_byte SEGS _ _ _ _ (HEFF (Z.of_nat i) ltac:(lia))) as (b & Hb & Hv & _).
        rewrite Hb. f_equal. apply uw_byte_zero. rewrite <- Hv. reflexivity.
      + intros i Hi. rewrite repeat_length in Hi.
        apply (ut_ajw_w (um_mk cx + i) ly3 S3 W3 mem2 md2 (uw_wr_mk cx (um_mk cx + i) HM ltac:(lia)) HJ2
          (uw_bperm SK B cx fpos ly3 S3 W3 ms3 md3 HB) (uw_bfa SK B cx fpos ly3 S3 W3 ms3 md3 HB)).
    - (* the fake kernel: um_kinv's at c = n, the whole loop *)
      exists kbs.
      assert (KG : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> mbyte SEGS (rdW W3 mem2) x = mbyte SEGS (rdW W3 m3) x).
      { intros x Hx. apply KF; lia. }
      split.
      { destruct K1 as ((Kb & _) & KL). split; [split|exact KL].
        - apply (uw_abytes_move SEGS _ _ _ _ Kb). intros x Hx. apply KG. lia.
        - intros i Hi. assert (Hw : forall s0, s0 = AB1v.tfibsegs ->
            writable_at s0 (rdW W3 mem2) (LA_G_NL + i)) by (intros s0 ->; apply uw_rw_window; lia).
          exact (Hw SEGS HSEGS). }
      pose proof K2 as (W1 & W2 & W3' & _).
      split; [exact K2|]. split; [exact K4|]. split; [exact K5|]. split; [exact K6|].
      split.
      { apply (ut_aiftab_move SEGS _ _ _ _ K3 KG).
        intros i n2 ix p Hn Hp Hc x Hx.
        pose proof (uw_acstr_range SEGS _ _ _ Hc) as Hrp.
        destruct (ut_tab_str i n2 ix p Hn Hp Hc) as (D1 & D2).
        apply KF; [lia | lia | lia]. }
      split; [rewrite <- K7; unfold nk_kstate; cbn [snd k_next]; rewrite Z2Nat.id by lia; reflexivity|].
      split; [rewrite <- K7; reflexivity|].
      split; [rewrite <- K7; cbn [fst]; unfold nk_sent; rewrite length_map, length_seq, Z2Nat.id by lia; reflexivity|].
      split; [exact K8|]. split; [exact K9|]. split; [exact K10|].
      pose proof ut_n32. unfold MARKS_MAX. lia. }
  (* um_base at the RELEASE cut *)
  pose proof HB as (_ & _ & _ & _ & _ & _ & Hfr3 & Hnin & HfS & Hperm & HS1 & Hfa & B2 & B9 & B8 & B18 & B19 & B25
    & B20 & B3 & B4 & Bra & Bsv & Bfl & _ & _ & HK3 & Bfd & Bfs & Bro).
  pose proof (uw_aj_ar SK B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  pose proof (uw_fin3 SK B cx fpos ly3 S3 W3 ms3 md3 HB) as Hfin3.
  pose proof (uw_F SK B LAWS cx fpos ly3 S3 W3 ms3 md3 HB) as (F1 & F2 & F3 & F4).
  destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR2 Hfin3) as (_ & _ & HFp & HSp).
  rewrite F4 in HFp, HSp. change (fs_frame_bytes UM_CID) with 512 in HFp, HSp. change (512 / 8) with 64 in HSp.
  assert (PR : forall k (x : bv 5), acallee_saved k -> bv_unsigned x = k -> getr regs2 x = getr R3 x).
  { intros k x Hk Hx. rewrite (uw_pres R' regs2 k x HPR2 Hk Hx). exact (uw_pres R3 R' k x RCP Hk Hx). }
  (* the block never meets F (a side frame free at the call) *)
  assert (NBF : forall a, um_mk cx <= a < um_mk cx + MK_SIZE -> ~ (um_F cx fpos <= a < um_F cx fpos + 512)).
  { intros a Ha HF.
    pose proof (uw_fpos SK B cx fpos ly3 S3 W3 ms3 md3 HB) as Hp.
    pose proof (uw_bfr SK B cx fpos ly3 S3 W3 ms3 md3 HB) as (_ & NIN).
    refine (ajw_not_side SK SEGS B LAWS pa_img_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ UM_CID fpos a
      (uw_pg SK B cx HPRE) (uw_pj SK B cx HPRE) ltac:(unfold UM_CID; lia) Hp NIN
      (uw_pajw SK B cx HPRE a (uw_wr_mk cx a HM Ha)) ltac:(lia) _).
    left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes UM_CID) with 512. fold (um_F cx fpos). lia. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HJ2|].
  split; [exact Hfr3|]. split; [exact Hnin|]. split; [exact HfS|]. split; [exact Hperm|].
  split; [exact HS1|]. split; [exact Hfa|].
  cbn [ms_regs ms_mem mkst].
  split; [etransitivity; [uw_prr PR 2 | exact B2]|].
  split; [etransitivity; [uw_prr PR 9 | exact B9]|].
  split; [etransitivity; [uw_prr PR 8 | exact B8]|].
  split; [etransitivity; [uw_prr PR 18 | exact B18]|].
  split; [etransitivity; [uw_prr PR 19 | exact B19]|].
  split; [etransitivity; [uw_prr PR 25 | exact B25]|].
  split; [etransitivity; [uw_prr PR 20 | exact B20]|].
  split; [etransitivity; [uw_prr PR 3 | exact B3]|].
  split; [etransitivity; [uw_prr PR 4 | exact B4]|].
  split; [rewrite <- Bra; apply uw_rdword_ext; intros i Hi; apply HFR; lia|].
  split; [intros j Hj; rewrite <- (Bsv j Hj); apply uw_rdword_ext; intros i Hi; apply HFR; lia|].
  split.
  { rewrite <- Bfl. apply uw_rdword_ext. intros i Hi. unfold UM_FLAGPTR in *. apply HFR; [lia | | lia].
    intros Hb. exact (NBF _ Hb ltac:(lia)). }
  split; [intros a Ha; exact (proj1 (HFp a Ha))|].
  split.
  { intros a Ha. unfold um_SH in Ha. replace a with (shadow_addr (um_F cx fpos) + (a - shadow_addr (um_F cx fpos)))
      by (unfold shadow_addr; lia).
    apply (proj1 (HSp (a - shadow_addr (um_F cx fpos)) ltac:(unfold shadow_addr; unfold UM_SHN in Ha; lia))). }
  split.
  { apply (akept_step SK SEGS B LAWS pa_segs_low (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx) W3 m3 W3 mem2
      (um_sp cx - 8768) (um_sp cx) Ec Ec
      (fun a => (um_mk cx <= a < um_mk cx + MK_SIZE) \/ (um_sp1 cx - 4096 <= a < um_sp1 cx))
      (uw_par SK B cx HPRE) ltac:(lia) ltac:(lia) HK3).
    - intros a Ha Hx. apply HFR; [exact Ha | intros H; apply Hx; left; exact H | intros H; apply Hx; right; exact H].
    - intros a _ Hp. exact (HPRES a Hp).
    - intros a H. exact H.
    - intros a [Ha | Ha]; [left; left; exact (uw_wr_mk cx a HM Ha) | right; lia]. }
  unfold same_but_materialized in HSBM.
  split; [rewrite HSBM, (proj1 (wvb_fds_fs _ _ _)), Hfd'; exact Bfd|].
  split; [rewrite HSBM, (proj2 (wvb_fds_fs _ _ _)), Hfs'; exact Bfs|].
  intros a Hro Ho He. pose proof (uw_roP_img RELRO_IMG a Hro) as Hi. pose proof (pa_img_range a Hi) as Hir.
  rewrite (HFR a ltac:(lia)).
  - exact (Bro a Hro Ho He).
  - intros Hb. exact (uw_pnro SK B cx HPRE a (uw_wr_mk cx a HM Hb) Hro).
  - lia.
Qed.

Lemma ut_call : um_rel_obl SK B ->
  SRr SEGS W3 (mkCfg (mkst R' (Z_to_bv 64 (pa_sigma LS___asan_memset)) m3 (seg_rom SEGS)) md') (um_post SK B cx).
Proof.
  intros HREL.
  pose proof (uw_geo SK B cx HPRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (uw_sp_rng cx) as Hsp.
  pose proof (uw_mkf SK B cx HPRE HM) as (Mk0 & Mkr & MkR & MkH & Mkf & Mkg & Mke & Mka & Mkw).
  pose proof (uw_mk_rng SK B cx HPRE HM) as (Mk1 & Mk2).
  pose proof uw_consts as (_ & _ & _ & _ & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & _ & _ & C16 & C17 & C18 & _).
  pose proof asan_consts as ((AC1 & AC2) & _ & _ & AC5 & _).
  pose proof pa_B_ok as (HB0 & HB1 & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R3e & R4e & _).
  pose proof HPRE as ((_ & _ & _ & _ & _ & Hgp & Htp & _) & _).
  assert (Hes : ESTACK = 4096) by reflexivity.
  unfold apart_frame in Mkf. fold (um_sp cx) in Mkf.
  eapply SRr_bind.
  { apply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OSet (pa_sigma LS___asan_memset) HMS (um_G cx) (um_XO cx)
      (um_OUT cx) W3 R' m3 (um_STK cx) (um_sp0 cx) (um_FP cx) (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx)
      own' ly3 S3 md' (um_k cx) (um_mk cx) 0 MK_SIZE (w64 (BASE + UM_CUT_REL)) (uw_pg SK B cx HPRE) HJ' RC10 RC11 RC12).
    - lia.
    - lia.
    - unfold amem_range in Mkr. lia.
    - rewrite ut_spc. exact G8.
    - rewrite ut_spc, Hes. lia.
    - rewrite ut_spc. lia.
    - etransitivity; [uw_pr RCP 3 | etransitivity; [exact R3e | exact Hgp]].
    - etransitivity; [uw_pr RCP 4 | etransitivity; [exact R4e | exact Htp]].
    - exact RC1.
    - apply ret_ok_codeptr_v; unfold UM_CUT_REL, AF_reac_served_unmark_all; [lia | reflexivity].
    - (* the destination: the marks block, a byte of the contract's write set *)
      intros a Ha. rewrite ut_spc, Hes.
      pose proof (ajw_mono B _ _ _ _ _ _ _ _ _ _ _ ly3 S3 own' a (uw_pajw SK B cx HPRE a (uw_wr_mk cx a HM Ha))
        (uw_blk SK B cx fpos ly3 S3 W3 ms3 md3 HB) (fun x Hx => or_intror Hx) (uw_bfa SK B cx fpos ly3 S3 W3 ms3 md3 HB))
        as Hw.
      destruct Hw as [(Haw & Hno) | [HGa | Hout]].
      + left. split; [exact Haw|]. split; [exact Hno | lia].
      + right; left. split; [exact HGa|].
        destruct (uw_pg SK B cx HPRE a HGa) as (Hi & _).
        exact (ut_img_rw_writable SEGS PCAP_RLO PCAP_RHI a _ HSEGS Hi (uw_pnro SK B cx HPRE a (uw_wr_mk cx a HM Ha))).
      + right; right. exact Hout.
    - apply (uw_amem_sub (um_mk cx) (MK_SIZE + 8)); [exact Mkr | lia | lia].
    - exact (proj1 (uw_shadow3 SK B LAWS TB cx fpos ly3 S3 W3 ms3 md3 HPRE HM HB (um_mk cx) MK_SIZE ltac:(lia)
        ltac:(intros x Hx; apply (sclass_of_ajw SK SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x
                (uw_pg SK B cx HPRE) (uw_pj SK B cx HPRE) (uw_pajw SK B cx HPRE x (uw_wr_mk cx x HM Hx)));
              unfold amem_range in Mkr; lia) MkR MkH)).
    - intros _. exact (proj2 (uw_shadow3 SK B LAWS TB cx fpos ly3 S3 W3 ms3 md3 HPRE HM HB (um_mk cx) MK_SIZE ltac:(lia)
        ltac:(intros x Hx; apply (sclass_of_ajw SK SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x
                (uw_pg SK B cx HPRE) (uw_pj SK B cx HPRE) (uw_pajw SK B cx HPRE x (uw_wr_mk cx x HM Hx)));
              unfold amem_range in Mkr; lia) MkR MkH)).
    - exact I. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR2 & _ & HEFF & HFR & HPRES & HSBM).
  exact (HREL cx fpos ly3 S3 W3 _ md2 HPRE (ut_rel regs2 mem2 md2 HJ2 HPR2 HEFF HFR HPRES HSBM)).
Qed.

End d.
End c.

(* ==========================================================================
   The run of the four instructions, and the piece
   ========================================================================== *)

Theorem um_tail : um_rel_obl SK B -> um_tail_obl SK B.
Proof.
  intros HREL cx fpos ly3 S3 W3 ms3 md3 HPRE (Hpc & HM & HMK & (kbs & HKI) & HB).
  pose proof HB as (Hrv & Hsv & Hrom & Hfr & Hfc & HJ3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R20 & _).
  pose proof (uw_ms_eta ms3 (Z_to_bv 64 (BASE + UM_CUT_TAIL)) (seg_rom SEGS) Hrv Hsv Hrom Hfr Hfc Hpc) as Hms.
  remember (Eimg (Ereg (ms_regs ms3) uw_extra)) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (EREG : forall r : nat, (r < 32)%nat -> ew E r = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r))).
  { intros r Hr. subst E. apply ew_Eimg_Ereg_nat.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
    symmetry. apply Z.mod_small. lia. }
  assert (HS : st_ok_pi SEGS VAL E ut_ss (restrict (w_H W3) ms3)).
  { rewrite Hms. rewrite restrict_mkst_fx. unfold ut_ss.
    apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint]. exact I.
    - split; [|split]; exact I. }
  assert (SHOK : sh_ok SEGS uwBx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by (apply Forall_nil).
  pose (RUN := paj_run_x SK B LAWS (um_G cx) (uw_pg SK B cx HPRE) (um_XO cx) (um_OUT cx)).
  clear Hms.
  (* +0x340 .. +0x34c: addi a2, zero, 0x204; mv a0, s4; mv a1, zero; jal checked_memset *)
  paj_run_tok RUN HS HJ3 SHOK uwSpan.
  { unfold ut_ss. cbn [ss_mem]. apply awr_ok_x_nil. }
  pmkst HS.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (1%bv : bv 5) Q1.
  assert (Em : ms_mem ms = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF. intros (r & [] & _). }
  rewrite Em in HJ3 |- *.
  apply (ut_call cx fpos ly3 S3 W3 ms3 md3 kbs HPRE HM HKI HB (ms_regs ms) _).
  - rewrite Q10, (EREG 20%nat ltac:(lia)).
    transitivity (getr (um_regs cx) 10); [exact R20|].
    transitivity (Z_to_bv 64 (bv_unsigned (getr (um_regs cx) 10))); [symmetry; apply Z_to_bv_bv_unsigned | reflexivity].
  - rewrite Q11. reflexivity.
  - rewrite Q12. reflexivity.
  - rewrite Q1. reflexivity.
  - intros k Hk. unfold acallee_saved in Hk.
    assert (Hk' : k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/
                  k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
    clear Hk.
    repeat (destruct Hk' as [-> | Hk']; [
      lazymatch goal with |- getr _ (Z_to_bv 5 ?kk) = _ =>
        let n := eval vm_compute in (Z.to_nat kk) in
        let Hr := fresh "Hr" in
        prreg HS (Z_to_bv 5 kk) Hr; rewrite Hr, (EREG n ltac:(lia)); reflexivity
      end |]).
    subst k.
    prreg HS (Z_to_bv 5 27) Hr; rewrite Hr, (EREG 27%nat ltac:(lia)); reflexivity.
  - exact HJ3.
  - rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  - rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
  - exact HREL.
Qed.

About um_tail.
Print Assumptions um_tail.

End b.
End a.
