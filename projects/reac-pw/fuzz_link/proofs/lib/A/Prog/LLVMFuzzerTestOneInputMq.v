(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 361 of its 425 lines of code are new or changed and 340 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputDec.v; 421 of its 544 lines of code are new or changed and 302 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): the call of
   mark_quietly (0x883d4; lib/A/Prog/mark_quietly_c.v) from the walk, at op_refused's site 0x831f8 (ra 0x831fc) and op_mark's
   0x8347c (ra 0x83480), both with sp = s1 and a0 = the marks block or NULL. This file states, for both sites:
   1. the image facts mark_quietly's Pre names, by computation over the pin's segments (the policy strings, the empty
      string .str.1 0x20fc0 that op_refused passes, the mode string "w", the writable globals g_sink / g_say / g_said and
      errno, and the zero shadow of g_said);
   2. the interface table's strings at the call: where each entry's pointer points (lf_ifp) and astr_rt_ok of its
      string;
   3. `lf_amq_common`: reac_served_mark's premises amq_common at the call, from the interface's cut clauses, for any
      name the caller supplies with its own facts.
   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom AF0m AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputSu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
  model_decide_c remember_c reac_code_emit_c reac_served_mark_c mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YK1d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. The image facts, by computation
   ========================================================================== *)

(* the read-only strings mark_quietly's Pre names, with the bytes the pin holds there *)
Definition mq_pol : list (Z * list byte) :=
  [(LA_RSD_PREFIX, S_PREFIX); (LA_RSD_VLAN, S_VLAN); (LA_S_SERVED, S_SERVED); (LA_FMT_S, S_FMT_S);
   (LA_FMT_SS, S_FMT_SS); (LA_S_REACPW, S_REACPW); (LA_S_E_NOT_MARKED, S_E_NOT_MARKED);
   (LA_S_READERR, S_STR3); (LA_S_WRITEERR, S_STR5); (LA_S_VLANLINE, S_STR8); (LA_S_OWNALIAS, S_STR9);
   (LA_S_NOCAP, S_STR6); (LA_S_EMPTY, []); (LA_STR1, []); (LA_MODE_STR, S_MODE_W)].

Definition mq_img_b (segs : list Segment) (own : list (Z * Z)) (err : Z) : bool :=
  forallb (fun e => kp_kstr_b segs own err (fst e) (map bv_unsigned (snd e))) mq_pol
  && kp_akbs_b segs own err LA_STR1 1
  && kp_ra_b LA_G_SAID SAID_SIZE && kp_hull_b LA_G_SAID SAID_SIZE.

Lemma mq_img_checks : mq_img_b tfibsegs Tfib_owned_static TFIB_ERRNO = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mq_wseg_sink : YK1d.wseg_ok tfibsegs (Z_to_bv 64 LA_G_SINK) (Z.to_nat 8) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mq_wseg_say : YK1d.wseg_ok tfibsegs (Z_to_bv 64 LA_G_SAY) (Z.to_nat 8) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mq_wseg_said : YK1d.wseg_ok tfibsegs (Z_to_bv 64 LA_G_SAID) (Z.to_nat SAID_SIZE) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mq_wseg_errno : YK1d.wseg_ok tfibsegs (Z_to_bv 64 TFIB_ERRNO) (Z.to_nat 4) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mq_byte_list : forall s : list byte, map (Z_to_bv 8) (map bv_unsigned s) = s.
Proof.
  induction s as [|b s IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal. apply Z_to_bv_bv_unsigned.
Qed.

(* The bytes past a heap block, to the next multiple of 16 of its size, are visible at every AR state:
   reac_served_markKitAt.v srm_blk_tail_vis16 (libreac/fuzz_boxreg BoxTailVis.v ar_blk_tail_vis), restated here
   because that walk file does not build on W6's contract until its lane updates it. *)
Section tv. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

Lemma mq_chunk_tail_in_ajunk : forall ly S k, In k (st_chunks S) ->
  In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S).
Proof.
  intros ly S k Hk. unfold ajunk. right. right.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_flat_map. exists k. split; [exact Hk|].
  unfold chunk_junk. cbv zeta.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
Qed.

Lemma mq_chunk_room_mod16 : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) ->
  (ck_extent k - ck_rz k) mod 16 = 0.
Proof.
  intros ly S rd k M Hk.
  pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & RZ & _ & _ & G).
  assert (EX : ck_extent k mod 16 = 0).
  { destruct (ck_beg k) as [|off|r o|c q]; try solve [destruct G].
    - cbv zeta in G. destruct G as (Gc & _ & _ & Gext & _).
      pose proof (class_ok (prim_class off) ltac:(lia)) as (_ & K2 & _). rewrite Gext.
      apply Z.mod_divide in K2 as [q K2]; [|lia]. rewrite K2. replace (q * 32) with ((q * 2) * 16) by lia.
      apply Z.mod_mul. lia.
    - destruct G as (_ & Hp & _ & Gext & _). pose proof (secondary_geometry (ck_req k)) as SG.
      pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & _ & Hn & _).
      destruct (SG ltac:(lia) Hp) as (_ & _ & _ & _ & S5 & _). rewrite Gext.
      apply Z.mod_divide in S5 as [q S5]; [|unfold kPage; lia]. rewrite S5. unfold kPage.
      replace (q * 4096 - 4096) with ((q * 256 - 256) * 16) by lia. apply Z.mod_mul. lia. }
  apply Z.mod_divide in EX as [a EX]; [|lia]. apply Z.mod_divide in RZ as [b RZ]; [|lia].
  rewrite EX, RZ. replace (a * 16 - b * 16) with ((a - b) * 16) by lia. apply Z.mod_mul. lia.
Qed.

Lemma mq_blk_tail_vis16 : forall ly S (W : world segs) mem md p n a,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p + n <= a < p + round_up n 16 -> aview segs (w_H W) mem a <> None.
Proof.
  intros ly S W mem md p n a (M & _) Hb Ha.
  unfold ablocks, blocks in Hb. apply in_map_iff in Hb as ([u r] & Eb & Hb). cbn [fst snd] in Eb.
  injection Eb as Ep En.
  apply in_map_iff in Hb as (k & Ek & Hk). injection Ek as Eu Er. subst u r.
  apply filter_In in Hk as [Hk _].
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & UA & _ & _ & Hn & HX & _).
  pose proof (mq_chunk_room_mod16 ly S _ k M Hk) as R16.
  assert (N1 : 1 <= n).
  { destruct (Z.eq_dec n 0) as [->|]; [|lia]. unfold round_up in Ha. cbn in Ha. lia. }
  assert (CN : ck_n k = n) by (unfold ck_n, req_size; destruct (Z.eqb_spec (ck_req k) 0); lia).
  assert (RU : round_up n 16 <= ck_extent k - ck_rz k).
  { apply round_up_le; [lia | | exact R16]. unfold ck_n in CN. lia. }
  pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ M) _ (mq_chunk_tail_in_ajunk ly S k Hk)) as V.
  unfold range_vis in V. cbn [fst snd] in V. rewrite CN in V.
  rewrite aeval_aoff in V by (intros e'; destruct (ck_beg k); cbn; discriminate).
  change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
  replace a with (ck_base B ly k + (ck_rz k + n) + (a - (ck_base B ly k + (ck_rz k + n)))) by lia.
  apply V. rewrite <- Ep, UA in Ha. lia.
Qed.
End tv.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.

(* lf_data but marks_are: op_mark calls mark_quietly after its model remembered the name, so the marks block and
   the model's marks differ there until mark_quietly's own mark *)
Definition lf_data_nm (cx : lcx) (md mk : Z) (kbs mbs gbs : list byte) (m : word -> option byte) : Prop :=
  anlk_at SEGS m LA_G_NL kbs /\ nlk_wf kbs /\ aiftab_at SEGS m LA_G_NL kbs lf_tab /\
  nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = nk_closed kbs /\
  amodel_at SEGS m md mbs /\ model_wf mbs /\
  amarks_at SEGS m mk gbs /\ marks_wf gbs /\
  lf_ifp m 64 /\
  lf_gnames_at 64 m /\ lf_gnames_w m /\ lf_odd_at m /\ lf_texts_at m /\ lf_la_at m.

Lemma lf_data_nm_of : forall cx md mk kbs mbs gbs m,
  lf_data cx md mk kbs mbs gbs m -> lf_data_nm cx md mk kbs mbs gbs m.
Proof.
  intros cx md mk kbs mbs gbs m (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & _ & D12 & D13 & D14 & D15 & D16 & D17).
  exact (conj D1 (conj D2 (conj D3 (conj D4 (conj D5 (conj D6 (conj D7 (conj D8 (conj D9 (conj D10
    (conj D12 (conj D13 (conj D14 (conj D15 (conj D16 D17))))))))))))))).
Qed.

Lemma lf_data_of_nm : forall cx md mk kbs mbs gbs m,
  lf_data_nm cx md mk kbs mbs gbs m -> marks_are gbs mbs -> lf_data cx md mk kbs mbs gbs m.
Proof.
  intros cx md mk kbs mbs gbs m (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D12 & D13 & D14 & D15 & D16 & D17) D11.
  exact (conj D1 (conj D2 (conj D3 (conj D4 (conj D5 (conj D6 (conj D7 (conj D8 (conj D9 (conj D10 (conj D11
    (conj D12 (conj D13 (conj D14 (conj D15 (conj D16 D17)))))))))))))))).
Qed.

Lemma mq_img_here : mq_img_b SEGS (as_owned_static B) (as_errno B) = true.
Proof. rewrite HSEGS, (ts_owned B TB), (ts_errno B TB). exact mq_img_checks. Qed.

Lemma mq_said_rd : forall ly S rd, ARm B ly S rd ->
  range_addressable rd SHADOW_OFF LA_G_SAID SAID_SIZE /\ shadow_hull_vis rd LA_G_SAID SAID_SIZE.
Proof.
  intros ly S rd HM. pose proof mq_img_here as KI. unfold mq_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  match goal with H : kp_ra_b LA_G_SAID _ = true |- _ => rename H into Hr end.
  match goal with H : kp_hull_b LA_G_SAID _ = true |- _ => rename H into Hh end.
  split; [exact (kp_ra B TB ly S rd _ _ HM Hr) | exact (kp_hull B TB ly S rd _ _ HM Hh)].
Qed.

Lemma mq_writable : forall m a,
  (LA_G_SINK <= a < LA_G_SINK + 8 \/ LA_G_SAY <= a < LA_G_SAY + 8 \/ LA_G_SAID <= a < LA_G_SAID + SAID_SIZE \/
   TFIB_ERRNO <= a < TFIB_ERRNO + 4) -> writable_at SEGS m a.
Proof.
  intros m a Ha. rewrite HSEGS. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
  - apply (writable_at_of_wseg tfibsegs m LA_G_SINK 8); [unfold LA_G_SINK; lia | unfold LA_G_SINK; lia | exact mq_wseg_sink | exact Ha].
  - apply (writable_at_of_wseg tfibsegs m LA_G_SAY 8); [unfold LA_G_SAY; lia | unfold LA_G_SAY; lia | exact mq_wseg_say | exact Ha].
  - apply (writable_at_of_wseg tfibsegs m LA_G_SAID SAID_SIZE);
      [unfold LA_G_SAID; lia | unfold LA_G_SAID, SAID_SIZE; lia | exact mq_wseg_said | exact Ha].
  - apply (writable_at_of_wseg tfibsegs m TFIB_ERRNO 4); [unfold TFIB_ERRNO; lia | unfold TFIB_ERRNO; lia | exact mq_wseg_errno | exact Ha].
Qed.

(* a read-only string the booleans describe: acstr_at and astr_rt_ok at a call whose window is above g_nl *)
Lemma mq_rt_kstr : forall ly S (W : world SEGS) mem mdl (regs : bvmap 5 word) K p l,
  AR SEGS B ly S W mem mdl ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  kp_kstr_b SEGS (as_owned_static B) (as_errno B) p l = true ->
  LA_G_NL <= spZ regs - K ->
  acstr_at SEGS (rdW W mem) p (map (Z_to_bv 8) l) /\
  astr_rt_ok SEGS regs K (rdW W mem) p (map (Z_to_bv 8) l).
Proof.
  intros ly S W mem mdl regs K p l HAR HRO Hk HK.
  pose proof HAR as (M & _).
  destruct (kp_kstr_acstr B (w_H W) mem p l HRO Hk) as (Hs & Hp0 & Hpl).
  split; [exact Hs|].
  unfold kp_kstr_b in Hk.
  repeat match type of Hk with (_ && _)%bool = true => apply andb_prop in Hk as [Hk ?] end.
  match goal with H : kp_hull_b _ _ = true |- _ => rename H into Hh end.
  match goal with H : kp_ra_b _ _ = true |- _ => rename H into Hra end.
  match goal with H : kp_somes_b _ _ _ = true |- _ => rename H into Hsl end.
  unfold astr_rt_ok. rewrite length_map. unfold LA_G_NL in Hpl.
  split; [exact Hp0|]. split; [lia|]. split; [unfold amem_range, kLowMemEnd; left; lia|].
  split; [rewrite ard_aview; exact (kp_ra B TB ly S _ p _ M Hra)|].
  split; [rewrite ard_aview; exact (kp_hull B TB ly S _ p _ M Hh)|].
  split.
  - intros b Hb. pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)) as Hm.
    assert (Hc : (- (p + Z.of_nat (length l) + 1)) mod 8 = 7 - (p + Z.of_nat (length l)) mod 8) by lia.
    destruct (kp_somes_mbyte SEGS (rdW W mem) _ _ Hsl (Z.to_nat (b - (p + Z.of_nat (length l) + 1)))
      ltac:(rewrite Hc; lia)) as (bb & Hbb).
    rewrite Z2Nat.id in Hbb by lia. replace (p + Z.of_nat (length l) + 1 + (b - (p + Z.of_nat (length l) + 1))) with b in Hbb by lia.
    unfold ard. rewrite Hbb. discriminate.
  - unfold apart_frame. left. lia.
Qed.

(* ==========================================================================
   2. The interface table's strings at a call
   ========================================================================== *)

(* where entry i's pointer points, and what its string is *)
Lemma mq_tab_ptr : forall ly S (W : world SEGS) mem mdl kbs i n2 ix p,
  AR SEGS B ly S W mem mdl ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  aiftab_at SEGS (rdW W mem) LA_G_NL kbs lf_tab -> lf_ifp (rdW W mem) 64 ->
  nth_error lf_tab i = Some (n2, ix) ->
  au64_at SEGS (rdW W mem) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
  ((i < 60)%nat /\ p = LA_G_NAMES + 8 * (Z.of_nat i + Z.of_nat i / 15) /\ (length n2 <= 4)%nat) \/
  ((60 <= i < 64)%nat /\ 0x10000 <= p /\
   exists l, kp_kstr_b SEGS (as_owned_static B) (as_errno B) p l = true /\ n2 = map (Z_to_bv 8) l /\
     nth (i - 59) KP_ODD (0, []) = (p, l)).
Proof.
  intros ly S W mem mdl kbs i n2 ix p HAR HRO Htab Hifp Hnth Hp Hpr.
  pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  match goal with H : forallb _ (seq 1 4) = true |- _ => rename H into KOdd end.
  pose proof (eq_refl (as_owned_static B)) as Ho. pose proof (eq_refl (as_errno B)) as He.
  destruct (lf_tab_entry i n2 ix Hnth) as (H64 & Hlt & Hge).
  destruct Htab as (_ & _ & Ht). destruct (Ht i n2 ix Hnth) as (_ & p1 & Hp1 & _ & Hsn1 & _).
  destruct (Hifp (Z.of_nat i) ltac:(lia)) as (qq & Hqq & Hqlo & Hqhi).
  pose proof (kp_vm8_mod _ _ _ _ _ Hp Hqq) as Ep.
  rewrite (Z.mod_small p) in Ep by exact Hpr.
  destruct (Nat.lt_ge_cases i 60) as [Hi60 | Hi60].
  - left. split; [exact Hi60|]. split; [|exact (Hlt Hi60)].
    rewrite Ep, (Hqlo ltac:(lia)). rewrite Z.mod_small by (unfold LA_G_NAMES; lia). reflexivity.
  - right. split; [lia|].
    set (j := (i - 59)%nat).
    assert (Lj : (1 <= j < 5)%nat -> 0x10000 <= fst (nth j KP_ODD (0, [])))
      by (intros Hj'; destruct j as [|[|[|[|[|j]]]]]; cbn [nth KP_ODD fst]; lia).
    assert (Hj : (1 <= j < 5)%nat) by (unfold j; lia).
    pose proof (proj1 (forallb_forall _ _) KOdd j ltac:(apply in_seq; lia)) as Hx. cbv beta zeta in Hx.
    apply andb_prop in Hx as [Hw Hk].
    pose proof (kp_val_mem8 SEGS _ _ B (w_H W) mem _ _ Ho He HRO Hw) as Hv.
    specialize (Hqhi ltac:(lia)).
    replace (LA_ODD + 8 * (Z.of_nat i - 59)) with (LA_ODD + 8 * Z.of_nat j) in Hqhi by (unfold j; lia).
    pose proof (kp_vm8_mod _ _ _ _ _ Hqhi Hv) as Eq.
    pose proof (kp_odd_low) as KL. pose proof (proj1 (forallb_forall _ _) KL j ltac:(apply in_seq; lia)) as Hlow.
    cbv beta in Hlow. apply andb_prop in Hlow as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
    assert (Epq : p = fst (nth j KP_ODD (0, []))).
    { rewrite Ep, Eq. apply Z.mod_small. unfold LA_G_NL in L2. lia. }
    (* the string at p is the odd string, by uniqueness *)
    destruct (kp_kstr_acstr B (w_H W) mem _ _ HRO Hk) as (Hs2 & _ & _).
    pose proof (kp_vm8_mod _ _ _ _ _ Hp1 Hqq) as E1.
    assert (R1 : 0 <= p1 < 2 ^ 64).
    { destruct Hsn1 as ((A1 & A2 & _) & _). rewrite length_app in A2. cbn [length] in A2. lia. }
    rewrite (Z.mod_small p1) in E1 by exact R1.
    assert (Ep1 : p1 = p) by (rewrite E1; rewrite Ep; reflexivity).
    rewrite Ep1, Epq in Hsn1.
    pose proof (kp_acstr_unique _ _ _ _ _ Hsn1 Hs2) as En.
    split; [rewrite Epq; apply Lj; exact Hj|].
    exists (snd (nth j KP_ODD (0, []))). split; [rewrite Epq; exact Hk|]. split; [exact En|].
    rewrite Epq. fold j. destruct (nth j KP_ODD (0, [])); reflexivity.
Qed.

(* an entry's string at a call whose window is above the allocator's ceiling: astr_rt_ok, and where it lies
   (the read-only image below g_nl, or g_names) *)
Lemma mq_tab_rt : forall ly S (W : world SEGS) mem mdl kbs (regs : bvmap 5 word) K i n2 ix p,
  AR SEGS B ly S W mem mdl ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  aiftab_at SEGS (rdW W mem) LA_G_NL kbs lf_tab -> lf_ifp (rdW W mem) 64 -> lf_gnames_at 64 (rdW W mem) ->
  alloc_ceiling <= spZ regs - K ->
  nth_error lf_tab i = Some (n2, ix) ->
  au64_at SEGS (rdW W mem) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
  astr_rt_ok SEGS regs K (rdW W mem) p n2 /\ 0x10000 <= p /\
  (p + Z.of_nat (length n2) + 1 <= LA_G_NL \/
   (LA_G_NAMES <= p /\ p + Z.of_nat (length n2) + 1 <= LA_G_NAMES + G_NAMES_SIZE)).
Proof.
  intros ly S W mem mdl kbs regs K i n2 ix p HAR HRO Htab Hifp Hgn HK Hnth Hp Hpr.
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof HAR as (M & _).
  pose proof Htab as Htab'. destruct Htab' as (_ & _ & Ht). destruct (Ht i n2 ix Hnth) as (_ & p1 & Hp1 & _ & Hsn1 & _).
  destruct (mq_tab_ptr ly S W mem mdl kbs i n2 ix p HAR HRO Htab Hifp Hnth Hp Hpr)
    as [(Hi60 & Ep & Hl4) | (Hi64 & Hp16 & l & Hk & En & _)].
  - set (kk := Z.of_nat i + Z.of_nat i / 15) in *.
    assert (Hkk : 0 <= kk <= 63) by (unfold kk; lia).
    destruct (lf_zsh_gnames_rd B TB ly S _ M) as (Gra & Ghv).
    unfold astr_rt_ok. unfold LA_G_NAMES in Ep.
    assert (Hp0 : 0 < p) by lia.
    split; [|split; [lia | right; unfold LA_G_NAMES, G_NAMES_SIZE; lia]].
    split; [exact Hp0|]. split; [lia|].
    split; [unfold amem_range, kLowMemEnd; left; lia|].
    split; [rewrite ard_aview; apply (lf_ra_sub _ LA_G_NAMES 512); [exact Gra | unfold LA_G_NAMES; lia | unfold LA_G_NAMES; lia]|].
    split; [rewrite ard_aview; apply (lf_hull_sub _ LA_G_NAMES 512); [exact Ghv | lia | lia | unfold LA_G_NAMES; lia | unfold LA_G_NAMES; lia]|].
    split.
    + intros b Hb. assert (Hpm : (p + Z.of_nat (length n2)) mod 8 = Z.of_nat (length n2)) by lia.
      destruct (Hgn kk ltac:(lia)) as (rest & (_ & _ & Hab) & Hlen8).
      assert (Hbi : (Z.to_nat (b - (LA_G_NAMES + 8 * kk)) < length (lf_gname kk ++ Z_to_bv 8 0 :: rest))%nat)
        by (rewrite Hlen8; unfold LA_G_NAMES in *; lia).
      pose proof (Hab _ Hbi) as Hbb.
      rewrite Z2Nat.id in Hbb by (unfold LA_G_NAMES in *; lia).
      replace (LA_G_NAMES + 8 * kk + (b - (LA_G_NAMES + 8 * kk))) with b in Hbb by lia.
      destruct (nth_error_Some (lf_gname kk ++ Z_to_bv 8 0 :: rest) (Z.to_nat (b - (LA_G_NAMES + 8 * kk)))) as [_ Hs].
      specialize (Hs Hbi).
      unfold ard. rewrite Hbb.
      destruct (nth_error (lf_gname kk ++ Z_to_bv 8 0 :: rest) (Z.to_nat (b - (LA_G_NAMES + 8 * kk)))) as [x|] eqn:Ex;
        [cbn [option_map]; discriminate | exfalso; apply Hs; reflexivity].
    + unfold apart_frame. left. unfold LA_G_NAMES in *. lia.
  - subst n2. destruct (mq_rt_kstr ly S W mem mdl regs K p l HAR HRO Hk ltac:(unfold LA_G_NL; lia)) as (_ & Hrt).
    destruct (kp_kstr_acstr B (w_H W) mem p l HRO Hk) as (_ & Hp0 & Hpl).
    split; [exact Hrt|]. split; [exact Hp16|]. left. rewrite length_map. lia.
Qed.

(* reac_served_mark's premises at mark_quietly's call, from the interface's clauses. The FILE range (fb, fn) is
   (0, 0) on the opening call and the kept FILE block on a later one; the name is the caller's, with its own facts. *)
Lemma lf_amq_common : forall cx ly S (W : world SEGS) mem mdl md mk kbs mbs gbs T3 (regs : bvmap 5 word) fb fn nm,
  AR SEGS B ly S W mem mdl ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_blocks B cx md mk T3 ly S (rdW W mem) -> lf_data_nm cx md mk kbs mbs gbs (rdW W mem) ->
  nk_opened kbs + 2 < 2 ^ 31 ->
  alloc_ceiling <= spZ regs - MARK_QUIETLY_AK ->
  (aarg regs 0 = 0 \/ aarg regs 0 = mk) ->
  ((fb = 0 /\ fn = 0) \/ (In (fb, fn) (ablocks B ly S) /\ In (fb, fn) T3)) ->
  astr_arg SEGS (rdW W mem) (aarg regs 1) nm ->
  amk_name_ok SEGS B regs MARK_QUIETLY_AK fb fn (rdW W mem) nm ->
  (forall s, nm = Some s -> aarg regs 1 + Z.of_nat (length s) + 8 <= LA_G_SINK) ->
  amq_common SEGS B fb fn (ablocks B ly S) regs (rdW W mem).
Proof.
  intros cx ly S W mem mdl md mk kbs mbs gbs T3 regs fb fn nm HAR HRO HBL HD Hop HK Ha0 Hf Hnm Hnok Hnlo.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HAR as (M & _).
  destruct HBL as (Hmdin & Hmkin & Hmdc & Hmkc & HmdT & HmkT & Hmd16 & Hmk16 & Hmdt & Hmkt & Hapmm & _ & _
    & Hramd & Hramk & Hammd & Hammk).
  pose proof HD as (Hnl & Hwf & Htab & Hop0 & Hmi & Hoc & Hmd & Hmwf & Hmk & Hkwf & Hifp & Hgn & Hgw & Hodd
    & Htx & Hla).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ mk MK_SIZE HAR Hmkin) as (_ & Hmk4096 & Hmkceil & Hmkapp & _).
  change (req_size MK_SIZE) with 516 in Hmkceil, Hmkapp.
  pose proof (ts_errno B TB) as HE. pose proof (ts_tp B TB) as HTP.
  assert (HE0 : TFIB_ERRNO = 0x631b6c) by reflexivity.
  assert (HAK : MARK_QUIETLY_AK = 24608) by reflexivity.
  (* the FILE range lies apart from every image byte and from the marks block *)
  assert (HF : (fb + fn <= 0x10000 \/ YImgTop.IMG_TOP <= fb) /\ apart fb fn mk MK_SIZE /\ 0 <= fb /\ 0 <= fn).
  { destruct Hf as [(-> & ->) | (Hfin & HfT)].
    - unfold apart. split; [left; lia|]. split; [left; lia|]. lia.
    - pose proof (blk_off_imgP B ly S W mem mdl fb fn HAR Hfin) as Hoff. unfold off_img, YImgTop.IMG_LO in Hoff.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ fb fn HAR Hfin) as (_ & Hf4096 & Hfceil & _ & _ & _ & Hfn).
      assert (Hne : (fb, fn) <> (mk, MK_SIZE)) by (intros E; rewrite E in HfT; exact (HmkT HfT)).
      pose proof (sep_blocks _ _ LAWS _ _ _ _ _ fb fn mk MK_SIZE HAR Hfin Hmkin Hne) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. change (req_size MK_SIZE) with 516 in D.
      assert (Rf : fn <= req_size fn) by (unfold req_size; destruct (Z.eqb_spec fn 0); lia).
      unfold apart, MK_SIZE. split; [|split; [lia | lia]]. destruct Hoff as [Hoff | Hoff]; [left | right]; lia. }
  destruct HF as (Hfimg & Hfmk & Hfb0 & Hfn0).
  exists kbs, lf_tab, nm.
  (* (1) the marks block in the ledger *)
  split; [intros H0; destruct Ha0 as [Ha0 | Ha0]; [contradiction | rewrite Ha0; split; [exact Hmkin | exact Hmkt]]|].
  (* (2) the globals apart from the name and the table's strings *)
  split.
  { intros g n Hg. assert (Hgl : LA_G_SINK <= g) by
      (cbn [amq_globals In] in Hg; unfold LA_G_SINK, LA_G_SAID, LA_G_SAY, LA_OFL_HEAD in *;
       destruct Hg as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia).
    split.
    - intros s Hs. pose proof (Hnlo s Hs). unfold apart. right. lia.
    - intros i n2 ix p Hnth Hp Hpr.
      destruct (mq_tab_rt ly S W mem mdl kbs regs MARK_QUIETLY_AK i n2 ix p HAR HRO Htab Hifp Hgn HK Hnth Hp Hpr)
        as (_ & _ & Hloc).
      unfold apart. right. destruct Hloc; unfold LA_G_NL, LA_G_NAMES, G_NAMES_SIZE, LA_G_SINK in *; lia. }
  (* (3) g_nl *)
  split.
  { destruct (zsh_gnl_ard B TB SEGS ly S W mem mdl HAR) as (Gra & Ghv).
    unfold amk_nlk_ok. split; [exact Hnl|]. split; [exact Hwf|]. split; [exact Hop0|].
    split; [lia|]. split; [lia|]. split; [exact Htab|]. split; [exact Gra | exact Ghv]. }
  (* (4) errno *)
  split.
  { destruct (zsh_errno_ard B TB SEGS ly S W mem mdl HAR) as (Era & _).
    unfold amk_errno_ok. rewrite HE, HTP. split; [reflexivity|].
    split; [intros i Hi; apply mq_writable; right; right; right; lia|].
    split; [rewrite <- HE; exact Era|].
    split; [unfold apart_frame; left; lia|].
    split; [unfold apart_gnl, LA_G_NL, NK_SIZE; right; lia|].
    split; [unfold apart; destruct Hfimg; [right | left]; unfold YImgTop.IMG_TOP in *; lia|].
    intros H0. destruct Ha0 as [Ha0 | Ha0]; [contradiction|]. rewrite Ha0.
    unfold apart, MK_SIZE. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MK_SIZE in Hmkt. lia. }
  (* (5) errno apart from the four globals *)
  rewrite HE.
  split; [unfold apart, LA_G_SAY; right; lia|]. split; [unfold apart, LA_G_SAID, SAID_SIZE; right; lia|].
  split; [unfold apart, LA_G_SINK; right; lia|]. split; [unfold apart, LA_OFL_HEAD; left; lia|].
  (* (6) the table *)
  split.
  { intros i n2 ix p Hnth Hp Hpr.
    destruct (mq_tab_rt ly S W mem mdl kbs regs MARK_QUIETLY_AK i n2 ix p HAR HRO Htab Hifp Hgn HK Hnth Hp Hpr)
      as (Hrt & Hp0 & Hloc).
    split; [exact Hrt|].
    split; [unfold apart_gnl; destruct Hloc as [Hl | Hl]; [left | right]; unfold LA_G_NL, NK_SIZE, LA_G_NAMES in *; lia|].
    split; [unfold apart; right; destruct Hloc; unfold LA_G_NL, LA_G_NAMES, G_NAMES_SIZE in *; lia|].
    split; [unfold apart; destruct Hfimg; [left | right]; destruct Hloc; unfold LA_G_NL, LA_G_NAMES, G_NAMES_SIZE,
            YImgTop.IMG_TOP in *; lia|].
    intros H0. destruct Ha0 as [Ha0 | Ha0]; [contradiction|]. rewrite Ha0. unfold apart, MK_SIZE.
      unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MK_SIZE in Hmkt.
      destruct Hloc; unfold LA_G_NL, LA_G_NAMES, G_NAMES_SIZE, YImgTop.IMG_TOP in *; lia. }
  (* (7) the policy strings *)
  split.
  { pose proof mq_img_here as KI. unfold mq_img_b in KI.
    repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
    assert (KP : forall p s, In (p, s) mq_pol ->
              acstr_at SEGS (rdW W mem) p s /\ astr_rt_ok SEGS regs MARK_QUIETLY_AK (rdW W mem) p s).
    { intros p s Hin. rewrite forallb_forall in KI. pose proof (KI (p, s) Hin) as Hk. cbn [fst snd] in Hk.
      rewrite <- (mq_byte_list s).
      exact (mq_rt_kstr ly S W mem mdl regs MARK_QUIETLY_AK p _ HAR HRO Hk ltac:(unfold LA_G_NL; lia)). }
    unfold amk_policy_ok.
    repeat match goal with |- _ /\ _ => split end;
      (first [ eapply proj1; apply KP | eapply proj2; apply KP ]);
      cbn [mq_pol In]; repeat (first [left; reflexivity | right]). }
  (* (8), (9) the name *)
  split; [exact Hnm|]. split; [exact Hnok|].
  (* (10) the marks block *)
  intros H0. destruct Ha0 as [Ha0 | Ha0]; [contradiction|]. rewrite Ha0.
  split.
  { unfold amarks_blk_ok. split; [lia|].
    split; [unfold amem_range, MK_SIZE; unfold in_app, kLowShadowBeg, ASAN_CEIL in Hmkapp; lia|].
    split; [exact Hramk|].
    split; [rewrite ard_aview; apply (shadow_hull_vis_of_block _ _ LAWS _ _ _ _ _ mk MK_SIZE mk MK_SIZE HAR Hmkin);
            change (req_size MK_SIZE) with 516; unfold MK_SIZE; lia|].
    split; [intros b Hb; rewrite ard_aview; apply (mq_blk_tail_vis16 SEGS B ly S W mem mdl mk MK_SIZE b HAR Hmkin);
            replace (round_up MK_SIZE 16) with 528 by reflexivity; unfold MK_SIZE in *; lia|].
    unfold apart_frame, MK_SIZE. left. lia. }
  split; [unfold apart_gnl, LA_G_NL, NK_SIZE, MK_SIZE; unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MK_SIZE in Hmkt; lia|].
  split; [unfold apart, MK_SIZE; unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MK_SIZE in Hmkt; lia|].
  split; [exact Hfmk|].
  exists gbs. split; [exact Hmk | exact Hkwf].
Qed.

(* g_said's facts, which both Pres ask *)
Lemma mq_said_facts : forall ly S (W : world SEGS) mem mdl, AR SEGS B ly S W mem mdl ->
  awrange SEGS (rdW W mem) LA_G_SAID SAID_SIZE /\ amem_range LA_G_SAID SAID_SIZE /\
  range_addressable (ard SEGS (rdW W mem)) SHADOW_OFF LA_G_SAID SAID_SIZE /\
  shadow_hull_vis (ard SEGS (rdW W mem)) LA_G_SAID SAID_SIZE.
Proof.
  intros ly S W mem mdl (M & _). destruct (mq_said_rd ly S _ M) as (Hra & Hhv).
  split; [intros i Hi; apply mq_writable; right; right; left; lia|].
  split; [unfold amem_range, LA_G_SAID, SAID_SIZE, kLowMemEnd; left; lia|].
  rewrite ard_aview. split; [exact Hra | exact Hhv].
Qed.

(* a heap block of 16-byte alignment has 8 bytes of application memory past it *)
Lemma mq_amem8 : forall ly S (W : world SEGS) mem mdl p n, AR SEGS B ly S W mem mdl ->
  In (p, n) (ablocks B ly S) -> p mod 16 = 0 -> 0 < n -> n mod 16 <= 8 -> n mod 16 <> 0 \/ True ->
  amem_range p (n + 8).
Proof.
  intros ly S W mem mdl p n HAR Hin H16 Hn Hm _.
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4096 & Hceil & Happ & _).
  assert (Rq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia). rewrite Rq in Hceil, Happ.
  unfold amem_range. unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in Happ.
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
Qed.

(* the Pre of a later call: g_sink holds the kept FILE *)
Lemma lf_mq_pre_again : forall cx ly S (W : world SEGS) mem mdl md mk kbs mbs gbs (regs : bvmap 5 word) nm sink,
  AR SEGS B ly S W mem mdl ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_blocks B cx md mk [(sink, AMF_BLOCK)] ly S (rdW W mem) -> lf_data_nm cx md mk kbs mbs gbs (rdW W mem) ->
  incl [(sink, AMF_BLOCK)] (ablocks B ly S) ->
  amf_heads SEGS link_amf (rdW W mem) sink -> amemfile_at SEGS link_amf (rdW W mem) sink ->
  nk_opened kbs + 2 < 2 ^ 31 ->
  alloc_ceiling <= spZ regs - MARK_QUIETLY_AK ->
  (aarg regs 0 = 0 \/ aarg regs 0 = mk) ->
  astr_arg SEGS (rdW W mem) (aarg regs 1) nm ->
  amk_name_ok SEGS B regs MARK_QUIETLY_AK sink AMF_BLOCK (rdW W mem) nm ->
  (forall s, nm = Some s -> aarg regs 1 + Z.of_nat (length s) + 8 <= LA_G_SINK) ->
  mark_quietly_apre_again SEGS B sink (ablocks B ly S) regs (rdW W mem).
Proof.
  intros cx ly S W mem mdl md mk kbs mbs gbs regs nm sink HAR HRO HBL HD Hincl Hh Hf Hop HK Ha0 Hnm Hnok Hnlo.
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (Hin : In (sink, AMF_BLOCK) (ablocks B ly S)) by (apply Hincl; left; reflexivity).
  destruct Hh as (Hgs & Hgy & Hgo). cbn [amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock link_amf] in Hgs, Hgy, Hgo.
  pose proof Hf as (Hf0 & Hf64 & Hf16 & Hst & Hfl & Hom & Hwin & Hck).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ sink AMF_BLOCK HAR Hin) as (_ & Hs4096 & Hsceil & Hsapp & Hspres & _).
  change (req_size AMF_BLOCK) with 1304 in Hsceil, Hsapp, Hspres.
  destruct (mq_said_facts ly S W mem mdl HAR) as (Sw & Sam & Sra & Shv).
  unfold mark_quietly_apre_again.
  split; [exact Hin|]. split; [exact Hgs|]. split; [lia|].
  split; [apply (lf_amq_common cx ly S W mem mdl md mk kbs mbs gbs [(sink, AMF_BLOCK)] regs sink AMF_BLOCK nm
                   HAR HRO HBL HD Hop HK Ha0 ltac:(right; split; [exact Hin | left; reflexivity]) Hnm Hnok Hnlo)|].
  split.
  { pose proof Hwin as (_ & _ & Hw). destruct Hw as [(W1 & W2 & W3) | (kk & Hkk & W1 & W2 & W3)].
    - exists 0. split; [exact Hf|]. split; [left; split; [reflexivity|]; split; [exact W1|]; split; [exact W2 | exact W3]|].
      split; [intros i Hi; apply (apresent_writable SEGS); apply (proj1 (Hspres (sink + i) ltac:(unfold AMF_BLOCK in *; lia)))|].
      exact Sw.
    - exists kk. split; [exact Hf|]. split; [right; split; [exact Hkk|]; split; [exact W1|]; split; [exact W2 | exact W3]|].
      split; [intros i Hi; apply (apresent_writable SEGS); apply (proj1 (Hspres (sink + i) ltac:(unfold AMF_BLOCK in *; lia)))|].
      exact Sw. }
  split; [exact Hgy|]. split; [exact Hgo|].
  split.
  { unfold amf_blk_ok. split; [apply (mq_amem8 ly S W mem mdl sink AMF_BLOCK HAR Hin Hf16); unfold AMF_BLOCK; [lia | lia | right; exact I]|].
    split; [rewrite ard_aview; apply (range_addressable_of_block _ _ LAWS _ _ _ _ _ sink AMF_BLOCK sink AMF_BLOCK HAR Hin);
            change (req_size AMF_BLOCK) with 1304; unfold AMF_BLOCK; lia|].
    split; [rewrite ard_aview; apply (shadow_hull_vis_of_block _ _ LAWS _ _ _ _ _ sink AMF_BLOCK sink AMF_BLOCK HAR Hin);
            change (req_size AMF_BLOCK) with 1304; unfold AMF_BLOCK; lia|].
    unfold apart_frame, AMF_BLOCK. left. lia. }
  split; [exact Sw|]. split; [exact Sam|]. split; [exact Sra | exact Shv].
Qed.

(* the Pre of the opening call: g_sink is NULL *)
Lemma lf_mq_pre_open : forall cx ly S (W : world SEGS) mem mdl md mk kbs mbs gbs (regs : bvmap 5 word) nm,
  AR SEGS B ly S W mem mdl ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_blocks B cx md mk [] ly S (rdW W mem) -> lf_data_nm cx md mk kbs mbs gbs (rdW W mem) ->
  amf_heads SEGS link_amf (rdW W mem) 0 -> amf_env SEGS link_amf (rdW W mem) ->
  nk_opened kbs + 2 < 2 ^ 31 ->
  alloc_ceiling <= spZ regs - MARK_QUIETLY_AK ->
  (aarg regs 0 = 0 \/ aarg regs 0 = mk) ->
  aarg regs 1 < alloc_ceiling ->
  astr_arg SEGS (rdW W mem) (aarg regs 1) nm ->
  amk_name_ok SEGS B regs MARK_QUIETLY_AK 0 0 (rdW W mem) nm ->
  (forall s, nm = Some s -> aarg regs 1 + Z.of_nat (length s) + 8 <= LA_G_SINK) ->
  mark_quietly_apre_open SEGS B (ablocks B ly S) regs (rdW W mem).
Proof.
  intros cx ly S W mem mdl md mk kbs mbs gbs regs nm HAR HRO HBL HD Hh Henv Hop HK Ha0 Ha1 Hnm Hnok Hnlo.
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct Hh as (Hgs & Hgy & Hgo). cbn [amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock link_amf] in Hgs, Hgy, Hgo.
  destruct (mq_said_facts ly S W mem mdl HAR) as (Sw & Sam & Sra & Shv).
  unfold mark_quietly_apre_open.
  split; [exact Hgs|].
  split; [apply (lf_amq_common cx ly S W mem mdl md mk kbs mbs gbs [] regs 0 0 nm
                   HAR HRO HBL HD Hop HK Ha0 ltac:(left; split; reflexivity) Hnm Hnok Hnlo)|].
  split; [exact Henv|]. split; [exact Ha1|]. split; [exact Hgo|].
  split; [intros i Hi; apply mq_writable; left; lia|].
  split; [intros i Hi; apply mq_writable; right; left; lia|].
  split; [exact Sw|]. split; [exact Sam|]. split; [exact Sra|]. split; [exact Shv|].
  pose proof mq_img_here as KI. unfold mq_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  rewrite forallb_forall in KI. pose proof (KI (LA_MODE_STR, S_MODE_W) ltac:(cbn [mq_pol In]; repeat (first [left; reflexivity | right]))) as Hk.
  cbn [fst snd] in Hk. rewrite <- (mq_byte_list S_MODE_W).
  exact (mq_rt_kstr ly S W mem mdl regs MARK_QUIETLY_AK _ _ HAR HRO Hk ltac:(unfold LA_G_NL; lia)).
Qed.


(* ==========================================================================
   4. The read set (reac_served_mark_c.v amk_rd at W6's fix: each string with its NUL)
   ========================================================================== *)

(* its bytes are akb bytes at the call, given the name's own *)
Lemma mq_ard_akb : forall ly S (W : world SEGS) mem mdl kbs (regs : bvmap 5 word) lyc Sc slo shi,
  AR SEGS B ly S W mem mdl ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  gx_ok SEGS B G_HARNESS ->
  anlk_at SEGS (rdW W mem) LA_G_NL kbs -> aiftab_at SEGS (rdW W mem) LA_G_NL kbs lf_tab -> lf_ifp (rdW W mem) 64 ->
  (forall a, aarg regs 1 <> 0 -> forall s, acstr_at SEGS (rdW W mem) (aarg regs 1) s ->
     aarg regs 1 <= a <= aarg regs 1 + Z.of_nat (length s) -> akb SEGS B lyc Sc slo shi a) ->
  forall a, mark_quietly_ard SEGS regs (rdW W mem) a -> akb SEGS B lyc Sc slo shi a.
Proof.
  intros ly S W mem mdl kbs regs lyc Sc slo shi HAR HRO HGX Hnl Htab Hifp Hname a Ha.
  pose proof (kp_ard_here B TB HSEGS) as KA. unfold kp_ard_b in KA.
  repeat match type of KA with (_ && _)%bool = true => apply andb_prop in KA as [KA ?] end.
  match goal with H : forallb _ (seq 1 4) = true |- _ => rename H into KAodd end.
  assert (HE0 : TFIB_ERRNO = 0x631b6c) by reflexivity.
  assert (AG : forall x, (LA_G_NL <= x < LA_G_NL + NK_SIZE \/ LA_G_NAMES <= x < LA_G_NAMES + G_NAMES_SIZE) ->
                 akb SEGS B lyc Sc slo shi x).
  { intros x Hx. apply (kp_akb_G B TB lyc Sc slo shi x HGX);
      [| unfold LA_G_NL, NK_SIZE, LA_G_NAMES, G_NAMES_SIZE in Hx; lia].
    unfold inG, G_HARNESS. unfold LA_G_NAMES, G_NAMES_SIZE, NK_SIZE in Hx.
    destruct Hx as [Hx | Hx].
    - apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
    - apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold LA_G_NAMES in *. lia. }
  unfold mark_quietly_ard, amk_rd, astr_rd, amk_tab_rd in Ha.
  destruct Ha as [(Hp & s & Hs & Hx) | [Hx | (bs & tab & i & n2 & ix & p & Hbs & Htb & Hnth & Hp & Hs & Hx)]].
  - exact (Hname a Hp s Hs Hx).
  - apply AG. left. unfold rd_ivl in Hx. unfold NK_IF_NAME, NK_SIZE in *. lia.
  - (* the table read through the memory is lf_tab *)
    assert (Ebs : bs = kbs).
    { destruct Hbs as ((Hb1 & _) & L1). destruct Hnl as ((Hb2 & _) & L2).
      apply (abytes_unique SEGS _ _ _ _ Hb1 Hb2). lia. }
    subst bs.
    destruct Htb as (Hn1 & _ & Ht1). destruct Htab as (Hn2 & H80 & Ht2).
    assert (Hi64 : (i < 64)%nat).
    { assert (HL : length tab = 64%nat) by (rewrite <- lf_tab_len; apply Nat2Z.inj; congruence).
      rewrite <- HL. apply nth_error_Some. rewrite Hnth. discriminate. }
    destruct (nth_error lf_tab i) as [[n0 ix0]|] eqn:Hn0;
      [| exfalso; apply nth_error_None in Hn0; rewrite lf_tab_len in Hn0; lia].
    destruct (Ht2 i n0 ix0 Hn0) as (_ & p0 & Hp0 & _ & Hs0 & _).
    assert (Rp : 0 <= p < 2 ^ 64).
    { destruct Hs as ((A1 & A2 & _) & _). rewrite length_app in A2. cbn [length] in A2. lia. }
    assert (Rp0 : 0 <= p0 < 2 ^ 64).
    { destruct Hs0 as ((A1 & A2 & _) & _). rewrite length_app in A2. cbn [length] in A2. lia. }
    pose proof (kp_vm8_mod _ _ _ _ _ Hp Hp0) as E. rewrite !Z.mod_small in E by lia. subst p0.
    pose proof (kp_acstr_unique _ _ _ _ _ Hs Hs0) as En. subst n0.
    destruct (mq_tab_ptr ly S W mem mdl kbs i n2 ix0 p HAR HRO
                (conj Hn2 (conj H80 Ht2)) Hifp Hn0 Hp Rp) as [(Hi60 & Ep & Hl4) | (Hi60 & Hp16 & l & Hk & En & Hj)].
    + apply AG. right. unfold LA_G_NAMES, G_NAMES_SIZE in *. lia.
    + set (j := (i - 59)%nat) in *.
      pose proof (proj1 (forallb_forall _ _) KAodd j ltac:(apply in_seq; unfold j; lia)) as Hx'. cbv beta zeta in Hx'.
      rewrite Hj in Hx'. cbn [fst snd] in Hx'. subst n2. rewrite length_map in Hx.
      exact (kp_akbs_of_b B lyc Sc slo shi p (Datatypes.S (length l)) a Hx' ltac:(lia)).
Qed.

End k.
