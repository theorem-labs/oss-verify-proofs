(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 361 of its 425 lines of code are new or changed and 340 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: what a text_of answer is, and the decide Pre built from it (listed in
   the slot walk's shared file list). The body calls text_of at 0x82e24, 0x82e34 (op_decide) and 0x837d8 (op_write);
   each answer s is either one of the eleven texts strings (text_of_c.v text_of_apostA, own = 0) or a fresh block
   of at most TEXT_OF_LIVE = 320 bytes holding the copied string (own <> 0). The answer is consumed by
   reac_served_decide / model_decide (0x82e44, 0x82e54; model_decide_c.v decide_apre) and by op_write's
   model_write, reac_link_alias_write and the strlen wrapper.

   1. dec_ans ly S m s t: the answer, in a form a callee step keeps (the texts entry: image bytes, re-read at any
      memory from arodata_okP; the fresh block: a block of the state with the string's bytes inside it).
   2. dec_of_text_of: text_of's post gives dec_ans at the return state.
   3. dec_rt_ok: at any AR state with arodata_okP, a dec_ans string has acstr_at and model_decide_c.v's
      astr_rt_ok for a callee called with sp at most the realigned stack pointer and window K below it (the
      texts strings by computation over the pin, as LLVMFuzzerTestOneInputKpre.v checks them; a fresh block from
      AR's block law, its shadow law and the chunk's tail, which AR keeps visible: dec_blk_tail_vis16).
   4. dec_lits: the four decide literals (.str.14 / .str.17 of model_decide, .str / .str.1 of
      reac_served_decide) by computation.
   5. dec_decide_apre / dec_decide_ard: decide_apre at either decide function and its read set's akb, from two
      dec_ans strings.
   6. lf_apre_at: apre at a call made with sp = the realigned stack pointer on the walk's journal, for any window K
      the real frame leaves room for.

   The chunk-tail lemmas of section 0 are copies of lib/A/Prog/reac_served_markKitAt.v's
   srm_chunk_tail_in_ajunk / srm_chunk_room_mod16 /
   srm_blk_tail_vis16, renamed dec_*.

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c model_decide_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   0. The bytes past a heap block, to the next multiple of 16 of its size, are visible at every AR state
      (copied from reac_served_markKitAt.v, see the header)
   ========================================================================== *)
Section tv. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

Lemma dec_chunk_tail_in_ajunk : forall ly S k, In k (st_chunks S) ->
  In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S).
Proof.
  intros ly S k Hk. unfold ajunk. right. right.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_flat_map. exists k. split; [exact Hk|].
  unfold chunk_junk. cbv zeta.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
Qed.

Lemma dec_chunk_room_mod16 : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) ->
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

Lemma dec_blk_tail_vis16 : forall ly S (W : world segs) mem md p n a,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p + n <= a < p + round_up n 16 -> aview segs (w_H W) mem a <> None.
Proof.
  intros ly S W mem md p n a (M & _) Hb Ha.
  unfold ablocks, blocks in Hb. apply in_map_iff in Hb as ([u r] & Eb & Hb). cbn [fst snd] in Eb.
  injection Eb as Ep En.
  apply in_map_iff in Hb as (k & Ek & Hk). injection Ek as Eu Er. subst u r.
  apply filter_In in Hk as [Hk _].
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & UA & _ & _ & Hn & HX & _).
  pose proof (dec_chunk_room_mod16 ly S _ k M Hk) as R16.
  assert (N1 : 1 <= n).
  { destruct (Z.eq_dec n 0) as [->|]; [|lia]. unfold round_up in Ha. cbn in Ha. lia. }
  assert (CN : ck_n k = n) by (unfold ck_n, req_size; destruct (Z.eqb_spec (ck_req k) 0); lia).
  assert (RU : round_up n 16 <= ck_extent k - ck_rz k).
  { apply round_up_le; [lia | | exact R16]. unfold ck_n in CN. lia. }
  pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ M) _ (dec_chunk_tail_in_ajunk ly S k Hk)) as V.
  unfold range_vis in V. cbn [fst snd] in V. rewrite CN in V.
  rewrite aeval_aoff in V by (intros e'; destruct (ck_beg k); cbn; discriminate).
  change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
  replace a with (ck_base B ly k + (ck_rz k + n) + (a - (ck_base B ly k + (ck_rz k + n)))) by lia.
  apply V. rewrite <- Ep, UA in Ha. lia.
Qed.
End tv.

(* ==========================================================================
   The image checks: the four decide literals (and the texts strings, Kpre.v's kp_img_b)
   ========================================================================== *)
Definition DEC_PREFIX_Z : list Z := [114; 101; 97; 99; 45; 112; 119; 58].
Definition DEC_VLAN_Z : list Z := [118; 108; 97; 110].
Lemma dec_prefix_eq : S_PREFIX = map (Z_to_bv 8) DEC_PREFIX_Z. Proof. reflexivity. Qed.
Lemma dec_vlan_eq : S_VLAN = map (Z_to_bv 8) DEC_VLAN_Z. Proof. reflexivity. Qed.

Definition dec_lits_b (segs : list Segment) (own : list (Z * Z)) (err : Z) : bool :=
  kp_kstr_b segs own err LA_MD_PREFIX DEC_PREFIX_Z && kp_kstr_b segs own err LA_MD_VLAN DEC_VLAN_Z
  && kp_kstr_b segs own err LA_RSD_PREFIX DEC_PREFIX_Z && kp_kstr_b segs own err LA_RSD_VLAN DEC_VLAN_Z.
Lemma dec_lits_checks : dec_lits_b tfibsegs Tfib_owned_static TFIB_ERRNO = true.
Proof. vm_compute. reflexivity. Qed.

(* every texts string is shorter than 320 bytes, and its bytes are akb image bytes (Kpre.v kp_ard_b) *)
Lemma dec_texts_short :
  forallb (fun i => Nat.ltb (length (snd (nth i KP_TEXTS (0, [])))) 320) (seq 0 11) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_aview_present : forall segs H (mem : word -> option byte) a, apresent H mem a -> aview segs H mem a <> None.
Proof. intros segs H mem a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.

Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.

#[local] Notation BASEF cx := (lf_base SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

Lemma dec_lits_here : dec_lits_b SEGS (as_owned_static B) (as_errno B) = true.
Proof. rewrite HSEGS, (ts_owned B TB), (ts_errno B TB). exact dec_lits_checks. Qed.

(* ==========================================================================
   1. The answer
   ========================================================================== *)
Definition dec_ans (ly : alayout) (S : astate) (m : word -> option byte) (s : Z) (t : list byte) : Prop :=
  (exists i, (i < 11)%nat /\ s = fst (nth i KP_TEXTS (0, [])) /\ t = map (Z_to_bv 8) (snd (nth i KP_TEXTS (0, []))))
  \/ (exists k, In (s, k) (ablocks B ly S) /\ Z.of_nat (length t) + 1 <= k <= TEXT_OF_LIVE /\ acstr_at SEGS m s t).

(* ==========================================================================
   3. The runtime-string facts of an answer
   ========================================================================== *)

(* a string a kp_kstr_b check describes *)
Lemma dec_kstr_rt : forall ly S (W : world SEGS) mem mdl (regs : bvmap 5 word) K p l,
  AR SEGS B ly S W mem mdl -> arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  alloc_ceiling <= spZ regs - K ->
  kp_kstr_b SEGS (as_owned_static B) (as_errno B) p l = true ->
  acstr_at SEGS (rdW W mem) p (map (Z_to_bv 8) l) /\
  astr_rt_ok SEGS regs K (rdW W mem) p (map (Z_to_bv 8) l).
Proof.
  intros ly S W mem mdl regs K p l HAR HRO HK Hk.
  pose proof HAR as (M & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (kp_kstr_acstr B (w_H W) mem p l HRO Hk) as (Hcs & Hp0 & Hpl).
  unfold kp_kstr_b in Hk.
  repeat match type of Hk with (_ && _)%bool = true => apply andb_prop in Hk as [Hk ?] end.
  match goal with H : kp_hull_b _ _ = true |- _ => rename H into Hh end.
  match goal with H : kp_ra_b _ _ = true |- _ => rename H into Hra end.
  match goal with H : kp_somes_b _ _ _ = true |- _ => rename H into Hsl end.
  split; [exact Hcs|].
  unfold astr_rt_ok. rewrite length_map. unfold LA_G_NL in Hpl.
  split; [lia|]. split; [lia|]. split; [unfold amem_range; left; lia|].
  split; [rewrite ard_aview; exact (kp_ra B TB ly S _ p _ M Hra)|].
  split; [rewrite ard_aview; exact (kp_hull B TB ly S _ p _ M Hh)|].
  split.
  - intros b Hb. rewrite ard_aview.
    pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)) as Hm.
    assert (Hcnt : (Z.to_nat (b - (p + Z.of_nat (length l) + 1)) <
                    Z.to_nat ((- (p + Z.of_nat (length l) + 1)) mod 8))%nat).
    { assert (E : (- (p + Z.of_nat (length l) + 1)) mod 8 = 7 - (p + Z.of_nat (length l)) mod 8).
      { symmetry. apply Z.mod_unique_pos with (q := - ((p + Z.of_nat (length l)) / 8) - 1); [lia|].
        pose proof (Z.div_mod (p + Z.of_nat (length l)) 8 ltac:(lia)). lia. }
      rewrite E. lia. }
    destruct (kp_somes_mbyte SEGS (rdW W mem) _ _ Hsl _ Hcnt) as (bt & Hbt).
    replace (p + Z.of_nat (length l) + 1 + Z.of_nat (Z.to_nat (b - (p + Z.of_nat (length l) + 1)))) with b
      in Hbt by lia.
    unfold aview. rewrite Hbt. cbn. discriminate.
  - unfold apart_frame. left. lia.
Qed.

(* the texts entries *)
Lemma dec_texts_rt : forall ly S (W : world SEGS) mem mdl (regs : bvmap 5 word) K i,
  AR SEGS B ly S W mem mdl -> arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  alloc_ceiling <= spZ regs - K -> (i < 11)%nat ->
  acstr_at SEGS (rdW W mem) (fst (nth i KP_TEXTS (0, []))) (map (Z_to_bv 8) (snd (nth i KP_TEXTS (0, [])))) /\
  astr_rt_ok SEGS regs K (rdW W mem) (fst (nth i KP_TEXTS (0, []))) (map (Z_to_bv 8) (snd (nth i KP_TEXTS (0, [])))).
Proof.
  intros ly S W mem mdl regs K i HAR HRO HK Hi.
  pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  match goal with H : forallb _ (seq 0 11) = true |- _ => rename H into KTx end.
  pose proof (kp_forallb_seq _ _ KTx i Hi) as Hx. cbv beta zeta in Hx. apply andb_prop in Hx as [_ Hs].
  exact (dec_kstr_rt ly S W mem mdl regs K _ _ HAR HRO HK Hs).
Qed.

(* the table word of entry i is the entry's address *)
Lemma dec_texts_word : forall (W : world SEGS) mem i v,
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) -> (i < 11)%nat ->
  au64_at SEGS (rdW W mem) (LA_TEXTS + 8 * Z.of_nat i) v -> 0 <= v < 2 ^ 64 ->
  v = fst (nth i KP_TEXTS (0, [])).
Proof.
  intros W mem i v HRO Hi Hv Rv.
  pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  match goal with H : forallb _ (seq 0 11) = true |- _ => rename H into KTx end.
  pose proof (kp_forallb_seq _ _ KTx i Hi) as Hx. cbv beta zeta in Hx. apply andb_prop in Hx as [Hw Hs].
  pose proof (kp_val_mem8 SEGS _ _ B (w_H W) mem _ _ eq_refl eq_refl HRO Hw) as Ve.
  pose proof (kp_vm8_mod _ _ _ _ _ Hv Ve) as E.
  destruct (kp_kstr_acstr B (w_H W) mem _ _ HRO Hs) as (_ & Hq0 & Hql). unfold LA_G_NL in Hql.
  rewrite !Z.mod_small in E by lia. exact E.
Qed.

(* the facts of a fresh block's string *)
Lemma dec_blk_rt : forall ly S (W : world SEGS) mem mdl (regs : bvmap 5 word) K s k t,
  AR SEGS B ly S W mem mdl -> In (s, k) (ablocks B ly S) -> Z.of_nat (length t) + 1 <= k <= TEXT_OF_LIVE ->
  acstr_at SEGS (rdW W mem) s t -> alloc_ceiling <= spZ regs - K ->
  astr_rt_ok SEGS regs K (rdW W mem) s t.
Proof.
  intros ly S W mem mdl regs K s k t HAR Hin Hk Hcs HK.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (H16 & H4096 & Hceil & Happ & Hpres & _).
  assert (Rk : req_size k = k) by (unfold req_size; destruct (k =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]).
  rewrite Rk in Hceil, Happ, Hpres.
  unfold TEXT_OF_LIVE in Hk. unfold astr_rt_ok.
  set (n := Z.of_nat (length t)) in *.
  split; [lia|]. split; [lia|].
  split; [unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *; lia|].
  split; [rewrite ard_aview; eapply range_addressable_of_block; [eassumption | eassumption | exact Hin | lia | rewrite Rk; lia]|].
  split; [rewrite ard_aview; eapply shadow_hull_vis_of_block;
          [eassumption | eassumption | exact Hin | lia | rewrite Rk; lia | lia]|].
  split.
  - intros b Hb. rewrite ard_aview.
    pose proof (Z.mod_pos_bound (s + n) 8 ltac:(lia)) as Hm.
    destruct (Z_lt_le_dec b (s + k)) as [Hin' | Hout].
    + destruct (Hpres b ltac:(lia)) as (Hp & _). exact (dec_aview_present SEGS (w_H W) mem b Hp).
    + apply (dec_blk_tail_vis16 SEGS B ly S W mem mdl s k b HAR Hin). split; [exact Hout|].
      unfold round_up. pose proof (Z.div_mod (s + n) 8 ltac:(lia)) as D8.
      apply Z.mod_divide in H16 as [q16 Q16]; [|lia].
      assert (Hb' : b < s + n - (s + n) mod 8 + 8) by lia.
      assert (Hdiv : (k + 16 - 1) / 16 * 16 >= k).
      { pose proof (Z.div_mod (k + 16 - 1) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (k + 16 - 1) 16 ltac:(lia)). lia. }
      assert (Hgran : s + n - (s + n) mod 8 + 8 <= s + (k + 16 - 1) / 16 * 16).
      { pose proof (Z.div_mod (k + 16 - 1) 16 ltac:(lia)) as D16.
        pose proof (Z.mod_pos_bound (k + 16 - 1) 16 ltac:(lia)) as M16.
        (* s is a multiple of 16, so the granule end of s + n is s + 8 * ceil((n + 1) / 8) <= s + round_up k 16 *)
        assert (E8 : (s + n) mod 8 = n mod 8).
        { rewrite Q16. rewrite Z.add_comm. replace (q16 * 16) with ((2 * q16) * 8) by lia.
          rewrite Z.mod_add by lia. reflexivity. }
        rewrite E8. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
        set (r := (k + 16 - 1) / 16) in *.
        assert (8 * (n / 8) + 8 <= 16 * r) by lia. lia. }
      lia.
  - unfold apart_frame. left. lia.
Qed.

Lemma dec_rt_ok : forall ly S (W : world SEGS) mem mdl (regs : bvmap 5 word) K s t,
  AR SEGS B ly S W mem mdl -> arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  alloc_ceiling <= spZ regs - K ->
  dec_ans ly S (rdW W mem) s t ->
  acstr_at SEGS (rdW W mem) s t /\ astr_rt_ok SEGS regs K (rdW W mem) s t /\ Z.of_nat (length t) < 320 /\ s <> 0.
Proof.
  intros ly S W mem mdl regs K s t HAR HRO HK [(i & Hi & -> & ->) | (k & Hin & Hk & Hcs)].
  - destruct (dec_texts_rt ly S W mem mdl regs K i HAR HRO HK Hi) as (Hcs & Hrt).
    pose proof (kp_forallb_seq _ _ dec_texts_short i Hi) as Hsh. cbv beta in Hsh. apply Nat.ltb_lt in Hsh.
    split; [exact Hcs|]. split; [exact Hrt|]. rewrite length_map. split; [lia|].
    destruct Hrt as (Hp & _). lia.
  - pose proof (dec_blk_rt ly S W mem mdl regs K s k t HAR Hin Hk Hcs HK) as Hrt.
    split; [exact Hcs|]. split; [exact Hrt|]. unfold TEXT_OF_LIVE in Hk. split; [lia|].
    destruct Hrt as (Hp & _). lia.
Qed.

(* ==========================================================================
   2. text_of's post gives an answer
   ========================================================================== *)
(* the texts entry an own = 0 answer is (dec_ans's left case, memory-free) *)
Definition dec_ans_l (s : Z) (t : list byte) : Prop :=
  exists i, (i < 11)%nat /\ s = fst (nth i KP_TEXTS (0, [])) /\ t = map (Z_to_bv 8) (snd (nth i KP_TEXTS (0, []))).

Lemma dec_l_of_text_of : forall (W : world SEGS) mem (W2 : world SEGS) mem2 s t,
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) mem2) ->
  acstr_at SEGS (rdW W2 mem2) s t ->
  (exists i, 0 <= i < TEXTS_N /\ au64_at SEGS (rdW W mem) (LA_TEXTS + 8 * i) s) ->
  dec_ans_l s t.
Proof.
  intros W mem W2 mem2 s t HRO HRO2 Hcs (i & Hi & Hw). unfold TEXTS_N in Hi.
  exists (Z.to_nat i). split; [lia|].
  pose proof Hcs as ((Hs & Hse & _) & _).
  assert (Es : s = fst (nth (Z.to_nat i) KP_TEXTS (0, []))).
  { apply (dec_texts_word W mem (Z.to_nat i) s HRO ltac:(lia)); [rewrite Z2Nat.id by lia; exact Hw|].
    rewrite length_app in Hse. cbn [length] in Hse. lia. }
  split; [exact Es|].
  pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  match goal with H : forallb _ (seq 0 11) = true |- _ => rename H into KTx end.
  pose proof (kp_forallb_seq _ _ KTx (Z.to_nat i) ltac:(lia)) as Hx. cbv beta zeta in Hx.
  apply andb_prop in Hx as [_ Hk].
  destruct (kp_kstr_acstr B (w_H W2) mem2 _ _ HRO2 Hk) as (Hcs' & _).
  rewrite <- Es in Hcs'.
  exact (kp_acstr_unique SEGS _ s t _ Hcs Hcs').
Qed.

Lemma dec_of_text_of : forall (W : world SEGS) mem (W2 : world SEGS) mem2 ly2 S2 (bl : list (Z * Z)) s t own,
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) mem2) ->
  s <> 0 -> acstr_at SEGS (rdW W2 mem2) s t -> Z.of_nat (length t) < 320 ->
  (own = 0 -> Permutation (ablocks B ly2 S2) bl /\
     (exists i, 0 <= i < TEXTS_N /\ au64_at SEGS (rdW W mem) (LA_TEXTS + 8 * i) s) /\
     text_of_ro SEGS PCAP_RLO PCAP_RHI B s (Z.of_nat (length t) + 1)) ->
  (own <> 0 -> own = s /\ 4096 <= own /\
     exists k, 1 <= k <= TEXT_OF_LIVE /\ Z.of_nat (length t) + 1 <= k /\ ablocks B ly2 S2 = bl ++ [(own, k)]) ->
  dec_ans ly2 S2 (rdW W2 mem2) s t.
Proof.
  intros W mem W2 mem2 ly2 S2 bl s t own HRO HRO2 Hs0 Hcs Hlen H0 H1.
  destruct (Z.eq_dec own 0) as [E | E].
  - destruct (H0 E) as (_ & (i & Hi & Hw) & _). left. unfold TEXTS_N in Hi.
    exists (Z.to_nat i). split; [lia|].
    pose proof Hcs as ((Hs & Hse & _) & _).
    assert (Es : s = fst (nth (Z.to_nat i) KP_TEXTS (0, []))).
    { apply (dec_texts_word W mem (Z.to_nat i) s HRO ltac:(lia)); [rewrite Z2Nat.id by lia; exact Hw|].
      rewrite length_app in Hse. cbn [length] in Hse. lia. }
    split; [exact Es|].
    pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
    repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
    match goal with H : forallb _ (seq 0 11) = true |- _ => rename H into KTx end.
    pose proof (kp_forallb_seq _ _ KTx (Z.to_nat i) ltac:(lia)) as Hx. cbv beta zeta in Hx.
    apply andb_prop in Hx as [_ Hk].
    destruct (kp_kstr_acstr B (w_H W2) mem2 _ _ HRO2 Hk) as (Hcs' & _).
    rewrite <- Es in Hcs'.
    exact (kp_acstr_unique SEGS _ s t _ Hcs Hcs').
  - destruct (H1 E) as (-> & H4096 & k & Hk1 & Hk2 & Hbl). right. exists k.
    split; [rewrite Hbl; apply in_or_app; right; left; reflexivity|].
    split; [lia | exact Hcs].
Qed.

(* ==========================================================================
   4, 5. The decide Pre and its read set
   ========================================================================== *)
Lemma dec_lit_rt : forall ly S (W : world SEGS) mem mdl (regs : bvmap 5 word),
  AR SEGS B ly S W mem mdl -> arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  alloc_ceiling <= spZ regs - DECIDE_AK ->
  (acstr_at SEGS (rdW W mem) LA_MD_PREFIX S_PREFIX /\ astr_rt_ok SEGS regs DECIDE_AK (rdW W mem) LA_MD_PREFIX S_PREFIX) /\
  (acstr_at SEGS (rdW W mem) LA_MD_VLAN S_VLAN /\ astr_rt_ok SEGS regs DECIDE_AK (rdW W mem) LA_MD_VLAN S_VLAN) /\
  (acstr_at SEGS (rdW W mem) LA_RSD_PREFIX S_PREFIX /\ astr_rt_ok SEGS regs DECIDE_AK (rdW W mem) LA_RSD_PREFIX S_PREFIX) /\
  (acstr_at SEGS (rdW W mem) LA_RSD_VLAN S_VLAN /\ astr_rt_ok SEGS regs DECIDE_AK (rdW W mem) LA_RSD_VLAN S_VLAN).
Proof.
  intros ly S W mem mdl regs HAR HRO HK.
  pose proof dec_lits_here as KL. unfold dec_lits_b in KL.
  apply andb_prop in KL as [KL K4]. apply andb_prop in KL as [KL K3]. apply andb_prop in KL as [K1 K2].
  rewrite dec_prefix_eq, dec_vlan_eq.
  split; [exact (dec_kstr_rt ly S W mem mdl regs DECIDE_AK _ _ HAR HRO HK K1)|].
  split; [exact (dec_kstr_rt ly S W mem mdl regs DECIDE_AK _ _ HAR HRO HK K2)|].
  split; [exact (dec_kstr_rt ly S W mem mdl regs DECIDE_AK _ _ HAR HRO HK K3)|].
  exact (dec_kstr_rt ly S W mem mdl regs DECIDE_AK _ _ HAR HRO HK K4).
Qed.

Lemma dec_decide_apre : forall ly S (W : world SEGS) mem mdl (regs : bvmap 5 word) s1 t1 s2 t2 prefix vlan,
  AR SEGS B ly S W mem mdl -> arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  alloc_ceiling <= spZ regs - DECIDE_AK ->
  ((prefix = LA_MD_PREFIX /\ vlan = LA_MD_VLAN) \/ (prefix = LA_RSD_PREFIX /\ vlan = LA_RSD_VLAN)) ->
  aarg regs 0 = s1 -> aarg regs 1 = s2 ->
  dec_ans ly S (rdW W mem) s1 t1 -> dec_ans ly S (rdW W mem) s2 t2 ->
  decide_apre SEGS prefix vlan regs (rdW W mem).
Proof.
  intros ly S W mem mdl regs s1 t1 s2 t2 prefix vlan HAR HRO HK Hpv Ha0 Ha1 HD1 HD2.
  destruct (dec_rt_ok ly S W mem mdl regs DECIDE_AK s1 t1 HAR HRO HK HD1) as (C1 & R1 & L1 & N1).
  destruct (dec_rt_ok ly S W mem mdl regs DECIDE_AK s2 t2 HAR HRO HK HD2) as (C2 & R2 & L2 & N2).
  destruct (dec_lit_rt ly S W mem mdl regs HAR HRO HK) as ((P1 & Q1) & (P2 & Q2) & (P3 & Q3) & (P4 & Q4)).
  exists (Some t1), (Some t2). rewrite Ha0, Ha1.
  split; [split; [exact N1 | exact C1]|]. split; [split; [exact N2 | exact C2]|].
  destruct Hpv as [(-> & ->) | (-> & ->)].
  - split; [exact P1|]. split; [exact Q1|]. split; [exact P2|]. split; [exact Q2|].
    split; [intros t E; injection E as <-; exact R1 | intros t E; injection E as <-; exact R2].
  - split; [exact P3|]. split; [exact Q3|]. split; [exact P4|]. split; [exact Q4|].
    split; [intros t E; injection E as <-; exact R1 | intros t E; injection E as <-; exact R2].
Qed.

(* an answer's bytes are akb bytes of a call's state *)
Lemma dec_ans_akb : forall ly S (W : world SEGS) mem mdl s t slo shi a,
  AR SEGS B ly S W mem mdl -> arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  dec_ans ly S (rdW W mem) s t ->
  (exists u, acstr_at SEGS (rdW W mem) s u /\ s <= a <= s + Z.of_nat (length u)) ->
  akb SEGS B ly S slo shi a.
Proof.
  intros ly S W mem mdl s t slo shi a HAR HRO HD (u & Hu & Ha).
  destruct HD as [(i & Hi & -> & ->) | (k & Hin & Hk & Hcs)].
  - pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
    repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
    match goal with H : forallb _ (seq 0 11) = true |- _ => rename H into KTx end.
    pose proof (kp_forallb_seq _ _ KTx i Hi) as Hx. cbv beta zeta in Hx. apply andb_prop in Hx as [_ Hk].
    destruct (kp_kstr_acstr B (w_H W) mem _ _ HRO Hk) as (Hcs & _).
    pose proof (kp_acstr_unique SEGS _ _ _ _ Hu Hcs) as Eu. subst u. rewrite length_map in Ha.
    clear KTx.
    pose proof (kp_ard_here B TB HSEGS) as KA. unfold kp_ard_b in KA.
    repeat match type of KA with (_ && _)%bool = true => apply andb_prop in KA as [KA ?] end.
    match goal with H : forallb _ (seq 0 11) = true |- _ => rename H into KAx end.
    pose proof (kp_forallb_seq _ _ KAx i Hi) as Hy. cbv beta zeta in Hy.
    apply (kp_akbs_of_b B ly S slo shi _ _ a Hy). rewrite Nat2Z.inj_succ. lia.
  - pose proof (kp_acstr_unique SEGS _ _ _ _ Hu Hcs) as Eu. subst u.
    right; left. exists s, k. split; [exact Hin|].
    unfold req_size. destruct (k =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. unfold TEXT_OF_LIVE in Hk. lia.
Qed.

Lemma dec_decide_ard : forall ly S (W : world SEGS) mem mdl (regs : bvmap 5 word) s1 t1 s2 t2 slo shi,
  AR SEGS B ly S W mem mdl -> arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  aarg regs 0 = s1 -> aarg regs 1 = s2 ->
  dec_ans ly S (rdW W mem) s1 t1 -> dec_ans ly S (rdW W mem) s2 t2 ->
  forall a, decide_ard SEGS regs (rdW W mem) a -> akb SEGS B ly S slo shi a.
Proof.
  intros ly S W mem mdl regs s1 t1 s2 t2 slo shi HAR HRO Ha0 Ha1 HD1 HD2 a [(_ & u & Hu & Ha) | (_ & u & Hu & Ha)].
  - rewrite Ha0 in Hu, Ha. exact (dec_ans_akb ly S W mem mdl s1 t1 slo shi a HAR HRO HD1 (ex_intro _ u (conj Hu Ha))).
  - rewrite Ha1 in Hu, Ha. exact (dec_ans_akb ly S W mem mdl s2 t2 slo shi a HAR HRO HD2 (ex_intro _ u (conj Hu Ha))).
Qed.

(* ==========================================================================
   6. apre at a call made with sp = s1
   ========================================================================== *)
Lemma lf_apre_at : forall cx fp ly S (W : world SEGS) mem mdl k (regs : bvmap 5 word) K EV SIDE Wr,
  BASEF cx -> JRN cx fp ly S W mem mdl k ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  spZ regs = lf_sp1 cx ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  0 <= K <= LLVMF_STK - 448 -> 0 <= EV -> k + EV <= EV_LIB -> aside_room S SIDE ->
  (forall a, inFP Wr a -> ajw B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
                            (c_ly cx) (c_S cx) ly S [(LF_CID, fp)] a) ->
  (forall a, inFP Wr a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a) ->
  apre SK SEGS PCAP_RLO PCAP_RHI B K EV SIDE Wr G_HARNESS 0 [] LLVMF_STK
    (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)]
    ly S W mem mdl k regs.
Proof.
  intros cx fp ly S W mem mdl k regs K EV SIDE Wr HB HJ HRO Hsp Hgp Htp Hret Hra4 HK HEV Hk HSIDE HW HR.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem mdl k
    HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  pose proof HB as (HPRE & _ & HGX & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hnev & _).
  set (sp0 := spZ (c_regs cx)) in *.
  assert (Hs1 : sp0 - 416 - 16 <= lf_sp1 cx <= sp0 - 416 /\ lf_sp1 cx mod 32 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range sp0 ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16) as (R & R32 & _).
    unfold LF_MFRAME in R. split; [exact R | exact R32]. }
  destruct Hs1 as (Hs1 & Hs32).
  assert (HEVv : EV_LIB = 196) by reflexivity.
  unfold LLVMF_STK in *.
  unfold apre. split; [exact HJ|]. split; [exact HGX|]. split; [exact HRO|]. split; [exact Hret|].
  split; [exact Hra4|]. split; [exact Hgp|]. split; [exact Htp|].
  split; [rewrite Hsp; pose proof (Z.div_mod (lf_sp1 cx) 32 ltac:(lia)) as D32;
          rewrite Hs32 in D32; rewrite D32; replace (32 * (lf_sp1 cx / 32) + 0) with ((lf_sp1 cx / 32 * 2) * 16) by lia;
          apply Z.mod_mul; lia|].
  split; [rewrite Hsp; lia|]. split; [rewrite Hsp; lia|].
  split; [lia|]. split; [exact HSIDE|]. split; [exact HW | exact HR].
Qed.

(* an answer across a callee whose write set misses the blocks of the call, and which keeps the blocks *)
Lemma dec_ans_callee : forall cx K ly3 S3 ly2 S2 (W3 : world SEGS) mem3 (W2 : world SEGS) mem2 (E : Z -> Prop) s t,
  lf_call B cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E ->
  (forall b m a, In (b, m) (ablocks B ly3 S3) -> b <= a < b + m -> ~ E a) ->
  (forall b m, In (b, m) (ablocks B ly3 S3) -> In (b, m) (ablocks B ly2 S2)) ->
  dec_ans ly3 S3 (rdW W3 mem3) s t -> dec_ans ly2 S2 (rdW W2 mem2) s t.
Proof.
  intros cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E s t HC HE Hbl [Ht | (k & Hin & Hk & Hcs)]; [left; exact Ht|].
  right. exists k. split; [exact (Hbl _ _ Hin)|]. split; [exact Hk|].
  apply (acstr_keep SEGS _ _ _ s t (lf_call_kagree B cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E HC)); [|exact Hcs].
  intros i Hi. apply (lfx_blk B ly3 S3 ly2 S2 _ _ E s k (s + i) Hin); [lia|].
  apply (HE s k (s + i) Hin). lia.
Qed.

End b.
End a.
