(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACfh.v (srz_enter, the journal over a token list), ACk2.v (the file system a closed journal keeps), ACfj.v (tfib_lib_x) and ACfi.v (tfib_lib_x_all) for libreac/fuzz_grant: module paths, GrantB, the library shape grant_shape, and the entry function's phase machine of lib/A/Prog/GrantEntryDefs.v in place of cgif's. *)
(* The ASan build's program contract for fuzz_grant: the walk of the entry function,
   phase by phase, closed at the shape of its library (lib/A/GrantShape.v) and in the
   form a Theorem Labs lane's lib/A/ACfn.v states it.

   The walk itself is in lib/A/Prog/GrantEntry*.v, one file per phase; this file says
   what the phases together give (`ge_start … ge_post`, the whole call from its first
   slot) and turns that into `tfib_lib_contract_x`, whose pre-condition carries the
   file system and the sink that fuzz_grant never touches. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0s YK14 YK15 YK18 YP09 YI04 YI09 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YE00 YE01 YL01 YO09 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import AB1v AE2k ACfn ACej AF0l AD2l AF0m.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import GrantShape.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantAddr GrantImg GrantEntryDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* From a run that keeps the world to the set of traces the statement speaks of: the
   form of cgif_file's lib/A/ACfh.v:47-50. *)
Lemma srz_enter : forall segs (W : world segs) (c : config) (T : TSet),
  AI segs (w_H W) (w_A W) (cfg_model c) ->
  SRr segs W c (fun W' c' => AI segs (w_H W') (w_A W') (cfg_model c') -> srealizes segs c' T) ->
  srealizes segs c T.
Proof. intros segs W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.

Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* No byte belongs to the empty token list, and a journal that opened no sink carries
   over to any token list: cgif_file's lib/A/ACfh.v:29-43 proves the same two facts of
   its own entry walk. *)
Lemma grant_inFP_nil : forall a, ~ inFP [] a.
Proof. intros a (r & Hin & _). exact Hin. Qed.

Lemma grant_journal_fp : forall STK sp0 FP ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
  intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
    (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
  split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
  split; [eapply aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (sink_closed_nil Ho)|].
  split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
  split; [intros q m i H1 H2 Hi _; apply (F2 q m i H1 H2 Hi); apply grant_inFP_nil|].
  split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply fp_spares_closed;
          intros Ho; exact (sink_closed_nil Ho)|].
  split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply grant_inFP_nil|].
  split; [intros q m i H1 H2 Hi; exfalso; exact (grant_inFP_nil _ (Hgone q m i H1 H2 Hi))|].
  split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.

(* What a journal that opened no sink leaves of the file system. *)
Lemma grant_journal_io : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
  intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ.
  pose proof HJ as (_ & _ & _ & _ & Hos & _).
  destruct (aos_step_closed [] md md' sink_closed_nil Hos) as (Efd & Efsys & _ & _).
  unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.

End b.
End a.

(* ---- the call, at the shape of fuzz_grant's library ---- *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM XN : Z -> Z.
Variables RLO RHI : Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis AIL : asink_img_laws tfibsegs B tfib_K.
(* The read-only data of the image, in the range the entry contract names and in the
   range the listing's instance names. *)
Hypothesis HRO : forall rd, arodata_okS tfibsegs B RLO RHI rd ->
  arodata_okP tfibsegs (pa_relro_lo (PAImg := PI_grant)) (pa_relro_hi (PAImg := PI_grant)) B rd.
(* The call traces of the wrappers for malloc and free, at the six slots of this
   function that call them. *)
Hypothesis HTR : forall (ly : alayout) (regs regsT : bvmap 5 word) (pcf : Z),
  raZ regs = RA_LLVMF ->
  (pcf = pc_malloc_ra0 (as_code B) /\ In (raZ regsT - grant_text) GE_MSITES) \/
  (pcf = pc_free_ra0 (as_code B) /\ In (raZ regsT - grant_text) GE_FSITES) ->
  In (call_trace0 pcf regsT
       (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []))
     (as_universe B).
(* The budget the caller grants covers what the call spends, and the budget the
   post-condition reports is at least that. *)
Hypothesis HXM : forall n, GE_NEED MT <= XM n.
Hypothesis HXMN : forall n, XM n <= XN n.
Hypothesis START :
  ge_start (PI := PI_grant) B MT (ge_post (PI := PI_grant) B MT).

(* The context of the call, as the entry contract hands it over. *)
Definition grant_cx (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (p : Z) (pl : list byte) (T : Z)
  : ecx (PI := PI_grant) :=
  mkECX (PI := PI_grant) ly S W regs mem md p pl
    (32 * ((spZ regs + -288) / 32)) (Ereg regs [w64 SHADOW_OFF]) T.

Theorem grant_lib_x : tfib_lib_contract_x B MT XM XN RLO RHI.
Proof.
  intros ly S W regs mem md p n pl M K HAI HPRE HK.
  destruct HPRE as (HFN & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr & Hev & Hlive & HROS &
                    HSNK & HFD & HSORT & HAM & HMOK).
  assert (HB : ge_base B MT (grant_cx ly S W regs mem md p pl (XM n))).
  { unfold ge_base, grant_cx, c_n.
    cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_sp1 c_E0 c_T].
    rewrite <- Hnpl.
    split; [exact HFN|]. split; [exact Hp|]. split; [exact Hn|].
    split; [exact Hpn|]. split; [exact HPL|]. split; [exact Hfr|].
    split; [exact Hev|]. split; [exact Hlive|].
    split; [exact (HRO _ HROS)|].
    split; [reflexivity|].
    split; [intros m0 r Hm0; exact (ew_Ereg_nat regs _ m0 r Hm0)|].
    split; [exact (f_equal (fun w => bv_unsigned w) (ew_Ereg_nat regs _ 2 2%bv eq_refl))|].
    split; [exact (ew_Ereg_extra regs [w64 SHADOW_OFF] 0)|].
    split; [exact HMOK|].
    split; [intros pcf regsT Hsite; exact (HTR ly regs regsT pcf Hra Hsite)|].
    exact (HXM n). }
  change (LIBK pl (m_fs md) K) with (K (LL 0 (m_fs md) [])).
  refine (srz_enter tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md) _ HAI _).
  eapply SRr_mono.
  { exact (START _ HB). }
  intros W' c' Hwle HPOST HAI'.
  unfold ge_post, grant_cx in HPOST.
  cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_T] in HPOST.
  destruct HPOST as (ly' & S' & regs' & mem' & md' & k & Ec & HJ & Hk & HPR & Ha0 & HPerm & HMLE & HFkeep).
  destruct (grant_journal_io (PI := PI_grant) B LLVMF_STK (spZ regs) ly S W mem md [] ly' S' W' mem' md' k HJ)
    as [Efds Efs].
  apply (HK (LL 0 (m_fs md) []) W' c' Hwle HAI').
  exists ly', S', regs', mem', md', k.
  split.
  { rewrite Ec. unfold cfg_at. f_equal. f_equal.
    unfold w64. rewrite <- Hra. unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold tfib_lib_post_x. cbn [ll_fs ll_ret ll_out].
  split; [exact (grant_journal_fp (PI := PI_grant) B LLVMF_STK (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k HJ)|].
  split; [exact Hk|]. split; [exact HPR|]. split; [exact Ha0|]. split; [exact HPerm|].
  split; [intros fd; rewrite Efds; reflexivity|].
  split; [exact Efs|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT|].
  split; [exact (asink_none_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ sink_closed_nil HSNK)|].
  split; [exact (ameta_inv_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAM)|].
  split; [exact (mle_weaken MT S S' (XM n) (XN n) MTL HMLE (HXMN n))|].
  intros i Hi. apply HFkeep. unfold c_n. cbn [c_pl]. lia.
Qed.

End c.

(* ---- the call at fuzz_grant's own asyms, meter and read-only range ---- *)
(* The read-only range a Theorem Labs lane's driver states the contract over (lib/A/AGrantT.v:28-31):
   the ASan build's .data.rel.ro and .got, and the meter that counts nothing. *)
Definition GX_RLO : Z := 0x9c1a0.
Definition GX_RHI : Z := 0x9d568.
Definition GX_XL0 : Z -> Z := fun _ => 0.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The walks' read-only range is the driver's own (GrantImg.v fixes `pa_relro_lo` and
   `pa_relro_hi` at the ASan build's .data.rel.ro and .got, which is what the entry
   contract's range is), so the driver's view of it is the walks' view of it. *)
Lemma grant_HRO : forall rd, arodata_okS tfibsegs GrantB GX_RLO GX_RHI rd ->
  arodata_okP tfibsegs (pa_relro_lo (PAImg := PI_grant)) (pa_relro_hi (PAImg := PI_grant)) GrantB rd.
Proof. intros rd H a Ha. exact (H a Ha). Qed.

(* The call traces of the wrappers for malloc and free at this function's six call
   sites are in the universe of fuzz_grant's traces (lib/A/ACej.v:29-41). *)
Lemma grant_HTR : forall (ly : alayout) (regs regsT : bvmap 5 word) (pcf : Z),
  raZ regs = RA_LLVMF ->
  (pcf = pc_malloc_ra0 (as_code GrantB) /\ In (raZ regsT - grant_text) GE_MSITES) \/
  (pcf = pc_free_ra0 (as_code GrantB) /\ In (raZ regsT - grant_text) GE_FSITES) ->
  In (call_trace0 pcf regsT
       (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []))
     (as_universe GrantB).
Proof.
  intros ly regs regsT pcf Hra Hs.
  assert (Hc : (pcf = 0x52dec /\ (raZ regsT = 0x80994 \/ raZ regsT = 0x80e90 \/ raZ regsT = 0x8132c)) \/
               (pcf = 0x52c8c /\ (raZ regsT = 0x812a0 \/ raZ regsT = 0x813b8 \/ raZ regsT = 0x817d0))).
  { unfold GE_MSITES, GE_FSITES, grant_text in Hs.
    cbn [as_code GrantB Tfib_code pc_malloc_ra0 pc_free_ra0 In] in Hs.
    destruct Hs as [[-> Hm] | [-> Hf]]; [left | right]; (split; [reflexivity|]); lia. }
  remember (raZ regsT) as ra eqn:Era.
  unfold RA_LLVMF in Hra.
  destruct (spZ regs + 16 <? ly_top ly).
  - rewrite call_trace_cons, <- Era, Hra. apply TRACES_LLVMFuzzerTestOneInput_U.
    destruct Hc as [[-> [-> | [-> | ->]]] | [-> [-> | [-> | ->]]]];
      vm_compute; repeat (first [left; reflexivity | right]).
  - rewrite call_trace_nil, <- Era. apply TRACES_LLVMFuzzerTestOneInput_U.
    destruct Hc as [[-> [-> | [-> | ->]]] | [-> [-> | [-> | ->]]]];
      vm_compute; repeat (first [left; reflexivity | right]).
Qed.

Lemma grant_need : forall n, GE_NEED ameter_triv <= GX_XL0 n.
Proof. intros n. unfold GE_NEED, GE_A3, GE_A2, GE_A1, GX_XL0. cbn. lia. Qed.

(* The sink of the image keeps its laws (proved for GrantB as lib/A/AD1u.v:43
   `tfib_AIL`). *)
Hypothesis AILG : asink_img_laws tfibsegs GrantB tfib_K.
Hypothesis START :
  ge_start (PI := PI_grant) GrantB ameter_triv (ge_post (PI := PI_grant) GrantB ameter_triv).

Theorem grant_lib_x_closed : tfib_lib_contract_x GrantB ameter_triv GX_XL0 GX_XL0 GX_RLO GX_RHI.
Proof.
  apply (grant_lib_x GrantB ameter_triv GX_XL0 GX_XL0 GX_RLO GX_RHI ameter_triv_laws
          AILG grant_HRO grant_HTR grant_need
          (fun n => Z.le_refl _) START).
Qed.

End d.
