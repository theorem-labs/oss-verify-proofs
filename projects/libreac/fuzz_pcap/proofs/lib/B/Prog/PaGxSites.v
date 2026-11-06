(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-10: ADAPTATION of aj_gx_entry_at (W_sites.v:313 at a working branch d07c8d46c63, proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, blob 11270d5ab359829dd7eb85bf2516c7e158a9a1b3), re-sectioned over fuzz_pcap's program kit: only the runtime-entry lift aj_gx_entry_at (W_sites.v:313-417) and what it needs, aentry_post and ascratch_ok (W_sites.v:54-69) and aview_wrap64 (W_sites.v:306-312); the listing is pcap_listing (lib/A/Prog/PcapPa.v PAImg, in place of fuzz_reply's fr_prog_listing), the journal is lib/A/W_journal.v's ajournal_gx; module paths changed (plugin_hostd.fuzz_reply -> libreac.fuzz_pcap; Reusable.YP0b / YP0a -> A.Prog.PaTable / PaSym; A.W_syms / W_listing / W_kit -> A.Prog.PcapSyms / PcapList / PcapPa / PcapPaLib). fuzz_reply's own entry contracts (the rest of W_sites.v), W_contract and the printf model are not taken. No proof text changed. *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PaGxSites.v for fuzz_pcap.asan-ubsan (v1.9.0): the listing, its names, PAImg and PALib are lib/B's (PcapSyms, PcapList, PcapPa, PcapPaLib); the lemmas are stated over PAImg pcap_listing and use no image constant, so the text is otherwise lib/A's. *)
(* aj_gx_entry_at: a runtime entry that keeps the allocator state, given by its contract in aentry_post form, called
   from a walk that holds W_journal.v's ajournal_gx G XO OUT, returns with that journal kept (the entry's writes are
   to G or to awr_bytes of the walk's own window outside its out cells), its result Pr, every byte outside its
   writes and its scratch unchanged, and presence kept. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
Section c.
Variable B : asyms.

(* The common post of an entry that keeps the allocator state: W unchanged, back at ra, AR at the same ly S, the
   callee-saved registers kept, the model changed only by materialisation, the result Pr on the new registers and
   memory, every byte outside the written set Wr and the scratch [sp - stk, sp) unchanged, presence kept. *)
Definition aentry_post (stk : Z) ly S (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(Wr : Z -> Prop) (Pr : bvmap 5 word -> (word -> option byte) -> Prop) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at SEGS (raZ regs) regs' mem' md' /\
AR SEGS B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
Pr regs' mem' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> ~ (spZ regs - stk <= a < spZ regs) ->
 aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).

(* The pre every entry shares beyond ecall_pre: stk bytes of present scratch below sp, above the stack's floor. *)
Definition ascratch_ok (stk : Z) ly (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
ly_stk_lo ly + stk <= spZ regs /\ (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a).

End c.

Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma aview_wrap64 : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte.
assert (E : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. }
rewrite E. reflexivity.
Qed.
Lemma aj_gx_entry_at : forall G XO OUT (stk pc : Z) (Wr : Z -> Prop) (Pr : bvmap 5 word -> (word -> option byte) -> Prop)
  W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
gx_ok SEGS B G -> XO mod 16 = 0 ->
ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK <= stk -> stk - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, Wr a \/ ~ Wr a) ->
(forall a, Wr a -> inG G a -> apresent (w_H W) memT a) ->
(forall a, Wr a -> ~ inG G a ->
 awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) ->
(ecall_pre SEGS B lyc Sc W regsT memT mdc -> ascratch_ok stk lyc W regsT memT ->
 SRr SEGS W (cfg_at SEGS pc regsT memT mdc) (aentry_post B stk lyc Sc W regsT memT mdc Wr Pr)) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\ Pr regs2 mem2 /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> ~ (sp0 + o - stk <= a < sp0 + o) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros G XO OUT stk pc Wr Pr W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HG HX16 HJ Hsp Hal Hneg Hstk Hbud Hgp Htp Hra Hraw HWd HWg HWa AM.
pose proof pa_segs_low as Hsegs.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout).
pose proof HJi as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _ & HQT).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc W memT mdc k regsT (o - XO) HJi);
  [lia | rewrite <- Zminus_mod_idemp_r, HX16, Z.sub_0_r; exact Hal | lia | lia | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
assert (HSC : ascratch_ok stk lyc W regsT memT).
{ split; [rewrite Eslo, Hsp; lia|]. intros a Ha. apply Hpres. rewrite Hsp in Ha. lia. }
eapply SRr_mono; [exact (AM HPRE HSC)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsame & HPr & Hfr & Hgr).
rewrite Hsp in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
(* the memory that is the call's outside G and the caller's on G *)
set (memM := fun x : word => if inGb G (bv_unsigned x) then memT x else mem2 x).
assert (MG : forall x, inGb G (bv_unsigned x) = false -> memM x = mem2 x) by (intros x Hx; unfold memM; rewrite Hx; reflexivity).
assert (MT : forall x, inGb G (bv_unsigned x) = true -> memM x = memT x) by (intros x Hx; unfold memM; rewrite Hx; reflexivity).
assert (GLO : forall a, inG G a -> 0 <= a < kLowMemEnd) by (intros a Ha; exact (inG_low SEGS B Hsegs G a HG Ha)).
assert (GB : forall a, 0 <= a < 2 ^ 64 -> inGb G (bv_unsigned (Z_to_bv 64 a)) = inGb G a)
by (intros a Ha; rewrite unsigned_lit_small by lia; reflexivity).
assert (AVT : forall a, 0 <= a < 2 ^ 64 -> inG G a -> aview SEGS (w_H W) memM a = aview SEGS (w_H W) memT a).
{ intros a Ha HGa. apply aview_eq_of. unfold mrestrict. rewrite MT; [reflexivity|]. rewrite GB by exact Ha. apply inGb_spec. exact HGa. }
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview SEGS (w_H W) memM a = aview SEGS (w_H W) mem2 a).
{ intros a Ha HGa. apply aview_eq_of. unfold mrestrict. rewrite MG; [reflexivity|]. rewrite GB by exact Ha. apply inGb_false. exact HGa. }
(* the scratch lies in the stack, far above every global *)
assert (SCG : forall a, inG G a -> ~ (sp0 + o - stk <= a < sp0 + o)) by (intros a Ha Hs; pose proof (GLO a Ha); unfold kLowMemEnd in *; lia).
assert (HARM : AR SEGS B lyc Sc W memM md2).
{ eapply (al_frame _ _ LAWS); [exact HAR2 | | | reflexivity | reflexivity | reflexivity |].
  - intros a Ha Ho. apply AV2; [exact Ha|]. intros HGa. destruct (HG a HGa) as [Hi Hno].
    apply Hno. exact (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR2 Hi) Ho).
  - intros a Hv. rewrite aview_wrap64 in Hv |- *.
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ra. set (a' := a mod 2 ^ 64) in *.
    destruct (inGb G a') eqn:Hg.
    + apply inGb_spec in Hg. rewrite (AVT a' Ra Hg). destruct (HWd a') as [HW | HW].
      * destruct (HWg a' HW Hg) as [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
      * rewrite <- (Hfr a' Ra HW (SCG a' Hg)). exact Hv.
    + rewrite (AV2 a' Ra ltac:(apply inGb_false; exact Hg)). exact Hv.
  - intros a _ Hh. unfold memM. destruct (inGb G (bv_unsigned (w64 a))) eqn:Hg; [|reflexivity].
    exfalso. apply inGb_spec in Hg. pose proof (proj1 (HG _ Hg)) as Hi.
    rewrite (hidden_not_img SEGS W _ Hi) in Hh. discriminate. }
(* (i) the writes outside G, by the donor's ajournal_after_write *)
assert (HJM : ajournal SEGS B (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc W memM md2 k).
{ eapply (ajournal_after_write SEGS B LAWS Hsegs (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc W memT mdc k memM md2
    (fun a => (Wr a /\ ~ inG G a) \/ (sp0 + o - stk <= a < sp0 + o)) Sc own HJi).
  - intros a Ha Hn. destruct (inGb G a) eqn:Hg.
    + apply inGb_spec in Hg. exact (AVT a Ha Hg).
    + assert (HnG : ~ inG G a) by (apply inGb_false; exact Hg). rewrite (AV2 a Ha HnG).
      apply Hfr; [exact Ha | | intros Hs; apply Hn; right; exact Hs].
      intros HW. apply Hn. left. split; [exact HW | exact HnG].
  - intros a [Hh [b Hb]]. split; [exact Hh|]. unfold memM. destruct (inGb G (bv_unsigned (Z_to_bv 64 a))).
    + exists b. exact Hb.
    + exact (proj2 (Hgr a (conj Hh (ex_intro _ b Hb)))).
  - exact Hsame.
  - intros a [[HW HnG] | Hs]; left.
    + destruct (HWa a HW HnG) as [[Hs | Hrest] _]; [left; lia | right; exact Hrest].
    + left. lia.
  - exact HARM.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
(* (ii) the writes to G, by W_journal.v's ajournal_rebase, and (iii) the repack *)
assert (HJ2 : ajournal SEGS B (STK + XO) (sp0 + XO) FP ly S W0 (gover G memS mem2) md own lyc Sc W mem2 md2 k).
{ apply (ajournal_rebase SEGS B LAWS Hsegs G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 HG HJM).
  - intros x Hx. symmetry. exact (MG x Hx).
  - intros x Hx. unfold mrestrict in Hx |- *. destruct (w_H W x) eqn:Hh; [exact Hx|].
    destruct (inGb G (bv_unsigned x)) eqn:Hg; [|rewrite (MG x Hg) in Hx; exact Hx].
    rewrite (MT x Hg) in Hx. destruct (memT x) as [b|] eqn:Eb; [|exfalso; exact (Hx eq_refl)].
    assert (Hp : apresent (w_H W) memT (bv_unsigned x)) by (split; rewrite Z_to_bv_bv_unsigned; [exact Hh | exists b; exact Eb]).
    destruct (Hgr _ Hp) as [_ [b2 Hb2]]. rewrite Z_to_bv_bv_unsigned in Hb2. rewrite Hb2. discriminate. }
split.
{ apply (ajournal_gx_pack SEGS B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k (gover G memS mem2) HSTK HXO HJ2).
  - intros x Hx. unfold mrestrict, gover in *. rewrite Hx. exact (Hag x Hx).
  - intros a Ha Hno. rewrite <- (Hout a Ha Hno). apply Hfr; [lia | | lia].
    intros HW. destruct (inGb G a) eqn:Hg.
    + apply inGb_spec in Hg. pose proof (GLO a Hg). unfold kLowMemEnd in *. lia.
    + destruct (HWa a HW ltac:(apply inGb_false; exact Hg)) as [_ Hn]. exact (Hn Ha). }
split; [exact HP2|]. split; [exact HPr|]. split; [exact Hfr | exact Hgr].
Qed.

End d.
End b.
End a.
(* The sink head is EXPLICIT on the exported statements of this file that depend on it (a Theorem Labs lane, 21:57Z): the only
   global sink_head instance in fuzz_pcap's closure is the plain build's, so it must never be inferred. *)
Arguments aj_gx_entry_at {fx rc} SK {PI}.
