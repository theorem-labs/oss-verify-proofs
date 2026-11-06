(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecNf.v (commit 3d8ad2aeb77e, H4 stage B (slack-indexed post relation; DMrcDefs / DGif1Geo split; re-hide head); file sha256 262727ebd833) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMrcSecNf.v at commit ca2e244ea73, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (1 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4): the SECONDARY arm of __asan::QuarantineCallback::Recycle (0x33e88)
   without the cache flag: DMrcSec.rchunk_sec_mach over DMiface.rcc_pre_sec (rcc_pre_x without st_cache_inited X = true),
   in MnRecycle.de_rchunk_m_t's post without its st_cache_inited conjunct.
   rule 24: no function proved (a corollary of DMrcSec.rchunk_sec_mach, the walk proved there; one conjunct less in its pre
   and in its post).
   FIELDS: rc_sec_cut_nf_t / rc_sec_mapr_nf_t / rc_sec_step_nf_t are DMrcSecReads.rc_sec_cut_t / rc_sec_mapr_t /
   rc_sec_step_t over rcc_pre_sec, and the step without its last post conjunct st_cache_inited (YFg8.X2v X k r sm i) = true.
   ROUTE: the walk does not read the flag; it only carries it from rcc_pre_x through rc_sec_step_t to rc_mach_sec.  So
   rchunk_sec_mach is used unchanged, at X1 = set_cache_inited true X and over the relation and owned set read at the flag
   b of X ([ARXu ARXr b] / [AOXu AOX b]: ARXr / AOX at set_cache_inited b Y).  Its three fields at ARXu / AOXu follow from the
   flag-free fields (sec_cut does not read the flag: [sec_cut_flag]; the post flag of X2v Y is the pre flag of Y), and its
   post at X1 is the post at X: X1 differs from X only in the flag, and the munmap node's answer check (aok) does not read
   the snapshot ([amreal_unmap1]).  No walk file is copied.
   POST RELATION: rc_sec_step_nf_g is rc_sec_step_nf_t with the cut relation of the post a parameter [ARXp] indexed by
   the slack (DMrcSecReads.rc_sec_step_g: the post at ARXp (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP));
   rc_mach_nf_g is rc_mach_nf over a post relation [ARXp] (DMrcSec.rc_mach_sec_g).  Section e is the route over them
   (RSu_g, rchunk_sec_mach_nf_g, rchunk_sec_m_nf_g, through DMrcSec.rchunk_sec_mach_g: rc_mach_nf_g at the recycled
   slot's slack), Section i its ARXp := fun _ => ARXr instances (RSu, rchunk_sec_mach_nf, rchunk_sec_m_nf). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFex YFfu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFew YFeu YFfm YFf3 YFf4 YFff YFgu YFf5 YFgw YFfb YFg8 YFfc YB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG08 YG0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMwalkIF DMrcSecFc DMrcSecGv DMrcSecF6 DMrcSecMun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG MemnormT DMrcReads DMrcSecReads DMrcSec YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DIfaceR DMwalkIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0v YFfn YA05 YG0j YFfk.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Section f.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
(* DMrcSecReads.rc_sec_cut_t over rcc_pre_sec. *)
Definition rc_sec_cut_nf_t : Prop :=
forall inst ly X k cbp W regs mem md r o sm i,
rcc_pre_sec B ARXr inst ly X k cbp W regs mem md -> ck_beg k = PSec r o -> nth_error (st_secs X) r = Some sm ->
nth_error (st_sec_arr X) i = Some r -> In k (st_chunks X) -> ck_state k = CQuarantined ->
inst = as_inst B /\ ly_tsd ly = as_tsd B /\ Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly) /\
DMrcSecFc.sec_cut B ly X k W regs mem r o sm i.
(* DMrcSecReads.rc_sec_mapr_t over rcc_pre_sec. *)
Definition rc_sec_mapr_nf_t : Prop :=
forall inst ly X k cbp W regs mem md r o sm i,
rcc_pre_sec B ARXr inst ly X k cbp W regs mem md -> ck_beg k = PSec r o -> nth_error (st_secs X) r = Some sm ->
nth_error (st_sec_arr X) i = Some r ->
index_of (st_sec_arr X) r 0%nat = Some i /\
In (YFg8.MAP ly r, YFg8.MAP ly r + YFg8.LEN sm) (w_A W) /\ In (w64 (YFg8.MAP ly r), w64 (YFg8.LEN sm)) (vm_maps (m_vmmaps md)) /\ amwf md /\
(forall PB kk, 0 < kk -> DMrcSecGv.SHAv (YFg8.MAP ly r) <= PB -> PB + kk <= DMrcSecGv.SHEv (YFg8.MAP ly r) (YFg8.LEN sm) ->
 madvise_dontneed_ok (m_vmmaps md) (Z_to_bv 64 PB) (Z_to_bv 64 kk) = true).
End f.
Section g.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable ARXp : Z -> (Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
(* DMrcSecReads.rc_sec_step_g over rcc_pre_sec, without its last post conjunct st_cache_inited (YFg8.X2v X k r sm i) = true. *)
Definition rc_sec_step_nf_g : Prop :=
forall inst ly X k cbp W regs mem md r o sm i regsD memD mat1 regs' mem' mat,
rcc_pre_sec B ARXr inst ly X k cbp W regs mem md -> ck_beg k = PSec r o -> nth_error (st_secs X) r = Some sm ->
nth_error (st_sec_arr X) i = Some r ->
In k (st_chunks X) -> ck_state k = CQuarantined -> ~ In (ck_beg k) (map ck_beg (q_items X)) ->
DMrcSecMun.LINKD ly W regs mem regsD memD ->
let MAP := YFg8.MAP ly r in let LEN := YFg8.LEN sm in
let mdM := munmap_model (w64 MAP) (w64 LEN) (with_vm_backing (m_vm_lazy md) mat1 md) in
DMrcSecGv.at_RET W ly regsD memD MAP LEN (YFg8.idx i) (YFg8.nA X) (YFg8.qi ly i) (YFg8.lst ly X r)
  (DMrcSecF6.v regs 1%bv) (DMrcSecF6.v regs 8%bv) (DMrcSecF6.v regs 9%bv) (DMrcSecF6.v regs 18%bv) (YFg8.own X i) mdM
  W (mkCfg (mkst regs' (w64 (DMrcSecF6.v regs 1%bv)) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy mdM) mat mdM)) ->
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (as_const B ly) ->
ARXp (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP) inst ly (YFg8.X2v X k r sm i) (YFg8.W2 ly W r sm) mem'
  (with_vm_backing (m_vm_lazy mdM) mat mdM) /\
(forall a, 0 <= a < 2 ^ 64 -> DMrcSecMun.WPRE ly regs a \/ DMrcSecGv.WIN3 ly regs MAP LEN (YFg8.qi ly i) (YFg8.lst ly X r) a ->
 AOX ly X a \/ ascratch B KSTACK_CF regs a) /\
(forall a, AOX ly (YFg8.X2v X k r sm i) a -> AOX ly X a) /\
(forall a, YFeuC.puser ly X a -> YFeuC.puser ly (YFg8.X2v X k r sm i) a) /\
(forall a, YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
 ~ DMrcSecMun.WPRE ly regs a /\ ~ DMrcSecGv.WIN3 ly regs MAP LEN (YFg8.qi ly i) (YFg8.lst ly X r) a).
End g.
Section gm.
Variable B : asyms.
Variable ARXp : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
(* DMrcSec.rc_mach_sec_g without its st_cache_inited conjunct. *)
Definition rc_mach_nf_g (inst : Z) (ly : alayout) (X : astate) (k : chunk) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (r0 : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXp AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\
  MemnormT.memnorm_keep tfibsegs mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r0) a) /\
  (forall a, AOX ly (snd r0) a -> AOX ly X a).
End gm.
Section t.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
(* DMrcSecReads.rc_sec_step_t over rcc_pre_sec, without its last post conjunct st_cache_inited (YFg8.X2v X k r sm i) = true. *)
Definition rc_sec_step_nf_t : Prop := rc_sec_step_nf_g B ARXr (fun _ => ARXr) AOX.
(* DMrcSec.rc_mach_sec without its st_cache_inited conjunct. *)
Definition rc_mach_nf (inst : Z) (ly : alayout) (X : astate) (k : chunk) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (r0 : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
rc_mach_nf_g B ARXr AOX inst ly X k W regs mem md r0 W' c'.
End t.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The flag is read by none of these.                                                                               *)

(* The cut-read record does not read the flag. *)
Lemma sec_cut_flag : forall B ly X k W regs mem r o sm i b,
DMrcSecFc.sec_cut B ly (set_cache_inited b X) k W regs mem r o sm i -> DMrcSecFc.sec_cut B ly X k W regs mem r o sm i.
Proof. intros B ly X k W regs mem r o sm i b []. constructor; assumption. Qed.

Lemma flag_eta : forall X, set_cache_inited (st_cache_inited X) (set_cache_inited true X) = X.
Proof. intros []. reflexivity. Qed.

(* The munmap node (aok (KMunmapSec _ _) z is z = 1, whatever the snapshot): its realization at snapshot s1 and answer
   v1 gives the one at s2 and v2 when the post at v1 gives the post at v2. *)
Lemma amreal_unmap1 {R} : forall r len (s1 s2 : astate) (v1 v2 : R) W c (Q1 Q2 : R -> world tfibsegs -> config -> Prop),
(forall W' c', Q1 v1 W' c' -> Q2 v2 W' c') ->
amreal tfibsegs (IAsk (KMunmapSec r len) s1 (fun _ => IRet v1)) W c Q1 ->
amreal tfibsegs (IAsk (KMunmapSec r len) s2 (fun _ => IRet v2)) W c Q2.
Proof.
intros r len s1 s2 v1 v2 W c Q1 Q2 HQ H. cbn [amreal aok] in *.
eapply SRr_mono; [exact H|]. intros W1 c1 _ (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc).
exists J, nx, bit, sp, i0. do 7 (split; [assumption|]).
intros j Hj. eapply SRr_mono; [exact (Hc j Hj) | intros W' c' _ H1; exact (HQ W' c' H1)].
Qed.

(* The relation and the owned set read at the flag [b]. *)
Definition ARXu (ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop) (b : bool) :
  Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop :=
fun inst ly Y W mem md => ARXr inst ly (set_cache_inited b Y) W mem md.
Definition AOXu (AOX : alayout -> astate -> Z -> Prop) (b : bool) : alayout -> astate -> Z -> Prop :=
fun ly Y a => AOX ly (set_cache_inited b Y) a.

(* The route over the step field rc_sec_step_nf_g, whose post relation [ARXp] is indexed by the slack. *)
Section e.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable ARXp : Z -> (Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variables NMAXD LMAXD : Z.
Hypothesis NOK : DMwalkIF.nmaxd_ok NMAXD.
Hypothesis LOK : DMwalkIF.lmaxd_ok NMAXD LMAXD.
Hypothesis RCnf : rc_sec_cut_nf_t B ARXr.
Hypothesis RMnf : rc_sec_mapr_nf_t B ARXr.
Hypothesis RSnf : rc_sec_step_nf_g B ARXr ARXp AOX.
Hypothesis RHD : DMrcReads.rc_head_t DRq.
Hypothesis RMD : DMrcReads.rc_model_t DRq.
Hypothesis RDS : DMwalkIF.drq_sizes DRq NMAXD LMAXD.

Lemma pre_u : forall b inst ly Y k cbp W regs mem md, rcc_pre_x B (ARXu ARXr b) inst ly Y k cbp W regs mem md ->
rcc_pre_sec B ARXr inst ly (set_cache_inited b Y) k cbp W regs mem md.
Proof. intros b inst ly Y k cbp W regs mem md (HA & _ & P). exact (conj HA P). Qed.

(* DMrcSec's three fields at ARXu b / AOXu b. *)
Lemma RCu : forall b, DMrcSecReads.rc_sec_cut_t B (ARXu ARXr b).
Proof.
intros b inst ly Y k cbp W regs mem md r o sm i P Hb Hsm Hi Hk Hst.
destruct (RCnf inst ly (set_cache_inited b Y) k cbp W regs mem md r o sm i (pre_u b inst ly Y k cbp W regs mem md P) Hb Hsm Hi Hk Hst)
  as (H1 & H2 & H3 & SC).
exact (conj H1 (conj H2 (conj H3 (sec_cut_flag B ly Y k W regs mem r o sm i b SC)))).
Qed.
Lemma RMu : forall b, DMrcSecReads.rc_sec_mapr_t B (ARXu ARXr b).
Proof.
intros b inst ly Y k cbp W regs mem md r o sm i P Hb Hsm Hi.
exact (RMnf inst ly (set_cache_inited b Y) k cbp W regs mem md r o sm i (pre_u b inst ly Y k cbp W regs mem md P) Hb Hsm Hi).
Qed.
Lemma RSu_g : forall b, DMrcSecReads.rc_sec_step_g B (ARXu ARXr b) (fun d => ARXu (ARXp d) b) (AOXu AOX b).
Proof.
intros b inst ly Y k cbp W regs mem md r o sm i regsD memD mat1 regs' mem' mat P Hb Hsm Hi Hk Hst Hni LNK.
cbv zeta. intros HR CONST.
pose proof P as (_ & Hci & _).
destruct (RSnf inst ly (set_cache_inited b Y) k cbp W regs mem md r o sm i regsD memD mat1 regs' mem' mat
  (pre_u b inst ly Y k cbp W regs mem md P) Hb Hsm Hi Hk Hst Hni LNK HR CONST) as (A1 & A2 & A3 & A4 & A5).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. exact Hci.
Qed.

(* The machine part: DMrcSec.rchunk_sec_mach_g at X1 = set_cache_inited true X over ARXu / AOXu at the flag of X, the
   post relation at the recycled slot's slack. *)
Theorem rchunk_sec_mach_nf_g : forall inst ly X k cbp W regs mem md r o sm i,
rcc_pre_sec B ARXr inst ly X k cbp W regs mem md -> ck_beg k = PSec r o -> nth_error (st_secs X) r = Some sm ->
nth_error (st_sec_arr X) i = Some r -> ck_n k < NMAXD -> ck_extent k <= LMAXD -> ck_state k = CQuarantined ->
~ In (ck_beg k) (map ck_beg (q_items X)) -> In k (st_chunks X) ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md)
  (rc_mach_nf_g B (ARXp (YGcfRehidePost.rh_hi (YFg8.MAP ly r) (YFg8.LEN sm) - YGcfRehidePost.rh_lo (YFg8.MAP ly r))) AOX
     inst ly X k W regs mem md).
Proof.
intros inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi HN HE Hst Hni Hkin.
pose proof (RCnf inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hkin Hst) as (_ & _ & _ & SC).
pose proof (RMnf inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi) as (Hidx & _).
pose proof (DMrcSecMun.SMALL B ly X k W regs mem r o sm i SC NMAXD LMAXD LOK HE) as SMALL.
assert (PRE1 : rcc_pre_x B (ARXu ARXr (st_cache_inited X)) inst ly (set_cache_inited true X) k cbp W regs mem md).
{ destruct PRE as (HA & P). split; [unfold ARXu; rewrite flag_eta; exact HA | split; [reflexivity | exact P]]. }
pose proof (DMrcSec.rchunk_sec_mach_g B TB (ARXu ARXr (st_cache_inited X)) (fun d => ARXu (ARXp d) (st_cache_inited X))
  (AOXu AOX (st_cache_inited X))
  (RCu _) (RMu _) (RSu_g _)
  NMAXD LMAXD NOK LOK inst ly (set_cache_inited true X) k cbp W regs mem md r o sm i PRE1 Hb Hsm Hi HN HE Hst Hni Hkin) as M.
rewrite (YFg8.recycle_chunk_sec k X r o sm i (proj2 (mem_chunk_spec _ _) Hkin) Hb Hsm Hidx SMALL).
rewrite (YFg8.recycle_chunk_sec k (set_cache_inited true X) r o sm i (proj2 (mem_chunk_spec _ _) Hkin) Hb Hsm Hidx SMALL) in M.
clear - M. destruct X.
eapply amreal_unmap1; [|exact M].
intros W' c' (regs' & mem' & md' & Hc & HP & HR & HE & HK & HV & PU & _ & AO).
exists regs', mem', md'.
split; [exact Hc|]. split; [exact HP|]. split; [exact HR|]. split; [exact HE|]. split; [exact HK|].
split; [exact HV|]. split; [exact PU | exact AO].
Qed.

(* The secondary arm in MnRecycle.de_rchunk_m_t's post (as DMrc.rchunk_ok uses it) without its st_cache_inited
   conjunct: the machine part, and the model part from rc_model_t. *)
Theorem rchunk_sec_m_nf_g : forall inst ly X k ks zs cbp W regs mem md r o sm i,
rcc_pre_sec B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs -> ck_beg k = PSec r o ->
nth_error (st_secs X) r = Some sm -> nth_error (st_sec_arr X) i = Some r ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md)
(fun r0 W' c' => exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  acall_post_x B (ARXp (YGcfRehidePost.rh_hi (YFg8.MAP ly r) (YFg8.LEN sm) - YGcfRehidePost.rh_lo (YFg8.MAP ly r))) AOX inst
    KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\
  MemnormT.memnorm_keep tfibsegs mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r0) a) /\
  DRq (snd r0) ks zs /\ (forall a, AOX ly (snd r0) a -> AOX ly X a)).
Proof.
intros inst ly X k ks zs cbp W regs mem md r o sm i PRE RX Hb Hsm Hi.
pose proof (RDS X (k :: ks) zs k RX (or_introl eq_refl)) as [[_ HN] HE].
destruct (RHD X k ks zs RX) as (Hkin & Hst & Hni).
pose proof (amreal_apost tfibsegs _ _ W _ _ (RMD X k ks zs RX)
  (rchunk_sec_mach_nf_g inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi HN HE Hst Hni Hkin)) as A.
eapply amreal_mono; [|exact A]. cbv beta.
intros r0 W' c' [DQ (regs' & mem' & md' & Hc & HP & HR & HE' & HK & HV & PU & AO)].
exists regs', mem', md'. repeat (split; [assumption|]). exact AO.
Qed.
End e.

(* The route at ARXp := fun _ => ARXr. *)
Section i.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variables NMAXD LMAXD : Z.
Hypothesis NOK : DMwalkIF.nmaxd_ok NMAXD.
Hypothesis LOK : DMwalkIF.lmaxd_ok NMAXD LMAXD.
Hypothesis RCnf : rc_sec_cut_nf_t B ARXr.
Hypothesis RMnf : rc_sec_mapr_nf_t B ARXr.
Hypothesis RSnf : rc_sec_step_nf_t B ARXr AOX.
Hypothesis RHD : DMrcReads.rc_head_t DRq.
Hypothesis RMD : DMrcReads.rc_model_t DRq.
Hypothesis RDS : DMwalkIF.drq_sizes DRq NMAXD LMAXD.

Lemma RSu : forall b, DMrcSecReads.rc_sec_step_t B (ARXu ARXr b) (AOXu AOX b).
Proof. exact (RSu_g B ARXr (fun _ => ARXr) AOX RSnf). Qed.

(* The machine part: DMrcSec.rchunk_sec_mach at X1 = set_cache_inited true X over ARXu / AOXu at the flag of X. *)
Theorem rchunk_sec_mach_nf : forall inst ly X k cbp W regs mem md r o sm i,
rcc_pre_sec B ARXr inst ly X k cbp W regs mem md -> ck_beg k = PSec r o -> nth_error (st_secs X) r = Some sm ->
nth_error (st_sec_arr X) i = Some r -> ck_n k < NMAXD -> ck_extent k <= LMAXD -> ck_state k = CQuarantined ->
~ In (ck_beg k) (map ck_beg (q_items X)) -> In k (st_chunks X) ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rc_mach_nf B ARXr AOX inst ly X k W regs mem md).
Proof. exact (rchunk_sec_mach_nf_g B TB ARXr (fun _ => ARXr) AOX NMAXD LMAXD NOK LOK RCnf RMnf RSnf). Qed.

(* The secondary arm in MnRecycle.de_rchunk_m_t's post (as DMrc.rchunk_ok uses it) without its st_cache_inited
   conjunct: the machine part, and the model part from rc_model_t. *)
Theorem rchunk_sec_m_nf : forall inst ly X k ks zs cbp W regs mem md r o sm i,
rcc_pre_sec B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs -> ck_beg k = PSec r o ->
nth_error (st_secs X) r = Some sm -> nth_error (st_sec_arr X) i = Some r ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md)
(fun r0 W' c' => exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\
  MemnormT.memnorm_keep tfibsegs mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r0) a) /\
  DRq (snd r0) ks zs /\ (forall a, AOX ly (snd r0) a -> AOX ly X a)).
Proof. exact (rchunk_sec_m_nf_g B TB ARXr (fun _ => ARXr) AOX DRq NMAXD LMAXD NOK LOK RCnf RMnf RSnf RHD RMD RDS). Qed.
End i.
End d.
