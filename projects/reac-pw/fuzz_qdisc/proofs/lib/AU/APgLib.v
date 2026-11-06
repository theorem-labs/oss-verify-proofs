(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements
   are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc's ASan image (fuzz_qdisc.asan, sha256
   980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e) from
   proofs/libreac/fuzz_knock/lib/A/APgLib.v at origin/ossv/recipes 6ebe35ba632, with its module paths
   changed. rule 24 (reuse): no function is proved here; this file is the program contract's statement, its
   closed form and the bridge to the core's contract text. Names knock_* -> qdisc_*; the pre and the post are
   lib/A/QPgCSpec.v's image-independent text (qd_lib_pre_x / qd_lib_post_x / qd_lib_contract_x) at this image's
   instance; the walk is S0 + the loop closed by induction on the budget + the exit; no fake-frame links (the
   harness calls no allocator); LEAF holds by eq_refl at AgreeQdisc.ag_sil_shape (ZTraceSpec.checksum_shape). *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/QPgLib.v of this library, for fuzz_qdisc's
   ASan-UBSan image (fuzz_qdisc.asan-ubsan, sha256 eb657d77bd4b27038d93f75626dcc6b37a48be09c889fda664b4f451c6602062),
   written by hand from that file. What differs:
   - imports: the lib/AU twins (AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm YE2k YF0m YD2l, YD1u
     and YCfn Required) and image B's walk files lib/AU/APgRt, APgLoop0, APgCatch, APgCheck, APgMain0, APgMain1,
     APgMain2, APgMain3, APgMain7, APgMainL; the shared texts lib/A/QPgBase.v and lib/A/QPgCSpec.v are the same.
   - constants: A_LLVMF 0x7e694, RA_LLVMF 0x7e590, A_EMPTY 0x5cff20, EV_LIB 0, LIVE_LIB 2 ^ 33, LLVMF_STK 32768
     are lib/AU/YCfm.v's; the read-only pair is image B's .data.rel.ro start .. .got end, RO_LO 0x953a0 ..
     RO_HI 0x965f8 (section headers of the pinned image; the second disjunct of lib/AU/YCeh.v in_ro_tfa).
   - the two callee contracts are discharged by lib/AU/APgCatch.v qdisc_pb_slotsX and lib/AU/APgCheck.v
     qdisc_pb_checkX at image B's entries 0x7e984 and 0x7e8a4 and the divisor cell 0x10350.
   - qdisc_TfibLib and qdisc_ROB are proved over image B's record (lib/AU/YD2l.v TfibB, lib/AU/YF0m.v tables) and
     segments. As on image A, the callee walks are concrete (no program listing, no PAImg bridge), so this file
     needs neither knock's lib/AU/APgImg.v nor APgImgLink.v.
   The statement of qdisc_lib_x_all is the A file's at image B's names: Section {rc} {LS} and the one hypothesis
   LEAF, which the closing join discharges by eq_refl at AgreeQdisc.ag_sil_shape. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG05 YG0q YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import QPgBase QPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import APgRt APgLoop0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import APgCatch APgCheck APgMain0 APgMain1 APgMain2 APgMain3 APgMain7 APgMainL.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import YE2k YF0m YD2l.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require YD1u YCfn.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YI5b.
(* SINK-HEAD GUARD (knock A/APgLib.v:59-67): this file's load closure carries the plain build's
   `#[global] Instance src0_sink_head` (Reusable/YI5b.v:12). It is removed, #[global], so no
   {SK : YI16.sink_head} is ever inferred here or in a file that loads this one; lib/AU/YE2k.v's
   tfib_sink_head is passed by name at every SK use. *)
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* fuzz_qdisc asan-ubsan .data.rel.ro start .. .got end (section headers of the pinned image), the second
   disjunct of AU/YCeh.v in_ro_tfa *)
Definition RO_LO : Z := 0x953a0.
Definition RO_HI : Z := 0x965f8.
Definition XL0 : Z -> Z := fun _ => 0.
Lemma XL0_HXL : forall n, 0 <= XL0 n. Proof. intros n. unfold XL0. lia. Qed.

(* ============================== the contract ============================== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Definition qdisc_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world tfibsegs)
(mem : word -> option byte) (md : Model) (p n : Z) (pl : list byte) (M : Z) : Prop :=
qd_lib_pre_x tfibsegs B MT tfib_K XM_LIB RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK
regs ly S W mem md p n pl M.
Definition qdisc_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world tfibsegs)
(mem : word -> option byte) (md : Model) (p n : Z) (M : Z) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world tfibsegs) (regs' : bvmap 5 word) (mem' : word -> option byte)
(md' : Model) (k : Z) : Prop :=
qd_lib_post_x tfibsegs B MT tfib_K XN_LIB EV_LIB LLVMF_STK
regs ly S W mem md p n M l ly' S' W' regs' mem' md' k.
Definition qdisc_lib_contract_x : Prop :=
qd_lib_contract_x tfibsegs B MT tfib_K XM_LIB XN_LIB RLO RHI
A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
End a.
Definition qdisc_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
forall fx : YK11.FPState, @qdisc_lib_contract_x fx rc LS B MT XM_LIB XN_LIB RLO RHI.

(* ============================== journal facts [knock A/APgLib.v:126-168] ============================== *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Lemma ajournal_fp_nil : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal (SK := SK) segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (sink_closed_nil Ho)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi _; apply (F2 p n i H1 H2 Hi); apply inFP_nil|].
split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply (fp_spares_closed (SK := SK)); intros Ho; exact (sink_closed_nil Ho)|].
split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply inFP_nil|].
split; [intros p n i H1 H2 Hi; exfalso; exact (inFP_nil _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.
Lemma ajournal_closed_io : forall STK sp0 FP ly S (W : world segs) mem md own ly' S' W' mem' md' k,
~ YI16.sink_open_fp FP ->
ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k Hcl HJ. pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed FP md md' Hcl Hos) as (Efd & Efsys & _ & _).
unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.
Lemma ajournal_nil_io : forall STK sp0 ly S (W : world segs) mem md own ly' S' W' mem' md' k,
ajournal (SK := SK) segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ. exact (ajournal_closed_io _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sink_closed_nil HJ). Qed.
End e.
Section f.
Variable segs : list Segment.
Lemma srz_enter : forall (W : world segs) (c : config) (T : TSet),
AI segs (w_H W) (w_A W) (cfg_model c) ->
SRr segs W c (fun W' c' => AI segs (w_H W') (w_A W') (cfg_model c') -> srealizes segs c' T) -> srealizes segs c T.
Proof. intros W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.
End f.
End d.
(* the read-only premise of QPgCSpec's text is lib/A/QPgBase.v's image-independent in_roP; at this
   image's RO_LO / RO_HI it is exactly lib/AU/YCeh.v's arodata_ok, which the walk takes *)
Lemma qd_rod_of_P : forall B rd, arodata_okP tfibsegs RO_LO RO_HI B rd -> arodata_ok B rd.
Proof. intros B rd H a Ha. apply H. exact Ha. Qed.
(* in_ro_tfa lies below the sink head A_ofl_head 0x5f0f48 (lib/AU/YE2k.v:28, 37): its read-only segments
   are the first two PT_LOADs, which end at 0x2e9ec and 0x94368, and its second disjunct is 0x953a0 ..
   0x965f8 (lib/AU/YCeh.v:58-60). lib/AU/APgMain2.v and APgMain3.v carry arodata_ok along the journal with
   YCeh.arodata_ok_journal, which needs this. Local, so the statement of qdisc_lib_x_all does not change. *)
#[local] Instance qdisc_ROB : @YCeh.ro_tfa_below_ofl tfib_sink_head.
Proof.
intros a [(sg & Hs & Hw & Hr) | Hr]; cbn [YI16.sk_ofl_head tfib_sink_head]; unfold A_ofl_head; [|lia].
assert (E : tfibsegs = [AsanUbsan.AsanUbsan_segment_000; AsanUbsan.AsanUbsan_segment_001;
  AsanUbsan.AsanUbsan_segment_002; AsanUbsan.AsanUbsan_segment_003])
by reflexivity.
rewrite E in Hs. destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; vm_compute in Hw; try discriminate Hw;
lazymatch type of Hr with ?lo <= a < ?hi =>
let l := eval vm_compute in lo in let h := eval vm_compute in hi in change (l <= a < h) in Hr end; lia.
Qed.

(* ============================== the proof [knock A/APgLib.v:170-243] ============================== *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AIL : asink_img_laws (SK := tfib_sink_head) tfibsegs B tfib_K.
Hypothesis HB : TfibSyms B.
(* the two callee contracts, at image B's entries and its divisor cell *)
Hypothesis SLOTS : qdisc_slots_specX (SK := tfib_sink_head) tfibsegs B MT A_QD_SLOTS A_QD_MAGIC.
Hypothesis CHECK : qdisc_check_specX (SK := tfib_sink_head) tfibsegs B MT A_QD_CHECK A_QD_MAGIC.
Variable XL : Z -> Z.
Hypothesis HXL : forall n, 0 <= XL n.
Hypothesis LEAF : forall pl fs (K : lleaf -> TSet), LIBK pl fs K = K (LL 0 fs []).
(* the harness walk S1 .. S3 and its exit, closed by the budget induction. The divisor cell's premise is
   lib/AU/APgMain3.v's own lemma qd_magic_rom, so it is not a hypothesis here. *)
Let POSTQ := rt_post (SK := tfib_sink_head) B MT [].
Let RX : rt_from (SK := tfib_sink_head) B MT [] POSTQ ss_X (INV_X B MT) :=
rt_X (SK := tfib_sink_head) B MT MTL [] TL LAWS.
Let RL : rt_from (SK := tfib_sink_head) B MT [] POSTQ ss_L (INV_L B MT 7) :=
rt_loop (SK := tfib_sink_head) B MT [] POSTQ
(rt_S1 (SK := tfib_sink_head) B MT [] POSTQ TL LAWS eq_refl)
(rt_S2 (SK := tfib_sink_head) B MT [] POSTQ TL LAWS HB)
(rt_S3 (SK := tfib_sink_head) B MT MTL [] POSTQ TL LAWS SLOTS CHECK)
RX.
Theorem qdisc_lib_x_body :
forall ly S (W : world tfibsegs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI tfibsegs (w_H W) (w_A W) md ->
qdisc_lib_pre_x B MT XL RO_LO RO_HI regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world tfibsegs) (c' : config),
wle W W' -> AI tfibsegs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
qdisc_lib_post_x B MT XL regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes tfibsegs c' (K l)) ->
srealizes tfibsegs (cfg_at tfibsegs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
Proof.
intros ly S W regs mem md p n pl M K HAI HPRE HK.
rewrite LEAF.
unfold qdisc_lib_pre_x, qd_lib_pre_x in HPRE.
destruct HPRE as (HPRE0 & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK & HFD & HSORT & HAM & HMOK).
assert (HROD : arodata_ok B (aview tfibsegs (w_H W) mem)) by (apply qd_rod_of_P; exact HROS).
apply (srz_enter tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md) _ HAI).
eapply SRr_mono.
{ exact (qdisc_lib_A_seg (SK := tfib_sink_head) B MT MTL TL LAWS [] eq_refl POSTQ RL RX
  ly S W regs mem md p n (XL n) HPRE0 Hra Hp Hn Hpn Hfr0 Hev Hlive HROD HMOK (HXL n)). }
intros W' c' Hwle HPOST HAI'.
unfold rt_post, rt_postP in HPOST.
destruct HPOST as (ly' & S' & regs' & mem' & md' & k' & -> & HJ & Hk & HPR & Ha0 & HPerm & HMLE & _).
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_E0 c_T] in HJ, HPR, HPerm, HMLE.
destruct (ajournal_nil_io tfib_sink_head tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efds Efs].
apply (HK (LL 0 (m_fs md) []) W' _ Hwle HAI').
exists ly', S', regs', mem', md', k'. split; [reflexivity|].
unfold qdisc_lib_post_x, qd_lib_post_x. cbn [ll_fs ll_ret ll_out].
assert (HSNK' : asink_none tfibsegs tfib_K (mrestrict (w_H W') mem') md').
{ eapply (asink_none_kept (SK := tfib_sink_head) tfibsegs B tfib_K AIL); [exact HJ | intros Ho; exact (sink_closed_nil Ho) | exact HSNK]. }
split; [apply (ajournal_fp_nil tfib_sink_head); exact HJ|]. split; [exact Hk|]. split; [exact HPR|]. split; [exact Ha0|].
split; [exact HPerm|].
split; [intros fd; rewrite Efds; reflexivity|].
split; [exact Efs|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT|].
split; [exact HSNK'|].
split; [exact (ameta_inv_kept (SK := tfib_sink_head) tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAM)|].
split; [exact HMLE|].
intros i Hi. destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hi Hn0; lia|].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hpin).
- eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. exact Hpin.
- unfold req_size. destruct (Z.eqb_spec n 0) as [Heq0|Hne0]; [exfalso; clear - Hnpos Heq0; lia | exact Hi].
- apply inFP_nil.
Qed.
Theorem qdisc_lib_x : qdisc_lib_contract_x B MT XL XL RO_LO RO_HI.
Proof. exact qdisc_lib_x_body. Qed.
End h.
End g.

(* ============================== the links and the closed form ==============================
   As on image A, image B has no program listing and no PAImg bridge -- the two callee walks are concrete
   (lib/AU/APgCatch.v, APgCheck.v) -- so the TfibLib instance is proved here, from lib/AU/YD2l.v's record
   and lib/AU/YF0m.v's start-up tables. Every field is a numeral of the pinned image. *)
Lemma qdisc_TfibLib : TfibLib TfibB.
Proof.
constructor; try reflexivity.
- (* errno sits in the bss: TFIB_ERRNO = 0x5d07ac (lib/AU/YF0m.v:21) *)
  cbn [as_errno TfibB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- (* ... inside the fourth PT_LOAD [0x975f8, 0x5f2130), page range [0x97000, 0x5f3000) *)
  intros a Ha. cbn [as_errno TfibB] in Ha. unfold TFIB_ERRNO in Ha.
  exists AsanUbsan.AsanUbsan_segment_003. split; [do 3 right; left; reflexivity|].
  let b := eval vm_compute in (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_003)) in
  let z := eval vm_compute in (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_003)) in
  change (b <= a < b + z); lia.
- (* the two .rodata cells the program reads, 0x10350 and the frame-rate table 0x20c80 .. 0x20c98, are in no
     Tfib_owned_static row (each row is checked: the nearest, (0x20c98, 0x28), starts at the table's end) nor errno *)
  intros a Ha. cbn [as_owned_static as_errno TfibB]. unfold Tfib_owned_static, TFIB_ERRNO, lib_const_addr in *.
  split; [|lia]. intros HEx. apply Exists_exists in HEx as (r & Hr & Hin). unfold in_zr in Hin.
  repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Hin; lia|]). destruct Hr.
- cbn [as_gp TfibB]. unfold TFIB_GP. lia.
Qed.
Section f. Context {rc : YM05.RunCeil} {LS : lib_shape}.
Hypothesis LEAF : forall pl fs (K : lleaf -> TSet), LIBK pl fs K = K (LL 0 fs []).
Theorem qdisc_lib_x_all : qdisc_lib_contract_x_all TfibB ameter_triv XL0 XL0 RO_LO RO_HI.
Proof.
intros fx.
pose proof (model_laws_ok (as_universe TfibB) (ts_universe TfibB TfibB_syms)) as MLB.
exact (qdisc_lib_x (fx := fx) (LS := LS) TfibB ameter_triv ameter_triv_laws qdisc_TfibLib
(AR_laws_ok tfibsegs TfibB) (YD1u.tfib_AIL TfibB TfibB_syms) TfibB_syms
(qdisc_pb_slotsX TfibB ameter_triv ameter_triv_laws qdisc_TfibLib (AR_laws_ok tfibsegs TfibB) MLB)
(qdisc_pb_checkX TfibB ameter_triv ameter_triv_laws qdisc_TfibLib (AR_laws_ok tfibsegs TfibB) MLB)
XL0 XL0_HXL LEAF).
Qed.
End f.

(* ============================== the bridge to the core's contract [knock A/APgLib.v:315-371] ==========
   The AU core (lib/AU/YD2f.v, YD1m.v) and image B's join take YCfn.tfib_lib_contract_x_all. The two texts
   are the same with YCfn's constants for YCfm's: A_LLVMF, RA_LLVMF, A_EMPTY, LIVE_LIB and LLVMF_STK are equal
   in both (qdisc_consts), and EV_LIB is 2000 in YCfn and 0 in YCfm (qdisc_ev). So YCfn's pre gives this
   file's pre and this file's post gives YCfn's, at the same B MT XM_LIB XN_LIB RLO RHI. YCfn is Required,
   not Imported, so its names keep the YCfn prefix. *)
Lemma qdisc_consts :
  YCfn.A_LLVMF = A_LLVMF /\ YCfn.RA_LLVMF = RA_LLVMF /\ YCfn.A_EMPTY = A_EMPTY /\
  YCfn.LIVE_LIB = LIVE_LIB /\ YCfn.LLVMF_STK = LLVMF_STK.
Proof. repeat split; reflexivity. Qed.
Lemma qdisc_ev : EV_LIB <= YCfn.EV_LIB.
Proof. unfold EV_LIB, YCfn.EV_LIB. lia. Qed.
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Lemma qdisc_lib_pre_x_of_tfib : forall regs ly S (W : world tfibsegs) mem md p n pl M,
  YCfn.tfib_lib_pre_x B MT XM_LIB RLO RHI regs ly S W mem md p n pl M ->
  qdisc_lib_pre_x B MT XM_LIB RLO RHI regs ly S W mem md p n pl M.
Proof.
intros regs ly S W mem md p n pl M H. unfold YCfn.tfib_lib_pre_x in H. unfold qdisc_lib_pre_x, qd_lib_pre_x.
destruct qdisc_consts as (_ & HRA & HE & HLIVE & HSTK). rewrite HRA, HE, HLIVE, HSTK in H.
destruct H as (HPRE & HRA' & H10 & H11 & HPN & HLEN & HARR & HFR & HEV & HREST).
refine (conj HPRE (conj HRA' (conj H10 (conj H11 (conj HPN (conj HLEN (conj HARR (conj HFR (conj _ HREST))))))))).
pose proof qdisc_ev as Hle. lia.
Qed.
Lemma qdisc_lib_post_x_tfib : forall regs ly S (W : world tfibsegs) mem md p n M l ly' S' W' regs' mem' md' k,
  qdisc_lib_post_x B MT XN_LIB regs ly S W mem md p n M l ly' S' W' regs' mem' md' k ->
  YCfn.tfib_lib_post_x B MT XN_LIB regs ly S W mem md p n M l ly' S' W' regs' mem' md' k.
Proof.
intros regs ly S W mem md p n M l ly' S' W' regs' mem' md' k H.
unfold qdisc_lib_post_x, qd_lib_post_x in H. unfold YCfn.tfib_lib_post_x.
destruct qdisc_consts as (_ & _ & _ & _ & HSTK). rewrite HSTK.
destruct H as (HJ & Hk & HREST).
refine (conj HJ (conj _ HREST)).
pose proof qdisc_ev as Hle. lia.
Qed.
Lemma qdisc_lib_contract_x_tfib :
  qdisc_lib_contract_x B MT XM_LIB XN_LIB RLO RHI -> YCfn.tfib_lib_contract_x B MT XM_LIB XN_LIB RLO RHI.
Proof.
unfold qdisc_lib_contract_x, qd_lib_contract_x, YCfn.tfib_lib_contract_x.
destruct qdisc_consts as (HA & HRA & _ & _ & _). rewrite HA, HRA.
intros HX ly S W regs mem md p n pl M K HAI HPRE HK.
apply (HX ly S W regs mem md p n pl M K HAI (qdisc_lib_pre_x_of_tfib regs ly S W mem md p n pl M HPRE)).
intros l W' c' Hle HAI' (ly' & S' & regs' & mem' & md' & k & Hc & HPOST).
apply (HK l W' c' Hle HAI').
exists ly', S', regs', mem', md', k. split; [exact Hc|].
exact (qdisc_lib_post_x_tfib regs ly S W mem md p n M l ly' S' W' regs' mem' md' k HPOST).
Qed.
End k.
Lemma qdisc_lib_contract_x_all_tfib {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops)
  (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) :
  qdisc_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI -> YCfn.tfib_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI.
Proof. intros HX fx. exact (qdisc_lib_contract_x_tfib (fx := fx) B MT XM_LIB XN_LIB RLO RHI (HX fx)). Qed.
