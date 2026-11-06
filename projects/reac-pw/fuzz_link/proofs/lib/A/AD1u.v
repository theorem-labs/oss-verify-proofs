(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1u.v (origin/ossv/recipes c8557374ad2e), with its module paths changed, names TfibSyms -> PcapSyms and its addresses moved to libreac/fuzz_pcap's ASan build. RESTATED over pcap's read SOURCE (porter a Theorem Labs lane ruling 2): cgif's harness writes a file sink (asink_syms tfib_K, lib/A/AE2k.v, not ported: fuzz_pcap's ASan image holds none of cgif's sink strings), pcap's harness reads a memory stream, so the driver invariant FINV is stated over pcap's source symbols pcap_KS (lib/A/Stdio/PSourceK.v) with the source vocabulary of lib/A/Stdio/PSource.v / PSourceMeta.v: donor AD1u.v:60-63 FINV = ameta_inv tfib_K /\ astdio_env tfib_K /\ ofl head 0 becomes asrc_meta_inv pcap_KS /\ asrc_stdio_env pcap_KS /\ ofl head 0 (the last two are PSource.v's asource_none pcap_KS, the conjunct the program contract lib/A/Prog/PcapEntry.v asks). The donor's image laws tfib_AIL (AD1u.v:34, asink_img_laws) become tfib_ASIL (asource_img_laws, PSourceMeta.v:77, the sink head SK passed explicitly); FINV_IVS lists pcap_KS's cells (the meta pointer pair, "rwa\0", "rb\0", the canary, threaded, need_locks, ofl lock and head) in place of cgif's (no path / trailer string). The two frame lemmas the donor takes from YE00.v (astdio_env_frame, ameta_ok_frame) are restated here for the source record (asrc_stdio_env_frame, asrc_meta_ok_frame), bodies identical up to the field names, and meta_ptr_of_AR is PSourceMeta.v's asrc_meta_ptr_of_AR with the law read off B's constant table. The sink head is the Section's SK; the class pcap_head ties it to pcap's measured ofl_head 0x652308 (instantiated by reflexivity at SK := PcapSinkHeads.asan_sink_head). rule 24: no function proved anew; the image end is pcap_img_end (Reusable/PcapImgEnd.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YP0m YP09 YI04 YI00 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0p.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YCbq YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AD1y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* The source record this driver reads (porter ruling 2: FINV over pcap's SOURCE). *)
(* The two frame lemmas of the source vocabulary: donor YE00.v astdio_env_frame / ameta_ok_frame with ak_ -> as_
   and the source's two string cells ("rb\0", "rwa\0", PSource.v:222-230) in place of cgif's four. *)
(* The sink head the driver states against is pcap's measured ofl_head (PSourceK.v pcap_KS_head = 0x652308; the
   ASan image's head PcapSinkHeads.asan_sink_head, checked against the code by lib/A/PcapSinkHeadCheck.v). A class
   in the form of lib/A/ACeh.v's ro_tfa_below_ofl, so the lemmas keep the donor's explicit arguments; the driver's
   top instantiates it at SK := asan_sink_head by reflexivity. *)
Class pcap_head {SK : YI16.sink_head} : Prop := pcap_head_eq : @YI16.sk_ofl_head SK = 0x652308.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {PH : pcap_head}.
Section e.
Variable B : asyms.
Hypothesis HB : PcapSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Local Notation segs := tfibsegs.
Lemma owned_off : forall lo hi a, forallb (ext_avoids lo hi) Tfib_owned_static = true -> lo <= a < hi ->
~ Exists (in_zr a) (as_owned_static B).
Proof. intros lo hi a Hc Ha. rewrite (ts_owned B HB). exact (ext_avoids_sound lo hi _ a Hc Ha). Qed.
(* PSourceMeta.v:132 asrc_meta_ptr_of_AR (= donor YE01.v:139 ameta_ptr_of_AR) with the law asil_meta_ptr read off
   B's constant table directly, so the FINV lemmas below do not depend on the sink head. *)
(* donor AD1u.v:34 tfib_AIL : asink_img_laws segs B tfib_K, clause for clause over the source record. *)
Definition finv_loc (T : list (Z * Z)) : Prop :=
forall f, In (f, AMF_BLOCK) T -> in_app f AMF_BLOCK /\ (forall a, f <= a < f + AMF_BLOCK -> ~ in_img segs a).
(* donor AD1u.v:60-63: the driver's frame invariant, over the source (porter ruling 2). The last two conjuncts are
   asource_none segs KS (PSource.v:314). *)
Definition FINV (T : list (Z * Z)) (H : word -> bool) (mem : word -> option byte) : Prop :=
amf_gi segs link_amf T (mrestrict H mem) /\ amf_env segs link_amf (mrestrict H mem) /\
val_mem segs (mrestrict H mem) LinkEntryA.LA_NUL 1 0 /\ finv_loc T.
Lemma FINV_loc : forall T H mem, FINV T H mem -> finv_loc T.
Proof. intros T H mem (_ & _ & _ & HL). exact HL. Qed.
Definition in_kept (T : list (Z * Z)) (a : Z) : Prop := exists f, In (f, AMF_BLOCK) T /\ f <= a < f + AMF_BLOCK.
Lemma in_kept_nil : forall a, ~ in_kept [] a.
Proof. intros a (f & [] & _). Qed.
Lemma finv_kept_place : forall T a, finv_loc T -> in_kept T a -> 4096 <= a < ASAN_CEIL /\ ~ in_img segs a.
Proof.
intros T a HL (f & Hin & Hfa). destruct (HL f Hin) as (Happ & Hni).
split; [exact (app_addr_below_ceil a (in_app_addr f AMF_BLOCK a Happ Hfa)) | exact (Hni a Hfa)].
Qed.
Definition finv_img (a : Z) : Prop := amf_head_addr link_amf a \/ amf_env_addr link_amf a \/ a = LinkEntryA.LA_NUL.
Definition FINV_IVS : list (Z * Z) :=
[(0x62fec0, 0x62fec8); (0x6312e0, 0x6312e8); (0x652308, 0x652310); (0x651ea1, 0x651ea2);
(0x651ea3, 0x651ea4); (0x652300, 0x652304); (0x62fe6c, 0x62fe6d)].
Lemma link_amf_vals : amf_sink_addr link_amf = 0x62fec0 /\ amf_say_addr link_amf = 0x6312e0 /\ amf_ofl_lock link_amf = 0x652300 /\
amf_threaded link_amf = 0x651ea1 /\ amf_need_locks link_amf = 0x651ea3.
Proof. repeat split; reflexivity. Qed.
Lemma LA_NUL_val : LinkEntryA.LA_NUL = 0x62fe6c.
Proof. reflexivity. Qed.
Lemma finv_img_ivs : forall a, finv_img a -> exists lo hi, In (lo, hi) FINV_IVS /\ lo <= a < hi.
Proof.
intros a Ha. pose proof link_amf_vals as (V1 & V2 & V3 & V4 & V5). pose proof LA_NUL_val as V6.
unfold finv_img, amf_head_addr, amf_env_addr, amf_ofl_head in Ha. rewrite V1, V2, V3, V4, V5, V6 in Ha. unfold FINV_IVS.
destruct Ha as [[Ha|[Ha|Ha]]|[[Ha|[Ha|Ha]]|Ha]];
[ exists 0x62fec0, 0x62fec8 | exists 0x6312e0, 0x6312e8 | exists 0x652308, 0x652310 | exists 0x651ea1, 0x651ea2
| exists 0x651ea3, 0x651ea4 | exists 0x652300, 0x652304 | exists 0x62fe6c, 0x62fe6d ];
(split; [cbn; tauto | lia]).
Qed.
Definition ivs_avoid (lo hi : Z) : bool := forallb (fun iv => (hi <=? fst iv) || (snd iv <=? lo))%bool FINV_IVS.
Lemma ivs_avoid_sound : forall lo hi a, ivs_avoid lo hi = true -> lo <= a < hi -> ~ finv_img a.
Proof.
intros lo hi a Hc Ha Hf. destruct (finv_img_ivs a Hf) as (l & h & Hin & Hlh).
pose proof (proj1 (forallb_forall _ _) Hc (l, h) Hin) as X. cbn [fst snd] in X.
apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
Qed.
Lemma ivs_avoid_sub : forall lo hi lo' hi', ivs_avoid lo hi = true -> lo <= lo' -> hi' <= hi -> ivs_avoid lo' hi' = true.
Proof.
intros lo hi lo' hi' Hc H1 H2. unfold ivs_avoid in *. apply forallb_forall. intros iv Hiv.
pose proof (proj1 (forallb_forall _ _) Hc iv Hiv) as X. apply orb_prop in X as [X|X]; apply Z.leb_le in X; apply orb_true_intro; [left | right]; apply Z.leb_le; lia.
Qed.
Lemma FINV_IVS_img : forallb (fun iv => (0x10000 <=? fst iv) && (snd iv <=? pcap_img_end))%bool FINV_IVS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma finv_img_range : forall a, finv_img a -> 0x10000 <= a < pcap_img_end.
Proof.
intros a Hf. destruct (finv_img_ivs a Hf) as (l & h & Hin & Hlh).
pose proof (proj1 (forallb_forall _ _) FINV_IVS_img (l, h) Hin) as X. cbn [fst snd] in X. apply andb_prop in X as [X1 X2].
apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.
Lemma finv_img_img : forall a, finv_img a -> in_img segs a.
Proof. intros a Ha. apply in_img_hull. pose proof (finv_img_range a Ha) as R. unfold pcap_img_end, YImgTop.IMG_TOP in R. exact R. Qed.
Lemma FINV_IVS_unowned : forallb (fun iv => forallb (ext_avoids (fst iv) (snd iv)) Tfib_owned_static) FINV_IVS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma finv_img_not_owned : forall a, finv_img a -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros a Ha. destruct (finv_img_ivs a Ha) as (l & h & Hin & Hlh).
pose proof (proj1 (forallb_forall _ _) FINV_IVS_unowned (l, h) Hin) as X. cbn [fst snd] in X. exact (owned_off l h a X Hlh).
Qed.
Lemma FINV_IVS_drvw : forallb (fun d => ivs_avoid (fst d) (snd d)) DRV_IVS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma finv_img_not_drvw : forall a, finv_img a -> DRVW a = true -> False.
Proof.
intros a Ha Hw. unfold DRVW in Hw. apply existsb_exists in Hw as (d & Hd & Hb). apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (proj1 (forallb_forall _ _) FINV_IVS_drvw d Hd) as X. exact (ivs_avoid_sound (fst d) (snd d) a X ltac:(lia) Ha).
Qed.
Lemma FINV_IVS_errno : ivs_avoid TFIB_ERRNO (TFIB_ERRNO + 4) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma finv_img_not_errno : forall a, finv_img a -> ~ (as_errno B <= a < as_errno B + 4).
Proof. intros a Ha He. rewrite (ts_errno B HB) in He. exact (ivs_avoid_sound _ _ a FINV_IVS_errno He Ha). Qed.
Lemma finv_frame : forall {T : list (Z * Z)} H H' (mem mem' : word -> option byte),
(forall a, finv_img a \/ in_kept T a -> mbyte segs (mrestrict H' mem') a = mbyte segs (mrestrict H mem) a) ->
FINV T H mem -> FINV T H' mem'.
Proof.
intros T H H' mem mem' Hfr (HG & Henv & Hnul & HL). split; [|split; [|split]].
- apply (amf_gi_frame segs link_amf (mrestrict H mem) (mrestrict H' mem') T); [| |exact HG].
+ intros a Ha. apply Hfr. left. left. exact Ha.
+ intros f x Hin Hx. apply Hfr. right. exists f. split; [exact Hin | unfold AMF_ZEROED, AMF_BLOCK in *; lia].
- apply (amf_env_frame segs link_amf (mrestrict H mem) (mrestrict H' mem')); [|exact Henv].
intros a Ha. apply Hfr. left. right. left. exact Ha.
- eapply val_mem_frame; [|exact Hnul]. intros x Hx. apply Hfr. left. right. right. rewrite LA_NUL_val in Hx |- *. lia.
- exact HL.
Qed.
Lemma finv_aview : forall {T : list (Z * Z)} H H' (mem mem' : word -> option byte),
(forall a, finv_img a \/ in_kept T a -> aview segs H' mem' a = aview segs H mem a) ->
FINV T H mem -> FINV T H' mem'.
Proof. intros T H H' mem mem' Hfr HF. apply (finv_frame H H' mem mem'); [|exact HF]. intros a Ha. apply mbyte_of_aview. exact (Hfr a Ha). Qed.
Lemma finv_stretch : forall {T : list (Z * Z)} ly S W mem0 md (H : word -> bool) E rs (m m' : word -> option byte) usp,
AR segs B ly S W mem0 md ->
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb drv_win_ok rs = true -> bv_unsigned (ew E 0) = usp ->
ly_stk_lo ly <= usp - 65536 -> usp <= ly_stk_hi ly -> sp_window_lo <= usp ->
FINV T H m -> FINV T H m'.
Proof.
intros T ly S W mem0 md H E rs m m' usp HAR HF Hok E0 Hlo Hhi Husp HFI.
pose proof (lo_stk_ceil _ (am_layout _ _ _ _ (proj1 HAR))) as SC. pose proof (FINV_loc T H m HFI) as HL.
apply (finv_frame H H m m'); [|exact HFI].
intros a Ha. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. intros Hw.
apply (in_wrange_drv E rs) in Hw; [|exact Hok]. rewrite E0 in Hw.
assert (Hr : 0 <= a < 2 ^ 64).
{ destruct Ha as [Ha|Ha]; [pose proof (finv_img_range a Ha); unfold pcap_img_end, YImgTop.IMG_TOP in *; lia|].
destruct (finv_kept_place T a HL Ha) as [Hc _]. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)). lia. }
rewrite u64_lit in Hw by exact Hr.
destruct Ha as [Ha|Ha].
- pose proof (finv_img_range a Ha). destruct Hw as [Hw|Hw]; [unfold sp_window_lo, pcap_img_end, YImgTop.IMG_TOP in *; lia | exact (finv_img_not_drvw a Ha Hw)].
- destruct (finv_kept_place T a HL Ha) as [Hc Hi]. destruct Hw as [Hw|Hw]; [lia|].
apply Hi. apply in_img_rw. pose proof (DRVW_lo a Hw). lia.
Qed.
Lemma finv_acall_post : forall stk ly S W regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md',
AR segs B ly S W mem md ->
acall_post segs B stk ly S W regs mem md E ly' S' W' regs' mem' md' ->
(forall a, E a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(exists p n, In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n)) ->
ly_stk_lo ly <= spZ regs - stk -> spZ regs <= ly_stk_hi ly -> 2 ^ 24 <= spZ regs - stk ->
FINV [] (w_H W) mem -> FINV [] (w_H W') mem'.
Proof.
intros stk ly S W regs mem md E ly' S' W' regs' mem' md' HAR HP HE Hlo Hhi H24 HFI.
destruct HP as (HAR' & Hle & Hwle & Hregs & Hio & Hfr & Hpres).
apply (finv_aview (w_H W) (w_H W') mem mem'); [|exact HFI].
intros a [Ha|Ha]; [|exfalso; exact (in_kept_nil a Ha)].
pose proof (finv_img_range a Ha) as R. pose proof (finv_img_img a Ha) as Hi. pose proof (finv_img_not_owned a Ha) as Hns.
apply Hfr; [unfold pcap_img_end, YImgTop.IMG_TOP in R; lia | | | |].
+ intros Ho. exact (Hns (proj1 (al_owned_image _ _ ARL ly S W mem md a HAR Hi) Ho)).
+ intros Ho. exact (Hns (proj1 (al_owned_image _ _ ARL ly' S' W' mem' md' a HAR' Hi) Ho)).
+ unfold ascratch. intros [Hsc | Her]; [unfold pcap_img_end, YImgTop.IMG_TOP in R; lia | exact (finv_img_not_errno a Ha Her)].
+ intros Ea. destruct (HE a Ea) as [(p & n & Hin & Hpa) | (p & n & Hin & Hpa)].
* exact (proj2 (al_client_img _ _ ARL ly S W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa))))) Hi).
* exact (proj2 (al_client_img _ _ ARL ly' S' W' mem' md' a HAR' (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa))))) Hi).
Qed.
Lemma finv_off : forall {T : list (Z * Z)} ly S W mem md (mem' : word -> option byte) (X1 X2 : Z -> Prop),
AR segs B ly S W mem md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ X1 a -> ~ X2 a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, finv_img a \/ in_kept T a -> ~ X1 a /\ ~ X2 a) ->
FINV T (w_H W) mem -> FINV T (w_H W) mem'.
Proof.
intros T ly S W mem md mem' X1 X2 HAR Hfr HX HF. apply (finv_aview (w_H W) (w_H W) mem mem'); [|exact HF].
intros a Ha. destruct (HX a Ha) as [H1 H2]. apply Hfr; [|exact H1|exact H2].
destruct Ha as [Ha|Ha]; [pose proof (finv_img_range a Ha); unfold pcap_img_end, YImgTop.IMG_TOP in *; lia|].
destruct (finv_kept_place T a (FINV_loc T _ _ HF) Ha) as [Hc _]. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)). lia.
Qed.
Lemma finv_avoids_block : forall ly S W mem md p n a,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
finv_img a \/ in_kept [] a -> ~ (p <= a < p + req_size n).
Proof.
intros ly S W mem md p n a HAR Hin Ha Hpa. destruct Ha as [Ha|Ha]; [|exact (in_kept_nil a Ha)].
exact (proj2 (al_client_img _ _ ARL ly S W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa))))) (finv_img_img a Ha)).
Qed.
Lemma finv_avoids_stack : forall {T : list (Z * Z)} ly S W mem md lo hi a,
AR segs B ly S W mem md -> finv_loc T -> ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly -> 2 ^ 24 <= lo ->
finv_img a \/ in_kept T a -> ~ (lo <= a < hi).
Proof.
intros T ly S W mem md lo hi a HAR HL Hlo Hhi H24 Ha Hr.
pose proof (lo_stk_ceil _ (am_layout _ _ _ _ (proj1 HAR))) as SC.
destruct Ha as [Ha|Ha].
- pose proof (finv_img_range a Ha). unfold pcap_img_end, YImgTop.IMG_TOP in *. lia.
- destruct (finv_kept_place T a HL Ha) as [Hc _]. lia.
Qed.
Lemma finv_avoids_img : forall {T : list (Z * Z)} ly S W mem md lo hi a,
AR segs B ly S W mem md -> finv_loc T -> (forall x, lo <= x < hi -> in_img segs x) -> ivs_avoid lo hi = true ->
finv_img a \/ in_kept T a -> ~ (lo <= a < hi).
Proof.
intros T ly S W mem md lo hi a HAR HL Himg Hc Ha Hr. destruct Ha as [Ha|Ha].
- exact (ivs_avoid_sound lo hi a Hc Hr Ha).
- destruct (finv_kept_place T a HL Ha) as [_ Hi]. exact (Hi (Himg a Hr)).
Qed.
Lemma finv_img_write : forall ly S W mem0 md (H : word -> bool) (m m' : word -> option byte) lo hi,
AR segs B ly S W mem0 md ->
(forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> m' x = m x) ->
(forall x, lo <= x < hi -> in_img segs x) -> ivs_avoid lo hi = true ->
FINV [] H m -> FINV [] H m'.
Proof.
intros ly S W mem0 md H m m' lo hi HAR Hout Himg Hc HF. apply (finv_frame H H m m'); [|exact HF].
intros a [Ha|Ha]; [|exfalso; exact (in_kept_nil a Ha)].
pose proof (finv_img_range a Ha) as R. pose proof (ivs_avoid_sound lo hi a Hc) as Hna0.
assert (Hna : ~ (lo <= a < hi)) by (intros X; exact (Hna0 X Ha)).
unfold mbyte, mrestrict. rewrite (Hout (Z_to_bv 64 a)) by (rewrite u64_lit by (unfold pcap_img_end, YImgTop.IMG_TOP in R; lia); lia). reflexivity.
Qed.
End e.
End b.
