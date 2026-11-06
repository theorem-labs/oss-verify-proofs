From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1u.v (origin/ossv/recipes c8557374ad2e), with its module paths changed, names TfibSyms -> PcapSyms and its addresses moved to libreac/fuzz_pcap's ASan build. RESTATED over pcap's read SOURCE (porter ruling 2): cgif's harness writes a file sink (asink_syms tfib_K, lib/A/AE2k.v, not ported: fuzz_pcap's ASan image holds none of cgif's sink strings), pcap's harness reads a memory stream, so the driver invariant FINV is stated over pcap's source symbols pcap_KS (lib/A/Stdio/PSourceK.v) with the source vocabulary of lib/A/Stdio/PSource.v / PSourceMeta.v: donor AD1u.v:60-63 FINV = ameta_inv tfib_K /\ astdio_env tfib_K /\ ofl head 0 becomes asrc_meta_inv pcap_KS /\ asrc_stdio_env pcap_KS /\ ofl head 0 (the last two are PSource.v's asource_none pcap_KS, the conjunct the program contract lib/A/Prog/PcapEntry.v asks). The donor's image laws tfib_AIL (AD1u.v:34, asink_img_laws) become tfib_ASIL (asource_img_laws, PSourceMeta.v:77, the sink head SK passed explicitly); FINV_IVS lists pcap_KS's cells (the meta pointer pair, "rwa\0", "rb\0", the canary, threaded, need_locks, ofl lock and head) in place of cgif's (no path / trailer string). The two frame lemmas the donor takes from YE00.v (astdio_env_frame, ameta_ok_frame) are restated here for the source record (asrc_stdio_env_frame, asrc_meta_ok_frame), bodies identical up to the field names, and meta_ptr_of_AR is PSourceMeta.v's asrc_meta_ptr_of_AR with the law read off B's constant table. The sink head is the Section's SK; the class pcap_head ties it to pcap's measured ofl_head 0x5f4f88 (instantiated by reflexivity at SK := PcapSinkHeads.asan_sink_head). rule 24: no function proved anew; the image end is pcap_img_end (Reusable/PcapImgEnd.v). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.libreac.fuzz_pcap.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YP0m YP09 YI04 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0p.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AF0m AD1y.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* The source record this driver reads (porter ruling 2: FINV over pcap's SOURCE). *)
Local Notation KS := pcap_KS.
Ltac kcst := unfold PCAP_THREADED, PCAP_NEED_LOCKS, PCAP_OFL_LOCK, PCAP_MODE, PCAP_RWA, PCAP_CANARY, PCAP_CAN_GOT,
PCAP_META_PTR, PCAP_META_MEM, PCAP_MREAD, PCAP_MWRITE, PCAP_MSEEK, PCAP_MCLOSE in *.
(* The two frame lemmas of the source vocabulary: donor YE00.v astdio_env_frame / ameta_ok_frame with ak_ -> as_
   and the source's two string cells ("rb\0", "rwa\0", PSource.v:222-230) in place of cgif's four. *)
Lemma asrc_stdio_env_frame : forall segs (m m' : word -> option byte),
(forall a, asrc_env_addr KS a -> mbyte segs m' a = mbyte segs m a) -> asrc_stdio_env segs KS m -> asrc_stdio_env segs KS m'.
Proof.
intros segs m m' Hfr (H1 & H2 & H3 & H4 & H5 & (cv & Hcv & H8)). unfold asrc_stdio_env.
split; [eapply val_mem_frame; [|exact H1]; intros x Hx; apply Hfr; unfold asrc_env_addr; cbn in Hx |- *; lia|].
split; [eapply val_mem_frame; [|exact H2]; intros x Hx; apply Hfr; unfold asrc_env_addr; cbn in Hx |- *; lia|].
split; [eapply val_mem_frame; [|exact H3]; intros x Hx; apply Hfr; unfold asrc_env_addr; cbn in Hx |- *; lia|].
split; [eapply garr8_frame; [exact H4|]; intros x Hx; apply Hfr; unfold asrc_env_addr; cbn in Hx |- *; lia|].
split; [eapply garr8_frame; [exact H5|]; intros x Hx; apply Hfr; unfold asrc_env_addr; cbn in Hx |- *; lia|].
exists cv. split; [exact Hcv|]. eapply val_mem_frame; [|exact H8]; intros x Hx; apply Hfr; unfold asrc_env_addr; cbn in Hx |- *; lia.
Qed.
Lemma asrc_meta_ok_frame : forall segs (m m' : word -> option byte) M,
(forall a, (as_meta_ptr KS <= a < as_meta_ptr KS + 8) \/ (as_meta_mem KS <= a < as_meta_mem KS + 8) \/ (M <= a < M + AMETA_SIZE) ->
mbyte segs m' a = mbyte segs m a) ->
asrc_meta_ok segs KS m M -> asrc_meta_ok segs KS m' M.
Proof.
intros segs m m' M Hfr (H1 & H2 & H3 & H4 & H5 & HZ). unfold asrc_meta_ok.
split; [eapply val_mem_frame; [|exact H1]; intros x Hx; apply Hfr; cbn in Hx |- *; lia|].
split; [eapply val_mem_frame; [|exact H2]; intros x Hx; apply Hfr; cbn in Hx |- *; lia|].
split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
intros a Ha. rewrite Hfr by lia. exact (HZ a Ha).
Qed.
(* The sink head the driver states against is pcap's measured ofl_head (PSourceK.v pcap_KS_head = 0x5f4f88; the
   ASan image's head PcapSinkHeads.asan_sink_head, checked against the code by lib/A/PcapSinkHeadCheck.v). A class
   in the form of lib/A/ACeh.v's ro_tfa_below_ofl, so the lemmas keep the donor's explicit arguments; the driver's
   top instantiates it at SK := asan_sink_head by reflexivity. *)
Class pcap_head {SK : YI16.sink_head} : Prop := pcap_head_eq : @YI16.sk_ofl_head SK = (symaddr Symbols.Asan.s_ofl_head).
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
Lemma const_abs_in : forall ly c, In c Tfib_const_abs -> In c (as_const B ly).
Proof. intros ly c Hc. rewrite (ts_const B HB). unfold Tfib_const. apply in_app_iff. right. apply in_app_iff. left. exact Hc. Qed.
Ltac in_list := cbn; repeat (first [left; reflexivity | right]).
(* PSourceMeta.v:132 asrc_meta_ptr_of_AR (= donor YE01.v:139 ameta_ptr_of_AR) with the law asil_meta_ptr read off
   B's constant table directly, so the FINV lemmas below do not depend on the sink head. *)
Lemma meta_ptr_of_AR : forall ly S W mem md,
AR segs B ly S W mem md -> val_mem segs (mrestrict (w_H W) mem) (as_meta_ptr KS) 8 (as_meta_mem KS).
Proof.
intros ly S W mem md HAR k Hk.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC.
assert (Hin : In (z8 (ANum (as_meta_ptr KS)) (as_meta_mem KS)) (as_const B ly)) by (apply const_abs_in; in_list).
pose proof (proj1 (Forall_forall _ _) HC _ Hin) as Hc. unfold z8, c8, cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
specialize (Hc k Hk). unfold aview in Hc.
destruct (mbyte segs (mrestrict (w_H W) mem) (as_meta_ptr KS + Z.of_nat k)) as [b|] eqn:E; [|discriminate Hc]. cbn in Hc.
injection Hc as Hc. f_equal. apply bv_eq. rewrite Hc, Z_to_bv_unsigned. symmetry.
change (YO0f.le_byte (as_meta_mem KS) 8 k) with (YG0f.le_byte (as_meta_mem KS) 8 k). unfold YG0f.le_byte.
unfold bv_wrap. change (bv_modulus 8) with 256%Z. apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.
Lemma head_eq : YCbq.AOFL_HEAD = as_ofl_head KS.
Proof. unfold YCbq.AOFL_HEAD. rewrite pcap_head_eq. reflexivity. Qed.
(* donor AD1u.v:34 tfib_AIL : asink_img_laws segs B tfib_K, clause for clause over the source record. *)
Lemma tfib_ASIL : asource_img_laws SK segs B KS.
Proof.
pose proof (ts_errno B HB) as EE. unfold TFIB_ERRNO in EE.
pose proof head_eq as HE. unfold as_ofl_head in HE. cbn -[Z.add] in HE. kcst.
constructor.
- rewrite head_eq. reflexivity.
- intros a Ha. unfold asrc_env_addr in Ha. cbn -[Z.add Z.lt Z.le] in Ha. kcst.
split; [apply in_img_hull; unfold pcap_img_end, YImgTop.IMG_TOP; lia|]. split; [| rewrite EE; lia].
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
+ apply (owned_off PCAP_THREADED (PCAP_THREADED + 1)); [vm_compute; reflexivity | kcst; lia].
+ apply (owned_off PCAP_NEED_LOCKS (PCAP_NEED_LOCKS + 1)); [vm_compute; reflexivity | kcst; lia].
+ apply (owned_off PCAP_OFL_LOCK (PCAP_OFL_LOCK + 16)); [vm_compute; reflexivity | kcst; lia].
+ apply (owned_off PCAP_MODE (PCAP_MODE + 3)); [vm_compute; reflexivity | kcst; lia].
+ apply (owned_off PCAP_RWA (PCAP_RWA + 4)); [vm_compute; reflexivity | kcst; lia].
+ apply (owned_off PCAP_CANARY (PCAP_CANARY + 8)); [vm_compute; reflexivity | kcst; lia].
- intros a Ha. rewrite HE. unfold asrc_env_addr in Ha. cbn -[Z.add Z.lt Z.le] in Ha. kcst. lia.
- intros a Ha. rewrite HE. cbn -[Z.add Z.lt Z.le] in Ha. kcst. lia.
- intros ly. apply const_abs_in. in_list.
- intros a Ha. rewrite HE. cbn -[Z.add Z.lt Z.le] in Ha. kcst.
split; [apply in_img_hull; unfold pcap_img_end, YImgTop.IMG_TOP; lia|].
split; [apply (owned_off PCAP_META_MEM (PCAP_META_MEM + 8)); [vm_compute; reflexivity | kcst; lia]|]. rewrite EE. lia.
- intros ly. apply const_abs_in. in_list.
- intros a Ha. rewrite EE in Ha. apply in_img_hull. unfold pcap_img_end, YImgTop.IMG_TOP. lia.
- intros ly c Hc. cbn in Hc.
destruct Hc as [<-|[<-|[]]]; apply const_abs_in; in_list.
Qed.
(* donor AD1u.v:60-63: the driver's frame invariant, over the source (porter ruling 2). The last two conjuncts are
   asource_none segs KS (PSource.v:314). *)
Definition FINV (ly : alayout) (H : word -> bool) (mem : word -> option byte) : Prop :=
(exists M, asrc_meta_inv segs KS ly (mrestrict H mem) M) /\
asrc_stdio_env segs KS (mrestrict H mem) /\
val_mem segs (mrestrict H mem) (as_ofl_head KS) 8 0.
Lemma FINV_source_none : forall ly H mem, FINV ly H mem -> asource_none segs KS (mrestrict H mem).
Proof. intros ly H mem (_ & Henv & Hhead). exact (conj Henv Hhead). Qed.
Lemma FINV_of_source_none : forall ly H mem M, asrc_meta_inv segs KS ly (mrestrict H mem) M ->
asource_none segs KS (mrestrict H mem) -> FINV ly H mem.
Proof. intros ly H mem M HM (Henv & Hhead). split; [exists M; exact HM | exact (conj Henv Hhead)]. Qed.
Definition finv_img (a : Z) : Prop :=
(as_meta_ptr KS <= a < as_meta_ptr KS + 16) \/ asrc_env_addr KS a \/ (as_ofl_head KS <= a < as_ofl_head KS + 8).
Definition FINV_IVS : list (Z * Z) :=
[(PCAP_META_PTR, PCAP_META_PTR + 16); (PCAP_RWA, PCAP_RWA + 4); (PCAP_MODE, PCAP_MODE + 3);
(PCAP_CANARY, PCAP_CANARY + 8); (PCAP_THREADED, PCAP_THREADED + 1); (PCAP_NEED_LOCKS, PCAP_NEED_LOCKS + 1);
(PCAP_OFL_LOCK, PCAP_OFL_LOCK + 16)].
Lemma finv_img_ivs : forall a, finv_img a -> exists lo hi, In (lo, hi) FINV_IVS /\ lo <= a < hi.
Proof.
intros a Ha. unfold finv_img, asrc_env_addr, as_ofl_head in Ha. cbn -[Z.add Z.lt Z.le] in Ha. unfold FINV_IVS.
destruct Ha as [Ha|[[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]|Ha]];
[ exists PCAP_META_PTR, (PCAP_META_PTR + 16) | exists PCAP_THREADED, (PCAP_THREADED + 1)
| exists PCAP_NEED_LOCKS, (PCAP_NEED_LOCKS + 1) | exists PCAP_OFL_LOCK, (PCAP_OFL_LOCK + 16)
| exists PCAP_MODE, (PCAP_MODE + 3) | exists PCAP_RWA, (PCAP_RWA + 4) | exists PCAP_CANARY, (PCAP_CANARY + 8)
| exists PCAP_OFL_LOCK, (PCAP_OFL_LOCK + 16) ];
(split; [cbn; tauto | kcst; lia]).
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
Lemma FINV_IVS_unowned : forallb (fun iv => forallb (ext_avoids (fst iv) (snd iv)) Tfib_owned_static) (tl FINV_IVS ++ [(PCAP_META_MEM, PCAP_META_MEM + 8)]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma finv_img_not_owned : forall a, finv_img a -> ~ (PCAP_META_PTR <= a < PCAP_META_PTR + 8) -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros a Ha Hnp. destruct (finv_img_ivs a Ha) as (l & h & Hin & Hlh).
assert (CASE : In (l, h) (tl FINV_IVS ++ [(PCAP_META_MEM, PCAP_META_MEM + 8)]) \/ (PCAP_META_MEM <= a < PCAP_META_MEM + 8)).
{ cbn [FINV_IVS tl] in Hin |- *. destruct Hin as [E | Hin].
- right. injection E as <- <-. unfold PCAP_META_MEM, PCAP_META_PTR in *. lia.
- left. apply in_app_iff. left. exact Hin. }
destruct CASE as [Hin' | Hm].
- pose proof (proj1 (forallb_forall _ _) FINV_IVS_unowned (l, h) Hin') as X. cbn [fst snd] in X. exact (owned_off l h a X Hlh).
- assert (Hin' : In (PCAP_META_MEM, PCAP_META_MEM + 8) (tl FINV_IVS ++ [(PCAP_META_MEM, PCAP_META_MEM + 8)])) by (apply in_app_iff; right; left; reflexivity).
pose proof (proj1 (forallb_forall _ _) FINV_IVS_unowned _ Hin') as X. cbn [fst snd] in X. exact (owned_off _ _ a X Hm).
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
Lemma finv_frame : forall ly H H' (mem mem' : word -> option byte),
(forall a, finv_img a \/ Exists (in_zr a) (ly_extra ly) -> mbyte segs (mrestrict H' mem') a = mbyte segs (mrestrict H mem) a) ->
FINV ly H mem -> FINV ly H' mem'.
Proof.
intros ly H H' mem mem' Hfr ((M & HX & Himg & Hok) & Henv & Hhead). split; [|split].
- exists M. split; [exact HX|]. split; [exact Himg|].
apply (asrc_meta_ok_frame segs (mrestrict H mem)); [|exact Hok].
intros a Ha. apply Hfr. cbn -[Z.add Z.lt Z.le] in Ha. destruct Ha as [Ha|[Ha|Ha]].
+ left. unfold finv_img. left. cbn -[Z.add Z.lt Z.le]. lia.
+ left. unfold finv_img. left. cbn -[Z.add Z.lt Z.le] in Ha |- *. kcst. lia.
+ right. apply Exists_exists. exists (M, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
- apply (asrc_stdio_env_frame segs (mrestrict H mem)); [|exact Henv]. intros a Ha. apply Hfr. left. right. left. exact Ha.
- eapply val_mem_frame; [|exact Hhead]. intros a Ha. apply Hfr. left. right. right. cbn in Ha. exact Ha.
Qed.
Lemma finv_aview : forall ly H H' (mem mem' : word -> option byte),
(forall a, finv_img a \/ Exists (in_zr a) (ly_extra ly) -> aview segs H' mem' a = aview segs H mem a) ->
FINV ly H mem -> FINV ly H' mem'.
Proof. intros ly H H' mem mem' Hfr HF. apply (finv_frame ly H H' mem mem'); [|exact HF]. intros a Ha. apply mbyte_of_aview. exact (Hfr a Ha). Qed.
Lemma finv_lyle : forall n ly ly' H mem, layout_le n ly ly' -> FINV ly H mem -> FINV ly' H mem.
Proof.
intros n ly ly' H mem Hle ((M & HX & Himg & Hok) & Henv & Hhead).
pose proof Hle as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
split; [| exact (conj Henv Hhead)]. exists M. split; [rewrite Eextra; exact HX | exact (conj Himg Hok)].
Qed.
Lemma extra_place : forall ly S W mem md a, AR segs B ly S W mem md -> Exists (in_zr a) (ly_extra ly) ->
~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_img segs a /\ ~ aowned B ly S a /\
(forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n)).
Proof.
intros ly S W mem md a HAR HX. destruct (AR_extra_law_ok segs B ly S W mem md a HAR HX) as (Ho & Hb & _ & Hs & Hi & _). tauto.
Qed.
Lemma finv_stretch : forall ly S W mem0 md (H : word -> bool) E rs (m m' : word -> option byte) usp,
AR segs B ly S W mem0 md ->
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb drv_win_ok rs = true -> bv_unsigned (ew E 0) = usp ->
ly_stk_lo ly <= usp - 65536 -> usp <= ly_stk_hi ly -> sp_window_lo <= usp ->
FINV ly H m -> FINV ly H m'.
Proof.
intros ly S W mem0 md H E rs m m' usp HAR HF Hok E0 Hlo Hhi Husp HFI. apply (finv_frame ly H H m m'); [|exact HFI].
intros a Ha. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. intros Hw.
apply (in_wrange_drv E rs) in Hw; [|exact Hok]. rewrite E0 in Hw.
assert (Hr : 0 <= a < 2 ^ 64).
{ destruct Ha as [Ha|Ha]; [pose proof (finv_img_range a Ha); unfold pcap_img_end, YImgTop.IMG_TOP in *; lia|].
destruct (AR_extra_law_ok segs B ly S W mem0 md a HAR Ha) as (_ & _ & _ & _ & _ & _ & Happ).
pose proof (app_addr_below_ceil a Happ). pose proof (proj1 (@YG0f.ASAN_CEIL_range _)). lia. }
rewrite u64_lit in Hw by exact Hr.
destruct Ha as [Ha|Ha].
- pose proof (finv_img_range a Ha). destruct Hw as [Hw|Hw]; [unfold sp_window_lo, pcap_img_end, YImgTop.IMG_TOP in *; lia | exact (finv_img_not_drvw a Ha Hw)].
- destruct (extra_place ly S W mem0 md a HAR Ha) as (Hs & Hi & _). destruct Hw as [Hw|Hw]; [lia|].
apply Hi. apply in_img_rw. pose proof (DRVW_lo a Hw). lia.
Qed.
Lemma finv_acall_post : forall stk ly S W regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md',
AR segs B ly S W mem md ->
acall_post segs B stk ly S W regs mem md E ly' S' W' regs' mem' md' ->
(forall a, E a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(exists p n, In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n)) ->
ly_stk_lo ly <= spZ regs - stk -> spZ regs <= ly_stk_hi ly -> 2 ^ 24 <= spZ regs - stk ->
FINV ly (w_H W) mem -> FINV ly' (w_H W') mem'.
Proof.
intros stk ly S W regs mem md E ly' S' W' regs' mem' md' HAR HP HE Hlo Hhi H24 ((M & HX & Himg & Hok) & Henv & Hhead).
destruct HP as (HAR' & Hle & Hwle & Hregs & Hio & Hfr & Hpres).
pose proof Hle as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Estklo & Estkhi & _ & _ & Eextra & _).
pose proof (ts_errno B HB) as EE. unfold TFIB_ERRNO in EE.
assert (HX' : In (M, AMETA_SIZE) (ly_extra ly')) by (rewrite Eextra; exact HX).
assert (FR : forall a, (finv_img a /\ ~ (PCAP_META_PTR <= a < PCAP_META_PTR + 8)) \/ Exists (in_zr a) (ly_extra ly) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
{ intros a Ha. destruct Ha as [[Ha Hnp] | Ha].
- pose proof (finv_img_range a Ha) as R. pose proof (finv_img_img a Ha) as Hi. pose proof (finv_img_not_owned a Ha Hnp) as Hns.
apply Hfr; [unfold pcap_img_end, YImgTop.IMG_TOP in R; lia | | | |].
+ intros Ho. exact (Hns (proj1 (al_owned_image _ _ ARL ly S W mem md a HAR Hi) Ho)).
+ intros Ho. exact (Hns (proj1 (al_owned_image _ _ ARL ly' S' W' mem' md' a HAR' Hi) Ho)).
+ unfold ascratch. intros [Hsc | Her]; [unfold pcap_img_end, YImgTop.IMG_TOP in R; lia | exact (finv_img_not_errno a Ha Her)].
+ intros Ea. destruct (HE a Ea) as [(p & n & Hin & Hpa) | (p & n & Hin & Hpa)].
* exact (proj2 (al_client_img _ _ ARL ly S W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa))))) Hi).
* exact (proj2 (al_client_img _ _ ARL ly' S' W' mem' md' a HAR' (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa))))) Hi).
- destruct (extra_place ly S W mem md a HAR Ha) as (Hs & Hi & Ho & Hb).
assert (Ha' : Exists (in_zr a) (ly_extra ly')) by (rewrite Eextra; exact Ha).
destruct (extra_place ly' S' W' mem' md' a HAR' Ha') as (_ & _ & Ho' & Hb').
destruct (AR_extra_law_ok segs B ly S W mem md a HAR Ha) as (_ & _ & _ & _ & _ & _ & Happ).
pose proof (app_addr_below_ceil a Happ). pose proof (proj1 (@YG0f.ASAN_CEIL_range _)).
apply Hfr; [lia | exact Ho | exact Ho' | |].
+ unfold ascratch. rewrite EE. intros [Hsc | Her]; [lia|]. apply Hi. apply in_img_hull. unfold pcap_img_end, YImgTop.IMG_TOP. lia.
+ intros Ea. destruct (HE a Ea) as [(p & n & Hin & Hpa) | (p & n & Hin & Hpa)]; [exact (Hb p n Hin Hpa) | exact (Hb' p n Hin Hpa)]. }
split; [|split].
- exists M. split; [exact HX'|]. split; [exact Himg|].
destruct Hok as (Hp & Hm & H0 & H47 & Hal & HZ). split; [exact (meta_ptr_of_AR ly' S' W' mem' md' HAR')|].
split.
+ eapply val_mem_frame; [|exact Hm]. intros x Hx. apply mbyte_of_aview. apply FR. left. cbn -[Z.add Z.lt Z.le] in Hx. unfold finv_img. cbn -[Z.add Z.lt Z.le]. kcst. lia.
+ split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
intros a Ha. rewrite <- (HZ a Ha). apply mbyte_of_aview. apply FR. right.
apply Exists_exists. exists (M, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
- apply (asrc_stdio_env_frame segs (mrestrict (w_H W) mem)); [|exact Henv].
intros a Ha. apply mbyte_of_aview. apply FR. left. split; [right; left; exact Ha|].
unfold asrc_env_addr in Ha. cbn -[Z.add Z.lt Z.le] in Ha. kcst. lia.
- eapply val_mem_frame; [|exact Hhead]. intros a Ha. apply mbyte_of_aview. apply FR. left. change (Z.of_nat 8) with 8 in Ha. unfold finv_img, as_ofl_head in *. cbn -[Z.add Z.lt Z.le] in Ha |- *. kcst. lia.
Qed.
Lemma finv_off : forall ly S W mem md (mem' : word -> option byte) (X1 X2 : Z -> Prop),
AR segs B ly S W mem md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ X1 a -> ~ X2 a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, finv_img a \/ Exists (in_zr a) (ly_extra ly) -> ~ X1 a /\ ~ X2 a) ->
FINV ly (w_H W) mem -> FINV ly (w_H W) mem'.
Proof.
intros ly S W mem md mem' X1 X2 HAR Hfr HX HF. apply (finv_aview ly (w_H W) (w_H W) mem mem'); [|exact HF].
intros a Ha. destruct (HX a Ha) as [H1 H2]. apply Hfr; [|exact H1|exact H2].
destruct Ha as [Ha|Ha]; [pose proof (finv_img_range a Ha); unfold pcap_img_end, YImgTop.IMG_TOP in *; lia|].
destruct (AR_extra_law_ok segs B ly S W mem md a HAR Ha) as (_ & _ & _ & _ & _ & _ & Happ).
pose proof (app_addr_below_ceil a Happ). pose proof (proj1 (@YG0f.ASAN_CEIL_range _)). lia.
Qed.
Lemma finv_avoids_block : forall ly S W mem md p n a,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
finv_img a \/ Exists (in_zr a) (ly_extra ly) -> ~ (p <= a < p + req_size n).
Proof.
intros ly S W mem md p n a HAR Hin Ha Hpa. destruct Ha as [Ha|Ha].
- exact (proj2 (al_client_img _ _ ARL ly S W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa))))) (finv_img_img a Ha)).
- destruct (extra_place ly S W mem md a HAR Ha) as (_ & _ & _ & Hb). exact (Hb p n Hin Hpa).
Qed.
Lemma finv_avoids_stack : forall ly S W mem md lo hi a,
AR segs B ly S W mem md -> ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly -> 2 ^ 24 <= lo ->
finv_img a \/ Exists (in_zr a) (ly_extra ly) -> ~ (lo <= a < hi).
Proof.
intros ly S W mem md lo hi a HAR Hlo Hhi H24 Ha Hr. destruct Ha as [Ha|Ha].
- pose proof (finv_img_range a Ha). unfold pcap_img_end, YImgTop.IMG_TOP in *. lia.
- destruct (extra_place ly S W mem md a HAR Ha) as (Hs & _). lia.
Qed.
Lemma finv_avoids_img : forall ly S W mem md lo hi a,
AR segs B ly S W mem md -> (forall x, lo <= x < hi -> in_img segs x) -> ivs_avoid lo hi = true ->
finv_img a \/ Exists (in_zr a) (ly_extra ly) -> ~ (lo <= a < hi).
Proof.
intros ly S W mem md lo hi a HAR Himg Hc Ha Hr. destruct Ha as [Ha|Ha].
- exact (ivs_avoid_sound lo hi a Hc Hr Ha).
- destruct (extra_place ly S W mem md a HAR Ha) as (_ & Hi & _). exact (Hi (Himg a Hr)).
Qed.
Lemma finv_fp_u64 : forall ly S W mem md a, AR segs B ly S W mem md ->
finv_img a \/ Exists (in_zr a) (ly_extra ly) -> 0 <= a < 2 ^ 64.
Proof.
intros ly S W mem md a HAR [Ha|Ha]; [pose proof (finv_img_range a Ha); unfold pcap_img_end, YImgTop.IMG_TOP in *; lia|].
destruct (AR_extra_law_ok segs B ly S W mem md a HAR Ha) as (_ & _ & _ & _ & _ & _ & Happ).
pose proof (app_addr_below_ceil a Happ). pose proof (proj1 (@YG0f.ASAN_CEIL_range _)). lia.
Qed.
Lemma finv_img_write : forall ly S W mem0 md (H : word -> bool) (m m' : word -> option byte) lo hi,
AR segs B ly S W mem0 md ->
(forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> m' x = m x) ->
(forall x, lo <= x < hi -> in_img segs x) -> ivs_avoid lo hi = true ->
FINV ly H m -> FINV ly H m'.
Proof.
intros ly S W mem0 md H m m' lo hi HAR Hout Himg Hc HF. apply (finv_frame ly H H m m'); [|exact HF].
intros a Ha. pose proof (finv_fp_u64 ly S W mem0 md a HAR Ha) as Hr.
pose proof (finv_avoids_img ly S W mem0 md lo hi a HAR Himg Hc Ha) as Hna.
unfold mbyte, mrestrict. rewrite (Hout (Z_to_bv 64 a)) by (rewrite u64_lit by exact Hr; lia). reflexivity.
Qed.
End e.
End b.
