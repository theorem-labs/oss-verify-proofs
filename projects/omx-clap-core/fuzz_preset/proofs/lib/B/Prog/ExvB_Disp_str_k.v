(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Rebound 2026-10-29 onto the old-pin kit of record (4f18c75d4900; base 2d66a982044b): fpre's new last
   conjunct raZ regs < alloc_ceiling; ex_ws_x is no longer Required (two of its journal-free helpers restated below, the
   other two are ExvB_Open_kt.v's exk_val_kept / exk_garr8_kept, cited). *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value, segment C1 DISP, the STRING ARM (lane ExvDisp, sub-lane ExvDispStr): the helpers of
   lib/B/Prog/ExvB_Disp_str.v. Proves nothing about the program on its own.
   - pure: ex_string's decoded string has no NUL byte (PjGrammar.decode_stop, restated as plain ex_value_m.v
     ex_string_rest's last conjunct; no plain lemma cited, no lib/Prog file Required), the tag of a tree node, the
     bytes of a NUL-terminated string read through aview (first_byte, equality from strcmp's answer);
   - the geometry of a cut state (EXV_PRE + EXB: the frame base s1, the cursor q, the stack need of ex_string and of
     the string runtime under ex_value's own need);
   - the cursor's bytes across a stretch or a call (prhex_cur), and EXV_RES at an exit;
   - journal-free helpers restated from lib/B/Prog/ex_ws_x.v (exw_region_nth, exw_field, skip_ws_x.v's), so this
     lane does not wait for ex_ws_x's rebind.
   Rule 24: proves no function (kind: segment lemma). Numerals: 0x1d0, 0x1d8, 0x23c, 0x240, 0xa7c (DERIVED:
   B 0x836fc, 0x83704, 0x83768, 0x8376c, 0x83fa8 minus ex_value's entry 0x8352c, the internal file neutral_dis.py on the rebuilt
   image); 288, 304, 319, 320, 176, 152 (LENGTH: ex_value's frame and its pi_frame, its 32-alignment slack, slot
   offsets); 8, 16, 24, 32, 36, 40, 55, 56 (LENGTH: struct ex / pj_value field offsets and widths); 4, 6 (WORD: the
   JStr tag, the largest tag); 2, 3, 4, 8, 9, 18, 19, 21, 24, 25, 26 (WORD: register numbers); 2 ^ 32, 2 ^ 44,
   2 ^ 46, 2 ^ 47, 2 ^ 63, 2 ^ 64, 4096 (DERIVED: address-space, shadow-band and width bounds). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YK06 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Open_kt ExvB_Disp_arms.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.
(* plain lia (YZ00's `lia` prunes hypotheses and fails on goals over record projections) *)
Ltac zl := Zify.zify; xlia zchecker.

(* ---- pcs (paj engine offsets from the listing base) ---- *)
Definition EXVS0 : Z := B_prog_sigma AS_ex_value - B_prog_val A_TEXT.
Lemma exvs_pc_eq : forall off, exv_pc off = B_prog_val A_TEXT + (EXVS0 + off).
Proof. intros off. unfold exv_pc, EXVS0. lia. Qed.
Definition EXVS_Bx : sv := SOff 25 0.
Definition EXVS_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition EXVS_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv.

(* ---- journal-free helpers, restated from lib/B/Prog/ex_ws_x.v :133-148 (skip_ws_x.v's, unchanged) ---- *)
Section h. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Lemma exvs_region_nth : forall E ss ms i r,
  st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok segs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok segs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma exvs_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem segs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok segs E m b od w e v Hck He Hv Hw).
Qed.
End h.

(* ---- pure ---- *)
(* ex_string's success: the rest, and the decoded string's bytes are not NUL (PjGrammar.decode_stop) *)
Lemma exvs_string_dec : forall y s r, fst (fst (PjGrammar.jr_string y [])) = Some (s, r) ->
  exists c, PjGrammar.scan y = Some c /\ r = skipn (S c) y /\ (c < length y)%nat /\ (length s <= c)%nat /\
    Forall (fun b => b <> 0) s.
Proof.
intros y s r H. unfold PjGrammar.jr_string in H.
destruct (PjGrammar.scan y) as [c|] eqn:Es; [|discriminate H].
exists c. split; [reflexivity|]. pose proof (PjGrammar.scan_quote y c Es) as [Hc _].
unfold PjGrammar.jbind, PjGrammar.jalloc, PjGrammar.take in H. cbn in H.
destruct (PjGrammar.decode y) as [[s' r']|] eqn:Ed; cbn in H; [|discriminate H].
injection H as -> ->. destruct (PjGrammar.decode_stop y s r Ed) as (c' & Hc' & Hr & Hl & _ & Hnz).
rewrite Es in Hc'. injection Hc' as <-. split; [exact Hr|]. split; [exact Hc|]. split; [exact Hl | exact Hnz].
Qed.

Lemma exvs_tag_range : forall t, 0 <= PjTree.tag t <= 6.
Proof. intros t. destruct t; cbn [PjTree.tag]; lia. Qed.
Lemma exvs_tag4 : forall t, PjTree.tag t = 4 -> exists s, t = PjTree.JStr s.
Proof. intros t H. destruct t; cbn [PjTree.tag] in H; try discriminate H. eexists; reflexivity. Qed.

(* bytes through aview *)
Lemma exvs_av_vm1 : forall (H : word -> bool) mem a v,
  val_mem rsegs (mrestrict H mem) a 1 v -> 0 <= v < 256 -> aview rsegs H mem a = Some v.
Proof.
intros H mem a v Hv Hr. unfold aview. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. rewrite Hv.
cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r. rewrite !Z.mod_mod by lia. apply Z.mod_small. exact Hr.
Qed.
Lemma exvs_av_garr8 : forall (H : word -> bool) mem a l j,
  garr8 rsegs (mrestrict H mem) a l -> (j < length l)%nat -> aview rsegs H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof. intros H mem a l j G Hj. destruct (G j Hj) as [V R]. exact (exvs_av_vm1 H mem _ _ V R). Qed.

(* a NUL-terminated string of non-NUL bytes: strcmp's first_byte *)
Lemma exvs_first_byte : forall (W : world rsegs) mem a l,
  garr8 rsegs (mrestrict (w_H W) mem) a (l ++ [0]) -> Forall (fun b => b <> 0) l ->
  first_byte rsegs W mem a (Z.of_nat (length l) + 1) 0 (Z.of_nat (length l)).
Proof.
intros W mem a l G F. rewrite Forall_forall in F. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) l 0).
  pose proof (exvs_av_garr8 (w_H W) mem a (l ++ [0]) (Z.to_nat i) G ltac:(rewrite length_app; cbn; lia)) as A.
  rewrite Z2Nat.id in A by lia. rewrite app_nth1 in A by lia. split; [exact A|].
  apply F. apply nth_In. lia.
- intros _. pose proof (exvs_av_garr8 (w_H W) mem a (l ++ [0]) (length l) G ltac:(rewrite length_app; cbn; lia)) as A.
  rewrite app_nth2, Nat.sub_diag in A by lia. exact A.
Qed.

(* two NUL-terminated strings with the same length and the same bytes are equal *)
Lemma exvs_eq_bytes : forall (W : world rsegs) mem a b l1 l2,
  garr8 rsegs (mrestrict (w_H W) mem) a (l1 ++ [0]) -> garr8 rsegs (mrestrict (w_H W) mem) b (l2 ++ [0]) ->
  length l1 = length l2 ->
  (forall i, 0 <= i < Z.of_nat (length l1) -> aview rsegs (w_H W) mem (a + i) = aview rsegs (w_H W) mem (b + i)) ->
  l1 = l2.
Proof.
intros W mem a b l1 l2 G1 G2 Hl Heq. apply (nth_ext l1 l2 0 0 Hl). intros j Hj.
pose proof (exvs_av_garr8 (w_H W) mem a (l1 ++ [0]) j G1 ltac:(rewrite length_app; cbn; lia)) as A1.
pose proof (exvs_av_garr8 (w_H W) mem b (l2 ++ [0]) j G2 ltac:(rewrite length_app; cbn; lia)) as A2.
rewrite app_nth1 in A1 by lia. rewrite app_nth1 in A2 by lia.
specialize (Heq (Z.of_nat j) ltac:(lia)). rewrite A1, A2 in Heq. injection Heq as Heq. exact Heq.
Qed.

(* a node's header (pj_nodeR, PRH_Reader.v:133-152, whatever its tree), and a string node's bytes *)
Lemma exvs_node_hdr : forall (m : word -> option byte) (lblk : Z -> Z -> Prop) p t D,
  PRH_Reader.pj_nodeR rsegs m lblk p t D ->
  exists num str kids keys n cap, PRH_Reader.pj_hdrR rsegs m p (PjTree.tag t) num str kids keys n cap /\
    (forall s', t = PjTree.JStr s' -> exists k, PRH_Reader.pj_cstrR rsegs m lblk str k s').
Proof.
intros m lblk p t D H.
destruct t as [| | | txt bits | s0 | items | members]; cbn [PRH_Reader.pj_nodeR] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & HH & HM);
  exists num, str, kids, keys, n, cap; (split; [exact HH|]); intros s' Hs'; try discriminate Hs'.
injection Hs' as <-. destruct HM as (_ & _ & _ & _ & k & HK & _). exists k. exact HK.
Qed.

(* the largest need of a list bounds each *)
Lemma exvs_zmaxl_in : forall x l, In x l -> x <= zmaxl l.
Proof.
intros x l. induction l as [|y l IH]; intros H; [destruct H|]. cbn [zmaxl fold_right].
destruct H as [<-|H]; [lia|]. specialize (IH H). fold (zmaxl l). lia.
Qed.

(* ex_value's need covers its frame (with the alignment slack) plus ex_string's and the string runtime's *)
Lemma exvs_stk : forall n, 0 <= STK_ex_string /\ STK_ex_string + 320 <= STK_ex_value n /\
  2 * ESTACK + 320 <= STK_ex_value n /\ 304 <= STK_ex_value n.
Proof.
intros n. unfold STK_ex_value.
pose proof (exvs_zmaxl_in STK_RT_STRTOD [STK_RT_ECALL; STK_RT_STR; STK_RT_STRTOD; STK_ex_string; STK_ex_word; STK_ex_ws]
  ltac:(cbn; tauto)) as M.
assert (HF : @pi_frame prh_img_B F_ex_value = 304) by (vm_compute; reflexivity). rewrite HF.
assert (HS0 : 0 <= STK_ex_string) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HS1 : STK_ex_string + 320 <= 304 + STK_RT_STRTOD) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HE : 2 * ESTACK + 320 <= 304 + STK_RT_STRTOD) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HR : 0 <= STK_RT_STRTOD) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (Nat2Z.is_nonneg n). rewrite Nat2Z.inj_succ. lia.
Qed.

(* ---- the arm's facts at a cut state ---- *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.

(* the geometry of a cut: the entry stack, the cursor, the realigned frame base, the journal's window *)
Lemma exvs_geom : forall E lyc Sc Hpc Wc regs memc mdc k pos,
  EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  exv_sp E mod 16 = 0 /\ 0 <= e_d E /\ e_d E mod 16 = 0 /\
  YM05.alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_lo lyc + exv_STK E <= exv_sp E /\
  exv_sp E + e_d E <= ly_top lyc /\ ly_top lyc <= ly_stk_hi lyc /\ ly_stk_hi lyc <= 2 ^ 47 /\
  exv_sp E + 64 <= ly_stk_hi lyc /\
  exv_sp E <= e_q E /\ e_q E + 40 <= exv_sp E + e_d E /\ e_q E mod 8 = 0 /\
  exv_sp E - 319 <= exv_s1 E <= exv_sp E - 288 /\ exv_s1 E mod 32 = 0 /\
  0 <= STK_ex_string /\ STK_ex_string + 320 <= exv_STK E /\ 2 * ESTACK + 320 <= exv_STK E /\
  (forall a, exv_sp E - exv_STK E <= a < exv_sp E + e_d E -> apresent (w_H Wc) memc a) /\
  ARx lyc Sc Hpc Wc memc mdc.
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos HP HB.
unfold EXV_PRE in HP. cbv zeta in HP. unfold EXB in HB. cbv zeta in HB.
destruct HP as (HFP & _ & _ & _ & _ & _ & Hq8 & _ & Hspq & Hqd & Hwin & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _ & H64 & _).
destruct Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop).
destruct Hwin as (Hd0 & Hd16 & Hdtop & _).
destruct HB as (HJ & _).
destruct HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (exv_s1_le E) as (S1a & S1b).
pose proof (exvs_stk (e_n E)) as (K0 & K1 & K2 & _).
unfold exv_sp, exv_STK in *. rewrite Etop, Eslo, Eshi.
split; [exact Hal|]. split; [exact Hd0|]. split; [exact Hd16|]. split; [exact Hceil|]. split; [exact Hslo|].
split; [exact Hdtop|]. split; [exact Htop|]. split; [exact H47|]. split; [exact H64|]. split; [exact Hspq|].
split; [exact Hqd|]. split; [exact Hq8|]. split; [exact S1a|]. split; [exact S1b|]. split; [exact K0|].
split; [exact K1|]. split; [exact K2|]. split; [|exact HAR].
intros a Ha. apply HPRES.
replace (spZ (e_regs E) + e_d E - (STK_ex_value (e_n E) + e_d E)) with (spZ (e_regs E) - STK_ex_value (e_n E)) by ring.
exact Ha.
Qed.

(* the cursor's bytes, carried to a memory that agrees on [q, q + 32), with in->differs read there *)
Lemma exvs_cur_keep : forall (W : world rsegs) mem mem' q p e dep scr dl dl',
  prhex_cur (PA := PI_prog_B) W mem q p e dep scr dl ->
  (forall a, q <= a < q + 32 -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
  val_mem rsegs (mrestrict (w_H W) mem') (q + 32) 4 dl' ->
  prhex_cur (PA := PI_prog_B) W mem' q p e dep scr dl'.
Proof.
intros W mem mem' q p e dep scr dl dl' (C1 & C2 & C3 & C4 & _) HK V.
split; [|split; [|split; [|split; [|exact V]]]].
- eapply exk_val_kept; [|exact C1]. intros x Hx. cbn in Hx. apply HK. lia.
- eapply exk_val_kept; [|exact C2]. intros x Hx. cbn in Hx. apply HK. lia.
- eapply exk_val_kept; [|exact C3]. intros x Hx. cbn in Hx. apply HK. lia.
- eapply exk_val_kept; [|exact C4]. intros x Hx. cbn in Hx. apply HK. lia.
Qed.
(* across a call the world grows: the same bytes read through two worlds *)
Lemma exvs_vm2 : forall (H H' : word -> bool) (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview rsegs H' m' x = aview rsegs H m x) ->
  val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v HE Hv kk Hk.
rewrite (mbyte_of_aview rsegs H H' m m' (a + Z.of_nat kk)) by (apply HE; lia). exact (Hv kk Hk).
Qed.
Lemma exvs_cur2 : forall (W W' : world rsegs) mem mem' q p p' e dep scr dl,
  prhex_cur (PA := PI_prog_B) W mem q p e dep scr dl -> val_mem rsegs (mrestrict (w_H W') mem') q 8 p' ->
  (forall a, q + 8 <= a < q + 40 -> aview rsegs (w_H W') mem' a = aview rsegs (w_H W) mem a) ->
  prhex_cur (PA := PI_prog_B) W' mem' q p' e dep scr dl.
Proof.
intros W W' mem mem' q p p' e dep scr dl (_ & C2 & C3 & C4 & C5) V HK.
split; [exact V|]. split; [|split; [|split]].
- eapply exvs_vm2; [|exact C2]. intros x Hx. cbn in Hx. apply HK. lia.
- eapply exvs_vm2; [|exact C3]. intros x Hx. cbn in Hx. apply HK. lia.
- eapply exvs_vm2; [|exact C4]. intros x Hx. cbn in Hx. apply HK. lia.
- eapply exvs_vm2; [|exact C5]. intros x Hx. cbn in Hx. apply HK. lia.
Qed.
(* s5 is callee-saved *)
Lemma exvs_aregs21 : forall regs regs' : bvmap 5 word, aregs_preserved regs regs' -> getr regs' 21%bv = getr regs 21%bv.
Proof.
intros regs regs' HP. rewrite <- (Z_to_bv_bv_unsigned 5 21%bv). apply HP.
assert (H21 : bv_unsigned (21%bv : bv 5) = 21) by reflexivity. rewrite H21. unfold acallee_saved. lia.
Qed.
Lemma exvs_cur_eq : forall (W : world rsegs) mem mem' q p e dep scr dl,
  prhex_cur (PA := PI_prog_B) W mem q p e dep scr dl ->
  (forall a, q <= a < q + 40 -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
  prhex_cur (PA := PI_prog_B) W mem' q p e dep scr dl.
Proof.
intros W mem mem' q p e dep scr dl HC HK. apply (exvs_cur_keep W mem mem' q p e dep scr dl dl HC).
- intros a Ha. apply HK. lia.
- destruct HC as (_ & _ & _ & _ & C5). eapply exk_val_kept; [|exact C5]. intros x Hx. cbn in Hx. apply HK. lia.
Qed.

(* EXV_RES at an exit: the grammar refused (r = -1), or read u with rest (r = 0) *)
Lemma exvs_res_none : forall E (W : world rsegs) mem p dl, exv_V E = None ->
  prhex_cur (PA := PI_prog_B) W mem (e_q E) (e_x0 E + p) (e_x0 E + exv_len E) (e_dep E) (e_scr E) dl ->
  0 <= p <= exv_len E ->
  (dl = 0 \/ dl = 1) -> e_dep E <= 33 -> EXV_RES E W mem (-1).
Proof.
intros E W mem p dl HV HC Hp Hdl Hd. exists p, (e_dep E), dl. split; [exact HC|]. split; [exact Hdl|].
rewrite HV. split; [reflexivity|]. split; [exact Hp | lia].
Qed.
Lemma exvs_res_ok : forall E (W : world rsegs) mem u rest dl, exv_V E = Some (u, rest) ->
  prhex_cur (PA := PI_prog_B) W mem (e_q E) (e_x0 E + (exv_len E - Z.of_nat (length rest))) (e_x0 E + exv_len E)
    (e_dep E)
    (e_scr E) dl -> (dl = 0 \/ dl = 1) -> (dl = 1 <-> e_dl E = 1 \/ (e_v E <> 0 /\ e_t E <> u)) ->
  EXV_RES E W mem 0.
Proof.
intros E W mem u rest dl HV HC Hdl Hiff. exists (exv_len E - Z.of_nat (length rest)), (e_dep E), dl.
split; [exact HC|]. split; [exact Hdl|]. rewrite HV. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
exact Hiff.
Qed.

(* the registers EXB reads are callee-saved *)
Lemma exvs_aregs_kept : forall regs regs' : bvmap 5 word, aregs_preserved regs regs' ->
  forall r, In r EXVS_KEPT -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP.
assert (Hz : In (bv_unsigned r) [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]).
{ unfold EXVS_KEPT in Hr. apply (in_map (@bv_unsigned 5)) in Hr. exact Hr. }
unfold acallee_saved. cbn [In] in Hz. lia.
Qed.

(* the tree's root v (not NULL): in the application range, below 2 ^ 47, apart from the stack window and the cursor *)
Lemma exvs_v_rng : forall E lyc Sc Hpc Wc regs memc mdc k pos,
  EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> e_v E <> 0 ->
  4096 <= e_v E /\ e_v E + 56 <= 2 ^ 47 /\
  (forall x, e_v E <= x < e_v E + 56 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44)) /\
  (forall z, e_v E <= z < e_v E + 56 -> ~ (exv_sp E - exv_STK E <= z < exv_sp E) /\ ~ (e_q E <= z < e_q E + 40)).
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos HP HB Hv0.
pose proof (eh_laws B ARx SK HYP) as LAWS. pose proof asan_consts as (C1 & _).
pose proof (@cf_head_nonneg cp) as CH0.
pose proof (exvs_geom E lyc Sc Hpc Wc regs memc mdc k pos HP HB) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 &
  G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & HAR).
pose proof HP as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPV & _).
destruct HPV as [HPV | (_ & _ & HDJ)]; [exfalso; exact (Hv0 HPV)|].
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & HLED & _ & R2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & HTREE).
destruct HTREE as [Hv | (Hnd & Hhome & _ & _)]; [exfalso; exact (Hv0 Hv)|].
pose proof (exv_foot_rng B ARx SK HYP lyc Sc Hpc Wc memc mdc (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
  regs (e_v E) (e_t E) (e_D E) HAR HLED Hnd Hhome G8) as FOOT.
pose proof (FOOT (e_v E) ltac:(left; lia)) as F0. pose proof (FOOT (e_v E + 55) ltac:(left; lia)) as F1.
assert (HAPP : 4096 <= e_v E /\ (forall x, e_v E <= x < e_v E + 56 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44))).
{ destruct Hhome as [(b & kk & Hin & H1 & H2) | [(cid & pos' & Hin & H1 & H2) | (H1 & H2)]].
  - pose proof HLED as (_ & _ & HBL & _). rewrite Forall_forall in HBL.
    destruct (HBL (b, kk) Hin) as (Hk0 & Hblk & _ & _ & _). cbn [fst snd] in *.
    destruct (alx_blocks rsegs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hblk) as (_ & H4096 & _ & Happ & _).
    assert (Hrq : kk + cf_head <= req_size (kk + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
    split; [lia|]. intros x Hx. pose proof (in_app_addr _ _ x Happ ltac:(lia)) as Hx'.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
  - destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ cid pos' HAR Hin) as (F2 & F3 & Happ).
    split; [lia|]. intros x Hx. pose proof (in_app_addr _ _ x Happ ltac:(lia)) as Hx'.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
  - unfold spZ in H1. rewrite R2 in H1. unfold w64 in H1. rewrite unsigned_lit_small in H1 by zl.
    split; [zl|]. intros x Hx. unfold SHADOW_OFF. zl. }
destruct HAPP as (HA1 & HA2).
split; [exact HA1|]. split; [lia|]. split; [exact HA2|].
intros z Hz. destruct (HDJ z ltac:(left; exact Hz)) as (_ & Hq & Hst & _). unfold exv_sp, exv_STK. split; assumption.
Qed.

(* a NUL-terminated string of non-NUL bytes inside a live block: what strcmp asks of each operand but the shadow *)
Lemma exvs_blk_op : forall ly S Hp (W : world rsegs) mem md b m x l,
  ARx ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> b <= x -> x + Z.of_nat (length l) + 1 <= b + m ->
  garr8 rsegs (mrestrict (w_H W) mem) x (l ++ [0]) -> Forall (fun c => c <> 0) l ->
  4096 <= x /\ Z.of_nat (length l) + 1 < 2 ^ 32 /\ x + Z.of_nat (length l) + 1 <= YM05.alloc_ceiling /\
  YGcallMx.amem_range8 x (Z.of_nat (length l) + 1) /\
  first_byte rsegs W mem x (Z.of_nat (length l) + 1) 0 (Z.of_nat (length l)) /\
  (forall a, x <= a < x + Z.of_nat (length l) + 1 -> aview rsegs (w_H W) mem a <> None) /\
  (forall a, x + Z.of_nat (length l) < a < x + Z.of_nat (length l) - (x + Z.of_nat (length l)) mod 8 + 8 ->
     aview rsegs (w_H W) mem a <> None).
Proof.
intros ly S Hp W mem md b m x l HAR Hin Hbx Hxm G F.
pose proof (eh_laws B ARx SK HYP) as LAWS.
destruct (alx_blocks rsegs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4096 & Hbc & _ & Hpres & _).
pose proof (eh_blk32 B ARx SK HYP ly S Hp W mem md b m HAR Hin) as H32.
pose proof (eh_blk_amem8 B ARx SK HYP ly S Hp W mem md b m (x - b + Z.of_nat (length l)) HAR Hin ltac:(lia)) as HA8.
assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ unfold YGcallMx.amem_range8 in *. destruct HA8 as [H|[H1 H2]]; [left; lia | right; split; lia]. }
split; [exact (exvs_first_byte W mem x l G F)|]. split.
{ intros a Ha. replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia.
  rewrite (exvs_av_garr8 (w_H W) mem x (l ++ [0]) (Z.to_nat (a - x)) G) by (rewrite length_app; cbn; lia).
  discriminate. }
intros a Ha. destruct (Z_lt_le_dec a (b + req_size m)) as [Hlt|Hge].
- apply (aview_some_of_apresent rsegs). apply (proj1 (Hpres a ltac:(lia))).
- apply (alx_blocks_tail rsegs B ARx LAWS ly S Hp W mem md b m a HAR Hin). split; [exact Hge|]. zl.
Qed.
End k.
