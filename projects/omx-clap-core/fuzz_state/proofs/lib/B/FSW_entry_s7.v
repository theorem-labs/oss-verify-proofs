(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_entry.v, with its module paths and module names changed; 2668 of its 2786 lines of code are new or changed and 1447 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S7a_put.v, with its module paths and module names changed; 881 of its 954 lines of code are new or changed and 2713 lines of the source are left out. *)
(* fs program part, lane ENTRY, IMAGE B (fs.asan-ubsan, sha256 5ac5ce0954f8...), segment S7 of the LLVMFuzzerTestOneInput
   walk (fs.asan-ubsan 0x81148-0x8116c; lib/B/FSW_entry_defs.v): from check_as_written's return (C6, 0x81148) to the join
   after the round-trip / reject check (C7, 0x81170). `ld a2, 0(s4)` (0x81148) reads len (the frame's offset 32, atom 46;
   s4 is re-expressed as the frame atom + 32), `beqz s6` (0x8114c) splits on decode's answer (caw_answerA): body <> 0
   calls check_round_trip(text, body, len) at 0x81158 (ra 0x8115c) and runs its `j 0x81170`; body = 0 calls
   check_reject_clean(0, len, live) at 0x8116c (ra 0x81170). The segment's eleven instructions are A's 0x810c8-0x810ec
   word for word (B = A + 0x80 here; every numeral above is read from the B listing). Each call is a program call: the
   callee's fpreU from the walk's journal (YCbq afn_pre_at; the chain is the entry's pushed by its frame record), the
   spec (lib/B/FSH_Fn_crt.v / FSH_Fn_checks.v, CTX-free: no call-context premise), the callee journal composed by
   FSW_K3.fsw_ajournal_sub4, the boundary state by FSW_entry_canon.fe_canon; the data the walk keeps (the text, decode's
   answer, the payload, the allocator statics) is carried across each run by its frame and across each call by the
   callee's journal and AR at the return.
   rule 24: proves function LLVMFuzzerTestOneInput (segment S7; reuse search: proof-index LLVMFuzzerTestOneInput,
   ported from a working branch 08ad70da3bf).
   Ported from: a working branch 0d34d65d2b7 lib/A/FSW_entry_s7.v (fuzz_state's own A walk, from
   a working branch 08ad70da3bf, itself from donor cgif_file_fuzzer lib/A/ACf5.v:73-84 and A/ACfk.v:220-245), with
   the CTX premise of check_round_trip_spec dropped (post-drop shape) and the image-B form of cgif_file_fuzzer
   lib/YCfj.v + lib/YCfi.v (origin/ossv/recipes).
   Named Section hypotheses, owner RELOC-B: none (the Section takes only the statement's own facts: fs_img_facts and the
   two callee specs of FsEntryFns). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YE01 YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_frame FSW_K3 FSW_strkit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YCfn FSH_Harness FSH_Fn_entry.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Fn_alloc FSH_Fn_checks FSH_Fn_cno FSH_Fn_crt FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSW_entry_defs FSW_entry_canon.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- facts about fs.asan-ubsan's image, by computation ---- *)
Lemma s7_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hb : forallb (fun r => existsb (fun s => (Z.of_N (seg_base s) <=? fst r) &&
  (snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs) FS_PSTAT_FP = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. apply existsb_exists in H as (sg & Hsg & H).
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hsg | lia].
Qed.
Lemma s7_pstat_low : forall a, inFP FS_PSTAT_FP a -> 0 <= a < FS_IMG_END.
Proof. intros a H. exact (fs_segs_img a (s7_pstat_img a H)). Qed.
Lemma s7_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. intros (r & Hr & Ha). cbn in Hr. repeat destruct Hr as [<-|Hr]; cbn in Ha; lia. Qed.
(* a read-only byte (a read-only segment or the relro range) is an image byte outside the statics *)
Lemma s7_roP : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a /\ ~ inFP FS_PSTAT_FP a.
Proof.
intros a [(sg & Hsg & Hw & Ha) | Ha].
- split; [exists sg; split; [exact Hsg | exact Ha]|].
  assert (Hb : forallb (fun s => seg_writable s || forallb (fun r => (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? fst r)
    || (snd r <=? Z.of_N (seg_base s))) FS_PSTAT_FP) tfibsegs = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hb sg Hsg) as H. cbn beta in H. rewrite Hw in H. cbn [orb] in H.
  intros (r & Hr & Har). pose proof (proj1 (forallb_forall _ _) H r Hr) as Hr'.
  apply orb_prop in Hr' as [Hr' | Hr']; apply Z.leb_le in Hr'; lia.
- split.
  + assert (Hb : existsb (fun s => (Z.of_N (seg_base s) <=? FS_RLO) &&
      (FS_RHI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true) by (vm_compute; reflexivity).
    apply existsb_exists in Hb as (sg & Hsg & H). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    exists sg. split; [exact Hsg | lia].
  + intros (r & Hr & Har). cbn in Hr. unfold FS_RLO, FS_RHI in Ha.
    repeat destruct Hr as [<-|Hr]; cbn in Har; lia.
Qed.

(* the text's length *)
Lemma s7_zfind_lt : forall c l j, zfind c l = Some j -> (j < length l)%nat.
Proof.
intros c l. induction l as [|x t IH]; intros j H; cbn in H; [discriminate H|].
destruct (x =? c); [injection H as <-; cbn; lia|].
destruct (zfind c t) as [j'|] eqn:E; cbn in H; [injection H as <-; cbn; specialize (IH j' eq_refl); lia | discriminate H].
Qed.
Lemma s7_n_le : forall cx, c_n cx = Z.of_nat (length (c_pl cx)) -> 0 <= fe_n cx <= c_n cx.
Proof.
intros cx Hn. unfold fe_n. destruct (zfind 0 (fe_bytes cx)) as [j|] eqn:E; [|lia].
pose proof (s7_zfind_lt 0 _ j E) as H. unfold fe_bytes in H. rewrite length_map in H. lia.
Qed.
Lemma s7_tb_len : forall cx, c_n cx = Z.of_nat (length (c_pl cx)) -> Z.of_nat (length (fe_tb cx)) = fe_n cx.
Proof.
intros cx Hn. pose proof (s7_n_le cx Hn) as H. unfold fe_tb. rewrite length_firstn.
unfold fe_bytes. rewrite length_map. lia.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis en_round_trip : @check_round_trip_spec fx rc SK tfibsegs B.
Hypothesis en_reject_clean : @check_reject_clean_spec fx rc SK tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Lemma s7_base_sp : forall cx, fe_base B cx ->
  fe_sp0 cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= fe_sp0 cx /\ fe_sp0 cx <= 2 ^ 47.
Proof.
intros cx ((HAP & _) & _). pose proof (fsw_sp_pre B LLVMF_STK _ _ _ _ _ _ _ HAP) as (H1 & H2 & H3 & _).
unfold fe_sp0. lia.
Qed.

(* the data the walk keeps across S7: decode's answer, the text, the payload, the allocator statics *)
Definition s7_mf (cx : fecx) ly S U (W : world tfibsegs) (m : word -> option byte) (text body l live cnt : Z) : Prop :=
  caw_answerA tfibsegs B ly S U W m (fe_tb cx) body l /\ cstr_ok tfibsegs W m text (fe_tb cx) /\
  (forall i, 0 <= i < c_n cx ->
     aview tfibsegs (w_H W) m (c_p cx + i) = aview tfibsegs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)) /\
  fs_stat tfibsegs W m live cnt.

(* the addresses that data reads: the bytes of a live block, their shadow bytes, the statics *)
Definition s7_kaddr (ly : alayout) (S : astate) (a : Z) : Prop :=
  (exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
  (exists b n x, In (b, n) (ablocks B ly S) /\ b <= x < b + req_size n /\ a = shadow_addr x) \/
  inFP FS_PSTAT_FP a.

(* the data carried over a memory change that keeps those addresses and only adds bytes (a run of the engine) *)
Lemma s7_mf_keep : forall cx ly S U (W : world tfibsegs) m m' md text body l live cnt,
  c_n cx = Z.of_nat (length (c_pl cx)) ->
  ARU tfibsegs B ly S U W m md ->
  In (text, fe_n cx + 1) (ablocks B ly S) ->
  (c_n cx = 0 \/ In (c_p cx, c_n cx) (ablocks B ly S)) ->
  (forall a, 0 <= a < 2 ^ 64 -> s7_kaddr ly S a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  s7_mf cx ly S U W m text body l live cnt -> s7_mf cx ly S U W m' text body l live cnt.
Proof.
intros cx ly S U W m m' md text body l live cnt Hn HARU Htext Hpay K HG (Hans & Hcs & Hpl & Hst).
pose proof (ARU_AR tfibsegs B ly S U W m md HARU) as HAR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* a block byte, a block byte's shadow, a static: kept *)
assert (KB : forall b n a, In (b, n) (ablocks B ly S) -> b <= a < b + req_size n ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) /\ m' (Z_to_bv 64 (shadow_addr a)) = m (Z_to_bv 64 (shadow_addr a))).
{ intros b n a Hb Ha.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hb) as (_ & H4096 & Hceil & _).
  split; apply K.
  - lia.
  - left. exists b, n. auto.
  - unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos a 8). pose proof (Z.div_le_upper_bound a 8 (2 ^ 61)). lia.
  - right. left. exists b, n, a. auto. }
assert (KM : forall b n a, In (b, n) (ablocks B ly S) -> b <= a < b + req_size n ->
  mbyte tfibsegs (mrestrict (w_H W) m') a = mbyte tfibsegs (mrestrict (w_H W) m) a).
{ intros b n a Hb Ha. unfold mbyte, mrestrict. rewrite (proj1 (KB b n a Hb Ha)). reflexivity. }
assert (KS : forall b n a, In (b, n) (ablocks B ly S) -> b <= a < b + req_size n ->
  aview tfibsegs (w_H W) m' (shadow_addr a) = aview tfibsegs (w_H W) m (shadow_addr a)).
{ intros b n a Hb Ha. apply aview_at. exact (proj2 (KB b n a Hb Ha)). }
assert (KV : forall a, aview tfibsegs (w_H W) m a <> None -> aview tfibsegs (w_H W) m' a <> None)
  by (intros a Hv; exact (aview_keeps_vis tfibsegs (w_H W) m m' a HG Hv)).
pose proof (s7_tb_len cx Hn) as Hlen.
split; [|split; [|split]].
- destruct Hans as [Hans | (bs & mm & Hd & Hbd & Hl & Hsrc & Hrb & Hlm & HU)]; [left; exact Hans|].
  right. exists bs, mm. split; [exact Hd|]. split; [exact Hbd|]. split; [exact Hl|].
  destruct Hrb as (Hin & Hmod & Hpos & Hv).
  assert (Hrq : req_size (mm + HEAD) = mm + 16) by (unfold req_size, HEAD; destruct (Z.eqb_spec (mm + 16) 0); lia).
  destruct Hsrc as (Hz & H4096 & Hcl & Ham & Hra & Hhv).
  split; [|split; [|split; [exact Hlm | exact HU]]].
  + split; [|split; [exact H4096|split; [exact Hcl|split; [exact Ham|split]]]].
    * unfold zbytes_at in *. apply (garr8_frame tfibsegs _ _ body bs Hz). intros a Ha.
      apply (KM _ _ a Hin). rewrite Hrq. unfold HEAD. lia.
    * intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
      change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hs |- *.
      rewrite (KS _ _ x Hin) by (rewrite Hrq; unfold HEAD; lia). exact Hs.
    * intros Hlt s Hs. exact (KV s (Hhv Hlt s Hs)).
  + split; [exact Hin|]. split; [exact Hmod|]. split; [exact Hpos|].
    intros k Hk. rewrite (KM _ _ (body - HEAD + Z.of_nat k) Hin) by (rewrite Hrq; unfold HEAD; lia). exact (Hv k Hk).
- destruct Hcs as ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
  assert (Hrq : req_size (fe_n cx + 1) = fe_n cx + 1) by (unfold req_size; destruct (Z.eqb_spec (fe_n cx + 1) 0); lia).
  split; [split; [|exact Hnz]|].
  { apply (garr8_frame tfibsegs _ _ text _ Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
    apply (KM _ _ a Htext). rewrite Hrq. lia. }
  split; [exact H4096|]. split; [exact Hcl|]. split; [exact H32|]. split; [exact Ham|].
  split.
  { intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hs |- *.
    rewrite (KS _ _ x Htext) by (rewrite Hrq; lia). exact Hs. }
  split; [intros s Hs; exact (KV s (Hhv s Hs))|].
  intros a Ha. exact (KV a (Htl a Ha)).
- intros i Hi. rewrite <- (Hpl i Hi). destruct Hpay as [H0 | Hin]; [lia|].
  apply aview_at. apply (proj1 (KB _ _ (c_p cx + i) Hin ltac:(unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia))).
- destruct Hst as (peak & G1 & G2 & G3 & G4 & R). exists peak.
  assert (KG : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) m) g 8 v ->
    val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
  { intros g v Hg Hv k Hk. rewrite <- (Hv k Hk). unfold mbyte, mrestrict.
    assert (Hf : inFP FS_PSTAT_FP (g + Z.of_nat k)) by (apply (inFP_FS_PSTAT_FP g Hg); lia).
    pose proof (s7_pstat_low _ Hf) as Hlo. unfold FS_IMG_END in Hlo.
    rewrite (K (g + Z.of_nat k)) by (try lia; right; right; exact Hf). reflexivity. }
  split; [apply KG; [cbn; tauto | exact G1]|]. split; [apply KG; [cbn; tauto | exact G2]|].
  split; [apply KG; [cbn; tauto | exact G3]|]. split; [apply KG; [cbn; tauto | exact G4]|]. exact R.
Qed.

(* a run whose regions are the boundary state's (the frame, its shadow, the saved words) keeps those addresses *)
Lemma s7_keep_frame : forall cx E cs ly S U (W : world tfibsegs) m m' md,
  fe_base B cx -> fe_regs_core cx E ->
  ARU tfibsegs B ly S U W m md -> In (0, c_fpos cx) (frames S) -> ly_F ly = ly_F (c_ly cx) ->
  frame_of E (fe_regions cs) m m' ->
  forall a, 0 <= a < 2 ^ 64 -> s7_kaddr ly S a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros cx E cs ly S U W m m' md Hb (E8 & _ & _ & _ & E24 & E25 & _) HARU Hfr ELY HF a Ha Hk.
pose proof (ARU_AR tfibsegs B ly S U W m md HARU) as HAR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (s7_base_sp cx Hb) as (Hal16 & Hceil & H47). unfold LLVMF_STK in Hceil.
assert (EF : frame_addr ly 0 (c_fpos cx) = fe_F cx) by (unfold fe_F, frame_addr; rewrite ELY; reflexivity).
destruct (al_frames _ _ LAWS ly S W (unpoison U m) md 0 (c_fpos cx) HAR Hfr) as (Hal32 & Happ & _).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U m) md 0 (c_fpos cx) HAR Hfr) as (H4096 & Hfc & _).
rewrite EF in Hal32, Happ, H4096, Hfc.
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in Happ, Hfc.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
assert (ESF : fe_SF cx = SHADOW_OFF + fe_F cx / 8) by reflexivity.
assert (Hsp0 : 0 <= fe_sp0 cx < 2 ^ 64) by (unfold fe_sp0, spZ; apply bv_unsigned_in_range).
assert (B24 : bv_unsigned (ew E 24) = fe_F cx) by (rewrite E24; apply wz; lia).
assert (B25 : bv_unsigned (ew E 25) = fe_SF cx)
  by (rewrite E25; apply wz; rewrite ESF; unfold SHADOW_OFF; pose proof (Z.div_pos (fe_F cx) 8); pose proof (Z.div_le_upper_bound (fe_F cx) 8 (2 ^ 61)); lia).
assert (B8 : bv_unsigned (ew E 8) = fe_sp0 cx) by (rewrite E8; apply wz; exact Hsp0).
(* where a kept address lies *)
assert (KL : (exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n /\
               4096 <= a < alloc_ceiling /\ (a < kLowShadowBeg \/ kHighMemBeg <= a) /\ ~ (fe_F cx <= a < fe_F cx + 64)) \/
             (exists x, 4096 <= x < alloc_ceiling /\ ~ (fe_F cx <= x < fe_F cx + 64) /\ a = shadow_addr x) \/
             (0 <= a < FS_IMG_END /\ ~ (fe_F cx <= a < fe_F cx + 64))).
{ destruct Hk as [(b & n & Hin & Hr) | [(b & n & x & Hin & Hr & ->) | Hf]].
  - left. exists b, n. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4 & Hbc & Hbapp & _).
    pose proof (sep_block_frame tfibsegs B LAWS ly S W (unpoison U m) md b n 0 (c_fpos cx) HAR Hin Hfr) as Hd.
    rewrite EF, Hfb in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. unfold kLowShadowBeg, kHighMemBeg.
    split; [exact Hin|]. split; [exact Hr|]. lia.
  - right. left. exists x. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4 & Hbc & _).
    pose proof (sep_block_frame tfibsegs B LAWS ly S W (unpoison U m) md b n 0 (c_fpos cx) HAR Hin Hfr) as Hd.
    rewrite EF, Hfb in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - right. right. split; [exact (s7_pstat_low a Hf)|]. intros Hr.
    apply (frm_img tfibsegs B LAWS ly S W (unpoison U m) md 0 (c_fpos cx) a HAR Hfr); [rewrite EF, Hfb; exact Hr|].
    exact (s7_pstat_img a Hf). }
apply HF. rewrite (wz a Ha). intros (r & Hin & Hr).
unfold fe_regions in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fe_frame_region fe_shadow_region fs_ret_s0_region] in Hr.
- rewrite B24 in Hr. destruct KL as [(b & n & _ & _ & _ & _ & HnF) | [(x & Hx & HxF & ->) | (_ & HnF)]]; [lia| |lia].
  unfold shadow_addr, SHADOW_OFF in Hr. unfold kLowShadowBeg, kHighMemBeg in *.
  pose proof (Z.div_pos x 8). pose proof (Z.div_le_upper_bound x 8 (2 ^ 61)). lia.
- rewrite B25, ESF in Hr. unfold SHADOW_OFF in Hr.
  destruct KL as [(b & n & _ & _ & Ha4 & Hlh & _) | [(x & Hx & HxF & ->) | (Hlo & _)]].
  + unfold kLowShadowBeg, kHighMemBeg, FS_IMG_END in *.
    pose proof (Z.div_pos (fe_F cx) 8). pose proof (Z.div_le_upper_bound (fe_F cx) 8 (2 ^ 61)). lia.
  + unfold shadow_addr, SHADOW_OFF in Hr.
    destruct (proj1 (Zmod_divides _ 32 ltac:(lia)) Hal32) as (c & Hc).
    assert (F8 : fe_F cx / 8 = 4 * c) by (rewrite Hc; replace (32 * c) with ((4 * c) * 8) by lia; apply Z.div_mul; lia).
    pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
  + unfold FS_IMG_END in Hlo. pose proof (Z.div_pos (fe_F cx) 8). lia.
- rewrite B8 in Hr. unfold FS_IMG_END in *.
  destruct KL as [(b & n & _ & _ & Ha4 & _) | [(x & Hx & _ & ->) | (Hlo & _)]]; [lia| |lia].
  unfold shadow_addr, SHADOW_OFF in Hr. pose proof (Z.div_le_upper_bound x 8 (2 ^ 61)). lia.
Qed.

(* the data carried over a program call: the callee's journal keeps every live block's bytes outside its footprint
   (image bytes only), AR at the return gives the blocks' shadow, and U is the same at both ends *)
Lemma s7_mf_call : forall cx STKc spc FP1 ly S U (W : world tfibsegs) m md ly' S' W' m' md' kc text body l live cnt
  live' cnt',
  c_n cx = Z.of_nat (length (c_pl cx)) ->
  ARU tfibsegs B ly S U W m md ->
  ajournal tfibsegs B STKc spc FP1 ly S W (unpoison U m) md [] ly' S' W' (unpoison U m') md' kc ->
  upoison_ok B ly' S' U -> upoisoned tfibsegs W' m' U ->
  (forall a, inFP FP1 a -> in_img tfibsegs a) ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  In (text, fe_n cx + 1) (ablocks B ly S) ->
  (c_n cx = 0 \/ In (c_p cx, c_n cx) (ablocks B ly S)) ->
  U = fe_body_U body ->
  s7_mf cx ly S U W m text body l live cnt -> fs_stat tfibsegs W' m' live' cnt' ->
  s7_mf cx ly' S' U W' m' text body l live' cnt'.
Proof.
intros cx STKc spc FP1 ly S U W m md ly' S' W' m' md' kc text body l live cnt live' cnt' Hn HARU HJ OK' PO' HFP Hinc
  Htext Hpay EU (Hans & Hcs & Hpl & Hst) Hst'.
pose proof (ARU_AR tfibsegs B ly S U W m md HARU) as HAR.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (HARU' : ARU tfibsegs B ly' S' U W' m' md') by (split; [exact HAR' | split; [exact OK' | exact PO']]).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KA : forall b n a, In (b, n) (ablocks B ly S) -> b <= a < b + req_size n ->
  aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a).
{ intros b n a Hb Ha.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hb) as (_ & Hb4 & Hbc & Hbapp & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  assert (Hr : 0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)) by (unfold SHADOW_OFF, kHighMemBeg; lia).
  rewrite <- (aview_at tfibsegs (w_H W') (unpoison U m') m' a) by (exact (unpoison_app B ly' S' U W' m' md' a HARU' (proj1 Hr) (proj2 Hr))).
  rewrite <- (aview_at tfibsegs (w_H W) (unpoison U m) m a) by (exact (unpoison_app B ly S U W m md a HARU (proj1 Hr) (proj2 Hr))).
  replace a with (b + (a - b)) by lia.
  apply (F2 b n (a - b) Hb (Hinc _ Hb)); [lia|]. intros Hf.
  apply (blk_img tfibsegs B LAWS ly S W (unpoison U m) md b n (b + (a - b)) HAR Hb); [lia | exact (HFP _ Hf)]. }
assert (KM : forall b n a, In (b, n) (ablocks B ly S) -> b <= a < b + req_size n ->
  mbyte tfibsegs (mrestrict (w_H W') m') a = mbyte tfibsegs (mrestrict (w_H W) m) a)
  by (intros b n a Hb Ha; apply (mbyte_of_aview tfibsegs); exact (KA b n a Hb Ha)).
pose proof (s7_tb_len cx Hn) as Hlen.
split; [|split; [|split; [|exact Hst']]].
- destruct Hans as [Hans | (bs & mm & Hd & Hbd & Hl & Hsrc & Hrb & Hlm & HU)]; [left; exact Hans|].
  right. exists bs, mm. split; [exact Hd|]. split; [exact Hbd|]. split; [exact Hl|].
  destruct Hrb as (Hin & Hmod & Hpos & Hv).
  assert (Hrq : req_size (mm + HEAD) = mm + 16) by (unfold req_size, HEAD; destruct (Z.eqb_spec (mm + 16) 0); lia).
  pose proof (Hinc _ Hin) as Hin'.
  destruct Hsrc as (Hz & H4096 & Hcl & Ham & Hra & Hhv).
  assert (EU1 : U = [(body - HEAD, HEAD)]) by (rewrite EU; unfold fe_body_U; destruct (Z.eqb_spec body 0); [lia | reflexivity]).
  split; [|split; [|split; [exact Hlm | exact HU]]].
  + split; [|split; [exact H4096|split; [exact Hcl|split; [exact Ham|split]]]].
    * unfold zbytes_at in *. apply (garr8_frame tfibsegs _ _ body bs Hz). intros a Ha.
      apply (KM _ _ a Hin). rewrite Hrq. unfold HEAD. lia.
    * intros x Hx.
      destruct (range_addressable_of_block tfibsegs B LAWS ly' S' W' (unpoison U m') md' (body - HEAD) (mm + HEAD) body
        (Z.of_nat (length bs)) HAR' Hin' ltac:(unfold HEAD; lia) ltac:(rewrite Hrq; unfold HEAD; lia) x Hx) as (s & Hs & Hok).
      exists s. split; [|exact Hok].
      change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hs |- *.
      rewrite <- (aview_unpoison_sh U W' m' (shadow_addr x)); [exact Hs | |].
      -- unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos x 8). pose proof (Z.div_le_upper_bound x 8 (2 ^ 61)).
         unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia.
      -- rewrite EU1. unfold in_ush. cbn [existsb fst snd]. rewrite orb_false_r.
         apply andb_false_intro2. apply Z.ltb_ge. unfold shadow_addr, HEAD.
         destruct (proj1 (Zmod_divides _ 16 ltac:(lia)) Hmod) as (c & Hc).
         assert (E1 : (body - 16) / 8 = 2 * c - 2) by (rewrite Hc; replace (16 * c - 16) with ((2 * c - 2) * 8) by lia; apply Z.div_mul; lia).
         assert (E2 : body / 8 <= x / 8) by (apply Z.div_le_mono; lia).
         assert (E3 : body / 8 = 2 * c) by (rewrite Hc; replace (16 * c) with ((2 * c) * 8) by lia; apply Z.div_mul; lia).
         change (16 / 8) with 2. lia.
    * intros Hlt s Hs. apply (aview_unpoison_vis U W' m' s PO').
      destruct (al_shadow _ _ LAWS ly' S' W' (unpoison U m') md' (body - HEAD) (mm + HEAD) HAR' Hin') as (_ & Hhv').
      apply (shadow_hull_vis_sub _ (body - HEAD) (req_size (mm + HEAD)) body (Z.of_nat (length bs)) Hhv');
        [unfold HEAD; lia | rewrite Hrq; unfold HEAD; lia | exact Hlt | exact Hs].
  + split; [exact Hin'|]. split; [exact Hmod|]. split; [exact Hpos|].
    intros k Hk. rewrite (KM _ _ (body - HEAD + Z.of_nat k) Hin) by (rewrite Hrq; unfold HEAD; lia). exact (Hv k Hk).
- assert (Hrq : req_size (fe_n cx + 1) = fe_n cx + 1) by (unfold req_size; destruct (Z.eqb_spec (fe_n cx + 1) 0); lia).
  apply (cstr_ok_kept_blkU B STKc spc FP1 ly S U W m md [] ly' S' U W' m' md' kc text (fe_tb cx) text (fe_n cx + 1)
    HARU HJ OK' PO' Htext (Hinc _ Htext) ltac:(lia) ltac:(lia)); [| intros r Hr; left; exact Hr | exact Hcs].
  intros a Ha Hf. apply (blk_img tfibsegs B LAWS ly S W (unpoison U m) md text (fe_n cx + 1) a HAR Htext);
    [rewrite Hrq; lia | exact (HFP a Hf)].
- intros i Hi. rewrite <- (Hpl i Hi). destruct Hpay as [H0 | Hin]; [lia|].
  apply (KA _ _ (c_p cx + i) Hin). unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia.
Qed.

(* an 8-byte value in memory, read as a word *)
Lemma s7_rdword_of_val_mem : forall (H : word -> bool) m a v,
  val_mem tfibsegs (mrestrict H m) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview tfibsegs H m) a = Some v.
Proof.
intros H m a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview tfibsegs H m (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply YG0s.le_bytes8. exact Hr.
Qed.

(* a word chunk holding an atom, moved to another memory holding the same bytes and an env agreeing on the atom *)
Lemma s7_chunk_move : forall E E' (mc m' : word -> option byte) base off n,
  YP09.chunk_ok tfibsegs E mc base (YP09.mkChunk off (CVal 8 (SOff n 0))) ->
  ew E' n = ew E n ->
  (forall j, 0 <= j < 8 -> mbyte tfibsegs m' (base + off + j) = mbyte tfibsegs mc (base + off + j)) ->
  YP09.chunk_ok tfibsegs E' m' base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E E' mc m' base off n Hc En Hm.
pose proof (bv_unsigned_in_range 64 (ew E n)) as Hrg. change (bv_modulus 64) with (2 ^ 64) in Hrg.
pose proof (val_of_chunk_ok tfibsegs E mc base off 8 (SOff n 0) (bv_unsigned (ew E n)) Hc
  ltac:(rewrite fsw_SOff0, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(lia)) as Hv.
apply (chunk_ok_val tfibsegs E' m' base off 8 (SOff n 0) (bv_unsigned (ew E n)));
  [rewrite fsw_SOff0, En, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
intros k Hk. rewrite Hm by (cbn in Hk; lia). exact (Hv k Hk).
Qed.

(* the boundary state at a program call's return: fe_canon from the call state's regions, carried by the callee's
   journal (its window lies below the saved words, its footprint misses the frame) *)
Lemma s7_st_ret : forall cx E ssc (W : world tfibsegs) msc md ly S U STKc FP1 regs' ly' S' W' m' md' kc k l r,
  fe_base B cx -> fe_E cx E -> fe_regs_core cx E -> ew E 46 = Z_to_bv 64 l ->
  st_ok tfibsegs E ssc (restrict (w_H W) msc) -> ss_mem ssc = fe_regions [fe_len_atom 46] ->
  ARU tfibsegs B ly S U W (ms_mem msc) md -> In (0, c_fpos cx) (frames S) -> ly_F ly = ly_F (c_ly cx) ->
  ajournal tfibsegs B STKc (spZ (ms_regs msc)) FP1 ly S W (unpoison U (ms_mem msc)) md [] ly' S' W' (unpoison U m') md'
    kc ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly' S' W' (unpoison U m') md' k ->
  ARU tfibsegs B ly' S' U W' m' md' ->
  (forall a, inFP FP1 a -> in_img tfibsegs a) ->
  spZ (ms_regs msc) <= fe_sp0 cx - 88 ->
  YK11.getr regs' 8%bv = Z_to_bv 64 (fe_sp0 cx) -> YK11.getr regs' 24%bv = Z_to_bv 64 (fe_F cx) ->
  YK11.getr regs' 18%bv = Z_to_bv 64 (fe_F cx) -> YK11.getr regs' 25%bv = Z_to_bv 64 (fe_SF cx) ->
  st_ok tfibsegs (Ereg regs' (fe_extra cx ++ [Z_to_bv 64 l])) (fe_ss r [fe_len_atom 46])
    (restrict (w_H W') (YK11.mkst regs' (Z_to_bv 64 r) m' (YK11.seg_rom tfibsegs))).
Proof.
intros cx E ssc W msc md ly S U STKc FP1 regs' ly' S' W' m' md' kc k l r Hb HE Hcore E46 HSc Hmem HARU Hfr ELY HJc HJ
  HARU' HFP Hspc R8 R24 R18 R25.
pose proof (ARU_AR tfibsegs B ly S U W (ms_mem msc) md HARU) as HAR.
pose proof Hcore as (E8 & _ & _ & _ & E24 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (s7_base_sp cx Hb) as (Hal16 & Hceil & H47). unfold LLVMF_STK in Hceil.
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _ & _ & F1 & _ & _ & F4 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hlyc as (_ & _ & _ & _ & _ & ELYc & _).
assert (EF : frame_addr ly 0 (c_fpos cx) = fe_F cx) by (unfold fe_F, frame_addr; rewrite ELY; reflexivity).
destruct (al_frames _ _ LAWS ly S W (unpoison U (ms_mem msc)) md 0 (c_fpos cx) HAR Hfr) as (Hal32 & Happ & _).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U (ms_mem msc)) md 0 (c_fpos cx) HAR Hfr) as (H4096 & Hfc & _).
rewrite EF in Hal32, Happ, H4096, Hfc.
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in Happ, Hfc.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
assert (Hsp0 : 0 <= fe_sp0 cx < 2 ^ 64) by (unfold fe_sp0, spZ; apply bv_unsigned_in_range).
assert (B24 : bv_unsigned (ew E 24) = fe_F cx) by (rewrite E24; apply wz; lia).
assert (B8 : bv_unsigned (ew E 8) = fe_sp0 cx) by (rewrite E8; apply wz; exact Hsp0).
(* the call state's regions *)
assert (Hrg0 := fsw_region_nth E ssc _ 0 (fe_frame_region [fe_len_atom 46]) HSc ltac:(rewrite Hmem; reflexivity)).
assert (Hrg2 := fsw_region_nth E ssc _ 2 (fs_ret_s0_region (-88) 0 fe_sv_chunks) HSc ltac:(rewrite Hmem; reflexivity)).
destruct Hrg0 as (_ & _ & _ & Hch0). destruct Hrg2 as (_ & _ & _ & Hch2).
cbn [YP09.r_base YP09.r_chunks base_val fe_frame_region fs_ret_s0_region] in Hch0, Hch2.
rewrite B24 in Hch0. rewrite B8 in Hch2. cbn [ms_mem restrict] in Hch0, Hch2.
(* bytes kept by the callee: the saved words (above its window), the frame (its footprint is image bytes) *)
assert (KS : forall a, fe_sp0 cx - 88 <= a < fe_sp0 cx ->
  mbyte tfibsegs (mrestrict (w_H W') m') a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem msc)) a).
{ intros a Ha. apply (mbyte_of_aview tfibsegs).
  rewrite <- (fsw_aview_unpoison_high B ly' S' U W' m' md' a HARU') by lia.
  rewrite <- (fsw_aview_unpoison_high B ly S U W (ms_mem msc) md a HARU) by lia.
  apply F1; lia. }
assert (KF : forall a, fe_F cx <= a < fe_F cx + 64 ->
  mbyte tfibsegs (mrestrict (w_H W') m') a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem msc)) a).
{ intros a Ha. apply (mbyte_of_aview tfibsegs).
  assert (Hr : 0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)) by (unfold SHADOW_OFF, kHighMemBeg; lia).
  rewrite <- (aview_at tfibsegs (w_H W') (unpoison U m') m' a) by (exact (unpoison_app B ly' S' U W' m' md' a HARU' (proj1 Hr) (proj2 Hr))).
  rewrite <- (aview_at tfibsegs (w_H W) (unpoison U (ms_mem msc)) (ms_mem msc) a) by (exact (unpoison_app B ly S U W (ms_mem msc) md a HARU (proj1 Hr) (proj2 Hr))).
  apply (F4 0 (c_fpos cx) a Hfr).
  - left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EF, Hfb. lia.
  - intros Hf. apply (frm_img tfibsegs B LAWS ly S W (unpoison U (ms_mem msc)) md 0 (c_fpos cx) a HAR Hfr);
      [rewrite EF, Hfb; lia | exact (HFP a Hf)]. }
assert (EE : forall j, (j < 14)%nat -> ew (Ereg regs' (fe_extra cx ++ [Z_to_bv 64 l])) (32 + j) = ew E (32 + j)).
{ intros j Hj. rewrite (fe_extra_atom cx regs' [Z_to_bv 64 l] j Hj). symmetry. exact (HE j Hj). }
assert (E46' : ew (Ereg regs' (fe_extra cx ++ [Z_to_bv 64 l])) 46 = ew E 46).
{ rewrite E46. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra. reflexivity. }
apply (fe_canon B cx ly' S' U W' m' md' regs' [Z_to_bv 64 l] r [fe_len_atom 46] HARU').
- rewrite Hfrsc. exact Hfr.
- rewrite ELYc. exact ELY.
- exact R8.
- exact R24.
- exact R18.
- exact R25.
- exact Hal16.
- lia.
- exact H47.
- intros a Ha. apply (fsw_apresent_unpoison B ly' S' U W' m' md' a HARU'); [lia|]. apply Hpres. unfold LLVMF_STK. lia.
- unfold fe_sv_chunks in Hch2 |- *. rewrite Forall_map in Hch2 |- *. rewrite Forall_forall in Hch2 |- *.
  intros j Hj. pose proof (Hch2 j Hj) as Hc. apply in_seq in Hj.
  apply (s7_chunk_move E _ _ _ _ _ _ Hc).
  + change (33 + j)%nat with (32 + (1 + j))%nat. apply EE. lia.
  + intros i Hi. apply KS. lia.
- assert (EFL : flag_addr ly 0 (c_fpos cx) = fe_FL cx) by (unfold fe_FL, flag_addr; rewrite ELY; reflexivity).
  destruct (al_flag _ _ LAWS ly S W (unpoison U (ms_mem msc)) md 0 (c_fpos cx) HAR Hfr) as (_ & _ & Hflapp & Hflc).
  rewrite EFL in Hflapp, Hflc. unfold in_app in Hflapp.
  assert (HFL : 0 <= fe_FL cx < 2 ^ 64) by lia.
  apply (s7_rdword_of_val_mem (w_H W') m' (fe_F cx + 56) (fe_FL cx)); [|exact HFL].
  assert (Hc : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem msc)) (fe_F cx)
    (YP09.mkChunk 56 (CVal 8 (SOff 44 0)))) by (inversion Hch0; assumption).
  assert (E44 : ew E 44 = Z_to_bv 64 (fe_FL cx)) by (change 44%nat with (32 + 12)%nat; rewrite (HE 12%nat) by lia; reflexivity).
  pose proof (val_of_chunk_ok tfibsegs E _ (fe_F cx) 56 8 (SOff 44 0) (fe_FL cx) Hc
    ltac:(rewrite fsw_SOff0; exact E44) ltac:(cbn; lia) ltac:(lia)) as Hv.
  intros j Hj. rewrite KF by (cbn in Hj; lia). exact (Hv j Hj).
- apply fe_regions_wf_len_atom.
- constructor; [cbn; lia | constructor].
- constructor; [|constructor].
  assert (Hc : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem msc)) (fe_F cx) (fe_len_atom 46))
    by (inversion Hch0 as [|? ? ? Hl]; inversion Hl; assumption).
  apply (s7_chunk_move E _ _ _ _ _ _ Hc); [exact E46'|]. intros i Hi. apply KF. lia.
Qed.

(* the walk may write the boundary state's regions: the frame and its shadow (its own fake frame), the saved words
   (its stack window) *)
Lemma s7_awr : forall cx E cs lyc Sc fr0,
  fe_regs_core cx E -> ly_F lyc = ly_F (c_ly cx) -> 4096 <= fe_F cx -> fe_F cx + 64 <= alloc_ceiling ->
  awr_ok tfibsegs B E (fe_regions cs) LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx))
    (ablocks B lyc Sc) lyc [(0, c_fpos cx)] fr0.
Proof.
intros cx E cs lyc Sc fr0 (E8 & _ & _ & _ & E24 & E25 & _) ELY HF0 HF1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EF : frame_addr lyc 0 (c_fpos cx) = fe_F cx) by (unfold fe_F, frame_addr; rewrite ELY; reflexivity).
assert (Hsp0 : 0 <= fe_sp0 cx < 2 ^ 64) by (unfold fe_sp0, spZ; apply bv_unsigned_in_range).
unfold fe_regions.
apply (awr_ok_cons_gen tfibsegs B _ _ _ _ _ _ _ _ _ _ _ 24 (fe_F cx)); [reflexivity | rewrite E24; apply wz; lia | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi fe_frame_region] in Ha. left. right. right. right.
  exists 0, (c_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. lia. }
apply (awr_ok_cons_gen tfibsegs B _ _ _ _ _ _ _ _ _ _ _ 25 (fe_SF cx)); [reflexivity | rewrite E25; apply wz | |].
{ unfold fe_SF, shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (fe_F cx) 8). pose proof (Z.div_le_upper_bound (fe_F cx) 8 (2 ^ 61)). lia. }
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi fe_shadow_region] in Ha. left. right. right. right.
  exists 0, (c_fpos cx). split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0 / 8) with 8.
  unfold fe_SF in Ha. lia. }
apply (awr_ok_cons_stack tfibsegs B _ _ _ _ _ _ _ _ _ _ _ 8); [reflexivity | rewrite E8; apply wz; exact Hsp0 | cbn; unfold LLVMF_STK; lia | cbn; lia |].
apply awr_ok_nil.
Qed.

(* the callee's chain: the entry's, pushed by the entry's frame record when the entry sp is below ly_top - 16 *)
Lemma s7_chain : forall cx ly' (rd' : reader) sp',
  fe_base B cx -> ly_top ly' = ly_top (c_ly cx) ->
  (forall a, fe_sp0 cx <= a < 2 ^ 64 -> rd' a = aview tfibsegs (w_H (c_W cx)) (c_mem cx) a) ->
  rdword rd' (fe_sp0 cx - 8) = Some RA_LLVMF -> rdword rd' (fe_sp0 cx - 16) = Some (s0Z (c_regs cx)) ->
  sp' + 16 <= fe_sp0 cx ->
  exists ch, achain ly' rd' sp' (fe_sp0 cx) ch /\ (spine ch = [] \/ spine ch = [FS_RA_LLVMF]).
Proof.
intros cx ly' rd' sp' Hb Htop Hk H8 H16 Hsp'.
pose proof Hb as ((HAP & _) & _).
pose proof HAP as (_ & _ & _ & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof (achain_ly_top _ ly' _ _ _ _ Htop Hch) as Hch'.
destruct (Z_lt_le_dec (fe_sp0 cx) (ly_top ly' - 16)) as [Hlt | Hge].
- exists [(fe_sp0 cx, RA_LLVMF, s0Z (c_regs cx))]. split; [|right; reflexivity].
  assert (Hm8 : fe_sp0 cx mod 8 = 0).
  { unfold fe_sp0. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia].
    destruct Hal16 as (c & Hc). exists (2 * c). lia. }
  assert (Hc8 : alloc_ceiling <= fe_sp0 cx) by (unfold fe_sp0, LLVMF_STK in *; lia).
  assert (Ht64 : ly_top ly' <= 2 ^ 64) by (rewrite Htop; lia).
  exact (achain_push ly' _ rd' (fe_sp0 cx) (s0Z (c_regs cx)) RA_LLVMF [] sp' Hch' Ht64 Hk H8 H16
    ltac:(unfold RA_LLVMF; lia) Hc8 Hm8 Hlt Hsp').
- exists []. split; [|left; reflexivity]. left. split; [right; left; exact Hge | reflexivity].
Qed.

(* the read-only view at any state the walk's journal reaches (its footprint is the statics, never read-only bytes) *)
Lemma s7_arodata : forall cx ly' S' (W' : world tfibsegs) m' md' k',
  fe_base B cx ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly' S' W' m' md' k' ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') m').
Proof.
intros cx ly' S' W' m' md' k' Hb HJ a Hro Ho He.
pose proof Hb as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro0 & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (s7_roP a Hro) as (Hi & Hnf).
rewrite (F3 a Hi Ho He Hnf (fp_spares_closed FS_PSTAT_FP a s7_pstat_closed)).
exact (Hro0 a Hro Ho He).
Qed.
(* ... read on the machine's memory: read-only bytes are image bytes, below the shadow *)
Lemma s7_arodata_m : forall ly S U (W : world tfibsegs) m md,
  ARU tfibsegs B ly S U W m md -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U m)) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m).
Proof.
intros ly S U W m md HARU H a Hro Ho He.
pose proof (fs_segs_img a (proj1 (s7_roP a Hro))) as Hl. unfold FS_IMG_END in Hl.
rewrite <- (aview_at tfibsegs (w_H W) (unpoison U m) m a); [exact (H a Hro Ho He)|].
apply (unpoison_app B ly S U W m md a HARU); unfold SHADOW_OFF; lia.
Qed.
(* the reader cells (rom view, canary cells) at any ARU state of the walk, from the image facts *)
Lemma s7_rd_cells : forall ly S U (W : world tfibsegs) m md,
  ARU tfibsegs B ly S U W m md -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U m)) ->
  rd_cells tfibsegs W m.
Proof.
intros ly S U W m md HARU HRO.
destruct (proj2 IMG ly S W (unpoison U m) md (ARU_AR tfibsegs B ly S U W m md HARU) HRO)
  as (Hrom & (cval & Hg & Hc & Hcr) & _).
assert (MB : forall a, 0 <= a < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W) m) a = mbyte tfibsegs (mrestrict (w_H W) (unpoison U m)) a)
  by (intros a Ha; symmetry; apply (mbyte_unpoison_app B ly S U W m md a HARU); unfold SHADOW_OFF in *; lia).
split.
- intros a (sg & Hsg & Hw & Ha). pose proof (fs_segs_img a (ex_intro _ sg (conj Hsg Ha))) as Hl. unfold FS_IMG_END in Hl.
  rewrite <- (aview_at tfibsegs (w_H W) (unpoison U m) m a); [apply Hrom; exists sg; split; [exact Hsg | split; [exact Hw | exact Ha]]|].
  apply (unpoison_app B ly S U W m md a HARU); unfold SHADOW_OFF; lia.
- exists cval. split; [|split; [|exact Hcr]]; intros j Hj; rewrite MB.
  + exact (Hg j Hj).
  + unfold FS_GOT_canary, SHADOW_OFF. lia.
  + exact (Hc j Hj).
  + unfold FS_canary, SHADOW_OFF. lia.
Qed.

(* bytes read as numbers and back *)
Lemma s7_zs_bz : forall (W : world tfibsegs) m p bs, zbytes_at tfibsegs W m p bs -> HState.zs (HState.bz bs) = bs.
Proof.
intros W m p bs Hz. unfold HState.zs, HState.bz. rewrite map_map. rewrite <- (map_id bs) at 2. apply map_ext_in.
intros x Hx. destruct (In_nth bs x 0 Hx) as (j & Hj & Ej). destruct (Hz j Hj) as (_ & Hr). rewrite Ej in Hr.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.

(* the boundary registers after a program call that keeps the callee-saved registers *)
Definition s7_cs_atoms : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma s7_regs_ret : forall cx E (regsc regs' : bvmap 5 word) xs,
  fe_regs_core cx E ->
  (forall r : nat, In r s7_cs_atoms -> YK11.getr regsc (Z_to_bv 5 (Z.of_nat r)) = ew E r) ->
  aregs_preserved regsc regs' ->
  fe_regs_core cx (Ereg regs' (fe_extra cx ++ xs)) /\
  (forall r : nat, In r s7_cs_atoms -> ew (Ereg regs' (fe_extra cx ++ xs)) r = ew E r).
Proof.
intros cx E regsc regs' xs Hcore HR HP.
assert (K : forall r : nat, In r s7_cs_atoms -> ew (Ereg regs' (fe_extra cx ++ xs)) r = ew E r).
{ intros r Hr. rewrite <- (HR r Hr).
  assert (Hr32 : Z.of_nat r = bv_unsigned (Z_to_bv 5 (Z.of_nat r))).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small; [reflexivity|].
    unfold s7_cs_atoms in Hr. cbn in Hr. repeat destruct Hr as [<-|Hr]; [..|destruct Hr]; cbn; lia. }
  rewrite (ew_Ereg_nat regs' _ r (Z_to_bv 5 (Z.of_nat r)) Hr32).
  pose proof (HP (Z.of_nat r)) as Hp. apply Hp.
  unfold s7_cs_atoms in Hr. cbn in Hr. unfold acallee_saved.
  repeat destruct Hr as [<-|Hr]; [..|destruct Hr]; cbn; lia. }
split; [|exact K].
unfold fe_regs_core in *. unfold s7_cs_atoms in K.
repeat rewrite K by (cbn; tauto). exact Hcore.
Qed.

(* the C7 invariant from its parts *)
Lemma s7_inv7 : forall cx E' k' ly' S' U (W' : world tfibsegs) ms' md' text body l cnt7,
  fe_regs_core cx E' ->
  ew E' 19 = Z_to_bv 64 (fe_n cx) -> ew E' 20 = Z_to_bv 64 (fe_F cx + 32) -> ew E' 21 = Z_to_bv 64 text ->
  ew E' 22 = Z_to_bv 64 body -> ew E' 23 = Z_to_bv 64 (c_live cx) -> ew E' 46 = Z_to_bv 64 l ->
  U = fe_body_U body ->
  Permutation (ablocks B ly' S') (fe_body_blocks cx body ++ (text, fe_n cx + 1) :: ablocks B (c_ly cx) (c_S cx)) ->
  fe_n cx <= 3 * 2 ^ 20 ->
  s7_mf cx ly' S' U W' (ms_mem ms') text body l (fe_live6 cx body) cnt7 ->
  c_cnt cx + 4 <= cnt7 <= c_cnt cx + 4 + (if body =? 0 then 0 else CRT_ALLOCS) ->
  0 <= k' <= EV_check_no_overread + 1 + EV_preset_base64_decode + EV_check_as_written + EV_check_round_trip ->
  same_io (c_md cx) md' -> blocks_bytes S' <= blocks_bytes (c_S cx) + 2 ^ 32 ->
  INV_C7 B cx E' k' ly' S' U W' ms' md'.
Proof.
intros cx E' k' ly' S' U W' ms' md' text body l cnt7 Hcore E19 E20 E21 E22 E23 E46 EU Hperm Hn (Hans & Hcs & Hpl & Hst)
  Hcnt Hk Hio Hbb.
exists text, body, l. split; [|split; [|exists cnt7; split; [exact Hst | exact Hcnt]]].
- split; [exact EU|]. split; [exact Hperm|]. split; [exact Hans|]. split; [exact Hcore|]. split; [exact Hn|].
  repeat (split; [assumption|]). exact Hcs.
- split; [exact Hk|]. split; [exact Hio|]. split; [exact Hpl | exact Hbb].
Qed.

(* a saved word of the prologue (atom 33 + j at s0 - 8 (j + 1)), read on the unpoisoned memory of a boundary state *)
Lemma s7_saved_word : forall cx E cs ss (W : world tfibsegs) ms ly S U md j v,
  fe_base B cx -> fe_regs_core cx E -> ss_mem ss = fe_regions cs ->
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> ARU tfibsegs B ly S U W (ms_mem ms) md ->
  (j < 11)%nat -> ew E (33 + j) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview tfibsegs (w_H W) (unpoison U (ms_mem ms))) (fe_sp0 cx - 8 * (Z.of_nat j + 1)) = Some v.
Proof.
intros cx E cs ss W ms ly S U md j v Hb Hcore Hmem HS HARU Hj Ev Hv.
pose proof Hcore as (E8 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (s7_base_sp cx Hb) as (Hal16 & Hceil & H47). unfold LLVMF_STK in Hceil.
assert (Hsp0 : 0 <= fe_sp0 cx < 2 ^ 64) by (unfold fe_sp0, spZ; apply bv_unsigned_in_range).
assert (B8 : bv_unsigned (ew E 8) = fe_sp0 cx) by (rewrite E8; apply wz; exact Hsp0).
assert (Hrg2 := fsw_region_nth E ss _ 2 (fs_ret_s0_region (-88) 0 fe_sv_chunks) HS ltac:(rewrite Hmem; reflexivity)).
destruct Hrg2 as (_ & _ & _ & Hch2).
cbn [YP09.r_base YP09.r_chunks base_val fs_ret_s0_region] in Hch2. rewrite B8 in Hch2. cbn [ms_mem restrict] in Hch2.
assert (Hc : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (fe_sp0 cx)
  (YP09.mkChunk (- 8 * (Z.of_nat j + 1)) (CVal 8 (SOff (33 + j) 0)))).
{ rewrite Forall_forall in Hch2. apply Hch2. unfold fe_sv_chunks. apply in_map_iff. exists j. split; [reflexivity|].
  apply in_seq. lia. }
pose proof (val_of_chunk_ok tfibsegs E _ (fe_sp0 cx) _ 8 (SOff (33 + j) 0) v Hc ltac:(rewrite fsw_SOff0; exact Ev)
  ltac:(cbn; lia) ltac:(lia)) as Hval.
apply (s7_rdword_of_val_mem (w_H W) (unpoison U (ms_mem ms)) _ v); [|exact Hv].
replace (fe_sp0 cx - 8 * (Z.of_nat j + 1)) with (fe_sp0 cx + - 8 * (Z.of_nat j + 1)) by lia.
intros i Hi. rewrite (mbyte_unpoison_app B ly S U W (ms_mem ms) md _ HARU); [exact (Hval i Hi) | |]; cbn in Hi; lia.
Qed.

Ltac s7_sreg HS :=
  etransitivity; [exact (st_ok_reg tfibsegs _ _ _ _ HS)|];
  lazymatch goal with |- sv_denot _ (sr_get ?x ?y) = _ =>
    let v := eval vm_compute in (sr_get x y) in change (sr_get x y) with v end.

Lemma s7_soff : forall E n v c, bv_unsigned (ew E n) = v -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c Hn Hr. apply bv_eq. rewrite denot_SOff, Hn, (wz (v + c) Hr). apply zcanon_small. lia.
Qed.
(* what the crt call at 0x81158 and the crc call at 0x8116c need of their callees' stack bounds, over the definitions
   (lib/B/FSH_Base.v STK_check_round_trip / STK_check_reject_clean, YCfn's LLVMF_STK), not their values:
   YCbq.afn_pre_at's `0 <= STK1` and `STK1 - o <= LLVMF_STK` at o = fe_sp1 - fe_sp0 >= -127 (the re-aligned sp), the
   same bound for the callee's window (above every heap byte) and for fsw_ajournal_sub4's window inclusion *)
Lemma s7_stk_crt : 0 <= STK_check_round_trip /\ STK_check_round_trip + 127 <= LLVMF_STK.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma s7_stk_crc : 0 <= STK_check_reject_clean /\ STK_check_reject_clean + 127 <= LLVMF_STK.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma s7_atom46 : forall cx regs' l, ew (Ereg regs' (fe_extra cx ++ [Z_to_bv 64 l])) 46 = Z_to_bv 64 l.
Proof. intros cx regs' l. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.
Lemma s7_same_io_wvb : forall md0 md X, same_io md0 md -> same_io md0 (with_vm_backing (m_vm_lazy md) X md).
Proof.
intros md0 md X H. apply (same_io_trans _ md); [exact H|].
apply same_io_materialized. apply same_but_materialized_wvb_any.
Qed.

Lemma fe_seg7 : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss RA_crc [fe_len_atom 46]) (INV_C7 B) ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_caw [fe_len_atom 46]) (INV_C6 B).
Proof.
intros POST Hnext cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (text & body & l & HAD & HCOM & HST).
pose proof HAD as (EU & Hperm & Hans & Hcore & Hn3 & E19 & E20 & E21 & E22 & E23 & E46 & Hcstr).
pose proof Hcore as (E8 & E9 & E2 & E18 & E24 & E25 & E3 & E4 & E26 & E27).
pose proof HCOM as (Hk & Hio & Hpl & Hbb).
pose proof Hb as (PRE & Hst0 & Hc0 & Hc1 & Hl0).
pose proof PRE as (HAP & Hra0 & Hp0 & Hn0 & Hpn & Hpl0 & Hg0 & Hfrs0 & Hnev0 & Hbb0 & Hro0 & _).
pose proof HAP as (_ & _ & _ & Hgp & Htp & Hstk0 & _).
pose proof Hstk0 as (_ & _ & _ & _ & _ & _ & _ & Htop0 & _).
pose proof (s7_base_sp cx Hb) as (Hal16 & Hceil & H47). unfold LLVMF_STK in Hceil.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & ELY3 & _ & _ & ETOP3 & _).
assert (Hfr3 : In (0, c_fpos cx) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (EF3 : frame_addr ly3 0 (c_fpos cx) = fe_F cx) by (unfold fe_F, frame_addr; rewrite ELY3; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 _ md3 0 (c_fpos cx) HAR3 Hfr3) as (HF4096 & HFc & _).
rewrite EF3 in HF4096, HFc. change (fs_frame_bytes 0) with 64 in HFc.
assert (Hsp0 : 0 <= fe_sp0 cx < 2 ^ 64) by (unfold fe_sp0, spZ; apply bv_unsigned_in_range).
assert (Hsp1 : fe_sp0 cx - 127 <= fe_sp1 cx <= fe_sp0 cx - 96 /\ fe_sp1 cx mod 32 = 0).
{ unfold fe_sp1. pose proof (Z.div_mod (fe_sp0 cx - 96) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (fe_sp0 cx - 96) 32 ltac:(lia)).
  split; [lia|]. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
assert (Hfrl : Z.of_nat (length (frames S3)) <= FRL_CHECK) by (rewrite Hfrs3, Hfrs0; cbn; unfold FRL_CHECK; lia).
assert (Htext : In (text, fe_n cx + 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
assert (Hpay : c_n cx = 0 \/ In (c_p cx, c_n cx) (ablocks B ly3 S3)).
{ destruct Hpn as [(H0 & _) | (_ & Hin)]; [left; exact H0|]. right.
  apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. right. exact Hin. }
assert (Hmf3 : s7_mf cx ly3 S3 U3 W3 (ms_mem ms3) text body l (fe_live6 cx body) (c_cnt cx + 4))
  by (split; [exact Hans | split; [exact Hcstr | split; [exact Hpl | exact HST]]]).
assert (Hkb : 0 <= k <= 19) by (unfold EV_check_no_overread, EV_preset_base64_decode, EV_check_as_written in Hk; lia).
assert (Hbb3 : blocks_bytes S3 <= blocks_bytes (c_S cx) + 2 ^ 32) by exact Hbb.
pose proof HARU as HARU3.
pose proof (s7_tb_len cx Hpl0) as Htblen.
(* the text as bytes *)
set (tb := firstn (Z.to_nat (fe_n cx)) (c_pl cx)).
assert (Etb : HState.zs tb = fe_tb cx) by (unfold tb, HState.zs, fe_tb, fe_bytes; rewrite firstn_map; reflexivity).
(* s4 is &len: the frame atom + 32 *)
assert (R20 : YK11.getr (ms_regs (restrict (w_H W3) ms3)) 20%bv = sv_denot E (SOff 24 32)).
{ rewrite (st_ok_reg tfibsegs E _ _ 20%bv HS). change (sr_get (ss_regs (fe_ss RA_caw [fe_len_atom 46])) 20%bv) with (SOff 20 0).
  rewrite fsw_SOff0, E20. symmetry. apply s7_soff; [rewrite E24; apply wz|]; lia. }
pose proof (YI08.st_ok_set_reg tfibsegs E _ _ 20%bv (SOff 24 32) HS ltac:(discriminate) R20) as HS1.
clear R20 HS.
destruct (Z.eq_dec body 0) as [Hb0 | Hbn0].
- (* body = 0: check_reject_clean (0, len, live) *)
  destruct Hans as [(Hdec & _ & El) | (bs & mm & _ & Hbn & _)]; [|exfalso; exact (Hbn Hb0)].
  subst body.
  assert (EU0 : U3 = []) by (rewrite EU; reflexivity).
  assert (R22 : YK11.getr (ms_regs (restrict (w_H W3) ms3)) 22%bv = sv_denot E (SLit 0)).
  { etransitivity; [exact (st_ok_reg tfibsegs _ _ _ 22%bv HS1)|].
    lazymatch goal with |- sv_denot _ (sr_get ?x ?y) = _ =>
      let v := eval vm_compute in (sr_get x y) in change (sr_get x y) with v end.
    rewrite fsw_SOff0, E22. reflexivity. }
  pose proof (YI08.st_ok_set_reg tfibsegs E _ _ 22%bv (SLit 0) HS1 ltac:(discriminate) R22) as HS2.
  clear R22 HS1.
  fsw_aj_run_toU entry_tbl_ok HS2 HJ HARU A_check_reject_clean.
  { exact (s7_awr cx E _ ly3 S3 _ Hcore ELY3 HF4096 HFc). }
  assert (HF' : frame_of E (fe_regions [fe_len_atom 46]) (ms_mem ms3) (ms_mem ms)) by exact HF.
  pose proof (s7_mf_keep cx ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 text 0 l _ _ Hpl0 HARU3 Htext Hpay
    (s7_keep_frame cx E [fe_len_atom 46] ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 Hb Hcore HARU3 Hfr3 ELY3 HF') HG Hmf3)
    as Hmfc.
  clear HF HFr HG HF'.
  lazymatch type of HS2 with st_ok _ _ ?s _ => set (ssc := s) in HS2 end.
  pose proof Hmfc as (Hansc & Hcstrc & Hplc & Hstc).
  pose proof HARU as (HARc & OKc & POc).
  (* the registers at the call *)
  assert (RG : forall r : nat, In r s7_cs_atoms -> YK11.getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = ew E r).
  { intros r Hr. unfold s7_cs_atoms in Hr. cbn in Hr.
    repeat destruct Hr as [<-|Hr]; [..|destruct Hr]; s7_sreg HS2;
      first [ apply fsw_SOff0 | rewrite E20; apply s7_soff; [rewrite E24; apply wz; lia | lia]
            | rewrite E22; reflexivity ]. }
  assert (RA1 : YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 RA_crc) by (s7_sreg HS2; reflexivity).
  assert (R10 : YK11.getr (ms_regs ms) 10%bv = w64 0) by (s7_sreg HS2; reflexivity).
  assert (R11 : YK11.getr (ms_regs ms) 11%bv = w64 SIZE_MAXZ) by (s7_sreg HS2; rewrite fsw_SOff0, E46, El; reflexivity).
  assert (R12 : YK11.getr (ms_regs ms) 12%bv = w64 (c_live cx)) by (s7_sreg HS2; rewrite fsw_SOff0, E23; reflexivity).
  assert (R2 : YK11.getr (ms_regs ms) 2%bv = ew E 2) by exact (RG 2%nat ltac:(cbn; tauto)).
  assert (R3 : YK11.getr (ms_regs ms) 3%bv = ew E 3) by exact (RG 3%nat ltac:(cbn; tauto)).
  assert (R4 : YK11.getr (ms_regs ms) 4%bv = ew E 4) by exact (RG 4%nat ltac:(cbn; tauto)).
  assert (R8 : YK11.getr (ms_regs ms) 8%bv = ew E 8) by exact (RG 8%nat ltac:(cbn; tauto)).
  assert (Rsp : spZ (ms_regs ms) = fe_sp1 cx).
  { unfold spZ. rewrite R2, E2. apply wz. lia. }
  assert (Rs0 : s0Z (ms_regs ms) = fe_sp0 cx).
  { unfold s0Z. rewrite R8, E8. apply wz. exact Hsp0. }
  (* the callee's chain *)
  assert (Hck : forall a, fe_sp0 cx <= a < 2 ^ 64 ->
    aview tfibsegs (w_H W3) (unpoison U3 (ms_mem ms)) a = aview tfibsegs (w_H (c_W cx)) (c_mem cx) a).
  { intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). apply F1; lia. }
  assert (H8w : rdword (aview tfibsegs (w_H W3) (unpoison U3 (ms_mem ms))) (fe_sp0 cx - 8) = Some RA_LLVMF).
  { rewrite <- Hra0. unfold raZ.
    apply (s7_saved_word cx E [fe_len_atom 46] ssc W3 ms ly3 S3 U3 _ 0 _ Hb Hcore eq_refl HS2 HARU ltac:(lia));
      [| apply bv_unsigned_in_range].
    rewrite Z_to_bv_bv_unsigned. change (33 + 0)%nat with (32 + 1)%nat. rewrite (HE 1%nat) by lia. reflexivity. }
  assert (H16w : rdword (aview tfibsegs (w_H W3) (unpoison U3 (ms_mem ms))) (fe_sp0 cx - 16) = Some (s0Z (c_regs cx))).
  { unfold s0Z.
    apply (s7_saved_word cx E [fe_len_atom 46] ssc W3 ms ly3 S3 U3 _ 1 _ Hb Hcore eq_refl HS2 HARU ltac:(lia));
      [| apply bv_unsigned_in_range].
    rewrite Z_to_bv_bv_unsigned. change (33 + 1)%nat with (32 + 2)%nat. rewrite (HE 2%nat) by lia. reflexivity. }
  destruct (s7_chain cx ly3 (aview tfibsegs (w_H W3) (unpoison U3 (ms_mem ms))) (spZ (ms_regs ms)) Hb ETOP3 Hck H8w H16w
    ltac:(lia)) as (ch & Hch & _).
  (* check_reject_clean's premises *)
  assert (HPRE : fpreU tfibsegs B STK_check_reject_clean ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms)
    (with_vm_backing (m_vm_lazy md3) mat md3) ch).
  { split; [split; [|split; [exact OKc | exact POc]]|].
    - apply (afn_pre_at tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP _ _ _ _ _ _ ly3 S3 W3 _ _ k (ms_regs ms)
        STK_check_reject_clean (fe_sp1 cx - fe_sp0 cx) ch HJ).
      + lia.
      + rewrite Zminus_mod. rewrite Hal16. destruct Hsp1 as (_ & Hs32).
        assert (fe_sp1 cx mod 16 = 0) as -> by (rewrite Z.mod_divide in Hs32 |- * by lia; destruct Hs32 as (c & Hc); exists (2 * c); lia).
        reflexivity.
      + lia.
      + pose proof s7_stk_crc. lia.
      + pose proof s7_stk_crc. unfold LLVMF_STK in *. lia.
      + rewrite RA1. reflexivity.
      + unfold raZ. rewrite RA1. rewrite wz; unfold RA_crc; lia.
      + rewrite R3, E3. exact Hgp.
      + rewrite R4, E4. exact Htp.
      + rewrite Rs0. exact Hch.
    - exact (s7_arodata_m ly3 S3 U3 W3 (ms_mem ms) _ HARU (s7_arodata cx ly3 S3 W3 _ _ k Hb HJ)). }
  assert (Hheads : fs_heads B ly3 S3 U3) by (rewrite EU0; intros r []).
  replace (fe_live6 cx 0) with (c_live cx) in Hstc by (unfold fe_live6; cbn; lia).
  destruct Hstc as (peak & Hglob).
  assert (Hcall := en_reject_clean ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) _ ch (c_live cx) peak (c_cnt cx + 4) SIZE_MAXZ
    HPRE Hheads Hglob R10 R11 R12).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ssc ms HS2 eq_refl).
  eapply SRr_bind; [exact Hcall|]. cbv beta.
  intros W' c' Hwle Hpost.
  destruct Hpost as (ly' & S' & regs' & m' & md' & -> & HJc & OK' & PO' & HP & Hab' & Hglob').
  rewrite RA1.
  assert (HFP0 : forall a, inFP [] a -> in_img tfibsegs a) by (intros a Hf; destruct (inFP_nil a Hf)).
  assert (HJ' := fsw_ajournal_sub4 B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms)) _ k STK_check_reject_clean (spZ (ms_regs ms)) [] []
    ly' S' W' (unpoison U3 m') md' 0 HJ HJc
    ltac:(rewrite Rsp; pose proof s7_stk_crc; unfold LLVMF_STK in *; lia) ltac:(rewrite Rsp; lia)
    (fun a Hf => False_ind _ (inFP_nil a Hf))).
  cbn [app] in HJ'.
  assert (HARU' : ARU tfibsegs B ly' S' U3 W' m' md') by (split; [exact (proj1 HJ') | split; [exact OK' | exact PO']]).
  assert (Hinc : forall x, In x (ablocks B ly3 S3) -> In x (ablocks B ly' S')) by (intros x Hx; rewrite Hab'; exact Hx).
  pose proof (s7_mf_call cx STK_check_reject_clean (spZ (ms_regs ms)) [] ly3 S3 U3 W3 (ms_mem ms) _ ly' S' W' m' md'
    0 text 0 l _ _ (c_live cx) (c_cnt cx + 4) Hpl0 HARU HJc OK' PO' HFP0 Hinc Htext Hpay EU Hmfc
    (ex_intro _ peak Hglob')) as Hmf'.
  destruct (s7_regs_ret cx E (ms_regs ms) regs' [Z_to_bv 64 l] Hcore RG HP) as (Hcore' & RK).
  pose proof Hcore' as (E8' & E9' & E2' & E18' & E24' & E25' & _).
  assert (HSr := s7_st_ret cx E ssc W3 ms _ ly3 S3 U3 STK_check_reject_clean [] regs' ly' S' W' m' md'
    0 (k + 0) l RA_crc Hb HE Hcore E46 HS2 eq_refl HARU Hfr3 ELY3 HJc HJ' HARU'
    HFP0 ltac:(rewrite Rsp; lia)
    ltac:(rewrite <- (ew_Ereg_nat regs' (fe_extra cx ++ [Z_to_bv 64 l]) 8 8%bv eq_refl); exact E8')
    ltac:(rewrite <- (ew_Ereg_nat regs' (fe_extra cx ++ [Z_to_bv 64 l]) 24 24%bv eq_refl); exact E24')
    ltac:(rewrite <- (ew_Ereg_nat regs' (fe_extra cx ++ [Z_to_bv 64 l]) 18 18%bv eq_refl); exact E18')
    ltac:(rewrite <- (ew_Ereg_nat regs' (fe_extra cx ++ [Z_to_bv 64 l]) 25 25%bv eq_refl); exact E25')).
  assert (Hio' : same_io (c_md cx) md').
  { apply (same_io_trans _ (with_vm_backing (m_vm_lazy md3) mat md3)); [exact (s7_same_io_wvb _ md3 mat Hio)|].
    pose proof HJc as (_ & _ & _ & _ & Hos & _).
    exact (aos_step_closed_same_io [] _ _ (fun H => match H with ex_intro _ r (conj Hr _) => Hr end) Hos). }
  assert (Hbb' : blocks_bytes S' <= blocks_bytes (c_S cx) + 2 ^ 32).
  { rewrite (blocks_bytes_bsum B ly' S'), Hab', <- (blocks_bytes_bsum B ly3 S3). exact Hbb3. }
  apply (Hnext cx _ (k + 0) ly' S' U3 W' (YK11.mkst regs' (Z_to_bv 64 RA_crc) m' (YK11.seg_rom tfibsegs)) md' Hb
    (fe_E_Ereg cx regs' [Z_to_bv 64 l]) HJ' HARU'); [|exact HSr].
  apply (s7_inv7 cx _ _ ly' S' U3 W' _ md' text 0 l (c_cnt cx + 4) Hcore').
  + rewrite (RK 19%nat ltac:(cbn; tauto)). exact E19.
  + rewrite (RK 20%nat ltac:(cbn; tauto)). exact E20.
  + rewrite (RK 21%nat ltac:(cbn; tauto)). exact E21.
  + rewrite (RK 22%nat ltac:(cbn; tauto)). exact E22.
  + rewrite (RK 23%nat ltac:(cbn; tauto)). exact E23.
  + apply s7_atom46.
  + exact EU.
  + rewrite Hab'. exact Hperm.
  + exact Hn3.
  + replace (fe_live6 cx 0) with (c_live cx) by (unfold fe_live6; cbn; lia). exact Hmf'.
  + cbn. lia.
  + unfold EV_check_no_overread, EV_preset_base64_decode, EV_check_as_written, EV_check_round_trip. lia.
  + exact Hio'.
  + exact Hbb'.
- (* body <> 0: check_round_trip (text, body, len) *)
  destruct Hans as [(_ & Hb0 & _) | (bs & mm & Hdec & _ & El & Hsrc & Hrb & Hlm & HUin)]; [exfalso; exact (Hbn0 Hb0)|].
  pose proof Hsrc as (Hzb & Hb4096 & Hbcl & _).
  pose proof Hrb as (Hrbin & Hrbmod & Hrbpos & _).
  assert (EU1 : U3 = [(body - HEAD, HEAD)]) by (rewrite EU; unfold fe_body_U; destruct (Z.eqb_spec body 0); [lia | reflexivity]).
  assert (HS2 := st_ok_add_fact tfibsegs E _ _ 22%nat (mkAF 1 (2 ^ 47) 0) HS1).
  assert (B22 : bv_unsigned (ew E 22) = body) by (rewrite E22; apply wz; lia).
  specialize (HS2 ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite B22; rewrite Z.pow_0_r, Z.mod_1_r; lia)).
  clear HS1.
  fsw_aj_run_toU entry_tbl_ok HS2 HJ HARU A_check_round_trip.
  { exact (s7_awr cx E _ ly3 S3 _ Hcore ELY3 HF4096 HFc). }
  assert (HF' : frame_of E (fe_regions [fe_len_atom 46]) (ms_mem ms3) (ms_mem ms)) by exact HF.
  pose proof (s7_mf_keep cx ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 text body l _ _ Hpl0 HARU3 Htext Hpay
    (s7_keep_frame cx E [fe_len_atom 46] ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 Hb Hcore HARU3 Hfr3 ELY3 HF') HG Hmf3)
    as Hmfc.
  clear HF HFr HG HF'.
  lazymatch type of HS2 with st_ok _ _ ?s _ => set (ssc := s) in HS2 end.
  pose proof Hmfc as (Hansc & Hcstrc & Hplc & Hstc).
  pose proof HARU as (HARc & OKc & POc).
  (* the registers at the call *)
  assert (RG : forall r : nat, In r s7_cs_atoms -> YK11.getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = ew E r).
  { intros r Hr. unfold s7_cs_atoms in Hr. cbn in Hr.
    repeat destruct Hr as [<-|Hr]; [..|destruct Hr]; s7_sreg HS2;
      first [ apply fsw_SOff0 | rewrite E20; apply s7_soff; [rewrite E24; apply wz; lia | lia] ]. }
  assert (RA1 : YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 RA_crt) by (s7_sreg HS2; reflexivity).
  assert (R10 : YK11.getr (ms_regs ms) 10%bv = w64 text) by (s7_sreg HS2; rewrite fsw_SOff0; exact E21).
  assert (R11 : YK11.getr (ms_regs ms) 11%bv = w64 body) by (s7_sreg HS2; rewrite fsw_SOff0; exact E22).
  assert (R12 : YK11.getr (ms_regs ms) 12%bv = w64 (Z.of_nat (length bs))) by (s7_sreg HS2; rewrite fsw_SOff0, E46, El; reflexivity).
  assert (R2 : YK11.getr (ms_regs ms) 2%bv = ew E 2) by exact (RG 2%nat ltac:(cbn; tauto)).
  assert (R3 : YK11.getr (ms_regs ms) 3%bv = ew E 3) by exact (RG 3%nat ltac:(cbn; tauto)).
  assert (R4 : YK11.getr (ms_regs ms) 4%bv = ew E 4) by exact (RG 4%nat ltac:(cbn; tauto)).
  assert (R8 : YK11.getr (ms_regs ms) 8%bv = ew E 8) by exact (RG 8%nat ltac:(cbn; tauto)).
  assert (Rsp : spZ (ms_regs ms) = fe_sp1 cx).
  { unfold spZ. rewrite R2, E2. apply wz. lia. }
  assert (Rs0 : s0Z (ms_regs ms) = fe_sp0 cx).
  { unfold s0Z. rewrite R8, E8. apply wz. exact Hsp0. }
  (* the callee's chain *)
  assert (Hck : forall a, fe_sp0 cx <= a < 2 ^ 64 ->
    aview tfibsegs (w_H W3) (unpoison U3 (ms_mem ms)) a = aview tfibsegs (w_H (c_W cx)) (c_mem cx) a).
  { intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). apply F1; lia. }
  assert (H8w : rdword (aview tfibsegs (w_H W3) (unpoison U3 (ms_mem ms))) (fe_sp0 cx - 8) = Some RA_LLVMF).
  { rewrite <- Hra0. unfold raZ.
    apply (s7_saved_word cx E [fe_len_atom 46] ssc W3 ms ly3 S3 U3 _ 0 _ Hb Hcore eq_refl HS2 HARU ltac:(lia));
      [| apply bv_unsigned_in_range].
    rewrite Z_to_bv_bv_unsigned. change (33 + 0)%nat with (32 + 1)%nat. rewrite (HE 1%nat) by lia. reflexivity. }
  assert (H16w : rdword (aview tfibsegs (w_H W3) (unpoison U3 (ms_mem ms))) (fe_sp0 cx - 16) = Some (s0Z (c_regs cx))).
  { unfold s0Z.
    apply (s7_saved_word cx E [fe_len_atom 46] ssc W3 ms ly3 S3 U3 _ 1 _ Hb Hcore eq_refl HS2 HARU ltac:(lia));
      [| apply bv_unsigned_in_range].
    rewrite Z_to_bv_bv_unsigned. change (33 + 1)%nat with (32 + 2)%nat. rewrite (HE 2%nat) by lia. reflexivity. }
  destruct (s7_chain cx ly3 (aview tfibsegs (w_H W3) (unpoison U3 (ms_mem ms))) (spZ (ms_regs ms)) Hb ETOP3 Hck H8w H16w
    ltac:(lia)) as (ch & Hch & _).
  (* check_round_trip's premises *)
  assert (HPRE : fpreU tfibsegs B STK_check_round_trip ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms)
    (with_vm_backing (m_vm_lazy md3) mat md3) ch).
  { split; [split; [|split; [exact OKc | exact POc]]|].
    - apply (afn_pre_at tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP _ _ _ _ _ _ ly3 S3 W3 _ _ k (ms_regs ms)
        STK_check_round_trip (fe_sp1 cx - fe_sp0 cx) ch HJ).
      + lia.
      + rewrite Zminus_mod. rewrite Hal16. destruct Hsp1 as (_ & Hs32).
        assert (fe_sp1 cx mod 16 = 0) as -> by (rewrite Z.mod_divide in Hs32 |- * by lia; destruct Hs32 as (c & Hc); exists (2 * c); lia).
        reflexivity.
      + lia.
      + pose proof s7_stk_crt. lia.
      + pose proof s7_stk_crt. unfold LLVMF_STK in *. lia.
      + rewrite RA1. reflexivity.
      + unfold raZ. rewrite RA1. rewrite wz; unfold RA_crt; lia.
      + rewrite R3, E3. exact Hgp.
      + rewrite R4, E4. exact Htp.
      + rewrite Rs0. exact Hch.
    - exact (s7_arodata_m ly3 S3 U3 W3 (ms_mem ms) _ HARU (s7_arodata cx ly3 S3 W3 _ _ k Hb HJ)). }
  assert (Hheads : fs_heads B ly3 S3 U3).
  { rewrite EU1. intros r [<-|[]]. split; [reflexivity|]. exists (mm + HEAD). split; [exact Hrbin|].
    unfold req_size, HEAD. destruct (Z.eqb_spec (mm + 16) 0); lia. }
  pose proof Hcstrc as ((Hcg & Hcnz) & Hc4096 & Hccl & _).
  assert (Htz : zbytes_at tfibsegs W3 (ms_mem ms) text (HState.zs (tb ++ [Z_to_bv 8 0]))).
  { unfold zbytes_at. unfold HState.zs in *. rewrite map_app, Etb. exact Hcg. }
  assert (Hnul : ~ In (Z_to_bv 8 0) tb).
  { intros Hin. apply (in_map (fun b : byte => bv_unsigned b)) in Hin. change (map _ tb) with (HState.zs tb) in Hin.
    rewrite Etb in Hin. rewrite Forall_forall in Hcnz. exact (Hcnz _ Hin eq_refl). }
  assert (Hlen : Z.of_nat (length tb) = fe_n cx).
  { rewrite <- Htblen. rewrite <- Etb. unfold HState.zs. rewrite length_map. reflexivity. }
  assert (Hwin : forall a, text <= a < text + Z.of_nat (length tb) + 1 ->
    ~ HState.in_window (spZ (ms_regs ms)) STK_check_round_trip a).
  { intros a Ha. unfold HState.in_window. rewrite Rsp. pose proof s7_stk_crt. unfold LLVMF_STK in *. lia. }
  assert (Hblk : exists pt kt, In (pt, kt) (ablocks B ly3 S3) /\ pt <= text /\
    text + Z.of_nat (length tb) + 1 <= pt + kt) by (exists text, (fe_n cx + 1); split; [exact Htext | lia]).
  pose proof Hansc as [(_ & Hb0 & _) | (bs' & mm' & Hdec' & _ & El' & Hsrc' & Hrb' & Hlm' & _)]; [exfalso; exact (Hbn0 Hb0)|].
  rewrite Hdec in Hdec'. injection Hdec' as <-.
  pose proof Hsrc' as (Hzb' & _).
  assert (Hquiet : quiet (c_cnt cx + 4) SIZE_MAXZ EV_check_round_trip)
    by (unfold quiet, FS_CNT_LIB, EV_check_round_trip in *; lia).
  assert (Hrd : rd_cells tfibsegs W3 (ms_mem ms))
    by exact (s7_rd_cells ly3 S3 U3 W3 (ms_mem ms) _ HARU (s7_arodata cx ly3 S3 W3 _ _ k Hb HJ)).
  assert (Hnev : st_nev S3 + EV_check_round_trip <= EV_MAX)
    by (unfold EV_check_round_trip, EV_LIB in *; lia).
  assert (Hroom : blocks_bytes S3 + LIVE_check_round_trip <= LIVE_MAX)
    by (unfold LIVE_check_round_trip, YCfn.LIVE_LIB in *; lia).
  assert (Hlive : fe_live6 cx body + LIVE_check_round_trip < 2 ^ 64).
  { unfold fe_live6. destruct (Z.eqb_spec body 0) as [Hb0' | _]; [exfalso; exact (Hbn0 Hb0')|].
    unfold dec_size. rewrite Htblen.
    assert (Hd0 : 0 <= fe_n cx / 4) by (apply Z.div_pos; lia).
    assert (Hd1 : fe_n cx / 4 <= fe_n cx) by (apply Z.div_le_upper_bound; lia).
    unfold LIVE_check_round_trip, YCfn.LIVE_LIB in *. lia. }
  assert (Hrbk : exists k0, fs_rblock tfibsegs B ly3 S3 W3 (ms_mem ms) body k0 /\ Z.of_nat (length bs) <= k0)
    by (exists mm'; split; [exact Hrb' | lia]).
  (* the text block overlaps no head of U: U is the body's fuzz head, inside the body's own live block, which AR
     separates from the text's block (YCbq.sep_blocks_perm over the walk's ledger, body first) *)
  assert (HUd : Forall (fun q => text + Z.of_nat (length tb) + 1 <= fst q \/ fst q + snd q <= text) U3).
  { rewrite EU1. constructor; [|constructor]. cbn [fst snd].
    assert (Ebb : fe_body_blocks cx body = [(body - HEAD, dec_size (fe_tb cx) + HEAD)])
      by (unfold fe_body_blocks; destruct (Z.eqb_spec body 0) as [Hb0 | _]; [exfalso; exact (Hbn0 Hb0) | reflexivity]).
    assert (HpB := Hperm). rewrite Ebb in HpB. cbn [app] in HpB.
    pose proof (sep_blocks_perm tfibsegs B LAWS _ _ _ _ _ _ _ _ HAR3 HpB) as Hd.
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
    assert (Hd3 : 0 <= dec_size (fe_tb cx)) by (unfold dec_size; Z.div_mod_to_equations; lia).
    unfold req_size in Hd. destruct (Z.eqb_spec (dec_size (fe_tb cx) + HEAD) 0);
      destruct (Z.eqb_spec (fe_n cx + 1) 0); unfold HEAD in *; lia. }
  assert (Hcall := en_round_trip ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) _ ch text body tb bs (fe_live6 cx body) (c_cnt cx + 4)
    HPRE Hheads ltac:(rewrite Rsp, ETOP3; unfold fe_sp0 in *; lia) Hfrl R10 R11 R12 Htz Hnul ltac:(lia) Hwin Hblk HUd
    ltac:(rewrite Etb; exact Hdec) Hbn0
    ltac:(rewrite (s7_zs_bz W3 (ms_mem ms) body bs Hzb'); exact Hzb') Hrbk
    Hstc Hquiet Hlive Hrd ltac:(rewrite Rsp; lia) Hnev Hroom).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ssc ms HS2 eq_refl).
  eapply SRr_bind; [exact Hcall|]. cbv beta.
  intros W' c' Hwle Hpost.
  destruct Hpost as (ly' & S' & regs' & m' & md' & -> & HJc & OK' & PO' & HP & Hperm' & (cnt' & Hcnt' & Hst') & _).
  rewrite RA1.
  (* the walk's journal and the data at the return *)
  assert (HJ' := fsw_ajournal_sub4 B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms)) _ k STK_check_round_trip (spZ (ms_regs ms)) FS_PSTAT_FP []
    ly' S' W' (unpoison U3 m') md' EV_check_round_trip HJ HJc
    ltac:(rewrite Rsp; pose proof s7_stk_crt; unfold LLVMF_STK in *; lia) ltac:(rewrite Rsp; lia)
    (fun a Hf => or_intror (or_intror (or_introl (conj Hf (s7_pstat_img a Hf)))))).
  cbn [app] in HJ'.
  assert (HARU' : ARU tfibsegs B ly' S' U3 W' m' md') by (split; [exact (proj1 HJ') | split; [exact OK' | exact PO']]).
  assert (Hinc : forall x, In x (ablocks B ly3 S3) -> In x (ablocks B ly' S'))
    by (intros x Hx; exact (Permutation_in x (Permutation_sym Hperm') Hx)).
  pose proof (s7_mf_call cx STK_check_round_trip (spZ (ms_regs ms)) FS_PSTAT_FP ly3 S3 U3 W3 (ms_mem ms) _ ly' S' W' m' md'
    EV_check_round_trip text body l _ _ _ _ Hpl0 HARU HJc OK' PO' s7_pstat_img Hinc Htext Hpay EU Hmfc Hst') as Hmf'.
  destruct (s7_regs_ret cx E (ms_regs ms) regs' [Z_to_bv 64 l] Hcore RG HP) as (Hcore' & RK).
  pose proof Hcore' as (E8' & E9' & E2' & E18' & E24' & E25' & _).
  assert (HSr := s7_st_ret cx E ssc W3 ms _ ly3 S3 U3 STK_check_round_trip FS_PSTAT_FP regs' ly' S' W' m' md'
    EV_check_round_trip (k + EV_check_round_trip) l RA_crt Hb HE Hcore E46 HS2 eq_refl HARU Hfr3 ELY3 HJc HJ' HARU'
    s7_pstat_img ltac:(rewrite Rsp; lia)
    ltac:(rewrite <- (ew_Ereg_nat regs' (fe_extra cx ++ [Z_to_bv 64 l]) 8 8%bv eq_refl); exact E8')
    ltac:(rewrite <- (ew_Ereg_nat regs' (fe_extra cx ++ [Z_to_bv 64 l]) 24 24%bv eq_refl); exact E24')
    ltac:(rewrite <- (ew_Ereg_nat regs' (fe_extra cx ++ [Z_to_bv 64 l]) 18 18%bv eq_refl); exact E18')
    ltac:(rewrite <- (ew_Ereg_nat regs' (fe_extra cx ++ [Z_to_bv 64 l]) 25 25%bv eq_refl); exact E25')).
  assert (ELY' : ly_F ly' = ly_F (c_ly cx))
    by (pose proof HJ' as (_ & Hl' & _); destruct Hl' as (_ & _ & _ & _ & _ & EL & _); exact EL).
  assert (Hfr' : In (0, c_fpos cx) (frames S'))
    by (pose proof HJ' as (_ & _ & _ & _ & _ & Hf & _); rewrite Hf; left; reflexivity).
  assert (Hpay' : c_n cx = 0 \/ In (c_p cx, c_n cx) (ablocks B ly' S'))
    by (destruct Hpay as [H0 | Hin]; [left; exact H0 | right; exact (Hinc _ Hin)]).
  assert (Hio' : same_io (c_md cx) md').
  { apply (same_io_trans _ (with_vm_backing (m_vm_lazy md3) mat md3)); [exact (s7_same_io_wvb _ md3 mat Hio)|].
    pose proof HJc as (_ & _ & _ & _ & Hos & _). exact (aos_step_closed_same_io FS_PSTAT_FP _ _ s7_pstat_closed Hos). }
  assert (Hbb' : blocks_bytes S' <= blocks_bytes (c_S cx) + 2 ^ 32).
  { rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ Hperm'), <- (blocks_bytes_bsum B ly3 S3). exact Hbb3. }
  pose proof HARU' as HARUr.
  clear HS2 HJ HARU.
  (* `j 0x81170` (0x8115c) *)
  fsw_aj_run_toU entry_tbl_ok HSr HJ' HARU' RA_crc.
  { exact (s7_awr cx _ _ ly' S' _ Hcore' ELY' HF4096 HFc). }
  assert (HF' : frame_of (Ereg regs' (fe_extra cx ++ [Z_to_bv 64 l])) (fe_regions [fe_len_atom 46]) m' (ms_mem ms0))
    by exact HF.
  pose proof (s7_mf_keep cx ly' S' U3 W' m' (ms_mem ms0) md' text body l _ _ Hpl0 HARUr (Hinc _ Htext) Hpay'
    (s7_keep_frame cx _ [fe_len_atom 46] ly' S' U3 W' m' (ms_mem ms0) md' Hb Hcore' HARUr Hfr' ELY' HF') HG Hmf')
    as Hmf''.
  apply (Hnext cx _ (k + EV_check_round_trip) ly' S' U3 W' ms0 _ Hb (fe_E_Ereg cx regs' [Z_to_bv 64 l]) HJ' HARU');
    [|exact HSr].
  apply (s7_inv7 cx _ _ ly' S' U3 W' ms0 _ text body l cnt' Hcore').
  + rewrite (RK 19%nat ltac:(cbn; tauto)). exact E19.
  + rewrite (RK 20%nat ltac:(cbn; tauto)). exact E20.
  + rewrite (RK 21%nat ltac:(cbn; tauto)). exact E21.
  + rewrite (RK 22%nat ltac:(cbn; tauto)). exact E22.
  + rewrite (RK 23%nat ltac:(cbn; tauto)). exact E23.
  + apply s7_atom46.
  + exact EU.
  + exact (Permutation_trans Hperm' Hperm).
  + exact Hn3.
  + exact Hmf''.
  + replace (if body =? 0 then 0 else CRT_ALLOCS) with CRT_ALLOCS by (destruct (Z.eqb_spec body 0); [lia | reflexivity]).
    exact Hcnt'.
  + unfold EV_check_no_overread, EV_preset_base64_decode, EV_check_as_written, EV_check_round_trip. lia.
  + exact (s7_same_io_wvb _ md' _ Hio').
  + exact Hbb'.
Qed.

End s.
