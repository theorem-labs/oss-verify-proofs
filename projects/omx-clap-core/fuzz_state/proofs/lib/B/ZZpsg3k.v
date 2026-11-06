(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE B (fs.asan-ubsan) walk of parse_value 0x82fcc, stage lemmas. HEADER: see
   FSW_parse_value_holds.v (the composition into parse_value_spec k, the rule-24 line, the reuse search, the port
   sources, every pc walked and every report site). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value.v, with its module names and numbers changed; 1163 of its 1272 lines of code are new or changed and 1247 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/FSW_put_string.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_put_string.v; 421 of its 500 lines of code are new or changed and 1193 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/ZZpsg3k.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* Shared HELPERS for the three put call sites of put_string's walk, image B (fs.asan-ubsan), the twin of
   lib/A/ZZpsg3k.v (piece R6 of a Theorem Labs lane). Helpers only, no walk: ZZpsg1.v, ZZpsg2.v and ZZpsg3.v (SEG3) import
   this file. Image-independent text: no register, address or STK value of put_string's own code appears here
   (the frame slot at sp1 + 80 holds atom 24, the fake frame, on image B too: FSW_put_string.psj_scs0); zz_eq_dec
   and uswap_kept_head come from lib/B/FSW_writer_kit.v (a Theorem Labs lane, on the fold a working branch).
   - ps_chain_call: put's `achain` premise at put #2 / #3 (sp = the re-aligned sp1, s0 = the entry sp), from the
     entry chain and a reader that agrees with the entry's on [sp0, ly_top) OFF the out-object [o, o + 32) -
     ps_pre's `fp <= o \/ o + 48 <= fp` clause is what keeps every chain record off the object.
     FSW_put_string.ps_chain_put asks agreement on ALL of [sp0, 2^64), which put #1 breaks at [o, o + 32).
   - ps_chain_agree: that agreement, from the entry-to-call journal (bytes above the window top) and the bytes of
     [sp0, ot) off the object (wkeep), with the poison sets read through ARU at both ends.
   - ps_str_keep: cstr_ok and wsrc_kept of put_string's string at a later state (a put's return), re-derived from
     the ENTRY facts over the entry-to-now journal (ps_put_call hands back only that one): the block arms by
     FSW_strkit.cstr_ok_kept_blkU (the string's block is not the buffer's, so bswap keeps it and the footprint
     misses it), the table arm by FSW_strkit.cstr_ok_kept_tbl.
   - ps_wout_pt / ps_aro_pt / ps_agree_pt: transports onto a memory that agrees POINTWISE (the joins hand back
     `forall x, ms_mem ms' x = ms_mem ms x`).
   Templates (cited, not imported): the block-list lemmas psg3k_block_low / psg3k_pairwise_dup / psg3k_ab_mid_dup
   are a Theorem Labs lane's ZZwv_comp.v zzwv_block_low / zzwv_pairwise_dup / zzwv_ab_mid_dup
   (a working branch d25c24802e0, :96-105, :147-155, :173-188), renamed. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_frame FSW_frame3 FSW_strkit FSW_writer_kit FSW_put_string ZZpsjoin ZZpskeep ZZpssep.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterRet.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= closed arithmetic and list facts (lia only here) ================= *)
Lemma psg3k_bad_next_false : forall fp top nfp, bad_next fp top nfp = false ->
  fp < nfp /\ nfp < top - 16 /\ nfp mod 8 = 0.
Proof.
intros fp top nfp H. unfold bad_next in H.
apply orb_false_iff in H as [H H3]. apply orb_false_iff in H as [H1 H2].
apply Z.leb_gt in H1. apply Z.leb_gt in H2. apply negb_false_iff, Z.eqb_eq in H3.
split; [exact H1 | split; [exact H2 | exact H3]].
Qed.

Lemma psg3k_mod8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

(* the pairwise relation of a list that holds x twice relates x to itself (ZZwv_comp.v zzwv_pairwise_dup) *)
Lemma psg3k_pairwise_dup : forall {X : Type} (R : X -> X -> Prop) (l1 l2 : list X) (x : X),
  pairwise R (l1 ++ x :: l2) -> In x (l1 ++ l2) -> R x x.
Proof.
  intros X R l1. induction l1 as [|y l1 IH]; intros l2 x HP Hin.
  - cbn in HP. destruct HP as [HF _]. rewrite Forall_forall in HF. apply HF. exact Hin.
  - cbn in HP. destruct HP as [HF HP]. cbn in Hin. destruct Hin as [-> | Hin].
    + rewrite Forall_forall in HF. apply HF. apply in_or_app. right. left. reflexivity.
    + exact (IH l2 x HP Hin).
Qed.

(* one byte read twice at one address is one value *)
Lemma psg3k_byte_uniq : forall (m : word -> option byte) a v1 v2,
  val_mem tfibsegs m a 1 v1 -> val_mem tfibsegs m a 1 v2 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> v1 = v2.
Proof.
intros m a v1 v2 H1 H2 R1 R2.
pose proof (H1 0%nat ltac:(lia)) as E1. pose proof (H2 0%nat ltac:(lia)) as E2.
rewrite E1 in E2.
pose proof (f_equal (fun ob => match ob with Some b => bv_unsigned b | None => 0 end) E2) as E. cbn beta iota in E.
rewrite !Z_to_bv_unsigned in E. unfold bv_wrap, YG0f.le_byte, YO0f.le_byte in E.
change (bv_modulus 8) with 256 in E. change (2 ^ (8 * Z.of_nat 1)) with 256 in E.
change (8 * Z.of_nat 0) with 0 in E. rewrite !Z.shiftr_0_r in E.
rewrite !(Z.mod_small v1 256), !(Z.mod_small v2 256) in E by assumption. exact E.
Qed.

(* two NUL-terminated strings without inner zero at one address on one memory are one string *)
Lemma psg3k_cstr_uniq : forall (m : word -> option byte) l1 l2 p,
  garr8 tfibsegs m p (l1 ++ [0]) -> Forall (fun c => c <> 0) l1 ->
  garr8 tfibsegs m p (l2 ++ [0]) -> Forall (fun c => c <> 0) l2 -> l1 = l2.
Proof.
intros m l1. induction l1 as [|c1 l1 IH]; intros l2 p G1 F1 G2 F2.
- destruct l2 as [|c2 l2]; [reflexivity|]. exfalso.
  destruct (G1 0%nat ltac:(cbn; lia)) as (V1 & R1). destruct (G2 0%nat ltac:(cbn; lia)) as (V2 & R2).
  cbn [nth app] in V1, V2, R1, R2.
  apply (Forall_inv F2). exact (psg3k_byte_uniq m _ _ _ V2 V1 R2 R1).
- destruct l2 as [|c2 l2].
  + exfalso.
    destruct (G1 0%nat ltac:(cbn; lia)) as (V1 & R1). destruct (G2 0%nat ltac:(cbn; lia)) as (V2 & R2).
    cbn [nth app] in V1, V2, R1, R2.
    apply (Forall_inv F1). exact (psg3k_byte_uniq m _ _ _ V1 V2 R1 R2).
  + destruct (G1 0%nat ltac:(cbn; lia)) as (V1 & R1). destruct (G2 0%nat ltac:(cbn; lia)) as (V2 & R2).
    cbn [nth app] in V1, V2, R1, R2.
    pose proof (psg3k_byte_uniq m _ _ _ V1 V2 R1 R2) as Ec. subst c2.
    f_equal. apply (IH l2 (p + 1)).
    * intros j Hj. destruct (G1 (S j) ltac:(cbn [length app] in *; lia)) as (V & R).
      cbn [nth app] in V, R. split; [|exact R].
      replace (p + 1 + Z.of_nat j) with (p + Z.of_nat (S j)) by lia. exact V.
    * exact (Forall_inv_tail F1).
    * intros j Hj. destruct (G2 (S j) ltac:(cbn [length app] in *; lia)) as (V & R).
      cbn [nth app] in V, R. split; [|exact R].
      replace (p + 1 + Z.of_nat j) with (p + Z.of_nat (S j)) by lia. exact V.
    * exact (Forall_inv_tail F2).
Qed.

(* ================= the frame chain, kept on the bytes it reads ================= *)
(* an fpchain reads, at each record's fp b, the two words [b - 16, b); the final link reads [b - 8, b) of the last
   continued fp. So agreement on [b - 16, b) for the start and every continued fp keeps the chain. *)
Lemma psg3k_fpchain_kept : forall (rd rd' : reader) top ch bp,
  fpchain (rdword rd) bp top ch ->
  (forall b, (b = bp \/ exists r, In r ch /\ snd r = b /\ bad_next (fst (fst r)) top b = false) ->
     forall a, b - 16 <= a < b -> rd' a = rd a) ->
  fpchain (rdword rd') bp top ch.
Proof.
intros rd rd' top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hc Hag; cbn [fpchain] in *.
- destruct Hc as (r & Hr & Hb). exists r. split; [|exact Hb].
  rewrite (rdword_ext rd rd' (bp - 8)); [exact Hr|].
  intros j Hj. apply (Hag bp (or_introl eq_refl)). lia.
- destruct Hc as (Efp & Hal & H8 & H16 & Hra & Hrest). subst fp.
  split; [reflexivity|]. split; [exact Hal|].
  split; [rewrite (rdword_ext rd rd' (bp - 8)); [exact H8 | intros j Hj; apply (Hag bp (or_introl eq_refl)); lia]|].
  split; [rewrite (rdword_ext rd rd' (bp - 16)); [exact H16 | intros j Hj; apply (Hag bp (or_introl eq_refl)); lia]|].
  split; [exact Hra|].
  destruct (bad_next bp top nfp) eqn:Eb; [exact Hrest|].
  apply IH; [exact Hrest|].
  intros b Hb. apply Hag. right. destruct Hb as [-> | (r & Hr & Hs & Hbn)].
  + exists (bp, ra, nfp). split; [left; reflexivity|]. split; [reflexivity | exact Eb].
  + exists r. split; [right; exact Hr | split; [exact Hs | exact Hbn]].
Qed.

Section K. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* fs's image facts (RELOC / RUNTIME-owned, the walk's open hypothesis, approved by a Theorem Labs lane 2026-10-29): the table
   arm of the string's home re-derives cstr_ok from them *)
Hypothesis HIMG : fs_img_facts tfibsegs B.

(* ================= 1. the chain at a later put call ================= *)
Lemma ps_chain_call : forall ly S U (W : world tfibsegs) regs mem md ch o ly' (W' : world tfibsegs) m' sp1,
  afn_preU tfibsegs B STK_put_string ly S U W regs mem md ch ->
  (forall fp, fp = s0Z regs \/ (exists r, In r ch /\ snd r = fp /\ bad_next (fst (fst r)) (ly_top ly) fp = false) ->
     fp <= o \/ o + 48 <= fp) ->
  ly_top ly' = ly_top ly ->
  (forall a, spZ regs <= a < ly_top ly -> ~ (o <= a < o + 32) ->
     aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) (unpoison U mem) a) ->
  rdword (aview tfibsegs (w_H W') m') (spZ regs - 8) = Some (raZ regs) ->
  rdword (aview tfibsegs (w_H W') m') (spZ regs - 16) = Some (s0Z regs) ->
  sp1 + 16 <= spZ regs ->
  achain ly' (aview tfibsegs (w_H W') m') sp1 (spZ regs) (ps_ch1 ly regs ch).
Proof.
intros ly S U W regs mem md ch o ly' W' m' sp1 HPRE Hfp Etop Hag H8 H16 Hsp1.
pose proof HPRE as ((HAR & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & Hqt) & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (psg3k_mod8 _ Hal16) as Hal8.
assert (Hsp0 : alloc_ceiling <= spZ regs) by (clear - HSTK0 Hceil Hslo; lia).
unfold ps_ch1, achain. rewrite Etop.
destruct (Z.leb_spec (ly_top ly - 16) (spZ regs)) as [Hle | Hlt].
- left. split; [right; left; exact Hle | reflexivity].
- right. split; [exact Hsp1|]. split; [exact Hlt|]. split; [exact Hal8|]. split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact Hal8|]. split; [exact H8|]. split; [exact H16|].
    split; [exact Hra4|].
    destruct (bad_next (spZ regs) (ly_top ly) (s0Z regs)) eqn:Eb.
    * destruct Hch as [(_ & Hc) | (H1 & H2 & H3 & _ & _)]; [exact Hc|].
      exfalso. unfold bad_next in Eb.
      rewrite (proj2 (Z.leb_gt (s0Z regs) (spZ regs)) ltac:(clear - H1; lia)),
              (proj2 (Z.leb_gt (ly_top ly - 16) (s0Z regs)) H2), H3 in Eb.
      cbn in Eb. discriminate Eb.
    * destruct (psg3k_bad_next_false _ _ _ Eb) as (B1 & B2 & B3).
      destruct Hch as [(Hbad & _) | (H1 & H2 & H3 & Hfc & Hfa)].
      -- exfalso. destruct Hbad as [Hb | [Hb | Hb]];
           [clear - Hb B1 Hsp0; lia | clear - Hb B2; lia | exact (Hb B3)].
      -- apply (psg3k_fpchain_kept (aview tfibsegs (w_H W) (unpoison U mem)) _ (ly_top ly) ch (s0Z regs) Hfc).
         pose proof (fpchain_fps_increase _ _ _ _ Hfc) as Hinc.
         intros b Hb a Ha.
         assert (Hb2 : spZ regs + 16 <= b /\ b <= ly_top ly).
         { destruct Hb as [-> | (r & Hr & Hs & Hbn)]; [clear - H1 H2; lia|].
           destruct (psg3k_bad_next_false _ _ _ Hbn) as (C1 & C2 & _).
           rewrite Forall_forall in Hinc. pose proof (Hinc r Hr) as Hr0. clear - H1 C1 C2 Hr0. lia. }
         apply Hag; [clear - Hb2 Ha; lia|].
         destruct (Hfp b Hb) as [Hx | Hx]; clear - Hx Ha; lia.
  + constructor; [cbn [fst]; exact Hsp1|].
    destruct Hch as [(_ & ->) | (_ & _ & _ & _ & Hfa)]; [constructor|].
    eapply Forall_impl; [|exact Hfa]. intros r Hr. cbv beta in Hr |- *. clear - Hr Hsp1. lia.
Qed.

(* the agreement ps_chain_call asks, from what a put call site holds: the journal from the entry (window top ot)
   keeps every byte at or above ot; [sp0, ot) off the object keeps its bytes (wkeep); both are stack bytes, high
   application memory, where unpoison changes nothing *)
Lemma ps_chain_agree : forall STK ot FP ly S U (W : world tfibsegs) mem md own lyc Sc Uc (Wc : world tfibsegs) memc
    mdc k sp0 o,
  ajournal tfibsegs B STK ot FP ly S W (unpoison U mem) md own lyc Sc Wc (unpoison Uc memc) mdc k ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  ot - STK <= sp0 -> alloc_ceiling <= sp0 ->
  (forall a, sp0 <= a < ot -> ~ (o <= a < o + 32) ->
     mbyte tfibsegs (mrestrict (w_H Wc) memc) a = mbyte tfibsegs (mrestrict (w_H W) mem) a) ->
  forall a, sp0 <= a < 2 ^ 64 -> ~ (o <= a < o + 32) ->
    aview tfibsegs (w_H Wc) (unpoison Uc memc) a = aview tfibsegs (w_H W) (unpoison U mem) a.
Proof.
intros STK ot FP ly S U W mem md own lyc Sc Uc Wc memc mdc k sp0 o HJ HARU HARUc Hwin Hceil Hkeep a Ha Ho.
pose proof asan_consts as (C1 & _ & C3 & _).
destruct (Z.ltb_spec a ot) as [Hlt | Hge].
- assert (Happ : a < SHADOW_OFF \/ kHighMemBeg <= a) by (right; rewrite C3; clear - C1 Hceil Ha; lia).
  assert (Ha64 : 0 <= a < 2 ^ 64) by (clear - Ha C1 Hceil; lia).
  rewrite (aview_unpoison_out tfibsegs (w_H Wc) Uc memc a)
    by (rewrite (wz a Ha64); exact (pske_ush_aru B lyc Sc Uc Wc memc mdc a HARUc Happ)).
  rewrite (aview_unpoison_out tfibsegs (w_H W) U mem a)
    by (rewrite (wz a Ha64); exact (pske_ush_aru B ly S U W mem md a HARU Happ)).
  unfold aview. rewrite (Hkeep a ltac:(clear - Ha Hlt; lia) Ho). reflexivity.
- pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & Hout & _).
  exact (Hout a ltac:(clear - Ha Hceil; lia) ltac:(clear - Hge; lia)).
Qed.

(* ================= 2. pointwise-equal memories ================= *)
Lemma ps_agree_pt : forall (W : world tfibsegs) (m m' : word -> option byte) Wr,
  (forall x, m' x = m x) -> pske_agree W W m m' Wr.
Proof.
intros W m m' Wr E. split.
- intros a _ _. exact (psj_mbyte_pt (w_H W) m m' a (E _)).
- intros a _ _ Hp. unfold apresent in *. rewrite (E (Z_to_bv 64 a)). exact Hp.
Qed.

Lemma ps_aro_pt : forall (W : world tfibsegs) (m m' : word -> option byte),
  (forall x, m' x = m x) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m').
Proof.
intros W m m' E H a H1 H2 H3. rewrite (aview_at tfibsegs (w_H W) m' m a (E _)). exact (H a H1 H2 H3).
Qed.

Lemma ps_wout_pt : forall ly S (W : world tfibsegs) (m m' : word -> option byte) o buf cap failed text,
  (forall x, m' x = m x) ->
  FSH_Fn_writer.wout_ok B tfibsegs ly S W m o buf cap failed text ->
  FSH_Fn_writer.wout_ok B tfibsegs ly S W m' o buf cap failed text.
Proof.
intros ly S W m m' o buf cap failed text E
  (Hal & Ho0 & Hotop & Hwp & Hb & Hc & V0 & V8 & V16 & V24 & Hf & Hbo & Hdisj).
assert (Em : forall a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) by (intros a; apply E).
unfold FSH_Fn_writer.wout_ok.
split; [exact Hal|]. split; [exact Ho0|]. split; [exact Hotop|].
split.
{ intros i Hi. destruct (Hwp i Hi) as (Hw & Hpr). split.
  - exact (psj_writable_pt (w_H W) m m' (o + i) (Em _) Hw).
  - unfold apresent in *. rewrite (Em (o + i)). exact Hpr. }
split; [exact Hb|]. split; [exact Hc|].
split; [exact (psj_val_mem_pt (w_H W) m m' o 8 buf (fun k _ => Em _) V0)|].
split; [exact (psj_val_mem_pt (w_H W) m m' (o + 8) 8 _ (fun k _ => Em _) V8)|].
split; [exact (psj_val_mem_pt (w_H W) m m' (o + 16) 8 cap (fun k _ => Em _) V16)|].
split; [exact (psj_val_mem_pt (w_H W) m m' (o + 24) 4 failed (fun k _ => Em _) V24)|].
split; [exact Hf|]. split; [exact Hbo|].
destruct Hdisj as [Hz | (Hj & (Hbl & Hmm & Hcap & Hhd) & Hlen & Hz)]; [left; exact Hz|].
right. split; [exact Hj|]. split.
- split; [exact Hbl|]. split; [exact Hmm|]. split; [exact Hcap|].
  exact (psj_val_mem_pt (w_H W) m m' (buf - HEAD) 8 cap (fun k _ => Em _) Hhd).
- split; [exact Hlen|].
  unfold zbytes_at in *. apply (garr8_frame tfibsegs _ _ buf (text ++ [0]) Hz).
  intros a _. exact (psj_mbyte_pt (w_H W) m m' a (Em a)).
Qed.

(* ================= 3. live blocks ================= *)
(* ZZwv_comp.v zzwv_block_low, renamed *)
Lemma psg3k_block_low : forall ly S W mem md p n,
  AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 4096 <= p /\ 0 <= n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W mem md p n HAR Hin)
    as (_ & H4096 & _ & _ & _ & _ & Hn).
  split; [exact H4096 | lia].
Qed.

(* ZZwv_comp.v zzwv_ab_mid_dup, renamed: a block that is live twice overlaps itself *)
Lemma psg3k_ab_mid_dup : forall ly S W mem md C1 C2 x,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = C1 ++ x :: C2 -> In x (C1 ++ C2) -> False.
Proof.
  intros ly S W mem md C1 C2 [p n] HAR E Hin.
  assert (Hx : In (p, n) (ablocks B ly S))
    by (rewrite E; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W mem md p n HAR Hx)
    as (_ & _ & _ & _ & _ & Hpw & Hn).
  rewrite E, map_app in Hpw. cbn [map] in Hpw.
  assert (Hin2 : In (p, req_size n) (map (fun b : Z * Z => (fst b, req_size (snd b))) C1 ++
                                     map (fun b : Z * Z => (fst b, req_size (snd b))) C2)).
  { rewrite <- map_app. exact (in_map (fun b : Z * Z => (fst b, req_size (snd b))) (C1 ++ C2) (p, n) Hin). }
  pose proof (psg3k_pairwise_dup zdisjoint _ _ _ Hpw Hin2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold req_size in Hd.
  destruct (Z.eqb_spec n 0); lia.
Qed.

(* a block of the call's start that is not the buffer's does not start where the NEW buffer block does *)
Lemma psg3k_not_new : forall ly' S' (W' : world tfibsegs) m' md' A buf buf' cap cap' b mm,
  AR tfibsegs B ly' S' W' m' md' ->
  FSH_Fn_writer.bswap A (ablocks B ly' S') buf buf' cap cap' ->
  In (b, mm) A -> b <> buf - HEAD -> In (b, mm) (ablocks B ly' S') -> b = buf' - HEAD -> False.
Proof.
intros ly' S' W' m' md' A buf buf' cap cap' b mm HAR Hsw Hin Hne Hin' Eb.
assert (Hbuf : buf' <> buf) by (intros E; apply Hne; rewrite Eb, E; reflexivity).
assert (Hnew : exists C1 C2, ablocks B ly' S' = C1 ++ (buf' - HEAD, cap' + HEAD) :: C2 /\ In (b, mm) (C1 ++ C2)).
{ destruct Hsw as [(E & _ & _) | [(_ & C1 & C2 & E1 & E2) | (A1 & A2 & C1 & C2 & E1 & E2 & E3)]].
  - exfalso. exact (Hbuf E).
  - exists C1, C2. split; [exact E1 | rewrite E2; exact Hin].
  - exists C1, C2. split; [exact E2|]. rewrite E3. rewrite E1 in Hin.
    apply in_app_or in Hin. apply in_or_app. destruct Hin as [H | [H | H]]; [left; exact H | | right; exact H].
    exfalso. injection H as H1 _. apply Hne. symmetry. exact H1. }
destruct Hnew as (C1 & C2 & E & Hin2).
destruct (zz_eq_dec (b, mm) (buf' - HEAD, cap' + HEAD)) as [Ex | Nx].
- rewrite Ex in Hin2. exact (psg3k_ab_mid_dup ly' S' W' m' md' C1 C2 _ HAR E Hin2).
- assert (Hx : In (buf' - HEAD, cap' + HEAD) (ablocks B ly' S'))
    by (rewrite E; apply in_or_app; right; left; reflexivity).
  pose proof (sep_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly' S' W' m' md' b mm _ _ HAR Hin' Hx Nx) as Hd.
  destruct (psg3k_block_low ly' S' W' m' md' b mm HAR Hin') as (_ & Hm0).
  destruct (psg3k_block_low ly' S' W' m' md' _ _ HAR Hx) as (_ & Hc0).
  pose proof (req_size_pos mm Hm0) as (R1 & _). pose proof (req_size_pos (cap' + HEAD) Hc0) as (R2 & _).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd R1 R2 Eb. lia.
Qed.

(* a byte of a block that is not the buffer's lies off put_string's footprint *)
Lemma psg3k_off_fp : forall ly S (W : world tfibsegs) m md b mm buf cap a,
  AR tfibsegs B ly S W m md -> In (b, mm) (ablocks B ly S) -> b <> buf - HEAD ->
  (cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S)) ->
  b <= a < b + req_size mm -> ~ inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) a.
Proof.
intros ly S W m md b mm buf cap a HAR Hin Hne Hbuf Ha HF.
apply inFP_app in HF as [HF | HF].
- apply (blk_img tfibsegs B (AR_laws_ok tfibsegs B) ly S W m md b mm a HAR Hin Ha). apply pss_pstat_img. exact HF.
- unfold FSH_Fn_writer.wbuf_fp in HF. revert HF. destruct (Z.eqb_spec cap 0) as [E0 | Enz]; intros HF;
    cbv beta iota in HF.
  + exact (inFP_nil a HF).
  + destruct HF as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
    assert (Hbb : (b, mm) <> (buf - HEAD, cap + HEAD)) by (intros E; injection E as E1 _; exact (Hne E1)).
    pose proof (sep_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W m md b mm _ _ HAR Hin (Hbuf Enz) Hbb) as Hd.
    pose proof (pss_wbuf_in buf cap a Hr) as Hw.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Hw Ha. lia.
Qed.

(* a byte of a block live at both ends and off the footprint reads the same on the machine's memories *)
Lemma psg3k_blk_byte : forall STK jt FP ly S U (W : world tfibsegs) mem md own ly' S' U' (W' : world tfibsegs) mem'
    md' k b mm a,
  ARU tfibsegs B ly S U W mem md ->
  ajournal tfibsegs B STK jt FP ly S W (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' k ->
  ARU tfibsegs B ly' S' U' W' mem' md' ->
  In (b, mm) (ablocks B ly S) -> In (b, mm) (ablocks B ly' S') -> b <= a < b + req_size mm -> ~ inFP FP a ->
  mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a.
Proof.
intros STK jt FP ly S U W mem md own ly' S' U' W' mem' md' k b mm a H HJ H' Hin Hin' Ha HnF.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBL & _).
destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W (unpoison U mem) md b mm (proj1 H) Hin)
  as (_ & H4 & Hcl & Happ & _).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (Ha64 : 0 <= a < 2 ^ 64) by (clear - Ha H4 Hcl C1; lia).
assert (Hap : a < SHADOW_OFF \/ kHighMemBeg <= a).
{ rewrite C3. unfold in_app, kLowShadowBeg, SHADOW_OFF in *. rewrite C3 in Happ. clear - Happ Ha. lia. }
assert (Hi : 0 <= a - b < req_size mm) by (clear - Ha; lia).
assert (Ea : b + (a - b) = a) by ring.
pose proof (HBL b mm (a - b) Hin Hin' Hi ltac:(rewrite Ea; exact HnF)) as E.
rewrite Ea in E.
pose proof (mbyte_of_aview tfibsegs _ _ _ _ a E) as E2.
rewrite (mbyte_unpoison_app B ly' S' U' W' mem' md' a H' Ha64 Hap) in E2.
rewrite (mbyte_unpoison_app B ly S U W mem md a H Ha64 Hap) in E2.
exact E2.
Qed.

(* every head of U' misses a string that lies in a live block not starting at the head *)
Lemma psg3k_heads_miss : forall ly' S' U' (W' : world tfibsegs) m' md' b mm s n r,
  AR tfibsegs B ly' S' W' m' md' -> fs_heads B ly' S' U' ->
  In (b, mm) (ablocks B ly' S') -> b <= s -> s + n <= b + mm ->
  In r U' -> fst r <> b -> fst r + snd r <= s \/ s + n <= fst r.
Proof.
intros ly' S' U' W' m' md' b mm s n r HAR HH Hin Hb Hbn Hr Hne.
destruct (HH r Hr) as (Hs16 & m0 & Hm0 & H16).
assert (Hd0 : (fst r, m0) <> (b, mm)) by (intros E; injection E as E1 _; exact (Hne E1)).
pose proof (sep_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly' S' W' m' md' _ _ _ _ HAR Hm0 Hin Hd0) as Hd.
destruct (psg3k_block_low ly' S' W' m' md' b mm HAR Hin) as (_ & Hmm).
pose proof (req_size_pos mm Hmm) as (_ & R2).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hs16. clear - Hd H16 R2 Hb Hbn. lia.
Qed.

(* ================= 4. the string at a later state ================= *)
Lemma ps_str_keep : forall STK jt ly S U (W : world tfibsegs) mem md own ly' S' U' (W' : world tfibsegs) mem' md' k
    buf cap buf' cap' s (bs : list Z),
  ARU tfibsegs B ly S U W mem md -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  ajournal tfibsegs B STK jt (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) ly S W (unpoison U mem) md own
    ly' S' W' (unpoison U' mem') md' k ->
  ARU tfibsegs B ly' S' U' W' mem' md' -> fs_heads B ly' S' U' ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem') ->
  FSH_Fn_writer.bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap cap' ->
  FSH_Fn_writer.uswap U U' buf buf' cap ->
  (cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S)) ->
  cstr_ok tfibsegs W mem s bs -> FSH_Fn_writer.wsrc_kept B tfibsegs ly S U W mem buf s (bs ++ [0]) ->
  cstr_ok tfibsegs W' mem' s bs /\ FSH_Fn_writer.wsrc_kept B tfibsegs ly' S' U' W' mem' buf' s (bs ++ [0]).
Proof.
intros STK jt ly S U W mem md own ly' S' U' W' mem' md' k buf cap buf' cap' s bs
  H HRO HJ H' HH' HRO' Hsw Hus Hbuf Hc Hsrc.
pose proof H as (HAR & _ & _). pose proof H' as (HAR' & OK' & PO').
pose proof (pss_len0 bs) as EL.
destruct Hsrc as [(Hnil & _) | [(p & kk & Hp & (Hb & Hm & Hk & Hv) & Hs1 & Hs2)
                             | [(p & kk & Hp & Hb & Hs1 & Hs2 & Hr) | (l & Hl & Hlen)]]].
- exfalso. exact (app_cons_not_nil bs [] 0 (eq_sym Hnil)).
- (* a fuzz reader block other than the buffer *)
  rewrite EL in Hs2.
  pose proof (pss_neq_head p buf Hp) as Hne.
  pose proof (pss_bswap_keep _ _ _ _ _ _ _ _ Hsw Hb Hne) as Hin'.
  assert (Hnn : p - HEAD <> buf' - HEAD)
    by (intros E; exact (psg3k_not_new ly' S' W' (unpoison U' mem') md' _ buf buf' cap cap' _ _ HAR' Hsw Hb Hne
                           Hin' E)).
  assert (Hreq : req_size (kk + HEAD) = kk + HEAD)
    by (unfold req_size, HEAD; destruct (Z.eqb_spec (kk + 16) 0) as [E | E]; clear - Hk E; lia).
  assert (HnF : forall a, s <= a < s + Z.of_nat (length bs) + 1 ->
                  ~ inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) a).
  { intros a Ha. apply (psg3k_off_fp ly S W (unpoison U mem) md (p - HEAD) (kk + HEAD) buf cap a HAR Hb Hne Hbuf).
    rewrite Hreq. unfold HEAD in *. clear - Ha Hs1 Hs2. lia. }
  assert (HU' : forall r, In r U' -> fst r + snd r <= s \/ s + (Z.of_nat (length bs) + 1) <= fst r).
  { intros r Hr. destruct (Z.eq_dec (fst r) (p - HEAD)) as [Ef | Nf].
    - left. destruct (HH' r Hr) as (Hs16 & _). rewrite Ef, Hs16. unfold HEAD. clear - Hs1. lia.
    - apply (psg3k_heads_miss ly' S' U' W' (unpoison U' mem') md' (p - HEAD) (kk + HEAD) s
               (Z.of_nat (length bs) + 1) r HAR' HH' Hin');
        [unfold HEAD in *; clear - Hs1; lia | unfold HEAD in *; clear - Hs2; lia | exact Hr | exact Nf]. }
  split.
  + apply (cstr_ok_kept_blkU B STK jt _ ly S U W mem md own ly' S' U' W' mem' md' k s bs (p - HEAD) (kk + HEAD)
      H HJ OK' PO' Hb Hin'); [unfold HEAD in *; clear - Hs1; lia | unfold HEAD in *; clear - Hs2; lia
                              | exact HnF | | exact Hc].
    intros r Hr. right. destruct (HU' r Hr) as [X | X]; [left; exact X | right; clear - X; lia].
  + right. left. exists p, kk. split; [intros E; apply Hnn; rewrite E; reflexivity|].
    split; [|split; [exact Hs1 | rewrite EL; exact Hs2]].
    split; [exact Hin'|]. split; [exact Hm|]. split; [exact Hk|].
    intros j Hj. rewrite <- (Hv j Hj).
    apply (psg3k_blk_byte STK jt _ ly S U W mem md own ly' S' U' W' mem' md' k (p - HEAD) (kk + HEAD) _
             H HJ H' Hb Hin').
    * rewrite Hreq. unfold HEAD in *. clear - Hj Hk. lia.
    * apply (psg3k_off_fp ly S W (unpoison U mem) md (p - HEAD) (kk + HEAD) buf cap _ HAR Hb Hne Hbuf).
      rewrite Hreq. unfold HEAD in *. clear - Hj Hk. lia.
- (* any live block other than the buffer's, off every poisoned head *)
  rewrite EL in Hs2, Hr.
  pose proof (pss_bswap_keep _ _ _ _ _ _ _ _ Hsw Hb Hp) as Hin'.
  assert (Hnn : p <> buf' - HEAD)
    by (intros E; exact (psg3k_not_new ly' S' W' (unpoison U' mem') md' _ buf buf' cap cap' p kk HAR' Hsw Hb Hp
                           Hin' E)).
  destruct (psg3k_block_low ly S W (unpoison U mem) md p kk HAR Hb) as (_ & Hk0).
  pose proof (req_size_pos kk Hk0) as (_ & Rk).
  assert (HnF : forall a, s <= a < s + Z.of_nat (length bs) + 1 ->
                  ~ inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) a).
  { intros a Ha. apply (psg3k_off_fp ly S W (unpoison U mem) md p kk buf cap a HAR Hb Hp Hbuf).
    clear - Ha Hs1 Hs2 Rk. lia. }
  assert (HU' : forall r, In r U' -> fst r + snd r <= s \/ s + (Z.of_nat (length bs) + 1) <= fst r).
  { intros r Hr'. destruct (uswap_kept_head U U' buf buf' cap r Hus Hr') as [HrU | ->].
    - exact (Hr r HrU).
    - apply (psg3k_heads_miss ly' S' U' W' (unpoison U' mem') md' p kk s (Z.of_nat (length bs) + 1) _
               HAR' HH' Hin' Hs1 Hs2 Hr').
      cbn [fst]. intros E. exact (Hnn (eq_sym E)). }
  split.
  + apply (cstr_ok_kept_blkU B STK jt _ ly S U W mem md own ly' S' U' W' mem' md' k s bs p kk
      H HJ OK' PO' Hb Hin' Hs1); [clear - Hs2; lia | exact HnF | | exact Hc].
    intros r Hr'. right. destruct (HU' r Hr') as [X | X]; [left; exact X | right; clear - X; lia].
  + right. right. left. exists p, kk. split; [exact Hnn|]. split; [exact Hin'|]. split; [exact Hs1|].
    rewrite EL. split; [exact Hs2|]. exact HU'.
- (* a table string: fs_img_facts re-derives it, and it IS the table's entry (one string at s) *)
  assert (Hc0 : cstr_ok tfibsegs W mem s l)
    by exact (cstr_ok_kept_tbl B ly S U W mem md s l HIMG H HRO (or_introl Hl)).
  assert (El : bs = l)
    by exact (psg3k_cstr_uniq _ bs l s (proj1 (proj1 Hc)) (proj2 (proj1 Hc)) (proj1 (proj1 Hc0))
                (proj2 (proj1 Hc0))).
  subst l.
  split; [exact (cstr_ok_kept_tbl B ly' S' U' W' mem' md' s bs HIMG H' HRO' (or_introl Hl))|].
  right. right. right. exists bs. split; [exact Hl | exact Hlen].
Qed.

(* ================= 5. at a put's return: the frame's three chunk sets, the window, the stack words ================= *)
(* the frame slot at sp1 + 80 (atom 24, the fake frame) on another env and memory *)
Lemma ps_slot_move : forall (E E' : env) (m m' : word -> option byte) sp1,
  ew E' 24 = ew E 24 ->
  (forall a, sp1 + 80 <= a < sp1 + 88 -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  YP09.chunk_ok tfibsegs E m sp1 (YP09.mkChunk 80 (CVal 8 (SOff 24 0))) ->
  YP09.chunk_ok tfibsegs E' m' sp1 (YP09.mkChunk 80 (CVal 8 (SOff 24 0))).
Proof.
intros E E' m m' sp1 Ew Hm H.
apply (psj_chunk_pt E' m m' sp1).
- apply (ps_chunk_transfer E E' m sp1 80 8 (SOff 24 0) (SOff 24 0)); [rewrite !fsw_SOff0, Ew; reflexivity | exact H].
- intros i Hi. cbn in Hi |- *. apply Hm. lia.
Qed.

(* the fake frame's header chunks (three literals and the flag address, xatom 13) *)
Lemma ps_hdr_move : forall (E E' : env) (m m' : word -> option byte) F,
  ew E' (xatom 13) = ew E (xatom 13) ->
  (forall a, F <= a < F + 64 -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  Forall (YP09.chunk_ok tfibsegs E m F) ps_hdr_chunks -> Forall (YP09.chunk_ok tfibsegs E' m' F) ps_hdr_chunks.
Proof.
intros E E' m m' F Ex Hm H. rewrite Forall_forall in H |- *. intros c Hc.
pose proof (H c Hc) as Hc'. unfold ps_hdr_chunks in Hc. cbn [In] in Hc.
destruct Hc as [<- | [<- | [<- | [<- | []]]]].
- apply (psj_chunk_pt E' m m' F); [apply (psl_chunk_lit_env E E' m F); exact Hc'|].
  intros i Hi. cbn in Hi |- *. apply Hm. lia.
- apply (psj_chunk_pt E' m m' F); [apply (psl_chunk_lit_env E E' m F); exact Hc'|].
  intros i Hi. cbn in Hi |- *. apply Hm. lia.
- apply (psj_chunk_pt E' m m' F); [apply (psl_chunk_lit_env E E' m F); exact Hc'|].
  intros i Hi. cbn in Hi |- *. apply Hm. lia.
- apply (psj_chunk_pt E' m m' F).
  + apply (ps_chunk_transfer E E' m F 56 8 (SOff (xatom 13) 0) (SOff (xatom 13) 0));
      [rewrite !fsw_SOff0, Ex; reflexivity | exact Hc'].
  + intros i Hi. cbn in Hi |- *. apply Hm. lia.
Qed.

(* the frame's eight shadow bytes (literals) *)
Lemma ps_fsh_move : forall (E E' : env) (m m' : word -> option byte) shF,
  (forall a, shF <= a < shF + 8 -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  Forall (YP09.chunk_ok tfibsegs E m shF) ps_fsh_chunks -> Forall (YP09.chunk_ok tfibsegs E' m' shF) ps_fsh_chunks.
Proof.
intros E E' m m' shF Hm H. rewrite Forall_forall in H |- *. intros c Hc.
pose proof (H c Hc) as Hc'. unfold ps_fsh_chunks in Hc. cbn [In] in Hc.
destruct Hc as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]];
  (apply (psj_chunk_pt E' m m' shF); [apply (psl_chunk_lit_env E E' m shF); exact Hc'|]);
  intros i Hi; cbn in Hi |- *; apply Hm; lia.
Qed.

(* the thirteen saved entry words (extra atoms only) on another register file *)
Lemma ps_sv_move : forall (regs regs' : bvmap 5 word) X (m : word -> option byte) b,
  Forall (YP09.chunk_ok tfibsegs (Ereg regs X) m b) ps_sv_chunks ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' X) m b) ps_sv_chunks.
Proof.
intros regs regs' X m b H. rewrite Forall_forall in H |- *. intros c Hc.
pose proof (H c Hc) as Hc'. unfold ps_sv_chunks in Hc. apply in_map_iff in Hc as (k & <- & _).
apply (ps_chunk_transfer (Ereg regs X) (Ereg regs' X) m b _ 8 (SOff (xatom k) 0) (SOff (xatom k) 0)); [|exact Hc'].
rewrite !fsw_SOff0, !ps_ew_x. reflexivity.
Qed.

(* the window [sp0, ot) off the object: the entry-to-call keep, a pointwise-equal memory, then put's own keep *)
Lemma ps_wkeep_call : forall (W W2 W3 : world tfibsegs) mem mem2 memc mem3 sp0 sp1 ot o,
  wkeep tfibsegs W W2 mem mem2 sp0 ot o 32 -> (forall x, memc x = mem2 x) ->
  wkeep tfibsegs W2 W3 memc mem3 sp1 ot o 32 -> sp1 <= sp0 ->
  wkeep tfibsegs W W3 mem mem3 sp0 ot o 32.
Proof.
intros W W2 W3 mem mem2 memc mem3 sp0 sp1 ot o H1 E H2 Hs a Ha Hno.
destruct (H1 a Ha Hno) as (E1 & I1). destruct (H2 a ltac:(clear - Ha Hs; lia) Hno) as (E2 & I2).
assert (E3 : mbyte tfibsegs (mrestrict (w_H W2) memc) a = mbyte tfibsegs (mrestrict (w_H W2) mem2) a)
  by exact (psj_mbyte_pt (w_H W2) mem2 memc a (E _)).
split; [rewrite E2, E3; exact E1|].
split.
- intros Hx. apply I2. apply (psj_writable_pt (w_H W2) mem2 memc a (E _)). apply I1. exact Hx.
- intros Hx. apply I1. apply (psj_writable_pt (w_H W2) memc mem2 a (eq_sym (E _))). apply I2. exact Hx.
Qed.

(* a present byte reads Some *)
Lemma ps_aview_some : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> aview tfibsegs H m a <> None.
Proof. intros H m a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. intros E. discriminate E. Qed.

(* a present byte of high application memory (the stack) on the unpoisoned reading is present on the machine's *)
Lemma ps_apresent_unpoison : forall ly S U (W : world tfibsegs) m md a,
  ARU tfibsegs B ly S U W m md -> 0 <= a < 2 ^ 64 -> (a < SHADOW_OFF \/ kHighMemBeg <= a) ->
  apresent (w_H W) (unpoison U m) a -> apresent (w_H W) m a.
Proof.
intros ly S U W m md a H Ha Happ (Hh & b & Hb). split; [exact Hh|]. exists b.
rewrite unpoison_out in Hb; [exact Hb|]. rewrite (wz a Ha). exact (pske_ush_aru B ly S U W m md a H Happ).
Qed.

(* a word of high application memory reads the same through unpoison *)
Lemma ps_rdword_unpoison : forall ly S U (W : world tfibsegs) m md a v,
  ARU tfibsegs B ly S U W m md -> kHighMemBeg <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview tfibsegs (w_H W) m) a = Some v -> rdword (aview tfibsegs (w_H W) (unpoison U m)) a = Some v.
Proof.
intros ly S U W m md a v H Ha Ha8 E.
assert (Ha0 : 0 <= a) by (unfold kHighMemBeg in Ha; clear - Ha; lia).
rewrite (rdword_ext (aview tfibsegs (w_H W) m) _ a); [exact E|].
intros k Hk. apply (aview_unpoison_out tfibsegs). rewrite (wz (a + k) ltac:(clear - Hk Ha0 Ha8; lia)).
apply (pske_ush_aru B ly S U W m md _ H). right. clear - Hk Ha. lia.
Qed.

End K.
