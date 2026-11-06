(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 342 of its 368 lines of code are new or changed and 492 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): what the three INTERCEPTOR calls of segment A7 of
   reac_segconf_parse_file's walk ask, derived once from a cut of A7 (segment A7's proof,
   2026-10-30). No instruction is walked here.

   A7 calls three interceptors through their trampolines; their contracts are the interceptor owner's accepted texts:
     strchr       0x87f74  RtSeg.astrchr_realizes      (lib/A/Rt/RtSeg.v row 6), window 2 * ESTACK
     strncasecmp  0x880dc  RtSeg.astrncasecmp_realizes (lib/A/Rt/RtSeg.v row 7), window 2 * ESTACK
     strlen       0x88338  RtString.astrlen_realizes   (lib/A/Rt/RtString.v),   window ESTACK
   Each asks, besides its argument registers, the runtime-call pre-state with its window (ecall_pre_stk), each
   C string as a byte list (astr_at), the read range (aread_ok), band room past the string (amem_range), the
   bytes after the NUL up to the word's end (atail_vis) and the read-only view (rt_rom_view), all at the call's
   state (lib/A/Rt/RtDefs.v). Every string A7 hands to them lies in parse_file's buf[512] (the class-5 frame's
   object at F + 0x40), except strncasecmp's second, the .rodata literal "segment".

     a7_astr_of_sa      SegABase's sa_str (list Z, with its slack) gives astr_at / astr_atR at seg_spec.zb l,
                        astr_len (zb l) = |l|, zs (zb l) = l and atail_vis.
     a7_read_ok_buf     aread_ok of any range of buf at a call made at parse_file's realigned sp (pf_s1): the
                        shadow part is pf_a7_d.v's a7_addr_buf, the bytes are mapped because every byte of a
                        live frame is present (AR_laws' al_frames), and buf is below alloc_ceiling, which the
                        journal's astk_ok puts at or below ly_stk_lo <= sp - stk.
     a7_amem_frame      amem_range of any range of the class-5 frame (the + 8 past a string at buf's end).
     a7_tail_vis_buf    atail_vis at a NUL inside buf (buf is 8-aligned, so the word's end stays in buf).
     a7_ecall_pre_buf   ecall_pre_stk at a call of A7, by PaArt.v's ecall_pre_stk_at from a7_st's journal
                        (o = pf_s1 - sp0 in [-336, -320], a multiple of 16; the window fits STK = 12800).
     a7_lit_read        the same facts for a literal of PARSE_FILE_LITS, from sa_lit (sa_pinned and the
                        image range): what strncasecmp's "segment" needs.
     a7_rom             rt_rom_view at the cut's reader, from a7_obj's arodata_okP: rt_rom_view's in_rom is
                        in_roP's read-only-segment arm, and its two exclusions (owned statics, errno) are
                        arodata_okP's (the same derivation as A5's pf_a5_k.v a5_rom). So no Section
                        hypothesis is needed for it.
     a7_strchr_pre_87f74 / a7_ncase_pre_880dc / a7_strlen_pre_88338
                        each call's premise list, in the order its _realizes text states it.
     a7_keep_art        after an art_post call (aj_art_at / aj_art_atF) the cut's a7_st holds again at the
                        call's new memory, from the journal step and the keep clause outside the window.

   No Section hypothesis: the file is closed over the listing instance PI and the symbols B. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a7_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require PaArt reac_segconf_parse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the 8-byte shadow hull of a sub-range lies inside the hull of the range *)
Lemma a7_hull_sub : forall (rd : reader) q n q' n', shadow_hull_vis rd q n -> q <= q' -> 0 < n' ->
  q' + n' <= q + n -> shadow_hull_vis rd q' n'.
Proof.
  intros rd q n q' n' H Hq Hn Hle s Hs. apply H.
  pose proof (shadow_mono q q' Hq) as M1.
  pose proof (shadow_mono (q' + n' - 1) (q + n - 1) ltac:(lia)) as M2.
  assert (R8 : forall u w, u <= w -> u / 8 * 8 <= w / 8 * 8)
    by (intros u w Huw; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
  pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* sa_addr of a sub-range *)
Lemma a7_sa_addr_sub : forall (rd : reader) q n q' n', sa_addr rd q n -> q <= q' -> 0 <= n' ->
  q' + n' <= q + n -> sa_addr rd q' n'.
Proof.
  intros rd q n q' n' (A0 & A1 & A2 & A3 & A4) Hq Hn Hle.
  split; [lia|]. split; [lia|].
  split; [unfold amem_range in *; destruct A2 as [A2|A2]; [left; lia | right; lia]|].
  split; [eapply range_addressable_sub; [exact A3 | lia | lia]|].
  intros Hn'. exact (a7_hull_sub rd q n q' n' (A4 ltac:(lia)) Hq Hn' Hle).
Qed.

(* every byte of a C string and its NUL is mapped *)
Lemma a7_str_some : forall (rd : reader) p s a, sa_str rd p s -> p <= a <= p + Z.of_nat (length s) ->
  rd a <> None.
Proof.
  intros rd p s a [[Hz _] _] Ha.
  assert (Hi : (Z.to_nat (a - p) < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (Hz _ Hi) as E. rewrite Z2Nat.id in E by lia.
  replace (p + (a - p)) with a in E by lia. rewrite E. discriminate.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(** ** 1. The text bridge: sa_str (list Z) to astr_at / astr_atR (list byte) *)
Lemma a7_astr_of_sa : forall (W : world SEGS) mem q l,
  sa_str (rdW W mem) q l ->
  astr_at SEGS W mem q (seg_spec.zb l) /\ astr_atR (rdW W mem) q (seg_spec.zb l) /\
  astr_len (seg_spec.zb l) = Z.of_nat (length l) /\ seg_spec.zs (seg_spec.zb l) = l /\
  atail_vis SEGS W mem (q + astr_len (seg_spec.zb l)).
Proof.
  intros W mem q l [Hz Ht].
  destruct (sa_strz_bytes SEGS (w_H W) mem q l Hz) as (Hb & Hn & Hzs).
  assert (HR : astr_atR (rdW W mem) q (seg_spec.zb l)) by (split; [exact Hb | exact Hn]).
  assert (HL : astr_len (seg_spec.zb l) = Z.of_nat (length l))
    by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
  split; [apply astr_atR_view; exact HR|].
  split; [exact HR|]. split; [exact HL|]. split; [exact Hzs|].
  rewrite HL. exact Ht.
Qed.

(** ** A range parse_file's memory holds, as aread_ok *)
Lemma a7_read_ok_of_addr : forall (W : world SEGS) regs mem stk q n,
  sa_addr (rdW W mem) q n -> 0 <= n < 2 ^ 32 ->
  (forall a, q <= a < q + n -> rdW W mem a <> None) -> q + n <= spZ regs - stk ->
  aread_ok SEGS stk W regs mem q n.
Proof.
  intros W regs mem stk q n (A0 & A1 & A2 & A3 & A4) Hn Hm Hw.
  split; [exact A0|]. split; [exact A1|]. split; [exact Hn|].
  split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
  intros a Ha. split; [exact (Hm a Ha)|]. unfold ascratch_stk. lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** ** The read-only view at the cut's reader *)
(* rt_rom_view (RtDefs.v) is arodata_okP's read-only-segment arm: in_rom is in_roP's first disjunct, and the
   two exclusions are the same (aerrno_cell B a unfolds to arodata_okP's errno range). As segment A5's pf_a5_k.v
   a5_rom (commit 385fd095481f), from a7_obj in place of pf_base. *)
Lemma a7_rom : forall v pos lyc Sc Wc memc mdc, a7_st B v pos lyc Sc Wc memc mdc ->
  rt_rom_view SEGS B Wc memc.
Proof.
  intros v pos lyc Sc Wc memc mdc [_ _ _ _ Hobj _].
  destruct Hobj as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
  intros a (sg & Hsg & Hw & Hr) Ho He.
  exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
Qed.

(** ** The stack at a cut of A7: sp0, s1 = pf_s1, and the windows of the calls made at s1 *)
Lemma a7_stk : forall v pos lyc Sc Wc memc mdc, a7_st B v pos lyc Sc Wc memc mdc ->
  pf_sp0 v mod 16 = 0 /\ alloc_ceiling <= ly_stk_lo lyc /\
  ly_stk_lo lyc + STK_reac_segconf_parse_file <= pf_sp0 v /\
  pf_s1 v mod 32 = 0 /\ pf_sp0 v - 336 <= pf_s1 v <= pf_sp0 v - 320 /\ (pf_s1 v - pf_sp0 v) mod 16 = 0.
Proof.
  intros v pos lyc Sc Wc memc mdc [_ Hj Ely _ _ _].
  pose proof Hj as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (Hal16 & _ & Hceil & Hslo & _).
  subst lyc.
  pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)) as D0.
  pose proof (Z.div_mod (pf_sp0 v - 0x140) 32 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (pf_sp0 v - 0x140) 32 ltac:(lia)) as M1.
  assert (E1 : pf_s1 v = 32 * ((pf_sp0 v - 0x140) / 32)) by (unfold pf_s1; lia).
  pose proof (Z.div_mod (pf_s1 v) 32 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (pf_s1 v) 32 ltac:(lia)) as M2.
  pose proof (Z.div_mod (pf_s1 v - pf_sp0 v) 16 ltac:(lia)) as D3.
  pose proof (Z.mod_pos_bound (pf_s1 v - pf_sp0 v) 16 ltac:(lia)) as M3.
  split; [exact Hal16|]. split; [exact Hceil|]. split; [exact Hslo|].
  split; [lia|]. split; [lia|]. lia.
Qed.

(* a call made at s1 with a window stk <= 3 * ESTACK: the window lies above alloc_ceiling, fits the layout's
   stack, and fits parse_file's STK (12800 = 320 + 16 + 12464, SegInstA.STK_values) *)
Lemma a7_win : forall v pos lyc Sc Wc memc mdc stk, a7_st B v pos lyc Sc Wc memc mdc ->
  0 <= stk <= 3 * ESTACK ->
  ly_stk_lo lyc + stk <= pf_s1 v /\ alloc_ceiling <= pf_s1 v - stk /\
  stk - (pf_s1 v - pf_sp0 v) <= STK_reac_segconf_parse_file.
Proof.
  intros v pos lyc Sc Wc memc mdc stk H Hs.
  destruct (a7_stk v pos lyc Sc Wc memc mdc H) as (_ & Hc & Hlo & _ & Hs1 & _).
  pose proof STK_values as (_ & _ & _ & E & _). unfold ESTACK in Hs.
  rewrite E in Hlo |- *. lia.
Qed.

(* every byte of the class-5 frame is mapped (AR_laws' al_frames: a live frame's bytes are present) *)
Lemma a7_frame_some : forall v pos lyc Sc Wc memc mdc a, a7_st B v pos lyc Sc Wc memc mdc ->
  pf_F v pos <= a < pf_F v pos + 2048 -> rdW Wc memc a <> None.
Proof.
  intros v pos lyc Sc Wc memc mdc a H Ha.
  pose proof (a7_AR B v pos lyc Sc Wc memc mdc H) as HAR.
  pose proof (a7_fin B v pos lyc Sc Wc memc mdc H) as Hfin.
  destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hfin) as (_ & _ & Hpres & _).
  destruct H as [_ _ Ely _ _ _]. subst lyc.
  apply (aview_some_of_apresent SEGS). apply (Hpres a).
  unfold pf_F in Ha. rewrite a7_fb5. exact Ha.
Qed.

(** ** 2. aread_ok of a range of buf at a call made at s1 *)
Lemma a7_read_ok_buf : forall v pos lyc Sc Wc memc mdc regsc stk q n, a7_st B v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> 0 <= stk <= 3 * ESTACK ->
  a7_buf v pos <= q -> 0 <= n -> q + n <= a7_buf v pos + 512 ->
  aread_ok SEGS stk Wc regsc memc q n.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc stk q n H Hsp Hs Hq Hn Hqn.
  pose proof (a7_addr_buf B v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn) as HA.
  destruct (a7_frame_rng B v pos lyc Sc Wc memc mdc H) as (_ & F2 & _ & _).
  destruct (a7_win v pos lyc Sc Wc memc mdc stk H Hs) as (_ & W2 & _).
  unfold a7_buf, PF_O_BUF in Hq, Hqn.
  apply a7_read_ok_of_addr; [exact HA | lia | | rewrite Hsp; lia].
  intros a Ha. apply (a7_frame_some v pos lyc Sc Wc memc mdc a H). lia.
Qed.

(** ** 3. amem_range of a range of the class-5 frame *)
Lemma a7_amem_frame : forall v pos lyc Sc Wc memc mdc q n, a7_st B v pos lyc Sc Wc memc mdc ->
  pf_F v pos <= q -> 0 <= n -> q + n <= pf_F v pos + 2048 -> amem_range q n.
Proof.
  intros v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn.
  destruct (a7_frame_rng B v pos lyc Sc Wc memc mdc H) as (H1 & H2 & H3 & _).
  apply amem_range_high; [lia| |lia].
  destruct H3 as [_ [Hlo | [Hhi1 Hhi2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
    [left; lia | right; lia].
Qed.

(** ** 4. atail_vis at a NUL inside buf *)
Lemma a7_tail_vis_buf : forall v pos lyc Sc Wc memc mdc e, a7_st B v pos lyc Sc Wc memc mdc ->
  a7_buf v pos <= e < a7_buf v pos + 512 -> atail_vis SEGS Wc memc e.
Proof.
  intros v pos lyc Sc Wc memc mdc e H He a Ha.
  destruct (a7_frame_rng B v pos lyc Sc Wc memc mdc H) as (H1 & _ & _ & H4).
  unfold a7_buf, PF_O_BUF in He.
  pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D0.
  pose proof (Z.div_mod e 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as M1.
  apply (a7_frame_some v pos lyc Sc Wc memc mdc a H). lia.
Qed.

(** ** 5. The runtime-call pre-state at a call of A7 *)
Lemma a7_ecall_pre_buf : forall v pos lyc Sc Wc memc mdc regsc stk, a7_st B v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> ESTACK <= stk <= 3 * ESTACK ->
  YK0s.ret_ok (getr regsc 1) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  ecall_pre_stk SEGS B stk lyc Sc Wc regsc memc mdc.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc stk H Hsp Hs Hra Hgp Htp.
  destruct (a7_stk v pos lyc Sc Wc memc mdc H) as (_ & _ & _ & _ & Hs1 & Hal).
  destruct (a7_win v pos lyc Sc Wc memc mdc stk H ltac:(unfold ESTACK in *; lia)) as (_ & _ & Hbud).
  destruct H as [_ Hj _ _ _ _].
  apply (PaArt.ecall_pre_stk_at SEGS B stk STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
    (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 regsc (pf_s1 v - pf_sp0 v) Hj);
    [lia | exact Hal | lia | exact (proj1 Hs) | exact Hbud | exact Hra | exact Hgp | exact Htp].
Qed.

(** ** A literal of PARSE_FILE_LITS at a call made at s1 (sa_lit of a7_obj: sa_pinned, sa_img, the bytes) *)
Lemma a7_lit_read : forall v pos lyc Sc Wc memc mdc regsc stk s m, a7_st B v pos lyc Sc Wc memc mdc ->
  In s PARSE_FILE_LITS -> spZ regsc = pf_s1 v -> 0 <= stk <= 3 * ESTACK ->
  0 <= m <= Z.of_nat (length s) + 1 ->
  0 < seg_litA_rc s /\
  astr_at SEGS Wc memc (seg_litA_rc s) (seg_spec.zb s) /\ astr_len (seg_spec.zb s) = Z.of_nat (length s) /\
  aread_ok SEGS stk Wc regsc memc (seg_litA_rc s) m /\
  amem_range (seg_litA_rc s) (Z.of_nat (length s) + 8) /\
  atail_vis SEGS Wc memc (seg_litA_rc s + Z.of_nat (length s)).
Proof.
  intros v pos lyc Sc Wc memc mdc regsc stk s m H Hin Hsp Hs Hm.
  pose proof (a7_AR B v pos lyc Sc Wc memc mdc H) as HAR.
  destruct (a7_win v pos lyc Sc Wc memc mdc stk H Hs) as (_ & W2 & _).
  destruct H as [_ _ _ _ Hobj _].
  destruct Hobj as (_ & _ & _ & _ & _ & _ & HL & _).
  destruct (HL s Hin) as (Ha & Hstr & Hp & _ & Hi).
  destruct (a7_astr_of_sa Wc memc _ s Hstr) as (HA & _ & HLn & _ & HT).
  pose proof (Hp lyc Sc Wc memc mdc HAR) as HP.
  pose proof (proj1 (Hi (seg_litA_rc s + Z.of_nat (length s)) ltac:(lia))) as Himg.
  pose proof (pa_img_range _ Himg) as Hrg.
  pose proof asan_consts as (C1 & _ & _ & _ & C5). unfold kImgEnd in Hrg.
  split; [exact Ha|]. split; [exact HA|]. split; [exact HLn|].
  split; [|split].
  - apply a7_read_ok_of_addr.
    + apply (a7_sa_addr_sub _ _ _ _ _ HP); lia.
    + lia.
    + intros a Ha'. apply (a7_str_some _ _ _ a Hstr). lia.
    + rewrite Hsp. lia.
  - unfold amem_range. left. rewrite C5. lia.
  - rewrite HLn in HT. exact HT.
Qed.

(** ** 6. The premise lists of the three interceptor calls *)
(* strchr(lp, ']') at 0x87f74 (0x87f6c `addi a1, zero, 0x5d`, 0x87f70 `mv a0, s7`): RtSeg.astrchr_realizes's
   premises in its order, for the C string l at x in buf (at HDR, x = lp and l = the trimmed line) *)
Lemma a7_strchr_pre_87f74 : forall v pos lyc Sc Wc memc mdc regsc x l,
  a7_st B v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 10 = w64 x -> getr regsc 11 = w64 0x5d ->
  sa_str (rdW Wc memc) x l -> pf_inb (pf_F v pos + PF_O_BUF) x l ->
  ecall_pre_stk SEGS B (2 * ESTACK) lyc Sc Wc regsc memc mdc /\
  getr regsc 10 = w64 x /\ getr regsc 11 = w64 0x5d /\ 0 < 0x5d < 256 /\ 0 < x /\
  astr_at SEGS Wc memc x (seg_spec.zb l) /\
  aread_ok SEGS (2 * ESTACK) Wc regsc memc x (astr_len (seg_spec.zb l) + 1) /\
  amem_range x (astr_len (seg_spec.zb l) + 8) /\
  atail_vis SEGS Wc memc (x + astr_len (seg_spec.zb l)) /\
  rt_rom_view SEGS B Wc memc.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc x l H Hsp Hra Hgp Htp H10 H11 Hs [Hb Hl].
  destruct (a7_astr_of_sa Wc memc x l Hs) as (HA & _ & HLn & _ & HT).
  destruct (a7_frame_rng B v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
  unfold PF_O_BUF in Hb, Hl.
  split; [exact (a7_ecall_pre_buf v pos lyc Sc Wc memc mdc regsc (2 * ESTACK) H Hsp
                   ltac:(unfold ESTACK; lia) Hra Hgp Htp)|].
  split; [exact H10|]. split; [exact H11|]. split; [lia|]. split; [lia|].
  split; [exact HA|].
  split; [rewrite HLn; apply (a7_read_ok_buf v pos lyc Sc Wc memc mdc regsc);
          [exact H | exact Hsp | unfold ESTACK; lia | unfold a7_buf, PF_O_BUF; lia | lia
          | unfold a7_buf, PF_O_BUF; lia]|].
  split; [rewrite HLn; apply (a7_amem_frame v pos lyc Sc Wc memc mdc); [exact H | lia | lia | lia]|].
  split; [exact HT|].
  exact (a7_rom v pos lyc Sc Wc memc mdc H).
Qed.

(* strncasecmp(body, "segment", 7) at 0x880dc (0x880cc-0x880d0 a1 = .str.6 0x214a0 = seg_litA_rc S_segment,
   0x880d4 `addi a2, zero, 7`, 0x880d8 `mv a0, s3`): RtSeg.astrncasecmp_realizes's premises in its order, for
   the C string l at x in buf (the trimmed body); the literal's facts from a7_obj's sa_lit *)
Lemma a7_ncase_pre_880dc : forall v pos lyc Sc Wc memc mdc regsc x l,
  a7_st B v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 10 = w64 x -> getr regsc 11 = w64 (seg_litA_rc S_segment) -> getr regsc 12 = w64 7 ->
  sa_str (rdW Wc memc) x l -> pf_inb (pf_F v pos + PF_O_BUF) x l ->
  ecall_pre_stk SEGS B (2 * ESTACK) lyc Sc Wc regsc memc mdc /\
  getr regsc 10 = w64 x /\ getr regsc 11 = w64 (seg_litA_rc S_segment) /\ getr regsc 12 = w64 7 /\
  0 <= 7 < 2 ^ 32 /\ 0 < x /\ 0 < seg_litA_rc S_segment /\
  astr_at SEGS Wc memc x (seg_spec.zb l) /\ astr_at SEGS Wc memc (seg_litA_rc S_segment) (seg_spec.zb S_segment) /\
  aread_ok SEGS (2 * ESTACK) Wc regsc memc x (Z.min 7 (astr_len (seg_spec.zb l) + 1)) /\
  amem_range x (astr_len (seg_spec.zb l) + 8) /\
  aread_ok SEGS (2 * ESTACK) Wc regsc memc (seg_litA_rc S_segment)
    (Z.min 7 (astr_len (seg_spec.zb S_segment) + 1)) /\
  amem_range (seg_litA_rc S_segment) (astr_len (seg_spec.zb S_segment) + 8) /\
  atail_vis SEGS Wc memc (x + astr_len (seg_spec.zb l)) /\
  atail_vis SEGS Wc memc (seg_litA_rc S_segment + astr_len (seg_spec.zb S_segment)) /\
  rt_rom_view SEGS B Wc memc.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc x l H Hsp Hra Hgp Htp H10 H11 H12 Hs [Hb Hl].
  (* "segment" is the seventh text of PARSE_FILE_LITS (reac_segconf_parse_file_c.v:126) *)
  assert (HIN : In S_segment PARSE_FILE_LITS)
    by (unfold PARSE_FILE_LITS; apply in_or_app; left; do 6 right; left; reflexivity).
  assert (L7 : Z.of_nat (length S_segment) = 7) by (vm_compute; reflexivity).
  assert (L7b : astr_len (seg_spec.zb S_segment) = 7)
    by (unfold astr_len, seg_spec.zb; rewrite length_map; exact L7).
  destruct (a7_lit_read v pos lyc Sc Wc memc mdc regsc (2 * ESTACK) S_segment
    (Z.min 7 (astr_len (seg_spec.zb S_segment) + 1)) H HIN Hsp ltac:(unfold ESTACK; lia)
    ltac:(rewrite L7b, L7; lia)) as (Ly0 & LyA & LyL & LyR & LyM & LyT).
  destruct (a7_astr_of_sa Wc memc x l Hs) as (HA & _ & HLn & _ & HT).
  destruct (a7_frame_rng B v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
  unfold PF_O_BUF in Hb, Hl.
  split; [exact (a7_ecall_pre_buf v pos lyc Sc Wc memc mdc regsc (2 * ESTACK) H Hsp
                   ltac:(unfold ESTACK; lia) Hra Hgp Htp)|].
  split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [lia|]. split; [lia|].
  split; [exact Ly0|]. split; [exact HA|]. split; [exact LyA|].
  split; [rewrite HLn; apply (a7_read_ok_buf v pos lyc Sc Wc memc mdc regsc);
          [exact H | exact Hsp | unfold ESTACK; lia | unfold a7_buf, PF_O_BUF; lia | lia
          | unfold a7_buf, PF_O_BUF; lia]|].
  split; [rewrite HLn; apply (a7_amem_frame v pos lyc Sc Wc memc mdc); [exact H | lia | lia | lia]|].
  split; [exact LyR|].
  split; [rewrite LyL; exact LyM|].
  split; [exact HT|].
  split; [rewrite LyL; exact LyT|].
  exact (a7_rom v pos lyc Sc Wc memc mdc H).
Qed.

(* strlen(name) at 0x88338 (0x88334 `mv a0, s9`): RtString.astrlen_realizes's premises in its order, for the
   C string l at x in buf (the trimmed name) *)
Lemma a7_strlen_pre_88338 : forall v pos lyc Sc Wc memc mdc regsc x l,
  a7_st B v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 10 = w64 x ->
  sa_str (rdW Wc memc) x l -> pf_inb (pf_F v pos + PF_O_BUF) x l ->
  ecall_pre_stk SEGS B ESTACK lyc Sc Wc regsc memc mdc /\
  getr regsc 10 = w64 x /\ 0 < x /\
  astr_at SEGS Wc memc x (seg_spec.zb l) /\
  aread_ok SEGS ESTACK Wc regsc memc x (astr_len (seg_spec.zb l) + 1) /\
  atail_vis SEGS Wc memc (x + astr_len (seg_spec.zb l)) /\
  rt_rom_view SEGS B Wc memc.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc x l H Hsp Hra Hgp Htp H10 Hs [Hb Hl].
  destruct (a7_astr_of_sa Wc memc x l Hs) as (HA & _ & HLn & _ & HT).
  destruct (a7_frame_rng B v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
  unfold PF_O_BUF in Hb, Hl.
  split; [exact (a7_ecall_pre_buf v pos lyc Sc Wc memc mdc regsc ESTACK H Hsp
                   ltac:(unfold ESTACK; lia) Hra Hgp Htp)|].
  split; [exact H10|]. split; [lia|].
  split; [exact HA|].
  split; [rewrite HLn; apply (a7_read_ok_buf v pos lyc Sc Wc memc mdc regsc);
          [exact H | exact Hsp | unfold ESTACK; lia | unfold a7_buf, PF_O_BUF; lia | lia
          | unfold a7_buf, PF_O_BUF; lia]|].
  split; [exact HT|].
  exact (a7_rom v pos lyc Sc Wc memc mdc H).
Qed.

(** ** 7. After an art_post call: a7_st again at the call's new memory *)
(* the caller's objects carry over to a reader that agrees below alloc_ceiling, at a state with AR: the text's
   and the block's bytes and shadow (sa_addr re-derived from the live blocks, reac_segconf_parse.v
   sa_addr_of_heap), the catalogue, the literals, the read-only window, the stack-protector cells *)
Lemma a7_obj_low : forall v lyc Sc (Wc : world SEGS) memc memc' mdc',
  AR SEGS B lyc Sc Wc memc' mdc' -> pf_obj B v lyc Sc (rdW Wc memc) ->
  (forall a, 0 <= a < alloc_ceiling -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_obj B v lyc Sc (rdW Wc memc').
Proof.
  intros v lyc Sc Wc memc memc' mdc' HAR' (Ht & At & Ht2 & Ac & Hc & CAT & LITS & ROD & SSP) LK.
  assert (Ht0 : 0 <= p_t v) by (destruct At; lia).
  assert (Hc0 : 0 <= p_c v) by (destruct Ac; lia).
  destruct (reac_segconf_parse.sa_addr_of_heap B lyc Sc Wc memc' mdc' (p_t v) (pf_len v) HAR' Ht2 Ht0
    ltac:(unfold pf_len; lia)) as [At' Hte].
  destruct (reac_segconf_parse.sa_addr_of_heap B lyc Sc Wc memc' mdc' (p_c v) seg_spec.SEG_C_SIZE HAR' Hc Hc0
    ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [Ac' _].
  split; [apply (reac_segconf_parse.sa_str_low _ _ _ _ Ht); [exact Ht0 | unfold pf_len in Hte; lia | exact LK]|].
  split; [exact At'|]. split; [exact Ht2|]. split; [exact Ac'|]. split; [exact Hc|].
  split; [exact (reac_segconf_parse.sa_cat_low B _ _ CAT LK)|].
  split; [intros x Hx; exact (reac_segconf_parse.sa_lit_low B _ _ _ _ (LITS x Hx) LK)|].
  split; [|exact (reac_segconf_parse.sa_ssp_low _ _ SSP LK)].
  intros a Hro Ho He.
  assert (Ha : 0 <= a < alloc_ceiling).
  { pose proof asan_consts as (C1 & _).
    destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
    - assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
      pose proof (pa_img_range a Hi) as Hrg. unfold kImgEnd in Hrg. lia.
    - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. lia. }
  rewrite (LK a Ha). exact (ROD a Hro Ho He).
Qed.

(* What aj_art_at (PaArt.v) / aj_art_atF (PaFx.v) return after a call made at sp0 + o with window stk and no
   written cells (Eb = fun _ => False): the journal at the new memory memc' and the keep clause outside
   [sp0 + o - stk, sp0 + o). Every fact of a7_st other than the journal is about bytes below alloc_ceiling
   (the heap text and block, image literals and cells, the frame's shadow), which the journal's astk_ok puts
   below sp0 - STK <= sp0 + o - stk, so the keep clause keeps them all. *)
Lemma a7_keep_art : forall v pos lyc Sc Wc memc mdc memc' mdc' o stk,
  a7_st B v pos lyc Sc Wc memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
    (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  stk - o <= STK_reac_segconf_parse_file ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_sp0 v + o - stk <= a < pf_sp0 v + o) -> ~ (fun _ : Z => False) a ->
     rdW Wc memc' a = rdW Wc memc a) ->
  a7_st B v pos lyc Sc Wc memc' mdc'.
Proof.
  intros v pos lyc Sc Wc memc mdc memc' mdc' o stk H HJ' Hbud HK.
  destruct (a7_stk v pos lyc Sc Wc memc mdc H) as (_ & Hceil & Hslo & _).
  destruct (a7_frame_rng B v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
  pose proof asan_consts as (C1 & C2 & _ & C4 & C5).
  assert (LK : forall a, 0 <= a < alloc_ceiling -> rdW Wc memc' a = rdW Wc memc a).
  { intros a Ha. apply HK; [lia | lia | intros Hf; exact Hf]. }
  pose proof (proj1 HJ') as HAR'.
  pose proof (shadow_addr_bounds (pf_F v pos) ltac:(rewrite C4; lia)) as HSB.
  rewrite C2, C5 in HSB.
  destruct H as [Hcx _ Ely Hperm Hobj Hfsh].
  constructor.
  - exact Hcx.
  - exact HJ'.
  - exact Ely.
  - exact Hperm.
  - exact (a7_obj_low v lyc Sc Wc memc memc' mdc' HAR' Hobj LK).
  - intros i Hi.
    assert (HS : 0 <= pf_SH v pos + i < alloc_ceiling) by (unfold pf_SH; lia).
    rewrite (LK _ HS). exact (Hfsh i Hi).
Qed.

End e.
End f.
End d.
