(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 408 of its 431 lines of code are new or changed and 495 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the kit of stretch SA9_A of segment A9 of
   reac_segconf_parse_file's walk (KEY 0x87fac -> REF3 / K2 0x87fe4; segment A9's proof, by the G3 walk owner, 2026-10-30).
   No instruction is walked here: these are the facts the walk file lib/A/Prog/pf_a9_s1.v reads at its two calls.

   - s1_st and the buf facts (s1_addr_buf, s1_fframe_buf, ...): segment A7's a7_st and its lemmas,
     lib/A/Prog/pf_a7_d.v (commit 0c85038238f5), renamed a7_ -> s1_.
   - the strchr premise list (s1_strchr_pre) and its helpers: segment A7's pf_a7_r.v (commit
     ebe0b30cca65) a7_strchr_pre_87f74 with the byte '=' (0x3d) in place of ']' (0x5d), renamed a7_ -> s1_.
   - the trim call's premise list (s1_trim_call, s1_trim_site_ok): segment A7's pf_a7_s.v (commit
     980fbe9c6015) a7_trim_call / a7_trim_site_ok, renamed; trim_site_ok_87fdc is rule 1j-bis for the call
     trim(line) at 0x87fdc, after the store `sb zero, 0(eq)` at 0x87fd4.
   - s1_move: THE transport of a9_core (pf_a9_d.v) across a step or a call whose writes miss A5's write set
     a5_Wrx v pos false false (the stack below s1 and buf): the strchr interceptor (its 2 * ESTACK window), the
     store at eq (in buf), and trim (its STK_trim window and the one NUL byte it writes in buf). Built on
     pf_a5_k.v's a5_move0 / a5_keep_st / a5_keep_slot / a5_keep_fsh: no Section hypothesis.
   - the bytes of buf after the store and after trim (s1_key_after, s1_rest_after, ...): the key's C string at
     kp = lp + trim_lead K and the rest of the line at eq + 1, K = firstn ei line.
   No Section hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  trim_c pf_pieces pf_a5_d pf_a5_k pf_a9_d pf_a9_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ============================== lists, readers (no machine state) ============================== *)
(* the 8-byte shadow hull of a sub-range lies inside the hull of the range (pf_a7_r.v a7_hull_sub) *)
Lemma s1_hull_sub : forall (rd : reader) q n q' n', shadow_hull_vis rd q n -> q <= q' -> 0 < n' ->
  q' + n' <= q + n -> shadow_hull_vis rd q' n'.
Proof.
  intros rd q n q' n' H Hq Hn Hle s Hs. apply H.
  pose proof (shadow_mono q q' Hq) as M1.
  pose proof (shadow_mono (q' + n' - 1) (q + n - 1) ltac:(lia)) as M2.
  assert (R8 : forall u w, u <= w -> u / 8 * 8 <= w / 8 * 8)
    by (intros u w Huw; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
  pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* every byte of a C string and its NUL is mapped (pf_a7_r.v a7_str_some) *)
Lemma s1_str_some : forall (rd : reader) p s a, sa_str rd p s -> p <= a <= p + Z.of_nat (length s) ->
  rd a <> None.
Proof.
  intros rd p s a [[Hz _] _] Ha.
  assert (Hi : (Z.to_nat (a - p) < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (Hz _ Hi) as E. rewrite Z2Nat.id in E by lia.
  replace (p + (a - p)) with a in E by lia. rewrite E. discriminate.
Qed.

(* the i-th byte of a C string through the reader *)
Lemma s1_str_nth : forall (rd : reader) p s i, sa_str rd p s -> (i <= length s)%nat ->
  rd (p + Z.of_nat i) = Some (nth i (s ++ [0]) 0).
Proof.
  intros rd p s i [[Hz _] _] Hi. apply Hz. rewrite length_app. cbn [length]. lia.
Qed.

(* the mapped span of a C string at p: its bytes, its NUL and the slack to the next 8-byte boundary *)
Definition s1_span (p : Z) (s : list Z) : Z := p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8.
Lemma s1_span_some : forall (rd : reader) p s x, sa_str rd p s -> p <= x < s1_span p s -> rd x <> None.
Proof.
  intros rd p s x Hs Hx. unfold s1_span in Hx.
  destruct (Z_le_gt_dec x (p + Z.of_nat (length s))) as [H1 | H1].
  - exact (s1_str_some rd p s x Hs ltac:(lia)).
  - destruct Hs as [_ Ht]. apply Ht. lia.
Qed.
Lemma s1_span_mono : forall p s e, p <= e <= p + Z.of_nat (length s) ->
  e - e mod 8 + 8 <= s1_span p s.
Proof.
  intros p s e He. unfold s1_span.
  pose proof (Z.div_mod e 8 ltac:(lia)). pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
  pose proof (Z.div_mod (p + Z.of_nat (length s)) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
  assert (e / 8 <= (p + Z.of_nat (length s)) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

(* a C string out of its bytes, the NUL and a mapped slack *)
Lemma s1_sa_str_of : forall (rd : reader) q l,
  (forall i, (i < length l)%nat -> rd (q + Z.of_nat i) = Some (nth i l 0)) ->
  rd (q + Z.of_nat (length l)) = Some 0 -> ~ In 0 l ->
  (forall x, q + Z.of_nat (length l) < x < q + Z.of_nat (length l) - (q + Z.of_nat (length l)) mod 8 + 8 ->
     rd x <> None) ->
  sa_str rd q l.
Proof.
  intros rd q l Hb H0 Hn Ht. split; [split|].
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i (length l)) as [Hl | Hl].
    + rewrite app_nth1 by exact Hl. exact (Hb i Hl).
    + assert (i = length l) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. exact H0.
  - exact Hn.
  - intros x Hx. exact (Ht x Hx).
Qed.

(* sa_addr of a sub-range (pf_a7_r.v a7_sa_addr_sub) *)
Lemma s1_sa_addr_sub : forall (rd : reader) q n q' n', sa_addr rd q n -> q <= q' -> 0 <= n' ->
  q' + n' <= q + n -> sa_addr rd q' n'.
Proof.
  intros rd q n q' n' (A0 & A1 & A2 & A3 & A4) Hq Hn Hle.
  split; [lia|]. split; [lia|].
  split; [unfold amem_range in *; destruct A2 as [A2|A2]; [left; lia | right; lia]|].
  split; [eapply range_addressable_sub; [exact A3 | lia | lia]|].
  intros Hn'. exact (s1_hull_sub rd q n q' n' (A4 ltac:(lia)) Hq Hn' Hle).
Qed.

Lemma s1_fb5 : fs_frame_bytes 5 = 2048.
Proof. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* sa_str (list Z) to astr_at / astr_atR (list byte) (pf_a7_r.v a7_astr_of_sa) *)
Lemma s1_astr_of_sa : forall (W : world SEGS) mem q l,
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

(* a range parse_file's memory holds, as aread_ok (pf_a7_r.v a7_read_ok_of_addr) *)
Lemma s1_read_ok_of_addr : forall (W : world SEGS) regs mem stk q n,
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

(* ============================== a cut of A9: the frame facts (pf_a7_d.v a7_st) ============================== *)
Record s1_st (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) : Prop := mkS1St {
  s1_cx : pf_cx B v;
  s1_j : ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
           (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0;
  s1_lyc : lyc = p_ly v;
  s1_perm : Permutation (ablocks B lyc Sc) (ablocks B (p_ly v) (p_S v));
  s1_obj : pf_obj B v lyc Sc (rdW Wc memc);
  s1_fsh_line : pf_fsh (rdW Wc memc) (pf_SH v pos) PF_SC_LINE
}.

Lemma s1_st_of_base : forall v pos lyc Sc Wc rX memc mdc,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> s1_st v pos lyc Sc Wc memc mdc.
Proof.
  intros v pos lyc Sc Wc rX memc mdc (HCX & (HJ & Hly & _ & HP & _) & HOBJ & _ & HFSH).
  exact (mkS1St v pos lyc Sc Wc memc mdc HCX HJ Hly HP HOBJ HFSH).
Qed.

Lemma s1_AR : forall v pos lyc Sc Wc memc mdc, s1_st v pos lyc Sc Wc memc mdc ->
  AR SEGS B lyc Sc Wc memc mdc.
Proof. intros v pos lyc Sc Wc memc mdc H. exact (proj1 (s1_j _ _ _ _ _ _ _ H)). Qed.

Lemma s1_fin : forall v pos lyc Sc Wc memc mdc, s1_st v pos lyc Sc Wc memc mdc ->
  In (5, pos) (frames Sc).
Proof.
  intros v pos lyc Sc Wc memc mdc H.
  pose proof (s1_j _ _ _ _ _ _ _ H) as (_ & _ & _ & _ & _ & Hfr & _).
  rewrite Hfr. left. reflexivity.
Qed.

Lemma s1_frame_rng : forall v pos lyc Sc Wc memc mdc, s1_st v pos lyc Sc Wc memc mdc ->
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ in_app (pf_F v pos) 2048 /\
  pf_F v pos mod 32 = 0.
Proof.
  intros v pos lyc Sc Wc memc mdc H.
  pose proof (s1_AR v pos lyc Sc Wc memc mdc H) as HAR.
  pose proof (s1_fin v pos lyc Sc Wc memc mdc H) as Hfin.
  destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hfin) as (H1 & H2 & H3).
  destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hfin) as (H4 & _ & _ & _).
  pose proof (s1_lyc _ _ _ _ _ _ _ H) as Ely.
  rewrite s1_fb5 in H2, H3. unfold pf_F. rewrite <- Ely.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

Lemma s1_sh_at : forall v pos lyc Sc Wc memc mdc x, s1_st v pos lyc Sc Wc memc mdc ->
  pf_F v pos + PF_O_BUF <= x < pf_F v pos + PF_O_BUF + 512 ->
  rdW Wc memc (shadow_of_addr SHADOW_OFF x) = Some 0.
Proof.
  intros v pos lyc Sc Wc memc mdc x H Hx.
  destruct (s1_frame_rng v pos lyc Sc Wc memc mdc H) as (H1 & H2 & _ & H4).
  unfold PF_O_BUF in Hx.
  assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
  replace x with (pf_F v pos + (x - pf_F v pos)) by lia.
  rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (x - pf_F v pos) HF8).
  change (shadow_of_addr SHADOW_OFF (pf_F v pos)) with (pf_SH v pos).
  rewrite (s1_fsh_line _ _ _ _ _ _ _ H ((x - pf_F v pos) / 8)).
  - f_equal. apply a9_shb_buf.
    split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia].
  - split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma s1_sh_some : forall v pos lyc Sc Wc memc mdc s, s1_st v pos lyc Sc Wc memc mdc ->
  pf_SH v pos <= s < pf_SH v pos + 144 -> rdW Wc memc s <> None.
Proof.
  intros v pos lyc Sc Wc memc mdc s H Hs.
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
  rewrite (s1_fsh_line _ _ _ _ _ _ _ H (s - pf_SH v pos) ltac:(lia)). discriminate.
Qed.

(* a range of buf is addressable, with its shadow mapped (pf_a7_d.v a7_addr_buf) *)
Lemma s1_addr_buf : forall v pos lyc Sc Wc memc mdc q n, s1_st v pos lyc Sc Wc memc mdc ->
  pf_F v pos + PF_O_BUF <= q -> 0 <= n -> q + n <= pf_F v pos + PF_O_BUF + 512 ->
  sa_addr (rdW Wc memc) q n.
Proof.
  intros v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn.
  destruct (s1_frame_rng v pos lyc Sc Wc memc mdc H) as (H1 & H2 & H3 & H4).
  pose proof alloc_ceiling_lt as HC.
  unfold PF_O_BUF in Hq, Hqn.
  assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
  split; [lia|]. split; [lia|].
  split.
  { apply amem_range_high; [lia| |lia].
    destruct H3 as [_ [Hlo | [Hhi1 Hhi2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
    [left; lia | right; lia]. }
  split.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    apply (s1_sh_at v pos lyc Sc Wc memc mdc x H). unfold PF_O_BUF. lia.
  - intros Hn0 s Hs.
    assert (E1 : shadow_addr q = pf_SH v pos + (q - pf_F v pos) / 8).
    { unfold shadow_addr. replace q with (pf_F v pos + (q - pf_F v pos)) at 1 by lia.
      change (SHADOW_OFF + (pf_F v pos + (q - pf_F v pos)) / 8)
        with (shadow_of_addr SHADOW_OFF (pf_F v pos + (q - pf_F v pos))).
      rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (q - pf_F v pos) HF8). reflexivity. }
    assert (E2 : shadow_addr (q + n - 1) = pf_SH v pos + (q + n - 1 - pf_F v pos) / 8).
    { unfold shadow_addr. replace (q + n - 1) with (pf_F v pos + (q + n - 1 - pf_F v pos)) at 1 by lia.
      change (SHADOW_OFF + (pf_F v pos + (q + n - 1 - pf_F v pos)) / 8)
        with (shadow_of_addr SHADOW_OFF (pf_F v pos + (q + n - 1 - pf_F v pos))).
      rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (q + n - 1 - pf_F v pos) HF8). reflexivity. }
    assert (B1 : 8 <= (q - pf_F v pos) / 8) by (apply Z.div_le_lower_bound; lia).
    assert (B2 : (q + n - 1 - pf_F v pos) / 8 < 72) by (apply Z.div_lt_upper_bound; lia).
    rewrite E1, E2 in Hs.
    apply (s1_sh_some v pos lyc Sc Wc memc mdc s H).
    pose proof (Z.div_mod (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as M1.
    pose proof (Z.div_mod (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as M2.
    lia.
Qed.

(* a range of buf lies in a live side-stack frame (pf_a7_d.v a7_fframe_buf) *)
Lemma s1_fframe_buf : forall v pos lyc Sc Wc memc mdc q n, s1_st v pos lyc Sc Wc memc mdc ->
  pf_F v pos + PF_O_BUF <= q -> 0 <= n -> q + n <= pf_F v pos + PF_O_BUF + 512 ->
  sa_fframe lyc Sc q n.
Proof.
  intros v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn.
  exists 5, pos. split; [exact (s1_fin v pos lyc Sc Wc memc mdc H)|].
  split; [lia|].
  pose proof (s1_lyc _ _ _ _ _ _ _ H) as Ely.
  unfold PF_O_BUF, pf_F in Hq, Hqn. rewrite <- Ely in Hq, Hqn.
  rewrite s1_fb5. lia.
Qed.

(* ============================== the strchr call (pf_a7_r.v) ============================== *)
Lemma s1_rom : forall v pos lyc Sc Wc memc mdc, s1_st v pos lyc Sc Wc memc mdc ->
  rt_rom_view SEGS B Wc memc.
Proof.
  intros v pos lyc Sc Wc memc mdc [_ _ _ _ Hobj _].
  destruct Hobj as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
  intros a (sg & Hsg & Hw & Hr) Ho He.
  exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
Qed.

Lemma s1_stk : forall v pos lyc Sc Wc memc mdc, s1_st v pos lyc Sc Wc memc mdc ->
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

Lemma s1_win : forall v pos lyc Sc Wc memc mdc stk, s1_st v pos lyc Sc Wc memc mdc ->
  0 <= stk <= 3 * ESTACK ->
  ly_stk_lo lyc + stk <= pf_s1 v /\ alloc_ceiling <= pf_s1 v - stk /\
  stk - (pf_s1 v - pf_sp0 v) <= STK_reac_segconf_parse_file.
Proof.
  intros v pos lyc Sc Wc memc mdc stk H Hs.
  destruct (s1_stk v pos lyc Sc Wc memc mdc H) as (_ & Hc & Hlo & _ & Hs1 & _).
  pose proof STK_values as (_ & _ & _ & E & _). unfold ESTACK in Hs.
  rewrite E in Hlo |- *. lia.
Qed.

Lemma s1_frame_some : forall v pos lyc Sc Wc memc mdc a, s1_st v pos lyc Sc Wc memc mdc ->
  pf_F v pos <= a < pf_F v pos + 2048 -> rdW Wc memc a <> None.
Proof.
  intros v pos lyc Sc Wc memc mdc a H Ha.
  pose proof (s1_AR v pos lyc Sc Wc memc mdc H) as HAR.
  pose proof (s1_fin v pos lyc Sc Wc memc mdc H) as Hfin.
  destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hfin) as (_ & _ & Hpres & _).
  destruct H as [_ _ Ely _ _ _]. subst lyc.
  apply (aview_some_of_apresent SEGS). apply (Hpres a).
  unfold pf_F in Ha. rewrite s1_fb5. exact Ha.
Qed.

Lemma s1_read_ok_buf : forall v pos lyc Sc Wc memc mdc regsc stk q n, s1_st v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> 0 <= stk <= 3 * ESTACK ->
  pf_F v pos + PF_O_BUF <= q -> 0 <= n -> q + n <= pf_F v pos + PF_O_BUF + 512 ->
  aread_ok SEGS stk Wc regsc memc q n.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc stk q n H Hsp Hs Hq Hn Hqn.
  pose proof (s1_addr_buf v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn) as HA.
  destruct (s1_frame_rng v pos lyc Sc Wc memc mdc H) as (_ & F2 & _ & _).
  destruct (s1_win v pos lyc Sc Wc memc mdc stk H Hs) as (_ & W2 & _).
  unfold PF_O_BUF in Hq, Hqn.
  apply s1_read_ok_of_addr; [exact HA | lia | | rewrite Hsp; lia].
  intros a Ha. apply (s1_frame_some v pos lyc Sc Wc memc mdc a H). lia.
Qed.

Lemma s1_amem_frame : forall v pos lyc Sc Wc memc mdc q n, s1_st v pos lyc Sc Wc memc mdc ->
  pf_F v pos <= q -> 0 <= n -> q + n <= pf_F v pos + 2048 -> amem_range q n.
Proof.
  intros v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn.
  destruct (s1_frame_rng v pos lyc Sc Wc memc mdc H) as (H1 & H2 & H3 & _).
  apply amem_range_high; [lia| |lia].
  destruct H3 as [_ [Hlo | [Hhi1 Hhi2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
    [left; lia | right; lia].
Qed.

Lemma s1_ecall_pre_buf : forall v pos lyc Sc Wc memc mdc regsc stk, s1_st v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> ESTACK <= stk <= 3 * ESTACK ->
  YK0s.ret_ok (getr regsc 1) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  ecall_pre_stk SEGS B stk lyc Sc Wc regsc memc mdc.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc stk H Hsp Hs Hra Hgp Htp.
  destruct (s1_stk v pos lyc Sc Wc memc mdc H) as (_ & _ & _ & _ & Hs1 & Hal).
  destruct (s1_win v pos lyc Sc Wc memc mdc stk H ltac:(unfold ESTACK in *; lia)) as (_ & _ & Hbud).
  destruct H as [_ Hj _ _ _ _].
  apply (PaArt.ecall_pre_stk_at SEGS B stk STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
    (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 regsc (pf_s1 v - pf_sp0 v) Hj);
    [lia | exact Hal | lia | exact (proj1 Hs) | exact Hbud | exact Hra | exact Hgp | exact Htp].
Qed.

(* strchr(lp, '=') at 0x87fb4 (0x87fac `addi a1, zero, 0x3d`, 0x87fb0 `mv a0, s7`): RtSeg.astrchr_realizes's
   premises in its order, for the C string l at x in buf (pf_a7_r.v a7_strchr_pre_87f74 with 0x3d) *)
Lemma s1_strchr_pre : forall v pos lyc Sc Wc memc mdc regsc x l,
  s1_st v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 10 = w64 x -> getr regsc 11 = w64 0x3d ->
  sa_str (rdW Wc memc) x l -> pf_inb (pf_F v pos + PF_O_BUF) x l ->
  ecall_pre_stk SEGS B (2 * ESTACK) lyc Sc Wc regsc memc mdc /\
  getr regsc 10 = w64 x /\ getr regsc 11 = w64 0x3d /\ 0 < 0x3d < 256 /\ 0 < x /\
  astr_at SEGS Wc memc x (seg_spec.zb l) /\
  aread_ok SEGS (2 * ESTACK) Wc regsc memc x (astr_len (seg_spec.zb l) + 1) /\
  amem_range x (astr_len (seg_spec.zb l) + 8) /\
  atail_vis SEGS Wc memc (x + astr_len (seg_spec.zb l)) /\
  rt_rom_view SEGS B Wc memc.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc x l H Hsp Hra Hgp Htp H10 H11 Hs [Hb Hl].
  destruct (s1_astr_of_sa Wc memc x l Hs) as (HA & _ & HLn & _ & HT).
  destruct (s1_frame_rng v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
  unfold PF_O_BUF in Hb, Hl.
  split; [exact (s1_ecall_pre_buf v pos lyc Sc Wc memc mdc regsc (2 * ESTACK) H Hsp
                   ltac:(unfold ESTACK; lia) Hra Hgp Htp)|].
  split; [exact H10|]. split; [exact H11|]. split; [lia|]. split; [lia|].
  split; [exact HA|].
  split; [rewrite HLn; apply (s1_read_ok_buf v pos lyc Sc Wc memc mdc regsc);
          [exact H | exact Hsp | unfold ESTACK; lia | unfold PF_O_BUF; lia | lia
          | unfold PF_O_BUF; lia]|].
  split; [rewrite HLn; apply (s1_amem_frame v pos lyc Sc Wc memc mdc); [exact H | lia | lia | lia]|].
  split; [exact HT|].
  exact (s1_rom v pos lyc Sc Wc memc mdc H).
Qed.

(* ============================== the trim call (pf_a7_s.v) ============================== *)
Definition s1_trim_call (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (regs : bvmap 5 word) (p : Z) (s : list Z) : Prop :=
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  getr regs 10 = w64 p /\ 0 <= p < 2 ^ 64 /\
  trim_pre SEGS B lyc Sc Wc memc regs p s /\
  st_nev Sc + EV_trim <= EV_MAX.

Lemma s1_room_ev : forall v pos lyc Sc Wc memc mdc, s1_st v pos lyc Sc Wc memc mdc ->
  sa_room Sc /\ st_nev Sc <= EV_MAX.
Proof.
  intros v pos lyc Sc Wc memc mdc H.
  pose proof H as [HCX HJ _ _ _ _].
  pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HROOM & HEV).
  pose proof HJ as (_ & _ & _ & _ & _ & Hfr & Hnev & _).
  unfold sa_room_n in HROOM. unfold EV_reac_segconf_parse_file in HEV.
  split; [|lia].
  unfold sa_room. rewrite Hfr, length_app. cbn [length]. lia.
Qed.

Lemma s1_trim_site_ok : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) p s,
  s1_st v pos lyc Sc Wc memc mdc ->
  getr regs 10 = w64 p -> sa_str (rdW Wc memc) p s -> pf_inb (pf_F v pos + PF_O_BUF) p s ->
  s1_trim_call lyc Sc Wc memc regs p s.
Proof.
  intros v pos lyc Sc Wc memc mdc regs p s H R10 HS [HI1 HI2].
  pose proof H as [HCX HJ HLY HPERM HOBJ HFSH].
  pose proof HOBJ as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
  destruct (s1_frame_rng v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
  destruct (s1_room_ev v pos lyc Sc Wc memc mdc H) as [_ HEV].
  pose proof alloc_ceiling_lt as HC.
  unfold PF_O_BUF in HI1, HI2.
  pose proof (s1_addr_buf v pos lyc Sc Wc memc mdc p (Z.of_nat (length s) + 1) H
    ltac:(unfold PF_O_BUF; lia) ltac:(lia) ltac:(unfold PF_O_BUF; lia)) as HA.
  pose proof HA as (_ & _ & _ & HRA & _).
  unfold s1_trim_call.
  split; [exact HROD|]. split; [exact R10|]. split; [lia|].
  split; [|unfold EV_trim; lia].
  unfold trim_pre.
  split; [lia|]. split; [exact HS|]. split; [exact HA|].
  split; [|lia].
  left. split; [|exact HRA].
  exact (s1_fframe_buf v pos lyc Sc Wc memc mdc p (Z.of_nat (length s) + 1) H
    ltac:(unfold PF_O_BUF; lia) ltac:(lia) ltac:(unfold PF_O_BUF; lia)).
Qed.

(* ============================== the transport of a9_core ============================== *)
Lemma s1_wrx_mono : forall v pos a, a5_Wrx v pos false false a -> a5_Wrx v pos true true a.
Proof. intros v pos a H. exact (a5_Wrx_mono v pos false false a H). Qed.

(* a9_core after a step or a call that keeps every byte off a5_Wrx v pos false false (the stack below s1 and
   buf), keeps every visible byte visible, and returns the journal at the same layout with the frame state
   changed at most (set_fs) and the live blocks permuted *)
Lemma s1_move : forall n x lyc Sc Wc rX memc mdc Sc' Wc' rX' memc' mdc',
  a9_core B n x lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc' Wc' memc'
    mdc' 0 ->
  (exists f, Sc' = set_fs f Sc) -> Permutation (ablocks B lyc Sc') (ablocks B lyc Sc) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx (y_v x) (y_pos x) false false a -> rdW Wc' memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc' memc' a <> None) ->
  pf_rg rX' (a5_FI B (y_v x)) ->
  a9_core B n x lyc Sc' Wc' rX' memc' mdc'.
Proof.
  intros n x lyc Sc Wc rX memc mdc Sc' Wc' rX' memc' mdc' (HB & HM & HS & HL & HLT & HD0 & HDL) HJ' HSf HPerm
    HK HV HRG.
  pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
  pose proof (a5_text B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & HC).
  assert (HKt : forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx (y_v x) (y_pos x) true true a ->
      rdW Wc' memc' a = rdW Wc memc a).
  { intros a Ha Hn. apply HK; [exact Ha|]. intros Hw. apply Hn. exact (s1_wrx_mono _ _ _ Hw). }
  assert (HFSH : pf_fsh (rdW Wc memc) (pf_SH (y_v x) (y_pos x)) PF_SC_LINE)
    by (destruct HB as (_ & _ & _ & _ & H); exact H).
  assert (HFSH' : pf_fsh (rdW Wc' memc') (pf_SH (y_v x) (y_pos x)) PF_SC_LINE)
    by (eapply a5_keep_fsh; [exact G | exact HK | exact HFSH]).
  split; [exact (a5_move0 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB HJ' HSf HPerm HKt HV HRG HFSH')|].
  split; [exact HM|].
  split; [eapply a5_keep_st; eassumption|].
  split; [eapply a5_keep_slot; [exact G | exact HK | exact HL]|].
  split; [exact HLT|]. split; [exact HD0 | exact HDL].
Qed.

End e.
End f.
End d.
