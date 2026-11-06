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
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_put_string.v; 360 of its 426 lines of code are new or changed and 1206 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/ZZpstail.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* SEG4 of ZZpsclose.ps_close on image B - from put #3's return (PS_CLOSE_RET 0x862b4) through the epilogue (frame
   retire, flag store, the `ret` at 0x86350) to put_string_spec's post (image A: lib/A/ZZpstail.v, PS_CLOSE_RET 0x85d9c).
   The route: FSW_put_string.ps_epilogue (the epilogue's run, the flag store, the `ret`), at the journal window top
   ot and the heads U3 of the third return; its Q receives the five regions the epilogue writes and the final
   journal + ARU. The post's clauses come from ps_inv at the third return:
   - wout_ok, wkeep, fs_glob: carried across the epilogue's write set (ZZpskeep, psg4_Wr below), which lies below sp0
     and below alloc_ceiling, so off the out-object, the window [sp0, ot), the buffer block and the statics;
   - wbudget_kept, bswap: unchanged, since stack_free_state only changes st_fs, never st_chunks (definitional);
   - cstr_ok: re-derived per arm of the ENTRY wsrc_kept (psg4_cstr): a string in a live block by
     FSW_strkit.cstr_ok_kept_blkU over the walk's FINAL journal from the entry; a read-only literal (FS_RO_STRS) by
     the ZZpskeep transport, whose shadow hull is proved off the frame's shadow granule (psg4_tbl). *)
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
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_frame FSW_frame3 FSW_put_string ZZpsjoin ZZpsclose ZZpskeep ZZpssep ZZpsres.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
FSH_Fn_writer FSW_strkit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= arithmetic, standalone (no lia in the walk's context) ================= *)
Lemma psg4_stk : 208 <= STK_put_string.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* the re-aligned sp: ps_inv's form and ps_epilogue's form agree, 16 below or at sp0 - 192 *)
Lemma psg4_sp1 : forall sp0, sp0 mod 16 = 0 ->
  32 * ((sp0 - PS_FRAME_OWN) / 32) = sp0 - 192 - (sp0 - 192) mod 32 /\
  sp0 - 208 <= sp0 - 192 - (sp0 - 192) mod 32 <= sp0 - 192.
Proof.
intros sp0 H. unfold PS_FRAME_OWN.
pose proof (Z.div_mod (sp0 - 192) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0 - 192) 32 ltac:(lia)).
pose proof (Z.div_mod sp0 16 ltac:(lia)).
split; lia.
Qed.

Lemma psg4_arith : forall STK sp0 ot o lo hi top ac sp1,
  208 <= STK -> 0x7fff7f800000 <= ac -> ac <= lo -> lo + STK <= sp0 -> top <= hi -> hi <= 2 ^ 47 ->
  sp0 <= o -> o + 32 <= ot -> ot <= top -> sp0 - 208 <= sp1 <= sp0 - 192 ->
  ot - (STK + (ot - sp0)) <= sp0 - 208 /\ sp0 <= ot /\ 0 <= sp0 - 208 /\ sp0 < 2 ^ 64 /\
  ac <= sp1 /\ sp1 + 192 <= sp0 /\ o + 32 <= 2 ^ 64 /\ ot <= 2 ^ 64 /\ sp1 <= sp0 /\ 0 <= sp0.
Proof. intros. lia. Qed.

(* the shadow hull of a prefix of an fs read-only literal (FS_RO_STRS lies in [0x20ea0, 0x21303), ZZpssep.pss_ro_rng;
   image B's literals sit at A's addresses, lib/B/FSH_Rt.v:36-65); 0x7fff8000 is SHADOW_OFF *)
Lemma psg4_hull_bd : forall s n t, 0x20ea0 <= s -> 0 <= n -> s + n + 1 <= 0x21303 ->
  shadow_addr s / 8 * 8 <= t < shadow_addr (s + n) / 8 * 8 + 8 ->
  0x7fff8000 + 0x41cd <= t < 0x7fff8000 + 0x4268.
Proof.
intros s n t H1 H2 H3 Ht. unfold shadow_addr, SHADOW_OFF in Ht.
pose proof (Z.div_mod s 8 ltac:(lia)). pose proof (Z.mod_pos_bound s 8 ltac:(lia)).
pose proof (Z.div_mod (s + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + n) 8 ltac:(lia)).
pose proof (Z.div_mod (0x7fff8000 + s / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (0x7fff8000 + s / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (0x7fff8000 + (s + n) / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (0x7fff8000 + (s + n) / 8) 8 ltac:(lia)).
lia.
Qed.

(* a frame outside image B's first segment [0x10000, 0x30000) (ZZpssep.pss_img_seg0) has its shadow granule outside
   that hull *)
Lemma psg4_fsh_off : forall F t, 0 <= F -> (F + 64 <= 0x10000 \/ 0x30000 <= F) ->
  0x7fff8000 + 0x41cd <= t < 0x7fff8000 + 0x4268 -> ~ (shadow_addr F <= t < shadow_addr F + 8).
Proof.
intros F t H0 HF Ht Hw. unfold shadow_addr, SHADOW_OFF in Hw.
pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)). lia.
Qed.

Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* ps_epilogue's Section hypotheses (FSW_put_string.v Section W: HML, HASF, HFFL); no other is used here *)
Hypothesis HML : model_laws (as_universe B).
Hypothesis HASF : astack_free_law tfibsegs B.
Hypothesis HFFL : frame_flag_lawP tfibsegs B.
#[local] Abbreviation ps_pre := (ZZpsclose.ps_pre B).
#[local] Abbreviation ps_inv := (ZZpsclose.ps_inv B).

(* ================= the epilogue's write set ================= *)
(* the five regions of ps_epi_ss, as ps_epilogue's Q lists them: the saved words below sp0, the re-aligned frame,
   the fake frame, its shadow granule and its flag byte *)
Definition psg4_Wr (sp0 sp1 F FL : Z) (a : Z) : Prop :=
  (sp0 - 104 <= a < sp0) \/ (sp1 <= a < sp1 + 88) \/ (F <= a < F + 64) \/
  (shadow_addr F <= a < shadow_addr F + 8) \/ a = FL.

Lemma psg4_frame_agree : forall (W : world tfibsegs) (mem mem' : word -> option byte) sp0 sp1 F FL,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 104 <= a < sp0) -> ~ (sp1 <= a < sp1 + 88) -> ~ (F <= a < F + 64) ->
     ~ (shadow_addr F <= a < shadow_addr F + 8) -> a <> FL -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  pske_agree W W mem mem' (psg4_Wr sp0 sp1 F FL).
Proof.
intros W mem mem' sp0 sp1 F FL H.
assert (E : forall a, 0 <= a < 2 ^ 64 -> ~ psg4_Wr sp0 sp1 F FL a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha Hw. unfold psg4_Wr in Hw. apply H; [exact Ha | intro Hx; apply Hw; tauto ..]. }
split.
- intros a Ha Hw. unfold mbyte, mrestrict. rewrite (E a Ha Hw). reflexivity.
- intros a Ha Hw (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite (E a Ha Hw). exact Hb.
Qed.

(* everything at or above sp0 is off the write set *)
Lemma psg4_hi : forall sp0 sp1 F FL a ac, ac <= sp1 -> sp1 + 192 <= sp0 -> F + 64 <= ac ->
  shadow_addr F + 8 <= ac -> FL < ac -> sp0 <= a -> ~ psg4_Wr sp0 sp1 F FL a.
Proof. intros sp0 sp1 F FL a ac H1 H2 H3 H4 H5 H6. unfold psg4_Wr. intros [H|[H|[H|[H|H]]]]; lia. Qed.

(* the live frame, its shadow granule and its flag byte lie below alloc_ceiling *)
Lemma psg4_frame_bd : forall ly S (W : world tfibsegs) mem md pos,
  AR tfibsegs B ly S W mem md -> In (0, pos) (frames S) ->
  frame_addr ly 0 pos + 64 <= alloc_ceiling /\ shadow_addr (frame_addr ly 0 pos) + 8 <= alloc_ceiling /\
  flag_addr ly 0 pos < alloc_ceiling.
Proof.
intros ly S W mem md pos HAR Hin. pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (frames_bounds tfibsegs B LAWS ly S W mem md 0 pos HAR Hin) as (HF0 & HFc & _). rewrite pss_fb0 in HFc.
destruct (al_flag _ _ LAWS ly S W mem md 0 pos HAR Hin) as (_ & _ & _ & HFLc).
pose proof (psr_sh_bd (frame_addr ly 0 pos) HF0 HFc) as (_ & Hsh).
split; [exact HFc|]. split; [exact Hsh | exact HFLc].
Qed.

(* a live block misses the write set: below alloc_ceiling <= sp1, off the frame and its shadow (pss_fr_off_blk),
   and off the flag byte (owned, a block byte is not) *)
Lemma psg4_blk_off : forall ly S (W : world tfibsegs) mem md pos p n a sp0 sp1,
  AR tfibsegs B ly S W mem md -> In (0, pos) (frames S) -> In (p, n) (ablocks B ly S) ->
  p <= a < p + req_size n -> alloc_ceiling <= sp1 -> sp1 + 192 <= sp0 ->
  ~ psg4_Wr sp0 sp1 (frame_addr ly 0 pos) (flag_addr ly 0 pos) a.
Proof.
intros ly S W mem md pos p n a sp0 sp1 HAR Hin Hblk Ha Hac Hsp. pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hblk) as (_ & _ & Hpc & _ & Hown & _).
destruct (al_flag _ _ LAWS ly S W mem md 0 pos HAR Hin) as (_ & HFLo & _).
unfold psg4_Wr. intros [Hw | [Hw | [Hw | [Hw | Hw]]]].
- lia.
- lia.
- apply (pss_fr_off_blk B ly S W mem md 0 pos p n a HAR Hin Hblk); [left; rewrite pss_fb0; exact Hw | exact Ha].
- apply (pss_fr_off_blk B ly S W mem md 0 pos p n a HAR Hin Hblk); [right; rewrite pss_fb0 | exact Ha].
  change (64 / 8) with 8. exact Hw.
- subst a. exact (proj2 (Hown _ Ha) HFLo).
Qed.

(* the writer's buffer block (wout_ok's live arm) misses the write set *)
Lemma psg4_buf_off : forall ly S (W : world tfibsegs) mem md memw pos o buf cap failed (text : list Z) sp0 sp1,
  AR tfibsegs B ly S W mem md -> In (0, pos) (frames S) ->
  FSH_Fn_writer.wout_ok B tfibsegs ly S W memw o buf cap failed text ->
  alloc_ceiling <= sp1 -> sp1 + 192 <= sp0 -> cap <> 0 ->
  HEAD <= buf /\ buf + cap <= 2 ^ 64 /\
  (forall a, buf - HEAD <= a < buf + cap -> ~ psg4_Wr sp0 sp1 (frame_addr ly 0 pos) (flag_addr ly 0 pos) a).
Proof.
intros ly S W mem md memw pos o buf cap failed text sp0 sp1 HAR Hin HOUT Hac Hsp Hc.
destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [(E0 & _) | (_ & HRB & _)]); [contradiction|].
destruct HRB as (Hblk & _ & Hpos & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hblk) as (_ & H4096 & Hpc & _).
assert (Hrq : req_size (cap + HEAD) = cap + HEAD)
  by (unfold req_size, HEAD; destruct (Z.eqb_spec (cap + 16) 0); lia).
rewrite Hrq in Hpc.
split; [unfold HEAD in *; lia|]. split; [unfold HEAD in *; lia|].
intros a Ha. apply (psg4_blk_off ly S W mem md pos (buf - HEAD) (cap + HEAD) a sp0 sp1 HAR Hin Hblk);
  [rewrite Hrq; unfold HEAD in *; lia | exact Hac | exact Hsp].
Qed.

(* fs's statics miss the write set: image bytes, off the frame and its shadow (pss_fr_off_pstat), and the flag byte is
   no image byte (AR's client-image law) *)
Lemma psg4_pstat_off : forall ly S (W : world tfibsegs) mem md pos sp0 sp1 a,
  AR tfibsegs B ly S W mem md -> In (0, pos) (frames S) -> alloc_ceiling <= sp1 -> sp1 + 192 <= sp0 ->
  inFP FS_PSTAT_FP a -> ~ psg4_Wr sp0 sp1 (frame_addr ly 0 pos) (flag_addr ly 0 pos) a.
Proof.
intros ly S W mem md pos sp0 sp1 a HAR Hin Hac Hsp HP.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
destruct (pss_pstat_rng a HP) as (P0 & P1).
unfold psg4_Wr. intros [Hw | [Hw | [Hw | [Hw | Hw]]]].
- lia.
- lia.
- apply (pss_fr_off_pstat B ly S W mem md 0 pos a HAR Hin); [left; rewrite pss_fb0; exact Hw | exact HP].
- apply (pss_fr_off_pstat B ly S W mem md 0 pos a HAR Hin); [right; rewrite pss_fb0 | exact HP].
  change (64 / 8) with 8. exact Hw.
- subst a.
  apply (proj2 (al_client_img _ _ LAWS ly S W mem md _ HAR
    (or_intror (or_intror (ex_intro _ 0 (ex_intro _ pos (conj Hin eq_refl))))))).
  exact (pss_pstat_img _ HP).
Qed.

(* the window [sp0, ot) keeps its bytes and writability across the epilogue *)
Lemma psg4_wkeep : forall (W W3 : world tfibsegs) mem mem3 memf Wr sp0 sp1 ot o,
  wkeep tfibsegs W W3 mem mem3 sp0 ot o 32 ->
  pske_agree W3 W3 mem3 memf Wr ->
  (forall a, sp0 <= a < ot -> ~ Wr a) -> 0 <= sp0 -> ot <= 2 ^ 64 -> sp1 <= sp0 ->
  (forall a, sp1 <= a < ot -> apresent (w_H W3) mem3 a) ->
  wkeep tfibsegs W W3 mem memf sp0 ot o 32.
Proof.
intros W W3 mem mem3 memf Wr sp0 sp1 ot o HK AG Hoff H0 Hot Hs1 HP a Ha Ho.
destruct (HK a Ha Ho) as (E & Wb).
assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
split.
- rewrite (pske_mbyte W3 W3 mem3 memf Wr a AG Ha64 (Hoff a Ha)). exact E.
- rewrite Wb. apply (pske_writable W3 W3 mem3 memf Wr a AG Ha64 (Hoff a Ha)). left. apply HP. lia.
Qed.

(* ================= cstr_ok at the end ================= *)
(* every user-poisoned range misses an addressable string: its shadow bytes read 0xf7, the string's are addressable
   (FSW_strkit.ush_off_addressable), and each range is whole granules (upoison_ok) *)
Lemma psg4_U_off : forall ly S U (W : world tfibsegs) mem md s (bs : list Z),
  ARU tfibsegs B ly S U W mem md -> cstr_ok tfibsegs W mem s bs ->
  forall r, In r U -> fst r + snd r <= s \/ s + Z.of_nat (length bs) + 1 <= fst r.
Proof.
intros ly S U W mem md s bs (_ & OK & PO) Hc r Hr.
destruct Hc as (_ & _ & _ & _ & _ & Hra & _).
destruct (upoison_ok_In B ly S U r OK Hr) as (A8 & L8 & M8 & _).
destruct (Z_le_gt_dec (fst r + snd r) s) as [H1 | H1]; [left; exact H1|].
destruct (Z_le_gt_dec (s + Z.of_nat (length bs) + 1) (fst r)) as [H2 | H2]; [right; exact H2|].
exfalso.
assert (Hx : s <= Z.max s (fst r) < s + (Z.of_nat (length bs) + 1)) by lia.
pose proof (FSW_strkit.ush_off_addressable U W mem s _ _ PO Hra Hx) as E.
assert (E' : in_ush U (shadow_addr (Z.max s (fst r))) = true).
{ apply in_ush_spec. exists r. split; [exact Hr|].
  destruct r as [q z]. cbn [fst snd] in *.
  apply Z.mod_divide in A8 as [a8 Ha8]; [|lia]. apply Z.mod_divide in M8 as [z8 Hz8]; [|lia]. subst q z.
  unfold shadow_addr. rewrite !Z.div_mul by lia.
  pose proof (Z.div_mod (Z.max s (a8 * 8)) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (Z.max s (a8 * 8)) 8 ltac:(lia)).
  lia. }
rewrite E in E'. discriminate E'.
Qed.

(* the block arm: FSW_strkit.cstr_ok_kept_blkU over a journal from the entry *)
Lemma psg4_blk : forall ly S U (W : world tfibsegs) mem md STK jt FP lyf Sf Uf (Wf : world tfibsegs) memf mdf k s
    (bs : list Z) b m,
  ARU tfibsegs B ly S U W mem md ->
  ajournal tfibsegs B STK jt FP ly S W (unpoison U mem) md [] lyf Sf Wf (unpoison Uf memf) mdf k ->
  ARU tfibsegs B lyf Sf Uf Wf memf mdf ->
  In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B lyf Sf) -> b <= s -> s + Z.of_nat (length bs) + 1 <= b + m ->
  (forall a, b <= a < b + req_size m -> ~ inFP FP a) ->
  (forall r, In r Uf -> fst r + snd r <= s \/ s + Z.of_nat (length bs) + 1 <= fst r) ->
  cstr_ok tfibsegs W mem s bs -> cstr_ok tfibsegs Wf memf s bs.
Proof.
intros ly S U W mem md STK jt FP lyf Sf Uf Wf memf mdf k s bs b m H0 HJ (_ & OKf & POf) Hin Hin' Hb Hbm HFP HU Hc.
apply (FSW_strkit.cstr_ok_kept_blkU B STK jt FP ly S U W mem md [] lyf Sf Uf Wf memf mdf k s bs b m
  H0 HJ OKf POf Hin Hin' Hb Hbm); [| | exact Hc].
- intros a Ha. apply HFP. pose proof (pss_req_ge m) as Hq. lia.
- intros r Hr. right. exact (HU r Hr).
Qed.

(* a live block other than the writer's buffer misses the walk's footprint: off the statics (image bytes) and off
   the buffer block (AR's block separation) *)
Lemma psg4_blk_fp : forall ly S (W : world tfibsegs) mem md memw o buf cap failed (text : list Z) b m a,
  AR tfibsegs B ly S W mem md -> FSH_Fn_writer.wout_ok B tfibsegs ly S W memw o buf cap failed text ->
  In (b, m) (ablocks B ly S) -> b <> buf - HEAD -> b <= a < b + req_size m ->
  ~ inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) a.
Proof.
intros ly S W mem md memw o buf cap failed text b m a HAR HOUT Hin Hne Ha.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
unfold FSH_Fn_writer.wbuf_fp. destruct (Z.eqb_spec cap 0) as [E | E]; intros HP.
- rewrite app_nil_r in HP. exact (blk_img tfibsegs B LAWS ly S W mem md b m a HAR Hin Ha (pss_pstat_img a HP)).
- apply inFP_app in HP as [HP | HP].
  + exact (blk_img tfibsegs B LAWS ly S W mem md b m a HAR Hin Ha (pss_pstat_img a HP)).
  + destruct HP as (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [(E0 & _) | (_ & HRB & _)]);
      [exact (E E0)|].
    destruct HRB as (Hbuf & _).
    assert (Hneq : (b, m) <> (buf - HEAD, cap + HEAD)) by (intros Eq; injection Eq as E1 _; exact (Hne E1)).
    pose proof (sep_blocks tfibsegs B LAWS ly S W mem md b m (buf - HEAD) (cap + HEAD) HAR Hin Hbuf Hneq) as Hd.
    pose proof (pss_wbuf_in buf cap a Hra) as Hw.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the table arm: a prefix of a read-only literal sits in [0x20ea0, 0x21303) (pss_ro_rng), inside image B's first
   segment (pss_img_seg0); the write set misses its bytes and its shadow hull (the frame is no image byte, so its shadow granule
   is far from the literal's hull) *)
Lemma psg4_tbl : forall ly S (W : world tfibsegs) mem md pos sp0 sp1 s (bs : list Z) l,
  AR tfibsegs B ly S W mem md -> In (0, pos) (frames S) ->
  alloc_ceiling <= sp1 -> sp1 + 192 <= sp0 ->
  In (s, l) FS_RO_STRS -> (length (bs ++ [0%Z]) <= Nat.succ (length l))%nat ->
  (forall a, s <= a < s + Z.of_nat (length bs) + 8 -> ~ psg4_Wr sp0 sp1 (frame_addr ly 0 pos) (flag_addr ly 0 pos) a) /\
  (forall t, shadow_addr s / 8 * 8 <= t < shadow_addr (s + Z.of_nat (length bs)) / 8 * 8 + 8 ->
     ~ psg4_Wr sp0 sp1 (frame_addr ly 0 pos) (flag_addr ly 0 pos) t).
Proof.
intros ly S W mem md pos sp0 sp1 s bs l HAR Hin Hac Hsp Hl Hlen.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
destruct (pss_ro_rng s l Hl) as (Hs0 & Hs1).
assert (HL : Z.of_nat (length bs) <= Z.of_nat (length l)).
{ rewrite length_app in Hlen. cbn [length] in Hlen. rewrite Nat.add_1_r in Hlen. apply le_S_n in Hlen.
  apply Nat2Z.inj_le in Hlen. exact Hlen. }
destruct (frames_bounds tfibsegs B LAWS ly S W mem md 0 pos HAR Hin) as (HF0 & HFc & HFapp).
rewrite pss_fb0 in HFc, HFapp.
destruct (al_flag _ _ LAWS ly S W mem md 0 pos HAR Hin) as (_ & _ & HFLapp & HFLc).
assert (HFLimg : ~ in_img tfibsegs (flag_addr ly 0 pos)).
{ exact (proj2 (al_client_img _ _ LAWS ly S W mem md _ HAR
    (or_intror (or_intror (ex_intro _ 0 (ex_intro _ pos (conj Hin eq_refl))))))). }
assert (HFimg : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> ~ in_img tfibsegs a).
{ intros a Ha. apply (frm_img tfibsegs B LAWS ly S W mem md 0 pos a HAR Hin). rewrite pss_fb0. exact Ha. }
assert (HFseg : frame_addr ly 0 pos + 64 <= 0x10000 \/ 0x30000 <= frame_addr ly 0 pos).
{ destruct (Z_le_gt_dec (frame_addr ly 0 pos + 64) 0x10000) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec 0x30000 (frame_addr ly 0 pos)) as [H'|H']; [right; exact H'|].
  exfalso. apply (HFimg (Z.max (frame_addr ly 0 pos) 0x10000)); [lia|]. apply pss_img_seg0. lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, HFLapp.
split.
- intros a Ha. unfold psg4_Wr. intros [Hw | [Hw | [Hw | [Hw | Hw]]]].
  + lia.
  + lia.
  + apply (HFimg a Hw). apply pss_img_seg0. lia.
  + unfold shadow_addr, SHADOW_OFF in Hw. pose proof (Z.div_pos (frame_addr ly 0 pos) 8 ltac:(lia) ltac:(lia)). lia.
  + subst a. apply HFLimg. apply pss_img_seg0. lia.
- intros t Ht.
  pose proof (psg4_hull_bd s (Z.of_nat (length bs)) t Hs0 ltac:(lia) ltac:(lia) Ht) as Htb.
  unfold psg4_Wr. intros [Hw | [Hw | [Hw | [Hw | Hw]]]].
  + lia.
  + lia.
  + lia.
  + exact (psg4_fsh_off (frame_addr ly 0 pos) t ltac:(lia) HFseg Htb Hw).
  + lia.
Qed.

(* cstr_ok at the final state, per arm of the ENTRY wsrc_kept *)
Lemma psg4_cstr : forall ly S U (W : world tfibsegs) mem md o buf cap failed (text : list Z) s (bs : list Z)
    STK jt ly3 S3 U3 (W3 : world tfibsegs) mem3 md3 buf3 cap3 pos memf mdj k sp0 sp1,
  ARU tfibsegs B ly S U W mem md ->
  FSH_Fn_writer.wout_ok B tfibsegs ly S W mem o buf cap failed text ->
  cstr_ok tfibsegs W mem s bs ->
  FSH_Fn_writer.wsrc_kept B tfibsegs ly S U W mem buf s (bs ++ [0]) ->
  ajournal tfibsegs B STK jt (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly3 (stack_free_state 0 pos S3) W3 (unpoison U3 memf) mdj k ->
  ARU tfibsegs B ly3 (stack_free_state 0 pos S3) U3 W3 memf mdj ->
  FSH_Fn_writer.bswap (ablocks B ly S) (ablocks B ly3 S3) buf buf3 cap cap3 ->
  ARU tfibsegs B ly3 S3 U3 W3 mem3 md3 -> cstr_ok tfibsegs W3 mem3 s bs -> In (0, pos) (frames S3) ->
  alloc_ceiling <= sp1 -> sp1 + 192 <= sp0 ->
  pske_agree W3 W3 mem3 memf (psg4_Wr sp0 sp1 (frame_addr ly3 0 pos) (flag_addr ly3 0 pos)) ->
  cstr_ok tfibsegs W3 memf s bs.
Proof.
intros ly S U W mem md o buf cap failed text s bs STK jt ly3 S3 U3 W3 mem3 md3 buf3 cap3 pos memf mdj k sp0 sp1
  H0 HOUT Hc Hsk HJ Hf HBS H3 Hc3 Hin Hac Hsp AG.
pose proof (ARU_AR tfibsegs B ly S U W mem md H0) as HAR0.
pose proof (ARU_AR tfibsegs B ly3 S3 U3 W3 mem3 md3 H3) as HAR3.
pose proof (psg4_U_off ly3 S3 U3 W3 mem3 md3 s bs H3 Hc3) as HU.
assert (EA : ablocks B ly3 (stack_free_state 0 pos S3) = ablocks B ly3 S3) by reflexivity.
destruct Hsk as [(E & _) | [(p & k' & Hne & HRB & Hp & Hk) | [(p & k' & Hne & Hblk & Hp & Hk & _) | (l & Hl & Hlen)]]].
- exfalso. destruct bs; discriminate E.
- (* a live reader block other than the buffer: its user bytes *)
  destruct HRB as (Hblk & _). rewrite pss_len0 in Hk.
  apply (psg4_blk ly S U W mem md STK jt _ ly3 (stack_free_state 0 pos S3) U3 W3 memf mdj k s bs
    (p - HEAD) (k' + HEAD) H0 HJ Hf Hblk).
  + rewrite EA. exact (pss_bswap_keep _ _ buf buf3 cap cap3 _ _ HBS Hblk (pss_neq_head p buf Hne)).
  + clear - Hp. unfold HEAD. lia.
  + clear - Hk. lia.
  + intros a Ha. exact (psg4_blk_fp ly S W (unpoison U mem) md mem o buf cap failed text (p - HEAD) (k' + HEAD) a
      HAR0 HOUT Hblk (pss_neq_head p buf Hne) Ha).
  + exact HU.
  + exact Hc.
- (* any live block other than the buffer's *)
  rewrite pss_len0 in Hk.
  apply (psg4_blk ly S U W mem md STK jt _ ly3 (stack_free_state 0 pos S3) U3 W3 memf mdj k s bs
    p k' H0 HJ Hf Hblk).
  + rewrite EA. exact (pss_bswap_keep _ _ buf buf3 cap cap3 _ _ HBS Hblk Hne).
  + exact Hp.
  + clear - Hk. lia.
  + intros a Ha. exact (psg4_blk_fp ly S W (unpoison U mem) md mem o buf cap failed text p k' a
      HAR0 HOUT Hblk Hne Ha).
  + exact HU.
  + exact Hc.
- (* a prefix of a read-only literal *)
  destruct (psg4_tbl ly3 S3 W3 (unpoison U3 mem3) md3 pos sp0 sp1 s bs l HAR3 Hin Hac Hsp Hl Hlen) as (Hb & Hh).
  exact (pske_cstr_ok W3 W3 mem3 memf _ s bs AG Hb Hh Hc3).
Qed.

(* ================= SEG4 (ZZpsclose.ps_close's fourth premise, verbatim) ================= *)
Lemma psg4 :
  (forall ly S U W regs mem md ch ot o s buf cap failed (text bs : list Z) live peak cnt fail
     pos lyc ly3 S3 U3 W3 regs3 mem3 md3 buf3,
   ps_pre ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail ->
   ps_inv ly S U W regs mem md ot o s bs buf cap failed text live peak cnt fail pos lyc
     [[34]; bs; [34]] PS_CLOSE_RET (ps_epi_ss PS_CLOSE_RET)
     ly3 S3 U3 W3 regs3 mem3 md3 buf3 ->
   SRr tfibsegs W3 (mkCfg (mkst regs3 (Z_to_bv 64 PS_CLOSE_RET) mem3 (seg_rom tfibsegs)) md3)
     (fun W' c' => exists (st' : WriterApp.wst) buf' U',
        st' = WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs) /\
        FSH_Fn_writer.uswap U U' buf buf' cap /\
        FSH_Fn_writer.wpost B tfibsegs STK_put_string ot
          (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) regs ly S U W mem md
          (FSH_Fn_writer.wevk cap st') U'
          (fun ly' S' W'' regs' mem' md' =>
             FSH_Fn_writer.wout_ok B tfibsegs ly' S' W'' mem' o buf' (WriterApp.w_cap st')
               (WriterApp.w_failed st') (WriterApp.w_text st') /\
             FSH_Fn_writer.wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st')
               (WriterApp.w_cnt st') /\
             FSH_Fn_writer.bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
             wkeep tfibsegs W W'' mem mem' (spZ regs) ot o 32 /\
             cstr_ok tfibsegs W'' mem' s bs /\
             (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
                fs_glob tfibsegs W'' mem' (live + WriterApp.w_cap st' - cap) peak'
                  (WriterApp.w_cnt st') (WriterApp.w_fail st')))
          W' c')).
Proof.
intros ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail
  pos lyc ly3 S3 U3 W3 regs3 mem3 md3 buf3 PRE INV.
destruct PRE as (HPRE & Hheads & Hfr & G10 & G11 & HOUT & HGLOB & HHEAD & Hspo & Hoot & Hot16 & Hottop & Hchain &
  HFP & HPRESENT & Hcstr & Hsrck & Hbok & Hnz & Hplain & Hsep & Hwmax & Hcap & Hlive & Hbp).
unfold ZZpsclose.ps_inv in INV. cbv zeta in INV. unfold ps_st in INV.
(* image B: R18 is ps_inv's string register clause, x18 = s2 holds s (image A: x26 = s10) *)
destruct INV as (Hin & Efr & -> & HJ & HARU & HS & _ & R2 & R8 & R9 & R19 & R21 & R22 & R23 & R24 & R18 & R3 & R4 &
  Cslot & Chdr & Cfsh & HUS & HOUT3 & HBK & HBS & HWK & HCS3 & HPK & HSRC3 & HHD3 & HHEADS3 & HRO3 & HPR3).
rewrite (ps_three_puts bs Hplain).
set (st' := WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) [[34]; bs; [34]]) in *.
(* the entry: ARU, the return address, the stack window *)
destruct HPRE as ((AFN & UOK & UPO) & _).
destruct AFN as (HAR0 & Hret & _ & _ & _ & HSTK & _).
pose proof (conj HAR0 (conj UOK UPO) : ARU tfibsegs B ly S U W mem md) as HARU0.
destruct HSTK as (Hal16 & _ & Hac & Hlo & Hhi & Hhi47 & _ & _ & Htophi).
(* the layout at the third return keeps the fake-stack base, so the frame and its flag have the entry's addresses *)
pose proof HJ as (_ & LLE & _).
destruct LLE as (_ & _ & _ & _ & _ & EF & _).
assert (EFA : frame_addr ly3 0 pos = frame_addr ly 0 pos) by (unfold frame_addr; rewrite EF; reflexivity).
assert (EFL : flag_addr ly3 0 pos = flag_addr ly 0 pos) by (unfold flag_addr; rewrite EF; reflexivity).
rewrite <- EFA, <- EFL in HS. rewrite <- EFA in R24.
pose proof (psg4_sp1 (spZ regs) Hal16) as (Esp1 & Bsp1).
rewrite Esp1 in R9, HPR3.
pose proof asan_consts as (C1 & _).
pose proof (psg4_arith STK_put_string (spZ regs) ot o (ly_stk_lo ly) (ly_stk_hi ly) (ly_top ly) alloc_ceiling
  (spZ regs - 192 - (spZ regs - 192) mod 32) psg4_stk (proj1 C1) Hac Hlo Htophi Hhi47 Hspo Hoot Hottop Bsp1)
  as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
pose proof (ARU_AR tfibsegs B ly3 S3 U3 W3 mem3 md3 HARU) as HAR3.
destruct (psg4_frame_bd ly3 S3 W3 (unpoison U3 mem3) md3 pos HAR3 Hin) as (HFc & Hshc & HFLc).
assert (EB : blocks_bytes (stack_free_state 0 pos S3) = blocks_bytes S3) by reflexivity.
assert (EA : ablocks B ly3 (stack_free_state 0 pos S3) = ablocks B ly3 S3) by reflexivity.
pose (Qp := fun (ly' : alayout) (S' : astate) (W'' : world tfibsegs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) =>
  FSH_Fn_writer.wout_ok B tfibsegs ly' S' W'' mem' o buf3 (WriterApp.w_cap st')
    (WriterApp.w_failed st') (WriterApp.w_text st') /\
  FSH_Fn_writer.wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st')
    (WriterApp.w_cnt st') /\
  FSH_Fn_writer.bswap (ablocks B ly S) (ablocks B ly' S') buf buf3 cap (WriterApp.w_cap st') /\
  wkeep tfibsegs W W'' mem mem' (spZ regs) ot o 32 /\
  cstr_ok tfibsegs W'' mem' s bs /\
  (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
     fs_glob tfibsegs W'' mem' (live + WriterApp.w_cap st' - cap) peak'
       (WriterApp.w_cnt st') (WriterApp.w_fail st'))).
eapply SRr_mono.
- apply (ps_epilogue B HML HASF HFFL (STK_put_string + (ot - spZ regs)) ot (spZ regs)
    (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) ly S W mem md ly3 S3 U U3 W3 regs3 regs mem3 md3
    (FSH_Fn_writer.wevk cap st') pos Qp HS HJ HARU Hin R8 R9 R24 A1 A2 A3 A4 Hal16).
  + rewrite R8. unfold spZ. apply Z_to_bv_bv_unsigned.
  + exact R3.
  + exact R4.
  + exact Hret.
  + intros ms' md' HFE (mdj & HJf & HARUf).
    pose proof (psg4_frame_agree W3 mem3 (ms_mem ms') (spZ regs) (spZ regs - 192 - (spZ regs - 192) mod 32)
      (frame_addr ly3 0 pos) (flag_addr ly3 0 pos) HFE) as AG.
    pose proof (fun a => psg4_hi (spZ regs) (spZ regs - 192 - (spZ regs - 192) mod 32) (frame_addr ly3 0 pos)
      (flag_addr ly3 0 pos) a alloc_ceiling A5 A6 HFc Hshc HFLc) as HHI.
    unfold Qp.
    split; [|split; [|split; [|split; [|split]]]].
    * (* the out-object: its 32 bytes lie at or above sp0, the buffer block below alloc_ceiling *)
      apply (pske_wout_ok B ly3 S3 ly3 (stack_free_state 0 pos S3) W3 W3 mem3 (ms_mem ms') _ o buf3 _ _ _ AG
        (Z.le_refl _) A7).
      -- intros a Ha. apply HHI. exact (Z.le_trans _ _ _ Hspo (proj1 Ha)).
      -- intros Hc0. exact (psg4_buf_off ly3 S3 W3 (unpoison U3 mem3) md3 mem3 pos o buf3 _ _ _ (spZ regs) _
           HAR3 Hin HOUT3 A5 A6 Hc0).
      -- rewrite EA. exact (fun H => H).
      -- exact HOUT3.
    * (* the stack free leaves st_chunks: blocks_bytes is S3's *)
      unfold FSH_Fn_writer.wbudget_kept in *. rewrite EB. exact HBK.
    * rewrite EA. exact HBS.
    * exact (psg4_wkeep W W3 mem mem3 (ms_mem ms') _ (spZ regs) _ ot o HWK AG (fun a Ha => HHI a (proj1 Ha))
        A10 A8 A9 HPR3).
    * exact (psg4_cstr ly S U W mem md o buf cap failed text s bs (STK_put_string + (ot - spZ regs)) ot
        ly3 S3 U3 W3 mem3 md3 buf3 (WriterApp.w_cap st') pos (ms_mem ms') mdj (FSH_Fn_writer.wevk cap st')
        (spZ regs) _ HARU0 HOUT Hcstr Hsrck HJf HARUf HBS HARU HCS3 Hin A5 A6 AG).
    * destruct HPK as (pk & Hpk & HG). exists pk. split; [exact Hpk|].
      exact (pske_glob W3 W3 mem3 (ms_mem ms') _ _ _ _ _ AG
        (fun a Ha => psg4_pstat_off ly3 S3 W3 (unpoison U3 mem3) md3 pos (spZ regs) _ a HAR3 Hin A5 A6 Ha) HG).
- intros W' c' _ HF. exists st', buf3, U3. split; [reflexivity|]. split; [exact HUS|]. exact HF.
Qed.

(* the statement is ps_close's fourth premise: ps_close takes psg4 as SEG4 *)
Check (fun SEG1 SEG2 SEG3 => ps_close B SEG1 SEG2 SEG3 psg4).

End T.
