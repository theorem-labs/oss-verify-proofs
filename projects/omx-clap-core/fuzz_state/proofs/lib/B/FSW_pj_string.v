(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACem.v, with its module paths and module names changed; 1542 of its 1603 lines of code are new or changed and 390 lines of the source are left out. *)
(* pj_string 0x83e58 (pf.c:406-411), 49 instructions of fs.asan-ubsan (image B, sha256 5ac5ce0954f8...): the ASan walk
   of the READER lane's B statement pj_string_spec (lib/B/FSH_Fn_reader.v:722, success form, statement unchanged), a
   symbolic walk of B's OWN code (decode table lib/B/FSW_pj_string_tbl.v over B's text 0x83e58 .. 0x83f1c).

   Rule 24: the function's released plain / ubsan proofs exist (c8557374ad2e lib/Prog/pj_string.v, lib/U/Prog); no
   ASan-image proof of pj_string exists. Reuse search (a Theorem Labs lane, outputs under (internal path)):
   `proof-index pj_get pj_free pj_string` (r24-pj_get-free.txt) and `proof-index pj_object pj_get_str
   pj_string` (r24-B3.txt): plain lib/Prog and ubsan lib/U hits only, no ASan address; B's address 0x83e58 (.symtab,
   direct jal callee, no wrapper) has no proof; git grep of the cold branches by name and address (r24-cold-B3.txt,
   r24-cold-pjget-free.txt, chk-cold-extra.txt): only a Theorem Labs lane's bespoke evt-form lib/B/Prog/pj_string.v (a
   TEMPLATE, not bridgeable), S0's statement and this lane's own A walk. Second-agent check a Theorem Labs lane:
   "pj_string B: CONFIRM" (chk-B4-summary.txt).

   Form: this lane's image-A walk (a working branch 32e0eda0d83 lib/A/FSW_pj_string.v), RE-WALKED over B's own
   code with the lib/B kit (FSW_K / FSW_ret / FSW_K3 / FSW_rd). B is not A's code: UBSan adds two inline checks of v
   before the first store. Route (same C control flow as the plain proof, pf.c:406-411):
   - run 1 (FSW_K fsw_aj_run_toU): prologue, s2 := the shadow base (GOT 0x9fc10 -> cell 0xa8438), memset arguments, to
     `jal __asan_memset` 0x83e88;
   - __asan_memset (v, 0, 56) at PC_memset 0x5222c: FSW_K.fsw_intrin_atU over fs_memset_realizesU (pjs_memset_at);
   - resume at 0x83e8c (pjs_resume_rt / pjs_resume2: FSW_ret's fss_retT, s2 pinned to atom 32);
   - run 2 (token engine, pjs_seg2), B's own checks, each decided by a named premise:
     * UBSan null check `beqz s0, 0x83f00` (0x83e8c, the trap `unimp` 0x83f00): never taken. s0 is atom 8 = v with the
       fact pjs_vfact (range [4096, PJS_CEIL]), whose lower bound is pobj's placement arm (pjs_loc_facts: 4096 <= v for
       a fake frame or for a heap block past its head); the engine's branch test (Reusable/YP0e.v decide_cond2) reads
       v <> 0 from that range.
     * UBSan alignment check `andi a0, s0, 7; bnez a0, 0x83f00` (0x83e90 / 0x83e94): never taken. pjs_vfact's
       alignment (al2 = 3) is pobj's `v mod 8 = 0` conjunct; the engine's ALU_AND arm (Reusable/YP0m.v s_alu,
       s_and_ptr) folds v & 7 to the literal 0.
     * ASan shadow check of the 4-byte store to v->type (`lb` 0x83ea0, `bnez a1, 0x83f04` 0x83ea4; slow path
       0x83f04 .. 0x83f08, then `jal __asan_report_store4` 0x83f10): never taken. pobj's range_addressable conjunct
       gives the shadow entry pjs_SH = [mkSHE 8 0 56] (shent_ok_of_range), so the token engine reads the shadow byte as
       0 (YCbn.v tok_load, covered).
     s = NULL picks the literal FS_RO_STRS 0x21020; to `jal fuzz_strdup` 0x83ec0;
   - fuzz_strdup (pjs_call): callee pre by afn_pre_at (its chain is empty: s0 = v below alloc_ceiling, YCbq achain_low;
     its trace is [0x83ec4]), post from fs_fuzz_strdup, resume by FSW_K3.fsw_after_callFPU_args (callee FP
     FS_PSTAT_FP inside the caller's FP, image arm);
   - run 3 (token engine, pjs_tail): the ASan shadow check of the 8-byte store to v->str (`lbu` 0x83ed0,
     `bnez a1, 0x83f14` 0x83ed4 -> `jal __asan_report_store8` 0x83f18): never taken, the same shadow entry (pobj's
     range_addressable, carried across the calls: pjs_ra_heap / pjs_ra_frame); return value 0 (the new block is
     non-NULL: atom 10 >= 4112, fs_fuzz_strdup's `4096 + HEAD <= res`), epilogue, `ret` 0x83efc; FSW_ret.fsw_retU to
     fpostU.
   No exit of the walk is at the UBSan trap or an __asan_report_* call. v's placement: pobj's heap arm or its fake-frame
   arm, both written under the core's awr_byte (its fake-frame arm, frames at the journal's start); pj_string_holds
   splits the two.

   Section hypotheses (owners):
   - IMG : fs_img_facts tfibsegs B                          (S0, lib/B/FSH_Rt.v; the spec Section's IMG)
   - HSS : FsShadowSyms B                                   (S0, lib/B/FSH_Base.v: GOT 0x9fc10, cell 0xa8438)
   - fs_memset_realizesU : aintrin_realizesU tfibsegs B OSet PC_memset   (RUNTIME / POISON-U, lib/A/FSupoisonU.v
                                                              form, at B's PC_memset 0x5222c; lib/B/FSH_Rt.v fr_memset)
   - fs_fuzz_strdup : fuzz_strdup_spec                      (ALLOC a Theorem Labs lane, lib/B/FSH_Fn_alloc.v)
   Built over a working branch 2e266b38dbb (S0 + image B's relocated core + C5) with the lib/B walk kit
   a working branch 65632947036 and the CTX-free statements of a working branch adfa7850046.
   No lib/A image-content file is loaded: lib.A's FSupoison / FSupoisonU / FSH_YC20 / FSH_Gen only. The struct pj
   field lemmas fsw_val_pj_u64 / fsw_val_pj_u32 / fsw_pj_part_okW are lib/B/FSW_pj.v's (the B kit twin of
   lib/A/FSW_pj.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_K3 FSW_rd FSW_pj FSH_Fn_reader FSH_Fn_alloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSW_pj_string_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* ---- the walk's symbolic states ---- *)
Definition pjs_cs : list YP09.chunk :=
  [YP09.mkChunk 24 (CVal 8 (SOff (xatom 0) 0)); YP09.mkChunk 16 (CVal 8 (SOff (xatom 1) 0));
   YP09.mkChunk 8 (CVal 8 (SOff (xatom 2) 0)); YP09.mkChunk 0 (CVal 8 (SOff (xatom 3) 0))].
Definition pjs_vreg (lo hi : Z) : YP09.region := YP09.mkRegion (Some 8%nat) lo hi lo hi [].
(* the largest alloc_ceiling of any run (YCbq.v asan_consts: alloc_ceiling <= 0x7fffff800000) *)
Definition PJS_CEIL : Z := 0x7fffff800000.
Definition pjs_vfact : nat * afact := (8%nat, mkAF 4096 PJS_CEIL 3).
Definition pjs_pin (ss : sstate) : sstate :=
  mkSS (ss_pc ss) (sr_set (ss_regs ss) 18%bv (SOff 32 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss).
(* after the memset, s <> 0: atom 9 (s1 = s) is known nonzero *)
Definition pjs_ss2n : sstate :=
  pjs_pin (fss_retT 0x83e8c 32 pjs_cs [pjs_vreg 0 4] [pjs_vfact; (9%nat, mkAF 1 (2 ^ 64 - 1) 0)]).
(* after the memset, s = 0: s1 is the literal 0 *)
Definition pjs_ss2z : sstate :=
  let ss := pjs_pin (fss_retT 0x83e8c 32 pjs_cs [pjs_vreg 0 4] [pjs_vfact]) in
  mkSS (ss_pc ss) (sr_set (ss_regs ss) 9%bv (SLit 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition pjs_ss3 : sstate :=
  pjs_pin (fss_retT 0x83ec4 32 pjs_cs [pjs_vreg 16 24] [pjs_vfact; (10%nat, mkAF 4112 PJS_CEIL 4)]).
Definition pjs_SH : list shent := [mkSHE 8 0 56].


Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* owner S0 (lib/B/FSH_Rt.v fs_img_facts), proved once for build B's asyms: the image facts, the spec Section's IMG
   (lib/B/FSH_Fn_reader.v:251) *)
Hypothesis IMG : fs_img_facts tfibsegs B.
(* owner S0 (lib/B/FSH_Base.v FsShadowSyms: B's GOT word 0x9fc10 and shadow-offset cell 0xa8438) *)
Hypothesis HSS : FsShadowSyms B.
(* owner RUNTIME / POISON-U: FSupoisonU's ARU form of the donor's __asan_memset contract, at fs.asan-ubsan's PC_memset
   0x5222c (lib/B/FSH_Rt.v fr_memset; spec header lib/B/FSH_Fn_reader.v:90-92) *)
Hypothesis fs_memset_realizesU : aintrin_realizesU tfibsegs B OSet PC_memset.
(* owner ALLOC (a Theorem Labs lane): fuzz_strdup's contract (lib/B/FSH_Fn_alloc.v fuzz_strdup_spec, U form; spec header
   lib/B/FSH_Fn_reader.v:81-83) *)
Hypothesis fs_fuzz_strdup : @fuzz_strdup_spec fx rc SK tfibsegs B.

(* ---- user poison: an application byte is never a user-poisoned shadow byte ---- *)
Lemma pjs_unpoison_app : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF <= a < kHighMemBeg) ->
  unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros ly S U W mem md a H Ha Hn. apply unpoison_out. rewrite (wz a Ha).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
pose proof (ush_facts tfibsegs B ly S U W mem md a H E) as (_ & L). lia.
Qed.
Lemma pjs_aview_app : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF <= a < kHighMemBeg) ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md a H Ha Hn. apply (FSupoison.aview_at tfibsegs).
exact (pjs_unpoison_app ly S U W mem md a H Ha Hn).
Qed.
(* the shadow byte of x is no head's when x is in no live block's first 16 bytes (fs_heads: heads are block starts) *)
Lemma pjs_shadow_out : forall ly S U (W : world tfibsegs) mem md x,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U -> 0 <= x ->
  (forall h m, In (h, m) (ablocks B ly S) -> 16 <= req_size m -> ~ (h <= x < h + 16)) ->
  in_ush U (shadow_addr x) = false.
Proof.
intros ly S U W mem md x HARU HH Hx Hno.
destruct (in_ush U (shadow_addr x)) eqn:E; [|reflexivity]. exfalso.
apply in_ush_spec in E as (r & Hr & Hs).
destruct (HH r Hr) as (H16 & m & Hm & Hreq).
destruct (upoison_ok_In B ly S U r (ARU_ok tfibsegs B ly S U W mem md HARU) Hr) as (H8 & _).
destruct r as [h len]. cbn [fst snd] in *. subst len.
apply (Hno h m Hm Hreq). unfold shadow_addr in Hs.
pose proof (Z.div_mod h 8 ltac:(lia)) as Dh. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)). change (16 / 8) with 2 in Hs. lia.
Qed.

(* ---- where v lies: a live heap block past its head (ofr = false), or a fake frame live at entry (ofr = true) ---- *)
Definition pjs_loc (ofr : bool) (ly : alayout) (S : astate) (v : Z) : Prop :=
  if ofr then exists cid pos, In (cid, pos) (frames S) /\ 0 <= cid /\
    frame_addr ly cid pos <= v /\ v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid
  else exists b m, In (b, m) (ablocks B ly S) /\ b + HEAD <= v /\ v + 56 <= b + req_size m.

Lemma pjs_loc_facts : forall ofr ly S (W : world tfibsegs) mem md v,
  AR tfibsegs B ly S W mem md -> pjs_loc ofr ly S v ->
  4096 <= v /\ v + 56 <= alloc_ceiling /\ amem_range v 56 /\
  (forall x, v <= x < v + 56 -> app_addr x /\ ~ in_img tfibsegs x /\ ~ aowned B ly S x /\ apresent (w_H W) mem x).
Proof.
intros ofr ly S W mem md v HAR Hloc. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct ofr; cbn [pjs_loc] in Hloc.
- destruct Hloc as (cid & pos & Hin & Hc & H1 & H2).
  destruct (frames_bounds tfibsegs B LAWS ly S W mem md cid pos HAR Hin) as (F0 & Fc & Fapp).
  destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & Hfb & _).
  split; [lia|]. split; [lia|].
  split; [destruct Fapp as [A0 [A1 | [A2 A3]]]; unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd,
    ASAN_CEIL in *; lia|].
  intros x Hx. split; [exact (in_app_addr _ _ x Fapp ltac:(lia))|].
  split; [exact (frm_img tfibsegs B LAWS ly S W mem md cid pos x HAR Hin ltac:(lia))|].
  destruct (Hfb x ltac:(lia)) as [Hp Ho]. split; [exact Ho | exact Hp].
- destruct Hloc as (b & m & Hin & H1 & H2).
  destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hc & Happ & Hb & _).
  unfold HEAD in *.
  split; [lia|]. split; [lia|].
  split; [destruct Happ as [A0 [A1 | [A2 A3]]]; unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd,
    ASAN_CEIL in *; lia|].
  intros x Hx. split; [exact (in_app_addr _ _ x Happ ltac:(lia))|].
  split; [exact (blk_img tfibsegs B LAWS ly S W mem md b m x HAR Hin ltac:(lia))|].
  destruct (Hb x ltac:(lia)) as [Hp Ho]. split; [exact Ho | exact Hp].
Qed.

(* no byte of v lies in a live block's first 16 bytes *)
Lemma pjs_loc_nohead : forall ofr ly S (W : world tfibsegs) mem md v,
  AR tfibsegs B ly S W mem md -> pjs_loc ofr ly S v ->
  forall x, v <= x < v + 56 -> forall h m, In (h, m) (ablocks B ly S) -> 16 <= req_size m -> ~ (h <= x < h + 16).
Proof.
intros ofr ly S W mem md v HAR Hloc x Hx h m Hm Hreq Hhx.
destruct ofr; cbn [pjs_loc] in Hloc.
- destruct Hloc as (cid & pos & Hin & Hc & H1 & H2).
  pose proof (sep_block_frame tfibsegs B LAWS ly S W mem md h m cid pos HAR Hm Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- destruct Hloc as (b & m0 & Hin & H1 & H2). unfold HEAD in *.
  destruct (Z.eq_dec h b) as [-> | Hhb]; [lia|].
  assert (Hne : (h, m) <> (b, m0)) by (intros E; injection E as E1 _; exact (Hhb E1)).
  pose proof (sep_blocks tfibsegs B LAWS ly S W mem md h m b m0 HAR Hm Hin Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the shadow of v's bytes is not user-poisoned *)
Lemma pjs_v_shadow_out : forall ofr ly S U (W : world tfibsegs) mem md v,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U -> pjs_loc ofr ly S v ->
  forall x, v <= x < v + 56 -> in_ush U (shadow_addr x) = false.
Proof.
intros ofr ly S U W mem md v HARU HH Hloc x Hx.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (pjs_loc_facts ofr ly S W _ md v HAR Hloc) as (V0 & _).
apply (pjs_shadow_out ly S U W mem md x HARU HH ltac:(lia)).
exact (pjs_loc_nohead ofr ly S W _ md v HAR Hloc x Hx).
Qed.

(* ---- range_addressable / shadow_hull_vis of v on the machine memory ---- *)
Lemma pjs_ra_unp : forall ofr ly S U (W : world tfibsegs) mem md v,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U -> pjs_loc ofr ly S v ->
  forall x, v <= x < v + 56 ->
  aview tfibsegs (w_H W) (unpoison U mem) (shadow_of_addr SHADOW_OFF x) =
  aview tfibsegs (w_H W) mem (shadow_of_addr SHADOW_OFF x).
Proof.
intros ofr ly S U W mem md v HARU HH Hloc x Hx.
pose proof asan_consts as (C1 & _).
destruct (pjs_loc_facts ofr ly S W _ md v (ARU_AR tfibsegs B ly S U W mem md HARU) Hloc) as (V0 & V1 & _).
apply (aview_unpoison_out tfibsegs). change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
rewrite (wz (shadow_addr x)) by (unfold shadow_addr, SHADOW_OFF; lia).
exact (pjs_v_shadow_out ofr ly S U W mem md v HARU HH Hloc x Hx).
Qed.
Lemma pjs_ra_heap : forall ly S U (W : world tfibsegs) mem md v,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U -> pjs_loc false ly S v ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF v 56.
Proof.
intros ly S U W mem md v HARU HH Hloc.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof Hloc as Hl. cbn [pjs_loc] in Hl. destruct Hl as (b & m & Hin & H1 & H2). unfold HEAD in H1.
pose proof (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md b m v 56 HAR Hin ltac:(lia) H2)
  as Hra.
intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. symmetry. exact (pjs_ra_unp false ly S U W mem md v HARU HH Hloc x Hx).
Qed.
Lemma pjs_ra_frame : forall STK sp0 FP ly S U (W : world tfibsegs) mem md own ly' S' U' (W' : world tfibsegs) mem' md' k v,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' k ->
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  ARU tfibsegs B ly' S' U' W' mem' md' -> FSupoisonU.fs_heads B ly' S' U' ->
  pjs_loc true ly S v -> pjs_loc true ly' S' v ->
  (forall x, inFP FP x -> x < kLowShadowBeg \/ kHighShadowEnd <= x) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF v 56 ->
  range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF v 56.
Proof.
intros STK sp0 FP ly S U W mem md own ly' S' U' W' mem' md' k v HJ HARU HH HARU' HH' Hloc Hloc' HFP Hra.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof Hloc as Hl. cbn [pjs_loc] in Hl. destruct Hl as (cid & pos & Hin & Hc & H1 & H2).
destruct (al_frames _ _ LAWS ly S W (unpoison U mem) md cid pos HAR Hin) as (H32 & _).
assert (H8 : frame_addr ly cid pos mod 8 = 0).
{ apply Z.mod_divide in H32; [|lia]. destruct H32 as [q Hq]. rewrite Hq.
  replace (q * 32) with ((q * 4) * 8) by lia. apply Z_mod_mult. }
assert (Hra0 : range_addressable (aview tfibsegs (w_H W) (unpoison U mem)) SHADOW_OFF v 56).
{ intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. exact (pjs_ra_unp true ly S U W mem md v HARU HH Hloc x Hx). }
pose proof (range_addressable_entry_frame tfibsegs B LAWS STK sp0 FP ly S W (unpoison U mem) md own ly' S' W'
  (unpoison U' mem') md' k cid pos v 56 HJ Hin Hc H1 H2 H8 HFP HAR Hra0) as Hra1.
intros x Hx. destruct (Hra1 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. symmetry. exact (pjs_ra_unp true ly' S' U' W' mem' md' v HARU' HH' Hloc' x Hx).
Qed.

(* the shadow hull of a fake-frame object (the donor's A/ACem.v frame_al64 / shadow_hull_vis_of_frame, which this core
   cannot load) *)
Lemma pjs_frame_al64 : forall ly S (W : world tfibsegs) mem md cid pos,
  AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid.
Proof.
intros ly S W mem md cid pos [M _] Hin.
destruct (frame_facts B ly S _ cid pos M Hin) as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & H64 & Hb & _).
unfold frame_addr, page_aligned in *. split; [|split; [exact Hb | exact H64]].
rewrite Z.add_mod, Hoff, Z.add_0_r, Z.mod_mod by lia.
replace (ly_F ly) with (64 * (ly_F ly / 4096 * 64)) by (pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma pjs_hull_frame : forall ly S (W : world tfibsegs) mem md cid pos d n,
  AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= d -> d + n <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 < n ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) d n.
Proof.
intros ly S W mem md cid pos d n HAR Hin Hfd Hdn Hn s Hs.
destruct (pjs_frame_al64 ly S W mem md cid pos HAR Hin) as (Hal & Hbal & Hb64).
destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & _ & Hsh).
set (f := frame_addr ly cid pos) in *. set (bs := fs_frame_bytes cid) in *.
pose proof (Z.div_mod f 64 ltac:(lia)) as Df. pose proof (Z.div_mod bs 64 ltac:(lia)) as Db.
assert (E8f : f / 8 = 8 * (f / 64)) by (rewrite Hal, Z.add_0_r in Df; rewrite Df at 1;
  replace (64 * (f / 64)) with (8 * (f / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (E8b : bs / 8 = 8 * (bs / 64)) by (rewrite Hbal, Z.add_0_r in Db; rewrite Db at 1;
  replace (64 * (bs / 64)) with (8 * (bs / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (Hsf : shadow_addr f = 8 * (268431360 + f / 64)) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (L1 : shadow_addr f <= shadow_addr d / 8 * 8).
{ pose proof (shadow_mono f d Hfd) as M1. rewrite Hsf. rewrite Hsf in M1.
  assert (268431360 + f / 64 <= shadow_addr d / 8) by (apply Z.div_le_lower_bound; lia). lia. }
assert (L2 : shadow_addr (d + n - 1) / 8 * 8 + 8 <= shadow_addr f + bs / 8).
{ assert (M2 : shadow_addr (d + n - 1) < shadow_addr f + bs / 8).
  { unfold shadow_addr in *. assert ((d + n - 1) / 8 < f / 8 + bs / 8) by (apply Z.div_lt_upper_bound; lia). lia. }
  rewrite Hsf, E8b in M2. rewrite Hsf, E8b.
  assert (shadow_addr (d + n - 1) / 8 < 268431360 + f / 64 + bs / 64) by (apply Z.div_lt_upper_bound; lia). lia. }
specialize (Hsh (s - shadow_addr f) ltac:(lia)). replace (shadow_addr f + (s - shadow_addr f)) with s in Hsh by lia.
apply (aview_some_of_apresent tfibsegs). exact (proj1 Hsh).
Qed.
Lemma pjs_hull : forall ofr ly S U (W : world tfibsegs) mem md v,
  ARU tfibsegs B ly S U W mem md -> pjs_loc ofr ly S v ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) v 56.
Proof.
intros ofr ly S U W mem md v HARU Hloc.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
assert (H0 : shadow_hull_vis (aview tfibsegs (w_H W) (unpoison U mem)) v 56).
{ destruct ofr; cbn [pjs_loc] in Hloc.
  - destruct Hloc as (cid & pos & Hin & Hc & H1 & H2).
    exact (pjs_hull_frame ly S W _ md cid pos v 56 HAR Hin H1 H2 ltac:(lia)).
  - destruct Hloc as (b & m & Hin & H1 & H2). unfold HEAD in H1.
    exact (shadow_hull_vis_of_block tfibsegs B LAWS ly S W _ md b m v 56 HAR Hin ltac:(lia) H2 ltac:(lia)). }
intros s Hs. pose proof (H0 s Hs) as Hv.
pose proof asan_consts as (C1 & _).
destruct (pjs_loc_facts ofr ly S W _ md v HAR Hloc) as (V0 & V1 & _).
assert (Hsr : 0 <= s < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF in Hs.
  assert (0 <= v / 8) by (apply Z.div_pos; lia).
  assert ((v + 56 - 1) / 8 <= PJS_CEIL / 8) by (apply Z.div_le_mono; unfold PJS_CEIL in *; lia).
  assert (0 <= (2147450880 + v / 8) / 8) by (apply Z.div_pos; lia).
  assert ((2147450880 + (v + 56 - 1) / 8) / 8 <= (2147450880 + PJS_CEIL / 8) / 8) by (apply Z.div_le_mono; lia).
  unfold PJS_CEIL in *. lia. }
destruct (in_ush U s) eqn:EU.
- rewrite (ARU_poisoned tfibsegs B ly S U W mem md HARU s EU). discriminate.
- rewrite (aview_unpoison_out tfibsegs) in Hv by (rewrite (wz s Hsr); exact EU). exact Hv.
Qed.

(* ---- the write permission of a walk step: the core's awr_byte at the journal's start frames (its fake-frame arm covers
   a byte of check_round_trip's fake frame inside the FP) ---- *)
Definition pjs_wperm (ofr : bool) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (lyc : alayout)
  (Sc : astate) (own : list (Z * Z)) (a : Z) : Prop :=
  awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a.
Lemma pjs_wperm_stack : forall ofr STK sp0 FP ly S lyc Sc own a,
  sp0 - STK <= a < sp0 -> pjs_wperm ofr STK sp0 FP ly S lyc Sc own a.
Proof. intros ofr STK sp0 FP ly S lyc Sc own a Ha. unfold pjs_wperm, awr_byte, awr_byte0. left. left. exact Ha. Qed.
Lemma pjs_perm_v : forall ofr STK sp0 FP ly S lyc Sc own v,
  pjs_loc ofr ly S v ->
  (forall p n, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B lyc Sc)) ->
  (forall cid pos, frame_addr lyc cid pos = frame_addr ly cid pos) ->
  (forall a, v <= a < v + 56 -> inFP FP a) ->
  forall a, v <= a < v + 56 -> pjs_wperm ofr STK sp0 FP ly S lyc Sc own a.
Proof.
intros ofr STK sp0 FP ly S lyc Sc own v Hloc Hbl Hfa HFP a Ha. unfold pjs_wperm, awr_byte, awr_byte0.
destruct ofr; cbn [pjs_loc] in Hloc.
- destruct Hloc as (cid & pos & Hin & Hc & H1 & H2). right. right. split; [exact (HFP a Ha)|].
  exists cid, pos. split; [exact Hin|]. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa. lia.
- destruct Hloc as (b & m & Hin & H1 & H2). left. right. left. split; [exact (HFP a Ha)|].
  exists b, m. split; [exact (Hbl b m Hin)|]. unfold HEAD in H1. lia.
Qed.

(* FSW_K.fsw_run_to_tok_AJU, its write premise as pjs_wperm *)
Lemma pjs_run_to_tok : forall (ofr : bool) tbl (tbl_ok : table_ok tfibsegs tbl)
  (W : world tfibsegs) n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  sh_ok tfibsegs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_run_toN_tok tfibsegs tbl K Bx Bspan SH n stop ss = (st', r) ->
  match r with TS_ecall => False | _ => True end ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  Forall (ob_holds tfibsegs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  (forall a, in_wrange E (ss_mem ss) a -> pjs_wperm ofr STK sp0 FP ly S lyc Sc own a) ->
  run_post_tok_AJU B W E K Bx SH ss st' ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros ofr tbl tbl_ok W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q
  HS Hsh Hchk Hrun Hr HARU HJ Hobl Hwr Hk.
exact (fsw_run_to_tok_AJU B tbl tbl_ok W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q
  HS Hsh Hchk Hrun Hr HARU HJ Hobl Hwr Hk).
Qed.

(* the token run to a stop pc under pjs_wperm (FSW_K's fsw_aj_run_to_tokU over pjs_run_to_tok) *)
Ltac pjs_run_to_tokU ofr tblok HS HJ HARU SHOK Bspan stop :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of SHOK with
    | sh_ok _ ?Bx ?SH _ _ =>
      lazymatch type of tblok with
      | table_ok _ ?tbl =>
        let K := eval vm_compute in (run_K 0 Bx SH ss) in
        let r := eval vm_compute in (sym_run_toN_tok segs tbl K Bx Bspan SH FUEL stop ss) in
        lazymatch r with
        | (?st', ?rs) =>
          let Hrun := fresh "Hrun" in
          assert (Hrun : sym_run_toN_tok segs tbl K Bx Bspan SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
          eapply (pjs_run_to_tok ofr tbl tblok W FUEL stop E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            HS SHOK ltac:(vm_compute; reflexivity) Hrun I HARU HJ);
          [ clear Hrun; cbn [sh_obls]; srr_obls
          | clear Hrun
          | clear Hrun HS HJ HARU SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
            fsw_aj_after_run_tokU HS HJ HARU SHOK ]
        end
      end end
  | _ => fail "pjs_run_to_tokU: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
  end.

(* ---- the __asan_memset (v, 0, 56) call ---- *)
Definition pjs_msq (regsT : bvmap 5 word) (W : world tfibsegs) (memT : word -> option byte) (d : Z)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  aregs_preserved regsT regs2 /\
  (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W) mem2 (d + i) = Some 0) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 56) -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
     aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
  (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a).
Lemma pjs_memset_at : forall (ofr : bool)
  STK sp0 FP ly S W0 mem md own lyc Sc U (W : world tfibsegs) memT mdc k regsT (o : Z) d,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U memT) mdc k ->
  ARU tfibsegs B lyc Sc U W memT mdc ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (YK11.getr regsT 1) -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 10 = w64 d -> YK11.getr regsT 11 = w64 0 -> YK11.getr regsT 12 = w64 56 ->
  0 <= d -> d + 56 <= 2 ^ 63 -> amem_range d 56 ->
  dest_ok tfibsegs B lyc Sc W regsT memT d 56 ->
  range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF d 56 ->
  shadow_hull_vis (aview tfibsegs (w_H W) memT) d 56 ->
  (forall a, d <= a < d + 56 -> pjs_wperm ofr STK sp0 FP ly S lyc Sc own a) ->
  SRr tfibsegs W (cfg_at tfibsegs PC_memset regsT memT mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (YK11.getr regsT 1) mem2 (seg_rom tfibsegs)) md2 /\
       ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U mem2) md2 k /\
       ARU tfibsegs B lyc Sc U W mem2 md2 /\ pjs_msq regsT W memT d regs2 mem2 md2).
Proof.
intros ofr STK sp0 FP ly S W0 mem md own lyc Sc U W memT mdc k regsT o d HJ HARU Hsp Hal Hneg Hbud Hra Hgp Htp
  Hd Hx Hn Hd0 Hdn Ham Hdest Hrad Hhull Hperm.
pose proof (fsw_ecall_preU_at B STK sp0 FP ly S W0 mem md own lyc Sc U W memT mdc k regsT o HJ HARU Hsp Hal Hneg Hbud
  Hra Hgp Htp) as HPRE.
assert (HC : SRr tfibsegs W (cfg_at tfibsegs PC_memset regsT memT mdc)
  (fun W' c' => W' = W /\ exists regs' mem' md',
     c' = mkCfg (mkst regs' (YK11.getr regsT 1) mem' (seg_rom tfibsegs)) md' /\
     ARU tfibsegs B lyc Sc U W mem' md' /\ same_but_materialized mdc md' /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ ((d <= a < d + 56) \/ (spZ regsT - ESTACK <= a < spZ regsT)) ->
        aview tfibsegs (w_H W) (unpoison U mem') a = aview tfibsegs (w_H W) (unpoison U memT) a) /\
     (forall a, apresent (w_H W) (unpoison U memT) a -> apresent (w_H W) (unpoison U mem') a) /\
     pjs_msq regsT W memT d regs' mem' md')).
{ eapply SRr_mono; [exact (fs_memset_realizesU lyc Sc U W regsT memT mdc d 0 56 HPRE Hd Hx Hn ltac:(lia) Hd0 Hdn Hdest
    Ham Hrad (fun _ => Hhull) I)|].
  intros W' c' _ (-> & regs' & mem' & md' & Ec & HARU' & HP & Hsame & H10 & Hz & Hfr & Hpres).
  split; [reflexivity|]. exists regs', mem', md'.
  split; [rewrite Ec; unfold cfg_at, raZ, YG0d.w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact HARU'|]. split; [exact Hsame|].
  split; [|split; [|split; [exact HP|split; [|split; [exact Hfr | exact Hpres]]]]].
  - intros a Ha HWa.
    destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:EU.
    + apply (aview_unpoison_in tfibsegs). exact EU.
    + rewrite !(aview_unpoison_out tfibsegs) by exact EU.
      apply Hfr; [exact Ha | intros H'; apply HWa; left; exact H' | intros H'; apply HWa; right; exact H'].
  - intros a [Hh [b Hb]]. split; [exact Hh|]. unfold unpoison in Hb |- *.
    destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:EU; [eexists; reflexivity|].
    destruct (Hpres a (conj Hh (ex_intro _ b Hb))) as [_ [b' Hb']]. exists b'. exact Hb'.
  - intros i Hi. rewrite (Hz i Hi). reflexivity. }
assert (ESTACK = 4096) as Hes by reflexivity.
apply (fsw_intrin_atU B STK sp0 FP ly S W0 mem md own lyc Sc U W memT mdc k U
  (fun a => (d <= a < d + 56) \/ (spZ regsT - ESTACK <= a < spZ regsT)) (YK11.getr regsT 1) _
  (pjs_msq regsT W memT d) HJ HC).
intros a [Ha | Ha]; [exact (Hperm a Ha) | apply (pjs_wperm_stack ofr); rewrite Hsp in Ha; lia].
Qed.

(* ---- the resumed state after a runtime call that keeps the caller's frame (FSW_ret.fss_retT, built as
   fsw_after_callU_args builds it, from the caller's journal at the return memory and the call's frame equality) ---- *)
Lemma pjs_resume_rt : forall STK sp0 FP own ly S U (W0 : world tfibsegs) mem md lyc Sc (W : world tfibsegs) memT memR
  mdR k regsT regsR f xs cs rs gf r,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U memR) mdR k ->
  ARU tfibsegs B lyc Sc U W memR mdR ->
  aregs_preserved regsT regsR ->
  spZ regsT = sp0 - f -> 0 < f -> f <= STK -> f mod 16 = 0 ->
  (forall a, sp0 - f <= a < sp0 -> aview tfibsegs (w_H W) memR a = aview tfibsegs (w_H W) memT a) ->
  regions_wf (fsT_ret_regions f cs rs) = true ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regsR (fs_extraT ++ xs)) (mrestrict (w_H W) memT) (sp0 - f)) cs ->
  Forall (region_ok tfibsegs (Ereg regsR (fs_extraT ++ xs)) (mrestrict (w_H W) memR)) rs ->
  pairwise_disjoint (Ereg regsR (fs_extraT ++ xs)) (fsT_ret_regions f cs rs) ->
  atoms_ok (Ereg regsR (fs_extraT ++ xs)) gf ->
  st_ok tfibsegs (Ereg regsR (fs_extraT ++ xs)) (fss_retT r f cs rs gf)
    (restrict (w_H W) (mkst regsR (Z_to_bv 64 r) memR (seg_rom tfibsegs))).
Proof.
intros STK sp0 FP own ly S U W0 mem md lyc Sc W memT memR mdR k regsT regsR f xs cs rs gf r
  HJ HARU HP Hsp Hf HfS Hal Hfr Hwf Hin Hcs Hrs Hpd Hgf.
destruct HSS as [Hgot Hcell].
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Esp : getr regsR 2 = getr regsT 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp : spZ regsR = sp0 - f) by (unfold spZ; rewrite Esp; exact Hsp).
assert (E2 : bv_unsigned (ew (Ereg regsR (fs_extraT ++ xs)) 2) = sp0 - f)
  by (rewrite (ew_Ereg_nat regsR (fs_extraT ++ xs) 2 2%bv eq_refl); exact Usp).
assert (E32 : ew (Ereg regsR (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32 : bv_unsigned (ew (Ereg regsR (fs_extraT ++ xs)) 32) = SHADOW_OFF) by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
destruct (fsw_got_shadow B lyc Sc W (unpoison U memR) mdR Hgot Hcell HAR2) as [Kgot Kcell].
assert (MB : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W) memR) x = mbyte tfibsegs (mrestrict (w_H W) (unpoison U memR)) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B lyc Sc U W memR mdR (Z_to_bv 64 x) HARU
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM : forall a v, 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W) (unpoison U memR)) a 8 v -> val_mem tfibsegs (mrestrict (w_H W) memR) a 8 v).
{ intros a v Ha Hb Hv k0 Hk0. rewrite (MB (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H W) memR) tfib_D_GOT_asan_shadow_memory_dynamic_address 8
  tfib_D_asan_shadow_memory_dynamic_address).
{ apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U memR) _ _ Kgot)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H W) memR) tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
{ apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U memR) _ _ Kcell)]. }
rewrite restrict_mkst_fx. unfold fss_retT, fsT_ret_regions in *. cbn [app] in *. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor; [|constructor; [|exact Hrs]]].
  + unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs).
      apply (fsw_apresent_unpoison B lyc Sc U W memR mdR _ HARU); [lia|]. apply Hpres2. lia.
    * apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hin c Hc) as Hci.
      pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
      apply (chunk_ok_mbyte _ (mrestrict (w_H W) memT)); [|exact Hck].
      destruct Hci as [Hc0 Hc1]. intros i Hi. apply (mbyte_of_aview tfibsegs). apply Hfr. lia.
  + unfold fs_got_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
      (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
      [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
  + unfold fs_bcell_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
      [rewrite fsw_SOff0, E32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
- exact Hpd.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok at 1 2. cbn [af_lo af_hi af_al2].
  rewrite E2, U32. split; [|split; [|exact Hgf]].
  + change (2 ^ 4) with 16. split; [lia|]. split; [|lia].
    rewrite Zminus_mod, Hal16. assert (f mod 16 = 0) as -> by exact Hal. reflexivity.
  + rewrite Z.pow_0_r. split; [lia | split; [apply Z.mod_1_r | lia]].
Qed.

(* ---- image segments of fs.asan-ubsan (PT_LOADs, `readelf -lW`: [0x10000, +0x1fd20) R, [0x30d20, +0x6d954) R E,
   [0x9f678, +0x1988) RW (relro), [0xa1920, +0x55b3f0) RW): each lemma finds a segment of tfibsegs that covers its
   range, by position, and checks the bounds by computation ---- *)
Ltac pjs_seg_bounds :=
  match goal with |- Z.le ?lo ?x /\ Z.lt ?x (?lo' + ?sz) =>
    let l := eval vm_compute in lo in let h := eval vm_compute in sz in
    change lo with l; change sz with h end; lia.
Ltac pjs_seg_find :=
  intros x Hx; unfold in_img;
  first [ eexists; split; [left; reflexivity | pjs_seg_bounds]
        | eexists; split; [right; left; reflexivity | pjs_seg_bounds]
        | eexists; split; [right; right; left; reflexivity | pjs_seg_bounds]
        | eexists; split; [right; right; right; left; reflexivity | pjs_seg_bounds]
        | eexists; split; [right; right; right; right; left; reflexivity | pjs_seg_bounds]
        | eexists; split; [right; right; right; right; right; left; reflexivity | pjs_seg_bounds] ].
Lemma pjs_rw_img : forall x, 0xa1000 <= x < 0x5fd000 -> in_img tfibsegs x.
Proof. pjs_seg_find. Qed.
Lemma pjs_ro_img : forall x, 0x10000 <= x < 0x30000 -> in_img tfibsegs x.
Proof. pjs_seg_find. Qed.
Lemma pjs_relro_img : forall x, 0x9f000 <= x < 0xa1000 -> in_img tfibsegs x.
Proof. pjs_seg_find. Qed.
(* fuzz/alloc.c's statics, carried by any memory change that keeps every image byte *)
Lemma pjs_glob_keep : forall (W : world tfibsegs) m m' live peak cnt fail,
  (forall x, in_img tfibsegs x -> mbyte tfibsegs (mrestrict (w_H W) m') x = mbyte tfibsegs (mrestrict (w_H W) m) x) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail HK (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, 0xa1000 <= g -> g + 8 <= 0x5fd000 ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v H1 H2 Hv k Hk. rewrite HK; [exact (Hv k Hk)|]. apply pjs_rw_img. lia. }
unfold fs_glob, fs_glob_at in *. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VB; [lia | lia | exact G1]|].
split; [apply VB; [lia | lia | exact G2]|].
split; [apply VB; [lia | lia | exact G3]|].
split; [apply VB; [lia | lia | exact G4]|].
exact R.
Qed.
Lemma pjs_zero8 : forall (m : word -> option byte) a,
  (forall k, 0 <= k < 8 -> mbyte tfibsegs m (a + k) = Some (Z_to_bv 8 0)) -> val_mem tfibsegs m a 8 0.
Proof.
intros m a H k Hk. rewrite (H (Z.of_nat k) ltac:(lia)). f_equal. f_equal.
lazymatch goal with |- 0 = ?X => change X with ((Z.shiftr (0 mod 2 ^ (8 * Z.of_nat 8)) (8 * Z.of_nat k)) mod 256) end.
rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity.
Qed.
(* the new block of fuzz_strdup is apart from v *)
Lemma pjs_new_apart : forall ofr ly S ly4 S4 (W4 : world tfibsegs) m4 md4 v a k,
  AR tfibsegs B ly4 S4 W4 m4 md4 -> pjs_loc ofr ly S v -> pjs_loc ofr ly4 S4 v ->
  ablocks B ly4 S4 = ablocks B ly S ++ [(a - HEAD, k + HEAD)] -> 0 <= k ->
  forall x, a - HEAD <= x < a + k -> ~ (v <= x < v + 56).
Proof.
intros ofr ly S ly4 S4 W4 m4 md4 v a k HAR4 Hloc Hloc4 Ebl Hk x Hx Hvx.
assert (Hin4 : In (a - HEAD, k + HEAD) (ablocks B ly4 S4)) by (rewrite Ebl; apply in_or_app; right; left; reflexivity).
assert (Hreq : req_size (k + HEAD) = k + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (k + 16) 0); lia).
destruct ofr; cbn [pjs_loc] in Hloc, Hloc4.
- destruct Hloc4 as (cid & pos & Hin & Hc & H1 & H2).
  pose proof (sep_block_frame tfibsegs B LAWS ly4 S4 W4 m4 md4 _ _ cid pos HAR4 Hin4 Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd. unfold HEAD in *. lia.
- destruct Hloc as (b & m & Hin & H1 & H2).
  apply in_split in Hin as (l1 & l2 & El).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly4 S4 W4 m4 md4 (b, m) (a - HEAD, k + HEAD) l1 l2 [] HAR4) as Hd.
  rewrite Ebl, El, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd. unfold HEAD in *. lia.
Qed.
(* the expected callee-saved registers at pj_string's ret: sp back up by the frame, s0 / s1 / s2 reloaded from the
   frame (atoms xatom 1..3), the rest untouched *)
Definition pjs_expect (r : bv 5) : sv :=
  match bv_unsigned r with 2 => SOff 2 32 | 8 => SOff (xatom 1) 0 | 9 => SOff (xatom 2) 0 | 18 => SOff (xatom 3) 0
  | z => SOff (Z.to_nat z) 0 end.

(* ---- the tail: after fuzz_strdup returns (0x83ec4) to pj_string's ret (0x83efc), and fpostU ---- *)
Lemma pjs_tail : forall (ofr : bool)
  ly S UP (W : world tfibsegs) regs mem md v (cs : list Z) live peak cnt fail
  ly4 S4 UP4 (W4 : world tfibsegs) regs4 mem4 md4 a,
  ARU tfibsegs B ly S UP W mem md -> FSupoisonU.fs_heads B ly S UP ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  pjs_loc ofr ly S v -> v mod 8 = 0 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF v 56 ->
  Forall (fun c => c <> 0) cs ->
  ajournal tfibsegs B STK_pj_string (spZ regs) ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison UP mem) md []
    ly4 S4 W4 (unpoison UP4 mem4) md4 1 ->
  ARU tfibsegs B ly4 S4 UP4 W4 mem4 md4 ->
  st_ok tfibsegs (Ereg regs4 (fs_extraT ++ [YK11.getr regs 1; YK11.getr regs 8; YK11.getr regs 9; YK11.getr regs 18]))
    pjs_ss3 (restrict (w_H W4) (YK11.mkst regs4 (Z_to_bv 64 0x83ec4) mem4 (YK11.seg_rom tfibsegs))) ->
  YK11.getr regs4 10 = w64 a -> 4096 + HEAD <= a ->
  ablocks B ly4 S4 = ablocks B ly S ++ [(a - HEAD, Z.of_nat (length cs) + 1 + HEAD)] ->
  pjs_loc ofr ly4 S4 v ->
  FSupoisonU.fs_heads B ly4 S4 UP4 ->
  fs_rblock tfibsegs B ly4 S4 W4 mem4 a (Z.of_nat (length cs) + 1) ->
  zbytes_at tfibsegs W4 mem4 a (cs ++ [0]) ->
  fs_glob tfibsegs W4 mem4 (live + (Z.of_nat (length cs) + 1)) (Z.max peak (live + (Z.of_nat (length cs) + 1)))
    (cnt + 1) fail ->
  val_mem tfibsegs (mrestrict (w_H W4) mem4) v 4 4 ->
  (forall i, 4 <= i < 56 -> ~ (16 <= i < 24) -> mbyte tfibsegs (mrestrict (w_H W4) mem4) (v + i) = Some (Z_to_bv 8 0)) ->
  spZ regs4 = spZ regs - 32 -> YK11.getr regs4 8 = w64 v ->
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 2 -> bv_unsigned r <> 8 -> bv_unsigned r <> 9 ->
     bv_unsigned r <> 18 -> YK11.getr regs4 r = YK11.getr regs r) ->
  SRr tfibsegs W4 (mkCfg (YK11.mkst regs4 (Z_to_bv 64 0x83ec4) mem4 (YK11.seg_rom tfibsegs)) md4)
    (fpostU tfibsegs B STK_pj_string (spZ regs) ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S UP W mem md EV_pj_string UP4
      (fun ly' S' W' regs' mem' md' =>
         YK11.getr regs' 10 = w64 0 /\ 4096 + HEAD <= a /\
         ablocks B ly' S' = ablocks B ly S ++ [(a - HEAD, Z.of_nat (length cs) + 1 + HEAD)] /\
         rtree tfibsegs B ly' S' W' mem' v (PjTree.JStr cs) [(a, Z.of_nat (length cs) + 1)] /\
         pobj tfibsegs B ly' S' W' mem' v /\
         fs_glob tfibsegs W' mem' (live + (Z.of_nat (length cs) + 1)) (Z.max peak (live + (Z.of_nat (length cs) + 1)))
           (cnt + 1) fail)).
Proof.
intros ofr ly S UP W regs mem md v cs live peak cnt fail ly4 S4 UP4 W4 regs4 mem4 md4 a
  HARU HH Hra Hloc Hv8 Hra0 Hcs HJ4 HARU4 HS4 H10 Ha16 Ebl Hloc4 HH4 Hrb4 Hzb4 HG4 Hty4 Hz4 Hsp4 H8 Hcs4.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly S UP W mem md HARU) as HAR.
pose proof (ARU_AR tfibsegs B ly4 S4 UP4 W4 mem4 md4 HARU4) as HAR4.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FS : 32 + 4096 <= STK_pj_string) by (vm_compute; intros Hc; discriminate Hc).
destruct (pjs_loc_facts ofr ly S W _ md v HAR Hloc) as (V0 & V1 & Vam & Vx).
destruct (fsw_rblock_low B ly4 S4 W4 _ md4 mem4 a _ HAR4 Hrb4) as (A0 & A1).
set (n := Z.of_nat (length cs) + 1) in *.
assert (Hn1 : 1 <= n) by (unfold n; lia).
set (xs := [YK11.getr regs 1; YK11.getr regs 8; YK11.getr regs 9; YK11.getr regs 18]) in *.
set (E := Ereg regs4 (fs_extraT ++ xs)) in HS4.
assert (E2 : bv_unsigned (ew E 2) = spZ regs - 32)
  by (subst E; rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl); exact Hsp4).
assert (E8 : ew E 8 = Z_to_bv 64 v) by (subst E; rewrite (ew_Ereg_nat regs4 _ 8 8%bv eq_refl); exact H8).
assert (U8 : U E (SOff 8 0) = v) by (apply U_atom; [exact E8 | lia]).
assert (UB : U E fs_Bx = SHADOW_OFF).
{ unfold fs_Bx. apply U_atom; [|unfold SHADOW_OFF; lia].
  subst E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (HFPa : forall x, inFP ([(v, v + 56)] ++ FS_PSTAT_FP) x -> x < kLowShadowBeg \/ kHighShadowEnd <= x).
{ intros x (r & Hr & Hx). apply in_app_or in Hr as [Hr|Hr].
  - destruct Hr as [<- | []]. cbn [fst snd] in Hx. destruct (Vx x Hx) as (Happ & _).
    unfold app_addr in Happ. unfold kLowShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
  - unfold FS_PSTAT_FP in Hr. cbv [In] in Hr.
    repeat destruct Hr as [<- | Hr]; cbn [fst snd] in Hx; try (unfold kLowShadowBeg; lia). }
assert (Hra4 : range_addressable (aview tfibsegs (w_H W4) mem4) SHADOW_OFF v 56).
{ destruct ofr.
  - exact (pjs_ra_frame STK_pj_string (spZ regs) _ ly S UP W mem md [] ly4 S4 UP4 W4 mem4 md4 1 v HJ4 HARU HH HARU4 HH4
      Hloc Hloc4 HFPa Hra0).
  - exact (pjs_ra_heap ly4 S4 UP4 W4 mem4 md4 v HARU4 HH4 Hloc4). }
assert (SHOK : sh_ok tfibsegs fs_Bx pjs_SH E (mrestrict (w_H W4) mem4)).
{ constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H W4) mem4 E fs_Bx 8 v 56 v 0 56 Hra4 UB U8); [lia | lia |].
  intros x Hx. destruct (Vx x ltac:(lia)) as (Happ & _). unfold app_addr in Happ.
  unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
pjs_run_to_tokU ofr pj_string_tbl_ok HS4 HJ4 HARU4 SHOK fs_Bspan 540412.
- (* the run writes its frame and v's str field *)
  intros x (r & Hin & Hx). cbn [pjs_ss3 pjs_pin fss_retT fsT_ret_regions ss_mem app In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    cbn [fstk_ret fs_got_region fs_bcell_region pjs_vreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx.
  + rewrite E2 in Hx. apply (pjs_wperm_stack ofr). lia.
  + lia.
  + lia.
  + rewrite E8, (wz v) in Hx by lia.
    apply (pjs_perm_v ofr STK_pj_string (spZ regs) _ ly S ly4 S4 [] v Hloc); [ | | | lia].
    * intros p0 n0 Hp. rewrite Ebl. apply in_or_app. left. exact Hp.
    * intros cid pos. pose proof HJ4 as (_ & Hly4 & _). unfold frame_addr.
      destruct Hly4 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
    * intros y Hy. exists (v, v + 56). split; [left; reflexivity | cbn [fst snd]; lia].
- (* at the ret *)
  pose proof (fsw_reg_extra _ regs4 (fs_extraT ++ xs) _ ms 1%bv 1 HS4 ltac:(vm_compute; reflexivity)) as R1F.
  cbn [nth app fs_extraT] in R1F. subst xs. cbn [nth] in R1F.
  apply (fsw_retU B pj_string_tbl pj_string_tbl_ok W4 E _ ms _ STK_pj_string (spZ regs) ([(v, v + 56)] ++ FS_PSTAT_FP)
    regs ly S UP W mem md ly4 S4 UP4 EV_pj_string _ HS4 eq_refl ltac:(vm_compute; reflexivity)).
  + rewrite R1F. exact Hra.
  + exact HJ4.
  + exact HARU4.
  + apply (fsw_preserved _ E _ ms regs pjs_expect HS4); [vm_compute; reflexivity|].
    intros r Hr; cbv [CALLEE_SAVED In] in Hr; repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
    lazymatch goal with |- sv_denot _ (pjs_expect ?q) = _ =>
      let e := eval vm_compute in (pjs_expect q) in change (pjs_expect q) with e end;
    first
    [ eapply fsw_sp_back; exact E2
    | rewrite fsw_SOff0; subst E; lazymatch goal with |- ew _ ?k = _ =>
        let j := eval vm_compute in (Nat.sub k 32) in change k with (32 + j)%nat end;
      rewrite ew_Ereg_extra; reflexivity
    | rewrite fsw_SOff0; subst E; lazymatch goal with |- ew _ ?k = YK11.getr _ ?q =>
        rewrite (ew_Ereg_nat regs4 _ k q eq_refl) end;
      apply Hcs4;
      lazymatch goal with |- context [bv_unsigned ?q] =>
        let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end;
      try unfold acallee_saved; lia ].
  + intros mat2.
    set (memf := ms_mem ms) in *.
    pose proof (ARU_AR tfibsegs B ly4 S4 UP4 W4 memf _ HARU4) as HARf.
    assert (KEEP : forall x, 0 <= x < spZ regs - 32 -> ~ (v + 16 <= x < v + 24) ->
      mbyte tfibsegs (mrestrict (w_H W4) memf) x = mbyte tfibsegs (mrestrict (w_H W4) mem4) x).
    { intros x Hx Hvx. unfold mbyte. rewrite (HFr (Z_to_bv 64 x)); [reflexivity|].
      rewrite (wz x) by lia. intros (r & Hin & Hr). cbn [pjs_ss3 pjs_pin fss_retT fsT_ret_regions ss_mem app In] in Hin.
      destruct Hin as [<- | [<- | [<- | [<- | []]]]];
        cbn [fstk_ret fs_got_region fs_bcell_region pjs_vreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
      - rewrite E2 in Hr. lia.
      - lia.
      - lia.
      - rewrite E8, (wz v) in Hr by lia. lia. }
    assert (KEEPimg : forall x, in_img tfibsegs x ->
      mbyte tfibsegs (mrestrict (w_H W4) memf) x = mbyte tfibsegs (mrestrict (w_H W4) mem4) x).
    { intros x Hx. pose proof (fs_segs_img x Hx) as Hb. apply KEEP; [unfold FS_IMG_END in Hb; lia|].
      intros Hv. destruct (Vx x ltac:(lia)) as (_ & Hni & _). exact (Hni Hx). }
    (* the str field *)
    assert (Ha64 : 0 <= a < 2 ^ 64) by (clear - A0 A1 Hn1 C1; unfold HEAD in *; lia).
    pose proof (fsw_region_nth E _ _ 3 _ HS4 eq_refl) as HR3. cbn [ms_mem restrict] in HR3.
    pose proof (fsw_field E _ 8 v _ _ _ _ _ 16 8%N (SOff 10 0) a HR3 ltac:(rewrite E8; apply wz; lia)
      ltac:(cbn; tauto)
      ltac:(rewrite fsw_SOff0; subst E; rewrite (ew_Ereg_nat regs4 _ 10 10%bv eq_refl); exact H10)
      Ha64 ltac:(cbn; lia)) as Vstr.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vstr.
    (* the new block apart from v *)
    pose proof (pjs_new_apart ofr ly S ly4 S4 W4 _ _ v a n HARf Hloc Hloc4 Ebl ltac:(lia)) as Hap.
    (* v's bytes present at the end *)
    destruct (pjs_loc_facts ofr ly4 S4 W4 _ _ v HARf Hloc4) as (_ & _ & _ & Vxf).
    assert (Vpres : forall x, v <= x < v + 56 -> apresent (w_H W4) memf x).
    { intros x Hx. destruct (Vxf x Hx) as (Happ & _ & _ & [Hh [b Hb]]). split; [exact Hh|]. exists b.
      rewrite <- (pjs_unpoison_app ly4 S4 UP4 W4 memf _ x HARU4 ltac:(lia)); [exact Hb|].
      unfold app_addr in Happ. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
    assert (Hraf : range_addressable (aview tfibsegs (w_H W4) memf) SHADOW_OFF v 56).
    { destruct ofr.
      - exact (pjs_ra_frame STK_pj_string (spZ regs) _ ly S UP W mem md [] ly4 S4 UP4 W4 memf _ 1 v HJ4 HARU HH HARU4 HH4
          Hloc Hloc4 HFPa Hra0).
      - exact (pjs_ra_heap ly4 S4 UP4 W4 memf _ v HARU4 HH4 Hloc4). }
    split; [apply (fsw_reg_lit _ E _ ms 10%bv 0 HS4); [vm_compute; reflexivity | lia]|].
    split; [exact Ha16|].
    split; [exact Ebl|].
    split; [|split].
    * (* rtree *)
      unfold rtree, rnode. split; [|split].
      -- cbn [PjStruct.pj_node].
         split; [constructor; [intros Hc; inversion Hc | constructor]|].
         split; [intros b0 x Hb0 Hx; destruct Hb0 as [<- | []]; unfold PjStruct.pj_holds in Hx; cbn [fst snd] in Hx;
           apply (Hap x); unfold HEAD; lia|].
         exists 0, a, 0, 0, 0, 0. split.
         ++ split.
            { split; [exact Hv8|]. split; [lia|]. split; [lia|]. intros y Hy.
              destruct (Vpres y Hy) as [Hh [b Hb]]. split.
              - apply (apresent_writable tfibsegs). split; [exact Hh | exists b; exact Hb].
              - exists b. lazymatch goal with |- ?f _ ?m (?g y) = _ => change (mbyte tfibsegs m y = Some b) end.
                unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity. }
            split.
            { change (PjTree.tag (PjTree.JStr cs)) with 4. apply (fsw_val_pj_u32 tfibsegs); [| lia | lia | lia].
              intros k Hk. rewrite KEEP by lia. exact (Hty4 k Hk). }
            split.
            { apply (fsw_val_pj_u64 tfibsegs); [| lia | lia | lia]. apply pjs_zero8. intros k Hk.
              rewrite KEEP by lia. replace (v + 8 + k) with (v + (8 + k)) by lia. apply Hz4; lia. }
            split.
            { apply (fsw_val_pj_u64 tfibsegs); [exact Vstr | lia | lia | lia]. }
            split; [|split; [|split]];
              (apply (fsw_val_pj_u64 tfibsegs); [| lia | lia | lia]; apply pjs_zero8; intros k Hk; rewrite KEEP by lia;
               lazymatch goal with |- mbyte _ _ (v + ?o + k) = _ => replace (v + o + k) with (v + (o + k)) by lia end;
               apply Hz4; lia).
         ++ split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
            exists n. split; [|reflexivity].
            split; [left; reflexivity|]. split; [lia|].
            split.
            { apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hc0.
              apply In_nth with (d := 0) in Hc as (j & Hj & <-).
              destruct (Hzb4 j ltac:(rewrite length_app; cbn; lia)) as (_ & Hr).
              rewrite app_nth1 in Hr by lia. lia. }
            split; [lia|]. split; [rewrite length_map, length_app; cbn [length]; unfold n in *; lia|].
            intros j Hj. rewrite length_map in Hj.
            rewrite nth_error_map, (nth_error_nth' _ 0 Hj). cbn [option_map].
            destruct (Hzb4 j Hj) as (Hb & Hr).
            pose proof (Hb 0%nat ltac:(lia)) as Hb0. rewrite Z.add_0_r in Hb0.
            lazymatch goal with |- ?f _ ?m (?g (a + Z.of_nat j)) = _ =>
              change (f _ m (g (a + Z.of_nat j))) with (mbyte tfibsegs m (a + Z.of_nat j)) end.
            rewrite KEEP; [| rewrite length_app in Hj; cbn [length] in Hj; lia
              | intros Hv; apply (Hap (a + Z.of_nat j)); [rewrite length_app in Hj; cbn [length] in Hj; unfold n, HEAD; lia | lia]].
            rewrite Hb0. f_equal.
            lazymatch goal with |- Z_to_bv 8 (?f ?c 1%nat 0%nat) = _ =>
              change (f c 1%nat 0%nat) with ((Z.shiftr (c mod 2 ^ (8 * Z.of_nat 1)) (8 * Z.of_nat 0)) mod 256) end.
            change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
            rewrite Z.mod_mod by lia. rewrite Z.mod_small by lia. reflexivity.
      -- intros a0 k0 Hk0. destruct Hk0 as [E0 | []]. injection E0 as <- <-.
         destruct Hrb4 as (Hin & Hal & Hn0 & Hv). split; [exact Hin|]. split; [exact Hal|]. split; [exact Hn0|].
         intros k Hk. rewrite KEEP; [exact (Hv k Hk) | unfold HEAD in *; lia |].
         intros Hv'. apply (Hap (a - HEAD + Z.of_nat k)); [unfold n, HEAD in *; lia | lia].
      -- intros x Hx. exact Hx.
    * (* pobj *)
      split.
      -- destruct ofr; cbn [pjs_loc] in Hloc4.
         ++ left. destruct Hloc4 as (cid & pos & Hin & Hc & H1 & H2).
            destruct (al_frames _ _ LAWS ly4 S4 W4 _ _ cid pos HARf Hin) as (H32 & _).
            split; [|split; [exact Hv8 | exact Hraf]].
            exists cid, pos. split; [exact Hin|]. split; [exact Hc|]. split; [|split; [exact H1 | exact H2]].
            apply Z.mod_divide in H32; [|lia]. destruct H32 as [q Hq]. rewrite Hq.
            replace (q * 32) with ((q * 4) * 8) by lia. apply Z_mod_mult.
         ++ right. destruct Hloc4 as (b & m & Hin & H1 & H2).
            split; [exists b, m; split; [exact Hin|]; split; [exact H1 | exact H2]|]. split; [exact Hv8 | exact Hraf].
      -- intros i Hi. apply (apresent_writable tfibsegs). apply Vpres. lia.
    * (* the statics *)
      exact (pjs_glob_keep W4 mem4 memf _ _ _ _ KEEPimg HG4).
Qed.

(* ---- the call of fuzz_strdup and the resume ---- *)
Lemma pjs_mbyte_unp : forall ly S U (W : world tfibsegs) m md x,
  ARU tfibsegs B ly S U W m md -> 0 <= x < 2 ^ 64 -> ~ (SHADOW_OFF <= x < kHighMemBeg) ->
  mbyte tfibsegs (mrestrict (w_H W) (unpoison U m)) x = mbyte tfibsegs (mrestrict (w_H W) m) x.
Proof.
intros ly S U W m md x H Hx Hn. unfold mbyte, mrestrict.
rewrite (pjs_unpoison_app ly S U W m md x H Hx Hn). reflexivity.
Qed.
Lemma pjs_loc_journal : forall ofr STK sp0 FP ly S (W : world tfibsegs) mem md ly' S' (W' : world tfibsegs) mem' md' k v,
  ajournal tfibsegs B STK sp0 FP ly S W mem md [] ly' S' W' mem' md' k ->
  (forall p n, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S')) ->
  pjs_loc ofr ly S v -> pjs_loc ofr ly' S' v.
Proof.
intros ofr STK sp0 FP ly S W mem md ly' S' W' mem' md' k v HJ Hbl Hloc.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
destruct ofr; cbn [pjs_loc] in *.
- destruct Hloc as (cid & pos & Hin & Hc & H1 & H2). exists cid, pos.
  assert (Efa : frame_addr ly' cid pos = frame_addr ly cid pos)
    by (unfold frame_addr; destruct Hly as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
  rewrite Efa, Hfrs. cbn [app]. auto.
- destruct Hloc as (b & m & Hin & H1 & H2). exists b, m. auto.
Qed.
(* v's bytes across fuzz_strdup: its journal's footprint is FS_PSTAT_FP (image statics), v lies in an old block or in a
   fake frame, neither in the image *)
Lemma pjs_v_keep_call : forall ofr STKc spc ly S U (W : world tfibsegs) m md ly4 S4 U4 (W4 : world tfibsegs) m4 md4 kc v,
  ajournal tfibsegs B STKc spc FS_PSTAT_FP ly S W (unpoison U m) md [] ly4 S4 W4 (unpoison U4 m4) md4 kc ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly4 S4 U4 W4 m4 md4 ->
  pjs_loc ofr ly S v -> (forall p n, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly4 S4)) ->
  forall x, v <= x < v + 56 -> mbyte tfibsegs (mrestrict (w_H W4) m4) x = mbyte tfibsegs (mrestrict (w_H W) m) x.
Proof.
intros ofr STKc spc ly S U W m md ly4 S4 U4 W4 m4 md4 kc v HJ HARU HARU4 Hloc Hbl x Hx.
pose proof (ARU_AR tfibsegs B ly S U W m md HARU) as HAR.
destruct (pjs_loc_facts ofr ly S W _ md v HAR Hloc) as (V0 & V1 & _ & Vx).
destruct (Vx x Hx) as (Happ & Hni & _).
pose proof asan_consts as (C1 & _).
assert (HnF : ~ inFP FS_PSTAT_FP x).
{ intros Hf. apply Hni. destruct Hf as (r & Hr & Hxr). unfold FS_PSTAT_FP in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hxr; apply pjs_rw_img; lia. }
assert (HA : aview tfibsegs (w_H W4) (unpoison U4 m4) x = aview tfibsegs (w_H W) (unpoison U m) x).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _ & F4 & _).
  destruct ofr; cbn [pjs_loc] in Hloc.
  - destruct Hloc as (cid & pos & Hin & Hc & H1 & H2).
    apply (F4 cid pos x Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnF].
  - destruct Hloc as (b & mm & Hin & H1 & H2). unfold HEAD in H1.
    replace x with (b + (x - b)) by lia. apply (F2 b mm (x - b) Hin (Hbl b mm Hin)); [lia|].
    replace (b + (x - b)) with x by lia. exact HnF. }
apply (mbyte_of_aview tfibsegs) in HA.
unfold app_addr in Happ.
rewrite <- (pjs_mbyte_unp ly4 S4 U4 W4 m4 md4 x HARU4), <- (pjs_mbyte_unp ly S U W m md x HARU);
  [exact HA | | | |]; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia.
Qed.
(* a byte window of v next to an image byte range c..c+len: apart from it *)
Lemma pjs_disj_img : forall v lo hi c len, 0 <= lo -> lo < hi -> hi <= 56 -> 0 < len ->
  (forall x, v <= x < v + 56 -> ~ in_img tfibsegs x) -> (forall y, c <= y < c + len -> in_img tfibsegs y) ->
  v + hi <= c \/ c + len <= v + lo.
Proof.
intros v lo hi c len H0 H1 H2 H3 Hv Hc.
destruct (Z_le_gt_dec (v + hi) c) as [L|L]; [left; exact L|].
destruct (Z_le_gt_dec (c + len) (v + lo)) as [R|R]; [right; exact R|].
exfalso. apply (Hv (Z.max c (v + lo))); [lia|]. apply Hc. lia.
Qed.

Ltac pjs_cs_tac := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

Lemma pjs_call : forall (ofr : bool)
  ly S U (W : world tfibsegs) regs mem md ch v s' (cs : list Z) live peak cnt fail regs3 mem3 md3,
  fpreU tfibsegs B STK_pj_string ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  pjs_loc ofr ly S v -> v mod 8 = 0 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF v 56 ->
  Forall (fun c => c <> 0) cs ->
  quiet cnt fail 1 -> Z.of_nat (length cs) + 1 + HEAD < MALLOC_MAX -> live + (Z.of_nat (length cs) + 1) < 2 ^ 64 ->
  st_nev S + EV_pj_string <= EV_MAX -> blocks_bytes S + (Z.of_nat (length cs) + 1 + HEAD) <= LIVE_MAX ->
  ajournal tfibsegs B STK_pj_string (spZ regs) ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md []
    ly S W (unpoison U mem3) md3 0 ->
  ARU tfibsegs B ly S U W mem3 md3 ->
  YK11.getr regs3 1 = Z_to_bv 64 0x83ec4 -> spZ regs3 = spZ regs - 32 ->
  YK11.getr regs3 3 = w64 (as_gp B) -> YK11.getr regs3 4 = w64 (as_tp B) -> YK11.getr regs3 8 = w64 v ->
  YK11.getr regs3 18 = Z_to_bv 64 SHADOW_OFF -> YK11.getr regs3 10 = w64 s' ->
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 2 -> bv_unsigned r <> 8 -> bv_unsigned r <> 9 ->
     bv_unsigned r <> 18 -> YK11.getr regs3 r = YK11.getr regs r) ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 8) 8 (raZ regs) ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 16) 8 (s0Z regs) ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 24) 8 (bv_unsigned (YK11.getr regs 9)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) (spZ regs - 32) 8 (bv_unsigned (YK11.getr regs 18)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem3) v 4 4 ->
  (forall i, 4 <= i < 56 -> mbyte tfibsegs (mrestrict (w_H W) mem3) (v + i) = Some (Z_to_bv 8 0)) ->
  fs_glob tfibsegs W mem3 live peak cnt fail ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem3) ->
  cstr_ok tfibsegs W mem3 s' cs -> cstr_kept B ly S U s' cs ->
  SRr tfibsegs W (mkCfg (YK11.mkst regs3 (Z_to_bv 64 A_fuzz_strdup) mem3 (YK11.seg_rom tfibsegs)) md3)
    (fun W' c' => exists a,
       fpostU tfibsegs B STK_pj_string (spZ regs) ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U W mem md EV_pj_string
         (U ++ [(a - HEAD, HEAD)])
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10 = w64 0 /\ 4096 + HEAD <= a /\
            ablocks B ly' S' = ablocks B ly S ++ [(a - HEAD, Z.of_nat (length cs) + 1 + HEAD)] /\
            rtree tfibsegs B ly' S' W' mem' v (PjTree.JStr cs) [(a, Z.of_nat (length cs) + 1)] /\
            pobj tfibsegs B ly' S' W' mem' v /\
            fs_glob tfibsegs W' mem' (live + (Z.of_nat (length cs) + 1)) (Z.max peak (live + (Z.of_nat (length cs) + 1)))
              (cnt + 1) fail) W' c').
Proof.
intros ofr ly S U W regs mem md ch v s' cs live peak cnt fail regs3 mem3 md3 HPRE HH Hloc Hv8 Hra0 Hcs Hq Hmax Hlive
  Hnev Hbb HJ3 HARU3 R1 Hsp3 R3 R4 R8 R18 R10 Hcs3 V1 V2 V3 V4 Hty3 Hz3 HG3 HRO3 Hstr Hkept.
pose proof HSS as [Hgot Hcell].
destruct HPRE as [HAPU HRO].
pose proof (fsw_sp B _ ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof HAPU as (HAP & _ & _).
pose proof HAP as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HAPU) as HARU.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : STK_fuzz_strdup + 32 <= STK_pj_string) by (vm_compute; intros Hc; discriminate Hc).
assert (FS0 : 0 <= STK_fuzz_strdup) by (vm_compute; intros Hc; discriminate Hc).
destruct (pjs_loc_facts ofr ly S W _ md v HAR0 Hloc) as (V0 & V1' & Vam & Vx).
destruct Hstr as [Hstr0 Hstr1]. pose proof Hstr1 as (Hs4096 & Hsceil & _).
pose proof (proj1 HARU3) as HAR3.
(* fuzz_strdup's premise at the call *)
assert (HPREc : fpreU tfibsegs B STK_fuzz_strdup ly S U W regs3 mem3 md3 []).
{ split; [|exact HRO3]. split; [|exact (proj2 HARU3)].
  exact (afn_pre_at tfibsegs B STK_pj_string (spZ regs) _ ly S W (unpoison U mem) md [] ly S W (unpoison U mem3) md3 0
    regs3 STK_fuzz_strdup (-32) [] HJ3 ltac:(lia) ltac:(reflexivity) ltac:(lia) FS0 ltac:(lia)
    ltac:(rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity)
    ltac:(unfold raZ; rewrite R1, unsigned_lit_small by lia; lia) R3 R4
    ltac:(apply achain_low; unfold s0Z; rewrite R8; unfold w64; rewrite unsigned_lit_small by lia; lia)). }
eapply SRr_bind.
{ exact (fs_fuzz_strdup ly S U W regs3 mem3 md3 [] s' cs live peak cnt fail HPREc HH
    R10 (conj Hstr0 Hstr1) Hkept ltac:(intros x Hx Hx'; lia) HG3 (fun _ => Hlive)
    ltac:(destruct Hq as (_ & _ & Hq); lia) Hmax
    ltac:(unfold EV_pj_string, EV_fuzz_strdup in Hnev; lia) (fun _ => Hbb)). }
intros W4 c4 Hwle4 [(Hcf & _) | (Hcf & res & Hpost)].
{ exfalso. destruct Hq as (Hf & Hc0 & Hq). unfold SIZE_MAXZ in Hf. lia. }
unfold apost_baseU, fpostU in Hpost.
destruct Hpost as (ly4 & S4 & regs4 & mem4 & md4 & Ec4 & HJc & OK4 & PO4 & HP4 & H10 & Ha16 & Ebl & HH4 & Hrb4 & Hzb4 &
  HG4).
subst c4. rewrite R1.
pose proof HJc as (HAR4 & _).
assert (HARU4 : ARU tfibsegs B ly4 S4 (U ++ [(res - HEAD, HEAD)]) W4 mem4 md4) by (split; [exact HAR4 | split; assumption]).
assert (Hbl : forall p n, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly4 S4))
  by (intros p n Hp; rewrite Ebl; apply in_or_app; left; exact Hp).
pose proof (pjs_loc_journal ofr _ _ _ ly S W _ md3 ly4 S4 W4 _ md4 1 v HJc Hbl Hloc) as Hloc4.
destruct (pjs_loc_facts ofr ly4 S4 W4 _ md4 v HAR4 Hloc4) as (_ & _ & _ & Vx4).
destruct (fsw_rblock_low B ly4 S4 W4 _ md4 mem4 res _ HAR4 Hrb4) as (A0 & A1).
pose proof Hrb4 as (_ & Hres16 & _).
set (xs := [YK11.getr regs 1; YK11.getr regs 8; YK11.getr regs 9; YK11.getr regs 18]).
assert (P2 : YK11.getr regs4 2 = YK11.getr regs3 2) by exact (fsw_pres regs3 regs4 2%bv HP4 ltac:(pjs_cs_tac)).
assert (P8 : YK11.getr regs4 8 = w64 v)
  by (rewrite (fsw_pres regs3 regs4 8%bv HP4 ltac:(pjs_cs_tac)); exact R8).
assert (P18 : YK11.getr regs4 18 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (fsw_pres regs3 regs4 18%bv HP4 ltac:(pjs_cs_tac)); exact R18).
assert (Hsp4 : spZ regs4 = spZ regs - 32) by (unfold spZ in *; rewrite P2; exact Hsp3).
assert (E2 : bv_unsigned (ew (Ereg regs4 (fs_extraT ++ xs)) 2) = spZ regs - 32)
  by (rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl); exact Hsp4).
assert (E8 : ew (Ereg regs4 (fs_extraT ++ xs)) 8 = Z_to_bv 64 v) by (rewrite (ew_Ereg_nat regs4 _ 8 8%bv eq_refl); exact P8).
(* the resumed state *)
destruct (fsw_after_callFPU_args B STK_pj_string (spZ regs) ([(v, v + 56)] ++ FS_PSTAT_FP) [] ly S U W mem md W ly S U
  mem3 md3 0 STK_fuzz_strdup FS_PSTAT_FP 32 regs3 ly4 S4 (U ++ [(res - HEAD, HEAD)]) W4 regs4 mem4 md4 1 xs pjs_cs
  [pjs_vreg 16 24] [pjs_vfact; (10%nat, mkAF 4112 PJS_CEIL 4)] 0x83ec4 Hgot Hcell HJ3 HARU3 HJc)
  as (HJ4 & HARU4' & HS4').
- (* fsw_fp_sub: the statics are image bytes in the caller's FP *)
  intros x (r & Hr & Hx). right. right. left. split.
  + exists r. split; [apply in_or_app; right; exact Hr | exact Hx].
  + unfold FS_PSTAT_FP in Hr. destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hx; apply pjs_rw_img; lia.
- exact OK4.
- exact PO4.
- exact HP4.
- lia.
- lia.
- exact FS0.
- lia.
- reflexivity.
- vm_compute. reflexivity.
- unfold pjs_cs. repeat constructor; cbn; lia.
- unfold pjs_cs. repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val tfibsegs _ _ _ 24 8%N (SOff (xatom 0) 0) (raZ regs));
      [rewrite fsw_SOff0; change (xatom 0) with (32 + 1)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
       unfold raZ; symmetry; apply Z_to_bv_bv_unsigned | unfold raZ; apply u64_range | cbn; lia
       | replace (spZ regs - 32 + 24) with (spZ regs - 8) by lia; exact V1].
  + apply (chunk_ok_val tfibsegs _ _ _ 16 8%N (SOff (xatom 1) 0) (s0Z regs));
      [rewrite fsw_SOff0; change (xatom 1) with (32 + 2)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
       unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned | unfold s0Z; apply u64_range | cbn; lia
       | replace (spZ regs - 32 + 16) with (spZ regs - 16) by lia; exact V2].
  + apply (chunk_ok_val tfibsegs _ _ _ 8 8%N (SOff (xatom 2) 0) (bv_unsigned (YK11.getr regs 9)));
      [rewrite fsw_SOff0; change (xatom 2) with (32 + 3)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
       symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia
       | replace (spZ regs - 32 + 8) with (spZ regs - 24) by lia; exact V3].
  + apply (chunk_ok_val tfibsegs _ _ _ 0 8%N (SOff (xatom 3) 0) (bv_unsigned (YK11.getr regs 18)));
      [rewrite fsw_SOff0; change (xatom 3) with (32 + 4)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
       symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia
       | replace (spZ regs - 32 + 0) with (spZ regs - 32) by lia; exact V4].
- constructor; [|constructor]. unfold pjs_vreg.
  apply (fsw_pj_part_okW tfibsegs _ _ 8 v v 16 24 16 24 [] ltac:(lia) ltac:(lia));
    [| rewrite E8; apply wz; lia | lia | lia | right; lia | constructor].
  intros o Ho. apply (apresent_writable tfibsegs).
  destruct (Vx4 (v + o) ltac:(lia)) as (Happ & _ & _ & [Hh [b Hb]]). split; [exact Hh|]. exists b.
  rewrite <- (pjs_unpoison_app ly4 S4 _ W4 mem4 md4 (v + o) HARU4 ltac:(lia)); [exact Hb|].
  unfold app_addr in Happ. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
- apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pjs_vreg, extent_of_region.
  cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E8, (wz v) by lia.
  assert (NI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x) by (intros x Hx; exact (proj1 (proj2 (Vx x Hx)))).
  pose proof (pjs_disj_img v 16 24 tfib_D_GOT_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) NI ltac:(intros y Hy; apply pjs_relro_img; unfold tfib_D_GOT_asan_shadow_memory_dynamic_address in *; lia))
    as D1.
  pose proof (pjs_disj_img v 16 24 tfib_D_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) NI ltac:(intros y Hy; apply pjs_rw_img; unfold tfib_D_asan_shadow_memory_dynamic_address in *; lia))
    as D2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- cbn [atoms_ok]. unfold pjs_vfact, afact_ok. cbn [af_lo af_hi af_al2]. rewrite E8, (wz v) by lia.
  rewrite (ew_Ereg_nat regs4 _ 10 10%bv eq_refl), H10. unfold w64. rewrite (wz res) by (unfold HEAD in *; lia).
  change (2 ^ 3) with 8. change (2 ^ 4) with 16. unfold PJS_CEIL, HEAD in *.
  split; [split; [lia | split; [exact Hv8 | lia]]|]. split; [split; [lia | split; [exact Hres16 | lia]] | exact I].
- (* s2 pinned to the shadow base atom *)
  assert (HS4 : st_ok tfibsegs (Ereg regs4 (fs_extraT ++ xs)) pjs_ss3
    (restrict (w_H W4) (YK11.mkst regs4 (Z_to_bv 64 0x83ec4) mem4 (YK11.seg_rom tfibsegs)))).
  { unfold pjs_ss3, pjs_pin. apply (st_ok_regs tfibsegs _ _ _ _ HS4').
    intros q. destruct (decide (q = 18%bv)) as [-> | Hq18].
    - rewrite sr_get_set_same by reflexivity. change (sr_get (ss_regs (fss_retT 0x83ec4 32 pjs_cs [pjs_vreg 16 24]
        [pjs_vfact; (10%nat, mkAF 4112 PJS_CEIL 4)])) 18%bv) with (SOff 18 0).
      rewrite !fsw_SOff0. change 32%nat with (32 + 0)%nat at 1. rewrite ew_Ereg_extra.
      rewrite (ew_Ereg_nat regs4 _ 18 18%bv eq_refl), P18. reflexivity.
    - rewrite sr_get_set_other by exact Hq18. reflexivity. }
  eapply SRr_mono.
  + apply (pjs_tail ofr ly S U W regs mem md v cs live peak cnt fail ly4 S4 (U ++ [(res - HEAD, HEAD)]) W4 regs4 mem4
      md4 res HARU HH Hra Hloc Hv8 Hra0 Hcs HJ4 HARU4' HS4 H10 Ha16 Ebl Hloc4 HH4 Hrb4 Hzb4 HG4).
    * intros k Hk. rewrite (pjs_v_keep_call ofr _ _ ly S U W mem3 md3 ly4 S4 _ W4 mem4 md4 1 v HJc HARU3 HARU4 Hloc Hbl);
        [exact (Hty3 k Hk) | lia].
    * intros i Hi Hi'. rewrite (pjs_v_keep_call ofr _ _ ly S U W mem3 md3 ly4 S4 _ W4 mem4 md4 1 v HJc HARU3 HARU4 Hloc
        Hbl); [exact (Hz3 i ltac:(lia)) | lia].
    * exact Hsp4.
    * exact P8.
    * intros r Hr H2 H8 H9 H18. rewrite (fsw_pres regs3 regs4 r HP4 Hr). exact (Hcs3 r Hr H2 H8 H9 H18).
  + intros W' c' _ Hp. exists res. exact Hp.
Qed.

(* the relro / read-only view, carried by any memory change that keeps every image byte *)
Lemma pjs_arodata_keep : forall (W : world tfibsegs) m m',
  (forall x, in_img tfibsegs x -> aview tfibsegs (w_H W) m' x = aview tfibsegs (w_H W) m x) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m').
Proof.
intros W m m' HK HR a Ha Ho He. rewrite HK; [exact (HR a Ha Ho He)|].
destruct Ha as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr]|].
apply pjs_relro_img. unfold FS_RLO, FS_RHI in Hr. lia.
Qed.
(* a C string apart from v, carried by a change of v's bytes and the stack above alloc_ceiling only *)
Lemma pjs_cstr_keep : forall (W : world tfibsegs) m m' v p l,
  (forall x, 0 <= x < alloc_ceiling -> ~ (v <= x < v + 56) -> aview tfibsegs (w_H W) m' x = aview tfibsegs (w_H W) m x) ->
  (forall x, v <= x < v + 56 -> aview tfibsegs (w_H W) m x <> None -> aview tfibsegs (w_H W) m' x <> None) ->
  (forall x, v <= x < v + 56 -> x < kLowShadowBeg \/ kHighMemBeg <= x) ->
  (p + (Z.of_nat (length l) + 1) <= v \/ v + 56 <= p) ->
  cstr_ok tfibsegs W m p l -> cstr_ok tfibsegs W m' p l.
Proof.
intros W m m' v p l Hag Hvis Happ Hdj ((Hg & Hnz) & H4096 & Hceil & H32 & Ham & Hra & Hhull & Htail).
pose proof asan_consts as (C1 & _).
assert (SHB : forall x, 0 <= x < alloc_ceiling -> SHADOW_OFF <= shadow_addr x /\ shadow_addr x + 8 < kHighMemBeg).
{ intros x Hx. unfold shadow_addr, SHADOW_OFF, kHighMemBeg. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  assert (x / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia). lia. }
assert (NV : forall y, SHADOW_OFF <= y < kHighMemBeg -> ~ (v <= y < v + 56)).
{ intros y Hy Hv. destruct (Happ y Hv); unfold SHADOW_OFF, kLowShadowBeg in *; lia. }
split; [split; [|exact Hnz]|].
- intros j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr]. intros k Hk. rewrite <- (Hv k Hk).
  rewrite length_app in Hj; cbn [length] in Hj.
  apply (mbyte_of_aview tfibsegs). apply Hag; lia.
- split; [exact H4096|]. split; [exact Hceil|]. split; [exact H32|]. split; [exact Ham|].
  split; [|split].
  + intros x Hx. destruct (Hra x Hx) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
    rewrite <- Hs. change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
    destruct (SHB x ltac:(lia)) as [S1 S2].
    apply Hag; [unfold kHighMemBeg, SHADOW_OFF in *; lia | apply NV; lia].
  + intros sx Hsx. pose proof (Hhull sx Hsx) as Hv.
    destruct (SHB p ltac:(lia)) as [S1 S2]. destruct (SHB (p + (Z.of_nat (length l) + 1) - 1) ltac:(lia)) as [S3 S4].
    assert (B1 : SHADOW_OFF <= shadow_addr p / 8 * 8).
    { assert (SHADOW_OFF = SHADOW_OFF / 8 * 8) as E by reflexivity.
      rewrite E. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
    assert (B2 : shadow_addr (p + (Z.of_nat (length l) + 1) - 1) / 8 * 8 <= shadow_addr (p + (Z.of_nat (length l) + 1) - 1))
      by (pose proof (Z.mul_div_le (shadow_addr (p + (Z.of_nat (length l) + 1) - 1)) 8 ltac:(lia)); lia).
    rewrite Hag; [exact Hv | unfold kHighMemBeg, SHADOW_OFF in *; lia | apply NV; lia].
  + intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)) as Hm.
    (* the word holding the NUL ends at or below alloc_ceiling: p + |l| + 1 <= alloc_ceiling and alloc_ceiling is
       4096-aligned (YM05.alloc_ceiling_value), so (p + |l|) / 8 * 8 + 8 <= alloc_ceiling (FSW_K.cstr_ok_below) *)
    pose proof (Z.div_mod (p + Z.of_nat (length l)) 8 ltac:(lia)).
    pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)).
    pose proof (proj2 YM05.alloc_ceiling_value).
    destruct (Z_le_gt_dec (v + 56) x) as [L | L]; [rewrite Hag; [exact (Htail x Hx) | lia | lia]|].
    destruct (Z_le_gt_dec v x) as [L2 | L2]; [apply Hvis; [lia | exact (Htail x Hx)]|].
    rewrite Hag; [exact (Htail x Hx) | lia | lia].
Qed.
(* an image string, from the unpoisoned reading to the machine's (its bytes and their shadow are no head's) *)
Lemma pjs_cstr_unp : forall ly S U (W : world tfibsegs) m md p l,
  ARU tfibsegs B ly S U W m md -> FSupoisonU.fs_heads B ly S U ->
  (forall x, p <= x < p + Z.of_nat (length l) + 8 -> in_img tfibsegs x) ->
  cstr_ok tfibsegs W (unpoison U m) p l -> cstr_ok tfibsegs W m p l.
Proof.
intros ly S U W m md p l HARU HH Himg ((Hg & Hnz) & H4096 & Hceil & H32 & Ham & Hra & Hhull & Htail).
pose proof (ARU_AR tfibsegs B ly S U W m md HARU) as HAR.
pose proof asan_consts as (C1 & _).
assert (IB : forall x, p <= x < p + Z.of_nat (length l) + 8 -> 0 <= x < FS_IMG_END)
  by (intros x Hx; exact (fs_segs_img x (Himg x Hx))).
assert (AV : forall x, p <= x < p + Z.of_nat (length l) + 8 ->
  aview tfibsegs (w_H W) m x = aview tfibsegs (w_H W) (unpoison U m) x).
{ intros x Hx. symmetry. pose proof (IB x Hx). apply (pjs_aview_app ly S U W m md x HARU);
    unfold FS_IMG_END, SHADOW_OFF in *; lia. }
assert (NOH : forall x, p <= x < p + Z.of_nat (length l) + 8 ->
  forall h mm, In (h, mm) (ablocks B ly S) -> 16 <= req_size mm -> ~ (h <= x < h + 16)).
{ intros x Hx h mm Hin Hreq Hhx. apply (blk_img tfibsegs B LAWS ly S W _ md h mm x HAR Hin ltac:(lia)).
  exact (Himg x Hx). }
pose proof (IB p ltac:(lia)) as Pb. pose proof (IB (p + Z.of_nat (length l)) ltac:(lia)) as Pe.
split; [split; [|exact Hnz]|].
- intros j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr]. intros k Hk. rewrite <- (Hv k Hk).
  rewrite length_app in Hj; cbn [length] in Hj.
  apply (mbyte_of_aview tfibsegs). apply AV. lia.
- split; [exact H4096|]. split; [exact Hceil|]. split; [exact H32|]. split; [exact Ham|].
  split; [|split].
  + intros x Hx. destruct (Hra x Hx) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
    rewrite <- Hs. change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). symmetry.
    apply (aview_unpoison_out tfibsegs).
    pose proof (IB x ltac:(lia)).
    rewrite (wz (shadow_addr x)) by (unfold shadow_addr, SHADOW_OFF, FS_IMG_END in *; pose proof (Z.div_pos x 8); lia).
    apply (pjs_shadow_out ly S U W m md x HARU HH ltac:(lia)). exact (NOH x ltac:(lia)).
  + intros sx Hsx. pose proof (Hhull sx Hsx) as Hv.
    assert (Hs64 : 0 <= sx < 2 ^ 64).
    { unfold shadow_addr, SHADOW_OFF, FS_IMG_END in *.
      assert (0 <= (2147450880 + p / 8) / 8) by (apply Z.div_pos; [pose proof (Z.div_pos p 8); lia | lia]).
      pose proof (Z.mul_div_le (2147450880 + (p + (Z.of_nat (length l) + 1) - 1) / 8) 8 ltac:(lia)).
      assert ((p + (Z.of_nat (length l) + 1) - 1) / 8 <= 0x5fd000 / 8) by (apply Z.div_le_mono; lia).
      lia. }
    destruct (in_ush U sx) eqn:EU.
    * rewrite (ARU_poisoned tfibsegs B ly S U W m md HARU sx EU). discriminate.
    * rewrite (aview_unpoison_out tfibsegs) in Hv by (rewrite (wz sx Hs64); exact EU). exact Hv.
  + intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)) as Hm.
    rewrite AV; [exact (Htail x Hx) | lia].
Qed.

(* the callee-saved registers other than sp, s0, s1, s2 *)
Lemma pjs_cs_other : forall (P : bv 5 -> Prop), P 3%bv -> P 4%bv -> P 19%bv -> P 20%bv -> P 21%bv -> P 22%bv ->
  P 23%bv -> P 24%bv -> P 25%bv -> P 26%bv -> P 27%bv ->
  forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 2 -> bv_unsigned r <> 8 -> bv_unsigned r <> 9 ->
  bv_unsigned r <> 18 -> P r.
Proof.
intros P P3 P4 P19 P20 P21 P22 P23 P24 P25 P26 P27 r Hr H2 H8 H9 H18. unfold acallee_saved in Hr.
assert (Hc : bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/
  bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/
  bv_unsigned r = 27) by lia.
repeat (destruct Hc as [Hc | Hc]; [match goal with HP : P ?q |- _ =>
  lazymatch goal with Hq : bv_unsigned r = ?z |- _ =>
    let w := eval vm_compute in (bv_unsigned q) in
    lazymatch w with z => replace r with q by (apply bv_eq; rewrite Hc; reflexivity); exact HP end end end|]).
replace r with (27%bv : bv 5) by (apply bv_eq; rewrite Hc; reflexivity). exact P27.
Qed.
Ltac pjs_lit_tac := lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; try unfold acallee_saved; lia.

(* ---- after the memset (0x83e8c) to the fuzz_strdup call (0x83ec0 -> 0x82d60) ---- *)
Lemma pjs_seg2 : forall (ofr : bool)
  ly S UP (W : world tfibsegs) regs mem md ch v s (cs : list Z) live peak cnt fail regs2 mem2 md2,
  fpreU tfibsegs B STK_pj_string ly S UP W regs mem md ch -> FSupoisonU.fs_heads B ly S UP ->
  pjs_loc ofr ly S v -> v mod 8 = 0 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF v 56 ->
  (s = 0 /\ cs = [] \/ s <> 0 /\ cstr_ok tfibsegs W mem2 s cs /\ cstr_kept B ly S UP s cs /\
     (s + (Z.of_nat (length cs) + 1) <= v \/ v + 56 <= s)) ->
  quiet cnt fail 1 -> Z.of_nat (length cs) + 1 + HEAD < MALLOC_MAX -> live + (Z.of_nat (length cs) + 1) < 2 ^ 64 ->
  st_nev S + EV_pj_string <= EV_MAX -> blocks_bytes S + (Z.of_nat (length cs) + 1 + HEAD) <= LIVE_MAX ->
  ajournal tfibsegs B STK_pj_string (spZ regs) ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison UP mem) md []
    ly S W (unpoison UP mem2) md2 0 ->
  ARU tfibsegs B ly S UP W mem2 md2 ->
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ [YK11.getr regs 1; YK11.getr regs 8; YK11.getr regs 9; YK11.getr regs 18]))
    (if s =? 0 then pjs_ss2z else pjs_ss2n)
    (restrict (w_H W) (YK11.mkst regs2 (Z_to_bv 64 0x83e8c) mem2 (YK11.seg_rom tfibsegs))) ->
  fs_glob tfibsegs W mem2 live peak cnt fail ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem2) ->
  (forall i, 0 <= i < 56 -> mbyte tfibsegs (mrestrict (w_H W) mem2) (v + i) = Some (Z_to_bv 8 0)) ->
  spZ regs2 = spZ regs - 32 -> YK11.getr regs2 8 = w64 v -> YK11.getr regs2 9 = w64 s ->
  YK11.getr regs2 3 = w64 (as_gp B) -> YK11.getr regs2 4 = w64 (as_tp B) ->
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 2 -> bv_unsigned r <> 8 -> bv_unsigned r <> 9 ->
     bv_unsigned r <> 18 -> YK11.getr regs2 r = YK11.getr regs r) ->
  SRr tfibsegs W (mkCfg (YK11.mkst regs2 (Z_to_bv 64 0x83e8c) mem2 (YK11.seg_rom tfibsegs)) md2)
    (fun W' c' => exists a,
       fpostU tfibsegs B STK_pj_string (spZ regs) ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S UP W mem md EV_pj_string
         (UP ++ [(a - HEAD, HEAD)])
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10 = w64 0 /\ 4096 + HEAD <= a /\
            ablocks B ly' S' = ablocks B ly S ++ [(a - HEAD, Z.of_nat (length cs) + 1 + HEAD)] /\
            rtree tfibsegs B ly' S' W' mem' v (PjTree.JStr cs) [(a, Z.of_nat (length cs) + 1)] /\
            pobj tfibsegs B ly' S' W' mem' v /\
            fs_glob tfibsegs W' mem' (live + (Z.of_nat (length cs) + 1)) (Z.max peak (live + (Z.of_nat (length cs) + 1)))
              (cnt + 1) fail) W' c').
Proof.
intros ofr ly S UP W regs mem md ch v s cs live peak cnt fail regs2 mem2 md2 HPRE HH Hloc Hv8 Hra0 Hscase Hq Hmax
  Hlive Hnev Hbb HJ2 HARU2 HS2 HG2 HRO2 Hz2 Hsp2 R8 R9 R3 R4 Hcs2.
pose proof HPRE as [HAPU HRO].
pose proof (fsw_sp B _ ly S UP W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof HAPU as (HAP & _ & _).
pose proof HAP as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_ARU B _ ly S UP W regs mem md ch HAPU) as HARU.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : 32 + 4096 <= STK_pj_string) by (vm_compute; intros Hc; discriminate Hc).
destruct (pjs_loc_facts ofr ly S W _ md v HAR0 Hloc) as (V0 & V1 & Vam & Vx).
set (xs := [YK11.getr regs 1; YK11.getr regs 8; YK11.getr regs 9; YK11.getr regs 18]) in *.
set (E := Ereg regs2 (fs_extraT ++ xs)) in HS2.
assert (E2 : bv_unsigned (ew E 2) = spZ regs - 32)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact Hsp2).
assert (E8 : ew E 8 = Z_to_bv 64 v) by (subst E; rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl); exact R8).
assert (U8 : U E (SOff 8 0) = v) by (apply U_atom; [exact E8 | lia]).
assert (UB : U E fs_Bx = SHADOW_OFF).
{ unfold fs_Bx. apply U_atom; [|unfold SHADOW_OFF; lia].
  subst E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (HFPa : forall x, inFP ([(v, v + 56)] ++ FS_PSTAT_FP) x -> x < kLowShadowBeg \/ kHighShadowEnd <= x).
{ intros x (r & Hr & Hx). apply in_app_or in Hr as [Hr|Hr].
  - destruct Hr as [<- | []]. cbn [fst snd] in Hx. destruct (Vx x Hx) as (Happ & _).
    unfold app_addr in Happ. unfold kLowShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
  - unfold FS_PSTAT_FP in Hr. cbv [In] in Hr.
    repeat destruct Hr as [<- | Hr]; cbn [fst snd] in Hx; try (unfold kLowShadowBeg; lia). }
assert (Hra2 : range_addressable (aview tfibsegs (w_H W) mem2) SHADOW_OFF v 56).
{ destruct ofr.
  - exact (pjs_ra_frame STK_pj_string (spZ regs) _ ly S UP W mem md [] ly S UP W mem2 md2 0 v HJ2 HARU HH HARU2 HH
      Hloc Hloc HFPa Hra0).
  - exact (pjs_ra_heap ly S UP W mem2 md2 v HARU2 HH Hloc). }
assert (SHOK : sh_ok tfibsegs fs_Bx pjs_SH E (mrestrict (w_H W) mem2)).
{ constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H W) mem2 E fs_Bx 8 v 56 v 0 56 Hra2 UB U8); [lia | lia |].
  intros x Hx. destruct (Vx x ltac:(lia)) as (Happ & _). unfold app_addr in Happ.
  unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
assert (NI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x) by (intros x Hx; exact (proj1 (proj2 (Vx x Hx)))).
assert (WR : forall x, in_wrange E (fsT_ret_regions 32 pjs_cs [pjs_vreg 0 4]) x ->
  spZ regs - 32 <= x < spZ regs \/ v <= x < v + 4).
{ intros x (r & Hin & Hx). cbn [fsT_ret_regions app In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    cbn [fstk_ret fs_got_region fs_bcell_region pjs_vreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx.
  - rewrite E2 in Hx. left. lia.
  - lia.
  - lia.
  - rewrite E8, (wz v) in Hx by lia. right. lia. }
assert (AWR : forall x, in_wrange E (fsT_ret_regions 32 pjs_cs [pjs_vreg 0 4]) x ->
  pjs_wperm ofr STK_pj_string (spZ regs) ([(v, v + 56)] ++ FS_PSTAT_FP) ly S ly S [] x).
{ intros x Hx. destruct (WR x Hx) as [Hs | Hv].
  - apply (pjs_wperm_stack ofr). lia.
  - apply (pjs_perm_v ofr STK_pj_string (spZ regs) _ ly S ly S [] v Hloc); [ | | | lia].
    + intros p0 n0 Hp. exact Hp.
    + intros cid pos. reflexivity.
    + intros y Hy. exists (v, v + 56). split; [left; reflexivity | cbn [fst snd]; lia]. }
(* the run's frame: what stays at the call *)
assert (KEEPf : forall ms', frame_of E (fsT_ret_regions 32 pjs_cs [pjs_vreg 0 4]) (mrestrict (w_H W) mem2)
    (mrestrict (w_H W) (ms_mem ms')) ->
  forall x, 0 <= x < spZ regs - 32 -> ~ (v <= x < v + 4) ->
  mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms')) x = mbyte tfibsegs (mrestrict (w_H W) mem2) x).
{ intros ms' HFr x Hx Hvx. unfold mbyte. rewrite (HFr (Z_to_bv 64 x)); [reflexivity|].
  rewrite (wz x) by lia. intros Hin. destruct (WR x Hin); lia. }
destruct (Z.eqb_spec s 0) as [Hs0 | Hs0].
- (* s = NULL: fuzz_strdup of the empty literal 0x21020 *)
  subst s. destruct Hscase as [[_ Hcs0] | [Hn _]]; [|lia]. subst cs.
  change (if 0 =? 0 then pjs_ss2z else pjs_ss2n) with pjs_ss2z in HS2.
  pjs_run_to_tokU ofr pj_string_tbl_ok HS2 HJ2 HARU2 SHOK fs_Bspan 535904.
  + exact AWR.
  + pose proof (KEEPf ms HFr) as KEEP.
    assert (KEEPimg : forall x, in_img tfibsegs x ->
      aview tfibsegs (w_H W) (ms_mem ms) x = aview tfibsegs (w_H W) mem2 x).
    { intros x Hx. pose proof (fs_segs_img x Hx) as Hb. unfold aview. rewrite KEEP; [reflexivity | unfold FS_IMG_END in Hb; lia|].
      intros Hv. exact (NI x ltac:(lia) Hx). }
    pose proof (fsw_region_nth E _ _ 0 _ HS2 eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
    pose proof (fsw_region_nth E _ _ 3 _ HS2 eq_refl) as HR3. cbn [ms_mem restrict] in HR3.
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS2 eq_refl). cbn [ss_pc].
    pose proof (proj1 HARU2) as HAR3.
    destruct (IMG) as (_ & IMGc).
    destruct (IMGc ly S W _ _ HAR3 ltac:(apply (pjs_arodata_keep W mem2 (unpoison UP (ms_mem ms)));
      [intros x Hx; rewrite (pjs_aview_app ly S UP W (ms_mem ms) _ x HARU2); [exact (KEEPimg x Hx) | | ];
       pose proof (fs_segs_img x Hx); unfold FS_IMG_END, SHADOW_OFF in *; lia | exact HRO2]))
      as (_ & _ & Hstrs & _).
    assert (Hlit : cstr_ok tfibsegs W (unpoison UP (ms_mem ms)) 0x21020 []).
    { unfold FS_RO_STRS in Hstrs. repeat (apply Forall_inv_tail in Hstrs; try (apply Forall_inv in Hstrs; exact (proj1 Hstrs))). }
    apply (pjs_call ofr ly S UP W regs mem md ch v 0x21020 [] live peak cnt fail (ms_regs ms) (ms_mem ms) _ HPRE HH
      Hloc Hv8 Hra0 (Forall_nil _) Hq Hmax Hlive Hnev Hbb HJ2 HARU2).
    * exact (fsw_reg_lit _ E _ ms 1%bv 540356 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)).
    * unfold spZ at 1. rewrite (fsw_reg_off _ E _ ms 2%bv 2 0 (spZ regs - 32) HS2 ltac:(vm_compute; reflexivity) E2
        ltac:(lia)). lia.
    * rewrite (fsw_reg_atom _ regs2 _ _ ms 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl). exact R3.
    * rewrite (fsw_reg_atom _ regs2 _ _ ms 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl). exact R4.
    * rewrite (fsw_reg_atom _ regs2 _ _ ms 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl). exact R8.
    * rewrite (fsw_reg_extra _ regs2 _ _ ms 18%bv 0 HS2 ltac:(vm_compute; reflexivity)). reflexivity.
    * exact (fsw_reg_lit _ E _ ms 10%bv 135200 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)).
    * apply pjs_cs_other;
        (lazymatch goal with |- YK11.getr _ ?q = _ =>
           let n := eval vm_compute in (Z.to_nat (bv_unsigned q)) in
           rewrite (fsw_reg_atom _ regs2 _ _ ms q q n HS2 ltac:(vm_compute; reflexivity) eq_refl) end;
         apply Hcs2; pjs_lit_tac).
    * replace (spZ regs - 8) with (spZ regs - 32 + 24) by lia.
      exact (fsw_field E _ 2 (spZ regs - 32) _ _ _ _ _ 24 8%N (SOff (xatom 0) 0) (raZ regs) HR0 E2 ltac:(cbn; tauto)
        ltac:(rewrite fsw_SOff0; subst E; change (xatom 0) with (32 + 1)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
              unfold raZ; symmetry; apply Z_to_bv_bv_unsigned) ltac:(unfold raZ; apply u64_range) ltac:(cbn; lia)).
    * replace (spZ regs - 16) with (spZ regs - 32 + 16) by lia.
      exact (fsw_field E _ 2 (spZ regs - 32) _ _ _ _ _ 16 8%N (SOff (xatom 1) 0) (s0Z regs) HR0 E2 ltac:(cbn; tauto)
        ltac:(rewrite fsw_SOff0; subst E; change (xatom 1) with (32 + 2)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
              unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned) ltac:(unfold s0Z; apply u64_range) ltac:(cbn; lia)).
    * replace (spZ regs - 24) with (spZ regs - 32 + 8) by lia.
      exact (fsw_field E _ 2 (spZ regs - 32) _ _ _ _ _ 8 8%N (SOff (xatom 2) 0) (bv_unsigned (YK11.getr regs 9)) HR0 E2
        ltac:(cbn; tauto)
        ltac:(rewrite fsw_SOff0; subst E; change (xatom 2) with (32 + 3)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
              symmetry; apply Z_to_bv_bv_unsigned) ltac:(apply u64_range) ltac:(cbn; lia)).
    * replace (spZ regs - 32) with (spZ regs - 32 + 0) by lia.
      exact (fsw_field E _ 2 (spZ regs - 32) _ _ _ _ _ 0 8%N (SOff (xatom 3) 0) (bv_unsigned (YK11.getr regs 18)) HR0 E2
        ltac:(cbn; tauto)
        ltac:(rewrite fsw_SOff0; subst E; change (xatom 3) with (32 + 4)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
              symmetry; apply Z_to_bv_bv_unsigned) ltac:(apply u64_range) ltac:(cbn; lia)).
    * pose proof (fsw_field E _ 8 v _ _ _ _ _ 0 4%N (SLit 4) 4 HR3 ltac:(rewrite E8; apply wz; lia) ltac:(cbn; tauto)
        ltac:(apply bv_eq; rewrite denot_lit_U; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Hty.
      rewrite Z.add_0_r in Hty. exact Hty.
    * intros i Hi. rewrite KEEP by lia. exact (Hz2 i ltac:(lia)).
    * apply (pjs_glob_keep W mem2 (ms_mem ms)); [|exact HG2].
      intros x Hx. apply (mbyte_of_aview tfibsegs). exact (KEEPimg x Hx).
    * apply (pjs_arodata_keep W mem2 (ms_mem ms)); [exact KEEPimg | exact HRO2].
    * apply (pjs_cstr_unp ly S UP W (ms_mem ms) _ 0x21020 [] HARU2 HH); [|exact Hlit].
      intros x Hx. apply pjs_ro_img. cbn [length Z.of_nat] in Hx. lia.
    * right. left. cbv [FS_RO_STRS]. repeat (first [left; reflexivity | right]).
- (* s <> NULL: fuzz_strdup of s *)
  destruct Hscase as [[Hc _] | (_ & Hstr & Hkept & Hdj)]; [lia|].
  change (if false then pjs_ss2z else pjs_ss2n) with pjs_ss2n in HS2.
  pjs_run_to_tokU ofr pj_string_tbl_ok HS2 HJ2 HARU2 SHOK fs_Bspan 535904.
  + exact AWR.
  + pose proof (KEEPf ms HFr) as KEEP.
    assert (KEEPimg : forall x, in_img tfibsegs x ->
      aview tfibsegs (w_H W) (ms_mem ms) x = aview tfibsegs (w_H W) mem2 x).
    { intros x Hx. pose proof (fs_segs_img x Hx) as Hb. unfold aview. rewrite KEEP; [reflexivity | unfold FS_IMG_END in Hb; lia|].
      intros Hv. exact (NI x ltac:(lia) Hx). }
    pose proof (fsw_region_nth E _ _ 0 _ HS2 eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
    pose proof (fsw_region_nth E _ _ 3 _ HS2 eq_refl) as HR3. cbn [ms_mem restrict] in HR3.
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS2 eq_refl). cbn [ss_pc].
    assert (Hcsnz : Forall (fun c => c <> 0) cs) by exact (proj2 (proj1 Hstr)).
    apply (pjs_call ofr ly S UP W regs mem md ch v s cs live peak cnt fail (ms_regs ms) (ms_mem ms) _ HPRE HH
      Hloc Hv8 Hra0 Hcsnz Hq Hmax Hlive Hnev Hbb HJ2 HARU2).
    * exact (fsw_reg_lit _ E _ ms 1%bv 540356 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)).
    * unfold spZ at 1. rewrite (fsw_reg_off _ E _ ms 2%bv 2 0 (spZ regs - 32) HS2 ltac:(vm_compute; reflexivity) E2
        ltac:(lia)). lia.
    * rewrite (fsw_reg_atom _ regs2 _ _ ms 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl). exact R3.
    * rewrite (fsw_reg_atom _ regs2 _ _ ms 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl). exact R4.
    * rewrite (fsw_reg_atom _ regs2 _ _ ms 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl). exact R8.
    * rewrite (fsw_reg_extra _ regs2 _ _ ms 18%bv 0 HS2 ltac:(vm_compute; reflexivity)). reflexivity.
    * rewrite (fsw_reg_atom _ regs2 _ _ ms 10%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl). exact R9.
    * apply pjs_cs_other;
        (lazymatch goal with |- YK11.getr _ ?q = _ =>
           let n := eval vm_compute in (Z.to_nat (bv_unsigned q)) in
           rewrite (fsw_reg_atom _ regs2 _ _ ms q q n HS2 ltac:(vm_compute; reflexivity) eq_refl) end;
         apply Hcs2; pjs_lit_tac).
    * replace (spZ regs - 8) with (spZ regs - 32 + 24) by lia.
      exact (fsw_field E _ 2 (spZ regs - 32) _ _ _ _ _ 24 8%N (SOff (xatom 0) 0) (raZ regs) HR0 E2 ltac:(cbn; tauto)
        ltac:(rewrite fsw_SOff0; subst E; change (xatom 0) with (32 + 1)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
              unfold raZ; symmetry; apply Z_to_bv_bv_unsigned) ltac:(unfold raZ; apply u64_range) ltac:(cbn; lia)).
    * replace (spZ regs - 16) with (spZ regs - 32 + 16) by lia.
      exact (fsw_field E _ 2 (spZ regs - 32) _ _ _ _ _ 16 8%N (SOff (xatom 1) 0) (s0Z regs) HR0 E2 ltac:(cbn; tauto)
        ltac:(rewrite fsw_SOff0; subst E; change (xatom 1) with (32 + 2)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
              unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned) ltac:(unfold s0Z; apply u64_range) ltac:(cbn; lia)).
    * replace (spZ regs - 24) with (spZ regs - 32 + 8) by lia.
      exact (fsw_field E _ 2 (spZ regs - 32) _ _ _ _ _ 8 8%N (SOff (xatom 2) 0) (bv_unsigned (YK11.getr regs 9)) HR0 E2
        ltac:(cbn; tauto)
        ltac:(rewrite fsw_SOff0; subst E; change (xatom 2) with (32 + 3)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
              symmetry; apply Z_to_bv_bv_unsigned) ltac:(apply u64_range) ltac:(cbn; lia)).
    * replace (spZ regs - 32) with (spZ regs - 32 + 0) by lia.
      exact (fsw_field E _ 2 (spZ regs - 32) _ _ _ _ _ 0 8%N (SOff (xatom 3) 0) (bv_unsigned (YK11.getr regs 18)) HR0 E2
        ltac:(cbn; tauto)
        ltac:(rewrite fsw_SOff0; subst E; change (xatom 3) with (32 + 4)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
              symmetry; apply Z_to_bv_bv_unsigned) ltac:(apply u64_range) ltac:(cbn; lia)).
    * pose proof (fsw_field E _ 8 v _ _ _ _ _ 0 4%N (SLit 4) 4 HR3 ltac:(rewrite E8; apply wz; lia) ltac:(cbn; tauto)
        ltac:(apply bv_eq; rewrite denot_lit_U; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Hty.
      rewrite Z.add_0_r in Hty. exact Hty.
    * intros i Hi. rewrite KEEP by lia. exact (Hz2 i ltac:(lia)).
    * apply (pjs_glob_keep W mem2 (ms_mem ms)); [|exact HG2].
      intros x Hx. apply (mbyte_of_aview tfibsegs). exact (KEEPimg x Hx).
    * apply (pjs_arodata_keep W mem2 (ms_mem ms)); [exact KEEPimg | exact HRO2].
    * apply (pjs_cstr_keep W mem2 (ms_mem ms) v s cs); [| | | exact Hdj | exact Hstr].
      -- intros x Hx Hvx. unfold aview. rewrite KEEP; [reflexivity | lia | lia].
      -- intros x Hx Hv. eapply aview_keeps_vis; [exact HG | exact Hv].
      -- intros x Hx. destruct (Vx x Hx) as (Happ & _). unfold app_addr in Happ.
         unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
    * exact Hkept.
Qed.

(* ---- the resumed state after __asan_memset (0x83e8c): FSW_ret's fss_retT over the call's frame equality ---- *)
Lemma pjs_resume2_base : forall STK sp0 FP ly S U (W0 : world tfibsegs) mem md (W : world tfibsegs) memT mem2 md2
  regs regsT regs2 v gf,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md [] ly S W (unpoison U mem2) md2 0 ->
  ARU tfibsegs B ly S U W mem2 md2 ->
  aregs_preserved regsT regs2 ->
  spZ regsT = sp0 - 32 -> 32 <= STK -> alloc_ceiling + 32 <= sp0 ->
  (forall a, sp0 - 32 <= a < sp0 -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) ->
  val_mem tfibsegs (mrestrict (w_H W) memT) (sp0 - 8) 8 (raZ regs) ->
  val_mem tfibsegs (mrestrict (w_H W) memT) (sp0 - 16) 8 (s0Z regs) ->
  val_mem tfibsegs (mrestrict (w_H W) memT) (sp0 - 24) 8 (bv_unsigned (YK11.getr regs 9)) ->
  val_mem tfibsegs (mrestrict (w_H W) memT) (sp0 - 32) 8 (bv_unsigned (YK11.getr regs 18)) ->
  YK11.getr regsT 8 = w64 v ->
  4096 <= v -> v + 56 <= alloc_ceiling -> v mod 8 = 0 ->
  (forall x, v <= x < v + 56 -> ~ in_img tfibsegs x) ->
  (forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W) mem2) (v + i)) ->
  atoms_ok (Ereg regs2 (fs_extraT ++ [YK11.getr regs 1; YK11.getr regs 8; YK11.getr regs 9; YK11.getr regs 18])) gf ->
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ [YK11.getr regs 1; YK11.getr regs 8; YK11.getr regs 9; YK11.getr regs 18]))
    (fss_retT 0x83e8c 32 pjs_cs [pjs_vreg 0 4] gf)
    (restrict (w_H W) (YK11.mkst regs2 (Z_to_bv 64 0x83e8c) mem2 (YK11.seg_rom tfibsegs))).
Proof.
intros STK sp0 FP ly S U W0 mem md W memT mem2 md2 regs regsT regs2 v gf HJ HARU HP Hsp HSTK Hsp0 Hfr V1 V2 V3 V4
  R8 Hv0 Hv1 Hv8 NI Hpv Hgf.
pose proof asan_consts as (C1 & _).
set (xs := [YK11.getr regs 1; YK11.getr regs 8; YK11.getr regs 9; YK11.getr regs 18]) in *.
assert (P2 : YK11.getr regs2 2 = YK11.getr regsT 2) by exact (fsw_pres regsT regs2 2%bv HP ltac:(pjs_cs_tac)).
assert (P8 : YK11.getr regs2 8 = w64 v) by (rewrite (fsw_pres regsT regs2 8%bv HP ltac:(pjs_cs_tac)); exact R8).
assert (Hsp2 : spZ regs2 = sp0 - 32) by (unfold spZ in *; rewrite P2; exact Hsp).
assert (E2 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ xs)) 2) = sp0 - 32)
  by (rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact Hsp2).
assert (E8 : ew (Ereg regs2 (fs_extraT ++ xs)) 8 = Z_to_bv 64 v) by (rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl); exact P8).
apply (pjs_resume_rt STK sp0 FP [] ly S U W0 mem md ly S W memT mem2 md2 0 regsT regs2 32 xs pjs_cs [pjs_vreg 0 4] gf
  0x83e8c HJ HARU HP Hsp ltac:(lia) HSTK ltac:(reflexivity) Hfr).
- vm_compute. reflexivity.
- unfold pjs_cs. repeat constructor; cbn; lia.
- unfold pjs_cs. repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val tfibsegs _ _ _ 24 8%N (SOff (xatom 0) 0) (raZ regs));
      [rewrite fsw_SOff0; change (xatom 0) with (32 + 1)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
       unfold raZ; symmetry; apply Z_to_bv_bv_unsigned | unfold raZ; apply u64_range | cbn; lia
       | replace (sp0 - 32 + 24) with (sp0 - 8) by lia; exact V1].
  + apply (chunk_ok_val tfibsegs _ _ _ 16 8%N (SOff (xatom 1) 0) (s0Z regs));
      [rewrite fsw_SOff0; change (xatom 1) with (32 + 2)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
       unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned | unfold s0Z; apply u64_range | cbn; lia
       | replace (sp0 - 32 + 16) with (sp0 - 16) by lia; exact V2].
  + apply (chunk_ok_val tfibsegs _ _ _ 8 8%N (SOff (xatom 2) 0) (bv_unsigned (YK11.getr regs 9)));
      [rewrite fsw_SOff0; change (xatom 2) with (32 + 3)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
       symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia
       | replace (sp0 - 32 + 8) with (sp0 - 24) by lia; exact V3].
  + apply (chunk_ok_val tfibsegs _ _ _ 0 8%N (SOff (xatom 3) 0) (bv_unsigned (YK11.getr regs 18)));
      [rewrite fsw_SOff0; change (xatom 3) with (32 + 4)%nat; rewrite ew_Ereg_extra; cbn [nth app fs_extraT xs];
       symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia
       | replace (sp0 - 32 + 0) with (sp0 - 32) by lia; exact V4].
- constructor; [|constructor]. unfold pjs_vreg.
  exact (fsw_pj_part_okW tfibsegs _ _ 8 v v 0 4 0 4 [] ltac:(lia) ltac:(lia) Hpv ltac:(rewrite E8; apply wz; lia)
    ltac:(lia) ltac:(lia) ltac:(right; lia) (Forall_nil _)).
- apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pjs_vreg, extent_of_region.
  cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E8, (wz v) by lia.
  pose proof (pjs_disj_img v 0 4 tfib_D_GOT_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) NI ltac:(intros y Hy; apply pjs_relro_img; unfold tfib_D_GOT_asan_shadow_memory_dynamic_address in *; lia))
    as D1.
  pose proof (pjs_disj_img v 0 4 tfib_D_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) NI ltac:(intros y Hy; apply pjs_rw_img; unfold tfib_D_asan_shadow_memory_dynamic_address in *; lia))
    as D2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- exact Hgf.
Qed.
Lemma pjs_resume2 : forall STK sp0 FP ly S U (W0 : world tfibsegs) mem md (W : world tfibsegs) memT mem2 md2
  regs regsT regs2 v s,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md [] ly S W (unpoison U mem2) md2 0 ->
  ARU tfibsegs B ly S U W mem2 md2 ->
  aregs_preserved regsT regs2 ->
  spZ regsT = sp0 - 32 -> 32 <= STK -> alloc_ceiling + 32 <= sp0 ->
  (forall a, sp0 - 32 <= a < sp0 -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) ->
  val_mem tfibsegs (mrestrict (w_H W) memT) (sp0 - 8) 8 (raZ regs) ->
  val_mem tfibsegs (mrestrict (w_H W) memT) (sp0 - 16) 8 (s0Z regs) ->
  val_mem tfibsegs (mrestrict (w_H W) memT) (sp0 - 24) 8 (bv_unsigned (YK11.getr regs 9)) ->
  val_mem tfibsegs (mrestrict (w_H W) memT) (sp0 - 32) 8 (bv_unsigned (YK11.getr regs 18)) ->
  YK11.getr regsT 8 = w64 v -> YK11.getr regsT 9 = w64 s -> YK11.getr regsT 18 = Z_to_bv 64 SHADOW_OFF ->
  4096 <= v -> v + 56 <= alloc_ceiling -> v mod 8 = 0 -> 0 <= s < 2 ^ 64 ->
  (forall x, v <= x < v + 56 -> ~ in_img tfibsegs x) ->
  (forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W) mem2) (v + i)) ->
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ [YK11.getr regs 1; YK11.getr regs 8; YK11.getr regs 9; YK11.getr regs 18]))
    (if s =? 0 then pjs_ss2z else pjs_ss2n)
    (restrict (w_H W) (YK11.mkst regs2 (Z_to_bv 64 0x83e8c) mem2 (YK11.seg_rom tfibsegs))).
Proof.
intros STK sp0 FP ly S U W0 mem md W memT mem2 md2 regs regsT regs2 v s HJ HARU HP Hsp HSTK Hsp0 Hfr V1 V2 V3 V4
  R8 R9 R18 Hv0 Hv1 Hv8 Hs NI Hpv.
pose proof asan_consts as (C1 & _).
set (xs := [YK11.getr regs 1; YK11.getr regs 8; YK11.getr regs 9; YK11.getr regs 18]) in *.
assert (P8 : YK11.getr regs2 8 = w64 v) by (rewrite (fsw_pres regsT regs2 8%bv HP ltac:(pjs_cs_tac)); exact R8).
assert (P9 : YK11.getr regs2 9 = w64 s) by (rewrite (fsw_pres regsT regs2 9%bv HP ltac:(pjs_cs_tac)); exact R9).
assert (P18 : YK11.getr regs2 18 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (fsw_pres regsT regs2 18%bv HP ltac:(pjs_cs_tac)); exact R18).
assert (E8 : ew (Ereg regs2 (fs_extraT ++ xs)) 8 = Z_to_bv 64 v) by (rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl); exact P8).
assert (AV : afact_ok (Ereg regs2 (fs_extraT ++ xs)) 8%nat (mkAF 4096 PJS_CEIL 3)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E8, (wz v) by lia.
  change (2 ^ 3) with 8. unfold PJS_CEIL in *. split; [lia | split; [exact Hv8 | lia]]. }
destruct (Z.eqb_spec s 0) as [Es | Es].
- subst s. change (if 0 =? 0 then pjs_ss2z else pjs_ss2n) with pjs_ss2z.
  pose proof (pjs_resume2_base STK sp0 FP ly S U W0 mem md W memT mem2 md2 regs regsT regs2 v [pjs_vfact] HJ HARU HP Hsp
    HSTK Hsp0 Hfr V1 V2 V3 V4 R8 Hv0 Hv1 Hv8 NI Hpv ltac:(unfold pjs_vfact; cbn [atoms_ok]; split; [exact AV | exact I]))
    as HR.
  unfold pjs_ss2z, pjs_pin. cbv zeta. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
  apply (st_ok_regs tfibsegs _ _ _ _ HR).
  intros q. destruct (decide (q = 9%bv)) as [-> | Hq9].
  + rewrite sr_get_set_same by reflexivity.
    lazymatch goal with |- _ = sv_denot _ (sr_get ?R 9%bv) =>
      let t := eval vm_compute in (sr_get R 9%bv) in change (sr_get R 9%bv) with t end.
    rewrite fsw_SOff0, (ew_Ereg_nat regs2 _ 9 9%bv eq_refl), P9. reflexivity.
  + rewrite sr_get_set_other by exact Hq9.
    destruct (decide (q = 18%bv)) as [-> | Hq18].
    * rewrite sr_get_set_same by reflexivity.
      lazymatch goal with |- _ = sv_denot _ (sr_get ?R 18%bv) =>
        let t := eval vm_compute in (sr_get R 18%bv) in change (sr_get R 18%bv) with t end.
      rewrite !fsw_SOff0. change 32%nat with (32 + 0)%nat at 1. rewrite ew_Ereg_extra.
      rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl), P18. reflexivity.
    * rewrite sr_get_set_other by exact Hq18. reflexivity.
- change (if s =? 0 then pjs_ss2z else pjs_ss2n) with pjs_ss2n.
  assert (AS : afact_ok (Ereg regs2 (fs_extraT ++ xs)) 9%nat (mkAF 1 (2 ^ 64 - 1) 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl), P9. unfold w64.
    rewrite (wz s) by lia. rewrite Z.pow_0_r. split; [lia | split; [apply Z.mod_1_r | lia]]. }
  pose proof (pjs_resume2_base STK sp0 FP ly S U W0 mem md W memT mem2 md2 regs regsT regs2 v
    [pjs_vfact; (9%nat, mkAF 1 (2 ^ 64 - 1) 0)] HJ HARU HP Hsp HSTK Hsp0 Hfr V1 V2 V3 V4 R8 Hv0 Hv1 Hv8 NI Hpv
    ltac:(unfold pjs_vfact; cbn [atoms_ok]; split; [exact AV | split; [exact AS | exact I]])) as HR.
  unfold pjs_ss2n, pjs_pin. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
  apply (st_ok_regs tfibsegs _ _ _ _ HR).
  intros q. destruct (decide (q = 18%bv)) as [-> | Hq18].
  + rewrite sr_get_set_same by reflexivity.
    lazymatch goal with |- _ = sv_denot _ (sr_get ?R 18%bv) =>
      let t := eval vm_compute in (sr_get R 18%bv) in change (sr_get R 18%bv) with t end.
    rewrite !fsw_SOff0. change 32%nat with (32 + 0)%nat at 1. rewrite ew_Ereg_extra.
    rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl), P18. reflexivity.
  + rewrite sr_get_set_other by exact Hq18. reflexivity.
Qed.

(* ---- the walk, for either placement of v (ofr = false: a heap block past its head; ofr = true: a fake frame) ---- *)
Lemma pjs_walk : forall (ofr : bool)
  ly S U (W : world tfibsegs) regs mem md ch v s (cs : list Z) live peak cnt fail,
  fpreU tfibsegs B STK_pj_string ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  YK11.getr regs 10 = w64 v -> YK11.getr regs 11 = w64 s ->
  pjs_loc ofr ly S v -> v mod 8 = 0 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF v 56 ->
  (forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W) mem) (v + i)) ->
  (s = 0 /\ cs = [] \/ s <> 0 /\ cstr_ok tfibsegs W mem s cs /\ cstr_kept B ly S U s cs /\
     (s + (Z.of_nat (length cs) + 1) <= v \/ v + 56 <= s)) ->
  fs_glob tfibsegs W mem live peak cnt fail -> quiet cnt fail 1 ->
  Z.of_nat (length cs) + 1 + HEAD < MALLOC_MAX -> live + (Z.of_nat (length cs) + 1) < 2 ^ 64 ->
  st_nev S + EV_pj_string <= EV_MAX -> blocks_bytes S + (Z.of_nat (length cs) + 1 + HEAD) <= LIVE_MAX ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_pj_string regs mem md)
    (fun W' c' => exists a,
       fpostU tfibsegs B STK_pj_string (spZ regs) ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U W mem md EV_pj_string
         (U ++ [(a - HEAD, HEAD)])
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10 = w64 0 /\ 4096 + HEAD <= a /\
            ablocks B ly' S' = ablocks B ly S ++ [(a - HEAD, Z.of_nat (length cs) + 1 + HEAD)] /\
            rtree tfibsegs B ly' S' W' mem' v (PjTree.JStr cs) [(a, Z.of_nat (length cs) + 1)] /\
            pobj tfibsegs B ly' S' W' mem' v /\
            fs_glob tfibsegs W' mem' (live + (Z.of_nat (length cs) + 1)) (Z.max peak (live + (Z.of_nat (length cs) + 1)))
              (cnt + 1) fail) W' c').
Proof.
intros ofr ly S U W regs mem md ch v s cs live peak cnt fail HPRE HH H10 H11 Hloc Hv8 Hra0 HWR0 Hscase HG Hq Hmax
  Hlive Hnev Hbb.
pose proof HSS as [Hgot Hcell].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (FS : 32 + 4096 <= STK_pj_string) by (vm_compute; intros Hc; discriminate Hc).
pose proof HPRE as [HAPU HRO].
pose proof (fsw_sp B _ ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof HAPU as (HAP & HOK & HPOI).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HAPU) as HARU.
destruct (pjs_loc_facts ofr ly S W _ md v HAR Hloc) as (V0 & V1 & Vam & Vx).
assert (NI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x) by (intros x Hx; exact (proj1 (proj2 (Vx x Hx)))).
assert (Hsr : 0 <= s < 2 ^ 64).
{ destruct Hscase as [[-> _] | (_ & ((_ & _) & Hs4096 & Hsceil & _) & _)]; lia. }
assert (HFPv : forall y, v <= y < v + 56 -> inFP ([(v, v + 56)] ++ FS_PSTAT_FP) y)
  by (intros y Hy; exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]).
(* ---- the entry state and the journal ---- *)
pose proof (fsw_entryT B STK_pj_string 32 ly S U W regs mem md ch A_pj_string Hgot Hcell HAPU ltac:(lia)
  ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_pj_string ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W regs (unpoison U mem) md ch HAP)
  as HJ.
assert (Usp : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
unfold YG0d.cfg_at. change (w64 A_pj_string) with (Z_to_bv 64 A_pj_string).
(* ---- run 1: 0x83e58 .. `jal __asan_memset` 0x83e88, stopping at the callee's entry 0x5222c ---- *)
fsw_aj_run_toU pj_string_tbl_ok HS HJ HARU PC_memset.
{ cbn [ss_mem fss0T fsT_regions].
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact Usp | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HS into HSc.
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ intros x Hx. apply HF. rewrite unsigned_lit_small by lia. intros (r & Hin & Hr).
  cbn [ss_mem fss0T fsT_regions In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]];
    unfold fstk, fs_got_region, fs_bcell_region in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    try rewrite Usp in Hr; lia. }
pose proof (fsw_reg_lit _ _ _ ms 1%bv 0x83e8c HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fsw_reg_off _ _ _ ms 2%bv 2 (-32) (spZ regs) HSc ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HSc ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HSc ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 8%bv 10%bv 10 HSc ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 9%bv 11%bv 11 HSc ltac:(vm_compute; reflexivity) eq_refl) as R9.
pose proof (fsw_reg_extra _ regs fs_extraT _ ms 18%bv 0 HSc ltac:(vm_compute; reflexivity)) as R18.
cbn [nth fs_extraT] in R18.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 10%bv 10%bv 10 HSc ltac:(vm_compute; reflexivity) eq_refl) as R10.
rewrite H10 in R8, R10. rewrite H11 in R9.
pose proof (fsw_reg_lit _ _ _ ms 11%bv 0 HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R11.
pose proof (fsw_reg_lit _ _ _ ms 12%bv 56 HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R12.
assert (HspC : spZ (ms_regs ms) = spZ regs - 32) by (unfold spZ at 1; rewrite R2; lia).
(* the four saved registers in the frame *)
pose proof (fsw_region_nth _ _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (fsw_field (Ereg regs fs_extraT) _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HR0 Usp
  ltac:(cbn; tauto)
  ltac:(rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 1 1%bv eq_refl); unfold raZ; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(unfold raZ; apply u64_range) ltac:(cbn; lia)) as Vra.
pose proof (fsw_field (Ereg regs fs_extraT) _ 2 (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) (s0Z regs) HR0 Usp
  ltac:(cbn; tauto)
  ltac:(rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 8 8%bv eq_refl); unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(unfold s0Z; apply u64_range) ltac:(cbn; lia)) as Vs0.
pose proof (fsw_field (Ereg regs fs_extraT) _ 2 (spZ regs) _ _ _ _ _ (-24) 8%N (SOff 9 0)
  (bv_unsigned (YK11.getr regs 9)) HR0 Usp
  ltac:(cbn; tauto)
  ltac:(rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 9 9%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(apply u64_range) ltac:(cbn; lia)) as Vs1.
pose proof (fsw_field (Ereg regs fs_extraT) _ 2 (spZ regs) _ _ _ _ _ (-32) 8%N (SOff 18 0)
  (bv_unsigned (YK11.getr regs 18)) HR0 Usp
  ltac:(cbn; tauto)
  ltac:(rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 18 18%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(apply u64_range) ltac:(cbn; lia)) as Vs2.
clear HR0.
(* ---- the call of __asan_memset (v, 0, 56) ---- *)
assert (HDEST : dest_ok tfibsegs B ly S W (ms_regs ms) (ms_mem ms) v 56).
{ intros a Ha. split; [|split].
  - replace a with (v + (a - v)) by lia.
    apply (fsw_writable_below (w_H W) mem (ms_mem ms) (v + (a - v)) SB1); [lia|]. apply HWR0. lia.
  - exact (proj1 (proj2 (proj2 (Vx a Ha)))).
  - rewrite HspC, Hes. lia. }
pose proof (fsw_range_addressable_below (w_H W) mem (ms_mem ms) v 56 SB1 ltac:(lia) V1 Hra0) as HRAD.
pose proof (pjs_hull ofr ly S U W (ms_mem ms) _ v HARU Hloc) as HHULL.
pose proof (pjs_perm_v ofr STK_pj_string (spZ regs) _ ly S ly S [] v Hloc (fun p n H => H) (fun _ _ => eq_refl) HFPv) as HPERM.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HSc eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ exact (pjs_memset_at ofr STK_pj_string (spZ regs) ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md []
    ly S U W (ms_mem ms) _ 0 (ms_regs ms) (-32) v HJ HARU ltac:(lia) eq_refl ltac:(lia) ltac:(rewrite Hes; lia)
    ltac:(rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity)
    ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp) R10 R11 R12 ltac:(lia) ltac:(lia) Vam HDEST HRAD HHULL
    HPERM). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & Hz2 & Hfr2 & Hpr2).
rewrite R1.
(* ---- back at 0x83e8c: the resumed state ---- *)
pose proof HJ2 as (HAR2 & _).
assert (Hpv2 : forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W) mem2) (v + i)).
{ intros i Hi. apply (apresent_writable tfibsegs). destruct (pjs_loc_facts ofr ly S W _ md2 v HAR2 Hloc) as (_ & _ & _ & Vx2).
  destruct (Vx2 (v + i) ltac:(lia)) as (Happ & _ & _ & [Hh [b Hb]]). split; [exact Hh|]. exists b.
  rewrite <- (pjs_unpoison_app ly S U W mem2 md2 (v + i) HARU2 ltac:(lia)); [exact Hb|].
  unfold app_addr in Happ. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
assert (KS : forall a, spZ regs - 32 <= a < spZ regs ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem ms) a)
  by (intros a Ha; apply Hfr2; [lia | lia | rewrite HspC, Hes; lia]).
pose proof (pjs_resume2 STK_pj_string (spZ regs) _ ly S U W (unpoison U mem) md W (ms_mem ms) mem2 md2 regs (ms_regs ms)
  regs2 v s HJ2 HARU2 HP2 HspC ltac:(lia) ltac:(lia) KS
  ltac:(replace (spZ regs - 8) with (spZ regs + -8) by lia; exact Vra)
  ltac:(replace (spZ regs - 16) with (spZ regs + -16) by lia; exact Vs0)
  ltac:(replace (spZ regs - 24) with (spZ regs + -24) by lia; exact Vs1)
  ltac:(replace (spZ regs - 32) with (spZ regs + -32) by lia; exact Vs2)
  R8 R9 R18 V0 V1 Hv8 Hsr NI Hpv2) as HS2.
assert (P2 : YK11.getr regs2 2 = YK11.getr (ms_regs ms) 2) by exact (fsw_pres _ _ 2%bv HP2 ltac:(pjs_cs_tac)).
assert (Hsp2 : spZ regs2 = spZ regs - 32) by (unfold spZ in *; rewrite P2; exact HspC).
(* the image bytes kept across the run and the call *)
assert (KIMG : forall x, in_img tfibsegs x -> aview tfibsegs (w_H W) mem2 x = aview tfibsegs (w_H W) mem x).
{ intros x Hx. pose proof (fs_segs_img x Hx) as Hb. unfold FS_IMG_END in Hb.
  rewrite Hfr2; [| lia | intros Hv; exact (NI x Hv Hx) | rewrite HspC, Hes; lia].
  apply (aview_below (w_H W) mem (ms_mem ms) alloc_ceiling x SB1). lia. }
apply (pjs_seg2 ofr ly S U W regs mem md ch v s cs live peak cnt fail regs2 mem2 md2 HPRE HH Hloc Hv8 Hra0).
- destruct Hscase as [Hz | (Hs0 & Hstr & Hkept & Hdj)]; [left; exact Hz | right].
  split; [exact Hs0|]. split; [|split; [exact Hkept | exact Hdj]].
  assert (APP : forall x, v <= x < v + 56 -> x < kLowShadowBeg \/ kHighMemBeg <= x).
  { intros x Hx. destruct (Vx x Hx) as (Happ & _). unfold app_addr in Happ.
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  apply (pjs_cstr_keep W (ms_mem ms) mem2 v s cs); [| | exact APP | exact Hdj |].
  + intros x Hx Hvx. apply Hfr2; [lia | exact Hvx | rewrite HspC, Hes; lia].
  + intros x Hx _. replace x with (v + (x - v)) by lia. rewrite (Hz2 (x - v)) by lia. discriminate.
  + apply (pjs_cstr_keep W mem (ms_mem ms) v s cs); [| | exact APP | exact Hdj | exact Hstr].
    * intros x Hx _. exact (aview_below (w_H W) mem (ms_mem ms) alloc_ceiling x SB1 Hx).
    * intros x Hx Hv. rewrite (aview_below (w_H W) mem (ms_mem ms) alloc_ceiling x SB1) by lia. exact Hv.
- exact Hq.
- exact Hmax.
- exact Hlive.
- exact Hnev.
- exact Hbb.
- exact HJ2.
- exact HARU2.
- exact HS2.
- apply (pjs_glob_keep W mem mem2); [|exact HG].
  intros x Hx. apply (mbyte_of_aview tfibsegs). exact (KIMG x Hx).
- apply (pjs_arodata_keep W mem mem2); [exact KIMG | exact HRO].
- intros i Hi. pose proof (Hz2 i Hi) as Hzi. unfold aview in Hzi.
  destruct (mbyte tfibsegs (mrestrict (w_H W) mem2) (v + i)) as [b|]; [|discriminate Hzi].
  cbn in Hzi. injection Hzi as Hb0. f_equal. apply bv_eq. rewrite Hb0. reflexivity.
- exact Hsp2.
- rewrite (fsw_pres _ _ 8%bv HP2 ltac:(pjs_cs_tac)). exact R8.
- rewrite (fsw_pres _ _ 9%bv HP2 ltac:(pjs_cs_tac)). exact R9.
- rewrite (fsw_pres _ _ 3%bv HP2 ltac:(pjs_cs_tac)), R3. exact Hgp.
- rewrite (fsw_pres _ _ 4%bv HP2 ltac:(pjs_cs_tac)), R4. exact Htp.
- apply pjs_cs_other;
    (lazymatch goal with |- YK11.getr _ ?q = _ =>
       let n := eval vm_compute in (Z.to_nat (bv_unsigned q)) in
       rewrite (fsw_pres (ms_regs ms) regs2 q HP2 ltac:(pjs_lit_tac));
       exact (fsw_reg_atom _ regs fs_extraT _ ms q q n HSc ltac:(vm_compute; reflexivity) eq_refl) end).
Qed.

(* ---- pj_string_spec: pobj's two arms ---- *)
Theorem pj_string_holds : @pj_string_spec fx rc SK tfibsegs B.
Proof.
intros ly S U W regs mem md ch v s cs live peak cnt fail. cbv zeta.
intros HPRE HH H10 H11 HPO _ Hscase HG Hq Hmax Hlive Hnev Hbb.
pose proof HPO as [HPL HWR].
destruct HPL as [((cid & pos & Hin & Hc & Hal & H1 & H2) & Hv8 & Hra0) | ((b & m & Hin & H1 & H2) & Hv8 & Hra0)].
- apply (pjs_walk true ly S U W regs mem md ch v s cs live peak cnt fail HPRE HH H10 H11);
    try assumption.
  cbn [pjs_loc]. exists cid, pos. split; [exact Hin | split; [exact Hc | split; [exact H1 | exact H2]]].
- apply (pjs_walk false ly S U W regs mem md ch v s cs live peak cnt fail
    HPRE HH H10 H11); try assumption.
  cbn [pjs_loc]. exists b, m. split; [exact Hin | split; [exact H1 | exact H2]].
Qed.

End W.
