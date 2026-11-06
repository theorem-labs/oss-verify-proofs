(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: shared helpers of the MATCH hops of the IMAGE-B walk of fuzz_reply's
   relay_remove (lib/B/W_rr_match_cx.v; hop files W_rr_m_drain.v, W_rr_m_ge.v, W_rr_m_free.v, W_rr_m_cpy.v).
   Proves no function (kind: segment-lemma helpers).  A hop that needs a helper another hop also needs adds it here
   rather than copy it.

   Where each part comes from:
   - rr_zall_nth, rr_zpw_nth, rr_writable2, rr_nG_DR, rr_capsrc_nerr, rr_img_kept: the image-A twin's kit
     (a working branch 30748eb0198 lib/A/W_rr_m_kit.v), verbatim but the import paths.
   - rm_eb_len, rm_concat_len, rm_nth_le_bytes, rm_garr8_le, rm_concat_split: the B scan's rrs_ lemmas
     (a working branch's lib/B/W_rr_scan.v), verbatim.
   - rm_gx_callS, rm_ajgx_keep_high, rm_ajgx_keep_img, rm_ajgx_ly_top, rm_apk_trans, rm_ablocks_nodup,
     rm_aout_facts, rm_aout_fp_cases: lib/B/W_gesture_end.v gx_callS / ajgx_keep_high / ajgx_keep_img / ajgx_ly_top /
     apk_trans / ablocks_nodup / aout_facts / aout_fp_cases, verbatim (copied so the hops need not build that walk).
   - rm_pads, rm_tpre_len, rm_tpost_len: lib/A/W_rr_m_ge.v rgl_pads / rgl_tpre_len / rgl_tpost_len.
   - rr_achain_fd, rr_chain_pre_fd: NEW for image B.  B's relay_remove keeps fd in s0 (`mv s0,a0` at 0x8421c), so at
     every call of the walk s0 = fd < 2^31 < alloc_ceiling and the frame-pointer chain the callee's contract asks for
     is the empty one (YCbq.v achain_low); image A's walk kept the entry sp in s0 and pushed its frame.
   - rr_live_call: the A twin's, less the fake frame (image B's RLIVE owns no frame).
   - rm_tbl_rel: NEW: RRG's / RRF's / RRC's rmtbl at slot i, from arelay_at (the table as at the entry). *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (lane RRX, the image-A twin a Theorem Labs lane f4cd818e98d
   lib/A/W_rr_m_kit.v): the helpers over ARx, in place (Section c is W_relay_remove_cx.v's generic block): the call
   and journal helpers are lib/B/W_gesture_end.v's generic gx_callS / ajgx_keep_high / ajgx_keep_img (an image byte
   is kept when it is also off PST) / ablocks_nodup / ajgx_ly_top over ajournal_gx_x, verbatim but AJGX unfolded;
   rr_img_kept takes the PST premise; rr_live_call is over RLIVE's ajournal_gx_x at RR_STK_x with the callee's stack
   up to DRAIN_STK_x, rom_view by ajournal_gx_rom_view_x (PSTR) and g_lock / g_wake[1] off PST by PSTG; rm_tbl_rel at
   an ARx state (alx_blocks). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame W_wake_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x W_wake_c_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
(* route R (the Section wR below): SRrG, and the R contract texts of drain / gestures_end (a Theorem Labs lane) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_relayB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_remove_cx W_rr_match_cx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* pairwise-apart ranges (YA0q.v zpairwise_disjoint): any two of them *)
Lemma rr_zall_nth : forall a l j, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l (0, 0)).
Proof.
intros a l. induction l as [|b l IH]; intros j H Hj; cbn [length] in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.
Lemma rr_zpw_nth : forall l i j, zpairwise_disjoint l -> (i < j < length l)%nat ->
  zdisj (nth i l (0, 0)) (nth j l (0, 0)).
Proof.
induction l as [|a l IH]; intros i j H Hij; cbn [length] in Hij; [lia|].
destruct H as [H1 H2]. destruct i as [|i]; destruct j as [|j]; [lia | | lia |].
- cbn [nth]. apply rr_zall_nth; [exact H1 | lia].
- cbn [nth]. apply IH; [exact H2 | lia].
Qed.

(* ------------------------------------------------------------------ byte lists (the B scan's rrs_ lemmas) *)
Lemma rm_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma rm_concat_split : forall {X : Type} (f : X -> list byte) (l : list X) (d : X) (i : nat),
  (i < length l)%nat ->
  concat (map f l) = concat (map f (firstn i l)) ++ f (nth i l d) ++ concat (map f (skipn (S i) l)).
Proof.
  intros X f l d. induction l as [|x l IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [firstn skipn nth map concat].
  - reflexivity.
  - rewrite (IH i ltac:(cbn [length] in Hi; lia)) at 1. cbn [map concat]. rewrite app_assoc. reflexivity.
Qed.
Lemma rm_eb_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
intros e P1 P2. unfold entry_bytes.
rewrite !length_app, !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8, P1, P2. reflexivity.
Qed.
Lemma rm_concat_len : forall l, Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) l ->
  length (concat (map entry_bytes l)) = (56 * length l)%nat.
Proof.
induction l as [|e l IH]; intros HF; [reflexivity|].
apply Forall_cons_iff in HF as [[P1 P2] HF]. cbn [map concat length]. rewrite length_app, (rm_eb_len e P1 P2), (IH HF). lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Lemma rm_garr8_le : forall m a n z, garr8 SEGS m a (bzs (Z_to_le_bytes n z)) -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  val_mem SEGS m a n z.
Proof.
intros m a n z Hg Hz k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n z)))%nat) by (unfold bzs; rewrite length_map, length_Z_to_le_bytes; exact Hk).
destruct (Hg k Hl) as [Hv _]. specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
rewrite Hv. apply f_equal.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite map_nth, rm_nth_le_bytes by exact Hk. unfold bz.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.

(* writability across two worlds: a writable byte stays writable when its presence is kept (W_frame.v
   writable_kept, with the hidden set changing) *)
Lemma rr_writable2 : forall H H2 (m m2 : word -> option byte) a,
  (apresent H m a -> apresent H2 m2 a) -> writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H2 m2) a.
Proof.
intros H H2 m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; intros Hw.
- destruct (H2 (Z_to_bv 64 a)); [exact Hw|]. destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  + destruct (Hp (conj EH (ex_intro _ b Em))) as [EH2 [b2 Hb2]]. rewrite EH2, Hb2. discriminate.
  + destruct (H2 (Z_to_bv 64 a)); [exact Hw|]. destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (one table for free and free(NULL); image B's closed singleton row) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'). ---- *)
(* the generic relation's laws and its empty head set (CONVERSION.md (sha256 1015972e02a9; internal record) 1.) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (image B's top, W_wake_x.v's form), a live block's
   size non-negative (BLKN, W_kit_x.v), the owned-low law OWNLOW, the model invariant WFx with its law WFL and the two
   facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC); ASMP / ASF / FFL are the class-0
   fake frame's laws (image B's relay_remove takes none: wake does, W_wake_x.v) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis HG : gx_ok SEGS B (G_RR B RG).
(* the register images of g_nsrc / g_src (the abstract placement does not fix them against the objects; PB_fr on
   AsanUbsan discharges both by vm_compute, as the image-A twin's HH59 / HH60) *)
Hypothesis HH53 : VAL (A_HI 53) = rg_nsrc RG + RR_HI_NSRC.
Hypothesis HH54 : VAL (A_HI 54) = rg_src RG + RR_HI_SRC.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are unowned image bytes (the image-A twin's HRGP / HRGI, verbatim) *)
Hypothesis HRGP : zpairwise_disjoint
[(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
 (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
 (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
 (as_errno B, as_errno B + 4)].
Hypothesis HRGI : forall a,
(rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* no read-only image byte is owned by the runtime: rom_view survives the calls (W_journal_x.v ajournal_gx_rom_view_x) *)
Hypothesis HROMO : rom_out SEGS B (G_RR B RG).
Hypothesis MLAW : ameter_laws MT.
(* the meter does not see a change of the fake-frame state alone (KF-COUNT, the image-A twin's MO_FR): sound, since
   the seat's post state is a set_fs (Reusable/YG01.v stack_malloc_post) and the release is stack_free_state, a set_fs;
   image B meets it at wake's return (W_wake_c_x.v wk_post_x's seat fact S' = set_fs f S) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the runtime entries relay_remove calls, at their SIGMA pcs (image B calls free's interceptor directly, WS_free) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy).
(* the program functions relay_remove calls: drain, gestures_end (the kit's _x specs) and wake (W_wake_c_x.v) *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x8435c with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* B only: wake, tail-called at 0x843e8 (image A inlines it); W_relay_remove.v builds it by W_wake_x.v pb_wake_x *)
Hypothesis WAKE : wk_spec_x B PST ARx RG (BASE + AF_fr_wake).
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* The program statics PST hold no byte the walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x) and no byte of the relay's / output's cells or
   errno (rr_gcells, HRGP's list).  At PST := [] both hold trivially (the image-A twin's PSTR / PSTG, verbatim). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, Exists (fun r => fst r <= a < snd r) (rr_gcells B RG) -> ~ Exists (in_zr a) PST.

(* ------------------------------------------------------------------ lib/B/W_gesture_end.v's call helpers over ARx *)
(* A call to a program function inside a walk (W_gesture_end.v gx_callS, AJGX unfolded): the callee's contract is
   applied at its entry (its afn_pre_x from the caller's journal), and its journal is composed into the caller's
   (W_journal_x.v ajournal_gx_sub_x); o = 0 is a tail call. *)
Lemma rm_gx_callS : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
gx_ok SEGS B G ->
ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK1 (spZ regsc) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros G W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 K
HGx HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee.
  destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
  rewrite !Z.add_0_r in HJi.
  eapply (afn_pre_x_at SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memc mdc k regsc STK1 o ch1 HJi); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [reflexivity|].
rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own).
eapply (ajournal_gx_sub_x SEGS B PST ARx LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | lia | | exact HGx | exact HF].
intros a (r & Hr & _). destruct Hr.
Qed.
(* A callee's journal keeps every byte above alloc_ceiling outside its window (G lies in the image). *)
Lemma rm_ajgx_keep_high : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
gx_ok SEGS B G ->
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
pose proof asan_consts as (C1 & _).
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
pose proof (inG_low SEGS B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* A journal keeps the image bytes outside G, the allocator's statics, errno and the program statics PST. *)
Lemma rm_ajgx_keep_img : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a -> ~ inG G a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hpst Hf Hg.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hpst Hf).
pose proof (pa_segs_low a Hi) as HL.
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
(* The live blocks are pairwise distinct (their extents are pairwise disjoint and non-empty). *)
Lemma rm_ablocks_nodup : forall ly S Hp W mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp W mem md HAR.
assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
{ apply Forall_forall. intros [p n] Hin. pose proof (BLKN ly S Hp W mem md p n HAR Hin) as Hn.
  cbn [snd]. apply req_size_pos. lia. }
destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hpw _]. apply pairwise_app_l in Hpw as [Hpw _].
revert Hpos Hpw. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hpw; [constructor|].
inversion Hpos as [|b0 l0 Hb Hl]; subst.
cbn [map pairwise] in Hpw. destruct Hpw as [Hf Hpw]. constructor; [|exact (IH Hl Hpw)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
(* A journal keeps the top of the stack layout. *)
Lemma rm_ajgx_ly_top : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ly_top ly' = ly_top ly.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET.
Qed.
(* apres_kept (W_contract.v) composes. *)
Lemma rm_apk_trans : forall W1 (m1 : word -> option byte) W2 m2 W3 m3,
apres_kept B W1 m1 W2 m2 -> apres_kept B W2 m2 W3 m3 -> apres_kept B W1 m1 W3 m3.
Proof. intros W1 m1 W2 m2 W3 m3 H1 H2 a Hi Ho He Hp. exact (H2 a Hi Ho He (H1 a Hi Ho He Hp)). Qed.
Lemma rm_aout_fp_cases : forall cap out r, In r (aout_fp B RG cap out) -> In r (aout_fp B RG 0 0) \/ (cap <> 0 /\ r = (out, out + cap)).
Proof.
intros cap out r Hr. unfold aout_fp in Hr |- *. cbn [Z.eqb] in *.
do 9 (destruct Hr as [Hr | Hr]; [left; subst r; cbn; tauto|]).
destruct (Z.eqb_spec cap 0); [destruct Hr | destruct Hr as [<- | []]; right; split; [exact n | reflexivity]].
Qed.
Lemma rm_aout_facts : forall ly S W mem c O mx no cap out, aout_at B RG ly S W mem c O mx no cap out ->
0 <= mx <= 255 /\ Z.of_nat (length O) = no /\
((cap = 0 /\ out = 0 /\ no = 0) \/ (0 < cap /\ no <= cap /\ In (out, cap) (ablocks B ly S))).
Proof.
intros ly S W mem c O mx no cap out
(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmx & Hno & Hd).
split; [exact Hmx|]. split; [exact Hno|].
destruct Hd as [Hd | (H1 & H2 & H3 & _)]; [left; exact Hd | right; split; [exact H1 | split; [exact H2 | exact H3]]].
Qed.

(* ------------------------------------------------------------------ the frame-pointer chain at the walk's calls *)
(* image B's relay_remove keeps fd in s0: at every call s0 = fd, 0 <= fd < 2^31 < alloc_ceiling, so the chain a
   callee's contract asks for is empty (YCbq.v achain_low) *)
Lemma rr_achain_fd : forall cx ly rd sp, RBASE B ARx MT RP MMAX RG cx -> 0 <= rxFD cx ->
  achain ly rd sp (rxFD cx) [].
Proof.
intros cx ly rd sp HB HFD. apply achain_low.
pose proof HB as (_ & _ & _ & _ & _ & HFDr & _). pose proof ASAN_CEIL_range as (C1 & _). unfold ASAN_CEIL in C1. lia.
Qed.
Lemma rr_s0Z_fd : forall cx (regsT : bvmap 5 word), RBASE B ARx MT RP MMAX RG cx -> 0 <= rxFD cx ->
  getr regsT 8 = w64 (rxFD cx) -> s0Z regsT = rxFD cx.
Proof.
intros cx regsT HB HFD H8. pose proof HB as (_ & _ & _ & _ & _ & HFDr & _).
unfold s0Z. rewrite H8. unfold w64. apply unsigned_lit_small. lia.
Qed.
(* the same, as a runtime call site's chain_pre (free 0x8435c, __asan_memcpy 0x843bc) *)
Lemma rr_chain_pre_fd : forall cx ly rd (regsT : bvmap 5 word), RBASE B ARx MT RP MMAX RG cx -> 0 <= rxFD cx ->
  alloc_ceiling <= spZ regsT -> getr regsT 8 = w64 (rxFD cx) -> 4096 <= raZ regsT ->
  chain_pre ly rd regsT [].
Proof.
intros cx ly rd regsT HB HFD Hsp H8 Hra.
apply (achain_chain_pre ly rd (spZ regsT) (rxFD cx) [] regsT); [exact (rr_achain_fd cx ly rd _ HB HFD) | lia | | exact Hra].
exact (rr_s0Z_fd cx regsT HB HFD H8).
Qed.

(* ------------------------------------------------------------------ the globals drain's G leaves alone *)
(* g_lock, g_src, g_nsrc, g_capsrc and g_wake[1] are none of G_DR's cells (HRGP's pairs) *)
Ltac rr_pair i j P :=
  pose proof (rr_zpw_nth _ i j HRGP) as P; specialize (P ltac:(cbn [length]; lia));
  cbn [nth] in P; unfold zdisj in P; cbn [fst snd] in P.
Lemma rr_nG_DR : forall a,
  (rg_lock RG <= a < rg_lock RG + 12 \/ rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
   rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_wake RG + 4 <= a < rg_wake RG + 8) -> ~ inG (G_DR B RG) a.
Proof.
intros a Ha HGa. unfold G_DR, G_SL, inG in HGa. rewrite !Exists_cons, Exists_nil in HGa. unfold in_zr in HGa.
cbn [fst snd] in HGa.
destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
- rr_pair 0%nat 1%nat P1. rr_pair 0%nat 6%nat P2. rr_pair 0%nat 7%nat P3. rr_pair 0%nat 8%nat P4.
  rr_pair 0%nat 10%nat P5. rr_pair 0%nat 12%nat P6. rr_pair 0%nat 14%nat P7.
  clear HRGP. destruct HGa as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; lia.
- rr_pair 1%nat 2%nat P1. rr_pair 2%nat 6%nat P2. rr_pair 2%nat 7%nat P3. rr_pair 2%nat 8%nat P4.
  rr_pair 2%nat 10%nat P5. rr_pair 2%nat 12%nat P6. rr_pair 2%nat 14%nat P7.
  clear HRGP. destruct HGa as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; lia.
- rr_pair 1%nat 3%nat P1. rr_pair 3%nat 6%nat P2. rr_pair 3%nat 7%nat P3. rr_pair 3%nat 8%nat P4.
  rr_pair 3%nat 10%nat P5. rr_pair 3%nat 12%nat P6. rr_pair 3%nat 14%nat P7.
  clear HRGP. destruct HGa as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; lia.
- rr_pair 1%nat 4%nat P1. rr_pair 4%nat 6%nat P2. rr_pair 4%nat 7%nat P3. rr_pair 4%nat 8%nat P4.
  rr_pair 4%nat 10%nat P5. rr_pair 4%nat 12%nat P6. rr_pair 4%nat 14%nat P7.
  clear HRGP. destruct HGa as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; lia.
- rr_pair 1%nat 13%nat P1. rr_pair 6%nat 13%nat P2. rr_pair 7%nat 13%nat P3. rr_pair 8%nat 13%nat P4.
  rr_pair 10%nat 13%nat P5. rr_pair 12%nat 13%nat P6. rr_pair 13%nat 14%nat P7.
  clear HRGP. destruct HGa as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; lia.
Qed.
(* g_capsrc is not errno (HRGP's pair 4 / 14) *)
Lemma rr_capsrc_nerr : forall a, rg_capsrc RG <= a < rg_capsrc RG + 4 -> ~ (as_errno B <= a < as_errno B + 4).
Proof. intros a Ha. rr_pair 4%nat 14%nat P. clear HRGP. lia. Qed.

(* ------------------------------------------------------------------ what a callee's journal keeps *)
(* an image byte outside the callee's G (inside G_DR), the allocator's statics, errno and the program statics PST *)
Lemma rr_img_kept : forall Gc STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a,
  (forall x, inG Gc x -> inG (G_DR B RG) x) ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx Gc 0 [] STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  Forall (fun r => 0 < fst r) FP -> apres_kept B W mem W' mem' ->
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_DR B RG) a -> abyte_kept W mem W' mem' a.
Proof.
intros Gc STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a Hs HJ HF HPK Hi Ho He Hq Hg.
split.
- eapply rm_ajgx_keep_img; [exact HJ | exact Hi | exact Ho | exact He | exact Hq | |].
  + apply fp_spares_closed. apply sink_closed_pos. exact HF.
  + intros H. exact (Hg (Hs a H)).
- intros Hw. unfold arm in *. apply (rr_writable2 (w_H W) (w_H W') mem mem' a); [|exact Hw].
  intros Hpr. exact (HPK a Hi Ho He Hpr).
Qed.

(* ------------------------------------------------------------------ RLIVE across a program callee *)
(* The walk calls a program function at sp = the entry sp - 48 (drain, gestures_end).  RLIVE at the call, the
   callee's own journal (at its globals Gc, inside G_DR, from sp = rsp0 - 48, its stack at most DRAIN_STK_x) and the
   caller's composed journal give RLIVE at the callee's return: the saved registers lie above the callee's stack;
   g_lock and g_wake[1] are image bytes outside Gc (HRGP) and off PST (PSTG). *)
Lemma rr_live_call : forall cx ly1 S1 Hp1 W1 m1 md1 k1 Gc STK1 FP1 ly2 S2 Hp2 W2 m2 md2 kc k2,
  RBASE B ARx MT RP MMAX RG cx ->
  RLIVE B PST ARx RG cx ly1 S1 Hp1 W1 m1 md1 k1 ->
  gx_ok SEGS B Gc -> (forall a, inG Gc a -> inG (G_DR B RG) a) -> 0 <= STK1 <= DRAIN_STK_x ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx Gc 0 [] STK1 (rsp0 cx - RR_FRAME) FP1 ly1 S1 Hp1 W1 m1 md1 []
    ly2 S2 Hp2 W2 m2 md2 kc ->
  Forall (fun r => 0 < fst r) FP1 ->
  apres_kept B W1 m1 W2 m2 ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
    (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly2 S2 Hp2 W2 m2 md2 k2 ->
  RLIVE B PST ARx RG cx ly2 S2 Hp2 W2 m2 md2 k2.
Proof.
intros cx ly1 S1 Hp1 W1 m1 md1 k1 Gc STK1 FP1 ly2 S2 Hp2 W2 m2 md2 kc k2 HB HL1 HGc HGcs HSTK1 HJc HFP0 HPK HJ2.
destruct HL1 as (HJ1 & HROM1 & HPK1 & HSV & HLK1 & HWK1).
destruct HB as (HPRE & _ & _ & RGP & _).
destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (GK : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_DR B RG) a -> abyte_kept W1 m1 W2 m2 a).
{ intros a Hi Ho He Hq Hg. eapply rr_img_kept;
    [exact HGcs | exact HJc | exact HFP0 | exact HPK | exact Hi | exact Ho | exact He | exact Hq | exact Hg]. }
split; [exact HJ2|].
split.
{ eapply (ajournal_gx_rom_view_x SEGS B PST ARx LAWS pa_segs_low); [exact HJc | | exact PSTR | exact HROM1].
  intros a Ha. destruct (HROMO a Ha) as (R1 & R2 & R3 & R4). split; [|exact (conj R2 (conj R3 R4))].
  intros Hg. apply R1. apply rr_G_DR_RR. exact (HGcs a Hg). }
split; [exact (rm_apk_trans _ _ _ _ _ _ HPK1 HPK)|].
split.
{ intros j Hj. apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [|exact (HSV j Hj)].
  intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  eapply rm_ajgx_keep_high; [exact HGc | exact HJc | |].
  + unfold rsp0, RR_STK_x, RR_STK, DRAIN_STK_x, DRAIN_STK, SL_STK, RR_FRAME, DRAIN_FRAME, SL_FRAME, ASTACK in *. lia.
  + unfold rsp0, RR_STK_x, RR_STK, DRAIN_STK_x, DRAIN_STK, SL_STK, RR_FRAME, DRAIN_FRAME, SL_FRAME, ASTACK in *. lia. }
split.
{ apply (alock_at_kept RG W1 m1 W2 m2 true HLK1). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct (RGIMG a ltac:(unfold rg_rng; lia)) as (Hi & Ho & He). apply GK; [exact Hi | exact Ho | exact He | |].
  - apply PSTG. unfold rr_gcells. apply Exists_cons_hd. cbn [fst snd]. lia.
  - apply rr_nG_DR. lia. }
{ apply (awake_at_kept RG W1 m1 W2 m2 HWK1). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct (RGIMG a ltac:(unfold rg_rng; lia)) as (Hi & Ho & He). apply GK; [exact Hi | exact Ho | exact He | |].
  - apply PSTG. unfold rr_gcells. do 13 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd]. lia.
  - apply rr_nG_DR. lia. }
Qed.

(* ------------------------------------------------------------------ the table *)
Lemma rm_pads : forall cx, RBASE B ARx MT RP MMAX RG cx ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx).
Proof.
intros cx HB. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & HR & _).
destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
eapply Forall_impl; [|exact HF]. intros e (_ & _ & P1 & P2 & _). split; assumption.
Qed.
(* the table before slot i: 56 i bytes; after it: 56 (|es| - i - 1) *)
Lemma rm_tpre_len : forall cx i, RBASE B ARx MT RP MMAX RG cx -> (i <= length (rxes cx))%nat ->
  Z.of_nat (length (rmTpre cx i)) = AENT * Z.of_nat i.
Proof.
intros cx i HB Hi. pose proof (rm_pads cx HB) as HP.
rewrite <- (firstn_skipn i (rxes cx)) in HP. apply Forall_app in HP as [HP _].
unfold rmTpre. rewrite (rm_concat_len _ HP), length_firstn. unfold AENT. lia.
Qed.
Lemma rm_tpost_len : forall cx i, RBASE B ARx MT RP MMAX RG cx -> (i < length (rxes cx))%nat ->
  Z.of_nat (length (rmTpost cx i)) = AENT * (Z.of_nat (length (rxes cx)) - Z.of_nat i - 1).
Proof.
intros cx i HB Hi. pose proof (rm_pads cx HB) as HP.
rewrite <- (firstn_skipn (S i) (rxes cx)) in HP. apply Forall_app in HP as [_ HP].
unfold rmTpost. rewrite (rm_concat_len _ HP), length_skipn. unfold AENT. lia.
Qed.
(* rmtbl at slot i, from the relay as at the entry (arelay_at with the entry's G0 and es), at an ARx state *)
Lemma rm_tbl_rel : forall cx i ly S Hp W m md, RBASE B ARx MT RP MMAX RG cx -> (i < length (rxes cx))%nat ->
  ARx ly S Hp W m md -> arelay_at B RG ly S W m (rxG0 cx) (rxes cx) ->
  rmtbl B RG cx i ly S W m (entry_bytes (rnth cx i)).
Proof.
intros cx i ly S Hp W m md HB Hi HAR HR.
pose proof HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & (tail & T1 & T2 & T3) & R10 & R11).
destruct (alx_blocks _ _ _ LAWS ly S Hp W m md (rxG0 cx) ATABLE HAR R8) as (_ & _ & _ & _ & Hpres & _).
change (req_size ATABLE) with 896 in Hpres.
pose proof (rm_pads cx HB) as HP.
assert (Hlen : Z.of_nat (length (rxes cx)) <= 16) by lia.
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
split; [exact R5|]. split; [exact R6|]. split; [exact R8|].
split.
{ rewrite Forall_forall in HP. destruct (HP _ (nth_In (rxes cx) relay_remove_b_c.no_entry Hi)) as [P1 P2].
  unfold rnth. rewrite (rm_eb_len _ P1 P2). reflexivity. }
split.
{ exists tail. split; [exact T1|].
  rewrite (rm_concat_split entry_bytes (rxes cx) relay_remove_b_c.no_entry i Hi) in T3.
  unfold rmTpre, rmTpost, rnth. rewrite <- !app_assoc in T3. exact T3. }
split.
{ intros k Hk. unfold arm. apply (apresent_writable SEGS). apply (proj1 (Hpres (rmSA cx i + k) ltac:(unfold rmSA, AENT in *; lia))). }
pose proof (rm_remove_perm (rxes cx) i relay_remove_b_c.no_entry Hi) as HPm.
pose proof (Permutation_Forall HPm R10) as HF. apply Forall_cons_iff in HF as [_ HF]. exact HF.
Qed.

(* ---- route R (G8b, the census rows of this file): the journal helpers at a world relation R.  ajournal_gx_x .. ARx
   -> ajournal_gx_xR .. ARx R, SRr SEGS -> SRrG SEGS R, RLIVE -> RLIVE_xR (W_relay_remove_cx.v), the engine steps -> their
   _xR twins (W_journal_x.v ajournal_gx_inner_xR / ajournal_gx_sub_xR / ajournal_gx_rom_view_xR, YCbqG.v afn_pre_x_atR).
   Rows: :207 AFREE, :211 DRAIN, :212 GSE, :214 AFREEN -> AFREE_R / DRAIN_R / GSE_R / AFREEN_R below (no twin uses them);
   :232 rm_gx_callS -> rm_gx_callS_xR; :274 rm_ajgx_keep_high -> rm_ajgx_keep_high_xR; :287 rm_ajgx_keep_img ->
   rm_ajgx_keep_img_xR; :312 rm_ajgx_ly_top -> rm_ajgx_ly_top_xR; :398 rr_img_kept -> rr_img_kept_xR; :419
   rr_live_call -> rr_live_call_xR.  No other lemma of this file states a journal, SRr, RLIVE or RHELD; they serve the
   R walks as they are.  The strict lemmas above keep their proofs (the hop files switch to these twins). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* the R free rules' call-boundary premise RO, from the journal's ARx at the call state (part 3c removed their memnorm
   premise) *)
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
(* :207 AFREE at R *)
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* :211 DRAIN, :212 GSE at R (W_contract_xR.v) *)
Hypothesis DRAIN_R : dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE_R : gse_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* :214 AFREEN at R *)
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.

(* :232 rm_gx_callS at R: W_journal_x.v gx_callS_xR's text at SEGS (the callee's SRrG continuation, the sub-journal by
   ajournal_gx_sub_xR with R_trans); the proof is W_gestures_end.v gse_callS_xR's *)
Lemma rm_gx_callS_xR : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
gx_ok SEGS B G ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
 SRrG SEGS R W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK1 (spZ regsc) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRrG SEGS R W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros G W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 K
HGx HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRrG_mono.
{ apply Hcallee.
  pose proof HJ as HJin. apply ajournal_gx_inner_xR in HJin. destruct HJin as (memS & HJi & _).
  rewrite !Z.add_0_r in HJi.
  eapply (afn_pre_x_atR SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memc mdc k regsc STK1 o ch1 HJi);
  try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HPr & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [reflexivity|].
rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HPr | exact HK]]].
change own with ([] ++ own).
eapply (ajournal_gx_sub_xR SEGS B PST ARx LAWS pa_segs_low R_trans);
[exact HJ | exact HJ1 | lia | lia | lia | | exact HGx | exact HF].
intros a (r & Hr & _). destruct Hr.
Qed.
(* :274 rm_ajgx_keep_high at R *)
Lemma rm_ajgx_keep_high_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
gx_ok SEGS B G ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
pose proof asan_consts as (C1 & _).
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
pose proof (inG_low SEGS B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* :287 rm_ajgx_keep_img at R *)
Lemma rm_ajgx_keep_img_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a -> ~ inG G a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hpst Hf Hg.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hpst Hf).
pose proof (pa_segs_low a Hi) as HL.
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
(* :312 rm_ajgx_ly_top at R *)
Lemma rm_ajgx_ly_top_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ly_top ly' = ly_top ly.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET.
Qed.
(* :398 rr_img_kept at R *)
Lemma rr_img_kept_xR : forall Gc STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a,
  (forall x, inG Gc x -> inG (G_DR B RG) x) ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R Gc 0 [] STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  Forall (fun r => 0 < fst r) FP -> apres_kept B W mem W' mem' ->
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_DR B RG) a -> abyte_kept W mem W' mem' a.
Proof.
intros Gc STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a Hs HJ HF HPK Hi Ho He Hq Hg.
split.
- eapply rm_ajgx_keep_img_xR; [exact HJ | exact Hi | exact Ho | exact He | exact Hq | |].
  + apply fp_spares_closed. apply sink_closed_pos. exact HF.
  + intros H. exact (Hg (Hs a H)).
- intros Hw. unfold arm in *. apply (rr_writable2 (w_H W) (w_H W') mem mem' a); [|exact Hw].
  intros Hpr. exact (HPK a Hi Ho He Hpr).
Qed.
(* :419 rr_live_call at R: RLIVE_xR at the call, the callee's journal at R and the caller's composed journal at R give
   RLIVE_xR at the callee's return *)
Lemma rr_live_call_xR : forall cx ly1 S1 Hp1 W1 m1 md1 k1 Gc STK1 FP1 ly2 S2 Hp2 W2 m2 md2 kc k2,
  RBASE B ARx MT RP MMAX RG cx ->
  RLIVE_xR B PST ARx R RG cx ly1 S1 Hp1 W1 m1 md1 k1 ->
  gx_ok SEGS B Gc -> (forall a, inG Gc a -> inG (G_DR B RG) a) -> 0 <= STK1 <= DRAIN_STK_x ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R Gc 0 [] STK1 (rsp0 cx - RR_FRAME) FP1 ly1 S1 Hp1 W1 m1 md1 []
    ly2 S2 Hp2 W2 m2 md2 kc ->
  Forall (fun r => 0 < fst r) FP1 ->
  apres_kept B W1 m1 W2 m2 ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
    (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly2 S2 Hp2 W2 m2 md2 k2 ->
  RLIVE_xR B PST ARx R RG cx ly2 S2 Hp2 W2 m2 md2 k2.
Proof.
intros cx ly1 S1 Hp1 W1 m1 md1 k1 Gc STK1 FP1 ly2 S2 Hp2 W2 m2 md2 kc k2 HB HL1 HGc HGcs HSTK1 HJc HFP0 HPK HJ2.
destruct HL1 as (HJ1 & HROM1 & HPK1 & HSV & HLK1 & HWK1).
destruct HB as (HPRE & _ & _ & RGP & _).
destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (GK : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_DR B RG) a -> abyte_kept W1 m1 W2 m2 a).
{ intros a Hi Ho He Hq Hg. eapply rr_img_kept_xR;
    [exact HGcs | exact HJc | exact HFP0 | exact HPK | exact Hi | exact Ho | exact He | exact Hq | exact Hg]. }
split; [exact HJ2|].
split.
{ eapply (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low); [exact HJc | | exact PSTR | exact HROM1].
  intros a Ha. destruct (HROMO a Ha) as (R1 & R2 & R3 & R4). split; [|exact (conj R2 (conj R3 R4))].
  intros Hg. apply R1. apply rr_G_DR_RR. exact (HGcs a Hg). }
split; [exact (rm_apk_trans _ _ _ _ _ _ HPK1 HPK)|].
split.
{ intros j Hj. apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [|exact (HSV j Hj)].
  intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  eapply rm_ajgx_keep_high_xR; [exact HGc | exact HJc | |].
  + unfold rsp0, RR_STK_x, RR_STK, DRAIN_STK_x, DRAIN_STK, SL_STK, RR_FRAME, DRAIN_FRAME, SL_FRAME, ASTACK in *. lia.
  + unfold rsp0, RR_STK_x, RR_STK, DRAIN_STK_x, DRAIN_STK, SL_STK, RR_FRAME, DRAIN_FRAME, SL_FRAME, ASTACK in *. lia. }
split.
{ apply (alock_at_kept RG W1 m1 W2 m2 true HLK1). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct (RGIMG a ltac:(unfold rg_rng; lia)) as (Hi & Ho & He). apply GK; [exact Hi | exact Ho | exact He | |].
  - apply PSTG. unfold rr_gcells. apply Exists_cons_hd. cbn [fst snd]. lia.
  - apply rr_nG_DR. lia. }
{ apply (awake_at_kept RG W1 m1 W2 m2 HWK1). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct (RGIMG a ltac:(unfold rg_rng; lia)) as (Hi & Ho & He). apply GK; [exact Hi | exact Ho | exact He | |].
  - apply PSTG. unfold rr_gcells. do 13 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd]. lia.
  - apply rr_nG_DR. lia. }
Qed.
End wR.

End c.
End b.
End a.
