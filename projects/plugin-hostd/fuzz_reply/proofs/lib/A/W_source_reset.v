(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's source_reset, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (an internal call) and lib/A/ACbk.v (entry and return). *)
(* source_reset(s) at 0x8575c (fuzz_reply.c:531-538): frame 32; it loads the shadow base through the GOT, calls
   list_free on s->pending (s+16), s->expected (s+64) and s->held (s+80), frees s->partial (s+40) behind a shadow
   check, and zeroes the 96 bytes of the struct with __asan_memset, so the source is closed.
   ONE proof, over the GENERIC allocator relation ARx (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)):
   Section c proves pb_source_reset_x : sr_spec_x B PST ARx MT G (W_contract_x.v), Section g pb_source_reset_g_x and
   Section gc pb_source_reset_gc_x over gx_prog_x. Section ar re-derives the AR theorems pb_source_reset,
   pb_source_reset_g and pb_source_reset_gc (statements unchanged) at ARx := W_journal_x.ARi0, PST := [].
   Section hypotheses of the generic form, with what owes them:
   - LAWS : AR_laws_x SEGS B ARx hl, HP0 (a Theorem Labs lane's ruling; this walk reads no block shadow, so it is unused),
     BLKN (W_kit_x.v's; a live block's size is not negative, which gx_keep_blk needs for its byte 0);
   - HPST : no byte of the image is a program static of PST (G-free; a list_free call keeps the bytes of G outside
     its own G1 only through the journal's image clause, whose premise is `~ Exists (in_zr a) PST`, and the ROM
     bytes for rom_view the same way). PST := [] at every walk instance (W2List-2, 2026-10-29), so it is
     `intros a _ H; inversion H` there;
   - LF : lf_spec_g_x B PST ARx MT (BASE + AF_fr_list_free) (the lane's list_free walk; taken G-generically and used
     at G' = [(HA + 16, 16)] / [(HA + 64, 16)] / [(HA + 80, 16)], so the callee's journal keeps every other image
     byte and s->partial and the other two headers survive the calls);
   - AFREE / AFREEN : afree_cf_rule_c_x / afree_null_cf_rule_c_x at the caller-context table CTX (W_journal_x.v
     Section hc), with HCTX_sr_free : In [BASE + AF_fr_source_reset + 0x54] CTX, the trace of the one free call
     (s0 holds s, an image address, so the chain handed to the rule is [] and the trace is its return address);
   - AMEMSET : aintrin_realizes_x SEGS B ARx OSet (SIGMA WS_asan_memset) (W_sites_x.v Section j, the runtime lane);
   - GX_ROM, GX_W, GSHV : the image facts about the walk's globals G - every byte of G is a byte of a readable
     segment and of a writable segment, and the shadow of a range of G is visible.  At PB_fr the first two are a
     vm_compute over the segments; the instance owes GSHV (ASan maps the whole low shadow). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_list_free.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_journal W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_kit_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_srlf_xR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_source_reset : Z := AF_fr_source_reset.
Definition A_source_resetP : Z := BASE + A_source_reset.
Definition A_sr_lf : Z := AF_fr_list_free.
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Variable RP : roomp.
Hypothesis MLAW : ameter_laws MT.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok SEGS B G.
Hypothesis HGR : gx_rt B G.
(* every byte of G is a byte of a readable and of a writable segment of the image *)
Hypothesis GX_ROM : forall a, inG G a -> seg_rom SEGS (Z_to_bv 64 a) <> None.
Hypothesis GX_W : forall a, inG G a -> forall m, writable_at SEGS m a.
(* the shadow of a range of G is visible in every state of the allocator *)
Hypothesis GSHV : forall ly S Hp W mem md a n, ARx ly S Hp W mem md -> 0 < n ->
(forall x, a <= x < a + n -> inG G x) -> shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Hypothesis LF : lf_spec_g_x B PST ARx MT RP (BASE + AF_fr_list_free).
Variable CTX : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AMEMSET : aintrin_realizes_x SEGS B ARx OSet (SIGMA WS_asan_memset).
(* the free call at +0x50 returns to +0x54 (fuzz_reply.objdump: 0x857ac jal free, source_reset at 0x8575c) *)
Hypothesis HCTX_sr_free : In [BASE + AF_fr_source_reset + 0x54] CTX.
(* ROM bytes are outside G, the allocator's statics, errno and the sink head (W_journal.v rom_out; vm_compute at PB_fr) *)
Hypothesis HRO : rom_out SEGS B G.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let HBfree := pal_free B TL.
Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
(* the ROM bytes are off PST: the form ajournal_gx_rom_view_x takes *)
Lemma sr_pstr : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Proof. intros a (sg & Hsg & _ & Hr). apply HPST. exists sg. split; [exact Hsg | exact Hr]. Qed.
(* ---------------------------------------------------------------- small facts about G *)
Lemma inG_img : forall a, inG G a -> 0x10000 <= a < 0x5fb000.
Proof. intros a Ha. exact (pa_img_range a (proj1 (HG a Ha))). Qed.
Lemma inG_lo : forall a, inG G a -> 0 <= a < kLowMemEnd.
Proof. intros a Ha. exact (pa_segs_low a (proj1 (HG a Ha))). Qed.
Lemma inG_not_owned_img : forall ly S Hp (W : world SEGS) mem md a, ARx ly S Hp W mem md -> in_img SEGS a ->
~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof. intros ly S Hp W mem md a HAR Hi Ho Hao. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W mem md a HAR Hi) Hao)). Qed.
Lemma inG_not_owned : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> inG G a -> ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a HAR Ha Ho.
exact (proj1 (proj2 (HG a Ha)) (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W mem md a HAR (proj1 (HG a Ha))) Ho)).
Qed.
Lemma azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof. intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2. exists r. split; [exact Hin|]. repeat split; lia. Qed.
Lemma aview_G_some : forall (W : world SEGS) m a, inG G a -> aview SEGS (w_H W) m a <> None.
Proof.
intros W m a Ha.
assert (Hi : in_img SEGS (bv_unsigned (Z_to_bv 64 a))).
{ rewrite unsigned_lit_small by (pose proof (inG_lo a Ha); unfold kLowMemEnd in *; lia). exact (proj1 (HG a Ha)). }
unfold aview, mbyte, mrestrict. rewrite (hidden_not_img SEGS W (Z_to_bv 64 a) Hi).
destruct (m (Z_to_bv 64 a)) as [b|]; cbn; [discriminate|].
destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|] eqn:Er; cbn; [discriminate | intros _; exact (GX_ROM a Ha Er)].
Qed.
(* W_sites.v:279, which this file does not import *)
Lemma aview_wrap64 : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte.
assert (E : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. }
rewrite E. reflexivity.
Qed.
Lemma writable_kept' : forall (H : word -> bool) (m m2 : word -> option byte) a,
(apresent H m a -> apresent H m2 a) -> writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H m2) a.
Proof.
intros H m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; intros Hw; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma le_byte_zero : forall w k, YO0f.le_byte 0 w k = 0.
Proof. intros w k. unfold YO0f.le_byte. rewrite Zmod_0_l, Z.shiftr_0_l, Zmod_0_l. reflexivity. Qed.
Lemma garr8_of_zero_view : forall (W : world SEGS) m a (n : nat),
(forall i, 0 <= i < Z.of_nat n -> aview SEGS (w_H W) m (a + i) = Some 0) ->
garr8 SEGS (mrestrict (w_H W) m) a (repeat 0 n).
Proof.
intros W m a n Hz. apply garr8_zeros. intros x Hx.
destruct (aview_byte SEGS (w_H W) m x 0 ltac:(replace x with (a + (x - a)) by lia; apply Hz; lia)) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hv. unfold bv_wrap.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma val_mem_of_zeros : forall (m : word -> option byte) a (N : nat) i (n : nat),
garr8 SEGS m a (repeat 0 N) -> 0 <= i -> (Z.to_nat i + n <= N)%nat -> val_mem SEGS m (a + i) n 0.
Proof.
intros m a N i n Hg Hi Hn k Hk.
destruct (Hg (Z.to_nat i + k)%nat ltac:(rewrite repeat_length; lia)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
rewrite nth_repeat in Hv.
replace (a + i + Z.of_nat k) with (a + Z.of_nat (Z.to_nat i + k)) by lia.
rewrite Hv, !le_byte_zero. reflexivity.
Qed.
Lemma nodup_app_disj : forall {A : Type} (l1 l2 : list A), NoDup (l1 ++ l2) -> forall x, In x l1 -> In x l2 -> False.
Proof.
intros A l1. induction l1 as [|a l1 IH]; cbn; intros l2 HN x H1 H2; [destruct H1|].
apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HN. apply List.NoDup_cons_iff in HN. destruct HN as [Hna HN'].
destruct H1 as [-> | H1].
- apply Hna. apply in_or_app. right. exact H2.
- exact (IH l2 (proj2 (stdpp.base.NoDup_ListNoDup _) HN') x H1 H2).
Qed.
Lemma nodup_app_right : forall {A : Type} (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l2.
Proof.
intros A l1 l2 HN. apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HN.
apply (proj2 (stdpp.base.NoDup_ListNoDup _)). exact (List.NoDup_app_remove_l l1 l2 HN).
Qed.
Lemma map_fst_list_blks : forall l, map fst (list_blks l) = list_blocks l.
Proof.
intros l. unfold list_blks, list_blocks. rewrite map_app, map_map. cbn [fst].
destruct (hl_cap l =? 0); reflexivity.
Qed.

(* ---------------------------------------------------------------- the model, uniform in the two cases *)
Definition sr_l1 (op : option hsrc) : hlist := match op with Some h => hs_pending h | None => empty_list end.
Definition sr_l2 (op : option hsrc) : hlist := match op with Some h => hs_expected h | None => empty_list end.
Definition sr_l3 (op : option hsrc) : hlist := match op with Some h => hs_held h | None => empty_list end.
Definition sr_p (op : option hsrc) : Z := match op with Some h => hs_partial h | None => 0 end.

Lemma sr_rep_lists : forall ly S Hp W mem md HA op,
ARx ly S Hp W mem md ->
match op with Some h => asrc_at B ly S W mem HA h | None => asrc_closed W mem HA end ->
alist_at B ly S W mem (HA + 16) (sr_l1 op) false /\
alist_at B ly S W mem (HA + 64) (sr_l2 op) true /\
alist_at B ly S W mem (HA + 80) (sr_l3 op) true /\
val_mem SEGS (mrestrict (w_H W) mem) (HA + 40) 8 (sr_p op) /\
match op with Some h => In (sr_p op, APARTIAL) (ablocks B ly S) | None => sr_p op = 0 end.
Proof.
intros ly S Hp W mem md HA op HAR HREP. destruct op as [h|].
- pose proof HREP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HP1 & _ & HP2 & _ & _ & _ & _ & _ & HP3 & _ & _ & _ & HP4 & HP5 & _).
  cbn [sr_l1 sr_l2 sr_l3 sr_p]. split; [exact HP1|]. split; [exact HP4|]. split; [exact HP5|].
  split; [exact HP2 | exact HP3].
- destruct HREP as [Hz Hw]. cbn [sr_l1 sr_l2 sr_l3 sr_p].
  assert (HV : forall i (n : nat), 0 <= i -> (Z.to_nat i + n <= Z.to_nat ASRC)%nat ->
    val_mem SEGS (mrestrict (w_H W) mem) (HA + i) n 0)
  by (intros i n Hi Hn; exact (val_mem_of_zeros _ HA (Z.to_nat ASRC) i n Hz Hi Hn)).
  assert (HL : forall d, 0 <= d -> d + 16 <= ASRC -> forall lines,
    alist_at B ly S W mem (HA + d) empty_list lines).
  { intros d Hd Hd16 lines. unfold alist_at, empty_list. cbn [hl_v hl_n hl_cap hl_recs hl_junk].
    change (Z.of_nat (length (@nil (Z * list byte)))) with 0.
    split; [exact (HV d 8%nat Hd ltac:(unfold ASRC in *; lia))|].
    split; [replace (HA + d + 8) with (HA + (d + 8)) by lia; exact (HV (d + 8) 4%nat ltac:(lia) ltac:(unfold ASRC in *; lia))|].
    split; [replace (HA + d + 12) with (HA + (d + 12)) by lia; exact (HV (d + 12) 4%nat ltac:(lia) ltac:(unfold ASRC in *; lia))|].
    split; [intros i Hi; replace (HA + d + i) with (HA + (d + i)) by lia; apply (Hw (d + i)); unfold ASRC in *; lia|].
    split; [first [ (cbn; lia) | (vm_compute; split; [discriminate | reflexivity])
                  | (match goal with |- ?g => idtac "DBG G5" g end; fail) ]|].
    split; [left; split; reflexivity|].
    split; [constructor|]. split; [cbn; intros []|]. constructor. }
  split; [exact (HL 16 ltac:(lia) ltac:(unfold ASRC; lia) false)|].
  split; [exact (HL 64 ltac:(lia) ltac:(unfold ASRC; lia) true)|].
  split; [exact (HL 80 ltac:(lia) ltac:(unfold ASRC; lia) true)|].
  split; [exact (HV 40 8%nat ltac:(lia) ltac:(unfold ASRC; lia)) | reflexivity].
Qed.

(* ---------------------------------------------------------------- what a list's predicate reads *)
Lemma sr_text_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec.
rewrite length_app, !word_le8_length. lia.
Qed.
Lemma alist_blks_in : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines ->
forall b n, In (b, n) (list_blks l) -> In (b, n) (ablocks B ly S).
Proof.
intros ly S W mem LA l lines HL b n Hin.
pose proof HL as (_ & _ & _ & _ & _ & Hvec & _ & _ & Hrecs).
unfold list_blks in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc | Hc]; [destruct Hin|].
  destruct Hin as [E | []]. injection E as <- <-.
  destruct Hvec as [[Hc0 _] | (_ & Hin & _)]; [lia | exact Hin].
- apply in_map_iff in Hin. destruct Hin as (q & E & Hq). injection E as <- <-.
  exact (proj1 (proj1 (Forall_forall _ _) Hrecs q Hq)).
Qed.
Lemma fp_blocks_pos : forall ly S Hp W mem md l lines LA,
ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines ->
~ YI16.sink_open_fp (blk_FP (list_blks l)).
Proof.
intros ly S Hp W mem md l lines LA HAR HL (r & Hr & Hr1 & Hr2).
unfold blk_FP in Hr. apply in_map_iff in Hr. destruct Hr as ((b, n) & <- & Hin).
cbn [fst snd] in Hr1, Hr2.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n HAR (alist_blks_in ly S W mem LA l lines HL b n Hin)) as (_ & H4096 & _).
lia.
Qed.
Lemma blks_not_in_fp : forall ly S Hp W mem md (l : hlist) b n,
ARx ly S Hp W mem md ->
(forall b' n', In (b', n') (list_blks l) -> In (b', n') (ablocks B ly S)) ->
In (b, n) (ablocks B ly S) -> ~ In b (list_blocks l) ->
forall i, 0 <= i < req_size n -> ~ inFP (blk_FP (list_blks l)) (b + i).
Proof.
intros ly S Hp W mem md l b n HAR Hsub Hin Hnb i Hi (r & Hr & Hra).
unfold blk_FP in Hr. apply in_map_iff in Hr. destruct Hr as ((b', n') & <- & Hin').
cbn [fst snd] in Hra. destruct Hra as [Hr1 Hr2].
assert (Hne : (b', n') <> (b, n)).
{ intros E. injection E as <- <-. apply Hnb. rewrite <- map_fst_list_blks.
  exact (in_map fst _ _ Hin'). }
pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md b' n' b n HAR (Hsub b' n' Hin') Hin Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma alist_fp_in : forall ly S W mem LA l lines r,
alist_at B ly S W mem LA l lines -> In r (alist_fp LA l) ->
r = (LA, LA + 16) \/ exists b n, In (b, n) (list_blks l) /\ fst r = b /\ snd r <= b + req_size n.
Proof.
intros ly S W mem LA l lines r HL Hr.
pose proof HL as (_ & _ & _ & _ & (Hn & Hcap) & Hvec & _ & _ & Hrecs).
unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; reflexivity | right].
apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0 | Hc0]; [destruct Hr|].
  destruct Hr as [<- | []]. exists (hl_v l), (AREC * hl_cap l).
  split; [unfold list_blks; rewrite (proj2 (Z.eqb_neq _ _) Hc0); apply in_or_app; left; left; reflexivity|].
  split; [reflexivity|]. cbn [gfp fst snd]. unfold bzs. rewrite length_map, length_app, sr_text_len.
  destruct Hvec as [[Hc _] | (_ & _ & Hj & _)]; [lia|].
  unfold AREC, req_size in *. rewrite (proj2 (Z.eqb_neq (16 * hl_cap l) 0) ltac:(unfold hl_n in *; lia)).
  unfold hl_n in *. lia.
- apply in_map_iff in Hr. destruct Hr as (q & <- & Hq).
  exists (fst q), (Z.of_nat (length (snd q)) + 1).
  split; [unfold list_blks; apply in_or_app; right; apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))); exact Hq|].
  split; [reflexivity|]. cbn [gfp fst snd]. unfold bzs. rewrite length_map, length_app.
  cbn [length]. unfold req_size. rewrite (proj2 (Z.eqb_neq (Z.of_nat (length (snd q)) + 1) 0) ltac:(lia)). lia.
Qed.
Lemma alist_kept_gen : forall ly S W mem ly' S' W' mem' LA l lines,
alist_at B ly S W mem LA l lines ->
(forall b n, In (b, n) (list_blks l) -> In (b, n) (ablocks B ly' S')) ->
(forall a, LA <= a < LA + 16 -> inG G a) ->
(forall a, LA <= a < LA + 16 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall b n, In (b, n) (list_blks l) -> forall i, 0 <= i < req_size n ->
 aview SEGS (w_H W') mem' (b + i) = aview SEGS (w_H W) mem (b + i) /\
 writable_at SEGS (mrestrict (w_H W') mem') (b + i)) ->
alist_at B ly' S' W' mem' LA l lines.
Proof.
intros ly S W mem ly' S' W' mem' LA l lines HL HB HGL HKH HKB.
apply (alist_at_kept B ly S W mem ly' S' W' mem' LA l lines HL);
[|intros [b n] Hb; exact (HB b n Hb)].
intros r Hr a Ha.
destruct (alist_fp_in ly S W mem LA l lines r HL Hr) as [-> | (b & n & Hin & Hb & Hn)].
- cbn [fst snd] in Ha. split; [exact (HKH a Ha)|]. intros _. exact (GX_W a (HGL a Ha) _).
- rewrite Hb in Ha.
  assert (Hi : 0 <= a - b < req_size n) by lia.
  destruct (HKB b n Hin (a - b) Hi) as [Hv Hw].
  replace (b + (a - b)) with a in Hv, Hw by lia.
  split; [exact Hv | intros _; exact Hw].
Qed.

(* ---------------------------------------------------------------- what a callee's journal keeps *)
Lemma gx_keep_hi : forall G1 STK1 sp1 FP1 lyc Sc Hpc (W : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
(forall a, inG G1 a -> inG G a) ->
ajournal_gx_x SEGS B PST ARx G1 0 [] STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 Hsub HJ a Ha Hno.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
rewrite (F1 a Ha Hno). apply (aview_gagree SEGS G1 (w_H W) memc memS a Hag).
apply (proj2 (inGb_false G1 _)). rewrite unsigned_lit_small by lia.
intros Hc. pose proof (inG_lo a (Hsub a Hc)). unfold kLowMemEnd in *. lia.
Qed.
Lemma gx_keep_img : forall G1 STK1 sp1 FP1 lyc Sc Hpc (W : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
(forall a, inG G1 a -> inG G a) -> ~ YI16.sink_open_fp FP1 ->
ajournal_gx_x SEGS B PST ARx G1 0 [] STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
forall a, inG G a -> ~ inG G1 a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 Hsub Hfp HJ a Ha Hna.
destruct HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof (inG_lo a Ha) as Hlo.
rewrite (F3 a (proj1 (HG a Ha)) (proj1 (proj2 (HG a Ha))) (proj1 (HGR a Ha)) (HPST a (proj1 (HG a Ha)))
  ltac:(intros Hso; exfalso; exact (Hfp Hso))).
apply (aview_gagree SEGS G1 (w_H W) memc memS a Hag).
apply (proj2 (inGb_false G1 _)). rewrite unsigned_lit_small by (unfold kLowMemEnd in *; lia). exact Hna.
Qed.
Lemma gx_keep_blk : forall G1 STK1 sp1 FP1 lyc Sc Hpc (W : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 p n,
(forall a, inG G1 a -> inG G a) ->
ARx lyc Sc Hpc W memc mdc ->
ajournal_gx_x SEGS B PST ARx G1 0 [] STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
In (p, n) (ablocks B lyc Sc) -> (forall i, 0 <= i < req_size n -> ~ inFP FP1 (p + i)) ->
In (p, n) (ablocks B ly2 S2) /\
(forall i, 0 <= i < req_size n -> aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) memc (p + i)).
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 p n Hsub HAR HJ Hin Hno.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc p n HAR Hin) as (_ & H4096 & Hceil & _).
pose proof (BLKN lyc Sc Hpc W memc mdc p n HAR Hin) as Hn0.
assert (Hrq : 0 < req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
pose proof HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _ & _ & Hgone & _).
assert (Hin2 : In (p, n) (ablocks B ly2 S2)).
{ destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B ly2 S2)) as [Hc|Hc];
  [exact Hc | exfalso; exact (Hno 0 ltac:(lia) (Hgone p n 0 Hin Hc ltac:(lia)))]. }
split; [exact Hin2|]. intros i Hi.
rewrite (F2 p n i Hin Hin2 Hi (Hno i Hi)).
apply (aview_gagree SEGS G1 (w_H W) memc memS (p + i) Hag).
apply (proj2 (inGb_false G1 _)). rewrite unsigned_lit_small by lia.
intros Hc. pose proof (inG_lo (p + i) (Hsub (p + i) Hc)) as Hlo.
destruct (alx_client_img _ _ _ LAWS lyc Sc Hpc W memc mdc (p + i) HAR ltac:(left; exists p, n; split; [exact Hin | lia])) as [_ Hni].
exact (Hni (proj1 (HG (p + i) (Hsub (p + i) Hc)))).
Qed.

(* ---------------------------------------------------------------- the memset site in the journal frame *)
(* Reusable/YCbq.v:1955 aj_intrin_at wants the written bytes to be awr_bytes of the walk's own window; here they
   are bytes of a program global, so this is W_sites_x.v aj_gx_entry_at_x's proof at OSet, with its presence
   premise on the bytes of G weakened to visibility (which is all its ARx_frame_law step uses). *)
Lemma aj_set_gx_at : forall pc, aintrin_realizes_x SEGS B ARx OSet pc ->
forall (W : world SEGS) regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n (o : Z) raw,
ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n ->
0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> inG G a) ->
amem_range d n ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) d n) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\
 (forall i, 0 <= i < n -> aview SEGS (w_H W) mem2 (d + i) = Some (x mod 256)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw HdG Hamr Hra_d Hhull.
pose proof pa_segs_low as Hsegs.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres &
  (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _ & HQT).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre_x SEGS B ARx lyc Sc Hpc W regsT memT mdc).
{ eapply (ecall_pre_at_x SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memT mdc k regsT o HJi);
  [exact Hsp | exact Hal | exact Hneg | lia | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
assert (SCG : forall a, inG G a -> ~ (sp0 + o - ESTACK <= a < sp0 + o)).
{ intros a Ha Hs. pose proof (inG_lo a Ha). unfold kLowMemEnd in *. lia. }
assert (HDEST : dest_ok SEGS B lyc Sc W regsT memT d n).
{ intros a Ha. split; [exact (GX_W a (HdG a Ha) _)|].
  split; [exact (inG_not_owned lyc Sc Hpc W memT mdc a HAR (HdG a Ha))|].
  rewrite Hsp. exact (SCG a (HdG a Ha)). }
eapply SRr_mono.
{ exact (AM lyc Sc Hpc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr
    (* QMm W1: the destination is in G, and gx_ok's W0' clause puts G outside the kept ranges *)
    (fun a Ha HK => proj2 (proj2 (HG a (HdG a Ha))) (proj1 (proj2 HK))) Hra_d Hhull I). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsame & Hres & Heff & Hfr & Hgr).
rewrite Hsp in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
set (memM := fun y : word => if inGb G (bv_unsigned y) then memT y else mem2 y).
assert (MG : forall y, inGb G (bv_unsigned y) = false -> memM y = mem2 y) by (intros y Hy; unfold memM; rewrite Hy; reflexivity).
assert (MT2 : forall y, inGb G (bv_unsigned y) = true -> memM y = memT y) by (intros y Hy; unfold memM; rewrite Hy; reflexivity).
assert (GB : forall a, 0 <= a < 2 ^ 64 -> inGb G (bv_unsigned (Z_to_bv 64 a)) = inGb G a)
by (intros a Ha; rewrite unsigned_lit_small by lia; reflexivity).
assert (AVT : forall a, 0 <= a < 2 ^ 64 -> inG G a -> aview SEGS (w_H W) memM a = aview SEGS (w_H W) memT a).
{ intros a Ha Hga. apply aview_eq_of. unfold mrestrict. rewrite MT2; [reflexivity|]. rewrite GB by exact Ha. apply inGb_spec. exact Hga. }
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview SEGS (w_H W) memM a = aview SEGS (w_H W) mem2 a).
{ intros a Ha Hga. apply aview_eq_of. unfold mrestrict. rewrite MG; [reflexivity|]. rewrite GB by exact Ha. apply (proj2 (inGb_false G a)). exact Hga. }
assert (HARM : ARx lyc Sc Hpc W memM md2).
{ eapply (alx_frame _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2); [ | | reflexivity | reflexivity | reflexivity | |].
  - intros a Ha Ho. apply AV2; [exact Ha|]. intros Hga. exact (inG_not_owned lyc Sc Hpc W mem2 md2 a HAR2 Hga Ho).
  - intros a Hv. rewrite aview_wrap64 in Hv |- *.
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ra. set (a' := a mod 2 ^ 64) in *.
    destruct (inGb G a') eqn:Hgg.
    + apply inGb_spec in Hgg. rewrite (AVT a' Ra Hgg). exact (aview_G_some W memT a' Hgg).
    + rewrite (AV2 a' Ra (proj1 (inGb_false G a') Hgg)). exact Hv.
  - intros a _ Hh. unfold memM. destruct (inGb G (bv_unsigned (w64 a))) eqn:Hgg; [|reflexivity].
    exfalso. apply inGb_spec in Hgg. pose proof (proj1 (HG _ Hgg)) as Hi.
    rewrite (hidden_not_img SEGS W _ Hi) in Hh. discriminate.
  - (* QMm W0': a kept byte is not in G (gx_ok's as_kept clause), so memM is mem2 there *)
    intros a Ha (_ & Hk & _). unfold memM. destruct (inGb G (bv_unsigned (w64 a))) eqn:Hgg; [|reflexivity].
    exfalso. apply inGb_spec in Hgg. rewrite unsigned_lit_small in Hgg by lia.
    exact (proj2 (proj2 (HG a Hgg)) Hk). }
assert (HJM : ajournal_x SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memM md2 k).
{ eapply (ajournal_x_after_write SEGS B PST ARx LAWS Hsegs STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memT mdc k memM md2
    (fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc Hpc own HJi).
  - intros a Ha Hna. destruct (inGb G a) eqn:Hgg.
    + apply inGb_spec in Hgg. exact (AVT a Ha Hgg).
    + assert (HnG : ~ inG G a) by (apply (proj1 (inGb_false G a)); exact Hgg). rewrite (AV2 a Ha HnG).
      apply Hfr; [exact Ha | intros Hw; exact (HnG (HdG a Hw)) | exact Hna].
  - intros a [Hh [b Hb]]. split; [exact Hh|]. unfold memM. destruct (inGb G (bv_unsigned (Z_to_bv 64 a))).
    + exists b. exact Hb.
    + exact (proj2 (Hgr a (conj Hh (ex_intro _ b Hb)))).
  - exact Hsame.
  - intros a Ha. left. left. lia.
  - exact HARM.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
assert (HJ2 : ajournal_x SEGS B PST ARx STK sp0 FP ly S Hp W0 (gover G memS mem2) md own lyc Sc Hpc W mem2 md2 k).
{ apply (ajournal_rebase_x SEGS B PST ARx LAWS Hsegs G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 HG HJM).
  - intros y Hy. symmetry. exact (MG y Hy).
  - intros y Hy. unfold mrestrict in Hy |- *. destruct (w_H W y) eqn:Hh; [exact Hy|].
    destruct (inGb G (bv_unsigned y)) eqn:Hgg; [|rewrite (MG y Hgg) in Hy; exact Hy].
    rewrite (MT2 y Hgg) in Hy. destruct (memT y) as [b|] eqn:Eb; [|exfalso; exact (Hy eq_refl)].
    assert (Hpy : apresent (w_H W) memT (bv_unsigned y)) by (split; rewrite Z_to_bv_bv_unsigned; [exact Hh | exists b; exact Eb]).
    destruct (Hgr _ Hpy) as [_ [b2 Hb2]]. rewrite Z_to_bv_bv_unsigned in Hb2. rewrite Hb2. discriminate. }
split.
{ apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k (gover G memS mem2) HSTK HXO);
  [rewrite !Z.add_0_r; exact HJ2 | | intros a Ha Hno; lia].
  intros y Hy. unfold mrestrict, gover in *. rewrite Hy. exact (Hag y Hy). }
split; [exact HP2|]. split; [exact Heff | split; [exact Hfr | exact Hgr]].
Qed.

(* ---------------------------------------------------------------- an internal call, journal to journal *)
Lemma aj_gx_call : forall (G1 : list (Z * Z)) (W : world SEGS) regsT memT pc STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Z -> Prop),
(forall a, inG G1 a -> inG G a) ->
ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md [] lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memT) (sp0 + o) (s0Z regsT) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsT memT mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_x SEGS B PST ARx G1 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsT regs2 /\ K ly2 S2 W2 regs2 mem2 md2 k1)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_x SEGS B PST ARx G1 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsT regs2 /\ K ly2 S2 W2 regs2 mem2 md2 k1).
Proof.
intros G1 W regsT memT pc STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 o raw ch1 K
HGsub HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof pa_segs_low as Hsegs.
pose proof HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
eapply SRr_mono.
{ apply Hcallee. exact (afn_pre_x_at SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md [] lyc Sc Hpc W memT mdc k regsT STK1 o ch1 HJi
    Hsp Hal Hneg Hstk1 Hbud ltac:(rewrite Hra; exact Hraw) ltac:(unfold raZ; rewrite Hra; exact Hra4) Hgp Htp
    ltac:(rewrite Hsp; exact Hch)). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [reflexivity|].
split; [|split; [exact HJ1 | split; [exact HP | exact HK]]].
replace (@nil (Z * Z)) with ([] ++ @nil (Z * Z)) by reflexivity.
eapply (ajournal_gx_sub_x SEGS B PST ARx LAWS Hsegs G STK sp0 0 [] FP ly S Hp W0 mem md [] lyc Sc Hpc W memT mdc k
  STK1 (sp0 + o) 0 [] FP1 [] ly2 S2 Hp2 W2 mem2 md2 k1 HJ);
[ exact (ajournal_gx_G_mono_x SEGS B PST ARx G1 G 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 HGsub HJ1)
| lia | lia | lia | intros a (r & [] & _) | exact HG | exact HF ].
Qed.

(* ---------------------------------------------------------------- a region kept across a call *)
Lemma region_kept_sp : forall E (W W2 : world SEGS) (m m2 : word -> option byte) n sp lo hi wlo whi cs,
bv_unsigned (ew E n) = sp -> lo <= wlo -> whi <= hi ->
(forall a, sp + lo <= a < sp + hi -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a) ->
(forall a, sp + lo <= a < sp + hi -> apresent (w_H W2) m2 a) ->
region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W2) m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E W W2 m m2 n sp lo hi wlo whi cs Hn Hw1 Hw2 Hv Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hv. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. lia.
Qed.

(* ---------------------------------------------------------------- one call of list_free *)
Definition sr_G1 (x : Z) : list (Z * Z) := [(x, 16)].
Lemma sr_G1_in : forall x a, inG (sr_G1 x) a <-> x <= a < x + 16.
Proof.
intros x a. unfold sr_G1, inG. rewrite Exists_cons, Exists_nil. unfold in_zr. cbn [fst snd].
split; [intros [H | []]; lia | intros H; left; lia].
Qed.
(* ---------------------------------------------------------------- the room round's counts across one call *)
(* a NoDup list of blocks, each live, is a sub-multiset of the live blocks *)
Lemma perm_of_incl_nodup : forall (L M : list (Z * Z)), List.NoDup L -> (forall b n, In (b, n) L -> In (b, n) M) ->
  exists rest, Permutation M (L ++ rest).
Proof.
induction L as [|[b n] L IH]; intros M HN HI.
- exists M. reflexivity.
- apply List.NoDup_cons_iff in HN as [Hx HN].
  destruct (in_split (b, n) M (HI b n (or_introl eq_refl))) as (M1 & M2 & ->).
  destruct (IH (M1 ++ M2) HN) as (rest & Hp).
  + intros b' n' Hy. assert (Hy' : In (b', n') (M1 ++ (b, n) :: M2)) by (apply HI; right; exact Hy).
    apply in_app_or in Hy' as [H | [H | H]].
    * apply in_or_app. left. exact H.
    * exfalso. apply Hx. rewrite H. exact Hy.
    * apply in_or_app. right. exact H.
  + exists rest. cbn [app]. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
    apply perm_skip. exact Hp.
Qed.
(* a list's blocks have distinct addresses (alist_at's NoDup and the vector off the texts) *)
Lemma list_blks_nodup : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines -> List.NoDup (list_blks l).
Proof.
intros ly S W mem LA l lines HL. pose proof HL as (_ & _ & _ & _ & _ & _ & Hnd & Hnv & _).
eapply List.NoDup_map_inv with (f := fst). rewrite map_fst_list_blks. unfold list_blocks.
apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in Hnd.
destruct (hl_cap l =? 0); cbn [app]; [exact Hnd|]. constructor; [exact Hnv | exact Hnd].
Qed.
(* list_free's post (its blocks gone from some rest of the live blocks) keeps the live counts under their bounds *)
Lemma sr_cnt_rest : forall RP0 (L M M' rest : list (Z * Z)), Permutation M (L ++ rest) -> Permutation M' rest ->
  cnt_ok RP0 M -> cnt_ok RP0 M'.
Proof.
intros RP0 L M M' rest H1 H2 H. unfold cnt_ok in *.
apply (cnt_ok_pk_mono RP0 (fun _ => 0%nat) (fun _ => 0%nat) M M'); [|exact H].
intros P. cbv beta. rewrite (acnt_perm P _ _ H1), (acnt_perm P _ _ H2), acnt_app. lia.
Qed.
Lemma sr_rm_cast : forall RP0 S0 (m m' : nat), rp_RM RP0 S0 m -> m = m' -> rp_RM RP0 S0 m'.
Proof. intros RP0 S0 m m' H <-. exact H. Qed.

Lemma sr_call_lf : forall (LA : Z) (l : hlist) (lines : bool)
(W : world SEGS) regsT memT STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k (o : Z) raw (kr : nat),
LA mod 8 = 0 ->
(forall a, LA <= a < LA + 16 -> inG G a) -> azs B LA 16 -> rom_view SEGS W memT ->
ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md [] lyc Sc Hpc W memT mdc k ->
alist_at B lyc Sc W memT LA l lines ->
mo_ok MT Sc (lf_cost MT l) ->
rp_RM RP Sc (Z.to_nat (lf_cost MT_rk l) + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
getr regsT 10 = w64 LA ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> LF_STK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
s0Z regsT < alloc_ceiling ->
(forall b n, In (b, n) (list_blks l) -> forall i, 0 <= i < req_size n -> inFP FP (b + i)) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_fr_list_free)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 aregs_preserved regsT regs2 /\
 alist_at B ly2 S2 W2 mem2 LA empty_list lines /\
 (forall rest, Permutation (ablocks B lyc Sc) (list_blks l ++ rest) -> Permutation (ablocks B ly2 S2) rest) /\
 apres_kept B W memT W2 mem2 /\
 (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
 frames S2 = frames Sc /\ mo_le MT Sc S2 (lf_cost MT l) /\ rp_RM RP S2 kr /\ cnt_ok RP (ablocks B ly2 S2) /\
 (forall a, inG G a -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memT a) /\
 (forall b n, In (b, n) (ablocks B lyc Sc) ->
  (forall i, 0 <= i < req_size n -> ~ inFP (blk_FP (list_blks l)) (b + i)) ->
  In (b, n) (ablocks B ly2 S2) /\
  (forall i, 0 <= i < req_size n -> aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memT (b + i))) /\
 (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + o - LF_STK <= a < sp0 + o) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros LA l lines W regsT memT STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k o raw kr
HAL8 HGL HZS HROM HJ HL HMO HRM HCNT H10 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hra4 Hs0 HFP.
pose proof HJ as HARc. apply ajournal_gx_AR_x in HARc.
assert (Hsub : forall a, inG (sr_G1 LA) a -> inG G a)
by (intros a Ha; apply HGL; exact (proj1 (sr_G1_in LA a) Ha)).
assert (HG1 : gx_ok SEGS B (sr_G1 LA)) by (exact (gx_ok_sub SEGS B (sr_G1 LA) G Hsub HG)).
assert (HR1 : gx_rt B (sr_G1 LA)) by (exact (gx_rt_sub B (sr_G1 LA) G Hsub HGR)).
assert (HP1 : gx_prog_x B ARx (sr_G1 LA))
by (exact (gx_prog_sub_x B ARx (sr_G1 LA) G Hsub (conj HG (conj HGR (conj HRO (conj GX_ROM (conj GX_W GSHV))))))).
assert (HFPpos : ~ YI16.sink_open_fp (blk_FP (list_blks l)))
by (exact (fp_blocks_pos lyc Sc Hpc W memT mdc l lines LA HARc HL)).
eapply SRr_mono.
{ eapply (aj_gx_call (sr_G1 LA) W regsT memT (BASE + AF_fr_list_free) STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k
    LF_STK (blk_FP (list_blks l)) o raw []
    (fun ly2 S2 W2 regs2 mem2 md2 k1 =>
       alist_at B ly2 S2 W2 mem2 LA empty_list lines /\
       (forall rest, Permutation (ablocks B lyc Sc) (list_blks l ++ rest) -> Permutation (ablocks B ly2 S2) rest) /\
       apres_kept B W memT W2 mem2 /\
       (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
       frames S2 = frames Sc /\ mo_le MT Sc S2 (lf_cost MT l) /\ rp_RM RP S2 kr)
    Hsub HJ Hsp Hal Hneg ltac:(unfold LF_STK, ASTACK; lia) Hbud Hgp Htp Hra Hraw Hra4
    ltac:(apply achain_low; exact Hs0)).
  - intros HPRE1. eapply SRr_mono.
    { exact (LF (sr_G1 LA) HP1 W lyc Sc Hpc regsT memT mdc [] LA l lines HPRE1 H10 HAL8 HL
        ltac:(intros a Ha; apply (proj2 (sr_G1_in LA a)); exact Ha) HZS HROM HMO kr HRM HCNT). }
    cbv beta. unfold lf_post_x.
    intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & -> & HJ2 & HP2 & HAL & HPerm & HPK & HER & HFr & HMLE & HRM2).
    exists ly2, S2, Hp2, regs2, mem2, md2, kk.
    split; [rewrite Hra; reflexivity|]. split; [rewrite <- Hsp; exact HJ2|].
    split; [exact HP2|]. split; [exact HAL | split; [exact HPerm | split; [exact HPK | split; [exact HER |
      split; [exact HFr | split; [exact HMLE | exact HRM2]]]]]].
  - intros a Ha. left. split.
    + unfold blk_FP in Ha. destruct Ha as (r & Hr & Hra2). apply in_map_iff in Hr.
      destruct Hr as ((b, n) & <- & Hin). cbn [fst snd] in Hra2.
      replace a with (b + (a - b)) by lia. apply (HFP b n Hin). lia.
    + unfold blk_FP in Ha. destruct Ha as (r & Hr & Hra2). apply in_map_iff in Hr.
      destruct Hr as ((b, n) & <- & Hin). cbn [fst snd] in Hra2.
      exists b, n. split; [exact (alist_blks_in lyc Sc W memT LA l lines HL b n Hin) | lia]. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJa & HJb & HP & HAL & HPerm & HPK & HER & HFr & HMLE & HRM2).
exists ly2, S2, Hp2, regs2, mem2, md2, k1.
split; [reflexivity|]. split; [exact HJa|]. split; [exact HP|]. split; [exact HAL|].
split; [exact HPerm|]. split; [exact HPK|]. split; [exact HER|]. split; [exact HFr|]. split; [exact HMLE|].
split; [exact HRM2|].
split.
{ destruct (perm_of_incl_nodup (list_blks l) (ablocks B lyc Sc) (list_blks_nodup lyc Sc W memT LA l lines HL)
    (alist_blks_in lyc Sc W memT LA l lines HL)) as (rest & Hrest).
  exact (sr_cnt_rest RP _ _ _ _ Hrest (HPerm rest Hrest) HCNT). }
split.
{ intros a Ha Hno. apply (gx_keep_img (sr_G1 LA) LF_STK (sp0 + o) (blk_FP (list_blks l)) lyc Sc Hpc W memT mdc
    ly2 S2 Hp2 W2 mem2 md2 k1 Hsub HFPpos HJb a Ha).
  intros Hc. exact (Hno (proj1 (sr_G1_in LA a) Hc)). }
split.
{ intros b n Hin Hno. exact (gx_keep_blk (sr_G1 LA) LF_STK (sp0 + o) (blk_FP (list_blks l)) lyc Sc Hpc W memT mdc
    ly2 S2 Hp2 W2 mem2 md2 k1 b n Hsub HARc HJb Hin Hno). }
intros a Ha Hno.
exact (gx_keep_hi (sr_G1 LA) LF_STK (sp0 + o) (blk_FP (list_blks l)) lyc Sc Hpc W memT mdc ly2 S2 Hp2 W2 mem2 md2 k1
  Hsub HJb a Ha Hno).
Qed.

(* ---------------------------------------------------------------- the entry state *)
Definition sr_Bx : sv := SOff 33 0.
Definition SR_FRAME : Z := 32.
Definition sr_regions : smem := [ stack_region SR_FRAME; got_regionP; bcell_regionP 33 ].
Definition sr_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0x10000 (0x5fb000 - 96) 0);
(32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_sr : sstate := mkSS A_source_reset sr_atoms sr_regions None sr_facts.
Definition sr_SH : list shent := [].
Definition sr_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition sr_extra (p : Z) : list word := map (Z_to_bv 64) [p; SB].
Definition sr_preg : YP09.region :=
YP09.mkRegion (Some 10%nat) 40 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 32 0))].

Lemma sr_HA_range : forall HA, (forall a, HA <= a < HA + ASRC -> inG G a) -> 0x10000 <= HA /\ HA + 96 <= 0x5fb000.
Proof.
intros HA HGL. pose proof (inG_img HA (HGL HA ltac:(unfold ASRC; lia))) as H1.
pose proof (inG_img (HA + 95) (HGL (HA + 95) ltac:(unfold ASRC; lia))) as H2. lia.
Qed.

Lemma sr_entry : forall W ly S Hp regs mem md ch HA (op : option hsrc),
afn_pre_x SEGS B ARx SR_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 HA ->
(forall a, HA <= a < HA + ASRC -> inG G a) -> 0 <= sr_p op < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (sr_extra (sr_p op)))) ss_sr
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_source_resetP) mem (seg_rom SEGS)))
/\ sh_ok SEGS sr_Bx sr_SH (Eimg (Ereg regs (sr_extra (sr_p op)))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch HA op HPRE H10 HGL Rp.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (sr_HA_range HA HGL) as HAR0.
assert (WS : SR_STK = 16496) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (sr_extra (sr_p op)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 HA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (sr_p op)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E273 : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
split.
- unfold ss_sr, A_source_resetP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold sr_regions, stack_region, got_regionP, bcell_regionP, SR_FRAME.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o0 Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o0 Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
[cbn [sv_denot]; rewrite E273, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia). split; [lia|]. split; [lia|]. split; [intros o0 Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 sr_Bx SB);
[cbn [sv_denot sr_Bx]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ apply pairwise_disjoint_of_extents. unfold sr_regions, stack_region, got_regionP, bcell_regionP, extent_of_region, SR_FRAME.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia). cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [sr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 HAR0 Rp. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, sr_SH. constructor.
Qed.

(* ---------------------------------------------------------------- bookkeeping across one call *)
Lemma apresent_of_grows : forall (H : word -> bool) (m1 m2 : word -> option byte) a,
mem_grows (mrestrict H m1) (mrestrict H m2) -> apresent H m1 a -> apresent H m2 a.
Proof.
intros H m1 m2 a Hgr [Hh [b Hb]]. split; [exact Hh|].
pose proof (Hgr (Z_to_bv 64 a)) as Hx. unfold mrestrict in Hx. rewrite Hh in Hx. cbn in Hx. rewrite Hb in Hx.
destruct (m2 (Z_to_bv 64 a)) as [b2|] eqn:E2; [exists b2; reflexivity|].
exfalso. apply Hx; [discriminate | first [exact E2 | reflexivity]].
Qed.
Lemma gx_pres : forall G0 STK sp0 FP ly S Hp (W0 : world SEGS) mem md own ly' S' Hp' (W' : world SEGS) mem' md' k,
ajournal_gx_x SEGS B PST ARx G0 0 [] STK sp0 FP ly S Hp W0 mem md own ly' S' Hp' W' mem' md' k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros G0 STK sp0 FP ly S Hp W0 mem md own ly' S' Hp' W' mem' md' k HJ a Ha.
destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _). exact (Hpr a Ha).
Qed.
Lemma blk_writable : forall ly S Hp (W : world SEGS) mem md b n,
ARx ly S Hp W mem md -> In (b, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n ->
writable_at SEGS (mrestrict (w_H W) mem) (b + i).
Proof.
intros ly S Hp W mem md b n HAR Hin i Hi. apply (apresent_writable SEGS).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n HAR Hin) as (_ & _ & _ & _ & Hpr & _).
exact (proj1 (Hpr (b + i) ltac:(lia))).
Qed.
Lemma blk_bounds : forall ly S Hp (W : world SEGS) mem md b n,
ARx ly S Hp W mem md -> In (b, n) (ablocks B ly S) -> 4096 <= b /\ b + req_size n <= alloc_ceiling.
Proof.
intros ly S Hp W mem md b n HAR Hin.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n HAR Hin) as (_ & H1 & H2 & _). lia.
Qed.
(* a list that list_free did not touch survives the call *)
Lemma sr_list_across : forall (lf : hlist) (LF0 : Z) (l : hlist) (LA : Z) (lines : bool)
lyc Sc Hpc (Wc : world SEGS) memc mdc ly' S' (W' : world SEGS) mem',
ARx lyc Sc Hpc Wc memc mdc ->
alist_at B lyc Sc Wc memc LA l lines ->
(forall b n, In (b, n) (list_blks lf) -> In (b, n) (ablocks B lyc Sc)) ->
(forall x, In x (list_blocks l) -> In x (list_blocks lf) -> False) ->
(forall a, LA <= a < LA + 16 -> inG G a) ->
(forall a, LA <= a < LA + 16 -> ~ (LF0 <= a < LF0 + 16)) ->
(forall a, inG G a -> ~ (LF0 <= a < LF0 + 16) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H Wc) memc a) ->
(forall b n, In (b, n) (ablocks B lyc Sc) ->
 (forall i, 0 <= i < req_size n -> ~ inFP (blk_FP (list_blks lf)) (b + i)) ->
 In (b, n) (ablocks B ly' S') /\
 (forall i, 0 <= i < req_size n -> aview SEGS (w_H W') mem' (b + i) = aview SEGS (w_H Wc) memc (b + i))) ->
(forall b n, In (b, n) (ablocks B ly' S') -> forall i, 0 <= i < req_size n ->
 writable_at SEGS (mrestrict (w_H W') mem') (b + i)) ->
alist_at B ly' S' W' mem' LA l lines.
Proof.
intros lf LF0 l LA lines lyc Sc Hpc Wc memc mdc ly' S' W' mem' HARc HL Hsublf Hapart HGL HLdis HKG HKB HW.
assert (Hsub : forall b n, In (b, n) (list_blks l) -> In (b, n) (ablocks B lyc Sc))
by (intros b n Hin; exact (alist_blks_in lyc Sc Wc memc LA l lines HL b n Hin)).
assert (Hno : forall b n, In (b, n) (list_blks l) -> forall i, 0 <= i < req_size n ->
  ~ inFP (blk_FP (list_blks lf)) (b + i)).
{ intros b n Hin i Hi.
  apply (blks_not_in_fp lyc Sc Hpc Wc memc mdc lf b n HARc Hsublf (Hsub b n Hin)); [|exact Hi].
  intros Hc. apply (Hapart b); [rewrite <- map_fst_list_blks; exact (in_map fst _ _ Hin) | exact Hc]. }
apply (alist_kept_gen lyc Sc Wc memc ly' S' W' mem' LA l lines HL).
- intros b n Hin. exact (proj1 (HKB b n (Hsub b n Hin) (Hno b n Hin))).
- exact HGL.
- intros a Ha. exact (HKG a (HGL a Ha) (HLdis a Ha)).
- intros b n Hin i Hi.
  destruct (HKB b n (Hsub b n Hin) (Hno b n Hin)) as [Hin' Hv].
  split; [exact (Hv i Hi) | exact (HW b n Hin' i Hi)].
Qed.
Lemma apres_kept_trans : forall (W1 W2 W3 : world SEGS) m1 m2 m3,
apres_kept B W1 m1 W2 m2 -> apres_kept B W2 m2 W3 m3 -> apres_kept B W1 m1 W3 m3.
Proof. intros W1 W2 W3 m1 m2 m3 H12 H23 a Hi Ho He Hp. exact (H23 a Hi Ho He (H12 a Hi Ho He Hp)). Qed.
Lemma apres_kept_of_pres : forall (W1 W2 : world SEGS) m1 m2,
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) -> apres_kept B W1 m1 W2 m2.
Proof. intros W1 W2 m1 m2 H a _ _ _ Hp. exact (H a Hp). Qed.
(* the block of s->partial survives a call of list_free *)
Lemma sr_blk_across : forall (lf : hlist) lyc Sc Hpc (Wc : world SEGS) memc mdc ly' S' (W' : world SEGS) mem' p n,
ARx lyc Sc Hpc Wc memc mdc ->
(forall b m, In (b, m) (list_blks lf) -> In (b, m) (ablocks B lyc Sc)) ->
~ In p (list_blocks lf) ->
In (p, n) (ablocks B lyc Sc) ->
(forall b m, In (b, m) (ablocks B lyc Sc) ->
 (forall i, 0 <= i < req_size m -> ~ inFP (blk_FP (list_blks lf)) (b + i)) ->
 In (b, m) (ablocks B ly' S') /\
 (forall i, 0 <= i < req_size m -> aview SEGS (w_H W') mem' (b + i) = aview SEGS (w_H Wc) memc (b + i))) ->
In (p, n) (ablocks B ly' S').
Proof.
intros lf lyc Sc Hpc Wc memc mdc ly' S' W' mem' p n HARc Hsublf Hnp Hin HKB.
exact (proj1 (HKB p n Hin (blks_not_in_fp lyc Sc Hpc Wc memc mdc lf p n HARc Hsublf Hin Hnp))).
Qed.

(* two journal facts at the walk's G, with their journal arguments implicit *)
Lemma sr_gx_AR : forall {STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k},
ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ARx ly' S' Hp' W' mem' md'.
Proof. intros * HJ. exact (ajournal_gx_AR_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). Qed.
Lemma sr_rom_view : forall {STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k},
ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
rom_view SEGS W mem -> rom_view SEGS W' mem'.
Proof.
intros * HJ Hrv. eapply ajournal_gx_rom_view_x;
first [exact LAWS | exact pa_segs_low | exact HJ | exact HRO | exact sr_pstr | exact Hrv].
Qed.
(* ---------------------------------------------------------------- the walk *)
Theorem pb_source_reset_x : sr_spec_x B PST ARx MT RP G A_source_resetP.
Proof.
intros W ly S Hp regs mem md ch HA op HPRE H10 HAL8 HREP HGL HZS HROM HMO kr HRM0 HCNT0.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (sr_HA_range HA HGL) as HARng.
pose proof (mo_free_nonneg MT MLAW) as MF0.
(* errno: four image bytes below kLowMemEnd (PALib's api_env), so below the allocator ceiling and the stack *)
pose proof (proj1 (pal_env B TL)) as [He0 He1].
assert (HEL : forall i, 0 <= i < 4 -> 0 <= as_errno B + i < alloc_ceiling)
by (intros i Hi; clear - He0 He1 C1 Hi; unfold kLowMemEnd in He1; lia).
assert (WS : SR_STK = 16496) by reflexivity.
assert (HC1 : 0 <= lf_cost MT (sr_l1 op)) by (unfold lf_cost, hl_n; apply Z.mul_nonneg_nonneg; lia).
assert (HC2 : 0 <= lf_cost MT (sr_l2 op)) by (unfold lf_cost, hl_n; apply Z.mul_nonneg_nonneg; lia).
assert (HC3 : 0 <= lf_cost MT (sr_l3 op)) by (unfold lf_cost, hl_n; apply Z.mul_nonneg_nonneg; lia).
assert (HCsum : lf_cost MT (sr_l1 op) + lf_cost MT (sr_l2 op) + lf_cost MT (sr_l3 op) + mo_free MT = sr_cost MT op).
{ destruct op as [h|]; cbn [sr_l1 sr_l2 sr_l3 sr_cost]; [reflexivity|].
  unfold lf_cost, hl_n, empty_list. cbn [hl_recs length]. lia. }
(* the room budget: the three lists' list_free budgets and the free of s->partial (W_contract_x.v sr_spec_x) *)
assert (HRK0 : Z.to_nat (sr_cost MT_rk op) =
  (Z.to_nat (lf_cost MT_rk (sr_l1 op)) + Z.to_nat (lf_cost MT_rk (sr_l2 op)) + Z.to_nat (lf_cost MT_rk (sr_l3 op)) + 1)%nat).
{ assert (Hk : forall l, 0 <= lf_cost MT_rk l) by (intros l; unfold lf_cost, hl_n; cbn [mo_free MT_rk]; lia).
  assert (Hs : lf_cost MT_rk (sr_l1 op) + lf_cost MT_rk (sr_l2 op) + lf_cost MT_rk (sr_l3 op) + 1 = sr_cost MT_rk op).
  { destruct op as [h|]; cbn [sr_l1 sr_l2 sr_l3 sr_cost]; [reflexivity|].
    unfold lf_cost, hl_n, empty_list. cbn [hl_recs length mo_free MT_rk]. lia. }
  rewrite <- Hs. pose proof (Hk (sr_l1 op)) as K1. pose proof (Hk (sr_l2 op)) as K2. pose proof (Hk (sr_l3 op)) as K3.
  clear - K1 K2 K3. lia. }
destruct (sr_rep_lists ly S Hp W mem md HA op HAR HREP) as (HL1 & HL2 & HL3 & HVP & HBP).
(* the blocks of the three lists and of s->partial have distinct addresses *)
assert (HD : (forall x, In x (list_blocks (sr_l1 op)) -> In x (list_blocks (sr_l2 op)) -> False) /\
  (forall x, In x (list_blocks (sr_l1 op)) -> In x (list_blocks (sr_l3 op)) -> False) /\
  (forall x, In x (list_blocks (sr_l2 op)) -> In x (list_blocks (sr_l3 op)) -> False) /\
  ~ In (sr_p op) (list_blocks (sr_l1 op)) /\ ~ In (sr_p op) (list_blocks (sr_l2 op)) /\
  ~ In (sr_p op) (list_blocks (sr_l3 op))).
{ destruct op as [h|].
  - pose proof HREP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HN).
    unfold hs_blocks in HN. cbn [sr_l1 sr_l2 sr_l3 sr_p].
    pose proof (nodup_app_disj _ _ HN) as D1. pose proof (nodup_app_right _ _ HN) as HN2.
    pose proof (nodup_app_disj _ _ HN2) as D2. pose proof (nodup_app_right _ _ HN2) as HN3.
    pose proof (nodup_app_disj _ _ HN3) as D3.
    split; [intros x H1 H2; apply (D1 x H1); cbn [app]; right; apply in_or_app; left; exact H2|].
    split; [intros x H1 H2; apply (D1 x H1); cbn [app]; right; apply in_or_app; right; exact H2|].
    split; [exact D3|].
    split; [intros Hc; apply (D1 _ Hc); cbn [app]; left; reflexivity|].
    split; [intros Hc; apply (D2 (hs_partial h) ltac:(left; reflexivity)); apply in_or_app; left; exact Hc|].
    intros Hc. apply (D2 (hs_partial h) ltac:(left; reflexivity)). apply in_or_app. right. exact Hc.
  - cbn [sr_l1 sr_l2 sr_l3 sr_p]. unfold list_blocks, empty_list. cbn [hl_cap hl_v hl_recs map app].
    repeat split; unfold not; intros; match goal with Hx : In _ _ |- _ => cbn in Hx; destruct Hx end. }
destruct HD as (HD12 & HD13 & HD23 & HDp1 & HDp2 & HDp3).
(* the footprint of the walk *)
assert (HFPof : forall b n, In (b, n) (sr_blks op) -> forall i, 0 <= i < req_size n -> inFP (blk_FP (sr_blks op)) (b + i)).
{ intros b n Hin i Hi. exists (b, b + req_size n). split; [|cbn [fst snd]; lia].
  unfold blk_FP. exact (in_map (fun q : Z * Z => (fst q, fst q + req_size (snd q))) _ (b, n) Hin). }
assert (HIN1 : forall b n, In (b, n) (list_blks (sr_l1 op)) -> In (b, n) (sr_blks op)).
{ destruct op as [h|]; cbn [sr_blks sr_l1]; intros b n Hin; [unfold hs_blks; apply in_or_app; left; exact Hin|].
  unfold list_blks, empty_list in Hin. cbn in Hin. destruct Hin. }
assert (HIN2 : forall b n, In (b, n) (list_blks (sr_l2 op)) -> In (b, n) (sr_blks op)).
{ destruct op as [h|]; cbn [sr_blks sr_l2]; intros b n Hin;
  [unfold hs_blks; apply in_or_app; right; cbn [app]; right; apply in_or_app; left; exact Hin|].
  unfold list_blks, empty_list in Hin. cbn in Hin. destruct Hin. }
assert (HIN3 : forall b n, In (b, n) (list_blks (sr_l3 op)) -> In (b, n) (sr_blks op)).
{ destruct op as [h|]; cbn [sr_blks sr_l3]; intros b n Hin;
  [unfold hs_blks; apply in_or_app; right; cbn [app]; right; apply in_or_app; right; exact Hin|].
  unfold list_blks, empty_list in Hin. cbn in Hin. destruct Hin. }
(* the entry *)
assert (Rp : 0 <= sr_p op < 2 ^ 64).
{ destruct op as [h|]; cbn [sr_p] in *; [|lia].
  destruct (blk_bounds ly S Hp W mem md _ _ HAR HBP) as [Hb1 Hb2]. unfold req_size, APARTIAL in Hb2. cbn in Hb2. lia. }
destruct (sr_entry W ly S Hp regs mem md ch HA op HPRE H10 HGL Rp) as [HS SHOK].
pose proof (ajournal_gx_init_x SEGS B PST ARx G 0 [] SR_STK (blk_FP (sr_blks op)) ly S Hp W regs mem md ch HPRE
  ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg regs (sr_extra (sr_p op)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 HA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (sr_p op)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (sr_extra (sr_p op))) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_source_resetP) with (Z_to_bv 64 A_source_resetP).
unfold A_source_resetP, A_source_reset.
(* ---- the prologue, to list_free(&s->pending) ---- *)
paj_run_to_tok_x RUNTO HS HJ SHOK sr_Bspan A_sr_lf. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
(* the prologue wrote only the 32-byte frame *)
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbn [ss_sr sr_regions ss_mem In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]];
  cbn [stack_region got_regionP bcell_regionP SR_FRAME YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite Usp in Hr; unfold SR_FRAME in Hr; apply Hno; lia | lia | lia]. }
assert (KLO0 : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
by (intros a Ha; apply KEEP0; lia).
assert (KG0 : forall a, inG G a -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
by (intros a Ha; apply KLO0; pose proof (inG_lo a Ha) as Hl; unfold kLowMemEnd in Hl; lia).
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) |- _ =>
  assert (PR0 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Hpa; exact (apresent_of_grows (w_H W) mem (ms_mem ms) a Hgr Hpa)) end.
assert (TR0 : forall LA l lines, alist_at B ly S W mem LA l lines -> (forall a, LA <= a < LA + 16 -> inG G a) ->
  alist_at B ly S W (ms_mem ms) LA l lines).
{ intros LA l lines HL HLG. apply (alist_kept_gen ly S W mem ly S W (ms_mem ms) LA l lines HL).
  - exact (alist_blks_in ly S W mem LA l lines HL).
  - exact HLG.
  - intros a Ha. exact (KG0 a (HLG a Ha)).
  - intros b n Hin i Hi. pose proof (alist_blks_in ly S W mem LA l lines HL b n Hin) as Hb.
    destruct (blk_bounds ly S Hp W mem md b n HAR Hb) as [Hb1 Hb2].
    split; [apply KLO0; lia|].
    apply (writable_kept' (w_H W) mem (ms_mem ms) (b + i) (PR0 (b + i))).
    exact (blk_writable ly S Hp W mem md b n HAR Hb i Hi). }
assert (HG16 : forall a, HA + 16 <= a < HA + 16 + 16 -> inG G a) by (intros a Ha; apply HGL; unfold ASRC; lia).
assert (HG64 : forall a, HA + 64 <= a < HA + 64 + 16 -> inG G a) by (intros a Ha; apply HGL; unfold ASRC; lia).
assert (HG80 : forall a, HA + 80 <= a < HA + 80 + 16 -> inG G a) by (intros a Ha; apply HGL; unfold ASRC; lia).
assert (HG40 : forall a, HA + 40 <= a < HA + 48 -> inG G a) by (intros a Ha; apply HGL; unfold ASRC; lia).
pose proof (TR0 _ _ _ HL1 HG16) as HL1a. pose proof (TR0 _ _ _ HL2 HG64) as HL2a. pose proof (TR0 _ _ _ HL3 HG80) as HL3a.
assert (HVPa : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (HA + 40) 8 (sr_p op)).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms)); [|exact HVP].
  intros k0 Hk. apply KG0. apply HG40. cbn in Hk. lia. }
assert (HROMa : rom_view SEGS W (ms_mem ms)) by (exact (sr_rom_view HJ HROM)).
pose proof (sr_gx_AR HJ) as HAR0.
(* ---- list_free(&s->pending) ---- *)
assert (R10 : getr (ms_regs ms) 10 = w64 (HA + 16)).
{ rewrite Q10, E10. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Usp1 : spZ (ms_regs ms) = spZ regs + -32).
{ unfold spZ. rewrite Q2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
assert (S01 : s0Z (ms_regs ms) = HA).
{ unfold s0Z. rewrite Q8, E10. apply unsigned_lit_small. lia. }
assert (HRMa : rp_RM RP S (Z.to_nat (lf_cost MT_rk (sr_l1 op)) +
  (Z.to_nat (lf_cost MT_rk (sr_l2 op)) + Z.to_nat (lf_cost MT_rk (sr_l3 op)) + 1 + kr))).
{ apply (sr_rm_cast RP S _ _ HRM0). rewrite HRK0. clear - kr. lia. }
eapply SRr_bind.
{ eapply (sr_call_lf (HA + 16) (sr_l1 op) false W (ms_regs ms) (ms_mem ms) SR_STK (spZ regs)
    (blk_FP (sr_blks op)) ly S Hp W mem md ly S Hp _ 0 (-32) _
    (Z.to_nat (lf_cost MT_rk (sr_l2 op)) + Z.to_nat (lf_cost MT_rk (sr_l3 op)) + 1 + kr)%nat
    ltac:(clear - HAL8; rewrite Z.add_mod, HAL8 by lia; reflexivity) HG16
    (azs_sub HA ASRC (HA + 16) 16 HZS ltac:(lia) ltac:(unfold ASRC; lia)) HROMa HJ HL1a
    (mok_station MT S S (sr_cost MT op) 0 (lf_cost MT (sr_l1 op)) MLAW HMO (mle_start MT S MLAW) HC1 ltac:(lia))
    HRMa HCNT0
    R10 Usp1 eq_refl ltac:(lia) ltac:(unfold LF_STK, ASTACK; lia)
    ltac:(rewrite Q3, E3; exact Hgp) ltac:(rewrite Q4, E4; exact Htp) Q1
    ltac:(apply ret_ok_codeptr_v; [lia | reflexivity]) ltac:(rewrite unsigned_lit_small by lia; lia)
    ltac:(rewrite S01; lia)
    (fun b n Hin i Hi => HFPof b n (HIN1 b n Hin) i Hi)). }
cbv beta. intros W1 c1 Hwle1
  (ly1 & S1 & Hp1 & regs1 & mem1 & md1 & k1 & -> & HJ1 & HP1 & HAL1 & HPM1 & HPK1 & HER1 & HFR1 & HML1 & HRM1 & HCN1 & KG1 & KB1 & KH1).
pose proof (sr_gx_AR HJ1) as HAR1.
jafter_call_keep_pi HS 34%nat regs1 (mrestrict (w_H W1) mem1) HP1 [0]%nat HS1.
match type of HS1 with ?ty -> _ => assert (HRK : ty); [|specialize (HS1 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  apply (region_kept_sp E W W1 (ms_mem ms) mem1 2%nat (spZ regs) (-32) 0 (-32) 0 _ Usp ltac:(lia) ltac:(lia)).
  - intros a Ha. apply KH1; lia.
  - intros a Ha. apply (gx_pres G SR_STK (spZ regs) _ ly S Hp W mem md [] ly1 S1 Hp1 W1 mem1 md1 _ HJ1). lia. }
clear HS. rewrite <- restrict_mkst_fx in HS1. rename HS1 into HS.
remember (havoc E 34 (map (getr regs1) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m0, (m0 < 34)%nat -> ew Ea m0 = ew E m0) by (intros m0 Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs (sr_extra (sr_p op))) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by (cbv; lia); exact Usp).
assert (SHOKa : sh_ok SEGS sr_Bx sr_SH Ea (mrestrict (w_H W1) mem1)) by (unfold sh_ok, sr_SH; constructor).
(* what the rest of the walk needs, at the state after list_free(&s->pending) *)
assert (HPKa : apres_kept B W mem W1 mem1)
by (exact (apres_kept_trans W W W1 mem (ms_mem ms) mem1 (apres_kept_of_pres W W mem (ms_mem ms) PR0) HPK1)).
assert (HERa : forall i, 0 <= i < 4 ->
  aview SEGS (w_H W1) mem1 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
{ intros i Hi. rewrite (HER1 i Hi). exact (KLO0 _ (HEL i Hi)). }
assert (HAL2 : alist_at B ly1 S1 W1 mem1 (HA + 64) (sr_l2 op) true).
{ apply (sr_list_across (sr_l1 op) (HA + 16) (sr_l2 op) (HA + 64) true ly S Hp W (ms_mem ms) _ ly1 S1 W1 mem1
    HAR0 HL2a (alist_blks_in ly S W (ms_mem ms) (HA + 16) (sr_l1 op) false HL1a)
    (fun x H2 H1 => HD12 x H1 H2) HG64 ltac:(intros a Ha Hc; lia) KG1 KB1
    (fun b n Hin i Hi => blk_writable ly1 S1 Hp1 W1 mem1 md1 b n HAR1 Hin i Hi)). }
assert (HAL3 : alist_at B ly1 S1 W1 mem1 (HA + 80) (sr_l3 op) true).
{ apply (sr_list_across (sr_l1 op) (HA + 16) (sr_l3 op) (HA + 80) true ly S Hp W (ms_mem ms) _ ly1 S1 W1 mem1
    HAR0 HL3a (alist_blks_in ly S W (ms_mem ms) (HA + 16) (sr_l1 op) false HL1a)
    (fun x H3 H1 => HD13 x H1 H3) HG80 ltac:(intros a Ha Hc; lia) KG1 KB1
    (fun b n Hin i Hi => blk_writable ly1 S1 Hp1 W1 mem1 md1 b n HAR1 Hin i Hi)). }
assert (HVP1 : val_mem SEGS (mrestrict (w_H W1) mem1) (HA + 40) 8 (sr_p op)).
{ apply (val_mem_kept SEGS (w_H W) (w_H W1) (ms_mem ms) mem1); [|exact HVPa].
  intros k0 Hk. cbn in Hk. apply KG1; [apply HG40; lia | lia]. }
assert (HBP1 : match op with Some _ => In (sr_p op, APARTIAL) (ablocks B ly1 S1) | None => True end).
{ destruct op as [h|]; [|exact I].
  exact (sr_blk_across (sr_l1 (Some h)) ly S Hp W (ms_mem ms) _ ly1 S1 W1 mem1 (sr_p (Some h)) APARTIAL HAR0
    (alist_blks_in ly S W (ms_mem ms) (HA + 16) (sr_l1 (Some h)) false HL1a) HDp1 HBP KB1). }
clear dependent ms. clear HL1 HL2 HL3 HVP HAL1.
(* ---- list_free(&s->expected) ---- *)
paj_run_to_tok_x RUNTO HS HJ1 SHOKa sr_Bspan A_sr_lf. { apply awr_ok_x_of0. awr_ok_tac. exact Uspa. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hno. apply (aview_kept_out Ea _ (w_H W1) mem1 (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr.
  rewrite Uspa in Hr. apply Hno. lia. }
assert (KLO1 : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
by (intros a Ha; apply KEEP1; lia).
assert (KGr1 : forall a, inG G a -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
by (intros a Ha; apply KLO1; pose proof (inG_lo a Ha) as Hl; unfold kLowMemEnd in Hl; lia).
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W1) mem1) (mrestrict (w_H W1) (ms_mem ms)) |- _ =>
  assert (PR1 : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) (ms_mem ms) a)
  by (intros a Hpa; exact (apresent_of_grows (w_H W1) mem1 (ms_mem ms) a Hgr Hpa)) end.
assert (TR1 : forall LA l lines, alist_at B ly1 S1 W1 mem1 LA l lines -> (forall a, LA <= a < LA + 16 -> inG G a) ->
  alist_at B ly1 S1 W1 (ms_mem ms) LA l lines).
{ intros LA l lines HL HLG. apply (alist_kept_gen ly1 S1 W1 mem1 ly1 S1 W1 (ms_mem ms) LA l lines HL).
  - exact (alist_blks_in ly1 S1 W1 mem1 LA l lines HL).
  - exact HLG.
  - intros a Ha. exact (KGr1 a (HLG a Ha)).
  - intros b n Hin i Hi. pose proof (alist_blks_in ly1 S1 W1 mem1 LA l lines HL b n Hin) as Hb.
    destruct (blk_bounds ly1 S1 Hp1 W1 mem1 md1 b n HAR1 Hb) as [Hb1 Hb2].
    split; [apply KLO1; lia|].
    apply (writable_kept' (w_H W1) mem1 (ms_mem ms) (b + i) (PR1 (b + i))).
    exact (blk_writable ly1 S1 Hp1 W1 mem1 md1 b n HAR1 Hb i Hi). }
pose proof (TR1 _ _ _ HAL2 HG64) as HL2a. pose proof (TR1 _ _ _ HAL3 HG80) as HL3a.
assert (HVPa : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (HA + 40) 8 (sr_p op)).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 (ms_mem ms)); [|exact HVP1].
  intros k0 Hk. apply KGr1. apply HG40. cbn in Hk. lia. }
assert (HROMa : rom_view SEGS W1 (ms_mem ms)) by (exact (sr_rom_view HJ1 HROM)).
pose proof (sr_gx_AR HJ1) as HAR0.
assert (R10 : getr (ms_regs ms) 10 = w64 (HA + 64)).
{ rewrite Q10, OLDa by (cbv; lia). rewrite E10. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Usp1 : spZ (ms_regs ms) = spZ regs + -32).
{ unfold spZ. rewrite Q2, Uspa. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
assert (S01 : s0Z (ms_regs ms) = HA).
{ unfold s0Z. rewrite Q8, OLDa by (cbv; lia). rewrite E10. apply unsigned_lit_small. lia. }
assert (HRMb : rp_RM RP S1 (Z.to_nat (lf_cost MT_rk (sr_l2 op)) + (Z.to_nat (lf_cost MT_rk (sr_l3 op)) + 1 + kr)))
by (apply (sr_rm_cast RP S1 _ _ HRM1); clear - kr; lia).
eapply SRr_bind.
{ eapply (sr_call_lf (HA + 64) (sr_l2 op) true W1 (ms_regs ms) (ms_mem ms) SR_STK (spZ regs)
    (blk_FP (sr_blks op)) ly S Hp W mem md ly1 S1 Hp1 _ (0 + k1) (-32) _ (Z.to_nat (lf_cost MT_rk (sr_l3 op)) + 1 + kr)%nat
    ltac:(clear - HAL8; rewrite Z.add_mod, HAL8 by lia; reflexivity) HG64
    (azs_sub HA ASRC (HA + 64) 16 HZS ltac:(lia) ltac:(unfold ASRC; lia)) HROMa HJ1 HL2a
    (mok_station MT S S1 (sr_cost MT op) (lf_cost MT (sr_l1 op)) (lf_cost MT (sr_l2 op)) MLAW HMO HML1 HC2 ltac:(lia))
    HRMb HCN1
    R10 Usp1 eq_refl ltac:(lia) ltac:(unfold LF_STK, ASTACK; lia)
    ltac:(rewrite Q3, OLDa by (cbv; lia); rewrite E3; exact Hgp) ltac:(rewrite Q4, OLDa by (cbv; lia); rewrite E4; exact Htp) Q1
    ltac:(apply ret_ok_codeptr_v; [lia | reflexivity]) ltac:(rewrite unsigned_lit_small by lia; lia)
    ltac:(rewrite S01; lia)
    (fun b n Hin i Hi => HFPof b n (HIN2 b n Hin) i Hi)). }
cbv beta. intros W2 c2 Hwle2
  (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & -> & HJ2 & HP2 & HAL2b & HPM2 & HPK2 & HER2 & HFR2 & HML2 & HRM2 & HCN2 & KG2 & KB2 & KH2).
pose proof (sr_gx_AR HJ2) as HAR2.
jafter_call_keep_pi HS 50%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  apply (region_kept_sp Ea W1 W2 (ms_mem ms) mem2 2%nat (spZ regs) (-32) 0 (-32) 0 _ Uspa ltac:(lia) ltac:(lia)).
  - intros a Ha. apply KH2; lia.
  - intros a Ha. apply (gx_pres G SR_STK (spZ regs) _ ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 _ HJ2). lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc Ea 50 (map (getr regs2) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m0, (m0 < 34)%nat -> ew Eb m0 = ew E m0)
by (intros m0 Hm; rewrite HEb; rewrite YN3v.ew_havoc_old by lia; apply OLDa; exact Hm).
assert (HAEb : env_agree 32 (Ereg regs (sr_extra (sr_p op))) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by (cbv; lia); exact Usp).
assert (SHOKb : sh_ok SEGS sr_Bx sr_SH Eb (mrestrict (w_H W2) mem2)) by (unfold sh_ok, sr_SH; constructor).
assert (HPKb : apres_kept B W mem W2 mem2)
by (exact (apres_kept_trans W W1 W2 mem (ms_mem ms) mem2
  (apres_kept_trans W W1 W1 mem mem1 (ms_mem ms) HPKa (apres_kept_of_pres W1 W1 mem1 (ms_mem ms) PR1)) HPK2)).
assert (HERb : forall i, 0 <= i < 4 ->
  aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
{ intros i Hi. rewrite (HER2 i Hi), (KLO1 _ (HEL i Hi)). exact (HERa i Hi). }
assert (HAL3b : alist_at B ly2 S2 W2 mem2 (HA + 80) (sr_l3 op) true).
{ apply (sr_list_across (sr_l2 op) (HA + 64) (sr_l3 op) (HA + 80) true ly1 S1 Hp1 W1 (ms_mem ms) _ ly2 S2 W2 mem2
    HAR0 HL3a (alist_blks_in ly1 S1 W1 (ms_mem ms) (HA + 64) (sr_l2 op) true HL2a)
    (fun x H3 H2 => HD23 x H2 H3) HG80 ltac:(intros a Ha Hc; lia) KG2 KB2
    (fun b n Hin i Hi => blk_writable ly2 S2 Hp2 W2 mem2 md2 b n HAR2 Hin i Hi)). }
assert (HVP2 : val_mem SEGS (mrestrict (w_H W2) mem2) (HA + 40) 8 (sr_p op)).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) (ms_mem ms) mem2); [|exact HVPa].
  intros k0 Hk. cbn in Hk. apply KG2; [apply HG40; lia | lia]. }
assert (HBP2 : match op with Some _ => In (sr_p op, APARTIAL) (ablocks B ly2 S2) | None => True end).
{ destruct op as [h|]; [|exact I].
  exact (sr_blk_across (sr_l2 (Some h)) ly1 S1 Hp1 W1 (ms_mem ms) _ ly2 S2 W2 mem2 (sr_p (Some h)) APARTIAL HAR0
    (alist_blks_in ly1 S1 W1 (ms_mem ms) (HA + 64) (sr_l2 (Some h)) true HL2a) HDp2 HBP1 KB2). }
clear dependent ms. clear HAL2 HAL3 HVP1 HAL2b.
(* ---- list_free(&s->held) ---- *)
paj_run_to_tok_x RUNTO HS HJ2 SHOKb sr_Bspan A_sr_lf. { apply awr_ok_x_of0. awr_ok_tac. exact Uspb. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hno. apply (aview_kept_out Eb _ (w_H W2) mem2 (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr.
  rewrite Uspb in Hr. apply Hno. lia. }
assert (KLO2 : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha; apply KEEP2; lia).
assert (KGr2 : forall a, inG G a -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha; apply KLO2; pose proof (inG_lo a Ha) as Hl; unfold kLowMemEnd in Hl; lia).
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms)) |- _ =>
  assert (PR2 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Hpa; exact (apresent_of_grows (w_H W2) mem2 (ms_mem ms) a Hgr Hpa)) end.
assert (HL3a : alist_at B ly2 S2 W2 (ms_mem ms) (HA + 80) (sr_l3 op) true).
{ apply (alist_kept_gen ly2 S2 W2 mem2 ly2 S2 W2 (ms_mem ms) (HA + 80) (sr_l3 op) true HAL3b).
  - exact (alist_blks_in ly2 S2 W2 mem2 (HA + 80) (sr_l3 op) true HAL3b).
  - exact HG80.
  - intros a Ha. exact (KGr2 a (HG80 a Ha)).
  - intros b n Hin i Hi. pose proof (alist_blks_in ly2 S2 W2 mem2 (HA + 80) (sr_l3 op) true HAL3b b n Hin) as Hb.
    destruct (blk_bounds ly2 S2 Hp2 W2 mem2 md2 b n HAR2 Hb) as [Hb1 Hb2].
    split; [apply KLO2; lia|].
    apply (writable_kept' (w_H W2) mem2 (ms_mem ms) (b + i) (PR2 (b + i))).
    exact (blk_writable ly2 S2 Hp2 W2 mem2 md2 b n HAR2 Hb i Hi). }
assert (HVPa : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms)) (HA + 40) 8 (sr_p op)).
{ apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact HVP2].
  intros k0 Hk. apply KGr2. apply HG40. cbn in Hk. lia. }
assert (HROMa : rom_view SEGS W2 (ms_mem ms)) by (exact (sr_rom_view HJ2 HROM)).
pose proof (sr_gx_AR HJ2) as HAR0.
assert (R10 : getr (ms_regs ms) 10 = w64 (HA + 80)).
{ rewrite Q10, OLDb by (cbv; lia). rewrite E10. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Usp1 : spZ (ms_regs ms) = spZ regs + -32).
{ unfold spZ. rewrite Q2, Uspb. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
assert (S01 : s0Z (ms_regs ms) = HA).
{ unfold s0Z. rewrite Q8, OLDb by (cbv; lia). rewrite E10. apply unsigned_lit_small. lia. }
assert (HRMc : rp_RM RP S2 (Z.to_nat (lf_cost MT_rk (sr_l3 op)) + (1 + kr))) by (apply (sr_rm_cast RP S2 _ _ HRM2); clear - kr; lia).
eapply SRr_bind.
{ eapply (sr_call_lf (HA + 80) (sr_l3 op) true W2 (ms_regs ms) (ms_mem ms) SR_STK (spZ regs)
    (blk_FP (sr_blks op)) ly S Hp W mem md ly2 S2 Hp2 _ (0 + k1 + k2) (-32) _ (1 + kr)%nat
    ltac:(clear - HAL8; rewrite Z.add_mod, HAL8 by lia; reflexivity) HG80
    (azs_sub HA ASRC (HA + 80) 16 HZS ltac:(lia) ltac:(unfold ASRC; lia)) HROMa HJ2 HL3a
    (mok_station MT S S2 (sr_cost MT op) (lf_cost MT (sr_l1 op) + lf_cost MT (sr_l2 op)) (lf_cost MT (sr_l3 op)) MLAW HMO
      (mle_station MT S S1 S2 _ _ MLAW HML1 HML2) HC3 ltac:(lia))
    HRMc HCN2
    R10 Usp1 eq_refl ltac:(lia) ltac:(unfold LF_STK, ASTACK; lia)
    ltac:(rewrite Q3, OLDb by (cbv; lia); rewrite E3; exact Hgp) ltac:(rewrite Q4, OLDb by (cbv; lia); rewrite E4; exact Htp) Q1
    ltac:(apply ret_ok_codeptr_v; [lia | reflexivity]) ltac:(rewrite unsigned_lit_small by lia; lia)
    ltac:(rewrite S01; lia)
    (fun b n Hin i Hi => HFPof b n (HIN3 b n Hin) i Hi)). }
cbv beta. intros W3 c3 Hwle3
  (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & -> & HJ3 & HP3 & HAL3c & HPM3 & HPK3 & HER3 & HFR3 & HML3 & HRM3 & HCN3 & KG3 & KB3 & KH3).
pose proof (sr_gx_AR HJ3) as HAR3.
jafter_call_keep_pi HS 66%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  apply (region_kept_sp Eb W2 W3 (ms_mem ms) mem3 2%nat (spZ regs) (-32) 0 (-32) 0 _ Uspb ltac:(lia) ltac:(lia)).
  - intros a Ha. apply KH3; lia.
  - intros a Ha. apply (gx_pres G SR_STK (spZ regs) _ ly S Hp W mem md [] ly3 S3 Hp3 W3 mem3 md3 _ HJ3). lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Eb 66 (map (getr regs3) CLOB)) as Ec eqn:HEc in HS.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
assert (OLDc : forall m0, (m0 < 34)%nat -> ew Ec m0 = ew E m0)
by (intros m0 Hm; rewrite HEc; rewrite YN3v.ew_havoc_old by lia; apply OLDb; exact Hm).
assert (HAEc : env_agree 32 (Ereg regs (sr_extra (sr_p op))) Ec) by (rewrite HEc; apply env_agree_havoc_ge; [cbv; lia | exact HAEb]).
clear HEc.
assert (Uspc : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLDc by (cbv; lia); exact Usp).
assert (HPKc : apres_kept B W mem W3 mem3)
by (exact (apres_kept_trans W W2 W3 mem (ms_mem ms) mem3
  (apres_kept_trans W W2 W2 mem mem2 (ms_mem ms) HPKb (apres_kept_of_pres W2 W2 mem2 (ms_mem ms) PR2)) HPK3)).
assert (HERc : forall i, 0 <= i < 4 ->
  aview SEGS (w_H W3) mem3 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
{ intros i Hi. rewrite (HER3 i Hi), (KLO2 _ (HEL i Hi)). exact (HERb i Hi). }
assert (HVP3 : val_mem SEGS (mrestrict (w_H W3) mem3) (HA + 40) 8 (sr_p op)).
{ apply (val_mem_kept SEGS (w_H W2) (w_H W3) (ms_mem ms) mem3); [|exact HVPa].
  intros k0 Hk. cbn in Hk. apply KG3; [apply HG40; lia | lia]. }
assert (HBP3 : match op with Some _ => In (sr_p op, APARTIAL) (ablocks B ly3 S3) | None => True end).
{ destruct op as [h|]; [|exact I].
  exact (sr_blk_across (sr_l3 (Some h)) ly2 S2 Hp2 W2 (ms_mem ms) _ ly3 S3 W3 mem3 (sr_p (Some h)) APARTIAL HAR0
    (alist_blks_in ly2 S2 W2 (ms_mem ms) (HA + 80) (sr_l3 (Some h)) true HL3a) HDp3 HBP2 KB3). }
clear dependent ms. clear HAL3b HVP2 HAL3c.
(* ---- the shadow-checked load of s->partial, then free(s->partial) ---- *)
assert (Rp3 : 0 <= sr_p op < 2 ^ 64) by exact Rp.
assert (HRG : region_ok SEGS Ec (mrestrict (w_H W3) mem3) sr_preg).
{ unfold region_ok, sr_preg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite OLDc by (cbv; lia). rewrite E10, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o0 Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS Ec _ HA 40 8 _ (sr_p op));
  [cbn [sv_denot]; rewrite OLDc by (cbv; lia); rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact HVP3]. }
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ss ?msx =>
  assert (HDJ : all_disjoint Ev sr_preg (ss_mem ss));
  [ cbn [ss_mem all_disjoint]; split; [|exact I]; unfold extent_disjoint, sr_preg;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Uspc; rewrite OLDc by (cbv; lia);
    rewrite E10, unsigned_lit_small by lia; left; lia
  | pose proof (st_ok_pi_add_region Ev ss msx sr_preg HS eq_refl HRG HDJ) as HS' ] end.
clear HS HDJ. rename HS' into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOKc : sh_ok SEGS sr_Bx sr_SH Ec (mrestrict (w_H W3) mem3)) by (unfold sh_ok, sr_SH; constructor).
paj_run_tok_x RUN HS HJ3 SHOKc sr_Bspan.
{ cbn [ms_mem mkst]. rewrite <- (aview_rd_of SEGS). unfold sr_Bx. rewrite !U_SOff. rewrite !OLDc by (cbv; lia).
  rewrite E10, E33, !unsigned_lit_small by (unfold SB; lia).
  rewrite !zcanon_id by (unfold M64, SB; lia). rewrite Z.add_0_r, SB_SHADOW_OFF.
  exact (azs_range_addressable_x B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 (HA + 40) 8 HAR3
    (azs_sub HA ASRC (HA + 40) 8 HZS ltac:(lia) ltac:(unfold ASRC; lia))). }
{ apply awr_ok_x_of0. awr_ok_tac. exact Uspc. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hno. apply (aview_kept_out Ec _ (w_H W3) mem3 (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [sr_preg YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
  rewrite Uspc in Hr. apply Hno. lia. }
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W3) mem3) (mrestrict (w_H W3) (ms_mem ms)) |- _ =>
  assert (PR3 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms) a)
  by (intros a Hpa; exact (apresent_of_grows (w_H W3) mem3 (ms_mem ms) a Hgr Hpa)) end.
pose proof (sr_gx_AR HJ3) as HAR3m.
assert (Usp4 : spZ (ms_regs ms) = spZ regs + -32).
{ unfold spZ. rewrite Q2, Uspc. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
assert (R10f : getr (ms_regs ms) 10 = w64 (sr_p op)) by (rewrite Q10, OLDc by (cbv; lia); exact E32).
assert (S0f : s0Z (ms_regs ms) = HA).
{ unfold s0Z. rewrite Q8, OLDc by (cbv; lia). rewrite E10. apply unsigned_lit_small. lia. }
assert (HCH : chain_pre ly3 (aview SEGS (w_H W3) (ms_mem ms)) (ms_regs ms) []).
{ unfold chain_pre. split; [unfold raZ; rewrite Q1; rewrite unsigned_lit_small by lia; lia|].
  destruct (frame0_ok ly3 (ms_regs ms)); [|reflexivity].
  replace (bad_next (spZ (ms_regs ms)) (ly_top ly3) (s0Z (ms_regs ms))) with true; [reflexivity|].
  symmetry. unfold bad_next. rewrite S0f, Usp4. apply orb_true_iff. left. apply orb_true_iff. left. apply Z.leb_le. lia. }
(* the free call's trace: s0 holds s, so the chain handed to the rule is [] and the trace is the return address *)
assert (HCX : In (raZ (ms_regs ms) :: spine []) CTX).
{ cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_source_reset + 0x54); [exact HCTX_sr_free|].
  unfold raZ. rewrite Q1, unsigned_lit_small by lia. unfold AF_fr_source_reset. lia. }
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, OLDc by (cbv; lia); rewrite E3; exact Hgp).
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, OLDc by (cbv; lia); rewrite E4; exact Htp).
assert (HML123 : mo_le MT S S3 (lf_cost MT (sr_l1 op) + lf_cost MT (sr_l2 op) + lf_cost MT (sr_l3 op)))
by (exact (mle_station MT S S2 S3 _ _ MLAW (mle_station MT S S1 S2 _ _ MLAW HML1 HML2) HML3)).
assert (HMOf : mo_ok MT S3 (mo_free MT))
by (exact (mok_station MT S S3 (sr_cost MT op) _ (mo_free MT) MLAW HMO HML123 MF0 ltac:(lia))).
destruct HJ3 as (HSTK3 & HXO3 & (memS3 & HJi3 & Hag3) & Hout3). rewrite !Z.add_0_r in HJi3.
rewrite HBfree.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
eapply SRr_bind with (R := fun W4 c4 => exists ly4 S4 Hp4 regs4 mem4 md4,
  c4 = mkCfg (mkst regs4 (getr rg 1) mem4 (seg_rom SEGS)) md4 /\
  (exists kk, ajournal_x SEGS B PST ARx SR_STK (spZ regs) (blk_FP (sr_blks op)) ly S Hp W memS3 md [] ly4 S4 Hp4 W4 mem4 md4 kk) /\
  aregs_preserved rg regs4 /\
  (forall rest, Permutation (ablocks B ly3 S3) ((match op with Some _ => [(sr_p op, APARTIAL)] | None => [] end) ++ rest) ->
   Permutation (ablocks B ly4 S4) rest) /\
  frames S4 = frames S3 /\
  acall_kept SEGS B ly3 S3 W3 mm W4 mem4 (spZ regs + -32 - ASTACK) (spZ regs + -32)
    (fun a => match op with Some _ => sr_p op <= a < sr_p op + req_size APARTIAL | None => False end) /\
  mo_le MT S3 S4 (mo_free MT) /\ rp_RM RP S4 kr /\
  (forall i, 0 <= i < 4 -> aview SEGS (w_H W4) mem4 (as_errno B + i) = aview SEGS (w_H W3) mm (as_errno B + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   apresent (w_H W3) mm a -> apresent (w_H W4) mem4 a))
end.
{ destruct op as [h|] eqn:Eop.
  - eapply SRr_mono.
    { exact (AFREE W3 (ms_regs ms) (ms_mem ms) SR_STK (spZ regs) (blk_FP (sr_blks (Some h))) ly S Hp W memS3 md [] ly3 S3 Hp3 _ _
        (sr_p (Some h)) APARTIAL (-32) (getr (ms_regs ms) 1) [] kr HJi3 HBP3 R10f Usp4 eq_refl ltac:(lia)
        ltac:(unfold SR_STK, LF_STK, ASTACK; lia)
        (aj_stack_room_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-32) (ms_regs ms) HJi3 Usp4 ltac:(unfold SR_STK, LF_STK, ASTACK; lia))
        HGP HTP eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
        HCH HCX HRM3 HCN3 (fun _ i Hi => HFPof _ _ ltac:(unfold sr_blks, hs_blks; apply in_or_app; right; left; reflexivity) i Hi) HMOf). }
    cbv beta.
    intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Eb1 & Eb2) & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [exists (0 + k1 + k2 + k3 + 1); exact HJ4|].
    split; [exact HP4|].
    split.
    { intros rest Hq. rewrite Eb2. rewrite Eb1 in Hq. cbn [app] in Hq.
      apply Permutation_sym in Hq. apply Permutation_cons_app_inv in Hq. exact (Permutation_sym Hq). }
    split; [exact HFr4|]. split; [exact HK4|]. split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Hi Ho He Hpa. pose proof (proj1 HJ4) as HAR4.
    apply (HPr4 a Hi); [exact (inG_not_owned_img ly3 S3 Hp3 W3 (ms_mem ms) _ a HAR3m Hi Ho)
      | exact (inG_not_owned_img ly4 S4 Hp4 W4 mem4 md4 a HAR4 Hi Ho) | exact He | | exact Hpa].
    intros Hblk. destruct (alx_client_img _ _ _ LAWS ly3 S3 Hp3 W3 (ms_mem ms) _ a HAR3m
      ltac:(left; exists (sr_p (Some h)), APARTIAL; split; [exact HBP3 | exact Hblk])) as [_ Hni]. exact (Hni Hi).
  - eapply SRr_mono.
    { exact (AFREEN W3 (ms_regs ms) (ms_mem ms) SR_STK (spZ regs) (blk_FP (sr_blks None)) ly S Hp W memS3 md [] ly3 S3 Hp3 _ _
        (-32) (getr (ms_regs ms) 1) [] kr HJi3 R10f Usp4 eq_refl ltac:(lia)
        ltac:(unfold SR_STK, LF_STK, ASTACK; lia)
        (aj_stack_room_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-32) (ms_regs ms) HJi3 Usp4 ltac:(unfold SR_STK, LF_STK, ASTACK; lia))
        HGP HTP eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
        HCH HCX HRM3 HCN3 HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPm & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [exists (0 + k1 + k2 + k3 + 1); exact HJ4|].
    split; [exact HP4|].
    split; [intros rest Hq; cbn [app] in Hq; exact (Permutation_trans HPm Hq)|].
    split; [exact HFr4|]. split; [exact HK4|]. split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Hi Ho He Hpa. pose proof (proj1 HJ4) as HAR4.
    exact (HPr4 a Hi (inG_not_owned_img ly3 S3 Hp3 W3 (ms_mem ms) _ a HAR3m Hi Ho)
      (inG_not_owned_img ly4 S4 Hp4 W4 mem4 md4 a HAR4 Hi Ho) He Hpa). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & (kk4 & HJi4) & HP4 & HPM4 & HFR4 & HK4 & HML4 & HRM4 & HER4 & HPR4).
rewrite Q1.
assert (HJ4 : ajournal_gx_x SEGS B PST ARx G 0 [] SR_STK (spZ regs) (blk_FP (sr_blks op)) ly S Hp W mem md [] ly4 S4 Hp4 W4 mem4 md4 kk4).
{ apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] SR_STK (spZ regs) _ ly S Hp W mem md [] ly4 S4 Hp4 W4 mem4 md4 kk4 memS3 HSTK3 HXO3);
  [rewrite !Z.add_0_r; exact HJi4 | exact Hag3 | intros a Ha _; lia]. }
jafter_call_keep_pi HS 82%nat regs4 (mrestrict (w_H W4) mem4) HP4 [1]%nat HS4.
match type of HS4 with ?ty -> _ => assert (HRK : ty); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  lazymatch goal with |- region_kept _ ?Ev _ _ _ =>
    apply (region_kept_sp Ev W3 W4 (ms_mem ms) mem4 2%nat (spZ regs) (-32) 0 (-32) 0 _
      ltac:(repeat (rewrite ew_ewset_other by lia); exact Uspc) ltac:(lia) ltac:(lia)) end.
  - intros a Ha. destruct HK4 as (K1 & _). apply K1; lia.
  - intros a Ha. apply (gx_pres G SR_STK (spZ regs) _ ly S Hp W mem md [] ly4 S4 Hp4 W4 mem4 md4 _ HJ4). lia. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Eh _ _ => remember Eh as Ed eqn:HEd in HS end.
assert (HEId : img_env VAL A_LIM Ed)
by (rewrite HEd; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLDd : forall m0, (m0 < 34)%nat -> ew Ed m0 = ew E m0)
by (intros m0 Hm; rewrite HEd; rewrite YN3v.ew_havoc_old by lia; repeat (rewrite ew_ewset_other by lia); apply OLDc; exact Hm).
assert (HAEd : env_agree 32 (Ereg regs (sr_extra (sr_p op))) Ed).
{ rewrite HEd. apply env_agree_havoc_ge; [cbv; lia|].
  split; [intros m Hm; repeat (rewrite ew_ewset_other by lia); exact (proj1 HAEc m Hm)
        | repeat (rewrite ed_ewset); exact (proj2 HAEc)]. }
assert (Uspd : bv_unsigned (ew Ed 2) = spZ regs) by (rewrite OLDd by (cbv; lia); exact Usp).
assert (HPKd : apres_kept B W mem W4 mem4)
by (exact (apres_kept_trans W W3 W4 mem (ms_mem ms) mem4
  (apres_kept_trans W W3 W3 mem mem3 (ms_mem ms) HPKc (apres_kept_of_pres W3 W3 mem3 (ms_mem ms) PR3)) HPR4)).
assert (HERd : forall i, 0 <= i < 4 ->
  aview SEGS (w_H W4) mem4 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
{ intros i Hi. pose proof (HEL i Hi) as Hei. rewrite (HER4 i Hi).
  rewrite (KEEP3 (as_errno B + i) ltac:(lia) ltac:(lia)). exact (HERc i Hi). }
clear HEd. clear dependent ms.
assert (SHOKd : sh_ok SEGS sr_Bx sr_SH Ed (mrestrict (w_H W4) mem4)) by (unfold sh_ok, sr_SH; constructor).
(* ---- __asan_memset(s, 0, 96) ---- *)
paj_run_tok_x RUN HS HJ4 SHOKd sr_Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Uspd. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
(* this run writes only the frame: errno keeps its view *)
assert (KEm : forall i, 0 <= i < 4 ->
  aview SEGS (w_H W4) (ms_mem ms) (as_errno B + i) = aview SEGS (w_H W4) mem4 (as_errno B + i)).
{ intros i Hi. pose proof (HEL i Hi) as Hei.
  apply (aview_kept_out Ed _ (w_H W4) mem4 (ms_mem ms) HFr (as_errno B + i) ltac:(lia)).
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr.
  rewrite Uspd in Hr. lia. }
pose proof (sr_gx_AR HJ4) as HAR4.
assert (Uspm : spZ (ms_regs ms) = spZ regs + -32).
{ unfold spZ. rewrite P2, Uspd. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
assert (HdG96 : forall a, HA <= a < HA + 96 -> inG G a) by (intros a Ha; apply HGL; unfold ASRC; lia).
eapply SRr_bind.
{ eapply (aj_set_gx_at (SIGMA WS_asan_memset) AMEMSET W4 (ms_regs ms) (ms_mem ms) SR_STK (spZ regs)
    (blk_FP (sr_blks op)) ly S Hp W mem md [] ly4 S4 Hp4 _ kk4 HA 0 96 (-32) (Z_to_bv 64 (BASE + 13524)) HJ4);
  [ rewrite P10, OLDd by (cbv; lia); exact E10
  | rewrite P11; reflexivity
  | rewrite P12; reflexivity
  | lia | lia | unfold ASRC in HARng; lia
  | exact Uspm | reflexivity | lia | unfold SR_STK, LF_STK, ASTACK, ESTACK; lia
  | rewrite P3, OLDd by (cbv; lia); rewrite E3; exact Hgp | rewrite P4, OLDd by (cbv; lia); rewrite E4; exact Htp
  | rewrite P1; reflexivity | apply ret_ok_codeptr_v; [lia | reflexivity]
  | exact HdG96
  | left; unfold kLowMemEnd in *; lia
  | exact (azs_range_addressable_x B ARx LAWS ly4 S4 Hp4 W4 (ms_mem ms) _ HA 96 HAR4
      (azs_sub HA ASRC HA 96 HZS ltac:(lia) ltac:(unfold ASRC; lia)))
  | intros _; exact (GSHV ly4 S4 Hp4 W4 (ms_mem ms) _ HA 96 HAR4 ltac:(lia) HdG96) ]. }
cbv beta. intros W5 c5 Hwle5 (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HZv & HFrm & HPRm).
(* after the memset: the 96 bytes of the source are zero *)
assert (HPKrun : forall a, apresent (w_H W4) mem4 a -> apresent (w_H W4) (ms_mem ms) a).
{ lazymatch goal with Hgr : mem_grows (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem ms)) |- _ =>
    intros a Hpa; exact (apresent_of_grows (w_H W4) mem4 (ms_mem ms) a Hgr Hpa) end. }
assert (HPKm : apres_kept B W mem W4 mem5).
{ eapply apres_kept_trans; [exact HPKd|].
  eapply apres_kept_trans; [apply apres_kept_of_pres; exact HPKrun | apply apres_kept_of_pres; exact HPRm]. }
(* errno is not a byte of the source (gx_rt keeps it out of G), nor of the stack *)
assert (HERm : forall i, 0 <= i < 4 ->
  aview SEGS (w_H W4) mem5 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
{ intros i Hi. pose proof (HEL i Hi) as Hei.
  rewrite (HFrm (as_errno B + i) ltac:(lia)
    ltac:(intros Hd; exact (proj1 (HGR (as_errno B + i) (HdG96 _ Hd)) ltac:(lia)))
    ltac:(unfold ESTACK; lia)).
  rewrite (KEm i Hi). exact (HERd i Hi). }
(* asrc_closed is re-established at the ret memory below; HZv (the zero view at mem5) carries there *)
jafter_call_keep_pi HS 98%nat regs5 (mrestrict (w_H W4) mem5) HP5 [0]%nat HS5.
match type of HS5 with ?ty -> _ => assert (HRK : ty); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  apply (region_kept_sp Ed W4 W4 (ms_mem ms) mem5 2%nat (spZ regs) (-32) 0 (-32) 0 _ Uspd ltac:(lia) ltac:(lia)).
  - intros a Ha. apply HFrm; [lia | intros [HA1 HA2]; lia | unfold ESTACK; intros [HA1 HA2]; lia].
  - intros a Ha. apply (gx_pres G SR_STK (spZ regs) _ ly S Hp W mem md [] ly4 S4 Hp4 W4 mem5 md5 _ HJ5). lia. }
clear HS. rewrite <- restrict_mkst_fx in HS5. rename HS5 into HS.
remember (havoc Ed 98 (map (getr regs5) CLOB)) as Ee eqn:HEe in HS.
assert (HEIe : img_env VAL A_LIM Ee) by (rewrite HEe; apply img_env_havoc; [exact HEId | cbv; lia]).
assert (OLDe : forall m0, (m0 < 34)%nat -> ew Ee m0 = ew E m0)
by (intros m0 Hm; rewrite HEe; rewrite YN3v.ew_havoc_old by lia; apply OLDd; exact Hm).
assert (HAEe : env_agree 32 (Ereg regs (sr_extra (sr_p op))) Ee) by (rewrite HEe; apply env_agree_havoc_ge; [cbv; lia | exact HAEd]).
clear HEe. clear dependent ms.
assert (SHOKe : sh_ok SEGS sr_Bx sr_SH Ee (mrestrict (w_H W4) mem5)) by (unfold sh_ok, sr_SH; constructor).
(* ---- the epilogue and ret ---- *)
paj_run_tok_x RUN HS HJ5 SHOKe sr_Bspan. { apply awr_ok_x_of0. awr_ok_tac. rewrite OLDe by (cbv; lia); exact Usp. }
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
assert (Uspe : bv_unsigned (ew Ee 2) = spZ regs) by (rewrite OLDe by (cbv; lia); exact Usp).
assert (KEEPep : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview SEGS (w_H W4) (ms_mem ms) a = aview SEGS (w_H W4) mem5 a).
{ intros a Ha Hno. apply (aview_kept_out Ee _ (w_H W4) mem5 (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr.
  rewrite Uspe in Hr. apply Hno. lia. }
assert (HALT : forall i, 0 <= i < 96 -> ~ (spZ regs - 32 <= HA + i < spZ regs)).
{ intros i Hi [HA1 HA2].
  pose proof (inG_lo (HA + i) (HGL (HA + i) ltac:(unfold ASRC; lia))) as Hl.
  unfold kLowMemEnd in Hl. unfold SR_STK, LF_STK, ASTACK in *. lia. }
assert (HCLOSEDf : asrc_closed W4 (ms_mem ms) HA).
{ unfold asrc_closed, arm. split.
  - replace (Z.to_nat ASRC) with 96%nat by (unfold ASRC; reflexivity).
    apply (garr8_of_zero_view W4 (ms_mem ms) HA 96). intros i Hi.
    rewrite KEEPep by (first [lia | exact (HALT i Hi)]).
    replace 0 with (0 mod 256) by reflexivity. exact (HZv i Hi).
  - intros i Hi. unfold ASRC in Hi. exact (GX_W (HA + i) (HGL (HA + i) ltac:(unfold ASRC; lia)) _). }
eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold sr_post_x.
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly4, S4, Hp4, r, m, d, kk4 end.
split; [cbn [ms_regs]; rewrite R1; rewrite OLDe by (cbv; lia); rewrite E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS pa_segs_low); exact HJ5|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ Ee _ _ regs (sr_extra (sr_p op)) HS); [exact HAEe | vm_compute; reflexivity]|].
split; [exact HCLOSEDf|].
split.
{ intros rest Hq. destruct op as [h|].
  - cbn [sr_blks] in Hq. unfold hs_blks in Hq. cbn [sr_l1 sr_l2 sr_l3 sr_p] in *.
    rewrite <- !app_assoc in Hq.
    pose proof (HPM1 _ Hq) as Hq1.
    pose proof (HPM2 _ (Permutation_trans Hq1
      (Permutation_middle (list_blks (hs_expected h)) (list_blks (hs_held h) ++ rest) (hs_partial h, APARTIAL)))) as Hq2.
    pose proof (HPM3 _ (Permutation_trans Hq2
      (Permutation_middle (list_blks (hs_held h)) rest (hs_partial h, APARTIAL)))) as Hq3.
    exact (HPM4 rest Hq3).
  - cbn [sr_blks sr_l1 sr_l2 sr_l3] in *. cbn [app] in Hq.
    unfold list_blks, empty_list in *. cbn [hl_cap hl_v hl_recs map app Z.eqb Pos.eqb] in *.
    exact (HPM4 rest (HPM3 rest (HPM2 rest (HPM1 rest Hq)))). }
split.
{ eapply apres_kept_trans; [exact HPKm | apply apres_kept_of_pres].
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H W4) mem5) (mrestrict (w_H W4) (ms_mem ms)) |- _ =>
    intros a Hpa; exact (apresent_of_grows (w_H W4) mem5 (ms_mem ms) a Hgr Hpa) end. }
split.
{ intros i Hi. transitivity (aview SEGS (w_H W4) mem5 (as_errno B + i)); [|exact (HERm i Hi)].
  pose proof (HEL i Hi) as Hei. apply KEEPep; lia. }
split; [rewrite HFR4, HFR3, HFR2, HFR1; reflexivity|].
split; [rewrite <- HCsum; exact (mle_station MT S S3 S4 _ _ MLAW HML123 HML4) | exact HRM4].
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): source_reset's walk at a world relation R.  Each <name>_xR below is <name> above
   with the journal `ajournal_gx_x SEGS B PST ARx` -> `ajournal_gx_xR SEGS B PST ARx R` (and `ajournal_x` ->
   `ajournal_xR .. R`), `SRr SEGS` -> `SRrG SEGS R`, the journal / call-step lemmas -> their R twins (W_journal_x.v,
   YCbqG.v, W_sites_x.v: ajournal_gx_*_xR, ajournal_x_after_writeR, ajournal_rebase_xR, ecall_pre_at_xR,
   afn_pre_x_atR), the runs -> paj_run_x_xG / paj_run_to_x_xG with paj_run_tok_xR / paj_run_to_tok_xR, the binds ->
   SRrG_bind SEGS R R_trans / SRrG_mono SEGS R, the return -> the strict step lifted by SRr_SRrG (WLE_R), and the calls
   -> their R forms: list_free LF_R := lf_spec_g_xR (W_contract_srlf_xR.v; a Theorem Labs lane's G6 proves it as
   pb_list_free_g_xR), free / free(NULL) AFREE_R / AFREEN_R := afree_cf_rule_c_xR / afree_null_cf_rule_c_xR .. RO CTX R
   (their RO call-boundary premise from ARx at the call state, RO_ARx; part 3c removed their memnorm premise), memset
   AMEMSET_R := aintrin_realizes_xR .. R OSet (a Theorem Labs lane e4c815100c57; aintrin_realizes_xR_of_x gives it from the
   strict rule).
   Every other token is the strict text's.  The strict pb_source_reset_x above keeps its proof. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis LF_R : lf_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_list_free).
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Hypothesis AMEMSET_R : aintrin_realizes_xR SEGS B ARx R OSet (SIGMA WS_asan_memset).
Let RUNG := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG 0 [].
(* ---------------------------------------------------------------- what a callee's journal keeps *)
(* :319 gx_keep_hi (line at 3a15e3071e9) *)
Lemma gx_keep_hi_xR : forall G1 STK1 sp1 FP1 lyc Sc Hpc (W : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
(forall a, inG G1 a -> inG G a) ->
ajournal_gx_xR SEGS B PST ARx R G1 0 [] STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 Hsub HJ a Ha Hno.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
rewrite (F1 a Ha Hno). apply (aview_gagree SEGS G1 (w_H W) memc memS a Hag).
apply (proj2 (inGb_false G1 _)). rewrite unsigned_lit_small by lia.
intros Hc. pose proof (inG_lo a (Hsub a Hc)). unfold kLowMemEnd in *. lia.
Qed.
(* :333 gx_keep_img (line at 3a15e3071e9) *)
Lemma gx_keep_img_xR : forall G1 STK1 sp1 FP1 lyc Sc Hpc (W : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
(forall a, inG G1 a -> inG G a) -> ~ YI16.sink_open_fp FP1 ->
ajournal_gx_xR SEGS B PST ARx R G1 0 [] STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
forall a, inG G a -> ~ inG G1 a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 Hsub Hfp HJ a Ha Hna.
destruct HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof (inG_lo a Ha) as Hlo.
rewrite (F3 a (proj1 (HG a Ha)) (proj1 (proj2 (HG a Ha))) (proj1 (HGR a Ha)) (HPST a (proj1 (HG a Ha)))
  ltac:(intros Hso; exfalso; exact (Hfp Hso))).
apply (aview_gagree SEGS G1 (w_H W) memc memS a Hag).
apply (proj2 (inGb_false G1 _)). rewrite unsigned_lit_small by (unfold kLowMemEnd in *; lia). exact Hna.
Qed.
(* :347 gx_keep_blk (line at 3a15e3071e9) *)
Lemma gx_keep_blk_xR : forall G1 STK1 sp1 FP1 lyc Sc Hpc (W : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 p n,
(forall a, inG G1 a -> inG G a) ->
ARx lyc Sc Hpc W memc mdc ->
ajournal_gx_xR SEGS B PST ARx R G1 0 [] STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
In (p, n) (ablocks B lyc Sc) -> (forall i, 0 <= i < req_size n -> ~ inFP FP1 (p + i)) ->
In (p, n) (ablocks B ly2 S2) /\
(forall i, 0 <= i < req_size n -> aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) memc (p + i)).
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 p n Hsub HAR HJ Hin Hno.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc p n HAR Hin) as (_ & H4096 & Hceil & _).
pose proof (BLKN lyc Sc Hpc W memc mdc p n HAR Hin) as Hn0.
assert (Hrq : 0 < req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
pose proof HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _ & _ & Hgone & _).
assert (Hin2 : In (p, n) (ablocks B ly2 S2)).
{ destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B ly2 S2)) as [Hc|Hc];
  [exact Hc | exfalso; exact (Hno 0 ltac:(lia) (Hgone p n 0 Hin Hc ltac:(lia)))]. }
split; [exact Hin2|]. intros i Hi.
rewrite (F2 p n i Hin Hin2 Hi (Hno i Hi)).
apply (aview_gagree SEGS G1 (w_H W) memc memS (p + i) Hag).
apply (proj2 (inGb_false G1 _)). rewrite unsigned_lit_small by lia.
intros Hc. pose proof (inG_lo (p + i) (Hsub (p + i) Hc)) as Hlo.
destruct (alx_client_img _ _ _ LAWS lyc Sc Hpc W memc mdc (p + i) HAR ltac:(left; exists p, n; split; [exact Hin | lia])) as [_ Hni].
exact (Hni (proj1 (HG (p + i) (Hsub (p + i) Hc)))).
Qed.
(* ---------------------------------------------------------------- the memset site in the journal frame *)
(* Reusable/YCbq.v:1955 aj_intrin_at wants the written bytes to be awr_bytes of the walk's own window; here they
   are bytes of a program global, so this is W_sites_x.v aj_gx_entry_at_x's proof at OSet, with its presence
   premise on the bytes of G weakened to visibility (which is all its ARx_frame_law step uses). *)
(* :378 aj_set_gx_at (line at 3a15e3071e9) *)
Lemma aj_set_gx_at_xR : forall pc, aintrin_realizes_xR SEGS B ARx R OSet pc ->
forall (W : world SEGS) regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n (o : Z) raw,
ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n ->
0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> inG G a) ->
amem_range d n ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) d n) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\
 (forall i, 0 <= i < n -> aview SEGS (w_H W) mem2 (d + i) = Some (x mod 256)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw HdG Hamr Hra_d Hhull.
pose proof pa_segs_low as Hsegs.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres &
  (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _ & HQT).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre_x SEGS B ARx lyc Sc Hpc W regsT memT mdc).
{ eapply (ecall_pre_at_xR SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memT mdc k regsT o HJi);
  [exact Hsp | exact Hal | exact Hneg | lia | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
assert (SCG : forall a, inG G a -> ~ (sp0 + o - ESTACK <= a < sp0 + o)).
{ intros a Ha Hs. pose proof (inG_lo a Ha). unfold kLowMemEnd in *. lia. }
assert (HDEST : dest_ok SEGS B lyc Sc W regsT memT d n).
{ intros a Ha. split; [exact (GX_W a (HdG a Ha) _)|].
  split; [exact (inG_not_owned lyc Sc Hpc W memT mdc a HAR (HdG a Ha))|].
  rewrite Hsp. exact (SCG a (HdG a Ha)). }
eapply (SRrG_mono SEGS R).
{ exact (AM lyc Sc Hpc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr
    (fun a Ha HK => proj2 (proj2 (HG a (HdG a Ha))) (proj1 (proj2 HK))) Hra_d Hhull I). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsame & Hres & Heff & Hfr & Hgr).
rewrite Hsp in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
set (memM := fun y : word => if inGb G (bv_unsigned y) then memT y else mem2 y).
assert (MG : forall y, inGb G (bv_unsigned y) = false -> memM y = mem2 y) by (intros y Hy; unfold memM; rewrite Hy; reflexivity).
assert (MT2 : forall y, inGb G (bv_unsigned y) = true -> memM y = memT y) by (intros y Hy; unfold memM; rewrite Hy; reflexivity).
assert (GB : forall a, 0 <= a < 2 ^ 64 -> inGb G (bv_unsigned (Z_to_bv 64 a)) = inGb G a)
by (intros a Ha; rewrite unsigned_lit_small by lia; reflexivity).
assert (AVT : forall a, 0 <= a < 2 ^ 64 -> inG G a -> aview SEGS (w_H W) memM a = aview SEGS (w_H W) memT a).
{ intros a Ha Hga. apply aview_eq_of. unfold mrestrict. rewrite MT2; [reflexivity|]. rewrite GB by exact Ha. apply inGb_spec. exact Hga. }
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview SEGS (w_H W) memM a = aview SEGS (w_H W) mem2 a).
{ intros a Ha Hga. apply aview_eq_of. unfold mrestrict. rewrite MG; [reflexivity|]. rewrite GB by exact Ha. apply (proj2 (inGb_false G a)). exact Hga. }
assert (HARM : ARx lyc Sc Hpc W memM md2).
{ eapply (alx_frame _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2); [ | | reflexivity | reflexivity | reflexivity | |].
  - intros a Ha Ho. apply AV2; [exact Ha|]. intros Hga. exact (inG_not_owned lyc Sc Hpc W mem2 md2 a HAR2 Hga Ho).
  - intros a Hv. rewrite aview_wrap64 in Hv |- *.
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ra. set (a' := a mod 2 ^ 64) in *.
    destruct (inGb G a') eqn:Hgg.
    + apply inGb_spec in Hgg. rewrite (AVT a' Ra Hgg). exact (aview_G_some W memT a' Hgg).
    + rewrite (AV2 a' Ra (proj1 (inGb_false G a') Hgg)). exact Hv.
  - intros a _ Hh. unfold memM. destruct (inGb G (bv_unsigned (w64 a))) eqn:Hgg; [|reflexivity].
    exfalso. apply inGb_spec in Hgg. pose proof (proj1 (HG _ Hgg)) as Hi.
    rewrite (hidden_not_img SEGS W _ Hi) in Hh. discriminate.
  - (* QMm W0': a kept byte is not in G (gx_ok's as_kept clause), so memM is mem2 there *)
    intros a Ha (_ & Hk & _). unfold memM. destruct (inGb G (bv_unsigned (w64 a))) eqn:Hgg; [|reflexivity].
    exfalso. apply inGb_spec in Hgg. rewrite unsigned_lit_small in Hgg by lia.
    exact (proj2 (proj2 (HG a Hgg)) Hk). }
assert (HJM : ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memM md2 k).
{ eapply (ajournal_x_after_writeR SEGS B PST ARx LAWS Hsegs STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memT mdc k memM md2
    (fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc Hpc own HJi).
  - intros a Ha Hna. destruct (inGb G a) eqn:Hgg.
    + apply inGb_spec in Hgg. exact (AVT a Ha Hgg).
    + assert (HnG : ~ inG G a) by (apply (proj1 (inGb_false G a)); exact Hgg). rewrite (AV2 a Ha HnG).
      apply Hfr; [exact Ha | intros Hw; exact (HnG (HdG a Hw)) | exact Hna].
  - intros a [Hh [b Hb]]. split; [exact Hh|]. unfold memM. destruct (inGb G (bv_unsigned (Z_to_bv 64 a))).
    + exists b. exact Hb.
    + exact (proj2 (Hgr a (conj Hh (ex_intro _ b Hb)))).
  - exact Hsame.
  - intros a Ha. left. left. lia.
  - exact HARM.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
assert (HJ2 : ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 (gover G memS mem2) md own lyc Sc Hpc W mem2 md2 k).
{ apply (ajournal_rebase_xR SEGS B PST ARx LAWS Hsegs G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 HG HJM).
  - intros y Hy. symmetry. exact (MG y Hy).
  - intros y Hy. unfold mrestrict in Hy |- *. destruct (w_H W y) eqn:Hh; [exact Hy|].
    destruct (inGb G (bv_unsigned y)) eqn:Hgg; [|rewrite (MG y Hgg) in Hy; exact Hy].
    rewrite (MT2 y Hgg) in Hy. destruct (memT y) as [b|] eqn:Eb; [|exfalso; exact (Hy eq_refl)].
    assert (Hpy : apresent (w_H W) memT (bv_unsigned y)) by (split; rewrite Z_to_bv_bv_unsigned; [exact Hh | exists b; exact Eb]).
    destruct (Hgr _ Hpy) as [_ [b2 Hb2]]. rewrite Z_to_bv_bv_unsigned in Hb2. rewrite Hb2. discriminate. }
split.
{ apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k (gover G memS mem2) HSTK HXO);
  [rewrite !Z.add_0_r; exact HJ2 | | intros a Ha Hno; lia].
  intros y Hy. unfold mrestrict, gover in *. rewrite Hy. exact (Hag y Hy). }
split; [exact HP2|]. split; [exact Heff | split; [exact Hfr | exact Hgr]].
Qed.

(* ---------------------------------------------------------------- an internal call, journal to journal *)
(* :476 aj_gx_call (line at 3a15e3071e9) *)
Lemma aj_gx_call_xR : forall (G1 : list (Z * Z)) (W : world SEGS) regsT memT pc STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Z -> Prop),
(forall a, inG G1 a -> inG G a) ->
ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md [] lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memT) (sp0 + o) (s0Z regsT) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsT memT mdc ch1 ->
 SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_xR SEGS B PST ARx R G1 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsT regs2 /\ K ly2 S2 W2 regs2 mem2 md2 k1)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_xR SEGS B PST ARx R G1 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsT regs2 /\ K ly2 S2 W2 regs2 mem2 md2 k1).
Proof.
intros G1 W regsT memT pc STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 o raw ch1 K
HGsub HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof pa_segs_low as Hsegs.
pose proof HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
eapply (SRrG_mono SEGS R).
{ apply Hcallee. exact (afn_pre_x_atR SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md [] lyc Sc Hpc W memT mdc k regsT STK1 o ch1 HJi
    Hsp Hal Hneg Hstk1 Hbud ltac:(rewrite Hra; exact Hraw) ltac:(unfold raZ; rewrite Hra; exact Hra4) Hgp Htp
    ltac:(rewrite Hsp; exact Hch)). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [reflexivity|].
split; [|split; [exact HJ1 | split; [exact HP | exact HK]]].
replace (@nil (Z * Z)) with ([] ++ @nil (Z * Z)) by reflexivity.
eapply (ajournal_gx_sub_xR SEGS B PST ARx LAWS Hsegs R_trans G STK sp0 0 [] FP ly S Hp W0 mem md [] lyc Sc Hpc W memT mdc k
  STK1 (sp0 + o) 0 [] FP1 [] ly2 S2 Hp2 W2 mem2 md2 k1 HJ);
[ exact (ajournal_gx_G_mono_xR SEGS B PST ARx G1 G 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 HGsub HJ1)
| lia | lia | lia | intros a (r & [] & _) | exact HG | exact HF ].
Qed.
(* :574 sr_call_lf (line at 3a15e3071e9) *)
Lemma sr_call_lf_xR : forall (LA : Z) (l : hlist) (lines : bool)
(W : world SEGS) regsT memT STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k (o : Z) raw (kr : nat),
LA mod 8 = 0 ->
(forall a, LA <= a < LA + 16 -> inG G a) -> azs B LA 16 -> rom_view SEGS W memT ->
ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md [] lyc Sc Hpc W memT mdc k ->
alist_at B lyc Sc W memT LA l lines ->
mo_ok MT Sc (lf_cost MT l) ->
rp_RM RP Sc (Z.to_nat (lf_cost MT_rk l) + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
getr regsT 10 = w64 LA ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> LF_STK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
s0Z regsT < alloc_ceiling ->
(forall b n, In (b, n) (list_blks l) -> forall i, 0 <= i < req_size n -> inFP FP (b + i)) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_fr_list_free)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 aregs_preserved regsT regs2 /\
 alist_at B ly2 S2 W2 mem2 LA empty_list lines /\
 (forall rest, Permutation (ablocks B lyc Sc) (list_blks l ++ rest) -> Permutation (ablocks B ly2 S2) rest) /\
 apres_kept B W memT W2 mem2 /\
 (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
 frames S2 = frames Sc /\ mo_le MT Sc S2 (lf_cost MT l) /\ rp_RM RP S2 kr /\ cnt_ok RP (ablocks B ly2 S2) /\
 (forall a, inG G a -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memT a) /\
 (forall b n, In (b, n) (ablocks B lyc Sc) ->
  (forall i, 0 <= i < req_size n -> ~ inFP (blk_FP (list_blks l)) (b + i)) ->
  In (b, n) (ablocks B ly2 S2) /\
  (forall i, 0 <= i < req_size n -> aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memT (b + i))) /\
 (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + o - LF_STK <= a < sp0 + o) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros LA l lines W regsT memT STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k o raw kr
HAL8 HGL HZS HROM HJ HL HMO HRM HCNT H10 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hra4 Hs0 HFP.
pose proof HJ as HARc. apply ajournal_gx_AR_xR in HARc.
assert (Hsub : forall a, inG (sr_G1 LA) a -> inG G a)
by (intros a Ha; apply HGL; exact (proj1 (sr_G1_in LA a) Ha)).
assert (HG1 : gx_ok SEGS B (sr_G1 LA)) by (exact (gx_ok_sub SEGS B (sr_G1 LA) G Hsub HG)).
assert (HR1 : gx_rt B (sr_G1 LA)) by (exact (gx_rt_sub B (sr_G1 LA) G Hsub HGR)).
assert (HP1 : gx_prog_x B ARx (sr_G1 LA))
by (exact (gx_prog_sub_x B ARx (sr_G1 LA) G Hsub (conj HG (conj HGR (conj HRO (conj GX_ROM (conj GX_W GSHV))))))).
assert (HFPpos : ~ YI16.sink_open_fp (blk_FP (list_blks l)))
by (exact (fp_blocks_pos lyc Sc Hpc W memT mdc l lines LA HARc HL)).
eapply (SRrG_mono SEGS R).
{ eapply (aj_gx_call_xR (sr_G1 LA) W regsT memT (BASE + AF_fr_list_free) STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k
    LF_STK (blk_FP (list_blks l)) o raw []
    (fun ly2 S2 W2 regs2 mem2 md2 k1 =>
       alist_at B ly2 S2 W2 mem2 LA empty_list lines /\
       (forall rest, Permutation (ablocks B lyc Sc) (list_blks l ++ rest) -> Permutation (ablocks B ly2 S2) rest) /\
       apres_kept B W memT W2 mem2 /\
       (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
       frames S2 = frames Sc /\ mo_le MT Sc S2 (lf_cost MT l) /\ rp_RM RP S2 kr)
    Hsub HJ Hsp Hal Hneg ltac:(unfold LF_STK, ASTACK; lia) Hbud Hgp Htp Hra Hraw Hra4
    ltac:(apply achain_low; exact Hs0)).
  - intros HPRE1. eapply (SRrG_mono SEGS R).
    { exact (LF_R (sr_G1 LA) HP1 W lyc Sc Hpc regsT memT mdc [] LA l lines HPRE1 H10 HAL8 HL
        ltac:(intros a Ha; apply (proj2 (sr_G1_in LA a)); exact Ha) HZS HROM HMO kr HRM HCNT). }
    cbv beta. unfold lf_post_xR.
    intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & -> & HJ2 & HP2 & HAL & HPerm & HPK & HER & HFr & HMLE & HRM2).
    exists ly2, S2, Hp2, regs2, mem2, md2, kk.
    split; [rewrite Hra; reflexivity|]. split; [rewrite <- Hsp; exact HJ2|].
    split; [exact HP2|]. split; [exact HAL | split; [exact HPerm | split; [exact HPK | split; [exact HER |
      split; [exact HFr | split; [exact HMLE | exact HRM2]]]]]].
  - intros a Ha. left. split.
    + unfold blk_FP in Ha. destruct Ha as (r & Hr & Hra2). apply in_map_iff in Hr.
      destruct Hr as ((b, n) & <- & Hin). cbn [fst snd] in Hra2.
      replace a with (b + (a - b)) by lia. apply (HFP b n Hin). lia.
    + unfold blk_FP in Ha. destruct Ha as (r & Hr & Hra2). apply in_map_iff in Hr.
      destruct Hr as ((b, n) & <- & Hin). cbn [fst snd] in Hra2.
      exists b, n. split; [exact (alist_blks_in lyc Sc W memT LA l lines HL b n Hin) | lia]. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJa & HJb & HP & HAL & HPerm & HPK & HER & HFr & HMLE & HRM2).
exists ly2, S2, Hp2, regs2, mem2, md2, k1.
split; [reflexivity|]. split; [exact HJa|]. split; [exact HP|]. split; [exact HAL|].
split; [exact HPerm|]. split; [exact HPK|]. split; [exact HER|]. split; [exact HFr|]. split; [exact HMLE|].
split; [exact HRM2|].
split.
{ destruct (perm_of_incl_nodup (list_blks l) (ablocks B lyc Sc) (list_blks_nodup lyc Sc W memT LA l lines HL)
    (alist_blks_in lyc Sc W memT LA l lines HL)) as (rest & Hrest).
  exact (sr_cnt_rest RP _ _ _ _ Hrest (HPerm rest Hrest) HCNT). }
split.
{ intros a Ha Hno. apply (gx_keep_img_xR (sr_G1 LA) LF_STK (sp0 + o) (blk_FP (list_blks l)) lyc Sc Hpc W memT mdc
    ly2 S2 Hp2 W2 mem2 md2 k1 Hsub HFPpos HJb a Ha).
  intros Hc. exact (Hno (proj1 (sr_G1_in LA a) Hc)). }
split.
{ intros b n Hin Hno. exact (gx_keep_blk_xR (sr_G1 LA) LF_STK (sp0 + o) (blk_FP (list_blks l)) lyc Sc Hpc W memT mdc
    ly2 S2 Hp2 W2 mem2 md2 k1 b n Hsub HARc HJb Hin Hno). }
intros a Ha Hno.
exact (gx_keep_hi_xR (sr_G1 LA) LF_STK (sp0 + o) (blk_FP (list_blks l)) lyc Sc Hpc W memT mdc ly2 S2 Hp2 W2 mem2 md2 k1
  Hsub HJb a Ha Hno).
Qed.
(* :758 gx_pres (line at 3a15e3071e9) *)
Lemma gx_pres_xR : forall G0 STK sp0 FP ly S Hp (W0 : world SEGS) mem md own ly' S' Hp' (W' : world SEGS) mem' md' k,
ajournal_gx_xR SEGS B PST ARx R G0 0 [] STK sp0 FP ly S Hp W0 mem md own ly' S' Hp' W' mem' md' k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros G0 STK sp0 FP ly S Hp W0 mem md own ly' S' Hp' W' mem' md' k HJ a Ha.
destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _). exact (Hpr a Ha).
Qed.
(* two journal facts at the walk's G, with their journal arguments implicit *)
(* :837 sr_gx_AR (line at 3a15e3071e9) *)
Lemma sr_gx_AR_xR : forall {STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k},
ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ARx ly' S' Hp' W' mem' md'.
Proof. intros * HJ. exact (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). Qed.
(* :841 sr_rom_view (line at 3a15e3071e9) *)
Lemma sr_rom_view_xR : forall {STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k},
ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
rom_view SEGS W mem -> rom_view SEGS W' mem'.
Proof.
intros * HJ Hrv. eapply ajournal_gx_rom_view_xR;
first [exact LAWS | exact pa_segs_low | exact HJ | exact HRO | exact sr_pstr | exact Hrv].
Qed.
(* ---------------------------------------------------------------- the walk *)
(* :849 pb_source_reset_x (line at 3a15e3071e9) *)
Theorem pb_source_reset_xR : sr_spec_xR B PST ARx R MT RP G A_source_resetP.
Proof.
intros W ly S Hp regs mem md ch HA op HPRE H10 HAL8 HREP HGL HZS HROM HMO kr HRM0 HCNT0.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (sr_HA_range HA HGL) as HARng.
pose proof (mo_free_nonneg MT MLAW) as MF0.
(* errno: four image bytes below kLowMemEnd (PALib's api_env), so below the allocator ceiling and the stack *)
pose proof (proj1 (pal_env B TL)) as [He0 He1].
assert (HEL : forall i, 0 <= i < 4 -> 0 <= as_errno B + i < alloc_ceiling)
by (intros i Hi; clear - He0 He1 C1 Hi; unfold kLowMemEnd in He1; lia).
assert (WS : SR_STK = 16496) by reflexivity.
assert (HC1 : 0 <= lf_cost MT (sr_l1 op)) by (unfold lf_cost, hl_n; apply Z.mul_nonneg_nonneg; lia).
assert (HC2 : 0 <= lf_cost MT (sr_l2 op)) by (unfold lf_cost, hl_n; apply Z.mul_nonneg_nonneg; lia).
assert (HC3 : 0 <= lf_cost MT (sr_l3 op)) by (unfold lf_cost, hl_n; apply Z.mul_nonneg_nonneg; lia).
assert (HCsum : lf_cost MT (sr_l1 op) + lf_cost MT (sr_l2 op) + lf_cost MT (sr_l3 op) + mo_free MT = sr_cost MT op).
{ destruct op as [h|]; cbn [sr_l1 sr_l2 sr_l3 sr_cost]; [reflexivity|].
  unfold lf_cost, hl_n, empty_list. cbn [hl_recs length]. lia. }
(* the room budget: the three lists' list_free budgets and the free of s->partial (W_contract_x.v sr_spec_x) *)
assert (HRK0 : Z.to_nat (sr_cost MT_rk op) =
  (Z.to_nat (lf_cost MT_rk (sr_l1 op)) + Z.to_nat (lf_cost MT_rk (sr_l2 op)) + Z.to_nat (lf_cost MT_rk (sr_l3 op)) + 1)%nat).
{ assert (Hk : forall l, 0 <= lf_cost MT_rk l) by (intros l; unfold lf_cost, hl_n; cbn [mo_free MT_rk]; lia).
  assert (Hs : lf_cost MT_rk (sr_l1 op) + lf_cost MT_rk (sr_l2 op) + lf_cost MT_rk (sr_l3 op) + 1 = sr_cost MT_rk op).
  { destruct op as [h|]; cbn [sr_l1 sr_l2 sr_l3 sr_cost]; [reflexivity|].
    unfold lf_cost, hl_n, empty_list. cbn [hl_recs length mo_free MT_rk]. lia. }
  rewrite <- Hs. pose proof (Hk (sr_l1 op)) as K1. pose proof (Hk (sr_l2 op)) as K2. pose proof (Hk (sr_l3 op)) as K3.
  clear - K1 K2 K3. lia. }
destruct (sr_rep_lists ly S Hp W mem md HA op HAR HREP) as (HL1 & HL2 & HL3 & HVP & HBP).
(* the blocks of the three lists and of s->partial have distinct addresses *)
assert (HD : (forall x, In x (list_blocks (sr_l1 op)) -> In x (list_blocks (sr_l2 op)) -> False) /\
  (forall x, In x (list_blocks (sr_l1 op)) -> In x (list_blocks (sr_l3 op)) -> False) /\
  (forall x, In x (list_blocks (sr_l2 op)) -> In x (list_blocks (sr_l3 op)) -> False) /\
  ~ In (sr_p op) (list_blocks (sr_l1 op)) /\ ~ In (sr_p op) (list_blocks (sr_l2 op)) /\
  ~ In (sr_p op) (list_blocks (sr_l3 op))).
{ destruct op as [h|].
  - pose proof HREP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HN).
    unfold hs_blocks in HN. cbn [sr_l1 sr_l2 sr_l3 sr_p].
    pose proof (nodup_app_disj _ _ HN) as D1. pose proof (nodup_app_right _ _ HN) as HN2.
    pose proof (nodup_app_disj _ _ HN2) as D2. pose proof (nodup_app_right _ _ HN2) as HN3.
    pose proof (nodup_app_disj _ _ HN3) as D3.
    split; [intros x H1 H2; apply (D1 x H1); cbn [app]; right; apply in_or_app; left; exact H2|].
    split; [intros x H1 H2; apply (D1 x H1); cbn [app]; right; apply in_or_app; right; exact H2|].
    split; [exact D3|].
    split; [intros Hc; apply (D1 _ Hc); cbn [app]; left; reflexivity|].
    split; [intros Hc; apply (D2 (hs_partial h) ltac:(left; reflexivity)); apply in_or_app; left; exact Hc|].
    intros Hc. apply (D2 (hs_partial h) ltac:(left; reflexivity)). apply in_or_app. right. exact Hc.
  - cbn [sr_l1 sr_l2 sr_l3 sr_p]. unfold list_blocks, empty_list. cbn [hl_cap hl_v hl_recs map app].
    repeat split; unfold not; intros; match goal with Hx : In _ _ |- _ => cbn in Hx; destruct Hx end. }
destruct HD as (HD12 & HD13 & HD23 & HDp1 & HDp2 & HDp3).
(* the footprint of the walk *)
assert (HFPof : forall b n, In (b, n) (sr_blks op) -> forall i, 0 <= i < req_size n -> inFP (blk_FP (sr_blks op)) (b + i)).
{ intros b n Hin i Hi. exists (b, b + req_size n). split; [|cbn [fst snd]; lia].
  unfold blk_FP. exact (in_map (fun q : Z * Z => (fst q, fst q + req_size (snd q))) _ (b, n) Hin). }
assert (HIN1 : forall b n, In (b, n) (list_blks (sr_l1 op)) -> In (b, n) (sr_blks op)).
{ destruct op as [h|]; cbn [sr_blks sr_l1]; intros b n Hin; [unfold hs_blks; apply in_or_app; left; exact Hin|].
  unfold list_blks, empty_list in Hin. cbn in Hin. destruct Hin. }
assert (HIN2 : forall b n, In (b, n) (list_blks (sr_l2 op)) -> In (b, n) (sr_blks op)).
{ destruct op as [h|]; cbn [sr_blks sr_l2]; intros b n Hin;
  [unfold hs_blks; apply in_or_app; right; cbn [app]; right; apply in_or_app; left; exact Hin|].
  unfold list_blks, empty_list in Hin. cbn in Hin. destruct Hin. }
assert (HIN3 : forall b n, In (b, n) (list_blks (sr_l3 op)) -> In (b, n) (sr_blks op)).
{ destruct op as [h|]; cbn [sr_blks sr_l3]; intros b n Hin;
  [unfold hs_blks; apply in_or_app; right; cbn [app]; right; apply in_or_app; right; exact Hin|].
  unfold list_blks, empty_list in Hin. cbn in Hin. destruct Hin. }
(* the entry *)
assert (Rp : 0 <= sr_p op < 2 ^ 64).
{ destruct op as [h|]; cbn [sr_p] in *; [|lia].
  destruct (blk_bounds ly S Hp W mem md _ _ HAR HBP) as [Hb1 Hb2]. unfold req_size, APARTIAL in Hb2. cbn in Hb2. lia. }
destruct (sr_entry W ly S Hp regs mem md ch HA op HPRE H10 HGL Rp) as [HS SHOK].
pose proof (ajournal_gx_init_xR SEGS B PST ARx R_refl G 0 [] SR_STK (blk_FP (sr_blks op)) ly S Hp W regs mem md ch HPRE
  ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg regs (sr_extra (sr_p op)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 HA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (sr_p op)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (sr_extra (sr_p op))) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_source_resetP) with (Z_to_bv 64 A_source_resetP).
unfold A_source_resetP, A_source_reset.
(* ---- the prologue, to list_free(&s->pending) ---- *)
paj_run_to_tok_xR RUNTOG HS HJ SHOK sr_Bspan A_sr_lf. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
(* the prologue wrote only the 32-byte frame *)
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbn [ss_sr sr_regions ss_mem In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]];
  cbn [stack_region got_regionP bcell_regionP SR_FRAME YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite Usp in Hr; unfold SR_FRAME in Hr; apply Hno; lia | lia | lia]. }
assert (KLO0 : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
by (intros a Ha; apply KEEP0; lia).
assert (KG0 : forall a, inG G a -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
by (intros a Ha; apply KLO0; pose proof (inG_lo a Ha) as Hl; unfold kLowMemEnd in Hl; lia).
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) |- _ =>
  assert (PR0 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Hpa; exact (apresent_of_grows (w_H W) mem (ms_mem ms) a Hgr Hpa)) end.
assert (TR0 : forall LA l lines, alist_at B ly S W mem LA l lines -> (forall a, LA <= a < LA + 16 -> inG G a) ->
  alist_at B ly S W (ms_mem ms) LA l lines).
{ intros LA l lines HL HLG. apply (alist_kept_gen ly S W mem ly S W (ms_mem ms) LA l lines HL).
  - exact (alist_blks_in ly S W mem LA l lines HL).
  - exact HLG.
  - intros a Ha. exact (KG0 a (HLG a Ha)).
  - intros b n Hin i Hi. pose proof (alist_blks_in ly S W mem LA l lines HL b n Hin) as Hb.
    destruct (blk_bounds ly S Hp W mem md b n HAR Hb) as [Hb1 Hb2].
    split; [apply KLO0; lia|].
    apply (writable_kept' (w_H W) mem (ms_mem ms) (b + i) (PR0 (b + i))).
    exact (blk_writable ly S Hp W mem md b n HAR Hb i Hi). }
assert (HG16 : forall a, HA + 16 <= a < HA + 16 + 16 -> inG G a) by (intros a Ha; apply HGL; unfold ASRC; lia).
assert (HG64 : forall a, HA + 64 <= a < HA + 64 + 16 -> inG G a) by (intros a Ha; apply HGL; unfold ASRC; lia).
assert (HG80 : forall a, HA + 80 <= a < HA + 80 + 16 -> inG G a) by (intros a Ha; apply HGL; unfold ASRC; lia).
assert (HG40 : forall a, HA + 40 <= a < HA + 48 -> inG G a) by (intros a Ha; apply HGL; unfold ASRC; lia).
pose proof (TR0 _ _ _ HL1 HG16) as HL1a. pose proof (TR0 _ _ _ HL2 HG64) as HL2a. pose proof (TR0 _ _ _ HL3 HG80) as HL3a.
assert (HVPa : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (HA + 40) 8 (sr_p op)).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms)); [|exact HVP].
  intros k0 Hk. apply KG0. apply HG40. cbn in Hk. lia. }
assert (HROMa : rom_view SEGS W (ms_mem ms)) by (exact (sr_rom_view_xR HJ HROM)).
pose proof (sr_gx_AR_xR HJ) as HAR0.
(* ---- list_free(&s->pending) ---- *)
assert (R10 : getr (ms_regs ms) 10 = w64 (HA + 16)).
{ rewrite Q10, E10. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Usp1 : spZ (ms_regs ms) = spZ regs + -32).
{ unfold spZ. rewrite Q2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
assert (S01 : s0Z (ms_regs ms) = HA).
{ unfold s0Z. rewrite Q8, E10. apply unsigned_lit_small. lia. }
assert (HRMa : rp_RM RP S (Z.to_nat (lf_cost MT_rk (sr_l1 op)) +
  (Z.to_nat (lf_cost MT_rk (sr_l2 op)) + Z.to_nat (lf_cost MT_rk (sr_l3 op)) + 1 + kr))).
{ apply (sr_rm_cast RP S _ _ HRM0). rewrite HRK0. clear - kr. lia. }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (sr_call_lf_xR (HA + 16) (sr_l1 op) false W (ms_regs ms) (ms_mem ms) SR_STK (spZ regs)
    (blk_FP (sr_blks op)) ly S Hp W mem md ly S Hp _ 0 (-32) _
    (Z.to_nat (lf_cost MT_rk (sr_l2 op)) + Z.to_nat (lf_cost MT_rk (sr_l3 op)) + 1 + kr)%nat
    ltac:(clear - HAL8; rewrite Z.add_mod, HAL8 by lia; reflexivity) HG16
    (azs_sub HA ASRC (HA + 16) 16 HZS ltac:(lia) ltac:(unfold ASRC; lia)) HROMa HJ HL1a
    (mok_station MT S S (sr_cost MT op) 0 (lf_cost MT (sr_l1 op)) MLAW HMO (mle_start MT S MLAW) HC1 ltac:(lia))
    HRMa HCNT0
    R10 Usp1 eq_refl ltac:(lia) ltac:(unfold LF_STK, ASTACK; lia)
    ltac:(rewrite Q3, E3; exact Hgp) ltac:(rewrite Q4, E4; exact Htp) Q1
    ltac:(apply ret_ok_codeptr_v; [lia | reflexivity]) ltac:(rewrite unsigned_lit_small by lia; lia)
    ltac:(rewrite S01; lia)
    (fun b n Hin i Hi => HFPof b n (HIN1 b n Hin) i Hi)). }
cbv beta. intros W1 c1 Hwle1
  (ly1 & S1 & Hp1 & regs1 & mem1 & md1 & k1 & -> & HJ1 & HP1 & HAL1 & HPM1 & HPK1 & HER1 & HFR1 & HML1 & HRM1 & HCN1 & KG1 & KB1 & KH1).
pose proof (sr_gx_AR_xR HJ1) as HAR1.
jafter_call_keep_pi HS 34%nat regs1 (mrestrict (w_H W1) mem1) HP1 [0]%nat HS1.
match type of HS1 with ?ty -> _ => assert (HRK : ty); [|specialize (HS1 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  apply (region_kept_sp E W W1 (ms_mem ms) mem1 2%nat (spZ regs) (-32) 0 (-32) 0 _ Usp ltac:(lia) ltac:(lia)).
  - intros a Ha. apply KH1; lia.
  - intros a Ha. apply (gx_pres_xR G SR_STK (spZ regs) _ ly S Hp W mem md [] ly1 S1 Hp1 W1 mem1 md1 _ HJ1). lia. }
clear HS. rewrite <- restrict_mkst_fx in HS1. rename HS1 into HS.
remember (havoc E 34 (map (getr regs1) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m0, (m0 < 34)%nat -> ew Ea m0 = ew E m0) by (intros m0 Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs (sr_extra (sr_p op))) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by (cbv; lia); exact Usp).
assert (SHOKa : sh_ok SEGS sr_Bx sr_SH Ea (mrestrict (w_H W1) mem1)) by (unfold sh_ok, sr_SH; constructor).
(* what the rest of the walk needs, at the state after list_free(&s->pending) *)
assert (HPKa : apres_kept B W mem W1 mem1)
by (exact (apres_kept_trans W W W1 mem (ms_mem ms) mem1 (apres_kept_of_pres W W mem (ms_mem ms) PR0) HPK1)).
assert (HERa : forall i, 0 <= i < 4 ->
  aview SEGS (w_H W1) mem1 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
{ intros i Hi. rewrite (HER1 i Hi). exact (KLO0 _ (HEL i Hi)). }
assert (HAL2 : alist_at B ly1 S1 W1 mem1 (HA + 64) (sr_l2 op) true).
{ apply (sr_list_across (sr_l1 op) (HA + 16) (sr_l2 op) (HA + 64) true ly S Hp W (ms_mem ms) _ ly1 S1 W1 mem1
    HAR0 HL2a (alist_blks_in ly S W (ms_mem ms) (HA + 16) (sr_l1 op) false HL1a)
    (fun x H2 H1 => HD12 x H1 H2) HG64 ltac:(intros a Ha Hc; lia) KG1 KB1
    (fun b n Hin i Hi => blk_writable ly1 S1 Hp1 W1 mem1 md1 b n HAR1 Hin i Hi)). }
assert (HAL3 : alist_at B ly1 S1 W1 mem1 (HA + 80) (sr_l3 op) true).
{ apply (sr_list_across (sr_l1 op) (HA + 16) (sr_l3 op) (HA + 80) true ly S Hp W (ms_mem ms) _ ly1 S1 W1 mem1
    HAR0 HL3a (alist_blks_in ly S W (ms_mem ms) (HA + 16) (sr_l1 op) false HL1a)
    (fun x H3 H1 => HD13 x H1 H3) HG80 ltac:(intros a Ha Hc; lia) KG1 KB1
    (fun b n Hin i Hi => blk_writable ly1 S1 Hp1 W1 mem1 md1 b n HAR1 Hin i Hi)). }
assert (HVP1 : val_mem SEGS (mrestrict (w_H W1) mem1) (HA + 40) 8 (sr_p op)).
{ apply (val_mem_kept SEGS (w_H W) (w_H W1) (ms_mem ms) mem1); [|exact HVPa].
  intros k0 Hk. cbn in Hk. apply KG1; [apply HG40; lia | lia]. }
assert (HBP1 : match op with Some _ => In (sr_p op, APARTIAL) (ablocks B ly1 S1) | None => True end).
{ destruct op as [h|]; [|exact I].
  exact (sr_blk_across (sr_l1 (Some h)) ly S Hp W (ms_mem ms) _ ly1 S1 W1 mem1 (sr_p (Some h)) APARTIAL HAR0
    (alist_blks_in ly S W (ms_mem ms) (HA + 16) (sr_l1 (Some h)) false HL1a) HDp1 HBP KB1). }
clear dependent ms. clear HL1 HL2 HL3 HVP HAL1.
(* ---- list_free(&s->expected) ---- *)
paj_run_to_tok_xR RUNTOG HS HJ1 SHOKa sr_Bspan A_sr_lf. { apply awr_ok_x_of0. awr_ok_tac. exact Uspa. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hno. apply (aview_kept_out Ea _ (w_H W1) mem1 (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr.
  rewrite Uspa in Hr. apply Hno. lia. }
assert (KLO1 : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
by (intros a Ha; apply KEEP1; lia).
assert (KGr1 : forall a, inG G a -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
by (intros a Ha; apply KLO1; pose proof (inG_lo a Ha) as Hl; unfold kLowMemEnd in Hl; lia).
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W1) mem1) (mrestrict (w_H W1) (ms_mem ms)) |- _ =>
  assert (PR1 : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) (ms_mem ms) a)
  by (intros a Hpa; exact (apresent_of_grows (w_H W1) mem1 (ms_mem ms) a Hgr Hpa)) end.
assert (TR1 : forall LA l lines, alist_at B ly1 S1 W1 mem1 LA l lines -> (forall a, LA <= a < LA + 16 -> inG G a) ->
  alist_at B ly1 S1 W1 (ms_mem ms) LA l lines).
{ intros LA l lines HL HLG. apply (alist_kept_gen ly1 S1 W1 mem1 ly1 S1 W1 (ms_mem ms) LA l lines HL).
  - exact (alist_blks_in ly1 S1 W1 mem1 LA l lines HL).
  - exact HLG.
  - intros a Ha. exact (KGr1 a (HLG a Ha)).
  - intros b n Hin i Hi. pose proof (alist_blks_in ly1 S1 W1 mem1 LA l lines HL b n Hin) as Hb.
    destruct (blk_bounds ly1 S1 Hp1 W1 mem1 md1 b n HAR1 Hb) as [Hb1 Hb2].
    split; [apply KLO1; lia|].
    apply (writable_kept' (w_H W1) mem1 (ms_mem ms) (b + i) (PR1 (b + i))).
    exact (blk_writable ly1 S1 Hp1 W1 mem1 md1 b n HAR1 Hb i Hi). }
pose proof (TR1 _ _ _ HAL2 HG64) as HL2a. pose proof (TR1 _ _ _ HAL3 HG80) as HL3a.
assert (HVPa : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (HA + 40) 8 (sr_p op)).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem1 (ms_mem ms)); [|exact HVP1].
  intros k0 Hk. apply KGr1. apply HG40. cbn in Hk. lia. }
assert (HROMa : rom_view SEGS W1 (ms_mem ms)) by (exact (sr_rom_view_xR HJ1 HROM)).
pose proof (sr_gx_AR_xR HJ1) as HAR0.
assert (R10 : getr (ms_regs ms) 10 = w64 (HA + 64)).
{ rewrite Q10, OLDa by (cbv; lia). rewrite E10. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Usp1 : spZ (ms_regs ms) = spZ regs + -32).
{ unfold spZ. rewrite Q2, Uspa. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
assert (S01 : s0Z (ms_regs ms) = HA).
{ unfold s0Z. rewrite Q8, OLDa by (cbv; lia). rewrite E10. apply unsigned_lit_small. lia. }
assert (HRMb : rp_RM RP S1 (Z.to_nat (lf_cost MT_rk (sr_l2 op)) + (Z.to_nat (lf_cost MT_rk (sr_l3 op)) + 1 + kr)))
by (apply (sr_rm_cast RP S1 _ _ HRM1); clear - kr; lia).
eapply (SRrG_bind SEGS R R_trans).
{ eapply (sr_call_lf_xR (HA + 64) (sr_l2 op) true W1 (ms_regs ms) (ms_mem ms) SR_STK (spZ regs)
    (blk_FP (sr_blks op)) ly S Hp W mem md ly1 S1 Hp1 _ (0 + k1) (-32) _ (Z.to_nat (lf_cost MT_rk (sr_l3 op)) + 1 + kr)%nat
    ltac:(clear - HAL8; rewrite Z.add_mod, HAL8 by lia; reflexivity) HG64
    (azs_sub HA ASRC (HA + 64) 16 HZS ltac:(lia) ltac:(unfold ASRC; lia)) HROMa HJ1 HL2a
    (mok_station MT S S1 (sr_cost MT op) (lf_cost MT (sr_l1 op)) (lf_cost MT (sr_l2 op)) MLAW HMO HML1 HC2 ltac:(lia))
    HRMb HCN1
    R10 Usp1 eq_refl ltac:(lia) ltac:(unfold LF_STK, ASTACK; lia)
    ltac:(rewrite Q3, OLDa by (cbv; lia); rewrite E3; exact Hgp) ltac:(rewrite Q4, OLDa by (cbv; lia); rewrite E4; exact Htp) Q1
    ltac:(apply ret_ok_codeptr_v; [lia | reflexivity]) ltac:(rewrite unsigned_lit_small by lia; lia)
    ltac:(rewrite S01; lia)
    (fun b n Hin i Hi => HFPof b n (HIN2 b n Hin) i Hi)). }
cbv beta. intros W2 c2 Hwle2
  (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & -> & HJ2 & HP2 & HAL2b & HPM2 & HPK2 & HER2 & HFR2 & HML2 & HRM2 & HCN2 & KG2 & KB2 & KH2).
pose proof (sr_gx_AR_xR HJ2) as HAR2.
jafter_call_keep_pi HS 50%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  apply (region_kept_sp Ea W1 W2 (ms_mem ms) mem2 2%nat (spZ regs) (-32) 0 (-32) 0 _ Uspa ltac:(lia) ltac:(lia)).
  - intros a Ha. apply KH2; lia.
  - intros a Ha. apply (gx_pres_xR G SR_STK (spZ regs) _ ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 _ HJ2). lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc Ea 50 (map (getr regs2) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m0, (m0 < 34)%nat -> ew Eb m0 = ew E m0)
by (intros m0 Hm; rewrite HEb; rewrite YN3v.ew_havoc_old by lia; apply OLDa; exact Hm).
assert (HAEb : env_agree 32 (Ereg regs (sr_extra (sr_p op))) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by (cbv; lia); exact Usp).
assert (SHOKb : sh_ok SEGS sr_Bx sr_SH Eb (mrestrict (w_H W2) mem2)) by (unfold sh_ok, sr_SH; constructor).
assert (HPKb : apres_kept B W mem W2 mem2)
by (exact (apres_kept_trans W W1 W2 mem (ms_mem ms) mem2
  (apres_kept_trans W W1 W1 mem mem1 (ms_mem ms) HPKa (apres_kept_of_pres W1 W1 mem1 (ms_mem ms) PR1)) HPK2)).
assert (HERb : forall i, 0 <= i < 4 ->
  aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
{ intros i Hi. rewrite (HER2 i Hi), (KLO1 _ (HEL i Hi)). exact (HERa i Hi). }
assert (HAL3b : alist_at B ly2 S2 W2 mem2 (HA + 80) (sr_l3 op) true).
{ apply (sr_list_across (sr_l2 op) (HA + 64) (sr_l3 op) (HA + 80) true ly1 S1 Hp1 W1 (ms_mem ms) _ ly2 S2 W2 mem2
    HAR0 HL3a (alist_blks_in ly1 S1 W1 (ms_mem ms) (HA + 64) (sr_l2 op) true HL2a)
    (fun x H3 H2 => HD23 x H2 H3) HG80 ltac:(intros a Ha Hc; lia) KG2 KB2
    (fun b n Hin i Hi => blk_writable ly2 S2 Hp2 W2 mem2 md2 b n HAR2 Hin i Hi)). }
assert (HVP2 : val_mem SEGS (mrestrict (w_H W2) mem2) (HA + 40) 8 (sr_p op)).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) (ms_mem ms) mem2); [|exact HVPa].
  intros k0 Hk. cbn in Hk. apply KG2; [apply HG40; lia | lia]. }
assert (HBP2 : match op with Some _ => In (sr_p op, APARTIAL) (ablocks B ly2 S2) | None => True end).
{ destruct op as [h|]; [|exact I].
  exact (sr_blk_across (sr_l2 (Some h)) ly1 S1 Hp1 W1 (ms_mem ms) _ ly2 S2 W2 mem2 (sr_p (Some h)) APARTIAL HAR0
    (alist_blks_in ly1 S1 W1 (ms_mem ms) (HA + 64) (sr_l2 (Some h)) true HL2a) HDp2 HBP1 KB2). }
clear dependent ms. clear HAL2 HAL3 HVP1 HAL2b.
(* ---- list_free(&s->held) ---- *)
paj_run_to_tok_xR RUNTOG HS HJ2 SHOKb sr_Bspan A_sr_lf. { apply awr_ok_x_of0. awr_ok_tac. exact Uspb. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hno. apply (aview_kept_out Eb _ (w_H W2) mem2 (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr.
  rewrite Uspb in Hr. apply Hno. lia. }
assert (KLO2 : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha; apply KEEP2; lia).
assert (KGr2 : forall a, inG G a -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha; apply KLO2; pose proof (inG_lo a Ha) as Hl; unfold kLowMemEnd in Hl; lia).
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms)) |- _ =>
  assert (PR2 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Hpa; exact (apresent_of_grows (w_H W2) mem2 (ms_mem ms) a Hgr Hpa)) end.
assert (HL3a : alist_at B ly2 S2 W2 (ms_mem ms) (HA + 80) (sr_l3 op) true).
{ apply (alist_kept_gen ly2 S2 W2 mem2 ly2 S2 W2 (ms_mem ms) (HA + 80) (sr_l3 op) true HAL3b).
  - exact (alist_blks_in ly2 S2 W2 mem2 (HA + 80) (sr_l3 op) true HAL3b).
  - exact HG80.
  - intros a Ha. exact (KGr2 a (HG80 a Ha)).
  - intros b n Hin i Hi. pose proof (alist_blks_in ly2 S2 W2 mem2 (HA + 80) (sr_l3 op) true HAL3b b n Hin) as Hb.
    destruct (blk_bounds ly2 S2 Hp2 W2 mem2 md2 b n HAR2 Hb) as [Hb1 Hb2].
    split; [apply KLO2; lia|].
    apply (writable_kept' (w_H W2) mem2 (ms_mem ms) (b + i) (PR2 (b + i))).
    exact (blk_writable ly2 S2 Hp2 W2 mem2 md2 b n HAR2 Hb i Hi). }
assert (HVPa : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms)) (HA + 40) 8 (sr_p op)).
{ apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact HVP2].
  intros k0 Hk. apply KGr2. apply HG40. cbn in Hk. lia. }
assert (HROMa : rom_view SEGS W2 (ms_mem ms)) by (exact (sr_rom_view_xR HJ2 HROM)).
pose proof (sr_gx_AR_xR HJ2) as HAR0.
assert (R10 : getr (ms_regs ms) 10 = w64 (HA + 80)).
{ rewrite Q10, OLDb by (cbv; lia). rewrite E10. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Usp1 : spZ (ms_regs ms) = spZ regs + -32).
{ unfold spZ. rewrite Q2, Uspb. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
assert (S01 : s0Z (ms_regs ms) = HA).
{ unfold s0Z. rewrite Q8, OLDb by (cbv; lia). rewrite E10. apply unsigned_lit_small. lia. }
assert (HRMc : rp_RM RP S2 (Z.to_nat (lf_cost MT_rk (sr_l3 op)) + (1 + kr))) by (apply (sr_rm_cast RP S2 _ _ HRM2); clear - kr; lia).
eapply (SRrG_bind SEGS R R_trans).
{ eapply (sr_call_lf_xR (HA + 80) (sr_l3 op) true W2 (ms_regs ms) (ms_mem ms) SR_STK (spZ regs)
    (blk_FP (sr_blks op)) ly S Hp W mem md ly2 S2 Hp2 _ (0 + k1 + k2) (-32) _ (1 + kr)%nat
    ltac:(clear - HAL8; rewrite Z.add_mod, HAL8 by lia; reflexivity) HG80
    (azs_sub HA ASRC (HA + 80) 16 HZS ltac:(lia) ltac:(unfold ASRC; lia)) HROMa HJ2 HL3a
    (mok_station MT S S2 (sr_cost MT op) (lf_cost MT (sr_l1 op) + lf_cost MT (sr_l2 op)) (lf_cost MT (sr_l3 op)) MLAW HMO
      (mle_station MT S S1 S2 _ _ MLAW HML1 HML2) HC3 ltac:(lia))
    HRMc HCN2
    R10 Usp1 eq_refl ltac:(lia) ltac:(unfold LF_STK, ASTACK; lia)
    ltac:(rewrite Q3, OLDb by (cbv; lia); rewrite E3; exact Hgp) ltac:(rewrite Q4, OLDb by (cbv; lia); rewrite E4; exact Htp) Q1
    ltac:(apply ret_ok_codeptr_v; [lia | reflexivity]) ltac:(rewrite unsigned_lit_small by lia; lia)
    ltac:(rewrite S01; lia)
    (fun b n Hin i Hi => HFPof b n (HIN3 b n Hin) i Hi)). }
cbv beta. intros W3 c3 Hwle3
  (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & -> & HJ3 & HP3 & HAL3c & HPM3 & HPK3 & HER3 & HFR3 & HML3 & HRM3 & HCN3 & KG3 & KB3 & KH3).
pose proof (sr_gx_AR_xR HJ3) as HAR3.
jafter_call_keep_pi HS 66%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  apply (region_kept_sp Eb W2 W3 (ms_mem ms) mem3 2%nat (spZ regs) (-32) 0 (-32) 0 _ Uspb ltac:(lia) ltac:(lia)).
  - intros a Ha. apply KH3; lia.
  - intros a Ha. apply (gx_pres_xR G SR_STK (spZ regs) _ ly S Hp W mem md [] ly3 S3 Hp3 W3 mem3 md3 _ HJ3). lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Eb 66 (map (getr regs3) CLOB)) as Ec eqn:HEc in HS.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
assert (OLDc : forall m0, (m0 < 34)%nat -> ew Ec m0 = ew E m0)
by (intros m0 Hm; rewrite HEc; rewrite YN3v.ew_havoc_old by lia; apply OLDb; exact Hm).
assert (HAEc : env_agree 32 (Ereg regs (sr_extra (sr_p op))) Ec) by (rewrite HEc; apply env_agree_havoc_ge; [cbv; lia | exact HAEb]).
clear HEc.
assert (Uspc : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLDc by (cbv; lia); exact Usp).
assert (HPKc : apres_kept B W mem W3 mem3)
by (exact (apres_kept_trans W W2 W3 mem (ms_mem ms) mem3
  (apres_kept_trans W W2 W2 mem mem2 (ms_mem ms) HPKb (apres_kept_of_pres W2 W2 mem2 (ms_mem ms) PR2)) HPK3)).
assert (HERc : forall i, 0 <= i < 4 ->
  aview SEGS (w_H W3) mem3 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
{ intros i Hi. rewrite (HER3 i Hi), (KLO2 _ (HEL i Hi)). exact (HERb i Hi). }
assert (HVP3 : val_mem SEGS (mrestrict (w_H W3) mem3) (HA + 40) 8 (sr_p op)).
{ apply (val_mem_kept SEGS (w_H W2) (w_H W3) (ms_mem ms) mem3); [|exact HVPa].
  intros k0 Hk. cbn in Hk. apply KG3; [apply HG40; lia | lia]. }
assert (HBP3 : match op with Some _ => In (sr_p op, APARTIAL) (ablocks B ly3 S3) | None => True end).
{ destruct op as [h|]; [|exact I].
  exact (sr_blk_across (sr_l3 (Some h)) ly2 S2 Hp2 W2 (ms_mem ms) _ ly3 S3 W3 mem3 (sr_p (Some h)) APARTIAL HAR0
    (alist_blks_in ly2 S2 W2 (ms_mem ms) (HA + 80) (sr_l3 (Some h)) true HL3a) HDp3 HBP2 KB3). }
clear dependent ms. clear HAL3b HVP2 HAL3c.
(* ---- the shadow-checked load of s->partial, then free(s->partial) ---- *)
assert (Rp3 : 0 <= sr_p op < 2 ^ 64) by exact Rp.
assert (HRG : region_ok SEGS Ec (mrestrict (w_H W3) mem3) sr_preg).
{ unfold region_ok, sr_preg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite OLDc by (cbv; lia). rewrite E10, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o0 Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS Ec _ HA 40 8 _ (sr_p op));
  [cbn [sv_denot]; rewrite OLDc by (cbv; lia); rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact HVP3]. }
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ss ?msx =>
  assert (HDJ : all_disjoint Ev sr_preg (ss_mem ss));
  [ cbn [ss_mem all_disjoint]; split; [|exact I]; unfold extent_disjoint, sr_preg;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Uspc; rewrite OLDc by (cbv; lia);
    rewrite E10, unsigned_lit_small by lia; left; lia
  | pose proof (st_ok_pi_add_region Ev ss msx sr_preg HS eq_refl HRG HDJ) as HS' ] end.
clear HS HDJ. rename HS' into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOKc : sh_ok SEGS sr_Bx sr_SH Ec (mrestrict (w_H W3) mem3)) by (unfold sh_ok, sr_SH; constructor).
paj_run_tok_xR RUNG HS HJ3 SHOKc sr_Bspan.
{ cbn [ms_mem mkst]. rewrite <- (aview_rd_of SEGS). unfold sr_Bx. rewrite !U_SOff. rewrite !OLDc by (cbv; lia).
  rewrite E10, E33, !unsigned_lit_small by (unfold SB; lia).
  rewrite !zcanon_id by (unfold M64, SB; lia). rewrite Z.add_0_r, SB_SHADOW_OFF.
  exact (azs_range_addressable_x B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 (HA + 40) 8 HAR3
    (azs_sub HA ASRC (HA + 40) 8 HZS ltac:(lia) ltac:(unfold ASRC; lia))). }
{ apply awr_ok_x_of0. awr_ok_tac. exact Uspc. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hno. apply (aview_kept_out Ec _ (w_H W3) mem3 (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [sr_preg YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
  rewrite Uspc in Hr. apply Hno. lia. }
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W3) mem3) (mrestrict (w_H W3) (ms_mem ms)) |- _ =>
  assert (PR3 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms) a)
  by (intros a Hpa; exact (apresent_of_grows (w_H W3) mem3 (ms_mem ms) a Hgr Hpa)) end.
pose proof (sr_gx_AR_xR HJ3) as HAR3m.
assert (Usp4 : spZ (ms_regs ms) = spZ regs + -32).
{ unfold spZ. rewrite Q2, Uspc. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
assert (R10f : getr (ms_regs ms) 10 = w64 (sr_p op)) by (rewrite Q10, OLDc by (cbv; lia); exact E32).
assert (S0f : s0Z (ms_regs ms) = HA).
{ unfold s0Z. rewrite Q8, OLDc by (cbv; lia). rewrite E10. apply unsigned_lit_small. lia. }
assert (HCH : chain_pre ly3 (aview SEGS (w_H W3) (ms_mem ms)) (ms_regs ms) []).
{ unfold chain_pre. split; [unfold raZ; rewrite Q1; rewrite unsigned_lit_small by lia; lia|].
  destruct (frame0_ok ly3 (ms_regs ms)); [|reflexivity].
  replace (bad_next (spZ (ms_regs ms)) (ly_top ly3) (s0Z (ms_regs ms))) with true; [reflexivity|].
  symmetry. unfold bad_next. rewrite S0f, Usp4. apply orb_true_iff. left. apply orb_true_iff. left. apply Z.leb_le. lia. }
(* the free call's trace: s0 holds s, so the chain handed to the rule is [] and the trace is the return address *)
assert (HCX : In (raZ (ms_regs ms) :: spine []) CTX).
{ cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_source_reset + 0x54); [exact HCTX_sr_free|].
  unfold raZ. rewrite Q1, unsigned_lit_small by lia. unfold AF_fr_source_reset. lia. }
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, OLDc by (cbv; lia); rewrite E3; exact Hgp).
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, OLDc by (cbv; lia); rewrite E4; exact Htp).
assert (HML123 : mo_le MT S S3 (lf_cost MT (sr_l1 op) + lf_cost MT (sr_l2 op) + lf_cost MT (sr_l3 op)))
by (exact (mle_station MT S S2 S3 _ _ MLAW (mle_station MT S S1 S2 _ _ MLAW HML1 HML2) HML3)).
assert (HMOf : mo_ok MT S3 (mo_free MT))
by (exact (mok_station MT S S3 (sr_cost MT op) _ (mo_free MT) MLAW HMO HML123 MF0 ltac:(lia))).
destruct HJ3 as (HSTK3 & HXO3 & (memS3 & HJi3 & Hag3) & Hout3). rewrite !Z.add_0_r in HJi3.
rewrite HBfree.
lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
eapply (SRrG_bind SEGS R R_trans) with (R := fun W4 c4 => exists ly4 S4 Hp4 regs4 mem4 md4,
  c4 = mkCfg (mkst regs4 (getr rg 1) mem4 (seg_rom SEGS)) md4 /\
  (exists kk, ajournal_xR SEGS B PST ARx R SR_STK (spZ regs) (blk_FP (sr_blks op)) ly S Hp W memS3 md [] ly4 S4 Hp4 W4 mem4 md4 kk) /\
  aregs_preserved rg regs4 /\
  (forall rest, Permutation (ablocks B ly3 S3) ((match op with Some _ => [(sr_p op, APARTIAL)] | None => [] end) ++ rest) ->
   Permutation (ablocks B ly4 S4) rest) /\
  frames S4 = frames S3 /\
  acall_kept SEGS B ly3 S3 W3 mm W4 mem4 (spZ regs + -32 - ASTACK) (spZ regs + -32)
    (fun a => match op with Some _ => sr_p op <= a < sr_p op + req_size APARTIAL | None => False end) /\
  mo_le MT S3 S4 (mo_free MT) /\ rp_RM RP S4 kr /\
  (forall i, 0 <= i < 4 -> aview SEGS (w_H W4) mem4 (as_errno B + i) = aview SEGS (w_H W3) mm (as_errno B + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   apresent (w_H W3) mm a -> apresent (w_H W4) mem4 a))
end.
{ destruct op as [h|] eqn:Eop.
  - eapply (SRrG_mono SEGS R).
    { exact (AFREE_R W3 (ms_regs ms) (ms_mem ms) SR_STK (spZ regs) (blk_FP (sr_blks (Some h))) ly S Hp W memS3 md [] ly3 S3 Hp3 _ _
        (sr_p (Some h)) APARTIAL (-32) (getr (ms_regs ms) 1) [] kr HJi3 HBP3 R10f Usp4 eq_refl ltac:(lia)
        ltac:(unfold SR_STK, LF_STK, ASTACK; lia)
        (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-32) (ms_regs ms) HJi3 Usp4 ltac:(unfold SR_STK, LF_STK, ASTACK; lia))
        HGP HTP eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
        HCH (RO_ARx _ _ _ _ _ _ (proj1 HJi3)) HCX HRM3 HCN3 (fun _ i Hi => HFPof _ _ ltac:(unfold sr_blks, hs_blks; apply in_or_app; right; left; reflexivity) i Hi) HMOf). }
    cbv beta.
    intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Eb1 & Eb2) & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [exists (0 + k1 + k2 + k3 + 1); exact HJ4|].
    split; [exact HP4|].
    split.
    { intros rest Hq. rewrite Eb2. rewrite Eb1 in Hq. cbn [app] in Hq.
      apply Permutation_sym in Hq. apply Permutation_cons_app_inv in Hq. exact (Permutation_sym Hq). }
    split; [exact HFr4|]. split; [exact HK4|]. split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Hi Ho He Hpa. pose proof (proj1 HJ4) as HAR4.
    apply (HPr4 a Hi); [exact (inG_not_owned_img ly3 S3 Hp3 W3 (ms_mem ms) _ a HAR3m Hi Ho)
      | exact (inG_not_owned_img ly4 S4 Hp4 W4 mem4 md4 a HAR4 Hi Ho) | exact He | | exact Hpa].
    intros Hblk. destruct (alx_client_img _ _ _ LAWS ly3 S3 Hp3 W3 (ms_mem ms) _ a HAR3m
      ltac:(left; exists (sr_p (Some h)), APARTIAL; split; [exact HBP3 | exact Hblk])) as [_ Hni]. exact (Hni Hi).
  - eapply (SRrG_mono SEGS R).
    { exact (AFREEN_R W3 (ms_regs ms) (ms_mem ms) SR_STK (spZ regs) (blk_FP (sr_blks None)) ly S Hp W memS3 md [] ly3 S3 Hp3 _ _
        (-32) (getr (ms_regs ms) 1) [] kr HJi3 R10f Usp4 eq_refl ltac:(lia)
        ltac:(unfold SR_STK, LF_STK, ASTACK; lia)
        (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-32) (ms_regs ms) HJi3 Usp4 ltac:(unfold SR_STK, LF_STK, ASTACK; lia))
        HGP HTP eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
        HCH (RO_ARx _ _ _ _ _ _ (proj1 HJi3)) HCX HRM3 HCN3 HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPm & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [exists (0 + k1 + k2 + k3 + 1); exact HJ4|].
    split; [exact HP4|].
    split; [intros rest Hq; cbn [app] in Hq; exact (Permutation_trans HPm Hq)|].
    split; [exact HFr4|]. split; [exact HK4|]. split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Hi Ho He Hpa. pose proof (proj1 HJ4) as HAR4.
    exact (HPr4 a Hi (inG_not_owned_img ly3 S3 Hp3 W3 (ms_mem ms) _ a HAR3m Hi Ho)
      (inG_not_owned_img ly4 S4 Hp4 W4 mem4 md4 a HAR4 Hi Ho) He Hpa). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & (kk4 & HJi4) & HP4 & HPM4 & HFR4 & HK4 & HML4 & HRM4 & HER4 & HPR4).
rewrite Q1.
assert (HJ4 : ajournal_gx_xR SEGS B PST ARx R G 0 [] SR_STK (spZ regs) (blk_FP (sr_blks op)) ly S Hp W mem md [] ly4 S4 Hp4 W4 mem4 md4 kk4).
{ apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] SR_STK (spZ regs) _ ly S Hp W mem md [] ly4 S4 Hp4 W4 mem4 md4 kk4 memS3 HSTK3 HXO3);
  [rewrite !Z.add_0_r; exact HJi4 | exact Hag3 | intros a Ha _; lia]. }
jafter_call_keep_pi HS 82%nat regs4 (mrestrict (w_H W4) mem4) HP4 [1]%nat HS4.
match type of HS4 with ?ty -> _ => assert (HRK : ty); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  lazymatch goal with |- region_kept _ ?Ev _ _ _ =>
    apply (region_kept_sp Ev W3 W4 (ms_mem ms) mem4 2%nat (spZ regs) (-32) 0 (-32) 0 _
      ltac:(repeat (rewrite ew_ewset_other by lia); exact Uspc) ltac:(lia) ltac:(lia)) end.
  - intros a Ha. destruct HK4 as (K1 & _). apply K1; lia.
  - intros a Ha. apply (gx_pres_xR G SR_STK (spZ regs) _ ly S Hp W mem md [] ly4 S4 Hp4 W4 mem4 md4 _ HJ4). lia. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Eh _ _ => remember Eh as Ed eqn:HEd in HS end.
assert (HEId : img_env VAL A_LIM Ed)
by (rewrite HEd; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLDd : forall m0, (m0 < 34)%nat -> ew Ed m0 = ew E m0)
by (intros m0 Hm; rewrite HEd; rewrite YN3v.ew_havoc_old by lia; repeat (rewrite ew_ewset_other by lia); apply OLDc; exact Hm).
assert (HAEd : env_agree 32 (Ereg regs (sr_extra (sr_p op))) Ed).
{ rewrite HEd. apply env_agree_havoc_ge; [cbv; lia|].
  split; [intros m Hm; repeat (rewrite ew_ewset_other by lia); exact (proj1 HAEc m Hm)
        | repeat (rewrite ed_ewset); exact (proj2 HAEc)]. }
assert (Uspd : bv_unsigned (ew Ed 2) = spZ regs) by (rewrite OLDd by (cbv; lia); exact Usp).
assert (HPKd : apres_kept B W mem W4 mem4)
by (exact (apres_kept_trans W W3 W4 mem (ms_mem ms) mem4
  (apres_kept_trans W W3 W3 mem mem3 (ms_mem ms) HPKc (apres_kept_of_pres W3 W3 mem3 (ms_mem ms) PR3)) HPR4)).
assert (HERd : forall i, 0 <= i < 4 ->
  aview SEGS (w_H W4) mem4 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
{ intros i Hi. pose proof (HEL i Hi) as Hei. rewrite (HER4 i Hi).
  rewrite (KEEP3 (as_errno B + i) ltac:(lia) ltac:(lia)). exact (HERc i Hi). }
clear HEd. clear dependent ms.
assert (SHOKd : sh_ok SEGS sr_Bx sr_SH Ed (mrestrict (w_H W4) mem4)) by (unfold sh_ok, sr_SH; constructor).
(* ---- __asan_memset(s, 0, 96) ---- *)
paj_run_tok_xR RUNG HS HJ4 SHOKd sr_Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Uspd. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
(* this run writes only the frame: errno keeps its view *)
assert (KEm : forall i, 0 <= i < 4 ->
  aview SEGS (w_H W4) (ms_mem ms) (as_errno B + i) = aview SEGS (w_H W4) mem4 (as_errno B + i)).
{ intros i Hi. pose proof (HEL i Hi) as Hei.
  apply (aview_kept_out Ed _ (w_H W4) mem4 (ms_mem ms) HFr (as_errno B + i) ltac:(lia)).
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr.
  rewrite Uspd in Hr. lia. }
pose proof (sr_gx_AR_xR HJ4) as HAR4.
assert (Uspm : spZ (ms_regs ms) = spZ regs + -32).
{ unfold spZ. rewrite P2, Uspd. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
assert (HdG96 : forall a, HA <= a < HA + 96 -> inG G a) by (intros a Ha; apply HGL; unfold ASRC; lia).
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_set_gx_at_xR (SIGMA WS_asan_memset) AMEMSET_R W4 (ms_regs ms) (ms_mem ms) SR_STK (spZ regs)
    (blk_FP (sr_blks op)) ly S Hp W mem md [] ly4 S4 Hp4 _ kk4 HA 0 96 (-32) (Z_to_bv 64 (BASE + 13524)) HJ4);
  [ rewrite P10, OLDd by (cbv; lia); exact E10
  | rewrite P11; reflexivity
  | rewrite P12; reflexivity
  | lia | lia | unfold ASRC in HARng; lia
  | exact Uspm | reflexivity | lia | unfold SR_STK, LF_STK, ASTACK, ESTACK; lia
  | rewrite P3, OLDd by (cbv; lia); rewrite E3; exact Hgp | rewrite P4, OLDd by (cbv; lia); rewrite E4; exact Htp
  | rewrite P1; reflexivity | apply ret_ok_codeptr_v; [lia | reflexivity]
  | exact HdG96
  | left; unfold kLowMemEnd in *; lia
  | exact (azs_range_addressable_x B ARx LAWS ly4 S4 Hp4 W4 (ms_mem ms) _ HA 96 HAR4
      (azs_sub HA ASRC HA 96 HZS ltac:(lia) ltac:(unfold ASRC; lia)))
  | intros _; exact (GSHV ly4 S4 Hp4 W4 (ms_mem ms) _ HA 96 HAR4 ltac:(lia) HdG96) ]. }
cbv beta. intros W5 c5 Hwle5 (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HZv & HFrm & HPRm).
(* after the memset: the 96 bytes of the source are zero *)
assert (HPKrun : forall a, apresent (w_H W4) mem4 a -> apresent (w_H W4) (ms_mem ms) a).
{ lazymatch goal with Hgr : mem_grows (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem ms)) |- _ =>
    intros a Hpa; exact (apresent_of_grows (w_H W4) mem4 (ms_mem ms) a Hgr Hpa) end. }
assert (HPKm : apres_kept B W mem W4 mem5).
{ eapply apres_kept_trans; [exact HPKd|].
  eapply apres_kept_trans; [apply apres_kept_of_pres; exact HPKrun | apply apres_kept_of_pres; exact HPRm]. }
(* errno is not a byte of the source (gx_rt keeps it out of G), nor of the stack *)
assert (HERm : forall i, 0 <= i < 4 ->
  aview SEGS (w_H W4) mem5 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
{ intros i Hi. pose proof (HEL i Hi) as Hei.
  rewrite (HFrm (as_errno B + i) ltac:(lia)
    ltac:(intros Hd; exact (proj1 (HGR (as_errno B + i) (HdG96 _ Hd)) ltac:(lia)))
    ltac:(unfold ESTACK; lia)).
  rewrite (KEm i Hi). exact (HERd i Hi). }
(* asrc_closed is re-established at the ret memory below; HZv (the zero view at mem5) carries there *)
jafter_call_keep_pi HS 98%nat regs5 (mrestrict (w_H W4) mem5) HP5 [0]%nat HS5.
match type of HS5 with ?ty -> _ => assert (HRK : ty); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  apply (region_kept_sp Ed W4 W4 (ms_mem ms) mem5 2%nat (spZ regs) (-32) 0 (-32) 0 _ Uspd ltac:(lia) ltac:(lia)).
  - intros a Ha. apply HFrm; [lia | intros [HA1 HA2]; lia | unfold ESTACK; intros [HA1 HA2]; lia].
  - intros a Ha. apply (gx_pres_xR G SR_STK (spZ regs) _ ly S Hp W mem md [] ly4 S4 Hp4 W4 mem5 md5 _ HJ5). lia. }
clear HS. rewrite <- restrict_mkst_fx in HS5. rename HS5 into HS.
remember (havoc Ed 98 (map (getr regs5) CLOB)) as Ee eqn:HEe in HS.
assert (HEIe : img_env VAL A_LIM Ee) by (rewrite HEe; apply img_env_havoc; [exact HEId | cbv; lia]).
assert (OLDe : forall m0, (m0 < 34)%nat -> ew Ee m0 = ew E m0)
by (intros m0 Hm; rewrite HEe; rewrite YN3v.ew_havoc_old by lia; apply OLDd; exact Hm).
assert (HAEe : env_agree 32 (Ereg regs (sr_extra (sr_p op))) Ee) by (rewrite HEe; apply env_agree_havoc_ge; [cbv; lia | exact HAEd]).
clear HEe. clear dependent ms.
assert (SHOKe : sh_ok SEGS sr_Bx sr_SH Ee (mrestrict (w_H W4) mem5)) by (unfold sh_ok, sr_SH; constructor).
(* ---- the epilogue and ret ---- *)
paj_run_tok_xR RUNG HS HJ5 SHOKe sr_Bspan. { apply awr_ok_x_of0. awr_ok_tac. rewrite OLDe by (cbv; lia); exact Usp. }
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
assert (Uspe : bv_unsigned (ew Ee 2) = spZ regs) by (rewrite OLDe by (cbv; lia); exact Usp).
assert (KEEPep : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview SEGS (w_H W4) (ms_mem ms) a = aview SEGS (w_H W4) mem5 a).
{ intros a Ha Hno. apply (aview_kept_out Ee _ (w_H W4) mem5 (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr.
  rewrite Uspe in Hr. apply Hno. lia. }
assert (HALT : forall i, 0 <= i < 96 -> ~ (spZ regs - 32 <= HA + i < spZ regs)).
{ intros i Hi [HA1 HA2].
  pose proof (inG_lo (HA + i) (HGL (HA + i) ltac:(unfold ASRC; lia))) as Hl.
  unfold kLowMemEnd in Hl. unfold SR_STK, LF_STK, ASTACK in *. lia. }
assert (HCLOSEDf : asrc_closed W4 (ms_mem ms) HA).
{ unfold asrc_closed, arm. split.
  - replace (Z.to_nat ASRC) with 96%nat by (unfold ASRC; reflexivity).
    apply (garr8_of_zero_view W4 (ms_mem ms) HA 96). intros i Hi.
    rewrite KEEPep by (first [lia | exact (HALT i Hi)]).
    replace 0 with (0 mod 256) by reflexivity. exact (HZv i Hi).
  - intros i Hi. unfold ASRC in Hi. exact (GX_W (HA + i) (HGL (HA + i) ltac:(unfold ASRC; lia)) _). }
apply (SRr_SRrG SEGS R WLE_R). eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold sr_post_xR.
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly4, S4, Hp4, r, m, d, kk4 end.
split; [cbn [ms_regs]; rewrite R1; rewrite OLDe by (cbv; lia); rewrite E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS pa_segs_low); exact HJ5|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ Ee _ _ regs (sr_extra (sr_p op)) HS); [exact HAEe | vm_compute; reflexivity]|].
split; [exact HCLOSEDf|].
split.
{ intros rest Hq. destruct op as [h|].
  - cbn [sr_blks] in Hq. unfold hs_blks in Hq. cbn [sr_l1 sr_l2 sr_l3 sr_p] in *.
    rewrite <- !app_assoc in Hq.
    pose proof (HPM1 _ Hq) as Hq1.
    pose proof (HPM2 _ (Permutation_trans Hq1
      (Permutation_middle (list_blks (hs_expected h)) (list_blks (hs_held h) ++ rest) (hs_partial h, APARTIAL)))) as Hq2.
    pose proof (HPM3 _ (Permutation_trans Hq2
      (Permutation_middle (list_blks (hs_held h)) rest (hs_partial h, APARTIAL)))) as Hq3.
    exact (HPM4 rest Hq3).
  - cbn [sr_blks sr_l1 sr_l2 sr_l3] in *. cbn [app] in Hq.
    unfold list_blks, empty_list in *. cbn [hl_cap hl_v hl_recs map app Z.eqb Pos.eqb] in *.
    exact (HPM4 rest (HPM3 rest (HPM2 rest (HPM1 rest Hq)))). }
split.
{ eapply apres_kept_trans; [exact HPKm | apply apres_kept_of_pres].
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H W4) mem5) (mrestrict (w_H W4) (ms_mem ms)) |- _ =>
    intros a Hpa; exact (apresent_of_grows (w_H W4) mem5 (ms_mem ms) a Hgr Hpa) end. }
split.
{ intros i Hi. transitivity (aview SEGS (w_H W4) mem5 (as_errno B + i)); [|exact (HERm i Hi)].
  pose proof (HEL i Hi) as Hei. apply KEEPep; lia. }
split; [rewrite HFR4, HFR3, HFR2, HFR1; reflexivity|].
split; [rewrite <- HCsum; exact (mle_station MT S S3 S4 _ _ MLAW HML123 HML4) | exact HRM4].
Qed.
End wR.
End c.
(* source_reset's G-generic form over ARx (W_contract_x.v sr_spec_g_x): every Section hypothesis on G is a conjunct of
   gx_prog_x; the laws, BLKN, HPST, the allocator rules with their caller-context fact, the memset contract and
   list_free's G-generic form stay hypotheses (all G-free). *)
Section g.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Variable RP : roomp.
Hypothesis MLAW : ameter_laws MT.
Hypothesis LF : lf_spec_g_x B PST ARx MT RP (BASE + AF_fr_list_free).
Variable CTX : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AMEMSET : aintrin_realizes_x SEGS B ARx OSet (SIGMA WS_asan_memset).
Hypothesis HCTX_sr_free : In [BASE + AF_fr_source_reset + 0x54] CTX.
Theorem pb_source_reset_g_x : sr_spec_g_x B PST ARx MT RP (BASE + AF_fr_source_reset).
Proof.
intros G (HG & HGR & HRO & GX_ROM & GX_W & GSHV).
change (BASE + AF_fr_source_reset) with A_source_resetP.
eapply pb_source_reset_x with (CTX := CTX); eassumption.
Qed.
End g.
(* route R: pb_source_reset_g_x at a world relation R (R right after ARx), from pb_source_reset_xR *)
Section gR.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Variable RP : roomp.
Hypothesis MLAW : ameter_laws MT.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis LF_R : lf_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_list_free).
Variable CTX : list (list Z).
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Hypothesis AMEMSET_R : aintrin_realizes_xR SEGS B ARx R OSet (SIGMA WS_asan_memset).
Hypothesis HCTX_sr_free : In [BASE + AF_fr_source_reset + 0x54] CTX.
(* :1497 pb_source_reset_g_x *)
Theorem pb_source_reset_g_xR : sr_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_source_reset).
Proof.
intros G (HG & HGR & HRO & GX_ROM & GX_W & GSHV).
change (BASE + AF_fr_source_reset) with A_source_resetP.
eapply pb_source_reset_xR with (CTX := CTX) (R := R) (RO := RO); eassumption.
Qed.
End gR.
(* and with list_free's G-generic form discharged by its walk (W_list_free.v pb_list_free_g_x), whose own Section
   hypotheses join: IMGC (W_kit_x.v), its two free calls' caller-context facts and the memmove contract; its ROM
   form of HPST (PSTR) follows from HPST. *)
Section gc.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Variable RP : roomp.
Hypothesis MLAW : ameter_laws MT.
Variable CTX : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AMEMSET : aintrin_realizes_x SEGS B ARx OSet (SIGMA WS_asan_memset).
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis HCTX_sr_free : In [BASE + AF_fr_source_reset + 0x54] CTX.
Hypothesis HCTX_lf_loop : In [BASE + AF_fr_list_free + 0x98] CTX.
Hypothesis HCTX_lf_exit : In [BASE + AF_fr_list_free + 0xf8] CTX.
Theorem pb_source_reset_gc_x : sr_spec_g_x B PST ARx MT RP (BASE + AF_fr_source_reset).
Proof.
assert (PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST)
by (intros a (sg & Hsg & _ & Hr); apply HPST; exists sg; split; [exact Hsg | exact Hr]).
eapply pb_source_reset_g_x with (CTX := CTX); try eassumption.
eapply W_list_free.pb_list_free_g_x with (CTX := CTX); eassumption.
Qed.
End gc.
(* route R: pb_source_reset_gc_x at a world relation R.  Until a Theorem Labs lane's G6 lands list_free's R walk
   (pb_list_free_g_xR : lf_spec_g_xR ..), list_free's R contract LF_R is this Section's premise (the brief's order);
   when it lands, LF_R is discharged by it, with gc's IMGC / HP0 / AMOVE / HCTX_lf_loop / HCTX_lf_exit. *)
Section gcR.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Variable RP : roomp.
Hypothesis MLAW : ameter_laws MT.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
(* list_free at R: a Theorem Labs lane's pb_list_free_g_xR when it lands *)
Hypothesis LF_R : lf_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_list_free).
Variable CTX : list (list Z).
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Hypothesis AMEMSET_R : aintrin_realizes_xR SEGS B ARx R OSet (SIGMA WS_asan_memset).
Hypothesis HCTX_sr_free : In [BASE + AF_fr_source_reset + 0x54] CTX.
(* :1530 pb_source_reset_gc_x *)
Theorem pb_source_reset_gc_xR : sr_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_source_reset).
Proof.
eapply pb_source_reset_g_xR with (CTX := CTX) (RO := RO); eassumption.
Qed.
End gcR.

(* ---- THE AR STATEMENTS, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_source_reset's, pb_source_reset_g's and
   pb_source_reset_gc's statements are the AR walk's, unchanged, now corollaries of the generic theorems at
   ARx := ARi0 (cgif's AR with the head set empty), PST := [].  The Section takes LX0 (the laws at ARi0, a Theorem Labs lane's
   rulings (a) and HP0) in place of LAWS: the instance builds it once, W_journal_x.AR_laws_x_ARi0
   (YCbqG.AR_laws_x_of_AR ..).  The allocator rules are the caller-context forms (W_journal.v Section hc) with CTX
   and the free call's trace HCTX_sr_free (and list_free's two for the gc form).  Bridges: W_contract_x's
   sr_spec_x_AR0 / sr_spec_g_x_AR0 (conclusion) and lf_spec_g_x_of_AR0 (callee), W_journal_x's
   afree(_null)_cf_rule_c_x_of_AR0, W_sites_x's aintrin_realizes_x_of_AR0 and amemmove_realizes_x_of_AR0;
   BLKN / IMGC are W_kit_x.AR_blkn / AR_imgc, HPST at PST := [] is immediate. ---- *)
Section cAR.
Variable B : asyms.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok SEGS B G.
Hypothesis HGR : gx_rt B G.
Hypothesis GX_ROM : forall a, inG G a -> seg_rom SEGS (Z_to_bv 64 a) <> None.
Hypothesis GX_W : forall a, inG G a -> forall m, writable_at SEGS m a.
Hypothesis GSHV : forall ly S W mem md a n, AR SEGS B ly S W mem md -> 0 < n ->
(forall x, a <= x < a + n -> inG G x) -> shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Hypothesis LF : lf_spec_g B MT (BASE + AF_fr_list_free).
Variable CTX : list (list Z).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX.
Hypothesis AFREEN : afree_null_cf_rule_c SEGS B MT CTX.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA WS_asan_memset).
Hypothesis AMOVE : W_sites.amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis HCTX_sr_free : In [BASE + AF_fr_source_reset + 0x54] CTX.
Hypothesis HCTX_lf_loop : In [BASE + AF_fr_list_free + 0x98] CTX.
Hypothesis HCTX_lf_exit : In [BASE + AF_fr_list_free + 0xf8] CTX.
Hypothesis HRO : rom_out SEGS B G.
(* the generic Sections' hypotheses at ARx := ARi0, PST := [] *)
Local Ltac sr_ari0 :=
  assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0;
  assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
    fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly))
    by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR));
  assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
    by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin));
  assert (HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) (@nil (Z * Z))) by (intros a _ H; inversion H);
  pose proof (afree_cf_rule_c_x_of_AR0 SEGS B MT CTX AFREE) as AFREEx;
  pose proof (afree_null_cf_rule_c_x_of_AR0 SEGS B MT CTX AFREEN) as AFREENx;
  pose proof (aintrin_realizes_x_of_AR0 SEGS B OSet _ AMEMSET) as AMEMSETx.
Theorem pb_source_reset : sr_spec B MT G A_source_resetP.
Proof.
apply sr_spec_x_AR0. sr_ari0.
assert (GSHVx : forall ly S Hp W mem md a n, ARi0 SEGS B ly S Hp W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> inG G x) -> shadow_hull_vis (aview SEGS (w_H W) mem) a n)
  by (intros ly S Hp W mem md a n H; exact (GSHV ly S W mem md a n (proj1 H))).
pose proof (lf_spec_g_x_of_AR0 B MT _ LF) as LFx.
eapply pb_source_reset_x with (CTX := CTX); eassumption.
Qed.
Theorem pb_source_reset_g : sr_spec_g B MT (BASE + AF_fr_source_reset).
Proof.
apply sr_spec_g_x_AR0. sr_ari0.
pose proof (lf_spec_g_x_of_AR0 B MT _ LF) as LFx.
eapply pb_source_reset_g_x with (CTX := CTX); eassumption.
Qed.
Theorem pb_source_reset_gc : sr_spec_g B MT (BASE + AF_fr_source_reset).
Proof.
apply sr_spec_g_x_AR0. sr_ari0.
pose proof (amemmove_realizes_x_of_AR0 B _ AMOVE) as AMOVEx.
eapply pb_source_reset_gc_x with (CTX := CTX); eassumption.
Qed.
End cAR.
End b.
End a.
