(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v, with its module names changed; 414 of its 469 lines of code are new or changed and 578 lines of the source are left out. *)
(* Facts the owe() segments of the image-A walk of LLVMFuzzerTestOneInput share (lib/A/Prog/codec_amain_inv.v, the
   cuts OWE0 .. OWE11 to CHK): the call record k at q = F + 176 after owe() wrote its answer.
   - owe_setZ: k with want_rc, want, want_len, want_key and want_display replaced.
   - owe_k_at_end: k_at of that record in a later memory, from the bytes [q, q + 140) and the unwritten tail of
     want kept, and the written fields read in the later memory.
   - owe_setZ_rec / owe_setZ_kz: owe_setZ keeps every field rec_okZ, enc_kZ and owe_kZ read.
   - owe_want_ok_succ / owe_want_ok_fail: owe_want_okZ of the record owe() leaves, on success and on failure.
   - owe_desk_region / owe_desk_region_ok / owe_desk_shent: the four desk bytes owe() reads at s7 + 8 .. s7 + 11
     (s7 = k.desk, atom 23; read-only, one 1-byte chunk each), from the read-only image and its marks;
     owe_img_frame_apart / owe_desk_apart_base: where they lie (in the image: off every side-stack frame, off the
     base regions of lib/A/Prog/codec_amain_st.v).
   - owe_SHk / owe_k_shent: the shadow entry of k's 184 bytes (marked usable in the loop body), which the engine
     needs for every write window on k; owe_frame_apart_base: a range of the frame is apart from the base regions.
   - owe_zone / owe_chk_end: the end of an OWEk segment at CHK 0x8273c. The walk writes only the cursor's window
     (not changed), want_rc .. want[L] (F + 316 .. F + 320 + L) and want_len .. want_display (F + 344 .. F + 360);
     from the kept fact outside that zone, the final state and the fields read in the final memory, the cut inv_chk
     (am_exit, am_mcut, owe_k_at_end). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_lem codec_amain_st.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AD1y.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ================================ the record owe() leaves ================================ *)
Definition owe_setZ (k : kcallZ) (r : Z) (w : list Z) (l key dp : Z) : kcallZ :=
mkKcallZ (kz_kind k) (kz_p k) (kz_desk k) (kz_a k) (kz_b k) (kz_c k) (kz_delta k)
         (kz_bytes k) (kz_n k) (kz_rc k) (kz_before k) (kz_out k) r w l key dp.

Lemma owe_setZ_rec : forall k od r w l key dp, rec_okZ k od -> rec_okZ (owe_setZ k r w l key dp) od.
Proof. intros k od r w l key dp H. exact H. Qed.

Lemma owe_setZ_kz : forall k od r w l key dp,
owe_kZ (owe_setZ k r w l key dp) od = owe_kZ k od /\ enc_kZ (owe_setZ k r w l key dp) od = enc_kZ k od /\
kz_rc (owe_setZ k r w l key dp) = kz_rc k.
Proof. intros. split; [reflexivity|]. split; reflexivity. Qed.

Lemma owe_want_ok_succ : forall k od w bs key dp,
owe_kZ k od = (0, (bs, key, dp)) -> firstn (length bs) w = map u8 bs ->
owe_want_okZ (owe_setZ k 0 w (Z.of_nat (length bs)) key dp) od.
Proof.
intros k od w bs key dp H Hw. unfold owe_want_okZ.
change (owe_kZ (owe_setZ k 0 w (Z.of_nat (length bs)) key dp) od) with (owe_kZ k od).
rewrite H. cbn [fst snd Z.eqb kz_want_rc kz_want kz_want_len kz_want_key kz_want_display owe_setZ].
split; [reflexivity|]. split; [reflexivity|]. split; [exact Hw|]. split; reflexivity.
Qed.

Lemma owe_want_ok_fail : forall k od w r, fst (owe_kZ k od) = r -> r <> 0 ->
owe_want_okZ (owe_setZ k r w 0 0 0) od.
Proof.
intros k od w r H Hr. unfold owe_want_okZ.
change (owe_kZ (owe_setZ k r w 0 0 0) od) with (owe_kZ k od).
cbn [kz_want_rc kz_want kz_want_len kz_want_key kz_want_display owe_setZ].
split; [symmetry; exact H|]. rewrite H.
destruct (Z.eqb_spec r 0) as [E|E]; [exfalso; exact (Hr E)|]. split; [reflexivity|]. split; reflexivity.
Qed.

(* ================================ the record in a later memory ================================ *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).

Lemma owe_garr8_kept : forall H H' (m m' : word -> option byte) a l,
(forall x, a <= x < a + Z.of_nat (length l) -> aview tfibsegs H' m' x = aview tfibsegs H m x) ->
garr8 tfibsegs (mrestrict H m) a l -> garr8 tfibsegs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (cw_val_mem_kept H H' m m' (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros x Hx. apply Hk. lia.
Qed.

Lemma owe_k_at_end : forall g pos k (W2 : world tfibsegs) mem2 (W3 : world tfibsegs) mem3 r bs l key dp,
k_at g pos k W2 mem2 -> (length bs <= 24)%nat ->
(forall a, FA g pos + 176 <= a < FA g pos + 176 + 140 \/
           FA g pos + 176 + 144 + Z.of_nat (length bs) <= a < FA g pos + 176 + 168 ->
 aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
val_mem tfibsegs (rd W3 mem3) (FA g pos + 176 + 140) 4 r ->
garr8 tfibsegs (rd W3 mem3) (FA g pos + 176 + 144) bs ->
val_mem tfibsegs (rd W3 mem3) (FA g pos + 176 + 168) 8 l ->
val_mem tfibsegs (rd W3 mem3) (FA g pos + 176 + 176) 4 key ->
val_mem tfibsegs (rd W3 mem3) (FA g pos + 176 + 180) 4 dp ->
- 2 ^ 31 <= r < 2 ^ 31 -> 0 <= l < 2 ^ 64 -> 0 <= key < 2 ^ 32 -> - 2 ^ 31 <= dp < 2 ^ 31 ->
k_at g pos (owe_setZ k r (bs ++ skipn (length bs) (kz_want k)) l key dp) W3 mem3.
Proof.
intros g pos k W2 mem2 W3 mem3 r bs l key dp [HK HW] Hbs KE Vr Gbs Vl Vkey Vdp Hr Hl Hkey Hdp.
set (q := FA g pos + 176) in *.
destruct HK as (Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gbytes & Vn & Vrc & Gbefore & Gout &
  _ & Gwant & _ & _ & _).
pose proof HW as (Wkind & Wp & Wdesk & Wa & Wb & Wc & Wdelta & Wn & Wrc & _ & _ & _ & _ &
  Lbytes & Lbefore & Lout & Lwant).
assert (VK : forall o n v, 0 <= o -> o + Z.of_nat n <= 140 ->
  val_mem tfibsegs (rd W2 mem2) (q + o) n v -> val_mem tfibsegs (rd W3 mem3) (q + o) n v).
{ intros o n v Ho Hn Hv. apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3 (q + o) n v); [|exact Hv].
  intros x Hx. apply KE. left. lia. }
assert (GK : forall o l', 0 <= o -> o + Z.of_nat (length l') <= 140 ->
  garr8 tfibsegs (rd W2 mem2) (q + o) l' -> garr8 tfibsegs (rd W3 mem3) (q + o) l').
{ intros o l' Ho Hn Hg. apply (owe_garr8_kept (w_H W2) (w_H W3) mem2 mem3 (q + o) l'); [|exact Hg].
  intros x Hx. apply KE. left. lia. }
assert (Lnew : length (bs ++ skipn (length bs) (kz_want k)) = 24%nat).
{ rewrite length_app, length_skipn, Lwant. lia. }
split.
- unfold kcall_atA. change (FA g pos + 176) with q.
  cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
    kz_want_rc kz_want kz_want_len kz_want_key kz_want_display owe_setZ].
  split; [rewrite <- (Z.add_0_r q); apply VK; [lia | cbn; lia | rewrite Z.add_0_r; exact Vkind]|].
  split; [apply VK; [lia | cbn; lia | exact Vp]|].
  split; [apply VK; [lia | cbn; lia | exact Vdesk]|].
  split; [apply VK; [lia | cbn; lia | exact Va]|].
  split; [apply VK; [lia | cbn; lia | exact Vb]|].
  split; [apply VK; [lia | cbn; lia | exact Vc]|].
  split; [apply VK; [lia | cbn; lia | exact Vdelta]|].
  split; [apply GK; [lia | rewrite Lbytes; cbn; lia | exact Gbytes]|].
  split; [apply VK; [lia | cbn; lia | exact Vn]|].
  split; [apply VK; [lia | cbn; lia | exact Vrc]|].
  split; [apply GK; [lia | rewrite Lbefore; cbn; lia | exact Gbefore]|].
  split; [apply GK; [lia | rewrite Lout; cbn; lia | exact Gout]|].
  split; [exact Vr|].
  split.
  + intros j Hj. rewrite Lnew in Hj.
    destruct (Nat.lt_ge_cases j (length bs)) as [Hlt | Hge].
    * rewrite app_nth1 by exact Hlt. exact (Gbs j Hlt).
    * rewrite app_nth2 by exact Hge. rewrite nth_skipn.
      replace (length bs + (j - length bs))%nat with j by lia.
      assert (Hj' : (j < length (kz_want k))%nat) by (rewrite Lwant; exact Hj).
      destruct (Gwant j Hj') as [Hv Hrg]. split; [|exact Hrg].
      apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3 (q + 144 + Z.of_nat j) 1 (nth j (kz_want k) 0));
      [|exact Hv].
      intros x Hx. apply KE. right. cbn in Hx. lia.
  + split; [exact Vl|]. split; [exact Vkey|]. exact Vdp.
- unfold kcall_wfZ. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
    kz_want_rc kz_want kz_want_len kz_want_key kz_want_display owe_setZ].
  repeat split; first [assumption | lia].
Qed.
End a.

(* ================================ the desk's four bytes at k.desk + 8 ================================ *)
Definition desk_bytesZ (d : desk) : list Z := [d_dev d; d_strips d; d_chars d; d_counter d].
(* vs: the four values as the walk names them (atoms or literals) *)
Definition owe_desk_region (vs : list sv) : YP09.region :=
YP09.mkRegion (Some 23%nat) 8 12 0 0
[YP09.mkChunk 8 (CVal 1 (nth 0 vs (SLit 0))); YP09.mkChunk 9 (CVal 1 (nth 1 vs (SLit 0)));
 YP09.mkChunk 10 (CVal 1 (nth 2 vs (SLit 0))); YP09.mkChunk 11 (CVal 1 (nth 3 vs (SLit 0)))].
Definition owe_desk_SH : shent := mkSHE 23 8 12.

Lemma owe_desk_range : forall pv dv d, pd_okA pv dv (Some d) -> 0x9d6a0 <= dv <= 0x9d6c0.
Proof.
intros pv dv d H. destruct (pd_range_A pv dv d H) as (_ & Hd & _). unfold CM_SPEC_C24, CM_SPEC_PC in Hd. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Lemma owe_desk_region_ok : forall E (W : world tfibsegs) mem pv dv d vs,
arodata_ok B (aview tfibsegs (w_H W) mem) -> pd_okA pv dv (Some d) -> bv_unsigned (ew E 23) = dv ->
(forall i, (i < 4)%nat -> sv_denot E (nth i vs (SLit 0)) = Z_to_bv 64 (nth i (desk_bytesZ d) 0)) ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (owe_desk_region vs).
Proof.
intros E W mem pv dv d vs HR Hpd Hdv Hvs.
pose proof (owe_desk_range pv dv d Hpd) as Hd.
destruct (pd_range_A pv dv d Hpd) as (_ & _ & R0 & R1 & R2 & R3).
assert (VB : forall o, 8 <= o < 12 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (dv + o) 1 (nth (Z.to_nat (o - 8)) (desk_bytesZ d) 0)).
{ intros o Ho. apply val_mem1_of_aviewA.
  pose proof (adesk_bytes_of_pd B TL W mem pv dv d (o - 8) HR Hpd ltac:(lia)) as X.
  replace (dv + 8 + (o - 8)) with (dv + o) in X by lia. exact X. }
unfold region_ok, owe_desk_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hdv.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val tfibsegs E _ dv 8 1 (nth 0 vs (SLit 0)) (nth 0 (desk_bytesZ d) 0));
  [exact (Hvs 0%nat ltac:(lia)) | cbn [desk_bytesZ nth]; zside | zside | exact (VB 8 ltac:(lia))].
- apply (chunk_ok_val tfibsegs E _ dv 9 1 (nth 1 vs (SLit 0)) (nth 1 (desk_bytesZ d) 0));
  [exact (Hvs 1%nat ltac:(lia)) | cbn [desk_bytesZ nth]; zside | zside | exact (VB 9 ltac:(lia))].
- apply (chunk_ok_val tfibsegs E _ dv 10 1 (nth 2 vs (SLit 0)) (nth 2 (desk_bytesZ d) 0));
  [exact (Hvs 2%nat ltac:(lia)) | cbn [desk_bytesZ nth]; zside | zside | exact (VB 10 ltac:(lia))].
- apply (chunk_ok_val tfibsegs E _ dv 11 1 (nth 3 vs (SLit 0)) (nth 3 (desk_bytesZ d) 0));
  [exact (Hvs 3%nat ltac:(lia)) | cbn [desk_bytesZ nth]; zside | zside | exact (VB 11 ltac:(lia))].
Qed.

(* the shadow entry of the four bytes, from their marks in every AR state (adesk_usable_of_pd) *)
Lemma owe_desk_shent : forall ly S (W : world tfibsegs) mem md E pv dv d,
globs_marked tfibsegs B CODEC_GLOBS -> img_shadow_vis tfibsegs B -> AR tfibsegs B ly S W mem md ->
pd_okA pv dv (Some d) -> ew E 23 = Z_to_bv 64 dv -> ew E 32 = Z_to_bv 64 SB ->
shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) mem) owe_desk_SH.
Proof.
intros ly S W mem md E pv dv d GM IV HAR Hpd E23 E32.
pose proof (owe_desk_range pv dv d Hpd) as Hd.
destruct (adesk_usable_of_pd B pv dv d GM IV Hpd) as [HU _].
destruct (HU ly S W mem md HAR) as [Hra _].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold owe_desk_SH. change 12 with (8 + 4).
apply (cw_shent_ra_off W mem E 23 dv 8 4 Hra); [unfold amem_range; rewrite C5; left; lia | lia | lia | lia | lia
  | exact E23 | exact E32].
Qed.

(* an image range [x, x + n) and a range [lo, hi) of a side-stack frame of the state are apart (al_client_img) *)
Lemma owe_img_frame_apart : forall ly S (W : world tfibsegs) mem md cid pos x n lo hi,
AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) ->
0x10000 <= x -> x + n <= 0x5fb000 -> 0 < n -> 0 <= lo < hi -> hi <= fs_frame_bytes cid ->
frame_addr ly cid pos + hi <= x \/ x + n <= frame_addr ly cid pos + lo.
Proof.
intros ly S W mem md cid pos x n lo hi HAR Hin Hx Hxn Hn Hlo Hhi.
set (F := frame_addr ly cid pos).
destruct (Z_le_gt_dec (F + hi) x) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (x + n) (F + lo)) as [H2|H2]; [right; exact H2|].
exfalso.
assert (Ha : exists a, x <= a < x + n /\ F <= a < F + fs_frame_bytes cid).
{ destruct (Z_le_gt_dec x (F + lo)) as [H3|H3]; [exists (F + lo) | exists x]; split; lia. }
destruct Ha as (a & Ha1 & Ha2).
pose proof (al_client_img _ _ LAWS ly S W mem md a HAR
  (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Ha2)))))) as [_ Hni].
apply Hni. apply AD1y.in_img_hull. lia.
Qed.
End d.

(* the desk region is apart from the base regions of codec_amain_st.v (the save area, the .got slot, the shadow
   cell, the spills and the cursor) *)
Lemma owe_desk_apart_base : forall E vs dv spv, bv_unsigned (ew E 23) = dv -> 0x9d6a0 <= dv <= 0x9d6c0 ->
bv_unsigned (ew E 2) = spv -> 2 ^ 46 <= spv ->
all_disjoint E (owe_desk_region vs) am_regs.
Proof.
intros E vs dv spv H23 Hd H2 Hsp.
unfold am_regs, am_regs0, cw_regs, am_spill_region, am_cur_region, stack_region, got_region, bcell_region,
  owe_desk_region.
cbn [app all_disjoint]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite H23, H2. unfold A_GOT_shadow, A_shadow_glob.
repeat split; lia.
Qed.

(* ================================ k's shadow entry, the frame's ranges, the end at CHK ================================ *)
Definition owe_SHk : shent := mkSHE 33 176 360.
(* the bytes an OWEk segment may write: the cursor's window (kept by its chunks), want_rc and want[0 .. L), and
   want_len .. want_display *)
Definition owe_zone (g : ectx) (pos sp1 L a : Z) : Prop :=
(sp1 + 152 <= a < sp1 + 168) \/ (FA g pos + 316 <= a < FA g pos + 320 + L) \/
(FA g pos + 344 <= a < FA g pos + 360).

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis LAWS : AR_laws tfibsegs B.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* the side-stack frame of a cut lies in application memory *)
Lemma owe_frame_app : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 kj,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
in_app (FA g pos) 512.
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as (EFA & _).
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Happ).
rewrite EFA in Happ. change (fs_frame_bytes 3) with 512 in Happ. exact Happ.
Qed.

(* k's 184 bytes are marked usable at every cut of the loop body (kv = 0): the engine's shadow entry for them *)
Lemma owe_k_shent : forall g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
shent_ok tfibsegs CW_Bx (am_env g pos c regs2 ys) (rd W2 mem2) owe_SHk.
Proof.
intros g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys HJ Hfr HC.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & _).
pose proof (owe_frame_app g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as Happ.
pose proof (am_bs_k B MT K XM_LIB g pos sp1 ly2 S2 W2 regs2 mem2 md2 HC) as HBS.
pose proof (block_shadow_range (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (FA g pos + 176) 184 (FA g pos + 176) 184
  HBS ltac:(lia) ltac:(lia)) as Hra.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
change (fs_frame_bytes 3) with 512 in Hfceil.
assert (Ham : amem_range (FA g pos + 176) 184) by (unfold AM_HI in *; appn; lia).
unfold owe_SHk. change 360 with (176 + 184).
apply (cw_shent_ra_off W2 mem2 (am_env g pos c regs2 ys) 33 (FA g pos) 176 184 Hra Ham);
  [lia | lia | lia | unfold AM_HI in *; lia | exact (am_ew_F g pos c regs2 ys) | exact (am_ew_SB g pos c regs2 ys)].
Qed.

(* a range of the frame is apart from the base regions (the save area, the .got slot, the shadow cell, the spills,
   the cursor) *)
Lemma owe_frame_apart_base : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 kj c ys lo hi wlo whi cs,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
0 <= lo < hi -> hi <= 448 ->
all_disjoint (am_env g pos c regs2 ys) (am_frame_region lo hi wlo whi cs) am_regs.
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 kj c ys lo hi wlo whi cs HJ Hfr HC Hlo Hhi.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
change (fs_frame_bytes 3) with 512 in Hfceil.
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos A_GOT_shadow 8 lo hi HAR Hin) as G1.
pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos A_shadow_glob 8 lo hi HAR Hin) as G2.
rewrite EFA in G1, G2. unfold A_GOT_shadow, A_shadow_glob in G1, G2.
change (fs_frame_bytes 3) with 512 in G1, G2.
specialize (G1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
specialize (G2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
pose proof HC as (_ & _ & R2 & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
unfold AM_HI in *.
assert (U2 : bv_unsigned (ew (am_env g pos c regs2 ys) 2) = sp1).
{ rewrite (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew (am_env g pos c regs2 ys) 33) = FA g pos).
{ rewrite (am_ew_F g pos c regs2 ys). apply unsigned_lit_small. lia. }
unfold am_regs, am_regs0, cw_regs, am_spill_region, am_cur_region, stack_region, got_region, bcell_region,
  am_frame_region.
cbn [app all_disjoint]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UF, U2. unfold A_GOT_shadow, A_shadow_glob.
repeat split; lia.
Qed.

(* The end of an OWEk segment at CHK: from the start cut's parts, the final journal and state, the kept fact outside
   owe_zone and the want fields read in the final memory, the cut inv_chk. The segment gives the fields from its
   regions' chunks (ACep.field_of_region_any) and owe_want_okZ from owe_spec. *)
Lemma owe_chk_end : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc od L mem3 regs3 md3 E ss r bs l key dp,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos kc W2 mem2 -> rec_okZ kc od ->
kz_rc kc = fst (enc_kZ kc od) ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem3 md3 kj ->
env_agree 37 (am_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs))) ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
nth_error (ss_mem ss) 4 = Some am_cur_region ->
L = Z.of_nat (length bs) -> (length bs <= 24)%nat ->
(forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 L a ->
 aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
val_mem tfibsegs (rd W2 mem3) (FA g pos + 316) 4 r -> garr8 tfibsegs (rd W2 mem3) (FA g pos + 320) bs ->
val_mem tfibsegs (rd W2 mem3) (FA g pos + 344) 8 l -> val_mem tfibsegs (rd W2 mem3) (FA g pos + 352) 4 key ->
val_mem tfibsegs (rd W2 mem3) (FA g pos + 356) 4 dp ->
- 2 ^ 31 <= r < 2 ^ 31 -> 0 <= l < 2 ^ 64 -> 0 <= key < 2 ^ 32 -> - 2 ^ 31 <= dp < 2 ^ 31 ->
owe_want_okZ (owe_setZ kc r (bs ++ skipn (length bs) (kz_want kc)) l key dp) od ->
SRr tfibsegs W2 (mkCfg (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs)) md3)
  (inv_chk B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc od L mem3 regs3 md3 E ss r bs l key dp
  HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJ3 HAE HS Hkeep H26 Hcur4 HL Hbs KE Vr Gbs Vl Vkey Vdp
  Hr Hl Hkey Hdp Hwant.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & _).
pose proof (owe_frame_app g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as Happ.
change (fs_frame_bytes 3) with 512 in Hfceil.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold AM_HI in *.
assert (HL24 : L <= 24) by lia.
pose proof HAE as (HA & HD).
assert (HAE35 : env_agree 35 (am_env g pos c regs2 ys) E) by (split; [intros nn Hnn; apply HA; lia | exact HD]).
pose proof HC as (_ & _ & R2 & _).
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
pose proof HC as HPm. do 45 (destruct HPm as (_ & HPm)).
assert (D8 : 0 <= FA g pos / 8 /\ 8 * (FA g pos / 8) <= FA g pos)
  by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
assert (Hzsh : forall i, 0 <= i < 56 -> ~ owe_zone g pos sp1 L (shadow_addr (FA g pos) + i)).
{ intros i Hi Hz. unfold owe_zone, shadow_addr, SHADOW_OFF in Hz. appn. lia. }
apply SRr_ret.
change (mkCfg (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs)) md3)
  with (cfg_at tfibsegs PC_CHK regs3 mem3 md3).
unfold inv_chk.
apply (am_mcut B MT K XM_LIB g pos sp1 0 PC_CHK _ ly2 S2 W2 regs3 mem3 md3 kj HJ3 Hfr Hk Hmo).
- apply (am_exit B MT K XM_LIB LAWS g pos sp1 0 0 c ys ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs3 mem3 md3 kj
    (Z_to_bv 64 PC_CHK) ss E HC HJ3 HAE35 HS Hkeep).
  + intros a Ha. apply KE; [unfold am_keepzone in Ha; lia | intros Hz; unfold am_keepzone, owe_zone in Ha, Hz; lia].
  + intros i Hi. rewrite (KE (shadow_addr (FA g pos) + i)); [exact (HSH i Hi) | unfold shadow_addr, SHADOW_OFF; lia |
      exact (Hzsh i Hi)].
  + exact HPm.
- cbv beta. split.
  { destruct Hops as [Hops1 Hops2]. split; [exact Hops1|].
    pose proof (st_ok_restrict_reg tfibsegs (w_H W2) E ss (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs))
      26%bv HS) as R26.
    change (getr (ms_regs (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs))) 26%bv) with (getr regs3 26%bv)
      in R26.
    rewrite R26, H26. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite (HA 26%nat ltac:(lia)), (am_ew_reg g pos c regs2 ys 26 26%bv eq_refl). exact Hops2. }
  exists c, (owe_setZ kc r (bs ++ skipn (length bs) (kz_want kc)) l key dp), od.
  split.
  { pose proof (st_ok_region_nth E ss _ 4 am_cur_region HS Hcur4) as Hrc4.
    rewrite restrict_mkst_fx in Hrc4. cbn [ms_mem] in Hrc4.
    unfold am_cur_region in Hrc4.
    assert (U2 : bv_unsigned (ew E 2) = sp1).
    { rewrite (HA 2%nat ltac:(lia)), (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64.
      apply unsigned_lit_small. lia. }
    destruct Hcur as (Hc & _ & _).
    split; [exact Hc|]. split.
    - apply (field_of_region E _ 2%nat sp1 _ 152 168 152 168 152 8 (SOff 35 0) (e_p g + c) Hrc4 U2);
      [left; reflexivity | | lia | lia].
      cbn [sv_denot]. rewrite (HA 35%nat ltac:(lia)), (am_ew_CP g pos c regs2 ys), Z.add_0_r, Z_to_bv_bv_unsigned.
      reflexivity.
    - apply (field_of_region E _ 2%nat sp1 _ 152 168 152 168 160 8 (SOff 36 0) (e_n g - c) Hrc4 U2);
      [right; left; reflexivity | | lia | lia].
      cbn [sv_denot]. rewrite (HA 36%nat ltac:(lia)), (am_ew_CN g pos c regs2 ys), Z.add_0_r, Z_to_bv_bv_unsigned.
      reflexivity. }
  split.
  { apply (owe_k_at_end g pos kc W2 mem2 W2 mem3 r bs l key dp Hkat Hbs).
    - intros a Ha. apply KE; [lia | intros Hz; unfold owe_zone in Hz; lia].
    - replace (FA g pos + 176 + 140) with (FA g pos + 316) by lia. exact Vr.
    - replace (FA g pos + 176 + 144) with (FA g pos + 320) by lia. exact Gbs.
    - replace (FA g pos + 176 + 168) with (FA g pos + 344) by lia. exact Vl.
    - replace (FA g pos + 176 + 176) with (FA g pos + 352) by lia. exact Vkey.
    - replace (FA g pos + 176 + 180) with (FA g pos + 356) by lia. exact Vdp.
    - exact Hr.
    - exact Hl.
    - exact Hkey.
    - exact Hdp. }
  split; [apply owe_setZ_rec; exact Hrec|].
  split; [destruct (owe_setZ_kz kc od r (bs ++ skipn (length bs) (kz_want kc)) l key dp) as (_ & E2 & E3);
    rewrite E2, E3; exact Hrc|].
  exact Hwant.
Qed.
End e.

(* ================================ the walk's helpers for an OWEk segment ================================
   The state of an OWEk segment is am_entry's base (regions 0-4: the save area, the .got slot, the shadow cell, the
   spills, the cursor) and three frame regions: k's fields read (index 5), want_rc .. want[L) (index 6, window
   [316, 320 + L)) and want_len .. want_display (index 7, window [344, 360)), with KE over owe_zone L. *)
(* `lw` of a 4-byte field s: the sign-extended value (lib/A/Prog/check_range_A.v:41-54, cg_U_sx32) *)
Lemma owe_U_sx32 : forall E n s, ew E n = Z_to_bv 64 s -> 0 <= s < 2 ^ 32 ->
U E (SExt true 32 (SOff n 0)) = if s <? 2 ^ 31 then s else s + (2 ^ 64 - 2 ^ 32).
Proof.
intros E n s Hn Hs. rewrite U_SExt. cbv iota beta. rewrite (U_atom E n s Hn) by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small s) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
destruct (Z.ltb_spec s (2 ^ 31)).
- rewrite (Z.mod_small (s + 2 ^ 31)) by lia. replace (s + 2 ^ 31 - 2 ^ 31) with s by lia. rewrite Z.mod_small by lia. reflexivity.
- replace (s + 2 ^ 31) with ((s - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (s - 2 ^ 31)) by lia.
  replace (s - 2 ^ 31 - 2 ^ 31) with ((s + (2 ^ 64 - 2 ^ 32)) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
(* the bytes of a field read back modulo the field's width *)
Lemma owe_vm : forall m a (n : nat) u v, val_mem tfibsegs m a n u ->
u mod 2 ^ (8 * Z.of_nat n) = v mod 2 ^ (8 * Z.of_nat n) -> val_mem tfibsegs m a n v.
Proof. intros m a n u v H Heq k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite Heq. reflexivity. Qed.
(* a 2-byte field as its two bytes *)
Lemma owe_split2 : forall m a u v, val_mem tfibsegs m a 2 u -> u mod 2 ^ 16 = v -> 0 <= v < 2 ^ 16 ->
val_mem tfibsegs m a 1 (v mod 256) /\ val_mem tfibsegs m (a + 1) 1 (v / 256).
Proof.
intros m a u v V Hu Hv. split; intros k Hk; (destruct k as [|k]; [|lia]).
- rewrite (V 0%nat ltac:(lia)). unfold YO0f.le_byte. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 1) with 8.
  change (8 * Z.of_nat 0) with 0. rewrite Hu, !Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia.
  reflexivity.
- replace (a + 1 + Z.of_nat 0) with (a + Z.of_nat 1) by lia. rewrite (V 1%nat ltac:(lia)). unfold YO0f.le_byte.
  change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Hu, Z.shiftr_0_r, Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  assert (Hd : 0 <= v / 256 < 256) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite !(Z.mod_small (v / 256) 256) by exact Hd.
  reflexivity.
Qed.
(* three bytes read back as a byte array *)
Lemma owe_garr3 : forall m a x0 x1 x2, val_mem tfibsegs m a 1 x0 -> val_mem tfibsegs m (a + 1) 1 x1 ->
val_mem tfibsegs m (a + 2) 1 x2 -> 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> garr8 tfibsegs m a [x0; x1; x2].
Proof.
intros m a x0 x1 x2 V0 V1 V2 R0 R1 R2 j Hj. cbn [length] in Hj.
destruct j as [|[|[|j]]]; cbn [nth].
- rewrite Z.add_0_r. split; assumption.
- change (Z.of_nat 1) with 1. split; assumption.
- change (Z.of_nat 2) with 2. split; assumption.
- lia.
Qed.
Lemma owe_u8_range : forall x, 0 <= u8 x < 256.
Proof. intros x. unfold u8. apply Z.mod_pos_bound. lia. Qed.

(* the write windows of the state lie in owe_zone (U2 / UF: atoms 2 and 33 are sp1 and F) *)
Ltac owe_kwr U2 UF :=
  idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta; unfold owe_zone;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U2, ?UF in Hb; lia | ]);
  destruct Hr.
(* every write window is the cursor's (the caller's stack allowance) or a range of the entry's own frame *)
Ltac owe_awr sp1v sp0v posv Fv U2 UF EFA :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp1v - sp0v));
    [reflexivity | rewrite U2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat Fv);
    [ reflexivity | exact UF
    | let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists 3, posv;
      split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; rewrite EFA;
      change (fs_frame_bytes 3) with 512; lia
    | ] ].
(* the region i of the state, by computation *)
Ltac owe_region HS i Hr :=
  lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
    let r := eval vm_compute in (nth i (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    assert (Hr : region_ok tfibsegs E (ms_mem ms) r) by (apply (st_ok_region_nth E ss ms i r HS); vm_compute; reflexivity)
  end.
Ltac owe_in := repeat (first [left; reflexivity | right]).
(* at the stop: the machine state as a mkst, regions 6 / 7, and the fields want_rc, want_len, want_key,
   want_display (V316, V344, V352, V356) *)
Ltac owe_fields HS UF Hrw Hrl :=
  let Ems := fresh "Ems" in
  pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Ems; rewrite Ems in HS; rewrite Ems; clear Ems;
  owe_region HS 6%nat Hrw; owe_region HS 7%nat Hrl;
  rewrite restrict_mkst_fx in Hrw, Hrl; cbn [ms_mem] in Hrw, Hrl;
  unfold am_frame_region in Hrw, Hrl;
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 316 4 _ Hrw UF ltac:(owe_in) ltac:(lia)) as V316;
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 344 8 _ Hrl UF ltac:(owe_in) ltac:(lia)) as V344;
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 352 4 _ Hrl UF ltac:(owe_in) ltac:(lia)) as V352;
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 356 4 _ Hrl UF ltac:(owe_in) ltac:(lia)) as V356.
(* one field of region Hr at offset off, width w *)
Ltac owe_fld Hr UF off w V := pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ off w _ Hr UF ltac:(owe_in) ltac:(lia)) as V.
(* a byte kept as an atom of the state (DX: an atom's value as an sv, X: the atom's value) *)
Ltac owe_byte V DX X :=
  lazymatch goal with |- val_mem _ _ ?x _ _ => lazymatch type of V with val_mem _ _ ?y _ _ =>
    replace x with y by lia end end;
  apply (owe_vm _ _ 1 _ _ V); rewrite (DX _ _ X), unsigned_lit_small by lia;
  change (2 ^ (8 * Z.of_N 1)) with 256; change (2 ^ (8 * Z.of_nat 1)) with 256; rewrite Z.mod_mod by lia;
  reflexivity.
Ltac owe_old3 V0 V1 V2 DX X0 X1 X2 Q0 Q1 Q2 :=
  apply owe_garr3; [owe_byte V0 DX X0 | owe_byte V1 DX X1 | owe_byte V2 DX X2 | exact Q0 | exact Q1 | exact Q2].
