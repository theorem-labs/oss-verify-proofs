(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths and module names changed; 428 of its 517 lines of code are new or changed and 925 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgW6cTail.v, with its addresses and numbers changed; 228 of its 404 lines of code are new or changed and 341 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6cTail.v at 4c23b042570d for reac-pw/fuzz_rate's
   image A: module paths changed; the pcs, the code table and the statements move to lib/A/RtPgW6cBase.v (rate's
   pcs: the memcpy 0x51860 returning to the `j J` at 0x81cdc, the memset 0x51cfc returning to 0x81c00); rate's join
   keeps the cursor in s9 and what is left in s8 (registers, no frame cell) and s6 = the shadow address of &pp->len,
   so the memset tail is `mv s8,s6; ld s6,0xe8(s1); j J` and the join's post names s6, s8, s9 and no cell; the
   intrinsic adapter is RtPgSteps.rts_intrin_at; role's RPgMem / RPgCfgChanges names become rate's RtPgMem /
   RtPgSteps ones; the frame's shadow flags are rate's seven. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6cTail.v at cb9cdc023f20; image B
   (fuzz_rate.asan-ubsan): the statements are lib/AU/RtPgW6cBaseB.v's; the intrinsics are __asan_memcpy 0x518b8
   (return 0x81f40) and __asan_memset 0x51d54 (return 0x81d84) by RtPgStepsB.rtsb_intrin_at; the pod is e62 =
   F + 0x210 (destination F + 0x218, its shadow from rsb_PJ by RtPgMemB.rtmb_B_ra_e62); the frame for locals is
   class 4 (1024 bytes, 128 shadow bytes, write rights by RtPgStepsB.rtsb_awr_fobj); both tails read s2 back from the
   cell R + 0x158 (one region at s1, no write window), and the join's post names t1, s2, s6 and s10. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6cTailB.v at 05426fac6916 for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths changed (lib/AU/Img0.rsegs, lib/A/RPgBase and
   RPgCSpec, lib/AU/RPgMem / RPgSteps / RPgSeg names); the statements are lib/AU/RPgW6cBase.v's; the intrinsics are
   __asan_memcpy 0x5116c (return 0x81738) and __asan_memset 0x51608 (return 0x81584) by RPgSteps.rl_intrin_at; the
   memcpy tail is `mv a3,s8; mv t1,s4; ld a5,0x140(s1); j J` and the memset tail `mv t1,s6; mv a3,s2;
   ld s6,0x130(s1); j 0x81740; ld a5,0x140(s1); j J`, so the tails read pp (and the memset tail pp + 0x4000) from
   the real frame's cells [R+0x140] and [R+0x130] (one region at s1 each, no write window, the values extra atoms 32
   and 33), and the join's post names t1, a3, s6 and a5; the real frame is 0x200 bytes. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the two calls that end
   ent_build's cases 6, 7 and 8 (pod.h:347, 356, 364) and the jumps to the join J 0x818d8. Proves no function (kind:
   segment lemma): the callees are the Section hypotheses AMEMCPY / AMEMSET, the kernel's YG0d.aintrin_realizes at
   __asan_memcpy 0x5116c and __asan_memset 0x51608.

   THE CODE (listing of image B; s1 = R the real frame's base, [R+0x130] = pp + 0x4000 = &pp->len, [R+0x140] = pp).
     cases 6, 7:  0x81730 a1 := s2; 0x81734 jal __asan_memcpy (e62.body, the input at the cursor, n);
                  0x81738 mv a3,s8; 0x8173c mv t1,s4; 0x81740 ld a5,0x140(s1); 0x81744 j J
     case 8:      0x81570 e62.size := a2; a0 := a4 (= F + 0x218); a1 := 0; 0x81580 jal __asan_memset;
                  0x81584 mv t1,s6; 0x81588 mv a3,s2; 0x8158c ld s6,0x130(s1); 0x81590 j 0x81740;
                  0x81740 ld a5,0x140(s1); 0x81744 j J
   The case heads run up to the callee's entry; this file takes the call and the rest, to RPgW6cBase.w6cb_jpost:
   the journal (no event), the I/O state, the registers the cut J keeps, t1 = what is left, a3 = the cursor,
   s6 = &pp->len, a5 = pp, every byte outside the callee's stack [R - ESTACK, R) and e62 (F + 0x210, 104 bytes)
   kept, and e62's bytes. Neither tail has a trap branch or an instrumented check: the only error paths are inside
   the two runtime routines, which their contracts exclude under the premises given here (the destination e62.body
   marked usable by the frame's shadow at J's cut, the source the input's bytes marked usable). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgMem RPgSteps RPgSeg RPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgW6cBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Lemma w6cb_ret_cpy : YK0s.ret_ok (Z_to_bv 64 W6CB_RCPY).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma w6cb_ret_set : YK0s.ret_ok (Z_to_bv 64 W6CB_RSET).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

(* the registers the cut J keeps are callee-saved (or sp, gp, tp) *)
Lemma w6cb_keep_saved : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
forall r, In r w6cb_keep -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP.
cbv [w6cb_keep In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<-|Hr];
  [match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia|]).
destruct Hr.
Qed.

(* e62's bytes after the two header stores and a copy of bs into the body, and after a fill of zeros *)
Lemma w6cb_skipn_repeat : forall {A} (x : A) n m, skipn n (repeat x m) = repeat x (m - n).
Proof. intros A x n. induction n as [|n IH]; intros [|m]; cbn; try reflexivity. apply IH. Qed.
Lemma w6cb_ent_cpy : forall ty sz (bs : list byte), (length bs <= Z.to_nat sz)%nat -> (Z.to_nat sz <= 96)%nat ->
Model.overwrite (le32 ty ++ le32 sz ++ zeros 96) 8 bs = ent_mem (Ent ty sz (bs ++ zeros (Z.to_nat sz - length bs))).
Proof.
intros ty sz bs H1 H2.
assert (L8 : length (le32 ty ++ le32 sz) = 8%nat) by (rewrite length_app, !length_le32; reflexivity).
unfold Model.overwrite. rewrite (app_assoc (le32 ty) (le32 sz) (zeros 96)).
rewrite firstn_app, L8, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia.
rewrite skipn_app, L8. rewrite (skipn_all2 (le32 ty ++ le32 sz)) by lia. cbn [app].
replace (8 + length bs - 8)%nat with (length bs) by lia.
unfold zeros. rewrite w6cb_skipn_repeat.
unfold ent_mem. cbn [e_type e_size e_body]. rewrite <- app_assoc. do 2 f_equal.
rewrite length_app, repeat_length, <- app_assoc, <- repeat_app. do 2 f_equal. lia.
Qed.
Lemma w6cb_ent_set : forall ty sz, (Z.to_nat sz <= 96)%nat ->
le32 ty ++ le32 sz ++ zeros 96 = ent_mem (Ent ty sz (zeros (Z.to_nat sz))).
Proof.
intros ty sz H. unfold ent_mem. cbn [e_type e_size e_body]. do 2 f_equal.
rewrite length_zeros. unfold zeros. rewrite <- repeat_app. f_equal. lia.
Qed.
Lemma w6cb_ow_zeros : forall ty sz, (Z.to_nat sz <= 96)%nat ->
Model.overwrite (le32 ty ++ le32 sz ++ zeros 96) 8 (zeros (Z.to_nat sz)) = le32 ty ++ le32 sz ++ zeros 96.
Proof.
intros ty sz H. rewrite w6cb_ent_cpy by (rewrite ?length_zeros; lia).
rewrite length_zeros, Nat.sub_diag. change (zeros 0) with (@nil byte). rewrite app_nil_r.
symmetry. apply w6cb_ent_set. exact H.
Qed.

Lemma w6cb_F8 : forall F, F mod 32 = 0 -> F mod 8 = 0.
Proof.
intros F HF. destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF) as [q Hq]. rewrite Hq.
replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult.
Qed.

(* the frame's shadow pattern at a case entry: e62's 13 granules in scope, the rest the prologue's *)
Lemma w6cb_PJ : rs_PJ = rm_sh false false false false false true false.
Proof. vm_compute. reflexivity. Qed.

(* the regions the tails read pp (atom 32) and pp + 0x4000 (atom 33) from; no write window *)
Definition w6cb_RSp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x140 0x148 0 0 [YP09.mkChunk 0x140 (CVal 8 (SOff 32 0))].
Definition w6cb_RSq : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x130 0x148 0 0
    [YP09.mkChunk 0x130 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x140 (CVal 8 (SOff 32 0))].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a run over one region without a write window keeps every byte *)
Lemma w6cb_kept_ro : forall E (r : YP09.region) (H : word -> bool) m m', YP09.r_whi r <= YP09.r_wlo r ->
frame_of E [r] m m' -> forall a, aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E r H m m' Hw HF a. apply (aview_eq_of rsegs). unfold mrestrict. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r' & [<-|[]] & Hr). lia.
Qed.

(* the shadow hull of [F + o, F + o + n) inside e62 (granules 66 .. 78) lies in the frame's 128 shadow bytes *)
Lemma w6cb_hull_e62 : forall (rd : reader) F o n, F mod 32 = 0 -> 0 <= F -> 0x210 <= o -> o + n <= 0x278 -> 0 < n ->
(forall i, 0 <= i < 128 -> rd (shadow_addr F + i) <> None) -> shadow_hull_vis rd (F + o) n.
Proof.
intros rd F o n HF H0 Ho Hn Hn0 Hsh s Hs.
assert (E1 : forall c, 0 <= c -> shadow_addr (F + c) = shadow_addr F + c / 8).
{ intros c Hc. unfold shadow_addr.
  destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF) as [q Hq]. rewrite Hq.
  replace (q * 32 + c) with (c + (4 * q) * 8) by lia. rewrite Z.div_add by lia.
  replace (q * 32) with ((4 * q) * 8) by lia. rewrite Z.div_mul by lia. lia. }
replace (F + o + n - 1) with (F + (o + n - 1)) in Hs by lia.
rewrite (E1 o) in Hs by lia. rewrite (E1 (o + n - 1)) in Hs by lia.
set (X := shadow_addr F) in *.
assert (A1 : 66 <= o / 8) by (apply Z.div_le_lower_bound; lia).
assert (A2 : (o + n - 1) / 8 < 79) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (X + o / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (X + o / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (X + (o + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (X + (o + n - 1) / 8) 8 ltac:(lia)).
replace s with (X + (s - X)) by lia. apply Hsh. lia.
Qed.

Section d.
Variable B : asyms.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6CB_CPY.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6CB_SET.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

(* the frame's facts every tail uses: the class-4 frame (4, pos), 1024 bytes and 128 shadow bytes *)
Lemma w6cb_frame : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> w6cb_geo STK sp0 own lyc R F pos ->
F + 1024 <= alloc_ceiling /\ 4096 <= F /\ F + 1024 <= 2 ^ 47 /\ alloc_ceiling <= R - T_SEG_STK /\ sp0 mod 16 = 0 /\
sp0 <= 2 ^ 47 /\
(forall i, 0 <= i < 128 -> aview rsegs (w_H W) memc (shadow_addr F + i) <> None) /\
(forall a, F <= a < F + 1024 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ (HR16 & HSTK & HRS & HRk & Hown & HF & HFapp & HF32).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HSTK0 & Hceil & Hlo & Hhi & H47 & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & _ & _ & HFS).
change (fs_frame_bytes 4) with 1024 in *. change (1024 / 8) with 128 in HFS. rewrite <- HF in HF4096, HFceil, HFS.
pose proof alloc_ceiling_lt as Hc47.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|].
split; [intros i Hi; apply (aview_some_of_apresent rsegs); exact (proj1 (HFS i Hi))|].
intros a Ha. apply (rl_awr_fobj STK sp0 FP _ _ lyc own pos a Hown). rewrite <- HF. exact Ha.
Qed.

(* the join from the engine's last state *)
Lemma w6cb_leaf : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F ed cur' nl' pp E ss ms md,
st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = W6CB_J ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k -> same_io mdc md ->
(forall r, In r w6cb_keep -> getr (ms_regs ms) r = getr regs r) ->
getr (ms_regs ms) 6 = w64 nl' -> getr (ms_regs ms) 13 = w64 cur' -> getr (ms_regs ms) 22 = w64 (pp + 0x4000) ->
getr (ms_regs ms) 15 = w64 pp ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0x210 <= a < F + 0x278) ->
 aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
rm_bytes rsegs (w_H W) (ms_mem ms) (F + 0x210) (ent_mem ed) ->
SRr rsegs W (mkCfg ms md) (w6cb_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F ed cur' nl' pp).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F ed cur' nl' pp E ss ms md
HS Hrv Hpc HJ Hio Hk H6 H13 H22 H15 Hm He.
apply SRr_ret. exists (ms_regs ms), (ms_mem ms), md. split; [reflexivity|].
split; [unfold cfg_at, w64; rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv) at 1; rewrite Hpc; reflexivity|].
repeat (split; [eassumption|]). exact He.
Qed.

(* the registers outside a tail's clobber list that w6cb_keep names *)
Ltac w6cb_keep_rk RK HP2 :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; rewrite RK;
  [ exact (w6cb_keep_saved _ _ HP2 r Hr)
  | cbv [w6cb_keep In] in Hr; repeat (destruct Hr as [<-|Hr]; [vm_compute; discriminate|]); destruct Hr
  | cbv [w6cb_keep In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [cbv [In]; let X := fresh "X" in intros X;
      repeat (destruct X as [X|X]; [discriminate X|]); exact X|]); destruct Hr ].

(* ===================== cases 6 and 7: memcpy(e62.body, src, n), then a3 := s8, t1 := s4, a5 := [R+0x140],
   `j J` ===================== *)
Theorem w6cb_tail_cpy : w6cb_tail_cpy_stmt B.
Proof using AMEMCPY.
unfold w6cb_tail_cpy_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos ty sz src bs cur' nl' pp
HJ HG H1 H2 H3 H4 H9 H10 H11 H12 H22 H24 H20 Hlen Hsz He Hbs Hra Hhl Hamr Hsrc0 Hsrc63 Hdis Hfsh Hpp Hpp0 Hpp1.
destruct (w6cb_frame STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ HG)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HF & HFapp & HF32).
set (n := Z.of_nat (length bs)) in *.
assert (Hn96 : 0 <= n <= 96) by (subst n; lia).
pose proof alloc_ceiling_value as (Hc1 & _). pose proof alloc_ceiling_lt as Hc2.
unfold kHighMemBeg, T_SEG_STK, ASTACK in HRk, HSTK, HRc.
assert (HspR : spZ regs = R).
{ unfold spZ. rewrite H2. unfold w64. apply unsigned_lit_small. lia. }
rewrite w6cb_PJ in Hfsh.
eapply SRr_bind.
{ apply (rl_intrin_at B LAWS OCpy W6CB_CPY AMEMCPY W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k (F + 0x218)
    src n (R - sp0) (w64 W6CB_RCPY) HJ H10 H11 H12).
  - lia.
  - lia.
  - lia.
  - rewrite HspR. lia.
  - rewrite Zminus_mod, HR16, Hsp16. reflexivity.
  - lia.
  - unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  - exact H3.
  - exact H4.
  - exact H1.
  - exact w6cb_ret_cpy.
  - intros a Ha. split; [apply HFw; lia|]. unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  - unfold in_app, ASAN_CEIL in HFapp. unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  - replace (F + 0x218) with (F + RM_E62 + 8) by (unfold RM_E62; lia).
    apply (rm_B_ra_e62 rsegs _ _ F false false false false false false 8 n);
      [exact Hfsh | apply w6cb_F8; exact HF32 | lia | lia].
  - intros Hn0. apply w6cb_hull_e62; [exact HF32 | lia | lia | lia | lia | exact HFS].
  - cbv iota. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [|rewrite HspR; exact (proj1 (Hdis a Ha))].
      pose proof (proj1 (rm_bytes_aview rsegs _ _ _ _) Hbs (Z.to_nat (a - src)) ltac:(subst n; lia)) as Hv.
      rewrite Z2Nat.id in Hv by lia. replace (src + (a - src)) with a in Hv by lia. rewrite Hv. discriminate. }
    split.
    { destruct (Z_le_gt_dec (F + 0x218 + n) src) as [X|X]; [left; exact X|].
      destruct (Z_le_gt_dec (src + n) (F + 0x218)) as [Y|Y]; [right; exact Y|].
      exfalso. apply (proj2 (Hdis (Z.max src (F + 0x218)) ltac:(lia))). lia. }
    split; [exact Hamr|]. split; [exact Hra | exact Hhl]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsame & Ha02 & Heff & Hfr).
assert (HK2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x218 <= a < F + 0x218 + n) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha H5 H6. apply Hfr; [exact Ha | exact H5 | lia]. }
(* 0x81738 mv a3,s8; mv t1,s4; ld a5,0x140(s1); j J *)
assert (U9 : bv_unsigned (ew (Ereg regs2 [Z_to_bv 64 pp]) 9) = R).
{ rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl).
  assert (E9 : getr regs2 9 = w64 R) by exact (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) H9).
  rewrite E9. unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs2 [Z_to_bv 64 pp]) 32 = Z_to_bv 64 pp) by exact (ew_Ereg_extra regs2 [Z_to_bv 64 pp] 0).
assert (HS : st_ok rsegs (Ereg regs2 [Z_to_bv 64 pp]) (mkSS W6CB_RCPY sr_atoms [w6cb_RSp] None
  (mkFacts [(9%nat, mkAF 0x10007fff8000 0x800000000000 4)] [] []))
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 W6CB_RCPY) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold w6cb_RSp. apply (rm_ro_region rsegs _ (w_H W) mem2 9%nat R); [exact U9 | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ R 0x140 8 (SOff 32 0) pp); [| cbn; lia | cbn; lia |].
    + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + apply (rl_val_kept (w_H W) memc mem2); [|exact Hpp].
      intros i Hi. apply HK2; [lia | lia | unfold ESTACK in *; lia].
  - split; exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9.
    split; [lia|]. split; [|lia].
    destruct (proj1 (Z.mod_divide R 16 ltac:(lia)) HR16) as [q ->]. change (2 ^ 4) with 16. apply Z_mod_mult. }
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsl. pose proof LAWS as HL.
change (w64 W6CB_RCPY) with (Z_to_bv 64 W6CB_RCPY).
aj_run_to w6cb_tbl_ok HS HJ2 W6CB_J.
{ eapply awr_ok_cons_stack_off with (n := 9%nat) (d := R - sp0);
  [reflexivity | rewrite U9; lia | unfold w6cb_RSp; cbn [YP09.r_wlo]; unfold T_SEG_STK, ASTACK in *; lia
  | unfold w6cb_RSp; cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
(* at J *)
assert (HE3 : forall a, aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem2 a).
{ lazymatch goal with Hx : frame_of ?E ?rs mem2 (ms_mem ms) |- _ =>
    change (frame_of E [w6cb_RSp] mem2 (ms_mem ms)) in Hx;
    intros a; exact (w6cb_kept_ro _ w6cb_RSp (w_H W) _ _ ltac:(cbn; lia) Hx a) end. }
assert (HM : forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0x210 <= a < F + 0x278) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha H5 H6. rewrite (HE3 a). apply HK2; [exact Ha | lia | exact H5]. }
assert (RK : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [6; 13; 15]%bv -> getr (ms_regs ms) r = getr regs2 r).
{ exact (regs_kept_of_st_ok rsegs _ _ ms regs2 [Z_to_bv 64 pp] (w_H W) [6; 13; 15]%bv HS
    (env_agree_refl _ _) ltac:(vm_compute; reflexivity)). }
pose proof (st_ok_restrict_reg rsegs (w_H W) _ _ ms (6%bv) HS) as R6.
pose proof (st_ok_restrict_reg rsegs (w_H W) _ _ ms (13%bv) HS) as R13.
pose proof (st_ok_restrict_reg rsegs (w_H W) _ _ ms (15%bv) HS) as R15.
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e6 := eval vm_compute in (sr_get (ss_regs ssf) (6%bv : bv 5)) in
  let e13 := eval vm_compute in (sr_get (ss_regs ssf) (13%bv : bv 5)) in
  let e15 := eval vm_compute in (sr_get (ss_regs ssf) (15%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (6%bv : bv 5)) with e6 in R6;
  change (sr_get (ss_regs ssf) (13%bv : bv 5)) with e13 in R13;
  change (sr_get (ss_regs ssf) (15%bv : bv 5)) with e15 in R15
end.
cbn [sv_denot] in R6, R13, R15.
rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned in R6.
rewrite (ew_Ereg_nat regs2 _ 24 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned in R13.
rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned in R15.
eapply (w6cb_leaf STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F _ cur' nl' pp _ _ _ _ HS).
- reflexivity.
- vm_compute. reflexivity.
- exact HJ2.
- eapply same_io_trans; [exact (same_io_materialized mdc md2 Hsame) | apply same_io_wvb].
- w6cb_keep_rk RK HP2.
- rewrite R6. exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) H20).
- rewrite R13. exact (eq_trans (HP2 24 ltac:(unfold acallee_saved; lia)) H24).
- rewrite RK; [| vm_compute; discriminate | cbv [In]; intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X].
  exact (eq_trans (HP2 22 ltac:(unfold acallee_saved; lia)) H22).
- unfold w64. exact R15.
- exact HM.
- rewrite <- (w6cb_ent_cpy ty sz bs) by lia.
  apply (rm_bytes_kept rsegs (w_H W) mem2 (w_H W) (ms_mem ms)); [|intros x _; apply HE3].
  replace (F + 0x218) with (F + 0x210 + Z.of_nat 8) in Heff, Hfr by lia.
  apply (rm_bytes_patch rsegs (w_H W) memc (w_H W) mem2 (F + 0x210) _ 8 bs He).
  + apply (rm_memcpy_bytes rsegs (w_H W) memc (w_H W) mem2 src (F + 0x210 + Z.of_nat 8) bs Hbs).
    intros i Hi. exact (Heff i Hi).
  + rewrite !length_app, !length_le32, length_zeros. lia.
  + intros y Hy Hny. rewrite !length_app, !length_le32, length_zeros in Hy. rewrite Nat2Z.inj_add in Hny.
    unfold n in *. apply Hfr; [lia | lia |]. unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
Qed.

(* ===================== case 8: memset(e62.body, 0, size), then the six instructions to J ===================== *)
Theorem w6cb_tail_set : w6cb_tail_set_stmt B.
Proof using AMEMSET.
unfold w6cb_tail_set_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos ty sz cur' nl' pp
HJ HG H1 H2 H3 H4 H9 H10 H11 H12 H18 H22 Hsz He Hfsh Hppl Hpp Hpp0 Hpp1.
destruct (w6cb_frame STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ HG)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HF & HFapp & HF32).
pose proof alloc_ceiling_value as (Hc1 & _). pose proof alloc_ceiling_lt as Hc2.
unfold kHighMemBeg, T_SEG_STK, ASTACK in HRk, HSTK, HRc.
assert (HspR : spZ regs = R).
{ unfold spZ. rewrite H2. unfold w64. apply unsigned_lit_small. lia. }
rewrite w6cb_PJ in Hfsh.
eapply SRr_bind.
{ apply (rl_intrin_at B LAWS OSet W6CB_SET AMEMSET W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k (F + 0x218)
    0 sz (R - sp0) (w64 W6CB_RSET) HJ H10 H11 H12).
  - lia.
  - lia.
  - lia.
  - rewrite HspR. lia.
  - rewrite Zminus_mod, HR16, Hsp16. reflexivity.
  - lia.
  - unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  - exact H3.
  - exact H4.
  - exact H1.
  - exact w6cb_ret_set.
  - intros a Ha. split; [apply HFw; lia|]. unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  - unfold in_app, ASAN_CEIL in HFapp. unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  - replace (F + 0x218) with (F + RM_E62 + 8) by (unfold RM_E62; lia).
    apply (rm_B_ra_e62 rsegs _ _ F false false false false false false 8 sz);
      [exact Hfsh | apply w6cb_F8; exact HF32 | lia | lia].
  - intros Hn0. apply w6cb_hull_e62; [exact HF32 | lia | lia | lia | lia | exact HFS].
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsame & Ha02 & Heff & Hfr).
assert (HK2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x218 <= a < F + 0x218 + sz) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha H5 H6. apply Hfr; [exact Ha | exact H5 | lia]. }
(* 0x81584 mv t1,s6; mv a3,s2; ld s6,0x130(s1); j 0x81740; ld a5,0x140(s1); j J *)
set (ex := [Z_to_bv 64 pp; Z_to_bv 64 (pp + 0x4000)]).
assert (U9 : bv_unsigned (ew (Ereg regs2 ex) 9) = R).
{ rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl).
  assert (E9 : getr regs2 9 = w64 R) by exact (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) H9).
  rewrite E9. unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs2 ex) 32 = Z_to_bv 64 pp) by exact (ew_Ereg_extra regs2 ex 0).
assert (E33 : ew (Ereg regs2 ex) 33 = Z_to_bv 64 (pp + 0x4000)) by exact (ew_Ereg_extra regs2 ex 1).
assert (HS : st_ok rsegs (Ereg regs2 ex) (mkSS W6CB_RSET sr_atoms [w6cb_RSq] None
  (mkFacts [(9%nat, mkAF 0x10007fff8000 0x800000000000 4)] [] []))
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 W6CB_RSET) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold w6cb_RSq. apply (rm_ro_region rsegs _ (w_H W) mem2 9%nat R); [exact U9 | lia | lia |].
    constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val rsegs _ _ R 0x130 8 (SOff 33 0) (pp + 0x4000)); [| cbn; lia | cbn; lia |].
      * cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * apply (rl_val_kept (w_H W) memc mem2); [|exact Hppl].
        intros i Hi. apply HK2; [lia | lia | unfold ESTACK in *; lia].
    + apply (chunk_ok_val rsegs _ _ R 0x140 8 (SOff 32 0) pp); [| cbn; lia | cbn; lia |].
      * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * apply (rl_val_kept (w_H W) memc mem2); [|exact Hpp].
        intros i Hi. apply HK2; [lia | lia | unfold ESTACK in *; lia].
  - split; exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9.
    split; [lia|]. split; [|lia].
    destruct (proj1 (Z.mod_divide R 16 ltac:(lia)) HR16) as [q ->]. change (2 ^ 4) with 16. apply Z_mod_mult. }
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsl. pose proof LAWS as HL.
change (w64 W6CB_RSET) with (Z_to_bv 64 W6CB_RSET).
aj_run_to w6cb_tbl_ok HS HJ2 W6CB_J.
{ eapply awr_ok_cons_stack_off with (n := 9%nat) (d := R - sp0);
  [reflexivity | rewrite U9; lia | unfold w6cb_RSq; cbn [YP09.r_wlo]; unfold T_SEG_STK, ASTACK in *; lia
  | unfold w6cb_RSq; cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
(* at J *)
assert (HE3 : forall a, aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem2 a).
{ lazymatch goal with Hx : frame_of ?E ?rs mem2 (ms_mem ms) |- _ =>
    change (frame_of E [w6cb_RSq] mem2 (ms_mem ms)) in Hx;
    intros a; exact (w6cb_kept_ro _ w6cb_RSq (w_H W) _ _ ltac:(cbn; lia) Hx a) end. }
assert (HM : forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0x210 <= a < F + 0x278) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha H5 H6. rewrite (HE3 a). apply HK2; [exact Ha | lia | exact H5]. }
assert (RK : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [6; 13; 15; 22]%bv -> getr (ms_regs ms) r = getr regs2 r).
{ exact (regs_kept_of_st_ok rsegs _ _ ms regs2 ex (w_H W) [6; 13; 15; 22]%bv HS
    (env_agree_refl _ _) ltac:(vm_compute; reflexivity)). }
pose proof (st_ok_restrict_reg rsegs (w_H W) _ _ ms (6%bv) HS) as R6.
pose proof (st_ok_restrict_reg rsegs (w_H W) _ _ ms (13%bv) HS) as R13.
pose proof (st_ok_restrict_reg rsegs (w_H W) _ _ ms (15%bv) HS) as R15.
pose proof (st_ok_restrict_reg rsegs (w_H W) _ _ ms (22%bv) HS) as R22.
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e6 := eval vm_compute in (sr_get (ss_regs ssf) (6%bv : bv 5)) in
  let e13 := eval vm_compute in (sr_get (ss_regs ssf) (13%bv : bv 5)) in
  let e15 := eval vm_compute in (sr_get (ss_regs ssf) (15%bv : bv 5)) in
  let e22 := eval vm_compute in (sr_get (ss_regs ssf) (22%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (6%bv : bv 5)) with e6 in R6;
  change (sr_get (ss_regs ssf) (13%bv : bv 5)) with e13 in R13;
  change (sr_get (ss_regs ssf) (15%bv : bv 5)) with e15 in R15;
  change (sr_get (ss_regs ssf) (22%bv : bv 5)) with e22 in R22
end.
cbn [sv_denot] in R6, R13, R15, R22.
rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned in R6.
rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned in R13.
rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned in R15.
rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned in R22.
eapply (w6cb_leaf STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F _ cur' nl' pp _ _ _ _ HS).
- reflexivity.
- vm_compute. reflexivity.
- exact HJ2.
- eapply same_io_trans; [exact (same_io_materialized mdc md2 Hsame) | apply same_io_wvb].
- w6cb_keep_rk RK HP2.
- rewrite R6. exact (eq_trans (HP2 22 ltac:(unfold acallee_saved; lia)) H22).
- rewrite R13. exact (eq_trans (HP2 18 ltac:(unfold acallee_saved; lia)) H18).
- unfold w64. exact R22.
- unfold w64. exact R15.
- exact HM.
- rewrite <- (w6cb_ent_set ty sz) by lia.
  apply (rm_bytes_kept rsegs (w_H W) mem2 (w_H W) (ms_mem ms)); [|intros x _; apply HE3].
  rewrite <- (w6cb_ow_zeros ty sz) by lia.
  apply (rm_bytes_patch rsegs (w_H W) memc (w_H W) mem2 (F + 0x210) _ 8 (zeros (Z.to_nat sz)) He).
  + apply (rm_memset_bytes rsegs (w_H W) mem2 (F + 0x210 + Z.of_nat 8) 0 (Z.to_nat sz)).
    intros i Hi. replace (F + 0x210 + Z.of_nat 8 + i) with (F + 0x218 + i) by lia. apply Heff. lia.
  + rewrite !length_app, !length_le32, !length_zeros. lia.
  + intros y Hy Hny. rewrite !length_app, !length_le32, !length_zeros in Hy.
    rewrite length_zeros, Nat2Z.inj_add, Z2Nat.id in Hny by lia.
    apply HK2; [lia | lia | unfold ESTACK in *; lia].
Qed.
End d.
End b.
