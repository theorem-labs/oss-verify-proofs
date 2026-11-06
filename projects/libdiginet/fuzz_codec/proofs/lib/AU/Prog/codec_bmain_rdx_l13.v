(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 201 of its 223 lines of code are new or changed and 227 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_rd13.v, with its module paths and module names changed; 18 of its 49 lines of code are new or changed and 192 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe9.v, with its module paths and module names changed; 422 of its 453 lines of code are new or changed and 18 lines of the source are left out. *)
(* Shared pieces of the image-B walk of LLVMFuzzerTestOneInput's text readers RD12 (SCRIBBLE_TEXT) and RD13
   (COUNTER_TEXT): RD13's regions and its join state at 0x8130c, the kept-memory step of a run and of an own callee,
   the image tables the text callees read (cimg_rd), the frame's shadow map while RD13 runs, text_arg's premises at
   the readers' call (sp1 + 184, F + 80), and the run / keep / entry tactics.
   It is the image-A layer lib/A/Prog/codec_amain_rd13l.v at image B: k = F + 192, text = F + 80, the dots byte at
   F + 448 (shadow byte 56), the cursor at 184(sp1) / 192(sp1), k.p in s6, the 60 shadow bytes of image B's frame. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YD1y.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import YImgTopU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CodecRo CodecGlobs CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkKeptU CPgWalkCallU CPgWalkRoU CPgWalkImgU CPgSatU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_headl codec_bmain_encl.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the record's fields RD13 writes, as RD13 starts: kind 13 at F + 192, p (atom 22 = s6) and desk (atom 37) at F + 200
   / F + 208, b 0 at F + 220; the frame's shadow byte 56 (the dots byte's) writable *)
Definition r13_kk : YP09.region := bm_frame_region 192 196 192 196 [YP09.mkChunk 192 (CVal 4 (SLit 13))].
Definition r13_kpd : YP09.region :=
bm_frame_region 200 216 200 216 [YP09.mkChunk 200 (CVal 8 (SOff 22 0)); YP09.mkChunk 208 (CVal 8 (SOff 37 0))].
Definition r13_kb : YP09.region := bm_frame_region 220 224 220 224 [YP09.mkChunk 220 (CVal 4 (SLit 0))].
Definition r13_rs : smem := [bm_shadow_region 56 57 bm_shm0; r13_kk; r13_kpd; r13_kb].
(* the state at 0x8130c where the two paths of `bnez s6` join: the shadow byte 56 set to 1, the p / desk region
   dropped (its values are carried as facts), the dead registers ra, a0, a1, a2 as the segment's atoms 38 .. 41 *)
Definition r13_sh_mid : YP09.region := Eval vm_compute in
YP09.mkRegion (Some 34%nat) 0 60 56 57
  (YP09.mkChunk 56 (CVal 1 (SLit 1)) :: filter (fun ch => negb (YP09.c_off ch =? 56)) (bm_sh_chunks bm_shm0 0)).
Definition r13_regs_mid : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set bm_sregs 1%bv (SOff 38 0)) 10%bv (SOff 39 0)) 11%bv (SOff 40 0)) 12%bv (SOff 41 0).
Definition r13_rs_mid : smem := Eval vm_compute in bm_regs ++ [r13_sh_mid; r13_kk; r13_kb].
Definition r13_ss_mid : sstate := mkSS 0x8130c r13_regs_mid r13_rs_mid None (mkFacts bm_atoms [] []).
(* the bytes RD13 leaves alone that its end cuts read: the spills, the saved words, the flag word, and the record's
   fields a, c, delta, bytes .. want_display *)
Definition r13_zone (g : ectx) (pos sp1 a : Z) : Prop :=
bm_keepzone g pos sp1 a \/ (FA g pos + 216 <= a < FA g pos + 220) \/ (FA g pos + 224 <= a < FA g pos + 376).

(* the frame's 60 shadow bytes while RD13 runs: shm 0 with the dots byte's (56) marked 01 *)
Definition r13_shm1 : list Z := Eval vm_compute in firstn 56 bm_shm0 ++ [1] ++ skipn 57 bm_shm0.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* the entry's frame address at any state of the journal (frame_addr reads ly_F only, which layout_le keeps) *)
Lemma r13_efa : forall g pos ly3 S3 W3 mem3 md3 k3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 k3 ->
frame_addr ly3 3 pos = FA g pos.
Proof.
intros g pos ly3 S3 W3 mem3 md3 k3 HJ. pose proof HJ as (_ & Hly & _).
unfold FA, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). lia.
Qed.

(* a byte off every write window of a run keeps its view *)
Lemma r13_run_kept : forall E rs H (m1 m2 : word -> option byte) (Z : Z -> Prop),
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, Z a -> 0 <= a < 2 ^ 64 /\ ~ in_wrange E rs a) ->
forall a, Z a -> aview tfibsegs H m2 a = aview tfibsegs H m1 a.
Proof.
intros E rs H m1 m2 Z HFr HZ a Ha. destruct (HZ a Ha) as [Ha64 Hw]. unfold aview, mbyte.
rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha64. exact Hw.
Qed.

(* a byte of the machine stack above the callee's window, of the entry's frame or of its shadow, off the callee's
   write set, keeps its view across the call (the callee post's tcj_kept, clauses 1 and 4) *)
Lemma r13_call_kept : forall T lyc Sc W m W' m' sp Er g pos (Z : Z -> Prop),
tcj_kept tfibsegs B T lyc Sc W m W' m' sp Er -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = FA g pos ->
(forall a, Z a -> ((alloc_ceiling <= a < 2 ^ 64 /\ ~ (sp - T <= a < sp)) \/ (FA g pos <= a < FA g pos + 512) \/
  (shadow_addr (FA g pos) <= a < shadow_addr (FA g pos) + 64)) /\ ~ Er a) ->
forall a, Z a -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a.
Proof.
intros T lyc Sc W m W' m' sp Er g pos Z (K1 & _ & _ & K4 & _) Hin EFA HZ a Ha.
destruct (HZ a Ha) as [[[H1 H2] | [H3 | H3]] HE].
- apply K1; [lia | exact H2 | exact HE].
- apply (K4 3 pos a Hin); [|exact HE]. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA.
  change (fs_frame_bytes 3) with 512. lia.
- apply (K4 3 pos a Hin); [|exact HE]. right. unfold in_zr. cbn [fst snd]. rewrite EFA.
  change (fs_frame_bytes 3 / 8) with 64. lia.
Qed.

(* bytes that are present are a garr8 of their own values *)
Definition r13_cur (W : world tfibsegs) (m : word -> option byte) (q n : Z) : list Z :=
map (fun i : nat => match aview tfibsegs (w_H W) m (q + Z.of_nat i) with Some v => v | None => 0 end) (seq 0 (Z.to_nat n)).
Lemma r13_cur_len : forall W m q n, 0 <= n -> length (r13_cur W m q n) = Z.to_nat n.
Proof. intros W m q n Hn. unfold r13_cur. rewrite length_map, length_seq. reflexivity. Qed.
Lemma r13_cur_garr8 : forall (W : world tfibsegs) m q n,
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) m (q + i) <> None) ->
garr8 tfibsegs (mrestrict (w_H W) m) q (r13_cur W m q n).
Proof.
intros W m q n Hp j Hj. unfold r13_cur in *. rewrite length_map, length_seq in Hj.
set (f := fun i : nat => match aview tfibsegs (w_H W) m (q + Z.of_nat i) with Some v => v | None => 0 end).
rewrite (nth_indep _ 0 (f 0%nat)) by (rewrite length_map, length_seq; lia).
rewrite map_nth, seq_nth by lia. cbn [Nat.add]. unfold f.
destruct (aview tfibsegs (w_H W) m (q + Z.of_nat j)) as [v|] eqn:Ev;
  [|exfalso; apply (Hp (Z.of_nat j)); [lia | exact Ev]].
split; [apply val_mem1_of_aviewA; exact Ev | exact (proj2 (bm_mb W m _ v Ev))].
Qed.

(* ---- the image tables the text callees read (cimg_rd): diginet_seg7's table, the glyph table and the 33 string
   rows, from the start-up facts (as the entry segment's be_cimg does for the personalities) ---- *)
Lemma r13_rows_ok : forallb (fun r => bm_ro_b (fst r) (snd r) && (0 <? snd r) && (IMG_LO + 64 <=? fst r) &&
  (fst r + snd r + 64 <=? IMG_HI) && (fst r + snd r <=? CB_RHI)) ((CB_SEG7, 364) :: CB_ROSTRS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma r13_cimg_rd : forall (W : world tfibsegs) memc sp T,
  TfibLib B -> globs_marked tfibsegs B CODEC_GLOBS -> img_shadow_vis tfibsegs B -> cpw_rows_free B CB_ROSTRS ->
  arodata_ok B (aview tfibsegs (w_H W) memc) -> CB_RHI <= sp - T ->
  cimg_rd tfibsegs B CB_RLO CB_RHI W memc sp T ((CB_SEG7, 364) :: (CB_GLYPH, 464) :: CB_ROSTRS).
Proof.
intros W memc sp T TL0 GM IV RF HR Hwin.
assert (U : forall q sz a n, In (q, sz) CODEC_GLOBS -> q <= a -> a + n <= q + sz -> 0 < n ->
  IMG_LO + 64 <= a -> a + n + 64 <= IMG_HI -> cimg_usable tfibsegs B a n).
{ intros q sz a n Hin Hqa Han Hn Hlo Hhi ly' S' W' mem' md' HAR.
  split; [exact (ro_usable_glob tfibsegs B CODEC_GLOBS ly' S' W' mem' md' q sz a n GM Hin HAR Hqa Han)|].
  intros _. exact (ro_hull tfibsegs B ly' S' W' mem' md' a n IV HAR Hn Hlo Hhi). }
(* a row of the read-only segments: diginet_seg7's table, or a string row *)
assert (RO : forall q sz, In (q, sz) ((CB_SEG7, 364) :: CB_ROSTRS) ->
  (forall a, q <= a < q + sz -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  (forall i, 0 <= i < sz -> in_roP tfibsegs CB_RLO CB_RHI (q + i)) /\ cimg_range tfibsegs B sp T q sz).
{ intros q sz Hin Hfree.
  pose proof (proj1 (forallb_forall _ _) r13_rows_ok (q, sz) Hin) as Hb. cbv beta in Hb. cbn [fst snd] in Hb.
  apply andb_prop in Hb as [Hb H5]. apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3].
  apply andb_prop in Hb as [Hro H2].
  apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5.
  assert (Hgl : In (q, sz) CODEC_GLOBS).
  { destruct Hin as [Heq | Hin]; [injection Heq as <- <-; exact cg_SEG7|].
    exact (proj1 (Forall_forall _ _) CB_ROSTRS_globs (q, sz) Hin). }
  split.
  - intros i Hi. apply (bm_in_ro q sz Hro). lia.
  - cbv [IMG_LO IMG_HI IMG_TOP CB_RHI] in H3, H4, H5, Hwin.
    unfold cimg_range.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [left; unfold kLowMemEnd; lia|].
    split; [left; lia|].
    split.
    + intros x Hx. split; [|exact (Hfree x Hx)].
      pose proof Hro as Hro'. unfold bm_ro_b in Hro'. apply existsb_exists in Hro' as (s & Hs & Hc).
      apply andb_prop in Hc as (Hc & Hhi). apply andb_prop in Hc as (_ & Hlo).
      apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
      unfold in_img. exists s. split; [exact Hs | lia].
    + apply (U q sz); [exact Hgl | lia | lia | lia | cbv [IMG_LO]; lia | cbv [IMG_HI IMG_TOP]; lia]. }
split; [intros a Ha; exact (HR a Ha)|].
apply Forall_cons; [|apply Forall_cons].
- cbn [fst snd]. apply RO; [left; reflexivity|].
  intros a Ha. apply (tl_lib_consts B TL0 a). unfold lib_const_addr, CB_SEG7 in *. lia.
- (* the glyph table, in .data.rel.ro *)
  cbn [fst snd]. split.
  + intros i Hi. right. unfold CB_GLYPH, CB_RLO, CB_RHI. lia.
  + unfold cimg_range.
    split; [unfold CB_GLYPH; lia|]. split; [lia|]. split; [unfold CB_GLYPH; lia|].
    split; [left; unfold CB_GLYPH, kLowMemEnd; lia|].
    split; [left; unfold CB_GLYPH, CB_RHI in *; lia|].
    split.
    * intros x Hx. split; [|exact (tl_lib_consts B TL0 x ltac:(unfold lib_const_addr; unfold CB_GLYPH in Hx; lia))].
      apply YD1y.in_img_hull. unfold CB_GLYPH in Hx. lia.
    * apply (U CB_GLYPH 464); [exact cg_GLYPH | lia | lia | lia | cbv [IMG_LO CB_GLYPH]; lia | cbv [IMG_HI IMG_TOP CB_GLYPH]; lia].
- apply Forall_forall. intros [q sz] Hin. cbn [fst snd].
  apply RO; [right; exact Hin|].
  intros x Hx. destruct (cpw_rows_free_In B CB_ROSTRS q sz (x - q) RF Hin ltac:(lia)) as (Ho & He).
  replace (q + (x - q)) with x in Ho, He by lia. exact (conj Ho He).
Qed.
(* the same without diginet_seg7's table (owed_counter_text's rows) *)
Lemma r13_cimg_rd2 : forall (W : world tfibsegs) memc sp T,
  TfibLib B -> globs_marked tfibsegs B CODEC_GLOBS -> img_shadow_vis tfibsegs B -> cpw_rows_free B CB_ROSTRS ->
  arodata_ok B (aview tfibsegs (w_H W) memc) -> CB_RHI <= sp - T ->
  cimg_rd tfibsegs B CB_RLO CB_RHI W memc sp T ((CB_GLYPH, 464) :: CB_ROSTRS).
Proof.
intros W memc sp T TL0 GM IV RF HR Hwin. destruct (r13_cimg_rd W memc sp T TL0 GM IV RF HR Hwin) as (HRO & HF).
split; [exact HRO | exact (Forall_inv_tail HF)].
Qed.

(* the three objects the text callees take, marked usable by those shadow bytes *)
Lemma r13_bs_all : forall (W : world tfibsegs) mem F, F mod 64 = 0 ->
(forall i, 0 <= i < 60 -> aview tfibsegs (w_H W) mem (shadow_addr F + i) = Some (nth (Z.to_nat i) r13_shm1 0)) ->
block_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 80) 65 /\
block_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 232) 24 /\
block_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 448) 1.
Proof.
intros W mem F H64 HS. split; [|split]; (apply bm_block_shadow; [exact H64 | lia | reflexivity | lia |]); intros i Hi.
- change ((65 + 7) / 8) with 9 in Hi. change (80 / 8) with 10. rewrite (HS (10 + i)) by lia.
  assert (Ei : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
  repeat (destruct Ei as [-> | Ei]; [vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
- change ((24 + 7) / 8) with 3 in Hi. change (232 / 8) with 29. rewrite (HS (29 + i)) by lia.
  assert (Ei : i = 0 \/ i = 1 \/ i = 2) by lia.
  repeat (destruct Ei as [-> | Ei]; [vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
- change ((1 + 7) / 8) with 1 in Hi. change (448 / 8) with 56. rewrite (HS (56 + i)) by lia.
  assert (Ei : i = 0) by lia. subst i. vm_compute. reflexivity.
Qed.

(* the premises of text_arg at RD13 / RD12's call (0x81318 / 0x815dc): &in = sp1 + 184 on the machine stack, the
   cursor's bytes in the input block, text = F + 80 in the frame *)
Lemma r13_ta_pre : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 kev c ly3 S3 W3 mem3 md3 k3,
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 k3 ->
frames S3 = [(3, pos)] -> Permutation (ablocks B ly3 S3) (ablocks B (e_ly g) (e_S g)) ->
1 <= c <= e_n g ->
block_shadow (aview tfibsegs (w_H W3) mem3) SHADOW_OFF (FA g pos + 80) 65 ->
let dat := skipn (Z.to_nat c) (map (fun b : byte => bv_unsigned b) (e_pl g)) in
cdstk_ok tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) ly3 S3 [(3, pos)] W3 mem3 sp1 TB_text_arg (sp1 + 184) 16 /\
Z.of_nat (length dat) = e_n g - c /\
0 < e_p g + c /\ e_p g + c + Z.of_nat (length dat) <= 2 ^ 63 /\
garr8 tfibsegs (mrestrict (w_H W3) mem3) (e_p g + c) dat /\
crd_ok tfibsegs W3 mem3 sp1 TB_text_arg (e_p g + c) (Z.of_nat (length dat)) /\
cdst_ok tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) ly3 S3 [(3, pos)] W3 mem3 sp1 TB_text_arg (FA g pos + 80) 65 /\
garr8 tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 80) (r13_cur W3 mem3 (FA g pos + 80) 65) /\
length (r13_cur W3 mem3 (FA g pos + 80) 65) = 65%nat /\
(sp1 + 184 + 16 <= FA g pos + 80 \/ FA g pos + 80 + 65 <= sp1 + 184) /\
(e_p g + c + Z.of_nat (length dat) <= FA g pos + 80 \/ FA g pos + 80 + 65 <= e_p g + c) /\
(e_p g + c + Z.of_nat (length dat) <= sp1 + 184 \/ sp1 + 184 + 16 <= e_p g + c) /\
(sp1 + 184) mod 8 = 0.
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 kev c ly3 S3 W3 mem3 md3 k3 HC HJ Hfr HJ3 Hfr3 HPerm3 Hc HBS dat.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (E512 : fs_frame_bytes 3 = 512) by reflexivity. rewrite E512 in Hfceil.
assert (Hes : ESTACK = 4096) by reflexivity.
unfold BM_HI in *.
pose proof HC as HGIN. do 48 (destruct HGIN as (_ & HGIN)). destruct HGIN as (GIN & _).
pose proof HC as (Hpre & _).
pose proof Hpre as Hpre'. unfold e_pre, codec_lib_pre_x in Hpre'.
destruct Hpre' as (_ & _ & _ & _ & _ & Hnpl & _).
set (inp := map (fun b : byte => bv_unsigned b) (e_pl g)) in *.
assert (Linp : Z.of_nat (length inp) = e_n g) by (unfold inp; rewrite length_map; lia).
assert (Ldat : Z.of_nat (length dat) = e_n g - c) by (unfold dat; rewrite length_skipn; lia).
destruct (Hblk ltac:(lia)) as (Hb2 & Hb0).
assert (Hb3 : In (e_p g, e_n g) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3 | exact Hb0]).
pose proof HJ3 as (HAR3 & _).
assert (EFA3 : frame_addr ly3 3 pos = FA g pos) by exact (r13_efa g pos ly3 S3 W3 mem3 md3 k3 HJ3).
assert (Hin3 : In (3, pos) (frames S3)) by (rewrite Hfr3; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 (e_p g) (e_n g) HAR3 Hb3) as (_ & H4096 & Hbc & _).
pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 mem3 md3 (e_p g) (e_n g) 3 pos HAR3 Hb3 Hin3) as Hsep.
rewrite EFA3, E512 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
(* the input bytes at the call state: the journal keeps the block's bytes (empty footprint) *)
assert (GIN3 : garr8 tfibsegs (mrestrict (w_H W3) mem3) (e_p g) inp).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J2 & _).
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J3 & _).
  apply (bm_garr8_kept_x (w_H W2) (w_H W3) mem2 mem3); [|exact GIN].
  intros x Hx. rewrite Linp in Hx. replace x with (e_p g + (x - e_p g)) by lia.
  rewrite (J3 (e_p g) (e_n g) (x - e_p g) Hb0 Hb3 ltac:(lia) (inFP_nil _)).
  rewrite (J2 (e_p g) (e_n g) (x - e_p g) Hb0 Hb2 ltac:(lia) (inFP_nil _)). reflexivity. }
assert (Gdat : garr8 tfibsegs (mrestrict (w_H W3) mem3) (e_p g + c) dat).
{ rewrite <- (firstn_skipn (Z.to_nat c) inp) in GIN3. apply garr8_app in GIN3 as [_ G2].
  rewrite length_firstn in G2. replace (Z.of_nat (Nat.min (Z.to_nat c) (length inp))) with c in G2 by lia.
  exact G2. }
split; [|split; [exact Ldat|]].
{ apply (sat_stack_dst tfibsegs B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
    ly3 S3 W3 mem3 md3 k3 sp1 TB_text_arg (sp1 + 184) 16 HJ3); unfold TB_text_arg in *; lia. }
split; [lia|]. split; [lia|]. split; [exact Gdat|].
split.
{ apply (sat_block_rd tfibsegs B LAWS ly3 S3 W3 mem3 md3 sp1 TB_text_arg (e_p g) (e_n g) (e_p g + c) _ LLVMF_STK (e_sp0 g)
    HAR3 Hb3); unfold TB_text_arg in *; lia. }
split.
{ apply (satU_main_text_dst tfibsegs B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
    ly3 S3 W3 mem3 md3 k3 sp1 TB_text_arg pos (FA g pos) HJ3 ltac:(left; reflexivity) Hin3 EFA3 Hf64 HBS);
  unfold TB_text_arg in *; lia. }
split.
{ apply r13_cur_garr8. intros i Hi. apply aview_some_of_apresent.
  destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 3 pos HAR3 Hin3) as (_ & _ & Hpr & _).
  rewrite EFA3, E512 in Hpr. exact (proj1 (Hpr (FA g pos + 80 + i) ltac:(lia))). }
split; [rewrite r13_cur_len by lia; reflexivity|].
split; [lia|]. split; [lia|]. split; [lia|].
pose proof (Z.div_mod sp1 32 ltac:(lia)) as D32. rewrite Hsp32, Z.add_0_r in D32.
rewrite D32. replace (32 * (sp1 / 32) + 184) with ((4 * (sp1 / 32) + 23) * 8) by lia. apply Z_mod_mult.
Qed.

(* owed_counter_text answers 0 or E_RANGE (rd13_ct2_go_rc / rd13_owed_rc of the plain walk's
   lib/Prog/codec_main_rd13.v, over the same Gallina) *)
Lemma r13_ct2_go_rc : forall k n s dot i seg d,
  fst (fst (ct2_go n s dot i k seg d)) = 0 \/ fst (fst (ct2_go n s dot i k seg d)) = E_RANGE.
Proof.
  induction k as [|k IH]; intros n s dot i seg d; cbn [ct2_go].
  - left. reflexivity.
  - repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      first [ apply IH | left; reflexivity | right; reflexivity ].
Qed.
Lemma r13_owed_rc : forall t r sg d, owed_counter_text_spec t = (r, sg, d) -> r = 0 \/ r = E_RANGE.
Proof.
  intros t r sg d H. unfold owed_counter_text_spec in H.
  destruct (ct1_owe t 0 [] (repeat 0 8)) as [[[n s] dot]|].
  - unfold ct2 in H. pose proof (r13_ct2_go_rc 8 n s dot 0 [] 0) as R. rewrite H in R. cbn [fst] in R. exact R.
  - injection H as <- _ _. right. reflexivity.
Qed.

(* the text after text_arg: its 65 bytes *)
Lemma r13_tb_len : forall dat tj, length tj = 65%nat ->
length (text_takenZ dat ++ [0] ++ skipn (1 + text_lenZ dat) tj) = 65%nat.
Proof.
intros dat tj Hl. unfold text_takenZ. rewrite !length_app, length_firstn, length_skipn, length_skipn, Hl. cbn [length].
assert (H1 : (text_lenZ dat <= length dat - text_hdrZ dat)%nat) by (unfold text_lenZ; lia).
assert (H2 : (text_lenZ dat <= 64)%nat).
{ unfold text_lenZ. pose proof (Z.mod_pos_bound (text_u16Z dat) 65 ltac:(lia)) as M. lia. }
lia.
Qed.

(* the segment's atoms extended at the end: the environment agrees on every atom below the old list's end *)
Lemma r13_env_prefix : forall g pos c regs ys ys',
env_agree (37 + length ys) (bm_env g pos c regs ys) (bm_env g pos c regs (ys ++ ys')).
Proof.
intros g pos c regs ys ys'. split; [|reflexivity]. intros n Hn. unfold bm_env, Ereg. cbn [ew].
destruct (Nat.ltb_spec n 32) as [Hlt|Hge]; [reflexivity|]. unfold cw_extra.
replace (SB :: bm_xs g pos c ++ ys ++ ys') with ((SB :: bm_xs g pos c ++ ys) ++ ys') by (cbn [app]; rewrite app_assoc; reflexivity).
rewrite map_app, app_nth1; [reflexivity|]. rewrite length_map. cbn [length]. rewrite length_app. unfold bm_xs. cbn [length]. lia.
Qed.

(* a frame byte is not a byte of the image (AR_client_img_law), so a range of the frame lies off an image range *)
Lemma r13_frame_apart : forall ly S W mem md pos F q n lo hi,
AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) -> frame_addr ly 3 pos = F ->
0 < n -> (forall a, q <= a < q + n -> in_img tfibsegs a) -> 0 <= lo -> lo < hi -> hi <= 512 ->
F + hi <= q \/ q + n <= F + lo.
Proof.
intros ly S W mem md pos F q n lo hi HAR Hin EFA Hn0 Himg Hlo Hlh Hhi.
destruct (Z_le_gt_dec (F + hi) q) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (q + n) (F + lo)) as [H2|H2]; [right; exact H2|].
exfalso. set (a := Z.max q (F + lo)).
pose proof (al_client_img _ _ LAWS ly S W mem md a HAR) as Hc. apply Hc; [|apply Himg; unfold a; lia].
right. left. exists 3, pos. split; [exact Hin|]. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA.
change (fs_frame_bytes 3) with 512. unfold a. lia.
Qed.

(* the call record at an end cut: kind, p, desk, b and bytes as the walk left them, every other field as RD13
   found it (k_rdZ 13 pv dv's), kept over [F + 216, F + 220), [F + 224, F + 232) and [F + 256, F + 376) *)
Lemma r13_k_kept : forall (W W' : world tfibsegs) m m' F pv dv kind' pv' dv' b' bytes',
kcall_atA tfibsegs W m (F + 192) (k_rdZ 13 pv dv) ->
(forall x, (F + 216 <= x < F + 220) \/ (F + 224 <= x < F + 232) \/ (F + 256 <= x < F + 376) ->
  aview tfibsegs (w_H W') m' x = aview tfibsegs (w_H W) m x) ->
val_mem tfibsegs (mrestrict (w_H W') m') (F + 192) 4 kind' ->
val_mem tfibsegs (mrestrict (w_H W') m') (F + 200) 8 pv' ->
val_mem tfibsegs (mrestrict (w_H W') m') (F + 208) 8 dv' ->
val_mem tfibsegs (mrestrict (w_H W') m') (F + 220) 4 b' ->
garr8 tfibsegs (mrestrict (w_H W') m') (F + 232) bytes' ->
kcall_atA tfibsegs W' m' (F + 192) (mkKcallZ kind' pv' dv' 0 b' 0 0 bytes' 0 0 fa5 fa5 0 (repeat 0 24) 0 0 0).
Proof.
intros W W' m m' F pv dv kind' pv' dv' b' bytes'
  (V0 & V8 & V16 & V24 & V28 & V32 & V36 & G40 & V64 & V72 & G76 & G108 & V140 & G144 & V168 & V176 & V180)
  Hk Vk Vp Vd Vb Gb.
cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out kz_want_rc kz_want kz_want_len
  kz_want_key kz_want_display k_rdZ] in *.
assert (KV : forall o n v, 0 <= o -> o + Z.of_nat n <= 184 ->
  (24 <= o /\ o + Z.of_nat n <= 28 \/ 32 <= o /\ o + Z.of_nat n <= 40 \/ 64 <= o) ->
  val_mem tfibsegs (mrestrict (w_H W) m) (F + 192 + o) n v -> val_mem tfibsegs (mrestrict (w_H W') m') (F + 192 + o) n v).
{ intros o n v H1 H2 H3 Hv. apply (cw_val_mem_kept (w_H W) (w_H W') m m'); [|exact Hv]. intros x Hx. apply Hk. lia. }
assert (KG : forall o l, 64 <= o -> o + Z.of_nat (length l) <= 184 ->
  garr8 tfibsegs (mrestrict (w_H W) m) (F + 192 + o) l -> garr8 tfibsegs (mrestrict (w_H W') m') (F + 192 + o) l).
{ intros o l H1 H2 Hg. apply (bm_garr8_kept_x (w_H W) (w_H W') m m'); [|exact Hg]. intros x Hx. apply Hk. lia. }
unfold kcall_atA. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out kz_want_rc
  kz_want kz_want_len kz_want_key kz_want_display].
split; [exact Vk|]. split; [replace (F + 192 + 8) with (F + 200) by lia; exact Vp|].
split; [replace (F + 192 + 16) with (F + 208) by lia; exact Vd|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V24]|].
split; [replace (F + 192 + 28) with (F + 220) by lia; exact Vb|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V32]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V36]|].
split; [replace (F + 192 + 40) with (F + 232) by lia; exact Gb|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V64]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V72]|].
split; [apply KG; [lia | rewrite fa5_len; cbn; lia | exact G76]|].
split; [apply KG; [lia | rewrite fa5_len; cbn; lia | exact G108]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V140]|].
split; [apply KG; [lia | rewrite repeat_length; cbn; lia | exact G144]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V168]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V176]|].
apply KV; [lia | cbn; lia | cbn; lia | exact V180].
Qed.
End b.
End a.

Ltac r13_awr :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch goal with B2 : bv_unsigned (ew E 2) = ?spv, BF : bv_unsigned (ew E 33) = ?Fv,
  BS : bv_unsigned (ew E 34) = ?Sv, EFL : frame_addr ly 3 ?posv = _ |- _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
  [reflexivity | rewrite B2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat Fv);
  [reflexivity | exact BF
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
    right; right; right; exists 3, posv; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
    rewrite EFL; change (fs_frame_bytes 3) with 512; lia |]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat Sv);
  [reflexivity | exact BS
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
    right; right; right; exists 3, posv; split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd];
    rewrite EFL; change (fs_frame_bytes 3 / 8) with 64; lia |] ]
end end.

Ltac r13_pin r j :=
  lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
  let HS1 := fresh "HS1" in
  pose proof (st_ok_pin_rege Ev ssv (restrict Hh msv) r (SOff (BM_X0 + j) 0) HS ltac:(intros X; discriminate X)
    ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite bm_ew_y; cbn [nth];
          apply Z_to_bv_bv_unsigned)) as HS1;
  clear HS; rename HS1 into HS end.

Ltac r13_join gv posv cv regsv dvv :=
  (lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
  let fa := eval vm_compute in (f_atoms (ss_facts ssv)) in
  let HS1 := fresh "HS1" in
  pose proof (st_ok_facts_incl3 tfibsegs Ev ssv (restrict Hh msv) fa [] [] HS ltac:(intros x Hx; exact Hx)
    ltac:(intros x [])  ltac:(intros x [])) as HS1;
  clear HS; rename HS1 into HS end);
  (lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv ?msv |- _ =>
  let HS1 := fresh "HS1" in
  pose proof (st_ok_submem tfibsegs Ev ssv msv r13_rs_mid HS ltac:(vm_compute; submem_to) ltac:(vm_compute; reflexivity)) as HS1;
  clear HS; rename HS1 into HS end);
  (lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
  let HS1 := fresh "HS1" in
  pose proof (st_ok_agree tfibsegs 38 Ev (bm_env gv posv cv regsv
    ([dvv] ++ [bv_unsigned (getr (ms_regs msv) 1); bv_unsigned (getr (ms_regs msv) 10);
     bv_unsigned (getr (ms_regs msv) 11); bv_unsigned (getr (ms_regs msv) 12)])) ssv _ HS
    (r13_env_prefix gv posv cv regsv [dvv] _)
    ltac:(vm_compute; reflexivity)) as HS1;
  clear HS; rename HS1 into HS; cbn [app] in HS end);
  (r13_pin (1%bv : bv 5) 1%nat; r13_pin (10%bv : bv 5) 2%nat; r13_pin (11%bv : bv 5) 3%nat; r13_pin (12%bv : bv 5) 4%nat);
  (lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv ?msv |- _ =>
  let Hss := fresh "Hss" in assert (Hss : ssv = r13_ss_mid) by (vm_compute; reflexivity);
  let HS1 := fresh "HS1" in
  pose proof (eq_ind ssv (fun s => YP0l.st_ok tfibsegs Ev s msv) HS r13_ss_mid Hss) as HS1;
  clear HS Hss; rename HS1 into HS end).

Ltac r13_reg HS r Hn :=
  lazymatch type of HS with YP0l.st_ok ?segs ?Ev ?ss (restrict ?Hh ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  pose proof (st_ok_restrict_reg segs Hh Ev ss ms r HS) as Hn;
  change (sr_get (ss_regs ss) r) with e in Hn; cbn [sv_denot] in Hn end.

Ltac r13_keep KT EFLc Hinc PRES HJa HJb :=
  first
  [ lazymatch goal with |- region_kept _ ?E _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
    lazymatch goal with B2 : bv_unsigned (ew E 2) = _ |- _ =>
    eapply (region_kept_tcj_stack _ E); [exact KT | exact B2
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; split; [lia | split; [lia | let HE := fresh "HE" in intros HE; cbv beta in HE; first [contradiction | lia]]]
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; split; lia ] end end
  | lazymatch goal with |- region_kept _ ?E _ _ (YP09.mkRegion (Some 34%nat) _ _ _ _ _) =>
    lazymatch goal with BS : bv_unsigned (ew E 34) = _ |- _ =>
    eapply (region_kept_tcj_frame _ E); [exact KT | exact BS | exact Hinc
    | right; rewrite EFLc; change (fs_frame_bytes 3 / 8) with 64; lia
    | let a := fresh "a" in let Ha := fresh "Ha" in let HE := fresh "HE" in intros a Ha HE; cbv beta in HE; first [contradiction | lia]
    | PRES ] end end
  | lazymatch goal with |- region_kept _ ?E _ _ (YP09.mkRegion (Some 33%nat) _ _ _ _ _) =>
    lazymatch goal with BF : bv_unsigned (ew E 33) = _ |- _ =>
    eapply (region_kept_tcj_frame _ E); [exact KT | exact BF | exact Hinc
    | left; rewrite EFLc; change (fs_frame_bytes 3) with 512; lia
    | let a := fresh "a" in let Ha := fresh "Ha" in let HE := fresh "HE" in intros a Ha HE; cbv beta in HE; first [contradiction | lia]
    | PRES ] end end
  | lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None _ _ _ _ _) => cpw_kept_std KT HJa HJb end ].

(* a byte of a zone off every write window of a state's regions: ~ in_wrange, given the bases of atoms 2, 33, 34 *)
Ltac r13_nwr B2 BF BS :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?B2, ?BF, ?BS in Hb; lia | ]);
  destruct Hr.
(* the callee's cdc_entry at an own call from the walk: the journal, ra, gp, tp, sp and the budgets *)
Ltac r13_entry Bv HJx Rra Rgp Rtp G3 G4 R3 R4 Usp Hsp32 Tv HPermX :=
  eapply (cpw_entry Bv);
  [ exact HJx
  | rewrite Rra; apply ret_ok_even; vm_compute; reflexivity
  | unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia
  | rewrite Rgp, Z.add_0_r, Z_to_bv_bv_unsigned, G3; exact R3
  | rewrite Rtp, Z.add_0_r, Z_to_bv_bv_unsigned, G4; exact R4
  | rewrite Usp;
    lazymatch goal with |- ?s mod 16 = 0 =>
      let D32 := fresh "D32" in pose proof (Z.div_mod s 32 ltac:(lia)) as D32; rewrite Hsp32, Z.add_0_r in D32;
      rewrite D32; replace (32 * (s / 32)) with ((2 * (s / 32)) * 16) by lia; apply Z_mod_mult end
  | rewrite Usp; let t := eval cbv in Tv in change Tv with t; lia
  | rewrite Usp; lia
  | unfold EV_CDC; lia
  | apply Permutation_refl
  | lazymatch goal with |- blocks_bytes ?Sx + _ <= _ =>
      lazymatch type of HPermX with Permutation (ablocks _ ?lyx Sx) _ =>
        rewrite (blocks_bytes_bsum Bv lyx Sx), (bsum_perm _ _ HPermX), <- (blocks_bytes_bsum Bv _ _) end end;
    unfold LIVE_CDC, LIVE_LIB in *; lia ].
