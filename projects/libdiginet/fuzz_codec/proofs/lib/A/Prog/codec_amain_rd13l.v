(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v, with its module names changed; 425 of its 456 lines of code are new or changed and 235 lines of the source are left out. *)
(* Shared pieces of the image-A walk of LLVMFuzzerTestOneInput's text readers RD12 (SCRIBBLE_TEXT) and RD13
   (COUNTER_TEXT): RD13's regions and its join state at 0x8105c, the kept-memory step of a run and of an own callee,
   the image tables the text callees read (cimg_rd), the frame's shadow map while RD13 runs, text_arg's premises at
   the readers' call (sp1 + 152, F + 64), and the run / keep / entry tactics. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YImgTop.
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgEncC CPgMainC CodecRo CodecGlobs CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalkKept CPgWalkCall CPgWalkRo CPgWalkImg CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_lem codec_amain_encl.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the record's fields RD13 writes, as RD13 starts: kind 13 at F + 176, p (atom 23 = s7) and desk (atom 37) at F + 184
   / F + 192, b 0 at F + 204; the frame's shadow byte 54 (the dots byte's) writable *)
Definition r13_kk : YP09.region := am_frame_region 176 180 176 180 [YP09.mkChunk 176 (CVal 4 (SLit 13))].
Definition r13_kpd : YP09.region :=
am_frame_region 184 200 184 200 [YP09.mkChunk 184 (CVal 8 (SOff 23 0)); YP09.mkChunk 192 (CVal 8 (SOff 37 0))].
Definition r13_kb : YP09.region := am_frame_region 204 208 204 208 [YP09.mkChunk 204 (CVal 4 (SLit 0))].
Definition r13_rs : smem := [am_shadow_region 54 55 am_shm0; r13_kk; r13_kpd; r13_kb].
(* the state at 0x8105c where the two paths of `bnez s7` join: the shadow byte 54 set to 1, the p / desk region
   dropped (its values are carried as facts), the dead registers ra, a0, a1, a2 as the segment's atoms 38 .. 41 *)
Definition r13_sh_mid : YP09.region := Eval vm_compute in
YP09.mkRegion (Some 34%nat) 0 56 54 55
  (YP09.mkChunk 54 (CVal 1 (SLit 1)) :: filter (fun ch => negb (YP09.c_off ch =? 54)) (am_sh_chunks am_shm0 0)).
Definition r13_regs_mid : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set am_sregs 1%bv (SOff 38 0)) 10%bv (SOff 39 0)) 11%bv (SOff 40 0)) 12%bv (SOff 41 0).
Definition r13_rs_mid : smem := Eval vm_compute in am_regs ++ [r13_sh_mid; r13_kk; r13_kb].
Definition r13_ss_mid : sstate := mkSS 0x8105c r13_regs_mid r13_rs_mid None (mkFacts am_atoms [] []).
(* the bytes RD13 leaves alone that its end cuts read: the spills, the saved words, the flag word, and the record's
   fields a, c, delta, bytes .. want_display *)
Definition r13_zone (g : ectx) (pos sp1 a : Z) : Prop :=
am_keepzone g pos sp1 a \/ (FA g pos + 200 <= a < FA g pos + 204) \/ (FA g pos + 208 <= a < FA g pos + 360).

(* a byte of the image: the segment that holds it, tried in order *)
(* the frame's 56 shadow bytes while RD13 runs: shm 0 with the dots byte's (54) marked 01 *)
Definition r13_shm1 : list Z := Eval vm_compute in firstn 54 am_shm0 ++ [1] ++ skipn 55 am_shm0.

(* a byte of the image: the segment that holds it, tried in order *)
Ltac r13_seg_bnd :=
  match goal with |- Z.le ?lo _ /\ Z.lt _ (?lo' + ?sz) =>
    let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end;
  lia.

Ltac r13_img_seg :=
  unfold in_img;
  first [ eexists; split; [left; reflexivity | r13_seg_bnd]
        | eexists; split; [right; left; reflexivity | r13_seg_bnd]
        | eexists; split; [right; right; left; reflexivity | r13_seg_bnd]
        | eexists; split; [right; right; right; left; reflexivity | r13_seg_bnd]
        | eexists; split; [right; right; right; right; left; reflexivity | r13_seg_bnd]
        | eexists; split; [right; right; right; right; right; left; reflexivity | r13_seg_bnd] ].


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis RF : cpw_rows_free B CA_ROSTRS.

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
split; [apply val_mem1_of_aviewA; exact Ev | exact (proj2 (am_mb W m _ v Ev))].
Qed.

(* ---- the image tables the text callees read (cimg_rd) ---- *)
Definition r13_img_ok (r : Z * Z) : Prop :=
In r CODEC_GLOBS /\ 0 < snd r /\ IMG_LO + 64 <= fst r /\ fst r + snd r + 64 <= IMG_HI /\ fst r + snd r <= CA_RHI /\
(forall a, fst r <= a < fst r + snd r ->
   in_roP tfibsegs CA_RLO CA_RHI a /\ in_img tfibsegs a /\ ~ Exists (in_zr a) (as_owned_static B) /\
   ~ (as_errno B <= a < as_errno B + 4)).
Lemma r13_cimg_rd : forall (W : world tfibsegs) m sp T l,
arodata_ok B (aview tfibsegs (w_H W) m) -> globs_marked tfibsegs B CODEC_GLOBS -> img_shadow_vis tfibsegs B ->
CA_RHI <= sp - T -> Forall r13_img_ok l ->
cimg_rd tfibsegs B CA_RLO CA_RHI W m sp T l.
Proof.
intros W m sp T l HR GM0 IV0 Hwin Hl. split; [intros a Ha; apply HR; exact Ha|].
eapply Forall_impl; [|exact Hl]. intros [q n] (Hin & Hn & Hlo & Hhi & Hrhi & Ha). cbn [fst snd] in *.
split; [intros i Hi; apply (Ha (q + i)); lia|].
pose proof (Ha q ltac:(lia)) as (_ & (sg & _ & Hsg) & _).
assert (Hq0 : 0 <= q) by (cbv [IMG_LO] in Hlo; lia).
apply (sat_img_rd tfibsegs B CODEC_GLOBS sp T q n GM0 Hin IV0 Hn Hq0 Hlo Hhi).
- unfold CA_RHI in Hrhi. lia.
- intros x Hx. destruct (Ha x Hx) as (_ & H1 & H2 & H3). exact (conj H1 (conj H2 H3)).
- left. unfold CA_RHI in Hrhi. unfold kLowMemEnd. lia.
- lia.
Qed.
(* a byte of a read-only segment is a byte of the image *)
Lemma r13_ro_img : forall q n, am_ro_b q n = true -> forall a, q <= a < q + n -> in_img tfibsegs a.
Proof.
intros q n Hb a Ha. unfold am_ro_b in Hb. apply existsb_exists in Hb as (sg & Hin & Hc).
apply andb_prop in Hc as (Hc & Hhi). apply andb_prop in Hc as (_ & Hlo).
apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. exists sg. split; [exact Hin | lia].
Qed.
Definition r13_row_b (r : Z * Z) : bool :=
am_ro_b (fst r) (snd r) && (0 <? snd r) && (IMG_LO + 64 <=? fst r) && (fst r + snd r + 64 <=? IMG_HI) &&
(fst r + snd r <=? CA_RHI).
Lemma r13_row_ok : forall r, r13_row_b r = true -> In r CODEC_GLOBS ->
(forall a, fst r <= a < fst r + snd r -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
r13_img_ok r.
Proof.
intros [q n] Hb Hin Ho. unfold r13_row_b in Hb. unfold r13_img_ok. cbn [fst snd] in *.
repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
split; [exact Hin|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
intros a Ha. split; [exact (am_in_ro q n ltac:(assumption) a Ha)|].
split; [exact (r13_ro_img q n ltac:(assumption) a Ha) | exact (Ho a Ha)].
Qed.
Lemma r13_rows_img : Forall r13_img_ok CA_ROSTRS.
Proof. assert (Hb : forallb r13_row_b CA_ROSTRS = true) by (vm_compute; reflexivity).
apply Forall_forall. intros [q n] Hin. apply r13_row_ok.
- exact (proj1 (forallb_forall _ _) Hb (q, n) Hin).
- exact (proj1 (Forall_forall _ _) CA_ROSTRS_globs (q, n) Hin).
- intros a Ha. cbn [fst snd] in Ha. replace a with (q + (a - q)) by lia.
  exact (cpw_rows_free_In B CA_ROSTRS q n (a - q) RF Hin ltac:(lia)).
Qed.
Lemma r13_seg7_img : r13_img_ok (CA_SEG7, 364).
Proof.
apply r13_row_ok; [vm_compute; reflexivity | exact cg_SEG7 |].
intros a Ha. cbn [fst snd] in Ha. apply (tl_lib_consts B TL a). unfold lib_const_addr, CA_SEG7 in *. lia.
Qed.
Lemma r13_glyph_img : r13_img_ok (CA_GLYPH, 464).
Proof.
unfold r13_img_ok. cbn [fst snd]. split; [exact cg_GLYPH|].
unfold CA_GLYPH, CA_RHI. cbv [IMG_LO IMG_HI IMG_TOP]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
intros a Ha. split; [right; unfold CA_RLO, CA_RHI; lia|]. split; [r13_img_seg|].
apply (tl_lib_consts B TL a). unfold lib_const_addr. lia.
Qed.

(* the three objects the text callees take, marked usable by those shadow bytes *)
Lemma r13_bs_all : forall (W : world tfibsegs) mem F, F mod 64 = 0 ->
(forall i, 0 <= i < 56 -> aview tfibsegs (w_H W) mem (shadow_addr F + i) = Some (nth (Z.to_nat i) r13_shm1 0)) ->
block_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 64) 65 /\
block_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 216) 24 /\
block_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 432) 1.
Proof.
intros W mem F H64 HS. split; [|split]; (apply am_block_shadow; [exact H64 | lia | reflexivity | lia |]); intros i Hi.
- change ((65 + 7) / 8) with 9 in Hi. change (64 / 8) with 8. rewrite (HS (8 + i)) by lia.
  assert (Ei : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
  repeat (destruct Ei as [-> | Ei]; [vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
- change ((24 + 7) / 8) with 3 in Hi. change (216 / 8) with 27. rewrite (HS (27 + i)) by lia.
  assert (Ei : i = 0 \/ i = 1 \/ i = 2) by lia.
  repeat (destruct Ei as [-> | Ei]; [vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
- change ((1 + 7) / 8) with 1 in Hi. change (432 / 8) with 54. rewrite (HS (54 + i)) by lia.
  assert (Ei : i = 0) by lia. subst i. vm_compute. reflexivity.
Qed.

(* the premises of text_arg at RD13 / RD12's call (0x81064 / 0x81290): &in = sp1 + 152 on the machine stack, the
   cursor's bytes in the input block, text = F + 64 in the frame *)
Lemma r13_ta_pre : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 kev c ly3 S3 W3 mem3 md3 k3,
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 k3 ->
frames S3 = [(3, pos)] -> Permutation (ablocks B ly3 S3) (ablocks B (e_ly g) (e_S g)) ->
1 <= c <= e_n g ->
block_shadow (aview tfibsegs (w_H W3) mem3) SHADOW_OFF (FA g pos + 64) 65 ->
let dat := skipn (Z.to_nat c) (map (fun b : byte => bv_unsigned b) (e_pl g)) in
cdstk_ok tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) ly3 S3 [(3, pos)] W3 mem3 sp1 T_text_arg (sp1 + 152) 16 /\
Z.of_nat (length dat) = e_n g - c /\
0 <= e_p g + c /\ e_p g + c + Z.of_nat (length dat) <= 2 ^ 63 /\
garr8 tfibsegs (mrestrict (w_H W3) mem3) (e_p g + c) dat /\
crd_ok tfibsegs W3 mem3 sp1 T_text_arg (e_p g + c) (Z.of_nat (length dat)) /\
cdst_ok tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) ly3 S3 [(3, pos)] W3 mem3 sp1 T_text_arg (FA g pos + 64) 65 /\
garr8 tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 64) (r13_cur W3 mem3 (FA g pos + 64) 65) /\
length (r13_cur W3 mem3 (FA g pos + 64) 65) = 65%nat /\
(sp1 + 152 + 16 <= FA g pos + 64 \/ FA g pos + 64 + 65 <= sp1 + 152) /\
(e_p g + c + Z.of_nat (length dat) <= FA g pos + 64 \/ FA g pos + 64 + 65 <= e_p g + c) /\
(e_p g + c + Z.of_nat (length dat) <= sp1 + 152 \/ sp1 + 152 + 16 <= e_p g + c).
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 kev c ly3 S3 W3 mem3 md3 k3 HC HJ Hfr HJ3 Hfr3 HPerm3 Hc HBS dat.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (E512 : fs_frame_bytes 3 = 512) by reflexivity. rewrite E512 in Hfceil.
assert (Hes : ESTACK = 4096) by reflexivity.
unfold AM_HI in *.
pose proof HC as HGIN. do 44 (destruct HGIN as (_ & HGIN)). destruct HGIN as (GIN & _).
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
  apply (am_garr8_kept (w_H W2) (w_H W3) mem2 mem3); [|exact GIN].
  intros x Hx. rewrite Linp in Hx. replace x with (e_p g + (x - e_p g)) by lia.
  rewrite (J3 (e_p g) (e_n g) (x - e_p g) Hb0 Hb3 ltac:(lia) (inFP_nil _)).
  rewrite (J2 (e_p g) (e_n g) (x - e_p g) Hb0 Hb2 ltac:(lia) (inFP_nil _)). reflexivity. }
assert (Gdat : garr8 tfibsegs (mrestrict (w_H W3) mem3) (e_p g + c) dat).
{ rewrite <- (firstn_skipn (Z.to_nat c) inp) in GIN3. apply garr8_app in GIN3 as [_ G2].
  rewrite length_firstn in G2. replace (Z.of_nat (Nat.min (Z.to_nat c) (length inp))) with c in G2 by lia.
  exact G2. }
split; [|split; [exact Ldat|]].
{ apply (sat_stack_dst tfibsegs B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
    ly3 S3 W3 mem3 md3 k3 sp1 T_text_arg (sp1 + 152) 16 HJ3); unfold T_text_arg in *; lia. }
split; [lia|]. split; [lia|]. split; [exact Gdat|].
split.
{ apply (sat_block_rd tfibsegs B LAWS ly3 S3 W3 mem3 md3 sp1 T_text_arg (e_p g) (e_n g) (e_p g + c) _ LLVMF_STK (e_sp0 g)
    HAR3 Hb3); unfold T_text_arg in *; lia. }
split.
{ apply (sat_main_text_dst tfibsegs B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
    ly3 S3 W3 mem3 md3 k3 sp1 T_text_arg pos (FA g pos) HJ3 ltac:(left; reflexivity) Hin3 EFA3 Hf64 HBS);
  unfold T_text_arg in *; lia. }
split.
{ apply r13_cur_garr8. intros i Hi. apply aview_some_of_apresent.
  destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 3 pos HAR3 Hin3) as (_ & _ & Hpr & _).
  rewrite EFA3, E512 in Hpr. exact (proj1 (Hpr (FA g pos + 64 + i) ltac:(lia))). }
split; [rewrite r13_cur_len by lia; reflexivity|].
split; [lia|]. split; [lia | lia].
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

(* the write windows of the walk's regions: the save area / cursor of atom 2 in the caller's stack allowance, and
   the frame (atom 33) or its shadow (atom 34), which the journal's own frame covers. Needs B2 : bv_unsigned (ew E 2)
   = sp1, BF : bv_unsigned (ew E 33) = F, BS : bv_unsigned (ew E 34) = shadow_addr F and EFL : frame_addr ly 3 pos = F
   for the state's layout ly. *)
(* the segment's atoms extended at the end: the environment agrees on every atom below the old list's end *)
Lemma r13_env_prefix : forall g pos c regs ys ys',
env_agree (37 + length ys) (am_env g pos c regs ys) (am_env g pos c regs (ys ++ ys')).
Proof.
intros g pos c regs ys ys'. split; [|reflexivity]. intros n Hn. unfold am_env, Ereg. cbn [ew].
destruct (Nat.ltb_spec n 32) as [Hlt|Hge]; [reflexivity|]. unfold cw_extra.
replace (SB :: am_xs g pos c ++ ys ++ ys') with ((SB :: am_xs g pos c ++ ys) ++ ys') by (cbn [app]; rewrite app_assoc; reflexivity).
rewrite map_app, app_nth1; [reflexivity|]. rewrite length_map. cbn [length]. rewrite length_app. unfold am_xs. cbn [length]. lia.
Qed.

(* pin register r to the segment's atom 37 + j that holds its value *)
(* the join at 0x8105c: drop the branch condition and the p / desk region, move to the segment's atoms, pin the dead
   registers to them *)
(* register r of a stopped state, as the denotation of the engine's value *)
(* a region of the walk kept across an own callee (its post's tcj_kept KT): the stack ones above the callee's
   window (clause 1), the frame's and its shadow's (clause 4), the two image cells (their values in both journals);
   PRES gives the frame bytes present after the call *)

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
   found it (k_rdZ 13 pv dv's), kept over [F + 200, F + 204), [F + 208, F + 216) and [F + 240, F + 360) *)
Lemma r13_k_kept : forall (W W' : world tfibsegs) m m' F pv dv kind' pv' dv' b' bytes',
kcall_atA tfibsegs W m (F + 176) (k_rdZ 13 pv dv) ->
(forall x, (F + 200 <= x < F + 204) \/ (F + 208 <= x < F + 216) \/ (F + 240 <= x < F + 360) ->
  aview tfibsegs (w_H W') m' x = aview tfibsegs (w_H W) m x) ->
val_mem tfibsegs (mrestrict (w_H W') m') (F + 176) 4 kind' ->
val_mem tfibsegs (mrestrict (w_H W') m') (F + 184) 8 pv' ->
val_mem tfibsegs (mrestrict (w_H W') m') (F + 192) 8 dv' ->
val_mem tfibsegs (mrestrict (w_H W') m') (F + 204) 4 b' ->
garr8 tfibsegs (mrestrict (w_H W') m') (F + 216) bytes' ->
kcall_atA tfibsegs W' m' (F + 176) (mkKcallZ kind' pv' dv' 0 b' 0 0 bytes' 0 0 fa5 fa5 0 (repeat 0 24) 0 0 0).
Proof.
intros W W' m m' F pv dv kind' pv' dv' b' bytes'
  (V0 & V8 & V16 & V24 & V28 & V32 & V36 & G40 & V64 & V72 & G76 & G108 & V140 & G144 & V168 & V176 & V180)
  Hk Vk Vp Vd Vb Gb.
cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out kz_want_rc kz_want kz_want_len
  kz_want_key kz_want_display k_rdZ] in *.
assert (KV : forall o n v, 0 <= o -> o + Z.of_nat n <= 184 ->
  (24 <= o /\ o + Z.of_nat n <= 28 \/ 32 <= o /\ o + Z.of_nat n <= 40 \/ 64 <= o) ->
  val_mem tfibsegs (mrestrict (w_H W) m) (F + 176 + o) n v -> val_mem tfibsegs (mrestrict (w_H W') m') (F + 176 + o) n v).
{ intros o n v H1 H2 H3 Hv. apply (cw_val_mem_kept (w_H W) (w_H W') m m'); [|exact Hv]. intros x Hx. apply Hk. lia. }
assert (KG : forall o l, 64 <= o -> o + Z.of_nat (length l) <= 184 ->
  garr8 tfibsegs (mrestrict (w_H W) m) (F + 176 + o) l -> garr8 tfibsegs (mrestrict (w_H W') m') (F + 176 + o) l).
{ intros o l H1 H2 Hg. apply (am_garr8_kept (w_H W) (w_H W') m m'); [|exact Hg]. intros x Hx. apply Hk. lia. }
unfold kcall_atA. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out kz_want_rc
  kz_want kz_want_len kz_want_key kz_want_display].
split; [exact Vk|]. split; [replace (F + 176 + 8) with (F + 184) by lia; exact Vp|].
split; [replace (F + 176 + 16) with (F + 192) by lia; exact Vd|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V24]|].
split; [replace (F + 176 + 28) with (F + 204) by lia; exact Vb|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V32]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V36]|].
split; [replace (F + 176 + 40) with (F + 216) by lia; exact Gb|].
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
  pose proof (st_ok_pin_rege Ev ssv (restrict Hh msv) r (SOff (AM_X0 + j) 0) HS ltac:(intros X; discriminate X)
    ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite am_ew_y; cbn [nth];
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
  pose proof (st_ok_agree tfibsegs 38 Ev (am_env gv posv cv regsv
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


Ltac r13_ner := let a := fresh "a" in let Ha := fresh "Ha" in let HE := fresh "HE" in
  intros a Ha HE; cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Ha; cbv beta in HE; lia.

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
