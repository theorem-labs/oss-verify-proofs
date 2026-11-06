(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, awr_ok_cons_gen, as w7_region_nth, w7_field, w7_awr_cons) for reac-pw/fuzz_role's image A; the rest of the file is new: the block-post shape, the code table and the helpers of the walk of LLVMFuzzerTestOneInput from 0x80d14 to 0x8165c. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at 25d4b718638 and the definitions
   w7_kept, w7_hull, w7_strok, w7_strz of proofs/reac-pw/fuzz_role/lib/A/RPgW7bKit.v at 25d4b718638, for
   reac-pw/fuzz_headamp's image B: w7_ -> hw7b_, role's image A code and record -> fuzz_headamp.asan-ubsan's (its own
   code table, pcs, registers and real-frame cells, measured on image B), module paths; the statements of the walk's
   blocks and call steps are new (hw7b_*_stmt), one per block of image B's own code; its hw7b_post,
   hw7b_post_of_run, hw7b_kept, hw7b_hull, hw7b_ra_kept, hw7b_hull_kept, hw7b_strok, hw7b_strz, hw7b_strok_kept and
   hw7b_strok_first_byte are lib/AU/HPgCaseB.v's cb_* since the dedup. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgW7bBase.v; 792 of its 841 lines of code are new or changed and 265 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the whole walk of
   LLVMFuzzerTestOneInput (0x80c40) from G 0x81afc to J 0x82618 over explicit facts (lib/AU/HPgW7bBase.v
   hw7b_core_stmt), from the statements of its blocks and call steps. Proves no function (kind: segment lemma).

   THE WALK. A1 (the param entry), A2 (sep, parts[0..3], strlen(parts[0])), four parts-loop turns (hw7b_iter_stmt:
   strlen, block B, memcpy(t + n, parts[i], l)) on "reac.headamp." at 0x20f40, the key's first part in ch, the
   separator and the param name, with C (the next part) between them, D (the 95 clamp, memcpy(e62.body, t, n)), the
   memcpy step, E1 and E2 (the NUL, type, size, t and ch out of scope, the reloads).
   WHAT IS CARRIED (hw7b_I, at the strlen entry of each turn). Every step before E2 keeps every byte outside hw7b_Z1
   (the callees' stack below R, the parts window R+0x178 .. R+0x198, t, and e62's first 9 + |js| bytes); E2 also
   writes 15 shadow bytes of the frame for locals. So the image's strings, the frame's shadow, ch, e62's zeros after
   the NUL and the real-frame cells the walk reads stay as at G. The ten registers the cut J keeps
   ([2; 3; 4; 8; 9; 19; 22; 24; 25; 27]) and s5 are in no block's clobber list and are callee-saved; t holds the parts
   written so far after each turn; the window holds the four parts from A2 on.
   REGISTERS: as HPgW7bBase.v's header; no other cell. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps HPgMem HPgCaseB HPgW7bBase HPgW7bFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ===================================== the geometry of the walk ===================================== *)
(* the bytes [lo, hi) lie in one segment of the image *)
Definition hw7b_in_seg_b (lo hi : Z) : bool :=
existsb (fun sg => (Z.of_N (seg_base sg) <=? lo) && (hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) rsegs.
Lemma hw7b_in_seg : forall lo hi a, hw7b_in_seg_b lo hi = true -> lo <= a < hi -> in_img rsegs a.
Proof.
intros lo hi a Hb Ha. unfold hw7b_in_seg_b in Hb. apply existsb_exists in Hb as (sg & Hin & Hs).
apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin | lia].
Qed.
(* the strings the walk reads ("reac.headamp.", "", ".", the eight param names) lie in [0x20f00, 0x21520) *)
Lemma hw7b_img_strs : hw7b_in_seg_b 0x20f00 0x21520 = true.
Proof. vm_compute. reflexivity. Qed.
(* the param table lies in [0x9c600, 0x9c640) *)
Lemma hw7b_img_ptab : hw7b_in_seg_b 0x9c600 0x9c640 = true.
Proof. vm_compute. reflexivity. Qed.

(* the zone every step before E2 writes in: the callees' stack below R, the parts window, t, e62's first 9 + L
   bytes *)
Definition hw7b_Z1 (R F L : Z) (a : Z) : Prop :=
R - 2 * ESTACK <= a < R \/ R + 0x178 <= a < R + 0x198 \/ F + 0x20 <= a < F + 0x80 \/ F + 0x210 <= a < F + 0x219 + L.

(* the shadow hull of a range at x >= 64 lies in the shadow map above SHADOW_OFF *)
Lemma hw7b_hull_box : forall x n a, 64 <= x -> 1 <= n -> cb_hull x n a ->
SHADOW_OFF <= a /\ a < SHADOW_OFF + (x + n) / 8 + 8.
Proof.
intros x n a Hx Hn Ha. unfold cb_hull in Ha.
assert (E1 : shadow_addr x = SHADOW_OFF + x / 8) by reflexivity.
assert (E2 : shadow_addr (x + n - 1) = SHADOW_OFF + (x + n - 1) / 8) by reflexivity.
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia)) as M1.
pose proof (Z.mul_div_le (shadow_addr (x + n - 1)) 8 ltac:(lia)) as D2.
assert (X8 : 8 <= x / 8) by (apply Z.div_le_lower_bound; lia).
pose proof (Z.div_le_mono (x + n - 1) (x + n) 8 ltac:(lia) ltac:(lia)) as D3.
unfold SHADOW_OFF in *. split; lia.
Qed.

(* the shadow hull of a frame object at F + c, c >= 0x20, lies in F's first 116 shadow bytes *)
Lemma hw7b_hull_in : forall F c n a, F mod 32 = 0 -> 0 <= F -> 0x20 <= c -> 0 <= n -> c + n <= 864 ->
cb_hull (F + c) n a -> shadow_addr F <= a < shadow_addr F + 116.
Proof.
intros F c n a HF HF0 Hc Hn Hcn Ha. unfold cb_hull, shadow_addr, SHADOW_OFF in *.
pose proof (Z.div_mod F 32 ltac:(lia)) as DF. rewrite HF, Z.add_0_r in DF.
set (q := F / 32) in *.
assert (E1 : (F + c) / 8 = 4 * q + c / 8).
{ rewrite DF. replace (32 * q + c) with (c + (4 * q) * 8) by ring. rewrite Z.div_add by lia. lia. }
assert (E0 : F / 8 = 4 * q).
{ rewrite DF. replace (32 * q) with ((4 * q) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
rewrite E1 in Ha. rewrite E0.
assert (Hc8 : 4 <= c / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hu : (F + c + n - 1) / 8 < 4 * q + 108).
{ apply Z.div_lt_upper_bound; [lia|]. lia. }
pose proof (Z.div_mod (2147450880 + (4 * q + c / 8)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (2147450880 + (4 * q + c / 8)) 8 ltac:(lia)) as M1.
pose proof (Z.mul_div_le (2147450880 + (F + c + n - 1) / 8) 8 ltac:(lia)) as D2.
lia.
Qed.
Lemma hw7b_hull_fsh : forall H mem F pat c n, hd_fsh rsegs H mem F pat -> Z.of_nat (length pat) = 116 ->
F mod 32 = 0 -> 0 <= F -> 0x20 <= c -> 0 <= n -> c + n <= 864 ->
shadow_hull_vis (aview rsegs H mem) (F + c) n.
Proof.
intros H mem F pat c n Hf Hl HF HF0 Hc Hn Hcn s Hs.
pose proof (hw7b_hull_in F c n s HF HF0 Hc Hn Hcn Hs) as Hin.
unfold hd_fsh in Hf. rewrite Hl in Hf.
replace s with (shadow_addr F + (s - shadow_addr F)) by lia.
rewrite (Hf (s - shadow_addr F) ltac:(lia)). discriminate.
Qed.

(* the four bytes of a 4-byte cell holding a value below 2 ^ 32 *)
Lemma hw7b_le32_split : forall v,
le32 v = [Z_to_bv 8 v; Z_to_bv 8 (Z.shiftr v 8); Z_to_bv 8 (Z.shiftr v 16); Z_to_bv 8 (Z.shiftr v 24)].
Proof. intros v. unfold le32. cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. reflexivity. Qed.
Lemma hw7b_le32_view : forall H m a v, 0 <= v < 2 ^ 32 -> val_mem rsegs (mrestrict H m) a 4 v ->
hm_bytes rsegs H m a (le32 v).
Proof.
intros H m a v Hv V. apply hm_bytes_aview. rewrite length_le32. intros i Hi.
unfold aview. rewrite (V i Hi). cbn [option_map]. f_equal.
rewrite hw7b_le32_split.
destruct i as [|[|[|[|i]]]]; [| | | | lia]; cbn [nth]; rewrite !Z_to_bv_unsigned; unfold bv_wrap;
change (bv_modulus 8) with 256; unfold YO0f.le_byte; change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32);
rewrite (Z.mod_small v (2 ^ 32)) by exact Hv;
first [ change (8 * Z.of_nat 0) with 0; rewrite Z.shiftr_0_r
      | change (8 * Z.of_nat 1) with 8 | change (8 * Z.of_nat 2) with 16 | change (8 * Z.of_nat 3) with 24 ];
rewrite Z.mod_mod by lia; reflexivity.
Qed.
Lemma hw7b_nth_zeros : forall n j, nth j (zeros n) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof. intros n j. unfold zeros, NUL. apply nth_repeat. Qed.

Section g. Context {rc : YM05.RunCeil}.
(* R above the allocator's ceiling, F a class-4 frame in the application's memory, outside the image *)
Definition hw7b_geo (R F : Z) : Prop :=
alloc_ceiling + T_SEG_STK <= R /\ R + 0x220 <= 2 ^ 47 /\ F mod 32 = 0 /\ in_app F 1024 /\
(forall a, F <= a < F + 1024 -> ~ in_img rsegs a).

Lemma hw7b_geo_facts : forall R F, hw7b_geo R F ->
0x7fff7f800000 + 16384 <= R /\ R + 0x220 <= 2 ^ 47 /\ 4096 <= F /\ F + 1024 <= alloc_ceiling /\
alloc_ceiling + 16384 <= R /\ SHADOW_OFF <= shadow_addr F /\ shadow_addr F + 128 <= alloc_ceiling /\
(F + 1024 <= shadow_addr F \/ shadow_addr F + 128 <= F) /\ F mod 8 = 0 /\
(F + 1024 <= kLowShadowBeg \/ kHighMemBeg <= F) /\ shadow_addr F = SHADOW_OFF + 4 * (F / 32) /\ F = 32 * (F / 32).
Proof.
intros R F (G1 & G2 & G3 & G4 & G5).
destruct (cb_bounds F G3 G4) as (B1 & B2 & B3 & B4 & B5 & _).
destruct (cb_div F G3) as [D1 D2].
pose proof (@asan_consts rc) as ((HC1 & HC2) & _).
assert (HT : T_SEG_STK = 16384) by reflexivity. rewrite HT in G1.
split; [lia|]. split; [exact G2|]. split; [exact B1|]. split; [exact B2|]. split; [exact G1|].
split; [rewrite D2; pose proof (Z.div_pos F 32 ltac:(lia) ltac:(lia)); lia|].
split; [exact B4|]. split; [exact B5|].
split; [rewrite D1; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by ring; apply Z.mod_mul; lia|].
split; [destruct G4 as [_ [X|[X _]]]; [left; exact X | right; exact X]|].
split; [exact D2 | exact D1].
Qed.

Lemma hw7b_nZ1_img : forall R F L a, hw7b_geo R F -> 0 <= L <= 95 -> in_img rsegs a -> ~ hw7b_Z1 R F L a.
Proof.
intros R F L a G HL Hi. pose proof (hw7b_geo_facts R F G) as (G1 & G2 & G3 & G4 & _).
pose proof (img_segs_low a Hi) as Hlow. destruct G as (_ & _ & _ & _ & G5).
unfold hw7b_Z1, ESTACK, kLowMemEnd in *.
intros [X|[X|[X|X]]]; try lia; apply (G5 a); [lia | exact Hi | lia | exact Hi].
Qed.
Lemma hw7b_nZ1_sh : forall R F L a, hw7b_geo R F -> 0 <= L <= 95 -> SHADOW_OFF <= a < kHighMemBeg -> ~ hw7b_Z1 R F L a.
Proof.
intros R F L a G HL Ha. pose proof (hw7b_geo_facts R F G) as (G1 & G2 & G3 & G4 & _ & _ & _ & _ & _ & G10 & _).
unfold hw7b_Z1, ESTACK, SHADOW_OFF, kHighMemBeg, kLowShadowBeg in *. lia.
Qed.
Lemma hw7b_nZ1_Rlow : forall R F L o, hw7b_geo R F -> 0 <= L <= 95 -> 0 <= o < 0x178 -> ~ hw7b_Z1 R F L (R + o).
Proof.
intros R F L o G HL Ho. pose proof (hw7b_geo_facts R F G) as (G1 & G2 & G3 & G4 & G5 & _).
unfold hw7b_Z1, ESTACK in *. lia.
Qed.
Lemma hw7b_nZ1_mid : forall R F L a, hw7b_geo R F -> 0 <= L <= 95 ->
(F + 0x80 <= a < F + 0x210 \/ F + 0x219 + L <= a < F + 0x278) -> ~ hw7b_Z1 R F L a.
Proof.
intros R F L a G HL Ha. pose proof (hw7b_geo_facts R F G) as (G1 & G2 & G3 & G4 & G5 & _).
unfold hw7b_Z1, ESTACK in *. lia.
Qed.
(* a frame sub-range is in the application's memory range the intrinsics ask *)
Lemma hw7b_amem_frame : forall R F c n, hw7b_geo R F -> 0 <= c -> 0 <= n -> c + n <= 1024 -> amem_range (F + c) n.
Proof.
intros R F c n G Hc Hn Hcn. destruct G as (_ & _ & _ & [_ HA] & _). pose proof ASAN_CEIL_range as [[C1 C2] _].
unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
Qed.
End g.

(* ===================================== registers across steps ===================================== *)
(* the registers the cut J keeps (HPgCaseBJ.cj_kregs) *)
Definition hw7b_keep : list Z := [2; 3; 4; 8; 9; 19; 22; 24; 25; 27].
Definition hw7b_req (l : list Z) (regs regs' : bvmap 5 word) : Prop :=
forall r, In r l -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Lemma hw7b_req_blk : forall l clob (regs0 regs1 regs2 : bvmap 5 word),
hw7b_req l regs0 regs1 ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q clob -> getr regs2 q = getr regs1 q) ->
forallb (fun r => cb_regok clob r) l = true -> hw7b_req l regs0 regs2.
Proof.
intros l clob regs0 regs1 regs2 H1 H2 Hb r Hr. rewrite (cb_reg_kept regs1 regs2 clob r H2).
- exact (H1 r Hr).
- exact (proj1 (forallb_forall _ _) Hb r Hr).
Qed.
Lemma hw7b_req_call : forall l (regs0 regs1 regs2 : bvmap 5 word),
hw7b_req l regs0 regs1 -> (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
Forall acallee_saved l -> hw7b_req l regs0 regs2.
Proof.
intros l regs0 regs1 regs2 H1 H2 Hc r Hr. rewrite (H2 r (proj1 (Forall_forall _ _) Hc r Hr)). exact (H1 r Hr).
Qed.
Lemma hw7b_req_iter : forall l (regs0 regs1 regs2 : bvmap 5 word),
hw7b_req l regs0 regs1 -> (forall r, acallee_saved r -> r <> 20 -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
Forall (fun r => acallee_saved r /\ r <> 20) l -> hw7b_req l regs0 regs2.
Proof.
intros l regs0 regs1 regs2 H1 H2 Hc r Hr. destruct (proj1 (Forall_forall _ _) Hc r Hr) as [Hcs Hn].
rewrite (H2 r Hcs Hn). exact (H1 r Hr).
Qed.
Lemma hw7b_keep_cs : Forall acallee_saved hw7b_keep.
Proof. apply Forall_forall. intros z Hz. unfold hw7b_keep in Hz. cbn [In] in Hz. unfold acallee_saved. lia. Qed.
Lemma hw7b_keep_cs20 : Forall (fun r => acallee_saved r /\ r <> 20) hw7b_keep.
Proof. apply Forall_forall. intros z Hz. unfold hw7b_keep in Hz. cbn [In] in Hz. unfold acallee_saved. lia. Qed.
Lemma hw7b_getr_eq : forall (regs regs' : bvmap 5 word) (r : Z) (q : bv 5), bv_unsigned q = r ->
getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r) -> getr regs' q = getr regs q.
Proof. intros regs regs' r q Hq H. rewrite !(cb_regZ _ q r Hq) in H. exact H. Qed.
(* a register a parts-loop turn keeps (callee-saved, not s4) *)
Lemma hw7b_it : forall (r r2 : bvmap 5 word) (q : bv 5) z,
(forall z, acallee_saved z -> z <> 20 -> getr r2 (Z_to_bv 5 z) = getr r (Z_to_bv 5 z)) ->
bv_unsigned q = z -> acallee_saved z -> z <> 20 -> getr r2 q = getr r q.
Proof. intros r r2 q z H Hq Hc Hn. exact (hw7b_getr_eq r r2 z q Hq (H z Hc Hn)). Qed.
(* a register a call keeps (callee-saved) *)
Lemma hw7b_ap : forall (r r2 : bvmap 5 word) (q : bv 5) z, aregs_preserved r r2 ->
bv_unsigned q = z -> acallee_saved z -> getr r2 q = getr r q.
Proof. intros r r2 q z H Hq Hc. exact (hw7b_getr_eq r r2 z q Hq (H z Hc)). Qed.
Ltac w7in := unfold hw7b_keep; cbn [In]; lia.
Ltac w7cs := unfold acallee_saved; lia.

(* the frame's shadow at G and at J: they differ exactly where t and ch go out of scope *)
Lemma hw7b_PG_PJ : forall i, 0 <= i < 116 ->
(4 <= i < 16 \/ 20 <= i < 23 -> nth (Z.to_nat i) (hmu_sh false false false false false true false false) 0 = 248) /\
(~ (4 <= i < 16 \/ 20 <= i < 23) -> nth (Z.to_nat i) (hmu_sh false false false false false true false false) 0 =
  nth (Z.to_nat i) (hmu_sh true true false false false true false false) 0).
Proof.
intros i Hi.
assert (HB : forallb (fun j => let z := Z.of_nat j in
  (implb ((4 <=? z) && (z <? 16) || (20 <=? z) && (z <? 23))
     (nth j (hmu_sh false false false false false true false false) 0 =? 248)) &&
  (implb (negb ((4 <=? z) && (z <? 16) || (20 <=? z) && (z <? 23)))
     (nth j (hmu_sh false false false false false true false false) 0 =?
      nth j (hmu_sh true true false false false true false false) 0))) (seq 0 116) = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in HB. specialize (HB (Z.to_nat i) ltac:(apply in_seq; lia)). cbv beta zeta in HB.
rewrite Z2Nat.id in HB by lia. apply andb_prop in HB as [H1 H2].
destruct ((4 <=? i) && (i <? 16) || (20 <=? i) && (i <? 23)) eqn:E.
- apply Bool.orb_true_iff in E. cbn [implb negb] in H1, H2. apply Z.eqb_eq in H1.
  split; [intros _; exact H1|]. intros Hc. exfalso. apply Hc.
  destruct E as [E|E]; apply andb_prop in E as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2; lia.
- apply Bool.orb_false_iff in E as [E1 E2]. cbn [implb negb] in H1, H2. apply Z.eqb_eq in H2.
  split; [|intros _; exact H2]. intros Hc. exfalso.
  apply Bool.andb_false_iff in E1. apply Bool.andb_false_iff in E2.
  destruct E1 as [E1|E1]; [apply Z.leb_gt in E1 | apply Z.ltb_ge in E1];
  (destruct E2 as [E2|E2]; [apply Z.leb_gt in E2 | apply Z.ltb_ge in E2]); lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis HA1 : hw7b_A1_stmt B.
Hypothesis HA2 : hw7b_A2_stmt B.
Hypothesis HC : hw7b_C_stmt B.
Hypothesis HD : hw7b_D_stmt B.
Hypothesis HE1 : hw7b_E1_stmt B.
Hypothesis HE2 : hw7b_E2_stmt B.
Hypothesis HIT : hw7b_iter_stmt B.
Hypothesis HMC : hw7b_memcpy_at_stmt B.
Hypothesis HSC : hw7b_strok_cstr_stmt.
Hypothesis HSCH : hw7b_strok_ch_stmt.

(* ===================================== one parts-loop turn, packaged =====================================
   The turn writes the part s after the parts P already in t; the continuation sees t holding P ++ s. *)
Lemma hw7b_turn : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k (regs : bvmap 5 word) R F (P : list byte)
  x s (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
hw7b_geo R F -> R mod 32 = 0 -> R + 0x220 <= sp0 -> sp0 - STK <= R - T_SEG_STK -> sp0 mod 16 = 0 ->
getr regs 1 = w64 HW7B_AFTER_STRLEN -> getr regs 10 = w64 x -> getr regs 23 = w64 x ->
getr regs 26 = w64 (Z.of_nat (length P)) -> getr regs 25 = w64 (F + 0x20) -> getr regs 2 = w64 R ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
cb_strok W mem R x s -> aro_unowned rsegs B (aview rsegs (w_H W) mem) ->
(length s <= 21)%nat -> (length P + length s <= 44)%nat -> (length P <= 40)%nat ->
hd_fsh rsegs (w_H W) mem F (hmu_sh true true false false false true false false) ->
(forall a, F <= a < F + 1024 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
(forall a, cb_strz x s a -> 0 <= a < R - 2 * ESTACK) ->
(F + 0x20 + Z.of_nat (length P) + Z.of_nat (length s) <= x \/ x + Z.of_nat (length s) <= F + 0x20 + Z.of_nat (length P)) ->
hm_bytes rsegs (w_H W) mem (F + 0x20) P ->
(forall regs2 mem2 md2,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k -> same_io md md2 ->
 (forall r, acallee_saved r -> r <> 20 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
 getr regs2 20 = w64 (Z.of_nat (length s)) ->
 hm_bytes rsegs (w_H W) mem2 (F + 0x20) (P ++ s) ->
 cb_kept W mem mem2 (fun a => R - 2 * ESTACK <= a < R \/
   F + 0x20 + Z.of_nat (length P) <= a < F + 0x20 + Z.of_nat (length P) + Z.of_nat (length s)) ->
 (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
 SRr rsegs W (mkCfg (mkst regs2 (Z_to_bv 64 HW7B_AFTER_MEMCPY) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 HW7B_STRLEN) mem (seg_rom rsegs)) md) Q.
Proof using HIT.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs R F P x s Q HJ G HR32 HRs HSTK Hs16
  H1 H10 H23 H26 H25 H2 H3 H4 HSO Haro Hls HlP HlP40 Hfsh Hfw Hzs Hdis HP K.
pose proof (hw7b_geo_facts R F G) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof G as (_ & _ & GF32 & _ & _).
assert (HE : ESTACK = 4096) by reflexivity. assert (HT : T_SEG_STK = 16384) by reflexivity.
set (n := Z.of_nat (length P)) in *. set (l := Z.of_nat (length s)) in *.
assert (Hl21 : 0 <= l <= 21) by (unfold l; lia). assert (Hn40 : 0 <= n <= 40) by (unfold n, l in *; lia).
assert (Hnl : n + l <= 44) by (unfold n, l in *; lia).
apply (HIT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs R (F + 0x20) n x s Q HJ H1 H10 H23 H26 H25 H2 H3 H4).
- assert (R mod 16 = 0); [|exact H].
  pose proof (Z.div_mod R 32 ltac:(lia)) as D. rewrite HR32, Z.add_0_r in D. rewrite D.
  replace (32 * (R / 32)) with ((2 * (R / 32)) * 16) by ring. apply Z.mod_mul. lia.
- exact Hs16.
- lia.
- rewrite HE, HT in *. lia.
- rewrite HE. lia.
- lia.
- exact HSO.
- exact Haro.
- exact Hls.
- exact Hn40.
- lia.
- rewrite HE. lia.
- intros a Ha. apply Hfw. lia.
- replace (F + 0x20 + n) with (F + (0x20 + n)) by lia. apply (hw7b_amem_frame R F); [exact G | lia | lia | lia].
- replace (F + 0x20 + n) with (F + HMU_T + n) by (unfold HMU_T; lia).
  apply (hmu_B_ra_t rsegs _ _ F true false false false true false false n l Hfsh G9); lia.
- intros Hl0. replace (F + 0x20 + n) with (F + (0x20 + n)) by lia.
  apply (hw7b_hull_fsh _ _ F _ (0x20 + n) l Hfsh ltac:(rewrite hmu_sh_len; reflexivity) GF32 ltac:(lia)); lia.
- intros a Ha. replace (F + 0x20 + n) with (F + (0x20 + n)) in Ha by lia.
  pose proof (hw7b_hull_in F (0x20 + n) l a GF32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ha). rewrite HE. unfold SHADOW_OFF in *. lia.
- exact Hzs.
- exact Hdis.
- intros regs2 mem2 md2 HJ2 Hio2 Hr2 H20 Hby Hk Hpr.
  apply (K regs2 mem2 md2 HJ2 Hio2 Hr2 H20); [| exact Hk | exact Hpr].
  apply hm_bytes_app. split.
  + apply (hm_bytes_kept rsegs (w_H W) mem (w_H W) mem2 _ P HP).
    intros y Hy. apply Hk; [lia|]. cbv beta. unfold n in *. rewrite HE. lia.
  + apply hm_bytes_aview. intros j Hj. fold n. exact (Hby j Hj).
Qed.

(* ===================================== the walk ===================================== *)
Section w.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (Sv : astate) (W0 : world rsegs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (R F p : Z) (chs : list byte)
  (pa vlen vcur vpp : Z) (Q : world rsegs -> config -> Prop).
Hypothesis HJ : ajournal rsegs B STK sp0 FP ly Sv W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis H2 : getr regs 2 = w64 R.
Hypothesis H9 : getr regs 9 = w64 R.
Hypothesis H3 : getr regs 3 = w64 (as_gp B).
Hypothesis H4 : getr regs 4 = w64 (as_tp B).
Hypothesis HR32 : R mod 32 = 0.
Hypothesis HRs : R + 0x220 <= sp0.
Hypothesis HSTK : sp0 - STK <= R - T_SEG_STK.
Hypothesis Hs47 : sp0 <= 2 ^ 47.
Hypothesis Hs16 : sp0 mod 16 = 0.
Hypothesis HRac : alloc_ceiling + T_SEG_STK <= R.
Hypothesis HF32 : F mod 32 = 0.
Hypothesis HF4096 : 4096 <= F.
Hypothesis HFac : F + 1024 <= alloc_ceiling.
Hypothesis HFapp : in_app F 1024.
Hypothesis HFw : forall a, F <= a < F + 1024 ->
 awr_byte STK sp0 FP (ablocks B ly Sv) (ablocks B lyc Sc) lyc own a /\ aview rsegs (w_H W) memc a <> None /\
 ~ in_img rsegs a.
Hypothesis HFshw : forall i, 0 <= i < 116 ->
 awr_byte STK sp0 FP (ablocks B ly Sv) (ablocks B lyc Sc) lyc own (shadow_addr F + i).
Hypothesis HPw : forall a, R + 0x178 <= a < R + 0x198 ->
 awr_byte STK sp0 FP (ablocks B ly Sv) (ablocks B lyc Sc) lyc own a.
Hypothesis H27 : getr regs 27 = w64 SHADOW_OFF.
Hypothesis H26 : getr regs 26 = w64 p.
Hypothesis Hp : 0 <= p < 256.
Hypothesis H25 : getr regs 25 = w64 (F + 0x20).
Hypothesis H18 : getr regs 18 = w64 (F + 0xa0).
Hypothesis H19 : getr regs 19 = w64 (shadow_addr F).
Hypothesis Hfsh : hd_fsh rsegs (w_H W) memc F (hmu_sh true true false false false true false false).
Hypothesis Hch : hm_bytes rsegs (w_H W) memc (F + 0xa0) (chs ++ [NUL]).
Hypothesis Hchnz : Forall (fun b : byte => bv_unsigned b <> 0) chs.
Hypothesis Hchl : (length chs <= 21)%nat.
Hypothesis He62 : hm_bytes rsegs (w_H W) memc (F + 0x210) (zeros 104).
Hypothesis Hhpfx : hd_cstr rsegs (w_H W) memc HW7B_HPFX (hd_zbytes HPFX).
Hypothesis Hsep : hd_cstr rsegs (w_H W) memc (hw7b_sep p) (hd_zbytes (hw7b_sepb p)).
Hypothesis HPA : val_mem rsegs (mrestrict (w_H W) memc) (HW7B_PTAB p) 8 pa.
Hypothesis Hpstr : hd_cstr rsegs (w_H W) memc pa (hd_zbytes (hw7b_pab p)).
Hypothesis Hpa : 0x20f40 <= pa <= 0x21460.
Hypothesis HRAtab : range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (HW7B_PTAB p) 8.
Hypothesis HRA180 : range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (R + 0x180) 8.
Hypothesis Haro : aro_unowned rsegs B (aview rsegs (w_H W) memc).
Hypothesis V118 : val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218).
Hypothesis V130 : val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210).
Hypothesis Ve8 : val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 ((- F - 0x219) mod 2 ^ 64).
Hypothesis V138 : val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 vlen.
Hypothesis Hvlen : 0 <= vlen < 2 ^ 64.
Hypothesis V110 : val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 vcur.
Hypothesis Hvcur : 0 <= vcur < 2 ^ 64.
Hypothesis V148 : val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 vpp.
Hypothesis Hvpp : 0 <= vpp < 2 ^ 64.
Hypothesis K : forall regs2 mem2 md2,
 ajournal rsegs B STK sp0 FP ly Sv W0 mem0 md0 own lyc Sc W mem2 md2 k -> same_io mdc md2 ->
 (forall r, In r [2; 3; 4; 8; 9; 19; 22; 24; 25; 27] -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
 getr regs2 6 = getr regs 6 -> getr regs2 13 = w64 vcur -> getr regs2 18 = w64 vlen ->
 getr regs2 20 = w64 (F + 0x210) -> getr regs2 23 = w64 vpp ->
 hm_bytes rsegs (w_H W) mem2 (F + 0x210) (hw7b_e62 (hw7b_js chs p)) ->
 hd_fsh rsegs (w_H W) mem2 F (hmu_sh false false false false false true false false) ->
 cb_kept W memc mem2 (fun a => R - 2 * ESTACK <= a < R \/ R + 0x178 <= a < R + 0x198 \/
   F + 0x20 <= a < F + 0x80 \/ F + 0x210 <= a < F + 0x278 \/ shadow_addr F <= a < shadow_addr F + 116) ->
 (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
 SRr rsegs W (mkCfg (mkst regs2 (Z_to_bv 64 HW7B_J) mem2 (seg_rom rsegs)) md2) Q.

(* ---- the state the walk carries ---- *)
Definition wL : Z := Z.of_nat (length (hw7b_js chs p)).
Definition wZ1 : Z -> Prop := hw7b_Z1 R F wL.
Definition wKz (m : word -> option byte) : Prop := cb_kept W memc m wZ1.
Definition wPr (m : word -> option byte) : Prop := forall a, apresent (w_H W) memc a -> apresent (w_H W) m a.
(* the parts window from A2 on: parts[1 .. 3] = ch, sep, the param name *)
Definition wWin (m : word -> option byte) : Prop :=
val_mem rsegs (mrestrict (w_H W) m) (R + 0x180) 8 (F + 0xa0) /\
val_mem rsegs (mrestrict (w_H W) m) (R + 0x188) 8 (hw7b_sep p) /\
val_mem rsegs (mrestrict (w_H W) m) (R + 0x190) 8 pa.
(* a part: its string facts at G, the bytes it reads outside hw7b_Z1 and below the callees' stack, apart from t *)
Definition wPart (x : Z) (s : list byte) : Prop :=
cb_strok W memc R x s /\ (forall a, cb_strz x s a -> ~ wZ1 a /\ 0 <= a < R - 2 * ESTACK) /\
(length s <= 21)%nat /\ (F + 0x80 <= x \/ x + Z.of_nat (length s) <= F).
(* the state at the strlen entry of turn i on the part x = s, t holding P *)
Definition wI (i : nat) (P : list byte) (x : Z) (s : list byte) (r : bvmap 5 word) (m : word -> option byte)
(d : Model) : Prop :=
ajournal rsegs B STK sp0 FP ly Sv W0 mem0 md0 own lyc Sc W m d k /\ same_io mdc d /\
hw7b_req hw7b_keep regs r /\ getr r 21 = getr regs 6 /\
getr r 1 = w64 HW7B_AFTER_STRLEN /\ getr r 10 = w64 x /\ getr r 23 = w64 x /\
getr r 26 = w64 (Z.of_nat (length P)) /\ getr r 18 = w64 (R + 0x178 + 8 * Z.of_nat i) /\
wKz m /\ wPr m /\ hm_bytes rsegs (w_H W) m (F + 0x20) P /\ wWin m /\
(length P <= 35 /\ length P + length s <= 44)%nat /\ wPart x s.

Lemma w_G : hw7b_geo R F.
Proof.
split; [exact HRac|]. split; [lia|]. split; [exact HF32|]. split; [exact HFapp|].
intros a Ha. exact (proj2 (proj2 (HFw a Ha))).
Qed.
Lemma w_R16 : R mod 16 = 0.
Proof.
pose proof (Z.div_mod R 32 ltac:(lia)) as D. rewrite HR32, Z.add_0_r in D. rewrite D.
replace (32 * (R / 32)) with ((2 * (R / 32)) * 16) by ring. apply Z.mod_mul. lia.
Qed.
Lemma w_wL : 0 <= wL <= 44.
Proof. unfold wL. pose proof (hw7b_js_len chs p Hchl). lia. Qed.
Lemma w_nZ_img : forall a, in_img rsegs a -> ~ wZ1 a.
Proof. intros a Ha. pose proof w_wL. exact (hw7b_nZ1_img R F wL a w_G ltac:(lia) Ha). Qed.
Lemma w_nZ_sh : forall a, SHADOW_OFF <= a < kHighMemBeg -> ~ wZ1 a.
Proof. intros a Ha. pose proof w_wL. exact (hw7b_nZ1_sh R F wL a w_G ltac:(lia) Ha). Qed.
Lemma w_nZ_R : forall o, 0 <= o < 0x178 -> ~ wZ1 (R + o).
Proof. intros o Ho. pose proof w_wL. exact (hw7b_nZ1_Rlow R F wL o w_G ltac:(lia) Ho). Qed.
Lemma w_nZ_mid : forall a, (F + 0x80 <= a < F + 0x210 \/ F + 0x219 + wL <= a < F + 0x278) -> ~ wZ1 a.
Proof. intros a Ha. pose proof w_wL. exact (hw7b_nZ1_mid R F wL a w_G ltac:(lia) Ha). Qed.

Lemma w_kz_step : forall m m' (Zn : Z -> Prop), wKz m -> cb_kept W m m' Zn -> (forall a, Zn a -> wZ1 a) -> wKz m'.
Proof.
intros m m' Zn K1 K2 Hz. apply (hw7b_kept_trans W memc m m' wZ1 Zn wZ1 K1 K2).
intros a [Ha|Ha]; [exact Ha | exact (Hz a Ha)].
Qed.
Lemma w_cell : forall m o v, wKz m -> 0 <= o -> o + 8 <= 0x178 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + o) 8 v -> val_mem rsegs (mrestrict (w_H W) m) (R + o) 8 v.
Proof.
intros m o v Km Ho1 Ho2 V. unfold wKz, cb_kept in Km. apply (cb_val_kept (w_H W) memc m (R + o) 8 v); [|exact V].
intros j Hj. change (Z.of_nat 8) with 8 in Hj. pose proof (hw7b_geo_facts R F w_G) as (G1 & G2 & _).
apply Km; [lia|]. replace (R + o + j) with (R + (o + j)) by lia. apply w_nZ_R. lia.
Qed.
Lemma w_win_kept : forall m m' (Zn : Z -> Prop), wWin m -> cb_kept W m m' Zn ->
(forall a, R + 0x178 <= a < R + 0x198 -> ~ Zn a) -> wWin m'.
Proof.
intros m m' Zn (X1 & X2 & X3) Km Hz. pose proof (hw7b_geo_facts R F w_G) as (G1 & G2 & _).
split; [|split].
- apply (cb_val_kept (w_H W) m m' _ 8 _); [|exact X1].
  intros j Hj. change (Z.of_nat 8) with 8 in Hj. apply Km; [lia | apply Hz; lia].
- apply (cb_val_kept (w_H W) m m' _ 8 _); [|exact X2].
  intros j Hj. change (Z.of_nat 8) with 8 in Hj. apply Km; [lia | apply Hz; lia].
- apply (cb_val_kept (w_H W) m m' _ 8 _); [|exact X3].
  intros j Hj. change (Z.of_nat 8) with 8 in Hj. apply Km; [lia | apply Hz; lia].
Qed.
Lemma w_strok : forall m x s, wKz m -> wPart x s -> cb_strok W m R x s.
Proof.
intros m x s Km (SO & Hz & _ & _). unfold wKz, cb_kept in Km. pose proof (hw7b_geo_facts R F w_G) as (G1 & G2 & _).
apply (cb_strok_kept W memc m R x s SO). intros a Ha.
destruct (Hz a Ha) as [Z1 Z2]. apply Km; [unfold ESTACK in Z2; lia | exact Z1].
Qed.
Lemma w_fsh : forall m, wKz m -> hd_fsh rsegs (w_H W) m F (hmu_sh true true false false false true false false).
Proof.
intros m Km. unfold wKz, cb_kept in Km. apply (hm_fsh_kept rsegs (w_H W) memc (w_H W) m F _ Hfsh). intros i Hi.
rewrite hmu_sh_len in Hi. change (Z.of_nat 116) with 116 in Hi.
pose proof (hw7b_geo_facts R F w_G) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (@asan_consts rc) as ((HC1 & HC2) & _).
apply Km; [unfold SHADOW_OFF in *; lia|]. apply w_nZ_sh. unfold kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma w_aro : forall m, wKz m -> aro_unowned rsegs B (aview rsegs (w_H W) m).
Proof.
intros m Km. unfold wKz, cb_kept in Km. apply (aro_unowned_keep rsegs B _ _ Haro). intros a Ha _ _.
assert (Hi : in_img rsegs a) by (destruct Ha as (sg & Hsg & _ & Hb); exists sg; split; [exact Hsg | exact Hb]).
pose proof (img_segs_low a Hi) as Hl. apply Km; [unfold kLowMemEnd in *; lia | exact (w_nZ_img a Hi)].
Qed.

(* the image's strings lie apart from the frame for locals *)
Lemma w_img_frame : F + 1024 <= 0x20f00 \/ 0x21520 <= F.
Proof.
destruct (Z_le_gt_dec (F + 1024) 0x20f00) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec 0x21520 F) as [H'|H']; [right; exact H'|]. exfalso.
assert (Ha : F <= Z.max F 0x20f00 < F + 1024 /\ 0x20f00 <= Z.max F 0x20f00 < 0x21520) by lia.
apply (proj2 (proj2 (HFw _ (proj1 Ha)))). exact (hw7b_in_seg _ _ _ hw7b_img_strs (proj2 Ha)).
Qed.
Lemma w_zimg : forall x (s : list byte) a, 0x20f40 <= x <= 0x21460 -> (length s <= 21)%nat -> cb_strz x s a ->
~ wZ1 a /\ 0 <= a < R - 2 * ESTACK.
Proof.
intros x s a Hx Hs [Ha|Ha]; pose proof (hw7b_geo_facts R F w_G) as (G1 & G2 & _).
- split; [apply w_nZ_img, (hw7b_in_seg _ _ a hw7b_img_strs); lia | unfold ESTACK; lia].
- pose proof (hw7b_hull_box x (Z.of_nat (length s) + 1) a ltac:(lia) ltac:(lia) Ha) as [B1 B2].
  assert (B3 : (x + (Z.of_nat (length s) + 1)) / 8 <= 0x4290) by (apply Z.div_le_upper_bound; lia).
  split; [apply w_nZ_sh; unfold kHighMemBeg, SHADOW_OFF in *; lia | unfold ESTACK, SHADOW_OFF in *; lia].
Qed.
Lemma w_zch : forall a, cb_strz (F + 0xa0) chs a -> ~ wZ1 a /\ 0 <= a < R - 2 * ESTACK.
Proof.
intros a Ha. pose proof (hw7b_geo_facts R F w_G) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof w_wL as HwL. destruct Ha as [Ha|Ha].
- split; [apply w_nZ_mid; lia | unfold ESTACK; lia].
- pose proof (hw7b_hull_in F 0xa0 (Z.of_nat (length chs) + 1) a HF32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ha).
  pose proof (@asan_consts rc) as ((HC1 & HC2) & _).
  split; [apply w_nZ_sh; unfold kHighMemBeg, SHADOW_OFF in *; lia | unfold ESTACK, SHADOW_OFF in *; lia].
Qed.
Lemma w_part_img : forall x l, hd_cstr rsegs (w_H W) memc x (hd_zbytes l) -> 0x20f40 <= x <= 0x21460 ->
(length l <= 21)%nat -> wPart x l.
Proof.
intros x l HCs Hx Hl. pose proof (hw7b_geo_facts R F w_G) as (G1 & G2 & _).
split; [|split; [|split]].
- apply (HSC W memc R x l HCs); [unfold ESTACK; lia | lia].
- intros a Ha. exact (w_zimg x l a Hx Hl Ha).
- exact Hl.
- destruct w_img_frame; [left | right]; lia.
Qed.
Lemma w_part_ch : wPart (F + 0xa0) chs.
Proof.
pose proof (hw7b_geo_facts R F w_G) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _).
split; [|split; [|split]].
- apply (HSCH W memc R F chs Hfsh G9 HFapp); [unfold ESTACK; lia | | exact Hch | exact Hchnz | exact Hchl].
  intros a Ha. exact (proj1 (proj2 (HFw a ltac:(lia)))).
- exact w_zch.
- exact Hchl.
- left; lia.
Qed.

Lemma w_kq : forall r (q : bv 5) z v, hw7b_req hw7b_keep regs r -> bv_unsigned q = z -> In z hw7b_keep ->
getr regs q = v -> getr r q = v.
Proof. intros r q z v Hq Hz Hin Hv. rewrite <- Hv. exact (hw7b_getr_eq regs r z q Hz (Hq z Hin)). Qed.

(* ---- one turn and the C block after it (i = 0 .. 2) ---- *)
Lemma wturnC : forall (i : nat) P x s r m d x' s', (i < 3)%nat -> wI i P x s r m d ->
(forall m', wWin m' -> val_mem rsegs (mrestrict (w_H W) m') (R + 0x180 + 8 * Z.of_nat i) 8 x') -> 0 <= x' < 2 ^ 64 ->
wPart x' s' -> (length P + length s + length s' <= 44)%nat -> (length P + length s <= 35)%nat ->
(forall r' m' d', wI (S i) (P ++ s) x' s' r' m' d' ->
 SRr rsegs W (mkCfg (mkst r' (Z_to_bv 64 HW7B_STRLEN) m' (seg_rom rsegs)) d') Q) ->
SRr rsegs W (mkCfg (mkst r (Z_to_bv 64 HW7B_STRLEN) m (seg_rom rsegs)) d) Q.
Proof.
intros i P x s r m d x' s' Hi (HJm & Hio & Hq & H21 & R1 & R10 & R23 & R26 & R18 & Kz & Pr & HP & Win & HlP & Hpt)
  Hslot Hx' Hpt' Hl' Hl35 Kn.
pose proof Hpt as (SO & Hz & Hls & Hdx).
pose proof (hw7b_geo_facts R F w_G) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
apply (hw7b_turn STK sp0 FP ly Sv W0 mem0 md0 own lyc Sc W m d k r R F P x s Q HJm w_G HR32 HRs HSTK Hs16 R1 R10 R23 R26
  (w_kq r 25%bv 25 _ Hq eq_refl ltac:(w7in) H25) (w_kq r 2%bv 2 _ Hq eq_refl ltac:(w7in) H2)
  (w_kq r 3%bv 3 _ Hq eq_refl ltac:(w7in) H3) (w_kq r 4%bv 4 _ Hq eq_refl ltac:(w7in) H4)
  (w_strok m x s Kz Hpt) (w_aro m Kz) Hls ltac:(lia) ltac:(lia) (w_fsh m Kz)).
- intros a Ha. exact (proj1 (HFw a Ha)).
- intros a Ha. exact (proj2 (Hz a Ha)).
- destruct Hdx; [left | right]; lia.
- exact HP.
- intros r2 m2 d2 HJ2 Hio2 Hr2 H20 Hby Hk Hpr.
  assert (Kz2 : wKz m2).
  { apply (w_kz_step m m2 _ Kz Hk). intros a Ha. cbv beta in Ha. unfold wZ1, hw7b_Z1.
    destruct Ha as [Ha|Ha]; [left; exact Ha | right; right; left; lia]. }
  assert (Win2 : wWin m2).
  { apply (w_win_kept m m2 _ Win Hk). intros a Ha Hz'. cbv beta in Hz'. unfold ESTACK in Hz'. lia. }
  eapply SRr_bind.
  { apply (HC STK sp0 FP ly Sv W0 mem0 md0 own lyc Sc W m2 d2 k r2 i R (Z.of_nat (length P)) (Z.of_nat (length s)) x' HJ2 Hi).
    - rewrite (hw7b_it r r2 9%bv 9 Hr2 eq_refl ltac:(w7cs) ltac:(lia)).
      exact (w_kq r 9%bv 9 _ Hq eq_refl ltac:(w7in) H9).
    - lia.
    - lia.
    - exact w_R16.
    - rewrite (hw7b_it r r2 18%bv 18 Hr2 eq_refl ltac:(w7cs) ltac:(lia)). exact R18.
    - rewrite (hw7b_it r r2 26%bv 26 Hr2 eq_refl ltac:(w7cs) ltac:(lia)). exact R26.
    - exact H20.
    - lia.
    - lia.
    - exact (Hslot m2 Win2).
    - exact Hx'. }
  cbv beta. intros W3 c3 _ (-> & r3 & m3 & d3 & -> & HJ3 & Hio3 & Hk3 & HK3 & Hpr3 & (S1 & S10 & S23 & S18 & S26)).
  apply Kn.
  refine (conj HJ3 (conj _ (conj _ (conj _ (conj S1 (conj S10 (conj S23 (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ Hpt')))))))))))))).
  + exact (same_io_trans _ _ _ (same_io_trans _ _ _ Hio Hio2) Hio3).
  + apply (hw7b_req_blk _ [1; 10; 18; 23; 26]%bv regs r2 r3); [| exact Hk3 | vm_compute; reflexivity].
    exact (hw7b_req_iter _ regs r r2 Hq Hr2 hw7b_keep_cs20).
  + rewrite (cb_kept_bv r2 r3 _ 21%bv Hk3 ltac:(vm_compute; reflexivity)).
    rewrite (hw7b_it r r2 21%bv 21 Hr2 eq_refl ltac:(w7cs) ltac:(lia)). exact H21.
  + rewrite S26, length_app, Nat2Z.inj_add. reflexivity.
  + rewrite S18. unfold w64. f_equal. lia.
  + exact (w_kz_step m2 m3 (fun _ => False) Kz2 HK3 (fun a h => match h with end)).
  + intros a Ha. exact (Hpr3 a (Hpr a (Pr a Ha))).
  + apply (hm_bytes_kept rsegs (w_H W) m2 (w_H W) m3 _ _ Hby). intros y Hy.
    rewrite length_app in Hy. apply HK3; [lia | intros []].
  + exact (w_win_kept m2 m3 (fun _ => False) Win2 HK3 (fun a _ h => h)).
  + rewrite length_app. lia.
Qed.

(* ---- the last turn, D, the memcpy, E1, E2 and J ---- *)
Lemma wlast : forall P r m d, wI 3 P pa (hw7b_pab p) r m d -> (length P <= 40)%nat ->
P ++ hw7b_pab p = hw7b_js chs p ->
SRr rsegs W (mkCfg (mkst r (Z_to_bv 64 HW7B_STRLEN) m (seg_rom rsegs)) d) Q.
Proof.
intros P r m d (HJm & Hio & Hq & H21 & R1 & R10 & R23 & R26 & R18 & Kz & Pr & HP & Win & HlP & Hpt) HP40 HPjs.
pose proof Hpt as (SO & Hz & Hls & Hdx).
pose proof (hw7b_geo_facts R F w_G) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (@asan_consts rc) as ((HC1 & HC2) & _).
assert (HE : ESTACK = 4096) by reflexivity. assert (HT : T_SEG_STK = 16384) by reflexivity.
assert (EwL : wL = Z.of_nat (length (hw7b_js chs p))) by reflexivity.
pose proof w_wL as HwL.
assert (EL : Z.of_nat (length P) + Z.of_nat (length (hw7b_pab p)) = wL)
  by (rewrite EwL, <- HPjs, length_app; lia).
apply (hw7b_turn STK sp0 FP ly Sv W0 mem0 md0 own lyc Sc W m d k r R F P pa (hw7b_pab p) Q HJm w_G HR32 HRs HSTK Hs16
  R1 R10 R23 R26
  (w_kq r 25%bv 25 _ Hq eq_refl ltac:(w7in) H25) (w_kq r 2%bv 2 _ Hq eq_refl ltac:(w7in) H2)
  (w_kq r 3%bv 3 _ Hq eq_refl ltac:(w7in) H3) (w_kq r 4%bv 4 _ Hq eq_refl ltac:(w7in) H4)
  (w_strok m pa _ Kz Hpt) (w_aro m Kz) Hls ltac:(lia) HP40 (w_fsh m Kz)).
- intros a Ha. exact (proj1 (HFw a Ha)).
- intros a Ha. exact (proj2 (Hz a Ha)).
- destruct Hdx; [left | right]; lia.
- exact HP.
- intros r2 m2 d2 HJ2 Hio2 Hr2 H20 Hby Hk Hpr.
  rewrite HPjs in Hby.
  assert (Kz2 : wKz m2).
  { apply (w_kz_step m m2 _ Kz Hk). intros a Ha. cbv beta in Ha. unfold wZ1, hw7b_Z1.
    destruct Ha as [Ha|Ha]; [left; exact Ha | right; right; left; lia]. }
  (* ======================== D ======================== *)
  eapply SRr_bind.
  { apply (HD STK sp0 FP ly Sv W0 mem0 md0 own lyc Sc W m2 d2 k r2 R (Z.of_nat (length P))
      (Z.of_nat (length (hw7b_pab p))) (F + 0x20) (F + 0x218) HJ2).
    - rewrite (hw7b_it r r2 9%bv 9 Hr2 eq_refl ltac:(w7cs) ltac:(lia)).
      exact (w_kq r 9%bv 9 _ Hq eq_refl ltac:(w7in) H9).
    - lia.
    - lia.
    - exact w_R16.
    - rewrite (hw7b_it r r2 18%bv 18 Hr2 eq_refl ltac:(w7cs) ltac:(lia)). rewrite R18. unfold w64. f_equal. lia.
    - rewrite (hw7b_it r r2 26%bv 26 Hr2 eq_refl ltac:(w7cs) ltac:(lia)). exact R26.
    - exact H20.
    - lia.
    - lia.
    - rewrite (hw7b_it r r2 25%bv 25 Hr2 eq_refl ltac:(w7cs) ltac:(lia)).
      exact (w_kq r 25%bv 25 _ Hq eq_refl ltac:(w7in) H25).
    - exact (w_cell m2 0x118 _ Kz2 ltac:(lia) ltac:(lia) V118).
    - lia. }
  cbv beta. intros W3 c3 _ (-> & r3 & m3 & d3 & -> & HJ3 & Hio3 & Hk3 & HK3 & Hpr3 & (D1 & D10 & D11 & D12 & D23 & D26)).
  rewrite EL in D12, D26.
  assert (Hq3 : hw7b_req hw7b_keep regs r3).
  { apply (hw7b_req_blk _ [1; 10; 11; 12; 18; 23; 26]%bv regs r2 r3); [| exact Hk3 | vm_compute; reflexivity].
    exact (hw7b_req_iter _ regs r r2 Hq Hr2 hw7b_keep_cs20). }
  assert (Kz3 : wKz m3) by exact (w_kz_step m2 m3 (fun _ => False) Kz2 HK3 (fun a h => match h with end)).
  assert (Hsp3 : spZ r3 = sp0 + (R - sp0)).
  { unfold spZ. rewrite (w_kq r3 2%bv 2 _ Hq3 eq_refl ltac:(w7in) H2). unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (Hby3 : hm_bytes rsegs (w_H W) m3 (F + 0x20) (hw7b_js chs p)).
  { apply (hm_bytes_kept rsegs (w_H W) m2 (w_H W) m3 _ _ Hby). intros y Hy. apply HK3; [lia | intros []]. }
  (* ======================== memcpy(e62.body, t, |js|) ======================== *)
  eapply SRr_bind.
  { apply (HMC W r3 m3 STK sp0 FP ly Sv W0 mem0 md0 own lyc Sc d3 k (F + 0x218) (F + 0x20) wL (R - sp0)
      (w64 HW7B_AFTER_TEXT) HJ3 D10 D11 D12).
    - lia.
    - lia.
    - lia.
    - exact Hsp3.
    - rewrite Zminus_mod, w_R16, Hs16. reflexivity.
    - lia.
    - rewrite HE, HT in *. lia.
    - exact (w_kq r3 3%bv 3 _ Hq3 eq_refl ltac:(w7in) H3).
    - exact (w_kq r3 4%bv 4 _ Hq3 eq_refl ltac:(w7in) H4).
    - exact D1.
    - apply ret_ok_even. vm_compute. reflexivity.
    - intros a Ha. split; [exact (proj1 (HFw a ltac:(lia))) | rewrite HE; lia].
    - exact (hw7b_amem_frame R F 0x218 wL w_G ltac:(lia) ltac:(lia) ltac:(lia)).
    - replace (F + 0x218) with (F + HMU_E62 + 8) by (unfold HMU_E62; lia).
      exact (hmu_B_ra_e62 rsegs _ _ F true true false false false false false 8 wL (w_fsh m3 Kz3) G9 ltac:(lia) ltac:(lia)).
    - intros Hn0. exact (hw7b_hull_fsh _ _ F _ 0x218 wL (w_fsh m3 Kz3) ltac:(rewrite hmu_sh_len; reflexivity) HF32
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    - lia.
    - lia.
    - intros a Ha. split.
      + pose proof (proj1 (hm_bytes_aview rsegs (w_H W) m3 (F + 0x20) _) Hby3 (Z.to_nat (a - (F + 0x20))) ltac:(lia)) as X.
        rewrite Z2Nat.id in X by lia. replace (F + 0x20 + (a - (F + 0x20))) with a in X by lia. rewrite X. discriminate.
      + rewrite Hsp3, HE. lia.
    - right. lia.
    - exact (hw7b_amem_frame R F 0x20 wL w_G ltac:(lia) ltac:(lia) ltac:(lia)).
    - replace (F + 0x20) with (F + HMU_T + 0) by (unfold HMU_T; lia).
      exact (hmu_B_ra_t rsegs _ _ F true false false false true false false 0 wL (w_fsh m3 Kz3) G9 ltac:(lia) ltac:(lia)).
    - intros Hn0. exact (hw7b_hull_fsh _ _ F _ 0x20 wL (w_fsh m3 Kz3) ltac:(rewrite hmu_sh_len; reflexivity) HF32
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
  cbv beta. intros W4 c4 _ (-> & r4 & m4 & d4 & -> & HJ4 & Hio4 & HP4 & M10 & Mcp & Mk & Mpr).
  assert (Kz4 : wKz m4).
  { apply (w_kz_step m3 m4 (fun a => F + 0x218 <= a < F + 0x218 + wL \/ R - ESTACK <= a < R) Kz3).
    - intros a Ha Hz'. apply Mk; [exact Ha | intros X; apply Hz'; left; exact X | intros X; apply Hz'; right; lia].
    - intros a Ha. cbv beta in Ha. unfold wZ1, hw7b_Z1. rewrite HE in *.
      destruct Ha as [Ha|Ha]; [right; right; right; lia | left; lia]. }
  assert (Hq4 : hw7b_req hw7b_keep regs r4) by exact (hw7b_req_call _ regs r3 r4 Hq3 HP4 hw7b_keep_cs).
  assert (Evc : (- F - 0x219) mod 2 ^ 64 = 2 ^ 64 - F - 0x219) by (symmetry; apply Z.mod_unique with (q := -1); lia).
  (* ======================== E1 ======================== *)
  eapply SRr_bind.
  { apply (HE1 STK sp0 FP ly Sv W0 mem0 md0 own lyc Sc W m4 d4 k r4 R (F + 0x218) wL vlen (F + 0x210)
      ((- F - 0x219) mod 2 ^ 64) HJ4).
    - exact (w_kq r4 9%bv 9 _ Hq4 eq_refl ltac:(w7in) H9).
    - lia.
    - lia.
    - exact w_R16.
    - rewrite (hw7b_ap r3 r4 23%bv 23 HP4 eq_refl ltac:(w7cs)). exact D23.
    - rewrite (hw7b_ap r3 r4 26%bv 26 HP4 eq_refl ltac:(w7cs)). exact D26.
    - lia.
    - lia.
    - lia.
    - exact (w_cell m4 0x138 _ Kz4 ltac:(lia) ltac:(lia) V138).
    - exact Hvlen.
    - exact (w_cell m4 0x130 _ Kz4 ltac:(lia) ltac:(lia) V130).
    - lia.
    - exact (w_cell m4 0xe8 _ Kz4 ltac:(lia) ltac:(lia) Ve8).
    - rewrite Evc. lia. }
  cbv beta. intros W5 c5 _ (-> & r5 & m5 & d5 & -> & HJ5 & Hio5 & Hk5 & HK5 & Hpr5 & (E10 & E18 & E20 & E26)).
  assert (Kz5 : wKz m5) by exact (w_kz_step m4 m5 (fun _ => False) Kz4 HK5 (fun a h => match h with end)).
  assert (Hq5 : hw7b_req hw7b_keep regs r5).
  { apply (hw7b_req_blk _ [10; 18; 20; 26]%bv regs r4 r5 Hq4 Hk5). vm_compute. reflexivity. }
  set (lv := bv_unsigned (getr regs 6)).
  assert (H21_5 : getr r5 21 = w64 lv).
  { rewrite (cb_kept_bv r4 r5 _ 21%bv Hk5 ltac:(vm_compute; reflexivity)).
    rewrite (hw7b_ap r3 r4 21%bv 21 HP4 eq_refl ltac:(w7cs)).
    rewrite (cb_kept_bv r2 r3 _ 21%bv Hk3 ltac:(vm_compute; reflexivity)).
    rewrite (hw7b_it r r2 21%bv 21 Hr2 eq_refl ltac:(w7cs) ltac:(lia)).
    rewrite H21. unfold lv, w64. symmetry. apply Z_to_bv_bv_unsigned. }
  (* ======================== E2 ======================== *)
  eapply SRr_bind.
  { apply (HE2 STK sp0 FP ly Sv W0 mem0 md0 own lyc Sc W m5 d5 k r5 R (shadow_addr F) (F + 0x218 + wL) (F + 0x210)
      (wL + 1) lv vcur vpp HJ5 E10).
    - exact (w_kq r5 9%bv 9 _ Hq5 eq_refl ltac:(w7in) H9).
    - lia.
    - lia.
    - exact w_R16.
    - exact (w_kq r5 19%bv 19 _ Hq5 eq_refl ltac:(w7in) H19).
    - exact E20.
    - exact E26.
    - lia.
    - exact H21_5.
    - exact (w_cell m5 0x110 _ Kz5 ltac:(lia) ltac:(lia) V110).
    - exact Hvcur.
    - exact (w_cell m5 0x148 _ Kz5 ltac:(lia) ltac:(lia) V148).
    - exact Hvpp.
    - lia.
    - lia.
    - lia.
    - unfold SHADOW_OFF in *. lia.
    - destruct G8; [right | left]; lia.
    - lia.
    - exact (proj1 (HFw (F + 0x218 + wL) ltac:(lia))).
    - intros a Ha. exact (proj1 (HFw a ltac:(lia))).
    - intros a Ha. replace a with (shadow_addr F + (a - shadow_addr F)) by lia. apply HFshw. lia. }
  cbv beta. intros W6 c6 _ (-> & r6 & m6 & d6 & -> & HJ6 & Hio6 & Hk6 & HK6 & Hpr6 & (F13 & F23 & F6 & Fnul & Fty & Fsz & Fsh)).
  (* what E2 keeps of a frame byte outside its zone, and of a shadow byte of F outside its granules *)
  assert (KE2 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (a = F + 0x218 + wL \/ F + 0x210 <= a < F + 0x210 + 8 \/ shadow_addr F + 4 <= a < shadow_addr F + 0x10 \/
       shadow_addr F + 0x14 <= a < shadow_addr F + 0x17) -> aview rsegs (w_H W) m6 a = aview rsegs (w_H W) m5 a)
    by exact HK6.
  pose proof Kz5 as Kz5'. unfold wKz, cb_kept in Kz5'.
  (* ======================== J ======================== *)
  apply K.
  + exact HJ6.
  + exact (same_io_trans _ _ _ (same_io_trans _ _ _ (same_io_trans _ _ _ (same_io_trans _ _ _
      (same_io_trans _ _ _ Hio Hio2) Hio3) Hio4) Hio5) Hio6).
  + exact (hw7b_req_blk _ [6; 10; 13; 23]%bv regs r5 r6 Hq5 Hk6 ltac:(vm_compute; reflexivity)).
  + rewrite F6. unfold lv, w64. apply Z_to_bv_bv_unsigned.
  + exact F13.
  + rewrite (cb_kept_bv r5 r6 _ 18%bv Hk6 ltac:(vm_compute; reflexivity)). exact E18.
  + rewrite (cb_kept_bv r5 r6 _ 20%bv Hk6 ltac:(vm_compute; reflexivity)). exact E20.
  + exact F23.
  + (* e62: type, size, the text, its NUL, the zeros of the memset *)
    unfold hw7b_e62. apply hm_bytes_app. split.
    { apply hw7b_le32_view; [lia | exact Fty]. }
    rewrite length_le32. change (Z.of_nat 4) with 4.
    apply hm_bytes_app. split.
    { apply hw7b_le32_view; [lia | exact Fsz]. }
    rewrite length_le32. change (Z.of_nat 4) with 4. replace (F + 0x210 + 4 + 4) with (F + 0x218) by lia.
    apply hm_bytes_app. split.
    { apply hm_bytes_aview. intros i Hi.
      rewrite KE2; [| lia | intros X; destruct G8; lia].
      rewrite HK5; [| lia | intros []].
      rewrite (Mcp (Z.of_nat i) ltac:(lia)).
      exact (proj1 (hm_bytes_aview rsegs (w_H W) m3 (F + 0x20) _) Hby3 i Hi). }
    rewrite <- EwL.
    apply hm_bytes_app. split.
    { apply hm_bytes_aview. intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
      change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Fnul. vm_compute. reflexivity. }
    cbn [length]. change (Z.of_nat 1) with 1.
    assert (Ez : zeros 104 = zeros (9 + length (hw7b_js chs p)) ++ zeros (95 - length (hw7b_js chs p)))
      by (rewrite <- zeros_app; f_equal; lia).
    pose proof He62 as He62'. rewrite Ez in He62'. apply hm_bytes_app in He62' as [_ Hz2].
    rewrite length_zeros in Hz2.
    replace (F + 0x210 + Z.of_nat (9 + length (hw7b_js chs p))) with (F + 0x218 + wL + 1) in Hz2 by lia.
    apply (hm_bytes_kept rsegs (w_H W) memc (w_H W) m6 _ _ Hz2). intros y Hy. rewrite length_zeros in Hy.
    rewrite KE2; [| lia | intros X; destruct G8; lia].
    apply Kz5'; [lia|]. apply w_nZ_mid. right. lia.
  + (* the frame's shadow at J *)
    unfold hd_fsh. rewrite hmu_sh_len. change (Z.of_nat 116) with 116. intros i Hi.
    destruct (hw7b_PG_PJ i Hi) as [P1 P2].
    assert (Hd : (4 <= i < 16 \/ 20 <= i < 23) \/ ~ (4 <= i < 16 \/ 20 <= i < 23)) by lia.
    destruct Hd as [Hin|Hout].
    * rewrite (Fsh i ltac:(lia)), (P1 Hin). reflexivity.
    * rewrite KE2; [| unfold SHADOW_OFF in *; lia | intros X; destruct G8; lia].
      rewrite Kz5'; [| unfold SHADOW_OFF in *; lia | apply w_nZ_sh; unfold kHighMemBeg, SHADOW_OFF in *; lia].
      rewrite (P2 Hout). unfold hd_fsh in Hfsh. rewrite hmu_sh_len in Hfsh. exact (Hfsh i ltac:(lia)).
  + (* the bytes the walk kept *)
    apply (hw7b_kept_trans W memc m5 m6 wZ1 _ _ Kz5 HK6). intros a Ha. cbv beta in *. unfold wZ1, hw7b_Z1 in Ha.
    rewrite HE in *. lia.
  + intros a Ha. exact (Hpr6 a (Hpr5 a (Mpr a (Hpr3 a (Hpr a (Pr a Ha)))))).
Qed.

(* ---- the walk ---- *)
Lemma w_walk : SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 HW7B_G) memc (seg_rom rsegs)) mdc) Q.
Proof using All.
pose proof (hw7b_geo_facts R F w_G) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (hw7b_param_len p) as Hpl. pose proof (hw7b_sep_len p) as Hsl. pose proof hw7b_hpfx_len as Hhl.
(* ======================== A1 ======================== *)
eapply SRr_bind.
{ exact (HA1 STK sp0 FP ly Sv W0 mem0 md0 own lyc Sc W memc mdc k regs p HJ H27 H26 Hp HRAtab). }
cbv beta. intros W1 c1 _ (-> & r1 & m1 & d1 & -> & HJ1 & Hio1 & Hk1 & HK1 & Hpr1 & R1a).
assert (Kz1 : wKz m1)
  by exact (w_kz_step memc m1 (fun _ => False) (hw7b_kept_refl W memc wZ1) HK1 (fun a h => match h with end)).
(* ======================== A2 ======================== *)
eapply SRr_bind.
{ apply (HA2 STK sp0 FP ly Sv W0 mem0 md0 own lyc Sc W m1 d1 k r1 p R (F + 0xa0) pa HJ1 R1a).
  - rewrite (cb_kept_bv regs r1 _ 27%bv Hk1 ltac:(vm_compute; reflexivity)). exact H27.
  - rewrite (cb_kept_bv regs r1 _ 26%bv Hk1 ltac:(vm_compute; reflexivity)). exact H26.
  - exact Hp.
  - rewrite (cb_kept_bv regs r1 _ 9%bv Hk1 ltac:(vm_compute; reflexivity)). exact H9.
  - lia.
  - lia.
  - exact w_R16.
  - rewrite (cb_kept_bv regs r1 _ 18%bv Hk1 ltac:(vm_compute; reflexivity)). exact H18.
  - lia.
  - apply (cb_val_kept (w_H W) memc m1 _ 8 pa); [|exact HPA].
    intros j Hj. change (Z.of_nat 8) with 8 in Hj. pose proof (Z.mod_pos_bound p 8 ltac:(lia)).
    apply HK1; [unfold HW7B_PTAB; lia | intros []].
  - lia.
  - apply (cb_ra_kept W memc m1 _ 8 HRA180); [lia|]. intros a Ha. apply HK1; [| intros []].
    pose proof (hw7b_hull_box (R + 0x180) 8 a ltac:(lia) ltac:(lia) Ha) as [B1 B2].
    assert ((R + 0x180 + 8) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
    unfold SHADOW_OFF in *. lia.
  - exact HPw. }
cbv beta. intros W2 c2 _ (-> & r2 & m2 & d2 & -> & HJ2 & Hio2 & Hk2 & HK2 & Hpr2 & (A1 & A10 & A23 & A18 & A21 & A26 & S0 & S1 & S2 & S3)).
assert (Kz2 : wKz m2).
{ apply (w_kz_step m1 m2 _ Kz1 HK2). intros a Ha. cbv beta in Ha. unfold wZ1, hw7b_Z1. right; left; exact Ha. }
assert (I0 : wI 0 [] HW7B_HPFX HPFX r2 m2 d2).
{ refine (conj HJ2 (conj _ (conj _ (conj _ (conj A1 (conj A10 (conj A23 (conj _ (conj _ (conj Kz2 (conj _ (conj _
    (conj (conj S1 (conj S2 S3)) (conj _ _)))))))))))))).
  - exact (same_io_trans _ _ _ Hio1 Hio2).
  - apply (hw7b_req_blk _ [1; 10; 11; 12; 18; 21; 23; 26]%bv regs r1 r2); [| exact Hk2 | vm_compute; reflexivity].
    apply (hw7b_req_blk _ [10; 11; 12]%bv regs regs r1); [intros z _; reflexivity | exact Hk1 | vm_compute; reflexivity].
  - rewrite A21. exact (cb_kept_bv regs r1 _ 6%bv Hk1 ltac:(vm_compute; reflexivity)).
  - exact A26.
  - rewrite A18. unfold w64. f_equal. lia.
  - intros a Ha. exact (Hpr2 a (Hpr1 a Ha)).
  - apply hm_bytes_aview. intros j Hj. cbn [length] in Hj. lia.
  - cbn [length]. lia.
  - apply w_part_img; [exact Hhpfx | unfold HW7B_HPFX; lia | lia]. }
(* ======================== the four turns ======================== *)
apply (wturnC 0 [] HW7B_HPFX HPFX r2 m2 d2 (F + 0xa0) chs ltac:(lia) I0).
{ intros m' (X1 & _ & _). replace (R + 0x180 + 8 * Z.of_nat 0) with (R + 0x180) by lia. exact X1. }
{ lia. }
{ exact w_part_ch. }
{ cbn [length]. lia. }
{ cbn [length]. lia. }
intros r3 m3 d3 I1.
apply (wturnC 1 ([] ++ HPFX) (F + 0xa0) chs r3 m3 d3 (hw7b_sep p) (hw7b_sepb p) ltac:(lia) I1).
{ intros m' (_ & X2 & _). replace (R + 0x180 + 8 * Z.of_nat 1) with (R + 0x188) by lia. exact X2. }
{ unfold hw7b_sep. destruct (Z.testbit p 7); lia. }
{ apply w_part_img; [exact Hsep | unfold hw7b_sep; destruct (Z.testbit p 7); lia | lia]. }
{ cbn [app]. lia. }
{ cbn [app]. lia. }
intros r4 m4 d4 I2.
apply (wturnC 2 (([] ++ HPFX) ++ chs) (hw7b_sep p) (hw7b_sepb p) r4 m4 d4 pa (hw7b_pab p) ltac:(lia) I2).
{ intros m' (_ & _ & X3). replace (R + 0x180 + 8 * Z.of_nat 2) with (R + 0x190) by lia. exact X3. }
{ lia. }
{ apply w_part_img; [exact Hpstr | lia | lia]. }
{ cbn [app]. rewrite length_app. lia. }
{ cbn [app]. rewrite length_app. lia. }
intros r5 m5 d5 I3.
apply (wlast _ r5 m5 d5 I3).
- cbn [app]. rewrite !length_app. lia.
- unfold hw7b_js. cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.
End w.

Lemma hw7b_core_L : hw7b_core_stmt B.
Proof.
intros STK sp0 FP ly Sv W0 mem0 md0 own lyc Sc W memc mdc k regs R F p chs pa vlen vcur vpp Q
  HJ H2 H9 H3 H4 HR32 HRs HSTK Hs47 Hs16 HRac HF32 HF4096 HFac HFapp HFw HFshw HPw
  H27 H26 Hp H25 H18 H19 Hfsh Hch Hchnz Hchl He62 Hhpfx Hsep HPA Hpstr Hpa HRAtab HRA180 Haro
  V118 V130 Ve8 V138 Hvlen V110 Hvcur V148 Hvpp K.
exact (w_walk STK sp0 FP ly Sv W0 mem0 md0 own lyc Sc W memc mdc k regs R F p chs pa vlen vcur vpp Q
  HJ H2 H9 H3 H4 HR32 HRs HSTK Hs47 Hs16 HRac HF32 HF4096 HFac HFapp HFw HFshw HPw
  H27 H26 Hp H25 H18 H19 Hfsh Hch Hchnz Hchl He62 Hhpfx Hsep HPA Hpstr Hpa HRAtab HRA180 Haro
  V118 V130 Ve8 V138 Hvlen V110 Hvcur V148 Hvpp K).
Qed.
End d.

(* the walk G -> J from the lane's part lemmas *)
Lemma hw7b_core : forall B, hw7b_A1_stmt B -> hw7b_A2_stmt B -> hw7b_C_stmt B -> hw7b_D_stmt B -> hw7b_E1_stmt B ->
hw7b_E2_stmt B -> hw7b_iter_stmt B -> hw7b_memcpy_at_stmt B -> hw7b_strok_cstr_stmt -> hw7b_strok_ch_stmt ->
hw7b_core_stmt B.
Proof. intros B A1 A2 C D E1 E2 IT MC SC SCH. exact (hw7b_core_L B A1 A2 C D E1 E2 IT MC SC SCH). Qed.
End b.

Print Assumptions hw7b_le32_view.
Print Assumptions hw7b_PG_PJ.
Print Assumptions hw7b_core.
