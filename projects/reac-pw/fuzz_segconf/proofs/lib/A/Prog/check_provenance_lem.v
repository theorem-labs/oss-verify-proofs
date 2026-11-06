(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of check_reply_answer's ASan walk (plugin-hostd/fuzz_command), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the walk's kit: regions, facts, register files, seed lemma cl_seed) over fuzz_command's listing (lib/A/Prog/CmdList.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_answer_k.v, with its module paths, module names and numbers changed; 313 of its 439 lines of code are new or changed and 303 lines of the source are left out. *)
(* The pieces of the ASan walk of check_provenance (fuzz_segconf image A, 0x872e0) that are not the run itself: the
   call rule of the strcmp wrapper in the journal form the walk uses, the byte bridges from the contract's reader
   forms (lib/A/Prog/SegABase.v) to the wrapper's (lib/A/Rt/RtDefs.v), the symbolic entry state and its seed lemma.
   The form is plugin-hostd/fuzz_command's lib/A/Prog/check_reply_answer_k.v at origin/ossv/recipes 501c0d516c69
   (acall_rule, acall_of_art, call_strcmp_of, cra_entry), over segconf's listing (lib/A/Prog/SegList.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaDenot PaSB PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegInstA PaArt PaNoChain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ reader and byte-list bridges ================================ *)
Lemma cpv_val_mem_of_sa : forall segs H (mem : word -> option byte) a n v,
sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate].
cbn in Hv. injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
try unfold YG0f.le_byte in *; try unfold YO0f.le_byte in *. rewrite <- Hv.
symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* SegABase's text at p (values in Z) is RtDefs' text of the bytes seg_spec.zb s (the base's sa_strz_bytes) *)
Lemma cpv_astr_of_strz : forall segs (W : world segs) mem p s,
  sa_strz (aview segs (w_H W) mem) p s -> astr_at segs W mem p (seg_spec.zb s).
Proof.
intros segs W mem p s HS. destruct (sa_strz_bytes segs (w_H W) mem p s HS) as (Hb & Hn & _).
split; [exact Hb | exact Hn].
Qed.

Lemma cpv_len_zb : forall l, astr_len (seg_spec.zb l) = Z.of_nat (length l).
Proof. intros l. unfold astr_len, seg_spec.zb. rewrite length_map. reflexivity. Qed.

(* SegModel.strcmp on the values of two NUL-free byte strings is 0 exactly when they are equal (the plain walk's
   lib/Prog/check_model.v bridge_strcmp, restated here over byte lists) *)
Lemma cpv_byte0 : forall b : byte, bv_unsigned b = 0 -> b = Z_to_bv 8 0.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.
Lemma cpv_bridge_strcmp : forall sx sy : list byte, ~ In (Z_to_bv 8 0) sx -> ~ In (Z_to_bv 8 0) sy ->
  SegModel.strcmp (seg_spec.zs sx) (seg_spec.zs sy) = 0 <-> sx = sy.
Proof.
unfold seg_spec.zs. induction sx as [|x sx IH]; intros [|y sy] NX NY; cbn [map SegModel.strcmp].
- split; intros; reflexivity.
- split; [|intros H; discriminate H]. intros H. exfalso. apply NY. cbn [In]. left. apply cpv_byte0. lia.
- split; [|intros H; discriminate H]. intros H. exfalso. apply NX. cbn [In]. left. apply cpv_byte0. exact H.
- assert (X0 : bv_unsigned x <> 0).
  { intros H. apply NX. cbn [In]. left. apply cpv_byte0. exact H. }
  assert (NX' : ~ In (Z_to_bv 8 0) sx) by (intros H; apply NX; cbn [In]; right; exact H).
  assert (NY' : ~ In (Z_to_bv 8 0) sy) by (intros H; apply NY; cbn [In]; right; exact H).
  destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E|E].
  + replace (bv_unsigned x =? 0) with false by (symmetry; apply Z.eqb_neq; exact X0).
    cbn [andb negb]. rewrite (IH sy NX' NY').
    assert (XY : x = y) by (apply bv_eq; exact E). subst y.
    split; [intros ->; reflexivity | intros H; injection H as H; exact H].
  + cbn [andb]. split; [intros H; lia | intros H; injection H as H1 H2; exfalso; apply E; rewrite H1; reflexivity].
Qed.

(* ======================================== sub-ranges ======================================== *)
Lemma cpv_ra_sub : forall rd q n q' n', range_addressable rd SHADOW_OFF q n -> q <= q' -> q' + n' <= q + n ->
  range_addressable rd SHADOW_OFF q' n'.
Proof. intros rd q n q' n' H H1 H2 x Hx. apply H. lia. Qed.
Lemma cpv_hull_sub : forall rd q n q' n', shadow_hull_vis rd q n -> q <= q' -> 0 < n' -> q' + n' <= q + n ->
  shadow_hull_vis rd q' n'.
Proof.
intros rd q n q' n' H H1 H0 H2 s Hs. apply H.
pose proof (shadow_mono q q' H1). pose proof (shadow_mono (q' + n' - 1) (q + n - 1) ltac:(lia)).
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ H3). pose proof (R8 _ _ H4). lia.
Qed.
Lemma cpv_mem_range_sub : forall q n q' n', amem_range q n -> q <= q' -> q' + n' <= q + n -> amem_range q' n'.
Proof. intros q n q' n' [H|[H H']] H1 H2; [left; lia | right; lia]. Qed.
Lemma cpv_addr_sub : forall rd q n q' n', sa_addr rd q n -> q <= q' -> 0 <= n' -> q' + n' <= q + n -> sa_addr rd q' n'.
Proof.
intros rd q n q' n' (Hq & Hn & Hm & Hra & Hhv) H1 H0 H2.
split; [lia|]. split; [lia|]. split; [exact (cpv_mem_range_sub q n q' n' Hm H1 H2)|].
split; [exact (cpv_ra_sub rd q n q' n' Hra H1 H2)|].
intros Hn'. apply (cpv_hull_sub rd q n q' n'); [apply Hhv; lia | lia | lia | lia].
Qed.

(* a reader-level read range is RtDefs' aread_ok once it lies outside the call's scratch window *)
Lemma cpv_aread_of_addr : forall segs (W : world segs) regs mem stk x n,
sa_addr (aview segs (w_H W) mem) x n -> 0 <= n < 2 ^ 32 ->
(forall a, x <= a < x + n -> aview segs (w_H W) mem a <> None) ->
(x + n <= spZ regs - stk \/ spZ regs <= x) ->
aread_ok segs stk W regs mem x n.
Proof.
intros segs W regs mem stk x n (Hq & Hn & Hm & Hra & Hhv) Hn32 Hrd Hout.
split; [lia|]. split; [lia|]. split; [lia|].
split; [intros a Ha; split; [exact (Hrd a Ha) | unfold ascratch_stk; lia]|].
split; [exact Hm|]. split; [exact Hra | exact Hhv].
Qed.

(* the bytes a word-at-a-time reader may touch after the NUL at e, from SegABase's sa_tail *)
Lemma cpv_tail_of_sa : forall segs (W : world segs) mem e, sa_tail (aview segs (w_H W) mem) e -> atail_vis segs W mem e.
Proof. intros segs W mem e H a Ha. exact (H a Ha). Qed.

(* ===================================== want's mseg entry ===================================== *)
Lemma cpv_nth_fld : forall {A : Type} (bs : list A) k n i d, (i < n)%nat -> nth i (firstn n (skipn k bs)) d = nth (k + i) bs d.
Proof.
intros A bs k. revert bs. induction k as [|k IH]; intros bs n i d Hi.
- cbn [skipn Nat.add]. revert bs i Hi. induction n as [|n IHn]; intros bs i Hi; [lia|].
  destruct bs as [|x bs]; [destruct i; reflexivity|]. destruct i as [|i]; [reflexivity|].
  cbn [firstn nth]. apply IHn. lia.
- destruct bs as [|x bs].
  + cbn [skipn]. assert (H0 : firstn n (@nil A) = []) by (destruct n; reflexivity). rewrite H0. destruct i; reflexivity.
  + cbn [skipn]. rewrite (IH bs n i d Hi). reflexivity.
Qed.

(* a flag word of the entry (seg_spec.flag_enc: 1 or 0 in four little-endian bytes) through the reader *)
Lemma cpv_flag_val : forall rd a bs off b, sa_bytes rd a bs -> 0 <= off -> (Z.to_nat off + 4 <= length bs)%nat ->
  seg_spec.flag_enc b (seg_spec.fldz off 4 bs) -> sa_val rd (a + off) 4 (if b then 1 else 0).
Proof.
intros rd a bs off b HB Ho Hl HF k Hk.
assert (Hn : nth k (seg_spec.fldz off 4 bs) ZB0 = nth (Z.to_nat off + k) bs ZB0).
{ unfold seg_spec.fldz, seg_spec.fld. change (Z.to_nat 4) with 4%nat. apply cpv_nth_fld. exact Hk. }
specialize (HB (Z.to_nat off + k)%nat ltac:(lia)).
replace (a + off + Z.of_nat k) with (a + Z.of_nat (Z.to_nat off + k)) by lia.
rewrite HB, <- Hn. unfold seg_spec.flag_enc in HF. rewrite HF. f_equal.
destruct b; do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.
Qed.

(* a char[cap] field of the entry holding s (seg_spec.cstr_enc): the C string s at its address *)
Lemma cpv_field_strz : forall rd a bs off (capn : nat) capz s, sa_bytes rd a bs -> 0 <= off -> Z.of_nat capn = capz ->
  (Z.to_nat off + capn <= length bs)%nat ->
  seg_spec.cstr_enc capn s (seg_spec.fldz off capz bs) -> sa_strz rd (a + off) s /\ (length s < capn)%nat.
Proof.
intros rd a bs off capn capz s HB Ho Hc Hl (Hfl & Hsl & Hn0 & Hfs).
split; [|exact Hsl]. split; [|exact Hn0].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
assert (Hfi : nth i (seg_spec.zs (seg_spec.fldz off capz bs)) 0 = nth i (s ++ [0]) 0).
{ rewrite <- Hfs. symmetry.
  pose proof (cpv_nth_fld (seg_spec.zs (seg_spec.fldz off capz bs)) 0 (S (length s)) i 0 ltac:(lia)) as Hq.
  cbn [skipn Nat.add] in Hq. exact Hq. }
assert (Hfn : nth i (seg_spec.zs (seg_spec.fldz off capz bs)) 0 = bv_unsigned (nth (Z.to_nat off + i) bs ZB0)).
{ unfold seg_spec.zs, seg_spec.fldz, seg_spec.fld.
  transitivity (nth i (map bv_unsigned (firstn (Z.to_nat capz) (skipn (Z.to_nat off) bs))) (bv_unsigned ZB0)); [reflexivity|].
  rewrite map_nth. f_equal. apply cpv_nth_fld. lia. }
specialize (HB (Z.to_nat off + i)%nat ltac:(lia)).
replace (a + off + Z.of_nat i) with (a + Z.of_nat (Z.to_nat off + i)) by lia.
rewrite HB, <- Hfn, Hfi. reflexivity.
Qed.

(* the bytes after a text inside the entry, up to the next 8-byte boundary, are bytes of the entry (want mod 4 = 0
   and the text ends by want + 251) *)
Lemma cpv_tail_in : forall rd a bs e, sa_bytes rd a bs -> length bs = 256%nat -> a mod 4 = 0 -> a <= e <= a + 251 ->
  sa_tail rd e.
Proof.
intros rd a bs e HB Hl Ha He x Hx.
assert (Hx2 : a <= x < a + 256).
{ pose proof (Z.mod_pos_bound e 8 ltac:(lia)). pose proof (Z.div_mod e 8 ltac:(lia)).
  pose proof (Z.div_mod a 4 ltac:(lia)). lia. }
specialize (HB (Z.to_nat (x - a)) ltac:(rewrite Hl; lia)).
rewrite Z2Nat.id in HB by lia. replace (a + (x - a)) with x in HB by lia. rewrite HB. discriminate.
Qed.

(* ============================ transport across a call or a run ============================ *)
(* A call or a run of this walk changes no byte below its own window: every object the contract names (want's
   mseg entry, the two texts, their shadow bytes) reads the same afterwards. L is the bottom of the window. *)
Definition cpv_agree (rd rd' : reader) (L : Z) : Prop := forall a, 0 <= a < L -> rd' a = rd a.
Lemma cpv_keep_bytes : forall rd rd' L a bs, cpv_agree rd rd' L -> 0 <= a -> a + Z.of_nat (length bs) <= L ->
  sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' L a bs HK Ha Hl H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma cpv_keep_zs : forall rd rd' L a l, cpv_agree rd rd' L -> 0 <= a -> a + Z.of_nat (length l) <= L ->
  sa_zs rd a l -> sa_zs rd' a l.
Proof. intros rd rd' L a l HK Ha Hl H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma cpv_keep_strz : forall rd rd' L p s, cpv_agree rd rd' L -> 0 <= p -> p + Z.of_nat (length s) + 1 <= L ->
  sa_strz rd p s -> sa_strz rd' p s.
Proof.
intros rd rd' L p s HK Hp Hl [Hz Hn]. split; [|exact Hn].
apply (cpv_keep_zs rd rd' L p _ HK Hp); [rewrite length_app; cbn [length]; lia | exact Hz].
Qed.
(* the tail reads only up to the next 8-byte boundary after e, so an 8-aligned bound L above e carries it *)
Lemma cpv_keep_tail : forall rd rd' L e, cpv_agree rd rd' L -> 0 <= e -> e < L -> L mod 8 = 0 ->
  sa_tail rd e -> sa_tail rd' e.
Proof.
intros rd rd' L e HK He Hl H8 H x Hx.
pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Hm. pose proof (Z.div_mod e 8 ltac:(lia)) as Hd.
pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as HmL. pose proof (Z.div_mod L 8 ltac:(lia)) as HdL.
rewrite HK by lia. exact (H x Hx).
Qed.
Lemma cpv_keep_str : forall rd rd' L p s, cpv_agree rd rd' L -> 0 <= p -> p + Z.of_nat (length s) + 8 <= L ->
  L mod 8 = 0 -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' L p s HK Hp Hl H8 [Hz Ht]. split.
- apply (cpv_keep_strz rd rd' L p s HK Hp ltac:(lia) Hz).
- apply (cpv_keep_tail rd rd' L (p + Z.of_nat (length s)) HK ltac:(lia) ltac:(lia) ltac:(assumption) Ht).
Qed.
(* the shadow bytes of a range below 2 ^ 47 lie below SHADOW_OFF + 2 ^ 44 + 8 *)
Lemma cpv_keep_addr : forall rd rd' L q n, cpv_agree rd rd' L -> 0 <= q -> 0 <= n -> q + n <= 2 ^ 47 ->
  SHADOW_OFF + 2 ^ 44 + 8 <= L -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros rd rd' L q n HK Hq Hn Hq47 HL (H1 & H2 & H3 & H4 & H5).
assert (Hsh : forall x, 0 <= x <= q + n -> 0 <= shadow_addr x /\ shadow_addr x + 8 <= L).
{ intros x Hx. unfold shadow_addr, SHADOW_OFF in *.
  pose proof (Z.div_le_mono x (2 ^ 47) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  change (2 ^ 47 / 8) with (2 ^ 44) in *. lia. }
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split.
- intros x Hx. destruct (H4 x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  unfold shadow_of_addr. rewrite HK; [exact Hsv|].
  destruct (Hsh x ltac:(lia)). unfold shadow_addr, SHADOW_OFF in *. lia.
- intros Hn0 x Hx. rewrite HK; [exact (H5 Hn0 x Hx)|].
  destruct (Hsh q ltac:(lia)) as [Hq8 Hq8L]. destruct (Hsh (q + n - 1) ltac:(lia)) as [Hqn8 Hqn8L].
  assert (R8 : forall u, 0 <= u -> 0 <= u / 8 * 8 <= u)
    by (intros u Hu; pose proof (Z.div_mod u 8 ltac:(lia)); pose proof (Z.mod_pos_bound u 8 ltac:(lia)); lia).
  pose proof (R8 (shadow_addr q) ltac:(lia)). pose proof (R8 (shadow_addr (q + n - 1)) ltac:(lia)).
  lia.
Qed.

(* ============================= the flag mask the two tests form ============================= *)
(* `seqz a3,a2; addi a3,a3,-1; and a3,a3,a1`: the field address under a set flag, 0 under a clear one. *)
Lemma cpv_land_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.land (2 ^ 64 - 1) x = x.
Proof.
intros x Hx. change (2 ^ 64 - 1) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
apply Z.mod_small. lia.
Qed.
Lemma cpv_mask1 : forall E n v m w c, ew E n = Z_to_bv 64 v -> v = 1 -> ew E m = Z_to_bv 64 w ->
  0 <= w -> 0 <= c -> 0 <= w + c < 2 ^ 64 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SOff n 0) (SLit 1)) (SLit (-1))) (SOff m c)) = w + c.
Proof.
intros E n v m w c Hn Hv Hm Hw Hc Hwc. subst v.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
rewrite (U_atom E n 1 Hn) by lia. rewrite (U_atom_off E m w c Hm) by lia.
rewrite (zcanon_id 1) by (unfold M64; lia).
replace (1 <? 1) with false by reflexivity. cbv iota.
rewrite Z.add_0_l.
replace (zcanon (zcanon (-1))) with (2 ^ 64 - 1) by reflexivity.
rewrite cpv_land_ones64 by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma cpv_mask0 : forall E n v m w c, ew E n = Z_to_bv 64 v -> v = 0 -> ew E m = Z_to_bv 64 w ->
  0 <= w -> 0 <= c -> 0 <= w + c < 2 ^ 64 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SOff n 0) (SLit 1)) (SLit (-1))) (SOff m c)) = 0.
Proof.
intros E n v m w c Hn Hv Hm Hw Hc Hwc. subst v.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
rewrite (U_atom E n 0 Hn) by lia. rewrite (U_atom_off E m w c Hm) by lia.
rewrite (zcanon_id 1) by (unfold M64; lia).
replace (0 <? 1) with true by reflexivity. cbv iota.
replace (zcanon (1 + zcanon (-1))) with 0 by reflexivity.
rewrite Z.land_0_l. reflexivity.
Qed.

(* a region kept by a step that changes no byte of it and leaves its writable window present (fuzz_command
   check_reply_answer_k.v region_kept_win) *)
Lemma cpv_region_kept_win : forall segs E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview segs H m2 a = aview segs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
region_kept segs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros segs E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav. exact Ha.
- intros _. apply (apresent_writable segs). apply Hp. exact Ha.
Qed.

(* ====================================== the symbolic state ====================================== *)
(* The walk's stack need is SegInstA's STK_check_provenance = 32 + 2 * ESTACK: its own frame (addi sp,sp,-32 at
   0x872e0) and, below it, the strcmp wrapper's window (RtString.astrcmp_realizes asks ecall_pre_stk (2 * ESTACK)
   at the call, sp = entry sp - 32). *)
(* Atoms (fuzz_command check_reply_answer_k.v's shape): 0..31 the registers at entry (12 = a2 = want); 32 the shadow
   base SB; 33 the word want->role_set (want + 0x14); 34 the word want->ignore_set (want + 0x1c); A_OBJ 0 the
   shadow-base GOT word, A_OBJ 12 the shadow-base cell (the listing's objects). *)
Definition CPV_WHI : Z := 0x7fffff800000 - 256.
Definition Bxp : sv := SOff 32 0.
Definition CPspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition cpv_want : YP09.region :=
YP09.mkRegion (Some 12%nat) 20 32 0 0 [YP09.mkChunk 20 (CVal 4 (SOff 33 0)); YP09.mkChunk 28 (CVal 4 (SOff 34 0))].
Definition cpv_regions : smem := [stack_region 32; got_regionP; bcell_regionP 32; cpv_want].
Definition cpv_facts : facts :=
mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (12%nat, mkAF 4096 CPV_WHI 2); (32%nat, mkAF SB SB 0);
(33%nat, mkAF 0 1 0); (34%nat, mkAF 0 1 0)] [] [].
Definition ss_cpv : sstate := mkSS AF_check_provenance sr_atoms cpv_regions None cpv_facts.
Definition cpv_extra (rs is : Z) : list word := map (Z_to_bv 64) [SB; rs; is].


Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ======================================= the call rule ======================================= *)
Section p.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variables RLO RHI : Z.

(* The call of a runtime entry at pc with window stk, entry premise P and post Q, in the journal form a walk applies
   (fuzz_command check_reply_answer_k.v acall_rule). *)
Definition cpv_acall_rule (pc stk : Z) (P : world SEGS -> bvmap 5 word -> (word -> option byte) -> Prop)
(Q : bvmap 5 word -> (word -> option byte) -> Prop) : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
arodata_okP SEGS RLO RHI B (rdW W memT) ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> stk - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
P W regsT memT ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\ Q regs2 mem2 /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> rdW W mem2 a = rdW W memT a)).
(* the strcmp wrapper's premises (lib/A/Rt/RtString.v astrcmp_realizes) without the read-only view *)
Definition cpv_P_strcmp (x y : Z) (sx sy : list byte) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
getr regs 10 = w64 x /\ getr regs 11 = w64 y /\ 0 < x /\ 0 < y /\
astr_at SEGS W mem x sx /\ astr_at SEGS W mem y sy /\
aread_ok SEGS (2 * ESTACK) W regs mem x (astr_len sx + 1) /\ aread_ok SEGS (2 * ESTACK) W regs mem y (astr_len sy + 1) /\
atail_vis SEGS W mem (x + astr_len sx) /\ atail_vis SEGS W mem (y + astr_len sy).
Definition CPV_CALL_STRCMP : Prop := forall x y sx sy,
cpv_acall_rule (SIGMA SS___interceptor_trampoline_strcmp) (2 * ESTACK) (cpv_P_strcmp x y sx sy)
(fun regs' _ => getr regs' 10 = w64 0 <-> sx = sy).

(* the read-only view the wrapper asks, carried across a call or a run of this walk *)
Lemma cpv_keep_aro : forall rd rd' L rlo rhi, cpv_agree rd rd' L ->
  (forall a, in_roP SEGS rlo rhi a -> 0 <= a < L) -> arodata_okP SEGS rlo rhi B rd -> arodata_okP SEGS rlo rhi B rd'.
Proof using. intros rd rd' L rlo rhi HK HB0 H a Hro Ho He. rewrite HK by exact (HB0 a Hro). exact (H a Hro Ho He). Qed.

(* the strcmp row's premises from the contract's reader forms *)
Lemma cpv_P_of : forall (W : world SEGS) mem (regs : bvmap 5 word) x y sx sy,
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
  sa_strz (rdW W mem) x sx -> sa_tail (rdW W mem) (x + Z.of_nat (length sx)) ->
  sa_addr (rdW W mem) x (Z.of_nat (length sx) + 1) -> Z.of_nat (length sx) + 1 < 2 ^ 32 ->
  x + Z.of_nat (length sx) + 1 <= spZ regs - 2 * ESTACK ->
  sa_strz (rdW W mem) y sy -> sa_tail (rdW W mem) (y + Z.of_nat (length sy)) ->
  sa_addr (rdW W mem) y (Z.of_nat (length sy) + 1) -> Z.of_nat (length sy) + 1 < 2 ^ 32 ->
  y + Z.of_nat (length sy) + 1 <= spZ regs - 2 * ESTACK ->
  cpv_P_strcmp x y (seg_spec.zb sx) (seg_spec.zb sy) W regs mem.
Proof using.
intros W mem regs x y sx sy H10 H11 Hx Hy SX TX AX R32x Wx SY TY AY R32y Wy.
assert (RDx : forall a, x <= a < x + (Z.of_nat (length sx) + 1) -> aview SEGS (w_H W) mem a <> None).
{ intros a Ha. destruct SX as [Hz _].
  specialize (Hz (Z.to_nat (a - x)) ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite Z2Nat.id in Hz by lia. replace (x + (a - x)) with a in Hz by lia. rewrite Hz. discriminate. }
assert (RDy : forall a, y <= a < y + (Z.of_nat (length sy) + 1) -> aview SEGS (w_H W) mem a <> None).
{ intros a Ha. destruct SY as [Hz _].
  specialize (Hz (Z.to_nat (a - y)) ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite Z2Nat.id in Hz by lia. replace (y + (a - y)) with a in Hz by lia. rewrite Hz. discriminate. }
unfold cpv_P_strcmp.
split; [exact H10|]. split; [exact H11|]. split; [exact Hx|]. split; [exact Hy|].
split; [exact (cpv_astr_of_strz SEGS W mem x sx SX)|].
split; [exact (cpv_astr_of_strz SEGS W mem y sy SY)|].
split.
{ rewrite cpv_len_zb. apply (cpv_aread_of_addr SEGS W regs mem (2 * ESTACK) x (Z.of_nat (length sx) + 1));
  [exact AX | lia | exact RDx | left; lia]. }
split.
{ rewrite cpv_len_zb. apply (cpv_aread_of_addr SEGS W regs mem (2 * ESTACK) y (Z.of_nat (length sy) + 1));
  [exact AY | lia | exact RDy | left; lia]. }
split; rewrite cpv_len_zb; apply cpv_tail_of_sa; assumption.
Qed.

Section q.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.

Lemma cpv_rt_rom_view_of_aro : forall (W : world SEGS) mem, arodata_okP SEGS RLO RHI B (rdW W mem) -> rt_rom_view SEGS B W mem.
Proof using. intros W mem HR a Hrom Ho He. apply HR; [left; exact Hrom | exact Ho | exact He]. Qed.
Lemma cpv_acall_of_art : forall pc stk P Q, ESTACK <= stk ->
(forall ly S W regs mem md, ecall_pre_stk SEGS B stk ly S W regs mem md -> P W regs mem -> rt_rom_view SEGS B W mem ->
 SRr SEGS W (cfg_at SEGS pc regs mem md) (art_post SEGS B stk ly S W regs mem md (fun _ => False) Q)) ->
cpv_acall_rule pc stk P Q.
Proof using LAWS TL.
intros pc stk P Q Hes AE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw HJ HRO Hsp Hal Hneg Hbud Hgp Htp Hra Hraw HP.
assert (HPS : ecall_pre_stk SEGS B stk lyc Sc W regsT memT mdc)
by (apply (ecall_pre_stk_at SEGS B stk STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg Hes Hbud);
    [rewrite Hra; exact Hraw | exact Hgp | exact Htp]).
assert (Hst : 0 <= stk) by (unfold ESTACK in Hes; lia).
eapply SRr_mono.
{ exact (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) stk (fun _ => False) pc W regsT memT STK sp0 FP ly S W0 mem md own
  lyc Sc mdc k o raw Q HJ Hsp Hal Hneg Hst Hbud Hra (fun a (H : False) => match H with end)
  (AE lyc Sc W regsT memT mdc HPS HP (cpv_rt_rom_view_of_aro W memT HRO))). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ & HK).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split; [exact HQ|]. intros a Ha Hn. exact (HK a Ha Hn (fun H => H)).
Qed.
Lemma cpv_call_strcmp_of : astrcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_strcmp) -> CPV_CALL_STRCMP.
Proof using LAWS TL.
intros AS x y sx sy. apply cpv_acall_of_art; [unfold ESTACK; lia|].
intros ly S W regs mem md HPS (H10 & H11 & Hx & Hy & Hsx & Hsy & Rx & Ry & Tx & Ty) HRV.
exact (AS ly S W regs mem md x y sx sy HPS H10 H11 Hx Hy Hsx Hsy Rx Ry Tx Ty HRV).
Qed.
End q.
End p.
Section e.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.

(* a live heap block lies above 4096 and below the allocator ceiling, so below this call's stack window *)
Lemma cpv_heap_bounds : forall ly S (W : world SEGS) mem md q n,
  AR SEGS B ly S W mem md -> sa_heap B ly S q n -> 0 <= n -> 4096 <= q /\ q + n <= alloc_ceiling.
Proof using LAWS.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hq) Hn.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hc & _).
assert (Hr : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
Qed.

Lemma cpv_entry : forall W ly S regs mem md want rs is,
afn_pre_na SEGS B STK_check_provenance ly S W regs mem md ->
getr regs 12 = w64 want -> 4096 <= want -> want + 256 <= alloc_ceiling -> want mod 4 = 0 ->
(want + 32 <= 0x10000 \/ 0x601000 <= want) ->
sa_val (rdW W mem) (want + 20) 4 rs -> 0 <= rs <= 1 ->
sa_val (rdW W mem) (want + 28) 4 is -> 0 <= is <= 1 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cpv_extra rs is))) ss_cpv
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_provenance)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bxp [] (Eimg (Ereg regs (cpv_extra rs is))) (mrestrict (w_H W) mem).
Proof using LAWS TL.
intros W ly S regs mem md want rs is HPRE H12 Hw Hwc Hw4 Hoff Hrs Rrs His Ris.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_check_provenance = 8224) by reflexivity.
pose proof (pa_obj_img 0 ltac:(lia)) as O0. pose proof (pa_obj_img 12 ltac:(lia)) as O12.
pose proof (pal_got_cell B TL) as Ogc. unfold kImgEnd in O0, O12.
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (cpv_extra rs is))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E12 : ew E 12 = Z_to_bv 64 want)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 rs) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 is) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_cpv. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cpv_regions, stack_region, got_regionP, bcell_regionP, cpv_want.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) _ E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) _ E253) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 12%nat want E12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ want 20 4 (SOff 33 0) rs);
           [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact (cpv_val_mem_of_sa SEGS (w_H W) mem _ _ _ Hrs).
      -- apply (chunk_ok_val SEGS E _ want 28 4 (SOff 34 0) is);
           [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact (cpv_val_mem_of_sa SEGS (w_H W) mem _ _ _ His).
  + apply pairwise_disjoint_of_extents.
    unfold cpv_regions, stack_region, got_regionP, bcell_regionP, cpv_want, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) _ E241), (VB (A_OBJ 12) _ E253), (VB 12%nat want E12) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 HSTK Hstk0 Hw Hwc Hoff O0 O12 Ogc. clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cpv_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E12, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB, CPV_WHI.
    revert Hslo Hshi H47 Hceil Hal16 C1 HSTK Hstk0 Hw Hwc Hw4 Rrs Ris. clear. unfold spZ. intros.
    repeat match goal with |- _ /\ _ => split end; try lia; reflexivity.
- unfold sh_ok. constructor.
Qed.
End e.
End k.
