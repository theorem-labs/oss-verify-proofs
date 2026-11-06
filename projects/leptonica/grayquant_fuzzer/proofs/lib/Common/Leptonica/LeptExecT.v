(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit SeqExec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptExec LeptExecW.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ExecT.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout}.
Context {PINS : LeptPins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma exT_blk_below : forall C A m md (p n : Z) (x : word), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n -> 0 <= p -> p + n < 2 ^ 64 -> 0 < n ->
  p <= u x < p + n -> u x < c_top C - LSTK.
Proof.
  intros C A m md p n x CK HW L Hp Hpn Hn Hx.
  destruct (blk_range C A m md (Z_to_bv 64 p) n CK HW L Hn) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia.
  destruct CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val. lia.
Qed.

(* [comment removed for export] *)
Lemma exT_blk_top32 : forall C A m md (p : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some 24 -> 0 <= p < 2 ^ 64 ->
  4096 <= p /\ p + 32 <= alloc_top (c_vm C).
Proof.
  intros C A m md p CK HW L Rp.
  destruct (blk_range C A m md (Z_to_bv 64 p) 24 CK HW L ltac:(lia)) as [G1 _]. rewrite u_Z2bv in G1 by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) L) as (_ & _ & TOP & _).
  destruct (w_vm _ _ _ _ HW) as (_ & E & _). rewrite E in TOP. rewrite u_Z2bv in TOP by lia.
  unfold round16 in TOP. change ((24 + 15) / 16) with 2 in TOP. lia.
Qed.

(* [comment removed for export] *)
Lemma exT_livk_at : forall A (M M' : word -> option byte) (p k : Z) (x : word), LIVK A M M' ->
  live A (Z_to_bv 64 p) = Some k -> 0 <= p -> p + k <= 2 ^ 64 -> p <= u x < p + k -> M' x = M x.
Proof.
  intros A M M' p k x L Lp G0 TP Hx.
  pose proof (L (Z_to_bv 64 p) k (u x - p) Lp ltac:(lia)) as E.
  replace (at_ (Z_to_bv 64 p) (u x - p)) with x in E by (unfold at_; apply bv_eq; rewrite !u_Z2bv; rewrite ?u_Z2bv; pose proof (u64_range x); lia).
  exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exT_pix_sess : forall C A (m M : word -> option byte) md (s F p : Z) (v : pixv), Cok C -> W C A m md -> c_top C - LSTK <= s - F ->
  live A (Z_to_bv 64 p) = Some 64 -> PIXat m p v -> (forall x : word, ~ (s - F <= u x < s) -> M x = m x) -> PIXat M p v.
Proof.
  intros C A m M md s F p v CK HW Hlo L PX FR. pose proof PX as (Hp0 & Hp64 & _).
  apply (PIXat_frame m); [exact PX|]. intros x Hx. apply FR.
  pose proof (exT_blk_below C A m md p 64 x CK HW L Hp0 Hp64 ltac:(lia) Hx). lia.
Qed.
Lemma exT_cmap_sess : forall C A (m M : word -> option byte) md (s F c : Z) (v : cmapv), Cok C -> W C A m md -> c_top C - LSTK <= s - F ->
  live A (Z_to_bv 64 c) = Some 24 -> CMAPat m c v -> (forall x : word, ~ (s - F <= u x < s) -> M x = m x) -> CMAPat M c v.
Proof.
  intros C A m M md s F c v CK HW Hlo L PX FR. pose proof PX as (Hp0 & Hp64 & _).
  apply (CMAPat_frame m); [exact PX|]. intros x Hx. apply FR.
  pose proof (exT_blk_below C A m md c 24 x CK HW L Hp0 ltac:(lia) ltac:(lia) Hx). lia.
Qed.
(* [comment removed for export] *)
Lemma exT_blk_sess : forall C A (m M : word -> option byte) md (s F p n : Z) (x : word), Cok C -> W C A m md -> c_top C - LSTK <= s - F ->
  live A (Z_to_bv 64 p) = Some n -> 0 <= p -> p + n < 2 ^ 64 -> 0 < n -> (forall x : word, ~ (s - F <= u x < s) -> M x = m x) ->
  p <= u x < p + n -> M x = m x.
Proof.
  intros C A m M md s F p n x CK HW Hlo L Hp Hpn Hn FR Hx. apply FR.
  pose proof (exT_blk_below C A m md p n x CK HW L Hp Hpn Hn Hx). lia.
Qed.

(* [comment removed for export] *)
Lemma exT_livk_sess : forall C A (m M : word -> option byte) md (s F : Z), Cok C -> W C A m md -> c_top C - LSTK <= s - F ->
  (forall x : word, ~ (s - F <= u x < s) -> M x = m x) -> LIVK A m M.
Proof.
  intros C A m M md s F CK HW Hlo FR q k i L Hi. apply FR.
  pose proof (u64_range q) as Rq.
  destruct (blk_range C A m md q k CK HW L ltac:(lia)) as [G1 G2].
  destruct CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  unfold at_. rewrite u_Z2bv by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma exT_kept_in : forall E (M M' : word -> option byte) (rb : expr) (b rlo rhi lo hi : Z),
  (forall a : word, lo <= u a < hi -> M' a = M a) -> edenot E rb = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 ->
  lo <= b + rlo -> b + rhi <= hi -> ex_region_kept E M M' (rb, rlo, rhi).
Proof.
  intros E M M' rb b rlo rhi lo hi IN He Rb H1 H2. cbn [ex_region_kept]. rewrite He, u_Z2bv by lia. intros x Hx. apply IN. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exT_pix_livk : forall A (M m' : word -> option byte) (p : Z) (v : pixv), PIXat M p v -> LIVK A M m' -> live A (Z_to_bv 64 p) = Some 64 -> PIXat m' p v.
Proof.
  intros A M m' p v PX LK L. pose proof PX as (Hp0 & Hp64 & _).
  apply (PIXat_frame M); [exact PX|]. intros x Hx. exact (exT_livk_at A M m' p 64 x LK L Hp0 ltac:(lia) Hx).
Qed.
Lemma exT_cmap_livk : forall A (M m' : word -> option byte) (c : Z) (v : cmapv), CMAPat M c v -> LIVK A M m' -> live A (Z_to_bv 64 c) = Some 24 -> CMAPat m' c v.
Proof.
  intros A M m' c v PX LK L. pose proof PX as (Hp0 & Hp64 & _).
  apply (CMAPat_frame M); [exact PX|]. intros x Hx. exact (exT_livk_at A M m' c 24 x LK L Hp0 ltac:(lia) Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exT_pix_frm : forall C A (M m' : word -> option byte) md (p q n lo hi : Z) (v : pixv), Cok C -> W C A M md ->
  live A (Z_to_bv 64 p) = Some 64 -> live A (Z_to_bv 64 q) = Some n -> Z_to_bv 64 p <> Z_to_bv 64 q -> 0 <= q < 2 ^ 64 -> 0 <= n -> q <= lo -> hi <= q + n ->
  PIXat M p v -> (forall x : word, ~ (lo <= u x < hi) -> m' x = M x) -> PIXat m' p v.
Proof.
  intros C A M m' md p q n lo hi v CK HW Lp Lq NE Rq Hn Hlo Hhi PX FR. pose proof PX as (Hp0 & Hp64 & _).
  pose proof (exW_blk_apart C A M md p q 64 n CK HW Lp Lq ltac:(intros ->; apply NE; reflexivity) ltac:(lia) Rq ltac:(lia) ltac:(lia)) as AP.
  apply (PIXat_frame M); [exact PX|]. intros x Hx. apply FR. lia.
Qed.
Lemma exT_cmap_frm : forall C A (M m' : word -> option byte) md (c q n lo hi : Z) (v : cmapv), Cok C -> W C A M md ->
  live A (Z_to_bv 64 c) = Some 24 -> live A (Z_to_bv 64 q) = Some n -> Z_to_bv 64 c <> Z_to_bv 64 q -> 0 <= q < 2 ^ 64 -> 0 <= n -> q <= lo -> hi <= q + n ->
  CMAPat M c v -> (forall x : word, ~ (lo <= u x < hi) -> m' x = M x) -> CMAPat m' c v.
Proof.
  intros C A M m' md c q n lo hi v CK HW Lp Lq NE Rq Hn Hlo Hhi PX FR. pose proof PX as (Hp0 & Hp64 & _).
  pose proof (exW_blk_apart C A M md c q 24 n CK HW Lp Lq ltac:(intros ->; apply NE; reflexivity) ltac:(lia) Rq ltac:(lia) ltac:(lia)) as AP.
  apply (CMAPat_frame M); [exact PX|]. intros x Hx. apply FR. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exT_pix_patch : forall C Aw A (M m' : word -> option byte) md (p q n a : Z) (bs : list byte) (v : pixv), Cok C -> W C Aw M md ->
  live Aw (Z_to_bv 64 p) = Some 64 -> live Aw (Z_to_bv 64 q) = Some n -> Z_to_bv 64 p <> Z_to_bv 64 q -> 0 <= q < 2 ^ 64 -> 0 < n ->
  q <= a -> a + Z.of_nat (length bs) <= q + n ->
  PIXat M p v -> LIVK A (wbytes M (Z_to_bv 64 a) bs) m' -> live A (Z_to_bv 64 p) = Some 64 -> PIXat m' p v.
Proof.
  intros C Aw A M m' md p q n a bs v CK HW Lp Lq NE Rq Hn Ha Hb PX LK L. pose proof PX as (Hp0 & Hp64 & _).
  destruct (blk_range C Aw M md (Z_to_bv 64 q) n CK HW Lq Hn) as [Gq1 Gq2]. rewrite u_Z2bv in Gq1, Gq2 by lia. pose proof (alloc_top_lt (c_vm C)) as ATL0. unfold two_pow_64 in ATL0.
  pose proof (exW_blk_apart C Aw M md p q 64 n CK HW Lp Lq ltac:(intros ->; apply NE; reflexivity) ltac:(lia) Rq ltac:(lia) ltac:(lia)) as AP.
  apply (PIXat_frame M); [exact PX|]. intros x Hx.
  rewrite (exT_livk_at A _ m' p 64 x LK L Hp0 ltac:(lia) Hx). apply MemSplit.wbytes_outside; rewrite u_Z2bv by lia; lia.
Qed.
Lemma exT_cmap_patch : forall C Aw A (M m' : word -> option byte) md (c q n a : Z) (bs : list byte) (v : cmapv), Cok C -> W C Aw M md ->
  live Aw (Z_to_bv 64 c) = Some 24 -> live Aw (Z_to_bv 64 q) = Some n -> Z_to_bv 64 c <> Z_to_bv 64 q -> 0 <= q < 2 ^ 64 -> 0 < n ->
  q <= a -> a + Z.of_nat (length bs) <= q + n ->
  CMAPat M c v -> LIVK A (wbytes M (Z_to_bv 64 a) bs) m' -> live A (Z_to_bv 64 c) = Some 24 -> CMAPat m' c v.
Proof.
  intros C Aw A M m' md c q n a bs v CK HW Lp Lq NE Rq Hn Ha Hb PX LK L. pose proof PX as (Hp0 & Hp64 & _).
  destruct (blk_range C Aw M md (Z_to_bv 64 q) n CK HW Lq Hn) as [Gq1 Gq2]. rewrite u_Z2bv in Gq1, Gq2 by lia. pose proof (alloc_top_lt (c_vm C)) as ATL0. unfold two_pow_64 in ATL0.
  pose proof (exW_blk_apart C Aw M md c q 24 n CK HW Lp Lq ltac:(intros ->; apply NE; reflexivity) ltac:(lia) Rq ltac:(lia) ltac:(lia)) as AP.
  apply (CMAPat_frame M); [exact PX|]. intros x Hx.
  rewrite (exT_livk_at A _ m' c 24 x LK L Hp0 ltac:(lia) Hx). apply MemSplit.wbytes_outside; rewrite u_Z2bv by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma exT_pix_patch2 : forall C Aw A (M m' : word -> option byte) md (p q n a pp : Z) (bs bs2 : list byte) (v : pixv), Cok C -> W C Aw M md ->
  live Aw (Z_to_bv 64 p) = Some 64 -> live Aw (Z_to_bv 64 q) = Some n -> Z_to_bv 64 p <> Z_to_bv 64 q -> 0 <= q < 2 ^ 64 -> 0 < n ->
  q <= a -> a + Z.of_nat (length bs) <= q + n -> c_top C - LSTK <= pp -> pp + Z.of_nat (length bs2) <= c_top C ->
  PIXat M p v -> LIVK A (wbytes (wbytes M (Z_to_bv 64 a) bs) (Z_to_bv 64 pp) bs2) m' -> live A (Z_to_bv 64 p) = Some 64 -> PIXat m' p v.
Proof.
  intros C Aw A M m' md p q n a pp bs bs2 v CK HW Lp Lq NE Rq Hn Ha Hb Hpp Hpp2 PX LK L. pose proof PX as (Hp0 & Hp64 & _).
  destruct (blk_range C Aw M md (Z_to_bv 64 q) n CK HW Lq Hn) as [Gq1 Gq2]. rewrite u_Z2bv in Gq1, Gq2 by lia.
  pose proof (exW_blk_apart C Aw M md p q 64 n CK HW Lp Lq ltac:(intros ->; apply NE; reflexivity) ltac:(lia) Rq ltac:(lia) ltac:(lia)) as AP.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as LV. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  apply (PIXat_frame M); [exact PX|]. intros x Hx.
  pose proof (exT_blk_below C Aw M md p 64 x CK HW Lp Hp0 Hp64 ltac:(lia) Hx) as BL.
  rewrite (exT_livk_at A _ m' p 64 x LK L Hp0 ltac:(lia) Hx).
  rewrite MemSplit.wbytes_outside by (rewrite u_Z2bv by lia; lia). apply MemSplit.wbytes_outside; rewrite u_Z2bv by lia; lia.
Qed.
Lemma exT_cmap_patch2 : forall C Aw A (M m' : word -> option byte) md (c q n a pp : Z) (bs bs2 : list byte) (v : cmapv), Cok C -> W C Aw M md ->
  live Aw (Z_to_bv 64 c) = Some 24 -> live Aw (Z_to_bv 64 q) = Some n -> Z_to_bv 64 c <> Z_to_bv 64 q -> 0 <= q < 2 ^ 64 -> 0 < n ->
  q <= a -> a + Z.of_nat (length bs) <= q + n -> c_top C - LSTK <= pp -> pp + Z.of_nat (length bs2) <= c_top C ->
  CMAPat M c v -> LIVK A (wbytes (wbytes M (Z_to_bv 64 a) bs) (Z_to_bv 64 pp) bs2) m' -> live A (Z_to_bv 64 c) = Some 24 -> CMAPat m' c v.
Proof.
  intros C Aw A M m' md c q n a pp bs bs2 v CK HW Lp Lq NE Rq Hn Ha Hb Hpp Hpp2 PX LK L. pose proof PX as (Hp0 & Hp64 & _).
  destruct (blk_range C Aw M md (Z_to_bv 64 q) n CK HW Lq Hn) as [Gq1 Gq2]. rewrite u_Z2bv in Gq1, Gq2 by lia.
  pose proof (exW_blk_apart C Aw M md c q 24 n CK HW Lp Lq ltac:(intros ->; apply NE; reflexivity) ltac:(lia) Rq ltac:(lia) ltac:(lia)) as AP.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as LV. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  apply (CMAPat_frame M); [exact PX|]. intros x Hx.
  pose proof (exT_blk_below C Aw M md c 24 x CK HW Lp Hp0 ltac:(lia) ltac:(lia) Hx) as BL.
  rewrite (exT_livk_at A _ m' c 24 x LK L Hp0 ltac:(lia) Hx).
  rewrite MemSplit.wbytes_outside by (rewrite u_Z2bv by lia; lia). apply MemSplit.wbytes_outside; rewrite u_Z2bv by lia; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exT_kn_pix : forall segs C A m md E (e we de wpe : expr) (p s F : Z) (v : pixv),
  Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some 64 -> PIXat m p v ->
  edenot E e = Z_to_bv 64 p -> edenot E we = Z_to_bv 64 s -> 0 <= s < 2 ^ 64 -> c_top C - LSTK <= s - F ->
  edenot E de = Z_to_bv 64 (p_data v) -> edenot E wpe = Z_to_bv 64 (p_wpl v) ->
  Forall (kentry_ok segs E m) [KRange e 4096 (2 ^ 47); KAlign e 16; KDisj (SA we (- F)) F (SA e 0) 64; KWord (SA e 56) 8 de; KWord (SA e 16) 4 wpe].
Proof.
  intros segs C A m md E e we de wpe p s F v CK HW L PX He Hwe Rs Hlo Hde Hwp. pose proof PX as (Hp0 & Hp64 & WF & _).
  assert (Rp : 0 <= p < 2 ^ 64) by lia.
  destruct (exW_blk_rng C A m md p 64 CK HW L Rp ltac:(lia)) as (G1 & G2 & G3).
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) L) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  repeat apply Forall_cons; [ | | | | | apply Forall_nil].
  - apply (ex_krange segs E m e p 4096 (2 ^ 47) He Rp). lia.
  - apply (ex_kalign segs E m e p 16 He Rp); [lia | exact ALp].
  - exact (ex_kdisj_apart segs E m we e s p (- F) F 0 64 Hwe He Rs Rp (exW_win_blk_apart_h C A m md s F p 64 CK HW L ltac:(lia) Rp Hlo)).
  - apply (ex_kword_Z segs E m e de p 56 (p_data v) 8 He Hde); try lia; [exact (wf_data _ WF) | exact (PIX_rd_data segs m p v PX)].
  - apply (ex_kword_Z segs E m e wpe p 16 (p_wpl v) 4 He Hwp); try lia; [pose proof (wf_wpl _ WF); lia | exact (PIX_rd_wpl segs m p v PX)].
Qed.

(* [comment removed for export] *)
Lemma exT_kn_whd : forall segs m E (e we he de : expr) (p : Z) (v : pixv), PIXat m p v ->
  edenot E e = Z_to_bv 64 p -> edenot E we = Z_to_bv 64 (p_w v) -> edenot E he = Z_to_bv 64 (p_h v) -> edenot E de = Z_to_bv 64 (p_d v) ->
  Forall (kentry_ok segs E m) [KWord (SA e 0) 4 we; KWord (SA e 4) 4 he; KWord (SA e 8) 4 de].
Proof.
  intros segs m E e we he de p v PX He Hw Hh Hd. pose proof PX as (Hp0 & Hp64 & WF & _). assert (Rp : 0 <= p < 2 ^ 64) by lia.
  pose proof (wf_w _ WF). pose proof (wf_h _ WF). pose proof (wf_d _ WF).
  repeat apply Forall_cons; [ | | | apply Forall_nil].
  - apply (ex_kword_Z segs E m e we p 0 (p_w v) 4 He Hw); try lia. rewrite Z.add_0_r. exact (PIX_rd_w segs m p v PX).
  - apply (ex_kword_Z segs E m e he p 4 (p_h v) 4 He Hh); try lia. exact (PIX_rd_h segs m p v PX).
  - apply (ex_kword_Z segs E m e de p 8 (p_d v) 4 He Hd); try lia. exact (PIX_rd_d segs m p v PX).
Qed.

(* [comment removed for export] *)
Lemma exT_wbytes_out : forall (M m' : word -> option byte) (a : Z) (bs : list byte), m' = wbytes M (Z_to_bv 64 a) bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  forall x : word, ~ (a <= u x < a + Z.of_nat (length bs)) -> m' x = M x.
Proof.
  intros M m' a bs -> Ha Hb x Hx. destruct (Z.eq_dec (Z.of_nat (length bs)) 0) as [E0|N0].
  - destruct bs; [reflexivity | cbn [length] in E0; lia].
  - apply MemSplit.wbytes_outside; rewrite u_Z2bv by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma exT_kn_cells : forall segs m E (e de wpe : expr) (p : Z) (v : pixv), PIXat m p v ->
  edenot E e = Z_to_bv 64 p -> edenot E de = Z_to_bv 64 (p_data v) -> edenot E wpe = Z_to_bv 64 (p_wpl v) ->
  Forall (kentry_ok segs E m) [KWord (SA e 56) 8 de; KWord (SA e 16) 4 wpe].
Proof.
  intros segs m E e de wpe p v PX He Hde Hwp. pose proof PX as (Hp0 & Hp64 & WF & _). assert (Rp : 0 <= p < 2 ^ 64) by lia.
  repeat apply Forall_cons; [ | | apply Forall_nil].
  - apply (ex_kword_Z segs E m e de p 56 (p_data v) 8 He Hde); try lia; [exact (wf_data _ WF) | exact (PIX_rd_data segs m p v PX)].
  - apply (ex_kword_Z segs E m e wpe p 16 (p_wpl v) 4 He Hwp); try lia; [pose proof (wf_wpl _ WF); lia | exact (PIX_rd_wpl segs m p v PX)].
Qed.

(* [comment removed for export] *)
Lemma exT_kept_patch1 : forall C A md (s off F : Z) (M M' : word -> option byte) E (rb : expr) (q n a : Z) (bs : list byte),
  Cok C -> W C A M md -> live A (Z_to_bv 64 q) = Some n -> 0 <= q < 2 ^ 64 -> 0 < n -> q <= a -> a + Z.of_nat (length bs) <= q + n ->
  FRM C (s + off) (wbytes M (Z_to_bv 64 a) bs) M' ->
  c_top C - LSTK + F <= s -> s <= c_top C -> (- F <=? off) = true -> (off <=? 0) = true -> edenot E rb = Z_to_bv 64 s ->
  ex_region_kept E M M' (rb, off, 0).
Proof.
  intros C A md s off F M M' E rb q n a bs CK HW Lq Rq Hn Ha Hb FR Hlo Hhi O1 O2 He.
  pose proof (exW_kept_stack2 C s off F _ M' E rb CK FR Hlo Hhi O1 O2 He) as K. apply Z.leb_le in O1, O2.
  destruct (exW_blk_rng C A M md q n CK HW Lq Rq Hn) as (G1 & G2 & G3).
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as LV.
  cbn [ex_region_kept] in K |- *. rewrite He, u_Z2bv in K |- * by lia. intros x Hx. rewrite (K x Hx).
  apply MemSplit.wbytes_outside; rewrite u_Z2bv by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma exT_kept_patch2 : forall C A md (s off F : Z) (M M' : word -> option byte) E (rb : expr) (q n a pp : Z) (bs bs2 : list byte),
  Cok C -> W C A M md -> live A (Z_to_bv 64 q) = Some n -> 0 <= q < 2 ^ 64 -> 0 < n -> q <= a -> a + Z.of_nat (length bs) <= q + n ->
  FRM C (s + off) (wbytes (wbytes M (Z_to_bv 64 a) bs) (Z_to_bv 64 pp) bs2) M' ->
  c_top C - LSTK + F <= s -> s <= c_top C -> (- F <=? off) = true -> (off <=? 0) = true -> edenot E rb = Z_to_bv 64 s ->
  0 <= pp -> pp + Z.of_nat (length bs2) <= s + off ->
  ex_region_kept E M M' (rb, off, 0).
Proof.
  intros C A md s off F M M' E rb q n a pp bs bs2 CK HW Lq Rq Hn Ha Hb FR Hlo Hhi O1 O2 He Hpp Hpp2.
  pose proof (exW_kept_stack2 C s off F _ M' E rb CK FR Hlo Hhi O1 O2 He) as K. apply Z.leb_le in O1, O2.
  destruct (exW_blk_rng C A M md q n CK HW Lq Rq Hn) as (G1 & G2 & G3).
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as LV.
  cbn [ex_region_kept] in K |- *. rewrite He, u_Z2bv in K |- * by lia. intros x Hx. rewrite (K x Hx).
  rewrite MemSplit.wbytes_outside by (rewrite u_Z2bv by lia; lia). apply MemSplit.wbytes_outside; rewrite u_Z2bv by lia; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exT_cmap_of_cells : forall segs C A m md (c arr d nalloc n pad : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 c) = Some 24 -> 0 <= c < 2 ^ 64 ->
  0 <= arr < 2 ^ 64 -> 0 <= d < 2 ^ 31 -> 0 <= nalloc < 2 ^ 31 -> 0 <= n < 2 ^ 31 -> 0 <= pad < 2 ^ 31 ->
  rdn segs m (Z_to_bv 64 (c + 0)) 8 = Some (Z_to_le_bytes 8 arr) -> rdn segs m (Z_to_bv 64 (c + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
  rdn segs m (Z_to_bv 64 (c + 12)) 4 = Some (Z_to_le_bytes 4 nalloc) -> rdn segs m (Z_to_bv 64 (c + 16)) 4 = Some (Z_to_le_bytes 4 n) ->
  rdn segs m (Z_to_bv 64 (c + 20)) 4 = Some (Z_to_le_bytes 4 pad) ->
  CMAPat m c (CMAPV arr d nalloc n pad).
Proof.
  intros segs C A m md c arr d nalloc n pad CK HW L Rc Ra Rd Rna Rn Rp C0 C8 C12 C16 C20.
  destruct (exW_blk_rng C A m md c 24 CK HW L Rc ltac:(lia)) as (G1 & G2 & G3).
  assert (DEF : forall i, 0 <= i < 24 -> m (Z_to_bv 64 (c + i)) <> None).
  { intros i Hi. destruct (blk_byte C A m md (Z_to_bv 64 c) 24 (Z_to_bv 64 (c + i)) CK HW L ltac:(rewrite !u_Z2bv by lia; lia)) as (_ & D & _). exact D. }
  split; [lia|]. split; [lia|]. split; [constructor; cbn; lia|].
  unfold cmap_bytes. cbn [c_arr c_d c_nalloc c_n c_pad].
  assert (L8 : forall z, length (Z_to_le_bytes 8 z) = 8%nat) by (intros z; apply length_Z_to_le_bytes).
  assert (L4 : forall z, length (Z_to_le_bytes 4 z) = 4%nat) by (intros z; apply length_Z_to_le_bytes).
  apply bytes_at_app. split.
  { apply (rdn_bytes_at segs m c (Z_to_le_bytes 8 arr)); rewrite ?L8; [lia | lia | intros i Hi; apply DEF; lia |]. rewrite Z.add_0_r in C0. exact C0. }
  rewrite L8. change (Z.of_nat 8) with 8. apply bytes_at_app. split.
  { apply (rdn_bytes_at segs m (c + 8) (Z_to_le_bytes 4 d)); rewrite ?L4; [lia | lia | intros i Hi; replace (c + 8 + i) with (c + (8 + i)) by lia; apply DEF; lia |]. exact C8. }
  rewrite L4. change (Z.of_nat 4) with 4. apply bytes_at_app. split.
  { apply (rdn_bytes_at segs m (c + 8 + 4) (Z_to_le_bytes 4 nalloc)); rewrite ?L4; [lia | lia | intros i Hi; replace (c + 8 + 4 + i) with (c + (12 + i)) by lia; apply DEF; lia |].
    replace (c + 8 + 4) with (c + 12) by lia. exact C12. }
  rewrite L4. change (Z.of_nat 4) with 4. apply bytes_at_app. split.
  { apply (rdn_bytes_at segs m (c + 8 + 4 + 4) (Z_to_le_bytes 4 n)); rewrite ?L4; [lia | lia | intros i Hi; replace (c + 8 + 4 + 4 + i) with (c + (16 + i)) by lia; apply DEF; lia |].
    replace (c + 8 + 4 + 4) with (c + 16) by lia. exact C16. }
  rewrite L4. change (Z.of_nat 4) with 4.
  apply (rdn_bytes_at segs m (c + 8 + 4 + 4 + 4) (Z_to_le_bytes 4 pad)); rewrite ?L4; [lia | lia | intros i Hi; replace (c + 8 + 4 + 4 + 4 + i) with (c + (20 + i)) by lia; apply DEF; lia |].
  replace (c + 8 + 4 + 4 + 4) with (c + 20) by lia. exact C20.
Qed.

(* [comment removed for export] *)
Lemma exT_pix_entry : forall C A m md (p : Z) (v : pixv), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some 64 -> PIXat m p v ->
  0 <= p < 2 ^ 64 /\ p <> 0 /\ p mod 16 = 0.
Proof.
  intros C A m md p v CK HW L PX. pose proof PX as (Hp0 & Hp64 & _). assert (Rp : 0 <= p < 2 ^ 64) by lia.
  destruct (exW_blk_rng C A m md p 64 CK HW L Rp ltac:(lia)) as (G1 & _).
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) L) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  split; [exact Rp | split; [lia | exact ALp]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exT_postm_clone : forall C Ar A1 A3 (m1 m2 m3 m4 : word -> option byte) md1 md3 (s pp pix : Z) (v : pixv),
  Cok C -> W C A1 m1 md1 -> W C A3 m3 md3 -> sub_live Ar A1 -> sub_live Ar A3 ->
  PIXat m1 pix v -> p_rc v = 1 -> live Ar (Z_to_bv 64 pix) = Some 64 ->
  0 <= pp -> c_top C - LSTK <= pp -> pp + 8 <= s -> s <= c_top C ->
  POSTM C A1 s (wbytes m1 (Z_to_bv 64 (pix + 20)) (Z_to_le_bytes 4 2)) m2 ->
  POSTM C Ar s m2 m3 ->
  POSTM C A3 (pp + 8) (wbytes (wbytes m3 (Z_to_bv 64 (pix + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 pp) (Z_to_le_bytes 8 0)) m4 ->
  POSTM C Ar s m1 m4.
Proof.
  intros C Ar A1 A3 m1 m2 m3 m4 md1 md3 s pp pix v CK HW1 HW3 SUB1 SUB3 PX Hrc Lr Hpp0 Hpp Hpps Hs [F12 L12] [F23 L23] [F34 L34].
  pose proof PX as (Hp0 & Hp64 & WF & HB).
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as LV. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (SUB1 _ _ Lr) as L1. pose proof (SUB3 _ _ Lr) as L3.
  assert (LEN4 : forall z, length (Z_to_le_bytes 4 z) = 4%nat) by (intros z; apply length_Z_to_le_bytes).
  assert (LEN8 : forall z, length (Z_to_le_bytes 8 z) = 8%nat) by (intros z; apply length_Z_to_le_bytes).
  (* [comment removed for export] *)
  assert (CELL : forall x : word, pix + 20 <= u x < pix + 24 -> wbytes m3 (Z_to_bv 64 (pix + 20)) (Z_to_le_bytes 4 1) x = m1 x).
  { intros x Hx. rewrite MemSplit.wbytes_inside by (rewrite ?LEN4, u_Z2bv by lia; lia). rewrite u_Z2bv by lia.
    specialize (HB (u x - pix) ltac:(rewrite pix_bytes_len; lia)).
    replace (Z_to_bv 64 (pix + (u x - pix))) with x in HB by (apply bv_eq; rewrite u_Z2bv by lia; lia).
    rewrite HB. f_equal. destruct v. cbn in Hrc. subst. unfold pix_bytes. cbn -[Z_to_le_bytes Z.to_nat nth].
    assert (J : u x - pix = 20 \/ u x - pix = 21 \/ u x - pix = 22 \/ u x - pix = 23) by lia.
    destruct J as [J|[J|[J|J]]]; rewrite J;
      [replace (u x - (pix + 20)) with 0 by lia | replace (u x - (pix + 20)) with 1 by lia | replace (u x - (pix + 20)) with 2 by lia | replace (u x - (pix + 20)) with 3 by lia]; reflexivity. }
  split.
  - (* [comment removed for export] *)
    intros a H1 H2 H3 H4 H5.
    assert (H5' : ~ scratch C (pp + 8) a) by (unfold scratch in *; lia).
    rewrite (F34 a H1 H2 H3 H4 H5').
    assert (NP : ~ (pp <= u a < pp + 8)) by (unfold scratch in H5; lia).
    rewrite MemSplit.wbytes_outside by (rewrite ?LEN8, u_Z2bv by lia; lia).
    assert (NC : ~ (pix + 20 <= u a < pix + 24)).
    { intros X. apply H1. destruct (blk_byte C A1 m1 md1 (Z_to_bv 64 pix) 64 a CK HW1 L1 ltac:(rewrite u_Z2bv by lia; lia)) as (G & _). exact G. }
    rewrite MemSplit.wbytes_outside by (rewrite ?LEN4, u_Z2bv by lia; lia).
    rewrite (F23 a H1 H2 H3 H4 H5), (F12 a H1 H2 H3 H4 H5).
    apply MemSplit.wbytes_outside; rewrite ?LEN4, u_Z2bv by lia; lia.
  - (* [comment removed for export] *)
    intros q k i Lq Hi.
    pose proof (SUB1 _ _ Lq) as Lq1. pose proof (SUB3 _ _ Lq) as Lq3.
    pose proof (u64_range q) as Rq.
    destruct (blk_range C A1 m1 md1 q k CK HW1 Lq1 ltac:(lia)) as [Gq1 Gq2].
    assert (Ux : u (at_ q i) = u q + i) by (unfold at_; rewrite u_Z2bv by lia; reflexivity).
    rewrite (L34 q k i Lq3 Hi).
    rewrite MemSplit.wbytes_outside by (rewrite ?LEN8, u_Z2bv by lia; lia).
    destruct (Z_le_gt_dec (pix + 20) (u (at_ q i))) as [X1|X1]; [destruct (Z_lt_ge_dec (u (at_ q i)) (pix + 24)) as [X2|X2]|].
    + apply CELL. lia.
    + rewrite MemSplit.wbytes_outside by (rewrite ?LEN4, u_Z2bv by lia; lia).
      rewrite (L23 q k i Lq Hi), (L12 q k i Lq1 Hi). apply MemSplit.wbytes_outside; rewrite ?LEN4, u_Z2bv by lia; lia.
    + rewrite MemSplit.wbytes_outside by (rewrite ?LEN4, u_Z2bv by lia; lia).
      rewrite (L23 q k i Lq Hi), (L12 q k i Lq1 Hi). apply MemSplit.wbytes_outside; rewrite ?LEN4, u_Z2bv by lia; lia.
Qed.
End ExecT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exT_cs_of_al : forall (E : env) (sr : list expr) (rE Rc : bvmap 5 word) (al : list (nat * expr)), regs_ok E sr Rc ->
  Forall (fun ke => edenot E (snd ke) = getr rE (Z_to_bv 5 (Z.of_nat (fst ke)))) al ->
  forallb (fun k => existsb (fun ke => Nat.eqb (fst ke) k && expr_eqb (snd ke) (nth k sr (ELit 0))) al) exW_cs_idx = true ->
  cs_kept rE Rc.
Proof.
  intros E sr rE Rc al HR HA HB r Hr. pose proof (exW_cs_idx_complete r Hr) as Hin. rewrite forallb_forall in HB. specialize (HB _ Hin).
  rewrite (HR r). unfold sr_get.
  assert (N0 : bv_eqb r 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. unfold callee_saved in Hr. intros X.
    destruct Hr as [->|[->|[->|[->|[->|H]]]]]; try discriminate X. change (bv_unsigned (0 : reg)) with 0%Z in X. lia. }
  rewrite N0.
  apply existsb_exists in HB as ([k e] & Hin' & Hke). cbn [fst snd] in Hke. apply andb_true_iff in Hke as [K1 K2].
  apply Nat.eqb_eq in K1. apply expr_eqb_eq in K2. subst k. rewrite <- K2.
  pose proof (proj1 (Forall_forall _ _) HA _ Hin') as X. cbn [fst snd] in X. rewrite X. f_equal. apply ridx_roundtrip.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exT_ret_step : forall (fx : FPState) segs (R : bvmap 5 word) (pc : Z) (M rom : word -> option byte) w rd rs1 (imm : bv 12) (retw : word) ms0,
  msteps segs ms0 (@mkst fx R (Z_to_bv 64 pc) M rom) ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  bv_eqb rd 0 = true -> bv_signed imm = 0%Z -> getr R rs1 = retw -> ret_ok retw ->
  msteps segs ms0 (@mkst fx R retw M rom).
Proof.
  intros fx segs R pc M rom w rd rs1 imm retw ms0 Hms Hf He Hd Hrd Himm Hra Hok.
  eapply (ex_msteps_snoc segs); [exact Hms | reflexivity |].
  rewrite (step_jalr_gen segs R (Z_to_bv 64 pc) M rom w rd rs1 imm Hf He Hd). rewrite Hrd, Himm, Hra.
  unfold ret_ok in Hok. change (jalr_tgt retw 0) with (v_jalr retw 0). rewrite Hok. reflexivity.
Qed.
