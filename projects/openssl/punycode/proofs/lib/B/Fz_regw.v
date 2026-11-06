(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require StoreOk SeqExec.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import Layout RT_iface D_kit D_libiface Fz_defs Fz_voc Fz_regions.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require WpEngine LibKit StrKit AShadow ABridge KBridge.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require BRt BCode BDecode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Abbreviation W z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Lemma bytes_at_sub : forall (m : mem) A bs k n, bytes_at bsegs m A bs -> (k + n <= length bs)%nat ->
  bytes_at bsegs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m A bs k n (H0 & H1 & H) Hk. split; [lia|]. split; [rewrite firstn_length, skipn_length; lia|].
  intros i Hi. rewrite firstn_length, skipn_length in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia. rewrite (H (k + i)%nat) by lia.
  rewrite nth_error_firstn. rewrite nth_error_skipn.
  destruct (Nat.ltb_spec i n) as [L|L]; [reflexivity | lia].
Qed.

Lemma stk_wview : forall (m : mem) lo hi (x : word), stk bsegs m lo hi -> lo <= bv_unsigned x < hi -> wview bsegs m x <> None.
Proof.
  intros m lo hi x (S0 & S1 & S) Hx. pose proof (proj1 (S (bv_unsigned x) Hx)) as Wv.
  unfold wa in Wv. rewrite Z_to_bv_bv_unsigned in Wv. exact Wv.
Qed.

Lemma wr_at_wview : forall (m : mem) a n (x : word), wr_at bsegs m a n -> a <= bv_unsigned x < a + n -> wview bsegs m x <> None.
Proof.
  intros m a n x (S0 & S1 & S) Hx. pose proof (S (bv_unsigned x - a) ltac:(lia)) as Wv.
  replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Wv by lia. unfold wa in Wv. rewrite Z_to_bv_bv_unsigned in Wv. exact Wv.
Qed.

(* [comment removed for export] *)
Lemma decode_w : forall (usp spa lo d FB : Z) (bs : list byte)
    (gp tp t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  BRt.rt_ok m -> mem_inv bsegs m ->
  Z.of_nat (length bs) < 2^26 -> bytes_at bsegs m d bs -> acc bsegs m d (Z.of_nat (length bs)) ->
  AShadow.memrange d (Z.of_nat (length bs)) -> (bs = [] \/ d + Z.of_nat (length bs) <= 0x10000 \/ 0xbfd000 <= d) -> 0 < d ->
  stk bsegs m lo spa -> 0x10007fff8000 <= lo -> lo + 2400 <= spa -> spa < 2^47 ->
  FB mod 64 = 0 -> 0xbfd000 <= FB -> FB + 256 <= lo -> (FB + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= FB) ->
  wr_at bsegs m (FB + 32) 64 -> rw_cells bsegs m (FB + 128) [C4 (Z_to_bv 64 16)] ->
  bytes_at bsegs m (shad FB + 4) (repeat z8 8) -> bytes_at bsegs m (shad FB + 16) [Z_to_bv 8 4] ->
  stk bsegs m (shad FB) (shad FB + 24) ->
  evt bsegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       ms' = MS (mkR (Z_to_bv 64 0x1ee174) (Z_to_bv 64 spa) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x1ee174) fc None m' (seg_rom bsegs)
       /\ munch [(spa - 2400, spa); (FB + 32, FB + 96); (FB + 128, FB + 132)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
       /\ StoreOk.mem_grows m m')
    (MS (mkR (Z_to_bv 64 0x1ee174) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 d)
             (Z_to_bv 64 (Z.of_nat (length bs))) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 128)) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_decode) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros RT MI NB BY ACC MR OFF D0 ST LOH LO SPH F64 FLO FHI FBAND WOUT CLEN SHO SHL SHW.
  set (n := Z.of_nat (length bs)) in *.
  assert (Hn : 0 <= n) by (unfold n; lia).
  assert (ESO : AShadow.sha (FB + 32) = shad FB + 4) by (unfold AShadow.sha, shad, SHB, AShadow.SB; Z.div_mod_to_equations; lia).
  assert (ESO2 : AShadow.sha (FB + 32 + 4 * 16 - 1) = shad FB + 11) by (unfold AShadow.sha, shad, SHB, AShadow.SB; Z.div_mod_to_equations; lia).
  assert (ESL : AShadow.sha (FB + 128) = shad FB + 16) by (unfold AShadow.sha, shad, SHB, AShadow.SB; Z.div_mod_to_equations; lia).
  assert (SH8 : shad FB mod 8 = 0) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  assert (SHR : 0xbfd000 <= shad FB /\ shad FB + 32 <= 0x10007fff8000) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  eapply evt_mono.
  - apply (decode_evt (Z_to_bv 64 0x1ee174) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 d)
             (Z_to_bv 64 n) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 128)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             spa d n (FB + 32) (FB + 128) 16); try reflexivity; try assumption.
    + lia.
    + apply addr_ok_of_acc; [lia | unfold AShadow.memrange, AShadow.LOMEM_END, AShadow.HIMEM_END in MR; lia | exact ACC].
    + destruct OFF as [->|OFF]; [intros i Hi; cbn in *; lia|]. exact (rd_ok_bytesA m d bs BY OFF).
    + lia.
    + apply (KBridge.cell_C4 bsegs m (FB + 128) (Z_to_bv 64 16)). exact (proj1 CLEN).
    + unfold BRt.B_IMG_END. lia.
    + right. unfold AShadow.HIMEM_BEG. lia.
    + apply (KBridge.wr_ok_stk bsegs m lo spa); [exact ST | lia | lia].
    + unfold BRt.B_IMG_END. lia.
    + unfold AShadow.memrange, AShadow.LOMEM_END, AShadow.HIMEM_BEG, AShadow.HIMEM_END. lia.
    + apply ABridge.addr_ok_of_zeros; [lia | lia |]. rewrite ESO2, ESO. replace (shad FB + 11 - (shad FB + 4) + 1) with (Z.of_nat 8) by lia.
      apply zeros_of_bytes; [exact SHO | right; lia].
    + intros _. unfold AShadow.shw_ok. rewrite ESO2, ESO.
      apply (rd_ok_stkA m (shad FB) (shad FB + 24)); [exact SHW | right; lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
    + apply (KBridge.wr_ok_wr_at bsegs m (FB + 32) 64); [exact WOUT | lia | lia].
    + unfold BRt.B_IMG_END. lia.
    + unfold AShadow.memrange, AShadow.LOMEM_END, AShadow.HIMEM_BEG, AShadow.HIMEM_END. lia.
    + apply (ABridge.addr_ok_partial m (FB + 128) 4 (Z_to_bv 8 4)); [lia | Z.div_mod_to_equations; lia | lia | | reflexivity].
      rewrite ESL. pose proof (bytes_offA m (shad FB + 16) [Z_to_bv 8 4] 0 SHL ltac:(right; lia) ltac:(cbn; lia)) as R.
      rewrite Z.add_0_r in R. exact R.
    + apply (KBridge.wr_ok_wr_at bsegs m (FB + 128) 4); [exact (rw_cells_wr_at bsegs m _ _ 4 CLEN ltac:(cbn; lia)) | lia | lia].
    + left. lia.
    + left. lia.
    + right. lia.
    + clear - F64. Z.div_mod_to_equations; lia.
    + clear - F64. Z.div_mod_to_equations; lia.
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _ & HU & HG).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [rewrite (LibKit.v_jalr_even (Z_to_bv 64 0x1ee174)) by reflexivity; reflexivity|].
    assert (HWV : forall x : word, BDecode.dec_FP spa (FB + 32) (FB + 128) 16 x -> wview bsegs m x <> None).
    { intros x [Hx|[Hx|Hx]]; unfold LibKit.inr in Hx.
      - apply (stk_wview m lo spa); [exact ST | lia].
      - apply (wr_at_wview m (FB + 32) 64); [exact WOUT | lia].
      - apply (wr_at_wview m (FB + 128) 4); [exact (rw_cells_wr_at bsegs m _ _ 4 CLEN ltac:(cbn; lia)) | lia]. }
    split; [| split; [exact (KBridge.wmono_of_grows bsegs m m' HG) | split; [exact (KBridge.mem_inv_unch bsegs m m' _ MI HU HWV) | exact HG]]].
    apply (KBridge.munch_of_unch _ m m' _ HU). intros x Hx Ho. cbn [outside] in Ho. unfold BDecode.dec_FP, LibKit.inr in Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma store0_w : forall (b n : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  mem_inv bsegs m -> 0 < b -> 0 <= n -> b + n + 1 < 2^47 ->
  acc bsegs m b (n + 1) -> wr_at bsegs m b (n + 1) ->
  evt bsegs (fun ms' => exists m' : mem,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (b + n)) (Z_to_bv 64 (bv_unsigned s7 + 144)) (Z_to_bv 64 16) a3 a4 a5 a6 a7 s2
                     (Z_to_bv 64 n) s4 (Z_to_bv 64 b) s6 s7 (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1ee1ac) fc None m' (seg_rom bsegs)
       /\ munch [(b + n, b + n + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ StoreOk.mem_grows m m'
       /\ bytes_at bsegs m' (b + n) [z8])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) s4 (Z_to_bv 64 b) s6 s7 (Z_to_bv 64 SHB) s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x1ee184) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros MI Hb Hn HB ACC WR.
  eapply evt_mono.
  - apply (store0_evt ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) s4 (Z_to_bv 64 b) s6 s7 (Z_to_bv 64 SHB)
             s9 s10 s11 t3 t4 t5 t6 F fc m b n); try reflexivity; try lia.
    + apply (addr_ok_of_acc m b (n + 1) ltac:(lia) ltac:(lia) ACC). lia.
    + apply (KBridge.wr_ok_wr_at bsegs m b (n + 1)); [exact WR | lia | lia].
  - intros ms' (m' & -> & HC & HU & HG). exists m'. split; [reflexivity|].
    split; [apply (KBridge.munch_of_unch _ m m' _ HU); intros x Hx Ho; cbn [outside] in Ho; unfold LibKit.inr in Hx; lia|].
    split; [exact (KBridge.wmono_of_grows bsegs m m' HG)|]. split; [| split; [exact HG|]].
    + apply (KBridge.mem_inv_unch bsegs m m' _ MI HU). intros x Hx. unfold LibKit.inr in Hx.
      apply (wr_at_wview m b (n + 1)); [exact WR | lia].
    + exact (KBridge.bytes_of_cell bsegs m' (b + n) 1 (Z_to_bv 64 0) ltac:(lia) ltac:(lia) HC).
Qed.
