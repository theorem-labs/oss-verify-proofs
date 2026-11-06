From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ASan-image walk of musl mseek for libreac/fuzz_pcap -- PFmopsM.v's
   amseek_rewind_spec, PROVED for the ORIGINAL v1.9.0 ASan image at mseek's measured entry 0x8ec28.

   PORTED from proofs/libreac/fuzz_pcap/lib/Prog/mseek_c.v and mseek_ro_c.v: facts, case split and pcs
   only, restated in the core's ASan vocabulary. The PLAIN proofs are not importable (lib/Lib's mkst
   empties the FP state). The released-proof lookup (ossv proof index v5, 2026-10-28T20:16:23Z,
   main@e966c513ee6c) found 4 files named for mseek and 4 related (mseek_ro), all on the plain image:
   no released proof stated mseek on pcap's ASan image.

   THE BODY, read off fuzz_pcap.objdump.txt (sha256 bf9d80d6e30f; internal record) (39 instructions, frame 48):
     0x8ec28-0x8ec30  addi sp,-48 ; sd ra,40(sp) ; sd s0,32(sp)
     0x8ec34-0x8ec44  s0 = *0x9a4b8 (the .got slot of __stack_chk_guard 0x5f48d0); 24(sp) = *s0
     0x8ec48          bgeu a2,3 -> EINVAL            whence = SEEK_CUR = 1: NOT taken (concrete)
     0x8ec4c-0x8ec54  a3 = f->cookie (+152) = f+232 ; a0 = c->pos (+232) ; a4 = c->len (+240)
     0x8ec5c-0x8ec70  0(sp) = 0 ; 8(sp) = pos ; 16(sp) = len ; a0 = 8(sp) = pos   (base[whence])
     0x8ec78          blt a1,-pos -> EINVAL          guard 1
     0x8ec7c-0x8ec84  a2 = c->size (+248) - pos ; bge a2,a1 -> 0x8ecb4   guard 2
     0x8ecb4-0x8ecbc  a0 = pos + off ; c->pos = a0 (0x8ecb8, the ONLY heap store) ; j 0x8ec98
     0x8ec98-0x8ecb0  canary re-check (bne -> __stack_chk_fail), restore ra / s0 / sp, ret
   The EINVAL arm (0x8ec88, __errno_location) and __stack_chk_fail (0x8ecc0) are UNREACHABLE here:
     - the bgeu is decided by the literal whence 1 < 3;
     - guard 1 holds because a1 = -(cpos - p) and p >= 0: SIGNED, p - cpos >= -cpos (fact c1);
     - guard 2 holds because n - cpos >= p - cpos, with cpos <= n < 2^63 so neither side wraps (fact c2);
     - the canary compare reads the same .bss cell twice and the frame slot it stored, so the two
       operands are the SAME symbolic value (SOff 34 0) and the engine decides the bne by syntax.
   Both guards enter the symbolic state as assumed conditions (f_conds), proved once at entry from
   asource_at's `p <= cpos <= n < 2^63` (a Theorem Labs lane row 1c); the engine then runs the body straight
   through from 0x8ec28 to the `ret` at 0x8ecb0 with no branch left open.

   THE CALLER'S cpos. The spec quantifies cpos with `val_mem (f+232) 8 cpos`, which fixes it only
   modulo 2^64; asource_at's own cookie value is the canonical one in [0, 2^63). wms_val_mem8_det
   ties the two, so a1 = Z_to_bv 64 (p - cpos) and the new position is exactly p.

   AR_laws Asan.M.loaded_segments B is NOT a hypothesis: lib/Reusable/YG0q.v proves
   `AR_laws_ok : AR_laws segs B` for every segs and B with no Section hypothesis, and the walk takes it
   from there, as the donor does (cgif lib/A/ACed.v:73; a Theorem Labs lane, 23:10Z).

   THE ONE REMAINING SECTION HYPOTHESIS of pcap_amseek_rewind (a law of the asyms record B, which the
   spec quantifies over, so no walk can discharge it):
     ASIL : asource_img_laws SK Asan.M.loaded_segments B pcap_KS
            -- PSourceMeta.v's record, discharged once at instantiation (row 4 with PSourceK row 6);
               this walk uses ONE field of it, asil_can_got (the .got slot 0x9a4b8 holds 0x5f48d0). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_pcap.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0p.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YE00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YE01 YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YG0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceK PSourceMeta PFmopsM.
(* The stdio image pcs come from the per-image numerals file (a Theorem Labs lane 02:31Z / 03:54Z). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PStdioImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The image: segments, code table, and the facts the core's walk lemmas take, all by evaluation.  *)
(* ---------------------------------------------------------------------------------------------- *)
Definition msegs : list Segment := Asan.M.loaded_segments.
Definition mtbl : ctable := build_table msegs PMSEEK 39 TEmpty.
Lemma mtbl_ok : table_ok msegs mtbl.
Proof. apply build_table_ok0. unfold PMSEEK. lia. Qed.

(* MEASURED (vm_compute of the segment list): four contiguous loaded segments,
   [0x10000,0x2f000) r--, [0x2f000,0x99000) r-x, [0x99000,0x9b000) rw-, [0x9b000,0x5f7000) rw-. *)
Lemma wms_seg_table :
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) msegs =
  [(65536, (symaddr (ImgPages.Asan.text_lo - ImgPages.Asan.ro_lo)%Z)); ((symaddr ImgPages.Asan.text_lo), (symaddr (ImgPages.Asan.relro_lo - ImgPages.Asan.text_lo)%Z)); ((symaddr ImgPages.Asan.relro_lo), (symaddr (ImgPages.Asan.rw_lo - ImgPages.Asan.relro_lo)%Z)); ((symaddr ImgPages.Asan.rw_lo), (symaddr (ImgPages.Asan.top - ImgPages.Asan.rw_lo)%Z))].
Proof. vm_compute. reflexivity. Qed.

Lemma wms_img_range : forall a, in_img msegs a -> 0x10000 <= a < (symaddr ImgPages.Asan.top).
Proof.
  intros a (sg & Hin & Hr).
  pose proof (in_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) msegs sg Hin) as H.
  rewrite wms_seg_table in H. cbn [In] in H.
  destruct H as [H|[H|[H|[H|[]]]]]; injection H as E1 E2; lia.
Qed.

Lemma wms_segs_low : forall a, in_img msegs a -> 0 <= a < kLowMemEnd.
Proof. intros a Ha. pose proof (wms_img_range a Ha). unfold kLowMemEnd. lia. Qed.

Lemma wms_wx : wx_segs_nowrap msegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Lemma wms_img_full : forall x, 0x10000 <= x < (symaddr ImgPages.Asan.top) -> in_img msegs x.
Proof.
  intros x Hx. pose proof wms_seg_table as Hm. unfold in_img.
  destruct msegs as [|s0 [|s1 [|s2 [|s3 [|s4 l]]]]]; cbn [map] in Hm; try discriminate Hm.
  injection Hm as E0 F0 E1 F1 E2 F2 E3 F3.
  destruct (Z_lt_le_dec x (symaddr ImgPages.Asan.text_lo)).
  { exists s0. split; [left; reflexivity | lia]. }
  destruct (Z_lt_le_dec x (symaddr ImgPages.Asan.relro_lo)).
  { exists s1. split; [right; left; reflexivity | lia]. }
  destruct (Z_lt_le_dec x (symaddr ImgPages.Asan.rw_lo)).
  { exists s2. split; [right; right; left; reflexivity | lia]. }
  exists s3. split; [right; right; right; left; reflexivity | lia].
Qed.

(* A byte range none of whose bytes is in the image lies wholly below or wholly above it. *)
Lemma wms_blk_off_img : forall p n, 0 < n -> (forall a, p <= a < p + n -> ~ in_img msegs a) ->
  p + n <= 0x10000 \/ (symaddr ImgPages.Asan.top) <= p.
Proof.
  intros p n Hn H. destruct (Z_le_gt_dec (p + n) 0x10000) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (symaddr ImgPages.Asan.top) p) as [L2|L2]; [right; exact L2|]. exfalso.
  apply (H (Z.max p 0x10000)); [lia|]. apply wms_img_full. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Byte-level helpers.                                                                             *)
(* ---------------------------------------------------------------------------------------------- *)
Lemma wms_le_bytes_mod : forall x y,
  (forall k, (k < 8)%nat -> YO0f.le_byte x 8 k = YO0f.le_byte y 8 k) -> x mod 2 ^ 64 = y mod 2 ^ 64.
Proof.
  intros x y H. unfold YO0f.le_byte in H. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in H.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i 64) as [Hlt|Hge].
  - pose proof (Z.div_mod i 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hm.
    assert (Hq : 0 <= i / 8 < 8) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    set (k := Z.to_nat (i / 8)).
    assert (Hk : (k < 8)%nat) by (subst k; lia).
    assert (Ek : Z.of_nat k = i / 8) by (subst k; rewrite Z2Nat.id; lia).
    specialize (H k Hk). change 256 with (2 ^ 8) in H.
    assert (Hb : forall z, Z.testbit (Z.shiftr (z mod 2 ^ 64) (8 * Z.of_nat k) mod 2 ^ 8) (i mod 8) =
                           Z.testbit (z mod 2 ^ 64) i).
    { intros z. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia. f_equal. lia. }
    rewrite <- (Hb x), <- (Hb y), H. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma wms_val_mem8_det : forall segs (m : word -> option byte) a x y,
  val_mem segs m a 8 x -> val_mem segs m a 8 y -> 0 <= y < 2 ^ 64 -> x mod 2 ^ 64 = y.
Proof.
  intros segs m a x y Hx Hy Hr. rewrite <- (Z.mod_small y (2 ^ 64)) by lia. apply wms_le_bytes_mod.
  intros k Hk. specialize (Hx k Hk). specialize (Hy k Hk). rewrite Hx in Hy.
  assert (Hb : Z_to_bv 8 (YO0f.le_byte x 8 k) = Z_to_bv 8 (YO0f.le_byte y 8 k)) by congruence. clear Hy.
  apply (f_equal bv_unsigned) in Hb. rewrite !Z_to_bv_unsigned in Hb. unfold bv_wrap in Hb. rename Hb into Hy.
  change (bv_modulus 8) with 256 in Hy. unfold YO0f.le_byte in *. rewrite !Z.mod_mod in Hy by lia. exact Hy.
Qed.

Lemma wms_mbyte_kept : forall segs E rs (m m' : word -> option byte) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> mbyte segs m' a = mbyte segs m a.
Proof.
  intros segs E rs m m' a HF Ha Hn. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

Lemma wms_val_mem_kept : forall segs E rs (m m' : word -> option byte) a n v,
  frame_of E rs m m' -> (forall k, 0 <= k < Z.of_nat n -> 0 <= a + k < 2 ^ 64 /\ ~ in_wrange E rs (a + k)) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof.
  intros segs E rs m m' a n v HF Hk Hv k Hkn.
  rewrite (wms_mbyte_kept segs E rs m m' (a + Z.of_nat k) HF); [apply Hv, Hkn | apply Hk; lia | apply Hk; lia].
Qed.

Lemma wms_swrap_congr : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> bv_swrap 64 x = bv_swrap 64 y.
Proof.
  intros x y H. rewrite <- (bv_swrap_wrap' 64 x), <- (bv_swrap_wrap' 64 y). unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite H. reflexivity.
Qed.

Lemma wms_bge : forall E a b, Sg E b <= Sg E a -> branch_taken BC_GE (sv_denot E a) (sv_denot E b) = true.
Proof.
  intros E a b H. cbn [branch_taken]. unfold bv_lts. apply negb_true_iff. apply Z.ltb_ge.
  unfold Sg in H. exact H.
Qed.

Lemma wms_wvb_io : forall m X,
  m_fds (with_vm_backing (m_vm_lazy m) X m) = m_fds m /\ m_fs (with_vm_backing (m_vm_lazy m) X m) = m_fs m.
Proof. intros m X. destruct m. split; reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The symbolic entry state of mseek's rewind call.                                                 *)
(*   atoms 0..31: the registers (a2 pinned to the literal whence 1); 32: cpos; 33: n; 34: canary.  *)
(*   regions: mseek's own 48-byte frame (writable); the cookie fields of the FILE (+152..+256, with *)
(*   ONLY the position cell +232..+240 writable); the .got slot and the canary cell (read-only).    *)
(* ---------------------------------------------------------------------------------------------- *)
Definition R_stk : YP09.region := YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [].
Definition R_file : YP09.region :=
  YP09.mkRegion (Some 10%nat) 152 256 232 240
    [YP09.mkChunk 152 (CVal 8 (SOff 10 232)); YP09.mkChunk 232 (CVal 8 (SOff 32 0));
     YP09.mkChunk 240 (CVal 8 (SOff 33 0)); YP09.mkChunk 248 (CVal 8 (SOff 33 0))].
Definition R_got : YP09.region :=
  YP09.mkRegion None (symaddr (Symbols.Asan.Sec.s_got + 0xce8)%Z) (symaddr (Symbols.Asan.Sec.s_got + 0xcf0)%Z) (symaddr (Symbols.Asan.Sec.s_got + 0xce8)%Z) (symaddr (Symbols.Asan.Sec.s_got + 0xce8)%Z) [YP09.mkChunk (symaddr (Symbols.Asan.Sec.s_got + 0xce8)%Z) (CVal 8 (SLit (symaddr Symbols.Asan.s___stack_chk_guard)))].
Definition R_can : YP09.region :=
  YP09.mkRegion None (symaddr Symbols.Asan.s___stack_chk_guard) (symaddr Symbols.Asan.s___abort_lock) (symaddr Symbols.Asan.s___stack_chk_guard) (symaddr Symbols.Asan.s___stack_chk_guard) [YP09.mkChunk (symaddr Symbols.Asan.s___stack_chk_guard) (CVal 8 (SOff 34 0))].
Definition ms_atoms : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47) 4);
   (32%nat, mkAF 0 (2 ^ 63 - 1) 0); (33%nat, mkAF 0 (2 ^ 63 - 1) 0)].
(* The two guards, in exactly the form the engine reaches them (0x8ec78 and 0x8ec84). *)
Definition ms_c1 : acond := mkAC BC_GE (SOff 11 0) (SAlu ALU_SUB (SLit 0) (SOff 32 0)).
Definition ms_c2 : acond := mkAC BC_GE (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit (-1))) (SOff 33 0)) (SOff 11 0).
Definition ss_ms : sstate :=
  mkSS PMSEEK (sr_set sr_atoms 12%bv (SLit 1)) [R_stk; R_file; R_got; R_can] None
    (mkFacts ms_atoms [ms_c1; ms_c2] []).
Definition ss_end : sstate := Eval vm_compute in fst (sym_run_toN msegs mtbl FUEL (symaddr (Symbols.Asan.s_mseek + 0x88)%Z) ss_ms).
Lemma ms_run : sym_run_toN msegs mtbl FUEL (symaddr (Symbols.Asan.s_mseek + 0x88)%Z) ss_ms = (ss_end, RS_running).
Proof. vm_compute. reflexivity. Qed.

Ltac rget HS r H :=
  pose proof (st_ok_restrict_reg msegs _ _ _ _ r HS) as H;
  lazymatch type of H with _ = sv_denot _ ?t => let e := eval vm_compute in t in change t with e in H end.
(* Side conditions on pcap_KS's concrete stdio cells (all in .rodata / .bss, inside the image). *)
Ltac kc :=
  cbv [as_threaded as_need_locks as_ofl_lock as_mode as_rwa as_canary as_ofl_head pcap_KS PCAP_THREADED
       PCAP_NEED_LOCKS PCAP_OFL_LOCK PCAP_MODE PCAP_RWA PCAP_CANARY src_mode_Z src_modeset_Z];
  cbn [length app]; lia.

(* ---------------------------------------------------------------------------------------------- *)
(* amseek_rewind_spec on pcap's v1.9.0 ASan image.                                                  *)
(* ---------------------------------------------------------------------------------------------- *)
Section W.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.
Hypothesis ASIL : asource_img_laws SK msegs B pcap_KS.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* The .got slot of __stack_chk_guard: the source analogue of PSourceMeta.asrc_meta_ptr_of_AR, for
   the field asil_can_got. *)
Lemma wms_can_got : forall ly S (W : world msegs) mem md, AR msegs B ly S W mem md ->
  val_mem msegs (rd W mem) (as_can_got pcap_KS) 8 (as_canary pcap_KS).
Proof.
  intros ly S W mem md HAR k Hk.
  pose proof (am_const _ _ _ _ (proj1 HAR)) as HC.
  pose proof (proj1 (Forall_forall _ _) HC _ (asil_can_got _ _ _ _ ASIL ly)) as Hc. unfold z8, c8, cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
  specialize (Hc k Hk). unfold aview in Hc.
  destruct (mbyte msegs (mrestrict (w_H W) mem) (as_can_got pcap_KS + Z.of_nat k)) as [b|] eqn:E; [|discriminate Hc]. cbn in Hc.
  injection Hc as Hc. f_equal. apply bv_eq. rewrite Hc, Z_to_bv_unsigned. symmetry.
  change (YO0f.le_byte (as_canary pcap_KS) 8 k) with (YG0f.le_byte (as_canary pcap_KS) 8 k). unfold YG0f.le_byte.
  unfold bv_wrap. change (bv_modulus 8) with 256%Z. apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.

Theorem pcap_amseek_rewind : amseek_rewind_spec SK msegs B pcap_KS PMSEEK.
Proof.
  intros W ly S regs mem md ch f b C p cpos' HPRE HSRC Hblk Hbsep Hcpos' Hpc' H10 H11 H12.
  pose proof wms_segs_low as Hsegs. pose proof wms_wx as Hwx.
  pose proof (YG0q.AR_laws_ok msegs B) as LAWS.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold PMSEEK_STK in Hslo, Hpres, Hstk0, Hbot, Hbsep.
  set (sp0 := spZ regs) in *.
  destruct HSRC as (Wn & cpos & fl & mdv & HSRC). cbv zeta in HSRC.
  destruct HSRC as (Hp0 & Hpc & Hcn & Hn63 & Hbn & Hcw & HWn & HbC & Hgarr & Hstat & Hwin & Hfl & Hfl24 & Hmode
    & Hcpv & Henv & Hhead & Hf0).
  set (n := Z.of_nat (length C)) in *.
  destruct Hstat as (S24 & S64 & S72 & S80 & S88 & S96 & S240 & S248 & S256 & S264 & S152 & S32 & S40 & S48 & S56
    & S104 & S112 & S168 & S120 & S140 & S144 & Hf0' & Hf16 & Hb0 & Hfb).
  pose proof Henv as (Ethr & Enl & Elk & Emode & Emset & (cval & Hcvr & Hcv)).
  (* the FILE block: live, below the stack, and off the image *)
  destruct (al_blocks _ _ LAWS ly S W mem md f SRC_FILE_BLOCK HAR Hblk) as (Hb16 & Hf4096 & Hfceil & Hfapp & Hfpres & _ & _).
  assert (RQ : req_size SRC_FILE_BLOCK = 1304) by reflexivity. rewrite RQ in Hfceil, Hfpres.
  assert (Hfimg : f + 1304 <= 0x10000 \/ (symaddr ImgPages.Asan.top) <= f).
  { apply (wms_blk_off_img f 1304); [lia|]. intros a Ha.
    exact (blk_img msegs B LAWS ly S W mem md f SRC_FILE_BLOCK a HAR Hblk ltac:(rewrite RQ; lia)). }
  (* the caller's cpos is the cookie's, modulo 2^64; so a1 = p - cpos *)
  assert (Hcmod : cpos' mod 2 ^ 64 = cpos)
    by (apply (wms_val_mem8_det msegs (rd W mem) (f + SRC_COOKIE_OFF) cpos' cpos Hcpos' Hcpv); lia).
  assert (H11' : getr regs 11 = Z_to_bv 64 (p - cpos)).
  { rewrite H11. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    pose proof (Z.div_mod cpos' (2 ^ 64) ltac:(lia)) as Hd. rewrite Hcmod in Hd.
    replace (- (cpos' - p)) with ((p - cpos) + (- (cpos' / 2 ^ 64)) * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  (* the environment of the symbolic run *)
  set (extra := [Z_to_bv 64 cpos; Z_to_bv 64 n; Z_to_bv 64 cval]).
  set (E := Ereg regs extra).
  assert (HAE : YP06.env_agree 32 (Ereg regs extra) E) by exact (YP06.env_agree_refl 32 E).
  assert (E1 : ew E 1 = getr regs 1) by exact (ew_Ereg_nat regs extra 1 1%bv eq_refl).
  assert (E2 : ew E 2 = getr regs 2) by exact (ew_Ereg_nat regs extra 2 2%bv eq_refl).
  assert (E10 : ew E 10 = Z_to_bv 64 f) by (rewrite <- H10; exact (ew_Ereg_nat regs extra 10 10%bv eq_refl)).
  assert (E11 : ew E 11 = Z_to_bv 64 (p - cpos)) by (rewrite <- H11'; exact (ew_Ereg_nat regs extra 11 11%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 cpos) by exact (ew_Ereg_extra regs extra 0).
  assert (E33 : ew E 33 = Z_to_bv 64 n) by exact (ew_Ereg_extra regs extra 1).
  assert (E34 : ew E 34 = Z_to_bv 64 cval) by exact (ew_Ereg_extra regs extra 2).
  assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
  assert (Uf : bv_unsigned (ew E 10) = f) by (rewrite E10; apply unsigned_lit_small; lia).
  (* the two guards, SIGNED, from p <= cpos <= n < 2^63 *)
  assert (G1 : Sg E (SOff 11 0) = p - cpos).
  { rewrite S_SOff, E11, unsigned_lit, Z.add_0_r, zcanon_wrap, bv_swrap_wrap'. apply swrap64_id. unfold half64. lia. }
  assert (G1b : Sg E (SAlu ALU_SUB (SLit 0) (SOff 32 0)) = - cpos).
  { rewrite S_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SOff, E32, unsigned_lit, Z.add_0_r.
    unfold zcanon, M64. rewrite Z.mod_mod by lia. rewrite (Z.mod_small cpos) by lia. rewrite Z.mod_0_l by lia.
    replace (0 - cpos) with (- cpos) by lia. apply swrap64_id. unfold half64. lia. }
  assert (G2 : Sg E (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit (-1))) (SOff 33 0)) = n - cpos).
  { rewrite S_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, !U_SOff, E32, E33, !unsigned_lit, !Z.add_0_r.
    rewrite <- (swrap64_id (n - cpos)) by (unfold half64; lia). apply wms_swrap_congr.
    unfold zcanon, M64. rewrite !Z.mod_mod by lia. rewrite (Z.mod_small cpos), (Z.mod_small n) by lia.
    rewrite Z.add_mod_idemp_l by lia. change ((-1) mod 2 ^ 64) with 18446744073709551615.
    replace (cpos * 18446744073709551615 + n) with ((n - cpos) + cpos * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  (* the entry state *)
  assert (HS : st_ok msegs E ss_ms (restrict (w_H W) (mkst regs (Z_to_bv 64 PMSEEK) mem (seg_rom msegs)))).
  { rewrite restrict_mkst_fx. unfold ss_ms. apply (entry_st_ok_full msegs); fold E.
    - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact H12].
    - vm_compute. reflexivity.
    - unfold R_stk, R_file, R_got, R_can. repeat apply Forall_cons; try apply Forall_nil.
      + apply (region_ok_stack msegs E _ 2 sp0 (-48) Usp); [lia | lia |].
        intros a Ha. apply (apresent_writable msegs). apply Hpres. lia.
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Uf. split; [lia|]. split; [lia|]. split.
        { intros o Ho. apply (apresent_writable msegs). apply (proj1 (Hfpres (f + o) ltac:(lia))). }
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val msegs E _ f 152 8 (SOff 10 232) (f + 232));
            [cbn [sv_denot]; rewrite Uf; reflexivity | cbn; lia | cbn; lia | exact S152].
        * apply (chunk_ok_val msegs E _ f 232 8 (SOff 32 0) cpos);
            [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact Hcpv].
        * apply (chunk_ok_val msegs E _ f 240 8 (SOff 33 0) n);
            [cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact S240].
        * apply (chunk_ok_val msegs E _ f 248 8 (SOff 33 0) n);
            [cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact S248].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val msegs E _ 0 (symaddr (Symbols.Asan.Sec.s_got + 0xce8)%Z) 8 (SLit (symaddr Symbols.Asan.s___stack_chk_guard)) (symaddr Symbols.Asan.s___stack_chk_guard));
          [reflexivity | cbn; lia | cbn; lia | exact (wms_can_got ly S W mem md HAR)].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val msegs E _ 0 (symaddr Symbols.Asan.s___stack_chk_guard) 8 (SOff 34 0) cval);
          [cbn [sv_denot]; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact Hcv].
    - apply pairwise_disjoint_of_extents. unfold R_stk, R_file, R_got, R_can, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uf.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; [|exact I]].
      + cbn [ms_atoms atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite Usp, Uf, E32, E33, !unsigned_lit_small by lia.
        change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
      + cbn [f_conds conds_ok acond_ok ms_c1 ms_c2 ac_c ac_a ac_b]. split; [|split; [|exact I]].
        * apply wms_bge.
          change (Sg E (SAlu ALU_SUB (SLit 0) (SOff 32 0)) <= Sg E (SOff 11 0)). rewrite G1, G1b. lia.
        * apply wms_bge.
          change (Sg E (SOff 11 0) <= Sg E (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit (-1))) (SOff 33 0))).
          rewrite G1, G2. lia. }
  pose proof (@ajournal_init _ SK msegs B PMSEEK_STK (asource_fp f) ly S W regs mem md ch HPRE) as HJ.
  unfold cfg_at. change (w64 PMSEEK) with (Z_to_bv 64 PMSEEK).
  clearbody E.
  (* the run: 0x8ec28 .. the ret at 0x8ecb0, straight through *)
  eapply (@SRr_run_to_AJ _ _ SK msegs B LAWS Hsegs mtbl mtbl_ok Hwx W FUEL (symaddr (Symbols.Asan.s_mseek + 0x88)%Z) E ss_ms ss_end RS_running
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS ms_run I HJ).
  { unfold ss_ms, R_stk, R_file, R_got, R_can. cbn [ss_mem].
    eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact Usp | cbn; unfold PMSEEK_STK; lia | cbn; lia |].
    eapply awr_ok_cons_block with (n := 10%nat) (b := f) (m := SRC_FILE_BLOCK);
      [reflexivity | exact Uf | exact Hblk | cbn; lia | cbn; rewrite ?RQ; unfold SRC_FILE_BLOCK; lia | |].
    { intros a Ha. cbn in Ha. exists (f, f + SRC_FILE_BLOCK). split; [left; reflexivity | cbn; unfold SRC_FILE_BLOCK; lia]. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  intros ms1 mat1 HS1 HJ1 HF1 HFr1 HG1. cbn [ms_mem mkst] in HF1, HFr1, HG1, HJ1.
  (* what the run left *)
  assert (Hnw : forall a, ~ (sp0 - 48 <= a < sp0) -> ~ (f + 232 <= a < f + 240) -> ~ in_wrange E (ss_mem ss_ms) a).
  { intros a Ha1 Ha2 (r & Hin & Hr). unfold ss_ms, R_stk, R_file, R_got, R_can in Hin. cbn [ss_mem In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?Usp, ?Uf in Hr; lia. }
  assert (Dp : sv_denot E (SAlu ALU_ADD (SOff 11 0) (SOff 32 0)) = Z_to_bv 64 p).
  { rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, E11, E32, !unsigned_lit, !Z.add_0_r.
    unfold zcanon, M64. rewrite !Z.mod_mod by lia. rewrite (Z.mod_small cpos) by lia.
    rewrite Z.add_mod_idemp_l by lia. replace (p - cpos + cpos) with p by lia. apply Z.mod_small. lia. }
  rget HS1 (10%bv : bv 5) Ra0. rewrite Dp in Ra0.
  rget HS1 (1%bv : bv 5) Rra. cbn [sv_denot] in Rra. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E1 in Rra.
  pose proof (st_ok_mem_ok msegs E ss_end _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
  lazymatch type of Hrs with Forall _ (ss_mem ?s) =>
    let l := eval vm_compute in (ss_mem s) in change (ss_mem s) with l in Hrs end.
  pose proof (Forall_inv (Forall_inv_tail Hrs)) as HR1. unfold region_ok in HR1.
  cbn [YP09.r_base YP09.r_chunks base_val] in HR1. destruct HR1 as (_ & _ & _ & Hcs).
  pose proof (Forall_inv Hcs) as Hck. rewrite Uf in Hck.
  pose proof (val_of_chunk_ok msegs E _ f 232 8 (SAlu ALU_ADD (SOff 11 0) (SOff 32 0)) p Hck Dp ltac:(cbn; lia) ltac:(cbn; lia))
    as Hcookie.
  assert (KV : forall a (k : nat) v, 0x10000 <= a -> a + Z.of_nat k <= (symaddr ImgPages.Asan.top) ->
    val_mem msegs (rd W mem) a k v -> val_mem msegs (rd W (ms_mem ms1)) a k v).
  { intros a k v Ha1 Ha2 Hv. apply (wms_val_mem_kept msegs E (ss_mem ss_ms) _ _ a k v HFr1); [|exact Hv].
    intros i Hi. split; [lia|]. apply Hnw; lia. }
  assert (KG : forall a l, 0x10000 <= a -> a + Z.of_nat (length l) <= (symaddr ImgPages.Asan.top) ->
    garr8 msegs (rd W mem) a l -> garr8 msegs (rd W (ms_mem ms1)) a l).
  { intros a l Ha1 Ha2 Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr]. apply KV; [lia | lia | exact Hv]. }
  (* the ret *)
  eapply (SRr_ret_at msegs mtbl mtbl_ok Hwx W E ss_end ms1 _ _ HS1 eq_refl); [vm_compute; reflexivity|].
  intros mat2. cbv beta.
  do 3 eexists. split.
  { rewrite Rra, Hra. reflexivity. }
  split; [apply (@ajournal_materialize _ SK msegs B LAWS Hsegs); exact HJ1|].
  split; [exact (aregs_preserved_of_st_ok msegs _ _ _ _ regs extra HS1 HAE ltac:(vm_compute; reflexivity))|].
  split; [exact Ra0|].
  split; [exact Hcookie|].
  split.
  { intros k Hk Hnk. unfold SRC_FILE_BLOCK, SRC_COOKIE_OFF in Hk, Hnk.
    apply (wms_mbyte_kept msegs E (ss_mem ss_ms) _ _ (f + k) HFr1); [lia|].
    apply Hnw; lia. }
  split.
  { intros j Hj. destruct (Hgarr j Hj) as [Hv Hr]. split; [|exact Hr].
    apply (wms_val_mem_kept msegs E (ss_mem ss_ms) _ _ _ _ _ HFr1); [|exact Hv].
    intros i Hi. assert (Hjn : Z.of_nat j < n) by (unfold n; lia). split; [lia|].
    apply Hnw; unfold SRC_FILE_BLOCK in Hfb; lia. }
  split.
  { unfold asrc_stdio_env.
    split; [apply KV; [kc | kc | exact Ethr]|].
    split; [apply KV; [kc | kc | exact Enl]|].
    split; [apply KV; [kc | kc | exact Elk]|].
    split; [apply KG; [kc | kc | exact Emode]|].
    split; [apply KG; [kc | kc | exact Emset]|].
    exists cval. split; [exact Hcvr | apply KV; [kc | kc | exact Hcv]]. }
  split.
  { apply KV; [kc | kc | exact Hhead]. }
  destruct (wms_wvb_io (with_vm_backing (m_vm_lazy md) mat1 md) mat2) as [A1 A2].
  destruct (wms_wvb_io md mat1) as [A3 A4].
  split; congruence.
Qed.

End W.

(* GUARD: SK stays explicit; the theorem takes it by position. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) =>
  pcap_amseek_rewind (fx:=fx) (rc:=rc) SK).

(* mseek is the pointer the FILE carries: asource_at pins +80 to as_seek K, and for pcap's measured
   symbol record that pointer IS the address proved here. *)
Lemma pcap_KS_seek : as_seek pcap_KS = PMSEEK.
Proof. reflexivity. Qed.

Print Assumptions pcap_amseek_rewind.
