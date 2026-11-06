(* The pieces the HEAD segment of the image-A walk of LLVMFuzzerTestOneInput shares (0x80abc-0x80c30,
   lib/A/Prog/codec_amain_inv.v seg_head): the cuts inside the segment, the arithmetic of the op byte
   (op mod 15 and op / 15 mod 3 as the multiply-shift forms of 0x80b60-0x80b9c compute them), the two calls of
   the runtime's checked memset (0x80b5c and 0x80c08) and the call of diginet_personality_of (0x80bc4) as steps
   from one cut to the next, and the small memory facts the record needs. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgEncC CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalk CPgWalkImg CPgWalkIntr CPgWalkKept CPgWalkFrame CPgWalkCall.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_encl codec_amain_head_cut codec_amain_heada.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ bytes that are zero ================================ *)
Lemma hd_le_byte_0 : forall w k, YO0f.le_byte 0 w k = 0.
Proof.
intros w k. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma hd_nth_repeat : forall (v : Z) (n j : nat), (j < n)%nat -> nth j (repeat v n) 0 = v.
Proof.
intros v n. induction n as [|n IH]; intros j Hj; [lia|].
cbn [repeat]. destruct j as [|j]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma hd_val_zero : forall (W : world tfibsegs) mem q (n : nat),
(forall i, 0 <= i < Z.of_nat n -> aview tfibsegs (w_H W) mem (q + i) = Some 0) ->
val_mem tfibsegs (mrestrict (w_H W) mem) q n 0.
Proof.
intros W mem q n H j Hj.
destruct (am_mb W mem (q + Z.of_nat j) 0 (H (Z.of_nat j) ltac:(lia))) as (Hm & _).
rewrite Hm, hd_le_byte_0. reflexivity.
Qed.
Lemma hd_garr8_val : forall (W : world tfibsegs) mem q (n : nat) v,
(forall i, 0 <= i < Z.of_nat n -> aview tfibsegs (w_H W) mem (q + i) = Some v) -> 0 <= v < 256 ->
garr8 tfibsegs (mrestrict (w_H W) mem) q (repeat v n).
Proof.
intros W mem q n v H Hv j Hj. rewrite repeat_length in Hj.
rewrite (hd_nth_repeat v n j Hj). split; [|exact Hv].
destruct (am_mb W mem (q + Z.of_nat j) v (H (Z.of_nat j) ltac:(lia))) as (Hm & _).
apply cpg_val_mem1; [exact Hv | exact Hm].
Qed.
Lemma hd_garr8_zero : forall (W : world tfibsegs) mem q (n : nat),
(forall i, 0 <= i < Z.of_nat n -> aview tfibsegs (w_H W) mem (q + i) = Some 0) ->
garr8 tfibsegs (mrestrict (w_H W) mem) q (repeat 0 n).
Proof. intros W mem q n H. apply (hd_garr8_val W mem q n 0 H ltac:(lia)). Qed.
End z.

(* ================================ the two calls inside HEAD ================================ *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section n.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws tfibsegs B.

(* a byte of the entry's own frame is none of the image's *)
Lemma hd_frame_not_img : forall pos F ly2 S2 (W2 : world tfibsegs) mem2 md2 a,
AR tfibsegs B ly2 S2 W2 mem2 md2 -> In (3, pos) (frames S2) -> frame_addr ly2 3 pos = F ->
F <= a < F + 512 -> in_img tfibsegs a -> False.
Proof using LAWS.
intros pos F ly2 S2 W2 mem2 md2 a HAR Hin EFA Ha Him.
pose proof (al_client_img _ _ LAWS ly2 S2 W2 mem2 md2 a HAR) as Hc.
apply Hc; [|exact Him]. right. left. exists 3, pos. split; [exact Hin|].
unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia.
Qed.

Lemma hd_hull_arith : forall F off n s,
F mod 64 = 0 -> 0 <= off -> 0 < n -> off + n <= 448 ->
(SHADOW_OFF + (F + off) / 8) / 8 * 8 <= s < (SHADOW_OFF + (F + off + n - 1) / 8) / 8 * 8 + 8 ->
0 <= s - (SHADOW_OFF + F / 8) < 56.
Proof.
intros F off n s H64 Hoff Hn Hon Hs.
assert (D64 : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)) as D; lia).
assert (E8 : F / 8 = 8 * (F / 64)).
{ rewrite D64 at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z.div_mul. lia. }
assert (DF : forall m, (F + m) / 8 = F / 8 + m / 8).
{ intros m. replace (F + m) with ((F / 8) * 8 + m) by lia. apply Z.div_add_l. lia. }
set (q := 268431360 + F / 64).
assert (EA : SHADOW_OFF + F / 8 = 8 * q) by (unfold q, SHADOW_OFF; lia).
rewrite (DF off) in Hs.
replace (F + off + n - 1) with (F + (off + n - 1)) in Hs by lia.
rewrite (DF (off + n - 1)) in Hs.
replace (SHADOW_OFF + (F / 8 + off / 8)) with (8 * q + off / 8) in Hs by lia.
replace (SHADOW_OFF + (F / 8 + (off + n - 1) / 8)) with (8 * q + (off + n - 1) / 8) in Hs by lia.
assert (R1 : (8 * q + off / 8) / 8 = q + off / 8 / 8)
  by (rewrite (Z.mul_comm 8 q); apply Z.div_add_l; lia).
assert (R2 : (8 * q + (off + n - 1) / 8) / 8 = q + (off + n - 1) / 8 / 8)
  by (rewrite (Z.mul_comm 8 q); apply Z.div_add_l; lia).
rewrite R1, R2 in Hs.
assert (P1 : 0 <= off / 8) by (apply Z.div_pos; lia).
assert (P2 : 0 <= off / 8 / 8) by (apply Z.div_pos; lia).
assert (P3 : 0 <= (off + n - 1) / 8) by (apply Z.div_pos; lia).
pose proof (Z.div_le_mono (off + n - 1) 447 8 ltac:(lia) ltac:(lia)) as A2.
change (447 / 8) with 55 in A2.
pose proof (Z.div_le_mono ((off + n - 1) / 8) 55 8 ltac:(lia) ltac:(lia)) as A3.
change (55 / 8) with 6 in A3.
lia.
Qed.

(* the shadow bytes of a range of the frame are readable (the cut's 56 shadow bytes cover their 8-byte hull) *)
Lemma hd_hull : forall B0 MT0 K0 XM0 g pos sp1 kv ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2 off n,
mcommon B0 MT0 K0 XM0 g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
0 <= off -> 0 < n -> off + n <= 448 ->
shadow_hull_vis (aview tfibsegs (w_H W2) mem2) (FA g pos + off) n.
Proof using.
intros B0 MT0 K0 XM0 g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 off n HC Hoff Hn Hon.
pose proof HC as HF64. do 14 (destruct HF64 as (_ & HF64)). destruct HF64 as (HF64 & _).
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
intros s Hs. unfold shadow_addr in Hs.
pose proof (hd_hull_arith (FA g pos) off n s HF64 Hoff Hn Hon Hs) as Hi.
replace s with (shadow_addr (FA g pos) + (s - (SHADOW_OFF + FA g pos / 8))) by (unfold shadow_addr; lia).
rewrite (HSH' (s - (SHADOW_OFF + FA g pos / 8)) Hi).
discriminate.
Qed.

(* ---- the checked memset of a range of the frame (0x80b5c and 0x80c08) ---- *)
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet CA_MEMSET.
Lemma hd_memset_at : forall (Q : world tfibsegs -> config -> Prop) g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 c off n x retpc,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 0 ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
cur_at g sp1 c W2 mem2 ->
getr regs2 10 = w64 (FA g pos + off) -> getr regs2 11 = w64 x -> getr regs2 12 = w64 n ->
0 <= x < 2 ^ 64 -> 0 < n < 2 ^ 32 -> 176 <= off -> off + n <= 360 ->
getr regs2 1 = w64 retpc -> YK0s.ret_ok (w64 retpc) -> 0 <= retpc < 2 ^ 64 ->
range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (FA g pos + off) n ->
(forall regs3 mem3 md3,
 ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem3 md3 0 ->
 mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs3 mem3 md3 ->
 cur_at g sp1 c W2 mem3 ->
 aregs_preserved regs2 regs3 ->
 (forall i, 0 <= i < n -> aview tfibsegs (w_H W2) mem3 (FA g pos + off + i) = Some (x mod 256)) ->
 (forall a, FA g pos <= a < FA g pos + 512 -> ~ (FA g pos + off <= a < FA g pos + off + n) ->
    aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
 SRr tfibsegs W2 (cfg_at tfibsegs retpc regs3 mem3 md3) Q) ->
SRr tfibsegs W2 (cfg_at tfibsegs CA_MEMSET regs2 mem2 md2) Q.
Proof using LAWS AMEMSET.
intros Q g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 c off n x retpc
  HJ Hfr HC Hcur H10 H11 H12 Hx Hn Hoff Hon H1 Hret Hretr HBS CONT.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 0 HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & Hblk).
unfold AM_HI in Hchi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Happ).
rewrite EFA in Happ. change (fs_frame_bytes 3) with 512 in Happ.
pose proof HC as (_ & _ & R2 & _ & _ & R3 & R4 & _).
assert (Usp : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hamr : amem_range (FA g pos + off) n).
{ unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. destruct Happ as (_ & [Hlo | (Hh1 & Hh2)]); [left; lia | right; lia]. }
unfold cfg_at. change (w64 CA_MEMSET) with (Z_to_bv 64 CA_MEMSET).
eapply SRr_bind.
{ eapply (aj_intrin_atS tfibsegs B LAWS tfib_segs_low OSet CA_MEMSET AMEMSET W2 regs2 mem2 LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 md2 0 (FA g pos + off) x n (sp1 - e_sp0 g) (w64 retpc)).
  - exact HJ.
  - exact H10.
  - exact H11.
  - exact H12.
  - lia.
  - lia.
  - lia.
  - rewrite Usp. lia.
  - assert (H16 : sp1 mod 16 = 0).
    { pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D.
      replace sp1 with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
    rewrite Zminus_mod, Hsp016, H16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - exact R3.
  - exact R4.
  - exact H1.
  - exact Hret.
  - intros a Ha. split.
    + right. right. right. exists 3, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia.
    + replace (e_sp0 g + (sp1 - e_sp0 g)) with sp1 by lia. unfold ESTACK. lia.
  - exact Hamr.
  - exact HBS.
  - intros _. exact (hd_hull B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 off n HC ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact I. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HPR & Ha0 & Hset & Hkeep & Hpres2 & Hsame).
replace (e_sp0 g + (sp1 - e_sp0 g)) with sp1 in Hkeep by lia.
(* what the call kept, in the walk's form *)
assert (KT0 : tcj_kept tfibsegs B 4096 ly2 S2 W2 mem2 W2 mem2 sp1 (fun a => FA g pos + off <= a < FA g pos + off + n))
  by exact (cw_kept0 B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
              ly2 S2 W2 mem2 md2 0 sp1 4096 _ HJ ltac:(lia) ltac:(lia)).
assert (KT : tcj_kept tfibsegs B 4096 ly2 S2 W2 mem2 W2 mem3 sp1 (fun a => FA g pos + off <= a < FA g pos + off + n)).
{ apply (cw_kept_step B LAWS 4096 ly2 S2 W2 mem2 md2 W2 mem2 mem3 sp1 _
    (fun a => (FA g pos + off <= a < FA g pos + off + n) \/ (sp1 - ESTACK <= a < sp1))
    ltac:(unfold ESTACK; lia) HAR KT0).
  - intros a Ha Hz. apply Hkeep; [exact Ha | intros X; apply Hz; left; exact X | intros X; apply Hz; right; exact X].
  - intros a [Ha | Ha]; [right; left; split; [exact Ha|] | left; unfold ESTACK in Ha; lia].
    intros Him. exact (hd_frame_not_img pos (FA g pos) ly2 S2 W2 mem2 md2 a HAR Hin EFA ltac:(lia) Him).
  - exact Hpres2. }
rewrite <- Usp in KT.
destruct (am_call_kept B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 0 c 4096
  (fun a => FA g pos + off <= a < FA g pos + off + n) ly2 S2 W2 regs3 mem3 md3 0
  HJ Hfr HC Hcur ltac:(intros a Ha; cbv beta in Ha; lia) HJ3 HPR (Permutation_refl _) KT) as (HC3 & Hcur3 & KF).
apply (CONT regs3 mem3 md3 HJ3 HC3 Hcur3 HPR).
- intros i Hi. replace (FA g pos + off + i) with (FA g pos + off + i) by lia. exact (Hset i Hi).
- intros a Ha Hna. exact (KF a Ha Hna).
Qed.

(* ---- the call of diginet_personality_of (0x80bc4) ---- *)
Hypothesis POF : cdc_pers_of_specX tfibsegs B MT AM_pers_of CA_PERS.
Lemma hd_pof_at : forall (Q : world tfibsegs -> config -> Prop) g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 c d retpc,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 0 ->
frames S2 = [(3, pos)] -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
cur_at g sp1 c W2 mem2 ->
getr regs2 10 = w64 d -> 0 <= d < 2 ^ 64 ->
getr regs2 1 = w64 retpc -> YK0s.ret_ok (w64 retpc) -> 4096 <= retpc < 2 ^ 64 ->
(forall (W3 : world tfibsegs) ly3 S3 regs3 mem3 md3,
 ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 0 ->
 frames S3 = [(3, pos)] -> mo_le MT (e_S g) S3 0 ->
 mcommon B MT K XM_LIB g pos sp1 kv ly3 S3 W3 regs3 mem3 md3 ->
 cur_at g sp1 c W3 mem3 ->
 aregs_preserved regs2 regs3 ->
 getr regs3 10 = w64 (pers_ofA CA_PERS d) ->
 (forall a, FA g pos <= a < FA g pos + 512 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
 SRr tfibsegs W3 (cfg_at tfibsegs retpc regs3 mem3 md3) Q) ->
SRr tfibsegs W2 (cfg_at tfibsegs AM_pers_of regs2 mem2 md2) Q.
Proof using MTL LAWS POF.
intros Q g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 c d retpc HJ Hfr Hmo HC Hcur H10 Hd H1 Hret Hretr CONT.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 0 HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & Hblk).
unfold AM_HI in Hchi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as (Hpre & _ & R2 & _ & _ & R3 & R4 & _).
pose proof HC as HPerm0. do 45 (destruct HPerm0 as (_ & HPerm0)).
assert (Usp : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hal16 : spZ regs2 mod 16 = 0).
{ rewrite Usp. pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D.
  replace sp1 with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
pose proof Hpre as HPRE. unfold e_pre, codec_lib_pre_x in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & Hlive & _).
assert (HENT : cdc_entry tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(3, pos)] ly2 S2 W2 mem2 md2 0 regs2 T_pers_of).
{ eapply (cpw_entry B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
    (e_ly g) (e_S g) ly2 S2 W2 mem2 md2 0 regs2 T_pers_of HJ).
  - rewrite H1. exact Hret.
  - unfold raZ. rewrite H1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact R3.
  - exact R4.
  - exact Hal16.
  - rewrite Usp. unfold T_pers_of. lia.
  - rewrite Usp. lia.
  - unfold EV_CDC. unfold EV_LIB in Hev. lia.
  - exact HPerm0.
  - unfold LIVE_CDC. unfold LIVE_LIB in Hlive. lia. }
unfold cfg_at. change (w64 AM_pers_of) with (Z_to_bv 64 AM_pers_of).
eapply SRr_bind.
{ change (Z_to_bv 64 AM_pers_of) with (w64 AM_pers_of).
  exact (POF LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 0
           regs2 d HENT H10 Hd). }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HPR & Hfrs3 & HPerm3 & Hio3 & Hmo3 & KTc & HRc).
unfold EV_CDC in HJ3. rewrite Z.add_0_r in HJ3.
rewrite H1 in *.
assert (Hfr3 : frames S3 = [(3, pos)]) by (rewrite Hfrs3; exact Hfr).
destruct (am_call_kept B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 0 c T_pers_of
  cno_wr ly3 S3 W3 regs3 mem3 md3 0 HJ Hfr HC Hcur ltac:(intros a []) HJ3 HPR HPerm3 KTc) as (HC3 & Hcur3 & KF).
assert (Hmo3' : mo_le MT (e_S g) S3 0)
  by (pose proof (mle_station _ _ _ _ 0 0 MTL Hmo Hmo3) as X; rewrite Z.add_0_r in X; exact X).
change (mkCfg (mkst regs3 (w64 retpc) mem3 (seg_rom tfibsegs)) md3)
  with (cfg_at tfibsegs retpc regs3 mem3 md3).
apply (CONT W3 ly3 S3 regs3 mem3 md3 HJ3 Hfr3 Hmo3' HC3 Hcur3 HPR HRc).
intros a Ha. exact (KF a Ha ltac:(intros [])).
Qed.
End n.
End m.
