(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* LLVMFuzzerTestOneInput_seg_entry: two of the nine segment statements of lib/A/Prog/LLVMFuzzerTestOneInput_segs.v.

   llvm_a_entry_ok : llvm_a_entry_stmt. The 29 instructions +0x000..+0x070 of DecodeList.v:28-56, stepped by the
   Pa engine from the slot pre: the frame (addi sp,sp,-224 and the probe store), the 13 callee saves, s0, the
   32-byte realign of sp into s1, the size and data pointers into s4 / s8, the two GOT words of the use-after-return
   flag and of the shadow base (objects 0 and 1) and the two cells they point at (objects 14 and 13), the `beqz a2`
   at +0x068 (never taken: the flag cell holds 1, a constant cell of B by dec_crt_cells), `li a0,64`, and the
   `jal __asan_stack_malloc_0` at +0x070, discharged by the statement's class-0 astack_malloc_realizes premise at
   the pc the premise pc_stack_malloc (as_code B) 0 = decode_sigma DS___asan_stack_malloc_0 gives.

   The call is composed into the walk's journal by sm_call below: YC85.v's aj_stack_malloc_atS with its journal
   step call_effect_journal (YCbq.v) restated for the stack malloc's own memory clause, which names no errno byte,
   so that api_env (which the entry statement does not carry) is not needed.

   llvm_a_early_ret_ok : llvm_a_early_ret_stmt. The +0x104 edge is unreachable: dec_a_base bounds n below 2 ^ 26
   (LLVMFuzzerTestOneInput_cg.v:107) and llvm_a_st_104 asks 2 ^ 26 <= n. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
  DecodeSyms DecodeList DecodeAddr DecodePa DecodePaLib DecodeImg YC4b YC1g YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import check_round_trip_cg LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI16.
Module DCells := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.AsanCells.
(* YC4b switches lia's division handling off for its importers; this file's arithmetic needs it (ReadName.v's line). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. Arithmetic and memory helpers                                     *)
(* ------------------------------------------------------------------ *)

(* GrantACja.v land_m32 / denot_and_m32 / sp1_facts: `andi sp,sp,-32` on a symbolic sp. *)
Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
(* CtrlStampHeadamp.v denot_and_m32_add0: `mv s1,sp` right after the realign. *)
Lemma denot_and_m32_add0 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit (-32))) (SLit 0)) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv.
assert (Hq : 0 <= 32 * ((v + c) / 32) < 2 ^ 64).
{ split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
  pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia. }
rewrite denot_lit_U. f_equal.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia.
rewrite (zcanon_id (32 * ((v + c) / 32))) by (unfold M64; lia).
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma sp1_facts : forall x, 0 <= x -> x mod 16 = 0 -> x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Section mh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* GrantFrame.v val_mem_of_rd32 / rdword_of_val_mem / val_mem_moved. *)
Lemma val_mem_of_rd32 : forall segs H mem a v,
rd32 (aview segs H mem) a v -> val_mem segs (mrestrict H mem) a 4 v.
Proof.
intros segs H mem a v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma rdword_of_val_mem : forall segs H mem a v,
val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
Lemma val_mem_moved : forall segs H H' (m m' : word -> option byte) a b n v,
(forall k, 0 <= k < Z.of_nat n -> aview segs H' m' (b + k) = aview segs H m (a + k)) ->
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') b n v.
Proof.
intros segs H H' m m' a b n v Hk Hv k Hkn. specialize (Hk (Z.of_nat k) ltac:(lia)). unfold aview in Hk.
rewrite (Hv k Hkn) in Hk. destruct (mbyte segs (mrestrict H' m') (b + Z.of_nat k)) as [b'|]; cbn in Hk; [|discriminate].
injection Hk as Hk. f_equal. apply bv_eq. exact Hk.
Qed.
(* A byte array is kept where every one of its bytes is. *)
Lemma garr8_kept : forall segs H H' (m m' : word -> option byte) base l,
(forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' m' (base + j) = aview segs H m (base + j)) ->
garr8 segs (mrestrict H m) base l -> garr8 segs (mrestrict H' m') base l.
Proof.
intros segs H H' m m' base l HK HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (base + Z.of_nat j) (base + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk. replace (base + Z.of_nat j + k) with (base + (Z.of_nat j + k)) by lia. apply HK. lia.
Qed.
(* A word is read the same where its eight bytes are. *)
Lemma rdword_kept : forall (r r' : reader) a, (forall i, 0 <= i < 8 -> r' (a + i) = r (a + i)) -> rdword r' a = rdword r a.
Proof.
intros r r' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
(* A saved register's word in a region of the symbolic state. *)
Lemma saved_slot : forall segs E m n cs lo hi wlo whi off (r : nat) b,
region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk off (CVal 8 (SOff r 0))) cs ->
val_mem segs m (b + off) 8 (bv_unsigned (ew E r)).
Proof.
intros segs E m n cs lo hi wlo whi off r b HR Hb Hc.
pose proof (bv_unsigned_in_range 64 (ew E r)) as Hrg. change (bv_modulus 64) with (2 ^ 64) in Hrg.
exact (field_of_region E m n b cs lo hi wlo whi off 8 (SOff r 0) (bv_unsigned (ew E r)) HR Hb Hc
  ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
End mh.

(* ------------------------------------------------------------------ *)
(* 2. The class-0 stack malloc composed into the caller's journal       *)
(* ------------------------------------------------------------------ *)

Section sm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
(* lib/Reusable/YCbq.v call_effect_journal, for a call whose memory clause is astack_malloc_realizes': it may change
   only owned bytes and its own stack window, never a heap block, and names no errno byte. *)
Lemma sm_effect_journal : forall stk lyc Sc W regs memc mdc ly2 S2 W2 mem2 md2 nf k1,
AR segs B ly2 S2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 -> wle W W2 -> same_io mdc md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ (spZ regs - stk <= a < spZ regs) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W2) mem2 a) ->
AR segs B lyc Sc W memc mdc ->
astk_ok stk lyc (spZ regs) ->
frames S2 = nf ++ frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
(length (st_secs Sc) <= length (st_secs S2))%nat ->
(forall p n, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2)) ->
qtight S2 ->
ajournal segs B stk (spZ regs) [] lyc Sc W memc mdc nf ly2 S2 W2 mem2 md2 k1.
Proof.
intros stk lyc Sc W regs memc mdc ly2 S2 W2 mem2 md2 nf k1
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs Hkeep HQT2.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
assert (KEEP : forall a, ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a ->
~ (spZ regs - stk <= a < spZ regs) -> 0 <= a < 2 ^ 64 ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a H1 H2 H3 H6. exact (Hfr a H6 H1 H2 H3). }
assert (BLK : forall b m a, In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2) -> b <= a < b + req_size m ->
app_addr a).
{ intros b m a [Hb|Hb] Hr.
- destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & _ & Hc & [Hh Hh2] & _). zlia.
- destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hb) as (_ & _ & Hc & [Hh Hh2] & _). zlia. }
split; [exact HAR2|]. split; [exact Hly2|]. split; [exact Hsecs|]. split; [exact Hwle2|]. split; [apply aos_step_of_same_io, Hio2|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk1|].
split.
{   intros a Ha Hs. apply KEEP.
- intros Ho. pose proof (al_owned_low _ _ LAWS _ _ _ _ _ a HAR Ho). zlia.
- intros Ho. pose proof (al_owned_low _ _ LAWS _ _ _ _ _ a HAR2 Ho). zlia.
- exact Hs.
- zlia. }
split.
{   intros p n i H1 H2 Hi Hnf. apply KEEP.
- exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc W memc mdc p n HAR H1))))) (p + i) ltac:(zlia))).
- exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 H2))))) (p + i) ltac:(zlia))).
- pose proof (BLK p n (p + i) (or_introl H1) ltac:(zlia)). zlia.
- pose proof (BLK p n (p + i) (or_introl H1) ltac:(zlia)). pose proof asan_consts. zlia. }
split.
{   intros a Hi Hns He _. pose proof (segs_low a Hi). apply KEEP.
- intros Ho. exact (Hns (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR Hi) Ho)).
- intros Ho. exact (Hns (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR2 Hi) Ho)).
- zlia.
- zlia. }
split.
{   intros cid pos a Hin Hr Hnf.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (_ & [Hh1 Hh2] & Hb & Hsh).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (_ & _ & Hb2 & Hsh2). rewrite Efa in Hb2, Hsh2.
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
apply KEEP.
- destruct Hr as [Hr|Hr]; [exact (proj2 (Hb a Hr))|].
specialize (Hsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh by zlia. exact (proj2 Hsh).
- destruct Hr as [Hr|Hr]; [exact (proj2 (Hb2 a Hr))|].
specialize (Hsh2 (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh2 by zlia. exact (proj2 Hsh2).
- destruct Hr as [Hr|Hr]; zlia.
- destruct Hr as [Hr|Hr].
  + clear -Hr Hf0 Hfc C1. lia.
  + destruct Hsb2 as [_ Hsb2b]. destruct Hsb1 as [Hsb1a _].
    assert (Hlt : shadow_addr (frame_addr lyc cid pos + fs_frame_bytes cid) < kHighMemBeg) by (apply Hsb2b; rewrite C4; lia).
    rewrite C3 in Hlt. unfold SHADOW_OFF in Hsb1a. clear -Hr Hse Hlt Hsb1a. lia. }
split; [intros p n i H1 H2 Hi; exfalso; exact (H2 (Hkeep p n H1))|].
split; [exact Hpres2|]. split; [exact Hstk|]. split; [|exact HQT2].
{   intros a HXa He.
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
pose proof (AR_extra_law_ok segs B lyc Sc W memc mdc a HAR HXa) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
pose proof (AR_extra_law_ok segs B ly2 S2 W2 mem2 md2 a HAR2 ltac:(rewrite Eextra; exact HXa)) as (Yo & Yb & _).
apply KEEP.
- exact Xo.
- exact Yo.
- intros Hs. apply Xs. zlia.
- unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp. zlia. }
Qed.
Hypothesis ML : model_laws (as_universe B).
Hypothesis stack_malloc_progress : stack_malloc_progressP B.
Local Abbreviation code := (as_code B).
(* lib/A/Prog/YC85.v aj_stack_malloc_atS with sm_effect_journal for its journal step; the post also keeps the
   frame's presence, which the astack_malloc_realizes post gives. *)
Lemma sm_call : forall cid, astack_malloc_realizes segs B cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc code cid)) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\
zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
(forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> apresent (w_H W) mem2 a) /\
acall_kept segs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) /\
(exists f, S2 = set_fs f Sc)).
Proof.
intros cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (stack_malloc_progress Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
pose proof (ml_stack_malloc _ ML Sc cid HWF Hcid) as HTOK.
destruct (atok_apath _ _ _ [] (PFake cid pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal segs B ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
{ apply (sm_effect_journal ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2 [(cid, pos)] 0);
  [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | exact Hfr | exact Hpres2
  | exact HAR | exact HstkC | cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros p n Hp; rewrite Eab2; exact Hp |].
  rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|].
split; [exact Hz|]. split; [exact Hflag|]. split; [exact Hfpres|].
rewrite Hsp' in HJ1. split; [| exists f; exact ES2].
eapply (acall_kept_of_journal segs B segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.
End sm.

(* ------------------------------------------------------------------ *)
(* 3. The symbolic state at +0x000                                      *)
(* ------------------------------------------------------------------ *)

(* Atom 32 is the shadow base, the value of the shadow-base cell (object 13) the code reaches through its GOT word
   (object 1); object 14 is the use-after-return flag cell, reached through its GOT word (object 0), which holds 1
   in every state, so the `beqz a2` at +0x068 is never taken. The machine-stack region is the 224 bytes below the
   entry sp (atom 2) that the prologue writes. *)
Definition en_extra : list word := [Z_to_bv 64 SHADOW_OFF].
Definition uar_got_regionD : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 14) 0))].
Definition uar_cell_regionD : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 14)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition en_regions : smem := [stack_region 224; got_regionP; bcell_regionP 32; uar_got_regionD; uar_cell_regionD].
Definition en_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_en : sstate := mkSS AF_LLVMFuzzerTestOneInput sr_atoms en_regions None en_facts.
Ltac awr_ro_rec := first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]; awr_ro_rec ].

Section en. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation SEGS := (@pa_segs _ decode_listing PI_decode).
Local Abbreviation VAL := (@pa_val _ decode_listing PI_decode).
Local Abbreviation BASE := (@pa_val _ decode_listing PI_decode A_TEXT).
Definition EEN (regs : bvmap 5 word) : env := Eimg (PI := PI_decode) (Ereg regs en_extra).
Lemma en_vals : VAL (A_OBJ 0) = DCells.GOT_UAR /\ VAL (A_OBJ 1) = DCells.GOT_CELL_K /\
  VAL (A_OBJ 13) = DCells.CELL_K /\ VAL (A_OBJ 14) = DCells.UAR.
Proof. vm_compute. repeat split. Qed.
Lemma en_entry : forall (B : asyms) ly S (W : world SEGS) (regs : bvmap 5 word) mem md,
AR SEGS B ly S W mem md -> dec_crt_cells B ->
(forall a, spZ regs - 224 <= a < spZ regs -> apresent (w_H W) mem a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
st_ok_pi SEGS VAL (EEN regs) ss_en
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput)) mem (seg_rom SEGS))).
Proof.
intros B ly S W regs mem md HAR HCELLS Hpres Hsp Hsp16.
destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview SEGS (w_H W) mem) c).
{ intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
assert (Kcell : rdword (aview SEGS (w_H W) mem) DCells.CELL_K = Some DCells.ASAN_K)
  by (apply (rdword_cell B ly); [unfold DCells.ASAN_K; lia | exact (CH _ I1)]).
assert (Kgot : rdword (aview SEGS (w_H W) mem) DCells.GOT_CELL_K = Some DCells.CELL_K)
  by (apply (rdword_cell B ly); [unfold DCells.CELL_K; lia | exact (CH _ I2)]).
assert (Kguar : rdword (aview SEGS (w_H W) mem) DCells.GOT_UAR = Some DCells.UAR)
  by (apply (rdword_cell B ly); [unfold DCells.UAR; lia | exact (CH _ I7)]).
assert (Kuar : rd32 (aview SEGS (w_H W) mem) DCells.UAR 1).
{ pose proof (CH _ I6) as H6. unfold cell_holds in H6. cbn [c_at c_val c_w z4 c4 aeval] in H6. intros k Hk. exact (H6 k Hk). }
destruct en_vals as (V0 & V1 & V13 & V14).
rewrite restrict_mkst_fx. unfold ss_en.
set (E := EEN regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs en_extra) n)
by (intros n Hn; unfold E, EEN; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO : forall i, (i < 15)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
by (intros i Hi; unfold E, EEN; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (EO 0%nat ltac:(lia)) as E241. pose proof (EO 1%nat ltac:(lia)) as E242.
pose proof (EO 13%nat ltac:(lia)) as E254. pose proof (EO 14%nat ltac:(lia)) as E255.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
assert (R241 : 0 <= VAL (A_OBJ 0) < 2 ^ 47) by (rewrite V0; unfold DCells.GOT_UAR; lia).
assert (R242 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold DCells.GOT_CELL_K; lia).
assert (R254 : 0 <= VAL (A_OBJ 13) < 2 ^ 47) by (rewrite V13; unfold DCells.CELL_K; lia).
assert (R255 : 0 <= VAL (A_OBJ 14) < 2 ^ 47) by (rewrite V14; unfold DCells.UAR; lia).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold en_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionD, uar_cell_regionD.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 13) 0) (VAL (A_OBJ 13)));
    [cbn [sv_denot]; rewrite E254, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r, V1, V13. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 13) (VAL (A_OBJ 13)) E254) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 13)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_r, V13. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 14) 0) (VAL (A_OBJ 14)));
    [cbn [sv_denot]; rewrite E255, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r, V0, V14. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
  + rewrite (VB (A_OBJ 14) (VAL (A_OBJ 14)) E255) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 14)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
    rewrite Z.add_0_r, V14. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold en_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionD, uar_cell_regionD, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241), (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242),
  (VB (A_OBJ 13) (VAL (A_OBJ 13)) E254), (VB (A_OBJ 14) (VAL (A_OBJ 14)) E255) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite V0, V1, V13, V14. unfold DCells.GOT_UAR, DCells.GOT_CELL_K, DCells.CELL_K, DCells.UAR.
  repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]].
  cbn [en_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.
End en.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac reg_at HS r v H tac :=
  lazymatch type of HS with st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* One saved word of dec_a_saved: the run stored it in the machine-stack region HR0 (the chunk at -off holds atom r,
   the entry value of register r), and the stack malloc kept it (HKS). *)
Ltac saved_tac HR0 HKS EE Usp msv regsv W :=
  lazymatch goal with |- rdword _ (spZ regsv - ?off) = Some (bv_unsigned (getr regsv (Z_to_bv 5 ?r))) =>
    let rn := eval vm_compute in (Z.to_nat r) in
    rewrite (rdword_kept (aview decodesegs0 (w_H W) (ms_mem msv)) _ (spZ regsv - off))
      by (intros i Hi; apply HKS; lia);
    rewrite <- (EE rn (Z_to_bv 5 r) eq_refl);
    apply rdword_of_val_mem;
    [ replace (spZ regsv - off) with (spZ regsv + (- off)) by lia;
      eapply (saved_slot _ _ _ _ _ _ _ _ _ (- off) rn (spZ regsv) HR0 Usp);
      cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])
    | let w := fresh "w" in pose proof (bv_unsigned_in_range 64 (ew (EEN regsv) rn)) as w;
      change (bv_modulus 64) with (2 ^ 64) in w; exact w ]
  end.

(* ------------------------------------------------------------------ *)
(* 4. The two segment theorems                                          *)
(* ------------------------------------------------------------------ *)

Section sg. Context {rc : YM05.RunCeil}.
(* lib/A/Prog/LLVMFuzzerTestOneInput_segs.v Section seg, variable for variable (it has no Hypothesis; neither theorem
   uses its lemma HROM). *)
Local Abbreviation tfib_sink_head := dec_A_sink_head.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable asink_img_laws : list Segment -> asyms -> asink_syms -> Prop.
Variable ro_below_ofl : list Segment -> Z -> Z -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegs0.

(* Flatten every conjunction and existential in the context: the projections below pick each fact by its TYPE, so a
   conjunct added to the slot pre or to a cut-point predicate cannot shift what they bind (BUILD.md:149-165). *)
Local Ltac flat_ctx := repeat match goal with Hx : ex _ |- _ => destruct Hx | Hx : _ /\ _ |- _ => destruct Hx end.
(* The conjuncts of the slot pre (LLVMFuzzerTestOneInput_cg.v dec_lib_pre_x) that the two segments read. *)
Lemma dec_pre_parts : forall (fx : YK11.FPState) ly S (W : world segs) regs mem md p n pl M,
  @dec_lib_pre_x fx rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI
    regs ly S W mem md p n pl M ->
  @afn_pre rc segs B DEC_LLVMF_STK ly S W regs mem md [] /\
  getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
  ((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
  n = Z.of_nat (length pl) /\ garr8 segs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) /\
  frames S = [] /\ mo_ok MT S (XL n) /\ frm_zero (@fp_csr fx).
Proof.
intros fx ly S W regs mem md p n pl M HPRE. unfold dec_lib_pre_x in HPRE. flat_ctx.
repeat (split; [assumption|]). assumption.
Qed.
(* The conjuncts of afn_pre (lib/Reusable/YCbq.v:336) that the entry segment reads. *)
Lemma afn_parts : forall ly S (W : world segs) regs mem md,
  @afn_pre rc segs B DEC_LLVMF_STK ly S W regs mem md [] ->
  AR segs B ly S W mem md /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  astk_ok DEC_LLVMF_STK ly (spZ regs) /\
  (forall a, spZ regs - DEC_LLVMF_STK <= a < spZ regs -> apresent (w_H W) mem a).
Proof.
intros ly S W regs mem md HA. unfold afn_pre in HA. flat_ctx.
repeat (split; [assumption|]). assumption.
Qed.

Theorem llvm_a_early_ret_ok :
  llvm_a_early_ret_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_a_early_ret_stmt.
intros _ _ cx W' c' HB _ H104. exfalso.
unfold dec_a_base in HB.
destruct (dec_pre_parts _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & Hn & _).
(* llvm_a_st_104's size fact, taken by its type *)
unfold llvm_a_st_104 in H104. flat_ctx.
assert (Hn26 : 2 ^ 26 <= d_n cx) by assumption.
destruct Hn as [[Hn0 _] | [Hn0 _]]; lia.
Qed.

Theorem llvm_a_entry_ok :
  llvm_a_entry_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_a_entry_stmt.
intros HPCS HCELLS LAWS ML MTL MTF SMP ASM0 fx ly S W regs mem md p n pl M HPRE HROMv HXL.
pose proof (ASM0 fx) as ASM. clear ASM0.
destruct (dec_pre_parts fx ly S W regs mem md p n pl M HPRE)
  as (HAFN & H10 & H11 & Hpn & Hlen & Hgarr & Hfrs & Hmo & Hfrm).
destruct (afn_parts ly S W regs mem md HAFN) as (HAR & Hgp & Htp & Hstk & Hpres).
assert (Hsp16 : spZ regs mod 16 = 0) by (unfold astk_ok in Hstk; decompose [and] Hstk; assumption).
(* the stack window's bounds, for lia *)
pose proof Hstk as Hstkf. unfold astk_ok in Hstkf. decompose [and] Hstkf. clear Hstkf.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hstkv : DEC_LLVMF_STK = 32768) by reflexivity.
pose proof (ajournal_init (SK := dec_A_sink_head) segs B DEC_LLVMF_STK [] ly S W regs mem md [] HAFN) as HJ.
pose proof (en_entry B ly S W regs mem md HAR HCELLS ltac:(intros a Ha; apply Hpres; lia) ltac:(lia) Hsp16) as HS.
assert (HEI : img_env (@pa_val _ decode_listing PI_decode) A_LIM (EEN regs)) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ decode_listing PI_decode) (SOff 32 0) (@nil shent) (EEN regs) (mrestrict (w_H W) mem))
  by constructor.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (EEN regs) n = getr regs r)
by (intros nn r Hn; unfold EEN; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E2 : ew (EEN regs) 2 = getr regs 2) by exact (EE 2%nat 2%bv eq_refl).
assert (Usp : bv_unsigned (ew (EEN regs) 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E32 : ew (EEN regs) 32 = Z_to_bv 64 SHADOW_OFF)
by (unfold EEN; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
pose proof (paj_run (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) as RUN.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr (@pa_segs _ decode_listing PI_decode) Wx
    (mkCfg (mkst regs (Z_to_bv 64 (@pa_val _ decode_listing PI_decode A_TEXT + AF_LLVMFuzzerTestOneInput)) mem
      (seg_rom (@pa_segs _ decode_listing PI_decode))) md) Q) end.
(* +0x000 .. +0x070: the frame, the saves, s0/s1, the realign, the GOT and cell loads, the never-taken `beqz`,
   `li a0,64`, up to the `jal __asan_stack_malloc_0`. *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
  [reflexivity | rewrite Usp; lia | cbn; rewrite Hstkv; lia | cbn; lia |].
  awr_ro_rec. }
assert (Hsprng : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
(* sp after `addi sp,sp,-224` and `andi sp,sp,-32` (+0x000, +0x040), and the registers at the call. *)
set (sp1 := 32 * ((spZ regs + -224) / 32)).
destruct (sp1_facts (spZ regs + -224) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (E2' : ew (EEN regs) 2 = Z_to_bv 64 (spZ regs)) by (rewrite E2; symmetry; apply Z_to_bv_bv_unsigned).
reg_at HS (1%bv : bv 5) (Z_to_bv 64 (@pa_val _ decode_listing PI_decode A_TEXT + 116)) R1
  ltac:(apply codeptr_val; exact HEI).
reg_at HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (denot_and_m32 (EEN regs) 2 (spZ regs) (-224) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
reg_at HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
reg_at HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
reg_at HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
reg_at HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (denot_and_m32_add0 (EEN regs) 2 (spZ regs) (-224) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
reg_at HS (18%bv : bv 5) (w64 SHADOW_OFF) R18
  ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (20%bv : bv 5) (w64 n) R20
  ltac:(cbn [sv_denot]; rewrite (EE 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
reg_at HS (24%bv : bv 5) (w64 p) R24
  ltac:(cbn [sv_denot]; rewrite (EE 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
(* The machine-stack region at the call: the probe word and the 13 saved words. *)
lazymatch type of HS with st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  assert (HR0 : region_ok segsx Ex (ms_mem (restrict Hh msx)) r0)
    by (apply (st_ok_region_nth Ex ssx (restrict Hh msx) 0 r0 HS); vm_compute; reflexivity)
end.
cbn [ms_mem restrict] in HR0.
(* +0x070: jal __asan_stack_malloc_0, at the pc the statement's premise names. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (mkst ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (mkst rg (Z_to_bv 64 (decode_sigma DS___asan_stack_malloc_0)) mm rom) mdx) Q) end.
rewrite <- HPCS.
assert (Hcnt : count_cid 0 (frames S) < fs_frames 0) by (rewrite Hfrs; vm_compute; reflexivity).
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
  eapply (sm_call (SK := dec_A_sink_head) (@pa_segs _ decode_listing PI_decode) B LAWS decode_segs_low ML SMP 0 ASM
    ltac:(lia) W rg mm DEC_LLVMF_STK (spZ regs) [] ly S W mem md [] ly S mdx 0 (sp1 - spZ regs)
    (Z_to_bv 64 (@pa_val _ decode_listing PI_decode A_TEXT + 116)) HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp16, Hsp1al16. reflexivity.
  - lia.
  - unfold ESTACK. rewrite Hstkv. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_decode)); [lia | reflexivity].
  - exact Hcnt. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hz & Hflag & Hfpres & HK
  & (f & ES2)).
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR2 Hfin2) as (HFal & _ & _ & _).
destruct (frames_bounds _ B LAWS _ _ _ _ _ 0 pos HAR2 Hfin2) as (HF4096 & HFceil & _).
change (fs_frame_bytes 0) with 64 in Hz, Hflag, Hfpres, HFceil.
(* the words above sp1 are the run's: the call's window is [sp1 - ESTACK, sp1) *)
assert (HKS : forall a, spZ regs - 224 <= a < spZ regs ->
  aview decodesegs0 (w_H W) mem2 a = aview decodesegs0 (w_H W) (ms_mem ms) a).
{ intros a Ha. apply (proj1 HK); unfold ESTACK; lia. }
(* the payload is in a heap block of the entry, which the journal keeps *)
assert (HPAY : forall j, 0 <= j < n -> aview decodesegs0 (w_H W) mem2 (p + j) = aview decodesegs0 (w_H W) mem (p + j)).
{ intros j Hj. destruct Hpn as [[Hn0 _] | [_ Hin]]; [lia|].
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  pose proof (req_size_pos n ltac:(lia)) as Hrq.
  apply (F2 p n j Hin); [rewrite Eab; exact Hin | lia | intros (rg & [] & _)]. }
exists pos.
unfold llvm_a_st_074, dec_a_core, dec_a_saved, d_sp1, d_sp0, d_F, d_FL, DEC_FCLASS.
cbn [d_fx d_ly d_S d_W d_regs d_mem d_md d_p d_n d_pl d_M d_fpos].
replace (spZ regs - 224) with (spZ regs + -224) by lia. fold sp1.
exists fx, ly, S2, regs2, mem2, md2.
split; [reflexivity|].
split; [exact Hfrm|].
split.
{ split; [exact HJ2|].
  split; [rewrite Hfrs2, Hfrs; reflexivity|].
  split; [transitivity (getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact R8]|].
  split; [transitivity (getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact R9]|].
  split; [unfold spZ at 1; transitivity (bv_unsigned (getr (ms_regs ms) 2));
    [f_equal; exact (HP2 2 ltac:(unfold acallee_saved; lia)) | rewrite R2; apply unsigned_lit_small; lia]|].
  split; [lia|]. split; [exact Hsp1al|].
  split; [transitivity (getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact R3]|].
  split; [transitivity (getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact R4]|].
  split.
  { unfold dec_a_saved_at. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: saved_tac HR0 HKS EE Usp ms regs W. }
  split; [exact HF4096|]. split; [exact HFal|].
  split; [intros a Ha; apply Hfpres; lia|].
  split; [replace (frame_addr ly 0 pos + 56) with (frame_addr ly 0 pos + 64 - 8) by lia; exact Hflag|].
  split; [intros Hn0; rewrite Eab; destruct Hpn as [[Hn' _] | [_ Hin]]; [lia | exact Hin]|].
  apply (garr8_kept decodesegs0 (w_H W) (w_H W) mem mem2 p _); [| exact Hgarr].
  intros j Hj. rewrite length_map, <- Hlen in Hj. apply HPAY. lia. }
split; [exact Eab|].
split; [unfold dec_spent_074; rewrite ES2; apply (mo_le_set_fs_r MT MTF); apply (mo_le_refl MT MTL)|].
split.
{ rewrite ES2. apply (mo_ok_set_fs MT MTF). apply (mo_ok_le MT MTL S (dec_rest_074 MT n) (XL n) Hmo).
  pose proof (dec_cost_ladder MT n) as (L0 & _). unfold dec_spent_074 in L0. pose proof (HXL n ltac:(lia)). lia. }
split; [exact Ha0|].
split; [transitivity (getr (ms_regs ms) 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact R18]|].
split; [transitivity (getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20]|].
split; [transitivity (getr (ms_regs ms) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact R24]|].
exact Hz.
Qed.

End sg.
