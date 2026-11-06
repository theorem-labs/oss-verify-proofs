(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v, with its module paths and module names changed; 410 of its 463 lines of code are new or changed and 580 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/codec_bmain_owel.v, with its module names changed; 958 of its 1102 lines of code are new or changed and 319 lines of the source are left out. *)
(* Segment OWE5 of the image-B walk of LLVMFuzzerTestOneInput (lib/AU/Prog/codec_bmain_inv.v seg_owe 5): owe()'s
   RING case (fuzz_codec.c:174-186), 0x82af0-0x82be0, its slow check block 0x830e0-0x830e4, the led loop
   0x82b54-0x82bd4 (codec_bmain_owe5_lib.v), the tail 0x82fb0-0x8301c with the slow check block 0x8344c-0x83450 and
   the copy of the payload (__asan_memcpy, 0x51ae8), the E_RANGE tail 0x82dc8-0x82dcc and the reload of s9 at
   0x82dd0, to CHK 0x82dd4. The image-A segment (lib/A/Prog/codec_amain_owe5.v) gives the spec lemmas and the
   arithmetic; image B keeps the ring payload p[3] in the frame at F + 32:
     0x82af0 / 0x82af8 the UBSan checks of the desk pointer d = s6, not taken (d is SPEC_C24 or SPEC_PC, 32-aligned,
     an atom fact of the state); 0x82afc the check of the strips byte's shadow (d + 9); lw a,24(s7); lbu strips;
     bgeu a,strips -> E_RANGE; lwu b,28(s7); srli b,15; bnez -> E_RANGE;
     0x82b28 shadow byte 4 of the frame := 3 (p[0..3) marked usable); p[0] = a | (b & 1) << 6, p[1] = p[2] = 0;
     0x82b54-0x82bd4 the 14 passes (codec_bmain_owe5_lib.v o5_loop): p[1], p[2] = owe_ring b; the UBSan check
     0x82b70 (the pointer F + 32 against overflow) is not taken (F is a frame address);
     0x82fb0 the check of the dev byte's shadow (d + 8), s9 reloaded; want[0..2) = 0xf0 0x13, want[2] = dev,
     want[3] = 0; __asan_memcpy(want + 4, p, 3); want[7] = 0xf7, want_len = 8, want_key = 0x30000 | (a & 0xffff),
     want_display = 0; shadow byte 4 := 0xf8 (s11); j CHK. 0x82dc8 want_rc = -11; 0x82dd0 s9 = F + 448.
   The state: k's a and b read-only (atoms 37, 38), want_rc and want[0..4), want[7] writable, want[4..7) read-only
   (want[0..8) as atoms 43-50 on the E_RANGE paths), want_len .. want_display writable, the desk's four bytes
   (atoms 39-42). The shadow byte and the payload are added as regions at 0x82b2c and run by the executor
   without shadow tokens; the loop runs from its own states (o5_loop); after it the state is re-seated
   (st_ok_after_stretch) without them, the copy is the runtime's intrinsic (CPgWalkIntrU.cw_intrin_call) and the
   shadow byte is added again for the last stores. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecRo CodecGlobs CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_lem codec_bmain_st.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_owel.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU CPgWalkIntrU codec_bmain_headl codec_bmain_owe5_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the bytes OWE5 may change ================================
   owe()'s fields (owe_zone with want[0..8)), the payload p[3] at F + 32, the frame's shadow byte 4 (3 while the
   payload is in use, 0xf8 before and after), and the stack the copy runtime uses below sp1. *)
Definition o5_zone (g : ectx) (pos sp1 a : Z) : Prop :=
owe_zone g pos sp1 8 a \/ (FA g pos + 32 <= a < FA g pos + 35) \/
(shadow_addr (FA g pos) + 4 <= a < shadow_addr (FA g pos) + 5) \/ (sp1 - 4096 <= a < sp1).

(* the frame's 60 shadow bytes with byte 4 = 3 (the payload's 3 bytes marked usable) *)
Definition o5_shm3 : list Z := Eval vm_compute in firstn 4 (shm 0) ++ [3] ++ skipn 5 (shm 0).
Lemma o5_shm3_nth : forall i, (i < 60)%nat -> i <> 4%nat -> nth i o5_shm3 0 = nth i (shm 0) 0.
Proof. intros i Hi H4. do 60 (destruct i as [|i]; [first [reflexivity | lia]|]). lia. Qed.

Lemma o5_submem2 : forall l, submem (skipn 2 l) l.
Proof.
intros [|a [|b l]]; cbn [skipn].
- apply submem_nil.
- apply submem_drop. apply submem_nil.
- apply submem_drop. apply submem_drop. apply submem_refl.
Qed.
(* the regions the walk keeps across the copy: those whose window lies inside their range (cw_intrin_call), but the
   copy's destination want[4..7) *)
Definition o5_callkeep (r : YP09.region) : bool :=
(YP09.r_lo r <=? YP09.r_wlo r) && (YP09.r_whi r <=? YP09.r_hi r) &&
negb ((YP09.r_lo r =? 340) && (YP09.r_hi r =? 343)).
Lemma o5_submem_filter : forall (f : YP09.region -> bool) (l : smem), submem (List.filter f l) l.
Proof.
intros f l. induction l as [|r l IH]; cbn [List.filter].
- apply submem_nil.
- destruct (f r).
  + apply submem_keep; [apply subregion_refl | exact IH].
  + apply submem_drop. exact IH.
Qed.
Lemma o5_shm0_k : forall i, 24 <= i < 47 -> nth (Z.to_nat i) (shm 0) 0 = 0.
Proof.
intros i Hi. unfold shm. rewrite app_nth2 by (cbn [length]; lia). cbn [length].
rewrite app_nth1 by (rewrite repeat_length; lia). apply hd_nth_repeat. lia.
Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* the frame's shadow bytes as a region of a state, from the bytes' values (codec_bmain_st.v bm_shadow_region_ok
   from AR and the values instead of mcommon) *)
Lemma o5_sh_region_ok : forall E (W : world tfibsegs) ly S mem md pos F vs wlo whi,
AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) -> frame_addr ly 3 pos = F ->
F mod 64 = 0 -> 4096 <= F -> F + 512 <= 0x7fffff800000 ->
bv_unsigned (ew E 34) = shadow_addr F -> length vs = 60%nat ->
(forall i, 0 <= i < 60 -> aview tfibsegs (w_H W) mem (shadow_addr F + i) = Some (nth (Z.to_nat i) vs 0)) ->
0 <= wlo -> whi <= 60 ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (bm_shadow_region wlo whi vs).
Proof.
intros E W ly S mem md pos F vs wlo whi HAR Hin EFA Hf64 Hf4096 Hfhi H34 Hlen HSH Hwlo Hwhi.
destruct (al_frames _ _ LAWS ly S W mem md 3 pos HAR Hin) as (_ & _ & _ & Hsh).
rewrite EFA in Hsh.
assert (Hd1 : 0 <= F / 8 <= F) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (HB : base_val E (Some 34%nat) = shadow_addr F) by (cbn [base_val]; exact H34).
unfold bm_shadow_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite HB.
split; [unfold shadow_addr, SHADOW_OFF; lia|]. split; [unfold shadow_addr, SHADOW_OFF; lia|]. split.
- intros o Ho. apply (apresent_writable tfibsegs). apply Hsh.
  change (fs_frame_bytes 3 / 8) with 64. lia.
- apply (bm_sh_chunks_ok _ W mem). intros j Hj. rewrite Hlen in Hj.
  rewrite Z.add_0_l. apply HSH. cbn in Hj. lia.
Qed.

(* a range of the frame as a region of a state, from AR (codec_bmain_st.v bm_frame_region_ok from AR) *)
Lemma o5_fr_region_ok : forall E (W : world tfibsegs) ly S mem md pos F lo hi wlo whi cs,
AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) -> frame_addr ly 3 pos = F ->
bv_unsigned (ew E 33) = F -> 4096 <= F -> F + 512 <= 0x7fffff800000 ->
0 <= lo -> lo <= hi -> hi <= 512 -> lo <= wlo -> whi <= hi ->
Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) mem) F) cs ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (bm_frame_region lo hi wlo whi cs).
Proof.
intros E W ly S mem md pos F lo hi wlo whi cs HAR Hin EFA H33 Hf4096 Hfhi Hlo Hlh Hhi Hwl Hwh Hcs.
destruct (al_frames _ _ LAWS ly S W mem md 3 pos HAR Hin) as (_ & _ & Hpr & _).
rewrite EFA in Hpr.
assert (HB : base_val E (Some 33%nat) = F) by (cbn [base_val]; exact H33).
unfold bm_frame_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite HB.
split; [lia|]. split; [lia|]. split; [|exact Hcs].
intros o Ho. apply (apresent_writable tfibsegs).
exact (proj1 (Hpr (F + o) ltac:(change (fs_frame_bytes 3) with 512; lia))).
Qed.
End h.

(* k's shadow entry from its 23 shadow bytes (owel's owe_k_shent from the bytes instead of mcommon) *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma o5_k_shent : forall E (W : world tfibsegs) m F,
F mod 64 = 0 -> 4096 <= F -> in_app F 512 -> F + 512 <= 0x7fffff800000 ->
(forall i, 24 <= i < 47 -> aview tfibsegs (w_H W) m (shadow_addr F + i) = Some 0) ->
ew E 33 = Z_to_bv 64 F -> ew E 32 = Z_to_bv 64 SB ->
shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) m) owe_SHk.
Proof.
intros E W m F Hf64 Hf4096 Happ Hfhi HK E33 E32.
assert (HBS : block_shadow (aview tfibsegs (w_H W) m) SHADOW_OFF (F + 192) 184).
{ apply (bm_block_shadow W m F 192 184 Hf64); [lia | reflexivity | lia |].
  intros i Hi. change ((184 + 7) / 8) with 23 in Hi. change (192 / 8) with 24. change (184 / 8) with 23.
  replace (i <? 23) with true by (symmetry; apply Z.ltb_lt; lia). apply HK. lia. }
pose proof (block_shadow_range (aview tfibsegs (w_H W) m) SHADOW_OFF (F + 192) 184 (F + 192) 184
  HBS ltac:(lia) ltac:(lia)) as Hra.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Ham : amem_range (F + 192) 184) by (appn; lia).
unfold owe_SHk. change 376 with (192 + 184).
apply (cw_shent_ra_off W m E 33 F 192 184 Hra Ham); [lia | lia | lia | lia | exact E33 | exact E32].
Qed.
(* the payload's 3 bytes are addressable once shadow byte 4 is 3 *)
Lemma o5_ra3 : forall (W : world tfibsegs) m F, F mod 64 = 0 ->
aview tfibsegs (w_H W) m (shadow_addr F + 4) = Some 3 ->
range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF (F + 32) 3.
Proof.
intros W m F Hf64 H4.
assert (HBS : block_shadow (aview tfibsegs (w_H W) m) SHADOW_OFF (F + 32) 3).
{ apply (bm_block_shadow W m F 32 3 Hf64); [lia | reflexivity | lia |].
  intros i Hi. change ((3 + 7) / 8) with 1 in Hi. replace i with 0 by lia. exact H4. }
exact (block_shadow_range (aview tfibsegs (w_H W) m) SHADOW_OFF (F + 32) 3 (F + 32) 3 HBS ltac:(lia) ltac:(lia)).
Qed.
(* the shadow bytes of a range of the frame are readable when its 60 shadow bytes are (headl's hd_hull from the
   bytes instead of mcommon) *)
Lemma o5_hull : forall (W : world tfibsegs) m F off n, F mod 64 = 0 -> 0 <= off -> 0 < n -> off + n <= 448 ->
(forall i, 0 <= i < 60 -> aview tfibsegs (w_H W) m (shadow_addr F + i) <> None) ->
shadow_hull_vis (aview tfibsegs (w_H W) m) (F + off) n.
Proof.
intros W m F off n Hf64 Hoff Hn Hon HV s Hs. unfold shadow_addr in Hs.
pose proof (hd_hull_arith F off n s Hf64 Hoff Hn Hon Hs) as Hi.
replace s with (shadow_addr F + (s - (SHADOW_OFF + F / 8))) by (unfold shadow_addr; lia).
apply HV. lia.
Qed.
(* a byte read as a value at a, at b of a memory whose view at b is the first's at a *)
Lemma o5_vm_move : forall H (m m' : word -> option byte) a b v, val_mem tfibsegs (mrestrict H m) a 1 v ->
aview tfibsegs H m' b = aview tfibsegs H m a -> val_mem tfibsegs (mrestrict H m') b 1 v.
Proof.
intros H m m' a b v V E k Hk. assert (k = 0%nat) by lia. subst k. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
pose proof (V 0%nat ltac:(lia)) as V0. change (Z.of_nat 0) with 0 in V0. rewrite Z.add_0_r in V0.
unfold aview in E. rewrite V0 in E. cbn [option_map] in E.
destruct (mbyte tfibsegs (mrestrict H m') b) as [y|] eqn:Ey; cbn [option_map] in E; [|discriminate].
injection E as Ey'. f_equal. apply bv_eq. rewrite Ey'. reflexivity.
Qed.
(* a byte read as a value is visible *)
Lemma o5_aview_vm : forall H (m : word -> option byte) a v, val_mem tfibsegs (mrestrict H m) a 1 v ->
aview tfibsegs H m a <> None.
Proof. intros H m a v V. unfold aview. pose proof (V 0%nat ltac:(lia)) as V0. rewrite Z.add_0_r in V0. rewrite V0. discriminate. Qed.
(* a region whose bytes lie off the zone Zout of the writes is kept, its window present after them *)
Lemma o5_region_kept : forall E H (m m' : word -> option byte) (Zout : Z -> Prop) r,
(forall a, 0 <= a < 2 ^ 64 -> ~ Zout a -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
  0 <= a < 2 ^ 64 /\ ~ Zout a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
  apresent H m' a) ->
region_kept tfibsegs E (mrestrict H m) (mrestrict H m') r.
Proof.
intros E H m m' Zout r HK Hr Hp. split.
- intros a Ha. destruct (Hr a Ha) as [Ha64 Hz]. apply (mbyte_of_aview tfibsegs). exact (HK a Ha64 Hz).
- intros a Ha _. apply (apresent_writable tfibsegs). exact (Hp a Ha).
Qed.
End k.

(* The end of OWE5 at CHK: owel's owe_chk_end over o5_zone (the payload, the shadow byte 4 and the copy runtime's
   stack added to owe()'s fields), with shadow byte 4 read back as 0xf8 and the cursor region anywhere in the
   state. *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis LAWS : AR_laws tfibsegs B.

Lemma o5_chk_end : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc od mem3 regs3 md3 E ss r bs l key dp,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos kc W2 mem2 -> rec_okZ kc od ->
kz_rc kc = fst (enc_kZ kc od) ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem3 md3 kj ->
env_agree 37 (bm_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs))) ->
bm_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 20%bv = SOff 20 0 ->
In bm_cur_region (ss_mem ss) ->
length bs = 8%nat ->
(forall a, 0 <= a < 2 ^ 64 -> ~ o5_zone g pos sp1 a ->
 aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
aview tfibsegs (w_H W2) mem3 (shadow_addr (FA g pos) + 4) = Some (nth 4 (shm 0) 0) ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 332) 4 r -> garr8 tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 336) bs ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 360) 8 l -> val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 368) 4 key ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 372) 4 dp ->
- 2 ^ 31 <= r < 2 ^ 31 -> 0 <= l < 2 ^ 64 -> 0 <= key < 2 ^ 32 -> - 2 ^ 31 <= dp < 2 ^ 31 ->
owe_want_okZ (owe_setZ kc r (bs ++ skipn (length bs) (kz_want kc)) l key dp) od ->
SRr tfibsegs W2 (mkCfg (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs)) md3)
  (inv_chk B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc od mem3 regs3 md3 E ss r bs l key dp
  HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJ3 HAE HS Hkeep H20 Hcr Hbs KE H4 Vr Gbs Vl Vkey Vdp
  Hr Hl Hkey Hdp Hwant.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & _).
pose proof (owe_frame_app B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as Happ.
change (fs_frame_bytes 3) with 512 in Hfceil.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold BM_HI in *.
pose proof HAE as (HA & HD).
assert (HAE35 : env_agree 35 (bm_env g pos c regs2 ys) E) by (split; [intros nn Hnn; apply HA; lia | exact HD]).
pose proof HC as (_ & _ & R2 & _).
pose proof HC as HSH. do 47 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
pose proof HC as HPm. do 49 (destruct HPm as (_ & HPm)).
assert (D8 : 0 <= FA g pos / 8 /\ 8 * (FA g pos / 8) <= FA g pos)
  by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
assert (Hzsh : forall i, 0 <= i < 60 -> i <> 4 -> ~ o5_zone g pos sp1 (shadow_addr (FA g pos) + i)).
{ intros i Hi H4' Hz. unfold o5_zone, owe_zone, shadow_addr, SHADOW_OFF in Hz. appn. lia. }
apply SRr_ret.
change (mkCfg (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs)) md3)
  with (cfg_at tfibsegs PC_CHK regs3 mem3 md3).
unfold inv_chk.
apply (bm_mcut B MT K XM_LIB g pos sp1 0 PC_CHK _ ly2 S2 W2 regs3 mem3 md3 kj HJ3 Hfr Hk Hmo).
- apply (bm_exit B MT K XM_LIB LAWS g pos sp1 0 0 c ys ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs3 mem3 md3 kj
    (Z_to_bv 64 PC_CHK) ss E HC HJ3 HAE35 HS Hkeep).
  + intros a Ha. apply KE; [unfold bm_keepzone in Ha; lia | intros Hz; unfold bm_keepzone, o5_zone, owe_zone, shadow_addr, SHADOW_OFF in Ha, Hz; appn; lia].
  + intros i Hi. destruct (Z.eq_dec i 4) as [-> | Hne]; [exact H4|].
    rewrite (KE (shadow_addr (FA g pos) + i)); [exact (HSH i Hi) | unfold shadow_addr, SHADOW_OFF; lia |
      exact (Hzsh i Hi Hne)].
  + exact HPm.
- cbv beta. split.
  { destruct Hops as [Hops1 Hops2]. split; [exact Hops1|].
    pose proof (st_ok_restrict_reg tfibsegs (w_H W2) E ss (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs))
      20%bv HS) as R20.
    change (getr (ms_regs (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs))) 20%bv) with (getr regs3 20%bv)
      in R20.
    rewrite R20, H20. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite (HA 20%nat ltac:(lia)), (bm_ew_reg g pos c regs2 ys 20 20%bv eq_refl). exact Hops2. }
  exists c, (owe_setZ kc r (bs ++ skipn (length bs) (kz_want kc)) l key dp), od.
  split.
  { pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & HRs & _).
    pose proof (proj1 (Forall_forall _ _) HRs _ Hcr) as Hrc4. cbn [ms_mem restrict] in Hrc4.
    try rewrite restrict_mkst_fx in Hrc4. cbn [ms_mem] in Hrc4.
    unfold bm_cur_region in Hrc4.
    assert (U2 : bv_unsigned (ew E 2) = sp1).
    { rewrite (HA 2%nat ltac:(lia)), (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64.
      apply unsigned_lit_small. lia. }
    destruct Hcur as (Hc & _ & _).
    split; [exact Hc|]. split.
    - apply (field_of_region E _ 2%nat sp1 _ 184 200 184 200 184 8 (SOff 35 0) (e_p g + c) Hrc4 U2);
      [left; reflexivity | | lia | lia].
      cbn [sv_denot]. rewrite (HA 35%nat ltac:(lia)), (bm_ew_CP g pos c regs2 ys), Z.add_0_r, Z_to_bv_bv_unsigned.
      reflexivity.
    - apply (field_of_region E _ 2%nat sp1 _ 184 200 184 200 192 8 (SOff 36 0) (e_n g - c) Hrc4 U2);
      [right; left; reflexivity | | lia | lia].
      cbn [sv_denot]. rewrite (HA 36%nat ltac:(lia)), (bm_ew_CN g pos c regs2 ys), Z.add_0_r, Z_to_bv_bv_unsigned.
      reflexivity. }
  split.
  { apply (owe_k_at_end g pos kc W2 mem2 W2 mem3 r bs l key dp Hkat ltac:(lia)).
    - intros a Ha. apply KE; [lia | intros Hz; unfold o5_zone, owe_zone, shadow_addr, SHADOW_OFF in Hz; appn; lia].
    - replace (FA g pos + 192 + 140) with (FA g pos + 332) by lia. exact Vr.
    - replace (FA g pos + 192 + 144) with (FA g pos + 336) by lia. exact Gbs.
    - replace (FA g pos + 192 + 168) with (FA g pos + 360) by lia. exact Vl.
    - replace (FA g pos + 192 + 176) with (FA g pos + 368) by lia. exact Vkey.
    - replace (FA g pos + 192 + 180) with (FA g pos + 372) by lia. exact Vdp.
    - exact Hr.
    - exact Hl.
    - exact Hkey.
    - exact Hdp. }
  split; [apply owe_setZ_rec; exact Hrec|].
  split; [destruct (owe_setZ_kz kc od r (bs ++ skipn (length bs) (kz_want kc)) l key dp) as (_ & E2 & E3);
    rewrite E2, E3; exact Hrc|].
  exact Hwant.
Qed.
End e.

(* ================================ the state at OWE5 ================================ *)
Definition o5_k : YP09.region := bm_frame_region 216 224 216 216
[YP09.mkChunk 216 (CVal 4 (SOff 37 0)); YP09.mkChunk 220 (CVal 4 (SOff 38 0))].
Definition o5_wa : YP09.region := bm_frame_region 332 340 332 340
[YP09.mkChunk 332 (CVal 4 (SLit 0));
 YP09.mkChunk 336 (CVal 1 (SOff 43 0)); YP09.mkChunk 337 (CVal 1 (SOff 44 0)); YP09.mkChunk 338 (CVal 1 (SOff 45 0));
 YP09.mkChunk 339 (CVal 1 (SOff 46 0))].
Definition o5_wc : YP09.region := bm_frame_region 340 343 340 340
[YP09.mkChunk 340 (CVal 1 (SOff 47 0)); YP09.mkChunk 341 (CVal 1 (SOff 48 0)); YP09.mkChunk 342 (CVal 1 (SOff 49 0))].
Definition o5_wb : YP09.region := bm_frame_region 343 344 343 344 [YP09.mkChunk 343 (CVal 1 (SOff 50 0))].
Definition o5_l : YP09.region := bm_frame_region 360 376 360 376
[YP09.mkChunk 360 (CVal 8 (SLit 0)); YP09.mkChunk 368 (CVal 4 (SLit 0)); YP09.mkChunk 372 (CVal 4 (SLit 0))].
Definition o5_d : YP09.region := owe_desk_region [SOff 39 0; SOff 40 0; SOff 41 0; SOff 42 0].
Definition o5_rs : smem := [o5_k; o5_wa; o5_wc; o5_wb; o5_l; o5_d].
Definition o5_AF : list (nat * afact) :=
[(22%nat, mkAF 0x9dfc0 0x9dfe0 5); (37%nat, mkAF 0 (2 ^ 32 - 1) 0); (38%nat, mkAF 0 (2 ^ 16 - 1) 0);
 (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0); (41%nat, mkAF 0 255 0); (42%nat, mkAF 0 255 0)].
Definition o5_ys (kc : kcallZ) (d : desk) : list Z :=
[kz_a kc; kz_b kc; d_dev d; d_strips d; d_chars d; d_counter d] ++ firstn 8 (kz_want kc).
(* the payload and the shadow byte 4, added to the state at 0x82b2c *)
Definition o5_pay : YP09.region := bm_frame_region 32 35 32 35 [].
Definition o5_sh0 : YP09.region := bm_shadow_region 4 5 bm_shm0.

(* the trap edges inside the segment's ranges: the two desk checks at its root and the payload pointer check *)
Lemma o5_traps :
  List.filter (fun a => ((0x82af0 <=? a) && (a <? 0x82be4)) || ((0x82fb0 <=? a) && (a <? 0x83020)) ||
                        ((0x830e0 <=? a) && (a <? 0x830ec)) || ((0x8344c <=? a) && (a <? 0x83458)) ||
                        ((0x82dc8 <=? a) && (a <? 0x82dd4)))
    (bm_trap_taken ++ bm_trap_fall) = [0x82af0; 0x82af8; 0x82b70].
Proof. vm_compute. reflexivity. Qed.

(* ================================ owe()'s RING case ================================
   o5_spec_rng / o5_spec_ok and the executor's values are the image-A segment's
   (lib/A/Prog/codec_amain_owe5.v:91-186). *)
Lemma o5_spec_rng : forall d a b c delta bytes n, 0 <= b -> d_strips d <= a \/ 2 ^ 15 <= b ->
fst (owe_spec 5 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
intros d a b c delta bytes n Hb H. unfold owe_spec. cbv beta iota zeta. cbn [Z.eqb Pos.eqb orb negb].
destruct (Z.leb_spec (d_strips d) a); [reflexivity|].
replace (Z.shiftr b 15 =? 0) with false; [reflexivity|].
symmetry. apply Z.eqb_neq. rewrite Z.shiftr_div_pow2 by lia.
assert (1 <= b / 2 ^ 15) by (apply Z.div_le_lower_bound; lia). lia.
Qed.
Lemma o5_spec_ok : forall d a b c delta bytes n, a < d_strips d -> 0 <= b < 2 ^ 15 ->
owe_spec 5 (Some d) a b c delta bytes n =
(0, ([0xf0; 0x13; u8 (d_dev d); 0; u8 (Z.lor a (bit_or_0 (Z.testbit b 0) 0x40));
      fst (owe_ring b); snd (owe_ring b); 0xf7], KEY 3 a, 0)).
Proof.
intros d a b c delta bytes n Ha Hb. unfold owe_spec. cbv beta iota zeta. cbn [Z.eqb Pos.eqb orb negb].
replace (d_strips d <=? a) with false by (symmetry; apply Z.leb_gt; lia).
replace (Z.shiftr b 15 =? 0) with true
  by (symmetry; apply Z.eqb_eq; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
cbn [orb negb]. destruct (owe_ring b) as [p1 p2]. unfold owe_sx. cbn. reflexivity.
Qed.
Lemma o5_DX : forall Ex n v, ew Ex n = Z_to_bv 64 v -> sv_denot Ex (SOff n 0) = Z_to_bv 64 v.
Proof. intros Ex n v Hv. cbn [sv_denot]. rewrite Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma o5_U_zx8 : forall Ex n v, ew Ex n = Z_to_bv 64 v -> 0 <= v < 256 -> U Ex (SExt false 8 (SOff n 0)) = v.
Proof.
intros Ex n v Hv Hr. rewrite U_SExt. cbv iota beta. rewrite (U_atom Ex n v Hv) by lia.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
Lemma o5_U_zx32 : forall Ex n v, ew Ex n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> U Ex (SExt false 32 (SOff n 0)) = v.
Proof.
intros Ex n v Hv Hr. rewrite U_SExt. cbv iota beta. rewrite (U_atom Ex n v Hv) by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite Z.mod_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
Lemma o5_U_srl15 : forall Ex e b, U Ex e = b -> 0 <= b < 2 ^ 16 ->
U Ex (SAlu ALU_SRL e (SLit 15)) = Z.shiftr b 15.
Proof.
intros Ex e b Hb Hr. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hb, U_lit by lia.
change (Z.land 15 63) with 15. unfold zcanon, M64. apply Z.mod_small.
rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
(* 0x82b34-0x82b48: p[0] = ((b << 63) >> 57) | a *)
Lemma o5_U_p0 : forall E a b, ew E 37 = Z_to_bv 64 a -> ew E 38 = Z_to_bv 64 b -> 0 <= a < 2 ^ 31 -> 0 <= b < 2 ^ 16 ->
U E (SAlu ALU_OR (SAlu ALU_SRL (SAlu ALU_SLL (SOff 38 0) (SLit 63)) (SLit 57)) (SExt true 32 (SOff 37 0)))
= Z.lor a (bit_or_0 (Z.testbit b 0) 64).
Proof.
intros E a b H37 H38 Ha Hb.
assert (Us : U E (SExt true 32 (SOff 37 0)) = a).
{ rewrite (owe_U_sx32 E 37 a H37) by lia. destruct (Z.ltb_spec a (2 ^ 31)); lia. }
assert (Ul : U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 38 0) (SLit 63)) (SLit 57)) = (b mod 2) * 64).
{ rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 38 b H38), !U_lit by lia.
  change (Z.land 63 63) with 63. change (Z.land 57 63) with 57.
  rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64.
  pose proof (Z.mod_pos_bound b 2 ltac:(lia)) as Hm.
  assert (E1 : (b * 2 ^ 63) mod 2 ^ 64 = (b mod 2) * 2 ^ 63).
  { rewrite (Z.div_mod b 2) at 1 by lia.
    replace ((2 * (b / 2) + b mod 2) * 2 ^ 63) with ((b mod 2) * 2 ^ 63 + (b / 2) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite E1, Z.shiftr_div_pow2 by lia.
  replace ((b mod 2) * 2 ^ 63) with ((b mod 2 * 64) * 2 ^ 57) by lia. rewrite Z.div_mul by lia.
  apply Z.mod_small. lia. }
assert (Bx : (b mod 2) * 64 = bit_or_0 (Z.testbit b 0) 64).
{ rewrite Zmod_odd, <- Z.bit0_odd. destruct (Z.testbit b 0); reflexivity. }
assert (Bx2 : 0 <= bit_or_0 (Z.testbit b 0) 64 < 128) by (destruct (Z.testbit b 0); cbn; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ul, Us, Bx.
pose proof (o5_lor_ltn 31 (bit_or_0 (Z.testbit b 0) 64) a ltac:(lia) ltac:(lia) ltac:(lia)) as L.
unfold zcanon, M64. rewrite Z.mod_small by lia. apply Z.lor_comm.
Qed.
(* 0x82ff0-0x82ffc: want_key = (a & 0xffff) | 0x30000 *)
Lemma o5_U_key : forall E a, ew E 37 = Z_to_bv 64 a -> 0 <= a < 2 ^ 16 ->
U E (SAlu ALU_OR (SAlu ALU_SRL (SAlu ALU_SLL (SExt true 32 (SOff 37 0)) (SLit 48)) (SLit 48)) (SLit 196608))
= KEY 3 a.
Proof.
intros E a H37 Ha.
assert (Us : U E (SExt true 32 (SOff 37 0)) = a).
{ rewrite (owe_U_sx32 E 37 a H37) by lia. destruct (Z.ltb_spec a (2 ^ 31)); lia. }
assert (Ul : U E (SAlu ALU_SRL (SAlu ALU_SLL (SExt true 32 (SOff 37 0)) (SLit 48)) (SLit 48)) = a).
{ rewrite !U_SAlu. cbn [zalu_raw]. rewrite Us, !U_lit by lia. change (Z.land 48 63) with 48.
  rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64.
  rewrite (Z.mod_small (a * 2 ^ 48)) by (change (2 ^ 48) with 281474976710656; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by (change (2 ^ 48) with 281474976710656; lia).
  apply Z.mod_small. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ul, U_lit by lia.
unfold KEY. change (3 * 65536) with 196608. change 0xffff with (Z.ones 16).
rewrite Z.land_ones by lia. rewrite (Z.mod_small a) by lia.
pose proof (o5_lor_ltn 18 a 196608 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as L.
unfold zcanon, M64. rewrite Z.mod_small by (cbn in L; lia). apply Z.lor_comm.
Qed.
Lemma o5_key_range : forall a, 0 <= KEY 3 a < 2 ^ 32.
Proof.
intros a. unfold KEY. change (3 * 65536) with 196608. change 0xffff with (Z.ones 16).
rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound a (2 ^ 16) ltac:(lia)) as Hm.
pose proof (o5_lor_ltn 18 196608 (a mod 2 ^ 16) ltac:(lia) ltac:(cbn; lia) ltac:(cbn in *; lia)) as L.
cbn in L |- *. lia.
Qed.
Definition o5_bs (kc : kcallZ) (d : desk) : list Z :=
[0xf0; 0x13; u8 (d_dev d); 0; u8 (Z.lor (kz_a kc) (bit_or_0 (Z.testbit (kz_b kc) 0) 0x40));
 fst (owe_ring (kz_b kc)); snd (owe_ring (kz_b kc)); 0xf7].

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
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy BM_asan_memcpy.

(* the write windows of a state: the cursor, the entry's own frame, the frame's shadow bytes *)
Ltac o5_awr sp1v sp0v posv Fv U2 UF U34 EFA :=
  idtac; cw_awrA;
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp1v - sp0v));
    [reflexivity | rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite U2; lia
    | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat Fv);
    [ reflexivity | rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact UF
    | let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists 3, posv;
      split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; rewrite EFA;
      change (fs_frame_bytes 3) with 512; lia
    | ]
  | eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 3 posv 34%nat);
    [reflexivity | rewrite EFA; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact U34 | left; reflexivity
    | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; change (fs_frame_bytes 3 / 8) with 64; lia |] ].
(* the windows lie in o5_zone *)
Ltac o5_kwr U2 UF U34 :=
  idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta; unfold o5_zone, owe_zone;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?ew_ewset_other, ?ew_havoc_old in Hb by lia;
     rewrite ?U2, ?UF, ?U34 in Hb; lia | ]);
  destruct Hr.

(* the E_RANGE end of OWE5: want_rc = -11, the other fields as at the cut (owel's owe_chk_end) *)
Ltac o5_fld HS i off w V :=
  lazymatch type of HS with st_ok _ ?Ev ?ss ?ms =>
    let r := eval vm_compute in (nth i (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    let Hr := fresh "Hr" in
    assert (Hr : region_ok tfibsegs Ev (ms_mem ms) r) by (apply (st_ok_region_nth Ev ss ms i r HS); vm_compute; reflexivity);
    rewrite ?restrict_mkst_fx in Hr; cbn [ms_mem] in Hr;
    pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ off w _ Hr
      ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by lia; eassumption) ltac:(owe_in) ltac:(lia)) as V; clear Hr
  end.
Ltac o5_fldx HS off w V :=
  first [ o5_fld HS 0%nat off w V | o5_fld HS 1%nat off w V | o5_fld HS 2%nat off w V | o5_fld HS 3%nat off w V
        | o5_fld HS 4%nat off w V | o5_fld HS 5%nat off w V | o5_fld HS 6%nat off w V | o5_fld HS 7%nat off w V
        | o5_fld HS 8%nat off w V | o5_fld HS 9%nat off w V | o5_fld HS 10%nat off w V | o5_fld HS 11%nat off w V
        | o5_fld HS 12%nat off w V ].
(* the tail's write windows lie in o5_zone and off want[4..7) *)
Ltac o5_kwr2 U2 UF U34 Hsh :=
  idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta; unfold o5_zone, owe_zone; unfold cw_hold in Hsh;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?ew_ewset_other, ?ew_havoc_old in Hb by lia;
     rewrite ?U2, ?UF, ?U34 in Hb; lia | ]);
  destruct Hr.

Theorem seg_owe5_holds : seg_owe B MT K XM_LIB 5.
Proof.
unfold seg_owe. intros g pos sp1 ops W2 c2 Hst.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct HP as (Hops & _ & c & kc & od & Hcur & Hkat & Hrec & Hkind & Hod & Hrc & Hw0 & Hwl0 & Hwk0 & Hwd0 & R22).
destruct od as [d|]; [| exfalso; destruct (Hod eq_refl) as [X | [X | X]]; lia].
pose proof Hrec as (_ & Hpd & Hrdr & _ & _).
pose proof Hrdr as (Ra & Rb & _ & _ & _ & _ & _ & R5 & _ & _). rewrite Hkind in R5. specialize (R5 eq_refl).
destruct (pd_range_B _ _ d Hpd) as (Hpv & Hdv & Rdev & Rstr & Rch & Rcnt).
pose proof (owe_desk_range _ _ _ Hpd) as Hdr.
assert (Hdal : kz_desk kc mod 32 = 0) by (destruct Hdv as [-> | ->]; reflexivity).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold BM_HI in *.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (owe_frame_app B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as Happ.
pose proof Hkat as (HK & HW).
destruct HK as (Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gbytes & Vn & Vrc & Gbef & Gout & Vwrc & Gwant & Vwl & Vwk & Vwd).
destruct HW as (Wkind & Wp & Wdesk & Wa & Wb & Wc & Wdelta & Wn & Wrc & Wwrc & Wwl & Wwk & Wwd & Lbytes & Lbef & Lout & Lwant).
pose proof HC as (Hpre & _ & R2 & R9 & R8 & R3 & R4 & R21 & R18 & R27 & R23 & R25 & R19 & R26 & _).
pose proof HC as HSH. do 47 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
assert (HRO : arodata_ok B (aview tfibsegs (w_H W2) mem2)) by exact (arodata_ok_at B MT K XM_LIB g _ _ _ _ _ _ _ Hpre HJ).
pose proof HJ as (HAR & _).
assert (HinS : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
set (dv := kz_desk kc) in *.
set (ys := o5_ys kc d).
set (E := bm_env g pos c regs2 ys).
assert (DX : forall n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v) by (intros n v Hv; exact (o5_DX E n v Hv)).
assert (X37 : ew E 37 = Z_to_bv 64 (kz_a kc)) by exact (bm_ew_y g pos c regs2 ys 0).
assert (X38 : ew E 38 = Z_to_bv 64 (kz_b kc)) by exact (bm_ew_y g pos c regs2 ys 1).
assert (X39 : ew E 39 = Z_to_bv 64 (d_dev d)) by exact (bm_ew_y g pos c regs2 ys 2).
assert (X40 : ew E 40 = Z_to_bv 64 (d_strips d)) by exact (bm_ew_y g pos c regs2 ys 3).
assert (X41 : ew E 41 = Z_to_bv 64 (d_chars d)) by exact (bm_ew_y g pos c regs2 ys 4).
assert (X42 : ew E 42 = Z_to_bv 64 (d_counter d)) by exact (bm_ew_y g pos c regs2 ys 5).
assert (XW : forall j, (j < 8)%nat -> ew E (43 + j) = Z_to_bv 64 (nth j (kz_want kc) 0)).
{ intros j Hj. change (43 + j)%nat with (BM_X0 + (6 + j))%nat.
  transitivity (Z_to_bv 64 (nth (6 + j) ys 0)); [exact (bm_ew_y g pos c regs2 ys (6 + j)) |].
  f_equal. unfold ys, o5_ys. rewrite app_nth2 by (cbn; lia). cbn [length].
  replace (6 + j - 6)%nat with j by lia. rewrite nth_firstn. replace (j <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  reflexivity. }
assert (QW : forall j, (j < 8)%nat ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 336 + Z.of_nat j) 1 (nth j (kz_want kc) 0) /\
  0 <= nth j (kz_want kc) 0 < 256).
{ intros j Hj. destruct (Gwant j ltac:(lia)) as [G Q]. split; [|exact Q].
  replace (FA g pos + 336 + Z.of_nat j) with (FA g pos + 192 + 144 + Z.of_nat j) by lia. exact G. }
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (EF : ew E 33 = Z_to_bv 64 (FA g pos)) by (subst E; apply bm_ew_F).
assert (UF : bv_unsigned (ew E 33) = FA g pos) by (rewrite EF; apply unsigned_lit_small; lia).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by (subst E; apply bm_ew_SH).
assert (Hshb : 0x7fff8000 <= shadow_addr (FA g pos) /\ shadow_addr (FA g pos) + 64 <= 0x10007fff8000 /\
  (shadow_addr (FA g pos) + 64 <= FA g pos \/ FA g pos + 512 <= shadow_addr (FA g pos))).
{ unfold shadow_addr, SHADOW_OFF. assert (FA g pos / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  change (0x7fffff800000 / 8) with 17592184995840 in *. assert (0 <= FA g pos / 8) by (apply Z.div_pos; lia).
  assert (8 * (FA g pos / 8) <= FA g pos) by (apply Z.mul_div_le; lia). appn. lia. }
assert (U34 : bv_unsigned (ew E 34) = shadow_addr (FA g pos)) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E22 : ew E 22 = Z_to_bv 64 dv).
{ subst E. rewrite (bm_ew_reg g pos c regs2 ys 22 22%bv eq_refl), R22. reflexivity. }
assert (U22 : bv_unsigned (ew E 22) = dv) by (rewrite E22; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (bm_ew_SB g pos c regs2 ys).
(* the entry state *)
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) o5_rs).
{ unfold o5_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
    [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]].
  6: { unfold o5_d. apply (owe_desk_region_ok B TL E W2 mem2 (kz_p kc) dv d); [exact HRO | exact Hpd | exact U22 |].
       intros i Hi. destruct i as [|[|[|[|i]]]]; cbn [nth desk_bytesZ];
       [exact (DX _ _ X39) | exact (DX _ _ X40) | exact (DX _ _ X41) | exact (DX _ _ X42) | lia]. }
  all: unfold o5_k, o5_wa, o5_wc, o5_wb, o5_l;
    (apply (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
     [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ]).
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 216 4 (SOff 37 0) (kz_a kc)); [exact (DX 37%nat _ X37) | zside | zside |].
      replace (FA g pos + 216) with (FA g pos + 192 + 24) by lia. exact Va.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 220 4 (SOff 38 0) (kz_b kc)); [exact (DX 38%nat _ X38) | zside | zside |].
      replace (FA g pos + 220) with (FA g pos + 192 + 28) by lia. exact Vb.
  - apply Forall_cons.
    { apply (chunk_ok_val tfibsegs E _ (FA g pos) 332 4 (SLit 0) 0); [reflexivity | zside | zside |].
      replace (FA g pos + 332) with (FA g pos + 192 + 140) by lia. rewrite <- Hw0. exact Vwrc. }
    repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 (SOff ?n 0))) =>
      let j := eval compute in (Z.to_nat (o - 336)) in
      destruct (QW j ltac:(lia)) as [G Q];
      apply (chunk_ok_val tfibsegs E _ (FA g pos) o 1 (SOff n 0) (nth j (kz_want kc) 0));
      [exact (DX _ _ (XW j ltac:(lia))) | cbn; lia | zside |];
      replace (FA g pos + o) with (FA g pos + 336 + Z.of_nat j) by (cbn; lia); exact G end.
  - repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 (SOff ?n 0))) =>
      let j := eval compute in (Z.to_nat (o - 336)) in
      destruct (QW j ltac:(lia)) as [G Q];
      apply (chunk_ok_val tfibsegs E _ (FA g pos) o 1 (SOff n 0) (nth j (kz_want kc) 0));
      [exact (DX _ _ (XW j ltac:(lia))) | cbn; lia | zside |];
      replace (FA g pos + o) with (FA g pos + 336 + Z.of_nat j) by (cbn; lia); exact G end.
  - repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 (SOff ?n 0))) =>
      let j := eval compute in (Z.to_nat (o - 336)) in
      destruct (QW j ltac:(lia)) as [G Q];
      apply (chunk_ok_val tfibsegs E _ (FA g pos) o 1 (SOff n 0) (nth j (kz_want kc) 0));
      [exact (DX _ _ (XW j ltac:(lia))) | cbn; lia | zside |];
      replace (FA g pos + o) with (FA g pos + 336 + Z.of_nat j) by (cbn; lia); exact G end.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 360 8 (SLit 0) 0); [reflexivity | zside | zside |].
      replace (FA g pos + 360) with (FA g pos + 192 + 168) by lia. rewrite <- Hwl0. exact Vwl.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 368 4 (SLit 0) 0); [reflexivity | zside | zside |].
      replace (FA g pos + 368) with (FA g pos + 192 + 176) by lia. rewrite <- Hwk0. exact Vwk.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 372 4 (SLit 0) 0); [reflexivity | zside | zside |].
      replace (FA g pos + 372) with (FA g pos + 192 + 180) by lia. rewrite <- Hwd0. exact Vwd. }
pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos dv 12 0 512 HAR HinS ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(change (fs_frame_bytes 3) with 512; lia)) as GAP. rewrite EFA in GAP.
pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos 0x10000 0x5ec000 0 512 HAR HinS ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(change (fs_frame_bytes 3) with 512; lia)) as GAPI. rewrite EFA in GAPI.
assert (Hpd2 : pairwise_disjoint E o5_rs).
{ unfold o5_rs, o5_k, o5_wa, o5_wc, o5_wb, o5_l, o5_d, owe_desk_region, bm_frame_region.
  cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UF, U22. repeat split; lia. }
assert (Hap : Forall (fun r => all_disjoint E r bm_regs) o5_rs).
{ unfold o5_rs. repeat apply Forall_cons; try apply Forall_nil.
  1-5: apply (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
       [exact HJ | exact Hfr | exact HC | lia | lia].
  apply (owe_desk_apart_base E _ dv sp1 U22 ltac:(lia) U2). lia. }
assert (HAF : atoms_ok E o5_AF).
{ unfold o5_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U22, X37, X38, X39, X40, X41, X42. rewrite !unsigned_lit_small by lia. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; lia. }
pose proof (bm_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c (owe_pc 5) ys o5_rs o5_AF
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) Hrs Hpd2 Hap HAF) as HS.
(* lia splits every disjunction of the context: hide the ones the walk no longer needs as such *)
cw_hide Hshb. cw_hide Hdv. cw_hide Hpv. cw_hide GAPI. clear GAP.
fold E in HS. change (owe_pc 5) with 0x82af0 in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_desk_SH; owe_SHk] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - exact (owe_desk_shent B ly2 S2 W2 mem2 md2 E (kz_p kc) dv d GM IV HAR Hpd E22 E32).
  - exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys HJ Hfr HC). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 8 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (HAE : env_agree 37 (bm_env g pos c regs2 ys) E) by (subst E; apply env_agree_refl).
pose proof HJ as HJR.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
assert (OK : owe_kZ kc (Some d) = owe_spec 5 (Some d) (kz_a kc) (kz_b kc) (kz_c kc) (kz_delta kc) (kz_bytes kc) (kz_n kc))
  by (unfold owe_kZ; rewrite Hkind; reflexivity).
assert (QA : forall j, (j < 8)%nat -> 0 <= nth j (kz_want kc) 0 < 256) by (intros j Hj; apply (QW j Hj)).
pose proof (QA 0%nat ltac:(lia)) as Q0. pose proof (QA 1%nat ltac:(lia)) as Q1. pose proof (QA 2%nat ltac:(lia)) as Q2.
pose proof (QA 3%nat ltac:(lia)) as Q3. pose proof (QA 4%nat ltac:(lia)) as Q4. pose proof (QA 5%nat ltac:(lia)) as Q5.
pose proof (QA 6%nat ltac:(lia)) as Q6. pose proof (QA 7%nat ltac:(lia)) as Q7.
unfold cfg_at. change (w64 0x82af0) with (Z_to_bv 64 0x82af0).
(* 0x82af0 the desk checks, the check of the strips byte's shadow, lw a, lbu strips, to bgeu a,strips *)
cw_run ltac:(o5_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF U34 EFA). cw_keep ltac:(owe_kwr U2 UF).
(* the run took two fresh atoms (51, 52); E1 agrees with E below 51 *)
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ => set (E1 := Ev) in * end.
assert (HA1 : env_agree 51 E E1) by (subst E1; apply env_agree_ewset2).
assert (HAE1 : env_agree 37 (bm_env g pos c regs2 ys) E1) by (subst E1; env_agree_chain HAE).
assert (U2_1 : bv_unsigned (ew E1 2) = sp1) by (rewrite (proj1 HA1 2%nat ltac:(lia)); exact U2).
assert (UF1 : bv_unsigned (ew E1 33) = FA g pos) by (rewrite (proj1 HA1 33%nat ltac:(lia)); exact UF).
assert (U34_1 : bv_unsigned (ew E1 34) = shadow_addr (FA g pos)) by (rewrite (proj1 HA1 34%nat ltac:(lia)); exact U34).
assert (DX1 : forall n v, ew E1 n = Z_to_bv 64 v -> sv_denot E1 (SOff n 0) = Z_to_bv 64 v)
  by (intros n v Hv; exact (o5_DX E1 n v Hv)).
assert (XW1 : forall j, (j < 8)%nat -> ew E1 (43 + j) = Z_to_bv 64 (nth j (kz_want kc) 0))
  by (intros j Hj; rewrite (proj1 HA1 (43 + j)%nat ltac:(lia)); exact (XW j Hj)).
cw_branch Hb1.
all: rewrite branch_geu_U, !(YCbn.U_agree 51 E E1 _ HA1) in Hb1 by reflexivity.
all: rewrite (owe_U_sx32 E 37 (kz_a kc) X37 ltac:(lia)), (U_atom E 40 (d_strips d) X40) in Hb1 by lia.
- (* strips <= a: the E_RANGE tail, to CHK *)
  apply negb_true_iff, Z.ltb_ge in Hb1.
  assert (Herr : d_strips d <= kz_a kc) by (destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia).
  cw_run_to ltac:(o5_awr sp1 (e_sp0 g) pos (FA g pos) U2_1 UF1 U34_1 EFA) 0x82dd4. cw_keep ltac:(owe_kwr U2_1 UF1).
  lazymatch goal with HS : st_ok _ ?Ec _ _ |- _ =>
    assert (HAE2 : env_agree 37 (bm_env g pos c regs2 ys) Ec) by env_agree_chain HAE;
    assert (HA2 : env_agree 51 E Ec) by env_agree_chain HA1;
    assert (XWc : forall j, (j < 8)%nat -> ew Ec (43 + j) = Z_to_bv 64 (nth j (kz_want kc) 0))
      by (intros j Hj; rewrite (proj1 HA2 (43 + j)%nat ltac:(lia)); exact (XW j Hj));
    pose proof (o5_DX Ec) as DXc end.
  let Ems := fresh "Ems" in
  pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Ems; rewrite Ems in HS; rewrite Ems; clear Ems.
  o5_fld HS 6%nat 332 4%N V332. o5_fld HS 6%nat 336 1%N V336. o5_fld HS 6%nat 337 1%N V337.
  o5_fld HS 6%nat 338 1%N V338. o5_fld HS 6%nat 339 1%N V339. o5_fld HS 7%nat 340 1%N V340.
  o5_fld HS 7%nat 341 1%N V341. o5_fld HS 7%nat 342 1%N V342. o5_fld HS 8%nat 343 1%N V343.
  o5_fld HS 9%nat 360 8%N V360. o5_fld HS 9%nat 368 4%N V368. o5_fld HS 9%nat 372 4%N V372.
  pose proof (XWc 0%nat ltac:(lia)) as XW0. pose proof (XWc 1%nat ltac:(lia)) as XW1'.
  pose proof (XWc 2%nat ltac:(lia)) as XW2. pose proof (XWc 3%nat ltac:(lia)) as XW3.
  pose proof (XWc 4%nat ltac:(lia)) as XW4. pose proof (XWc 5%nat ltac:(lia)) as XW5.
  pose proof (XWc 6%nat ltac:(lia)) as XW6. pose proof (XWc 7%nat ltac:(lia)) as XW7.
  cbn [Nat.add] in XW0, XW1', XW2, XW3, XW4, XW5, XW6, XW7.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
  lazymatch type of HS with st_ok _ ?Ec _ _ =>
  apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 8
    m3 r3 md3 Ec _ (-11) (firstn 8 (kz_want kc)) 0 0 0
    HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE2 HS) end end;
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | rewrite length_firstn, Lwant; reflexivity | rewrite length_firstn, Lwant; cbn; lia
  | exact KE | | | | | | lia | lia | lia | lia | ].
  * apply (owe_vm _ _ 4 _ _ V332). vm_compute. reflexivity.
  * intros j Hj. rewrite length_firstn, Lwant in Hj. cbn in Hj.
    rewrite nth_firstn, (proj2 (Nat.ltb_lt j 8) ltac:(lia)).
    split; [| apply (QW j); lia].
    destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];
    [ owe_byte V336 DXc XW0 | owe_byte V337 DXc XW1' | owe_byte V338 DXc XW2 | owe_byte V339 DXc XW3
    | owe_byte V340 DXc XW4 | owe_byte V341 DXc XW5 | owe_byte V342 DXc XW6 | owe_byte V343 DXc XW7 | lia ].
  * apply (owe_vm _ _ 8 _ _ V360). vm_compute. reflexivity.
  * apply (owe_vm _ _ 4 _ _ V368). vm_compute. reflexivity.
  * apply (owe_vm _ _ 4 _ _ V372). vm_compute. reflexivity.
  * apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply o5_spec_rng; lia.
- (* a < strips *)
  apply negb_false_iff, Z.ltb_lt in Hb1.
  assert (Ha : kz_a kc < d_strips d) by (destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia).
  (* 0x82b1c-0x82b24: lwu b, srli 15, bnez *)
  cw_run ltac:(o5_awr sp1 (e_sp0 g) pos (FA g pos) U2_1 UF1 U34_1 EFA). cw_keep ltac:(owe_kwr U2_1 UF1).
  cw_branch Hb2.
  all: rewrite branch_ne_U, U_lit in Hb2 by lia.
  all: lazymatch type of Hb2 with context [U ?Ev (SAlu ALU_SRL ?e (SLit 15))] =>
         rewrite (o5_U_srl15 Ev e (kz_b kc)
           ltac:(rewrite ?(YCbn.U_agree 51 E E1 _ HA1) by reflexivity;
                 first [ exact (U_atom E 38 (kz_b kc) X38 ltac:(lia))
                       | exact (o5_U_zx32 E 38 (kz_b kc) X38 ltac:(lia)) ]) ltac:(lia)) in Hb2 end.
  + (* b >= 2^15: the E_RANGE tail *)
    apply negb_true_iff, Z.eqb_neq in Hb2.
    assert (Herr : 2 ^ 15 <= kz_b kc).
    { destruct (Z.ltb_spec (kz_b kc) (2 ^ 15)) as [Hl|Hl]; [|exact Hl]. exfalso. apply Hb2.
      rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. }
    cw_run_to ltac:(o5_awr sp1 (e_sp0 g) pos (FA g pos) U2_1 UF1 U34_1 EFA) 0x82dd4. cw_keep ltac:(owe_kwr U2_1 UF1).
    lazymatch goal with HS : st_ok _ ?Ec _ _ |- _ =>
      assert (HAE2 : env_agree 37 (bm_env g pos c regs2 ys) Ec) by env_agree_chain HAE;
      assert (HA2 : env_agree 51 E Ec) by env_agree_chain HA1;
      assert (XWc : forall j, (j < 8)%nat -> ew Ec (43 + j) = Z_to_bv 64 (nth j (kz_want kc) 0))
        by (intros j Hj; rewrite (proj1 HA2 (43 + j)%nat ltac:(lia)); exact (XW j Hj));
      pose proof (o5_DX Ec) as DXc end.
    let Ems := fresh "Ems" in
    pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Ems; rewrite Ems in HS; rewrite Ems; clear Ems.
    o5_fld HS 6%nat 332 4%N V332. o5_fld HS 6%nat 336 1%N V336. o5_fld HS 6%nat 337 1%N V337.
    o5_fld HS 6%nat 338 1%N V338. o5_fld HS 6%nat 339 1%N V339. o5_fld HS 7%nat 340 1%N V340.
    o5_fld HS 7%nat 341 1%N V341. o5_fld HS 7%nat 342 1%N V342. o5_fld HS 8%nat 343 1%N V343.
    o5_fld HS 9%nat 360 8%N V360. o5_fld HS 9%nat 368 4%N V368. o5_fld HS 9%nat 372 4%N V372.
    pose proof (XWc 0%nat ltac:(lia)) as XW0. pose proof (XWc 1%nat ltac:(lia)) as XW1'.
    pose proof (XWc 2%nat ltac:(lia)) as XW2. pose proof (XWc 3%nat ltac:(lia)) as XW3.
    pose proof (XWc 4%nat ltac:(lia)) as XW4. pose proof (XWc 5%nat ltac:(lia)) as XW5.
    pose proof (XWc 6%nat ltac:(lia)) as XW6. pose proof (XWc 7%nat ltac:(lia)) as XW7.
    cbn [Nat.add] in XW0, XW1', XW2, XW3, XW4, XW5, XW6, XW7.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
    lazymatch type of HS with st_ok _ ?Ec _ _ =>
    apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 8
      m3 r3 md3 Ec _ (-11) (firstn 8 (kz_want kc)) 0 0 0
      HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE2 HS) end end;
    [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | rewrite length_firstn, Lwant; reflexivity | rewrite length_firstn, Lwant; cbn; lia
    | exact KE | | | | | | lia | lia | lia | lia | ].
    * apply (owe_vm _ _ 4 _ _ V332). vm_compute. reflexivity.
    * intros j Hj. rewrite length_firstn, Lwant in Hj. cbn in Hj.
      rewrite nth_firstn, (proj2 (Nat.ltb_lt j 8) ltac:(lia)).
      split; [| apply (QW j); lia].
      destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];
      [ owe_byte V336 DXc XW0 | owe_byte V337 DXc XW1' | owe_byte V338 DXc XW2 | owe_byte V339 DXc XW3
      | owe_byte V340 DXc XW4 | owe_byte V341 DXc XW5 | owe_byte V342 DXc XW6 | owe_byte V343 DXc XW7 | lia ].
    * apply (owe_vm _ _ 8 _ _ V360). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V368). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V372). vm_compute. reflexivity.
    * apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply o5_spec_rng; lia.
  + (* b < 2^15: to 0x82b2c, the store of the payload's shadow byte *)
    apply negb_false_iff, Z.eqb_eq in Hb2.
    assert (Hb15 : kz_b kc < 2 ^ 15).
    { rewrite Z.shiftr_div_pow2 in Hb2 by lia. destruct (Z.ltb_spec (kz_b kc) (2 ^ 15)) as [Hl|Hl]; [exact Hl|].
      assert (1 <= kz_b kc / 2 ^ 15) by (apply Z.div_le_lower_bound; lia). lia. }
    cw_run_to ltac:(o5_awr sp1 (e_sp0 g) pos (FA g pos) U2_1 UF1 U34_1 EFA) 0x82b2c. cw_keep ltac:(owe_kwr U2_1 UF1).
    (* 0x82b2c: the payload and the frame's shadow byte 4 join the state as writable regions *)
    lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ => set (E2 := Ev) in * end.
    assert (HA2 : env_agree 51 E E2) by (subst E2; env_agree_chain HA1).
    assert (U2_2 : bv_unsigned (ew E2 2) = sp1) by (rewrite (proj1 HA2 2%nat ltac:(lia)); exact U2).
    assert (UF2 : bv_unsigned (ew E2 33) = FA g pos) by (rewrite (proj1 HA2 33%nat ltac:(lia)); exact UF).
    assert (U34_2 : bv_unsigned (ew E2 34) = shadow_addr (FA g pos)) by (rewrite (proj1 HA2 34%nat ltac:(lia)); exact U34).
    assert (U22_2 : bv_unsigned (ew E2 22) = dv) by (rewrite (proj1 HA2 22%nat ltac:(lia)); exact U22).
    let Ems := fresh "Ems" in
    pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Ems; rewrite Ems in HS; rewrite Ems; clear Ems.
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ (mkst ?rx ?px ?mx ?romx)) =>
      assert (HSH2 : forall i, 0 <= i < 60 ->
        aview tfibsegs (w_H W2) mx (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) (shm 0) 0))
      by (intros i Hi; unfold cw_hold in Hshb; rewrite (KE (shadow_addr (FA g pos) + i));
          [exact (HSH i Hi) | lia | unfold owe_zone; lia]);
      pose proof HJR as (HAR2 & _);
      assert (Rpay : region_ok tfibsegs E2 (ms_mem (restrict (w_H W2) (mkst rx px mx romx))) o5_pay)
      by (rewrite restrict_mkst_fx; cbn [ms_mem]; unfold o5_pay;
          apply (o5_fr_region_ok B LAWS E2 W2 ly2 S2 mx _ pos (FA g pos) 32 35 32 35 [] HAR2 HinS EFA UF2);
          [lia | lia | lia | lia | lia | lia | lia | apply Forall_nil]);
      assert (Dpay : all_disjoint E2 o5_pay (ss_mem ssx))
      by (let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l;
          unfold o5_pay, bm_frame_region; cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U2_2, ?UF2, ?U22_2; unfold cw_hold in GAPI; repeat split; lia);
      pose proof (ast_ok_add_region tfibsegs E2 ssx _ o5_pay HS ltac:(vm_compute; reflexivity) Rpay Dpay) as HS1;
      cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1; clear HS Rpay Dpay; rename HS1 into HS
    end.
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ (mkst ?rx ?px ?mx ?romx)) =>
      assert (Rsh : region_ok tfibsegs E2 (ms_mem (restrict (w_H W2) (mkst rx px mx romx))) o5_sh0)
      by (rewrite restrict_mkst_fx; cbn [ms_mem]; unfold o5_sh0;
          apply (o5_sh_region_ok B LAWS E2 W2 ly2 S2 mx _ pos (FA g pos) bm_shm0 4 5 HAR2 HinS EFA Hf64);
          [lia | lia | exact U34_2 | reflexivity | intros i Hi; rewrite bm_shm0_eq; exact (HSH2 i Hi) | lia | lia]);
      assert (Dsh : all_disjoint E2 o5_sh0 (ss_mem ssx))
      by (let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l;
          unfold o5_sh0, bm_shadow_region; cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U2_2, ?UF2, ?U22_2, ?U34_2;
          unfold cw_hold in Hshb; repeat split; lia);
      pose proof (ast_ok_add_region tfibsegs E2 ssx _ o5_sh0 HS ltac:(vm_compute; reflexivity) Rsh Dsh) as HS1;
      cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1; clear HS Rsh Dsh; rename HS1 into HS
    end.
    (* the kept-memory fact over o5_zone from here on *)
    lazymatch type of KE with forall a, _ -> _ -> aview _ _ ?mx a = _ =>
      assert (KE5 : forall a, 0 <= a < 2 ^ 64 -> ~ o5_zone g pos sp1 a ->
        aview tfibsegs (w_H W2) mx a = aview tfibsegs (w_H W2) mem2 a)
        by (intros a Ha' Hz; apply KE; [exact Ha' | intros Hz'; apply Hz; left; exact Hz']) end.
    clear KE. rename KE5 into KE.
    (* 0x82b2c-0x82b50: shadow byte 4 := 3, p[0] = a | (b & 1) << 6, p[1] = p[2] = 0, a2 = 2, a3 = -2 *)
    aj_run_to_sh tfibtbl_lib_ok HS HJR 0x82b54. { o5_awr sp1 (e_sp0 g) pos (FA g pos) U2_2 UF2 U34_2 EFA. }
    cw_ajA HJR.
    cw_keep ltac:(o5_kwr U2_2 UF2 U34_2).
    (* the loop head 0x82b54: its numbers from the state *)
    let Ems := fresh "Ems" in
    pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Ems; rewrite Ems in HS; rewrite Ems; clear Ems.
    lazymatch type of HS with st_ok _ _ ?ssx _ => change (ss_pc ssx) with 535380 in HS |- * end.
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ (mkst ?rx ?px ?mx ?romx)) =>
      assert (RR : forall r, getr rx r = sv_denot E2 (sr_get (ss_regs ssx) r))
        by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W2) E2 ssx _ r HS)) end.
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ (mkst ?rx ?px ?mx ?romx)) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
      let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
      pose proof (st_ok_region_nth E2 ssx _ 0 r0 HS ltac:(vm_compute; reflexivity)) as RshL;
      pose proof (st_ok_region_nth E2 ssx _ 1 r1 HS ltac:(vm_compute; reflexivity)) as RpayL end.
    rewrite restrict_mkst_fx in RshL, RpayL. cbn [ms_mem] in RshL, RpayL.
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ (mkst ?rx ?px ?mx ?romx)) =>
      pose proof (bm_sh_read E2 W2 mx _ (shadow_addr (FA g pos)) 4 3 RshL
        ltac:(cbn [YP09.r_base base_val]; exact U34_2) ltac:(cbn [YP09.r_chunks]; left; reflexivity)) as SH4 end.
    change (3 mod 256) with 3 in SH4.
    pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 33 1 _ RpayL UF2 ltac:(owe_in) ltac:(cbn; lia)) as P33.
    pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 34 1 _ RpayL UF2 ltac:(owe_in) ltac:(cbn; lia)) as P34.
    pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 32 1 _ RpayL UF2 ltac:(owe_in) ltac:(cbn; lia)) as P32.
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ (mkst ?rx ?px ?mx ?romx)) =>
      assert (VK : forall a (m : nat) v, (forall i, 0 <= i < Z.of_nat m -> ~ o5_zone g pos sp1 (a + i)) ->
        0 <= a -> a + Z.of_nat m <= 2 ^ 64 ->
        val_mem tfibsegs (mrestrict (w_H W2) mem2) a m v -> val_mem tfibsegs (mrestrict (w_H W2) mx) a m v)
        by (intros a m0 v Hz Ha0 Ham0 Hv; apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mx); [|exact Hv];
            intros x Hx; apply KE; [clear - Hx Ha0 Ham0; lia|]; replace x with (a + (x - a)) by ring; apply Hz; clear - Hx; lia) end.
    pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V16 & V24 & V32 & V40 & V48 & V56 & V64 &
      V72 & V80 & V88 & V96 & V104 & V112 & _).
    assert (X38_2 : ew E2 38 = Z_to_bv 64 (kz_b kc)) by (rewrite (proj1 HA2 38%nat ltac:(lia)); exact X38).
    assert (E32_2 : ew E2 32 = Z_to_bv 64 SB) by (rewrite (proj1 HA2 32%nat ltac:(lia)); exact E32).
    (* 0x82b54-0x82bd4: the 14 passes *)
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ (mkst ?rx ?px ?mx ?romx)) =>
    eapply (o5_loop B LAWS 14 0 W2 rx mx _ LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(3, pos)] ly2 S2 kj _ pos (kz_b kc) (FA g pos) sp1 ltac:(lia) ltac:(lia) ltac:(lia) HJR ltac:(left; reflexivity)
      HinS EFA);
    [ rewrite (RR 11%bv); change (sr_get (ss_regs ssx) 11%bv) with (SOff 38 0); rewrite (o5_DX E2 38 _ X38_2); reflexivity
    | rewrite (RR 12%bv); change (sr_get (ss_regs ssx) 12%bv) with (SLit 2); reflexivity
    | rewrite (RR 13%bv); change (sr_get (ss_regs ssx) 13%bv) with (SLit 18446744073709551614); reflexivity
    | rewrite (RR 9%bv); change (sr_get (ss_regs ssx) 9%bv) with (SOff 2 0); cbn [sv_denot]; rewrite U2_2, Z.add_0_r;
      reflexivity
    | rewrite (RR 21%bv); change (sr_get (ss_regs ssx) 21%bv) with (SOff 32 0); rewrite (o5_DX E2 32 _ E32_2);
      rewrite <- SB_SHADOW_OFF; reflexivity
    | rewrite (RR 26%bv); change (sr_get (ss_regs ssx) 26%bv) with (SLit 1); reflexivity
    | exact Hf64 | exact Happ | lia | lia | lia
    | apply (VK _ 8%nat); [intros i Hi; cbn in Hi; unfold o5_zone, owe_zone; unfold cw_hold in Hshb; lia | lia | cbn; lia
      | exact V88]
    | apply (VK _ 8%nat); [intros i Hi; cbn in Hi; unfold o5_zone, owe_zone; unfold cw_hold in Hshb; lia | lia | cbn; lia
      | exact V96]
    | apply (VK _ 8%nat); [intros i Hi; cbn in Hi; unfold o5_zone, owe_zone; unfold cw_hold in Hshb; lia | lia | cbn; lia
      | exact V112]
    | apply (owe_vm _ _ 1 _ _ P33); vm_compute; reflexivity
    | apply (owe_vm _ _ 1 _ _ P34); vm_compute; reflexivity
    | exact (o5_ra3 W2 mx (FA g pos) Hf64 SH4)
    | appn; lia
    | ] end.
    (* 0x82fb0: the state re-seated without the payload and the shadow byte; the loop's registers fresh atoms *)
    intros regs' mem' md' HJ' Hk' V33' V34' KE'.
    pose proof HJ' as (HAR3 & _).
    destruct (al_frames _ _ LAWS ly2 S2 W2 mem' md' 3 pos HAR3 HinS) as (_ & _ & Hpr3 & _). rewrite EFA in Hpr3.
    pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk3 & _).
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ (mkst ?rx ?px ?mx ?romx)) =>
      assert (KEPT : Forall (region_kept tfibsegs E2 (ms_mem (restrict (w_H W2) (mkst rx px mx romx)))
        (mrestrict (w_H W2) mem')) (skipn 2 (ss_mem ssx)));
      [ rewrite restrict_mkst_fx; cbn [ms_mem];
        let l := eval vm_compute in (skipn 2 (ss_mem ssx)) in change (skipn 2 (ss_mem ssx)) with l;
        unfold cw_hold in GAPI;
        repeat apply Forall_cons; try apply Forall_nil;
        (apply (o5_region_kept E2 (w_H W2) mx mem' (fun a => FA g pos + 33 <= a < FA g pos + 35));
         [ exact KE'
         | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
           cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; rewrite ?U2_2, ?UF2, ?U22_2 in Ha; split; lia
         | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
           cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U2_2, ?UF2, ?U22_2 in Ha;
           first [ lia | apply Hstk3; lia
                 | exact (proj1 (Hpr3 a ltac:(change (fs_frame_bytes 3) with 512; lia))) ] ])
      | ] end.
    lazymatch type of HS with st_ok _ ?Ec ?ssx (restrict ?Hh (mkst ?rx ?px ?mx ?romx)) =>
      let Kk := eval vm_compute in (run_K 0 CW_Bx [] ssx) in
      pose proof (st_ok_after_stretch tfibsegs Kk Ec ssx (restrict Hh (mkst rx px mx romx)) regs' (mrestrict Hh mem')
        (skipn 2 (ss_mem ssx)) 0x82fb0 O5_CLOB HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (o5_submem2 _) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) (fun r Hr => Hk' r Hr) KEPT) as HS3 end.
    rewrite <- restrict_mkst_fx in HS3. clear HS KEPT. rename HS3 into HS.
    clear HJR. rename HJ' into HJR.
    assert (KE3 : forall a, 0 <= a < 2 ^ 64 -> ~ o5_zone g pos sp1 a ->
      aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) mem2 a).
    { intros a Ha' Hz. rewrite (KE' a Ha' ltac:(intros Hz'; apply Hz; right; left; lia)). exact (KE a Ha' Hz). }
    assert (SH4' : aview tfibsegs (w_H W2) mem' (shadow_addr (FA g pos) + 4) = Some 3)
      by (rewrite KE'; [exact SH4 | unfold cw_hold in Hshb; lia | unfold cw_hold in Hshb; lia]).
    clear KE. rename KE3 into KEm.
    lazymatch type of HS with st_ok _ ?Ev _ _ => set (E3 := Ev) in * end.
    assert (HA3 : env_agree 51 E E3) by (subst E3; env_agree_chain HA2).
    assert (U2_3 : bv_unsigned (ew E3 2) = sp1) by (rewrite (proj1 HA3 2%nat ltac:(lia)); exact U2).
    assert (UF3 : bv_unsigned (ew E3 33) = FA g pos) by (rewrite (proj1 HA3 33%nat ltac:(lia)); exact UF).
    assert (U34_3 : bv_unsigned (ew E3 34) = shadow_addr (FA g pos)) by (rewrite (proj1 HA3 34%nat ltac:(lia)); exact U34).
    assert (SHOK3 : sh_ok tfibsegs CW_Bx [owe_desk_SH; owe_SHk] E3 (mrestrict (w_H W2) mem')).
    { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - exact (owe_desk_shent B ly2 S2 W2 mem' md' E3 (kz_p kc) dv d GM IV HAR3 Hpd
          ltac:(rewrite (proj1 HA3 22%nat ltac:(lia)); exact E22) ltac:(rewrite (proj1 HA3 32%nat ltac:(lia)); exact E32)).
      - apply (o5_k_shent E3 W2 mem' (FA g pos) Hf64 Hf4096 Happ ltac:(lia));
        [ intros i Hi; rewrite (KEm (shadow_addr (FA g pos) + i));
          [ rewrite (HSH i ltac:(lia)); f_equal; apply o5_shm0_k; lia
          | unfold cw_hold in Hshb; lia
          | unfold o5_zone, owe_zone; unfold cw_hold in Hshb; lia ]
        | rewrite (proj1 HA3 33%nat ltac:(lia)); exact EF
        | rewrite (proj1 HA3 32%nat ltac:(lia)); exact E32 ]. }
    clear SHOK. rename SHOK3 into SHOK.
    (* from here the kept-memory fact is relative to mem' (the shadow byte 4 is 3 there) *)
    assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 8 a ->
      aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) mem' a) by (intros; reflexivity).
    (* 0x82fb0-0x82fec: the check of the dev byte's shadow, s9, want[0..4), the copy's arguments, jal *)
    cw_run ltac:(o5_awr sp1 (e_sp0 g) pos (FA g pos) U2_3 UF3 U34_3 EFA). cw_keep ltac:(owe_kwr U2_3 UF3).
    (* 0x51ae8: __asan_memcpy(want + 4 = F + 340, p = F + 32, 3) *)
    lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
      assert (RR4 : forall r, getr (ms_regs msx) r = sv_denot Ev (sr_get (ss_regs ssx) r))
        by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W2) Ev ssx msx r HS)) end.
    lazymatch type of HS with st_ok _ ?Ev _ _ => set (E4 := Ev) in * end.
    assert (HA4 : env_agree 51 E E4) by (subst E4; env_agree_chain HA3).
    assert (EF4 : ew E4 33 = Z_to_bv 64 (FA g pos)) by (rewrite (proj1 HA4 33%nat ltac:(lia)); exact EF).
    assert (E2_4 : ew E4 2 = Z_to_bv 64 sp1).
    { rewrite (proj1 HA4 2%nat ltac:(lia)). subst E. rewrite (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. reflexivity. }
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
      assert (SV4 : forall i, 0 <= i < 60 -> i <> 4 ->
        aview tfibsegs (w_H W2) (ms_mem msx) (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) (shm 0) 0))
      by (intros i Hi H4; unfold cw_hold in Hshb; rewrite (KE (shadow_addr (FA g pos) + i)) by (unfold owe_zone; lia);
          rewrite (KEm (shadow_addr (FA g pos) + i)) by (unfold o5_zone, owe_zone; lia); exact (HSH i Hi));
      assert (SB4 : aview tfibsegs (w_H W2) (ms_mem msx) (shadow_addr (FA g pos) + 4) = Some 3)
      by (unfold cw_hold in Hshb; rewrite (KE (shadow_addr (FA g pos) + 4)) by (unfold owe_zone; lia); exact SH4') end.
    assert (U2_4 : bv_unsigned (ew E4 2) = sp1) by (rewrite E2_4; apply unsigned_lit_small; lia).
    assert (UF4 : bv_unsigned (ew E4 33) = FA g pos) by (rewrite EF4; apply unsigned_lit_small; lia).
    assert (U22_4 : bv_unsigned (ew E4 22) = dv) by (rewrite (proj1 HA4 22%nat ltac:(lia)); exact U22).
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
      assert (SPZ : spZ (ms_regs msx) = sp1)
        by (unfold spZ; rewrite (RR4 2%bv); change (sr_get (ss_regs ssx) 2%bv) with (SOff 2 0);
            rewrite (o5_DX E4 2 sp1 E2_4); apply unsigned_lit_small; lia);
      (* the payload's bytes in the call state *)
      assert (PB33 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msx)) (FA g pos + 33) 1 (fst (owe_ring (kz_b kc))))
        by (apply (cw_val_mem_kept (w_H W2) (w_H W2) mem' (ms_mem msx)); [|exact V33'];
            intros x Hx; apply KE; [lia | unfold owe_zone; cbn in Hx; lia]);
      assert (PB34 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msx)) (FA g pos + 34) 1 (snd (owe_ring (kz_b kc))))
        by (apply (cw_val_mem_kept (w_H W2) (w_H W2) mem' (ms_mem msx)); [|exact V34'];
            intros x Hx; apply KE; [lia | unfold owe_zone; cbn in Hx; lia])
    end.
    lazymatch type of P32 with val_mem _ _ _ _ ?v32 =>
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
      assert (PB32 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msx)) (FA g pos + 32) 1 v32)
        by (apply (cw_val_mem_kept (w_H W2) (w_H W2) mem' (ms_mem msx));
            [ intros x Hx; apply KE; [lia | unfold owe_zone; cbn in Hx; lia]
            | eapply (cw_val_mem_kept (w_H W2) (w_H W2) _ mem'); cycle 1;
              [ exact P32 | intros x Hx; apply KE'; [lia | cbn in Hx; lia] ] ]) end end.
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
      let kk := eval vm_compute in (run_K 0 CW_Bx [] ssx) in
      let rs := eval vm_compute in (List.filter o5_callkeep (ss_mem ssx)) in
      eapply (cw_intrin_call B LAWS OCpy BM_asan_memcpy AMEMCPY W2 E4 ssx msx _ LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g)
        (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 kj (FA g pos + 340) (FA g pos + 32) 3 0x82ff0 kk rs _ HS
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJR);
      [ rewrite (RR4 10%bv); change (sr_get (ss_regs ssx) 10%bv) with (SOff 33 340);
        rewrite (bm_den_off E4 33 (FA g pos) 340 EF4) by lia; reflexivity
      | rewrite (RR4 11%bv); change (sr_get (ss_regs ssx) 11%bv) with (SOff 33 32);
        rewrite (bm_den_off E4 33 (FA g pos) 32 EF4) by lia; reflexivity
      | rewrite (RR4 12%bv); change (sr_get (ss_regs ssx) 12%bv) with (SLit 3); reflexivity
      | lia | lia | lia
      | rewrite SPZ; change ESTACK with 4096; lia
      | rewrite SPZ; lia
      | rewrite SPZ; rewrite (Z.div_mod sp1 32) by lia; rewrite Hsp32, Z.add_0_r;
        replace (32 * (sp1 / 32)) with ((sp1 / 32 * 2) * 16) by ring; apply Z_mod_mult
      | exact Hsp016
      | rewrite (RR4 3%bv); change (sr_get (ss_regs ssx) 3%bv) with (SOff 3 0); cbn [sv_denot];
        rewrite (proj1 HA4 3%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; subst E;
        rewrite (bm_ew_reg g pos c regs2 ys 3 3%bv eq_refl); exact R3
      | rewrite (RR4 4%bv); change (sr_get (ss_regs ssx) 4%bv) with (SOff 4 0); cbn [sv_denot];
        rewrite (proj1 HA4 4%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; subst E;
        rewrite (bm_ew_reg g pos c regs2 ys 4 4%bv eq_refl); exact R4
      | vm_compute; reflexivity
      | lia
      | apply ret_ok_even; vm_compute; reflexivity
      | intros a Hda; split;
        [ right; right; right; exists 3, pos; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
          rewrite EFA; change (fs_frame_bytes 3) with 512; lia
        | rewrite SPZ; change ESTACK with 4096; lia ]
      | appn; lia
      | apply (block_shadow_range (aview tfibsegs (w_H W2) (ms_mem msx)) SHADOW_OFF (FA g pos + 192) 184
          (FA g pos + 340) 3); [ | lia | lia ];
        apply (bm_block_shadow W2 (ms_mem msx) (FA g pos) 192 184 Hf64); [lia | reflexivity | lia |];
        intros i Hi; change ((184 + 7) / 8) with 23 in Hi; change (192 / 8) with 24; change (184 / 8) with 23;
        replace (i <? 23) with true by (symmetry; apply Z.ltb_lt; lia);
        rewrite (SV4 (24 + i) ltac:(lia) ltac:(lia)); f_equal; apply o5_shm0_k; lia
      | intros _; apply (o5_hull W2 (ms_mem msx) (FA g pos) 340 3 Hf64); [lia | lia | lia |];
        intros i Hi; destruct (Z.eq_dec i 4) as [-> | Hne]; [rewrite SB4; discriminate | rewrite (SV4 i Hi Hne); discriminate]
      | split; [lia|]; split; [lia|]; split;
        [ intros a Hda; split;
          [ assert (Ha3 : a = FA g pos + 32 \/ a = FA g pos + 33 \/ a = FA g pos + 34) by lia;
            destruct Ha3 as [-> | [-> | ->]];
            [exact (o5_aview_vm _ _ _ _ PB32) | exact (o5_aview_vm _ _ _ _ PB33) | exact (o5_aview_vm _ _ _ _ PB34)]
          | rewrite SPZ; change ESTACK with 4096; lia ] |];
        split; [lia|]; split; [appn; lia|]; split; [exact (o5_ra3 W2 (ms_mem msx) (FA g pos) Hf64 SB4)|];
        intros _; apply (o5_hull W2 (ms_mem msx) (FA g pos) 32 3 Hf64); [lia | lia | lia |];
        intros i Hi; destruct (Z.eq_dec i 4) as [-> | Hne]; [rewrite SB4; discriminate | rewrite (SV4 i Hi Hne); discriminate]
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | exact (o5_submem_filter o5_callkeep (ss_mem ssx))
      | repeat apply Forall_cons; try apply Forall_nil;
        (split; [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
                  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; rewrite ?U2_4, ?UF4, ?U22_4 in Ha;
                  rewrite SPZ; change ESTACK with 4096;
                  split; lia
                | cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; lia ])
      | ] end.
    intros regs5 mem5 md5 HJ5 HP5 Ha05 HCP5 HK5 HPR5 HSM5 HS5.
    rewrite SPZ in HK5. change ESTACK with 4096 in HK5.
    clear HS. rename HS5 into HS.
    lazymatch type of HS with st_ok _ ?Ev _ _ => set (E5 := Ev) in * end.
    assert (HA5 : env_agree 51 E E5).
    { subst E5. split; [intros nn Hnn; rewrite ew_havoc_old by lia; exact (proj1 HA4 nn Hnn) | exact (proj2 HA4)]. }
    assert (U2_5 : bv_unsigned (ew E5 2) = sp1) by (rewrite (proj1 HA5 2%nat ltac:(lia)); exact U2).
    assert (UF5 : bv_unsigned (ew E5 33) = FA g pos) by (rewrite (proj1 HA5 33%nat ltac:(lia)); exact UF).
    assert (U34_5 : bv_unsigned (ew E5 34) = shadow_addr (FA g pos)) by (rewrite (proj1 HA5 34%nat ltac:(lia)); exact U34).
    assert (U22_5 : bv_unsigned (ew E5 22) = dv) by (rewrite (proj1 HA5 22%nat ltac:(lia)); exact U22).
    (* the frame's shadow bytes after the copy: byte 4 still 3 *)
    lazymatch type of SB4 with aview _ _ ?mC _ = _ =>
      assert (SV5 : forall i, 0 <= i < 60 ->
        aview tfibsegs (w_H W2) mem5 (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) o5_shm3 0))
      by (intros i Hi; unfold cw_hold in Hshb;
          rewrite (HK5 (shadow_addr (FA g pos) + i)) by lia;
          destruct (Z.eq_dec i 4) as [-> | Hne];
          [ exact SB4
          | rewrite (SV4 i Hi Hne), o5_shm3_nth by lia; reflexivity ]) end.
    pose proof HJ5 as (HAR5 & _).
    (* 0x82ff0: the shadow byte 4 joins the state again as a writable region *)
    assert (Rsh : region_ok tfibsegs E5 (mrestrict (w_H W2) mem5) (bm_shadow_region 4 5 o5_shm3)).
    { apply (o5_sh_region_ok B LAWS E5 W2 ly2 S2 mem5 md5 pos (FA g pos) o5_shm3 4 5 HAR5 HinS EFA Hf64 Hf4096
        ltac:(clear - Hfceil Hchi; unfold BM_HI in *; lia) U34_5 eq_refl SV5 ltac:(lia) ltac:(lia)). }
    lazymatch type of HS with st_ok _ _ ?ssx _ =>
      let l := eval vm_compute in (ss_mem ssx) in
      assert (Dsh : all_disjoint E5 (bm_shadow_region 4 5 o5_shm3) (ss_mem ssx))
      by (change (ss_mem ssx) with l;
          unfold bm_shadow_region; cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U2_5, ?UF5, ?U22_5, ?U34_5;
          unfold cw_hold in Hshb; repeat split; clear - Hshb Hsp Hsp0c Hclo Hfceil Hchi FFS Hdr Hf4096; unfold BM_HI in *; lia) end.
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ (mkst ?rx ?px ?mx ?romx)) =>
      pose proof (ast_ok_add_region tfibsegs E5 ssx _ (bm_shadow_region 4 5 o5_shm3) HS ltac:(vm_compute; reflexivity)
        ltac:(rewrite restrict_mkst_fx; exact Rsh) Dsh) as HS1 end.
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1. clear HS Rsh Dsh. rename HS1 into HS.
    (* the payload's bytes at want[4..7) after the copy *)
    cbv beta iota in HCP5.
    lazymatch type of PB32 with val_mem _ (mrestrict _ ?mC) _ _ ?v32 =>
      pose proof (o5_vm_move (w_H W2) mC mem5 (FA g pos + 32) (FA g pos + 340) v32 PB32
        ltac:(pose proof (HCP5 0 ltac:(lia)) as Hc; rewrite !Z.add_0_r in Hc; exact Hc)) as W340;
      pose proof (o5_vm_move (w_H W2) mC mem5 (FA g pos + 33) (FA g pos + 341) _ PB33
        ltac:(pose proof (HCP5 1 ltac:(lia)) as Hc; replace (FA g pos + 340 + 1) with (FA g pos + 341) in Hc by lia;
              replace (FA g pos + 32 + 1) with (FA g pos + 33) in Hc by lia; exact Hc)) as W341;
      pose proof (o5_vm_move (w_H W2) mC mem5 (FA g pos + 34) (FA g pos + 342) _ PB34
        ltac:(pose proof (HCP5 2 ltac:(lia)) as Hc; replace (FA g pos + 340 + 2) with (FA g pos + 342) in Hc by lia;
              replace (FA g pos + 32 + 2) with (FA g pos + 34) in Hc by lia; exact Hc)) as W342 end.
    (* the kept-memory fact over o5_zone, at mem5 *)
    assert (KEo : forall a, 0 <= a < 2 ^ 64 -> ~ o5_zone g pos sp1 a ->
      aview tfibsegs (w_H W2) mem5 a = aview tfibsegs (w_H W2) mem2 a).
    { intros a Ha' Hz. unfold o5_zone in Hz.
      rewrite HK5 by (unfold owe_zone in Hz; lia).
      rewrite KE by (exact Ha' || (intros Hz'; apply Hz; left; exact Hz')).
      exact (KEm a Ha' ltac:(unfold o5_zone; exact Hz)). }
    clear KE KEm KE' HK5 HCP5.
    cw_hide KEo.
    clear HJR. rename HJ5 into HJR.
    (* the tail's kept fact: o5_zone without want[4..7) *)
    assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (o5_zone g pos sp1 a /\ ~ (FA g pos + 340 <= a < FA g pos + 343)) ->
      aview tfibsegs (w_H W2) mem5 a = aview tfibsegs (w_H W2) mem5 a) by (intros; reflexivity).
    (* 0x82ff0-0x8301c: want_key, want[7], want_len, want_display, shadow byte 4 := 0xf8, j CHK *)
    aj_run_to_sh tfibtbl_lib_ok HS HJR 0x82dd4. { o5_awr sp1 (e_sp0 g) pos (FA g pos) U2_5 UF5 U34_5 EFA. }
    cw_ajA HJR.
    cw_keep ltac:(o5_kwr2 U2_5 UF5 U34_5 Hshb).
    unfold cw_hold in KEo.
    let Ems := fresh "Ems" in
    pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Ems; rewrite Ems in HS; rewrite Ems; clear Ems.
    lazymatch type of HS with st_ok _ _ ?ssx _ =>
      let pcv := eval vm_compute in (ss_pc ssx) in change (ss_pc ssx) with pcv in HS |- * end.
    lazymatch type of HS with st_ok _ ?Ec _ _ => set (E6 := Ec) in * end.
    assert (HAc : env_agree 51 E E6) by (apply (env_agree_trans 51 _ E5); [exact HA5 | subst E6; env_agree_chain (env_agree_refl 51 E5)]).
    assert (HAEc : env_agree 37 (bm_env g pos c regs2 ys) E6).
    { apply (env_agree_trans 37 _ E); [exact HAE|]. destruct HAc as [HAc1 HAc2]. split; [intros nn Hnn; apply HAc1; lia | exact HAc2]. }
    assert (X37c : ew E6 37 = Z_to_bv 64 (kz_a kc)) by (rewrite (proj1 HAc 37%nat ltac:(lia)); exact X37).
    assert (X39c : ew E6 39 = Z_to_bv 64 (d_dev d)) by (rewrite (proj1 HAc 39%nat ltac:(lia)); exact X39).
    assert (X37_2 : ew E2 37 = Z_to_bv 64 (kz_a kc)) by (rewrite (proj1 HA2 37%nat ltac:(lia)); exact X37).
    assert (UF6 : bv_unsigned (ew E6 33) = FA g pos) by (rewrite (proj1 HAc 33%nat ltac:(lia)); exact UF).
    assert (U34_6 : bv_unsigned (ew E6 34) = shadow_addr (FA g pos)) by (rewrite (proj1 HAc 34%nat ltac:(lia)); exact U34).
    pose proof (o5_acc_range (kz_b kc) 14 ltac:(lia)) as RR14. rewrite o5_acc_14 in RR14.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
      assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ o5_zone g pos sp1 a ->
        aview tfibsegs (w_H W2) m3 a = aview tfibsegs (w_H W2) mem2 a)
        by (intros a Ha' Hz; rewrite (KE a Ha' ltac:(intros [Hz1 _]; exact (Hz Hz1))); exact (KEo a Ha' Hz));
      assert (KC : forall a, FA g pos + 340 <= a < FA g pos + 343 ->
        aview tfibsegs (w_H W2) m3 a = aview tfibsegs (w_H W2) mem5 a)
        by (intros a Ha'; apply KE; [lia | intros [_ Hz2]; apply Hz2; lia]);
      assert (H4 : aview tfibsegs (w_H W2) m3 (shadow_addr (FA g pos) + 4) = Some (nth 4 (shm 0) 0))
    end.
    { lazymatch type of HS with st_ok _ ?Ev ?ssx _ =>
        let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
        pose proof (st_ok_region_nth Ev ssx _ 0 r0 HS ltac:(vm_compute; reflexivity)) as Rr0 end.
      rewrite restrict_mkst_fx in Rr0. cbn [ms_mem] in Rr0.
      eapply eq_trans;
        [ eapply (bm_sh_read _ W2 _ _ (shadow_addr (FA g pos)) 4 _ Rr0);
          [ cbn [YP09.r_base base_val]; exact U34_6 | cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]) ]
        | vm_compute; reflexivity ]. }
    o5_fldx HS 332 4%N V332. o5_fldx HS 336 2%N V336. o5_fldx HS 338 1%N V338. o5_fldx HS 339 1%N V339.
    o5_fldx HS 343 1%N V343. o5_fldx HS 360 8%N V360. o5_fldx HS 368 4%N V368. o5_fldx HS 372 4%N V372.
    destruct (owe_split2 _ _ _ 5104 V336 ltac:(vm_compute; reflexivity) ltac:(lia)) as (V336a & V337a).
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
    apply (o5_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d)
      m3 r3 md3 E6 _ 0 (o5_bs kc d) 8 (KEY 3 (kz_a kc)) 0 HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAEc HS) end.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * lazymatch type of HS with st_ok _ _ ?ssx _ =>
        let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l end.
      unfold bm_cur_region. repeat (first [left; reflexivity | right]).
    * reflexivity.
    * exact KF.
    * exact H4.
    * apply (owe_vm _ _ 4 _ _ V332). vm_compute. reflexivity.
    * intros j Hj. unfold o5_bs in Hj |- *. cbn [length] in Hj.
      destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; cbn [nth]; [ | | | | | | | | lia ].
      -- change (Z.of_nat 0) with 0. rewrite Z.add_0_r. split; [exact V336a | lia].
      -- change (Z.of_nat 1) with 1. split; [exact V337a | lia].
      -- change (Z.of_nat 2) with 2. split; [| apply owe_u8_range].
         replace (FA g pos + 336 + 2) with (FA g pos + 338) by lia. apply (owe_vm _ _ 1 _ _ V338).
         change (bv_unsigned (sv_denot ?E ?e)) with (U E e).
         first [ rewrite (o5_U_zx8 E6 39 _ X39c) by lia | rewrite (U_atom E6 39 _ X39c) by lia ].
         unfold u8. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite !Z.mod_mod by lia. reflexivity.
      -- change (Z.of_nat 3) with 3. split; [| lia].
         replace (FA g pos + 336 + 3) with (FA g pos + 339) by lia. apply (owe_vm _ _ 1 _ _ V339). vm_compute. reflexivity.
      -- change (Z.of_nat 4) with 4. split; [| apply owe_u8_range].
         replace (FA g pos + 336 + 4) with (FA g pos + 340) by lia.
         apply (owe_vm _ _ 1 _ _ (o5_vm_move (w_H W2) mem5 _ _ _ _ W340 (KC (FA g pos + 340) ltac:(lia)))).
         change (bv_unsigned (sv_denot ?E ?e)) with (U E e).
         rewrite (o5_U_p0 E2 (kz_a kc) (kz_b kc) X37_2 X38_2 ltac:(lia) ltac:(lia)).
         unfold u8. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite !Z.mod_mod by lia. reflexivity.
      -- change (Z.of_nat 5) with 5. split; [| lia].
         replace (FA g pos + 336 + 5) with (FA g pos + 341) by lia.
         exact (o5_vm_move (w_H W2) mem5 _ _ _ _ W341 (KC (FA g pos + 341) ltac:(lia))).
      -- change (Z.of_nat 6) with 6. split; [| lia].
         replace (FA g pos + 336 + 6) with (FA g pos + 342) by lia.
         exact (o5_vm_move (w_H W2) mem5 _ _ _ _ W342 (KC (FA g pos + 342) ltac:(lia))).
      -- change (Z.of_nat 7) with 7. split; [| lia].
         replace (FA g pos + 336 + 7) with (FA g pos + 343) by lia. apply (owe_vm _ _ 1 _ _ V343). vm_compute. reflexivity.
    * apply (owe_vm _ _ 8 _ _ V360). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V368). change (bv_unsigned (sv_denot ?E ?e)) with (U E e).
      rewrite (o5_U_key E6 (kz_a kc) X37c ltac:(lia)). change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
      change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V372). vm_compute. reflexivity.
    * lia.
    * lia.
    * exact (o5_key_range (kz_a kc)).
    * lia.
    * apply (owe_want_ok_succ kc (Some d) _ (o5_bs kc d) (KEY 3 (kz_a kc)) 0).
      { rewrite OK. apply o5_spec_ok; lia. }
      unfold o5_bs. cbn [length firstn app map]. unfold u8. rewrite !Z.mod_mod by lia.
      rewrite (Z.mod_small (fst (owe_ring (kz_b kc)))) by lia. rewrite (Z.mod_small (snd (owe_ring (kz_b kc)))) by lia.
      reflexivity.
Qed.
End b.
End a.
