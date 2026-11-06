(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 280 of its 313 lines of code are new or changed and 293 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0OddW.v at 111d25b4415f (its memory facts and o_walk; the engine runs are in lib/A/RtPgEnt0OddR.v) for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the shadow offset is in s2 (x18), &ch in s6 (x22), the entry in s8 (x24), so s8 is the one callee-saved register the block changes and there is no `s9 := s8`; G is 0x8150c; the strings lie below 0x21400; the frame's shadow has 56 bytes (RtPgMem.rtm_sh, seven flags); RPgMem / RPgBase are lib/A/RtPgMem.v / RtPgBase.v (rtm_*, rt_cstr, rt_fsh); the kit is lib/A/RtPgW7bKit.v / RtPgW7bCall.v; AR_laws is the kernel theorem AR_laws_ok in place of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0OddW.v at 21da95a5fcd3; image B (images.AsanUbsan): c is in a3 (x13), the shadow offset in s4 (x20), &ch in s2 (x18), the entry in s6 (x22) and t1 saved in s8 (x24) and put back (0x81e2c / 0x81e4c), so the block changes the callee-saved s6 and s8 and keeps t1; the walk has the B-only run 1t (the UBSan trap 0x81e0c); G is 0x8160c; the frame for locals is of class 4 (1024 bytes, 88 shadow bytes written: RtPgMemB.rtmb_sh) and the real frame is 0x220 bytes; the calls are the strlen wrapper 0x421ec (RtPgW7bCallB.w7b_astrlen_realizes) and __asan_memcpy 0x518b8; the kit is lib/AU/RtPgW7bKitB.v / RtPgW7bCallB.v / RtPgStepsB.v; names o_ -> ob_. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgEnt0OddWB.v, with its module paths, module names, addresses and numbers changed; 26 of its 312 lines of code are new or changed and 27 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0OddW.v at 111d25b4415f (its memory facts and o_walk; the engine runs are in lib/A/RtPgEnt0OddR.v) for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the shadow offset is in s2 (x18), &ch in s6 (x22), the entry in s8 (x24), so s8 is the one callee-saved register the block changes and there is no `s9 := s8`; G is 0x8150c; the strings lie below 0x21400; the frame's shadow has 56 bytes (RtPgMem.rtm_sh, seven flags); RPgMem / RPgBase are lib/A/RtPgMem.v / RtPgBase.v (rtm_*, rt_cstr, rt_fsh); the kit is lib/A/RtPgW7bKit.v / RtPgW7bCall.v; AR_laws is the kernel theorem AR_laws_ok in place of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0OddW.v at 21da95a5fcd3; image B (images.AsanUbsan): c is in a3 (x13), the shadow offset in s4 (x20), &ch in s2 (x18), the entry in s6 (x22) and t1 saved in s8 (x24) and put back (0x81e2c / 0x81e4c), so the block changes the callee-saved s6 and s8 and keeps t1; the walk has the B-only run 1t (the UBSan trap 0x81e0c); G is 0x8160c; the frame for locals is of class 4 (1024 bytes, 88 shadow bytes written: RtPgMemB.rtmb_sh) and the real frame is 0x220 bytes; the calls are the strlen wrapper 0x421ec (RtPgW7bCallB.w7b_astrlen_realizes) and __asan_memcpy 0x518b8; the kit is lib/AU/RtPgW7bKitB.v / RtPgW7bCallB.v / RtPgStepsB.v; names o_ -> ob_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgEnt0OddWB.v at cc5ce244897b for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs; the shadow offset is in s11 (x27) and t1 is saved in s4 (x20) and put back (0x8162c / 0x8164c), so the block changes the callee-saved s4 and s6; G is 0x80dc8; the real frame is 0x200 bytes; the strings lie below 0x21360; the calls are the strlen wrapper 0x41b60 (RPgW7bCall.w7b_astrlen_realizes, ra 0x8163c) and checked_memcpy 0x5116c (ra 0x8164c); the kit is lib/AU/RPgW7bKit.v / RPgW7bCall.v / RPgSteps.v and lib/AU/RPgMem.v's rm_sh. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the walk of the ODD block of
   ent_build's case 0 (pod.h:247-248, `const char *o = odd_ch[c % 14]; memcpy(ch, o, strlen(o) + 1);`) from 0x815e0
   to G = 0x80dc8, over the journal (no cut state). Proves no function (kind: segment lemma).
   ob_walk chains lib/AU/RPgEnt0OddR.v's engine runs with the two calls: run 1a (8 (c mod 14)), run 1t (the UBSan
   test 0x8160c and the table entry's address), run 1b (its shadow check), run 2 (s4 := t1, s6 := the entry, `jal`
   the strlen wrapper), the wrapper (RPgW7bCall.w7b_strlen_at), run 3 (a2 := len + 1, a0 := &ch, a1 := s6, `jal`
   checked_memcpy), the intrinsic (RPgW7bKit.w7b_memcpy_at), run 4 (t1 := s4, `j` G).
   Its post: the journal kept, the callee-saved registers but s4 and s6 kept, t1 kept, every byte outside the
   callees' stack [R - 2 ESTACK, R) and ch's len + 1 bytes kept, and ch holding the string and its NUL. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgSteps RPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgW7bBase RPgW7bKit RPgW7bCall.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgEnt0OddB RPgEnt0OddR.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


(* a register outside a concrete clobber list *)
Ltac ob_notin :=
let H := fresh "H" in intros H; cbn [In] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
Ltac ob_keep Hk := rewrite Hk by first [cbv; discriminate | ob_notin].

(* a callee-saved register other than s4 and s6 is outside every clobber list of the walk *)
Lemma ob_cs_kept : forall (regs regs' : bvmap 5 word) (clob : list (bv 5)),
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs' r = getr regs r) ->
(forall q : bv 5, In q clob -> In (bv_unsigned q) [1; 6; 10; 11; 12; 20; 22]) ->
forall r, acallee_saved r -> r <> 22 -> r <> 20 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
intros regs regs' clob Hk Hc r Hr H22 H20.
assert (Hu : bv_unsigned (Z_to_bv 5 r) = r).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. unfold acallee_saved in Hr.
  apply Z.mod_small. lia. }
apply Hk.
- rewrite Hu. unfold acallee_saved in Hr. lia.
- intros Hin. pose proof (Hc _ Hin) as Hq. rewrite Hu in Hq. cbn [In] in Hq. unfold acallee_saved in Hr. lia.
Qed.
Ltac ob_clob := let q := fresh "q" in let Hq := fresh "Hq" in
intros q Hq; cbn [In] in Hq;
repeat (destruct Hq as [<-|Hq]; [cbn [In]; repeat (first [left; reflexivity | right]) |]); destruct Hq.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ======================== the memory facts of the walk ======================== *)
(* a run's memory clause with an empty write set holds at every address *)
Lemma ob_all_eq : forall (W : world rsegs) m m',
(forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a) ->
forall a, aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a.
Proof.
intros W m m' K a.
assert (Hm : forall mem, aview rsegs (w_H W) mem a = aview rsegs (w_H W) mem (a mod 2 ^ 64))
  by (intros mem; unfold aview, mbyte; rewrite Z_to_bv_mod64; reflexivity).
rewrite (Hm m'), (Hm m). apply K; [apply Z.mod_pos_bound; lia | tauto].
Qed.

(* the bytes a string fact reads lie below the stack and the high shadow *)
Lemma ob_strz_low : forall x (s : list byte) a, 0 <= x -> x + Z.of_nat (length s) + 8 <= 0x21360 ->
w7b_strz x s a -> 0 <= a < 2 ^ 40.
Proof.
intros x s a Hx Hs [Ha|Ha]; [lia|].
unfold w7b_hull, shadow_addr, SHADOW_OFF in Ha.
set (L := Z.of_nat (length s)) in *.
assert (P1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (P2 : (x + (L + 1) - 1) / 8 <= x + L) by (apply Z.div_le_upper_bound; lia).
assert (P3 : 0 <= (0x7fff8000 + x / 8) / 8) by (apply Z.div_pos; lia).
assert (P4 : 8 * ((0x7fff8000 + (x + (L + 1) - 1) / 8) / 8) <= 0x7fff8000 + (x + (L + 1) - 1) / 8)
  by (apply Z.mul_div_le; lia).
lia.
Qed.

(* the strlen / memcpy source premise from the string's facts *)
Lemma ob_src_ok : forall (W : world rsegs) m R x s (regs : bvmap 5 word),
w7b_strok W m R x s -> spZ regs = R -> src_ok rsegs W regs m x (Z.of_nat (length s) + 1).
Proof.
intros W m R x s regs (H0 & H1 & H2 & Hb & Hn & Ht & Hs & Ha & Hr & Hh) Hsp a Ha'.
assert (ESTACK = 4096) as Hes by reflexivity.
split.
- destruct (Z_lt_le_dec a (x + Z.of_nat (length s))) as [Hl|Hg].
  + destruct (Hb (Z.to_nat (a - x)) ltac:(lia)) as [E _]. rewrite Z2Nat.id in E by lia.
    replace (x + (a - x)) with a in E by lia. rewrite E. discriminate.
  + replace a with (x + Z.of_nat (length s)) by lia. rewrite Hn. discriminate.
- rewrite Hsp. intros Hin. apply (Hs a ltac:(lia)). lia.
Qed.

(* the string and its NUL as bytes *)
Lemma ob_strok_bytes : forall (W : world rsegs) m R x s,
w7b_strok W m R x s -> rm_bytes rsegs (w_H W) m x (s ++ [Cursor.NUL]).
Proof.
intros W m R x s (_ & _ & _ & Hb & Hn & _). apply rm_bytes_aview. intros i Hi.
rewrite length_app in Hi. cbn [length] in Hi.
destruct (Nat.lt_ge_cases i (length s)) as [Hl|Hg].
- rewrite app_nth1 by exact Hl. exact (proj1 (Hb i Hl)).
- assert (i = length s) as -> by lia. rewrite nth_middle. rewrite Hn. reflexivity.
Qed.

(* ch's shadow hull lies in the frame's 88 shadow bytes *)
Lemma ob_hull_ch : forall (rd : reader) F n,
(forall i, 0 <= i < 88 -> rd (shadow_addr F + i) <> None) -> F mod 8 = 0 -> 0 <= F -> 1 <= n <= 24 ->
shadow_hull_vis rd (F + 0xa0) n.
Proof.
intros rd F n Hp HF8 HF0 Hn s Hs. unfold shadow_addr in *.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
set (q := F / 8) in *.
assert (E1 : (F + 0xa0) / 8 = q + 20).
{ rewrite DF. replace (8 * q + 0xa0) with (q * 8 + 20 * 8) by lia. rewrite Z.div_add by lia.
  rewrite Z.div_mul by lia. reflexivity. }
assert (E2 : (F + 0xa0 + n - 1) / 8 <= q + 23).
{ apply Z.div_le_upper_bound; lia. }
assert (E3 : q + 20 <= (F + 0xa0 + n - 1) / 8).
{ apply Z.div_le_lower_bound; lia. }
rewrite E1 in Hs.
pose proof (Z.div_mod (SHADOW_OFF + (q + 20)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (q + 20)) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (F + 0xa0 + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (F + 0xa0 + n - 1) / 8) 8 ltac:(lia)) as M2.
replace s with (SHADOW_OFF + q + (s - (SHADOW_OFF + q))) by lia.
apply Hp. unfold SHADOW_OFF in *. lia.
Qed.

(* ======================== the walk ======================== *)
Section w.
Variable B : asyms.
Hypothesis ASTRLEN : w7b_astrlen_realizes rsegs B W7B_STRLEN.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy RL_MEMCPY.

(* the state at G: the journal, the I/O state, the callee-saved registers but s4 and s6, t1, every byte outside the
   callees' stack and ch's len + 1 bytes, and ch holding odd_ch[c mod 14] with its NUL *)
Definition ob_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(k : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (R F c : Z) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = cfg_at rsegs 0x80dc8 regs2 mem2 md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io md md2 /\
(forall r, acallee_saved r -> r <> 22 -> r <> 20 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
getr regs2 6 = getr regs 6 /\
w7b_kept W mem mem2 (fun a => (R - 2 * ESTACK <= a < R) \/ (F + 0xa0 <= a < F + 0xa0 + ob_len (c mod 14) + 1)) /\
rm_bytes rsegs (w_H W) mem2 (F + 0xa0) (ob_str (c mod 14) ++ [Cursor.NUL]).

Lemma ob_walk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k (regs : bvmap 5 word) R F pos c,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 27 = w64 SHADOW_OFF -> getr regs 13 = w64 c -> getr regs 18 = w64 (F + 0xa0) ->
200 <= c < 256 ->
R mod 16 = 0 -> R + 0x200 <= sp0 -> sp0 - STK <= R - T_SEG_STK ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
rl_fsh rsegs (w_H W) mem F (rm_sh true true false false false true false) ->
rom_view rsegs W mem ->
range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF (OB_TBL + 8 * (c mod 14)) 8 ->
val_mem rsegs (mrestrict (w_H W) mem) (OB_TBL + 8 * (c mod 14)) 8 (ob_ptr (c mod 14)) ->
rl_cstr rsegs (w_H W) mem (ob_ptr (c mod 14)) (map (fun b : byte => bv_unsigned b) (ob_str (c mod 14))) ->
SRr rsegs W (cfg_at rsegs OB_PC regs mem md) (ob_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k regs mem md R F c).
Proof using ASTRLEN AMEMCPY.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs R F pos c
  HJ H2 H3 H4 H27 H13 H18 Hc HR16 HRS HRSTK Hown HF Hfsh Hrom Hra Hcell Hcs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W mem md 4 pos HAR Hin4) as (HF32 & HFapp & _ & _).
rewrite <- HF in HF32, HFapp. change (fs_frame_bytes 4) with 1024 in HFapp.
pose proof (rl_fbounds F HF32 HFapp) as (Fb0 & Fb1 & Fb2 & Fb3 & Fb4 & Famr).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Hts : T_SEG_STK = 16384) by reflexivity.
rewrite Hts in HRSTK.
assert (HRlo : alloc_ceiling + 16384 <= R) by lia.
assert (HF8 : F mod 8 = 0).
{ pose proof HF32 as HF32'. apply Z.mod_divide in HF32'; [|lia]. destruct HF32' as [z Hz]. rewrite Hz.
  replace (z * 32) with ((4 * z) * 8) by lia. apply Z.mod_mul. lia. }
assert (Hshf : shadow_addr F + 88 <= R - 2 * ESTACK) by lia.
assert (Hm : 0 <= c mod 14 < 14) by (apply Z.mod_pos_bound; lia).
remember (c mod 14) as m eqn:Em.
pose proof (ob_ptr_lo m Hm) as (Hx0 & Hx1). pose proof (ob_len_le m Hm) as Hl21.
assert (Hlen : ob_len m = Z.of_nat (length (ob_str m))) by reflexivity.
assert (Hok : w7b_strok W mem R (ob_ptr m) (ob_str m)).
{ apply w7b_strok_cstr; [exact Hcs | | | lia].
  - intros a Ha. exact (ob_tail_img m Hm a Ha (w_H W) mem).
  - rewrite <- Hlen. lia. }
(* ---- run 1a ---- *)
eapply SRr_bind.
{ unfold cfg_at, w64. exact (ob_run1a B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs c HJ H13 Hc Hrom). }
intros W1 c1 _ (-> & r1 & m1 & d1 & -> & HJ1 & Hio1 & Hk1 & Hm1 & _ & H1a & H1b & H1c).
rewrite <- Em in H1a. pose proof (ob_all_eq W mem m1 Hm1) as A1.
(* ---- run 1t: the UBSan test and the table entry's address ---- *)
eapply SRr_bind.
{ exact (ob_run1t B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 d1 k r1 m HJ1 H1a Hm H1b H1c). }
intros W2 c2 _ (-> & r2 & m2 & d2 & -> & HJ2 & Hio2 & Hk2 & Hm2 & _ & H2a).
pose proof (ob_all_eq W m1 m2 Hm2) as A2.
(* ---- run 1b: the entry's shadow check ---- *)
eapply SRr_bind.
{ refine (ob_run1b B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m2 d2 k r2 m HJ2 _ H2a Hm _).
  - ob_keep Hk2. ob_keep Hk1. exact H27.
  - apply (w7b_ra_kept W mem m2 _ 8 Hra); [unfold OB_TBL; lia | intros a _; rewrite A2; apply A1]. }
intros W3 c3 _ (-> & r3 & m3 & d3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & _ & _).
assert (H3a : getr r3 10 = w64 (OB_TBL + 8 * m)) by (ob_keep Hk3; exact H2a).
pose proof (ob_all_eq W m2 m3 Hm3) as A3.
(* ---- run 2 ---- *)
eapply SRr_bind.
{ refine (ob_run2 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m3 d3 k r3 (OB_TBL + 8 * m) (ob_ptr m) HJ3 H3a _ _ _ _);
    [unfold OB_TBL; lia | unfold OB_TBL; lia | lia |].
  eapply val_mem_kept; [|exact Hcell]. intros j _. rewrite A3, A2, A1. reflexivity. }
intros W4 c4 _ (-> & r4 & m4 & d4 & -> & HJ4 & Hio4 & Hk4 & Hm4 & _ & H4a & H4b & H4c & H4d).
pose proof (ob_all_eq W m3 m4 Hm4) as A4.
assert (R4_2 : getr r4 2 = w64 R) by (ob_keep Hk4; ob_keep Hk3; ob_keep Hk2; ob_keep Hk1; exact H2).
assert (R4_3 : getr r4 3 = w64 (as_gp B)) by (ob_keep Hk4; ob_keep Hk3; ob_keep Hk2; ob_keep Hk1; exact H3).
assert (R4_4 : getr r4 4 = w64 (as_tp B)) by (ob_keep Hk4; ob_keep Hk3; ob_keep Hk2; ob_keep Hk1; exact H4).
assert (HR47 : R < 2 ^ 47) by lia.
assert (Hsp4 : spZ r4 = sp0 + (R - sp0)) by (unfold spZ; rewrite R4_2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hok4 : w7b_strok W m4 R (ob_ptr m) (ob_str m)).
{ eapply w7b_strok_kept; [exact Hok|]. intros a _. rewrite A4, A3, A2, A1. reflexivity. }
assert (Hrom4 : rom_view rsegs W m4).
{ intros a Ha. rewrite A4, A3, A2, A1. exact (Hrom a Ha). }
assert (Hmod : (R - sp0) mod 16 = 0) by (rewrite Zminus_mod, HR16, Hal16; reflexivity).
pose proof Hok4 as (Ok0 & Ok1 & Ok2 & _ & _ & Okt & Oks & Oka & Okr & Okh).
(* ---- the strlen wrapper ---- *)
eapply SRr_bind.
{ refine (w7b_strlen_at B LAWS W7B_STRLEN ASTRLEN W r4 m4 STK sp0 FP ly S W0 mem0 md0 own lyc Sc d4 k
    (ob_ptr m) (ob_len m) (R - sp0) (w64 0x8163c) HJ4 H4b Ok0 _ _ _ Hsp4 Hmod _ _ R4_3 R4_4 H4c _ _ _ _ _ _ _ _ _).
  - lia.
  - rewrite Hlen. exact Ok1.
  - rewrite Hlen. exact Ok2.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - rewrite Hlen. exact (w7b_strok_first_byte W m4 R _ _ Hok4).
  - rewrite Hlen. apply (ob_src_ok W m4 R _ _ r4 Hok4). rewrite Hsp4. lia.
  - intros a Ha. replace (sp0 + (R - sp0)) with R by lia. apply Oks. rewrite <- Hlen. exact Ha.
  - rewrite Hlen. exact Oka.
  - rewrite Hlen. exact Okr.
  - rewrite Hlen. exact Okh.
  - rewrite Hlen. exact Okt.
  - intros a Ha _ _. exact (Hrom4 a Ha). }
intros W5 c5 _ (-> & r5 & m5 & d5 & -> & HJ5 & Hio5 & Hpr5 & H5a & Hm5 & _).
(* ---- run 3 ---- *)
eapply SRr_bind.
{ refine (ob_run3 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m5 d5 k r5 (ob_len m) HJ5 H5a _ _); rewrite Hlen; lia. }
intros W6 c6 _ (-> & r6 & m6 & d6 & -> & HJ6 & Hio6 & Hk6 & Hm6 & _ & H6a & H6b & H6c & H6d).
pose proof (ob_all_eq W m5 m6 Hm6) as A6.
assert (R6 : forall r, acallee_saved r -> r <> 22 -> r <> 20 -> getr r6 (Z_to_bv 5 r) = getr r4 (Z_to_bv 5 r)).
{ intros r Hr H22 H20. rewrite (ob_cs_kept r5 r6 _ Hk6 ltac:(ob_clob) r Hr H22 H20). exact (Hpr5 r Hr). }
assert (R6_2 : getr r6 2 = w64 R)
  by (refine (eq_trans (R6 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) _); exact R4_2).
assert (R6_3 : getr r6 3 = w64 (as_gp B))
  by (refine (eq_trans (R6 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) _); exact R4_3).
assert (R6_4 : getr r6 4 = w64 (as_tp B))
  by (refine (eq_trans (R6 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) _); exact R4_4).
assert (R6_10 : getr r6 10 = w64 (F + 0xa0)).
{ refine (eq_trans H6b _). refine (eq_trans (Hpr5 18 ltac:(unfold acallee_saved; lia)) _).
  ob_keep Hk4. ob_keep Hk3. ob_keep Hk2. ob_keep Hk1. exact H18. }
assert (R6_11 : getr r6 11 = w64 (ob_ptr m)).
{ refine (eq_trans H6c _). refine (eq_trans (Hpr5 22 ltac:(unfold acallee_saved; lia)) _). exact H4a. }
assert (Hsp6 : spZ r6 = sp0 + (R - sp0)) by (unfold spZ; rewrite R6_2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (K64 : forall a, 0 <= a < 2 ^ 64 -> ~ (R - 2 * ESTACK <= a < R) -> aview rsegs (w_H W) m6 a = aview rsegs (w_H W) m4 a).
{ intros a Ha Hn. rewrite A6. apply Hm5; [exact Ha|]. replace (sp0 + (R - sp0)) with R by lia. exact Hn. }
assert (Hok6 : w7b_strok W m6 R (ob_ptr m) (ob_str m)).
{ eapply w7b_strok_kept; [exact Hok4|]. intros a Ha.
  pose proof (ob_strz_low (ob_ptr m) (ob_str m) a ltac:(lia) ltac:(rewrite <- Hlen; lia) Ha) as Hal.
  apply K64; lia. }
assert (Hfsh6 : rl_fsh rsegs (w_H W) m6 F (rm_sh true true false false false true false)).
{ eapply rm_fsh_kept; [exact Hfsh|]. rewrite rm_sh_len. intros i Hi.
  rewrite K64 by lia. rewrite A4, A3, A2, A1. reflexivity. }
pose proof Hok6 as (Pk0 & Pk1 & Pk2 & _ & _ & _ & Pks & Pka & Pkr & Pkh).
assert (Hn22 : 1 <= ob_len m + 1 <= 22) by (rewrite Hlen; lia).
(* ---- checked_memcpy (ch, o, len + 1) ---- *)
eapply SRr_bind.
{ refine (w7b_memcpy_at B LAWS AMEMCPY W r6 m6 STK sp0 FP ly S W0 mem0 md0 own lyc Sc d6 k (F + 0xa0) (ob_ptr m)
    (ob_len m + 1) (R - sp0) (w64 0x8164c) HJ6 R6_10 R6_11 H6a _ _ _ Hsp6 Hmod _ _ R6_3 R6_4 H6d _ _ _ _ _ _ _ _ _ _ _ _).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - intros a Ha. split.
    + apply (rl_awr_fobj _ _ _ _ _ _ _ pos); [exact Hown | rewrite <- HF; lia].
    + lia.
  - apply (Famr 0xa0 (ob_len m + 1)); lia.
  - replace (F + 0xa0) with (F + RM_CH + 0) by (unfold RM_CH; lia).
    apply (rm_B_ra_ch rsegs _ _ F true false false false true false 0 (ob_len m + 1) Hfsh6 HF8); lia.
  - intros _. apply (ob_hull_ch _ F (ob_len m + 1)); [| exact HF8 | lia | lia].
    intros i Hi. rewrite (Hfsh6 i ltac:(rewrite rm_sh_len; lia)). discriminate.
  - lia.
  - lia.
  - rewrite Hlen. apply (ob_src_ok W m6 R _ _ r6 Hok6). rewrite Hsp6. lia.
  - destruct (Z_le_gt_dec (ob_ptr m + (ob_len m + 1)) (F + 0xa0)) as [Hle|Hgt]; [right; exact Hle|].
    destruct (Z_le_gt_dec (F + 0xa0 + (ob_len m + 1)) (ob_ptr m)) as [Hle'|Hgt']; [left; exact Hle'|].
    exfalso. pose proof Hcs as (_ & _ & _ & _ & _ & Himg & _).
    rewrite length_map in Himg.
    apply (frm_img rsegs B LAWS lyc Sc W mem md 4 pos (Z.max (F + 0xa0) (ob_ptr m)) HAR Hin4).
    + rewrite <- HF. change (fs_frame_bytes 4) with 1024. lia.
    + replace (Z.max (F + 0xa0) (ob_ptr m)) with (ob_ptr m + (Z.max (F + 0xa0) (ob_ptr m) - ob_ptr m)) by lia.
      apply Himg. rewrite <- Hlen. lia.
  - rewrite Hlen. exact Pka.
  - rewrite Hlen. exact Pkr.
  - intros _. rewrite Hlen. exact Pkh. }
intros W7 c7 _ (-> & r7 & m7 & d7 & -> & HJ7 & Hio7 & Hpr7 & _ & Hcp7 & Hm7 & _).
(* ---- run 4 ---- *)
eapply SRr_mono.
{ exact (ob_run4 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m7 d7 k r7 HJ7). }
intros W8 c8 _ (-> & r8 & m8 & d8 & -> & HJ8 & Hio8 & Hk8 & Hm8 & _ & H8a).
pose proof (ob_all_eq W m7 m8 Hm8) as A8.
unfold ob_post. rewrite <- Em.
split; [reflexivity|]. exists r8, m8, d8.
split; [reflexivity|].
split; [exact HJ8|].
split.
{ eapply same_io_trans; [exact Hio1|]. eapply same_io_trans; [exact Hio2|]. eapply same_io_trans; [exact Hio3|].
  eapply same_io_trans; [exact Hio4|]. eapply same_io_trans; [exact Hio5|]. eapply same_io_trans; [exact Hio6|].
  eapply same_io_trans; [exact Hio7|]. exact Hio8. }
split.
{ intros r Hr H22 H20.
  rewrite (ob_cs_kept r7 r8 _ Hk8 ltac:(ob_clob) r Hr H22 H20), (Hpr7 r Hr), (R6 r Hr H22 H20),
    (ob_cs_kept r3 r4 _ Hk4 ltac:(ob_clob) r Hr H22 H20), (ob_cs_kept r2 r3 _ Hk3 ltac:(ob_clob) r Hr H22 H20),
    (ob_cs_kept r1 r2 _ Hk2 ltac:(ob_clob) r Hr H22 H20), (ob_cs_kept regs r1 _ Hk1 ltac:(ob_clob) r Hr H22 H20).
  reflexivity. }
split.
{ (* t1: saved in s4 (0x8162c), kept by both calls, put back (0x8164c) *)
  refine (eq_trans H8a _). refine (eq_trans (Hpr7 20 ltac:(unfold acallee_saved; lia)) _).
  ob_keep Hk6. refine (eq_trans (Hpr5 20 ltac:(unfold acallee_saved; lia)) _).
  refine (eq_trans H4d _). ob_keep Hk3. ob_keep Hk2. ob_keep Hk1. reflexivity. }
split.
{ intros a Ha Hn.
  assert (N1 : ~ (F + 0xa0 <= a < F + 0xa0 + (ob_len m + 1))) by (intros X; apply Hn; right; lia).
  assert (N2 : ~ (sp0 + (R - sp0) - ESTACK <= a < sp0 + (R - sp0))) by (intros X; apply Hn; left; lia).
  assert (N3 : ~ (R - 2 * ESTACK <= a < R)) by (intros X; apply Hn; left; exact X).
  rewrite A8, (Hm7 a Ha N1 N2), (K64 a Ha N3), A4, A3, A2, A1. reflexivity. }
eapply rm_bytes_kept; [| intros x _; apply A8].
apply (rm_memcpy_bytes rsegs (w_H W) m6 (w_H W) m7 (ob_ptr m) (F + 0xa0)).
- exact (ob_strok_bytes W m6 R _ _ Hok6).
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hcp7. rewrite Hlen. lia.
Qed.
End w.
End b.

Print Assumptions ob_walk.
