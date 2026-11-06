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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v, with its module paths and module names changed; 313 of its 359 lines of code are new or changed and 587 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/check_bytes_B.v, with its addresses and numbers changed; 474 of its 529 lines of code are new or changed and 304 lines of the source are left out. *)
(* owe_sysex (fuzz_codec.c:101-111) at image B 0x84e8c, 103 instructions, real frame 48, __asan_memcpy at 0x84f3c,
   against lib/AU/Prog/CPgChkU.v's cdcU_owe_sysex_specX. a0 = q = &k (the 184-byte call record), a1 = dev, a2 = fn,
   a3 = the payload pl, a4 = its length n (n <= 19). Image B only: at image A owe_sysex is inlined into its caller.
   The walk is split on n (0 .. 19): with n a literal, a4 is pinned to it (owe_pin14), so every address the function
   forms from n is the record's atom plus a constant, and the engine decides the two UBSan bound checks.
   - 0x84e8c-0x84ec4: the frame and the saves of ra, s0-s4 into [sp - 48, sp) (cw_awr_stk), the alignment check of q
     (atom 10's al2 = 3: not taken), s4 = the shadow offset through the .got slot and its cell; the walk then drops
     the two image regions (cw_drop_gb) and puts the record's four write windows on top (owe_add): want[0..4),
     want[4 + n], want_len and want_display, at offsets 144, 148 + n, 168 and 180 of atom 10 (q), each a window of
     cdst_ok's [q + 144, q + 184) (owe_awr), off the save area by its coff_win; KE's zone widens to the save area and
     the record (owe_KE_widen).
   - 0x84ec8-0x84f3c: the four header stores (0xf0, 0x13, dev, fn), each after its shadow check (mkSHE 10 0 184,
     crd_ok), then `jal __asan_memcpy(q + 148, pl, n)`: CPgWalkIntrU's cw_intrin_call (OCpy), its destination in
     cdst_ok's range and off the four windows, its source the payload (crd_ok pl n, off the record by the contract).
   - 0x84f40-0x84fcc: the two bound checks (n + 4 < 24; q + 144 + n + 4 does not wrap), the store of 0xf7 at
     q + 148 + n, want_len = n + 5, want_display = ((fn - 0x30) & 0xef) == 0, the restores and `ret` (cw_leaf).
   - The result: kcall_atA at the end memory of set_wantZ k (owe_sx's want ++ the rest of the old want, its length,
     its display flag), from the windows' chunks, the copied bytes and KE (owe_kcall). The memory clause: every byte
     the walk changes is in [sp - 48 - ESTACK, sp) or in the contract's write set [q + 144, q + 184). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YN0d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkStrU CPgWalkIntrU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition B_OWE_SYSEX : Z := 0x84e8c.
(* a write window [lo, hi) of the record, on atom 10 (q); no chunk when it is made *)
Definition owe_win (lo hi : Z) : YP09.region := YP09.mkRegion (Some 10%nat) lo hi lo hi [].
Definition owe_AF : list (nat * afact) :=
[(10%nat, mkAF 0 (2 ^ 47 - 185) 3); (11%nat, mkAF 0 255 0); (12%nat, mkAF 0 255 0)].
Definition owe_SH : list shent := [mkSHE 10 0 184].
(* the zone of the walk's writes: its frame and the stack __asan_memcpy uses below it; in the record, want[0 .. 5 + n)
   (the header, the copied payload and 0xf7), want_len and want_display *)
Definition owe_zone (sp q n a : Z) : Prop :=
sp - 48 - ESTACK <= a < sp \/ q + 144 <= a < q + 149 + n \/ q + 168 <= a < q + 176 \/ q + 180 <= a < q + 184.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MCPY : aintrin_realizes tfibsegs B OCpy CB_MEMCPY.

(* a window of a region based on the atom that holds q, inside [q + o, q + o + n), which the contract lets the call
   write (CPgWalkU's cw_awr_ok_cons_twr at an offset o) *)
Lemma owe_awr_off : forall E r rs STK sp0 FP ly S lyc Sc own (W : world tfibsegs) memc sp q o n m,
YP09.r_base r = Some m -> bv_unsigned (ew E m) = q -> o <= YP09.r_wlo r -> YP09.r_whi r <= o + n ->
twr_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc sp (q + o) n ->
awr_ok E rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
awr_ok E (r :: rs) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
intros E r rs STK sp0 FP ly S lyc Sc own W memc sp q o n m Hb Hq Hlo Hhi Htw H a (r' & [<- | Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hq in Ha. exact (proj1 (Htw a ltac:(lia))).
- apply H. exists r'. split; [exact Hin | exact Ha].
Qed.
(* a byte of the record's write set [q + 144, q + 184), kept since the call's start, is writable *)
Lemma owe_writable : forall STK sp0 FP ly S lyc Sc own (W : world tfibsegs) memc mdc sp T q (mem : word -> option byte) a,
AR tfibsegs B lyc Sc W memc mdc ->
cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc sp T (q + 144) 40 -> q + 144 <= a < q + 184 ->
aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) memc a ->
writable_at tfibsegs (mrestrict (w_H W) mem) a.
Proof.
intros STK sp0 FP ly S lyc Sc own W memc mdc sp T q mem a HAR (Hq & Hqn & Htd & Htw & _) Ha Hv.
apply (apresent_writable tfibsegs).
apply (apresent_transfer tfibsegs (w_H W) (w_H W) memc mem a); [lia | | exact Hv | exact (proj1 (proj2 (Htw a ltac:(lia))))].
intros Him. exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc (q + 144) 40 a HAR Htd ltac:(lia) Him).
Qed.
(* a window of the record on top of a state's regions (lib/A/Prog/CPgEncOut.v's ceo_add on atom 10) *)
Lemma owe_add : forall E ss ms q lo hi,
st_ok tfibsegs E ss ms -> bv_unsigned (ew E 10) = q -> 0 <= lo <= hi -> 0 <= q -> q + hi <= 2 ^ 64 ->
(forall o, lo <= o < hi -> writable_at tfibsegs (ms_mem ms) (q + o)) ->
all_disjoint E (owe_win lo hi) (ss_mem ss) ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (owe_win lo hi :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms q lo hi HS Hb Hlh Ho Hhi Hw Hd. apply ast_ok_add_region; [exact HS | | | exact Hd].
- unfold region_wf, owe_win. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks forallb].
  rewrite !Z.leb_refl, (proj2 (Z.leb_le lo hi) ltac:(lia)). cbn [andb]. rewrite orb_true_r. reflexivity.
- unfold region_ok, owe_win. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Hb. split; [lia|]. split; [lia|]. split; [exact Hw | constructor].
Qed.
(* the shadow facts of an application range survive a change confined to a zone with no byte of the shadow map
   (below kLowMemEnd or above kHighShadowEnd): the walk's frame, the stack __asan_memcpy uses, the record *)
Lemma owe_ra_kept : forall H (m m' : word -> option byte) (Zn : Z -> Prop) q n,
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
(forall a, Zn a -> a < kLowMemEnd \/ kHighShadowEnd <= a) ->
0 <= q -> q + n <= kHighMemEnd ->
range_addressable (aview tfibsegs H m) SHADOW_OFF q n -> range_addressable (aview tfibsegs H m') SHADOW_OFF q n.
Proof.
intros H m m' Zn q n HK HZ Hq Hqn Hra x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
pose proof (shadow_addr_bounds x ltac:(lia)) as Hb. unfold shadow_addr in Hb. unfold shadow_of_addr in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite C2, C5 in Hb.
rewrite HK; [exact Hs | lia | intros Hz; destruct (HZ _ Hz) as [Hz1 | Hz1]; rewrite ?C2, ?C5 in Hz1; lia].
Qed.
Lemma owe_hull_kept : forall H (m m' : word -> option byte) (Zn : Z -> Prop) q n,
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
(forall a, Zn a -> a < kLowMemEnd \/ kHighShadowEnd <= a) ->
0 <= q -> 0 < n -> q + n <= kHighMemEnd ->
shadow_hull_vis (aview tfibsegs H m) q n -> shadow_hull_vis (aview tfibsegs H m') q n.
Proof.
intros H m m' Zn q n HK HZ Hq Hn Hqn Hv s Hs.
pose proof (shadow_addr_bounds q ltac:(lia)) as B1. pose proof (shadow_addr_bounds (q + n - 1) ltac:(lia)) as B2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). rewrite C2, C5 in B1, B2.
pose proof (Z.div_mod (shadow_addr q) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr q) 8 ltac:(lia)).
pose proof (Z.div_mod (shadow_addr (q + n - 1)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr (q + n - 1)) 8 ltac:(lia)).
rewrite HK; [exact (Hv s Hs) | lia | intros Hz; destruct (HZ _ Hz) as [Hz1 | Hz1]; rewrite ?C2, ?C5 in Hz1; lia].
Qed.
(* the shadow hull of a sub-range lies in the hull of the range *)
Lemma owe_hull_sub : forall rd q n q' n', shadow_hull_vis rd q n -> 0 <= q -> q <= q' -> q' + n' <= q + n -> 0 < n' ->
shadow_hull_vis rd q' n'.
Proof.
intros rd q n q' n' H Hq H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
assert (A1 : (SHADOW_OFF + q / 8) / 8 * 8 <= (SHADOW_OFF + q' / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (A2 : (SHADOW_OFF + (q' + n' - 1) / 8) / 8 * 8 <= (SHADOW_OFF + (q + n - 1) / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.
(* a byte whose view at a2 in m2 is the view at a1 in m1 holds the same value *)
Lemma owe_val1_move : forall H (m1 m2 : word -> option byte) a1 a2 v,
aview tfibsegs H m2 a2 = aview tfibsegs H m1 a1 ->
val_mem tfibsegs (mrestrict H m1) a1 1 v -> val_mem tfibsegs (mrestrict H m2) a2 1 v.
Proof.
intros H m1 m2 a1 a2 v Heq Hv k Hk. assert (k = 0%nat) as -> by lia.
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in *. rewrite Z.add_0_r in *.
unfold aview in Heq. rewrite Hv in Heq. cbn [option_map] in Heq.
destruct (mbyte tfibsegs (mrestrict H m2) a2) as [b|] eqn:Eb; [|discriminate Heq].
cbn [option_map] in Heq. injection Heq as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.
(* want_display = ((fn - 0x30) & 0xef) == 0 (0x84fa0-0x84fa8), owe_sx's flag: fn is 0x30 or 0x40 *)
Lemma owe_U_dp : forall E fn, ew E 12 = Z_to_bv 64 fn -> 0 <= fn < 256 ->
U E (SAlu ALU_SLTU (SAlu ALU_AND (SOff 12 (-48)) (SLit 239)) (SLit 1)) =
bit_or_0 ((u8 fn =? 0x40) || (u8 fn =? 0x30)) 1.
Proof.
intros E fn H Hf. rewrite !U_SAlu, !U_SLit, U_SOff, H, unsigned_lit_small by lia. cbn [zalu_raw].
rewrite <- (Z2Nat.id fn) by lia. assert (Hn : (Z.to_nat fn < 256)%nat) by lia.
generalize (Z.to_nat fn) Hn. clear. intros f Hf.
do 256 (destruct f as [|f]; [vm_compute; reflexivity|]). lia.
Qed.

(* ================================ the record after the walk ================================ *)
Lemma owe_nth_skipn : forall (l : list Z) n i, nth i (skipn n l) 0 = nth (n + i) l 0.
Proof.
induction l as [|x l IH]; intros n i.
- destruct n; cbn [skipn]; rewrite !nth_overflow by (cbn [length]; lia); reflexivity.
- destruct n as [|n]; cbn [skipn]; [reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma owe_garr8_app : forall m base l1 l2,
garr8 tfibsegs m base l1 -> garr8 tfibsegs m (base + Z.of_nat (length l1)) l2 -> garr8 tfibsegs m base (l1 ++ l2).
Proof.
intros m base l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [J|J].
- rewrite app_nth1 by exact J. exact (H1 j J).
- rewrite app_nth2 by exact J. destruct (H2 (j - length l1)%nat ltac:(lia)) as [V R]. split; [|exact R].
  replace (base + Z.of_nat j) with (base + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia. exact V.
Qed.
Lemma owe_garr8_1 : forall m a v, val_mem tfibsegs m a 1 v -> 0 <= v < 256 -> garr8 tfibsegs m a [v].
Proof.
intros m a v H Hr j Hj. cbn [length] in Hj. assert (j = 0%nat) as -> by lia. cbn [nth]. split; [|exact Hr].
change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact H.
Qed.
Lemma owe_garr8_kept : forall H (memc mem2 : word -> option byte) base l,
garr8 tfibsegs (mrestrict H memc) base l ->
(forall a, base <= a < base + Z.of_nat (length l) -> aview tfibsegs H mem2 a = aview tfibsegs H memc a) ->
garr8 tfibsegs (mrestrict H mem2) base l.
Proof.
intros H memc mem2 base l HG HK j Hj. destruct (HG j Hj) as (Hv & Hr). split; [|exact Hr].
apply (cw_val_mem_kept H H memc mem2 _ 1 _); [intros x Hx; cbn [Z.of_nat] in Hx; apply HK; lia | exact Hv].
Qed.
Lemma owe_garr8_skipn : forall H (memc mem2 : word -> option byte) base l c,
garr8 tfibsegs (mrestrict H memc) base l -> (c <= length l)%nat ->
(forall a, base + Z.of_nat c <= a < base + Z.of_nat (length l) -> aview tfibsegs H mem2 a = aview tfibsegs H memc a) ->
garr8 tfibsegs (mrestrict H mem2) (base + Z.of_nat c) (skipn c l).
Proof.
intros H memc mem2 base l c HG Hc HK j Hj. rewrite length_skipn in Hj. rewrite owe_nth_skipn.
destruct (HG (c + j)%nat ltac:(lia)) as (Hv & Hr). split; [|exact Hr].
replace (base + Z.of_nat c + Z.of_nat j) with (base + Z.of_nat (c + j)) by lia.
apply (cw_val_mem_kept H H memc mem2 _ 1 _); [intros x Hx; cbn [Z.of_nat] in Hx; apply HK; lia | exact Hv].
Qed.
(* kcall_atA at the end memory: the fields below want and want_key kept, want = owe_sx's bytes then the old want's
   rest, want_len its length, want_display its flag *)
Lemma owe_kcall : forall (W : world tfibsegs) memc mem2 q kc dev fn bs,
kcall_atA tfibsegs W memc q kc -> kcall_wfZ kc -> (length bs <= 19)%nat ->
0 <= dev < 256 -> 0 <= fn < 256 ->
(forall a, q <= a < q + 144 \/ q + 149 + Z.of_nat (length bs) <= a < q + 168 \/ q + 176 <= a < q + 180 ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memc a) ->
val_mem tfibsegs (mrestrict (w_H W) mem2) (q + 144) 1 0xf0 ->
val_mem tfibsegs (mrestrict (w_H W) mem2) (q + 145) 1 0x13 ->
val_mem tfibsegs (mrestrict (w_H W) mem2) (q + 146) 1 dev ->
val_mem tfibsegs (mrestrict (w_H W) mem2) (q + 147) 1 fn ->
garr8 tfibsegs (mrestrict (w_H W) mem2) (q + 148) bs ->
val_mem tfibsegs (mrestrict (w_H W) mem2) (q + 148 + Z.of_nat (length bs)) 1 0xf7 ->
val_mem tfibsegs (mrestrict (w_H W) mem2) (q + 168) 8 (Z.of_nat (length bs) + 5) ->
val_mem tfibsegs (mrestrict (w_H W) mem2) (q + 180) 4 (bit_or_0 ((u8 fn =? 0x40) || (u8 fn =? 0x30)) 1) ->
let '(w, dp) := owe_sx dev fn bs in
kcall_atA tfibsegs W mem2 q (set_wantZ kc (w ++ skipn (length w) (kz_want kc)) (Z.of_nat (length w)) dp).
Proof.
intros W memc mem2 q kc dev fn bs HK0 Hwf Hl Hdev Hfn KE V0 V1 V2 V3 Gbs V7 Vlen Vdp.
unfold owe_sx. cbv beta iota.
pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lb & Lbef & Lout & Lw).
destruct HK0 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17).
assert (KV : forall a n v, q <= a -> a + Z.of_nat n <= q + 144 ->
  val_mem tfibsegs (mrestrict (w_H W) memc) a n v -> val_mem tfibsegs (mrestrict (w_H W) mem2) a n v).
{ intros a n v H1 H2 Hv. apply (cw_val_mem_kept (w_H W) (w_H W) memc mem2 a n v); [intros x Hx; apply KE; lia | exact Hv]. }
assert (KG : forall a l, q <= a -> a + Z.of_nat (length l) <= q + 144 ->
  garr8 tfibsegs (mrestrict (w_H W) memc) a l -> garr8 tfibsegs (mrestrict (w_H W) mem2) a l).
{ intros a l H1 H2 Hg. apply (owe_garr8_kept (w_H W) memc mem2 a l Hg). intros x Hx. apply KE. lia. }
assert (LW : length ([0xf0; 0x13; u8 dev; u8 fn] ++ bs ++ [0xf7]) = (length bs + 5)%nat)
  by (rewrite !length_app; cbn [length]; lia).
unfold kcall_atA, set_wantZ. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
  kz_want_rc kz_want kz_want_len kz_want_key kz_want_display].
rewrite LW.
assert (U8d : u8 dev = dev) by (unfold u8; apply Z.mod_small; lia).
assert (U8f : u8 fn = fn) by (unfold u8; apply Z.mod_small; lia).
split; [apply (KV q 4%nat); [lia | cbn; lia | exact K1]|].
split; [apply (KV (q + 8) 8%nat); [lia | cbn; lia | exact K2]|].
split; [apply (KV (q + 16) 8%nat); [lia | cbn; lia | exact K3]|].
split; [apply (KV (q + 24) 4%nat); [lia | cbn; lia | exact K4]|].
split; [apply (KV (q + 28) 4%nat); [lia | cbn; lia | exact K5]|].
split; [apply (KV (q + 32) 4%nat); [lia | cbn; lia | exact K6]|].
split; [apply (KV (q + 36) 4%nat); [lia | cbn; lia | exact K7]|].
split; [apply (KG (q + 40)); [lia | rewrite Lb; lia | exact K8]|].
split; [apply (KV (q + 64) 8%nat); [lia | cbn; lia | exact K9]|].
split; [apply (KV (q + 72) 4%nat); [lia | cbn; lia | exact K10]|].
split; [apply (KG (q + 76)); [lia | rewrite Lbef; lia | exact K11]|].
split; [apply (KG (q + 108)); [lia | rewrite Lout; lia | exact K12]|].
split; [apply (KV (q + 140) 4%nat); [lia | cbn; lia | exact K13]|].
split.
{ (* want *)
  rewrite U8d, U8f. rewrite <- !app_assoc.
  change ([0xf0; 0x13; dev; fn] ++ bs ++ [0xf7] ++ skipn (length bs + 5) (kz_want kc)) with
    ([0xf0] ++ [0x13] ++ [dev] ++ [fn] ++ bs ++ [0xf7] ++ skipn (length bs + 5) (kz_want kc)).
  apply owe_garr8_app; [apply owe_garr8_1; [exact V0 | lia]|]. cbn [length]. change (Z.of_nat 1) with 1.
  apply owe_garr8_app; [apply owe_garr8_1; [replace (q + 144 + 1) with (q + 145) by lia; exact V1 | lia]|].
  cbn [length]. change (Z.of_nat 1) with 1.
  apply owe_garr8_app; [apply owe_garr8_1; [replace (q + 144 + 1 + 1) with (q + 146) by lia; exact V2 | lia]|].
  cbn [length]. change (Z.of_nat 1) with 1.
  apply owe_garr8_app; [apply owe_garr8_1; [replace (q + 144 + 1 + 1 + 1) with (q + 147) by lia; exact V3 | lia]|].
  cbn [length]. change (Z.of_nat 1) with 1. replace (q + 144 + 1 + 1 + 1 + 1) with (q + 148) by lia.
  apply owe_garr8_app; [exact Gbs|].
  apply owe_garr8_app; [apply owe_garr8_1; [exact V7 | lia]|].
  cbn [length]. replace (q + 148 + Z.of_nat (length bs) + Z.of_nat 1) with (q + 144 + Z.of_nat (length bs + 5)) by lia.
  apply (owe_garr8_skipn (w_H W) memc mem2 (q + 144) (kz_want kc) (length bs + 5) K14); [rewrite Lw; lia|].
  intros a Ha. rewrite Lw in Ha. apply KE. lia. }
split; [rewrite Nat2Z.inj_add; exact Vlen|].
split; [apply (cw_val_mem_kept (w_H W) (w_H W) memc mem2 (q + 176) 4%nat _); [intros x Hx; apply KE; cbn in Hx; lia | exact K16]|].
exact Vdp.
Qed.

(* ================================ tactics ================================ *)
Ltac owe_env_norm :=
rewrite ?ew_ewset_other, ?ew_havoc_old by lia;
repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => progress rewrite H end.
Ltac owe_env_norm_in Hb :=
rewrite ?ew_ewset_other, ?ew_havoc_old in Hb by lia;
repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => progress rewrite H in Hb end.
(* the write-range obligation of a run: read-only regions, the save area of atom 2, the record's windows on atom 10
   paid by Htw : twr_ok .. (q + 144) 40 *)
Ltac owe_awr_go Htw :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion ?b _ _ ?wlo ?whi _ :: _) _ ?sp0 _ _ _ _ _ =>
  lazymatch eval vm_compute in (Z.leb whi wlo) with
  | true => apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | owe_awr_go Htw]
  | false =>
    lazymatch b with
    | Some 2%nat =>
      lazymatch goal with B2 : bv_unsigned (ew _ 2) = ?spv |- _ =>
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
      [reflexivity | owe_env_norm; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | owe_awr_go Htw] end
    | Some 10%nat =>
      lazymatch type of Htw with twr_ok _ _ _ _ _ _ _ _ _ _ _ _ _ (?qv + 144) 40 =>
      eapply (owe_awr_off) with (m := 10%nat) (q := qv) (o := 144) (n := 40);
      [reflexivity | owe_env_norm; reflexivity | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia
      | exact Htw | owe_awr_go Htw] end
    | _ => fail 100 "owe_awr: a writable region on an unexpected atom"
    end
  end
end.
Ltac owe_awr Htw :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
owe_awr_go Htw.
(* region i of the stop's state, as region_ok with atom 10 read as q *)
Ltac owe_region i HR :=
lazymatch goal with HS : st_ok _ ?E ?ss _ |- _ =>
  let ro := eval vm_compute in (nth_error (ss_mem ss) i) in
  lazymatch ro with Some ?rr =>
  pose proof (st_ok_region_nth E ss _ i rr HS ltac:(vm_compute; reflexivity)) as HR;
  unfold region_ok in HR;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict] in HR;
  owe_env_norm_in HR end end.
(* every write window of a state lies in owe_zone *)
Ltac owe_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; owe_env_norm_in Hb;
  unfold owe_zone, ESTACK; lia | ]);
destruct Hr.
(* every write window of a state is off the copied payload [base, base + len) *)
Ltac owe_kwr_out :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; owe_env_norm_in Hb;
  unfold coff_win in *; lia | ]);
destruct Hr.
(* carry the copied payload's bytes G : garr8 .. m1 base l across a run from m1 (its frame HFr) *)
Ltac owe_keepG :=
lazymatch goal with HFr : frame_of _ ?rs (mrestrict ?Hh ?m1) (mrestrict _ ?m2), G : garr8 _ (mrestrict _ ?m1) ?base ?l |- _ =>
  let KD := fresh "KD" in
  pose proof (cw_kept_run (fun a => ~ (base <= a < base + Z.of_nat (length l))) _ rs Hh m1 m1 m2
    (fun _ _ _ => eq_refl) HFr) as KD;
  lazymatch type of KD with ?P -> _ => let KW := fresh "KW" in assert (KW : P) by owe_kwr_out; specialize (KD KW) end;
  let G2 := fresh "G" in
  pose proof (owe_garr8_kept Hh m1 m2 base l G ltac:(let Hx := fresh "Hx" in intros a Ha; apply KD; [lia | intros Hx; apply Hx; exact Ha]))
    as G2;
  clear G KD; rename G2 into G end.
(* all_disjoint of a window of the record and the state's regions: the save area by cdst_ok's coff_win, the other
   windows by their offsets *)
Ltac owe_disj :=
idtac; lazymatch goal with
| |- all_disjoint ?E ?r ?rs =>
  let rs' := eval vm_compute in rs in change (all_disjoint E r rs');
  apply all_disjoint_of_extents;
  cbn [List.map zall_disjoint]; unfold extent_of_region, owe_win;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  owe_env_norm; unfold zdisj; cbn [fst snd];
  repeat split; unfold coff_win in *; lia
end.
(* register r at a stop as the literal val: its symbolic value is an atom plus a constant (eq rewrites the atom's
   unsigned value) or a literal (eq = idtac) *)
Ltac owe_rd R r val eq :=
lazymatch goal with HS : st_ok _ ?Ev ?ssx (restrict ?Hh ?msx) |- _ =>
  assert (R : getr (ms_regs msx) r = Z_to_bv 64 val)
    by (rewrite (st_ok_restrict_reg tfibsegs Hh Ev ssx msx r HS);
        let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
        change (sv_denot Ev e = Z_to_bv 64 val); cbn [sv_denot];
        rewrite ?ew_ewset_other, ?ew_havoc_old by lia; eq; f_equal; lia) end.
(* register r at a stop whose symbolic value is still its entry atom (E : ew E0 r = getr regs r) *)
Ltac owe_rdr R r E :=
lazymatch goal with HS : st_ok _ ?Ev ?ssx (restrict ?Hh ?msx), HR : getr _ r = _ |- _ => idtac | _ => idtac end;
lazymatch goal with HS : st_ok _ ?Ev ?ssx (restrict ?Hh ?msx) |- _ =>
  lazymatch type of E with ew _ _ = ?rv =>
  assert (R : getr (ms_regs msx) r = rv)
    by (rewrite (st_ok_restrict_reg tfibsegs Hh Ev ssx msx r HS);
        let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
        change (sv_denot Ev e = rv); cbn [sv_denot];
        rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite E, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) end end.
(* pin register r, whose symbolic value is atom 14 (n, a literal in each case), to SLit v *)
Ltac owe_pin r v E14 :=
lazymatch goal with HS : st_ok _ ?Ev ?ssx (restrict ?Hh ?msx) |- _ =>
  let Hv := fresh "Hv" in
  assert (Hv : sv_denot Ev (SLit v) = getr (ms_regs (restrict Hh msx)) r)
    by (change (getr (ms_regs (restrict Hh msx)) r) with (getr (ms_regs msx) r);
        rewrite (st_ok_restrict_reg tfibsegs Hh Ev ssx msx r HS);
        let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
        change (sv_denot Ev (SLit v) = sv_denot Ev e); cbn [sv_denot];
        rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite E14, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  let HS3 := fresh "HS3" in
  pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx (restrict Hh msx) r (SLit v) HS ltac:(vm_compute; reflexivity) Hv) as HS3;
  clear HS Hv; rename HS3 into HS; norm_ss HS end.
(* the four windows of the record on top of the state at 0x84ec8, for one n (v) *)
Ltac owe_windows v :=
lazymatch goal with Hd : cdst_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HAR : AR _ _ _ _ _ _ _, B10 : bv_unsigned (ew _ 10) = ?qv,
  KEh : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
  let addw lo hi :=
    lazymatch goal with HS : st_ok _ ?Ev ?ssx ?msx |- _ =>
      let HS3 := fresh "HS3" in
      pose proof (owe_add Ev ssx msx qv lo hi HS ltac:(owe_env_norm; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(intros o Ho; cbn [ms_mem restrict];
              eapply (owe_writable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR Hd);
              [lia | apply KEh; [lia | unfold coff_win in *; lia]])
        ltac:(owe_disj)) as HS3;
      cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3; clear HS; rename HS3 into HS end in
  let o1 := eval vm_compute in (148 + v) in let o2 := eval vm_compute in (149 + v) in
  addw 180 184; addw 168 176; addw o1 o2; addw 144 148
end.

Theorem owe_sysex_B_holds : cdcU_owe_sysex_specX tfibsegs B MT B_OWE_SYSEX.
Proof using MTL TL LAWS ML MCPY.
unfold cdcU_owe_sysex_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q dev fn pl n kc bs
  HE H10 Hq8 Hkc Hwf Hcrd Hdst Hdev Hfn H13 H14 Hn Hlen Hcrdp Hpl.
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwin & Hwhi & Hev & Hlive).
cw_keep_j0 HJ HJ0.
unfold TB_owe_sysex in *. assert (Hes : ESTACK = 4096) by reflexivity. rewrite Hes in *.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (48 + 4096) HE ltac:(lia))
  as (Hceil & H47 & H46 & _ & Hpres).
pose proof Hcrd as (Hq0 & Hq63 & Hqv & Hqra & Hqhull & Hqam & Hqwin).
assert (Hq47 : q + 184 <= 2 ^ 47 - 1).
{ unfold amem_range in Hqam. rewrite C4, C5 in Hqam. destruct Hqam as [Hl | [_ Hh]]; lia. }
destruct Hdev as (Hdev & R11). destruct Hfn as (Hfn & R12).
change (2 ^ 8) with 256 in Hdev, Hfn.
change (w64 q) with (Z_to_bv 64 q) in H10.
assert (HAF : atoms_ok (Ereg regs (cw_extra [])) owe_AF).
{ unfold owe_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10.
  rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), R11.
  rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), R12. unfold w64.
  rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8.
  repeat split; lia. }
pose proof (cw_entry_base_af B TL LAWS B_OWE_SYSEX 48 [] owe_AF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
  (48 + 4096) HE ltac:(lia) ltac:(vm_compute; reflexivity) HAF) as HS.
remember (Ereg regs (cw_extra [])) as E eqn:HEE.
assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E14 : ew E 14 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E13 : ew E 13 = Z_to_bv 64 pl) by (subst E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 dev) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E12 : ew E 12 = Z_to_bv 64 fn) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12).
clear HEE.
assert (SHOK : sh_ok tfibsegs CW_Bx owe_SH E (mrestrict (w_H W) memc)).
{ unfold owe_SH. apply Forall_cons; [|apply Forall_nil].
  exact (cw_shent_crd W memc (spZ regs) (48 + 4096) E 10 q 184 Hcrd E10 E32 ltac:(lia)). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 B_OWE_SYSEX) with (Z_to_bv 64 B_OWE_SYSEX).
(* 0x84e8c-0x84ec4: the saves, the alignment check of q, the shadow offset into s4 *)
cw_run_to cw_awr_stk 0x84ec8. cw_keep cw_kwr_stk.
cw_drop_gb.
pose proof HE as ((HAR & _) & _).
assert (B10 : bv_unsigned (ew E 10) = q) by (rewrite E10; apply unsigned_lit_small; lia).
pose proof Hdst as (Hd0 & Hd1 & Htd & Htw & Hdra & Hdhv & Hdam & Hdcw).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
pose proof Hcrdp as (Hp0 & Hpn & Hprd & Hpra & Hphv & Hpam & Hpcw).
assert (Hplh : pl + n <= kHighMemEnd) by (unfold amem_range in Hpam; rewrite C3, C4, C5 in Hpam; rewrite C4; lia).
assert (Hqh : q + 184 <= kHighMemEnd) by (rewrite C4; lia).
(* no byte of the walk's zone is a byte of the shadow map *)
assert (HZ : forall a, owe_zone (spZ regs) q n a -> a < kLowMemEnd \/ kHighShadowEnd <= a).
{ intros a Ha. unfold owe_zone in Ha. destruct Ha as [Ha | Ha]; [right; rewrite C2; unfold ESTACK in Ha; lia|].
  unfold amem_range in Hdam. rewrite C3, C4, C5 in Hdam. rewrite C2, C5. lia. }
assert (B13 : bv_unsigned (ew E 13) = pl) by (rewrite E13; apply unsigned_lit_small; unfold amem_range in Hpam; lia).
assert (HC : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
  n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19) by lia.
repeat destruct HC as [HC | HC].
all: rewrite HC in E14, H14, Hpn, Hprd, Hpra, Hphv, Hpam, Hpcw, Hpl, Hplh.
all: lazymatch goal with E14 : ew _ 14 = Z_to_bv 64 ?v |- _ => owe_pin (9%bv : bv 5) v E14; owe_windows v end.
(* KE's zone widens to the save area, the stack __asan_memcpy uses below it and the record's write set *)
all: lazymatch goal with KE0 : forall a, _ -> ~ _ -> aview _ _ ?m a = aview _ _ ?m0 a |- _ =>
  let KW := fresh "KW" in
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone (spZ regs) q n a -> aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) m0 a)
    by (intros a Ha Hz; apply KE0; [exact Ha | intros Hx; apply Hz; left; unfold ESTACK; lia]);
  clear KE0; rename KW into KE end.
(* 0x84ec8-0x84f3c: the four header stores, then jal __asan_memcpy *)
all: cw_run ltac:(owe_awr Htw). all: cw_keep owe_kwr.
(* 0x84f3c jal __asan_memcpy(q + 148, pl, n): CPgWalkIntrU's cw_intrin_call; the walk resumes at 0x84f40 *)
all: lazymatch goal with HS : st_ok _ ?Ev ?ssx (restrict _ ?msx), E14 : ew _ 14 = Z_to_bv 64 ?v |- _ =>
  owe_rd Ra0 (10%bv : bv 5) (q + 148) ltac:(rewrite B10);
  owe_rd Ra1 (11%bv : bv 5) pl ltac:(rewrite B13);
  owe_rd Ra2 (12%bv : bv 5) v idtac;
  owe_rd Rs2 (2%bv : bv 5) (spZ regs - 48) ltac:(rewrite B2);
  assert (Rsp : spZ (ms_regs msx) = spZ regs - 48)
    by (unfold spZ at 1; rewrite Rs2; apply unsigned_lit_small; lia);
  owe_rdr R3 (3%bv : bv 5) E3; owe_rdr R4 (4%bv : bv 5) E4;
  eapply (cw_intrin_call B LAWS OCpy CB_MEMCPY MCPY W Ev ssx msx _ STK sp0 FP ly S W0 mem0 md0 own _ _ k
    (q + 148) pl v 0x84f40 64 (ss_mem ssx) _ HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HJ | exact Ra0 | exact Ra1 | exact Ra2
  | lia | lia | lia
  | rewrite Rsp; unfold ESTACK; lia | rewrite Rsp; lia | rewrite Rsp, Zminus_mod, Hal16; reflexivity | exact Hsp0al
  | rewrite R3; exact Hgp | rewrite R4; exact Htp
  | vm_compute; reflexivity | lia | apply ret_ok_even; vm_compute; reflexivity
  | intros a Ha; split; [exact (proj1 (Htw a ltac:(lia))) | rewrite Rsp; unfold ESTACK, coff_win in *; lia]
  | unfold amem_range in *; lia
  | apply (owe_ra_kept _ memc _ (owe_zone (spZ regs) q n) (q + 148) v KE HZ); [lia | lia | intros x Hx; apply Hdra; lia]
  | intros Hv0; apply (owe_hull_kept _ memc _ (owe_zone (spZ regs) q n) (q + 148) v KE HZ); [lia | lia | lia |];
    apply (owe_hull_sub _ (q + 144) 40); [apply Hdhv; lia | lia | lia | lia | lia]
  | cbn iota; split; [lia|]; split; [lia|]; split;
    [ intros a Ha; split;
      [ rewrite (KE a); [apply Hprd; lia | lia |];
        intros [Hz | Hz]; [unfold coff_win in Hpcw; unfold ESTACK in Hz; lia | destruct (Hpl ltac:(lia)) as (_ & _ & Hov); lia]
      | rewrite Rsp; unfold ESTACK, coff_win in *; lia ] |];
    split; [destruct (Z.eq_dec v 0) as [Hv0 | Hv0]; [lia | destruct (Hpl ltac:(lia)) as (_ & _ & Hov); lia]|];
    split; [exact Hpam|];
    split; [apply (owe_ra_kept _ memc _ (owe_zone (spZ regs) q n) pl v KE HZ); [lia | exact Hplh | exact Hpra]|];
    intros Hv0; apply (owe_hull_kept _ memc _ (owe_zone (spZ regs) q n) pl v KE HZ); [lia | lia | exact Hplh | exact (Hphv Hv0)]
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | apply submem_refl
  | lazymatch goal with |- Forall ?P ?rs => let l := eval vm_compute in rs in change (Forall P l) end;
    repeat apply Forall_cons; try apply Forall_nil;
    (split; [intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; owe_env_norm_in Ha;
             split; [lia | rewrite Rsp; unfold ESTACK, coff_win in *; lia]
           | cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; lia])
  | intros regs2 mem2 md2 HJ2 Hpres2 Ha02 Hcpy Hout Hap Hsm HS2 ] end.
all: lazymatch goal with
  | HS2 : st_ok _ ?E2 _ (restrict _ (mkst _ _ ?mem2 _)), Hout : forall a, _ -> ~ _ -> ~ _ -> aview _ _ ?mem2 a = _ |- _ =>
    let KW := fresh "KW" in
    assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone (spZ regs) q n a ->
      aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memc a)
      by (intros a Ha Hz; rewrite (Hout a Ha); [apply KE; assumption | intros Hd; apply Hz; right; lia
          | intros Hs; apply Hz; left; rewrite Rsp in Hs; unfold ESTACK in *; lia]);
    let SW := fresh "SW" in
    assert (SW : sh_ok tfibsegs CW_Bx owe_SH E2 (mrestrict (w_H W) mem2))
      by (unfold owe_SH; apply Forall_cons; [|apply Forall_nil];
          exact (cw_shent_ra W mem2 E2 10 q 184 (owe_ra_kept _ memc _ (owe_zone (spZ regs) q n) q 184 KW HZ Hq0 Hqh Hqra)
                   Hqam Hq0 ltac:(lia) ltac:(lia) ltac:(rewrite ew_havoc_old by lia; exact E10)
                   ltac:(rewrite ew_havoc_old by lia; exact E32)));
    (* the copied payload: want[4 .. 4 + n) holds bs *)
    let G := fresh "G" in
    assert (G : garr8 tfibsegs (mrestrict (w_H W) mem2) (q + 148) bs)
      by (intros j Hj; destruct (Hpl ltac:(lia)) as (_ & Gp & Hov); destruct (Gp j Hj) as (Vj & Rj); split; [|exact Rj];
          apply (owe_val1_move (w_H W) memc mem2 (pl + Z.of_nat j) (q + 148 + Z.of_nat j)); [|exact Vj];
          rewrite (Hcpy (Z.of_nat j) ltac:(lia)); cbn iota; apply KE; [lia|];
          intros Hz; unfold owe_zone, ESTACK in Hz; unfold coff_win in Hpcw; lia);
    clear HS SHOK KE; rename HS2 into HS; rename SW into SHOK; rename KW into KE;
    clear HJ; rename HJ2 into HJ
  end.
(* 0x84f40-0x84f4c: bgeu n + 4, 24 (decided: n is a literal), then 0x84f50 bltu ~(q + 144), n + 4, the check that
   q + 144 + n + 4 does not wrap, which the engine leaves: its trap side is refuted, q + 184 < 2 ^ 47 *)
all: cw_run ltac:(owe_awr Htw). all: owe_keepG. all: cw_keep owe_kwr.
all: cw_branch Hb.
all: first [ cw_ub_ltu_not Hb 10%nat E10 | clear Hb ].
(* 0x84f54-0x84fcc: the store of 0xf7 at q + 148 + n, want_len, want_display, the restores, to `ret` *)
all: cw_run ltac:(owe_awr Htw). all: owe_keepG. all: cw_keep owe_kwr.
(* `ret`: the memory clause (the walk wrote only its zone: its frame, the stack __asan_memcpy used, and in the record
   want[0 .. 5 + n), want_len and want_display, all in [q + 144, q + 184)), and the result from the windows' chunks,
   the copied payload G and KE (owe_kcall) *)
all: lazymatch goal with HS : st_ok _ ?Ef ?ssf (restrict _ ?msf), E14 : ew _ 14 = Z_to_bv 64 ?v |- _ =>
  owe_region 0%nat HR0; owe_region 1%nat HR1; owe_region 2%nat HR2; owe_region 3%nat HR3;
  destruct HR0 as (_ & _ & _ & HR0); destruct HR1 as (_ & _ & _ & HR1);
  destruct HR2 as (_ & _ & _ & HR2); destruct HR3 as (_ & _ & _ & HR3);
  apply Forall_cons_iff in HR0 as [C147 HR0]; apply Forall_cons_iff in HR0 as [C146 HR0];
  apply Forall_cons_iff in HR0 as [C145 HR0]; apply Forall_cons_iff in HR0 as [C144 _];
  apply Forall_cons_iff in HR1 as [C7 _]; apply Forall_cons_iff in HR2 as [Clen _];
  apply Forall_cons_iff in HR3 as [Cdp _];
  assert (V0 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (q + 144) 1 0xf0)
    by (intros kk Hk; exact (chunk_bytes_cval tfibsegs _ _ _ _ _ _ 0xf0 C144 ltac:(vm_compute; reflexivity) kk Hk));
  assert (V1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (q + 145) 1 0x13)
    by (intros kk Hk; exact (chunk_bytes_cval tfibsegs _ _ _ _ _ _ 0x13 C145 ltac:(vm_compute; reflexivity) kk Hk));
  assert (V2 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (q + 146) 1 dev)
    by (intros kk Hk; refine (chunk_bytes_cval tfibsegs _ _ _ _ _ _ dev C146 _ kk Hk);
        cbn [sv_denot]; repeat (first [rewrite ew_havoc_old by lia | rewrite ew_ewset_other by lia]);
        rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned;
        rewrite unsigned_lit_small by lia; reflexivity);
  assert (V3 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (q + 147) 1 fn)
    by (intros kk Hk; refine (chunk_bytes_cval tfibsegs _ _ _ _ _ _ fn C147 _ kk Hk);
        cbn [sv_denot]; repeat (first [rewrite ew_havoc_old by lia | rewrite ew_ewset_other by lia]);
        rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned;
        rewrite unsigned_lit_small by lia; reflexivity);
  assert (V7 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (q + 148 + Z.of_nat (length bs)) 1 0xf7)
    by (replace (q + 148 + Z.of_nat (length bs)) with (q + (148 + v)) by lia;
        intros kk Hk; exact (chunk_bytes_cval tfibsegs _ _ _ _ _ _ 0xf7 C7 ltac:(vm_compute; reflexivity) kk Hk));
  assert (Vlen : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (q + 168) 8 (Z.of_nat (length bs) + 5))
    by (replace (Z.of_nat (length bs) + 5) with (v + 5) by lia;
        intros kk Hk; exact (chunk_bytes_cval tfibsegs _ _ _ _ _ _ (v + 5) Clen ltac:(vm_compute; reflexivity) kk Hk));
  assert (Vdp : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (q + 180) 4
      (bit_or_0 ((u8 fn =? 0x40) || (u8 fn =? 0x30)) 1))
    by (intros kk Hk; refine (chunk_bytes_cval tfibsegs _ _ _ _ _ _ _ Cdp _ kk Hk);
        change (bv_unsigned (sv_denot Ef ?e)) with (U Ef e);
        rewrite (owe_U_dp Ef fn ltac:(rewrite ?ew_havoc_old, ?ew_ewset_other by lia; exact E12) Hfn); reflexivity);
  cw_leaf ltac:(idtac; cw_kept HJ0 KE
      ltac:(let a := fresh "a" in let Ha := fresh "Ha" in let Him := fresh "Him" in intros a Ha Him; cbv beta in Ha;
            exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc (q + 144) 40 a HAR Htd ltac:(lia) Him))
      ltac:(let a := fresh "a" in let Hz := fresh "Hz" in intros a Hz; cbv beta; unfold owe_zone, ESTACK in Hz;
            unfold coff_win in *; lia))
    ltac:(cbv beta;
          exact (owe_kcall W memc (ms_mem msf) q kc dev fn bs Hkc Hwf Hlen Hdev Hfn
            ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply KE; [lia|];
                  unfold owe_zone, ESTACK; unfold coff_win in *; lia)
            V0 V1 V2 V3 G V7 Vlen Vdp))
end.
Qed.
End d.
End b.
