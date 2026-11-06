(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/CPgWalk.v and moved to image B (the ASan-UBSan build):
   the image-A core modules are image B's (lib/AU), YImgTop is YImgTopU, the CA_ constants are CB_ ones with
   image B's values; lemma and tactic names unchanged. *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image B); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* The plumbing every image-B walk of codec's own functions shares.
   - Atoms: the walks start from `Ereg regs (cw_extra xs)`: atoms 0..31 are the registers, atom 32 is the shadow
     offset SB (the engine's shadow base CW_Bx), atoms 33.. are xs.
   - Entry: cw_entry0 (no region: a register-only leaf), cw_entry (the save area [sp - frame, sp), the .got slot of
     the shadow-offset cell and the cell itself, then the walk's own regions rs and atom facts AF), cw_entry_base
     (the three base regions only, every side condition discharged from cdc_entry).
   - Runs: cw_run awr runs the engine to its next stop; the obligations it leaves (ob_holds) come first, before the
     write-range goal (awr) and the continuation. cw_keep kwr folds the run's frame into KE; cw_branch splits an
     undecided branch; cw_r10 names a0 at the stop.
   - Writes: cw_kwr_ro / cw_kwr_stk (the zone of a state's write windows), cw_awr_stk (the save area lies in the
     caller's stack allowance), cw_awr_ok_cons_twr (a window inside a caller object the contract lets the call write).
   - Shadow: cw_shent_ra / cw_shent_crd / cw_shent_cdst give the engine's shadow entry of a range a premise marks usable;
     the _off forms take a range at an offset of the atom's value.
   - Leaf: cw_tcj_of_kept / cw_tcj_of_zone turn the kept-memory fact into tcj_kept; cw_leaf ends a walk at `ret` in
     cdc_post, cw_kept discharges its memory clause. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecGlobs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ image B's constants ================================
   The instance every image-B walk states its contract at: the read window .data.rel.ro .. .got, the seg7 switch
   table, owed_seg7's glyph table, personalities[0], and the 33 string literals of the registered globals (rows 1-33
   of CodecGlobs.CODEC_GLOBS, in its order). *)
Definition CB_RLO : Z := 0x9dba0.
Definition CB_RHI : Z := 0x9f128.
Definition CB_SEG7 : Z := 0x21400.
Definition CB_GLYPH : Z := 0x9e000.
Definition CB_PERS : Z := 0x9e240.
Definition CB_ROSTRS : list (Z * Z) :=
[(0x20fc0, 9); (0x20fe0, 9); (0x21000, 8); (0x21020, 10); (0x21040, 1); (0x21060, 7); (0x21080, 3);
 (0x210a0, 6); (0x210c0, 6); (0x210e0, 5); (0x21100, 6); (0x21120, 7); (0x21140, 4); (0x21160, 8);
 (0x21180, 7); (0x211a0, 7); (0x211c0, 6); (0x211e0, 5); (0x21200, 6); (0x21220, 6); (0x21240, 5);
 (0x21260, 6); (0x21280, 5); (0x212a0, 5); (0x212c0, 4); (0x212e0, 5); (0x21300, 6); (0x21320, 3);
 (0x21340, 6); (0x21360, 6); (0x21380, 2); (0x213c0, 9); (0x213e0, 9)].
Lemma CB_ROSTRS_rows : CB_ROSTRS = firstn 33 (skipn 1 CODEC_GLOBS).
Proof. vm_compute. reflexivity. Qed.
Lemma CB_ROSTRS_globs : Forall (fun r => In r CODEC_GLOBS) CB_ROSTRS.
Proof.
unfold CB_ROSTRS. repeat (apply Forall_cons; [apply globs_In_b; vm_compute; reflexivity|]). apply Forall_nil.
Qed.

(* ================================ atoms, shadow base ================================ *)
Definition CW_Bx : sv := SOff 32 0.
Definition CW_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition cw_extra (xs : list Z) : list word := map (Z_to_bv 64) (SB :: xs).
Lemma cw_ew_SB : forall regs xs, ew (Ereg regs (cw_extra xs)) 32 = Z_to_bv 64 SB.
Proof. intros regs xs. exact (ew_Ereg_extra regs (cw_extra xs) 0). Qed.
Lemma cw_ew_x : forall regs xs j,
ew (Ereg regs (cw_extra xs)) (33 + j) = Z_to_bv 64 (nth j xs 0).
Proof.
intros regs xs j. change (33 + j)%nat with (32 + S j)%nat. rewrite ew_Ereg_extra.
unfold cw_extra. cbn [map nth]. apply map_nth.
Qed.
Lemma cw_ew_reg : forall regs xs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs (cw_extra xs)) n = getr regs r.
Proof. intros regs xs n r H. exact (ew_Ereg_nat regs _ n r H). Qed.
(* the executor reads an offset of an atom modulo 2 ^ 64 *)
Lemma cw_U_offx : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> U E (SOff n c) = (x + c) mod 2 ^ 64.
Proof. intros E n x c Hn Hx. rewrite U_SOff, Hn, unsigned_lit_small by lia. reflexivity. Qed.
Lemma cw_U_Bx : forall E, ew E 32 = Z_to_bv 64 SB -> U E CW_Bx = SHADOW_OFF.
Proof.
intros E H. unfold U, CW_Bx. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
Qed.
Lemma cw_U_atom0 : forall E n q, ew E n = Z_to_bv 64 q -> 0 <= q < 2 ^ 64 -> U E (SOff n 0) = q.
Proof.
intros E n q H Hq. unfold U. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hq.
Qed.
Lemma cw_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
(* `lw` of a 4-byte field s (0 <= s < 2^32) compared with a small constant c: the sign-extended value equals c exactly
   when s does *)
Lemma cw_U_sx32_eqb : forall E n s c, ew E n = Z_to_bv 64 s -> 0 <= s < 2 ^ 32 -> 0 <= c < 2 ^ 31 ->
(U E (SExt true 32 (SOff n 0)) =? U E (SLit c)) = (s =? c).
Proof.
intros E n s c Hn Hs Hc. rewrite U_SExt. cbv iota beta. rewrite (U_atom E n s Hn) by lia. rewrite U_lit by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small s) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
destruct (Z.ltb_spec s (2 ^ 31)).
- rewrite (Z.mod_small (s + 2 ^ 31)) by lia. replace (s + 2 ^ 31 - 2 ^ 31) with s by lia. rewrite Z.mod_small by lia. reflexivity.
- replace (s + 2 ^ 31) with ((s - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (s - 2 ^ 31)) by lia.
  replace (s - 2 ^ 31 - 2 ^ 31) with ((s + (2 ^ 64 - 2 ^ 32)) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  destruct (Z.eqb_spec (s + (2 ^ 64 - 2 ^ 32)) c); destruct (Z.eqb_spec s c); first [reflexivity | lia].
Qed.
(* a field read as n little-endian bytes holds its value modulo 2 ^ (8 n) *)
Lemma cw_val_mem_mod : forall (m : word -> option byte) a n v,
val_mem tfibsegs m a n v -> val_mem tfibsegs m a n (v mod 2 ^ (8 * Z.of_nat n)).
Proof. intros m a n v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite Z.mod_mod by lia. reflexivity. Qed.
(* bytes whose view is kept keep their value *)
Lemma cw_val_mem_kept : forall H H' (m m' : word -> option byte) a n v,
(forall x, a <= x < a + Z.of_nat n -> aview tfibsegs H' m' x = aview tfibsegs H m x) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv k Hlt. rewrite (mbyte_of_aview tfibsegs H H' m m' (a + Z.of_nat k)) by (apply Hk; lia).
exact (Hv k Hlt).
Qed.

(* ================================ the kept-memory fact ================================ *)
(* a run keeps every byte outside the zone its write windows lie in *)
Lemma cw_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview tfibsegs H m1 a = aview tfibsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview tfibsegs H m2 a = aview tfibsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.

(* ================================ the leaf's memory clause ================================ *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
(* What a call kept, from the caller's journal at the call's start (HJ) and at its end (HJ2) and the bytes the walk
   kept: everything outside the call's window [sp - T, sp) and its write set E. E holds no byte of the image. *)
Lemma cw_tcj_of_kept : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 k2 sp T
(E : Z -> Prop),
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k2 ->
sp0 - STK <= sp - T -> sp <= sp0 ->
(forall a, E a -> in_img segs a -> False) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - T <= a < sp) -> ~ E a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
tcj_kept segs B T lyc Sc W memc W2 mem2 sp E.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 k2 sp T E HJ HJ2 Hlo Hhi HEimg KE.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _ & _ & _ & _ & Gpres & _).
pose proof Hstk as (_ & HSTK & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KV : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a Ha Hw. transitivity (aview segs (w_H W0) mem0 a); [apply G1; [exact Ha | exact Hw]|].
  symmetry. apply F1; [exact Ha | exact Hw]. }
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw He. apply KE; [lia | exact Hw | exact He].
- intros b m i Hin Hi He.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & H4096 & Hbc & _).
  apply KE; [lia | lia | exact He].
- intros a Himg _ _. pose proof (segs_low a Himg) as Hl.
  apply KE; [lia | lia | intros He; exact (HEimg a He Himg)].
- intros cid pos a Hin Hr He.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
  destruct (frame_zone segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hr) as (Hac & [(Ha1 & _) | Ha2]);
  (apply KE; [lia | lia | exact He]).
- intros a Ha Hw Hp.
  destruct (Z_lt_le_dec a (sp0 - STK)) as [Hb|Hb]; [| destruct (Z_lt_le_dec a sp0) as [Hb2|Hb2]].
  + eapply (apresent_transfer segs); [lia | intros Him; pose proof (segs_low a Him); lia | apply KV; lia | exact Hp].
  + apply Gpres. lia.
  + eapply (apresent_transfer segs); [lia | intros Him; pose proof (segs_low a Him); lia | apply KV; lia | exact Hp].
- intros a Ha. apply Gpres. lia.
Qed.
(* The same, from a kept fact over a zone Zn of the walk's writes, each in the window or in E. *)
Lemma cw_tcj_of_zone : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 k2 sp T
(E Zn : Z -> Prop),
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k2 ->
sp0 - STK <= sp - T -> sp <= sp0 ->
(forall a, E a -> in_img segs a -> False) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
(forall a, Zn a -> (sp - T <= a < sp) \/ E a) ->
tcj_kept segs B T lyc Sc W memc W2 mem2 sp E.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 k2 sp T E Zn HJ HJ2 Hlo Hhi HEimg KE Hcov.
apply (cw_tcj_of_kept STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 k2 sp T E HJ HJ2 Hlo Hhi HEimg).
intros a Ha Hw He. apply KE; [exact Ha|]. intros Hz. destruct (Hcov a Hz) as [Hx | Hx]; [exact (Hw Hx) | exact (He Hx)].
Qed.
(* A byte a call writes into a block or a live frame of the call state (tdst_ok) is not a byte of the image. *)
Lemma cw_tdst_not_img : forall lyc Sc W memc mdc q n a,
AR segs B lyc Sc W memc mdc -> tdst_ok B lyc Sc q n -> q <= a < q + n -> in_img segs a -> False.
Proof.
intros lyc Sc W memc mdc q n a HAR Hd Ha Himg. pose proof (segs_low a Himg) as Hl.
pose proof (cj_dst_byte segs B LAWS lyc Sc W memc mdc q n a HAR Hd Ha) as (H1 & H2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (Hd a Ha) as [(b & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & _ & _ & Happ & _).
  pose proof (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR) as Hc. apply Hc; [|exact Himg].
  left. exists b, m. split; [exact Hin | lia].
- pose proof (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR) as Hc. apply Hc; [|exact Himg].
  right. left. exists cid, pos. split; [exact Hin|]. exact Hr.
Qed.
End k.

(* ================================ the stack the call uses ================================ *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* From cdc_entry: the call's window [sp - T, sp) lies in the caller's stack allowance, above the allocator
   ceiling and below 2 ^ 47, and is present. *)
Lemma cw_entry_stack : forall B STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k regs T,
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T ->
0 <= T ->
alloc_ceiling <= spZ regs - T /\ spZ regs <= 2 ^ 47 /\ 2 ^ 46 + T <= spZ regs /\ spZ regs mod 16 = 0 /\
(forall a, spZ regs - T <= a < spZ regs -> apresent (w_H W) memc a).
Proof.
intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T
(HJ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _) HT.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & HSTK & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hal16|].
intros a Ha. apply Hpres. lia.
Qed.
End s.

(* ================================ entry states ================================ *)
Definition cw_regs (frame : Z) : smem := [stack_region frame; got_region; bcell_region 32].
Definition cw_atoms : list (nat * afact) := [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0)].
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a register-only leaf: no region, no fact *)
Lemma cw_entry0 : forall pc xs (W : world tfibsegs) regs memc,
st_ok tfibsegs (Ereg regs (cw_extra xs)) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom tfibsegs))).
Proof.
intros pc xs W regs memc. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I|]. split; exact I.
Qed.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
(* the three base regions are ok in every state AR holds of, with the save area present *)
Lemma cw_regs_ok : forall frame xs ly S (W : world tfibsegs) regs memc md,
AR tfibsegs B ly S W memc md -> 0 <= frame -> frame <= spZ regs ->
(forall a, spZ regs - frame <= a < spZ regs -> apresent (w_H W) memc a) ->
Forall (region_ok tfibsegs (Ereg regs (cw_extra xs)) (mrestrict (w_H W) memc)) (cw_regs frame).
Proof.
intros frame xs ly S W regs memc md HAR Hf Hfs Hpres.
destruct (al_const _ _ LAWS ly S W memc md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite <- SB_SHADOW_OFF in Kcell.
set (E := Ereg regs (cw_extra xs)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hsp. change (bv_modulus 64) with (2 ^ 64) in Hsp.
unfold cw_regs, stack_region, got_region, bcell_region. repeat apply Forall_cons; try apply Forall_nil.
- unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  unfold spZ in *. split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable tfibsegs).
  apply Hpres. lia.
- unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E _ 0 A_GOT_shadow 8 (SLit A_shadow_glob) A_shadow_glob);
  [reflexivity | unfold A_shadow_glob; zside | zside |].
  rewrite Z.add_0_l. exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Kgot).
- unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E _ 0 A_shadow_glob 8 (SOff 32 0) SB);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
  rewrite Z.add_0_l. exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Kcell).
Qed.
(* the entry state with the three base regions, then the walk's regions rs and atom facts AF *)
Lemma cw_entry : forall pc frame xs (rs : smem) (AF : list (nat * afact)) ly S (W : world tfibsegs) regs memc md,
AR tfibsegs B ly S W memc md -> 0 <= frame ->
2 ^ 46 + frame <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - frame <= a < spZ regs -> apresent (w_H W) memc a) ->
regions_wf (cw_regs frame ++ rs) = true ->
Forall (region_ok tfibsegs (Ereg regs (cw_extra xs)) (mrestrict (w_H W) memc)) rs ->
pairwise_disjoint (Ereg regs (cw_extra xs)) (cw_regs frame ++ rs) ->
atoms_ok (Ereg regs (cw_extra xs)) AF ->
st_ok tfibsegs (Ereg regs (cw_extra xs))
(mkSS pc sr_atoms (cw_regs frame ++ rs) None (mkFacts (cw_atoms ++ AF) [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom tfibsegs))).
Proof.
intros pc frame xs rs AF ly S W regs memc md HAR Hf Hsp Hal Hpres Hwf Hrs Hpd HAF.
rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- apply Forall_app. split; [|exact Hrs]. apply (cw_regs_ok frame xs ly S W regs memc md HAR Hf ltac:(lia) Hpres).
- exact Hpd.
- split; [|split; exact I]. cbn [f_atoms cw_atoms app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). rewrite cw_ew_SB.
  change (bv_unsigned (getr regs 2)) with (spZ regs). rewrite unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
  split; [split; [lia|]; split; [exact Hal | lia]|]. split; [split; [unfold SB; lia|]; split; [reflexivity | lia]|].
  exact HAF.
Qed.
(* the base regions alone, every side condition from cdc_entry with frame <= T *)
Lemma cw_entry_base : forall pc frame xs STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k regs T,
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T ->
0 <= frame <= T -> regions_wf (cw_regs frame) = true ->
st_ok tfibsegs (Ereg regs (cw_extra xs))
(mkSS pc sr_atoms (cw_regs frame) None (mkFacts cw_atoms [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom tfibsegs))).
Proof.
intros pc frame xs STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T HE Hf Hwf.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T HE ltac:(lia))
  as (Hceil & H47 & H46 & Hal & Hpres).
pose proof HE as ((HAR & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite <- (app_nil_r (cw_regs frame)). rewrite <- (app_nil_r cw_atoms).
apply (cw_entry pc frame xs [] [] lyc Sc W regs memc mdc HAR ltac:(lia) ltac:(lia) Hal
  ltac:(intros a Ha; apply Hpres; lia) ltac:(rewrite app_nil_r; exact Hwf) (Forall_nil _)).
- rewrite app_nil_r. apply pairwise_disjoint_of_extents.
  unfold cw_regs, stack_region, got_region, bcell_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). change (bv_unsigned (getr regs 2)) with (spZ regs).
  unfold A_GOT_shadow, A_shadow_glob.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- exact I.
Qed.
(* the same with the walk's own atom facts AF (the atoms of xs, an object's base) *)
Lemma cw_entry_base_af : forall pc frame xs AF STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k
regs T,
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T ->
0 <= frame <= T -> regions_wf (cw_regs frame) = true -> atoms_ok (Ereg regs (cw_extra xs)) AF ->
st_ok tfibsegs (Ereg regs (cw_extra xs))
(mkSS pc sr_atoms (cw_regs frame) None (mkFacts (cw_atoms ++ AF) [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom tfibsegs))).
Proof.
intros pc frame xs AF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T HE Hf Hwf HAF.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T HE ltac:(lia))
  as (Hceil & H47 & H46 & Hal & Hpres).
pose proof HE as ((HAR & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite <- (app_nil_r (cw_regs frame)).
apply (cw_entry pc frame xs [] AF lyc Sc W regs memc mdc HAR ltac:(lia) ltac:(lia) Hal
  ltac:(intros a Ha; apply Hpres; lia) ltac:(rewrite app_nil_r; exact Hwf) (Forall_nil _)).
- rewrite app_nil_r. apply pairwise_disjoint_of_extents.
  unfold cw_regs, stack_region, got_region, bcell_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). change (bv_unsigned (getr regs 2)) with (spZ regs).
  unfold A_GOT_shadow, A_shadow_glob.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- exact HAF.
Qed.
End e.

(* ================================ shadow entries ================================ *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the engine's shadow entry for [q, q + n), q held by atom m, from the range's usable marks *)
Lemma cw_shent_ra : forall (W : world tfibsegs) memc E m q n,
range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF q n -> amem_range q n ->
0 <= q -> 0 <= n -> q + n <= 2 ^ 63 ->
ew E m = Z_to_bv 64 q -> ew E 32 = Z_to_bv 64 SB ->
shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) memc) (mkSHE m 0 n).
Proof.
intros W memc E m q n Hra Ham Hq Hn Hqn Em E32.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
rewrite (cw_U_Bx E E32), (cw_U_atom0 E m q Em ltac:(lia)), Z.add_0_r.
rewrite <- (aview_rd_of tfibsegs). split.
- replace (n - 0) with n by lia. exact Hra.
- intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold amem_range in Ham. rewrite C3, C4, C5 in Ham. unfold SHADOW_OFF. lia.
Qed.
Lemma cw_shent_crd : forall (W : world tfibsegs) memc sp T E m q n,
crd_ok tfibsegs W memc sp T q n ->
ew E m = Z_to_bv 64 q -> ew E 32 = Z_to_bv 64 SB -> 0 <= n ->
shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) memc) (mkSHE m 0 n).
Proof.
intros W memc sp T E m q n (Hq & Hqn & _ & Hra & _ & Ham & _) Em E32 Hn.
exact (cw_shent_ra W memc E m q n Hra Ham Hq Hn Hqn Em E32).
Qed.
Lemma cw_shent_cdst : forall B STK sp0 FP ly S lyc Sc own (W : world tfibsegs) memc sp T E m q n,
cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc sp T q n ->
ew E m = Z_to_bv 64 q -> ew E 32 = Z_to_bv 64 SB -> 0 <= n ->
shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) memc) (mkSHE m 0 n).
Proof.
intros B STK sp0 FP ly S lyc Sc own W memc sp T E m q n (Hq & Hqn & _ & _ & Hra & _ & Ham & _) Em E32 Hn.
exact (cw_shent_ra W memc E m q n Hra Ham ltac:(lia) Hn Hqn Em E32).
Qed.
(* the same for a range [p + o, p + o + n) at offset o of the atom that holds p *)
Lemma cw_shent_ra_off : forall (W : world tfibsegs) memc E m p o n,
range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF (p + o) n -> amem_range (p + o) n ->
0 <= p -> 0 <= o -> 0 <= n -> p + o + n <= 2 ^ 63 ->
ew E m = Z_to_bv 64 p -> ew E 32 = Z_to_bv 64 SB ->
shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) memc) (mkSHE m o (o + n)).
Proof.
intros W memc E m p o n Hra Ham Hp Ho Hn Hpn Em E32.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
rewrite (cw_U_Bx E E32), (cw_U_atom0 E m p Em ltac:(lia)).
rewrite <- (aview_rd_of tfibsegs). split.
- replace (o + n - o) with n by lia. exact Hra.
- intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold amem_range in Ham. rewrite C3, C4, C5 in Ham. unfold SHADOW_OFF. lia.
Qed.
Lemma cw_shent_crd_off : forall (W : world tfibsegs) memc sp T E m p o n,
crd_ok tfibsegs W memc sp T (p + o) n -> ew E m = Z_to_bv 64 p -> 0 <= p -> 0 <= o ->
ew E 32 = Z_to_bv 64 SB -> 0 <= n ->
shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) memc) (mkSHE m o (o + n)).
Proof.
intros W memc sp T E m p o n (Hq & Hqn & _ & Hra & _ & Ham & _) Em Hp Ho E32 Hn.
exact (cw_shent_ra_off W memc E m p o n Hra Ham Hp Ho Hn Hqn Em E32).
Qed.
Lemma cw_shent_cdst_off : forall B STK sp0 FP ly S lyc Sc own (W : world tfibsegs) memc sp T E m p o n,
cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc sp T (p + o) n -> ew E m = Z_to_bv 64 p -> 0 <= p -> 0 <= o ->
ew E 32 = Z_to_bv 64 SB -> 0 <= n ->
shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) memc) (mkSHE m o (o + n)).
Proof.
intros B STK sp0 FP ly S lyc Sc own W memc sp T E m p o n (Hq & Hqn & _ & _ & Hra & _ & Ham & _) Em Hp Ho E32 Hn.
exact (cw_shent_ra_off W memc E m p o n Hra Ham Hp Ho Hn Hqn Em E32).
Qed.
(* the same for an image range a contract gives as cimg_range (its shadow usable in every AR state) *)
Lemma cw_shent_img_off : forall B ly S (W : world tfibsegs) memc md sp T E m p o n,
AR tfibsegs B ly S W memc md -> cimg_range tfibsegs B sp T (p + o) n ->
ew E m = Z_to_bv 64 p -> 0 <= p -> 0 <= o -> ew E 32 = Z_to_bv 64 SB ->
shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) memc) (mkSHE m o (o + n)).
Proof.
intros B ly S W memc md sp T E m p o n HAR (Hq & Hn & Hqn & Ham & _ & _ & Hus) Em Hp Ho E32.
destruct (Hus ly S W memc md HAR) as (Hra & _).
exact (cw_shent_ra_off W memc E m p o n Hra Ham Hp Ho ltac:(lia) Hqn Em E32).
Qed.
Lemma cw_shent_img : forall B ly S (W : world tfibsegs) memc md sp T E m q n,
AR tfibsegs B ly S W memc md -> cimg_range tfibsegs B sp T q n ->
ew E m = Z_to_bv 64 q -> ew E 32 = Z_to_bv 64 SB ->
shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) memc) (mkSHE m 0 n).
Proof.
intros B ly S W memc md sp T E m q n HAR (Hq & Hn & Hqn & Ham & _ & _ & Hus) Em E32.
destruct (Hus ly S W memc md HAR) as (Hra & _).
exact (cw_shent_ra W memc E m q n Hra Ham Hq ltac:(lia) Hqn Em E32).
Qed.
End h.

(* ================================ write windows ================================ *)
(* a window of a region based on the atom that holds q, inside [q, q + n), which the contract lets the call write *)
Lemma cw_awr_ok_cons_twr : forall B E r rs STK sp0 FP ly S lyc Sc own (W : world tfibsegs) memc sp q n m,
YP09.r_base r = Some m -> bv_unsigned (ew E m) = q -> 0 <= YP09.r_wlo r -> YP09.r_whi r <= n ->
twr_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc sp q n ->
awr_ok E rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
awr_ok E (r :: rs) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
intros B E r rs STK sp0 FP ly S lyc Sc own W memc sp q n m Hb Hq Hlo Hhi Htw H a (r' & [<- | Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hq in Ha. exact (proj1 (Htw a ltac:(lia))).
- apply H. exists r'. split; [exact Hin | exact Ha].
Qed.
(* every region of the state is read-only, or is the save area [sp - frame, sp) of atom 2, which lies in the caller's
   stack allowance [sp0 - STK, sp0) by the contract's two stack-window premises. It needs
   B2 : bv_unsigned (ew E0 2) = spZ regs for the walk's base env E0; the state's env may extend E0 (ewset / havoc). *)
Ltac cw_awr_stk :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch goal with B2 : bv_unsigned (ew _ 2) = ?spv |- _ =>
let B2x := fresh "B2x" in
assert (B2x : bv_unsigned (ew E 2) = spv)
  by (first [exact B2 | rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact B2]);
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
[reflexivity | rewrite B2x; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ];
clear B2x
end end.
(* the zone of a state's write windows: none (cw_kwr_ro), or the save area of atom 2 (cw_kwr_stk; it needs
   B2 : bv_unsigned (ew E 2) = spZ regs for the walk's base env E) *)
Ltac cw_kwr_ro :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia | ]); destruct Hr.
Ltac cw_kwr_stk :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
rewrite ?ew_ewset_other, ?ew_havoc_old in Hb by lia;
first [ lazymatch goal with B2 : bv_unsigned (ew _ 2) = _ |- _ => rewrite B2 in Hb end; lia | lia ] | ]);
destruct Hr.

(* ================================ runs, branches, stops ================================ *)
(* one run of the engine to its next stop; the obligations (ob_holds) it leaves come first, then the continuation *)
Ltac cw_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok tfibtbl_lib_ok HS HJ SHOK CW_Bspan; [ .. | awr | idtac ] end.
(* the same, each obligation closed by obl *)
Ltac cw_run_ob awr obl :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok tfibtbl_lib_ok HS HJ SHOK CW_Bspan; [ obl .. | awr | idtac ] end.
(* the same, stopping at pc stop *)
Ltac cw_run_to awr stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK CW_Bspan stop; [ .. | awr | idtac ] end.
(* the model layer a run adds, collapsed everywhere (lib/Reusable/YA0o.v wvb_collapse); call it also after a runtime
   call or a reseat if the walk does not go through cw_keep there *)
Ltac cw_norm_model := repeat (rewrite wvb_collapse in * ).
(* lia case-splits every disjunction and every `<>` fact in the context: a walk with many branches accumulates
   c <> g facts and each later lia splits 2^k ways. Hide such a fact as cw_hold P (cw_hide H) and unfold cw_hold only
   at the leaf that needs it. *)
Definition cw_hold (P : Prop) : Prop := P.
Ltac cw_hide H := lazymatch type of H with ?P => change (cw_hold P) in H end.
(* fold the run's frame into the kept-memory fact KE, then collapse the run's model layer in every hypothesis
   (srr_norm_model does it in the goal only; the journal's copy would hold the previous model twice and double with
   every run: measured 0.2 s per run, then 4.3 s after about 23 runs, on a 45-run walk) *)
Ltac cw_keep kwr :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (cw_kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by kwr end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
cw_norm_model.
(* the branch the engine cannot decide, with its condition named Hc *)
Ltac cw_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tfibtbl_lib_ok HS SH CW_Bspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* a0 at the stop, as the engine's symbolic value *)
Ltac cw_r10 R10 :=
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ?ms) |- _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in
assert (R10 : getr (ms_regs ms) (10%bv : bv 5) = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms (10%bv : bv 5) HS)
end.

(* ================================ the `ret` leaf ================================
   The goal is SRr .. (cdc_post ..). Needs in context: HS (st_ok at a `ret`), the latest journal HJ, E1 : ew E 1 = ..
   for the walk's base env E, Hra : YK0s.ret_ok .., HAE : env_agree 32 (Ereg ..) E, MTL : ameter_laws MT.
   The state's layout and astate are the call state's (no allocation, no frame). ktac proves the memory clause
   (tcj_kept; cw_kept below), rtac the result R W (ms_mem ms) (ms_regs ms) (R10 names a0). *)
Ltac cw_leaf ktac rtac :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _ |- _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
let R10 := fresh "R10" in cw_r10 R10;
eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [lazymatch goal with E1 : ew _ 1 = _, Hra : YK0s.ret_ok _ |- _ => rewrite R1, E1, Hra; reflexivity end|];
split; [unfold EV_CDC; rewrite Z.add_0_r; eapply ajournal_materialize; eassumption|];
split; [eapply aregs_preserved_of_st_ok;
  [exact HS | lazymatch goal with HAE : env_agree 32 _ _ |- _ => env_agree_chain HAE end | vm_compute; reflexivity]|];
split; [reflexivity|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply cw_same_io_wvb]; kio
  | eapply same_io_trans; [| apply same_io_materialized; eassumption]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [ktac | rtac]
end.
(* the memory clause at the leaf: HJ0 is the caller's journal at the call's start (keep a copy before the first
   run), KE the kept fact over the zone of the walk's writes, eimg proves `forall a, E a -> in_img _ a -> False`
   (`intros ? []` for cno_wr), cov proves `forall a, Zn a -> (sp - T <= a < sp) \/ E a` *)
Ltac cw_kept HJ0 KE eimg cov :=
lazymatch goal with L : AR_laws tfibsegs ?Bv |- _ =>
eapply (cw_tcj_of_zone tfibsegs Bv L tfib_segs_low);
[ exact HJ0 | eassumption | first [assumption | lia] | first [assumption | lia] | eimg | exact KE | cov ]
end.
(* Use (lib/A/Prog/check_refusal_A.v is the first walk built with them):
   - the runs take the NEWEST `ajournal` hypothesis; keep the entry journal as the OLDER one: cw_keep_j0 HJ HJ0 makes
     a copy and leaves HJ0 the older name.
   - pass the leaf's memory tactic as a closure: cw_leaf ltac:(idtac; cw_kept HJ0 KE eimg cov) rtac (an applied Ltac
     in argument position is run at once otherwise).
   - an object of the caller held by an atom (a crd_ok / cdst_ok range) may lie anywhere the premise allows, also on
     the image's .got slot or the shadow-offset cell; so load the shadow offset first with the base regions, then
     cw_drop_gb (keep the save area only) and add the object's region with ast_ok_add_region, which then needs only
     its disjointness from the save area (crd_ok's / cdst_ok's coff_win). *)
Ltac cw_keep_j0 HJ HJ0 :=
let H1 := fresh "HJ1" in pose proof HJ as H1; rename HJ into HJ0; rename H1 into HJ.
(* keep only the first region of the state (the save area of cw_regs), dropping the .got slot and the cell *)
Ltac cw_drop_gb :=
lazymatch goal with HS : st_ok _ ?Ev ?ssv ?msv |- _ =>
  let l := eval vm_compute in (ss_mem ssv) in
  let r1 := eval vm_compute in (hd got_region l) in
  let HS1 := fresh "HS" in
  assert (HS1 : st_ok tfibsegs Ev (mkSS (ss_pc ssv) (ss_regs ssv) [r1] (ss_resv ssv) (ss_facts ssv)) msv)
  by (apply (st_ok_submem tfibsegs Ev ssv msv [r1] HS); [change (submem [r1] l); submem_to | reflexivity]);
  clear HS; rename HS1 into HS end.
(* ---- frame-owning walks (measured on check_text_scribble) ----
   - a frame region's write window never passes the token engine's static check (cells_safe_b): the frame atom's fact
     [4096, 2^47 - ..] contains the shadow band, and no tighter fact is provable. So close the frame's and the frame
     shadow's windows (cw_close_win [frame atom; shadow atom]) for every token run (the chunks stay readable, and
     shok_auto_with then emits and pays the frame's inverted shadow entry), and open the frame's window only for a
     plain aj_run_to_sh over the store into the frame.
   - after cw_branch the state stays on the branch: cw_run does not move, cw_run_to <the branch's target> does.
   - a token run extends the env with ewset: cw_rebase_tok carries the walk's agreement AG (if any) and every
     `ew E n = v` fact to the state's env. *)
Definition cw_close_rs (l : list nat) (rs : smem) : smem :=
map (fun r => match YP09.r_base r with
  | Some m => if existsb (Nat.eqb m) l then set_window r 0 0 else r
  | None => r end) rs.
Ltac cw_close_win l :=
lazymatch goal with HS : st_ok _ ?Ev ?ssv ?msv |- _ =>
  let rs' := eval vm_compute in (cw_close_rs l (ss_mem ssv)) in
  let HS1 := fresh "HS" in
  pose proof (st_ok_submem tfibsegs Ev ssv msv rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity))
    as HS1;
  clear HS; norm_ss HS1; rename HS1 into HS end.
Ltac cw_rebase_tok :=
try lazymatch goal with
| AG : forall nn, (nn < 33)%nat -> ew _ nn = ew ?Eb nn, HS : st_ok _ ?Ev _ _ |- _ =>
  let AG2 := fresh "AG2" in
  assert (AG2 : forall nn, (nn < 33)%nat -> ew Ev nn = ew Eb nn)
    by (intros nn Hnn; repeat rewrite ew_ewset_other by lia;
        first [ apply AG; lia
              | lazymatch goal with |- ew (extK ?E1 ?K ?ws) nn = _ =>
                  rewrite (proj1 (env_agree_extK E1 K ws) nn ltac:(lia)); apply AG; lia end ]);
  clear AG; rename AG2 into AG
end;
repeat match goal with
| H : ew ?Eold ?nn = ?v, HS : st_ok _ ?Ev _ _ |- _ =>
  lazymatch Eold with
  | Ev => fail
  | _ => let H2 := fresh "Eh" in
         assert (H2 : ew Ev nn = v) by (repeat rewrite ew_ewset_other by lia; exact H);
         clear H; rename H2 into H
  end
end.

(* ================================ the bcmp wrapper ================================
   lib/Reusable/YCbq.v's aj_bcmp_at with the wrapper's same_but_materialized kept in the post (the cdc_post leaf needs
   same_io of the model), at tfibsegs. *)
Section bc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma cw_bcmp_at : forall pc, abcmp_realizes tfibsegs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (o : Z) raw,
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok tfibsegs W regsT memT x n -> src_ok tfibsegs W regsT memT y n ->
(forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) x n) ->
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) y n) ->
SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom tfibsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview tfibsegs (w_H W) memT (x + i) = aview tfibsegs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw
HJ Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre tfibsegs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o);
  try eassumption; [zlia|]. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x y n HPRE Hlo2 Hpres2E Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy
  ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write tfibsegs B LAWS tfib_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; zlia.
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr|]. split; [exact Hpres2 | exact Hsame].
Qed.
End bc.

(* ================================ a state in the middle of a function ================================
   lib/Reusable/YI04.v's entry_st_ok_full with the env apart from the machine registers: the env keeps the entry
   registers (atoms 0..31, which the leaf's aregs_preserved_of_st_ok compares with), the machine state carries the
   registers at the cut. *)
Section st. Context {fx : YK11.FPState}.
Lemma cw_st_ok_at : forall (E : env) pc sr (rs : smem) (G : facts) regs mem,
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok tfibsegs E mem) rs ->
pairwise_disjoint E rs -> facts_ok E G ->
st_ok tfibsegs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)).
Proof.
intros E pc sr rs G regs mem Hsr Hwf Hrs Hpd HG.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG].
split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
End st.

(* ===================== image B only: the frame-flag law across the two image bounds =====================
   The contracts state frame_flag_lawP through lib/Reusable/YCbq.v, whose zone2 cites image A's bounds
   (YImgTop: [0x10000, 0x5fb000)); image B's core (lib/AU/YCem.v aj_run_flag_sh / aj_flag_store_sh) takes it
   through lib/AU/YCbqU.v, whose zone2 cites image B's (YImgTopU: [0x10000, 0x5fc000)). The two laws differ only
   there. A to U: the flag is not in image B's image, which covers [0x10000, 0x5fc000) (lib/AU/YD1y.v in_img_hull).
   U to A: 0x5fc000 <= flag gives 0x5fb000 <= flag. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YCbqU YD1y.
Section ffl. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma ffl_U_of_A : YCbq.frame_flag_lawP tfibsegs B -> YCbqU.frame_flag_lawP tfibsegs B.
Proof.
intros H ly S W mem md cid pos HAR Hin.
destruct (H ly S W mem md cid pos HAR Hin) as (P1 & P2 & (Ha & Hni) & (H4 & Hz & Hc)).
split; [exact P1|]. split; [exact P2|]. split; [split; [exact Ha | exact Hni]|]. split; [exact H4|]. split; [|exact Hc].
destruct Hz as [_ Hb]. split; [|exact Hb].
unfold YCbqU.off_img, YImgTopU.IMG_LO, YImgTopU.IMG_TOP.
destruct (Z.lt_ge_cases (flag_addr ly cid pos) 0x10000) as [Hl|Hl]; [left; lia|].
destruct (Z.lt_ge_cases (flag_addr ly cid pos) 0x5fc000) as [Hh|Hh]; [|right; lia].
exfalso. apply Hni. apply YD1y.in_img_hull. lia.
Qed.
Lemma lde_ffl_of_U : YCbqU.frame_flag_lawP tfibsegs B -> YCbq.frame_flag_lawP tfibsegs B.
Proof.
intros H ly S W mem md cid pos HAR Hin.
destruct (H ly S W mem md cid pos HAR Hin) as (P1 & P2 & P3 & (H4 & Hz & Hc)).
split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact H4|]. split; [|exact Hc].
destruct Hz as [Ho Hb]. split; [|exact Hb].
unfold YCbqU.off_img, YImgTopU.IMG_LO, YImgTopU.IMG_TOP in Ho. unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP. lia.
Qed.
End ffl.
(* lib/AU/YCem.v's frame kit (aj_run_sh / aj_run_to_sh / aj_run_flag_sh) states its journal and the run's write-window
   goal with lib/AU/YCbqU.v's ajournal and awr_ok, the plumbing above with lib/Reusable/YCbq.v's: the same text.
   cw_aj_of_U / cw_awr_of_A convert (identity); cw_ajA turns such a journal into the YCbq form, cw_awrA such a goal into
   the YCbqU form. Moved from lib/AU/Prog/diginet_scribble_encode_B_lib.v (its sce_aj_of_U,
   sce_awr_of_A, sce_ajA, sce_awrA) so every frame-taking image-B walk uses one copy. *)
Section aj. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma cw_aj_of_U : forall segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
YCbqU.ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
YCbq.ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k.
Proof. intros segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k H. exact H. Qed.
Lemma cw_awr_of_A : forall E rs STK sp0 FP bl0 blc ly own,
YCbq.awr_ok E rs STK sp0 FP bl0 blc ly own -> YCbqU.awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof. intros E rs STK sp0 FP bl0 blc ly own H. exact H. Qed.
End aj.
Ltac cw_ajA HJ :=
lazymatch type of HJ with
| YCbqU.ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply cw_aj_of_U in HJ
| _ => idtac
end.
Ltac cw_awrA :=
lazymatch goal with
| |- YCbqU.awr_ok _ _ _ _ _ _ _ _ _ => apply cw_awr_of_A
| _ => idtac
end.

(* ============== image B: arithmetic, field and run helpers from diginet_counter_text's walk ==============
   Moved from this library's lib/AU/Prog/diginet_counter_text_B*.v, with
   neutral names: ct_not / ct_lxor_ones / ct_denot_not (diginet_counter_text_B_inv.v, _s0.v), ct_denot_and_m32 /
   ct_fld (_s0_a.v), ct_fld_off (_s0_b.v), cta_den_dot / cta_U_m4 (_l1_a.v), ctb_den_dot_r / ctb_den_add_r /
   ct_ub_n7 (_l1_b.v, here with the atom as an argument), ctc_U8n (_l1_c.v), ct_awr0 (_s0_a.v, here with the
   re-anchored atom as an argument), ctx_run_flag (_x.v).
   - Image B's engine orders some operands the other way (the _r forms) and writes `not` as xori -1 (cw_denot_not).
   - After `andi sp,sp,-32` the realigned sp is no offset of the entry sp: run to the first store through it, pin
     the register that holds it to a fresh atom (its value 32 * ((sp - c) / 32), cw_denot_and_m32), and pay the
     run's windows of that atom and of atom 2 with cw_awr_anchor.
   - cw_run_flag is the release run over YCbq.aj_flag_store with the lemma's 16 journal arguments
     (lib/Reusable/YCbq.v's aj_run_flag passes 15, so it never applies).
   - A write with no instrumented check still needs a shadow entry for its object, else cells_safe_b refuses the
     run. *)
Definition cw_not (x : Z) : Z := 2 ^ 64 - 1 - x.
Lemma cw_lxor_ones : forall a n, 0 < n -> 0 <= a < 2 ^ n -> Z.lxor a (Z.ones n) = Z.ones n - a.
Proof.
intros a n Hn Ha.
assert (Hlog : Z.log2 a < n).
{ destruct (Z.eq_dec a 0) as [->|Hz]; [rewrite Z.log2_nonpos; lia|]. apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia. }
rewrite <- (Z.ldiff_ones_l_low a n) by lia.
rewrite Z.ldiff_land.
assert (E : Z.land (Z.ones n) (Z.lnot a) = Z.land (Z.lnot a) (Z.ones n)) by apply Z.land_comm. rewrite E.
rewrite Z.land_ones by lia. unfold Z.lnot, Z.ones. rewrite Z.shiftl_1_l.
replace (Z.pred (- a)) with ((2 ^ n - 1 - a) + (-1) * 2 ^ n) by lia. rewrite Z.mod_add by lia.
rewrite Z.mod_small by lia. lia.
Qed.
(* `not rd,rs` (xori rd,rs,-1) of an offset of an atom *)
Lemma cw_denot_not : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff n c) (SLit (-1))) = Z_to_bv 64 (cw_not (v + c)).
Proof.
intros E n v c Hn Hv Hvc. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn Hv Hvc).
change (zcanon (-1)) with (Z.ones 64). rewrite cw_lxor_ones by lia.
change (Z.ones 64) with (2 ^ 64 - 1). unfold cw_not. apply zcanon_id. unfold M64. lia.
Qed.
(* the same `not` as the unsigned value a bound test compares (diginet_sysex_encode_B_0.v's sx_U_not = owe_sysex_B's former owe_U_not) *)
Lemma cw_U_not : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SOff n c) (SLit (-1))) = 2 ^ 64 - 1 - (v + c).
Proof.
intros E n v c Hn Hv Hvc. unfold U. rewrite (cw_denot_not E n v c Hn Hv Hvc). unfold cw_not.
apply unsigned_lit_small. lia.
Qed.
(* `andi rd,rs,-32` of an offset of an atom: the atom's value plus the offset, rounded down to a multiple of 32 *)
Lemma cw_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
(* a0 = ((s << 2) - 4) + b: the address of the n-th 4-byte slot after b - 4 (the engine's operand order) *)
Lemma cw_den_dot : forall E (b c : nat) x n, ew E b = Z_to_bv 64 x -> ew E c = Z_to_bv 64 n ->
  0 <= x < 2 ^ 63 -> 1 <= n <= 8 -> 4 <= x ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff c 0) (SLit 2)) (SLit (-4))) (SOff b 0)) =
  Z_to_bv 64 (x - 4 + 4 * n).
Proof.
intros E b c x n Hb Hc Hx Hn Hx4. rewrite denot_lit_U. f_equal.
rewrite !U_SAlu, !U_SLit. cbn [zalu_raw].
rewrite (U_atom E c n Hc ltac:(lia)), (U_atom E b x Hb ltac:(lia)).
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite (zcanon_id (n * 4)) by (unfold M64; lia).
assert (Hm : zcanon (n * 4 + zcanon (-4)) = 4 * n - 4).
{ unfold zcanon, M64. rewrite Zplus_mod_idemp_r. replace (n * 4 + -4) with (4 * n - 4) by lia.
  apply Z.mod_small. lia. }
rewrite Hm. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* (s << 2) - 4 for 1 <= s <= 8 *)
Lemma cw_U_m4 : forall E c n, ew E c = Z_to_bv 64 n -> 1 <= n <= 8 ->
  U E (SAlu ALU_ADD (SAlu ALU_SLL (SOff c 0) (SLit 2)) (SLit (-4))) = 4 * n - 4.
Proof.
intros E c n Hc Hn. rewrite !U_SAlu, !U_SLit. cbn [zalu_raw].
rewrite (U_atom E c n Hc ltac:(lia)).
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite (zcanon_id (n * 4)) by (unfold M64; lia).
unfold zcanon, M64. rewrite Zplus_mod_idemp_r. replace (n * 4 + -4) with (4 * n - 4) by lia.
apply Z.mod_small. lia.
Qed.
(* (s << 2) + b, the engine's other operand order *)
Lemma cw_den_dot_r : forall E (b c : nat) x n, ew E b = Z_to_bv 64 x -> ew E c = Z_to_bv 64 n ->
  0 <= x < 2 ^ 63 -> 0 <= n <= 8 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff c 0) (SLit 2)) (SOff b 0)) = Z_to_bv 64 (x + 4 * n).
Proof.
intros E b c x n Hb Hc Hx Hn. rewrite denot_lit_U. f_equal.
rewrite !U_SAlu, U_SLit. cbn [zalu_raw].
change (Z.land (zcanon 2) 63) with 2.
rewrite (U_atom E c n Hc ltac:(lia)). rewrite (U_atom E b x Hb ltac:(lia)).
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite (zcanon_id (n * 4)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* c + b with the operands the other way round *)
Lemma cw_den_add_r : forall E (b c : nat) x n, ew E b = Z_to_bv 64 x -> ew E c = Z_to_bv 64 n ->
  0 <= x -> 0 <= n -> x + n < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff c 0) (SOff b 0)) = Z_to_bv 64 (x + n).
Proof.
intros E b c x n Hb Hc Hx Hn Hxn. rewrite Z.add_comm. apply denot_add2; [assumption | assumption | lia | lia | lia].
Qed.
(* 0 - (s - 8) = 8 - s for 0 <= s <= 8 *)
Lemma cw_U8n : forall E k n, ew E k = Z_to_bv 64 n -> 0 <= n <= 8 ->
  U E (SAlu ALU_SUB (SLit 0) (SOff k (-8))) = 8 - n.
Proof.
intros E k n Hk Hn. rewrite U_SAlu, U_SLit, U_SOff, Hk, unsigned_lit_small by lia. cbn [zalu_raw].
unfold zcanon, M64. rewrite Z.mod_0_l by lia. rewrite Zminus_mod_idemp_r.
replace (0 - (n + -8)) with (8 - n) by lia. apply Z.mod_small. lia.
Qed.
(* a field of a region whose chunk is an atom (cw_fld) or an atom at an offset (cw_fld_off) with a known value *)
Lemma cw_fld : forall E m n bse cs lo hi wlo whi od (w : N) i v,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = bse ->
  In (YP09.mkChunk od (CVal w (SOff i 0))) cs -> ew E i = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  Z.of_N w <= 8 ->
  val_mem tfibsegs m (bse + od) (N.to_nat w) v.
Proof.
intros E m n bse cs lo hi wlo whi od w i v Hr Hb Hc Hi Hv Hw.
eapply (field_of_region E m n bse cs lo hi wlo whi od w (SOff i 0) v Hr Hb Hc); [|exact Hv | exact Hw].
cbn [sv_denot]. rewrite Hi, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma cw_fld_off : forall E m n bse cs lo hi wlo whi od (w : N) i c v,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = bse ->
  In (YP09.mkChunk od (CVal w (SOff i c))) cs -> ew E i = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  0 <= v + c < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem tfibsegs m (bse + od) (N.to_nat w) (v + c).
Proof.
intros E m n bse cs lo hi wlo whi od w i c v Hr Hb Hc Hi Hv Hvc Hw.
eapply (field_of_region E m n bse cs lo hi wlo whi od w (SOff i c) (v + c) Hr Hb Hc); [|exact Hvc | exact Hw].
cbn [sv_denot]. rewrite Hi, unsigned_lit_small by lia. reflexivity.
Qed.
(* a UBSan check `bltu c,s` the engine cannot decide, with s the atom k (Ek : ew _ k = Z_to_bv 64 _): split on it and
   refute the trap side by lia from the facts in context; the other side stays, its condition in Hu *)
Ltac cw_ub_ltu k Ek :=
  let Hu := fresh "Hu" in cw_branch Hu;
  lazymatch type of Hu with branch_taken _ (sv_denot ?Ev _) _ = _ =>
    rewrite branch_ltu_U, U_lit, (U_atom Ev k _ ltac:(rewrite ?ew_havoc_old, ?ew_ewset_other by lia; exact Ek)
      ltac:(lia)) in Hu by lia end;
  try (exfalso; apply Z.ltb_lt in Hu; lia).
(* peel ewset / havoc layers (and env-agreement facts Q) off an atom read (diginet_sysex_encode_B_0.v's sx_ew_peel) *)
Ltac cw_ew_peel := repeat first [ rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia
  | match goal with Q : forall k, (k < _)%nat -> ew ?X k = ew _ k |- context [ew ?X _] => rewrite Q by lia end ].
(* the taken side Hu of a UBSan test `bltu ~(atom k + c), literal` (the address + length wraps), refuted from the
   atom's value (Ek : ew _ k = Z_to_bv 64 _) and the facts in context (diginet_sysex_encode_B_0.v's sx_ub_out, atom an argument) *)
Ltac cw_ub_ltu_not Hu k Ek :=
  exfalso; rewrite branch_ltu_U in Hu;
  lazymatch type of Hu with context [U ?Ex (SAlu ALU_XOR (SOff k ?c) (SLit (-1)))] =>
    rewrite (cw_U_not Ex k _ c ltac:(cw_ew_peel; exact Ek) ltac:(lia) ltac:(lia)) in Hu end;
  rewrite U_lit in Hu by lia; apply Z.ltb_lt in Hu; lia.
(* the write windows of a state after `andi sp,sp,-32`: read-only, or a window of the re-anchored atom m (Um :
   bv_unsigned (ew _ m) = spmv) or of atom 2 (Usp : bv_unsigned (ew _ 2) = spv), each in the caller's stack allowance
   from sp0v *)
Ltac cw_awr_anchor m Usp Um spv spmv sp0v :=
  lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyv ?ownv =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk s0 fp b0 bc lyv ownv) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ m (spmv - sp0v));
    [ reflexivity | rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite Um; lia
    | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0v));
    [ reflexivity | rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite Usp; lia
    | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ].
(* the release run over a frame-flag store: YCbq.aj_flag_store with its 16 journal arguments *)
Ltac cw_run_flag tblok HS HJ :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl YP03.FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl YP03.FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let HL := aj_laws in let HSL := aj_segs_low in let HWX := aj_wx in
let HML := lazymatch goal with H : model_laws _ |- _ => H end in
let HASF := lazymatch goal with H : astack_free_law _ _ |- _ => H end in
let HFFL := lazymatch goal with H : YCbq.frame_flag_lawP _ _ |- _ => H end in
eapply (YCbq.aj_flag_store segs _ HL HSL HML tbl tblok HWX HASF HFFL W YP03.FUEL E ss ss' st ms
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
[ clear Hrun | clear Hrun | clear Hrun | clear Hrun HS HJ; aj_after_run HS HJ ]
end
end
end.
