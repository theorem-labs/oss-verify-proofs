(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 338 of its 381 lines of code are new or changed and 247 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 3e85ad4cf5dd for reac-pw/fuzz_rate's
   image A: the run is the first run of the piece "write + record" (J 0x81e00 -> __asan_memcpy 0x51860) and its
   statement is lib/A/RtPgW8Kit.v's rw8_runA_stmt (post RtPgSteps.rts_post); the start state adds the frame for
   locals (e's type and size at F + 0xf0 / F + 0xf4, read through s3 = F + 0xe0) and two capacity conditions; the
   eight bytes written are read back as e->size and e->type (the second word carries the engine's sign extension). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW8A.v, with its module paths and module names changed; 284 of its 336 lines of code are new or changed and 329 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8Kit.v at 888d1ffb4c3; module paths fuzz_role -> fuzz_headamp, RPgBase / RPgCSpec / RPgImgA / RPgMem / RPgSeg -> HPgBase / HPgCSpec / HPgImgA / HPgMem / HPgSeg, the rl_ / rm_ / rs_ prefixes -> hd_ / hm_ / hs_; role's cfg-walk image facts (cfg_wx, cfg_segs_low, same_io_wvb) -> HPgSteps' (img_wx, img_segs_low, same_io_wvb); W_J 0x8165c -> 0x8237c, __asan_memcpy 0x510d4 -> 0x51d0c, __asan_memset 0x51570 -> 0x521a8 (alreloc a5c53bb2bed4); the ten real-frame cells the piece reads moved by headamp's frame-slot map (R+0x60 0x68 0x78 0xa8 0xc0 0xd0 0xd8 0xe0 0xe8 0xf0 -> R+0x88 0x90 0xa0 0xc8 0xe0 0xe8 0xf8 0x100 0x108 0x110, the region [R+0x60, R+0xf8) -> [R+0x88, R+0x118)); the frame for locals is class 4 (1024 bytes) and the real frame 0x1e0 bytes. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ============================== the code, the table ============================== *)
Definition W_J : Z := 0x8237c.
Definition W_MEMCPY : Z := 0x51d0c.
Definition W_MEMSET : Z := 0x521a8.
Definition wtbl : ctable := build_table rsegs W_J 144 TEmpty.
Lemma wtbl_ok : table_ok rsegs wtbl.
Proof. apply build_table_ok0. unfold W_J. lia. Qed.

Definition M2 (z : Z) : Z := z mod 2 ^ 64.
(* the env: registers are their own atoms; the extras *)
Definition A_F : nat := 32. Definition A_L : nat := 33. Definition A_Q : nat := 34. Definition A_SQ : nat := 35.
Definition A_TY : nat := 36. Definition A_SZ : nat := 37. Definition A_FS : nat := 38. Definition A_KK : nat := 39.
Definition A_CNT : nat := 40. Definition A_NE : nat := 41.
Definition wext (F L Q SQ ty sz fs kk cnt ne : Z) : list word := map (Z_to_bv 64) [F; L; Q; SQ; ty; sz; fs; kk; cnt; ne].

(* the R-relative cells the piece reads (hs_Kc / hs_L_Dc of the cut), with the engine's chunk values *)
Definition wslot_chunks : list YP09.chunk :=
[ YP09.mkChunk 0x88 (CVal 8 (SOff 27 0x4014));
  YP09.mkChunk 0x90 (CVal 8 (SAlu ALU_SRL (SOff 27 0x4d14) (SLit 3)));
  YP09.mkChunk 0xa0 (CVal 8 (SOff 27 0x4d14));
  YP09.mkChunk 0xc8 (CVal 8 (SOff A_CNT 0));
  YP09.mkChunk 0xe0 (CVal 8 (SOff A_F 0xf8));
  YP09.mkChunk 0xe8 (CVal 8 (SOff A_FS 0));
  YP09.mkChunk 0xf8 (CVal 8 (SOff A_KK 0));
  YP09.mkChunk 0x100 (CVal 8 (SLit (M2 (-0x4001))));
  YP09.mkChunk 0x108 (CVal 8 (SLit (M2 (-0x3ffd))));
  YP09.mkChunk 0x110 (CVal 8 (SOff A_F 0xf0)) ].
Definition wslot_vals (F pp fs kk cnt : Z) : list (Z * Z) :=
[ (0x88, pp + 0x4014); (0x90, Z.shiftr (pp + 0x4d14) 3); (0xa0, pp + 0x4d14); (0xc8, cnt); (0xe0, F + 0xf8);
  (0xe8, fs); (0xf8, kk); (0x100, -0x4001); (0x108, -0x3ffd); (0x110, F + 0xf0) ].
Definition r_slots := YP09.mkRegion (Some 9%nat) 0x88 0x118 0 0 wslot_chunks.
Definition r_e := YP09.mkRegion (Some A_F) 0xf0 0xf8 0 0
  [YP09.mkChunk 0xf0 (CVal 4 (SOff A_TY 0)); YP09.mkChunk 0xf4 (CVal 4 (SOff A_SZ 0))].
Definition r_len (c : Z) := YP09.mkRegion (Some 21%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff A_L c))].
Definition r_buf := YP09.mkRegion (Some A_Q) 0 8 0 8 [].
Definition r_shq := YP09.mkRegion (Some A_SQ) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition r_sh4 := YP09.mkRegion (Some 20%nat) 0 419 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0)); YP09.mkChunk 418 (CVal 1 (SLit 0))].
Definition rsA : smem := [r_slots; r_e; r_len 0; r_buf; r_shq; r_sh4].
Definition fatA : list (nat * afact) :=
[ (27%nat, mkAF 4096 (2 ^ 47) 4); (A_L, mkAF 0 5384 3); (A_Q, mkAF 4096 (2 ^ 47 + 5384) 3);
  (A_TY, mkAF 0 (2 ^ 32 - 1) 0); (A_SZ, mkAF 0 45 0) ].
Definition fcA : list acond :=
[ mkAC BC_GEU (SOff A_L (-16381)) (SLit (M2 (-0x4001))); mkAC BC_GEU (SOff A_L (-16377)) (SLit (M2 (-0x4001))) ].
Definition shx (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff A_Q c) (SLit 3)) (SOff 23 0).
Definition falA : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 27 0) (SOff A_L 0), SOff A_Q 0);
  (shx 0, SOff A_SQ 0); (shx 3, SOff A_SQ 0); (shx 4, SOff A_SQ 0); (shx 7, SOff A_SQ 0);
  (SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 0x4d14) (SLit 3)) (SOff 23 0), SOff 20 418) ].
Definition ssA : sstate := mkSS W_J sr_atoms rsA None (mkFacts fatA fcA falA).


(* ============================== generic helpers ============================== *)
Lemma wsv_off : forall E n c v, bv_unsigned (ew E n) = v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n c v H. cbn [sv_denot]. rewrite H. reflexivity. Qed.
Lemma wZ_to_bv_mod : forall x, Z_to_bv 64 (x mod 2 ^ 64) = Z_to_bv 64 x.
Proof.
intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.
Section h. Context {fx : YK11.FPState}.
Lemma wchunk8 : forall E (m : word -> option byte) base off e v,
sv_denot E e = Z_to_bv 64 v -> val_mem rsegs m (base + off) 8 (v mod 2 ^ 64) -> YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E m base off e v He Hv. apply (chunk_ok_val rsegs E m base off 8 e (v mod 2 ^ 64)).
- rewrite wZ_to_bv_mod. exact He.
- change (8 * Z.of_N 8) with 64. apply Z.mod_pos_bound. lia.
- lia.
- exact Hv.
Qed.
Lemma wchunk4 : forall E (m : word -> option byte) base off e v,
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> val_mem rsegs m (base + off) 4 v -> YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 4 e)).
Proof.
intros E m base off e v He Hr Hv. apply (chunk_ok_val rsegs E m base off 4 e v); [exact He | change (8 * Z.of_N 4) with 32; lia | lia | exact Hv].
Qed.
End h.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws rsegs B := YG0q.AR_laws_ok rsegs B.

Lemma wchunk1z : forall E H mem base off,
aview rsegs H mem (base + off) = Some 0 -> YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk off (CVal 1 (SLit 0))).
Proof.
intros E H mem base off Ha i Hi. cbn [c_len YP09.c_val YP09.c_off cv_len] in Hi. change (Z.of_N 1) with 1 in Hi.
assert (i = 0) by lia. subst i. exists (Z_to_bv 8 0). split.
- cbn [cbyte YP09.c_val YP09.c_off sv_denot byte_of_word]. f_equal.
- cbn [YP09.c_off]. rewrite Z.add_0_r. unfold aview in Ha.
destruct (mbyte rsegs (mrestrict H mem) (base + off)) as [b|] eqn:Eb; cbn [option_map] in Ha; [|discriminate].
injection Ha as Ha. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 b), Ha. reflexivity.
Qed.
Lemma wmod16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 16) with ((2 * q) * 8) by lia. apply Z_mod_mult. Qed.

Lemma wshadow_pp_L : forall pp L, pp mod 8 = 0 -> 0 <= L -> L mod 8 = 0 -> shadow_addr (pp + L) = shadow_addr pp + L / 8.
Proof.
intros pp L H1 H2 H3. unfold shadow_addr.
rewrite (Z.div_mod pp 8) at 1 by lia. rewrite (Z.div_mod L 8) at 1 by lia. rewrite H1, H3.
replace (8 * (pp / 8) + 0 + (8 * (L / 8) + 0)) with ((pp / 8 + L / 8) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.
Lemma wext_ew : forall regs F L Q SQ ty sz fs kk cnt ne,
let E := Ereg regs (wext F L Q SQ ty sz fs kk cnt ne) in
ew E A_F = Z_to_bv 64 F /\ ew E A_L = Z_to_bv 64 L /\ ew E A_Q = Z_to_bv 64 Q /\ ew E A_SQ = Z_to_bv 64 SQ /\
ew E A_TY = Z_to_bv 64 ty /\ ew E A_SZ = Z_to_bv 64 sz /\ ew E A_FS = Z_to_bv 64 fs /\ ew E A_KK = Z_to_bv 64 kk /\
ew E A_CNT = Z_to_bv 64 cnt /\ ew E A_NE = Z_to_bv 64 ne.
Proof. intros. repeat split; reflexivity. Qed.

Lemma wA_entry : forall (W : world rsegs) regs mem (R F pp L ty sz fs kk cnt : Z),
getr regs 9 = w64 R -> getr regs 20 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 21 = w64 (pp + 0x4000) ->
getr regs 23 = w64 SHADOW_OFF -> getr regs 27 = w64 pp ->
Forall (fun c => val_mem rsegs (mrestrict (w_H W) mem) (R + fst c) 8 (snd c mod 2 ^ 64)) (wslot_vals F pp fs kk cnt) ->
val_mem rsegs (mrestrict (w_H W) mem) (F + 0xf0) 4 ty -> val_mem rsegs (mrestrict (w_H W) mem) (F + 0xf4) 4 sz ->
val_mem rsegs (mrestrict (w_H W) mem) (pp + 0x4000) 8 L ->
(forall i, 0 <= i < 2468 -> aview rsegs (w_H W) mem (shadow_addr pp + i) = Some 0) ->
(forall i, 0 <= i < 19744 -> apresent (w_H W) mem (pp + i)) ->
pp mod 16 = 0 -> in_app pp 19744 -> in_app F 1024 -> pp + 19744 <= F \/ F + 1024 <= pp ->
pp + 19744 <= alloc_ceiling -> F + 1024 <= alloc_ceiling ->
alloc_ceiling <= R -> R + 0x1e0 <= 2 ^ 47 ->
0 <= L <= 5384 -> L mod 8 = 0 -> 0 <= ty < 2 ^ 32 -> 0 <= sz <= 45 ->
0 <= fs < 2 ^ 64 -> 0 <= kk < 2 ^ 64 -> 0 <= cnt < 2 ^ 64 ->
st_ok rsegs (Ereg regs (wext F L (pp + L) (shadow_addr (pp + L)) ty sz fs kk cnt 0)) ssA
(restrict (w_H W) (mkst regs (Z_to_bv 64 W_J) mem (seg_rom rsegs))).
Proof.
intros W regs mem R F pp L ty sz fs kk cnt H9 H20 H21 H23 H27 HSL HTY HSZ HLEN HSH HWR
Hpp16 Happ HFapp HpF Hpphi HFhi HR1 HR2 HL HL8 Hty Hsz Hfs Hkk Hcnt.
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happ, HFapp.
destruct Happ as [Hpplo Hppz]. destruct HFapp as [HFlo HFz].
pose proof YM05.alloc_ceiling_val as Hceil.
set (E := Ereg regs (wext F L (pp + L) (shadow_addr (pp + L)) ty sz fs kk cnt 0)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; exact (ew_Ereg_nat regs _ n r Hn)).
assert (EX : forall j, ew E (32 + j) = nth j (wext F L (pp + L) (shadow_addr (pp + L)) ty sz fs kk cnt 0) (Z_to_bv 64 0))
by (intros j; exact (ew_Ereg_extra regs _ j)).
assert (Hpp8 : pp mod 8 = 0) by (apply wmod16_8; exact Hpp16).
assert (HL673 : 0 <= L / 8 <= 673) by (split; [apply Z.div_pos; lia | change 673 with (5384 / 8); apply Z.div_le_mono; lia]).
assert (Hsh8 : shadow_addr (pp + L) = shadow_addr pp + L / 8) by (apply wshadow_pp_L; lia).
assert (Hsh4 : shadow_addr (pp + 0x4000) = shadow_addr pp + 2048) by (rewrite wshadow_pp_L by (try lia; reflexivity); reflexivity).
assert (HshB : 0x7fff8000 <= shadow_addr pp /\ shadow_addr pp + 2468 <= 0x10007fff8000).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos pp 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le pp 8 ltac:(lia)). lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = shadow_addr pp + 2048) by (rewrite (EE 20%nat 20%bv eq_refl), H20, Hsh4; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = pp + 0x4000) by (rewrite (EE 21%nat 21%bv eq_refl), H21; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (rewrite (EE 23%nat 23%bv eq_refl), H23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite (EE 27%nat 27%bv eq_refl), H27; apply unsigned_lit_small; lia).
destruct (wext_ew regs F L (pp + L) (shadow_addr (pp + L)) ty sz fs kk cnt 0) as (X32 & X33 & X34 & X35 & X36 & X37 & X38 & X39 & X40 & _).
fold E in X32, X33, X34, X35, X36, X37, X38, X39, X40.
assert (U32 : bv_unsigned (ew E A_F) = F) by (rewrite X32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E A_L) = L) by (rewrite X33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E A_Q) = pp + L) by (rewrite X34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E A_SQ) = shadow_addr pp + L / 8) by (rewrite X35, Hsh8; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E A_TY) = ty) by (rewrite X36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E A_SZ) = sz) by (rewrite X37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E A_FS) = fs) by (rewrite X38; apply unsigned_lit_small; lia).
assert (U39 : bv_unsigned (ew E A_KK) = kk) by (rewrite X39; apply unsigned_lit_small; lia).
assert (U40 : bv_unsigned (ew E A_CNT) = cnt) by (rewrite X40; apply unsigned_lit_small; lia).
clear X32 X33 X34 X35 X36 X37 X38 X39 X40 EX.
rewrite restrict_mkst_fx. unfold ssA. apply (entry_st_ok_full rsegs). all: fold E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- assert (HSLf : forall o v, In (o, v) (wslot_vals F pp fs kk cnt) ->
    val_mem rsegs (mrestrict (w_H W) mem) (R + o) 8 (v mod 2 ^ 64))
    by (intros o v Hin; exact (proj1 (Forall_forall _ _) HSL (o, v) Hin)).
  assert (HPR : forall o, 0 <= o < 19744 -> writable_at rsegs (mrestrict (w_H W) mem) (pp + o))
    by (intros o Ho; apply apresent_writable; apply HWR; exact Ho).
  unfold rsA. repeat apply Forall_cons; [ | | | | | | apply Forall_nil]; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val r_slots r_e r_len r_buf r_shq r_sh4].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    unfold wslot_chunks. repeat apply Forall_cons; [ | | | | | | | | | | apply Forall_nil].
    * apply (wchunk8 E _ R 0x88 _ (pp + 0x4014)); [cbn [sv_denot]; rewrite U27; reflexivity | apply HSLf; cbn; tauto].
    * apply (wchunk8 E _ R 0x90 _ (Z.shiftr (pp + 0x4d14) 3)); [| apply HSLf; cbn; tauto].
      rewrite denot_lit_U. f_equal. rewrite U_SAlu, U_SOff, U_SLit, U27. cbn [zalu_raw].
      change (Z.land (zcanon 3) 63) with 3. rewrite (zcanon_id (pp + 0x4d14)) by (unfold M64; lia).
      apply zcanon_id. rewrite Z.shiftr_div_pow2 by lia.
      split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold M64; lia].
    * apply (wchunk8 E _ R 0xa0 _ (pp + 0x4d14)); [cbn [sv_denot]; rewrite U27; reflexivity | apply HSLf; cbn; tauto].
    * apply (wchunk8 E _ R 0xc8 _ cnt); [cbn [sv_denot]; rewrite U40, Z.add_0_r; reflexivity | apply HSLf; cbn; tauto].
    * apply (wchunk8 E _ R 0xe0 _ (F + 0xf8)); [cbn [sv_denot]; rewrite U32; reflexivity | apply HSLf; cbn; tauto].
    * apply (wchunk8 E _ R 0xe8 _ fs); [cbn [sv_denot]; rewrite U38, Z.add_0_r; reflexivity | apply HSLf; cbn; tauto].
    * apply (wchunk8 E _ R 0xf8 _ kk); [cbn [sv_denot]; rewrite U39, Z.add_0_r; reflexivity | apply HSLf; cbn; tauto].
    * apply (wchunk8 E _ R 0x100 _ (-0x4001)); [cbn [sv_denot]; unfold M2; apply wZ_to_bv_mod | apply HSLf; cbn; tauto].
    * apply (wchunk8 E _ R 0x108 _ (-0x3ffd)); [cbn [sv_denot]; unfold M2; apply wZ_to_bv_mod | apply HSLf; cbn; tauto].
    * apply (wchunk8 E _ R 0x110 _ (F + 0xf0)); [cbn [sv_denot]; rewrite U32; reflexivity | apply HSLf; cbn; tauto].
  + rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; [ | | apply Forall_nil].
    * apply (wchunk4 E _ F 0xf0 _ ty); [cbn [sv_denot]; rewrite U36, Z.add_0_r; reflexivity | lia | exact HTY].
    * apply (wchunk4 E _ F 0xf4 _ sz); [cbn [sv_denot]; rewrite U37, Z.add_0_r; reflexivity | lia | exact HSZ].
  + rewrite U21. split; [lia|]. split; [lia|].
    split; [intros o Ho; replace (pp + 0x4000 + o) with (pp + (0x4000 + o)) by lia; apply HPR; lia|].
    repeat apply Forall_cons; [ | apply Forall_nil].
    apply (wchunk8 E _ (pp + 0x4000) 0 _ L); [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity|].
    rewrite Z.add_0_r, Z.mod_small by lia. exact HLEN.
  + rewrite U34. split; [lia|]. split; [lia|].
    split; [intros o Ho; replace (pp + L + o) with (pp + (L + o)) by lia; apply HPR; lia | apply Forall_nil].
  + rewrite U35. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; [ | apply Forall_nil].
    apply wchunk1z. rewrite Z.add_0_r. apply HSH. lia.
  + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; [ | | apply Forall_nil]; apply wchunk1z.
    * rewrite <- Z.add_assoc. apply HSH. lia.
    * rewrite <- Z.add_assoc. apply HSH. lia.
- apply pairwise_disjoint_of_extents. unfold rsA, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val r_slots r_e r_len r_buf r_shq r_sh4].
  rewrite U9, U32, U21, U34, U35, U20.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  clear HSL HSH HWR HTY HSZ HLEN EE H9 H20 H21 H23 H27.
  destruct Hppz as [Hz1 | [Hz2 Hz3]]; destruct HFz as [Hf1 | [Hf2 Hf3]]; destruct HpF as [HpF | HpF];
  repeat split; lia.
- split; [|split].
  + cbn [f_atoms fatA atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U27, U33, U34, U36, U37.
    assert (HQ8 : (pp + L) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hpp8, HL8; reflexivity).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    repeat split; lia.
  + cbn [f_conds fcA conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite !branch_geu_U, !U_SOff, !U_SLit, U33.
    assert (Hc1 : zcanon (L + -16381) = L + -16381 + 2 ^ 64)
      by (unfold zcanon, M64; rewrite <- (Z.mod_add (L + -16381) 1) by lia; rewrite Z.mod_small by lia; lia).
    assert (Hc2 : zcanon (L + -16377) = L + -16377 + 2 ^ 64)
      by (unfold zcanon, M64; rewrite <- (Z.mod_add (L + -16377) 1) by lia; rewrite Z.mod_small by lia; lia).
    assert (Hc3 : zcanon (M2 (-0x4001)) = 2 ^ 64 - 0x4001) by (vm_compute; reflexivity).
    rewrite Hc1, Hc2, Hc3.
    split; [apply negb_true_iff, Z.ltb_ge; lia|]. split; [apply negb_true_iff, Z.ltb_ge; lia|]. exact I.
  + cbn [f_alias falA alias_ok]. unfold shx.
    assert (HQd : forall c, 0 <= c < 8 -> (pp + L + c) / 8 = pp / 8 + L / 8).
    { intros c Hc. rewrite (Z.div_mod pp 8) at 1 by lia. rewrite (Z.div_mod L 8) at 1 by lia. rewrite Hpp8, HL8.
      replace (8 * (pp / 8) + 0 + (8 * (L / 8) + 0) + c) with (c + (pp / 8 + L / 8) * 8) by lia.
      rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
    assert (Hppd : (pp + 0x4d14) / 8 = pp / 8 + 2466).
    { rewrite (Z.div_mod pp 8) at 1 by lia. rewrite Hpp8.
      replace (8 * (pp / 8) + 0 + 0x4d14) with (4 + (pp / 8 + 2466) * 8) by lia.
      rewrite Z.div_add by lia. reflexivity. }
    assert (Hshp : shadow_addr pp = SHADOW_OFF + pp / 8) by reflexivity.
    unfold SHADOW_OFF in *.
    assert (HSRL : forall c, 0 <= c < 8 ->
      sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff A_Q c) (SLit 3)) (SOff 23 0)) = sv_denot E (SOff A_SQ 0)).
    { intros c Hc. apply U_inj. rewrite !U_SAlu, !U_SOff, !U_SLit, U34, U35, U23. cbn [zalu_raw].
      change (Z.land (zcanon 3) 63) with 3. unfold SHADOW_OFF.
      rewrite (zcanon_id (pp + L + c)) by (unfold M64; lia). rewrite Z.shiftr_div_pow2 by lia.
      change (2 ^ 3) with 8. rewrite HQd by lia. rewrite (zcanon_id (pp / 8 + L / 8)) by (unfold M64; lia).
      rewrite Hshp. unfold zcanon, M64. rewrite (Z.mod_small (0x7fff8000 + 0)) by lia. rewrite !Z.mod_small by lia. lia. }
    repeat split.
    * apply U_inj. rewrite U_SAlu, !U_SOff, U27, U33, U34. cbn [zalu_raw].
      rewrite !Z.add_0_r. rewrite (zcanon_id pp), (zcanon_id L) by (unfold M64; lia). reflexivity.
    * apply HSRL; lia.
    * apply HSRL; lia.
    * apply HSRL; lia.
    * apply HSRL; lia.
    * apply U_inj. rewrite !U_SAlu, !U_SOff, !U_SLit, U27, U23, U20. cbn [zalu_raw].
      change (Z.land (zcanon 3) 63) with 3. unfold SHADOW_OFF.
      rewrite (zcanon_id (pp + 0x4d14)) by (unfold M64; lia). rewrite Z.shiftr_div_pow2 by lia.
      change (2 ^ 3) with 8. rewrite Hppd. rewrite (zcanon_id (pp / 8 + 2466)) by (unfold M64; lia).
      rewrite Hshp. unfold zcanon, M64. rewrite (Z.mod_small (0x7fff8000 + 0)) by lia. rewrite !Z.mod_small by lia. lia.
Qed.

(* ============================== reading a run's final symbolic state ============================== *)
Lemma w_chunk_of : forall E ss ms r c, st_ok rsegs E ss ms -> In r (ss_mem ss) -> In c (YP09.r_chunks r) ->
YP09.chunk_ok rsegs E (ms_mem ms) (base_val E (YP09.r_base r)) c.
Proof.
intros E ss ms r c HS Hr Hc. destruct (st_ok_mem_ok rsegs E ss ms HS) as (_ & HF & _).
pose proof (proj1 (Forall_forall _ _) HF r Hr) as (_ & _ & _ & HC). exact (proj1 (Forall_forall _ _) HC c Hc).
Qed.
Lemma w_chunk1 : forall E m base off v, YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 1 v)) ->
mbyte rsegs m (base + off) = Some (Z_to_bv 8 (U E v)).
Proof.
intros E m base off v H. destruct (H 0 ltac:(cbn; lia)) as (b & Hb & Hm). cbn [cbyte YP09.c_val YP09.c_off] in Hb, Hm.
rewrite Z.add_0_r in Hm. rewrite Hm. injection Hb as <-. unfold byte_of_word, U. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
Qed.
Lemma w_chunk8 : forall E m base off v, YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 8 v)) ->
val_mem rsegs m (base + off) 8 (U E v).
Proof.
intros E m base off v H kk Hk. destruct (H (Z.of_nat kk) ltac:(cbn; lia)) as (b & Hb & Hm).
cbn [cbyte YP09.c_val YP09.c_off] in Hb, Hm. rewrite Hm. injection Hb as <-. f_equal.
unfold byte_of_word. rewrite hm_le_byte_bv by exact Hk. reflexivity.
Qed.
(* a byte of a 32-bit value is the same byte of any value congruent to it mod 2^32 *)
Lemma wbyte_sh : forall X y j, 0 <= j -> j + 8 <= 32 -> X mod 2 ^ 32 = y mod 2 ^ 32 ->
Z_to_bv 8 (Z.shiftr X j) = Z_to_bv 8 (Z.shiftr y j).
Proof.
intros X y j Hj Hj8 Hm. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
rewrite <- !Z.land_ones by lia. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.shiftr_spec by lia.
destruct (Z.ltb_spec n 8) as [Hl|Hg].
- rewrite Z.ones_spec_low by lia. rewrite !andb_true_r.
  rewrite <- (Z.mod_pow2_bits_low X 32 (n + j)) by lia. rewrite <- (Z.mod_pow2_bits_low y 32 (n + j)) by lia.
  rewrite Hm. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite !andb_false_r. reflexivity.
Qed.
Lemma wU_off0 : forall E n v, bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ 64 -> U E (SOff n 0) = v.
Proof. intros E n v H Hv. rewrite U_SOff, H, Z.add_0_r. apply zcanon_id. unfold M64. lia. Qed.
Lemma wU_off : forall E n c v, bv_unsigned (ew E n) = v -> 0 <= v + c < 2 ^ 64 -> U E (SOff n c) = v + c.
Proof. intros E n c v H Hv. rewrite U_SOff, H. apply zcanon_id. unfold M64. lia. Qed.
Lemma wU_srl : forall E e k, 0 <= k < 64 -> U E (SAlu ALU_SRL e (SLit k)) = Z.shiftr (U E e) k.
Proof.
intros E e k Hk. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id k) by (unfold M64; lia).
replace (Z.land k 63) with k by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 6) with 64; lia).
pose proof (U_range E e) as Hr. apply zcanon_id. rewrite Z.shiftr_div_pow2 by lia.
split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] | ].
apply (Z.le_lt_trans _ (U E e)); [apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|] | lia].
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). nia.
Qed.
Lemma wU_sext : forall E e, U E (SExt true 32 e) mod 2 ^ 32 = U E e mod 2 ^ 32.
Proof.
intros E e. rewrite U_SExt. change (Z.of_N 32) with 32. unfold zcanon, M64, bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
set (z := U E e mod 2 ^ 32).
set (w := (z + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31).
assert (Hw : w mod 2 ^ 32 = z mod 2 ^ 32).
{ unfold w. rewrite (Z.mod_eq (z + 2 ^ 31) (2 ^ 32)) by lia.
  replace (z + 2 ^ 31 - 2 ^ 32 * ((z + 2 ^ 31) / 2 ^ 32) - 2 ^ 31) with (z + (- ((z + 2 ^ 31) / 2 ^ 32)) * 2 ^ 32) by ring.
  apply Z.mod_add. lia. }
rewrite (Z.mod_eq w (2 ^ 64)) by lia.
replace (w - 2 ^ 64 * (w / 2 ^ 64)) with (w + (- (w / 2 ^ 64) * 2 ^ 32) * 2 ^ 32) by ring.
rewrite Z.mod_add by lia. rewrite Hw. unfold z. apply Z.mod_mod. lia.
Qed.
Lemma w_val4 : forall m a v x0 x1 x2 x3,
mbyte rsegs m a = Some (Z_to_bv 8 x0) -> mbyte rsegs m (a + 1) = Some (Z_to_bv 8 x1) ->
mbyte rsegs m (a + 2) = Some (Z_to_bv 8 x2) -> mbyte rsegs m (a + 3) = Some (Z_to_bv 8 x3) ->
Z_to_bv 8 x0 = Z_to_bv 8 (Z.shiftr v 0) -> Z_to_bv 8 x1 = Z_to_bv 8 (Z.shiftr v 8) ->
Z_to_bv 8 x2 = Z_to_bv 8 (Z.shiftr v 16) -> Z_to_bv 8 x3 = Z_to_bv 8 (Z.shiftr v 24) ->
val_mem rsegs m a 4 v.
Proof.
intros m a v x0 x1 x2 x3 H0 H1 H2 H3 E0 E1 E2 E3 kk Hk. rewrite hm_le_byte_bv by exact Hk.
destruct kk as [|[|[|[|kk]]]].
- change (Z.of_nat 0) with 0. rewrite Z.add_0_r, H0, E0. reflexivity.
- change (Z.of_nat 1) with 1. rewrite H1, E1. reflexivity.
- change (Z.of_nat 2) with 2. rewrite H2, E2. reflexivity.
- change (Z.of_nat 3) with 3. rewrite H3, E3. reflexivity.
- lia.
Qed.

End w.

(* a register of a run's final state, as the engine's symbolic value *)
Ltac wreg HS r :=
lazymatch type of HS with st_ok ?sg ?Ev ?ssf (restrict ?Hh ?msf) =>
rewrite (st_ok_restrict_reg sg Hh Ev ssf msf r HS);
let e := eval vm_compute in (sr_get (ss_regs ssf) r) in change (sr_get (ss_regs ssf) r) with e end.
