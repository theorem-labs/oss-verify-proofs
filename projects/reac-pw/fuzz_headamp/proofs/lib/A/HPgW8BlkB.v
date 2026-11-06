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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgW8Kit.v; 101 of its 146 lines of code are new or changed and 291 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8BlkA.v at 888d1ffb4c3; module paths fuzz_role -> fuzz_headamp, RPgBase / RPgCSpec / RPgImgA / RPgMem / RPgSeg -> HPgBase / HPgCSpec / HPgImgA / HPgMem / HPgSeg, the rl_ / rm_ / rs_ prefixes -> hd_ / hm_ / hs_; the run's start 0x8165c -> 0x8237c and the memcpy return address 0x817a4 -> 0x824c4 (alreloc a5c53bb2bed4); class-4 frame (1024 bytes), real frame 0x1e0 bytes. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgW8BlkA.v, with its numbers changed; 141 of its 208 lines of code are new or changed and 79 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8BlkB.v at 888d1ffb4c3; module paths fuzz_role -> fuzz_headamp, RPgBase / RPgCSpec / RPgImgA / RPgMem / RPgSeg -> HPgBase / HPgCSpec / HPgImgA / HPgMem / HPgSeg, the rl_ / rm_ / rs_ prefixes -> hd_ / hm_ / hs_; the four run pcs 0x817a4 / 0x817f0 / 0x81850 and the two exits 0x80a80 / 0x81ccc -> 0x824c4 / 0x82510 / 0x82570 and 0x817a0 / 0x82a14 (alreloc a5c53bb2bed4, the two pcs it left unmapped by the plan's alignment twins). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW8Kit HPgW8BlkA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition W_B : Z := 0x824c4.
Definition W_C : Z := 0x82510.
Definition W_D : Z := 0x82570.
Definition W_LOOP : Z := 0x817a0.
Definition W_CLOSE : Z := 0x82a14.
Definition r_lenv (v : sv) := YP09.mkRegion (Some 21%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 v)].
Definition r_fsh := YP09.mkRegion (Some 19%nat) 0x1e 0x2b 0x1e 0x2b [].
Definition r_ne := YP09.mkRegion (Some 27%nat) 0x4d14 0x4d18 0x4d14 0x4d18 [YP09.mkChunk 0x4d14 (CVal 4 (SOff A_NE 0))].
Definition al_ne : sv * sv := (SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 0x4d14) (SLit 3)) (SOff 23 0), SOff 20 418).

(* run B: after the body's memcpy, to the pad's memset *)
Definition ssB : sstate := mkSS W_B sr_atoms [r_lenv (SOff A_L 8); r_sh4] None
  (mkFacts [(27%nat, mkAF 4096 (2 ^ 47) 4); (A_L, mkAF 0 5384 3); (24%nat, mkAF 0 45 0)] [] []).
(* run C: after the pad's memset; fs = 0 runs to the loop's exit, fs = 1 to the record's memcpy *)
Definition fC (fs : Z) : list (nat * afact) :=
  [(27%nat, mkAF 4096 (2 ^ 47) 4); (A_L, mkAF 0 5384 3); (A_SZ, mkAF 0 45 0); (24%nat, mkAF 0 7 0);
   (A_FS, mkAF fs fs 0); (A_KK, mkAF 0 31 0); (A_CNT, mkAF 1 32 0); (A_NE, mkAF 0 31 0)].
Definition len_C : sv := SAlu ALU_ADD (SOff A_L 8) (SOff A_SZ 0).
Definition br_end (last : bool) : acond :=
  if last then mkAC BC_EQ (SOff A_KK 1) (SOff A_CNT 0) else mkAC BC_NE (SOff A_KK 1) (SOff A_CNT 0).
Definition ssC0 (last : bool) : sstate := mkSS W_C sr_atoms [r_slots; r_lenv len_C; r_sh4; r_fsh] None
  (mkFacts (fC 0) [mkAC BC_EQ (SOff A_FS 0) (SLit 0); br_end last] [al_ne]).
Definition ssC1 : sstate := mkSS W_C sr_atoms [r_slots; r_lenv len_C; r_sh4; r_ne] None
  (mkFacts (fC 1) [] [al_ne]).
(* run D: after the record's memcpy, to the loop's exit *)
Definition ssD (last : bool) : sstate := mkSS W_D sr_atoms [r_slots; r_fsh] None
  (mkFacts [(A_KK, mkAF 0 31 0); (A_CNT, mkAF 1 32 0)] [br_end last] []).


(* ============================== shared pieces of the entry states ============================== *)
Lemma wmod64_8 : forall x, (x mod 2 ^ 64) mod 8 = x mod 8.
Proof.
intros x. rewrite (Z.mod_eq x (2 ^ 64)) by lia.
replace (x - 2 ^ 64 * (x / 2 ^ 64)) with (x + (- (x / 2 ^ 64) * 2 ^ 61) * 8) by ring.
apply Z.mod_add. lia.
Qed.
Definition pad_sv : sv :=
  SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 24 0) (SLit (-1))) (SLit (-8)))
    (SMd M_MUL (SOff 33 0) (SLit (-1)))) (SLit 7).
Lemma wU8_add : forall E a b, U E (SAlu ALU_ADD a b) mod 8 = (U E a + U E b) mod 8.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. apply wmod64_8. Qed.
Lemma wU8_mul : forall E a c, U E (SMd M_MUL a (SLit c)) mod 8 = (U E a * c) mod 8.
Proof.
intros E a c. rewrite U_SMd, U_SLit. cbn [zmd_raw]. unfold zcanon, M64. rewrite wmod64_8.
rewrite <- Zmult_mod_idemp_r, wmod64_8, Zmult_mod_idemp_r. reflexivity.
Qed.
Lemma wU8_lit : forall E c, U E (SLit c) mod 8 = c mod 8.
Proof. intros E c. rewrite U_SLit. unfold zcanon, M64. apply wmod64_8. Qed.
Lemma wU_pad : forall E sz L, bv_unsigned (ew E 24) = sz -> bv_unsigned (ew E 33) = L -> L mod 8 = 0 ->
  0 <= sz < 2 ^ 63 -> 0 <= L < 2 ^ 63 -> U E pad_sv = Model.pad8 sz.
Proof.
intros E sz L H24 H33 HL8 Hsz HL. unfold pad_sv.
rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id 7) by (unfold M64; lia).
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
rewrite zcanon_id by (pose proof (Z.mod_pos_bound (U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 24 0) (SLit (-1))) (SLit (-8))) (SMd M_MUL (SOff 33 0) (SLit (-1))))) 8 ltac:(lia)); unfold M64; lia).
assert (A1 : U E (SMd M_MUL (SOff 24 0) (SLit (-1))) mod 8 = (- sz) mod 8)
  by (rewrite wU8_mul, (wU_off0 E 24 sz H24) by lia; f_equal; ring).
assert (A2 : U E (SMd M_MUL (SOff 33 0) (SLit (-1))) mod 8 = (- L) mod 8)
  by (rewrite wU8_mul, (wU_off0 E 33 L H33) by lia; f_equal; ring).
assert (A3 : U E (SAlu ALU_ADD (SMd M_MUL (SOff 24 0) (SLit (-1))) (SLit (-8))) mod 8 = (- sz - 8) mod 8)
  by (rewrite wU8_add, Zplus_mod, A1, wU8_lit, <- Zplus_mod; f_equal; ring).
rewrite wU8_add, Zplus_mod, A3, A2, <- Zplus_mod.
replace (- sz - 8 + - L) with (- sz + (- 1 - L / 8) * 8)
  by (pose proof (Z.div_mod L 8 ltac:(lia)); lia).
rewrite Z.mod_add by lia. unfold Model.pad8.
rewrite <- (Z.mod_add (8 - sz mod 8) (- 1) 8) by lia.
rewrite (Z.mod_eq sz 8) by lia.
replace (8 - (sz - 8 * (sz / 8)) + -1 * 8) with (- sz + (sz / 8) * 8) by ring.
rewrite Z.mod_add by lia. reflexivity.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws rsegs B := YG0q.AR_laws_ok rsegs B.

(* the zone facts of the pp block, for the apartness of its bytes from its shadow bytes *)
Lemma wpp_zone : forall pp, pp mod 16 = 0 -> in_app pp 19744 -> pp + 19744 <= alloc_ceiling ->
  4096 <= pp /\ 0x7fff8000 <= shadow_addr pp /\ shadow_addr pp + 2468 <= 0x10007fff8000 /\
  (pp + 19744 <= 0x7fff7000 \/ 0x10007fff8000 <= pp).
Proof.
intros pp H16 Happ Hhi. pose proof YM05.alloc_ceiling_val as Hceil.
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happ. destruct Happ as [Hlo Hz].
unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos pp 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le pp 8 ltac:(lia)).
split; [lia|]. split; [lia|]. split; [lia|]. destruct Hz as [Hz|[Hz1 Hz2]]; [left | right]; lia.
Qed.

(* ============================== run B: 0x824c4 to the pad's memset ============================== *)
Lemma w_blkB : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W regs mem md k (pp L sz : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem md k ->
In (pp, Layout.PP_SIZE) (ablocks B ly2 S2) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
getr regs 20 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 21 = w64 (pp + 0x4000) ->
getr regs 27 = w64 pp -> getr regs 24 = w64 sz ->
val_mem rsegs (mrestrict (w_H W) mem) (pp + 0x4000) 8 (L + 8) ->
(forall i, 0 <= i < 2468 -> aview rsegs (w_H W) mem (shadow_addr pp + i) = Some 0) ->
(forall i, 0 <= i < 19744 -> apresent (w_H W) mem (pp + i)) ->
pp mod 16 = 0 -> in_app pp 19744 -> pp + 19744 <= alloc_ceiling ->
0 <= L <= 5384 -> L mod 8 = 0 -> 0 <= sz <= 45 ->
SRr rsegs W (cfg_at rsegs W_B regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
 c' = mkCfg (mkst regs' (Z_to_bv 64 W_MEMSET) mem' (seg_rom rsegs)) md' /\
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem' md' k /\ same_io md md' /\
 getr regs' 1 = w64 0x82510 /\ getr regs' 10 = w64 (pp + L + 8 + sz) /\ getr regs' 11 = w64 0 /\
 getr regs' 12 = w64 (Model.pad8 sz) /\ getr regs' 24 = w64 (Model.pad8 sz) /\
 (forall r, In r wkeep -> getr regs' r = getr regs r) /\
 val_mem rsegs (mrestrict (w_H W) mem') (pp + 0x4000) 8 (L + 8 + sz) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (pp + 0x4000 <= a < pp + 0x4000 + 8) ->
  aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W regs mem md k pp L sz
HJ Hin Hfr H20 H21 H27 H24 HLEN HSH HWR Hpp16 Happ Hpphi HL HL8 Hsz.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof YM05.alloc_ceiling_val as Hceil.
destruct (wpp_zone pp Hpp16 Happ Hpphi) as (Hpplo & HshB & HshB2 & Hz).
set (E := Ereg regs (wext 0 L 0 0 0 0 0 0 0 0)).
assert (HAE : env_agree 32 (Ereg regs (wext 0 L 0 0 0 0 0 0 0 0)) E) by apply env_agree_refl.
destruct (wext_ew regs 0 L 0 0 0 0 0 0 0 0) as (_ & X33 & _). fold E in X33.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; exact (ew_Ereg_nat regs _ n r Hn)).
assert (Hpp8 : pp mod 8 = 0) by (apply wmod16_8; exact Hpp16).
assert (Hsh4 : shadow_addr (pp + 0x4000) = shadow_addr pp + 2048) by (rewrite wshadow_pp_L by (try lia; reflexivity); reflexivity).
assert (U20 : bv_unsigned (ew E 20) = shadow_addr pp + 2048) by (rewrite (EE 20%nat 20%bv eq_refl), H20, Hsh4; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = pp + 0x4000) by (rewrite (EE 21%nat 21%bv eq_refl), H21; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite (EE 27%nat 27%bv eq_refl), H27; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = sz) by (rewrite (EE 24%nat 24%bv eq_refl), H24; apply unsigned_lit_small; lia).
assert (U33a : bv_unsigned (ew E A_L) = L) by (rewrite X33; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = L) by exact U33a.
assert (HS : st_ok rsegs E ssB (restrict (w_H W) (mkst regs (Z_to_bv 64 W_B) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ssB. apply (entry_st_ok_full rsegs). all: fold E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; [ | | apply Forall_nil]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val r_lenv r_sh4].
    + rewrite U21. split; [lia|]. split; [lia|].
      split; [intros o Ho; replace (pp + 0x4000 + o) with (pp + (0x4000 + o)) by lia; apply apresent_writable, HWR; lia|].
      repeat apply Forall_cons; [ | apply Forall_nil].
      apply (wchunk8 E _ (pp + 0x4000) 0 _ (L + 8)); [cbn [sv_denot]; rewrite (U33 : bv_unsigned (ew E A_L) = L); reflexivity|].
      rewrite Z.add_0_r, Z.mod_small by lia. exact HLEN.
    + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; [ | | apply Forall_nil]; apply wchunk1z.
      * rewrite <- Z.add_assoc. apply HSH. lia.
      * rewrite <- Z.add_assoc. apply HSH. lia.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val r_lenv r_sh4].
    rewrite U21, U20. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct Hz as [Hz|Hz]; repeat split; lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U27, U33a, U24.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    repeat split; lia. }
unfold cfg_at. change (w64 W_B) with (Z_to_bv 64 W_B).
aj_run wtbl_ok HS HJ.
- lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 ow) end.
  assert (Haw : forall a, pp <= a < pp + Layout.PP_SIZE ->
    awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own a).
  { intros a Ha. replace a with (pp + (a - pp)) by lia. apply (hd_fresh_awr _ _ _ _ _ _ _ pp Layout.PP_SIZE); [exact Hin | exact Hfr |].
    unfold req_size, Layout.PP_SIZE in *. cbn. lia. }
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply awr_ok_cons_gen; [reflexivity | eassumption | intros a Ha; apply Haw; unfold Layout.PP_SIZE; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia |] ].
- lazymatch goal with
  | HS1 : st_ok _ _ ?ssf (restrict _ ?msf), HJ1 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdf _,
    HFr1 : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    apply SRr_ret; split; [reflexivity|];
    exists (ms_regs msf), (ms_mem msf), mdf;
    rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HS1 eq_refl) at 1;
    rename HS1 into HSf, HJ1 into HJf, HFr1 into HFrf
  end.
  lazymatch type of HSf with st_ok _ _ ?ssf ?msf =>
    let rl := eval vm_compute in (nth 0 (ss_mem ssf) (YP09.mkRegion None 0 0 0 0 [])) in
    assert (Inl : In rl (ss_mem ssf)) by (vm_compute; repeat (first [left; reflexivity | right]))
  end.
  pose proof (fun c Hc => w_chunk_of _ _ _ _ c HSf Inl Hc) as CL.
  cbn [YP09.r_chunks YP09.r_base base_val ms_mem restrict] in CL. rewrite U21 in CL.
  assert (Upad : U E pad_sv = Model.pad8 sz) by (apply (wU_pad E sz L); [exact U24 | exact U33 | exact HL8 | lia | lia]).
  split; [reflexivity|].
  split; [exact HJf|].
  split; [apply HPgSteps.same_io_wvb|].
  split; [wreg HSf (1%bv : bv 5); reflexivity|].
  split; [wreg HSf (10%bv : bv 5); rewrite denot_lit_U; unfold w64; f_equal;
          rewrite !U_SAlu; cbn [zalu_raw]; rewrite (wU_off E 24 8 sz U24), (wU_off0 E 27 pp U27), (wU_off0 E 33 L U33) by lia;
          rewrite (zcanon_id (sz + 8 + pp)) by (unfold M64; lia); rewrite zcanon_id by (unfold M64; lia); lia|].
  split; [wreg HSf (11%bv : bv 5); reflexivity|].
  split; [wreg HSf (12%bv : bv 5); rewrite denot_lit_U; unfold w64; f_equal;
          rewrite U_SAlu, U_SLit; cbn [zalu_raw]; fold pad_sv; rewrite Upad;
          pose proof (Model.pad8_bound sz); rewrite (zcanon_id 0) by (unfold M64; lia); rewrite zcanon_id by (unfold M64; lia); lia|].
  split; [wreg HSf (24%bv : bv 5); rewrite denot_lit_U; unfold w64; f_equal; fold pad_sv; exact Upad|].
  split; [intros r Hr; exact (regs_kept_of_st_ok rsegs E _ _ regs _ wkeep HSf HAE ltac:(vm_compute; reflexivity) r Hr)|].
  split.
  { pose proof (CL _ ltac:(cbn; left; reflexivity)) as C0. apply w_chunk8 in C0. rewrite Z.add_0_r in C0.
    replace (L + 8 + sz) with (U E (SAlu ALU_ADD (SOff 24 8) (SOff 33 0))); [exact C0|].
    rewrite U_SAlu. cbn [zalu_raw]. rewrite (wU_off E 24 8 sz U24), (wU_off0 E 33 L U33) by lia.
    rewrite zcanon_id by (unfold M64; lia). lia. }
  intros a Ha H1. apply aview_eq_of. apply HFrf. rewrite unsigned_lit_small by exact Ha.
  intros (r & Hr & Hw). unfold ssB in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_lenv r_sh4] in Hw; try lia.
Qed.
End w.
