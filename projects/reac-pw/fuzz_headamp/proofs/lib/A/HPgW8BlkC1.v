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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgW8BlkA.v, with its numbers changed; 111 of its 184 lines of code are new or changed and 73 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8BlkC1.v at 888d1ffb4c3; module paths fuzz_role -> fuzz_headamp, RPgBase / RPgCSpec / RPgImgA / RPgMem / RPgSeg -> HPgBase / HPgCSpec / HPgImgA / HPgMem / HPgSeg, the rl_ / rm_ / rs_ prefixes -> hd_ / hm_ / hs_; the run's start 0x817f0 -> 0x82510 and the memcpy return address 0x81850 -> 0x82570 (alreloc a5c53bb2bed4, the latter unmapped by it and set to the plan's alignment twin); real frame 0x1e0 bytes. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW8Kit HPgW8BlkA HPgW8BlkB HPgW8Rok.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws rsegs B := YG0q.AR_laws_ok rsegs B.

Lemma w_chunk4v : forall E m base off v, YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 4 v)) ->
val_mem rsegs m (base + off) 4 (U E v).
Proof.
intros E m base off v H kk Hk. destruct (H (Z.of_nat kk) ltac:(cbn; lia)) as (b & Hb & Hm).
cbn [cbyte YP09.c_val YP09.c_off] in Hb, Hm. rewrite Hm. injection Hb as <-. f_equal.
unfold byte_of_word. rewrite hm_le_byte_bv by exact Hk. reflexivity.
Qed.

(* the alias of n_ent's shadow cell, as run A states it *)
Lemma w_al_ne_ok : forall E pp, bv_unsigned (ew E 27) = pp -> bv_unsigned (ew E 23) = SHADOW_OFF ->
  bv_unsigned (ew E 20) = shadow_addr pp + 2048 -> pp mod 8 = 0 -> 4096 <= pp -> pp + 19744 <= 2 ^ 47 ->
  sv_denot E (fst al_ne) = sv_denot E (snd al_ne).
Proof.
intros E pp U27 U23 U20 Hpp8 Hlo Hhi. unfold al_ne. cbn [fst snd].
assert (Hppd : (pp + 0x4d14) / 8 = pp / 8 + 2466).
{ rewrite (Z.div_mod pp 8) at 1 by lia. rewrite Hpp8.
  replace (8 * (pp / 8) + 0 + 0x4d14) with (4 + (pp / 8 + 2466) * 8) by lia.
  rewrite Z.div_add by lia. reflexivity. }
assert (Hshp : shadow_addr pp = SHADOW_OFF + pp / 8) by reflexivity.
pose proof (Z.div_pos pp 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le pp 8 ltac:(lia)).
unfold SHADOW_OFF in *.
apply U_inj. rewrite !U_SAlu, !U_SOff, !U_SLit, U27, U23, U20. cbn [zalu_raw].
change (Z.land (zcanon 3) 63) with 3.
rewrite (zcanon_id (pp + 0x4d14)) by (unfold M64; lia). rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 3) with 8. rewrite Hppd. rewrite (zcanon_id (pp / 8 + 2466)) by (unfold M64; lia).
rewrite Hshp. rewrite (zcanon_id (0x7fff8000 + 0)) by (unfold M64; lia).
rewrite !zcanon_id by (unfold M64; lia). lia.
Qed.

(* ============================== run C, first = 1: 0x82510 to the record's memcpy ============================== *)
Lemma w_blkC1 : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W regs mem md k (R F pp L sz kk cnt ne : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem md k ->
In (pp, Layout.PP_SIZE) (ablocks B ly2 S2) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
getr regs 9 = w64 R -> getr regs 20 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 21 = w64 (pp + 0x4000) ->
getr regs 23 = w64 SHADOW_OFF -> getr regs 27 = w64 pp -> getr regs 24 = w64 (Model.pad8 sz) ->
Forall (fun c => val_mem rsegs (mrestrict (w_H W) mem) (R + fst c) 8 (snd c mod 2 ^ 64)) (wslot_vals F pp 1 kk cnt) ->
val_mem rsegs (mrestrict (w_H W) mem) (pp + 0x4000) 8 (L + 8 + sz) ->
val_mem rsegs (mrestrict (w_H W) mem) (pp + 0x4d14) 4 ne ->
(forall i, 0 <= i < 2468 -> aview rsegs (w_H W) mem (shadow_addr pp + i) = Some 0) ->
(forall i, 0 <= i < 19744 -> apresent (w_H W) mem (pp + i)) ->
pp mod 16 = 0 -> in_app pp 19744 -> pp + 19744 <= alloc_ceiling ->
alloc_ceiling <= R -> R + 0x1e0 <= 2 ^ 47 -> 0 <= F < 2 ^ 47 ->
0 <= L <= 5384 -> L mod 8 = 0 -> 0 <= sz <= 45 -> 0 <= kk <= 31 -> 1 <= cnt <= 32 -> 0 <= ne <= 31 ->
SRr rsegs W (cfg_at rsegs W_C regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
 c' = mkCfg (mkst regs' (Z_to_bv 64 W_MEMCPY) mem' (seg_rom rsegs)) md' /\
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem' md' k /\ same_io md md' /\
 getr regs' 1 = w64 0x82570 /\ getr regs' 10 = w64 (pp + 0x4014 + 104 * ne) /\ getr regs' 11 = w64 (F + 0xf0) /\
 getr regs' 12 = w64 104 /\
 (forall r, In r wkeep -> getr regs' r = getr regs r) /\
 val_mem rsegs (mrestrict (w_H W) mem') (pp + 0x4000) 8 (L + 8 + sz + Model.pad8 sz) /\
 val_mem rsegs (mrestrict (w_H W) mem') (pp + 0x4d14) 4 (ne + 1) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (pp + 0x4000 <= a < pp + 0x4000 + 8) -> ~ (pp + 0x4d14 <= a < pp + 0x4d14 + 4) ->
  aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W regs mem md k R F pp L sz kk cnt ne
HJ Hin Hfr H9 H20 H21 H23 H27 H24 HSL HLEN HNE HSH HWR Hpp16 Happ Hpphi HR1 HR2 HF HL HL8 Hsz Hkk Hcnt Hne.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof YM05.alloc_ceiling_val as Hceil.
destruct (wpp_zone pp Hpp16 Happ Hpphi) as (Hpplo & HshB & HshB2 & Hz).
pose proof (Model.pad8_bound sz) as Hpad.
set (E := Ereg regs (wext F L 0 0 0 sz 1 kk cnt ne)).
assert (HAE : env_agree 32 (Ereg regs (wext F L 0 0 0 sz 1 kk cnt ne)) E) by apply env_agree_refl.
destruct (wext_ew regs F L 0 0 0 sz 1 kk cnt ne) as (X32 & X33 & _ & _ & _ & X37 & X38 & X39 & X40 & X41).
fold E in X32, X33, X37, X38, X39, X40, X41.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; exact (ew_Ereg_nat regs _ n r Hn)).
assert (Hpp8 : pp mod 8 = 0) by (apply wmod16_8; exact Hpp16).
assert (Hsh4 : shadow_addr (pp + 0x4000) = shadow_addr pp + 2048) by (rewrite wshadow_pp_L by (try lia; reflexivity); reflexivity).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = shadow_addr pp + 2048) by (rewrite (EE 20%nat 20%bv eq_refl), H20, Hsh4; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = pp + 0x4000) by (rewrite (EE 21%nat 21%bv eq_refl), H21; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (rewrite (EE 23%nat 23%bv eq_refl), H23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite (EE 27%nat 27%bv eq_refl), H27; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = Model.pad8 sz) by (rewrite (EE 24%nat 24%bv eq_refl), H24; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E A_F) = F) by (rewrite X32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E A_L) = L) by (rewrite X33; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E A_SZ) = sz) by (rewrite X37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E A_FS) = 1) by (rewrite X38; apply unsigned_lit_small; lia).
assert (U39 : bv_unsigned (ew E A_KK) = kk) by (rewrite X39; apply unsigned_lit_small; lia).
assert (U40 : bv_unsigned (ew E A_CNT) = cnt) by (rewrite X40; apply unsigned_lit_small; lia).
assert (U41 : bv_unsigned (ew E A_NE) = ne) by (rewrite X41; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E ssC1 (restrict (w_H W) (mkst regs (Z_to_bv 64 W_C) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ssC1. apply (entry_st_ok_full rsegs). all: fold E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; [ | | | | apply Forall_nil].
    + apply (rok_slots E _ mem R F pp 1 kk cnt U9 U27 U32 U38 U39 U40 HSL); lia.
    + apply (rok_len E _ mem pp _ (L + 8 + sz) U21); [ | exact HLEN | lia | | lia | lia].
      * unfold len_C. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
        rewrite (wU_off E A_L 8 L U33), (wU_off0 E A_SZ sz U37) by lia.
        apply zcanon_id. unfold M64. lia.
      * intros i Hi. replace (pp + 0x4000 + i) with (pp + (0x4000 + i)) by lia. apply HWR. lia.
    + apply (rok_sh4 E _ mem pp U20 HSH); lia.
    + apply (rok_ne E _ mem pp ne U27 U41 HNE); [lia | | lia | lia].
      intros i Hi. replace (pp + 0x4d14 + i) with (pp + (0x4d14 + i)) by lia. apply HWR. lia.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val r_slots r_lenv r_sh4 r_ne].
    rewrite U9, U21, U20, U27. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct Hz as [Hz|Hz]; repeat split; lia.
  - split; [|split].
    + cbn [f_atoms fC atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U27, U33, U37, U24, U38, U39, U40, U41.
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      repeat split; lia.
    + exact I.
    + cbn [f_alias alias_ok]. split; [| exact I]. apply (w_al_ne_ok E pp U27 U23 U20 Hpp8); lia. }
unfold cfg_at. change (w64 W_C) with (Z_to_bv 64 W_C).
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
    let rl := eval vm_compute in (nth 1 (ss_mem ssf) (YP09.mkRegion None 0 0 0 0 [])) in
    let rn := eval vm_compute in (nth 3 (ss_mem ssf) (YP09.mkRegion None 0 0 0 0 [])) in
    assert (Inl : In rl (ss_mem ssf)) by (vm_compute; repeat (first [left; reflexivity | right]));
    assert (Inn : In rn (ss_mem ssf)) by (vm_compute; repeat (first [left; reflexivity | right]))
  end.
  pose proof (fun c Hc => w_chunk_of _ _ _ _ c HSf Inl Hc) as CL.
  pose proof (fun c Hc => w_chunk_of _ _ _ _ c HSf Inn Hc) as CN.
  cbn [YP09.r_chunks YP09.r_base base_val ms_mem restrict] in CL, CN. rewrite U21 in CL. rewrite U27 in CN.
  assert (Q24 : bv_unsigned (ew E 24) = Model.pad8 sz) by exact U24.
  assert (Q33 : bv_unsigned (ew E 33) = L) by exact U33.
  assert (Q37 : bv_unsigned (ew E 37) = sz) by exact U37.
  assert (Q41 : bv_unsigned (ew E 41) = ne) by exact U41.
  split; [reflexivity|].
  split; [exact HJf|].
  split; [apply HPgSteps.same_io_wvb|].
  split; [wreg HSf (1%bv : bv 5); reflexivity|].
  split; [wreg HSf (10%bv : bv 5); rewrite denot_lit_U; unfold w64; f_equal;
          rewrite U_SAlu, U_SMd, U_SLit; cbn [zalu_raw zmd_raw]; rewrite (wU_off E 27 16404 pp U27), (wU_off0 E 41 ne Q41) by lia;
          rewrite (zcanon_id 104) by (unfold M64; lia); rewrite (zcanon_id (ne * 104)) by (unfold M64; lia);
          rewrite zcanon_id by (unfold M64; lia); lia|].
  split; [wreg HSf (11%bv : bv 5); cbn [sv_denot]; rewrite (U32 : bv_unsigned (ew E 32) = F); reflexivity|].
  split; [wreg HSf (12%bv : bv 5); reflexivity|].
  split; [intros r Hr; exact (regs_kept_of_st_ok rsegs E _ _ regs _ wkeep HSf HAE ltac:(vm_compute; reflexivity) r Hr)|].
  split.
  { pose proof (CL _ ltac:(cbn; left; reflexivity)) as C0. apply w_chunk8 in C0. rewrite Z.add_0_r in C0.
    replace (L + 8 + sz + Model.pad8 sz) with (U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 24 8) (SOff 33 0)) (SOff 37 0))); [exact C0|].
    rewrite !U_SAlu. cbn [zalu_raw]. rewrite (wU_off E 24 8 _ Q24), (wU_off0 E 33 L Q33), (wU_off0 E 37 sz Q37) by lia.
    rewrite (zcanon_id (Model.pad8 sz + 8 + L)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
  split.
  { pose proof (CN _ ltac:(cbn; left; reflexivity)) as C0. apply w_chunk4v in C0.
    replace (ne + 1) with (U E (SOff 41 1)); [exact C0|]. apply (wU_off E 41 1 ne Q41). lia. }
  intros a Ha H1 H2. apply aview_eq_of. apply HFrf. rewrite unsigned_lit_small by exact Ha.
  intros (r & Hr & Hw). unfold ssC1 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_slots r_lenv r_sh4 r_ne] in Hw; try lia.
Qed.
End w.
