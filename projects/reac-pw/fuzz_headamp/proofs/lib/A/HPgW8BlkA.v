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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW8Kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws rsegs B := YG0q.AR_laws_ok rsegs B.

(* ============================== run A: 0x8237c to the body's memcpy ============================== *)
Definition wkeep : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv.
Lemma w_blkA : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W regs mem md k (R F pp L ty sz fs kk cnt : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem md k ->
In (pp, Layout.PP_SIZE) (ablocks B ly2 S2) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
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
SRr rsegs W (cfg_at rsegs W_J regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
 c' = mkCfg (mkst regs' (Z_to_bv 64 W_MEMCPY) mem' (seg_rom rsegs)) md' /\
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem' md' k /\ same_io md md' /\
 getr regs' 1 = w64 0x824c4 /\ getr regs' 10 = w64 (pp + L + 8) /\ getr regs' 11 = w64 (F + 0xf8) /\
 getr regs' 12 = w64 sz /\ getr regs' 24 = w64 sz /\
 (forall r, In r wkeep -> getr regs' r = getr regs r) /\
 val_mem rsegs (mrestrict (w_H W) mem') (pp + 0x4000) 8 (L + 8) /\
 val_mem rsegs (mrestrict (w_H W) mem') (pp + L) 4 sz /\
 val_mem rsegs (mrestrict (w_H W) mem') (pp + L + 4) 4 ty /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (pp + L <= a < pp + L + 8) -> ~ (pp + 0x4000 <= a < pp + 0x4000 + 8) ->
  aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W regs mem md k R F pp L ty sz fs kk cnt
HJ Hin Hfr H9 H20 H21 H23 H27 HSL HTY HSZ HLEN HSH HWR Hpp16 Happ HFapp HpF Hpphi HFhi HR1 HR2 HL HL8 Hty Hsz Hfs Hkk Hcnt.
pose proof (wA_entry W regs mem R F pp L ty sz fs kk cnt H9 H20 H21 H23 H27 HSL HTY HSZ HLEN HSH HWR
  Hpp16 Happ HFapp HpF Hpphi HFhi HR1 HR2 HL HL8 Hty Hsz Hfs Hkk Hcnt) as HS.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof YM05.alloc_ceiling_val as Hceil.
set (E := Ereg regs (wext F L (pp + L) (shadow_addr (pp + L)) ty sz fs kk cnt 0)) in HS.
assert (HAE : env_agree 32 (Ereg regs (wext F L (pp + L) (shadow_addr (pp + L)) ty sz fs kk cnt 0)) E) by apply env_agree_refl.
destruct (wext_ew regs F L (pp + L) (shadow_addr (pp + L)) ty sz fs kk cnt 0) as (X32 & X33 & X34 & X35 & X36 & X37 & X38 & X39 & X40 & _).
fold E in X32, X33, X34, X35, X36, X37, X38, X39, X40.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; exact (ew_Ereg_nat regs _ n r Hn)).
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happ, HFapp.
assert (U21 : bv_unsigned (ew E 21) = pp + 0x4000) by (rewrite (EE 21%nat 21%bv eq_refl), H21; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E A_L) = L) by (rewrite X33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E A_Q) = pp + L) by (rewrite X34; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E A_TY) = ty) by (rewrite X36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E A_SZ) = sz) by (rewrite X37; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E A_F) = F) by (rewrite X32; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 W_J) with (Z_to_bv 64 W_J).
aj_run wtbl_ok HS HJ.
- (* the two write windows lie in the fresh block pp *)
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?ow =>
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
  pose proof (U_range E (SLit 0)) as _.
  (* the final buffer bytes and the length cell *)
  lazymatch type of HSf with st_ok _ _ ?ssf ?msf =>
    let rb := eval vm_compute in (nth 3 (ss_mem ssf) (YP09.mkRegion None 0 0 0 0 [])) in
    let rl := eval vm_compute in (nth 2 (ss_mem ssf) (YP09.mkRegion None 0 0 0 0 [])) in
    assert (Inb : In rb (ss_mem ssf)) by (vm_compute; repeat (first [left; reflexivity | right]));
    assert (Inl : In rl (ss_mem ssf)) by (vm_compute; repeat (first [left; reflexivity | right]))
  end.
  pose proof (fun c Hc => w_chunk_of _ _ _ _ c HSf Inb Hc) as CB. pose proof (fun c Hc => w_chunk_of _ _ _ _ c HSf Inl Hc) as CL.
  cbn [YP09.r_chunks YP09.r_base base_val ms_mem restrict] in CB, CL.
  rewrite (U34 : bv_unsigned (ew E 34) = pp + L) in CB. rewrite U21 in CL.
  split; [reflexivity|].
  split; [exact HJf|].
  split; [apply HPgSteps.same_io_wvb|].
  split; [wreg HSf (1%bv : bv 5); reflexivity|].
  split; [wreg HSf (10%bv : bv 5); cbn [sv_denot]; rewrite (U34 : bv_unsigned (ew E 34) = pp + L); reflexivity|].
  split; [wreg HSf (11%bv : bv 5); cbn [sv_denot]; rewrite (U32 : bv_unsigned (ew E 32) = F); reflexivity|].
  split; [wreg HSf (12%bv : bv 5); cbn [sv_denot]; rewrite (U37 : bv_unsigned (ew E 37) = sz), Z.add_0_r; reflexivity|].
  split; [wreg HSf (24%bv : bv 5); cbn [sv_denot]; rewrite (U37 : bv_unsigned (ew E 37) = sz), Z.add_0_r; reflexivity|].
  split; [intros r Hr; exact (regs_kept_of_st_ok rsegs E _ _ regs _ wkeep HSf HAE ltac:(vm_compute; reflexivity) r Hr)|].
  assert (Q37 : bv_unsigned (ew E 37) = sz) by exact U37.
  assert (Q36 : bv_unsigned (ew E 36) = ty) by exact U36.
  assert (Q33 : bv_unsigned (ew E 33) = L) by exact U33.
  split.
  { pose proof (CL _ ltac:(cbn; left; reflexivity)) as C0. apply w_chunk8 in C0. rewrite Z.add_0_r in C0.
    rewrite (wU_off E 33 8 L Q33) in C0 by lia. exact C0. }
  split.
  { assert (Usz : U E (SOff 37 0) = sz) by (apply wU_off0; [exact Q37 | lia]).
    pose proof (w_chunk1 _ _ _ _ _ (CB (YP09.mkChunk 0 (CVal 1 (SOff 37 0))) ltac:(cbn; tauto))) as B0.
    pose proof (w_chunk1 _ _ _ _ _ (CB (YP09.mkChunk 1 (CVal 1 (SAlu ALU_SRL (SOff 37 0) (SLit 8)))) ltac:(cbn; tauto))) as B1.
    pose proof (w_chunk1 _ _ _ _ _ (CB (YP09.mkChunk 2 (CVal 1 (SAlu ALU_SRL (SOff 37 0) (SLit 16)))) ltac:(cbn; tauto))) as B2.
    pose proof (w_chunk1 _ _ _ _ _ (CB (YP09.mkChunk 3 (CVal 1 (SAlu ALU_SRL (SOff 37 0) (SLit 24)))) ltac:(cbn; tauto))) as B3.
    rewrite Z.add_0_r in B0. rewrite !wU_srl, Usz in B1, B2, B3 by lia.
    apply (w_val4 _ _ _ _ _ _ _ B0 B1 B2 B3); rewrite ?Usz, ?Z.shiftr_0_r; reflexivity. }
  split.
  { assert (Uty : U E (SExt true 32 (SOff 36 0)) mod 2 ^ 32 = ty mod 2 ^ 32)
      by (rewrite wU_sext; f_equal; apply wU_off0; [exact Q36 | lia]).
    pose proof (w_chunk1 _ _ _ _ _ (CB (YP09.mkChunk 4 (CVal 1 (SExt true 32 (SOff 36 0)))) ltac:(cbn; tauto))) as B0.
    pose proof (w_chunk1 _ _ _ _ _ (CB (YP09.mkChunk 5 (CVal 1 (SAlu ALU_SRL (SExt true 32 (SOff 36 0)) (SLit 8)))) ltac:(cbn; tauto))) as B1.
    pose proof (w_chunk1 _ _ _ _ _ (CB (YP09.mkChunk 6 (CVal 1 (SAlu ALU_SRL (SExt true 32 (SOff 36 0)) (SLit 16)))) ltac:(cbn; tauto))) as B2.
    pose proof (w_chunk1 _ _ _ _ _ (CB (YP09.mkChunk 7 (CVal 1 (SAlu ALU_SRL (SExt true 32 (SOff 36 0)) (SLit 24)))) ltac:(cbn; tauto))) as B3.
    rewrite !wU_srl in B1, B2, B3 by lia.
    replace (pp + L + 4) with (pp + L + 4 + 0) in B0 by lia.
    replace (pp + L + 5) with (pp + L + 4 + 1) in B1 by lia.
    replace (pp + L + 6) with (pp + L + 4 + 2) in B2 by lia.
    replace (pp + L + 7) with (pp + L + 4 + 3) in B3 by lia.
    rewrite Z.add_0_r in B0.
    apply (w_val4 _ _ _ _ _ _ _ B0 B1 B2 B3);
      [rewrite <- (Z.shiftr_0_r (U E (SExt true 32 (SOff 36 0)))) | | |]; apply wbyte_sh; lia. }
  intros a Ha H1 H2. apply aview_eq_of. apply HFrf. rewrite unsigned_lit_small by exact Ha.
  intros (r & Hr & Hw). unfold ssA, rsA in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_slots r_e r_len r_buf r_shq r_sh4] in Hw;
  try lia.
Qed.
End w.
