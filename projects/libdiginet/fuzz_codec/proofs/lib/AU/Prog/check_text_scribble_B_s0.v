(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgMain0.v at 6ebe35ba632 (the harness entry
   segment: the save area, sp1, the call of the side stack for frames, the frame facts, the frame and shadow regions,
   the header and shadow writes, the hand-off) made the first segment of reac_box_pin_parse on reac-pw/fuzz_pin's
   image A (fuzz_pin.asan, sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16): 0x80b44 -> the
   cut P1 at 0x80c4c (lib/A/PPgParseCx.v ss_P1). rule 24: no function proved (a segment of the walk).

   What changed against the donor, each read from the neutral excerpt of 0x80b44-0x80c48:
   - the function is a callee: the start is the contract's premises (PPgParseCx.v pp_pre, the caller's journal of
     pin_pre_kit) and the entry state ss_pp0 (pp_entry), not afn_pre / ajournal_init; every write of the walk is
     allowed by that journal (the save area lies in [sp0 - STK, sp0), the frame is in the journal's own list
     after the call).
   - 160-byte save area (`addi sp,sp,-0xa0` 0x80b44, `sd zero,0(sp)` at sp-160, ra .. s11 at sp-8 .. sp-104),
     `andi sp,sp,-0x20` at 0x80b84: sp1 = 32 * ((sp - 160) / 32) in [sp - 176, sp - 160] (donor: 192 / 208);
     the stack region is trimmed to the saves [-104, 0) (donor :228-234) and region 70 = [sp1+8, sp1+56) holds the
     spill of F at sp1+0x30 (donor :235-246 [16, 88)).
   - the GOT loads at 0x80b94-0x80ba8 (0x990a8 -> 0xa1600, the option word 1; 0x99050 -> 0xa15f8, SB into s3),
     `beqz a2` at 0x80bb0 decided by the option word, `li a0,0x40` and `jal 0x3c8e4` at 0x80bb4 / 0x80bb8 (RA
     0x80bbc): the class-0 call through aj_stack_malloc_atS with ASM0, its premises the call-site lemma
     pin_fs0_site below (count_cid 0 (frames Sc) < fs_frames 0 is the contract's premise).
   - the class-0 frame: 64 bytes, 8 shadow bytes, the flag pointer at F + 56 (donor class 1: 128 / 16 / F + 120).
   - 0x80bbc-0x80c48: `bnez s2` at 0x80bcc decided by HPTR 5 on F (the probe loop 0x80bd0-0x80be8 is not reached),
     `sd s11,0x30(s1)`, the header words F+0 = 0x41B58AB3, F+8 = 0x10add, F+16 = 0x80b44, s4 = SB + F/8, the 8
     shadow bytes f1 f1 f1 f1 f8 f3 f3 f3, a3 = -1; the run stops at 0x80c4c (the donor's size split has no
     counterpart here).
   - the hand-off is the continuation pp_from ss_P1 INV_P1 (PPgParseCx.v): the frame's shadow region made
     read-only, the four cell regions dropped, and the kept-memory fact (lib/Reusable/YCbq.v acall_kept, the
     form of proofs/libreac/fuzz_grant/lib/A/Prog/CtrlParse.v at 6ebe35ba632) carried from the entry memory
     through every step (lib/A/PPgParseLib.v pz_kept_refl / pz_kept_run / pz_kept_trans / pz_kept_own). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgParse0.v, with its module paths and module names changed; 211 of its 246 lines of code are new or changed and 358 lines of the source are left out. *)
(* Segment S0 of check_text_scribble's walk in image B (fuzz_codec.asan-ubsan 0x83dbc): bs_seg_S0 of
   check_text_scribble_B_inv.v, from part a (check_text_scribble_B_s0a.v: entry -> the frame request's return) and
   the part here, 0x83e30 .. the text loop's head 0x83ed4:
   s2 = s8 = F (bnez s2 at 0x83e40 is taken: F >= 4096, so the real-stack fallback 0x83e44 .. 0x83e5c is not
   reached); a1 = 0, s10 = 0; 24(s1) := F; s6 = F + 32; the frame header F[0] = 0x41b58ab3, F[8] = 0x16f70,
   F[16] = 0x83dbc; s9 = SB + F / 8; the frame's eight shadow bytes f1 x4 | 00 | f3 x3; a3 = ~q, a2 = ~(F + 32),
   a4 = 46, a5 = 8: one plain run from a state built at 0x83e30 (atoms 33 = FL, 34 = SB + F / 8; the frame, its
   shadow and the spill slot), then the loop head's boundary with i = o = 0. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_s0a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the complement of an atom plus an offset *)
Lemma bs_den_not : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff n c) (SLit (-1))) = w64 (bnot (v + c)).
Proof.
intros E n v c Hn Hv Hc. rewrite denot_lit_U. unfold w64, bnot. f_equal. exact (U_not_off E n v c Hn Hv Hc).
Qed.
(* one byte of a region from a literal 1-byte chunk *)
Lemma bs_fld_lit1 : forall E m n bse cs lo hi wlo whi od z v,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = bse ->
  In (YP09.mkChunk od (CVal 1 (SLit z))) cs -> z mod 2 ^ 64 mod 256 = v ->
  val_mem tfibsegs m (bse + od) 1 v.
Proof.
intros E m n bse cs lo hi wlo whi od z v Hr Hb Hc Hv.
pose proof (field_of_region_any E m n bse cs lo hi wlo whi od 1 (SLit z) Hr Hb Hc ltac:(lia)) as H.
cbn [sv_denot N.to_nat Pos.to_nat] in H. rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H.
change (bv_modulus 64) with (2 ^ 64) in H. change (2 ^ (8 * Z.of_N 1)) with 256 in H. rewrite Hv in H. exact H.
Qed.
(* a register of a stopped state as the denotation of its symbolic value, unsimplified *)
Ltac bs_rreg0 HS r H :=
lazymatch type of HS with st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = sv_denot Ex e) by exact (st_ok_restrict_reg segs Hh Ex ss ms r HS) end.

(* the state at 0x83e30: s7 = SB (atom 32), the frame at atom 10 (a0 = F) with the flag address (atom 33) at
   F + 56, the frame's shadow at atom 34, the spill slot 24(s1) *)
Definition bs_rs2 : smem :=
  [cw_frame_region 10 33 0; cw_fshadow_region 34 0; YP09.mkRegion (Some 9%nat) 24 32 24 32 []].
Definition bs_G2 : facts :=
  mkFacts [(10%nat, HPTR 6); (33%nat, HPTR 0); (34%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3);
           (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB SB 0)] []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0), SOff 34 0)].

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : YCbq.frame_flag_lawP tfibsegs B.
Hypothesis SMP : stack_malloc_progressP B.

Lemma bs_s0_p2 : forall g W2 c2, bs_pre B g -> bs_s0_r1 B g W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => exists pos, bs_cut B MT g pos PC_L (P_L g pos (S (Z.to_nat (bs_n g)))) W3 c3).
Proof.
intros [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb cj] W2 c2 Hpre Hr1.
unfold bs_pre in Hpre.
unfold bs_s0_r1, bs_s0_j, bs_saves, bs_sp, bs_sp1, bs_F, bs_FL, bs_wr, bs_len in *.
cbn [bs_STK bs_sp0 bs_FP bs_ly bs_S bs_W0 bs_mem0 bs_md0 bs_own bs_lyc bs_Sc bs_W bs_memc bs_mdc bs_k bs_regs
  bs_q bs_ch bs_n bs_tb bs_cj] in Hpre, Hr1 |- *.
destruct Hpre as (HE & H10 & Hstr & Hoq & Hoch & H11 & Hch & Hcj & Hcjl & H12 & Hn & Hdisj & Howe & Hfr8).
destruct Hr1 as (-> & S2 & regs2 & mem2 & md2 & pos & -> & (HJ2 & HK2 & Eab & Hfrs2 & Hnin & HSf & Hio & Hflag &
  V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26) & Hz & R10 & R2 & R9 & R8 & R3 & R4 &
  R19 & R20 & R21 & R23 & R27).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_check_text_scribble HE
  ltac:(unfold TB_check_text_scribble, ESTACK; lia)) as (Hceil & H47 & H46 & Hal & Hpres).
pose proof HE as (HJc & Hra & Hra4 & Hgp & Htp & _ & Hwlo & Hwhi & Hev & Hlive).
pose proof HJc as (HARc & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (TT : TB_check_text_scribble = 8352) by reflexivity. rewrite TT in *.
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & (Hsp0al & _) & _).
assert (Hin : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 0 pos HAR2 Hin) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 tfibsegs B _ _ _ _ _ 0 pos HAR2 Hin) as (HF64 & _ & _).
destruct (FFL _ _ _ _ _ 0 pos HAR2 Hin) as (_ & _ & _ & (HFL4096 & _ & HFLc)).
change (fs_frame_bytes 0) with 64 in HFceil, HFapp.
set (F := frame_addr lyc 0 pos) in *. set (FL := flag_addr lyc 0 pos) in *.
set (sp1 := 32 * ((spZ regs - 128) / 32)) in *.
destruct (sp1_facts (spZ regs - 128) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by lia. clear Hsp1r.
assert (HF0 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HF8 : F / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
pose proof Hstr as (Hq0 & _ & Hin0 & (_ & Hqn & _ & _ & _ & Hqam & Hqwin)).
(* the start state *)
set (E := Ereg regs2 (cw_extra [FL; SB + F / 8])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 FL) by (subst E; exact (cw_ew_x regs2 [FL; SB + F / 8] 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (SB + F / 8)) by (subst E; exact (cw_ew_x regs2 [FL; SB + F / 8] 1)).
assert (E10 : ew E 10 = Z_to_bv 64 F) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = Z_to_bv 64 q) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (U10 : bv_unsigned (ew E 10) = F) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = SB + F / 8) by (rewrite E34; apply unsigned_lit_small; unfold SB; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs2 (cw_extra [FL; SB + F / 8])) E) by (subst E; apply env_agree_refl).
assert (HS : st_ok tfibsegs E (mkSS 0x83e30 (sr_set sr_atoms 23%bv (SOff 32 0)) bs_rs2 None bs_G2)
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x83e30) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs2 (cw_extra [FL; SB + F / 8])) with E.
  - apply regs_ok_pin; [subst E; apply regs_ok_Ereg | intros Hx; discriminate Hx |].
    rewrite R23. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - vm_compute. reflexivity.
  - unfold bs_rs2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (cw_frame_region_ok B LAWS FFL _ 10 33 lyc S2 W mem2 md2 0 pos HAR2 Hin E10 E33).
      change (fs_frame_bytes 0) with 64. fold F FL. replace (F + 64 - 8) with (F + 56) by lia. exact Hflag.
    + apply (cw_fshadow_region_ok B LAWS _ 34 lyc S2 W mem2 md2 0 pos HAR2 Hin E34).
      change (fs_frame_bytes 0) with 64. exact Hz.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable tfibsegs). apply HJpres2. lia.
  - apply pairwise_disjoint_of_extents. unfold bs_rs2, cw_frame_region, cw_fshadow_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (fs_frame_bytes 0) with 64. change (64 / 8) with 8.
    rewrite U10, U34, U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, SB in *. repeat split; lia.
  - split; [|split; [exact I|]].
    + destruct (cw_frame_afacts B LAWS E 10 33 34 lyc S2 W mem2 md2 0 pos FFL HAR2 Hin E10 E33 E34) as (A10 & A33 & A34).
      unfold bs_G2. cbn [f_atoms atoms_ok]. split; [exact A10|]. split; [exact A33|]. split; [exact A34|].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U9, E32, unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
      split; [split; [lia|]; split; [exact Hsp1al | lia]|]. split; [split; [lia|]; split; [exact Hsp1al | lia]|].
      split; [split; [unfold SB; lia|]; split; [reflexivity | lia]|]. exact I.
    + unfold bs_G2. cbn [f_alias alias_ok]. split; [|exact I].
      exact (shadow_decl_ok E 10%nat 32%nat 34%nat F SB E10 ltac:(lia) E32 E34). }
clearbody E.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) mem2)) by constructor.
(* 0x83e30 .. the loop head 0x83ed4: one plain run *)
aj_run_to tfibtbl_lib_ok HS HJ2 0x83ed4.
{ lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyv ?ownv =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk s0 fp b0 bc lyv ownv) end.
  repeat first
  [ apply awr_ok_nil
  | eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 0 pos 10%nat);
      [reflexivity | exact U10 | left; reflexivity | cbn; lia | cbn; change (fs_frame_bytes 0) with 64; lia |]
  | eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 0 pos 34%nat);
      [reflexivity | rewrite U34; reflexivity | left; reflexivity | cbn; lia | cbn; change (fs_frame_bytes 0 / 8) with 8; lia |]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0)); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |] ]. }
assert (HP2 : Permutation (ablocks B lyc S2) (ablocks B lyc Sc)) by (rewrite Eab; apply Permutation_refl).
(* what the run kept: only the frame, its shadow and the spill slot 24(s1) changed *)
set (Xb := fun a => (F <= a < F + 64) \/ (SB + F / 8 <= a < SB + F / 8 + 8) \/ (sp1 + 24 <= a < sp1 + 32)).
lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
  assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ Xb a -> aview tfibsegs H m2 a = aview tfibsegs H m1 a);
  [ intros a Ha Hx; apply (bs_kept_of_frame Ef rs H m1 m2 HFr a Ha); intros (r & Hr & Hb); apply Hx; unfold Xb;
    lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
    repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U10, ?U34, ?U9 in Hb; lia | ]);
    destruct Hr
  | ];
  assert (KP : forall a, apresent H m1 a -> apresent H m2 a) by (intros a Hp; exact (apresent_grows _ _ _ a HG Hp));
  clear HFr HG
end.
clear_frames.
assert (HK3 : tcj_kept tfibsegs B 8352 lyc Sc W memc W (ms_mem ms) (spZ regs) (fun a => ch <= a < ch + 24)).
{ apply (cw_kept_step B LAWS 8352 lyc Sc W memc mdc W mem2 (ms_mem ms) (spZ regs) _ Xb ltac:(lia) HARc HK2 KX); [|exact KP].
  intros a Ha. unfold Xb in Ha. destruct Ha as [Ha | [Ha | Ha]]; [right; right | right; right | left; lia].
  - apply (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc S2 W (ms_mem ms) _ k 0 pos a
      HJc HJ2 HP2). left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. lia.
  - apply (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc S2 W (ms_mem ms) _ k 0 pos a
      HJc HJ2 HP2). right; left. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8.
    fold F. unfold SB in Ha. lia. }
assert (KV : forall a nb v, 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat nb -> ~ Xb x) ->
   val_mem tfibsegs (mrestrict (w_H W) mem2) a nb v -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) a nb v).
{ intros a nb v H0 H1 H2 Hv. apply (cw_val_mem_kept (w_H W) (w_H W) mem2 (ms_mem ms) a nb v); [|exact Hv].
  intros x Hx. apply KX; [lia | exact (H2 x Hx)]. }
(* the frame's shadow and the flag word at the loop head *)
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as RGF. pose proof (st_ok_region_nth E _ _ 1 _ HS eq_refl) as RGS.
cbn [ms_mem restrict] in RGF, RGS.
lazymatch type of RGF with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RGF end.
lazymatch type of RGS with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RGS end.
assert (GSH : garr8 tfibsegs (mrestrict (w_H W) (ms_mem ms)) (SB + F / 8) BS_FRAME_SHADOW).
{ intros j Hj. cbn [length BS_FRAME_SHADOW] in Hj.
  do 8 (destruct j as [|j]; [split; [eapply (bs_fld_lit1 E _ 34 _ _ _ _ _ _ _ _ _ RGS U34); [bs_in | reflexivity]
                                      | cbn [nth BS_FRAME_SHADOW]; lia] |]); lia. }
assert (VFL : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (F + 56) 8 FL).
{ eapply (bs_fld E _ 10 _ _ _ _ _ _ 56 8%N 33%nat FL RGF U10); [bs_in | exact E33 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia]. }
clear RGF RGS.
(* the registers at the loop head *)
bs_rreg0 HS (2%bv : bv 5) G2. bs_rreg0 HS (3%bv : bv 5) G3. bs_rreg0 HS (4%bv : bv 5) G4. bs_rreg0 HS (8%bv : bv 5) G8.
bs_rreg0 HS (9%bv : bv 5) G9. bs_rreg0 HS (11%bv : bv 5) G11. bs_rreg0 HS (12%bv : bv 5) G12. bs_rreg0 HS (13%bv : bv 5) G13.
bs_rreg0 HS (14%bv : bv 5) G14. bs_rreg0 HS (15%bv : bv 5) G15. bs_rreg0 HS (18%bv : bv 5) G18. bs_rreg0 HS (19%bv : bv 5) G19.
bs_rreg0 HS (20%bv : bv 5) G20. bs_rreg0 HS (21%bv : bv 5) G21. bs_rreg0 HS (22%bv : bv 5) G22. bs_rreg0 HS (23%bv : bv 5) G23.
bs_rreg0 HS (24%bv : bv 5) G24. bs_rreg0 HS (25%bv : bv 5) G25. bs_rreg0 HS (26%bv : bv 5) G26.
bs_rreg0 HS (27%bv : bv 5) G27.
destruct (cw_frame_start MT MTL MTF B lyc Sc S2 HSf) as (_ & HMO).
apply SRr_ret. exists pos.
unfold bs_cut, P_L, bs_common, bs_rest, bs_owe, bs_sp, bs_sp1, bs_F, bs_FL, bs_wr, bs_len.
cbn [bs_STK bs_sp0 bs_FP bs_ly bs_S bs_W0 bs_mem0 bs_md0 bs_own bs_lyc bs_Sc bs_W bs_memc bs_mdc bs_k bs_regs
  bs_q bs_ch bs_n bs_tb bs_cj].
fold F FL sp1. rewrite TT.
exists lyc, S2, (ms_regs ms), (ms_mem ms); eexists.
split; [rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) at 1; reflexivity|].
split; [exact HJ2|].
split; [exact HK3|]. split; [exact HP2|]. split; [exact Hnin|].
split; [eapply same_io_trans; [exact Hio | apply cw_same_io_wvb]|].
split; [exact HMO|].
split.
{ split; [rewrite G8, sv_denot_SOff0, (EE 8%nat 8%bv eq_refl); exact R8|].
  split; [rewrite G2, sv_denot_SOff0; exact E2|].
  split; [rewrite G9, sv_denot_SOff0; exact E9|].
  split; [rewrite G3, sv_denot_SOff0, (EE 3%nat 3%bv eq_refl); exact R3|].
  split; [rewrite G4, sv_denot_SOff0, (EE 4%nat 4%bv eq_refl); exact R4|].
  split; [rewrite G18, sv_denot_SOff0; exact E10|].
  split; [rewrite G24, sv_denot_SOff0; exact E10|].
  split; [rewrite G22; cbn [sv_denot]; rewrite U10; reflexivity|].
  split; [rewrite G23, sv_denot_SOff0; exact E32|].
  split; [rewrite G25; first
    [ rewrite sv_denot_SOff0; exact E34
    | rewrite (denot_shx E 10 32 0 F SB E10 E32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)), Z.add_0_r;
      reflexivity ]|].
  split; [rewrite G19, sv_denot_SOff0, (EE 19%nat 19%bv eq_refl); exact R19|].
  split; [rewrite G21, sv_denot_SOff0, (EE 21%nat 21%bv eq_refl); exact R21|].
  split; [rewrite G27, sv_denot_SOff0, (EE 27%nat 27%bv eq_refl); exact R27|].
  do 12 (split; [apply KV; [lia | cbn; lia | intros x Hx; unfold Xb, SB; cbn in Hx; lia | assumption]|]).
  split; [apply rdword_of_val_mem; [exact VFL | lia]|].
  exact GSH. }
exists 0, 0, [].
split; [rewrite G11; reflexivity|].
split; [rewrite G26; reflexivity|].
split; [rewrite G12; exact (bs_den_not E 10 F 32 E10 ltac:(lia) ltac:(lia))|].
split; [rewrite G13; replace (bnot q) with (bnot (q + 0)) by (f_equal; lia);
  exact (bs_den_not E 21 q 0 E21 ltac:(lia) ltac:(lia))|].
split; [rewrite G14; reflexivity|].
split; [rewrite G15; reflexivity|].
split; [rewrite G20, sv_denot_SOff0, (EE 20%nat 20%bv eq_refl); exact R20|].
split; [lia|]. split; [lia|]. split; [rewrite Z.sub_0_r; lia|].
split; [constructor|]. split; [reflexivity|].
split; [rewrite Z.sub_0_r; reflexivity|].
split; [rewrite Z.sub_0_r; reflexivity|].
apply garr8_nil.
Qed.

Hypothesis ASM0 : astack_malloc_realizes tfibsegs B 0.
(* S0: entry -> the frame request (part a) -> the text loop's head (above) *)
Theorem bs_s0_holds : bs_seg_S0 B MT.
Proof.
unfold bs_seg_S0. intros g Hpre Hnow.
eapply SRr_bind; [eapply bs_s0_p1; eassumption|]. intros W2 c2 _ H1.
exact (bs_s0_p2 g W2 c2 Hpre H1).
Qed.
End s.
