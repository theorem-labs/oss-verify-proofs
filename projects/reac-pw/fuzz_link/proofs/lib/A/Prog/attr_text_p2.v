(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the tail of pcap_source_open (fuzz_pcap.asan-ubsan 0x811e0, listing offset
   AF_pcap_source_open = 0xa58, 246 instructions) on libreac v1.9.0's ASan+UBSan build: lib/A's PcapSourceOpenB.v, the
   walk from the two semantic cuts of lib/B/Prog/PcapSourceOpenPh.v to the return. op_from_null and op_from_read prove
   `op_from op_gi_null` and `op_from op_gi_read`, i.e. lib/A's image-generic post tpcap_source_open_post (with
   topen_kept, lib/A/Prog/PcapSourceOpenDefs.v) at this image (SEGS = pa_segs, the relro window pa_relro_lo /
   pa_relro_hi of the lib/B PAImg instance PI); PcapSourceOpen.v (the head) composes them. At ossv/recipes 25e3d17bdb50 (2026-10-29), this image had no released
   proof (rule 24, a Theorem Labs lane, 22:35Z); the released v1.8 UBSan proof lib/U/Prog/pcap_source_open.v is the guard
   template only.

   The paths, at this image's pcs:
   - the empty input (cut 0x813f8, f = NULL): a0 := -1, `j 0x81474`, the epilogue without the buffer re-poison;
   - the short read (cut 0x8138c, kr <> 24): `bne a0,s9` to 0x81400, the shadow test of ps (0x81400 `lbu`, 0x81404
     `bnez`), f = ps->f (0x81408), the fclose wrapper's call (0x8140c), the second shadow test (0x81410, 0x81414
     `beqz` to 0x8145c), ps->f := NULL (0x8145c), a0 := -1, the epilogue from 0x81464 (op_fclose);
   - kr = 24: the UBSan guard G6 (below), the magic of the four header bytes F + 32 .. F + 35 (0x81398..0x813c4, the
     top byte through `slliw`, magic_U), then 0xd4c3b2a1 (0x813c8 `beq` to 0x81420: ps->swapped := 1, a0 := 0,
     `j 0x81464`), 0xa1b2c3d4 (0x813d4 `bne` falls to 0x813d8: ps->swapped := 0, a0 := 0, `j 0x81464`), or the bad
     magic (0x81444: as the short read, fclose at 0x81450);
   - the epilogue (op_epi): the buffer out of scope (0x81464..0x81470, 3 shadow bytes 0xf8), the retired magic
     0x45e0360e at F (0x8147c); 0x81480 `beqz s2` NOT taken (s2 = F >= 4096, atom 18's fact), so the machine-frame
     arm 0x814d4..0x81500 is dead; F's 16 shadow bytes 0xf5 (0x81484..0x814c4); the flag through `ld a1,0x78(s2)` and
     `sb zero,0(a1)` (0x814c8, 0x814cc), which gives the frame back (lib/B/Prog/PcapFrame.v aj_flag_store_pi:
     astack_free_law, frame_flag_lawP); the restores and `ret` (0x81504..0x81538).
   The two guards on ps (G5, 0x812f8 and 0x81300 / 0x81304) are before the cuts, in the head.

   THE GUARD G6. 0x81390 `addi a0,zero,-3`, 0x81394 `bgeu s4,a0` branches to the `unimp` at 0x8153c when the header
   buffer s4 = F + 32 lies within 3 bytes of 2^64. The symbolic run decides it, NOT taken: decide_cond2
   (Reusable/YP0e.v:932) maps BC_GEU to the negation of decide_ltu2 (:922), and decide_ltu (Reusable/YP0m.v:673) finds
   atom 20 (s4) below the literal 2^64 - 3 from its range fact [4128, 0x7fffff800020] (rd_facts), which rd_entry
   proves from frames_bounds on the class-1 frame (F + 128 <= alloc_ceiling <= 0x7fffff800000). Templates: the released
   UBSan proof of the v1.8 image, proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v on origin/ossv/recipes
   c8557374ad2e, open_mid :286 (premise bv_unsigned sp0 < 2 ^ 63 at :291, frame bounds :295-299), which decides the
   guard at :410-412; and the earlier walk of this image, on a working branch
   (a8ccd33b1a7) pcap_source_open_tl.v (sha256 4aaa5af08467; internal record) pso_rdchk :36-67 (premise bv_unsigned s4 < 2 ^ 64 - 3 at :44,
   `step; step; if_false` at :65).

   THE REPORT PATHS are proved unreachable; no run steps into one. Every shadow test of ps in this stretch
   (0x81400 / 0x81404 and 0x81410 / 0x81414 on the short read, 0x81444 / 0x81448 and 0x81454 / 0x81458 on the bad
   magic, 0x813e4 / 0x813e8 and 0x8142c / 0x81430 on ps + 8 before the slow checks 0x81570 / 0x81584) is decided by
   the shadow entry of ps (rd_SH: ps's 24 bytes addressable; shent_rd_ok from op_pre's range_addressable, kept to the
   cut by op_mid's topen_kept and across fclose by its journal, shok_transfer), so the token run reads a 0 shadow byte
   and takes the non-report successor: the report calls 0x8141c, 0x81580, 0x81594 and 0x815a0..0x815b4 are never
   reached.

   The callees are Section hypotheses of their exact statement types: the fclose wrapper AFCLOSE, of
   lib/A/Stdio/PFclose.v's image-generic afclose_source_spec (= afclose_source_spec_stk PFCLOSE_STK) at this image,
   bound as lib/B/Prog/PcapSourceClose.v binds it (its data-buffer premise from op_pre's input block); the file meter
   FM (lib/A/Stdio/PSourceMeter.v asrc_file_meter); the frame give-back laws astack_free_law (Reusable/YG0d.v:301) and
   frame_flag_lawP (Reusable/YCbq.v:797) with model_laws; the meter laws (Reusable/YC5d.v ameter_laws,
   ameter_fs_laws); ASIL (lib/A/Stdio/PSourceMeta.v asource_img_laws). The stream predicates' frame lemmas are copied
   from lib/B/Prog/PcapSourceClose.v (not required). getr / mkst / seg_rom come from YK11; nothing from lib/Lib is
   imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpenB.v, with its module paths, module names and numbers changed; 660 of its 725 lines of code are new or changed and 1681 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_entry.v, with its module names changed; 281 of its 315 lines of code are new or changed and 691 lines of the source are left out. *)
(* attr_text on image A (fuzz_link.asan 0x86b18; listing (internal path)
   (internal record, sha256 03340ee12716)), PHASE 2: the text, from the join +0x170 to the join +0x1d4
   (lib/A/Prog/attr_text_base.v explains the phase form).

   +0x170 the instrumented check C1 of n; +0x178 n; +0x188 `bltu n + len, 4097` (the room test of nl_put):
   - no room: +0x18c..+0x1a8 check C2 of full, full := 1, `j` to the join +0x1d4;
   - room: +0x1ac `beqz s3` (len = 0: no copy), else checked_memcpy(w + n, s, len) at +0x1bc (aj_gx_intrin_at over
     AMEMCPY: the destination [w + n, w + n + len) lies in b, inside [w, w + 4096); the source [s, s + len) is the
     Pre's string and NUL, which no step before has written, and its shadow premises are the Pre's); then
     +0x1c0..+0x1d0 C1, n := n + len, and the join +0x1d4.

   Section hypotheses: LAWS : AR_laws pa_segs B (the lib/A frame); AMEMCPY : aintrin_realizes pa_segs B OCpy
   (pa_sigma LS___asan_memcpy), discharged at the image by lib/A/AE2q.v asan_memcpy_realizes (0x52d78).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK0e.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC85G.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkLeaf LinkWalkNlw LinkWalkSide attr_text_c attr_text_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Variables rlo rhi : Z.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis AMEMCPY : aintrin_realizes pa_segs B OCpy (pa_sigma LS___asan_memcpy).
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Theorem at_p2 :
  at_from SK B rlo rhi (fun cx len n f ms md => at_inv SK B cx AT_J3 len n f ms md) ->
  at_from SK B rlo rhi (fun cx len n f ms md => at_inv SK B cx AT_J2 len n f ms md).
Proof.
intros HNEXT cx len n f ms3 md3 HB HI.
pose proof HB as HB0.
destruct HB as (HPRE & HRD & HNLW & HWF & Hs0 & HSTR & HSLEN & HSLACK & HAP & HAPF1 & HAPF2 &
  HMR1 & HRA1 & HHV1 & HMR2 & HRA2 & HHV2).
destruct HPRE as (HJ0 & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside &
  Hajw & Hro).
destruct HI as (HSHAPE & HLIVE & HJ & HFDS & HFS & HFIELDS & HN0 & Hlen0 & Hlen1 & HKEPT).
destruct (at_entry_J SK B rlo rhi cx AT_J2 len n f ms3 HB0 HSHAPE HLIVE HFIELDS HKEPT)
  as (U2 & U9 & HREGS & HS & SHOK).
pose proof HFIELDS as (Hw0 & Hwl & HPRES & HVN & HVF & (Hn0 & Hn1) & (Hf0 & Hf1)).
pose proof HSHAPE as (_ & _ & _ & _ & _ & _ & Hsp3 & HRK3 & _).
pose proof HLIVE as (L8 & L9 & L18 & L19 & L20 & L21 & L22).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (Hceil : alloc_ceiling <= c_sp0 cx - c_STK cx) by (eapply (aj_stk_ceiling SK SEGS B); exact HJ0).
assert (HSPlo : alloc_ceiling + ATTR_TEXT_AK <= c_sp cx) by (unfold c_sp in *; lia).
assert (HSPhi : c_sp cx < 2 ^ 64)
  by (unfold c_sp, spZ; pose proof (u64_range (getr (c_regs cx) 2)); lia).
assert (HAK : ATTR_TEXT_AK = 4160) by reflexivity.
pose proof (at_w_range cx) as Rw. pose proof (at_s_range cx) as Rs.
unfold NL_CHUNK_MAX in Hn1.
assert (Hamr : c_w cx + 4112 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, NW_SIZE in *; lia).
assert (Hsmr : c_s cx + c_slen cx + 1 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
set (E := Eimg (Ereg (ms_regs ms3) (at_extra cx n f))) in *.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall j, (j < 16)%nat -> ew E (32 + j)%nat = nth j (at_extra cx n f) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [at_extra nth Nat.add] in E32, E33, E34.
assert (E9 : ew E 9%nat = w64 (c_w cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 9 9%bv eq_refl); exact L9).
assert (E18 : ew E 18%nat = w64 (c_s cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 18 18%bv eq_refl); exact L18).
assert (E19 : ew E 19%nat = w64 len)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 19 19%bv eq_refl); exact L19).
pose (RUN := paj_run_x SK B LAWS (c_G cx) HGok (c_XO cx) (c_OUT cx)).
pose (RUNTO := paj_run_to_x SK B LAWS (c_G cx) HGok (c_XO cx) (c_OUT cx)).
pose (BR := paj_branch (PI := PI)).
(* +0x170 .. +0x188: C1, n, up to the room test `bltu n + len, 4097` *)
paj_run_to_tok RUNTO HS HJ SHOK at_span AT_J3.
{ unfold at_ssJ, at_fr, at_fl. cbn [ss_mem]. at_awr_tac Hajw. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => c_w cx + 4096 <= a < c_w cx + 4112) HFr
  ltac:(at_frame_tac)) as UN1.
pose proof (at_step_run cx _ _ _ UN1 ltac:(intros a Ha; cbv beta in Ha; unfold NW_SIZE; lia) HG) as ST1.
clear HF HFr HG UN1.
assert (UL : U E (SAlu ALU_ADD (SOff 19 0) (SOff 33 0)) = len + n) by at_U.
psrr_branch_tok RUN BR HS SHOK at_span.
- (* room: n + len < 4097 *)
  rewrite branch_ltu_U, UL, (U_lit E 4097) in Hc by lia. apply Z.ltb_lt in Hc. rename Hc into Hroom.
  paj_run_to_tok RUNTO HS HJ SHOK at_span AT_J3.
  { at_awr_tac Hajw. }
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => c_w cx + 4096 <= a < c_w cx + 4112) HFr
    ltac:(at_frame_tac)) as UN2.
  pose proof (at_step_trans cx _ _ _ ST1
    (at_step_run cx _ _ _ UN2 ltac:(intros a Ha; cbv beta in Ha; unfold NW_SIZE; lia) HG)) as ST2.
  clear HF HFr HG UN2 ST1.
  psrr_branch_tok RUN BR HS SHOK at_span.
  + (* len = 0: no copy; n := n + 0 *)
    rewrite branch_eq_U, (U_atom E 19 len E19 ltac:(lia)), (U_lit E 0) in Hc by lia. apply Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK at_span AT_J3.
    { at_awr_tac Hajw. }
    pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => c_w cx + 4096 <= a < c_w cx + 4112) HFr
      ltac:(at_frame_tac)) as UN3.
    pose proof (at_step_trans cx _ _ _ ST2
      (at_step_run cx _ _ _ UN3 ltac:(intros a Ha; cbv beta in Ha; unfold NW_SIZE; lia) HG)) as ST3.
    clear HF HFr HG UN3 ST2.
    lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      pose proof (at_regs_carry cx n f ms3 E ssx (w_H (c_W cx)) msc AT_LIVE_REGS HREGS (env_agree_refl 48 E) HS
        ltac:(vm_compute; reflexivity)) as HRC;
      pose proof (at_regs_carry cx n f ms3 E ssx (w_H (c_W cx)) msc [19%bv] HREGS (env_agree_refl 48 E) HS
        ltac:(vm_compute; reflexivity) 19%bv (or_introl eq_refl)) as HR19;
      pmkst HS;
      eapply (HNEXT cx len (len + n) f); [exact HB0|];
      eapply (at_inv_of SK B rlo rhi cx AT_J2 len n f ms3 AT_J3 len (len + n) f);
      [ exact HB0 | exact HSHAPE | exact HLIVE | exact HKEPT | exact HFIELDS | exact HRC
      | rewrite HR19; exact L19
      | exact ST3
      | exact HJ
      | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact HFDS
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact HFS
      | eapply (at_val_of_ss E ssx (w_H (c_W cx)) msc 1 9 (c_w cx) 4096 4112 4096 4112 _ 4096 8);
        [ exact HS | reflexivity | exact U9 | cbn [In]; first [left; reflexivity | right; left; reflexivity]
        | apply at_denot; at_U | cbn; lia | cbn; lia ]
      | eapply (at_val_of_ss E ssx (w_H (c_W cx)) msc 1 9 (c_w cx) 4096 4112 4096 4112 _ 4104 4);
        [ exact HS | reflexivity | exact U9 | cbn [In]; first [left; reflexivity | right; left; reflexivity]
        | apply at_denot; at_U | cbn; lia | cbn; lia ]
      | unfold NL_CHUNK_MAX; lia | lia | lia | lia ]
    end.
  + (* len <> 0: checked_memcpy(w + n, s, len) *)
    rewrite branch_eq_U, (U_atom E 19 len E19 ltac:(lia)), (U_lit E 0) in Hc by lia. apply Z.eqb_neq in Hc.
    paj_run_tok RUN HS HJ SHOK at_span.
    { at_awr_tac Hajw. }
    pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => c_w cx + 4096 <= a < c_w cx + 4112) HFr
      ltac:(at_frame_tac)) as UN3.
    pose proof (at_step_trans cx _ _ _ ST2
      (at_step_run cx _ _ _ UN3 ltac:(intros a Ha; cbv beta in Ha; unfold NW_SIZE; lia) HG)) as ST3.
    clear HF HFr HG UN3 ST2.
    lazymatch goal with HS : st_ok _ _ ?ssx (restrict _ ?msc) |- _ =>
      pose proof (at_regs_carry_ok cx n f ms3 E ssx (w_H (c_W cx)) msc AT_LIVE_REGS HREGS (env_agree_refl 48 E)
        HS ltac:(vm_compute; reflexivity)) as HRC
    end.
    pmkst HS.
    prreg HS (1%bv : bv 5) R1.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
      assert (Q3 : getr rg 3 = w64 (as_gp B))
        by (rewrite (HRC 3%bv ltac:(at_inl)), (proj1 HRK3); exact Hgp);
      assert (Q4 : getr rg 4 = w64 (as_tp B))
        by (rewrite (HRC 4%bv ltac:(at_inl)), (proj1 (proj2 HRK3)); exact Htp);
      assert (Qsp : spZ rg = c_sp cx - AT_FRAME)
        by (unfold spZ in Hsp3 |- *; rewrite (HRC 2%bv ltac:(at_inl)); exact Hsp3);
      assert (Q10 : getr rg 10 = w64 (c_w cx + n)) by (at_reg_val HS (10%bv : bv 5); at_U);
      assert (Q11 : getr rg 11 = w64 (c_s cx)) by (at_reg_val HS (11%bv : bv 5); at_U);
      assert (Q12 : getr rg 12 = w64 len) by (at_reg_val HS (12%bv : bv 5); at_U);
      assert (HKT : at_kept cx mm) by exact (at_kept_step cx _ _ HKEPT ST3)
    end.
    eapply SRr_bind.
    { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
        eapply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OCpy (pa_sigma LS___asan_memcpy) AMEMCPY
          (c_G cx) (c_XO cx) (c_OUT cx) (c_W cx) rg mm (c_STK cx) (c_sp0 cx) (c_FP cx)
          (c_ly cx) (c_S cx) (c_W0 cx) (c_mem0 cx) (c_md0 cx) (c_own cx) (c_lyc cx) (c_Sc cx) mdx (c_k cx)
          (c_w cx + n) (c_s cx) len _ HGok HJ Q10 Q11 Q12);
        [ lia | lia | lia
        | rewrite Qsp; unfold c_sp, AT_FRAME;
          replace (spZ (c_regs cx) - 64) with (spZ (c_regs cx) + (-4) * 16) by lia;
          rewrite Z_mod_plus_full; exact Hal16
        | rewrite Qsp; unfold c_sp, AT_FRAME, ESTACK in *; lia
        | rewrite Qsp; unfold c_sp, AT_FRAME in *; lia
        | exact Q3 | exact Q4 | exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
        | intros a Ha;
          destruct (Hajw a (at_E_in cx a ltac:(unfold NW_SIZE; lia))) as [[Haw Hxo] | [HGa | Hox]];
          [ left; split; [exact Haw|]; split; [exact Hxo|]; rewrite Qsp;
            unfold apart_frame, c_w, c_sp, ATTR_TEXT_AK, ATTR_TEXT_AFRAME, ESTACK, AT_FRAME, NW_SIZE in *; lia
          | right; left; split; [exact HGa|];
            apply (writable_kept (segs := SEGS) (w_H (c_W cx)) (ms_mem ms3) mm a (proj2 ST3 a));
            replace a with (c_w cx + (a - c_w cx)) by lia;
            exact (proj2 (HPRES (a - c_w cx) ltac:(unfold NW_SIZE; lia)))
          | right; right; exact Hox ]
        | unfold amem_range in *; unfold NW_SIZE in *; lia
        | eapply (range_addressable_sub _ SHADOW_OFF (c_w cx) NW_SIZE);
          [ exact (at_ra_keep2 SK B rlo rhi cx mm (c_w cx) NW_SIZE HB0 HKT HMR1 (proj1 Rw) HRA1)
          | lia | unfold NW_SIZE; lia ]
        | intros Hpos; eapply (at_hull_sub _ (c_w cx) NW_SIZE);
          [ exact (at_hull_keep SK B rlo rhi cx mm (c_w cx) NW_SIZE HB0 HKT HMR1 (proj1 Rw)
                     ltac:(unfold NW_SIZE; lia) HHV1)
          | lia | lia | unfold NW_SIZE; lia | lia ]
        | split; [lia|]; split; [lia|]; split;
          [ intros a Ha; split;
            [ rewrite (at_str_kept SK B rlo rhi cx mm a HB0 HKT ltac:(lia));
              exact (at_str_vis SK B rlo rhi cx a HB0 ltac:(lia))
            | rewrite Qsp; unfold apart_frame, c_sp, ATTR_TEXT_AK, ATTR_TEXT_AFRAME, ESTACK, AT_FRAME in *; lia ]
          |];
          split; [unfold apart, NW_SIZE in HAP; lia|];
          split; [unfold amem_range in *; lia|];
          split;
          [ eapply (range_addressable_sub _ SHADOW_OFF (c_s cx) (c_slen cx + 1));
            [ exact (at_ra_keep2 SK B rlo rhi cx mm (c_s cx) (c_slen cx + 1) HB0 HKT HMR2 (proj1 Rs) HRA2)
            | lia | lia ]
          | intros Hpos; eapply (at_hull_sub _ (c_s cx) (c_slen cx + 1));
            [ exact (at_hull_keep SK B rlo rhi cx mm (c_s cx) (c_slen cx + 1) HB0 HKT HMR2 (proj1 Rs)
                       ltac:(lia) HHV2)
            | lia | lia | lia | lia ] ] ]
      end. }
    cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3' & -> & HJ3 & HP3 & Hd3 & Hcpy & Hfr3 & Hpres3 & Hsm3).
    lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msc) |- _ =>
      assert (FD3 : m_fds md3' = m_fds (c_mdc cx) /\ m_fs md3' = m_fs (c_mdc cx));
      [ unfold same_but_materialized in Hsm3; rewrite Hsm3;
        repeat rewrite (proj1 (wvb_fds_fs _ _ _)); repeat rewrite (proj2 (wvb_fds_fs _ _ _));
        split; [exact HFDS | exact HFS] |];
      assert (ST4 : at_step cx (ms_mem msc) mem3);
      [ apply (at_step_call cx _ _ (c_w cx + n) len); [| exact Hpres3 | lia | unfold NW_SIZE; lia];
        intros a Ha Hd Hw; apply Hfr3; [exact Ha | exact Hd | rewrite Qsp; exact Hw] |]
    end.
    clear Hsm3 Hcpy.
    jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H (c_W cx)) mem3) HP3 [0; 1]%nat HS3.
    lazymatch type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U2; intros x Hx.
        + apply (lw_mbyte_of_aview SEGS). apply Hfr3.
          * unfold AT_FRAME in *. lia.
          * unfold apart_frame, c_w, c_sp, ATTR_TEXT_AK, ATTR_TEXT_AFRAME, ESTACK, AT_FRAME, NW_SIZE in *. lia.
          * rewrite Qsp. unfold AT_FRAME in *. lia.
        + intros _. exfalso. lia.
      - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U9; intros x Hx.
        + apply (lw_mbyte_of_aview SEGS). apply Hfr3.
          * lia.
          * lia.
          * rewrite Qsp.
            unfold apart_frame, c_w, c_sp, ATTR_TEXT_AK, ATTR_TEXT_AFRAME, ESTACK, AT_FRAME, NW_SIZE in *. lia.
        + intros Hwx. exact (writable_kept (segs := SEGS) (w_H (c_W cx)) _ mem3 x (Hpres3 x) Hwx). }
    clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
    remember (havoc E 48 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
    assert (HEI3 : img_env pa_val A_LIM E3) by (rewrite HE3; apply img_env_havoc; [assumption | cbv; lia]).
    assert (HA3 : env_agree 48 E E3) by (rewrite HE3; apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
    clear HE3.
    assert (F9 : ew E3 9%nat = w64 (c_w cx)) by (rewrite (proj1 HA3 9%nat ltac:(lia)); exact E9).
    assert (F19 : ew E3 19%nat = w64 len) by (rewrite (proj1 HA3 19%nat ltac:(lia)); exact E19).
    assert (F32 : ew E3 32%nat = w64 SHADOW_OFF) by (rewrite (proj1 HA3 32%nat ltac:(lia)); exact E32).
    assert (F33 : ew E3 33%nat = w64 n) by (rewrite (proj1 HA3 33%nat ltac:(lia)); exact E33).
    assert (F34 : ew E3 34%nat = w64 f) by (rewrite (proj1 HA3 34%nat ltac:(lia)); exact E34).
    assert (V2 : bv_unsigned (ew E3 2%nat) = c_sp cx - AT_FRAME) by (rewrite (proj1 HA3 2%nat ltac:(lia)); exact U2).
    assert (V9 : bv_unsigned (ew E3 9%nat) = c_w cx) by (rewrite (proj1 HA3 9%nat ltac:(lia)); exact U9).
    clear U2 U9 E9 E19 E32 E33 E34 UL.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
      assert (HK3 : at_kept cx (ms_mem msc)) by exact (at_kept_step cx _ _ HKEPT (at_step_trans cx _ _ _ ST3 ST4))
    end.
    clear SHOK.
    assert (SHOK : sh_ok SEGS at_Bx at_SH E3 (mrestrict (w_H (c_W cx)) mem3))
      by exact (at_shok SK B rlo rhi cx mem3 E3 HB0 HK3 F9 F32).
    (* +0x1c0 .. +0x1d0: C1, n := n + len *)
    paj_run_to_tok RUNTO HS HJ3 SHOK at_span AT_J3.
    { at_awr_tac Hajw. }
    pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => c_w cx + 4096 <= a < c_w cx + 4112) HFr
      ltac:(at_frame_tac)) as UN5.
    pose proof (at_step_trans cx _ _ _ (at_step_trans cx _ _ _ ST3 ST4)
      (at_step_run cx _ _ _ UN5 ltac:(intros a Ha; cbv beta in Ha; unfold NW_SIZE; lia) HG)) as ST5.
    clear HF HFr HG UN5.
    lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      pose proof (at_regs_carry cx n f ms3 E3 ssx (w_H (c_W cx)) msc AT_LIVE_REGS HREGS HA3 HS
        ltac:(vm_compute; reflexivity)) as HRC5;
      pose proof (at_regs_carry cx n f ms3 E3 ssx (w_H (c_W cx)) msc [19%bv] HREGS HA3 HS
        ltac:(vm_compute; reflexivity) 19%bv (or_introl eq_refl)) as HR19;
      pmkst HS;
      eapply (HNEXT cx len (len + n) f); [exact HB0|];
      eapply (at_inv_of SK B rlo rhi cx AT_J2 len n f ms3 AT_J3 len (len + n) f);
      [ exact HB0 | exact HSHAPE | exact HLIVE | exact HKEPT | exact HFIELDS | exact HRC5
      | rewrite HR19; exact L19
      | exact ST5
      | exact HJ3
      | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact (proj1 FD3)
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact (proj2 FD3)
      | eapply (at_val_of_ss E3 ssx (w_H (c_W cx)) msc 1 9 (c_w cx) 4096 4112 4096 4112 _ 4096 8);
        [ exact HS | reflexivity | exact V9 | cbn [In]; first [left; reflexivity | right; left; reflexivity]
        | apply at_denot; at_U | cbn; lia | cbn; lia ]
      | eapply (at_val_of_ss E3 ssx (w_H (c_W cx)) msc 1 9 (c_w cx) 4096 4112 4096 4112 _ 4104 4);
        [ exact HS | reflexivity | exact V9 | cbn [In]; first [left; reflexivity | right; left; reflexivity]
        | apply at_denot; at_U | cbn; lia | cbn; lia ]
      | unfold NL_CHUNK_MAX; lia | lia | lia | lia ]
    end.
- (* no room: full := 1 *)
  rewrite branch_ltu_U, UL, (U_lit E 4097) in Hc by lia. apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK at_span AT_J3.
  { at_awr_tac Hajw. }
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => c_w cx + 4096 <= a < c_w cx + 4112) HFr
    ltac:(at_frame_tac)) as UN2.
  pose proof (at_step_trans cx _ _ _ ST1
    (at_step_run cx _ _ _ UN2 ltac:(intros a Ha; cbv beta in Ha; unfold NW_SIZE; lia) HG)) as ST2.
  clear HF HFr HG UN2 ST1.
  lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
    pose proof (at_regs_carry cx n f ms3 E ssx (w_H (c_W cx)) msc AT_LIVE_REGS HREGS (env_agree_refl 48 E) HS
      ltac:(vm_compute; reflexivity)) as HRC;
    pose proof (at_regs_carry cx n f ms3 E ssx (w_H (c_W cx)) msc [19%bv] HREGS (env_agree_refl 48 E) HS
      ltac:(vm_compute; reflexivity) 19%bv (or_introl eq_refl)) as HR19;
    pmkst HS;
    eapply (HNEXT cx len n 1); [exact HB0|];
    eapply (at_inv_of SK B rlo rhi cx AT_J2 len n f ms3 AT_J3 len n 1);
    [ exact HB0 | exact HSHAPE | exact HLIVE | exact HKEPT | exact HFIELDS | exact HRC
    | rewrite HR19; exact L19
    | exact ST2
    | exact HJ
    | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact HFDS
    | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact HFS
    | eapply (at_val_of_ss E ssx (w_H (c_W cx)) msc 1 9 (c_w cx) 4096 4112 4096 4112 _ 4096 8);
      [ exact HS | reflexivity | exact U9 | cbn [In]; first [left; reflexivity | right; left; reflexivity]
      | apply at_denot; at_U | cbn; lia | cbn; lia ]
    | eapply (at_val_of_ss E ssx (w_H (c_W cx)) msc 1 9 (c_w cx) 4096 4112 4096 4112 _ 4104 4);
      [ exact HS | reflexivity | exact U9 | cbn [In]; first [left; reflexivity | right; left; reflexivity]
      | apply at_denot; at_U | cbn; lia | cbn; lia ]
    | unfold NL_CHUNK_MAX; lia | lia | lia | lia ]
  end.
Qed.

End b.
End a.
