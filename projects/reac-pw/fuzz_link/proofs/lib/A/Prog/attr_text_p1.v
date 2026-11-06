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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_entry.v, with its module names changed; 168 of its 205 lines of code are new or changed and 688 lines of the source are left out. *)
(* attr_text on image A (fuzz_link.asan 0x86b18; listing (internal path) (internal record, sha256 03340ee12716)),
   PHASE 1: the type, from the join +0xec to the join +0x170 (lib/A/Prog/attr_text_base.v explains the phase form).

   At +0xec a1 still holds 2 ^ 64 - 4095 (`addiw a1, a3, 1` at +0x6c, a3 = 0xfffff000), which the room test reuses,
   so the invariant at this join (`at_inv1`) pins it beside `at_inv`.
   +0xec the instrumented check C1 of n; +0xf4 n; +0xfc..+0x104 `bltu 2 ^ 64 - 4098, n - 4095` (room for the two
   bytes of the attribute's type: n <= 4094):
   - no room: +0x108..+0x124 check C2 of full, full := 1, `j` to the join +0x170;
   - room: +0x128 a0 := w + n, which the engine reaches through the alias (w + n, SOff 35 0) (atom 35 = w + n,
     attr_text_base.v at_extra); the two checks C3 of [w + n, w + n + 2) on the shadow entry [w + n, w + n + 2);
     +0x150..+0x158 the two bytes of type into b at w + n (a region of two writable bytes based at atom 35, disjoint
     from the fields' region because n <= 4094); +0x15c..+0x16c C1, n := n + 2, the join +0x170.

   Section hypothesis: LAWS : AR_laws pa_segs B (the lib/A frame).
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
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the invariant at +0xec: the join invariant, and a1 = 2 ^ 64 - 4095 *)
Definition at_inv1 (cx : atcx) (len n f : Z) (ms3 : machine_state) (md3 : Model) : Prop :=
  at_inv SK B cx AT_J1 len n f ms3 md3 /\ getr (ms_regs ms3) 11 = w64 (2 ^ 64 - 4095).

(* the region of the two bytes of b at w + n *)
Definition at_b2 : YP09.region := YP09.mkRegion (Some 35%nat) 0 2 0 2 [].

Theorem at_p1 :
  at_from SK B rlo rhi (fun cx len n f ms md => at_inv SK B cx AT_J2 len n f ms md) ->
  at_from SK B rlo rhi at_inv1.
Proof.
intros HNEXT cx len n f ms3 md3 HB (HI & Ha1).
pose proof HB as HB0.
destruct HB as (HPRE & HRD & HNLW & HWF & Hs0 & HSTR & HSLEN & HSLACK & HAP & HAPF1 & HAPF2 &
  HMR1 & HRA1 & HHV1 & HMR2 & HRA2 & HHV2).
destruct HPRE as (HJ0 & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside &
  Hajw & Hro).
destruct HI as (HSHAPE & HLIVE & HJ & HFDS & HFS & HFIELDS & HN0 & Hlen0 & Hlen1 & HKEPT).
destruct (at_entry_J SK B rlo rhi cx AT_J1 len n f ms3 HB0 HSHAPE HLIVE HFIELDS HKEPT)
  as (U2 & U9 & HREGS & HS0 & SHOK).
pose proof HFIELDS as (Hw0 & Hwl & HPRES & HVN & HVF & (Hn0 & Hn1) & (Hf0 & Hf1)).
pose proof HLIVE as (L8 & L9 & L18 & L19 & L20 & L21 & L22).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (Hceil : alloc_ceiling <= c_sp0 cx - c_STK cx) by (eapply (aj_stk_ceiling SK SEGS B); exact HJ0).
assert (HSPlo : alloc_ceiling + ATTR_TEXT_AK <= c_sp cx) by (unfold c_sp in *; lia).
assert (HSPhi : c_sp cx < 2 ^ 64)
  by (unfold c_sp, spZ; pose proof (u64_range (getr (c_regs cx) 2)); lia).
assert (HAK : ATTR_TEXT_AK = 4160) by reflexivity.
pose proof (at_w_range cx) as Rw.
unfold NL_CHUNK_MAX in Hn1.
assert (Hamr : c_w cx + 4113 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, NW_SIZE in *; lia).
set (E := Eimg (Ereg (ms_regs ms3) (at_extra cx n f))) in *.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall j, (j < 16)%nat -> ew E (32 + j)%nat = nth j (at_extra cx n f) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [at_extra nth Nat.add] in E32, E33, E34, E35.
assert (E9 : ew E 9%nat = w64 (c_w cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 9 9%bv eq_refl); exact L9).
(* a1, pinned at its value *)
pose proof (st_ok_pi_pin_reg' E (at_ssJ AT_J1) (restrict (w_H (c_W cx)) ms3) 11%bv (2 ^ 64 - 4095) HS0
  ltac:(cbn [restrict ms_regs]; exact Ha1) eq_refl) as HS.
clear HS0.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS end.
pose (RUN := paj_run_x SK B LAWS (c_G cx) HGok (c_XO cx) (c_OUT cx)).
pose (RUNTO := paj_run_to_x SK B LAWS (c_G cx) HGok (c_XO cx) (c_OUT cx)).
pose (BR := paj_branch (PI := PI)).
(* +0xec .. +0x104: C1, n, up to the room test *)
paj_run_to_tok RUNTO HS HJ SHOK at_span AT_J2.
{ at_awr_tac Hajw. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => c_w cx + 4096 <= a < c_w cx + 4112) HFr
  ltac:(at_frame_tac)) as UN1.
pose proof (at_step_run cx _ _ _ UN1 ltac:(intros a Ha; cbv beta in Ha; unfold NW_SIZE; lia) HG) as ST1.
clear HF HFr HG UN1.
assert (U4095 : U E (SOff 33 (-4095)) = (n - 4095) mod 2 ^ 64).
{ rewrite U_SOff, E33. unfold w64. rewrite unsigned_lit_small by lia. unfold zcanon, M64. f_equal; lia. }
psrr_branch_tok RUN BR HS SHOK at_span.
- (* room: n <= 4094 *)
  rewrite branch_ltu_U, (U_lit E 18446744073709547518), U4095 in Hc by lia. apply Z.ltb_lt in Hc.
  assert (Hn94 : n <= 4094) by lia.
  clear Hc.
  assert (U35 : bv_unsigned (ew E 35%nat) = c_w cx + n) by (rewrite E35; unfold w64; apply unsigned_lit_small; lia).
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
    assert (HK1 : at_kept cx (ms_mem msc)) by exact (at_kept_step cx _ _ HKEPT ST1)
  end.
  (* the alias w + n = atom 35, its range, its two-byte region, its shadow entry *)
  pose proof (st_ok_pi_add_alias SEGS pa_val E _ _ (SAlu ALU_ADD (SOff 9 0) (SOff 33 0)) (SOff 35 0) HS) as HS5.
  lazymatch type of HS5 with ?t -> _ =>
    assert (HR : t) by (apply U_inj; transitivity (c_w cx + n); [at_U | symmetry; at_U]);
    specialize (HS5 HR); clear HR end.
  clear HS.
  pose proof (st_ok_pi_add_fact E _ _ 35 (mkAF 0 (2 ^ 47 - 19) 0) HS5) as HS6.
  lazymatch type of HS6 with ?t -> _ =>
    assert (HR : t) by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U35, Z.pow_0_r, Z.mod_1_r; lia);
    specialize (HS6 HR); clear HR end.
  clear HS5.
  lazymatch type of HS6 with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS6 end.
  pose proof (st_ok_pi_add_region E _ _ at_b2 HS6 eq_refl) as HS7.
  lazymatch type of HS7 with ?t -> _ -> _ => assert (HR : t); [|specialize (HS7 HR); clear HR] end.
  { unfold region_ok, at_b2.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U35.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. cbn [ms_mem restrict].
    apply (writable_kept (segs := SEGS) (w_H (c_W cx)) (ms_mem ms3) _ _ (proj2 ST1 _)).
    replace (c_w cx + n + o) with (c_w cx + (n + o)) by lia.
    exact (proj2 (HPRES (n + o) ltac:(unfold NW_SIZE; lia))). }
  lazymatch type of HS7 with ?t -> _ => assert (HR : t); [|specialize (HS7 HR); clear HR] end.
  { cbv [ss_mem all_disjoint extent_disjoint at_b2 YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite U35, U2, U9.
    unfold apart_frame, c_w, c_sp, ATTR_TEXT_AK, ATTR_TEXT_AFRAME, ESTACK, AT_FRAME, NW_SIZE in *.
    split; [lia|]. split; [lia|]. exact I. }
  clear HS6. rename HS7 into HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS end.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
    assert (SHOK1 : sh_ok SEGS at_Bx [mkSHE 9 4096 4112; mkSHE 35 0 2] E (mrestrict (w_H (c_W cx)) (ms_mem msc)));
    [ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      [ apply (at_she_ok SK B rlo rhi cx (ms_mem msc) E 9 (c_w cx) 4096 4112 HB0 HK1 E9 E32); unfold NW_SIZE; lia
      | apply (at_she_ok SK B rlo rhi cx (ms_mem msc) E 35 (c_w cx + n) 0 2 HB0 HK1 E35 E32); unfold NW_SIZE; lia ]
    | ]
  end.
  clear SHOK. rename SHOK1 into SHOK.
  (* +0x128 .. +0x16c: C3 twice, the two bytes, C1, n := n + 2 *)
  paj_run_to_tok RUNTO HS HJ SHOK at_span AT_J2.
  { at_awr_tac Hajw. }
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
    (fun a => (c_w cx + 4096 <= a < c_w cx + 4112) \/ (c_w cx + n <= a < c_w cx + n + 2)) HFr
    ltac:(at_frame_tac)) as UN2.
  pose proof (at_step_trans cx _ _ _ ST1
    (at_step_run cx _ _ _ UN2 ltac:(intros a Ha; cbv beta in Ha; unfold NW_SIZE; lia) HG)) as ST2.
  clear HF HFr HG UN2 ST1.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E1 := Ex) in * end.
  assert (HA1 : env_agree 48 E E1) by (subst E1; at_agree).
  clearbody E1.
  assert (F33 : ew E1 33%nat = w64 n) by (rewrite (proj1 HA1 33%nat ltac:(lia)); exact E33).
  assert (F34 : ew E1 34%nat = w64 f) by (rewrite (proj1 HA1 34%nat ltac:(lia)); exact E34).
  assert (V9 : bv_unsigned (ew E1 9%nat) = c_w cx) by (rewrite (proj1 HA1 9%nat ltac:(lia)); exact U9).
  lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
    pose proof (at_regs_carry cx n f ms3 E1 ssx (w_H (c_W cx)) msc AT_LIVE_REGS HREGS HA1 HS
      ltac:(vm_compute; reflexivity)) as HRC;
    pose proof (at_regs_carry cx n f ms3 E1 ssx (w_H (c_W cx)) msc [19%bv] HREGS HA1 HS
      ltac:(vm_compute; reflexivity) 19%bv (or_introl eq_refl)) as HR19;
    pmkst HS;
    eapply (HNEXT cx len (n + 2) f); [exact HB0|];
    eapply (at_inv_of SK B rlo rhi cx AT_J1 len n f ms3 AT_J2 len (n + 2) f);
    [ exact HB0 | exact HSHAPE | exact HLIVE | exact HKEPT | exact HFIELDS | exact HRC
    | rewrite HR19; exact L19
    | exact ST2
    | exact HJ
    | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact HFDS
    | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact HFS
    | eapply (at_val_of_ss E1 ssx (w_H (c_W cx)) msc 2 9 (c_w cx) 4096 4112 4096 4112 _ 4096 8);
      [ exact HS | reflexivity | exact V9 | cbn [In]; first [left; reflexivity | right; left; reflexivity]
      | apply at_denot; at_U | cbn; lia | cbn; lia ]
    | eapply (at_val_of_ss E1 ssx (w_H (c_W cx)) msc 2 9 (c_w cx) 4096 4112 4096 4112 _ 4104 4);
      [ exact HS | reflexivity | exact V9 | cbn [In]; first [left; reflexivity | right; left; reflexivity]
      | apply at_denot; at_U | cbn; lia | cbn; lia ]
    | unfold NL_CHUNK_MAX; lia | lia | lia | lia ]
  end.
- (* no room: full := 1 *)
  rewrite branch_ltu_U, (U_lit E 18446744073709547518), U4095 in Hc by lia. apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK at_span AT_J2.
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
    eapply (at_inv_of SK B rlo rhi cx AT_J1 len n f ms3 AT_J2 len n 1);
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
