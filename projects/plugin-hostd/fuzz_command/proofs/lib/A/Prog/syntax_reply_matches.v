(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (the leaf walk: the seed at
   the entry, the run, the return) and lib/A/AC8b.v (loops by fuel induction) at c8557374ad2e: the walk of
   syntax_reply_matches on fuzz_command.asan. This file: the prologue (0x8857c to the item loop at 0x885e8), the entry
   facts the statement's premises give, and the theorem. The segments are in syntax_reply_matches_s1.v .. _s7.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa
  CmdPaLib PaSB PaDenot CmdBase CmdRep CmdObj CmdRo PaArt CmdChk PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase CmdRecCells CmdRecRo CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import syntax_reply_matches_c syntax_reply_matches_s1
  syntax_reply_matches_s2 syntax_reply_matches_s3 syntax_reply_matches_s4 syntax_reply_matches_s5 syntax_reply_matches_s6
  syntax_reply_matches_s7.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require PaLibH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* atoms at the entry: 0..31 the registers, 32 the shadow base; A_OBJ 0 the GOT word of the shadow-base cell, A_OBJ 12
   the cell (as rec_code_declared's walk seeds them, after cgif A/AChd.v) *)
Definition srm_Bx0 : sv := SOff 32 0.
Definition srm_regions : smem := [ stack_region 112; got_regionP; bcell_regionP 32 ].
Definition srm_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_srm : sstate := mkSS AF_syntax_reply_matches sr_atoms srm_regions None srm_facts.
Definition srm_extra : list word := [Z_to_bv 64 SB].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation STK := SYNTAX_REPLY_MATCHES_STK.
Lemma srm_val_objs : cmd_val_objs -> VAL (A_OBJ 0) = 0xa63f0 /\ VAL (A_OBJ 12) = 0xb10b8 /\ VAL (A_OBJ 23) = 0x21120.
Proof.
intros HVO.
rewrite (HVO 0%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)), (HVO 12%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)),
  (HVO 23%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
vm_compute. repeat split.
Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callee rules, with the statement's names (syntax_reply_matches_c.v:62-63) *)
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) A_SSP_GOT A_SSP_GUARD.
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp).
(* the per-binary facts, with cgif's names: the allocator laws,
   the shadow-base symbols, the allocator record's symbols and the image's facts *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
(* the CmdRecFacts lemmas, used below: the tail of the strcspn set " " (.str.4, 0x21120, 2 bytes) among
   CmdRo's literal ends (CmdRecRo.v's cmd_tail_vis_at), its shadow and that of a read-only shape by the record's
   checkers (CmdRecBase.v's cmd_aread_ok_chk), the stack-protector GOT word and guard cell musl's strcspn reads
   (CmdRecCells.v's cmd_rec_cells), and RtDefs.v's read-only view from arodata_okP (CmdRecImg.v's cmd_rom_view_on) *)
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

(* the seed at the entry (rec_code_declared's rcd_entry, after cgif A/AChd.v) *)
Lemma srm_entry_seed : forall ly S W (regs : bvmap 5 word) mem md,
  afn_pre_na SEGS B STK ly S W regs mem md -> cmd_val_objs ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs srm_extra)) ss_srm
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_syntax_reply_matches)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS srm_Bx0 [] (Eimg (Ereg regs srm_extra)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md HPRE HVO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK = 8304) by reflexivity.
destruct (srm_val_objs HVO) as (V0 & V12 & V23).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell, V0, V12 in Kgot. rewrite HBcell, V12 in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs srm_extra)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs srm_extra) n) by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 0xa63f0)
  by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V0; reflexivity).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 0xb10b8)
  by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V12; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_srm. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold srm_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
    * rewrite (VB (A_OBJ 0) 0xa63f0 EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ 0xa63f0 0 8 (SOff (A_OBJ 12) 0) 0xb10b8);
        [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) 0xb10b8 EO12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ 0xb10b8 0 8 srm_Bx0 SB);
        [unfold srm_Bx0; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold srm_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) 0xa63f0 EO0), (VB (A_OBJ 12) 0xb10b8 EO12) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite WS in Hstk0, Hslo. clear - Hslo Hshi H47 C1 Hceil.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [srm_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    rewrite WS in Hslo. clear - Hal16 Hslo Hshi H47 C1 Hceil. unfold SB.
    repeat split; first [lia | reflexivity].
- constructor.
Qed.

(* a read-only byte of the statement (in_roP over CMD_RLO / CMD_RHI) lies in the image *)
Lemma srm_ro_img : forall a, in_roP SEGS RLO RHI a -> 0x10000 <= a < 0x606000.
Proof.
intros a [(sg & Hsg & _ & Ha) | Hr]; [apply pa_img_range; exists sg; split; [exact Hsg | exact Ha] |].
unfold CMD_RLO, CMD_RHI in Hr. lia.
Qed.

(* The entry facts of the walk (srm_ok, syntax_reply_matches_s1.v) from the statement's premises
   (syntax_reply_matches_c.v:68-82) and the record's facts above. *)
Lemma srm_ok_entry : forall ly S W (regs : bvmap 5 word) mem md (ps rp : Z) (shape reply : list byte),
  afn_pre_na SEGS B STK ly S W regs mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) ->
  getr regs 10 = w64 ps -> getr regs 11 = w64 rp ->
  astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] ps (Some shape) ->
  Z.of_nat (length shape) < 2 ^ 31 ->
  in_blockA (ablocks B ly S) rp (Z.of_nat (length reply) + 1) -> astr_atR (rdW W mem) rp reply ->
  atail_vis SEGS W mem (rp + Z.of_nat (length reply)) ->
  cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
  srm_ok B (mkSRM ly S W regs mem md ps rp shape reply).
Proof.
intros ly S W regs mem md ps rp shape reply HPRE HARO H10 H11 HSH HSL HRB HRS HRT HRO HVO.
pose proof HPRE as (HAR & _).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
destruct HSH as (_ & HSs & _ & HSk).
(* the reply's band room 8 bytes past it (the strcspn entry's `+ 8` premise), also when its NUL is the block's last
   byte (check_reply makes it so; call site 13 of the band-premise survey) *)
pose proof (PaLibH.amem8_of_blockA SEGS B LAWS ly S W mem md rp (Z.of_nat (length reply)) HAR HRB ltac:(lia)) as HRM8.
destruct HRB as (p & k & Hin & Hp & Hpk).
destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hk).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq]. unfold MALLOC_MAX in Hk.
assert (HS1 : 4096 <= ps /\ ps + Z.of_nat (length shape) + 1 <= alloc_ceiling /\
  amem_range ps (Z.of_nat (length shape) + 1) /\
  range_addressable (rdW W mem) SHADOW_OFF ps (Z.of_nat (length shape) + 1) /\
  shadow_hull_vis (rdW W mem) ps (Z.of_nat (length shape) + 1)).
{ destruct HSk as [((p' & k' & Hin' & Hp' & Hpk') & _) | (Hro & Hca & Chh & _)].
  - destruct (al_blocks _ _ LAWS ly S W mem md p' k' HAR Hin') as (_ & Hp4096' & Hpceil' & _ & _ & _ & Hk').
    pose proof (req_size_pos k' ltac:(lia)) as [_ Hreq'].
    split; [lia|]. split; [lia|]. split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md p' k' ps (Z.of_nat (length shape) + 1) HAR Hin' Hp' ltac:(lia))|].
    split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md p' k' ps (Z.of_nat (length shape) + 1) HAR Hin' Hp' ltac:(lia))|].
    exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md p' k' ps (Z.of_nat (length shape) + 1) HAR Hin' Hp' ltac:(lia) ltac:(lia)).
  - pose proof (srm_ro_img _ (proj1 (Hro 0 ltac:(lia)))) as R0.
    pose proof (srm_ro_img _ (proj1 (Hro (Z.of_nat (length shape)) ltac:(lia)))) as R1.
    destruct (cmd_aread_ok_chk SEGS B LAWS HB ly S W mem md ps (Z.of_nat (length shape) + 1) HAR Hca Chh) as [Hra Hhv].
    split; [lia|]. split; [lia|]. split; [unfold amem_range; lia|]. split; [exact Hra | exact Hhv]. }
destruct HS1 as (HP1 & HP2 & HPm & HPa & HPh).
unfold srm_ok. cbn [x_ly x_S x_W x_regs x_mem x_md x_P x_R x_shape x_reply].
split; [exact HPRE|]. split; [exact H10|]. split; [exact H11|].
split; [exact HSs|]. split; [exact HP1|]. split; [exact HP2|]. split; [exact HPm|]. split; [exact HPa|].
split; [exact HPh|]. split; [exact HSL|].
split; [exact HRS|]. split; [lia|]. split; [lia|].
split; [exact HRM8|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md p k rp (Z.of_nat (length reply) + 1) HAR Hin Hp ltac:(lia))|].
split; [exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md p k rp (Z.of_nat (length reply) + 1) HAR Hin Hp ltac:(lia) ltac:(lia))|].
split; [lia|]. split; [exact HRT|].
destruct (cmd_rec_cells SEGS B LAWS HB IMG ly S W mem md HAR) as (_ & HG & _).
split; [exact HRO|]. split; [exact HVO|]. split; [exact HG|].
destruct (cmd_aread_ok_chk SEGS B LAWS HB ly S W mem md 0x21120 2 HAR ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
  as [Z1 Z2].
split; [exact Z1|]. split; [exact Z2|].
split; [apply (cmd_tail_vis_at SEGS B LAWS HB IMG ly S W mem md 0x21121 HAR); unfold cmd_ro_ends; repeat (first [left; reflexivity | right])|].
(* the unowned ROM bytes: the in-segment half of arodata_okP *)
exact (cmd_rom_view_on SEGS B LAWS HB IMG RLO RHI W mem HARO).
Qed.

(* The walk: the prologue runs to the item loop (0x885e8) with the frame saved and the constants loaded; srm_main
   (syntax_reply_matches_s7.v) gives the rest. *)
Theorem tsyntax_reply_matches_spec_holds : tsyntax_reply_matches_spec B MT.
Proof.
unfold tsyntax_reply_matches_spec.
intros ly S W regs mem md ps rp shape reply HPRE HARO H10 Hps H11 Hrp HSH HSL HRB HRS HRT HRO HVO Hev.
pose proof (srm_ok_entry ly S W regs mem md ps rp shape reply HPRE HARO H10 H11 HSH HSL HRB HRS HRT HRO HVO) as HX.
destruct (srm_entry_seed ly S W regs mem md HPRE HVO) as [HS SHOK].
pose proof (ajournal_init_na SEGS B STK [] ly S W regs mem md HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof (srm_ok_facts B (mkSRM ly S W regs mem md ps rp shape reply) HX) as (F1 & F2 & F3 & F4 & FP1 & FP2 & FR1 & FR2 & FL1 & FL2).
unfold srm_sp0 in F2, F3, F4. cbn [x_P x_R x_shape x_reply x_regs x_ly] in FP1, FP2, FR1, FR2, FL1, FL2, F1, F2, F3, F4.
pose proof asan_consts as (C1 & _).
assert (WS : SYNTAX_REPLY_MATCHES_STK = 8304) by reflexivity.
destruct (srm_val_objs HVO) as (V0 & V12 & V23).
remember (Eimg (Ereg regs srm_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs srm_extra) n) by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (V10 : bv_unsigned (ew E 10) = ps)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10; apply w64_unsigned; lia).
assert (V11 : bv_unsigned (ew E 11) = rp)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), H11; apply w64_unsigned; lia).
assert (V32 : bv_unsigned (ew E 32) = SB)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 0); apply unsigned_lit_small; unfold SB; lia).
assert (VO23 : bv_unsigned (ew E (A_OBJ 23)) = 0x21120)
  by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V23; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs srm_extra) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_syntax_reply_matches)) with (Z_to_bv 64 (BASE + AF_syntax_reply_matches)).
paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_L0;
  [awr_ok_tac; try (cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp)|].
lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?msn) =>
  let rs := eval vm_compute in (ss_mem ss) in
  lazymatch rs with ?r0 :: _ =>
    assert (HR0 : region_ok SEGS E (ms_mem (restrict (w_H W) msn)) r0)
      by exact (st_ok_region_nth (segs := SEGS) E _ _ 0 r0 HS ltac:(vm_compute; reflexivity))
  end;
  (* memory outside the 112-byte frame is the entry's *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> rdW W (ms_mem msn) a = rdW W mem a)
    by (apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem msn) (fun a => spZ regs - 112 <= a < spZ regs) HFr);
        intros b wlo whi a Hin Ha; unfold windows in Hin; apply in_map_iff in Hin as (r & Hr' & Hin);
        cbn in Hin; destruct Hin as [<- | [<- | [<- | []]]]; cbn in Hr'; injection Hr' as <- <- <-;
        cbn [base_val] in Ha; [rewrite Usp in Ha; lia | lia | lia]);
  srm_kept HS HAE ([3; 4]%bv : list (bv 5)) HK;
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => assert (HI : srm_inv B (mkSRM ly S W regs mem md ps rp shape reply) (ms_regs msn) (ms_mem msn) mdq) end
end.
{ split; [exact HJ|]. split.
  { intros a Ha Hn. apply KEEP; [exact Ha|]. unfold srm_sp0 in Hn. cbn [x_regs] in Hn. unfold STK, SYNTAX_REPLY_MATCHES_STK, ESTACK in Hn.
    lia. }
  split.
  { unfold srm_frame, SRM_SAVES, srm_sp0. cbn [x_W x_regs].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    lazymatch goal with |- val_mem _ _ (spZ ?rg - 112 + ?off) 8 (bv_unsigned (getr ?rg ?r)) =>
      let od := eval vm_compute in (off - 112) in
      let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
      replace (spZ rg - 112 + off) with (spZ rg + od) by lia;
      change 8%nat with (N.to_nat 8);
      apply (field_of_region E _ 2%nat (spZ rg) _ _ _ _ _ od 8 (SOff n 0) (bv_unsigned (getr rg r)) HR0 Usp);
      [ cbn [In]; repeat (first [left; reflexivity | right])
      | cbn [sv_denot]; rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat rg _ n r eq_refl), Z.add_0_r, !Z_to_bv_bv_unsigned;
        reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr rg r)) as Hr; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hr; exact Hr
      | lia ] end. }
  unfold srm_sp0. cbn [x_regs].
  split; [srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; lia|].
  split; [rewrite (HK 3%bv) by (cbn; tauto); reflexivity|].
  split; [rewrite (HK 4%bv) by (cbn; tauto); reflexivity|].
  split; [srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by (unfold SB; lia); reflexivity|].
  repeat split; srm_rgoal HS; srm_ucalc; reflexivity. }
pmkst HS.
eapply (srm_main B LAWS TL (ABCMP fx) (ASTRCSPN fx) (mkSRM ly S W regs mem md ps rp shape reply) (Datatypes.S (length shape)) HX 0%nat 0%nat (length shape) _ _ _ ltac:(cbn; lia) ltac:(lia)
  ltac:(lia) ltac:(cbn; lia) eq_refl HI).
- srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; cbn [x_P]; lia.
- srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; cbn [x_R]; lia.
- srm_rgoal HS; change (SOff 264 0) with (SOff (A_OBJ 23) 0); srm_ucalc; reflexivity.
- srm_rgoal HS; srm_ucalc; reflexivity.
Qed.
End e.
End f.
End d.
