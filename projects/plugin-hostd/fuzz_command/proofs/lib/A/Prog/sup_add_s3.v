(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: descriptors_panel_get's walk from the join of record()'s arms (0x8d180) to the call of xstrdup (plugin-hostd/fuzz_command.asan), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment proved from the next one's statement: seed, run, branch, call) and lib/A/Prog/sup_reply_code.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/descriptors_panel_get_s4.v, with its module paths and module names changed; 178 of its 222 lines of code are new or changed and 263 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_add_s4.v, with its module paths and module names changed; 128 of its 182 lines of code are new or changed and 168 lines of the source are left out. *)
(* sup_add's walk on the ASan build of plugin-hostd/fuzz_command: the stage from M1 (0x89f48) to the return of arg_i.

   The head (this file): buf[32] unpoisoned (`sb zero,4..7(s9)`, s9 = SB + F / 8), the `bnez s8` on uri (s8 = pu,
   never 0: sa_uri, so the "(null)" arm is pruned by the seed's fact on atom 24), `mv a0,s8`, `jal xstrdup`. The
   symbolic state is seeded fresh at M1 with the shadow window [4, 8) above s9 and no chunks. The rest, from the
   entry of xstrdup through arg_i's call, is sa3_cont (sup_add_s3a.v); it continues with the stage SA_A2_stmt at the
   FP state arg_i returns (sup_add_s3a.v's sa_a2_ok, assembled in sup_add.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaSB PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_add_s0 sup_add_lem sup_add_s3a PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the seed at M1 (14948 = AF_sup_add + 0x18c): atoms 0..31 the registers; the frame's shadow bytes [4, 8) above
   s9 (atom 25) writable, no chunks; s8 (atom 24) = pu is not 0. The stretch makes no inline check, so it runs
   without shadow entries (paj_run_shc, as stage 1's frame setup). *)
Definition s3_bufr : YP09.region := YP09.mkRegion (Some 25%nat) 4 8 4 8 [].
Definition s3_facts1 : facts := mkFacts [(24%nat, mkAF 1 18446744073709551615 0)] [] [].
Definition s3_ss1 : sstate := mkSS 14948 sr_atoms [s3_bufr] None s3_facts1.
Lemma s3_byte_of_aval : forall (rd : reader) a, aval_mem rd a 1 0 -> rd a = Some 0.
Proof. intros rd a H. pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. exact H0. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Section f. Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e. Variable B : asyms. Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO. #[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a :=
  CmdRecBase.cif_prog_img _ _ IMG.
Let cif_relro_img : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a :=
  CmdRecBase.cif_relro_img _ _ IMG.
Let cif_prog_not_ro : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a :=
  CmdRecBase.cif_prog_not_ro _ _ IMG.
Let cmd_ro_in_img : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI) :=
  CmdRecRo.cmd_ro_in_img SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let cmd_tail_vis_at : forall ly S (W : world SEGS) mem md e, AR SEGS B ly S W mem md -> In e cmd_ro_ends ->
  atail_vis SEGS W mem e :=
  CmdRecRo.cmd_tail_vis_at SEGS B LAWS HB IMG.
(* the rounding mode at this stage's FP state: arg_i's premise *)
Hypothesis FXR : frm0 fx.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.

Lemma s3_seed1 : forall lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc pos pu,
  AR SEGS B lyc Sc Wc memc mdc -> In (1, pos) (frames Sc) ->
  bv_unsigned (ew (Eimg (Ereg regs1 [])) 25) = SHADOW_OFF + frame_addr lyc 1 pos / 8 ->
  bv_unsigned (ew (Eimg (Ereg regs1 [])) 24) = pu -> 0 < pu ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) s3_ss1
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + 14948)) memc (seg_rom SEGS))).
Proof using LAWS.
intros lyc Sc Wc regs1 memc mdc pos pu HAR Hin U25 U24 Hpu.
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 1 pos HAR Hin) as (_ & _ & _ & HFSpres).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 1 pos HAR Hin) as (HF0 & HFc & _).
change (fs_frame_bytes 1) with 128 in HFc. change (fs_frame_bytes 1 / 8) with 16 in HFSpres.
pose proof asan_consts as (C1 & _).
pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)) as HF8.
pose proof (bv_unsigned_in_range 64 (ew (Eimg (Ereg regs1 [])) 24)) as H24r. change (bv_modulus 64) with (2 ^ 64) in H24r.
rewrite restrict_mkst_fx. unfold s3_ss1. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok, s3_bufr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U25. split; [unfold SHADOW_OFF; lia|]. split.
  + assert (frame_addr lyc 1 pos / 8 < 2 ^ 60) by (apply Z.div_lt_upper_bound; lia). unfold SHADOW_OFF. lia.
  + split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS).
    destruct (HFSpres o ltac:(lia)) as (Hp & _). unfold shadow_addr in Hp. exact Hp.
- apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [|split; [exact I | exact I]].
  cbn [s3_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U24, Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Local Ltac s3_kof1 U :=
  intros ?b ?wlo ?whi ?a' ?Hin ?Hrr; vm_compute in Hin;
  repeat (destruct Hin as [?Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U in Hrr; lia|]); destruct Hin.

Lemma sa_m1_ok : (forall fx1 : YK11.FPState, frm0 fx1 -> SA_A2_stmt (fx := fx1) B MT) -> SA_M1_stmt B MT.
Proof using HB LAWS MTL SIGP PRW cif_prog_img cif_relro_img cif_prog_not_ro cmd_ro_in_img cmd_ro_ok_of_aro
  cmd_heap_tail_vis cmd_tail_vis_at FXR TXSTRDUP TARG_I.
intros HA2 ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos HCX HM1.
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCX as HCX0. pose proof HM1 as HM10.
unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & _ & _ & _ & H10 & Hpu & _ & _ & _ & _ & _ & _ & HU & _).
pose proof HPRE as (HAR0 & _).
destruct (sa_uri_argA B HB LAWS ly S W mem md O pu uri (in_roP SEGS RLO RHI) HAR0 HU)
  as (u & _ & (Hpu0 & _)).
unfold sa_M1m, sa_core in HM1. cbv zeta in HM1.
destruct HM1 as ((HJ1 & _ & _ & _ & _ & _ & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R25 & R26) &
  R20 & R22 & R23 & R24 & R27 & _).
pose proof (proj1 HJ1) as HARc.
pose proof HJ1 as (_ & _ & _ & _ & _ & Hfrs1 & _).
assert (HinF : In (1, pos) (frames Sc)) by (rewrite Hfrs1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 1 pos HARc HinF) as (HF0 & HFc & _).
change (fs_frame_bytes 1) with 128 in HFc.
pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)) as HF8.
assert (HF8h : frame_addr lyc 1 pos / 8 < 2 ^ 60) by (apply Z.div_lt_upper_bound; lia).
(* the seed *)
remember (Eimg (Ereg regs1 [])) as E1 eqn:HE1.
assert (HEI1 : img_env VAL A_LIM E1) by (subst E1; apply Eimg_env).
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs1 r)
  by (intros n r Hn'; subst E1; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn').
assert (U25 : bv_unsigned (ew E1 25) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (rewrite (EE1 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U24 : bv_unsigned (ew E1 24) = pu)
  by (rewrite (EE1 24%nat 24%bv eq_refl), R24, H10; apply unsigned_lit_small; lia).
pose proof (s3_seed1 lyc Sc Wc regs1 memc mdc pos pu HARc HinF ltac:(subst E1; exact U25) ltac:(subst E1; exact U24)
  ltac:(lia)) as HS.
rewrite <- HE1 in HS. clear HE1.
change (Z_to_bv 64 (BASE + L_M1)) with (Z_to_bv 64 (BASE + 14948)).
(* 0x89f48 .. 0x89f68: the four shadow stores, `bnez s8` (taken: s8 = pu <> 0), `mv a0,s8`, `jal xstrdup` *)
paj_run_shc (SRr_run_pi_AJ B LAWS) (SRr_run_pi_AJ_call B LAWS) HS HJ1.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U25 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold awr_byte. right; right; right; left.
  exists 1, pos. split; [left; reflexivity | right]. unfold in_zr, shadow_addr. cbn [fst snd].
  change (fs_frame_bytes 1 / 8) with 16. lia. }
try (set (mdvx := with_vm_backing _ _ _) in *; clearbody mdvx).
lazymatch goal with Hfr : frame_of E1 _ (mrestrict _ memc) (mrestrict _ ?m1) |- _ =>
  pose proof (kept_of_frame (segs:=SEGS) E1 _ (w_H Wc) memc m1
    (fun a => SHADOW_OFF + frame_addr lyc 1 pos / 8 + 4 <= a < SHADOW_OFF + frame_addr lyc 1 pos / 8 + 8) Hfr
    ltac:(s3_kof1 U25)) as KH end.
(* buf[32]'s four shadow bytes are 0 *)
pose proof (st_ok_region_nth E1 _ _ 0%nat _ HS eq_refl) as HRg. cbn [ms_mem restrict mkst] in HRg.
assert (HBUFx : sa_buf0 (rdW Wc (ms_mem ms)) (frame_addr lyc 1 pos)).
{ intros i Hi. apply s3_byte_of_aval. apply s3_aval_of_val_mem.
  replace (SHADOW_OFF + frame_addr lyc 1 pos / 8 + 4 + i) with (SHADOW_OFF + frame_addr lyc 1 pos / 8 + (4 + i)) by lia.
  assert (Hi' : 4 + i = 4 \/ 4 + i = 5 \/ 4 + i = 6 \/ 4 + i = 7) by lia.
  destruct Hi' as [Ho | [Ho | [Ho | Ho]]]; rewrite Ho;
  lazymatch goal with |- val_mem _ _ (_ + ?od) _ _ =>
    exact (field_of_region E1 _ 25%nat _ _ _ _ _ _ od 1%N (SLit 0) 0 HRg U25
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(lia)) end. }
(* the registers at the entry of xstrdup *)
prreg HS (10%bv : bv 5) A10. prreg HS (1%bv : bv 5) A1.
prreg HS (2%bv : bv 5) A2. prreg HS (3%bv : bv 5) A3. prreg HS (4%bv : bv 5) A4. prreg HS (8%bv : bv 5) A8.
prreg HS (9%bv : bv 5) A9. prreg HS (18%bv : bv 5) A18. prreg HS (19%bv : bv 5) A19. prreg HS (20%bv : bv 5) A20.
prreg HS (21%bv : bv 5) A21. prreg HS (22%bv : bv 5) A22. prreg HS (23%bv : bv 5) A23.
prreg HS (25%bv : bv 5) A25. prreg HS (26%bv : bv 5) A26. prreg HS (27%bv : bv 5) A27.
rewrite (EE1 24%nat 24%bv eq_refl), R24 in A10.
rewrite (EE1 2%nat 2%bv eq_refl) in A2. rewrite (EE1 3%nat 3%bv eq_refl) in A3.
rewrite (EE1 4%nat 4%bv eq_refl) in A4. rewrite (EE1 8%nat 8%bv eq_refl) in A8.
rewrite (EE1 9%nat 9%bv eq_refl) in A9. rewrite (EE1 18%nat 18%bv eq_refl) in A18.
rewrite (EE1 19%nat 19%bv eq_refl) in A19. rewrite (EE1 20%nat 20%bv eq_refl) in A20.
rewrite (EE1 21%nat 21%bv eq_refl) in A21. rewrite (EE1 22%nat 22%bv eq_refl) in A22.
rewrite (EE1 23%nat 23%bv eq_refl) in A23. rewrite (EE1 25%nat 25%bv eq_refl) in A25.
rewrite (EE1 26%nat 26%bv eq_refl) in A26. rewrite (EE1 27%nat 27%bv eq_refl) in A27.
pmkst HS.
exact (sa3_cont B MT HB LAWS MTL SIGP PRW IMG FXR
  TXSTRDUP TARG_I HA2 ly S W regs mem md ch pu id pp pc uri placement client R O
  lyc Sc Wc regs1 memc mdc pos (ms_regs ms) (ms_mem ms) mdvx HCX0 HM10 HJ1 KH HBUFx (eq_trans A10 H10) A1
  A2 A3 A4 A8 A9 A18 A19 A20 A21 A22 A23 A25 A26 A27).
Qed.
End e.
End f.
End d.
