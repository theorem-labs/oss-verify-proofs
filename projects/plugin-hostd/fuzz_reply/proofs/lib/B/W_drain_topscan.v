(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the SLOT SCAN of the image-B (fuzz_reply.asan-ubsan) TOP head of
   fuzz_reply's drain (source_of's search of g_s for the relay entry's fd), on the cuts of
   lib/B/W_drain_tophead.v (DT1, DSC; FROZEN) and lib/B/W_drain_topb_cx.v (DT2; FROZEN):
     dt_scan_entry  DT1 0x83438 -> DSC i = 0 at 0x83498: the three shadow checks of the entry's buf / used
                    granules (frame 200 / 224 / 232), s->used and s->buf, the pointer-overflow trap
                    `bltu buf+used, buf` at 0x83468 (refuted: no wrap, buf and used are in band) and the
                    null-consistency trap at 0x8346c-0x83478 (decided from buf's atom fact), the shadow check of
                    the cap granule (frame 216), s->cap, s->fd and the shadow base (frame 240) into s3.
     dt_scan_step   DSC i -> DSC (S i) | DT2 0x83524: the two zero shadow loads of g_s[i] (HGSZ), the open test
                    `beqz a1` at 0x834ac and the fd test `beq a1,a4` at 0x834c0.  For i <> j, aothers_at gives
                    open = 0 or a different fd, so the body goes on to 0x834c4 and back to 0x83498 with
                    i + 1 <= j; for i = j, asrc_at at dHA gives open = 1 and fd = hs_fd = re_fd (DSAME, DBASE),
                    so the body reaches 0x83524.  The not-found exit 0x834d0 is refuted (i <= j < 4).
   The walk is the engine's (W_kit paj_run_tok / paj_run_to_tok / psrr_branch_tok), in the form of
   dt_nogrow (W_drain_tophead.v); its structure follows lib/A/W_drain_top.v's dt_scan / dt_scan_step
   (a working branch 752503c26ca), re-derived for B's code and registers. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame W_drain_cx W_drain_topb_cx
W_drain_tophead.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Variable CTX_R : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

#[local] Notation dt_sh m c := (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 35 0)).
#[local] Notation dt_gv c := (SAlu ALU_SRL (SOff 8 c) (SLit 3)).
#[local] Notation BxT := (SOff 35 0).

(* a register read off a symbolic state (W_drain_tophead.v's dt_reg, which is local to its section) *)
Ltac ts_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* no byte is in a region's write window: every region of a read-only stretch has whi <= wlo *)
Lemma ts_nowr_lem : forall E (rs : smem),
forallb (fun r => Z.leb (YP09.r_whi r) (YP09.r_wlo r)) rs = true -> forall x, ~ in_wrange E rs x.
Proof.
intros E rs HF x (r & Hin & Hr).
rewrite forallb_forall in HF. pose proof (HF r Hin) as Hq. apply Z.leb_le in Hq. lia.
Qed.

(* ---- The relay entry's fd and buf fields (dt_entry_used / dt_entry_cap's form). ---- *)
Lemma ts_entry_buf : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_buf e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) (SA + 16) 8 (re_buf e).
Proof.
intros W m SA e Hp1 Hv H.
unfold entry_bytes in H. rewrite !dt_bzs_app, !app_assoc in H.
do 5 (apply garr8_app in H as [H _]). apply garr8_app in H as [_ H].
rewrite (dt_le8_bytes (re_buf e) Hv) in H.
apply (dt_val_of_garr8 RG HGSB W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hv|].
apply (dt_garr8_at _ _ _ _ H).
rewrite ?length_app, ?dt_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes. cbn [length].
lia.
Qed.
Lemma ts_entry_fd : forall (W : world SEGS) m SA e,
0 <= re_fd e < 2 ^ 32 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> val_mem SEGS (arm W m) SA 4 (re_fd e).
Proof.
intros W m SA e Hv H.
unfold entry_bytes in H. rewrite !dt_bzs_app, !app_assoc in H.
do 8 (apply garr8_app in H as [H _]). apply garr8_app in H as [H _].
rewrite (dt_le4_bytes RG (re_fd e) Hv) in H.
apply (dt_val_of_garr8 RG HGSB W m _ 4 _); [change (8 * Z.of_nat 4) with 32; exact Hv | exact H].
Qed.

(* ---- Values the entry stretch leaves in a0 / a3 / a4. ---- *)
Lemma ts_den_add2 : forall E (n m : nat) v w, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 w ->
0 <= v -> 0 <= w -> v + w < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = w64 (v + w).
Proof.
intros E n m v w Hn Hm Hv Hw Hvw. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn) by lia. rewrite (U_atom E m w Hm) by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma ts_den_sx : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
sv_denot E (SExt true 32 (SOff n 0)) = w64 v.
Proof.
intros E n v Hn Hv. apply bv_eq. rewrite U_sext32'.
assert (HU : bv_unsigned (sv_denot E (SOff n 0)) = v) by exact (U_atom E n v Hn ltac:(lia)).
rewrite HU, (sx32_small v) by lia. unfold w64. symmetry. apply unsigned_lit_small. lia.
Qed.
Lemma ts_den_room : forall E cap used,
ew E 33 = Z_to_bv 64 cap -> ew E 34 = Z_to_bv 64 used -> 0 <= used <= cap -> cap <= 16384 ->
sv_denot E (SAlu ALU_ADD (SOff 33 0) (SMd M_MUL (SOff 34 0) (SLit (-1)))) = w64 (cap - used).
Proof.
intros E cap used H33 H34 Hu Hc. rewrite denot_lit_U. unfold w64. f_equal.
apply (dt_U_room RG HGSB E cap used); [rewrite H33; apply unsigned_lit_small; lia
                                      |rewrite H34; apply unsigned_lit_small; lia | lia | lia].
Qed.
(* the pointer-overflow trap `bltu buf+used, buf` (0x83468): no wrap, so never taken (W_traps.v trap_ptr_bltu's
   form, on the engine's sum of the two atoms) *)
Lemma ts_bltu_nowrap : forall E (n m : nat) v w, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 w ->
0 <= v -> 0 <= w -> v + w < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0))) (sv_denot E (SOff m 0)) = false.
Proof.
intros E n m v w Hn Hm Hv Hw Hvw. rewrite branch_ltu_U.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn) by lia. rewrite (U_atom E m w Hm) by lia.
rewrite zcanon_id by (unfold M64; lia). apply Z.ltb_ge. lia.
Qed.

(* ---- The symbolic state at DT1 (0x83438) for the stretch to the scan's head 0x83498. ----
   Registers as dt_nogrow's ss_ng (dt_regs_top); frame chunks 200 / 216 / 224 / 232 (the shadow addresses of
   SA, SA + 32, SA + 16, SA + 24) and 240 (the shadow base); the entry's fd / buf / used / cap; extras
   32 = SA, 33 = cap, 34 = used, 35 = SHADOW_OFF, 36 = buf, 37 = fd.  buf carries the pointer fact
   (W_traps.v recipe R1) from DT1's dinband. *)
Definition ts_PTRF : afact := mkAF 4096 140737479966720 3.
Definition ts_en_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 352 0 0
  [ YP09.mkChunk 200 (dt_shA 32 0); YP09.mkChunk 216 (dt_shA 32 32); YP09.mkChunk 224 (dt_shA 32 16);
    YP09.mkChunk 232 (dt_shA 32 24); YP09.mkChunk 240 (CVal 8 (SOff 35 0)) ].
Definition ts_en_sa : YP09.region := YP09.mkRegion (Some 32%nat) 0 56 0 0
  [ YP09.mkChunk 0 (CVal 4 (SOff 37 0)); YP09.mkChunk 16 (CVal 8 (SOff 36 0));
    YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0)) ].
Definition ts_en_facts : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (35%nat, mkAF SB SB 0); (8%nat, dt_IMGF);
    (32%nat, dt_HEAPF); (33%nat, mkAF 0 16384 0); (34%nat, mkAF 0 16384 0); (36%nat, ts_PTRF) ] [] [].
Definition ss_en : sstate := mkSS A_dr_mid dt_regs_top [ ts_en_frame; ts_en_sa ] None ts_en_facts.
Definition ts_en_extra (SA cap used buf fd : Z) : list word :=
  map (Z_to_bv 64) [SA; cap; used; SHADOW_OFF; buf; fd].

Theorem dt_scan_entry : dt_scan_entry_stmt B MT MMAX RG.
Proof.
intros cx sg D W1 c1 HB HD1 K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HD1 as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hregs & HMEM & HnoNUL & Hused & Hband & HLINK & HSAME & HHIST & HJ1 & Hroom & Hlater & Hbud).
pose proof Hregs as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HMEM as (HJ & _ & _ & _ & HFR & Hgarr & _ & HEOK & _ & _ & _ & _ & _ & Hperm).
pose proof HB as (Hafn & _ & _ & _ & HSAhi & HSA8 & _).
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HDS : DRAIN_STK = 16880) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 16880 <= dsp0 cx) by (unfold dsp0; clear - Hceil Hslo; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; clear - Hshi H47; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
clear Hafn Hstk Hal16 Hceil Hslo Hshi H47.
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2. unfold IMG_TOP in HGS2.
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
pose proof HB as (_ & _ & _ & HGle & _).
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; clear - HG4096 HGle; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; clear - HGceil HSAhi; lia).
pose proof HEOK as (_ & _ & Hpad1 & _ & Hfdv & Hcapv & HUlen & Hucap & _).
assert (Hcapb : 0 <= re_cap e1 <= 16384) by (clear - Hcapv; destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Husedb : 0 <= re_used e1 <= re_cap e1)
  by (clear - HUlen Hucap; pose proof (Nat2Z.is_nonneg (length (re_U e1))); lia).
clear Hcapv.
pose proof Hband as (Hbuf1 & Hbuf2 & Hbuf8). unfold DCEIL in Hbuf2.
subst c1. unfold cfg_at, w64.
remember (Eimg (Ereg regs1 (ts_en_extra (dxSA cx) (re_cap e1) (re_used e1) (re_buf e1) (re_fd e1))))
  as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs1 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs1 4) by (apply EREG; [lia | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_cap e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (re_buf e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (re_fd e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (BSA : 0 <= dxSA cx < 2 ^ 64) by (clear - HSAlo HSAcl C1; lia).
assert (BGS : 0 <= rg_s RG < 2 ^ 64) by (clear - HGS1 HGS2; lia).
assert (BSH : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; lia).
assert (Bcap : 0 <= re_cap e1 < 2 ^ 64) by (clear - Hcapb; lia).
assert (Bused : 0 <= re_used e1 < 2 ^ 64) by (clear - Husedb Hcapb; lia).
assert (Bbuf : 0 <= re_buf e1 < 2 ^ 64) by (clear - Hbuf1 Hbuf2 Hcapb; lia).
assert (Bfd : 0 <= re_fd e1 < 2 ^ 64) by (clear - Hfdv; lia).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG) by (rewrite E8; apply unsigned_lit_small; exact BGS).
assert (U35 : bv_unsigned (ew E 35) = SHADOW_OFF) by (rewrite E35; apply unsigned_lit_small; exact BSH).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; exact BSA).
assert (U33 : bv_unsigned (ew E 33) = re_cap e1) by (rewrite E33; apply unsigned_lit_small; exact Bcap).
assert (U34 : bv_unsigned (ew E 34) = re_used e1) by (rewrite E34; apply unsigned_lit_small; exact Bused).
assert (U36 : bv_unsigned (ew E 36) = re_buf e1) by (rewrite E36; apply unsigned_lit_small; exact Bbuf).
assert (R21' : getr regs1 21 = sv_denot E (SOff 32 0))
  by (rewrite (den_atom0 E 32 (dxSA cx) E32 BSA); exact R21).
assert (R24' : getr regs1 24 = sv_denot E (SOff 32 8))
  by (rewrite (den_atom E 32 (dxSA cx) 8 E32 ltac:(clear - BSA HSAcl C1; lia) BSA); exact R24).
assert (R20' : getr regs1 20 = sv_denot E (SOff 32 16))
  by (rewrite (den_atom E 32 (dxSA cx) 16 E32 ltac:(clear - BSA HSAcl C1; lia) BSA); exact R20).
assert (R22' : getr regs1 22 = sv_denot E (SOff 32 24))
  by (rewrite (den_atom E 32 (dxSA cx) 24 E32 ltac:(clear - BSA HSAcl C1; lia) BSA); exact R22).
assert (R27' : getr regs1 27 = sv_denot E (SOff 32 32))
  by (rewrite (den_atom E 32 (dxSA cx) 32 E32 ltac:(clear - BSA HSAcl C1; lia) BSA); exact R27).
assert (R9' : getr regs1 9 = sv_denot E (dt_gv 0))
  by (rewrite (dt_den_gv RG E (rg_s RG) 0 E8 BGS ltac:(clear - BGS; lia)), Z.add_0_r; exact R9).
assert (R18' : getr regs1 18 = sv_denot E (dt_gv 4))
  by (rewrite (dt_den_gv RG E (rg_s RG) 4 E8 BGS ltac:(clear - HGS1 HGS2; lia)); exact R18).
assert (R26' : getr regs1 26 = sv_denot E (SLit 384))
  by (rewrite denot_lit_U, U_lit by (clear; lia); exact R26).
pose proof HFR as (G8 & G32 & G40 & G48 & G56 & G64 & G72 & G80 & G88 & G104 & G120 & G128 & G136 &
  G144 & G152 & G176 & G184 & G200 & G208 & G216 & G224 & G232 & G240 & Gsaved).
assert (HS : st_ok_pi SEGS VAL E ss_en
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_mid)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_en. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R21' | exact R24' | exact R20' | exact R22' | exact R27'
              | exact R9' | exact R18' | exact R26' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, ts_en_frame, ts_en_sa;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp.
      split; [unfold DRAIN_FRAME; clear - HspA C1; lia|]. split; [unfold DRAIN_FRAME; clear - HspB; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      assert (Hsh : forall c, 0 <= c <= 56 -> 0 <= shadow_addr (dxSA cx + c) < 2 ^ (8 * Z.of_N 8)).
      { intros c Hc. unfold shadow_addr, SHADOW_OFF. change (8 * Z.of_N 8) with 64.
        assert (Hq1 : 0 <= (dxSA cx + c) / 8) by (apply Z.div_pos; clear - Hc HSAlo; lia).
        assert (Hq2 : (dxSA cx + c) / 8 <= dxSA cx + c) by (apply Z.div_le_upper_bound; clear - Hc HSAlo; lia).
        clear - Hq1 Hq2 Hc HSAcl C1. lia. }
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
      * apply (chunk_ok_val SEGS E _ _ 200 8 (dt_sh 32 0) (shadow_addr (dxSA cx)));
          [ rewrite (dt_den_sh RG E 32 (dxSA cx) 0 E32 E35 BSA ltac:(clear - BSA; lia)), Z.add_0_r;
            reflexivity
          | pose proof (Hsh 0 ltac:(clear; lia)) as Hq; rewrite Z.add_0_r in Hq; exact Hq
          | zside
          | exact G200 ].
      * apply (chunk_ok_val SEGS E _ _ 216 8 (dt_sh 32 32) (shadow_addr (dxSA cx + 32)));
          [ exact (dt_den_sh RG E 32 (dxSA cx) 32 E32 E35 BSA ltac:(clear - BSA HSAcl C1; lia))
          | exact (Hsh 32 ltac:(clear; lia))
          | zside
          | exact G216 ].
      * apply (chunk_ok_val SEGS E _ _ 224 8 (dt_sh 32 16) (shadow_addr (dxSA cx + 16)));
          [ exact (dt_den_sh RG E 32 (dxSA cx) 16 E32 E35 BSA ltac:(clear - BSA HSAcl C1; lia))
          | exact (Hsh 16 ltac:(clear; lia))
          | zside
          | exact G224 ].
      * apply (chunk_ok_val SEGS E _ _ 232 8 (dt_sh 32 24) (shadow_addr (dxSA cx + 24)));
          [ exact (dt_den_sh RG E 32 (dxSA cx) 24 E32 E35 BSA ltac:(clear - BSA HSAcl C1; lia))
          | exact (Hsh 24 ltac:(clear; lia))
          | zside
          | exact G232 ].
      * apply (chunk_ok_val SEGS E _ _ 240 8 (SOff 35 0) SHADOW_OFF);
          [ exact (den_atom0 E 35 SHADOW_OFF E35 BSH) | unfold SHADOW_OFF; zside | zside | exact G240 ].
    + cbn [base_val]. rewrite U32. split; [clear - BSA HSAlo HSAcl C1; lia|].
      split; [clear - BSA HSAlo HSAcl C1; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      * apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 37 0) (re_fd e1));
          [ exact (den_atom0 E 37 (re_fd e1) E37 Bfd) | clear - Hfdv; zside | zside | ].
        rewrite Z.add_0_r. exact (ts_entry_fd W1 m1 (dxSA cx) e1 ltac:(clear - Hfdv; lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 36 0) (re_buf e1));
          [ exact (den_atom0 E 36 (re_buf e1) E36 Bbuf) | clear - Bbuf; zside | zside | ].
        exact (ts_entry_buf W1 m1 (dxSA cx) e1 Hpad1 Bbuf Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 34 0) (re_used e1));
          [ exact (den_atom0 E 34 (re_used e1) E34 Bused) | clear - Bused; zside | zside | ].
        exact (dt_entry_used RG HGSB W1 m1 (dxSA cx) e1 Hpad1 Bused Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 33 0) (re_cap e1));
          [ exact (den_atom0 E 33 (re_cap e1) E33 Bcap) | clear - Bcap; zside | zside | ].
        exact (dt_entry_cap RG HGSB W1 m1 (dxSA cx) e1 Hpad1 Bcap Hgarr).
  - apply pairwise_disjoint_of_extents. unfold ts_en_frame, ts_en_sa, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1. clear. unfold DRAIN_FRAME.
    intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [ts_en_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF, ts_PTRF.
    cbn [af_lo af_hi af_al2].
    rewrite Usp, U8, U35, U32, U33, U34, U36.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8 Hcapb Husedb Hbuf1 Hbuf2 Hbuf8. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME, IMG_TOP.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHng E (mrestrict (w_H W1) m1)).
{ unfold SHng, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (dt_shent_sub B RG LAWS HGSB ly1 S1 W1 m1 md1 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR HtblC).
  - exact (U_atom E 35 SHADOW_OFF E35 BSH).
  - exact (U_atom E 32 (dxSA cx) E32 BSA).
  - clear - HGle. lia.
  - clear. lia.
  - rewrite RQT. unfold AENT, ATABLE in HSAhi. clear - HSAhi. lia. }
paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
psrr_branch_tok RUN BR HS SHOK DBspan.
{ (* 0x83468 taken: the pointer-overflow trap, refuted *)
  rewrite (ts_bltu_nowrap E 34 36 (re_used e1) (re_buf e1) E34 E36 ltac:(clear - Husedb; lia)
    ltac:(clear - Hbuf1; lia) ltac:(clear - Husedb Hcapb Hbuf2; lia)) in Hc.
  discriminate Hc. }
paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
rewrite ?wvb_collapse in HJ.
lazymatch type of HFr with frame_of _ ?rs _ _ =>
  assert (N0 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
  assert (N1 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
{ intros a.
  rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
  exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
  by (intros a Ha; exact (apresent_grows _ _ _ _ HG1 (apresent_grows _ _ _ _ HG0 Ha))).
ts_reg HS (2%bv : bv 5) X2. ts_reg HS (3%bv : bv 5) X3. ts_reg HS (4%bv : bv 5) X4.
ts_reg HS (8%bv : bv 5) X8. ts_reg HS (9%bv : bv 5) X9. ts_reg HS (10%bv : bv 5) X10.
ts_reg HS (12%bv : bv 5) X12. ts_reg HS (13%bv : bv 5) X13. ts_reg HS (14%bv : bv 5) X14.
ts_reg HS (18%bv : bv 5) X18. ts_reg HS (19%bv : bv 5) X19. ts_reg HS (20%bv : bv 5) X20.
ts_reg HS (21%bv : bv 5) X21. ts_reg HS (22%bv : bv 5) X22. ts_reg HS (24%bv : bv 5) X24.
ts_reg HS (26%bv : bv 5) X26. ts_reg HS (27%bv : bv 5) X27.
pmkst HS.
apply K. unfold DSC.
eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
split; [reflexivity|].
split.
{ unfold dregs_top.
  split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp|].
  split; [rewrite X3, (dt_den_reg E 3 _ E3); exact R3|].
  split; [rewrite X4, (dt_den_reg E 4 _ E4); exact R4|].
  split; [rewrite X21; exact (eq_trans (eq_sym R21') R21)|].
  split; [rewrite X24; exact (eq_trans (eq_sym R24') R24)|].
  split; [rewrite X20; exact (eq_trans (eq_sym R20') R20)|].
  split; [rewrite X22; exact (eq_trans (eq_sym R22') R22)|].
  split; [rewrite X27; exact (eq_trans (eq_sym R27') R27)|].
  split; [rewrite X8, (dt_den_reg E 8 _ E8); reflexivity|].
  split; [rewrite X9; exact (eq_trans (eq_sym R9') R9)|].
  split; [rewrite X18; exact (eq_trans (eq_sym R18') R18)
         |rewrite X26; exact (eq_trans (eq_sym R26') R26)]. }
split.
{ rewrite X10, (ts_den_add2 E 34 36 (re_used e1) (re_buf e1) E34 E36 ltac:(clear - Husedb; lia)
    ltac:(clear - Hbuf1; lia) ltac:(clear - Husedb Hcapb Hbuf2; lia)).
  unfold w64. f_equal. clear. lia. }
split; [rewrite X13; exact (ts_den_room E (re_cap e1) (re_used e1) E33 E34 ltac:(clear - Husedb; lia)
  ltac:(clear - Hcapb; lia))|].
split; [rewrite X14; exact (ts_den_sx E 37 (re_fd e1) E37 Hfdv)|].
split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal|].
split; [rewrite X19, (dt_den_reg E 35 _ E35); unfold w64; f_equal; cbn [Z.of_nat]; clear; lia|].
split; [clear; lia|].
split; [exact (dt_DMEM_kept B RG HGSB cx ly1 S1 W1 m1 (ms_mem ms0) md1 _ k1 k1 e1 h1 sg out1 ev1
  (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
split; [exact HLINK|]. split; [exact HSAME|].
split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
split; [exact Hlater | exact Hbud].
Qed.

(* ---- The scan body at slot i (0x83498 .. 0x834cc). ----
   The other three slots, with the values the machine compares: aothers_at gives each slot's fd and open as
   4-byte values and the fd test as `f mod 2 ^ 32 <> fd mod 2 ^ 32`, which is what `beq a1,a4` at 0x834c0
   decides; val_mem keeps only v mod 2 ^ 32, so the canonical witnesses hold just as well. *)
Lemma ts_val_mod : forall m a (n : nat) v,
val_mem SEGS m a n v -> val_mem SEGS m a n (v mod 2 ^ (8 * Z.of_nat n)).
Proof.
intros m a n v H k Hk. rewrite (H k Hk). f_equal. f_equal.
unfold YO0f.le_byte. rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma ts_others_canon : forall (W1 : world SEGS) m1 (j : nat) (fd : Z) i,
aothers_at RG W1 m1 j fd -> (i < 4)%nat -> i <> j -> 0 <= fd < 2 ^ 31 ->
exists f o, val_mem SEGS (arm W1 m1) (rg_s RG + ASRC * Z.of_nat i) 4 f /\
            val_mem SEGS (arm W1 m1) (rg_s RG + ASRC * Z.of_nat i + 4) 4 o /\
            0 <= f < 2 ^ 32 /\ 0 <= o < 2 ^ 32 /\ (o = 0 \/ f mod 2 ^ 32 <> fd mod 2 ^ 32).
Proof.
intros W1 m1 j fd i Hoth Hi4 Hne Hfd.
destruct (Hoth i Hi4 Hne) as (f & o & V1 & V2 & Hdis).
exists (f mod 2 ^ 32), (o mod 2 ^ 32).
assert (HM : 2 ^ (8 * Z.of_nat 4) = 2 ^ 32) by reflexivity.
split; [pose proof (ts_val_mod _ _ 4%nat f V1) as Hq; rewrite HM in Hq; exact Hq|].
split; [pose proof (ts_val_mod _ _ 4%nat o V2) as Hq; rewrite HM in Hq; exact Hq|].
split; [apply Z.mod_pos_bound; lia|].
split; [apply Z.mod_pos_bound; lia|].
destruct Hdis as [Hq|Hq]; [left; rewrite Hq; reflexivity | right].
rewrite Z.mod_mod by lia. exact Hq.
Qed.

(* a register re-expressed by another symbolic value with the same denotation *)
Lemma ts_reseat : forall E ss ms (r : bv 5) e,
st_ok_pi SEGS VAL E ss ms -> getr (ms_regs ms) r = sv_denot E e -> bv_eqb r 0 = false ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs SEGS E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
  (ss_facts ss)) ms (sr_set (ss_regs ss) r e) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. pose proof (st_ok_reg SEGS E _ ms r HS) as Hq.
  cbn [ss_regs] in Hq. rewrite <- Hq, Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

(* the 4 * 96 bytes of g_s as the walk's shadow-entry obligation (HGSZ) *)
Lemma ts_shent_azs : forall ly S (W : world SEGS) mem md E (m : nat) q n,
AR SEGS B ly S W mem md -> azs B q n -> U E BxT = SHADOW_OFF -> U E (SOff m 0) = q ->
0 <= n -> 0x10000 <= q -> q + n <= IMG_TOP ->
shent_ok SEGS BxT E (mrestrict (w_H W) mem) (mkSHE m 0 n).
Proof.
intros ly S W mem md E m q n HAR Hz HB Hm Hn Hq1 Hq2.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of SEGS).
split.
- rewrite Z.add_0_r, Z.sub_0_r. exact (azs_range_addressable B LAWS ly S W mem md q n HAR Hz).
- intros a Ha. unfold SHADOW_OFF, IMG_TOP in *. lia.
Qed.

(* the scan's shadow address ((g + c) >> 3) + (SB + 12 i), with g 8-aligned and c < 8, is
   shadow(g + 96 i + c): the form the engine reads a zero-shadow load from *)
Lemma ts_den_add_sh : forall E (n : nat) g c i,
ew E n = Z_to_bv 64 ((g + c) / 8) -> ew E 19 = Z_to_bv 64 (SHADOW_OFF + 12 * i) ->
ew E 8 = Z_to_bv 64 g -> ew E 35 = Z_to_bv 64 SHADOW_OFF ->
g mod 8 = 0 -> 0 <= c < 8 -> 0x10000 <= g -> g + 384 <= IMG_TOP -> 0 <= i < 4 ->
sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff 19 0)) = sv_denot E (dt_sh 8 (96 * i + c)).
Proof.
intros E n g c i Hn H19 H8 H35 Hg8 Hc Hg1 Hg2 Hi. unfold IMG_TOP in Hg2.
assert (Hk : g = 8 * (g / 8)) by (pose proof (Z_div_mod_eq_full g 8); lia).
assert (Hgc : (g + c) / 8 = g / 8).
{ rewrite Hk at 1. rewrite Z.mul_comm, Z.div_add_l by lia. rewrite (Z.div_small c 8) by lia. lia. }
assert (Hgi : (g + (96 * i + c)) / 8 = g / 8 + 12 * i).
{ replace (g + (96 * i + c)) with ((g / 8 + 12 * i) * 8 + c) by lia.
  rewrite Z.div_add_l by lia. rewrite (Z.div_small c 8) by lia. lia. }
assert (Hg0 : 0 <= g / 8 <= g) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite (denot_lit_U E (SAlu ALU_ADD (SOff n 0) (SOff 19 0))), (denot_lit_U E (dt_sh 8 (96 * i + c))).
f_equal.
rewrite (dt_U_sh RG E 8 g (96 * i + c) H8 H35) by lia. unfold shadow_addr. rewrite Hgi.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n ((g + c) / 8) Hn) by lia.
rewrite (U_atom E 19 (SHADOW_OFF + 12 * i) H19) by (unfold SHADOW_OFF; lia).
rewrite Hgc. rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

(* the scan's two tests on 4-byte fields: g_s[i].open (0x834ac) and g_s[i].fd against s->fd (0x834c0) *)
Lemma ts_beqz_sx : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E n v Hn Hv. rewrite branch_eq_U. unfold U. rewrite U_sext32'.
assert (HU : bv_unsigned (sv_denot E (SOff n 0)) = v) by exact (U_atom E n v Hn ltac:(lia)).
assert (HL : bv_unsigned (sv_denot E (SLit 0)) = 0) by exact (U_lit E 0 ltac:(lia)).
rewrite HU, HL. destruct (Z.eqb_spec v 0) as [->|Hne].
- rewrite (sx32_small 0) by lia. reflexivity.
- destruct (Z.eqb_spec (sx32 v) 0) as [He|He]; [|reflexivity].
  exfalso. apply (proj1 (sx32_zero_iff_u32 v Hv)) in He. lia.
Qed.
Lemma ts_beq_sx : forall E (n m : nat) v w,
ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 w -> 0 <= v < 2 ^ 32 -> 0 <= w < 2 ^ 31 ->
branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SOff m 0)) = (v =? w).
Proof.
intros E n m v w Hn Hm Hv Hw. rewrite branch_eq_U. unfold U. rewrite U_sext32'.
assert (HU : bv_unsigned (sv_denot E (SOff n 0)) = v) by exact (U_atom E n v Hn ltac:(lia)).
assert (HW : bv_unsigned (sv_denot E (SOff m 0)) = w) by exact (U_atom E m w Hm ltac:(lia)).
rewrite HU, HW.
destruct (Z.eqb_spec v w) as [->|Hne].
- rewrite (sx32_small w) by lia. apply Z.eqb_refl.
- apply Z.eqb_neq. intros He. rewrite <- (sx32_small w) in He by lia.
  apply (sx32_inj_u32 v w Hv ltac:(lia)) in He. lia.
Qed.

(* ---- The scan body's own symbolic state at 0x83498 (slot i). ----
   Every register keeps its own atom except a2 = 96 i and s10 = 384 (literals, so that &g_s[i] is g_s + 96 i
   and the loop test is decided); the extras are 32 = g_s[0].fd, 33 = g_s[0].open, 34 = g_s[1].fd,
   35 = SHADOW_OFF (the shadow base BxT, as in dt_nogrow), 36 = g_s[1].open, 37 = g_s[2].fd,
   38 = g_s[2].open, 39 = g_s[3].fd, 40 = g_s[3].open.  The two shadow addresses the body computes
   (s2 + s3 = (g_s + 4) / 8 + SB + 12 i and s1 + s3 = g_s / 8 + SB + 12 i) are re-expressed before their
   loads as shadow(g_s + 96 i + 4) and shadow(g_s + 96 i) (ts_reseat). *)
Definition ts_shl1 : Z := AF_fr_drain + 0x224.   (* 0x8349c, the shadow load of &g_s[i].open *)
Definition ts_shl2 : Z := AF_fr_drain + 0x23c.   (* 0x834b4, the shadow load of &g_s[i].fd *)
Definition ts_dsc_gs : YP09.region := YP09.mkRegion (Some 8%nat) 0 384 0 0
  [ YP09.mkChunk 0 (CVal 4 (SOff 32 0)); YP09.mkChunk 4 (CVal 4 (SOff 33 0));
    YP09.mkChunk 96 (CVal 4 (SOff 34 0)); YP09.mkChunk 100 (CVal 4 (SOff 36 0));
    YP09.mkChunk 192 (CVal 4 (SOff 37 0)); YP09.mkChunk 196 (CVal 4 (SOff 38 0));
    YP09.mkChunk 288 (CVal 4 (SOff 39 0)); YP09.mkChunk 292 (CVal 4 (SOff 40 0)) ].
Definition ts_dsc_facts : facts := mkFacts [ (35%nat, mkAF SB SB 0); (8%nat, dt_IMGF) ] [] [].
Definition ss_dsc (i : nat) : sstate :=
  mkSS A_dr_scan (sr_set (sr_set sr_atoms 12%bv (SLit (96 * Z.of_nat i))) 26%bv (SLit 384))
    [ ts_dsc_gs ] None ts_dsc_facts.
Definition SHdsc : list shent := [ mkSHE 8 0 384 ].
Definition ts_dsc_extra (f0 o0 f1 o1 f2 o2 f3 o3 : Z) : list word :=
  map (Z_to_bv 64) [f0; o0; f1; SHADOW_OFF; o1; f2; o2; f3; o3].


(* dregs_top at the cut: every one of its registers is its own atom in the scan's state, so the walk only has
   to show that the register is unchanged *)
Lemma ts_dregs_eq : forall cx (r1 r2 : bvmap 5 word),
dregs_top RG cx r1 ->
getr r2 2 = getr r1 2 -> getr r2 3 = getr r1 3 -> getr r2 4 = getr r1 4 ->
getr r2 8 = getr r1 8 -> getr r2 9 = getr r1 9 -> getr r2 18 = getr r1 18 ->
getr r2 20 = getr r1 20 -> getr r2 21 = getr r1 21 -> getr r2 22 = getr r1 22 ->
getr r2 24 = getr r1 24 -> getr r2 26 = getr r1 26 -> getr r2 27 = getr r1 27 ->
dregs_top RG cx r2.
Proof.
intros cx r1 r2 (Hs & H3 & H4 & H21 & H24 & H20 & H22 & H27 & H8 & H9 & H18 & H26)
  K2 K3 K4 K8 K9 K18 K20 K21 K22 K24 K26 K27.
unfold dregs_top, spZ in *.
rewrite K2, K3, K4, K8, K9, K18, K20, K21, K22, K24, K26, K27.
repeat split; assumption.
Qed.


Theorem dt_scan_step : dt_scan_step_stmt B MT MMAX RG.
Proof.
intros cx sg D i W1 c1 HB HDSC Knext Kfound.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
destruct HDSC as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hregs & R10 & R13 & R14 & R12 & R19 & Hij & HMEM & HnoNUL & Hused & Hband & HLINK & HSAME &
  HHIST & HJ1 & Hroom & Hlater & Hbud).
pose proof Hregs as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HMEM as (HJ & _ & _ & _ & _ & _ & _ & HEOK & Hsrc & Hoth & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hj4 & _ & _ & HfdB & _).
pose proof HSAME as (Sfd & Seof & Shfd & _).
assert (Hfdv : 0 <= re_fd e1 < 2 ^ 31) by (pose proof HEOK as (_ & _ & _ & _ & Hq & _); exact Hq).
assert (Hfd : hs_fd h1 = re_fd e1) by (rewrite Shfd, HfdB; exact (eq_sym Sfd)).
assert (Hi4 : (i < 4)%nat) by (clear - Hij Hj4; lia).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2. unfold IMG_TOP in HGS2.
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
(* the four slots of g_s, as the scan reads them *)
assert (Hslot : forall ii, (ii < 4)%nat -> exists f o,
  val_mem SEGS (arm W1 m1) (rg_s RG + 96 * Z.of_nat ii) 4 f /\
  val_mem SEGS (arm W1 m1) (rg_s RG + 96 * Z.of_nat ii + 4) 4 o /\
  0 <= f < 2 ^ 32 /\ 0 <= o < 2 ^ 32 /\
  (ii = dxj cx -> f = re_fd e1 /\ o <> 0) /\
  (ii <> dxj cx -> o = 0 \/ f <> re_fd e1)).
{ intros ii Hii. destruct (Nat.eq_dec ii (dxj cx)) as [->|Hne].
  - pose proof Hsrc as (V1 & V2 & _ & _ & _ & _ & _ & Hopen & Hfdr & _).
    unfold dHA, ASRC in V1, V2.
    exists (hs_fd h1), (hs_open h1).
    split; [exact V1|]. split; [exact V2|]. split; [clear - Hfdr; lia|].
    split; [rewrite Hopen; clear; lia|].
    split; [intros _; split; [exact Hfd | rewrite Hopen; clear; lia]|]. intros Hcc; contradiction.
  - assert (HfdvX : 0 <= re_fd (dxe cx) < 2 ^ 31) by (rewrite <- Sfd; exact Hfdv).
    destruct (ts_others_canon W1 m1 (dxj cx) (re_fd (dxe cx)) ii Hoth Hii Hne HfdvX)
      as (f & o & V1 & V2 & Bf & Bo & Hdis).
    unfold ASRC in V1, V2.
    exists f, o. split; [exact V1|]. split; [exact V2|]. split; [exact Bf|]. split; [exact Bo|].
    split; [intros Hcc; contradiction|]. intros _. rewrite Sfd.
    destruct Hdis as [Hq|Hq]; [left; exact Hq|right].
    rewrite (Z.mod_small f (2 ^ 32)) in Hq by (clear - Bf; lia).
    rewrite (Z.mod_small (re_fd (dxe cx)) (2 ^ 32)) in Hq by (clear - HfdvX; lia). exact Hq. }
destruct (Hslot 0%nat ltac:(clear; lia)) as (f0 & o0 & V00 & V01 & B00 & B01 & Hjj0 & Hoo0).
destruct (Hslot 1%nat ltac:(clear; lia)) as (f1 & o1 & V10 & V11 & B10 & B11 & Hjj1 & Hoo1).
destruct (Hslot 2%nat ltac:(clear; lia)) as (f2 & o2 & V20 & V21 & B20 & B21 & Hjj2 & Hoo2).
destruct (Hslot 3%nat ltac:(clear; lia)) as (f3 & o3 & V30 & V31 & B30 & B31 & Hjj3 & Hoo3).
clear Hslot.
replace (rg_s RG + 96 * Z.of_nat 0) with (rg_s RG) in V00 by (clear; lia).
replace (rg_s RG + 96 * Z.of_nat 0 + 4) with (rg_s RG + 4) in V01 by (clear; lia).
replace (rg_s RG + 96 * Z.of_nat 1) with (rg_s RG + 96) in V10 by (clear; lia).
replace (rg_s RG + 96 * Z.of_nat 1 + 4) with (rg_s RG + 100) in V11 by (clear; lia).
replace (rg_s RG + 96 * Z.of_nat 2) with (rg_s RG + 192) in V20 by (clear; lia).
replace (rg_s RG + 96 * Z.of_nat 2 + 4) with (rg_s RG + 196) in V21 by (clear; lia).
replace (rg_s RG + 96 * Z.of_nat 3) with (rg_s RG + 288) in V30 by (clear; lia).
replace (rg_s RG + 96 * Z.of_nat 3 + 4) with (rg_s RG + 292) in V31 by (clear; lia).
subst c1. unfold cfg_at, w64.
remember (Eimg (Ereg regs1 (ts_dsc_extra f0 o0 f1 o1 f2 o2 f3 o3))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (Q2 : ew E 2 = getr regs1 2) by (apply EREG; [clear; lia | reflexivity]).
assert (Q3 : ew E 3 = getr regs1 3) by (apply EREG; [clear; lia | reflexivity]).
assert (Q4 : ew E 4 = getr regs1 4) by (apply EREG; [clear; lia | reflexivity]).
assert (Q8 : ew E 8 = getr regs1 8) by (apply EREG; [clear; lia | reflexivity]).
assert (Q9 : ew E 9 = getr regs1 9) by (apply EREG; [clear; lia | reflexivity]).
assert (Q10 : ew E 10 = getr regs1 10) by (apply EREG; [clear; lia | reflexivity]).
assert (Q13 : ew E 13 = getr regs1 13) by (apply EREG; [clear; lia | reflexivity]).
assert (Q14 : ew E 14 = getr regs1 14) by (apply EREG; [clear; lia | reflexivity]).
assert (Q18 : ew E 18 = getr regs1 18) by (apply EREG; [clear; lia | reflexivity]).
assert (Q19 : ew E 19 = getr regs1 19) by (apply EREG; [clear; lia | reflexivity]).
assert (Q20 : ew E 20 = getr regs1 20) by (apply EREG; [clear; lia | reflexivity]).
assert (Q21 : ew E 21 = getr regs1 21) by (apply EREG; [clear; lia | reflexivity]).
assert (Q22 : ew E 22 = getr regs1 22) by (apply EREG; [clear; lia | reflexivity]).
assert (Q24 : ew E 24 = getr regs1 24) by (apply EREG; [clear; lia | reflexivity]).
assert (Q26 : ew E 26 = getr regs1 26) by (apply EREG; [clear; lia | reflexivity]).
assert (Q27 : ew E 27 = getr regs1 27) by (apply EREG; [clear; lia | reflexivity]).
assert (R26' : getr regs1 26 = sv_denot E (SLit 384))
  by (rewrite denot_lit_U, U_lit by (clear; lia); exact R26).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG)) by (rewrite Q8; exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 ((rg_s RG + 0) / 8)) by (rewrite Q9, Z.add_0_r; exact R9).
assert (E14 : ew E 14 = Z_to_bv 64 (re_fd e1)) by (rewrite Q14; exact R14).
assert (E18 : ew E 18 = Z_to_bv 64 ((rg_s RG + 4) / 8)) by (rewrite Q18; exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 (SHADOW_OFF + 12 * Z.of_nat i)) by (rewrite Q19; exact R19).
assert (E32 : ew E 32 = Z_to_bv 64 f0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 o0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 f1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 o1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 f2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 o2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 f3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 o3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 8)).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG)
  by (rewrite E8; apply unsigned_lit_small; clear - HGS1 HGS2; lia).
assert (U35 : bv_unsigned (ew E 35) = SHADOW_OFF)
  by (rewrite E35; apply unsigned_lit_small; unfold SHADOW_OFF; clear; lia).
assert (SHOK : sh_ok SEGS BxT SHdsc E (mrestrict (w_H W1) m1)).
{ unfold SHdsc, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (ts_shent_azs ly1 S1 W1 m1 md1 E 8 (rg_s RG) 384 HAR);
    [ change 384 with (4 * ASRC); exact HGSZ
    | exact (U_atom E 35 SHADOW_OFF E35 ltac:(unfold SHADOW_OFF; clear; lia))
    | exact (U_atom E 8 (rg_s RG) E8 ltac:(clear - HGS1 HGS2; lia))
    | clear; lia | clear - HGS1; lia | unfold IMG_TOP; clear - HGS2; lia ]. }
assert (HS : st_ok_pi SEGS VAL E (ss_dsc i)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_scan)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_dsc. apply pa_entry_st_ok_full.
  - apply regs_ok_pin;
      [ apply regs_ok_pin;
          [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact R12]
      | intros X; discriminate X
      | cbn [sv_denot]; exact R26 ].
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ts_dsc_gs.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [base_val]. rewrite U8. split; [clear - HGS1; lia|]. split; [clear - HGS1 HGS2; lia|].
    split; [intros o Ho; clear - Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 32 0) f0);
        [exact (den_atom0 E 32 f0 E32 ltac:(clear - B00; lia)) | clear - B00; zside | zside
        | rewrite Z.add_0_r; exact V00].
    + apply (chunk_ok_val SEGS E _ _ 4 4 (SOff 33 0) o0);
        [exact (den_atom0 E 33 o0 E33 ltac:(clear - B01; lia)) | clear - B01; zside | zside | exact V01].
    + apply (chunk_ok_val SEGS E _ _ 96 4 (SOff 34 0) f1);
        [exact (den_atom0 E 34 f1 E34 ltac:(clear - B10; lia)) | clear - B10; zside | zside | exact V10].
    + apply (chunk_ok_val SEGS E _ _ 100 4 (SOff 36 0) o1);
        [exact (den_atom0 E 36 o1 E36 ltac:(clear - B11; lia)) | clear - B11; zside | zside | exact V11].
    + apply (chunk_ok_val SEGS E _ _ 192 4 (SOff 37 0) f2);
        [exact (den_atom0 E 37 f2 E37 ltac:(clear - B20; lia)) | clear - B20; zside | zside | exact V20].
    + apply (chunk_ok_val SEGS E _ _ 196 4 (SOff 38 0) o2);
        [exact (den_atom0 E 38 o2 E38 ltac:(clear - B21; lia)) | clear - B21; zside | zside | exact V21].
    + apply (chunk_ok_val SEGS E _ _ 288 4 (SOff 39 0) f3);
        [exact (den_atom0 E 39 f3 E39 ltac:(clear - B30; lia)) | clear - B30; zside | zside | exact V30].
    + apply (chunk_ok_val SEGS E _ _ 292 4 (SOff 40 0) o3);
        [exact (den_atom0 E 40 o3 E40 ltac:(clear - B31; lia)) | clear - B31; zside | zside | exact V31].
  - cbn [pairwise_disjoint]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [ts_dsc_facts f_atoms atoms_ok]. unfold afact_ok, dt_IMGF. cbn [af_lo af_hi af_al2].
    rewrite U8, U35. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert HGS1 HGS2 HGS8. clear. unfold SB, SHADOW_OFF, IMG_TOP. intros.
    repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
destruct i as [|[|[|[|i]]]]; [| | | | clear - Hij Hj4; lia].
- paj_run_to_tok RUNTO HS HJ SHOK DBspan ts_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  ts_reg HS (11%bv : bv 5) Ra1.
  pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 0 + 4)) HS
    (eq_trans Ra1 (ts_den_add_sh E 18 (rg_s RG) 4 (Z.of_nat 0) E18 E19 E8 E35 HGS8
       ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
       ltac:(clear; lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUN BR HS SHOK DBspan.
  + (* g_s[0].open = 0: the slot is closed, on to the next *)
    rewrite (ts_beqz_sx E 33 o0 E33 ltac:(clear - B01; lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (0 <> dxj cx)%nat) by (intros Hq; destruct (Hjj0 Hq) as (_ & Ho); exact (Ho Hc)).
    paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
    rewrite ?wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    ts_reg HS (2%bv : bv 5) X2. ts_reg HS (3%bv : bv 5) X3. ts_reg HS (4%bv : bv 5) X4.
    ts_reg HS (8%bv : bv 5) X8. ts_reg HS (9%bv : bv 5) X9. ts_reg HS (10%bv : bv 5) X10.
    ts_reg HS (12%bv : bv 5) X12. ts_reg HS (13%bv : bv 5) X13. ts_reg HS (14%bv : bv 5) X14.
    ts_reg HS (18%bv : bv 5) X18. ts_reg HS (19%bv : bv 5) X19. ts_reg HS (20%bv : bv 5) X20.
    ts_reg HS (21%bv : bv 5) X21. ts_reg HS (22%bv : bv 5) X22. ts_reg HS (24%bv : bv 5) X24.
    ts_reg HS (26%bv : bv 5) X26. ts_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    apply Knext. unfold DSC.
    eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
    split; [reflexivity|].
    split.
    { apply (ts_dregs_eq cx regs1 _ Hregs).
      - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
      - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
      - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
      - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
      - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
      - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
      - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
      - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
      - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
      - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
      - exact (eq_trans X26 (eq_sym R26')).
      - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
    split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
    split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
    split; [rewrite X14, (dt_den_reg E 14 _ Q14); exact R14|].
    split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; clear; lia|].
    split.
    { rewrite X19. cbn [sv_denot]. rewrite Q19, R19.
      unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; clear; lia).
      f_equal; cbn [Z.of_nat]; clear; lia. }
    split; [clear - Hij Hne0; lia|].
    split; [exact (dt_DMEM_kept B RG HGSB cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 sg out1 ev1
      (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
    split; [exact HLINK|]. split; [exact HSAME|].
    split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
    split; [exact Hlater | exact Hbud].
  + paj_run_to_tok RUNTO HS HJ SHOK DBspan ts_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    ts_reg HS (11%bv : bv 5) Ra1.
    pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 0 + 0)) HS
      (eq_trans Ra1 (ts_den_add_sh E 9 (rg_s RG) 0 (Z.of_nat 0) E9 E19 E8 E35 HGS8
         ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
         ltac:(clear; lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUN BR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite (ts_beq_sx E 32 14 f0 (re_fd e1) E32 E14 ltac:(clear - B00; lia) Hfdv) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite (ts_beqz_sx E 33 o0 E33 ltac:(clear - B01; lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (0 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 0 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            exfalso; destruct (Hoo0 Hq) as [Ho|Hf]; [exact (Hc Ho) | exact (Hf Hc0)]).
      paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite ?wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      ts_reg HS (2%bv : bv 5) X2. ts_reg HS (3%bv : bv 5) X3. ts_reg HS (4%bv : bv 5) X4.
      ts_reg HS (8%bv : bv 5) X8. ts_reg HS (9%bv : bv 5) X9. ts_reg HS (10%bv : bv 5) X10.
      ts_reg HS (13%bv : bv 5) X13. ts_reg HS (18%bv : bv 5) X18. ts_reg HS (19%bv : bv 5) X19.
      ts_reg HS (20%bv : bv 5) X20. ts_reg HS (21%bv : bv 5) X21. ts_reg HS (22%bv : bv 5) X22.
      ts_reg HS (23%bv : bv 5) X23. ts_reg HS (24%bv : bv 5) X24. ts_reg HS (26%bv : bv 5) X26.
      ts_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split.
      { apply (ts_dregs_eq cx regs1 _ Hregs).
        - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
        - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
        - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
        - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
        - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
        - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
        - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
        - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
        - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
        - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
        - exact (eq_trans X26 (eq_sym R26')).
        - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
      split.
      { rewrite X23, (den_atom E 8 (rg_s RG) 0 E8 ltac:(clear - HGS1 HGS2; lia)
          ltac:(clear - HGS1 HGS2; lia)).
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split.
      { rewrite X19, (dt_den_reg E 19 _ Q19), R19. rewrite <- Hj0.
        unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
      split; [exact (dt_DMEM_kept B RG HGSB cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
      split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: on to the next *)
      rewrite (ts_beq_sx E 32 14 f0 (re_fd e1) E32 E14 ltac:(clear - B00; lia) Hfdv) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (0 <> dxj cx)%nat) by (intros Hq; destruct (Hjj0 Hq) as (Hf & _); exact (Hc0 Hf)).
      paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite ?wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      ts_reg HS (2%bv : bv 5) X2. ts_reg HS (3%bv : bv 5) X3. ts_reg HS (4%bv : bv 5) X4.
      ts_reg HS (8%bv : bv 5) X8. ts_reg HS (9%bv : bv 5) X9. ts_reg HS (10%bv : bv 5) X10.
      ts_reg HS (12%bv : bv 5) X12. ts_reg HS (13%bv : bv 5) X13. ts_reg HS (14%bv : bv 5) X14.
      ts_reg HS (18%bv : bv 5) X18. ts_reg HS (19%bv : bv 5) X19. ts_reg HS (20%bv : bv 5) X20.
      ts_reg HS (21%bv : bv 5) X21. ts_reg HS (22%bv : bv 5) X22. ts_reg HS (24%bv : bv 5) X24.
      ts_reg HS (26%bv : bv 5) X26. ts_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Knext. unfold DSC.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split.
      { apply (ts_dregs_eq cx regs1 _ Hregs).
        - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
        - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
        - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
        - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
        - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
        - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
        - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
        - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
        - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
        - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
        - exact (eq_trans X26 (eq_sym R26')).
        - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
      split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
      split; [rewrite X14, (dt_den_reg E 14 _ Q14); exact R14|].
      split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; clear; lia|].
      split.
      { rewrite X19. cbn [sv_denot]. rewrite Q19, R19.
        unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; clear; lia).
        f_equal; cbn [Z.of_nat]; clear; lia. }
      split; [clear - Hij Hne0; lia|].
      split; [exact (dt_DMEM_kept B RG HGSB cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
      split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
- paj_run_to_tok RUNTO HS HJ SHOK DBspan ts_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  ts_reg HS (11%bv : bv 5) Ra1.
  pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 1 + 4)) HS
    (eq_trans Ra1 (ts_den_add_sh E 18 (rg_s RG) 4 (Z.of_nat 1) E18 E19 E8 E35 HGS8
       ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
       ltac:(clear; lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUN BR HS SHOK DBspan.
  + (* g_s[1].open = 0: the slot is closed, on to the next *)
    rewrite (ts_beqz_sx E 36 o1 E36 ltac:(clear - B11; lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (1 <> dxj cx)%nat) by (intros Hq; destruct (Hjj1 Hq) as (_ & Ho); exact (Ho Hc)).
    paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
    rewrite ?wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    ts_reg HS (2%bv : bv 5) X2. ts_reg HS (3%bv : bv 5) X3. ts_reg HS (4%bv : bv 5) X4.
    ts_reg HS (8%bv : bv 5) X8. ts_reg HS (9%bv : bv 5) X9. ts_reg HS (10%bv : bv 5) X10.
    ts_reg HS (12%bv : bv 5) X12. ts_reg HS (13%bv : bv 5) X13. ts_reg HS (14%bv : bv 5) X14.
    ts_reg HS (18%bv : bv 5) X18. ts_reg HS (19%bv : bv 5) X19. ts_reg HS (20%bv : bv 5) X20.
    ts_reg HS (21%bv : bv 5) X21. ts_reg HS (22%bv : bv 5) X22. ts_reg HS (24%bv : bv 5) X24.
    ts_reg HS (26%bv : bv 5) X26. ts_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    apply Knext. unfold DSC.
    eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
    split; [reflexivity|].
    split.
    { apply (ts_dregs_eq cx regs1 _ Hregs).
      - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
      - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
      - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
      - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
      - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
      - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
      - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
      - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
      - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
      - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
      - exact (eq_trans X26 (eq_sym R26')).
      - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
    split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
    split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
    split; [rewrite X14, (dt_den_reg E 14 _ Q14); exact R14|].
    split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; clear; lia|].
    split.
    { rewrite X19. cbn [sv_denot]. rewrite Q19, R19.
      unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; clear; lia).
      f_equal; cbn [Z.of_nat]; clear; lia. }
    split; [clear - Hij Hne0; lia|].
    split; [exact (dt_DMEM_kept B RG HGSB cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 sg out1 ev1
      (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
    split; [exact HLINK|]. split; [exact HSAME|].
    split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
    split; [exact Hlater | exact Hbud].
  + paj_run_to_tok RUNTO HS HJ SHOK DBspan ts_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    ts_reg HS (11%bv : bv 5) Ra1.
    pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 1 + 0)) HS
      (eq_trans Ra1 (ts_den_add_sh E 9 (rg_s RG) 0 (Z.of_nat 1) E9 E19 E8 E35 HGS8
         ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
         ltac:(clear; lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUN BR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite (ts_beq_sx E 34 14 f1 (re_fd e1) E34 E14 ltac:(clear - B10; lia) Hfdv) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite (ts_beqz_sx E 36 o1 E36 ltac:(clear - B11; lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (1 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 1 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            exfalso; destruct (Hoo1 Hq) as [Ho|Hf]; [exact (Hc Ho) | exact (Hf Hc0)]).
      paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite ?wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      ts_reg HS (2%bv : bv 5) X2. ts_reg HS (3%bv : bv 5) X3. ts_reg HS (4%bv : bv 5) X4.
      ts_reg HS (8%bv : bv 5) X8. ts_reg HS (9%bv : bv 5) X9. ts_reg HS (10%bv : bv 5) X10.
      ts_reg HS (13%bv : bv 5) X13. ts_reg HS (18%bv : bv 5) X18. ts_reg HS (19%bv : bv 5) X19.
      ts_reg HS (20%bv : bv 5) X20. ts_reg HS (21%bv : bv 5) X21. ts_reg HS (22%bv : bv 5) X22.
      ts_reg HS (23%bv : bv 5) X23. ts_reg HS (24%bv : bv 5) X24. ts_reg HS (26%bv : bv 5) X26.
      ts_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split.
      { apply (ts_dregs_eq cx regs1 _ Hregs).
        - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
        - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
        - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
        - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
        - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
        - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
        - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
        - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
        - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
        - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
        - exact (eq_trans X26 (eq_sym R26')).
        - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
      split.
      { rewrite X23, (den_atom E 8 (rg_s RG) 96 E8 ltac:(clear - HGS1 HGS2; lia)
          ltac:(clear - HGS1 HGS2; lia)).
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split.
      { rewrite X19, (dt_den_reg E 19 _ Q19), R19. rewrite <- Hj0.
        unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
      split; [exact (dt_DMEM_kept B RG HGSB cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
      split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: on to the next *)
      rewrite (ts_beq_sx E 34 14 f1 (re_fd e1) E34 E14 ltac:(clear - B10; lia) Hfdv) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (1 <> dxj cx)%nat) by (intros Hq; destruct (Hjj1 Hq) as (Hf & _); exact (Hc0 Hf)).
      paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite ?wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      ts_reg HS (2%bv : bv 5) X2. ts_reg HS (3%bv : bv 5) X3. ts_reg HS (4%bv : bv 5) X4.
      ts_reg HS (8%bv : bv 5) X8. ts_reg HS (9%bv : bv 5) X9. ts_reg HS (10%bv : bv 5) X10.
      ts_reg HS (12%bv : bv 5) X12. ts_reg HS (13%bv : bv 5) X13. ts_reg HS (14%bv : bv 5) X14.
      ts_reg HS (18%bv : bv 5) X18. ts_reg HS (19%bv : bv 5) X19. ts_reg HS (20%bv : bv 5) X20.
      ts_reg HS (21%bv : bv 5) X21. ts_reg HS (22%bv : bv 5) X22. ts_reg HS (24%bv : bv 5) X24.
      ts_reg HS (26%bv : bv 5) X26. ts_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Knext. unfold DSC.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split.
      { apply (ts_dregs_eq cx regs1 _ Hregs).
        - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
        - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
        - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
        - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
        - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
        - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
        - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
        - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
        - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
        - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
        - exact (eq_trans X26 (eq_sym R26')).
        - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
      split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
      split; [rewrite X14, (dt_den_reg E 14 _ Q14); exact R14|].
      split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; clear; lia|].
      split.
      { rewrite X19. cbn [sv_denot]. rewrite Q19, R19.
        unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; clear; lia).
        f_equal; cbn [Z.of_nat]; clear; lia. }
      split; [clear - Hij Hne0; lia|].
      split; [exact (dt_DMEM_kept B RG HGSB cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
      split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
- paj_run_to_tok RUNTO HS HJ SHOK DBspan ts_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  ts_reg HS (11%bv : bv 5) Ra1.
  pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 2 + 4)) HS
    (eq_trans Ra1 (ts_den_add_sh E 18 (rg_s RG) 4 (Z.of_nat 2) E18 E19 E8 E35 HGS8
       ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
       ltac:(clear; lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUN BR HS SHOK DBspan.
  + (* g_s[2].open = 0: the slot is closed, on to the next *)
    rewrite (ts_beqz_sx E 38 o2 E38 ltac:(clear - B21; lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (2 <> dxj cx)%nat) by (intros Hq; destruct (Hjj2 Hq) as (_ & Ho); exact (Ho Hc)).
    paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
    rewrite ?wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    ts_reg HS (2%bv : bv 5) X2. ts_reg HS (3%bv : bv 5) X3. ts_reg HS (4%bv : bv 5) X4.
    ts_reg HS (8%bv : bv 5) X8. ts_reg HS (9%bv : bv 5) X9. ts_reg HS (10%bv : bv 5) X10.
    ts_reg HS (12%bv : bv 5) X12. ts_reg HS (13%bv : bv 5) X13. ts_reg HS (14%bv : bv 5) X14.
    ts_reg HS (18%bv : bv 5) X18. ts_reg HS (19%bv : bv 5) X19. ts_reg HS (20%bv : bv 5) X20.
    ts_reg HS (21%bv : bv 5) X21. ts_reg HS (22%bv : bv 5) X22. ts_reg HS (24%bv : bv 5) X24.
    ts_reg HS (26%bv : bv 5) X26. ts_reg HS (27%bv : bv 5) X27.
    pmkst HS.
    apply Knext. unfold DSC.
    eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
    split; [reflexivity|].
    split.
    { apply (ts_dregs_eq cx regs1 _ Hregs).
      - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
      - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
      - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
      - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
      - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
      - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
      - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
      - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
      - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
      - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
      - exact (eq_trans X26 (eq_sym R26')).
      - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
    split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
    split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
    split; [rewrite X14, (dt_den_reg E 14 _ Q14); exact R14|].
    split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; clear; lia|].
    split.
    { rewrite X19. cbn [sv_denot]. rewrite Q19, R19.
      unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; clear; lia).
      f_equal; cbn [Z.of_nat]; clear; lia. }
    split; [clear - Hij Hne0; lia|].
    split; [exact (dt_DMEM_kept B RG HGSB cx ly1 S1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 sg out1 ev1
      (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
    split; [exact HLINK|]. split; [exact HSAME|].
    split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
    split; [exact Hlater | exact Hbud].
  + paj_run_to_tok RUNTO HS HJ SHOK DBspan ts_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    ts_reg HS (11%bv : bv 5) Ra1.
    pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 2 + 0)) HS
      (eq_trans Ra1 (ts_den_add_sh E 9 (rg_s RG) 0 (Z.of_nat 2) E9 E19 E8 E35 HGS8
         ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
         ltac:(clear; lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUN BR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite (ts_beq_sx E 37 14 f2 (re_fd e1) E37 E14 ltac:(clear - B20; lia) Hfdv) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite (ts_beqz_sx E 38 o2 E38 ltac:(clear - B21; lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (2 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 2 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            exfalso; destruct (Hoo2 Hq) as [Ho|Hf]; [exact (Hc Ho) | exact (Hf Hc0)]).
      paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite ?wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      ts_reg HS (2%bv : bv 5) X2. ts_reg HS (3%bv : bv 5) X3. ts_reg HS (4%bv : bv 5) X4.
      ts_reg HS (8%bv : bv 5) X8. ts_reg HS (9%bv : bv 5) X9. ts_reg HS (10%bv : bv 5) X10.
      ts_reg HS (13%bv : bv 5) X13. ts_reg HS (18%bv : bv 5) X18. ts_reg HS (19%bv : bv 5) X19.
      ts_reg HS (20%bv : bv 5) X20. ts_reg HS (21%bv : bv 5) X21. ts_reg HS (22%bv : bv 5) X22.
      ts_reg HS (23%bv : bv 5) X23. ts_reg HS (24%bv : bv 5) X24. ts_reg HS (26%bv : bv 5) X26.
      ts_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split.
      { apply (ts_dregs_eq cx regs1 _ Hregs).
        - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
        - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
        - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
        - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
        - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
        - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
        - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
        - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
        - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
        - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
        - exact (eq_trans X26 (eq_sym R26')).
        - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
      split.
      { rewrite X23, (den_atom E 8 (rg_s RG) 192 E8 ltac:(clear - HGS1 HGS2; lia)
          ltac:(clear - HGS1 HGS2; lia)).
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split.
      { rewrite X19, (dt_den_reg E 19 _ Q19), R19. rewrite <- Hj0.
        unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
      split; [exact (dt_DMEM_kept B RG HGSB cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
      split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: on to the next *)
      rewrite (ts_beq_sx E 37 14 f2 (re_fd e1) E37 E14 ltac:(clear - B20; lia) Hfdv) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (2 <> dxj cx)%nat) by (intros Hq; destruct (Hjj2 Hq) as (Hf & _); exact (Hc0 Hf)).
      paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite ?wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      ts_reg HS (2%bv : bv 5) X2. ts_reg HS (3%bv : bv 5) X3. ts_reg HS (4%bv : bv 5) X4.
      ts_reg HS (8%bv : bv 5) X8. ts_reg HS (9%bv : bv 5) X9. ts_reg HS (10%bv : bv 5) X10.
      ts_reg HS (12%bv : bv 5) X12. ts_reg HS (13%bv : bv 5) X13. ts_reg HS (14%bv : bv 5) X14.
      ts_reg HS (18%bv : bv 5) X18. ts_reg HS (19%bv : bv 5) X19. ts_reg HS (20%bv : bv 5) X20.
      ts_reg HS (21%bv : bv 5) X21. ts_reg HS (22%bv : bv 5) X22. ts_reg HS (24%bv : bv 5) X24.
      ts_reg HS (26%bv : bv 5) X26. ts_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Knext. unfold DSC.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split.
      { apply (ts_dregs_eq cx regs1 _ Hregs).
        - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
        - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
        - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
        - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
        - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
        - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
        - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
        - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
        - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
        - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
        - exact (eq_trans X26 (eq_sym R26')).
        - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
      split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
      split; [rewrite X14, (dt_den_reg E 14 _ Q14); exact R14|].
      split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; clear; lia|].
      split.
      { rewrite X19. cbn [sv_denot]. rewrite Q19, R19.
        unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; clear; lia).
        f_equal; cbn [Z.of_nat]; clear; lia. }
      split; [clear - Hij Hne0; lia|].
      split; [exact (dt_DMEM_kept B RG HGSB cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
      split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
- paj_run_to_tok RUNTO HS HJ SHOK DBspan ts_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  ts_reg HS (11%bv : bv 5) Ra1.
  pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 3 + 4)) HS
    (eq_trans Ra1 (ts_den_add_sh E 18 (rg_s RG) 4 (Z.of_nat 3) E18 E19 E8 E35 HGS8
       ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
       ltac:(clear; lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUN BR HS SHOK DBspan.
  + (* g_s[3].open = 0: refuted, the scan reaches the harness's own slot j <= 3 first *)
    rewrite (ts_beqz_sx E 40 o3 E40 ltac:(clear - B31; lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (3 <> dxj cx)%nat) by (intros Hq; destruct (Hjj3 Hq) as (_ & Ho); exact (Ho Hc)).
    exfalso. clear - Hij Hj4 Hne0. lia.
  + paj_run_to_tok RUNTO HS HJ SHOK DBspan ts_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    ts_reg HS (11%bv : bv 5) Ra1.
    pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 3 + 0)) HS
      (eq_trans Ra1 (ts_den_add_sh E 9 (rg_s RG) 0 (Z.of_nat 3) E9 E19 E8 E35 HGS8
         ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
         ltac:(clear; lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok RUN HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUN BR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite (ts_beq_sx E 39 14 f3 (re_fd e1) E39 E14 ltac:(clear - B30; lia) Hfdv) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite (ts_beqz_sx E 40 o3 E40 ltac:(clear - B31; lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (3 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 3 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            exfalso; destruct (Hoo3 Hq) as [Ho|Hf]; [exact (Hc Ho) | exact (Hf Hc0)]).
      paj_run_to_tok RUNTO HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite ?wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply ts_nowr_lem; vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      ts_reg HS (2%bv : bv 5) X2. ts_reg HS (3%bv : bv 5) X3. ts_reg HS (4%bv : bv 5) X4.
      ts_reg HS (8%bv : bv 5) X8. ts_reg HS (9%bv : bv 5) X9. ts_reg HS (10%bv : bv 5) X10.
      ts_reg HS (13%bv : bv 5) X13. ts_reg HS (18%bv : bv 5) X18. ts_reg HS (19%bv : bv 5) X19.
      ts_reg HS (20%bv : bv 5) X20. ts_reg HS (21%bv : bv 5) X21. ts_reg HS (22%bv : bv 5) X22.
      ts_reg HS (23%bv : bv 5) X23. ts_reg HS (24%bv : bv 5) X24. ts_reg HS (26%bv : bv 5) X26.
      ts_reg HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2.
      eexists _, ly1, S1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split.
      { apply (ts_dregs_eq cx regs1 _ Hregs).
        - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
        - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
        - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
        - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
        - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
        - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
        - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
        - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
        - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
        - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
        - exact (eq_trans X26 (eq_sym R26')).
        - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
      split.
      { rewrite X23, (den_atom E 8 (rg_s RG) 288 E8 ltac:(clear - HGS1 HGS2; lia)
          ltac:(clear - HGS1 HGS2; lia)).
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split.
      { rewrite X19, (dt_den_reg E 19 _ Q19), R19. rewrite <- Hj0.
        unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
      split; [exact (dt_DMEM_kept B RG HGSB cx ly1 S1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
      split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: refuted, j <= 3 and j <> 3 *)
      rewrite (ts_beq_sx E 39 14 f3 (re_fd e1) E39 E14 ltac:(clear - B30; lia) Hfdv) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (3 <> dxj cx)%nat) by (intros Hq; destruct (Hjj3 Hq) as (Hf & _); exact (Hc0 Hf)).
      exfalso. clear - Hij Hj4 Hne0. lia.
Qed.

End c.
End b.
End a.

(* ---- THE GENERIC WALK (an internal work row, the ARx drain walk DR_x; the image-B twin of the dt_scan / dt_scan_step part of
   lib/A/W_drain_top.v's generic Section c, a working branch d80aca9181b).  Section cxs proves the two scan
   statements of W_drain_tophead.v's Section cxd, dt_scan_entry_stmt_x and dt_scan_step_stmt_x, over any allocator
   relation ARx, by the walk of Section c above: the scan makes no call, so each cut's DMEM_x journal, its ghost list
   Hp1 and its dbud_x pass through unchanged.  The lemmas of Section c that read AR have their twins here (ts_shent_sub_x
   of W_drain_tophead.v's dt_shent_sub, at the cut's Hp1 = [] by HP0; ts_shent_azs_x of ts_shent_azs; ts_DMEM_kept_x of
   W_drain_tophead.v's dt_DMEM_kept); the others are cited with the Section variables they take after End c.  The AR
   text above is unchanged; it is compiled before the Requires below, so no name of the generic kit is in scope in it
   (W_drain_topb_cx.v and W_drain_tophead.v, which it Requires, load the kit without Importing it; their global zify
   lines keep the flag false). ---- *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
(* the zify flag this file's AR text runs with (false: W_drain_tophead.v's setting, the last its Requires leave),
   whatever the Requires above leave *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section cxs.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
(* W_drain_cx_x.v Section c's hypotheses that Section c above has a twin of, word for word *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* no hidden head in any ARx state (a Theorem Labs lane's HP0 ruling): the shadow law at the cut's table block *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Variable CTX_R : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

#[local] Abbreviation dt_sh m c := (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 35 0)).
#[local] Abbreviation dt_gv c := (SAlu ALU_SRL (SOff 8 c) (SLit 3)).
#[local] Abbreviation BxT := (SOff 35 0).

(* Section c's ts_reg (local to it) *)
Local Ltac ts_reg_x HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* W_drain_tophead.v's dt_shent_sub over ARx, at the empty ghost list (the shadow law's hidden-head premise is void) *)
Lemma ts_shent_sub_x : forall ly S (W : world SEGS) mem md E (m : nat) p n q lo hi,
ARx ly S [] W mem md -> In (p, n) (ablocks B ly S) ->
U E BxT = SHADOW_OFF -> U E (SOff m 0) = q ->
p <= q + lo -> lo <= hi -> q + hi <= p + req_size n ->
shent_ok SEGS BxT E (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
intros ly S W mem md E m p n q lo hi HAR Hin HB Hm H1 H2 H3.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm.
rewrite <- (aview_rd_of SEGS).
destruct (alx_shadow _ _ _ LAWS ly S [] W mem md p n HAR Hin (fun h (Hh : In h []) => match Hh with end))
  as [Hbs _].
split.
- destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; lia].
  eapply block_shadow_range; [exact Hbs | lia | lia].
- destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
  intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* Section c's ts_shent_azs over ARx: the 4 * 96 bytes of g_s as the walk's shadow-entry obligation (HGSZ) *)
Lemma ts_shent_azs_x : forall ly S Hp (W : world SEGS) mem md E (m : nat) q n,
ARx ly S Hp W mem md -> azs B q n -> U E BxT = SHADOW_OFF -> U E (SOff m 0) = q ->
0 <= n -> 0x10000 <= q -> q + n <= IMG_TOP ->
shent_ok SEGS BxT E (mrestrict (w_H W) mem) (mkSHE m 0 n).
Proof.
intros ly S Hp W mem md E m q n HAR Hz HB Hm Hn Hq1 Hq2.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of SEGS).
split.
- rewrite Z.add_0_r, Z.sub_0_r. exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md q n HAR Hz).
- intros a Ha. unfold SHADOW_OFF, IMG_TOP in *. lia.
Qed.

(* ---- route R: the R twins of ts_DMEM_kept_x, dt_scan_entry_x and dt_scan_step_x, over W_drain_tophead.v's R
   carriers DT1_xR / DSC_xR and W_drain_topb_cx.v's DT2_xR; the runs are the G runs (paj_run_x_xG), the branch
   paj_branch_xR.  The scan makes no call.  The strict lemmas below are these twins at R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

Lemma ts_DMEM_kept_xR : forall cx Hp ly1 S1 Hp1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1,
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k2 ->
(forall a, aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
Proof.
intros cx Hp ly1 S1 Hp1 W1 m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 HMEM HJ2 KL HP.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (Hkept : forall a, abyte_kept W1 m1 W1 m2 a).
{ intros a. split; [exact (KL a)|]. unfold arm. apply (writable_kept (w_H W1) m1 m2 a (HP a)). }
assert (HKA : forall fp, akept W1 m1 W1 m2 fp) by (intros fp r Hr a Ha; exact (Hkept a)).
assert (HVM : forall a n v, val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v).
{ intros a n v H. apply (akept_vm W1 m1); [intros x Hx; exact (Hkept x) | exact H]. }
split; [exact HJ2|].
split; [intros a Ha; rewrite (KL a); exact (Hrom a Ha)|].
split; [intros a Ha1 Ha2 Ha3 Ha4; apply HP; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 &
    A17 & A18 & A19 & A20 & A21 & A22 & A23 & ASV).
  repeat match goal with |- _ /\ _ => split end;
    first [ apply HVM; assumption | intros i Hi; apply HVM; exact (ASV i Hi) ]. }
split; [exact (dt_garr8_kept W1 m1 W1 m2 _ _ Hgarr (fun x _ => Hkept x))|].
split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 m2 _ (HP _)); exact (Hawr i Hi)|].
split; [exact (dt_aentry_okx_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2 e1 HEOK (HKA _)
  (dt_aentry_blks_in B RG HGSB ly1 S1 W1 m1 e1 HEOK))|].
split; [exact (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 Hsrc (HKA _)
  (dt_asrc_blks_in B RG HGSB ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc))|].
split; [intros i Hi Hne; destruct (Hoth i Hi Hne) as (f & o & V1 & V2 & Hdis);
  exists f, o; split; [apply HVM; exact V1|]; split; [apply HVM; exact V2 | exact Hdis]|].
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as (Hv & Hw).
  split; [rewrite (KL x); exact Hv|].
  intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 x (HP x)). exact (Hw Hwr). }
split; [|split; [exact Hlivout | exact Hperm]].
apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2); [exact Hout | exact (HKA _)|].
intros b Hb. exact (dt_aout_blks_in B RG HGSB ly1 S1 W1 m1 _ _ _ _ _ _ Hout b Hb).
Qed.

Theorem dt_scan_entry_xR : dt_scan_entry_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros cx Hp kr sg D W1 c1 HB HD1 K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HD1 as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hregs & HMEM & HnoNUL & Hused & Hband & HLINK & HSAME & HHIST & HJ1 & Hroom & Hlater & Hbud).
pose proof Hregs as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HMEM as (HJ & _ & _ & _ & HFR & Hgarr & _ & HEOK & _ & _ & _ & _ & _ & Hperm).
(* the cut's ghost list Hp1 is [] (HP0 at the cut's state, the end of its journal) *)
assert (EHp1 : Hp1 = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJ). subst Hp1.
pose proof HB as (Hafn & _ & _ & _ & HSAhi & HSA8 & _).
pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HDS : DRAIN_STK_x = 17008) by reflexivity. rewrite HDS in Hslo.
assert (HspA : alloc_ceiling + 17008 <= dsp0 cx) by (unfold dsp0; clear - Hceil Hslo; lia).
assert (HspB : dsp0 cx <= 2 ^ 47) by (unfold dsp0; clear - Hshi H47; lia).
assert (HspM : dsp0 cx mod 16 = 0) by (unfold dsp0; exact Hal16).
clear Hafn Hstk Hal16 Hceil Hslo Hshi H47.
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2. unfold IMG_TOP in HGS2.
assert (HAR : ARx ly1 S1 [] W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HtblC : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly1 S1 [] W1 m1 md1 (dxG cx) ATABLE HAR HtblC) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil.
pose proof HB as (_ & _ & _ & HGle & _).
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in *; clear - HG4096 HGle; lia).
assert (HSAcl : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; clear - HGceil HSAhi; lia).
pose proof HEOK as (_ & _ & Hpad1 & _ & Hfdv & Hcapv & HUlen & Hucap & _).
assert (Hcapb : 0 <= re_cap e1 <= 16384) by (clear - Hcapv; destruct Hcapv as [Hq|[Hq|Hq]]; rewrite Hq; lia).
assert (Husedb : 0 <= re_used e1 <= re_cap e1)
  by (clear - HUlen Hucap; pose proof (Nat2Z.is_nonneg (length (re_U e1))); lia).
clear Hcapv.
pose proof Hband as (Hbuf1 & Hbuf2 & Hbuf8). unfold DCEIL in Hbuf2.
subst c1. unfold cfg_at, w64.
remember (Eimg (Ereg regs1 (ts_en_extra (dxSA cx) (re_cap e1) (re_used e1) (re_buf e1) (re_fd e1))))
  as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E2 : ew E 2 = getr regs1 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs1 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs1 4) by (apply EREG; [lia | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG))
  by (rewrite (EREG 8%nat 8%bv) by (first [lia | reflexivity]); exact R8).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_cap e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_used e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (re_buf e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (re_fd e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (BSA : 0 <= dxSA cx < 2 ^ 64) by (clear - HSAlo HSAcl C1; lia).
assert (BGS : 0 <= rg_s RG < 2 ^ 64) by (clear - HGS1 HGS2; lia).
assert (BSH : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; lia).
assert (Bcap : 0 <= re_cap e1 < 2 ^ 64) by (clear - Hcapb; lia).
assert (Bused : 0 <= re_used e1 < 2 ^ 64) by (clear - Husedb Hcapb; lia).
assert (Bbuf : 0 <= re_buf e1 < 2 ^ 64) by (clear - Hbuf1 Hbuf2 Hcapb; lia).
assert (Bfd : 0 <= re_fd e1 < 2 ^ 64) by (clear - Hfdv; lia).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite E2; exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG) by (rewrite E8; apply unsigned_lit_small; exact BGS).
assert (U35 : bv_unsigned (ew E 35) = SHADOW_OFF) by (rewrite E35; apply unsigned_lit_small; exact BSH).
assert (U32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; exact BSA).
assert (U33 : bv_unsigned (ew E 33) = re_cap e1) by (rewrite E33; apply unsigned_lit_small; exact Bcap).
assert (U34 : bv_unsigned (ew E 34) = re_used e1) by (rewrite E34; apply unsigned_lit_small; exact Bused).
assert (U36 : bv_unsigned (ew E 36) = re_buf e1) by (rewrite E36; apply unsigned_lit_small; exact Bbuf).
assert (R21' : getr regs1 21 = sv_denot E (SOff 32 0))
  by (rewrite (den_atom0 E 32 (dxSA cx) E32 BSA); exact R21).
assert (R24' : getr regs1 24 = sv_denot E (SOff 32 8))
  by (rewrite (den_atom E 32 (dxSA cx) 8 E32 ltac:(clear - BSA HSAcl C1; lia) BSA); exact R24).
assert (R20' : getr regs1 20 = sv_denot E (SOff 32 16))
  by (rewrite (den_atom E 32 (dxSA cx) 16 E32 ltac:(clear - BSA HSAcl C1; lia) BSA); exact R20).
assert (R22' : getr regs1 22 = sv_denot E (SOff 32 24))
  by (rewrite (den_atom E 32 (dxSA cx) 24 E32 ltac:(clear - BSA HSAcl C1; lia) BSA); exact R22).
assert (R27' : getr regs1 27 = sv_denot E (SOff 32 32))
  by (rewrite (den_atom E 32 (dxSA cx) 32 E32 ltac:(clear - BSA HSAcl C1; lia) BSA); exact R27).
assert (R9' : getr regs1 9 = sv_denot E (dt_gv 0))
  by (rewrite (dt_den_gv RG E (rg_s RG) 0 E8 BGS ltac:(clear - BGS; lia)), Z.add_0_r; exact R9).
assert (R18' : getr regs1 18 = sv_denot E (dt_gv 4))
  by (rewrite (dt_den_gv RG E (rg_s RG) 4 E8 BGS ltac:(clear - HGS1 HGS2; lia)); exact R18).
assert (R26' : getr regs1 26 = sv_denot E (SLit 384))
  by (rewrite denot_lit_U, U_lit by (clear; lia); exact R26).
pose proof HFR as (G8 & G32 & G40 & G48 & G56 & G64 & G72 & G80 & G88 & G104 & G120 & G128 & G136 &
  G144 & G152 & G176 & G184 & G200 & G208 & G216 & G224 & G232 & G240 & Gsaved).
assert (HS : st_ok_pi SEGS VAL E ss_en
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_mid)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_en. apply pa_entry_st_ok_full.
  - unfold dt_regs_top.
    repeat (apply regs_ok_pin;
      [ | intros X; discriminate X
      | first [ exact R21' | exact R24' | exact R20' | exact R22' | exact R27'
              | exact R9' | exact R18' | exact R26' ] ]).
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, ts_en_frame, ts_en_sa;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp.
      split; [unfold DRAIN_FRAME; clear - HspA C1; lia|]. split; [unfold DRAIN_FRAME; clear - HspB; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      assert (Hsh : forall c, 0 <= c <= 56 -> 0 <= shadow_addr (dxSA cx + c) < 2 ^ (8 * Z.of_N 8)).
      { intros c Hc. unfold shadow_addr, SHADOW_OFF. change (8 * Z.of_N 8) with 64.
        assert (Hq1 : 0 <= (dxSA cx + c) / 8) by (apply Z.div_pos; clear - Hc HSAlo; lia).
        assert (Hq2 : (dxSA cx + c) / 8 <= dxSA cx + c) by (apply Z.div_le_upper_bound; clear - Hc HSAlo; lia).
        clear - Hq1 Hq2 Hc HSAcl C1. lia. }
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
      * apply (chunk_ok_val SEGS E _ _ 200 8 (dt_sh 32 0) (shadow_addr (dxSA cx)));
          [ rewrite (dt_den_sh RG E 32 (dxSA cx) 0 E32 E35 BSA ltac:(clear - BSA; lia)), Z.add_0_r;
            reflexivity
          | pose proof (Hsh 0 ltac:(clear; lia)) as Hq; rewrite Z.add_0_r in Hq; exact Hq
          | zside
          | exact G200 ].
      * apply (chunk_ok_val SEGS E _ _ 216 8 (dt_sh 32 32) (shadow_addr (dxSA cx + 32)));
          [ exact (dt_den_sh RG E 32 (dxSA cx) 32 E32 E35 BSA ltac:(clear - BSA HSAcl C1; lia))
          | exact (Hsh 32 ltac:(clear; lia))
          | zside
          | exact G216 ].
      * apply (chunk_ok_val SEGS E _ _ 224 8 (dt_sh 32 16) (shadow_addr (dxSA cx + 16)));
          [ exact (dt_den_sh RG E 32 (dxSA cx) 16 E32 E35 BSA ltac:(clear - BSA HSAcl C1; lia))
          | exact (Hsh 16 ltac:(clear; lia))
          | zside
          | exact G224 ].
      * apply (chunk_ok_val SEGS E _ _ 232 8 (dt_sh 32 24) (shadow_addr (dxSA cx + 24)));
          [ exact (dt_den_sh RG E 32 (dxSA cx) 24 E32 E35 BSA ltac:(clear - BSA HSAcl C1; lia))
          | exact (Hsh 24 ltac:(clear; lia))
          | zside
          | exact G232 ].
      * apply (chunk_ok_val SEGS E _ _ 240 8 (SOff 35 0) SHADOW_OFF);
          [ exact (den_atom0 E 35 SHADOW_OFF E35 BSH) | unfold SHADOW_OFF; zside | zside | exact G240 ].
    + cbn [base_val]. rewrite U32. split; [clear - BSA HSAlo HSAcl C1; lia|].
      split; [clear - BSA HSAlo HSAcl C1; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      * apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 37 0) (re_fd e1));
          [ exact (den_atom0 E 37 (re_fd e1) E37 Bfd) | clear - Hfdv; zside | zside | ].
        rewrite Z.add_0_r. exact (ts_entry_fd RG HGSB W1 m1 (dxSA cx) e1 ltac:(clear - Hfdv; lia) Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 36 0) (re_buf e1));
          [ exact (den_atom0 E 36 (re_buf e1) E36 Bbuf) | clear - Bbuf; zside | zside | ].
        exact (ts_entry_buf RG HGSB W1 m1 (dxSA cx) e1 Hpad1 Bbuf Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 34 0) (re_used e1));
          [ exact (den_atom0 E 34 (re_used e1) E34 Bused) | clear - Bused; zside | zside | ].
        exact (dt_entry_used RG HGSB W1 m1 (dxSA cx) e1 Hpad1 Bused Hgarr).
      * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 33 0) (re_cap e1));
          [ exact (den_atom0 E 33 (re_cap e1) E33 Bcap) | clear - Bcap; zside | zside | ].
        exact (dt_entry_cap RG HGSB W1 m1 (dxSA cx) e1 Hpad1 Bcap Hgarr).
  - apply pairwise_disjoint_of_extents. unfold ts_en_frame, ts_en_sa, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HSAlo HSAcl HspA HspB C1. clear. unfold DRAIN_FRAME.
    intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [ts_en_facts f_atoms atoms_ok]. unfold afact_ok, dt_HEAPF, dt_IMGF, ts_PTRF.
    cbn [af_lo af_hi af_al2].
    rewrite Usp, U8, U35, U32, U33, U34, U36.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hspm : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
      by (unfold DRAIN_FRAME; rewrite Zminus_mod, HspM; reflexivity).
    revert HSAlo HSAcl HspA HspB C1 Hspm HGS1 HGS2 HGS8 Hcapb Husedb Hbuf1 Hbuf2 Hbuf8. clear.
    unfold SB, SHADOW_OFF, DRAIN_FRAME, IMG_TOP.
    intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS BxT SHng E (mrestrict (w_H W1) m1)).
{ unfold SHng, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (ts_shent_sub_x ly1 S1 W1 m1 md1 E 32 (dxG cx) ATABLE (dxSA cx) 0 56 HAR HtblC).
  - exact (U_atom E 35 SHADOW_OFF E35 BSH).
  - exact (U_atom E 32 (dxSA cx) E32 BSA).
  - clear - HGle. lia.
  - clear. lia.
  - rewrite RQT. unfold AENT, ATABLE in HSAhi. clear - HSAhi. lia. }
paj_run_tok_xR RUNG HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
psrr_branch_tok RUNG BRR HS SHOK DBspan.
{ (* 0x83468 taken: the pointer-overflow trap, refuted *)
  rewrite (ts_bltu_nowrap RG HGSB E 34 36 (re_used e1) (re_buf e1) E34 E36 ltac:(clear - Husedb; lia)
    ltac:(clear - Hbuf1; lia) ltac:(clear - Husedb Hcapb Hbuf2; lia)) in Hc.
  discriminate Hc. }
paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. all: try exact Usp. }
rewrite ?wvb_collapse in HJ.
lazymatch type of HFr with frame_of _ ?rs _ _ =>
  assert (N0 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
  assert (N1 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
{ intros a.
  rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
  exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
  by (intros a Ha; exact (apresent_grows _ _ _ _ HG1 (apresent_grows _ _ _ _ HG0 Ha))).
ts_reg_x HS (2%bv : bv 5) X2. ts_reg_x HS (3%bv : bv 5) X3. ts_reg_x HS (4%bv : bv 5) X4.
ts_reg_x HS (8%bv : bv 5) X8. ts_reg_x HS (9%bv : bv 5) X9. ts_reg_x HS (10%bv : bv 5) X10.
ts_reg_x HS (12%bv : bv 5) X12. ts_reg_x HS (13%bv : bv 5) X13. ts_reg_x HS (14%bv : bv 5) X14.
ts_reg_x HS (18%bv : bv 5) X18. ts_reg_x HS (19%bv : bv 5) X19. ts_reg_x HS (20%bv : bv 5) X20.
ts_reg_x HS (21%bv : bv 5) X21. ts_reg_x HS (22%bv : bv 5) X22. ts_reg_x HS (24%bv : bv 5) X24.
ts_reg_x HS (26%bv : bv 5) X26. ts_reg_x HS (27%bv : bv 5) X27.
pmkst HS.
apply K. unfold DSC_xR.
eexists _, ly1, S1, [], _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
split; [reflexivity|].
split.
{ unfold dregs_top.
  split; [unfold spZ; rewrite X2, (dt_den_reg E 2 _ E2); exact Hsp|].
  split; [rewrite X3, (dt_den_reg E 3 _ E3); exact R3|].
  split; [rewrite X4, (dt_den_reg E 4 _ E4); exact R4|].
  split; [rewrite X21; exact (eq_trans (eq_sym R21') R21)|].
  split; [rewrite X24; exact (eq_trans (eq_sym R24') R24)|].
  split; [rewrite X20; exact (eq_trans (eq_sym R20') R20)|].
  split; [rewrite X22; exact (eq_trans (eq_sym R22') R22)|].
  split; [rewrite X27; exact (eq_trans (eq_sym R27') R27)|].
  split; [rewrite X8, (dt_den_reg E 8 _ E8); reflexivity|].
  split; [rewrite X9; exact (eq_trans (eq_sym R9') R9)|].
  split; [rewrite X18; exact (eq_trans (eq_sym R18') R18)
         |rewrite X26; exact (eq_trans (eq_sym R26') R26)]. }
split.
{ rewrite X10, (ts_den_add2 RG HGSB E 34 36 (re_used e1) (re_buf e1) E34 E36 ltac:(clear - Husedb; lia)
    ltac:(clear - Hbuf1; lia) ltac:(clear - Husedb Hcapb Hbuf2; lia)).
  unfold w64. f_equal. clear. lia. }
split; [rewrite X13; exact (ts_den_room RG HGSB E (re_cap e1) (re_used e1) E33 E34 ltac:(clear - Husedb; lia)
  ltac:(clear - Hcapb; lia))|].
split; [rewrite X14; exact (ts_den_sx RG E 37 (re_fd e1) E37 Hfdv)|].
split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal|].
split; [rewrite X19, (dt_den_reg E 35 _ E35); unfold w64; f_equal; cbn [Z.of_nat]; clear; lia|].
split; [clear; lia|].
split; [exact (ts_DMEM_kept_xR cx Hp ly1 S1 [] W1 m1 (ms_mem ms0) md1 _ k1 k1 e1 h1 sg out1 ev1
  (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
split; [exact HLINK|]. split; [exact HSAME|].
split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
split; [exact Hlater | exact Hbud].
Qed.

Theorem dt_scan_step_xR : dt_scan_step_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros cx Hp kr sg D i W1 c1 HB HDSC Knext Kfound.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
destruct HDSC as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & tl &
  Hcfg & Hregs & R10 & R13 & R14 & R12 & R19 & Hij & HMEM & HnoNUL & Hused & Hband & HLINK & HSAME &
  HHIST & HJ1 & Hroom & Hlater & Hbud).
pose proof Hregs as (Hsp & R3 & R4 & R21 & R24 & R20 & R22 & R27 & R8 & R9 & R18 & R26).
pose proof HMEM as (HJ & _ & _ & _ & _ & _ & _ & HEOK & Hsrc & Hoth & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hj4 & _ & _ & HfdB & _).
pose proof HSAME as (Sfd & Seof & Shfd & _).
assert (Hfdv : 0 <= re_fd e1 < 2 ^ 31) by (pose proof HEOK as (_ & _ & _ & _ & Hq & _); exact Hq).
assert (Hfd : hs_fd h1 = re_fd e1) by (rewrite Shfd, HfdB; exact (eq_sym Sfd)).
assert (Hi4 : (i < 4)%nat) by (clear - Hij Hj4; lia).
pose proof HGSB as (HGS1 & HGS2 & HGS8). unfold ASRC in HGS2. unfold IMG_TOP in HGS2.
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
(* the four slots of g_s, as the scan reads them *)
assert (Hslot : forall ii, (ii < 4)%nat -> exists f o,
  val_mem SEGS (arm W1 m1) (rg_s RG + 96 * Z.of_nat ii) 4 f /\
  val_mem SEGS (arm W1 m1) (rg_s RG + 96 * Z.of_nat ii + 4) 4 o /\
  0 <= f < 2 ^ 32 /\ 0 <= o < 2 ^ 32 /\
  (ii = dxj cx -> f = re_fd e1 /\ o <> 0) /\
  (ii <> dxj cx -> o = 0 \/ f <> re_fd e1)).
{ intros ii Hii. destruct (Nat.eq_dec ii (dxj cx)) as [->|Hne].
  - pose proof Hsrc as (V1 & V2 & _ & _ & _ & _ & _ & Hopen & Hfdr & _).
    unfold dHA, ASRC in V1, V2.
    exists (hs_fd h1), (hs_open h1).
    split; [exact V1|]. split; [exact V2|]. split; [clear - Hfdr; lia|].
    split; [rewrite Hopen; clear; lia|].
    split; [intros _; split; [exact Hfd | rewrite Hopen; clear; lia]|]. intros Hcc; contradiction.
  - assert (HfdvX : 0 <= re_fd (dxe cx) < 2 ^ 31) by (rewrite <- Sfd; exact Hfdv).
    destruct (ts_others_canon RG HGSB W1 m1 (dxj cx) (re_fd (dxe cx)) ii Hoth Hii Hne HfdvX)
      as (f & o & V1 & V2 & Bf & Bo & Hdis).
    unfold ASRC in V1, V2.
    exists f, o. split; [exact V1|]. split; [exact V2|]. split; [exact Bf|]. split; [exact Bo|].
    split; [intros Hcc; contradiction|]. intros _. rewrite Sfd.
    destruct Hdis as [Hq|Hq]; [left; exact Hq|right].
    rewrite (Z.mod_small f (2 ^ 32)) in Hq by (clear - Bf; lia).
    rewrite (Z.mod_small (re_fd (dxe cx)) (2 ^ 32)) in Hq by (clear - HfdvX; lia). exact Hq. }
destruct (Hslot 0%nat ltac:(clear; lia)) as (f0 & o0 & V00 & V01 & B00 & B01 & Hjj0 & Hoo0).
destruct (Hslot 1%nat ltac:(clear; lia)) as (f1 & o1 & V10 & V11 & B10 & B11 & Hjj1 & Hoo1).
destruct (Hslot 2%nat ltac:(clear; lia)) as (f2 & o2 & V20 & V21 & B20 & B21 & Hjj2 & Hoo2).
destruct (Hslot 3%nat ltac:(clear; lia)) as (f3 & o3 & V30 & V31 & B30 & B31 & Hjj3 & Hoo3).
clear Hslot.
replace (rg_s RG + 96 * Z.of_nat 0) with (rg_s RG) in V00 by (clear; lia).
replace (rg_s RG + 96 * Z.of_nat 0 + 4) with (rg_s RG + 4) in V01 by (clear; lia).
replace (rg_s RG + 96 * Z.of_nat 1) with (rg_s RG + 96) in V10 by (clear; lia).
replace (rg_s RG + 96 * Z.of_nat 1 + 4) with (rg_s RG + 100) in V11 by (clear; lia).
replace (rg_s RG + 96 * Z.of_nat 2) with (rg_s RG + 192) in V20 by (clear; lia).
replace (rg_s RG + 96 * Z.of_nat 2 + 4) with (rg_s RG + 196) in V21 by (clear; lia).
replace (rg_s RG + 96 * Z.of_nat 3) with (rg_s RG + 288) in V30 by (clear; lia).
replace (rg_s RG + 96 * Z.of_nat 3 + 4) with (rg_s RG + 292) in V31 by (clear; lia).
subst c1. unfold cfg_at, w64.
remember (Eimg (Ereg regs1 (ts_dsc_extra f0 o0 f1 o1 f2 o2 f3 o3))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (Q2 : ew E 2 = getr regs1 2) by (apply EREG; [clear; lia | reflexivity]).
assert (Q3 : ew E 3 = getr regs1 3) by (apply EREG; [clear; lia | reflexivity]).
assert (Q4 : ew E 4 = getr regs1 4) by (apply EREG; [clear; lia | reflexivity]).
assert (Q8 : ew E 8 = getr regs1 8) by (apply EREG; [clear; lia | reflexivity]).
assert (Q9 : ew E 9 = getr regs1 9) by (apply EREG; [clear; lia | reflexivity]).
assert (Q10 : ew E 10 = getr regs1 10) by (apply EREG; [clear; lia | reflexivity]).
assert (Q13 : ew E 13 = getr regs1 13) by (apply EREG; [clear; lia | reflexivity]).
assert (Q14 : ew E 14 = getr regs1 14) by (apply EREG; [clear; lia | reflexivity]).
assert (Q18 : ew E 18 = getr regs1 18) by (apply EREG; [clear; lia | reflexivity]).
assert (Q19 : ew E 19 = getr regs1 19) by (apply EREG; [clear; lia | reflexivity]).
assert (Q20 : ew E 20 = getr regs1 20) by (apply EREG; [clear; lia | reflexivity]).
assert (Q21 : ew E 21 = getr regs1 21) by (apply EREG; [clear; lia | reflexivity]).
assert (Q22 : ew E 22 = getr regs1 22) by (apply EREG; [clear; lia | reflexivity]).
assert (Q24 : ew E 24 = getr regs1 24) by (apply EREG; [clear; lia | reflexivity]).
assert (Q26 : ew E 26 = getr regs1 26) by (apply EREG; [clear; lia | reflexivity]).
assert (Q27 : ew E 27 = getr regs1 27) by (apply EREG; [clear; lia | reflexivity]).
assert (R26' : getr regs1 26 = sv_denot E (SLit 384))
  by (rewrite denot_lit_U, U_lit by (clear; lia); exact R26).
assert (E8 : ew E 8 = Z_to_bv 64 (rg_s RG)) by (rewrite Q8; exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 ((rg_s RG + 0) / 8)) by (rewrite Q9, Z.add_0_r; exact R9).
assert (E14 : ew E 14 = Z_to_bv 64 (re_fd e1)) by (rewrite Q14; exact R14).
assert (E18 : ew E 18 = Z_to_bv 64 ((rg_s RG + 4) / 8)) by (rewrite Q18; exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 (SHADOW_OFF + 12 * Z.of_nat i)) by (rewrite Q19; exact R19).
assert (E32 : ew E 32 = Z_to_bv 64 f0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 o0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 f1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 o1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 f2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 o2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 f3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 o3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 8)).
assert (U8 : bv_unsigned (ew E 8) = rg_s RG)
  by (rewrite E8; apply unsigned_lit_small; clear - HGS1 HGS2; lia).
assert (U35 : bv_unsigned (ew E 35) = SHADOW_OFF)
  by (rewrite E35; apply unsigned_lit_small; unfold SHADOW_OFF; clear; lia).
assert (SHOK : sh_ok SEGS BxT SHdsc E (mrestrict (w_H W1) m1)).
{ unfold SHdsc, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (ts_shent_azs_x ly1 S1 Hp1 W1 m1 md1 E 8 (rg_s RG) 384 HAR);
    [ change 384 with (4 * ASRC); exact HGSZ
    | exact (U_atom E 35 SHADOW_OFF E35 ltac:(unfold SHADOW_OFF; clear; lia))
    | exact (U_atom E 8 (rg_s RG) E8 ltac:(clear - HGS1 HGS2; lia))
    | clear; lia | clear - HGS1; lia | unfold IMG_TOP; clear - HGS2; lia ]. }
assert (HS : st_ok_pi SEGS VAL E (ss_dsc i)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_scan)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_dsc. apply pa_entry_st_ok_full.
  - apply regs_ok_pin;
      [ apply regs_ok_pin;
          [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact R12]
      | intros X; discriminate X
      | cbn [sv_denot]; exact R26 ].
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ts_dsc_gs.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [base_val]. rewrite U8. split; [clear - HGS1; lia|]. split; [clear - HGS1 HGS2; lia|].
    split; [intros o Ho; clear - Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 32 0) f0);
        [exact (den_atom0 E 32 f0 E32 ltac:(clear - B00; lia)) | clear - B00; zside | zside
        | rewrite Z.add_0_r; exact V00].
    + apply (chunk_ok_val SEGS E _ _ 4 4 (SOff 33 0) o0);
        [exact (den_atom0 E 33 o0 E33 ltac:(clear - B01; lia)) | clear - B01; zside | zside | exact V01].
    + apply (chunk_ok_val SEGS E _ _ 96 4 (SOff 34 0) f1);
        [exact (den_atom0 E 34 f1 E34 ltac:(clear - B10; lia)) | clear - B10; zside | zside | exact V10].
    + apply (chunk_ok_val SEGS E _ _ 100 4 (SOff 36 0) o1);
        [exact (den_atom0 E 36 o1 E36 ltac:(clear - B11; lia)) | clear - B11; zside | zside | exact V11].
    + apply (chunk_ok_val SEGS E _ _ 192 4 (SOff 37 0) f2);
        [exact (den_atom0 E 37 f2 E37 ltac:(clear - B20; lia)) | clear - B20; zside | zside | exact V20].
    + apply (chunk_ok_val SEGS E _ _ 196 4 (SOff 38 0) o2);
        [exact (den_atom0 E 38 o2 E38 ltac:(clear - B21; lia)) | clear - B21; zside | zside | exact V21].
    + apply (chunk_ok_val SEGS E _ _ 288 4 (SOff 39 0) f3);
        [exact (den_atom0 E 39 f3 E39 ltac:(clear - B30; lia)) | clear - B30; zside | zside | exact V30].
    + apply (chunk_ok_val SEGS E _ _ 292 4 (SOff 40 0) o3);
        [exact (den_atom0 E 40 o3 E40 ltac:(clear - B31; lia)) | clear - B31; zside | zside | exact V31].
  - cbn [pairwise_disjoint]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [ts_dsc_facts f_atoms atoms_ok]. unfold afact_ok, dt_IMGF. cbn [af_lo af_hi af_al2].
    rewrite U8, U35. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert HGS1 HGS2 HGS8. clear. unfold SB, SHADOW_OFF, IMG_TOP. intros.
    repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
destruct i as [|[|[|[|i]]]]; [| | | | clear - Hij Hj4; lia].
- paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan ts_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  ts_reg_x HS (11%bv : bv 5) Ra1.
  pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 0 + 4)) HS
    (eq_trans Ra1 (ts_den_add_sh RG HGSB E 18 (rg_s RG) 4 (Z.of_nat 0) E18 E19 E8 E35 HGS8
       ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
       ltac:(clear; lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok_xR RUNG HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUNG BRR HS SHOK DBspan.
  + (* g_s[0].open = 0: the slot is closed, on to the next *)
    rewrite (ts_beqz_sx RG E 33 o0 E33 ltac:(clear - B01; lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (0 <> dxj cx)%nat) by (intros Hq; destruct (Hjj0 Hq) as (_ & Ho); exact (Ho Hc)).
    paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
    rewrite ?wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    ts_reg_x HS (2%bv : bv 5) X2. ts_reg_x HS (3%bv : bv 5) X3. ts_reg_x HS (4%bv : bv 5) X4.
    ts_reg_x HS (8%bv : bv 5) X8. ts_reg_x HS (9%bv : bv 5) X9. ts_reg_x HS (10%bv : bv 5) X10.
    ts_reg_x HS (12%bv : bv 5) X12. ts_reg_x HS (13%bv : bv 5) X13. ts_reg_x HS (14%bv : bv 5) X14.
    ts_reg_x HS (18%bv : bv 5) X18. ts_reg_x HS (19%bv : bv 5) X19. ts_reg_x HS (20%bv : bv 5) X20.
    ts_reg_x HS (21%bv : bv 5) X21. ts_reg_x HS (22%bv : bv 5) X22. ts_reg_x HS (24%bv : bv 5) X24.
    ts_reg_x HS (26%bv : bv 5) X26. ts_reg_x HS (27%bv : bv 5) X27.
    pmkst HS.
    apply Knext. unfold DSC_xR.
    eexists _, ly1, S1, Hp1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
    split; [reflexivity|].
    split.
    { apply (ts_dregs_eq RG cx regs1 _ Hregs).
      - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
      - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
      - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
      - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
      - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
      - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
      - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
      - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
      - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
      - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
      - exact (eq_trans X26 (eq_sym R26')).
      - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
    split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
    split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
    split; [rewrite X14, (dt_den_reg E 14 _ Q14); exact R14|].
    split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; clear; lia|].
    split.
    { rewrite X19. cbn [sv_denot]. rewrite Q19, R19.
      unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; clear; lia).
      f_equal; cbn [Z.of_nat]; clear; lia. }
    split; [clear - Hij Hne0; lia|].
    split; [exact (ts_DMEM_kept_xR cx Hp ly1 S1 Hp1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 sg out1 ev1
      (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
    split; [exact HLINK|]. split; [exact HSAME|].
    split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
    split; [exact Hlater | exact Hbud].
  + paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan ts_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    ts_reg_x HS (11%bv : bv 5) Ra1.
    pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 0 + 0)) HS
      (eq_trans Ra1 (ts_den_add_sh RG HGSB E 9 (rg_s RG) 0 (Z.of_nat 0) E9 E19 E8 E35 HGS8
         ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
         ltac:(clear; lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok_xR RUNG HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUNG BRR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite (ts_beq_sx RG HGSB E 32 14 f0 (re_fd e1) E32 E14 ltac:(clear - B00; lia) Hfdv) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite (ts_beqz_sx RG E 33 o0 E33 ltac:(clear - B01; lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (0 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 0 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            exfalso; destruct (Hoo0 Hq) as [Ho|Hf]; [exact (Hc Ho) | exact (Hf Hc0)]).
      paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite ?wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      ts_reg_x HS (2%bv : bv 5) X2. ts_reg_x HS (3%bv : bv 5) X3. ts_reg_x HS (4%bv : bv 5) X4.
      ts_reg_x HS (8%bv : bv 5) X8. ts_reg_x HS (9%bv : bv 5) X9. ts_reg_x HS (10%bv : bv 5) X10.
      ts_reg_x HS (13%bv : bv 5) X13. ts_reg_x HS (18%bv : bv 5) X18. ts_reg_x HS (19%bv : bv 5) X19.
      ts_reg_x HS (20%bv : bv 5) X20. ts_reg_x HS (21%bv : bv 5) X21. ts_reg_x HS (22%bv : bv 5) X22.
      ts_reg_x HS (23%bv : bv 5) X23. ts_reg_x HS (24%bv : bv 5) X24. ts_reg_x HS (26%bv : bv 5) X26.
      ts_reg_x HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2_xR.
      eexists _, ly1, S1, Hp1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split.
      { apply (ts_dregs_eq RG cx regs1 _ Hregs).
        - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
        - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
        - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
        - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
        - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
        - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
        - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
        - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
        - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
        - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
        - exact (eq_trans X26 (eq_sym R26')).
        - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
      split.
      { rewrite X23, (den_atom E 8 (rg_s RG) 0 E8 ltac:(clear - HGS1 HGS2; lia)
          ltac:(clear - HGS1 HGS2; lia)).
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split.
      { rewrite X19, (dt_den_reg E 19 _ Q19), R19. rewrite <- Hj0.
        unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
      split; [exact (ts_DMEM_kept_xR cx Hp ly1 S1 Hp1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
      split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: on to the next *)
      rewrite (ts_beq_sx RG HGSB E 32 14 f0 (re_fd e1) E32 E14 ltac:(clear - B00; lia) Hfdv) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (0 <> dxj cx)%nat) by (intros Hq; destruct (Hjj0 Hq) as (Hf & _); exact (Hc0 Hf)).
      paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite ?wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      ts_reg_x HS (2%bv : bv 5) X2. ts_reg_x HS (3%bv : bv 5) X3. ts_reg_x HS (4%bv : bv 5) X4.
      ts_reg_x HS (8%bv : bv 5) X8. ts_reg_x HS (9%bv : bv 5) X9. ts_reg_x HS (10%bv : bv 5) X10.
      ts_reg_x HS (12%bv : bv 5) X12. ts_reg_x HS (13%bv : bv 5) X13. ts_reg_x HS (14%bv : bv 5) X14.
      ts_reg_x HS (18%bv : bv 5) X18. ts_reg_x HS (19%bv : bv 5) X19. ts_reg_x HS (20%bv : bv 5) X20.
      ts_reg_x HS (21%bv : bv 5) X21. ts_reg_x HS (22%bv : bv 5) X22. ts_reg_x HS (24%bv : bv 5) X24.
      ts_reg_x HS (26%bv : bv 5) X26. ts_reg_x HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Knext. unfold DSC_xR.
      eexists _, ly1, S1, Hp1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split.
      { apply (ts_dregs_eq RG cx regs1 _ Hregs).
        - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
        - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
        - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
        - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
        - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
        - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
        - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
        - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
        - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
        - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
        - exact (eq_trans X26 (eq_sym R26')).
        - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
      split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
      split; [rewrite X14, (dt_den_reg E 14 _ Q14); exact R14|].
      split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; clear; lia|].
      split.
      { rewrite X19. cbn [sv_denot]. rewrite Q19, R19.
        unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; clear; lia).
        f_equal; cbn [Z.of_nat]; clear; lia. }
      split; [clear - Hij Hne0; lia|].
      split; [exact (ts_DMEM_kept_xR cx Hp ly1 S1 Hp1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
      split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
- paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan ts_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  ts_reg_x HS (11%bv : bv 5) Ra1.
  pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 1 + 4)) HS
    (eq_trans Ra1 (ts_den_add_sh RG HGSB E 18 (rg_s RG) 4 (Z.of_nat 1) E18 E19 E8 E35 HGS8
       ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
       ltac:(clear; lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok_xR RUNG HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUNG BRR HS SHOK DBspan.
  + (* g_s[1].open = 0: the slot is closed, on to the next *)
    rewrite (ts_beqz_sx RG E 36 o1 E36 ltac:(clear - B11; lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (1 <> dxj cx)%nat) by (intros Hq; destruct (Hjj1 Hq) as (_ & Ho); exact (Ho Hc)).
    paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
    rewrite ?wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    ts_reg_x HS (2%bv : bv 5) X2. ts_reg_x HS (3%bv : bv 5) X3. ts_reg_x HS (4%bv : bv 5) X4.
    ts_reg_x HS (8%bv : bv 5) X8. ts_reg_x HS (9%bv : bv 5) X9. ts_reg_x HS (10%bv : bv 5) X10.
    ts_reg_x HS (12%bv : bv 5) X12. ts_reg_x HS (13%bv : bv 5) X13. ts_reg_x HS (14%bv : bv 5) X14.
    ts_reg_x HS (18%bv : bv 5) X18. ts_reg_x HS (19%bv : bv 5) X19. ts_reg_x HS (20%bv : bv 5) X20.
    ts_reg_x HS (21%bv : bv 5) X21. ts_reg_x HS (22%bv : bv 5) X22. ts_reg_x HS (24%bv : bv 5) X24.
    ts_reg_x HS (26%bv : bv 5) X26. ts_reg_x HS (27%bv : bv 5) X27.
    pmkst HS.
    apply Knext. unfold DSC_xR.
    eexists _, ly1, S1, Hp1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
    split; [reflexivity|].
    split.
    { apply (ts_dregs_eq RG cx regs1 _ Hregs).
      - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
      - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
      - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
      - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
      - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
      - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
      - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
      - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
      - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
      - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
      - exact (eq_trans X26 (eq_sym R26')).
      - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
    split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
    split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
    split; [rewrite X14, (dt_den_reg E 14 _ Q14); exact R14|].
    split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; clear; lia|].
    split.
    { rewrite X19. cbn [sv_denot]. rewrite Q19, R19.
      unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; clear; lia).
      f_equal; cbn [Z.of_nat]; clear; lia. }
    split; [clear - Hij Hne0; lia|].
    split; [exact (ts_DMEM_kept_xR cx Hp ly1 S1 Hp1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 sg out1 ev1
      (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
    split; [exact HLINK|]. split; [exact HSAME|].
    split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
    split; [exact Hlater | exact Hbud].
  + paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan ts_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    ts_reg_x HS (11%bv : bv 5) Ra1.
    pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 1 + 0)) HS
      (eq_trans Ra1 (ts_den_add_sh RG HGSB E 9 (rg_s RG) 0 (Z.of_nat 1) E9 E19 E8 E35 HGS8
         ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
         ltac:(clear; lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok_xR RUNG HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUNG BRR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite (ts_beq_sx RG HGSB E 34 14 f1 (re_fd e1) E34 E14 ltac:(clear - B10; lia) Hfdv) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite (ts_beqz_sx RG E 36 o1 E36 ltac:(clear - B11; lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (1 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 1 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            exfalso; destruct (Hoo1 Hq) as [Ho|Hf]; [exact (Hc Ho) | exact (Hf Hc0)]).
      paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite ?wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      ts_reg_x HS (2%bv : bv 5) X2. ts_reg_x HS (3%bv : bv 5) X3. ts_reg_x HS (4%bv : bv 5) X4.
      ts_reg_x HS (8%bv : bv 5) X8. ts_reg_x HS (9%bv : bv 5) X9. ts_reg_x HS (10%bv : bv 5) X10.
      ts_reg_x HS (13%bv : bv 5) X13. ts_reg_x HS (18%bv : bv 5) X18. ts_reg_x HS (19%bv : bv 5) X19.
      ts_reg_x HS (20%bv : bv 5) X20. ts_reg_x HS (21%bv : bv 5) X21. ts_reg_x HS (22%bv : bv 5) X22.
      ts_reg_x HS (23%bv : bv 5) X23. ts_reg_x HS (24%bv : bv 5) X24. ts_reg_x HS (26%bv : bv 5) X26.
      ts_reg_x HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2_xR.
      eexists _, ly1, S1, Hp1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split.
      { apply (ts_dregs_eq RG cx regs1 _ Hregs).
        - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
        - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
        - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
        - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
        - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
        - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
        - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
        - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
        - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
        - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
        - exact (eq_trans X26 (eq_sym R26')).
        - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
      split.
      { rewrite X23, (den_atom E 8 (rg_s RG) 96 E8 ltac:(clear - HGS1 HGS2; lia)
          ltac:(clear - HGS1 HGS2; lia)).
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split.
      { rewrite X19, (dt_den_reg E 19 _ Q19), R19. rewrite <- Hj0.
        unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
      split; [exact (ts_DMEM_kept_xR cx Hp ly1 S1 Hp1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
      split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: on to the next *)
      rewrite (ts_beq_sx RG HGSB E 34 14 f1 (re_fd e1) E34 E14 ltac:(clear - B10; lia) Hfdv) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (1 <> dxj cx)%nat) by (intros Hq; destruct (Hjj1 Hq) as (Hf & _); exact (Hc0 Hf)).
      paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite ?wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      ts_reg_x HS (2%bv : bv 5) X2. ts_reg_x HS (3%bv : bv 5) X3. ts_reg_x HS (4%bv : bv 5) X4.
      ts_reg_x HS (8%bv : bv 5) X8. ts_reg_x HS (9%bv : bv 5) X9. ts_reg_x HS (10%bv : bv 5) X10.
      ts_reg_x HS (12%bv : bv 5) X12. ts_reg_x HS (13%bv : bv 5) X13. ts_reg_x HS (14%bv : bv 5) X14.
      ts_reg_x HS (18%bv : bv 5) X18. ts_reg_x HS (19%bv : bv 5) X19. ts_reg_x HS (20%bv : bv 5) X20.
      ts_reg_x HS (21%bv : bv 5) X21. ts_reg_x HS (22%bv : bv 5) X22. ts_reg_x HS (24%bv : bv 5) X24.
      ts_reg_x HS (26%bv : bv 5) X26. ts_reg_x HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Knext. unfold DSC_xR.
      eexists _, ly1, S1, Hp1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split.
      { apply (ts_dregs_eq RG cx regs1 _ Hregs).
        - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
        - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
        - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
        - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
        - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
        - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
        - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
        - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
        - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
        - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
        - exact (eq_trans X26 (eq_sym R26')).
        - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
      split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
      split; [rewrite X14, (dt_den_reg E 14 _ Q14); exact R14|].
      split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; clear; lia|].
      split.
      { rewrite X19. cbn [sv_denot]. rewrite Q19, R19.
        unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; clear; lia).
        f_equal; cbn [Z.of_nat]; clear; lia. }
      split; [clear - Hij Hne0; lia|].
      split; [exact (ts_DMEM_kept_xR cx Hp ly1 S1 Hp1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
      split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
- paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan ts_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  ts_reg_x HS (11%bv : bv 5) Ra1.
  pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 2 + 4)) HS
    (eq_trans Ra1 (ts_den_add_sh RG HGSB E 18 (rg_s RG) 4 (Z.of_nat 2) E18 E19 E8 E35 HGS8
       ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
       ltac:(clear; lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok_xR RUNG HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUNG BRR HS SHOK DBspan.
  + (* g_s[2].open = 0: the slot is closed, on to the next *)
    rewrite (ts_beqz_sx RG E 38 o2 E38 ltac:(clear - B21; lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (2 <> dxj cx)%nat) by (intros Hq; destruct (Hjj2 Hq) as (_ & Ho); exact (Ho Hc)).
    paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
    rewrite ?wvb_collapse in HJ.
    lazymatch type of HFr with frame_of _ ?rs _ _ =>
      assert (N0 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
      assert (N1 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
      assert (N2 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
    assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
    { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
      rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
      exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
    assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
            (apresent_grows _ _ _ _ HG0 Ha)))).
    ts_reg_x HS (2%bv : bv 5) X2. ts_reg_x HS (3%bv : bv 5) X3. ts_reg_x HS (4%bv : bv 5) X4.
    ts_reg_x HS (8%bv : bv 5) X8. ts_reg_x HS (9%bv : bv 5) X9. ts_reg_x HS (10%bv : bv 5) X10.
    ts_reg_x HS (12%bv : bv 5) X12. ts_reg_x HS (13%bv : bv 5) X13. ts_reg_x HS (14%bv : bv 5) X14.
    ts_reg_x HS (18%bv : bv 5) X18. ts_reg_x HS (19%bv : bv 5) X19. ts_reg_x HS (20%bv : bv 5) X20.
    ts_reg_x HS (21%bv : bv 5) X21. ts_reg_x HS (22%bv : bv 5) X22. ts_reg_x HS (24%bv : bv 5) X24.
    ts_reg_x HS (26%bv : bv 5) X26. ts_reg_x HS (27%bv : bv 5) X27.
    pmkst HS.
    apply Knext. unfold DSC_xR.
    eexists _, ly1, S1, Hp1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
    split; [reflexivity|].
    split.
    { apply (ts_dregs_eq RG cx regs1 _ Hregs).
      - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
      - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
      - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
      - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
      - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
      - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
      - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
      - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
      - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
      - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
      - exact (eq_trans X26 (eq_sym R26')).
      - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
    split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
    split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
    split; [rewrite X14, (dt_den_reg E 14 _ Q14); exact R14|].
    split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; clear; lia|].
    split.
    { rewrite X19. cbn [sv_denot]. rewrite Q19, R19.
      unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; clear; lia).
      f_equal; cbn [Z.of_nat]; clear; lia. }
    split; [clear - Hij Hne0; lia|].
    split; [exact (ts_DMEM_kept_xR cx Hp ly1 S1 Hp1 W1 m1 (ms_mem ms1) md1 _ k1 k1 e1 h1 sg out1 ev1
      (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
    split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
    split; [exact HLINK|]. split; [exact HSAME|].
    split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
    split; [exact Hlater | exact Hbud].
  + paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan ts_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    ts_reg_x HS (11%bv : bv 5) Ra1.
    pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 2 + 0)) HS
      (eq_trans Ra1 (ts_den_add_sh RG HGSB E 9 (rg_s RG) 0 (Z.of_nat 2) E9 E19 E8 E35 HGS8
         ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
         ltac:(clear; lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok_xR RUNG HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUNG BRR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite (ts_beq_sx RG HGSB E 37 14 f2 (re_fd e1) E37 E14 ltac:(clear - B20; lia) Hfdv) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite (ts_beqz_sx RG E 38 o2 E38 ltac:(clear - B21; lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (2 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 2 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            exfalso; destruct (Hoo2 Hq) as [Ho|Hf]; [exact (Hc Ho) | exact (Hf Hc0)]).
      paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite ?wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      ts_reg_x HS (2%bv : bv 5) X2. ts_reg_x HS (3%bv : bv 5) X3. ts_reg_x HS (4%bv : bv 5) X4.
      ts_reg_x HS (8%bv : bv 5) X8. ts_reg_x HS (9%bv : bv 5) X9. ts_reg_x HS (10%bv : bv 5) X10.
      ts_reg_x HS (13%bv : bv 5) X13. ts_reg_x HS (18%bv : bv 5) X18. ts_reg_x HS (19%bv : bv 5) X19.
      ts_reg_x HS (20%bv : bv 5) X20. ts_reg_x HS (21%bv : bv 5) X21. ts_reg_x HS (22%bv : bv 5) X22.
      ts_reg_x HS (23%bv : bv 5) X23. ts_reg_x HS (24%bv : bv 5) X24. ts_reg_x HS (26%bv : bv 5) X26.
      ts_reg_x HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2_xR.
      eexists _, ly1, S1, Hp1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split.
      { apply (ts_dregs_eq RG cx regs1 _ Hregs).
        - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
        - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
        - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
        - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
        - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
        - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
        - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
        - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
        - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
        - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
        - exact (eq_trans X26 (eq_sym R26')).
        - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
      split.
      { rewrite X23, (den_atom E 8 (rg_s RG) 192 E8 ltac:(clear - HGS1 HGS2; lia)
          ltac:(clear - HGS1 HGS2; lia)).
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split.
      { rewrite X19, (dt_den_reg E 19 _ Q19), R19. rewrite <- Hj0.
        unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
      split; [exact (ts_DMEM_kept_xR cx Hp ly1 S1 Hp1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
      split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: on to the next *)
      rewrite (ts_beq_sx RG HGSB E 37 14 f2 (re_fd e1) E37 E14 ltac:(clear - B20; lia) Hfdv) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (2 <> dxj cx)%nat) by (intros Hq; destruct (Hjj2 Hq) as (Hf & _); exact (Hc0 Hf)).
      paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan A_dr_scan. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite ?wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      ts_reg_x HS (2%bv : bv 5) X2. ts_reg_x HS (3%bv : bv 5) X3. ts_reg_x HS (4%bv : bv 5) X4.
      ts_reg_x HS (8%bv : bv 5) X8. ts_reg_x HS (9%bv : bv 5) X9. ts_reg_x HS (10%bv : bv 5) X10.
      ts_reg_x HS (12%bv : bv 5) X12. ts_reg_x HS (13%bv : bv 5) X13. ts_reg_x HS (14%bv : bv 5) X14.
      ts_reg_x HS (18%bv : bv 5) X18. ts_reg_x HS (19%bv : bv 5) X19. ts_reg_x HS (20%bv : bv 5) X20.
      ts_reg_x HS (21%bv : bv 5) X21. ts_reg_x HS (22%bv : bv 5) X22. ts_reg_x HS (24%bv : bv 5) X24.
      ts_reg_x HS (26%bv : bv 5) X26. ts_reg_x HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Knext. unfold DSC_xR.
      eexists _, ly1, S1, Hp1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split.
      { apply (ts_dregs_eq RG cx regs1 _ Hregs).
        - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
        - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
        - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
        - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
        - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
        - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
        - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
        - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
        - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
        - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
        - exact (eq_trans X26 (eq_sym R26')).
        - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
      split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
      split; [rewrite X14, (dt_den_reg E 14 _ Q14); exact R14|].
      split; [rewrite X12; cbn [sv_denot]; unfold w64; f_equal; clear; lia|].
      split.
      { rewrite X19. cbn [sv_denot]. rewrite Q19, R19.
        unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; clear; lia).
        f_equal; cbn [Z.of_nat]; clear; lia. }
      split; [clear - Hij Hne0; lia|].
      split; [exact (ts_DMEM_kept_xR cx Hp ly1 S1 Hp1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
      split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
- paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan ts_shl1. { apply awr_ok_x_of0. awr_ok_tac. }
  ts_reg_x HS (11%bv : bv 5) Ra1.
  pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 3 + 4)) HS
    (eq_trans Ra1 (ts_den_add_sh RG HGSB E 18 (rg_s RG) 4 (Z.of_nat 3) E18 E19 E8 E35 HGS8
       ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
       ltac:(clear; lia))) eq_refl) as HS'.
  clear HS Ra1. rename HS' into HS.
  paj_run_tok_xR RUNG HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
  psrr_branch_tok RUNG BRR HS SHOK DBspan.
  + (* g_s[3].open = 0: refuted, the scan reaches the harness's own slot j <= 3 first *)
    rewrite (ts_beqz_sx RG E 40 o3 E40 ltac:(clear - B31; lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (Hne0 : (3 <> dxj cx)%nat) by (intros Hq; destruct (Hjj3 Hq) as (_ & Ho); exact (Ho Hc)).
    exfalso. clear - Hij Hj4 Hne0. lia.
  + paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan ts_shl2. { apply awr_ok_x_of0. awr_ok_tac. }
    ts_reg_x HS (11%bv : bv 5) Ra1.
    pose proof (ts_reseat E _ _ 11%bv (dt_sh 8 (96 * Z.of_nat 3 + 0)) HS
      (eq_trans Ra1 (ts_den_add_sh RG HGSB E 9 (rg_s RG) 0 (Z.of_nat 3) E9 E19 E8 E35 HGS8
         ltac:(clear; lia) ltac:(clear - HGS1; lia) ltac:(unfold IMG_TOP; clear - HGS2; lia)
         ltac:(clear; lia))) eq_refl) as HS'.
    clear HS Ra1. rename HS' into HS.
    paj_run_tok_xR RUNG HS HJ SHOK DBspan. { apply awr_ok_x_of0. awr_ok_tac. }
    psrr_branch_tok RUNG BRR HS SHOK DBspan.
    * (* the slot's fd is s->fd: this is the harness's own slot *)
      rewrite (ts_beq_sx RG HGSB E 39 14 f3 (re_fd e1) E39 E14 ltac:(clear - B30; lia) Hfdv) in Hc0.
      apply Z.eqb_eq in Hc0.
      rewrite (ts_beqz_sx RG E 40 o3 E40 ltac:(clear - B31; lia)) in Hc. apply Z.eqb_neq in Hc.
      assert (Hj0 : (3 = dxj cx)%nat)
        by (destruct (Nat.eq_dec 3 (dxj cx)) as [Hq|Hq]; [exact Hq|];
            exfalso; destruct (Hoo3 Hq) as [Ho|Hf]; [exact (Hc Ho) | exact (Hf Hc0)]).
      paj_run_to_tok_xR RUNTOG HS HJ SHOK DBspan A_dr_slot. { apply awr_ok_x_of0. awr_ok_tac. }
      rewrite ?wvb_collapse in HJ.
      lazymatch type of HFr with frame_of _ ?rs _ _ =>
        assert (N0 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr0 with frame_of _ ?rs _ _ =>
        assert (N1 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
        assert (N2 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
        assert (N3 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      lazymatch type of HFr3 with frame_of _ ?rs _ _ =>
        assert (N4 : forall x, ~ in_wrange E rs x) by (apply (ts_nowr_lem RG HGSB); vm_compute; reflexivity) end.
      assert (KL : forall a, aview SEGS (w_H W1) (ms_mem ms3) a = aview SEGS (w_H W1) m1 a).
      { intros a. rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms2) (ms_mem ms3) a (HFr3 _ (N4 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms1) (ms_mem ms2) a (HFr2 _ (N3 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms0) (ms_mem ms1) a (HFr1 _ (N2 _))).
        rewrite (aview_eq_of SEGS (w_H W1) (ms_mem ms) (ms_mem ms0) a (HFr0 _ (N1 _))).
        exact (aview_eq_of SEGS (w_H W1) m1 (ms_mem ms) a (HFr _ (N0 _))). }
      assert (HPG : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ _ HG4 (apresent_grows _ _ _ _ HG3
              (apresent_grows _ _ _ _ HG2 (apresent_grows _ _ _ _ HG1
                 (apresent_grows _ _ _ _ HG0 Ha)))))).
      ts_reg_x HS (2%bv : bv 5) X2. ts_reg_x HS (3%bv : bv 5) X3. ts_reg_x HS (4%bv : bv 5) X4.
      ts_reg_x HS (8%bv : bv 5) X8. ts_reg_x HS (9%bv : bv 5) X9. ts_reg_x HS (10%bv : bv 5) X10.
      ts_reg_x HS (13%bv : bv 5) X13. ts_reg_x HS (18%bv : bv 5) X18. ts_reg_x HS (19%bv : bv 5) X19.
      ts_reg_x HS (20%bv : bv 5) X20. ts_reg_x HS (21%bv : bv 5) X21. ts_reg_x HS (22%bv : bv 5) X22.
      ts_reg_x HS (23%bv : bv 5) X23. ts_reg_x HS (24%bv : bv 5) X24. ts_reg_x HS (26%bv : bv 5) X26.
      ts_reg_x HS (27%bv : bv 5) X27.
      pmkst HS.
      apply Kfound. unfold DT2_xR.
      eexists _, ly1, S1, Hp1, _, _, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, tl.
      split; [reflexivity|].
      split.
      { apply (ts_dregs_eq RG cx regs1 _ Hregs).
        - exact (eq_trans X2 (dt_den_reg E 2 _ Q2)).
        - exact (eq_trans X3 (dt_den_reg E 3 _ Q3)).
        - exact (eq_trans X4 (dt_den_reg E 4 _ Q4)).
        - exact (eq_trans X8 (dt_den_reg E 8 _ Q8)).
        - exact (eq_trans X9 (dt_den_reg E 9 _ Q9)).
        - exact (eq_trans X18 (dt_den_reg E 18 _ Q18)).
        - exact (eq_trans X20 (dt_den_reg E 20 _ Q20)).
        - exact (eq_trans X21 (dt_den_reg E 21 _ Q21)).
        - exact (eq_trans X22 (dt_den_reg E 22 _ Q22)).
        - exact (eq_trans X24 (dt_den_reg E 24 _ Q24)).
        - exact (eq_trans X26 (eq_sym R26')).
        - exact (eq_trans X27 (dt_den_reg E 27 _ Q27)). }
      split.
      { rewrite X23, (den_atom E 8 (rg_s RG) 288 E8 ltac:(clear - HGS1 HGS2; lia)
          ltac:(clear - HGS1 HGS2; lia)).
        unfold dHA, ASRC. rewrite <- Hj0. unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split.
      { rewrite X19, (dt_den_reg E 19 _ Q19), R19. rewrite <- Hj0.
        unfold w64. f_equal; cbn [Z.of_nat]; clear; lia. }
      split; [rewrite X10, (dt_den_reg E 10 _ Q10); exact R10|].
      split; [rewrite X13, (dt_den_reg E 13 _ Q13); exact R13|].
      split; [exact (ts_DMEM_kept_xR cx Hp ly1 S1 Hp1 W1 m1 (ms_mem ms3) md1 _ k1 k1 e1 h1 sg out1 ev1
        (lines (dSTR cx) D) LB1 HMEM HJ KL HPG)|].
      split; [exact HnoNUL|]. split; [exact Hused|]. split; [exact Hband|].
      split; [exact HLINK|]. split; [exact HSAME|].
      split; [exact HHIST|]. split; [exact HJ1|]. split; [exact Hroom|].
      split; [exact Hlater | exact Hbud].
    * (* the slot is open but on another fd: refuted, j <= 3 and j <> 3 *)
      rewrite (ts_beq_sx RG HGSB E 39 14 f3 (re_fd e1) E39 E14 ltac:(clear - B30; lia) Hfdv) in Hc0.
      apply Z.eqb_neq in Hc0.
      assert (Hne0 : (3 <> dxj cx)%nat) by (intros Hq; destruct (Hjj3 Hq) as (Hf & _); exact (Hc0 Hf)).
      exfalso. clear - Hij Hj4 Hne0. lia.
Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R; the statements are the strict ones, checked by conversion). ---- *)
(* W_drain_tophead.v's dt_DMEM_kept over ARx: a stretch that writes no byte keeps the memory core *)
Lemma ts_DMEM_kept_x : forall cx Hp ly1 S1 Hp1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1,
DMEM_x B PST ARx RG cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k2 ->
(forall a, aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
DMEM_x B PST ARx RG cx Hp ly1 S1 Hp1 W1 m2 md2 k2 e1 h1 sg out1 ev1 sent LB1.
Proof. exact (ts_DMEM_kept_xR (@wle SEGS)). Qed.

(* ---- The stretch DT1_x 0x83438 -> DSC_x 0 at 0x83498 (dt_scan_entry's walk; ss_en, ts_en_extra). ---- *)
Theorem dt_scan_entry_x : dt_scan_entry_stmt_x B PST ARx MT RP MMAX RG.
Proof. exact (dt_scan_entry_xR (@wle SEGS)). Qed.

(* ---- The scan body DSC_x i -> DSC_x (S i) | DT2_x (dt_scan_step's walk; ss_dsc i, ts_dsc_extra). ---- *)
Theorem dt_scan_step_x : dt_scan_step_stmt_x B PST ARx MT RP MMAX RG.
Proof. exact (dt_scan_step_xR (@wle SEGS)). Qed.

End cxs.
End b.
End a.

(* ---- TOP over ARx (an internal work row; the image-B twin of A's dr_top_x, a working branch af2f55b6679):
   dr_top_x : W_drain_cx_x.v dr_top_stmt_x, from the head's leaves (W_drain_tophead.v dt_nogrow_x / dt_grow_x, this
   file's dt_scan_entry_x / dt_scan_step_x), composed as B composes the AR TOP (W_drain_tophead.v dr_tophead_of_x,
   dt_scan_of_x, dr_top_of_x), with the tail W_drain_topb_cx.v dr_toptail_stmt_x as the Section premise dt_tail_x
   (W_drain_topb.v proves it: dr_toptail_x).  Section cxt's hypotheses are Section cxs's, which are Section cxh's
   (W_drain_tophead.v), plus dt_tail_x. ---- *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section cxt.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Variable CTX_R : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
(* the tail, TOP's second half (W_drain_topb.v dr_toptail_x) *)
Hypothesis dt_tail_x : dr_toptail_stmt_x B PST ARx MT RP MMAX RG.

(* ---- route R: dr_top_xR, the R twin of dr_top_x, from the head's R twins (W_drain_tophead.v dt_nogrow_xR /
   dt_grow_xR, dr_tophead_of_xR, dt_scan_of_xR, dr_top_of_xR) and this file's dt_scan_entry_xR / dt_scan_step_xR, with the
   tail's R statement as the Section premise dt_tail_xR.  Realloc #1 is the R rule AREALLOC_R, whose call-boundary
   premises come from RO_ARx / HA_call.  The strict dr_top_x below is dr_top_xR at R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
Hypothesis AREALLOC_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HA CTX_R R (SIGMA WS_realloc).
Hypothesis dt_tail_xR : dr_toptail_stmt_xR B PST ARx MT RP MMAX RG R.

Theorem dr_top_xR : dr_top_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
apply (dr_top_of_xR B PST ARx MT RP MMAX RG R); [|exact dt_tail_xR].
apply (dr_tophead_of_xR B PST ARx MT RP MMAX RG R).
- eapply dt_nogrow_xR; eassumption.
- eapply dt_grow_xR; try exact AREALLOC_R; eassumption.
- apply (dt_scan_of_xR B PST ARx MT RP MMAX RG R).
  + eapply dt_scan_entry_xR; eassumption.
  + eapply dt_scan_step_xR; eassumption.
Qed.

End wR.

(* ---- the strict dr_top_x at R := wle: dr_top_xR above at wle (wle_trans for R_trans; the statement is the strict
   one, checked by conversion).  At wle realloc #1's R rule is the strict AREALLOC (arealloc_cf_rule_c_xR_of_x), with
   RO and HA at True, and the tail's R statement is dt_tail_x. ---- *)
Theorem dr_top_x : dr_top_stmt_x B PST ARx MT RP MMAX RG.
Proof.
exact (dr_top_xR (@wle SEGS) (@wle_trans SEGS) (fun _ => True) (fun _ _ _ _ _ _ => True)
  (fun _ _ _ _ _ _ _ => I) (fun _ _ _ _ _ _ _ => I) ltac:(apply arealloc_cf_rule_c_xR_of_x; exact AREALLOC) dt_tail_x).
Qed.

End cxt.
End b.
End a.

(* the zify flag files that Require this one saw before the generic kit was Required here (false: W_drain_tophead.v's
   setting), so that the kit's Requires above change nothing downstream *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
