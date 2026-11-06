(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from cgif's lib/A/ACgq.v and lib/A/ACk8.v (file header, walk tactic forms) for reac_ctrl_parse of libreac's fuzz_grant. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) segment of the reac_ctrl_parse 0x82774 walk, in the shape of lib/A/Prog/CtrlParseEpi.v at a working branch 603e40683a4 (image A 0x82000), over image B's listing and walk layer (lib/B/Prog), with image B's addresses and objects; image B's extra UBSan guards are decided by the engine from the atom facts. Source blob 2b3c8d40666f (lib/A/Prog/CtrlParseEpi.v at a working branch 603e40683a4; the same blob at 7e98c198edd). *)
(* reac_ctrl_parse, the walk from cut J (0x82b94, every path's join) to the return: the frame's shadow is
   poisoned, its flag cleared (the frame is released) and the saved registers reloaded. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantSyms GrantList GrantPa GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC45 YC85 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import CtrlParseLib KindOfLink1 GrantRo ACj1 GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import CtrlParseCut ACbf.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Lemma pz_segD : forall B G, pz_rt B G -> forall c, pz_ok B c -> pz_cutJ_spec B c.
Proof.
intros B G RT c Hok E ms md Hcur HS Ha0 Hout.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur. pz_std.
unfold YK0s.ret_ok in Hra.
pose proof (aj_flag_store_pi B LAWS ML ASF FFL) as RUNF.
pose proof (paj_ret_at (PL := PL_grant) (PI := PI)) as RET.
destruct (pz_nf_sep B LAWS lyc Sc S2 W (ms_mem ms) md fpos F FL HARc Hfrs2 Eab EF EFL FFL) as (N1 & N2 & N3 & N4).
(* 1. The flag byte FL as a writable region of one byte (the frame's flag pointer, chunk 120 of the frame,
   holds it; the epilogue stores 0 there). *)
assert (ROKF : region_ok SEGS E (ms_mem (restrict (w_H W) ms)) (YP09.mkRegion (Some 528%nat) 0 1 0 1 [])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
rewrite E528, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o0 Ho0. apply (apresent_writable SEGS). replace (FL + o0) with FL by lia. exact HFLpres. }
assert (RDJF : all_disjoint E (YP09.mkRegion (Some 528%nat) 0 1 0 1 []) (ss_mem ss_cutJ)).
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. pz_bases.
split; [|split; [|split; [|exact I]]].
- destruct (Z_lt_ge_dec FL (SB + F / 8)); [left; lia|].
destruct (Z_lt_ge_dec FL (SB + F / 8 + 16)); [exfalso | right; lia].
apply (proj2 (HFSpres (FL - (SB + F / 8)) ltac:(lia))). unfold shadow_addr. rewrite <- SB_SHADOW_OFF.
replace (SB + F / 8 + (FL - (SB + F / 8))) with FL by lia. exact HFLown.
- destruct (Z_lt_ge_dec FL F); [left; lia|].
destruct (Z_lt_ge_dec FL (F + 128)); [exfalso | right; lia].
exact (proj2 (HFpres FL ltac:(lia)) HFLown).
- left. lia. }
pose proof (st_ok_pi_add_region E ss_cutJ (restrict (w_H W) ms) (YP09.mkRegion (Some 528%nat) 0 1 0 1 []) HS eq_refl ROKF RDJF) as HS'.
clear HS ROKF RDJF; rename HS' into HS. pz_norm HS.
(* 2. The run from cut J to `ret`: the shadow bytes 4..8 marked 0xf8, the magic at F, `beqz s2` not taken
   (s2 = F >= 4096), all 16 shadow bytes marked 0xf5, the flag pointer loaded from F + 120 and the flag cleared,
   the saved registers reloaded and sp restored. The frame (1, fpos) leaves the journal's own frames. *)
paj_run_flag_sh RUNF HS HJ2.
{ lia. }
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end.
cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
revert Ha; pz_bases; intros Ha.
- right. rewrite <- EFL. lia.
- left. right; right; right. exists 1, fpos. split; [left; reflexivity|]. right.
rewrite <- EF. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
unfold SB in Ha. unfold SHADOW_OFF. lia.
- left. right; right; right. exists 1, fpos. split; [left; reflexivity|]. left.
rewrite <- EF. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
- left. left. lia. }
{ flag0 E528 EFL. }
(* 3. What the run kept: everything outside the stack slots of the saved registers, the own frame, its
   shadow bytes and its flag byte. *)
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp - 96 <= a < sp) \/ (F <= a < F + 128) \/ (SB + F / 8 <= a < SB + F / 8 + 16) \/ a = FL) a)
by (pz_win_tac ltac:(fun H => revert H; pz_bases; intros H)) end.
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ _ HFr Hw1) as Hkp.
pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc (ms_mem ms) md (ms_mem ms) (ms_mem ms0) (sp - TPARSE_STK) sp o fpos F FL
(fun a => (sp - 96 <= a < sp) \/ (F <= a < F + 128) \/ (SB + F / 8 <= a < SB + F / 8 + 16) \/ a = FL) co po
HAR HARc Hfrs2 Eab EF EFL FFL ltac:(lia) ltac:(lia) Hoin Holo Hohi
ltac:(intros a Ha; cbv beta in Ha; unfold pz_nf, SHADOW_OFF; unfold SB in Ha; lia) KP Hkp
(fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP2.
assert (Hout2 : forall i, (i < 36)%nat -> aview SEGS (w_H W) (ms_mem ms0) (o + Z.of_nat i) =
Some (bv_unsigned (nth i (snd (ctrlparse n fr)) cp_z))).
{ intros i Hi. rewrite Hkp; [exact (Hout i Hi) | lia |].
intros Hz. cbv beta in Hz. destruct Hz as [Hz | Hz]; [lia|].
apply (N3 co po (o + Z.of_nat i) Hoin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia|].
unfold pz_nf, SHADOW_OFF. unfold SB in Hz. lia. }
(* 4. `ret`: back at the caller's return address with the post-condition. *)
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold tctrl_parse_post. cbv beta.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?mm _) ?mdv = _ /\ _ =>
exists lyc, (stack_free_state 1 fpos S2), rg, mm, mdv end.
split; [rewrite R1; rewrite (AGX 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|].
split; [apply aregs_preserved_eqs; creg HS AGX EE|].
split.
{ change (frames (stack_free_state 1 fpos S2)) with (del_pos (frames S2) 1 fpos). rewrite Hfrs2. cbn [del_pos].
rewrite !Z.eqb_refl. reflexivity. }
split.
{ rewrite <- Eab. unfold ablocks. rewrite blocks_stack_free_state. reflexivity. }
split.
{ destruct ES2 as [ff ES2]. exists (mkFS (fs_hint (st_fs S2)) (del_pos (fs_live (st_fs S2)) 1 fpos)).
unfold stack_free_state. generalize (mkFS (fs_hint (st_fs S2)) (del_pos (fs_live (st_fs S2)) 1 fpos)). intros X.
rewrite ES2. reflexivity. }
split; [rewrite R10, Ha0; reflexivity|].
split; [exact Hout2|].
exact KP2.
Qed.
End d.
End b.
