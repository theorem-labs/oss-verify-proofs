(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from cgif's lib/A/ACgq.v and lib/A/ACk8.v (file header, walk tactic forms) for reac_ctrl_parse of libreac's fuzz_grant. *)
(* Modified by Theorem Labs, 2026-10: relocated to libreac/fuzz_disco (the same code at other addresses; the post side carries pz_kept, not acall_kept, and the caller's two objects name no frame). *)
(* reac_ctrl_parse, the walk from cut J (every path's join) to the return: the frame's shadow is
   poisoned, its flag cleared (the frame is released) and the saved registers reloaded. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC81 YC4b YC1g YC1h YC45 YC85 DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import CtrlParse CtrlParseLib KindOfLink1 DiscoRo ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import CtrlParseCut ACbf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg disco_listing}.
Context {RO : ro_below_ofl (@pa_segs _ disco_listing PI) (@pa_relro_lo _ disco_listing PI) (@pa_relro_hi _ disco_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
(* The bytes of a list, read one at a time, are the list as garr8 holds it (the post's out struct). *)
Lemma pz_garr8_of_view : forall (H : word -> bool) (m : word -> option byte) (base : Z) (l : list byte),
(forall j, (j < length l)%nat -> aview SEGS H m (base + Z.of_nat j) = Some (bv_unsigned (nth j l cp_z))) ->
garr8 SEGS (mrestrict H m) base (map (fun b : byte => bv_unsigned b) l).
Proof.
intros H m base l HV j Hj. first [rewrite length_map in Hj | rewrite map_length in Hj].
assert (Hnth : nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l cp_z))
by (rewrite <- (map_nth (fun b : byte => bv_unsigned b) l cp_z j); reflexivity).
pose proof (bv_unsigned_in_range 8 (nth j l cp_z)) as HR. change (bv_modulus 8) with 256 in HR.
split; [|rewrite Hnth; exact HR].
intros k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
pose proof (HV j Hj) as HVj. unfold aview in HVj.
destruct (mbyte SEGS (mrestrict H m) (base + Z.of_nat j)) as [b|] eqn:Hb; cbn in HVj; [|discriminate].
injection HVj as HVj. f_equal. rewrite Hnth.
apply bv_eq. rewrite Z_to_bv_unsigned, HVj. unfold bv_wrap, bv_modulus, YO0f.le_byte.
change (2 ^ Z.of_N 8) with 256. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma pz_segD : forall B G, pz_rt B G -> forall c, pz_ok B c -> pz_cutJ_spec B c.
Proof.
intros B G RT c Hok E ms md Hcur HS Ha0 Hout.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur.
(* Cut J is the join of the walk of 50 <= n and the short walk of n < 50, so the contract's premises about
   the frame f are not available (pz_open_f cannot run); the epilogue reads no byte of f. pz_std's only use
   of f is the bound of atom 10, so give it the register's own value, which is a 64-bit word. *)
assert (H10' : getr regs 10 = w64 (bv_unsigned (getr regs 10)))
by (unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Hf'b : 0 <= bv_unsigned (getr regs 10) < 2 ^ 64)
by (pose proof (bv_unsigned_in_range 64 (getr regs 10)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr).
clear H10.
pz_std.
unfold YK0s.ret_ok in Hra.
pose proof (aj_flag_store_pi (fx := fq) B LAWS ML ASF FFL) as RUNF.
pose proof (paj_ret_at (fx := fq) (PL := PL_disco) (PI := PI)) as RET.
(* The caller's out struct is apart from the frame the call took: each case of awr_byte is. *)
assert (Hnfo : forall a, o <= a < o + 36 -> ~ pz_nf F FL a)
by (intros a Ha; exact (pz_awr_nf B STK sp0 FP ly S lyc Sc own W memc mdc a F FL HAR Hownf N1 N3 N4
ltac:(lia) (proj1 (HOW a Ha)))).
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
(* 2. The run from cut J to `ret`: the shadow bytes marked, the flag pointer loaded from F + 120 and the
   flag cleared, the saved registers reloaded and sp restored. The frame (1, fpos) leaves the journal. *)
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
   shadow bytes and its flag byte. pz_kept_own carries the six clauses of pz_cur's KP across the run. *)
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp - 96 <= a < sp) \/ (F <= a < F + 128) \/ (SB + F / 8 <= a < SB + F / 8 + 16) \/ a = FL) a)
by (pz_win_tac ltac:(fun H => revert H; pz_bases; intros H)) end.
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ _ HFr Hw1) as Hkp.
pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc (ms_mem ms) md (ms_mem ms) (ms_mem ms0)
(sp - REAC_CTRL_PARSE_STK) sp o fpos F FL
(fun a => (sp - 96 <= a < sp) \/ (F <= a < F + 128) \/ (SB + F / 8 <= a < SB + F / 8 + 16) \/ a = FL)
HAR HARc Hfrs2 Eab EF EFL FFL ltac:(lia) ltac:(lia) Hoimg
ltac:(intros a Ha; cbv beta in Ha; destruct Ha as [Ha | [Ha | [Ha | Ha]]];
[left; lia
| right; right; unfold pz_nf; left; exact Ha
| right; right; unfold pz_nf; right; left; rewrite SB_SHADOW_OFF in Ha; exact Ha
| right; right; unfold pz_nf; right; right; exact Ha])
KP Hkp (fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP2.
assert (Hout2 : forall i, (i < 36)%nat -> aview SEGS (w_H W) (ms_mem ms0) (o + Z.of_nat i) =
Some (bv_unsigned (nth i (snd (ctrlparse n fr)) cp_z))).
{ intros i Hi. rewrite Hkp; [exact (Hout i Hi) | lia |].
intros HZa. cbv beta in HZa. destruct HZa as [Hs | Hrest].
- lia.
- apply (Hnfo (o + Z.of_nat i) ltac:(lia)). unfold pz_nf.
destruct Hrest as [Hr | [Hr | Hr]];
[left; exact Hr | right; left; rewrite SB_SHADOW_OFF in Hr; exact Hr | right; right; exact Hr]. }
assert (HGA : garr8 SEGS (mrestrict (w_H W) (ms_mem ms0)) o (map (fun b : byte => bv_unsigned b) (snd (ctrlparse n fr)))).
{ apply pz_garr8_of_view. intros j Hj. rewrite ctrlparse_length in Hj. exact (Hout2 j Hj). }
(* 4. `ret`: back at the caller's return address with the post-condition; its six memory clauses are KP2. *)
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold treac_ctrl_parse_post. cbv beta.
lazymatch goal with |- exists _ _ _ _ _ _, mkCfg (@mkst ?fxv ?rg _ ?mm _) ?mdv = _ /\ _ =>
exists fxv, lyc, (stack_free_state 1 fpos S2), rg, mm, mdv end.
split; [rewrite R1; rewrite (AGX 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
split; [intros kk _; reflexivity|].
split; [left; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|].
split; [apply aregs_preserved_eqs; creg HS AGX EE|].
split.
{ change (frames (stack_free_state 1 fpos S2)) with (del_pos (frames S2) 1 fpos). rewrite Hfrs2. cbn [del_pos].
rewrite !Z.eqb_refl. reflexivity. }
split.
{ rewrite <- Eab. unfold ablocks. rewrite blocks_stack_free_state. apply Permutation_refl. }
split; [rewrite R10, Ha0; reflexivity|].
split; [exact HGA|].
exact KP2.
Qed.
End d.
End b.
