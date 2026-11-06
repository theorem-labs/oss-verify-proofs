(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: what reac_grant_build_sweep's walk shares between its files (the cuts' symbolic states, the facts a cut carries, the cut lemmas' statements, and the walk's own tactics), adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v (the seat of a cut: submem, facts_incl, the havoc of the dead registers, and the writable-window case list of the flag-store run) and lib/A/ACa2.v (a loop walk split into cut-indexed lemmas); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantBuildSweepLib.v at a working branch eacc832ec38a (blob 9b1a1140806, the blob the walk was ported from): what reac_grant_build_sweep's walk shares between its files, over image B's listing and walk layer (lib/B/Prog). Image B differs from image A in the loop: the column index and the row index are kept in registers s11 / s6 and the width and the struct pointer are reloaded from the realigned frame's slots at 40 and 56, there is a UBSan bound check on the row index (`bgeu s6,s3` 0x85850, trap 0x85a3c), and the store's address is the values buffer's base s8 = F + 32 plus the row index, so the cuts carry the column c and the cell p as literals instead of image A's row-pointer atom. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC4b YC81 YC88 YCbw YCkd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantSyms GrantList GrantAddr GrantTop GrantPa GrantPaLib GrantFrame GrantRo YC1g YC1h YC1i YC45 YC85
ACj1 ACbf GrantACjr GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel GrantSweepModel BuildSweepModel.
(* The contract: image B's own, stated in lib/B/Prog/GrantBContracts.v. It is Required, not Imported: its SB
   would hide YC81's, which the walk tactics unfold. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require GrantBContracts.
(* The address-free layout of the 460-byte head-amp table, as the contract names it (GrantBContracts.v's ATx). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require HeadampLayout.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Module C := OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog.GrantBContracts.
Module ATx := OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.HeadampLayout.
(* The stack this call needs below its entry sp: its own 192-byte frame, the 16 bytes the `andi sp,sp,-32` at
   0x8563c may drop, and the deeper of the two callees' stacks (reac_ctrl_build_grant_sweep's 528 + ESTACK).
   An abbreviation, not a definition: the contract states afn_pre over C.STK_reac_grant_build_sweep itself,
   and lia must see one atom, not two. *)
Notation BSW_STK := C.STK_reac_grant_build_sweep.
(* ---- tactics ------------------------------------------------------------- *)
Ltac ulits := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
rewrite (unsigned_lit_small z) by (unfold SB in *; lia) end.
(* The writable windows of a flag-store run: the machine stack (the saved
   registers and the realigned frame), the side-stack frame and its shadow,
   and the flag byte itself. *)
Ltac bs_wrange AG fpos F EFA EFL Hsp1 FFS :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; rewrite FFS; clear - Hr Hsp1; lia
| left; right; right; right; exists 2, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 2) with 256; rewrite ?EFA; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
| fail 2 "bs_wrange: a window outside the stack, the frame, its shadow and the flag" ]
| ]);
destruct Hin.
(* The dead registers deads to fresh atoms N, N+1, ... (their values). *)
Ltac bs_havoc_regs HS N deads :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_havoc_hi N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl end;
norm_ss HS.
(* Seat a run's end on a cut: keep the regions rs (a subsequence of the
   state's regions, each a subregion of its partner), the atom facts fa and the aliases al,
   and give the dead registers deads the atoms N, N+1, ... (through 900, so
   that the old atoms N.. leave the state first). *)
Ltac bs_rejoin HS AG rs fa al deads N :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs' := eval vm_compute in rs in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_submem Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let fa' := eval vm_compute in fa in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_facts_incl3 Ex ssx msx fa' [] al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
bs_havoc_regs HS 900%nat deads;
let HEv := fresh "HEv" in ACj1.rebaseE HS AG HEv; clear HEv;
bs_havoc_regs HS N deads.
(* Carry `HK : forall a, lo <= a < hi -> aview (cur mem) a = aview mem0 a`
   across a run whose writes HFr bounds. *)
Ltac upd_rngW HK HFr btac tac :=
let HK' := fresh "HK" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HK with forall a, ?lo <= a < ?hi -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HK' : forall a, lo <= a < hi -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in
intros a Ha_rng; refine (eq_trans _ (HK a Ha_rng)); apply aview_eq_of; apply HFr;
rewrite unsigned_lit_small by btac;
let rg := fresh "rg" in let Hin := fresh "Hin" in
intros (rg & Hin & Hrg_rng);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg_rng; tac |]);
destruct Hin
| clear HK; rename HK' into HK ] end end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* The stack this call needs below its entry sp: its own 192-byte frame, the 16 bytes the `andi sp,sp,-32` at
   0x8563c may drop, and the deeper of the two callees' stacks (reac_ctrl_build_grant_sweep's 528 + ESTACK). *)
(* the stack bound is named by the contract itself; see the abbreviation above the sections *)
(* The entry state's extra atoms: 32 the shadow base, 33 al[0] (base), 34 al[1] (width), 35 al's shadow cell,
   36 the byte that cell holds. *)
Definition bs_extra (al base w shv : Z) : list word := map (Z_to_bv 64) [SB; base; w; SB + al / 8; shv].
(* The entry state: the machine-stack window, the GOT word and the shadow-base cell (objects 1 and 35 on image
   B), and the use-after-return flag's GOT word and cell (objects 0 and 36). *)
Definition bs_regions0 : smem :=
[ stack_region 192; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 36); uar_cell_regionP (A_OBJ 36) ].
Definition bs_atoms0 : list (nat * afact) := [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0) ].
Definition ss_bs0 : sstate := mkSS AF_reac_grant_build_sweep sr_atoms bs_regions0 None (mkFacts bs_atoms0 [] []).
(* Releasing a side-stack frame changes only the frame-stack part of the state. *)
Lemma set_fs_free : forall f S cid pos, exists g, stack_free_state cid pos (set_fs f S) = set_fs g S.
Proof. intros f S cid pos. eexists. unfold stack_free_state, set_fs. cbn. reflexivity. Qed.
Lemma set_fs_set_fs : forall f g S, set_fs g (set_fs f S) = set_fs g S.
Proof. intros f g S. reflexivity. Qed.
(* The shadow cell of a pointer a little above an 8-aligned one. *)
Lemma shadow_decl_okc : forall E (p b s : nat) (pv Bv c : Z),
ew E p = Z_to_bv 64 pv -> 0 <= pv -> 0 <= c -> pv + c < 2 ^ 64 -> (pv + c) / 8 = pv / 8 ->
ew E b = Z_to_bv 64 Bv ->
ew E s = Z_to_bv 64 (Bv + pv / 8) ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff p c) (SLit 3)) (SOff b 0)) = sv_denot E (SOff s 0).
Proof.
intros E p b s pv Bv c Hp Hpv Hc Hpc Hdiv Hb Hs. apply U_inj.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Hp, Hb, Hs, !Z.add_0_r.
rewrite (unsigned_lit_small pv) by lia. rewrite (zcanon_id (pv + c)) by (unfold M64; lia). rewrite Hdiv.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
unfold zcanon, M64. rewrite (Z.mod_mod Bv) by lia. rewrite Z.add_mod_idemp_r by lia.
rewrite (Z.mod_mod (Bv + pv / 8)) by lia. f_equal. lia.
Qed.
Lemma shadow_in_frame : forall fa fs x, fa mod 64 = 0 -> fs mod 64 = 0 -> 0 <= fa -> 0 <= fs -> fa <= x < fa + fs ->
fa / 8 <= x / 8 < fa / 8 + fs / 8.
Proof.
intros fa fs x Ha Hf Ha0 Hf0 Hx.
pose proof (Z.div_mod fa 64 ltac:(lia)) as Da. rewrite Ha, Z.add_0_r in Da.
pose proof (Z.div_mod fs 64 ltac:(lia)) as Df. rewrite Hf, Z.add_0_r in Df.
assert (Ea : fa / 8 = 8 * (fa / 64)) by (rewrite Da at 1; replace (64 * (fa / 64)) with ((8 * (fa / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (Ef : fs / 8 = 8 * (fs / 64)) by (rewrite Df at 1; replace (64 * (fs / 64)) with ((8 * (fs / 64)) * 8) by lia; apply Z.div_mul; lia).
split; [apply Z.div_le_mono; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
(* The checks at 0x85774 (`width - 41 <u -40`), 0x857a0 (`base + width - 49 <u -48`) and the dead one at
   0x857e4 (`width - 41 >=u -40`, always taken). *)
Lemma bsw_false_fits : forall s al mx base w, fits base w = false -> bsw_ok s al mx base w = false.
Proof. intros s al mx base w H. unfold bsw_ok. rewrite H, andb_false_r. reflexivity. Qed.
Lemma bsw_bad_w : forall s al mx base w, 0 <= w < 256 -> (w + -41) mod 2 ^ 64 < 18446744073709551576 ->
bsw_ok s al mx base w = false.
Proof.
intros s al mx base w Hw H. apply bsw_false_fits. unfold fits.
destruct (Z_lt_le_dec w 41) as [Hl | Hl].
- rewrite <- (Z.mod_unique (w + -41) (2 ^ 64) (-1) (w + -41 + 2 ^ 64)) in H by lia.
rewrite (proj2 (Z.leb_gt 1 w)) by lia. reflexivity.
- rewrite (proj2 (Z.leb_gt w 40)) by lia. rewrite andb_false_r. reflexivity.
Qed.
Lemma bsw_good_w : forall w, 0 <= w < 256 -> 18446744073709551576 <= (w + -41) mod 2 ^ 64 -> 1 <= w <= 40.
Proof.
intros w Hw H. destruct (Z_lt_le_dec w 41) as [Hl | Hl].
- rewrite <- (Z.mod_unique (w + -41) (2 ^ 64) (-1) (w + -41 + 2 ^ 64)) in H by lia. lia.
- rewrite Z.mod_small in H by lia. lia.
Qed.
(* Image B adds the source's redundant width check at 0x857e4; with 1 <= w <= 40 its branch is taken, so the
   -1 arm at 0x857e8 is not reached. *)
Lemma bsw_w_geu : forall w, 1 <= w <= 40 -> 18446744073709551576 <= (w + -41) mod 2 ^ 64.
Proof.
intros w Hw. rewrite <- (Z.mod_unique (w + -41) (2 ^ 64) (-1) (w + -41 + 2 ^ 64)) by lia. lia.
Qed.
(* The check at 0x857a0 is on base + w - 49 against -48. *)
Lemma bsw_bad_bw : forall s al mx base w, 48 < base + w -> bsw_ok s al mx base w = false.
Proof.
intros s al mx base w H. apply bsw_false_fits. unfold fits.
rewrite (proj2 (Z.leb_gt (base + w) 48)) by lia. rewrite andb_false_r. reflexivity.
Qed.
Lemma bsw_mod_wrap : forall x, -49 <= x < 0 -> x mod 2 ^ 64 = x + 2 ^ 64.
Proof.
intros x Hx. replace x with ((x + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma bsw_bw_bad : forall s al mx base w, 0 <= base < 256 -> 1 <= w < 256 ->
(base + w + -49) mod 2 ^ 64 < 18446744073709551568 -> bsw_ok s al mx base w = false.
Proof.
intros s al mx base w Hb Hw H. apply bsw_bad_bw.
destruct (Z_lt_le_dec (base + w) 49) as [Hl | Hl]; [|lia].
rewrite (bsw_mod_wrap (base + w + -49)) in H by lia. lia.
Qed.
Lemma bsw_bw_good : forall base w, 0 <= base < 256 -> 0 <= w < 256 ->
18446744073709551568 <= (base + w + -49) mod 2 ^ 64 -> base + w <= 48.
Proof.
intros base w Hb Hw H. destruct (Z_lt_le_dec (base + w) 49) as [Hl | Hl]; [lia|].
rewrite Z.mod_small in H by lia. lia.
Qed.
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
(* The value the fits check at 0x857a0 compares: image B adds base and the width and then subtracts 49,
   where image A compares 48 against the sum. *)
Lemma bsw_fits_U : forall E base w, ew E 33 = Z_to_bv 64 base -> ew E 34 = Z_to_bv 64 w ->
0 <= base < 256 -> 0 <= w < 256 ->
U E (SAlu ALU_ADD (SOff 33 (-49)) (SOff 34 0)) = (base + w + -49) mod 2 ^ 64.
Proof.
intros E base w H33 H34 Hb Hw.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, H33, H34, !unsigned_lit_small by lia.
unfold zcanon, M64. rewrite Z.add_0_r, Zplus_mod_idemp_l, Zplus_mod_idemp_r. f_equal. lia.
Qed.
(* The row aliases of bs_al are sound at any cut whose env gives F, the row and the row index:
   (F + 32) + (3c + p) is the row's address plus p. *)
Lemma bs_alias_ok : forall E F c p, ew E 516 = Z_to_bv 64 F -> ew E 619 = Z_to_bv 64 (F + 32 + 3 * c) ->
ew E 620 = Z_to_bv 64 (3 * c) -> 0 <= F -> F + 256 < 2 ^ 64 -> 0 <= c <= 40 -> 0 <= p <= 2 ->
sv_denot E (SAlu ALU_ADD (SOff 516 32) (SOff 620 p)) = sv_denot E (SOff 619 p).
Proof.
intros E F c p H516 H619 H620 HF0 HF1 Hc Hp. apply U_inj.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, H516, H619, H620, !unsigned_lit_small by lia.
unfold zcanon, M64. rewrite !(Z.mod_small (F + 32)) by lia. rewrite (Z.mod_small (3 * c + p)) by lia.
f_equal. lia.
Qed.
(* ---- the three cuts of the loop ------------------------------------------
   Atoms: 0..31 the entry registers, 32 the shadow base, 33 al[0] (base), 34 al[1] (width), 35 al's shadow
   cell, 36 the byte that cell holds, 60 the realigned sp (s1), 516 the side-stack frame F, 528 its flag,
   529 F's shadow cell; 619 the row F + 32 + 3c, 620 the row index 3c (s11; s6 runs over it as SOff 620 p),
   621 the column c (s2); 600.. the dead registers. *)
(* The byte al's shadow cell holds: 0, or (z = false) the atom 36, which is 2..7. *)
Definition bs_shc (z : bool) : sv := if z then SLit 0 else SOff 36 0.
(* The regions every cut keeps: al's shadow cell, al's two bytes, F's shadow (bytes 4..18 marked usable for
   the values buffer), F's header, F's tail with the flag pointer at F + 248, the realigned frame's slots,
   and the saved registers. The values buffer itself is not a region at a cut: the row the turn writes is,
   and the bytes written so far are carried in bs_mem. *)
Definition bs_RL0 (z : bool) : smem :=
[ YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (bs_shc z))];
YP09.mkRegion (Some 12%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0))];
YP09.mkRegion (Some 529%nat) 0 32 0 32
[YP09.mkChunk 18 (CVal 1 (SLit 0)); YP09.mkChunk 17 (CVal 1 (SLit 0)); YP09.mkChunk 16 (CVal 1 (SLit 0));
YP09.mkChunk 15 (CVal 1 (SLit 0)); YP09.mkChunk 14 (CVal 1 (SLit 0)); YP09.mkChunk 13 (CVal 1 (SLit 0));
YP09.mkChunk 12 (CVal 1 (SLit 0)); YP09.mkChunk 7 (CVal 1 (SLit 0)); YP09.mkChunk 6 (CVal 1 (SLit 0));
YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 4 (CVal 1 (SLit 0)); YP09.mkChunk 11 (CVal 1 (SLit 0));
YP09.mkChunk 10 (CVal 1 (SLit 0)); YP09.mkChunk 9 (CVal 1 (SLit 0)); YP09.mkChunk 8 (CVal 1 (SLit 0));
YP09.mkChunk 19 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 23 (CVal 1 (SLit 18446744073709551603));
YP09.mkChunk 22 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 21 (CVal 1 (SLit 18446744073709551603));
YP09.mkChunk 20 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601));
YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601));
YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 24 (CVal 8 (SLit 0))];
YP09.mkRegion (Some 516%nat) 0 32 0 32
[YP09.mkChunk 16 (CVal 8 (SOff 274 0)); YP09.mkChunk 8 (CVal 8 (SOff 273 0));
YP09.mkChunk 0 (CVal 8 (SLit 1102416563))];
YP09.mkRegion (Some 516%nat) 152 256 152 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 88 0 88
[YP09.mkChunk 40 (CVal 8 (SOff 12 0)); YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SOff 516 0));
YP09.mkChunk 32 (CVal 8 (SOff 516 0)); YP09.mkChunk 16 (CVal 8 (SOff 11 0)); YP09.mkChunk 8 (CVal 8 (SOff 10 0));
YP09.mkChunk 48 (CVal 8 (SOff 35 0)); YP09.mkChunk 56 (CVal 8 (SOff 34 0)); YP09.mkChunk 80 (CVal 8 (SOff 516 0))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0
[YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ].
(* The row of the values buffer the turn writes: three bytes at the atom 619 = F + 32 + 3c. *)
Definition bs_row : YP09.region := YP09.mkRegion (Some 619%nat) 0 3 0 3 [].
(* The store `sb a0,0(a1)` of a cell goes to s8 + s6 = (F + 32) + (3c + p); the engine cannot fold two atoms,
   so the cut declares the three sums (p = 0, 1, 2) equal to the row's atom. *)
Definition bs_al : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 516 32) (SOff 620 0), SOff 619 0);
(SAlu ALU_ADD (SOff 516 32) (SOff 620 1), SOff 619 1);
(SAlu ALU_ADD (SOff 516 32) (SOff 620 2), SOff 619 2) ].
(* The atom facts a cut carries. hi620 / hi621 bound the row index and the column: inside the loop
   3c <= 117 and c <= 39, at the instruction after it 3w <= 120 and w <= 40. The bound on 620 is what makes
   the UBSan check at 0x85850 (`bgeu s6,s3`, s3 = 120) false, so the trap 0x85a3c is not reached. *)
Definition bs_FL (z : bool) (hi620 hi621 : Z) : list (nat * afact) :=
(if z then [] else [(36%nat, mkAF 2 7 0)]) ++
[ (619%nat, HPTR 0); (620%nat, mkAF 0 hi620 0); (621%nat, mkAF 0 hi621 0);
(35%nat, mkAF (SB + 512) (SB + 17592186044416) 0); (34%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0);
(12%nat, mkAF 4096 140737479966720 3); (529%nat, mkAF (SB + 512) (SB + 17592186044416) 2);
(528%nat, HPTR 0); (516%nat, HPTR 5); (60%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 5);
(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0) ].
(* The registers at the head of the loop over the width (0x85820) and at the instruction after it
   (0x85890): s2 = the column (atom 621), s11 = the row index (atom 620), s6 = al, s5 = the table,
   s8 = F + 32, s10 = F's shadow cell, s3 = 120, s4 = 3; 600..617 are the dead ones (ra, t0..t2, a0..a7,
   s7, s9, t3..t6). *)
Definition bs_deads : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 25; 28; 29; 30; 31]%bv.
Definition bs_sr_L : list sv :=
[SLit 0; SOff 600 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 601 0; SOff 602 0; SOff 603 0;
SOff 2 0; SOff 60 0; SOff 604 0; SOff 605 0; SOff 606 0; SOff 607 0; SOff 608 0; SOff 609 0;
SOff 610 0; SOff 611 0; SOff 621 0; SLit 120; SLit 3; SOff 13 0; SOff 12 0; SOff 612 0;
SOff 516 32; SOff 613 0; SOff 529 0; SOff 620 0; SOff 614 0; SOff 615 0; SOff 616 0; SOff 617 0].
(* The registers at the head of the cell loop (0x85840), with p cells of the column written: s7 = p,
   s6 = 3c + p, s9 = (base + c) & 255; 600..615 are the dead ones (ra, t0..t2, a0..a7, t3..t6). *)
Definition bs_ch : sv := SAlu ALU_AND (SAlu ALU_ADD (SOff 33 0) (SOff 621 0)) (SLit 255).
Definition bs_deads_I : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition bs_sr_I (p : Z) : list sv :=
[SLit 0; SOff 600 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 601 0; SOff 602 0; SOff 603 0;
SOff 2 0; SOff 60 0; SOff 604 0; SOff 605 0; SOff 606 0; SOff 607 0; SOff 608 0; SOff 609 0;
SOff 610 0; SOff 611 0; SOff 621 0; SLit 120; SLit 3; SOff 13 0; SOff 620 p; SLit p;
SOff 516 32; bs_ch; SOff 529 0; SOff 620 0; SOff 612 0; SOff 613 0; SOff 614 0; SOff 615 0].
(* The head of the loop over the width (0x85820 = listing offset 19940). *)
Definition ss_L (z : bool) : sstate := mkSS 19940 bs_sr_L (bs_row :: bs_RL0 z) None (mkFacts (bs_FL z 117 39) [] bs_al).
(* The head of the loop over a column's three cells (0x85840 = listing offset 19972). *)
Definition ss_I (z : bool) (p : Z) : sstate := mkSS 19972 (bs_sr_I p) (bs_row :: bs_RL0 z) None (mkFacts (bs_FL z 117 39) [] bs_al).
(* The instruction after the loop (0x85890 = listing offset 20052). *)
Definition ss_X (z : bool) : sstate := mkSS 20052 bs_sr_L (bs_RL0 z) None (mkFacts (bs_FL z 120 40) [] bs_al).
(* ---- the contract's post-condition and the cuts' facts -------------------- *)
Definition bs_post (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) mem md
(s mx al tx base w : Z) (T : list byte) : world SEGS -> config -> Prop :=
C.tb_reac_grant_build_sweep_post B regs ly S W mem md s al mx tx base w T.
(* The rows the call may write lie in a heap block, so they miss every frame the caller took and those
   frames' shadow. *)
Lemma bsw_fp_frames : forall ly S W mem md s al mx base w,
AR SEGS B ly S W mem md ->
(bsw_ok s al mx base w = true -> exists sb sn, In (sb, sn) (ablocks B ly S) /\ sb <= s /\ s + 34 * (8 + 3 * w) <= sb + sn) ->
forall cid pos a, In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP (C.tb_reac_grant_build_sweep_FP s al mx base w) a.
Proof.
intros ly S W mem md s al mx base w HAR HSB cid pos a Hf Ha. unfold C.tb_reac_grant_build_sweep_FP.
destruct (bsw_ok s al mx base w) eqn:Hb; [|apply inFP_nil].
destruct (HSB eq_refl) as (sb & sn & Hin & Hlo & Hhi).
pose proof (bsw_ok_spec s al mx base w Hb) as (_ & _ & Hw & _).
intros Hfp. apply inFP_cons in Hfp. destruct Hfp as [Hfp | Hfp]; [|exact (inFP_nil _ Hfp)].
pose proof (sep_block_frame SEGS B LAWS ly S W mem md sb sn cid pos HAR Hin Hf) as Hd.
destruct (al_blocks _ _ LAWS ly S W mem md sb sn HAR Hin) as (_ & H4096 & Hceil & [Hih Hia] & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hf) as (Hf4096 & Hfceil & Hfapp).
pose proof (fs_frame_bytes_nonneg cid) as Hfs0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hrq : req_size sn = sn) by (unfold req_size; destruct (Z.eqb_spec sn 0); lia).
rewrite Hrq in *.
unfold zdisjoint, in_zr, frame_rng, shadow_addr, in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. cbn [fst snd] in *.
destruct Ha as [Ha | Ha]; [lia|].
assert (frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8 <= (frame_addr ly cid pos + fs_frame_bytes cid) / 8).
{ pose proof (Z.div_mod (frame_addr ly cid pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (frame_addr ly cid pos) 8 ltac:(lia)).
pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)).
apply Z.div_le_lower_bound; lia. }
assert ((frame_addr ly cid pos + fs_frame_bytes cid) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (0 <= frame_addr ly cid pos / 8) by (apply Z.div_pos; lia).
assert (alloc_ceiling / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
lia.
Qed.
(* What a cut knows of the call: the contract's premises (al <> 0 and the width checks passed), al's frame
   (cid, pos), the own frame (2, fpos) in S2, and the realigned sp. *)
Definition bs_ctx ly S W (regs : bvmap 5 word) mem md ch (s mx al tx base w : Z) (T : list byte)
(fpos : Z) (S2 : astate) (sp1 cid pos : Z) : Prop :=
afn_pre SEGS B BSW_STK ly S W regs mem md ch /\ Z.of_nat (length (frames S)) <= 7 /\ spZ regs + 32 <= ly_top ly /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) /\
getr regs 10 = w64 s /\ getr regs 11 = w64 mx /\ getr regs 12 = w64 al /\ getr regs 13 = w64 tx /\
0 <= s < 2 ^ 63 /\ - 2 ^ 31 <= mx < 2 ^ 31 /\
In (tx, ATx.TX_SIZE) (ablocks B ly S) /\ length T = 460%nat /\ tx_set01 T /\ tx_legal T /\
(bsw_ok s al mx base w = true -> exists sb sn, In (sb, sn) (ablocks B ly S) /\ sb <= s /\ s + 34 * (8 + 3 * w) <= sb + sn) /\
s <> 0 /\ al <> 0 /\ 1 <= w <= 40 /\ 0 <= base < 256 /\ base + w <= 48 /\
In (cid, pos) (frames S) /\ 0 <= cid /\ frame_addr ly cid pos <= al /\ al + 2 <= frame_addr ly cid pos + fs_frame_bytes cid /\
al mod 8 = 0 /\
frames S2 = (2, fpos) :: frames S /\ ablocks B ly S2 = ablocks B ly S /\ (exists f, S2 = set_fs f S) /\
spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0.
(* The atoms' values at a cut for column c: the atoms below 32 are the entry registers, 32 the shadow base,
   60 the realigned sp, 516 the side-stack frame F, 528 its flag, 529 F's shadow cell, 619 the row
   F + 32 + 3c, 620 the row index 3c, 621 the column c. *)
Definition bs_env (regs : bvmap 5 word) (al base w shv sp1 F FL c : Z) (Ec : env) : Prop :=
img_env VAL A_LIM Ec /\ (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ec n = getr regs r) /\ ew Ec 32 = Z_to_bv 64 SB /\
ew Ec 33 = Z_to_bv 64 base /\ ew Ec 34 = Z_to_bv 64 w /\ ew Ec 35 = Z_to_bv 64 (SB + al / 8) /\ ew Ec 36 = Z_to_bv 64 shv /\
ew Ec 60 = Z_to_bv 64 sp1 /\ ew Ec 516 = Z_to_bv 64 F /\ ew Ec 528 = Z_to_bv 64 FL /\ ew Ec 529 = Z_to_bv 64 (SB + F / 8) /\
ew Ec 619 = Z_to_bv 64 (F + 32 + 3 * c) /\ ew Ec 620 = Z_to_bv 64 (3 * c) /\ ew Ec 621 = Z_to_bv 64 c.
(* The read-only data: a state that keeps image B's bytes keeps arodata_okP. Image A's walks transport it with
   lib/A/Prog/GrantBase.v:34 arodata_ok_journalP (image B's twin: lib/B/PaBase.v:38), whose `fp_spares` side condition needs the section's Context RO
   (ro_below_ofl, which hyps_reac_grant_build_sweep now holds as IMG_RO_BELOW); this walk does not use it: it
   carries the image's bytes themselves (every window it writes - the machine stack, the side-stack frame, its
   shadow, al's frame - is off image B) and reads arodata_okP off them. *)
Lemma rod_img_kept : forall (W W' : world SEGS) (m m' : word -> option byte),
(forall a, 0x10000 <= a < 0x5fb000 -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m').
Proof.
intros W W' m m' HK HR a Hro Ho He.
assert (Himg : in_img SEGS a).
{ destruct Hro as [(sg & Hsg & _ & Hr) | Hrel]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hrel)]. }
pose proof (pa_img_range a Himg) as Hr2. rewrite IMG_LO_B_val, IMG_TOP_B_val in Hr2.
rewrite (HK a Hr2). exact (HR a Hro Ho He).
Qed.
(* Across a call, the same fact comes from acall_kept's image clause, which carries exactly arodata_okP's
   three side conditions. *)
Lemma rod_acall_kept : forall lyc Sc (W W2 : world SEGS) (m m2 : word -> option byte) slo shi (E : Z -> Prop),
acall_kept SEGS B lyc Sc W m W2 m2 slo shi E ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) m2).
Proof.
intros lyc Sc W W2 m m2 slo shi E (_ & _ & K3 & _) HR a Hro Ho He.
assert (Himg : in_img SEGS a).
{ destruct Hro as [(sg & Hsg & _ & Hr) | Hrel]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hrel)]. }
rewrite (K3 a Himg Ho He). exact (HR a Hro Ho He).
Qed.
(* The memory at a cut with nv values written: the journal since the call began, the caller's stack above sp
   untouched, image B's bytes untouched, the first nv values in the frame's values buffer, and the head-amp
   table. *)
Definition bs_mem ly S W (regs : bvmap 5 word) mem md (s mx al tx base w : Z) (T : list byte) (fpos : Z) (S2 : astate)
(ms3 : machine_state) (md3 : Model) (nv : Z) : Prop :=
ajournal SEGS B BSW_STK (spZ regs) (C.tb_reac_grant_build_sweep_FP s al mx base w) ly S W mem md [(2, fpos)] ly S2 W (ms_mem ms3) md3 0 /\
(forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a) /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem ms3)) /\
garr8 SEGS (mrestrict (w_H W) (ms_mem ms3)) (frame_addr ly 2 fpos + 32)
(map bv_unsigned (firstn (Z.to_nat nv) (sweep_vals T tx base (Z.to_nat w)))) /\
obj_at SEGS (mrestrict (w_H W) (ms_mem ms3)) tx ATx.LAY_TX (ATx.tx_vals T).
(* ---- the cut lemmas' statements ------------------------------------------ *)
(* The head segment: from the loop head (0x85820) through al's shadow check (the report call at 0x8588c is
   not reached) and the column's load to the head of the cell loop (0x85840), p = 0. *)
Definition bs_head_spec : Prop :=
forall (z : bool) ly S W (regs : bvmap 5 word) mem md ch (s mx al tx base w : Z) (T : list byte) shv fpos S2 sp1 cid pos
(c : Z) (Ec : env) (ms3 : machine_state) (md3 : Model) (Q : world SEGS -> config -> Prop),
bs_ctx ly S W regs mem md ch s mx al tx base w T fpos S2 sp1 cid pos -> 0 <= c < w ->
bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) c Ec ->
st_ok_pi SEGS VAL Ec (ss_L z) (restrict (w_H W) ms3) ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms3 md3 (3 * c) ->
(forall Ec' ms' md', bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) c Ec' ->
st_ok_pi SEGS VAL Ec' (ss_I z 0) (restrict (w_H W) ms') ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms' md' (3 * c) -> SRr SEGS W (mkCfg ms' md') Q) ->
SRr SEGS W (mkCfg ms3 md3) Q.
(* The cell segment: from the head of the cell loop with cell p of column c next (0x85840), through the call
   of reac_headamp_tx_effective (0x8584c), the UBSan bound check (0x85850, trap 0x85a3c not reached) and the
   store of its byte at F + 32 + 3c + p, to the next cell (p < 2), or through the column step to the loop
   head (c + 1 < w) or to the instruction after the loop (c + 1 = w). *)
Definition bs_cell_spec : Prop :=
forall (z : bool) ly S W (regs : bvmap 5 word) mem md ch (s mx al tx base w : Z) (T : list byte) shv fpos S2 sp1 cid pos
(c p : Z) (Ec : env) (ms3 : machine_state) (md3 : Model) (Q : world SEGS -> config -> Prop),
bs_ctx ly S W regs mem md ch s mx al tx base w T fpos S2 sp1 cid pos -> 0 <= c < w -> 0 <= p < 3 ->
bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) c Ec ->
st_ok_pi SEGS VAL Ec (ss_I z p) (restrict (w_H W) ms3) ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms3 md3 (3 * c + p) ->
(p < 2 -> forall Ec' ms' md', bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) c Ec' ->
st_ok_pi SEGS VAL Ec' (ss_I z (p + 1)) (restrict (w_H W) ms') ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms' md' (3 * c + p + 1) -> SRr SEGS W (mkCfg ms' md') Q) ->
(p = 2 -> c + 1 < w -> forall Ec' ms' md', bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) (c + 1) Ec' ->
st_ok_pi SEGS VAL Ec' (ss_L z) (restrict (w_H W) ms') ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms' md' (3 * (c + 1)) -> SRr SEGS W (mkCfg ms' md') Q) ->
(p = 2 -> c + 1 = w -> forall Ec' ms' md', bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) w Ec' ->
st_ok_pi SEGS VAL Ec' (ss_X z) (restrict (w_H W) ms') ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms' md' (3 * w) -> SRr SEGS W (mkCfg ms' md') Q) ->
SRr SEGS W (mkCfg ms3 md3) Q.
(* The tail's cut lemma: from the instruction after the loop (0x85890), all 3w values written, through al's
   shadow check (the report call at 0x85a6c is not reached), the call of reac_ctrl_build_grant_sweep
   (0x858b0), the re-poisoning, the inlined frame release and the return, to the contract's post. *)
Definition bs_tail_spec : Prop :=
forall (z : bool) ly S W (regs : bvmap 5 word) mem md ch (s mx al tx base w : Z) (T : list byte) shv fpos S2 sp1 cid pos
(Ec : env) (ms3 : machine_state) (md3 : Model),
bs_ctx ly S W regs mem md ch s mx al tx base w T fpos S2 sp1 cid pos ->
bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) w Ec ->
st_ok_pi SEGS VAL Ec (ss_X z) (restrict (w_H W) ms3) ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms3 md3 (3 * w) ->
SRr SEGS W (mkCfg ms3 md3) (bs_post ly S W regs mem md s mx al tx base w T).
(* The loop's cut lemma: from the head of the loop with c columns written. *)
Definition bs_loop_spec : Prop :=
forall (z : bool) ly S W (regs : bvmap 5 word) mem md ch (s mx al tx base w : Z) (T : list byte) shv fpos S2 sp1 cid pos
(n : nat) (c : Z) (Ec : env) (ms3 : machine_state) (md3 : Model),
bs_ctx ly S W regs mem md ch s mx al tx base w T fpos S2 sp1 cid pos ->
n = Z.to_nat (w - c) -> 0 <= c < w ->
bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) c Ec ->
st_ok_pi SEGS VAL Ec (ss_L z) (restrict (w_H W) ms3) ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms3 md3 (3 * c) ->
SRr SEGS W (mkCfg ms3 md3) (bs_post ly S W regs mem md s mx al tx base w T).
End e.
End d.
End b.
