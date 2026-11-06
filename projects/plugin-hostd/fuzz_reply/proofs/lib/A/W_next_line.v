(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's next_line, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites) and lib/A/ACbk.v (entry and return). *)
(* next_line(at, line, len) at 0x85d4c reads *at = A and g_nout = O; when A < O it finds the first NUL of the
   O - A bytes at g_out + A with the memchr interceptor and writes the line's start, its length and the new
   position through its three pointers.  Its spec is W_contract.v's nl_spec (Section w1n; agreed with lane W3).
   The three out cells lie in the caller's frame, the window [sp, sp + XO) of W_journal.v's ajournal_gx; the
   walk writes no global (G = []).  Section hypotheses: TL (the GOT slot and the shadow cell, W_kit.v PALib),
   NLAP (the four image objects the walk reads are apart; discharged at the pinned placement by vm_compute),
   AMEMCHR (the shared memchr text, lib/Rt/MemchrDef.v amemchr_realizesM, at the memchr entry) with HCROM (its
   constant window, musl memchr's masks at 0x10350 .. 0x10370, is read-only image), lifted with W_sites.v
   aj_gx_entry_at through aentry_of_memchrM below.
   The shadow checks of the three cells are decided inside paj_run_tok from nl_SH; the `nul == NULL` abort
   arm is refuted from the functional half (a NUL lies in the stream from A on). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_journal W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_srlf_xR W_contract_leaf_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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

Definition A_next_line : Z := AF_fr_next_line.
Definition A_next_lineP : Z := BASE + A_next_line.
(* The four image objects the walk reads (the GOT slot of the shadow cell, the shadow cell, g_nout and g_out) are
   apart.  The abstract placement PAImg does not fix the objects' values relative to each other, so this is a
   Section hypothesis, discharged at the pinned placement PB_fr (W_img.v) by vm_compute. *)
Definition nl_objs_apart : Prop :=
let g := VAL (A_OBJ 0) in let c := VAL (A_OBJ 32) in let no := VAL A_g_nout in let ou := VAL A_g_out in
(no + 8 <= ou \/ ou + 8 <= no) /\ (no + 8 <= g \/ g + 8 <= no) /\ (no + 8 <= c \/ c + 8 <= no) /\
(ou + 8 <= g \/ g + 8 <= ou) /\ (ou + 8 <= c \/ c + 8 <= ou).

(* ---- THE GENERIC WALK (route (b), step 3, on the check_bounded template, a working branch 663b15a129c):
   next_line over any allocator relation ARx with its laws, stated as W_contract_x.nl_spec_x.  AMEMCHR is the memchr
   text's twin W_sites_x.amemchr_realizesM_x; the call goes through W_sites_x.aj_gx_entry_at_x.  HP0 is the
   template's (this walk reads no heap block, so the closed theorem does not take it). ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis NLAP : nl_objs_apart.
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* Eight present bytes are a word. *)
Lemma present_val_mem8 : forall H (mem : word -> option byte) a,
(forall i, 0 <= i < 8 -> apresent H mem (a + i)) ->
exists v, 0 <= v < 2 ^ 64 /\ val_mem SEGS (mrestrict H mem) a 8 v.
Proof.
intros H mem a Hp.
assert (AV : forall i, 0 <= i < 8 -> exists x, aview SEGS H mem (a + i) = Some x /\ 0 <= x < 256).
{ intros i Hi. destruct (Hp i Hi) as [Hh [b Hb]]. exists (bv_unsigned b). split.
  - unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity.
  - pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. }
destruct (AV 0 ltac:(lia)) as (x0 & A0 & R0). destruct (AV 1 ltac:(lia)) as (x1 & A1 & R1).
destruct (AV 2 ltac:(lia)) as (x2 & A2 & R2). destruct (AV 3 ltac:(lia)) as (x3 & A3 & R3).
destruct (AV 4 ltac:(lia)) as (x4 & A4 & R4). destruct (AV 5 ltac:(lia)) as (x5 & A5 & R5).
destruct (AV 6 ltac:(lia)) as (x6 & A6 & R6). destruct (AV 7 ltac:(lia)) as (x7 & A7 & R7).
rewrite Z.add_0_r in A0.
exists (x0 + 256 * (x1 + 256 * (x2 + 256 * (x3 + 256 * (x4 + 256 * (x5 + 256 * (x6 + 256 * x7))))))).
split; [lia|].
apply val_mem_of_rdword. unfold rdword. rewrite A0, A1, A2, A3, A4, A5, A6, A7. reflexivity.
Qed.
Lemma val_mem_mod64 : forall m a v, val_mem SEGS m a 8 v -> val_mem SEGS m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* memchr's first occurrence is unique, so the shared text (which names its k) fixes the result register; its
   frame keeps every byte outside [sp - ESTACK, sp), so it gives aentry_post at any scratch of ESTACK or more. *)
Lemma first_byte_unique : forall W mem x n c k k',
first_byte SEGS W mem x n c k -> first_byte SEGS W mem x n c k' -> k = k'.
Proof.
intros W mem x n c k k' (Hk & Hb & Hf) (Hk' & Hb' & Hf').
destruct (Z.lt_trichotomy k k') as [Hlt | [Heq | Hgt]]; [exfalso | exact Heq | exfalso].
- destruct (Hb' k ltac:(lia)) as (b & Eb & Hne). rewrite (Hf ltac:(lia)) in Eb. injection Eb as <-. exact (Hne eq_refl).
- destruct (Hb k' ltac:(lia)) as (b & Eb & Hne). rewrite (Hf' ltac:(lia)) in Eb. injection Eb as <-. exact (Hne eq_refl).
Qed.
Lemma aentry_of_memchrM_x : forall lo hi pc stk ly S Hp W regs mem md x c n k,
amemchr_realizesM_x SEGS B ARx lo hi pc -> ESTACK <= stk ->
ecall_pre_x SEGS B ARx ly S Hp W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 c -> getr regs 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok SEGS W regs mem x n -> amem_range x n ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) x n) ->
consts_view SEGS lo hi W mem -> first_byte SEGS W mem x n c k ->
SRr SEGS W (cfg_at SEGS pc regs mem md)
(aentry_post_x ARx stk ly S Hp W regs mem md (fun _ => False)
 (fun regs' _ => getr regs' 10 = if k <? n then w64 (x + k) else w64 0)).
Proof.
intros lo hi pc stk ly S Hp W regs mem md x c n k HM Hstk HPRE H10 H11 H12 Hc Hn Hx Hxn Hsrc Hmr Hra Hhv Hcv Hfb.
eapply SRr_mono; [exact (HM ly S Hp W regs mem md x c n HPRE H10 H11 H12 Hc Hn Hx Hxn Hsrc Hmr Hra Hhv Hcv)|].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hcfg & HAR' & HP' & Hsm & (k' & Hfb' & H10') & Hfr & Hpr).
split; [reflexivity|]. exists regs', mem', md'.
split; [exact Hcfg|]. split; [exact HAR'|]. split; [exact HP'|]. split; [exact Hsm|].
split; [rewrite (first_byte_unique W mem x n c k k' Hfb Hfb'); exact H10'|].
split; [intros a Ha _ Hs; apply Hfr; [exact Ha | intros Hc'; apply Hs; lia]|].
exact Hpr.
Qed.

Definition Bx : sv := SOff 37 0.
Definition nl_regions : smem :=
[ stack_region NL_FRAME; got_regionP; bcell_regionP 37;
YP09.mkRegion (Some 10%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 11%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 35 0))];
YP09.mkRegion (Some 12%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))];
YP09.mkRegion (Some A_g_nout) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some A_g_out) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))] ].
Definition nl_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF (2^46) (2^47 - 8) 3); (11%nat, mkAF (2^46) (2^47 - 8) 3);
(12%nat, mkAF (2^46) (2^47 - 8) 3); (32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF 0 (2 ^ 64 - 1) 0);
(34%nat, mkAF 0 (2 ^ 64 - 1) 0); (35%nat, mkAF 0 (2 ^ 64 - 1) 0); (36%nat, mkAF 0 (2 ^ 64 - 1) 0);
(37%nat, mkAF SB SB 0) ] [] [].
Definition ss_nl : sstate := mkSS A_next_line sr_atoms nl_regions None nl_facts.
Definition nl_SH : list shent := [ mkSHE 10 0 8; mkSHE 11 0 8; mkSHE 12 0 8 ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition nl_extra (a o u vl vn : Z) : list word := map (Z_to_bv 64) [a; o; u; vl; vn; SB].

Lemma nl_entry_x : forall W ly S Hp regs mem md ch XO PA PL PN a o u vl vn,
afn_pre_x SEGS B ARx NL_STK ly S Hp W regs mem md ch -> 0 <= XO -> spZ regs + XO <= ly_top ly ->
(forall x, spZ regs <= x < spZ regs + XO -> apresent (w_H W) mem x) ->
getr regs 10 = w64 PA -> getr regs 11 = w64 PL -> getr regs 12 = w64 PN ->
PA mod 8 = 0 -> PL mod 8 = 0 -> PN mod 8 = 0 ->
spZ regs <= PA -> PA + 8 <= spZ regs + XO -> spZ regs <= PL -> PL + 8 <= spZ regs + XO ->
spZ regs <= PN -> PN + 8 <= spZ regs + XO ->
(PA + 8 <= PL \/ PL + 8 <= PA) -> (PA + 8 <= PN \/ PN + 8 <= PA) -> (PL + 8 <= PN \/ PN + 8 <= PL) ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PA 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PL 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PN 8 ->
val_mem SEGS (mrestrict (w_H W) mem) PA 8 a -> val_mem SEGS (mrestrict (w_H W) mem) PL 8 vl ->
val_mem SEGS (mrestrict (w_H W) mem) PN 8 vn ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_nout) 8 o -> val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_out) 8 u ->
0 <= a < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= u < 2 ^ 64 -> 0 <= vl < 2 ^ 64 -> 0 <= vn < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (nl_extra a o u vl vn))) ss_nl
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_next_lineP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx nl_SH (Eimg (Ereg regs (nl_extra a o u vl vn))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch XO PA PL PN a o u vl vn HPRE HXO HXtop HXp H10 H11 H12 PA8 PL8 PN8
PAlo PAhi PLlo PLhi PNlo PNhi DAL DAN DLN RAA RAL RAN MA ML MN MO MU Ra Ro Ru Rl Rn.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : NL_STK = 8256) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (nl_extra a o u vl vn))). pose proof pa_B_ok as HBASE.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E2 : ew E 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E10 : ew E 10 = Z_to_bv 64 PA) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 PL) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 PN) by (rewrite (EEo 12%nat 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 a) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 o) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 u) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 vl) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 vn) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (EO : forall i, (i < 33)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_obj_img 13 ltac:(lia)) as HnoR. pose proof (pa_obj_img 15 ltac:(lia)) as HouR.
change (A_OBJ 13) with A_g_nout in HnoR. change (A_OBJ 15) with A_g_out in HouR.
pose proof NLAP as (D1 & D2 & D3 & D4 & D5). cbv zeta in D1, D2, D3, D4, D5.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (VBO : forall i, (i < 33)%nat -> base_val E (Some (A_OBJ i)) = VAL (A_OBJ i)).
{ intros i Hi. apply VB; [exact (EO i Hi) | exact (pa_val_range _)]. }
split.
- unfold ss_nl, A_next_lineP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold nl_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. unfold NL_FRAME. split; [lia|]. split; [lia|]. split; [|constructor].
intros o0 Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VBO 0%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o0 Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
[cbn [sv_denot]; rewrite (EO 32%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VBO 32%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o0 Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 (SOff 37 0) SB);
[cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat PA E10) by lia. split; [lia|]. split; [lia|].
split; [intros o0 Ho; apply (apresent_writable SEGS); apply HXp; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ PA 0 8 (SOff 32 0) a);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact MA.
* rewrite (VB 11%nat PL E11) by lia. split; [lia|]. split; [lia|].
split; [intros o0 Ho; apply (apresent_writable SEGS); apply HXp; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ PL 0 8 (SOff 35 0) vl);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact ML.
* rewrite (VB 12%nat PN E12) by lia. split; [lia|]. split; [lia|].
split; [intros o0 Ho; apply (apresent_writable SEGS); apply HXp; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ PN 0 8 (SOff 36 0) vn);
[cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact MN.
* unfold A_g_nout. rewrite (VBO 13%nat ltac:(lia)). fold A_g_nout. split; [lia|]. split; [lia|]. split; [intros o0 Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL A_g_nout) 0 8 (SOff 33 0) o);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact MO.
* unfold A_g_out. rewrite (VBO 15%nat ltac:(lia)). fold A_g_out. split; [lia|]. split; [lia|]. split; [intros o0 Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL A_g_out) 0 8 (SOff 34 0) u);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact MU.
+ apply pairwise_disjoint_of_extents. unfold nl_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
unfold A_g_nout, A_g_out. rewrite (VBO 0%nat ltac:(lia)), (VBO 32%nat ltac:(lia)), (VBO 13%nat ltac:(lia)), (VBO 15%nat ltac:(lia)).
fold A_g_nout A_g_out. rewrite (VB 10%nat PA E10), (VB 11%nat PL E11), (VB 12%nat PN E12) by lia.
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold NL_FRAME.
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR HnoR HouR D1 D2 D3 D4 D5
PAlo PAhi PLlo PLhi PNlo PNhi DAL DAN DLN HXO HXtop Htop2. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [nl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E12, E32, E33, E34, E35, E36, E37, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Ra Ro Ru Rl Rn PA8 PL8 PN8
PAlo PAhi PLlo PLhi PNlo PNhi HXO HXtop Htop2. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- assert (HBx : U E Bx = SHADOW_OFF) by (unfold Bx; rewrite (U_atom E 37 SB E37) by (unfold SB; lia); reflexivity).
unfold sh_ok, nl_SH. constructor; [|constructor; [|constructor; [|constructor]]].
+ eapply shent_ok_of_range; [exact RAA | exact HBx | rewrite (U_atom E 10 PA E10) by lia; reflexivity | lia | lia |].
intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
+ eapply shent_ok_of_range; [exact RAL | exact HBx | rewrite (U_atom E 11 PL E11) by lia; reflexivity | lia | lia |].
intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
+ eapply shent_ok_of_range; [exact RAN | exact HBx | rewrite (U_atom E 12 PN E12) by lia; reflexivity | lia | lia |].
intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

Lemma in_cells : forall PA PL PN x,
(PA <= x < PA + 8) \/ (PL <= x < PL + 8) \/ (PN <= x < PN + 8) -> inFP (nl_cells PA PL PN) x.
Proof.
intros PA PL PN x [H | [H | H]]; unfold nl_cells;
[exists (PA, PA + 8) | exists (PL, PL + 8) | exists (PN, PN + 8)]; cbn [In fst snd]; tauto.
Qed.
Lemma in_cells_inv : forall PA PL PN x,
inFP (nl_cells PA PL PN) x -> (PA <= x < PA + 8) \/ (PL <= x < PL + 8) \/ (PN <= x < PN + 8).
Proof.
intros PA PL PN x (r & Hin & Hr). unfold nl_cells in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; tauto.
Qed.
(* Two memories that hold the same word at p agree on its bytes. *)
Lemma aview_of_val_mem2 : forall H H' (m m' : word -> option byte) p v x,
val_mem SEGS (mrestrict H m) p 8 v -> val_mem SEGS (mrestrict H' m') p 8 v -> p <= x < p + 8 ->
aview SEGS H' m' x = aview SEGS H m x.
Proof.
intros H H' m m' p v x H1 H2 Hx. unfold aview. replace x with (p + (x - p)) by lia.
rewrite (val_mem_agree SEGS _ _ p 8 v H1 H2 (x - p) ltac:(lia)). reflexivity.
Qed.
Lemma ra_kept : forall (v v' : Z -> option Z) a n,
(forall y, a <= y < a + n -> v' (shadow_of_addr SHADOW_OFF y) = v (shadow_of_addr SHADOW_OFF y)) ->
range_addressable v SHADOW_OFF a n -> range_addressable v' SHADOW_OFF a n.
Proof.
intros v v' a n Hk Hr y Hy. destruct (Hr y Hy) as (s & Hs & Hok). exists s. split; [rewrite (Hk y Hy); exact Hs | exact Hok].
Qed.
(* The first NUL of a list that has one. *)
Lemma first_zero_split : forall l : list byte, In (Z_to_bv 8 0) l ->
exists ln rest, l = ln ++ Z_to_bv 8 0 :: rest /\ ~ In (Z_to_bv 8 0) ln.
Proof.
induction l as [|b l IH]; intros Hin; [destruct Hin|].
destruct (Z.eq_dec (bv_unsigned b) 0) as [Hb | Hb].
- exists [], l. split; [|intros []]. cbn. f_equal. apply bv_eq. rewrite Hb. reflexivity.
- destruct Hin as [-> | Hin]; [exfalso; apply Hb; reflexivity|].
  destruct (IH Hin) as (ln & rest & -> & Hn). exists (b :: ln), rest. split; [reflexivity|].
  intros [Hbz | Hz]; [apply Hb; rewrite Hbz; reflexivity | exact (Hn Hz)].
Qed.
Lemma nth_skipn_add : forall (l : list byte) i j d, nth i (skipn j l) d = nth (j + i) l d.
Proof.
intros l i j d. revert l. induction j as [|j IH]; intros l; [reflexivity|].
destruct l as [|b l]; [destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
(* The stream byte at OUT + A + i, through the line split of the bytes from A. *)
Lemma nl_stream_byte : forall W mem OUT ob A ln rest i,
ob_at W mem OUT ob -> skipn (Z.to_nat A) ob = ln ++ Z_to_bv 8 0 :: rest -> 0 <= A -> 0 <= i ->
A + i < Z.of_nat (length ob) ->
aview SEGS (w_H W) mem (OUT + A + i) = Some (bv_unsigned (nth (Z.to_nat i) (ln ++ Z_to_bv 8 0 :: rest) (Z_to_bv 8 0))).
Proof.
intros W mem OUT ob A ln rest i HOB Hs HA Hi Hl. replace (OUT + A + i) with (OUT + (A + i)) by lia.
rewrite (HOB (A + i)) by lia. rewrite <- Hs, nth_skipn_add. rewrite Z2Nat.inj_add by lia. reflexivity.
Qed.
Lemma nl_line_byte : forall (ln rest : list byte) i, 0 <= i < Z.of_nat (length ln) -> ~ In (Z_to_bv 8 0) ln ->
bv_unsigned (nth (Z.to_nat i) (ln ++ Z_to_bv 8 0 :: rest) (Z_to_bv 8 0)) <> 0.
Proof.
intros ln rest i Hi Hn Hz. rewrite app_nth1 in Hz by lia. apply Hn.
assert (E0 : nth (Z.to_nat i) ln (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite Hz; reflexivity).
rewrite <- E0. apply nth_In. lia.
Qed.
Lemma nl_nul_byte : forall (ln rest : list byte),
bv_unsigned (nth (Z.to_nat (Z.of_nat (length ln))) (ln ++ Z_to_bv 8 0 :: rest) (Z_to_bv 8 0)) = 0.
Proof. intros ln rest. rewrite Nat2Z.id, nth_middle. reflexivity. Qed.
Ltac nl_nowr B2 B10 B11 B12 :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); vm_compute in Hin;
repeat (destruct Hin as [<- | Hin];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2, ?B10, ?B11, ?B12 in Hr; lia |]);
destruct Hin.
(* rewrite one run's frame: aview at its output memory = aview at its input memory, outside its writable ranges *)
Ltac nl_kept HFr B2 B10 B11 B12 :=
lazymatch type of HFr with frame_of ?Ev ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
rewrite (aview_kept_out Ev rs H m m' HFr); [| lia | nl_nowr B2 B10 B11 B12] end.

Lemma mul_lit : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
intros a b. apply bv_eq. rewrite mul_div_unsigned. cbn [zmd_raw].
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite <- Zmult_mod. reflexivity.
Qed.
(* the `sub a2,a2,a0` of 0x85db8, as the executor leaves it: a * (-1) + b *)
Lemma alu_negmul : forall a b,
alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 (-1))) (Z_to_bv 64 b) = Z_to_bv 64 (b - a).
Proof.
intros a b. apply bv_eq. rewrite alu64_unsigned, mul_div_unsigned. cbn [zalu_raw zmd_raw].
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite <- Zmult_mod, <- Zplus_mod. f_equal. ring.
Qed.

Ltac nl_awr1 :=
first [ lia
| left; split; [left; lia | lia]
| right; right; split; [apply in_cells; lia | lia] ].
Ltac nl_awr B2 B10 B11 B12 :=
lazymatch goal with |- awr_ok_x ?E ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok_x E rs' G XO OUT stk sp0 fp b0 bc ly own) end;
repeat first [ apply awr_ok_x_nil
| apply awr_ok_x_cons; [ let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite ?B2, ?B10, ?B11, ?B12 in Hx; nl_awr1 | ] ].

Theorem pb_next_line_x : nl_spec_x B PST ARx A_next_lineP.
Proof.
intros W ly S Hp regs mem md ch XO PA PL PN A O OUT ob HPRE HXO HX16 HXtop HXp H10 H11 H12 PA8 PL8 PN8
PAlo PAhi PLlo PLhi PNlo PNhi DAL DAN DLN RAA RAL RAN MA MO MOUT Hlen HOB HAO HOW HLT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_obj_img 13 ltac:(lia)) as HnoR. pose proof (pa_obj_img 15 ltac:(lia)) as HouR.
change (A_OBJ 13) with A_g_nout in HnoR. change (A_OBJ 15) with A_g_out in HouR.
assert (WS : NL_STK = 8256) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (present_val_mem8 (w_H W) mem PL ltac:(intros i Hi; apply HXp; lia)) as (vl & Rl & ML).
destruct (present_val_mem8 (w_H W) mem PN ltac:(intros i Hi; apply HXp; lia)) as (vn & Rn & MN).
pose proof (val_mem_mod64 _ _ _ MA) as MA'. pose proof (val_mem_mod64 _ _ _ MO) as MO'.
pose proof (val_mem_mod64 _ _ _ MOUT) as MOUT'.
pose proof (Z.mod_pos_bound A (2 ^ 64) ltac:(lia)) as RA. pose proof (Z.mod_pos_bound O (2 ^ 64) ltac:(lia)) as RO.
pose proof (Z.mod_pos_bound OUT (2 ^ 64) ltac:(lia)) as RU.
destruct (nl_entry_x W ly S Hp regs mem md ch XO PA PL PN (A mod 2 ^ 64) (O mod 2 ^ 64) (OUT mod 2 ^ 64) vl vn
HPRE HXO HXtop HXp H10 H11 H12 PA8 PL8 PN8 PAlo PAhi PLlo PLhi PNlo PNhi DAL DAN DLN RAA RAL RAN MA' ML MN MO' MOUT'
RA RO RU Rl Rn) as [HS SHOK].
pose proof (ajournal_gx_init_x SEGS B PST ARx [] XO (nl_cells PA PL PN) NL_STK [] ly S Hp W regs mem md ch HPRE HXO HX16 HXtop HXp) as HJ.
pose proof (paj_run_x_x B PST ARx LAWS [] (gx_ok_nil SEGS B) XO (nl_cells PA PL PN)) as RUN.
remember (Eimg (Ereg regs (nl_extra (A mod 2 ^ 64) (O mod 2 ^ 64) (OUT mod 2 ^ 64) vl vn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E1 : ew E 1 = getr regs 1) by exact (EEo 1%nat 1%bv eq_refl).
assert (E2 : ew E 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = getr regs 3) by exact (EEo 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = getr regs 4) by exact (EEo 4%nat 4%bv eq_refl).
assert (E10 : ew E 10 = Z_to_bv 64 PA) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 PL) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 PN) by (rewrite (EEo 12%nat 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 (A mod 2 ^ 64)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (O mod 2 ^ 64)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (OUT mod 2 ^ 64)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 vl) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 vn) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (HAE : env_agree 32 (Ereg regs (nl_extra (A mod 2 ^ 64) (O mod 2 ^ 64) (OUT mod 2 ^ 64) vl vn)) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE EEo.
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (B10 : bv_unsigned (ew E 10) = PA) by (rewrite E10; apply unsigned_lit_small; lia).
assert (B11 : bv_unsigned (ew E 11) = PL) by (rewrite E11; apply unsigned_lit_small; lia).
assert (B12 : bv_unsigned (ew E 12) = PN) by (rewrite E12; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 A_next_lineP) with (Z_to_bv 64 A_next_lineP). unfold A_next_lineP, A_next_line.
(* the prologue, the shadow check of *at, the loads of *at and g_nout, to the test *at == g_nout *)
paj_run_tok_x RUN HS HJ SHOK Bspan. { nl_awr B2 B10 B11 B12. }
psrr_branch_tok RUN BR HS SHOK Bspan.
-
(* *at <> g_nout: A < O, find the NUL with memchr *)
assert (HAlt : A < O).
{ rewrite branch_ne_U, (U_atom E 33 _ E33), (U_atom E 32 _ E32) in Hc by lia.
  apply (proj1 (Bool.negb_true_iff _)) in Hc. apply Z.eqb_neq in Hc.
  destruct (Z.eq_dec A O) as [-> | Hne]; [exfalso; apply Hc; reflexivity | lia]. }
destruct (HOW ltac:(lia)) as (HOUT0 & HO63 & HO40 & HOWIN).
destruct (HLT HAlt) as (HNUL & HMR & HRA & HHV & HROM).
assert (MA0 : A mod 2 ^ 64 = A) by (apply Z.mod_small; lia).
assert (MO0 : O mod 2 ^ 64 = O) by (apply Z.mod_small; lia).
assert (MU0 : OUT mod 2 ^ 64 = OUT) by (apply Z.mod_small; lia).
rewrite MA0 in E32. rewrite MO0 in E33. rewrite MU0 in E34.
destruct (first_zero_split _ HNUL) as (ln & rest & Hsplit & HnoZ).
assert (HK1 : Z.of_nat (length ln) < O - A).
{ assert (Hlsk : Z.of_nat (length (skipn (Z.to_nat A) ob)) = O - A)
  by (first [rewrite length_skipn | rewrite skipn_length]; lia).
  rewrite Hsplit in Hlsk. first [rewrite length_app in Hlsk | rewrite app_length in Hlsk].
  cbn [length] in Hlsk. lia. }
paj_run_tok_x RUN HS HJ SHOK Bspan. { nl_awr B2 B10 B11 B12. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (Usp0 : spZ (ms_regs ms0) = spZ regs - 64).
{ unfold spZ at 1. rewrite Q2, B2. apply unsigned_lit_small. unfold NL_STK, NL_FRAME, ESTACK in *. lia. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - NL_STK <= a < spZ regs + XO) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. nl_kept HFr0 B2 B10 B11 B12. nl_kept HFr B2 B10 B11 B12. reflexivity. }
assert (HCL : alloc_ceiling <= spZ regs - NL_STK) by (unfold NL_STK, NL_FRAME, ESTACK in *; lia).
assert (KEEPSH : forall y, 0 <= y < kHighMemEnd ->
  aview SEGS (w_H W) (ms_mem ms0) (shadow_of_addr SHADOW_OFF y) = aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF y)).
{ intros y Hy. destruct (shadow_below_stack (spZ regs - NL_STK) (spZ regs + XO) y HCL Hy) as [SA1 SA2].
  unfold shadow_of_addr. change (SHADOW_OFF + y / 8) with (shadow_addr y). apply KEEP1; assumption. }
assert (STB : forall i, 0 <= i <= Z.of_nat (length ln) ->
  aview SEGS (w_H W) (ms_mem ms0) (OUT + A + i) =
  Some (bv_unsigned (nth (Z.to_nat i) (ln ++ Z_to_bv 8 0 :: rest) (Z_to_bv 8 0)))).
{ intros i Hi. rewrite KEEP1 by (first [lia | apply HOWIN; lia]).
  exact (nl_stream_byte W mem OUT ob A ln rest i HOB Hsplit ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (HMIN : Z.min (O - A) (Z.of_nat (length ln) + 1) = O - A \/ Z.min (O - A) (Z.of_nat (length ln) + 1) <= O - A)
by (right; apply Z.le_min_l).
assert (MRY : forall x m y, amem_range x m -> 0 <= x -> x <= y -> y <= x + m -> 0 <= y < kHighMemEnd)
by exact amem_range_in.
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS [] XO (nl_cells PA PL PN) (2 * ESTACK) (SIGMA WS_memchr)
    (fun _ => False)
    (fun regs' (_ : word -> option byte) =>
       getr regs' 10 = if Z.of_nat (length ln) <? O - A then w64 (OUT + A + Z.of_nat (length ln)) else w64 0)
    W (ms_regs ms0) (ms_mem ms0) NL_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp _ 0 (-64)
    (Z_to_bv 64 (BASE + 15068))).
  - exact (gx_ok_nil SEGS B).
  - exact HX16.
  - exact HJ.
  - exact Usp0.
  - reflexivity.
  - lia.
  - unfold ESTACK; lia.
  - unfold NL_STK, NL_FRAME, ESTACK; lia.
  - rewrite Q3, E3. exact Hgp.
  - rewrite Q4, E4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. right. intros [].
  - intros a [].
  - intros a [].
  - intros HPRE2 _.
    assert (Hrom0 : rom_view SEGS W (ms_mem ms0)).
    { intros a Hin. assert (HI : 0x10000 <= a < 0x5fb000).
      { destruct Hin as (sg & Hsg & _ & Hr). apply (pa_img_range a). exists sg. split; [exact Hsg | exact Hr]. }
      rewrite KEEP1 by (unfold NL_STK, NL_FRAME, ESTACK in *; lia). apply HROM. exact Hin. }
    apply (aentry_of_memchrM_x 0x10350 0x10370 _ (2 * ESTACK) ly S Hp W (ms_regs ms0) (ms_mem ms0) _ (OUT + A) 0 (O - A)
      (Z.of_nat (length ln)) AMEMCHR ltac:(unfold ESTACK; lia) HPRE2).
    + rewrite Q10, E32, E34, YI08.alu64_add_lit. unfold w64. f_equal. lia.
    + rewrite Q11. reflexivity.
    + rewrite Q12, E32, E33, alu_negmul. reflexivity.
    + lia.
    + lia.
    + lia.
    + lia.
    + (* src_ok: the O - A stream bytes are visible and off memchr's scratch *)
      intros a Ha. split.
      * rewrite KEEP1 by (first [lia | apply HOWIN; lia]).
        replace a with (OUT + (a - OUT)) by lia. rewrite HOB by lia. discriminate.
      * rewrite Usp0. intros [HA1 HA2]. apply (HOWIN a ltac:(lia)). unfold NL_STK, NL_FRAME, ESTACK in *. lia.
    + unfold amem_range in HMR |- *. lia.
    + apply (ra_kept (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem ms0)) (OUT + A) (O - A)).
      -- intros y Hy. apply KEEPSH. exact (MRY OUT (O + 8) y HMR ltac:(lia) ltac:(lia) ltac:(lia)).
      -- eapply range_addressable_sub; [exact HRA | lia | lia].
    + intros Hpos s Hs.
      assert (HY1 : 0 <= OUT + A < kHighMemEnd)
      by exact (MRY OUT (O + 8) (OUT + A) HMR ltac:(lia) ltac:(lia) ltac:(lia)).
      assert (HY2 : 0 <= OUT + A + (O - A) - 1 < kHighMemEnd)
      by exact (MRY OUT (O + 8) (OUT + A + (O - A) - 1) HMR ltac:(lia) ltac:(lia) ltac:(lia)).
      destruct (shadow_hull_below_stack (spZ regs - NL_STK) (spZ regs + XO) (OUT + A) (O - A) s HCL HY1 HY2 Hs)
        as [SA1 SA2].
      rewrite KEEP1 by assumption. apply HHV.
      assert (HM1 : shadow_addr OUT / 8 * 8 <= shadow_addr (OUT + A) / 8 * 8).
      { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia | apply shadow_mono; lia]. }
      replace (OUT + A + (O - A) - 1) with (OUT + O - 1) in Hs by lia. lia.
    + exact (consts_view_of_rom_view SEGS 0x10350 0x10370 W (ms_mem ms0) HCROM Hrom0).
    + split; [lia|]. split.
      * intros i Hi. exists (bv_unsigned (nth (Z.to_nat i) (ln ++ Z_to_bv 8 0 :: rest) (Z_to_bv 8 0))).
        split; [apply STB; lia | apply nl_line_byte; [lia | exact HnoZ]].
      * intros _. rewrite (STB (Z.of_nat (length ln)) ltac:(lia)). f_equal. apply nl_nul_byte. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HR10 & Hfr2 & Hpres2).
assert (HA0 : getr regs2 10 = w64 (OUT + A + Z.of_nat (length ln))).
{ rewrite HR10. destruct (Z.ltb_spec (Z.of_nat (length ln)) (O - A)); [reflexivity | lia]. }
(* back in next_line with a0 = g_out + A + |ln|; keep the frame and the three cells *)
jafter_call_keep_pi HS 38%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;3;4;5]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview E (w_H W) (ms_mem ms0) mem2 2%nat (spZ regs));
    [exact B2 | intros a Ha; apply Hfr2; [lia | intros [] | unfold ESTACK in *; lia] | exact Hpres2].
  - apply (region_kept_aview E (w_H W) (ms_mem ms0) mem2 10%nat PA);
    [exact B10 | intros a Ha; apply Hfr2; [lia | intros [] | unfold ESTACK in *; lia] | exact Hpres2].
  - apply (region_kept_aview E (w_H W) (ms_mem ms0) mem2 11%nat PL);
    [exact B11 | intros a Ha; apply Hfr2; [lia | intros [] | unfold ESTACK in *; lia] | exact Hpres2].
  - apply (region_kept_aview E (w_H W) (ms_mem ms0) mem2 12%nat PN);
    [exact B12 | intros a Ha; apply Hfr2; [lia | intros [] | unfold ESTACK in *; lia] | exact Hpres2]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 38 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 38)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs (nl_extra (A mod 2 ^ 64) (O mod 2 ^ 64) (OUT mod 2 ^ 64) vl vn)) Ea)
by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (C1a : ew Ea 1 = getr regs 1) by (rewrite OLDa by (cbv; lia); exact E1).
assert (C2a : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by (cbv; lia); exact B2).
assert (C10a : bv_unsigned (ew Ea 10) = PA) by (rewrite OLDa by (cbv; lia); exact B10).
assert (C11a : bv_unsigned (ew Ea 11) = PL) by (rewrite OLDa by (cbv; lia); exact B11).
assert (C12a : bv_unsigned (ew Ea 12) = PN) by (rewrite OLDa by (cbv; lia); exact B12).
assert (E10a : ew Ea 10 = Z_to_bv 64 PA) by (rewrite OLDa by (cbv; lia); exact E10).
assert (E11a : ew Ea 11 = Z_to_bv 64 PL) by (rewrite OLDa by (cbv; lia); exact E11).
assert (E12a : ew Ea 12 = Z_to_bv 64 PN) by (rewrite OLDa by (cbv; lia); exact E12).
assert (E32a : ew Ea 32 = Z_to_bv 64 A) by (rewrite OLDa by (cbv; lia); exact E32).
assert (E34a : ew Ea 34 = Z_to_bv 64 OUT) by (rewrite OLDa by (cbv; lia); exact E34).
assert (E37a : ew Ea 37 = Z_to_bv 64 SB) by (rewrite OLDa by (cbv; lia); exact E37).
prreg HS (10%bv : bv 5) R10a.
assert (F42 : ew Ea 42 = Z_to_bv 64 (OUT + A + Z.of_nat (length ln))) by (rewrite <- R10a; exact HA0).
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - NL_STK <= a < spZ regs + XO) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. rewrite (Hfr2 a Ha ltac:(intros []) ltac:(unfold NL_STK, NL_FRAME, ESTACK in *; lia)).
  apply KEEP1; assumption. }
assert (KEEPSH2 : forall y, 0 <= y < kHighMemEnd ->
  aview SEGS (w_H W) mem2 (shadow_of_addr SHADOW_OFF y) = aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF y)).
{ intros y Hy. destruct (shadow_below_stack (spZ regs - NL_STK) (spZ regs + XO) y HCL Hy) as [SA1 SA2].
  unfold shadow_of_addr. change (SHADOW_OFF + y / 8) with (shadow_addr y). apply KEEP2; assumption. }
assert (HBxa : U Ea Bx = SHADOW_OFF)
by (unfold Bx; rewrite (U_atom Ea 37 SB E37a) by (unfold SB; lia); reflexivity).
assert (SHOK2 : sh_ok SEGS Bx nl_SH Ea (mrestrict (w_H W) mem2)).
{ unfold sh_ok, nl_SH. constructor; [|constructor; [|constructor; [|constructor]]].
  - eapply shent_ok_of_range;
    [ apply (ra_kept (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem2) PA 8);
      [intros y Hy; apply KEEPSH2; lia | exact RAA]
    | exact HBxa | rewrite (U_atom Ea 10 PA E10a) by lia; reflexivity | lia | lia
    | intros x Hx; unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia ].
  - eapply shent_ok_of_range;
    [ apply (ra_kept (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem2) PL 8);
      [intros y Hy; apply KEEPSH2; lia | exact RAL]
    | exact HBxa | rewrite (U_atom Ea 11 PL E11a) by lia; reflexivity | lia | lia
    | intros x Hx; unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia ].
  - eapply shent_ok_of_range;
    [ apply (ra_kept (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem2) PN 8);
      [intros y Hy; apply KEEPSH2; lia | exact RAN]
    | exact HBxa | rewrite (U_atom Ea 12 PN E12a) by lia; reflexivity | lia | lia
    | intros x Hx; unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia ]. }
(* the NULL arm is refuted: memchr found the NUL inside the stream *)
psrr_branch_tok RUN BR HS SHOK2 Bspan.
+ exfalso. rewrite branch_eq_U, (U_atom Ea 42 _ F42), U_lit in Hc0 by lia.
  apply Z.eqb_eq in Hc0. lia.
+ (* the stores *line = g_out + A, *len = |ln|, *at = A + |ln| + 1, return 1 *)
  paj_run_tok_x RUN HS HJ2 SHOK2 Bspan. { nl_awr C2a C10a C11a C12a. }
  prreg HS (1%bv : bv 5) R1b. prreg HS (10%bv : bv 5) R10b.
  assert (FRM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - NL_STK <= a < spZ regs + XO) ->
    aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
  { intros a Ha Hno. nl_kept HFr1 C2a C10a C11a C12a. apply KEEP2; assumption. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss _ =>
    pose proof (st_ok_pi_region_nth Ev ss _ 1 _ HS eq_refl) as RG1;
    pose proof (st_ok_pi_region_nth Ev ss _ 2 _ HS eq_refl) as RG2;
    pose proof (st_ok_pi_region_nth Ev ss _ 3 _ HS eq_refl) as RG3 end.
  cbn [ms_mem restrict] in RG1, RG2, RG3.
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 0 8 _ (A + Z.of_nat (length ln) + 1) RG1 C10a
    ltac:(cbn [In]; left; reflexivity)) as VPA.
  match type of VPA with ?P -> _ => assert (DPA : P); [|specialize (VPA DPA ltac:(zside) ltac:(zside))] end.
  { cbn [sv_denot]. rewrite E32a, E34a, F42, !Z.add_0_r, !Z_to_bv_bv_unsigned, !mul_lit, !YI08.alu64_add_lit.
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    transitivity ((A + Z.of_nat (length ln) + 1 + (A + OUT) * 2 ^ 64) mod 2 ^ 64);
    [f_equal; ring | apply Z_mod_plus_full]. }
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 0 8 _ (OUT + A) RG2 C11a
    ltac:(cbn [In]; left; reflexivity)) as VPL.
  match type of VPL with ?P -> _ => assert (DPL : P); [|specialize (VPL DPL ltac:(zside) ltac:(zside))] end.
  { cbn [sv_denot]. rewrite E32a, E34a, !Z.add_0_r, !Z_to_bv_bv_unsigned, !YI08.alu64_add_lit.
    f_equal. ring. }
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 0 8 _ (Z.of_nat (length ln)) RG3 C12a
    ltac:(cbn [In]; left; reflexivity)) as VPN.
  match type of VPN with ?P -> _ => assert (DPN : P); [|specialize (VPN DPN ltac:(zside) ltac:(zside))] end.
  { cbn [sv_denot]. rewrite E32a, E34a, F42, !Z.add_0_r, !Z_to_bv_bv_unsigned, !mul_lit, !YI08.alu64_add_lit.
    f_equal. ring. }
  rewrite Z.add_0_r in VPA, VPL, VPN.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold nl_post_x.
  lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
  split; [cbn [ms_regs]; rewrite R1b, C1a, Hra; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs); exact HJ2|].
  split; [lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs _ HS); [exact HAEa | vm_compute; reflexivity] end|].
  split; [reflexivity|]. cbn [ms_mem ms_regs].
  split; [intros a Hpa; apply (apresent_grows (w_H W) _ _ a HG1); apply Hpres2;
    apply (apresent_grows (w_H W) _ _ a HG0); apply (apresent_grows (w_H W) _ _ a HG); exact Hpa|].
  split; [intros a Ha Hno _; exact (FRM2 a Ha Hno)|].
  split.
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem _ _ 8 O); [|exact MO].
    intros q Hq. apply FRM2; [lia|]. unfold NL_STK, NL_FRAME, ESTACK in *. lia. }
  split.
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem _ _ 8 OUT); [|exact MOUT].
    intros q Hq. apply FRM2; [lia|]. unfold NL_STK, NL_FRAME, ESTACK in *. lia. }
  split.
  { intros i Hi. rewrite Hlen in Hi. rewrite FRM2; [apply HOB; lia | lia | apply HOWIN; lia]. }
  right. exists ln. split; [exact HAlt|]. split; [exists rest; split; [exact Hsplit | exact HnoZ]|].
  split; [rewrite R10b; reflexivity|].
  split; [exact VPA|]. split; [exact VPL | exact VPN].
-
(* *at = g_nout: A = O, return 0 *)
assert (HAeq : A = O).
{ rewrite branch_ne_U, (U_atom E 33 _ E33), (U_atom E 32 _ E32) in Hc by lia.
  apply (proj1 (Bool.negb_false_iff _)) in Hc. apply Z.eqb_eq in Hc.
  destruct (Z.eq_dec A O) as [| Hne]; [assumption|]. exfalso.
  destruct (HOW ltac:(lia)) as (HOUT0 & HOB63 & _). rewrite !Z.mod_small in Hc by lia. lia. }
paj_run_tok_x RUN HS HJ SHOK Bspan. { nl_awr B2 B10 B11 B12. }
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
assert (FRM : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - NL_STK <= a < spZ regs + XO) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. nl_kept HFr0 B2 B10 B11 B12. nl_kept HFr B2 B10 B11 B12. reflexivity. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss _ =>
  pose proof (st_ok_pi_region_nth Ev ss _ 3 _ HS eq_refl) as RG3;
  pose proof (st_ok_pi_region_nth Ev ss _ 4 _ HS eq_refl) as RG4;
  pose proof (st_ok_pi_region_nth Ev ss _ 5 _ HS eq_refl) as RG5 end.
cbn [ms_mem restrict] in RG3, RG4, RG5.
pose proof (field_of_region _ _ _ _ _ _ _ _ _ 0 8 _ (A mod 2 ^ 64) RG3 B10 ltac:(cbn [In]; tauto)
  ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(zside) ltac:(zside)) as VA.
pose proof (field_of_region _ _ _ _ _ _ _ _ _ 0 8 _ vl RG4 B11 ltac:(cbn [In]; tauto)
  ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(zside) ltac:(zside)) as VL.
pose proof (field_of_region _ _ _ _ _ _ _ _ _ 0 8 _ vn RG5 B12 ltac:(cbn [In]; tauto)
  ltac:(cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(zside) ltac:(zside)) as VN.
rewrite Z.add_0_r in VA, VL, VN.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold nl_post_x.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs); exact HJ|].
split; [lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs _ HS); [exact HAE | vm_compute; reflexivity] end|].
split; [reflexivity|]. cbn [ms_mem ms_regs].
split; [intros a Hpa; apply (apresent_grows (w_H W) _ _ a HG0); apply (apresent_grows (w_H W) _ _ a HG); exact Hpa|].
split; [intros a Ha Hno _; exact (FRM a Ha Hno)|].
split.
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem _ _ 8 O); [|exact MO].
  intros q Hq. apply FRM; [lia|]. unfold NL_STK, NL_FRAME, ESTACK in *. lia. }
split.
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem _ _ 8 OUT); [|exact MOUT].
  intros q Hq. apply FRM; [lia|]. unfold NL_STK, NL_FRAME, ESTACK in *. lia. }
split.
{ intros i Hi. rewrite Hlen in Hi. destruct (HOW ltac:(lia)) as (HU0 & HU63 & HU40 & HUW).
  rewrite FRM; [apply HOB; lia | lia | apply HUW; lia]. }
left. split; [exact HAeq|]. split; [rewrite R10; reflexivity|].
intros a Ha. apply in_cells_inv in Ha. destruct Ha as [Ha | [Ha | Ha]].
+ exact (aview_of_val_mem2 _ _ _ _ PA _ a MA' VA Ha).
+ exact (aview_of_val_mem2 _ _ _ _ PL _ a ML VL Ha).
+ exact (aview_of_val_mem2 _ _ _ _ PN _ a MN VN Ha).
Qed.

(* route R (a Theorem Labs lane crew, G7-leaf-AB): the walk at a world relation R, a LIFT of pb_next_line_x (no re-proof): the
   strict SRr fact is an SRrG fact at every R containing wle, and its post journal is the R journal at R (nl_spec_xR_of_x). *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Theorem pb_next_line_xR : nl_spec_xR B PST ARx R A_next_lineP.
Proof. exact (nl_spec_xR_of_x B PST ARx R WLE_R _ pb_next_line_x). Qed.
End wR.

End c.

(* ---- THE AR STATEMENT, re-derived (CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_next_line's statement is the AR walk's, byte-identical,
   now a corollary of pb_next_line_x at ARx := ARi0 (cgif's AR with the head set empty), PST := [].  The Section
   takes LX0 in place of LAWS (the instance builds it once: W_journal_x.AR_laws_x_ARi0 (YCbqG.AR_laws_x_of_AR ..));
   the bridges are W_contract_x nl_spec_x_AR0 and W_sites_x amemchr_realizesM_x_of_AR0. ---- *)
Section cAR.
Variable B : asyms.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis NLAP : nl_objs_apart.
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Theorem pb_next_line : nl_spec B A_next_lineP.
Proof.
apply nl_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
pose proof (amemchr_realizesM_x_of_AR0 SEGS B _ _ _ AMEMCHR) as AMX.
eapply pb_next_line_x; eassumption.
Qed.
End cAR.
End b.
End a.
