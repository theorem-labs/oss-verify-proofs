(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (G-BRA): the walk of image B's wake (fuzz_reply.asan-ubsan, 0x82484, 101
   instructions) over a GENERIC allocator relation ARx with its laws: pb_wake_x proves lib/B/W_wake_c_x.v's
   wk_spec_x B PST ARx RG at wake's entry (BASE + AF_fr_wake).  SOURCE: the AR walk lib/B/W_wake.v (pb_wake : wk_spec B
   RG (BASE + AF_fr_wake); taken by path from a working branch 22c3862876d), converted step for step by
   the C1 method of image A's relay_add conversion (fc38e83bfbf; its room form, W_relay_add.v (sha256 db38e2e41e5d; internal record), Section c).  The
   machine-code account, the symbolic states and every numeral are the AR walk's (image B's, checked there against the
   pinned binary); its AR-free helpers (wk_land_m32 .. wk_grab, the entry state) are restated here with the same text,
   so that this file does not build the AR walk.
   What changes against the AR proof, and nothing else:
   - afn_pre -> afn_pre_x, ajournal -> YCbqG.ajournal_x (Hp after S, kept to the end), the token run -> YC80x's
     SRr_run_pi_tok_AJx (tactic paj_run_tok_x), al_const / al_frames / frames_bounds -> alx_const / alx_frames /
     frames_bounds_x, FFL at Hp, YCbq.v's region_kept_stack_aj -> its ajournal_x twin wk_region_kept_stack_aj_x;
   - the fake-frame seat is W_frame_x.v's aj_stack_malloc_pres_at_raw_x (the room kit: OWNLOW, WFx / WFL / SMALLOC in
     place of model_laws / stack_malloc_progressP, ASM0 the image-presence contract of __asan_stack_malloc_0), whose post
     gives S2 = set_fs f S; the release is W_frame_x.v's aj_flag_store_pi_x (WFx / WFL / SFREE); errno_not_aowned ->
     errno_not_aowned_x;
   - the fake frame off image B ([0x10000, 0x5fc000)): W_frame_b.v's frm_off_imgB read AR's ledger; here
     wk_frm_off_imgB_x reads the image law alx_img and IMGC (W_frame_x.v Section c's text);
   - g_wake[1]: the generic journal's image clause exempts PST, so g_wake[1] (-1, awake_at) is carried from the entry as
     errno is - by the two runs' frames and by the seat's raw clause, where an image byte off the owned statics (HWK) is
     aowned in no ARx state (alx_owned_image) - not by the journal (image A's walk does the same, RAK);
   - wk_post_x's seat conjunct: the end state is stack_free_state 0 fpos S2 (a set_fs, Reusable/YG01.v) with
     S2 = set_fs f S, so it is set_fs (its own fake stack) S by conversion. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_frame W_img W_wake_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_frame_x W_wake_c_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---- andi x, -32 on a nonnegative value (W_wake.v wk_land_m32, verbatim). *)
Lemma wk_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551584 = 32 * (x / 32).
Proof.
  intros x Hx.
  replace (32 * (x / 32)) with (Z.shiftl (Z.shiftr x 5) 5)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; change (2 ^ 5) with 32; lia).
  replace 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity.
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec.
  destruct (Z.lt_ge_cases i 64) as [Hl|Hl].
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - assert (TB : Z.testbit x i = false)
      by (rewrite <- (Z.mod_small x (2 ^ 64)) by lia; apply Z.mod_pow2_bits_high; lia).
    rewrite TB. reflexivity.
Qed.

(* the rounded frame base Q below a 16-aligned sp (W_wake.v wkQ / wkQ_facts, verbatim) *)
Definition wkQ (S : Z) : Z := 32 * ((S - 64) / 32).
Lemma wkQ_facts : forall S, S mod 16 = 0 -> (wkQ S = S - 64 \/ wkQ S = S - 80) /\ wkQ S mod 32 = 0.
Proof.
  intros S HS. unfold wkQ.
  pose proof (Z.div_mod (S - 64) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (S - 64) 32 ltac:(lia)) as R.
  pose proof (Z.div_mod S 16 ltac:(lia)) as D2. rewrite HS, Z.add_0_r in D2.
  split; [|rewrite Z.mul_comm; apply Z_mod_mult].
  set (q := (S - 64) / 32) in *. set (r := (S - 64) mod 32) in *. set (k := S / 16) in *.
  assert (Hr : r = 0 \/ r = 16) by lia. lia.
Qed.
(* the engine's value of sp after `andi sp,sp,-32` (0x824a8), measured: SAlu ALU_AND (SOff 2 (-64)) (SLit (-32)) *)
Definition WK_AND : sv := SAlu ALU_AND (SOff 2 (-64)) (SLit (-32)).
Lemma wk_and_den : forall E S, ew E 2 = Z_to_bv 64 S -> 64 <= S < 2 ^ 64 ->
  sv_denot E WK_AND = Z_to_bv 64 (wkQ S).
Proof.
  intros E S H HS. apply bv_eq. rewrite unsigned_lit_small
    by (unfold wkQ; split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia] | Z.div_mod_to_equations; lia]).
  change (bv_unsigned (sv_denot E WK_AND)) with (U E WK_AND). unfold WK_AND.
  rewrite U_SAlu, (U_atom_off E 2 S (-64) H) by lia. rewrite U_SLit.
  change (zcanon (-32)) with 18446744073709551584. cbn [zalu_raw].
  rewrite wk_land_m32 by lia. apply zcanon_id. unfold M64, wkQ. Z.div_mod_to_equations. lia.
Qed.

(* `mv s1,sp` (0x824ac) is `addi s1,sp,0`: the engine keeps the + 0 *)
Lemma wk_add0 : forall E e, sv_denot E (SAlu ALU_ADD e (SLit 0)) = sv_denot E e.
Proof.
  intros E e. apply bv_eq. change (bv_unsigned (sv_denot E (SAlu ALU_ADD e (SLit 0)))) with (U E (SAlu ALU_ADD e (SLit 0))).
  change (bv_unsigned (sv_denot E e)) with (U E e).
  rewrite U_SAlu, (U_lit E 0) by lia. cbn [zalu_raw]. rewrite Z.add_0_r. apply zcanon_id. apply U_range.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_wakeP : Z := BASE + AF_fr_wake.

(* ---- The statement is W_wake_c_x.v's wk_spec_x B PST ARx RG at wake's entry, verbatim (no local form). *)

Section d.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable RG : rep_globals.
Context {hl : Z}.
(* ---- Section hypotheses.  The AR walk's LAWS / TL / TLF / ML / SMP / ASMP / ASF / FFL / HV8 / HWK / HERRS, converted as
   image A's W_relay_add.v (sha256 db38e2e41e5d; internal record) Section c states them: LAWS the generic relation's laws; in place of model_laws (ML) and
   stack_malloc_progressP (SMP) the model invariant WFx with its law WFL and the two facts W_frame_x.v reads off them,
   SFREE (the release's frame split) and SMALLOC (the seat's malloc path, whose state is a set_fs); OWNLOW the law
   call_effect_journal_x asks (W_frame_x.v Section fsp); IMGC the image cover W_frame_b.v's frm_off_imgB read off AR's
   ledger (W_frame_x.v Section c's text, image B's top 0x5fc000); ASM0 (ASMP's twin) __asan_stack_malloc_0's contract
   with the image-presence conjunct; ASF / FFL the frame laws over ARx.  HV8 / HWK / HERRS verbatim: the placement of
   g_wake (A_OBJ 8 of lib/B/W_listing.v = 0xa2520 = g_wake by nm, decided at the pin by wk_hv8_fr below), g_wake[1]'s
   bytes image bytes off the runtime's owned statics and off errno (lib/B/W_relay_add_cut.v's text), errno off the
   owned statics. *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis ASM0 : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis HV8 : VAL (A_OBJ 8) = rg_wake RG.
Hypothesis HWK : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HERRS : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* the plain journal's token run over ARx (Reusable/YC80x.v; W_kit.v's paj_run with its listing arguments) *)
Let RUN0 := Reusable.YC80x.SRr_run_pi_tok_AJx wsym SEGS B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) VAL SIGMA
fr_prog_listing (@pl_tpi fr_prog_listing PL_fr) (@pl_tw fr_prog_listing PL_fr) pa_fetch_ok pa_cert pa_B_ok A_LIM
A_LIM_text (@pl_lim fr_prog_listing PL_fr) (@pl_len fr_prog_listing PL_fr) (@pl_tpi_eq fr_prog_listing PL_fr)
(@pl_tw_eq fr_prog_listing PL_fr).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Let RUNF := aj_flag_store_pi_x (PL := PL_fr) B PST ARx LAWS ASF FFL WFx WFL SFREE.

(* ---- Helpers. ---- *)
(* presence of image bytes along the walk (W_wake.v wk_pres_grow, verbatim) *)
Lemma wk_pres_grow : forall (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, in_img SEGS a -> apresent H m0 a -> apresent H m1 a) ->
mem_grows (mrestrict H m1) (mrestrict H m2) ->
forall a, in_img SEGS a -> apresent H m0 a -> apresent H m2 a.
Proof. intros H m0 m1 m2 P Hgr a Hi Ha. exact (apresent_grows _ _ _ _ Hgr (P a Hi Ha)). Qed.
(* YCbq.v region_kept_stack_aj over ajournal_x (its proof: the journal's presence and stack clauses) *)
Lemma wk_region_kept_stack_aj_x : forall E lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi (Er : Z -> Prop)
n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
ajournal_x SEGS B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k
(K1 & _) HJ Hn Hshi Hlo Hhi Hw1 Hw2.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply K1; lia.
- intros _. apply (apresent_writable SEGS). apply Hpres. lia.
Qed.
(* W_frame_b.v frm_off_imgB over ARx: a live fake frame lies off image B's [0x10000, 0x5fc000) - at or above the
   image's top (the image law alx_img), which IMGC puts at or above 0x5fc000 (W_frame_x.v frm_off_imgP_x's proof) *)
Lemma wk_frm_off_imgB_x : forall ly S Hp (W : world SEGS) mem md cid pos,
ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos + fs_frame_bytes cid <= 0x10000 \/ 0x5fc000 <= frame_addr ly cid pos.
Proof.
intros ly S Hp W mem md cid pos HAR Hin.
destruct (IMGC ly S Hp W mem md HAR) as [_ C2].
pose proof (proj2 (alx_img _ _ _ LAWS ly S Hp W mem md HAR) cid pos Hin) as Hf.
right. lia.
Qed.
(* a byte outside every write window of a run keeps its view (the run's frame_of) *)
Ltac wk_nowin :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
 [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu in Hr end;
  unfold SB in Hr; lia |]);
destruct Hin.
(* after a plain run: its frame over the unhidden memory as HFr, its growth as HGr; the raw frame dropped *)
Ltac wk_grab :=
lazymatch goal with Hf : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => rename Hf into HFr_x; rename HFr_x into HFr end;
lazymatch goal with Hg : mem_grows (mrestrict _ _) (mrestrict _ _) |- _ => rename Hg into HGr_x; rename HGr_x into HGr end;
try match goal with Hf : frame_of _ _ ?x _ |- _ => lazymatch x with mrestrict _ _ => fail | _ => clear Hf end end.

(* ---- The entry state (W_wake.v's, verbatim): the frame's two stack pieces written by the prologue (the zero word at
   sp - 64 and the six saved registers at sp - 48 .. sp - 8), the ASan frame-pointer slot Q + 8 (atom 34 = Q), the GOT
   slot of the shadow cell, the cell, the GOT slot of the use-after-return cell and the cell. ---- *)
Definition Bx : sv := SOff 33 0.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition wk_regions0 : smem :=
[ YP09.mkRegion (Some 2%nat) (-64) (-56) (-64) (-56) [];
  YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [];
  YP09.mkRegion (Some 34%nat) 8 16 8 16 [];
  got_regionP; bcell_regionP 33; uar_got_regionP 32; uar_cell_regionP 32 ].
Definition wk_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF 0x10000 0x5fc000 2); (33%nat, mkAF SB SB 0);
  (34%nat, mkAF (2^46) (2^47) 5) ].
Definition ss_wk0 : sstate := mkSS AF_fr_wake sr_atoms wk_regions0 None (mkFacts wk_atoms0 [] []).
Definition wk_extra (S : Z) : list word := map (Z_to_bv 64) [as_uar_cell B; SB; wkQ S].
Lemma wk_entry_x : forall W ly S Hp regs mem md ch,
afn_pre_x SEGS B ARx WK_STK ly S Hp W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (wk_extra (spZ regs)))) ss_wk0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_wakeP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx [] (Eimg (Ereg regs (wk_extra (spZ regs)))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : WK_STK = 16448) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
destruct (wkQ_facts (spZ regs) Hal16) as (HQ & HQ32).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (wk_extra (spZ regs)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (wkQ (spZ regs))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E247 : ew E (A_OBJ 6) = Z_to_bv 64 (VAL (A_OBJ 6))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E271 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 6 ltac:(lia)) as Hob6. pose proof (pa_obj_img 30 ltac:(lia)) as Hob30.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (UQ : bv_unsigned (ew E 34) = wkQ (spZ regs)) by (rewrite E34; apply unsigned_lit_small; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_wk0, A_wakeP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold wk_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
    repeat apply Forall_cons; try apply Forall_nil.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UQ.
      split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
      [cbn [sv_denot]; rewrite E271, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E271) by (pose proof (pa_val_range (A_OBJ 30)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 (SOff 33 0) SB);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB (A_OBJ 6) (VAL (A_OBJ 6)) E247) by (pose proof (pa_val_range (A_OBJ 6)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 6)) 0 8 (SOff 32 0) (as_uar_cell B));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 32%nat (as_uar_cell B) E32) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
  + apply pairwise_disjoint_of_extents.
    unfold wk_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 32%nat (as_uar_cell B) E32) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E271) by (pose proof (pa_val_range (A_OBJ 30)); lia).
    rewrite (VB (A_OBJ 6) (VAL (A_OBJ 6)) E247) by (pose proof (pa_val_range (A_OBJ 6)); lia).
    cbn [base_val]. rewrite Usp, UQ.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hob0 Hob6 Hob30 Huar Hsep HQ. clear.
    unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
    repeat split; first [ assumption | (apply or_comm; assumption)
    | (repeat match goal with H : pa_val (A_OBJ _) + 8 <= _ \/ _ |- _ => clear H | H : as_uar_cell _ + 4 <= _ \/ _ |- _ => clear H end; lia) ].
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok wk_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, UQ, E32, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Huar Huar4 HQ HQ32. clear.
    unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold sh_ok. constructor.
Qed.

(* ---- The walk. ---- *)
Theorem pb_wake_x : wk_spec_x B PST ARx RG (BASE + AF_fr_wake).
Proof.
intros W ly S Hp regs mem md ch HPRE HCNT HWAKE HROM.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (wk_entry_x W ly S Hp regs mem md ch HPRE) as [HS SHOK].
pose proof (ajournal_x_init SEGS B PST ARx WK_STK [] ly S Hp W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : WK_STK = 16448) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (wkQ_facts (spZ regs) Hal16) as (HQ & HQ32).
set (Q := wkQ (spZ regs)) in *.
pose proof (pal_env B TL) as Henv. destruct Henv as ((He0 & He1) & HeImg & _).
remember (Eimg (Ereg regs (wk_extra (spZ regs)))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 Q) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (UQ : bv_unsigned (ew E 34) = Q) by (rewrite E34; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs (wk_extra (spZ regs))) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_wakeP) with (Z_to_bv 64 A_wakeP). unfold A_wakeP.
(* 0x82484-0x824d0: the prologue, sp rounded down to Q, the use-after-return cell (1: the beqz is decided), a0 = 64 *)
paj_run_tok_x RUN0 HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fp b0 bc ly0 own0) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 34%nat (Q - spZ regs)); [reflexivity | rewrite UQ; lia | cbn; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (WB : alloc_ceiling + 16448 <= spZ regs) by lia.
wk_grab.
(* errno and g_wake[1] lie in no write window of the run (image bytes; the run writes the stack) *)
lazymatch type of HGr with mem_grows (mrestrict _ ?m0) (mrestrict _ ?m1) =>
  pose proof (wk_pres_grow (w_H W) mem m0 m1 (fun a _ Ha => Ha) HGr) as PRES;
  assert (KE1 : forall i, 0 <= i < 4 -> aview SEGS (w_H W) m1 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i))
  by (intros i Hi; apply (aview_kept_out E _ (w_H W) mem m1 HFr); [lia|];
      pose proof (pa_img_range _ (HeImg (as_errno B + i) ltac:(lia))) as Ri; wk_nowin);
  assert (KW1 : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; pose proof (pa_img_range _ (proj1 (HWK a Ha))) as Ra;
      apply (aview_kept_out E _ (w_H W) mem m1 HFr); [lia|]; wk_nowin) end.
clear HFr HGr.
(* sp and s1 hold Q: name it by the atom 34 *)
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_restrict_reg SEGS (w_H W) E ssx msx 2%bv HS) as R2;
  pose proof (st_ok_restrict_reg SEGS (w_H W) E ssx msx 9%bv HS) as R9;
  let e2 := eval vm_compute in (sr_get (ss_regs ssx) 2%bv) in change (sr_get (ss_regs ssx) 2%bv) with e2 in R2;
  let e9 := eval vm_compute in (sr_get (ss_regs ssx) 9%bv) in change (sr_get (ss_regs ssx) 9%bv) with e9 in R9 end.
change (SAlu ALU_AND (SOff 2 (-64)) (SLit (-32))) with WK_AND in R2, R9.
rewrite ?wk_add0 in R9.
rewrite (wk_and_den E (spZ regs) E2) in R2, R9 by lia. fold Q in R2, R9.
assert (D34 : sv_denot E (SOff 34 0) = Z_to_bv 64 Q) by (cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
pose proof (ast_ok_set_reg_fp SEGS E _ _ 2%bv (SOff 34 0) HS eq_refl ltac:(cbn [ms_regs restrict]; rewrite D34, R2; reflexivity)) as HS'.
clear HS; rename HS' into HS.
pose proof (ast_ok_set_reg_fp SEGS E _ _ 9%bv (SOff 34 0) HS eq_refl ltac:(cbn [ms_regs restrict]; rewrite D34, R9; reflexivity)) as HS'.
clear HS; rename HS' into HS.
(* 0x824d0: __asan_stack_malloc_0 (64), the class-0 fake frame: the room kit's seat (its state a set_fs of S) *)
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite (palf_sm0 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply (W_frame_x.aj_stack_malloc_pres_at_raw_x SEGS B PST ARx LAWS Hsegs (pal_env B TL) OWNLOW WFx WFL SMALLOC 0 ASM0
    ltac:(lia) W rg mm WK_STK (spZ regs) _ ly S Hp W mem md [] ly S Hp _ 0 (Q - spZ regs) _ HJ) end.
  - unfold spZ at 1. rewrite R2. rewrite unsigned_lit_small by lia. unfold spZ in *. lia.
  - revert HQ32 Hal16. clear. intros. Z.div_mod_to_equations. lia.
  - lia. - rewrite WS, Hes. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp. - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HCNT. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HPR0 & HRAW & (fS2 & ES2)).
pose proof (fun a Hi Ha => HPR0 a Hi (PRES a Hi Ha)) as PRES2. clear PRES HPR0. rename PRES2 into PRES.
pose proof (proj1 HJ) as HARa. pose proof (proj1 HJ2) as HARb.
(* errno and g_wake[1] across the seat: its raw clause (aowned in neither state, below the callee's stack window) *)
assert (KE2 : forall i, 0 <= i < 4 -> aview SEGS (w_H W) mem2 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
{ intros i Hi. rewrite <- (KE1 i Hi). cbn [ms_mem restrict mkst] in HRAW |- *.
  pose proof (HeImg (as_errno B + i) ltac:(lia)) as Ii. pose proof (pa_img_range _ Ii) as Ri.
  apply HRAW; [lia | | | lia].
  - exact (errno_not_aowned_x SEGS B ARx LAWS (pal_env B TL) _ _ _ _ _ _ HARa (fun j Hj => HERRS (as_errno B + j) ltac:(lia)) i Hi).
  - exact (errno_not_aowned_x SEGS B ARx LAWS (pal_env B TL) _ _ _ _ _ _ HARb (fun j Hj => HERRS (as_errno B + j) ltac:(lia)) i Hi). }
assert (KW2 : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (KW1 a Ha). cbn [ms_mem restrict mkst] in HRAW |- *.
  destruct (HWK a Ha) as (Hi & Ho & _). pose proof (pa_img_range _ Hi) as Ra.
  apply HRAW; [lia | | | lia].
  - intros Hown. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARa Hi) Hown)).
  - intros Hown. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARb Hi) Hown)). }
clear HRAW KE1 KW1.
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W) mem2) HP2 [1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil].
  - eapply wk_region_kept_stack_aj_x; [exact HK | exact HJ2 | exact Usp | cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia].
  - eapply wk_region_kept_stack_aj_x; [exact HK | exact HJ2 | exact UQ | cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 35)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs (wk_extra (spZ regs))) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
prreg HS (10%bv : bv 5) RF.
(* seat the fake frame: F at atom 39 (a0), its flag FL at 512, the frame's shadow SB + F / 8 at 513 *)
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HFal & HFapp & HFpres & HFSpres).
pose proof (wk_frm_off_imgB_x _ _ _ _ _ _ 0 fpos HARb Hfin2) as HFimg.
destruct (FFL _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *. fold F FL in HFal, HFapp, HFpres, HFSpres, HFimg, HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc, HF4096, HFceil, HFhigh.
(* the flag byte is no image byte, so neither g_wake[1]'s nor errno's *)
assert (HFLgw : ~ (rg_wake RG + 4 <= FL < rg_wake RG + 8)) by (intros Hw; exact (HFLimg (proj1 (HWK FL Hw)))).
assert (HFLer : ~ (as_errno B <= FL < as_errno B + 4)) by (intros Hw; exact (HFLimg (HeImg FL Hw))).
assert (RF' : ew Ea 39 = Z_to_bv 64 F) by (rewrite <- RF, Ha0; reflexivity).
pose proof (st_ok_pi_havoc_hi 512 Ea _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc Ea 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 512)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (E512 : ew Eb 512 = Z_to_bv 64 FL) by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E513 : ew Eb 513 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAEb : env_agree 32 (Ereg regs (wk_extra (spZ regs))) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (E39 : ew Eb 39 = Z_to_bv 64 F) by (rewrite OLDb by lia; exact RF').
assert (E33b : ew Eb 33 = Z_to_bv 64 SB) by (rewrite OLDb, OLDa by lia; exact E33).
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
pose proof (st_ok_pi_add_fact Eb _ _ 39 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E39, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_fact Eb _ _ 512 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E512, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_fact Eb _ _ 513 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E513, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_alias Eb _ _ _ _ HS (shadow_decl_ok Eb 39 33 513 F SB E39 ltac:(lia) E33b E513)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
assert (U2b : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb, OLDa by lia; exact Usp).
assert (U34b : bv_unsigned (ew Eb 34) = Q) by (rewrite OLDb, OLDa by lia; exact UQ).
assert (U39 : bv_unsigned (ew Eb 39) = F) by (rewrite E39; apply unsigned_lit_small; lia).
assert (U512 : bv_unsigned (ew Eb 512) = FL) by (rewrite E512; apply unsigned_lit_small; lia).
assert (U513 : bv_unsigned (ew Eb 513) = SB + F / 8) by (rewrite E513; apply unsigned_lit_small; unfold SB; lia).
assert (U249 : bv_unsigned (ew Eb 249) = VAL (A_OBJ 8)) by exact (HEIb (A_OBJ 8) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U249o : bv_unsigned (ew Eb (A_OBJ 8)) = VAL (A_OBJ 8)) by exact U249.
pose proof (pa_obj_img 8 ltac:(lia)) as Hob8.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in C1, C3, Hslo, Hshi, H47, Hceil, Hstk0,
HFimg, HFapp, HF4096, HFceil, HFhigh, HFLapp, HFLimg, HFL4096, HFLc.
pose proof (st_ok_pi_add_region Eb _ _ (fframe_region 39 512 0 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 0) with 64; rewrite U39; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Eb _ F (64 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E512, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (64 - 8)) with (F + 64 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0) with 64; rewrite ?U39, ?U2b, ?U34b;
revert Hslo Hshi H47 Hceil Hstk0 C1 C3 WS HF4096 HFceil HFhigh HFimg HFapp HQ; clear; intros;
unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Eb _ _ (fshadow_region 513 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 0 / 8) with 8; rewrite U513; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres; apply (proj1 (HFSpres o ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Eb _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside |];
rewrite Z.add_0_r; apply val_mem_zero8; intros i Hi; unfold zero_shadow, shadow_of_addr in Hz; rewrite <- SB_SHADOW_OFF in Hz; apply Hz; change (64 / 8) with 8; lia ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0 / 8) with 8; rewrite ?U513, ?U39, ?U2b, ?U34b;
revert Hslo Hshi H47 Hceil Hstk0 C1 C3 WS HF4096 HFceil HFhigh HFimg HFapp HF8lo HF8hi HFq HF8 HQ; clear; intros;
unfold SB, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, alloc_ceiling in *; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
(* g_wake[1] (0x82574 `lw a0,4(a0)`, a0 = &g_wake): -1, kept from the entry (KW2: the first run's frame and the
   seat's raw clause) *)
pose proof (st_ok_pi_add_region Eb _ _ (YP09.mkRegion (Some (A_OBJ 8)) 4 8 4 4 [YP09.mkChunk 4 (CVal 4 (SLit 4294967295))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U249o; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Eb _ (VAL (A_OBJ 8)) 4 4 (SLit 4294967295) 4294967295); [reflexivity | zside | zside |];
rewrite HV8; apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem2); [intros k Hk; apply KW2; cbn in Hk; lia | exact HWAKE])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0 / 8) with 8; change (fs_frame_bytes 0) with 64; rewrite ?U249o, ?U249, ?U513, ?U39, ?U2b, ?U34b;
revert Hslo Hshi H47 Hceil Hstk0 C1 C3 WS HF4096 HFceil HFhigh HFimg HFapp HF8lo HF8hi HQ Hob8; clear; intros;
unfold SB, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, alloc_ceiling in *; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
(* the UBSan trap 0x82570 `beq &g_wake, -4` (-> unimp 0x82614): the runner decides it once g_wake's image atom (A_OBJ 8,
   atom 249) carries its range [0x10000, 0x5fc000] as a fact (W_traps.v recipe R1/R4; lib/B/W_op_add.v's form) *)
pose proof (st_ok_pi_add_fact Eb _ _ 249 (mkAF 0x10000 0x5fc000 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U249, Z.pow_0_r, Z.mod_1_r; lia)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
(* the frame's flag byte, a writable region on its atom 512 for the release's flag store 0x825c8 *)
lazymatch goal with HJx : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ _ |- _ =>
destruct (FFL _ _ _ _ mx _ 0 fpos (proj1 HJx) Hfin2) as (HFLp' & HFLo' & _ & _) end.
lazymatch goal with HJx : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ _ |- _ =>
destruct (alx_frames _ _ _ LAWS _ _ _ _ mx _ 0 fpos (proj1 HJx) Hfin2) as (_ & _ & HFpres' & HFSpres') end.
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *. fold F FL in HFLp', HFLo', HFpres', HFSpres'.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 512%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U512; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLp')
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?U512, ?U513, ?U39, ?U2b, ?U34b, ?U249;
repeat split;
lazymatch goal with
| |- ?fl + 1 <= F + ?l \/ F + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (F + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (F + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  exact (proj2 (HFpres' FL ltac:(lia)) HFLo')
| |- ?fl + 1 <= 2147450880 + F / 8 + ?l \/ 2147450880 + F / 8 + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (2147450880 + F / 8 + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (2147450880 + F / 8 + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  unfold shadow_addr in HFSpres'; rewrite <- SB_SHADOW_OFF in HFSpres'; unfold SB in HFSpres';
  exact (proj2 (HFSpres' (FL - (2147450880 + F / 8)) ltac:(lia)) ltac:(replace (2147450880 + F / 8 + (FL - (2147450880 + F / 8))) with FL by lia; exact HFLo'))
| |- ?fl + 1 <= SB + F / 8 + ?l \/ SB + F / 8 + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (SB + F / 8 + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (SB + F / 8 + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  unfold shadow_addr in HFSpres'; rewrite <- SB_SHADOW_OFF in HFSpres';
  exact (proj2 (HFSpres' (FL - (SB + F / 8)) ltac:(lia)) ltac:(replace (SB + F / 8 + (FL - (SB + F / 8))) with FL by lia; exact HFLo'))
| |- _ =>
  revert Hslo Hshi H47 Hceil Hstk0 C1 C3 WS HFL4096 HFLz HFLc HFLgw HV8 HQ Hob8; clear; intros;
  unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia
end)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
(* 0x824d4-0x82610: F <> 0 (the bnez is decided), F stored at Q + 8, the header, the shadow, b = 0, the trap test, the
   g_wake[1] read and the bltz (decided: -1), the release (magic, shadow 0xf5, the flag store) and the epilogue *)
paj_run_flag_sh_x RUNF HS HJ2.
{ lia. }
{ intros a (r & Hin & Hr).
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
cbn [In] in Hin. change (flag_addr ly 0 fpos) with FL.
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu in Hr end;
  first [ revert Hr; clear; intros Hr; lia
  | right; revert Hr; clear; intros Hr; lia
  | left; left; revert Hr HQ; clear; intros Hr HQ; assert (Hws : WK_STK = 16448) by reflexivity; lia
  | left; right; right; right; exists 0, fpos; split; [left; reflexivity|];
    change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
    first [ left; unfold in_zr; cbn [fst snd]; revert Hr; clear; intros Hr; lia
    | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8;
      revert Hr; clear; intros Hr; lia ]
  ]
| ]).
destruct Hin. }
{ intros msr HSr. change (flag_addr ly 0 fpos) with FL.
lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U512
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end.
rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0. }
wk_grab.
(* errno and g_wake[1] lie in no write window of the release run (image bytes, the flag byte is none) *)
lazymatch type of HGr with mem_grows (mrestrict _ ?m0) (mrestrict _ ?m1) =>
  pose proof (wk_pres_grow (w_H W) mem m0 m1 PRES HGr) as PRES3;
  assert (KE3 : forall i, 0 <= i < 4 -> aview SEGS (w_H W) m1 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i))
  by (intros i Hi; rewrite <- (KE2 i Hi);
      pose proof (pa_img_range _ (HeImg (as_errno B + i) ltac:(lia))) as Ri;
      assert (HFLe : FL <> as_errno B + i) by (intros Hq; apply HFLer; lia);
      apply (aview_kept_out _ _ (w_H W) m0 m1 HFr); [lia|]; wk_nowin);
  assert (KW3 : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; rewrite <- (KW2 a Ha);
      pose proof (pa_img_range _ (proj1 (HWK a Ha))) as Ra;
      assert (HFLa : FL <> a) by (intros Hq; apply HFLgw; lia);
      apply (aview_kept_out _ _ (w_H W) m0 m1 HFr); [lia|]; wk_nowin) end.
clear PRES HFr HGr. rename PRES3 into PRES.
prreg HS (1%bv : bv 5) Rr1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold wk_post_x.
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
  exists r, ly, (stack_free_state 0 fpos S2), Hp, m, d, 0 end.
split; [cbn [ms_regs]; rewrite Rr1, OLDb, OLDa, (EE 1%nat 1%bv eq_refl), Hra by lia; reflexivity|].
split.
{ cbn [ms_mem]. apply (proj2 (ajournal_gx_nil_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
  apply (ajournal_x_materialize SEGS B PST ARx LAWS Hsegs). exact HJ2. }
split. { eapply (aregs_preserved_of_st_ok SEGS _ Eb _ _ regs (wk_extra (spZ regs)) HS); [exact HAEb | vm_compute; reflexivity]. }
split. { rewrite <- Eab. unfold ablocks. rewrite blocks_stack_free_state. reflexivity. }
split. { cbn [ms_mem]. intros a Hi Ha. exact (PRES a Hi Ha). }
split.
{ unfold awake_at, arm. cbn [ms_mem]. apply (val_mem_kept SEGS (w_H W) (w_H W) mem); [|exact HWAKE].
  intros k Hk. cbn in Hk. apply KW3. lia. }
split. { cbn [ms_mem]. exact KE3. }
(* the seat: stack_free_state is a set_fs, of S2 = set_fs fS2 S *)
exists (st_fs (stack_free_state 0 fpos S2)). rewrite ES2. reflexivity.
Qed.
End d.
End b.
End a.

(* ---- The placement fact HV8 at the pin: PB_fr (lib/B W_img.v) and fr_globals_b (W_rep.v) (W_wake.v wk_hv8_fr). ---- *)
Section fr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma wk_hv8_fr : pa_val (PAImg := PB_fr) (A_OBJ 8) = rg_wake fr_globals_b.
Proof. vm_compute. reflexivity. Qed.
End fr.
