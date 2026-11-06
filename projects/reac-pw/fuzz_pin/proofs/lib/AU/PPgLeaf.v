(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632 for reac-pw/fuzz_qdisc's image A (fuzz_qdisc.asan sha256 980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e): it walks check_slots 0x7e870 against lib/A/QPgCSpec.v's qdisc_check_specX on the CONCRETE image tfibsegs / tfibtbl_lib, so knock's PAImg layer is gone (paj_run_tok / psrr_branch_tok / paj_ret_at -> the kit's aj_run_tok / srr_branch_tok / SRr_ret_at, step_entry -> check_entry over entry_st_ok_full); step_regions -> the 16-byte save slot stack_region 16 and the divisor cell 0x10350 (a base-None region with the literal chunk QD_MAGIC, paid by the contract's val_mem premise), knock's kp_region, step_SH and GOT / shadow-cell regions are dropped (no object, no shadow check, no shadow base); step_facts keeps only atom 2 (sp); knock's kawr / kwr (stack or object) -> awr_stk / kwr_stk (stack only), kept_step -> lib/A/QPgSlots.v's kept_run; knock's obj_at post is dropped (check_slots returns void), and the four `bne a0,a3` abort branches are refuted with lib/Prog/qdisc_div.v's lemmas; the arithmetic lemmas and the plumbing (qd_run, qd_keep, qd_branch, qd_leaf) are lib/A/QPgSlots.v's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 160c9b4d5750; made for reac-pw/fuzz_pin's image A (fuzz_pin.asan sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16): it walks check_known 0x80aa4, check_row 0x80acc and check_label 0x80aec against lib/A/PPgCSpec.v's tpin_check_known_specX and tpin_eq_leaf_specX (= tpin_check_row_specX = tpin_check_label_specX) over tfibsegs / tfibtbl_lib; the premise block is pin_pre_kit (destructured, its achain and event clauses unused) and the post is pin_post_simple with E = no cell (the extra premise of its memory clause) and R = True; check_entry -> lf_entry over the 16-byte save slot only (the divisor cell region qd_magic_region is dropped: no data read), awr_stk / kwr_stk -> lf_awr_stk / lf_kwr_stk; the plumbing of lib/A/QPgSlots.v (qd_run, qd_keep, qd_branch, qd_leaf, kept_run, same_io_wvb) and lib/A/QPgRt.v's RTBx / RTBspan / rt_extra are copied here under the lf_ prefix (qd_leaf without its a0 clause, ending in R's True); qdisc's arithmetic lemmas are dropped, and the abort branches (`beq` of the two `seqz` values in check_known, `bne a0,a1` in check_row / check_label) are refuted from the contract premises by lf_seqz_U / lf_seqz_ne and Z.eqb_refl. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgLeaf.v of this library, for reac-pw/fuzz_pin's image B (fuzz_pin.asan-ubsan, sha256 d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f). What differs: the entries are image B's (A_CHECK_KNOWN 0x80af8, A_CHECK_ROW 0x80b24, A_CHECK_LABEL 0x80b48, the st_value of check_known / check_row / check_label in the unstripped twin's .symtab); the image modules are image B's lib/AU twins (AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm; YCeh.ro_tfa_below_ofl for ACeh's); the contract lib/A/PPgCSpec.v is the same text. Image B's code of the three functions is image A's code word for word at the new addresses (abort is at 0x87844, so the abort call's word differs) plus one trap word `unimp` (c0001073) after each abort call (0x80b20, 0x80b44, 0x80b68); the trap word is reached only through the abort path, which the walk refutes as image A's does, so the proof text is image A's. *)
(* The three leaves (image B's excerpts with the runtime's names made neutral; the unstripped twin names them). Each opens a
   16-byte frame and saves ra: `addi sp,sp,-16` and `sd ra,8(sp)`. That store into [sp - 16, sp) is the walk's only
   write (lf_awr_stk: it lies in [sp0 - STK, sp0) by pin_pre_kit's two stack-window clauses; lf_kwr_stk: no write leaves
   it). No load is shadow-checked (the only load is the saved ra) and no data cell is read.
   check_known 0x80af8, 44 bytes:
     0x80b00 seqz a0,a0 ; 0x80b04 seqz a1,a1 ; 0x80b08 beq a0,a1,0x80b18.
     TAKEN would reach the abort path (0x80b18 jal before_abort, 0x80b1c jal abort, then the trap word 0x80b20).
     It is refuted: the engine's
     condition is (a0 = 0 ? 1 : 0) = (a1 = 0 ? 1 : 0) (lf_seqz_U), and CK1.1 (a0 = 0 iff a1 <> 0) makes the two
     values differ (lf_seqz_ne).
     not taken: 0x80b0c ld ra,8(sp) ; 0x80b10 addi sp,sp,16 ; 0x80b14 ret, with ra and sp restored.
   check_row 0x80b24 and check_label 0x80b48, 36 bytes each, the same code:
     0x80b2c / 0x80b50 bne a0,a1 -> 0x80b3c / 0x80b60 (the abort path, then the trap word 0x80b44 / 0x80b68).
     TAKEN is refuted: CR1.1 (a0 = a1) makes the
     engine's `negb (a0 =? a1)` equal to `negb true` (Z.eqb_refl).
     not taken: ld ra,8(sp) ; addi sp,sp,16 ; ret. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* the entries (image B, fuzz_pin.asan-ubsan: st_value of check_known / check_row / check_label in the unstripped
   twin's .symtab, = the first word of each excerpt) *)
Definition A_CHECK_KNOWN : Z := 0x80af8.
Definition A_CHECK_ROW : Z := 0x80b24.
Definition A_CHECK_LABEL : Z := 0x80b48.
(* the walk's shadow base: env slot 32 = SB (reac-pw/fuzz_qdisc's lib/A/QPgRt.v:61-63 RTBx / RTBspan / rt_extra) *)
Definition lf_RTBx : sv := SOff 32 0.
Definition lf_RTBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition lf_rt_extra : list word := [Z_to_bv 64 SB].
(* ---- the arithmetic of check_known's abort test ---- *)
(* `seqz a, x` (sltiu a, x, 1) as the engine leaves it *)
Lemma lf_seqz_U : forall E n (x : word), ew E n = x ->
U E (SAlu ALU_SLTU (SOff n 0) (SLit 1)) = if bv_unsigned x =? 0 then 1 else 0.
Proof.
intros E n x Hx. rewrite U_SAlu, U_SOff, U_SLit, Hx, Z.add_0_r, zcanon_unsigned. cbn [zalu_raw].
change (zcanon 1) with 1.
pose proof (bv_unsigned_in_range 64 x) as Hr.
destruct (Z.eqb_spec (bv_unsigned x) 0) as [H0 | H0].
- rewrite H0. reflexivity.
- rewrite (proj2 (Z.ltb_ge (bv_unsigned x) 1)) by lia. reflexivity.
Qed.
(* CK1.1 (a0 = 0 iff a1 <> 0) makes the two `seqz` values differ *)
Lemma lf_seqz_ne : forall x y : word, (x = Z_to_bv 64 0 <-> y <> Z_to_bv 64 0) ->
((if bv_unsigned x =? 0 then 1 else 0) =? (if bv_unsigned y =? 0 then 1 else 0)) = false.
Proof.
intros x y H.
assert (Z0 : forall z : word, z = Z_to_bv 64 0 <-> bv_unsigned z = 0).
{ intros z. split; intros Hz.
  - rewrite Hz, Z_to_bv_unsigned. reflexivity.
  - apply bv_eq. rewrite Hz, Z_to_bv_unsigned. reflexivity. }
destruct (Z.eqb_spec (bv_unsigned x) 0) as [Hx | Hx], (Z.eqb_spec (bv_unsigned y) 0) as [Hy | Hy].
- exfalso. exact (proj1 H (proj2 (Z0 x) Hx) (proj2 (Z0 y) Hy)).
- reflexivity.
- reflexivity.
- exfalso. exact (Hx (proj1 (Z0 x) (proj2 H (fun Hy' => Hy (proj1 (Z0 y) Hy'))))).
Qed.
(* ---- the walk's plumbing (reac-pw/fuzz_qdisc's lib/A/QPgSlots.v:123-188, lib/A/QPgCheck.v:45-69) ---- *)
Lemma lf_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
(* a run keeps every byte outside the zone its write windows lie in *)
Lemma lf_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview tfibsegs H m1 a = aview tfibsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview tfibsegs H m2 a = aview tfibsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
Definition lf_regions : smem := [ stack_region 16 ].
(* sp in [2^46, 2^47], 16-aligned: it places the save slot's window outside the shadow band, so the engine needs no
   shadow entry for it *)
Definition lf_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4) ] [] [].
Definition lf_ss (a : Z) : sstate := mkSS a sr_atoms lf_regions None lf_facts.
(* the write-range obligation: the save slot [sp - 16, sp) lies in the caller's stack allowance [sp0 - STK, sp0)
   (pin_pre_kit's two stack-window clauses); every other region is read-only *)
Ltac lf_awr_stk :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch goal with B2 : bv_unsigned (ew E 2) = ?spv |- _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
[reflexivity | rewrite B2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ]
end end.
(* every write window of a state lies in the save slot [sp - 16, sp) *)
Ltac lf_kwr_stk :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
first [ lazymatch goal with B2 : bv_unsigned (ew _ 2) = _ |- _ => rewrite B2 in Hb end; lia | lia ] | ]);
destruct Hr.
(* one run of the engine to its next stop *)
Ltac lf_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok tfibtbl_lib_ok HS HJ SHOK lf_RTBspan; [awr | ] end.
(* fold the run's frame into the kept-memory fact KE *)
Ltac lf_keep kwr :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (lf_kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by kwr end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the branch the engine cannot decide, with its condition named *)
Ltac lf_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tfibtbl_lib_ok HS SH lf_RTBspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* the `ret` leaf: pin_post_simple with E = no cell and R = True; the memory clause comes from KE *)
Ltac lf_leaf :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _ |- _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [lazymatch goal with E1 : ew E 1 = _, Hra : YK0s.ret_ok _ |- _ => rewrite R1, E1, Hra; reflexivity end|];
split; [unfold EV_leaf; rewrite Z.add_0_r; eapply ajournal_materialize; eassumption|];
split; [eapply aregs_preserved_of_st_ok; [exact HS | eassumption | vm_compute; reflexivity]|];
split; [reflexivity|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply lf_same_io_wvb]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split;
[ lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
  let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
  intros a Ha Hz _; exact (KE a Ha Hz) end
| exact I ]
end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Lemma lf_entry : forall a (W : world tfibsegs) regs memc,
(forall x, spZ regs - 16 <= x < spZ regs -> apresent (w_H W) memc x) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
st_ok tfibsegs (Ereg regs lf_rt_extra) (lf_ss a) (restrict (w_H W) (mkst regs (Z_to_bv 64 a) memc (seg_rom tfibsegs))).
Proof.
intros a W regs memc Hpres Hsp Hal.
rewrite restrict_mkst_fx.
set (E := Ereg regs lf_rt_extra).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold lf_ss. apply (entry_st_ok_full tfibsegs); change (Ereg regs lf_rt_extra) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lf_regions, stack_region. repeat apply Forall_cons; try apply Forall_nil.
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
- apply pairwise_disjoint_of_extents.
unfold lf_regions, stack_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]]. cbn [lf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
(* ================================ check_known (CK1) ================================ *)
Theorem pin_pb_check_knownX : tpin_check_known_specX tfibsegs B MT A_CHECK_KNOWN.
Proof using MTL TL LAWS.
unfold tpin_check_known_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch HK H10.
unfold pin_pre_kit in HK.
destruct HK as (HJ & Hra & Hra4 & Hgp & Htp & Hch & Hal16 & Hwlo & Hwhi & Hev).
unfold T_leaf_STK in Hwlo.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (lf_entry A_CHECK_KNOWN W regs memc ltac:(intros a Ha; apply Hpres; lia) ltac:(lia) Hal16) as HS.
remember (Ereg regs lf_rt_extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs lf_rt_extra) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = getr regs 10) by (subst E; exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (subst E; exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
clear HE.
assert (SHOK : sh_ok tfibsegs lf_RTBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 A_CHECK_KNOWN) with (Z_to_bv 64 A_CHECK_KNOWN).
(* 0x80af8 addi sp,sp,-16; sd ra,8(sp); seqz a0,a0; seqz a1,a1; stop at 0x80b08 beq a0,a1 *)
lf_run lf_awr_stk. lf_keep lf_kwr_stk.
lf_branch Hn.
- (* beq TAKEN would reach the abort path 0x80b18 (and the trap word 0x80b20): refuted,
   (a0 = 0 ? 1 : 0) <> (a1 = 0 ? 1 : 0) by CK1.1 *)
exfalso. rewrite branch_eq_U, (lf_seqz_U E 10 _ E10), (lf_seqz_U E 11 _ E11), (lf_seqz_ne _ _ H10) in Hn.
discriminate Hn.
- (* not taken: 0x80b0c ld ra,8(sp); addi sp,sp,16; ret *)
clear Hn. lf_run lf_awr_stk. lf_keep lf_kwr_stk.
lf_leaf.
Qed.
(* ========================= check_row and check_label (CR1) ========================= *)
Theorem pin_pb_eq_leafX : forall a, a = A_CHECK_ROW \/ a = A_CHECK_LABEL -> tpin_eq_leaf_specX tfibsegs B MT a.
Proof using MTL TL LAWS.
intros a Ha. unfold tpin_eq_leaf_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch HK Heq.
unfold pin_pre_kit in HK.
destruct HK as (HJ & Hra & Hra4 & Hgp & Htp & Hch & Hal16 & Hwlo & Hwhi & Hev).
unfold T_leaf_STK in Hwlo.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (lf_entry a W regs memc ltac:(intros x Hx; apply Hpres; lia) ltac:(lia) Hal16) as HS.
remember (Ereg regs lf_rt_extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs lf_rt_extra) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = getr regs 10) by (subst E; exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (subst E; exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
clear HE.
assert (SHOK : sh_ok tfibsegs lf_RTBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 16 <= x < spZ regs) ->
aview tfibsegs (w_H W) memc x = aview tfibsegs (w_H W) memc x) by (intros; reflexivity).
unfold cfg_at.
destruct Ha as [-> | ->].
- (* check_row 0x80b24 addi sp,sp,-16; sd ra,8(sp); stop at 0x80b2c bne a0,a1 *)
change (w64 A_CHECK_ROW) with (Z_to_bv 64 A_CHECK_ROW).
lf_run lf_awr_stk. lf_keep lf_kwr_stk.
lf_branch Hn.
+ (* bne TAKEN would reach the abort path 0x80b3c (and the trap word 0x80b44): refuted, a0 = a1 by CR1.1 *)
exfalso. rewrite branch_ne_U, !U_SOff, E10, E11, Heq, Z.eqb_refl in Hn. discriminate Hn.
+ (* not taken: 0x80b30 ld ra,8(sp); addi sp,sp,16; ret *)
clear Hn. lf_run lf_awr_stk. lf_keep lf_kwr_stk.
lf_leaf.
- (* check_label 0x80b48 addi sp,sp,-16; sd ra,8(sp); stop at 0x80b50 bne a0,a1 *)
change (w64 A_CHECK_LABEL) with (Z_to_bv 64 A_CHECK_LABEL).
lf_run lf_awr_stk. lf_keep lf_kwr_stk.
lf_branch Hn.
+ (* bne TAKEN would reach the abort path 0x80b60 (and the trap word 0x80b68): refuted, a0 = a1 by CR1.1 *)
exfalso. rewrite branch_ne_U, !U_SOff, E10, E11, Heq, Z.eqb_refl in Hn. discriminate Hn.
+ (* not taken: 0x80b54 ld ra,8(sp); addi sp,sp,16; ret *)
clear Hn. lf_run lf_awr_stk. lf_keep lf_kwr_stk.
lf_leaf.
Qed.
Theorem pin_pb_check_rowX : tpin_check_row_specX tfibsegs B MT A_CHECK_ROW.
Proof using MTL TL LAWS. exact (pin_pb_eq_leafX A_CHECK_ROW (or_introl eq_refl)). Qed.
Theorem pin_pb_check_labelX : tpin_check_label_specX tfibsegs B MT A_CHECK_LABEL.
Proof using MTL TL LAWS. exact (pin_pb_eq_leafX A_CHECK_LABEL (or_intror eq_refl)). Qed.
End d.
End b.
Print Assumptions pin_pb_check_knownX.
Print Assumptions pin_pb_check_rowX.
Print Assumptions pin_pb_check_labelX.
