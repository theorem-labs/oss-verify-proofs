(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module paths and module names changed; 229 of its 263 lines of code are new or changed and 220 lines of the source are left out. *)
(* trim's image-B walk, the leading-blank loop (0x89680 .. 0x896b4): tr_lead_ok : TR_AFTER_stmt -> TR_LEAD_stmt
   (lib/B/Prog/trim_k.v), by strong induction on lead - i, the blanks still before s0 = p + i. Written for image B on
   the pattern of the image-A G3 walk owner's image-A trailing loop lib/A/Prog/trim_tr.v (commit 07dedd5b93c6;
   image A's leading loop was not pushed when this was written) and of fuzz_command's answer_l.v (a loop with inline
   checks, re-seeded at each iteration); the plain proof of the same loop is the unit owner's lib/Prog/trim.v LOOP1 at
   db8c4beebf62, the UBSan one lib/U/Prog/trim.v:159-190 (commit 523c6a205596). One iteration:
     check 1 (0x89680-0x8968c, slow arm 0x896b8-0x896bc, error call 0x896c0 errpath_load1, load1 at a0 = s0 = p + i):
       the obligation that p + i is addressable, from trim_pre's sa_addr p (|s| + 1);
     the byte c = s[i] (0x89690 `lbu a4,0(s0)`), `bltu a1,a4` (0x20 < c) and bit c of the mask (0x89698-0x896a0): c not
       blank leaves to AFTER 0x896c4 (and then i = trim_lead s);
     0x896a4 `beq s0,a3` (a3 = -1), UBSan trap site 1 of 3 (s + 1 wraps; to the unimp 0x89770): decided not taken by
       the executor from the seed's range fact s0 = p + i <= 2 ^ 47 - 1 (p + |s| + 1 <= 2 ^ 47, tr_cx_facts);
     s0, s2 and a0 step (s0 = a0 = p + i + 1, s2 = 1 - (p + i + 1)) and `j 0x89680`. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase trim_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob trim_k trim_f trim_tr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegInstB.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- LEAD, 0x89680: every register its own atom but a1 = 0x20, a2 = the mask and a3 = -1 (pinned); s0 = p + i
   (atom 8; the load reads through it), a0 = p + i (atom 10, the check's address), s1 = SB (atom 9), s2 = 1 - s0 (atom
   18); the extra atom 32 is the byte at s0, the one region (read only). The range fact of atom 8 (s0 <= 2 ^ 47 - 1)
   decides the trap test `beq s0,a3` at 0x896a4 not taken. ---- *)
Definition tl_regs : list sv := sr_set (sr_set (sr_set sr_atoms 11%bv (SLit 32)) 12%bv (SLit TR_MASK)) 13%bv (SLit TR_M1).
Definition tl_regions : smem :=
[ YP09.mkRegion (Some 8%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition tl_facts : facts :=
mkFacts [ (8%nat, mkAF 4096 (2 ^ 47 - 1) 0); (10%nat, mkAF 4096 (2 ^ 47 - 1) 0);
          (9%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition tl_ss : sstate := mkSS TR_LEAD tl_regs tl_regions None tl_facts.
(* the registers a loop iteration does not write, and those an exit to AFTER does not write *)
Definition TL_KEPT : list (bv 5) := 2%bv :: 9%bv :: TR_KEPT.
Definition TLX_KEPT : list (bv 5) := 2%bv :: 8%bv :: 9%bv :: 18%bv :: TR_KEPT.
Lemma tlx_kept_incl : forall r, In r (2%bv :: 9%bv :: TR_KEPT) -> In r TLX_KEPT.
Proof.
intros r [<- | [<- | Hr]]; unfold TLX_KEPT; [left; reflexivity | right; right; left; reflexivity | right; right; right; right; exact Hr].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition tl_E (regs1 : bvmap 5 word) (C : Z) : env := Eimg (Ereg regs1 [Z_to_bv 64 C]).

Lemma tl_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc x C,
getr regs1 8 = w64 x -> getr regs1 10 = w64 x ->
getr regs1 11 = w64 32 -> getr regs1 12 = w64 TR_MASK -> getr regs1 13 = w64 TR_M1 -> getr regs1 9 = w64 SB ->
4096 <= x <= 2 ^ 47 - 1 -> 0 <= C <= 255 ->
rdW W memc x = Some C ->
st_ok_pi SEGS VAL (tl_E regs1 C) tl_ss (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + TR_LEAD)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc x C H8 H10 H11 H12 H13 H9 Hx HC HrdC.
set (E := tl_E regs1 C).
assert (E8 : ew E 8 = Z_to_bv 64 x) by (subst E; unfold tl_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 8 8%bv eq_refl); exact H8).
assert (E10 : ew E 10 = Z_to_bv 64 x) by (subst E; unfold tl_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 10 10%bv eq_refl); exact H10).
assert (E9 : ew E 9 = Z_to_bv 64 SB) by (subst E; unfold tl_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 C) by (subst E; unfold tl_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
rewrite restrict_mkst_fx. unfold tl_ss. apply pa_entry_st_ok_full.
- unfold tl_regs. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H11] | intros X; discriminate X | cbn [sv_denot]; exact H12] | intros X; discriminate X | cbn [sv_denot]; exact H13].
- vm_compute. reflexivity.
- unfold tl_regions. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E8, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
  destruct (aview_byte SEGS (w_H W) memc x C HrdC) as (b & Hb & Hv & _).
  exists b. split.
  + cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E32.
    rewrite !Z.add_0_r, (unsigned_lit_small C), (unsigned_lit_small C) by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
    subst C. apply Z_to_bv_bv_unsigned.
  + rewrite !Z.add_0_r. exact Hb.
- cbn. tauto.
- split; [|split; exact I].
  cbn [tl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E8, E10, E9, E32, !unsigned_lit_small by (unfold SB; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* after a run that writes nothing: the environment agrees with the seed's E0 below 33 (HAE), the memory is memc
   (KM), every byte present in memc is present (KP) *)
Ltac tl_after E0 HAE KM KP :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in let KPn := fresh "KPn" in
    assert (HAEn : env_agree 33 E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H _) (ms_mem msn) a = aview SEGS (w_H _) _ a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          rewrite (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (fun _ => False) HFr);
          [ exact (KM a Ha)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
            destruct Hin
          | exact Ha | tauto ]);
    assert (KPn : forall a, apresent (w_H _) _ a -> apresent (w_H _) (ms_mem msn) a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (apresent_grows _ _ _ a HG (KP a Ha)));
    clear HFr HG HAE KM KP; rename HAEn into HAE; rename KMn into KM; rename KPn into KP;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Ltac tl_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.


(* a register's value from the executor's terms over atoms of known value *)
Ltac tl_reg N :=
  rewrite N; cbn [sv_denot];
  repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- context [ew ?E ?n] => rewrite H end;
  rewrite ?w64_off, ?md_mul_lit, ?alu64_add_lit, ?alu64_sub_lit;
  unfold w64; first [reflexivity | f_equal; lia].

(* one iteration from LEAD, for every i with lead - i = n, given the loop at every smaller n *)
Definition TR_LEAD_n (n : nat) : Prop :=
forall ly S W regs mem md ch p s regs1 memc mdc i,
(seg_spec.trim_lead s - i = n)%nat ->
tr_cx B ly S W regs mem md ch p s -> tr_mid B ly S W regs mem md p s memc mdc -> tr_regs regs regs1 ->
(i <= seg_spec.trim_lead s)%nat ->
getr regs1 8 = w64 (p + Z.of_nat i) -> getr regs1 10 = w64 (p + Z.of_nat i) ->
getr regs1 18 = w64 (1 - (p + Z.of_nat i)) ->
getr regs1 11 = w64 32 -> getr regs1 12 = w64 TR_MASK -> getr regs1 13 = w64 TR_M1 ->
tr_at B regs ly S W mem md p s regs1 memc mdc TR_LEAD.

Lemma tl_step : TR_AFTER_stmt B -> forall n, (forall m, (m < n)%nat -> TR_LEAD_n m) -> TR_LEAD_n n.
Proof.
intros HAFTER n IH ly S W regs mem md ch p s regs1 memc mdc i Hn HCX HMID HRG Hi H8 H10 H18 H11 H12 H13.
pose proof (tr_cx_facts B LAWS ly S W regs mem md ch p s HCX)
  as (HSTR & HADDR & HZONE & HPR & HSB & Hp4096 & Hp47 & Hn32 & HOUT & Hal16 & Hsp0 & Hsp47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_trim = 4128) by reflexivity.
destruct HSTR as ((HZS & NZ) & HTAIL).
pose proof (TrimB.lead_le s NZ) as HLL.
pose proof (TrimB.lead_stop s NZ) as LSTOP.
pose proof (TrimB.lead_blank s i NZ) as LBL.
set (lead := seg_spec.trim_lead s) in *.
pose proof HRG as (R2 & R9 & RK).
pose proof HMID as (HJ & KEEP & KPR & _).
(* the byte at s0 = p + i *)
pose proof (sa_zs_nth _ p s i HZS ltac:(lia)) as V0.
set (C := nth i s 0) in *.
assert (VC : rdW W memc (p + Z.of_nat i) = Some C) by (rewrite KEEP by lia; exact V0).
destruct (aview_byte SEGS (w_H W) mem _ _ V0) as (_ & _ & _ & HCr).
(* the seed *)
pose proof (tl_entry W regs1 memc (p + Z.of_nat i) C H8 H10 H11 H12 H13 R9 ltac:(lia) ltac:(lia) VC) as HS.
assert (HEI : img_env VAL A_LIM (tl_E regs1 C)) by (unfold tl_E; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg regs1 [Z_to_bv 64 C]) (tl_E regs1 C))
  by (split; [intros n0 Hn0; unfold tl_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (E8 : ew (tl_E regs1 C) 8 = Z_to_bv 64 (p + Z.of_nat i)) by (unfold tl_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 8 8%bv eq_refl); exact H8).
assert (E10 : ew (tl_E regs1 C) 10 = Z_to_bv 64 (p + Z.of_nat i)) by (unfold tl_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 10 10%bv eq_refl); exact H10).
assert (E18 : ew (tl_E regs1 C) 18 = Z_to_bv 64 (1 - (p + Z.of_nat i))) by (unfold tl_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 18 18%bv eq_refl); exact H18).
assert (E9 : ew (tl_E regs1 C) 9 = Z_to_bv 64 SB) by (unfold tl_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 9 9%bv eq_refl); exact R9).
assert (E32 : ew (tl_E regs1 C) 32 = Z_to_bv 64 C) by (unfold tl_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
revert HS HEI HA0 E8 E10 E18 E9 E32. generalize (tl_E regs1 C) as E0. intros E0 HS HEI HA0 E8 E10 E18 E9 E32.
pose proof (env_agree_refl 33 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W memc a = rdW W memc a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W) memc a -> apresent (w_H W) memc a) by (intros; assumption).
assert (SHOK : sh_ok SEGS tr_Bx [] E0 (mrestrict (w_H W) memc)) by constructor.
assert (HRA : range_addressable (rdW W memc) SHADOW_OFF p (Z.of_nat (length s) + 1)).
{ apply (range_addressable_kept_win (rdW W mem) (rdW W memc) (spZ regs - STK_trim) (spZ regs)); [exact KEEP | lia | lia | lia |].
  destruct HADDR as (_ & _ & _ & HRA & _). exact HRA. }
(* the exits to AFTER: s0 and s2 unchanged, and i = lead *)
assert (EXIT : forall regs1' memc' mdc', tr_mid B ly S W regs mem md p s memc' mdc' ->
  (forall r, In r TLX_KEPT -> getr regs1' r = getr regs1 r) -> i = lead ->
  SRr SEGS W (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + TR_AFTER)) memc' (seg_rom SEGS)) mdc') (tr_post B regs ly S W mem md p s)).
{ intros regs1' memc' mdc' HM' HK' Hil.
  apply (HAFTER ly S W regs mem md ch p s regs1' memc' mdc' HCX HM'
    (tr_regs_kept regs regs1 regs1' HRG (fun r Hr => HK' r (tlx_kept_incl r Hr)))).
  - rewrite (HK' 8%bv) by (cbn; tauto). rewrite H8, Hil. reflexivity.
  - rewrite (HK' 18%bv) by (cbn; tauto). rewrite H18, Hil. reflexivity. }
unfold tr_at.
(* 0x89680 .. 0x89694: check 1, the byte, `bltu a1,a4` (c > 32 leaves) *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem]. unfold tr_Bx. rewrite (U_atom _ 9 SB E9), (U_atom _ 10 _ E10) by (unfold SB; lia). rewrite SB_SHADOW_OFF.
  exact (range_addressable_sub _ _ p (Z.of_nat (length s) + 1) (p + Z.of_nat i) 1 HRA ltac:(lia) ltac:(lia)). }
{ tl_awr. }
tl_after E0 HAE KM KP.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* c > 32: not blank, so i = lead; AFTER *)
  pose proof (tr_br_ltu_lit _ 32 _ 32 _ (tr_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) ltac:(lia) Hc) as Cgt.
  apply Z.ltb_lt in Cgt. clear Hc.
  assert (BC : SegModel.blank C = false)
    by (destruct (SegModel.blank C) eqn:BC0; [apply TrimB.blank_le32 in BC0; lia | reflexivity]).
  assert (Hil : i = lead).
  { destruct (Nat.eq_dec i lead) as [Ei|Ei]; [exact Ei|]. exfalso. pose proof (LBL ltac:(lia)) as X. fold C in X. congruence. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan TR_AFTER. { tl_awr. }
  tl_after E0 HAE KM KP.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ TLX_KEPT HS (tr_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
  apply (EXIT rg mm mdn) end.
  + exact (tr_mid_step B ly S W regs mem md p s memc mdc _ _ HMID ltac:(lia) HJ (fun a Ha _ => KM a Ha) (fun a _ Ha _ => KP a Ha)).
  + exact HK.
  + exact Hil.
- (* c <= 32: bit c of the mask *)
  pose proof (tr_br_ltu_lit _ 32 _ 32 _ (tr_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) ltac:(lia) Hc) as Cle.
  apply Z.ltb_ge in Cle. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan TR_LEAD. { tl_awr. }
  tl_after E0 HAE KM KP.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* the bit is 0: not blank, so i = lead; AFTER *)
    pose proof (tr_br_mask _ 32 C _ (tr_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) Hc) as BC.
    apply Bool.negb_true_iff in BC. clear Hc.
    assert (Hil : i = lead).
    { destruct (Nat.eq_dec i lead) as [Ei|Ei]; [exact Ei|]. exfalso. pose proof (LBL ltac:(lia)) as X. fold C in X. congruence. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan TR_AFTER. { tl_awr. }
    tl_after E0 HAE KM KP.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ TLX_KEPT HS (tr_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    apply (EXIT rg mm mdn) end.
    * exact (tr_mid_step B ly S W regs mem md p s memc mdc _ _ HMID ltac:(lia) HJ (fun a Ha _ => KM a Ha) (fun a _ Ha _ => KP a Ha)).
    * exact HK.
    * exact Hil.
  + (* blank: i < lead; the trap test 0x896a4 (decided), s0, s2, a0 step, back to LEAD *)
    pose proof (tr_br_mask _ 32 C _ (tr_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) Hc) as BC.
    apply Bool.negb_false_iff in BC. clear Hc.
    assert (Hil : (i < lead)%nat).
    { destruct (Nat.eq_dec i lead) as [Ei|Ei]; [|lia]. exfalso. rewrite <- Ei in LSTOP. fold C in LSTOP. congruence. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan TR_LEAD. { tl_awr. }
    tl_after E0 HAE KM KP.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ TL_KEPT HS (tr_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pose proof (tr_ag_ew _ _ _ 8 _ HAE ltac:(lia) E8) as E8n. pose proof (tr_ag_ew _ _ _ 10 _ HAE ltac:(lia) E10) as E10n.
    pose proof (tr_ag_ew _ _ _ 18 _ HAE ltac:(lia) E18) as E18n.
    prreg HS (8%bv : bv 5) N8. prreg HS (10%bv : bv 5) N10. prreg HS (18%bv : bv 5) N18.
    prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12. prreg HS (13%bv : bv 5) N13.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    apply (IH (lead - Datatypes.S i)%nat ltac:(lia) ly S W regs mem md ch p s rg mm mdn (Datatypes.S i)) end.
    * reflexivity.
    * exact HCX.
    * exact (tr_mid_step B ly S W regs mem md p s memc mdc _ _ HMID ltac:(lia) HJ (fun a Ha _ => KM a Ha) (fun a _ Ha _ => KP a Ha)).
    * exact (tr_regs_kept regs regs1 _ HRG (fun r Hr => HK r Hr)).
    * lia.
    * tl_reg N8.
    * tl_reg N10.
    * tl_reg N18.
    * first [exact N11 | rewrite N11; vm_compute; reflexivity].
    * first [exact N12 | rewrite N12; vm_compute; reflexivity].
    * first [exact N13 | rewrite N13; vm_compute; reflexivity].
Qed.

(* LEAD, by strong induction on lead - i *)
Lemma tr_lead_ok : TR_AFTER_stmt B -> TR_LEAD_stmt B.
Proof.
intros HAFTER.
assert (ALL : forall k m, (m <= k)%nat -> TR_LEAD_n m).
{ induction k as [|k IHk]; intros m Hm.
  - apply (tl_step HAFTER m). intros m' Hm'. lia.
  - apply (tl_step HAFTER m). intros m' Hm'. apply (IHk m'). lia. }
unfold TR_LEAD_stmt.
intros ly S W regs mem md ch p s regs1 memc mdc i HCX HMID HRG Hi H8 H10 H18 H11 H12 H13.
exact (ALL _ _ (le_n _) ly S W regs mem md ch p s regs1 memc mdc i eq_refl HCX HMID HRG Hi H8 H10 H18 H11 H12 H13).
Qed.

End e.
End f.
End d.
