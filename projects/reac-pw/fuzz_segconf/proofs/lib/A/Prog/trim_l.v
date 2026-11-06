(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module paths and module names changed; 361 of its 399 lines of code are new or changed and 216 lines of the source are left out. *)
(* trim's image-A walk, the entry (0x890a8 .. 0x890dc) and the leading-blank loop (0x890e0 .. 0x8911c):
   tr_lead_ok : TR_AFTER_stmt -> TR_LEAD_stmt and tr_entry_ok : TR_LEAD_stmt -> the walk from trim's entry
   (lib/A/Prog/trim_k.v). The entry: the 32-byte frame and its four slots, s1 = s0 = p, s2 = the shadow base (the GOT
   word as_got_shadow B, listing object 0, holds the cell as_shadow_cell B, object 12, which holds SHADOW_OFF), a0 = 0x20,
   a1 = the blank mask. One iteration of the loop at s0 = s1 = p + i: check 1 (0x890e0-0x89114, load1 at s1: the
   obligation that p + i is addressable, from trim_pre's sa_addr), the byte c = s[i], `bltu 0x20, c` and bit c of the
   mask: c not blank leaves for AFTER (then i = trim_lead s), c blank steps s0 and s1 (then i < trim_lead s). The plain
   proof of the same loop: the plain-build walk owner's lib/Prog/trim.v LOOP1 at db8c4beebf62. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegGlob SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import trim_c trim_k trim_t trim_tr.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- LEAD, 0x890e0: every register its own atom but a0 = 0x20 and a1 = the mask (pinned); s0 = s1 = p + i (atoms 8,
   9), s2 = SB (atom 18); the extra atom 32 is the byte at s0, the one region (read only) ---- *)
Definition tl_regs : list sv := sr_set (sr_set sr_atoms 10%bv (SLit 32)) 11%bv (SLit TR_MASK).
Definition tl_regions : smem := [ YP09.mkRegion (Some 8%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition tl_facts : facts :=
mkFacts [ (8%nat, mkAF 4096 (2 ^ 47 - 1) 0); (9%nat, mkAF 4096 (2 ^ 47 - 1) 0); (18%nat, mkAF SB SB 0);
          (32%nat, mkAF 0 255 0) ] [] [].
Definition tl_ss : sstate := mkSS TR_LEAD tl_regs tl_regions None tl_facts.
(* the registers an iteration that leaves does not write *)
Definition TLX_KEPT : list (bv 5) := 2%bv :: 8%bv :: 9%bv :: 18%bv :: TR_KEPT.
Lemma tlx_kept_incl : forall r, In r (2%bv :: 18%bv :: TR_KEPT) -> In r TLX_KEPT.
Proof.
intros r [<- | [<- | Hr]]; unfold TLX_KEPT; [left; reflexivity | right; right; right; left; reflexivity | right; right; right; right; exact Hr].
Qed.
Definition TLL_KEPT : list (bv 5) := 2%bv :: 18%bv :: TR_KEPT.

(* ---- the entry, 0x890a8: every register its own atom, the extra atom 32 the shadow base SB; the frame [sp - 32, sp)
   (written), the GOT word of the shadow base and the shadow-base cell (read only) ---- *)
Definition te_regions : smem := [stack_region 32; got_regionP; bcell_regionP 32%nat].
Definition te_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0) ] [] [].
Definition te_ss : sstate := mkSS AF_trim sr_atoms te_regions None te_facts.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition te_E (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SB]).

Lemma tl_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc A C,
getr regs1 8 = w64 A -> getr regs1 9 = w64 A -> getr regs1 10 = w64 32 -> getr regs1 11 = w64 TR_MASK ->
getr regs1 18 = w64 SB -> 4096 <= A <= 2 ^ 47 - 1 -> 0 <= C <= 255 -> rdW W memc A = Some C ->
st_ok_pi SEGS VAL (tt_E regs1 C) tl_ss (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + TR_LEAD)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc A C H8 H9 H10 H11 H18 HA HC HrdC.
set (E := tt_E regs1 C).
assert (E8 : ew E 8 = Z_to_bv 64 A) by (subst E; unfold tt_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 8 8%bv eq_refl); exact H8).
assert (E9 : ew E 9 = Z_to_bv 64 A) by (subst E; unfold tt_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 9 9%bv eq_refl); exact H9).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; unfold tt_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 18 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 C) by (subst E; unfold tt_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
rewrite restrict_mkst_fx. unfold tl_ss. apply pa_entry_st_ok_full.
- unfold tl_regs. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H10] | intros X; discriminate X | cbn [sv_denot]; exact H11].
- vm_compute. reflexivity.
- unfold tl_regions. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E8, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
  destruct (aview_byte SEGS (w_H W) memc A C HrdC) as (b & Hb & Hv & _).
  exists b. split.
  + cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E32.
    rewrite !Z.add_0_r, (unsigned_lit_small C), (unsigned_lit_small C) by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
    subst C. apply Z_to_bv_bv_unsigned.
  + rewrite !Z.add_0_r. exact Hb.
- cbn. tauto.
- split; [|split; exact I].
  cbn [tl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E8, E9, E18, E32, !unsigned_lit_small by (unfold SB; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Ltac tl_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* after a run that writes nothing: the environment agrees with E0 below k (HAE), the memory is the seed's (KM),
   every byte present at the seed is present (KP) *)
Ltac tl_after E0 HAE KM KP :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    lazymatch type of HAE with env_agree ?k _ _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in let KPn := fresh "KPn" in
    assert (HAEn : env_agree k E0 En) by (env_agree_chain HAE);
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
    end
  end.

Lemma tr_lead_ok : TR_AFTER_stmt B -> TR_LEAD_stmt B.
Proof.
intros HAFTER. unfold TR_LEAD_stmt.
intros ly S W regs mem md ch p s regs1 memc mdc i HCX.
pose proof (tr_cx_facts B LAWS ly S W regs mem md ch p s HCX)
  as (HSTR & HADDR & HZONE & HPR & HSB & Hp4096 & Hp47 & Hn32 & HOUT & Hal16 & Hsp0 & Hsp47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_trim = 4128) by reflexivity.
pose proof HSTR as ((HZS & NZ) & HTAIL).
pose proof (TrimA.lead_le s NZ) as HLL.
pose proof (TrimA.lead_blank s) as HLB. pose proof (TrimA.lead_stop s NZ) as HLS.
set (lead := seg_spec.trim_lead s) in *.
(* one iteration, with the next one as a premise *)
assert (ITER : forall i regs1 memc mdc, (i <= lead)%nat ->
  tr_mid B ly S W regs mem md p s memc mdc -> tr_regs regs regs1 ->
  getr regs1 8 = w64 (p + Z.of_nat i) -> getr regs1 9 = w64 (p + Z.of_nat i) ->
  getr regs1 10 = w64 32 -> getr regs1 11 = w64 TR_MASK ->
  ((i < lead)%nat -> forall regs1' memc' mdc', tr_mid B ly S W regs mem md p s memc' mdc' -> tr_regs regs regs1' ->
     getr regs1' 8 = w64 (p + Z.of_nat (Datatypes.S i)) -> getr regs1' 9 = w64 (p + Z.of_nat (Datatypes.S i)) ->
     getr regs1' 10 = w64 32 -> getr regs1' 11 = w64 TR_MASK ->
     tr_at B regs ly S W mem md p s regs1' memc' mdc' TR_LEAD) ->
  tr_at B regs ly S W mem md p s regs1 memc mdc TR_LEAD).
{ clear regs1 memc mdc i.
  intros i regs1 memc mdc Hi HMID HRG H8 H9 H10 H11 NEXT.
  pose proof HRG as (R2 & R18 & RK).
  pose proof HMID as (HJ & KEEP & KPR & _).
  pose proof (sa_zs_nth _ p s i HZS ltac:(lia)) as V0.
  set (C := nth i s 0) in *.
  assert (VC : rdW W memc (p + Z.of_nat i) = Some C) by (rewrite KEEP by lia; exact V0).
  destruct (aview_byte SEGS (w_H W) mem _ _ V0) as (_ & _ & _ & HCr).
  pose proof (tl_entry W regs1 memc (p + Z.of_nat i) C H8 H9 H10 H11 R18 ltac:(lia) ltac:(lia) VC) as HS.
  assert (HEI : img_env VAL A_LIM (tt_E regs1 C)) by (unfold tt_E; apply Eimg_env).
  assert (HA0 : env_agree 32 (Ereg regs1 [Z_to_bv 64 C]) (tt_E regs1 C))
    by (split; [intros n Hn; unfold tt_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
  assert (E8 : ew (tt_E regs1 C) 8 = Z_to_bv 64 (p + Z.of_nat i)) by (unfold tt_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 8 8%bv eq_refl); exact H8).
  assert (E9 : ew (tt_E regs1 C) 9 = Z_to_bv 64 (p + Z.of_nat i)) by (unfold tt_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 9 9%bv eq_refl); exact H9).
  assert (E18 : ew (tt_E regs1 C) 18 = Z_to_bv 64 SB) by (unfold tt_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 18 18%bv eq_refl); exact R18).
  assert (E32 : ew (tt_E regs1 C) 32 = Z_to_bv 64 C) by (unfold tt_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
  revert HS HEI HA0 E8 E9 E18 E32. generalize (tt_E regs1 C) as E0. intros E0 HS HEI HA0 E8 E9 E18 E32.
  pose proof (env_agree_refl 33 E0) as HAE.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W memc a = rdW W memc a) by (intros; reflexivity).
  assert (KP : forall a, apresent (w_H W) memc a -> apresent (w_H W) memc a) by (intros; assumption).
  assert (SHOK : sh_ok SEGS tr_Bx [] E0 (mrestrict (w_H W) memc)) by constructor.
  assert (HRA : range_addressable (rdW W memc) SHADOW_OFF p (Z.of_nat (length s) + 1)).
  { apply (range_addressable_kept_win (rdW W mem) (rdW W memc) (spZ regs - STK_trim) (spZ regs)); [exact KEEP | lia | lia | lia |].
    destruct HADDR as (_ & _ & _ & HRA & _). exact HRA. }
  (* the exit to AFTER: s0 = s1 = p + lead, i = lead *)
  assert (EXIT : forall regs1' memc' mdc', i = lead -> tr_mid B ly S W regs mem md p s memc' mdc' ->
    (forall r, In r TLX_KEPT -> getr regs1' r = getr regs1 r) ->
    SRr SEGS W (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + TR_AFTER)) memc' (seg_rom SEGS)) mdc') (tr_post B regs ly S W mem md p s)).
  { intros regs1' memc' mdc' Hil HM' HK'.
    exact (HAFTER ly S W regs mem md ch p s regs1' memc' mdc' HCX HM'
      (tr_regs_kept regs regs1 regs1' HRG (fun r Hr => HK' r (tlx_kept_incl r Hr)))
      ltac:(rewrite (HK' 8%bv) by (cbn; tauto); rewrite H8, Hil; reflexivity)
      ltac:(rewrite (HK' 9%bv) by (cbn; tauto); rewrite H9, Hil; reflexivity)). }
  unfold tr_at.
  (* 0x890e0 .. 0x890f4: check 1, the byte, `bltu a0,a2` (c > 32 leaves) *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { cbn [ms_mem]. unfold tr_Bx. rewrite (U_atom _ 18 SB E18), (U_atom _ 9 _ E9) by (unfold SB; lia). rewrite SB_SHADOW_OFF.
    exact (range_addressable_sub _ _ p (Z.of_nat (length s) + 1) (p + Z.of_nat i) 1 HRA ltac:(lia) ltac:(lia)). }
  { tl_awr. }
  tl_after E0 HAE KM KP.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  - (* c > 32: not blank, i = lead, AFTER *)
    pose proof (tr_br_ltu_lit _ 32 _ 32 _ (tr_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) ltac:(lia) Hc) as Cgt.
    apply Z.ltb_lt in Cgt. clear Hc.
    assert (Hil : i = lead).
    { destruct (Nat.lt_ge_cases i lead) as [Hlt|Hge]; [|lia].
      pose proof (TrimA.blank_le32 C (HLB i NZ Hlt)) as Hle. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan TR_AFTER. { tl_awr. }
    tl_after E0 HAE KM KP.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ TLX_KEPT HS (tr_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    apply (EXIT rg mm mdn Hil) end.
    + exact (tr_mid_step B ly S W regs mem md p s memc mdc _ _ HMID ltac:(lia) HJ (fun a Ha _ => KM a Ha) (fun a _ Ha _ => KP a Ha)).
    + exact HK.
  - (* c <= 32: bit c of the mask *)
    pose proof (tr_br_ltu_lit _ 32 _ 32 _ (tr_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) ltac:(lia) Hc) as Cle.
    apply Z.ltb_ge in Cle. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan TR_LEAD. { tl_awr. }
    tl_after E0 HAE KM KP.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    + (* the bit is 0: not blank, i = lead, AFTER *)
      pose proof (tr_br_mask _ 32 C _ (tr_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) Hc) as BC.
      apply Bool.negb_true_iff in BC. clear Hc.
      assert (Hil : i = lead).
      { destruct (Nat.lt_ge_cases i lead) as [Hlt|Hge]; [|lia].
        assert (Hb : SegModel.blank C = true) by exact (HLB i NZ Hlt). congruence. }
      paj_run_to_tok RUNTO HS HJ SHOK Bspan TR_AFTER. { tl_awr. }
      tl_after E0 HAE KM KP.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ TLX_KEPT HS (tr_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
      apply (EXIT rg mm mdn Hil) end.
      * exact (tr_mid_step B ly S W regs mem md p s memc mdc _ _ HMID ltac:(lia) HJ (fun a Ha _ => KM a Ha) (fun a _ Ha _ => KP a Ha)).
      * exact HK.
    + (* blank: i < lead, s0 and s1 step, back to the head *)
      pose proof (tr_br_mask _ 32 C _ (tr_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) Hc) as BC.
      apply Bool.negb_false_iff in BC. clear Hc.
      assert (Hlt : (i < lead)%nat).
      { destruct (Nat.lt_ge_cases i lead) as [Hlt|Hge]; [exact Hlt|].
        assert (i = lead) as Hil by lia.
        assert (Hb : SegModel.blank (nth lead s 0) = true) by (rewrite <- Hil; exact BC). congruence. }
      paj_run_to_tok RUNTO HS HJ SHOK Bspan TR_LEAD. { tl_awr. }
      tl_after E0 HAE KM KP.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ TLL_KEPT HS (tr_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      prreg HS (8%bv : bv 5) N8. prreg HS (9%bv : bv 5) N9. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
      rewrite E8 in N8. rewrite E9 in N9.
      rewrite unsigned_lit_small in N8 by lia. rewrite unsigned_lit_small in N9 by lia.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
      apply (NEXT Hlt rg mm mdn) end.
      * exact (tr_mid_step B ly S W regs mem md p s memc mdc _ _ HMID ltac:(lia) HJ (fun a Ha _ => KM a Ha) (fun a _ Ha _ => KP a Ha)).
      * exact (tr_regs_kept regs regs1 _ HRG HK).
      * rewrite N8. unfold w64. first [reflexivity | f_equal; lia].
      * rewrite N9. unfold w64. first [reflexivity | f_equal; lia].
      * exact N10.
      * exact N11. }
(* by induction on the leading blanks left *)
intros HMID HRG Hi H8 H9 H10 H11.
remember (lead - i)%nat as k eqn:Hk.
revert i regs1 memc mdc Hk HMID HRG Hi H8 H9 H10 H11.
induction k as [|k IH]; intros i regs1 memc mdc Hk HMID HRG Hi H8 H9 H10 H11;
  apply (ITER i regs1 memc mdc Hi HMID HRG H8 H9 H10 H11); intros Hlt regs1' memc' mdc' HM' HR' N8 N9 N10 N11.
- lia.
- apply (IH (Datatypes.S i) regs1' memc' mdc' ltac:(lia) HM' HR' ltac:(lia) N8 N9 N10 N11).
Qed.

(* ---- the entry ---- *)
Lemma te_entry : forall ly S W regs mem md ch, afn_pre SEGS B STK_trim ly S W regs mem md ch ->
st_ok_pi SEGS VAL (te_E regs) te_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_trim)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_trim = 4128) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
set (E := te_E regs).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; unfold te_E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; unfold te_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold te_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold te_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (pa_val_range (A_OBJ 0)) as Hv0. pose proof (pa_val_range (A_OBJ 12)) as Hv12.
pose proof (pal_got_cell B TL) as Hgc. unfold kImgEnd in Hob0, Hob12.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
  by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
rewrite restrict_mkst_fx. unfold te_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold te_regions, stack_region, got_regionP, bcell_regionP.
  constructor; [|constructor; [|constructor; [|constructor]]]; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite HSTK. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0 Hv0). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12 Hv12). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SB; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents.
  unfold te_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0 Hv0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12 Hv12).
  cbn [base_val]. rewrite E2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; exact I].
  cbn [te_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E32, unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r. rewrite Hal16. unfold SB. repeat split; lia.
Qed.

(* the slot a run wrote: an 8-byte chunk of the frame region *)
Lemma te_slot : forall E ss ms (H : word -> bool) n lo hi wlo whi cs od e b v,
st_ok_pi SEGS VAL E ss (restrict H ms) ->
nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
rdword (aview SEGS H (ms_mem ms)) (b + od) = Some v.
Proof.
intros E ss ms H n lo hi wlo whi cs od e b v HS Hn Hb Hin He Hv.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) 0 _ HS Hn) as Hr.
pose proof (field_of_region E _ n b cs lo hi wlo whi od 8%N e v Hr Hb Hin He ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as V.
cbn [ms_mem restrict] in V. exact (rdword_of_val_mem SEGS H (ms_mem ms) (b + od) v V Hv).
Qed.

(* the walk from trim's entry: the prologue up to the leading loop's head, then LEAD at i = 0 *)
Lemma tr_entry_ok : TR_LEAD_stmt B -> forall ly S W regs mem md ch p s,
tr_cx B ly S W regs mem md ch p s ->
SRr SEGS W (cfg_at SEGS (BASE + AF_trim) regs mem md) (tr_post B regs ly S W mem md p s).
Proof.
intros HLEAD ly S W regs mem md ch p s HCX.
pose proof (tr_cx_facts B LAWS ly S W regs mem md ch p s HCX)
  as (HSTR & HADDR & HZONE & HPR & HSB & Hp4096 & Hp47 & Hn32 & HOUT & Hal16 & Hsp0 & Hsp47).
pose proof HCX as (HPRE & HROD & H10 & Hp64 & _ & HEV).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_trim = 4128) by reflexivity.
pose proof (te_entry ly S W regs mem md ch HPRE) as HS.
pose proof (ajournal_init SEGS B STK_trim (tr_FP p s) ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (te_E regs)) by (unfold te_E; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) (te_E regs))
  by (split; [intros n Hn; unfold te_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (te_E regs) n = getr regs r)
  by (intros n r Hn; unfold te_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (te_E regs) 32 = Z_to_bv 64 SB) by (unfold te_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
revert HS HEI HA0 EE E32. generalize (te_E regs) as E. intros E HS HEI HA0 EE E32.
assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) mem)) by constructor.
unfold cfg_at. change (w64 (BASE + AF_trim)) with (Z_to_bv 64 (BASE + AF_trim)).
(* 0x890a8 .. 0x890dc: the frame, the four slots, s1 = s0 = p, s2 = SB, a0 = 0x20, a1 = the mask *)
paj_run_to_tok (paj_run_to B LAWS) HS HJ SHOK Bspan TR_LEAD.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; rewrite HSTK; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
(* the run wrote only the frame *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms) (fun a' => spZ regs - 32 <= a' < spZ regs) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U2 in Hrr; lia |]).
  destruct Hin. }
assert (KP : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
(* the four slots *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
  let r := eval vm_compute in (nth_error (ss_mem ssx) 0) in
  assert (HR0 : nth_error (ss_mem ssx) 0 = r) by (vm_compute; reflexivity) end.
lazymatch type of HR0 with _ = Some (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
  assert (K8 : rdword (rdW W (ms_mem ms)) (spZ regs - 8) = Some (bv_unsigned (getr regs 1)));
  [ replace (spZ regs - 8) with (spZ regs + -8) by lia;
    lazymatch cs with context [YP09.mkChunk (-8) (CVal 8 ?ev)] =>
      apply (te_slot _ _ _ _ n lo hi wlo whi cs (-8) ev _ _ HS HR0 U2);
      [ cbn [In]; repeat (first [left; reflexivity | right])
      | cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | apply bv_unsigned_in_range ] end | ];
  assert (K16 : rdword (rdW W (ms_mem ms)) (spZ regs - 16) = Some (bv_unsigned (getr regs 8)));
  [ replace (spZ regs - 16) with (spZ regs + -16) by lia;
    lazymatch cs with context [YP09.mkChunk (-16) (CVal 8 ?ev)] =>
      apply (te_slot _ _ _ _ n lo hi wlo whi cs (-16) ev _ _ HS HR0 U2);
      [ cbn [In]; repeat (first [left; reflexivity | right])
      | cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | apply bv_unsigned_in_range ] end | ];
  assert (K24 : rdword (rdW W (ms_mem ms)) (spZ regs - 24) = Some (bv_unsigned (getr regs 9)));
  [ replace (spZ regs - 24) with (spZ regs + -24) by lia;
    lazymatch cs with context [YP09.mkChunk (-24) (CVal 8 ?ev)] =>
      apply (te_slot _ _ _ _ n lo hi wlo whi cs (-24) ev _ _ HS HR0 U2);
      [ cbn [In]; repeat (first [left; reflexivity | right])
      | cbn [sv_denot]; rewrite (EE 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | apply bv_unsigned_in_range ] end | ];
  assert (K32 : rdword (rdW W (ms_mem ms)) (spZ regs - 32) = Some (bv_unsigned (getr regs 18)));
  [ replace (spZ regs - 32) with (spZ regs + -32) by lia;
    lazymatch cs with context [YP09.mkChunk (-32) (CVal 8 ?ev)] =>
      apply (te_slot _ _ _ _ n lo hi wlo whi cs (-32) ev _ _ HS HR0 U2);
      [ cbn [In]; repeat (first [left; reflexivity | right])
      | cbn [sv_denot]; rewrite (EE 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | apply bv_unsigned_in_range ] end | ]
end.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ TR_KEPT HS HA0 ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (2%bv : bv 5) N2. prreg HS (8%bv : bv 5) N8. prreg HS (9%bv : bv 5) N9. prreg HS (10%bv : bv 5) N10.
prreg HS (11%bv : bv 5) N11. prreg HS (18%bv : bv 5) N18.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
apply (HLEAD ly S W regs mem md ch p s rg mm mdn 0%nat HCX) end.
- split; [exact HJ|]. split.
  { intros a Ha Hn. apply KM; [exact Ha | rewrite HSTK in Hn; lia]. }
  split; [intros a _ Ha _; exact (KP a Ha)|].
  split; [exact K8|]. split; [exact K16|]. split; [exact K24 | exact K32].
- split; [rewrite N2, (EE 2%nat 2%bv eq_refl); unfold w64, spZ; f_equal; lia|].
  split; [rewrite N18, E32; reflexivity | exact HK].
- lia.
- rewrite N8, (EE 10%nat 10%bv eq_refl), H10. unfold w64. f_equal. lia.
- rewrite N9, (EE 10%nat 10%bv eq_refl), H10. unfold w64. f_equal. lia.
- first [exact N10 | rewrite N10; vm_compute; reflexivity].
- first [exact N11 | rewrite N11; vm_compute; reflexivity].
Qed.

End e.
End f.
End d.
