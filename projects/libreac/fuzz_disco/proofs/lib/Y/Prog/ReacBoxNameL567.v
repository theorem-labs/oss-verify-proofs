(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_L6.v, with its module paths changed; 2341 of its 2431 lines of code are new or changed and 2880 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v YI0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f YC1h YC88 YK0w YC85.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh ReacBoxNameLoops.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
(* Proof speed (common.md Proof speed (2)). Ltac profile of rl_step: 72% of the file's time is Zify's
   euclidean-division cleanup (the flag above), which every lia call runs over every / and mod in the context, and lia
   case-splits every disjunction it can see. So rl_step's case bodies hide the disjunctions (rs_hold) and the mod facts
   (rs_holdm), and rs_lia tries, in order: lia with the / and mod hypotheses cleared; lia; one disjunction shown with
   the / and mod hypotheses cleared; one disjunction shown; every disjunction shown; everything shown. *)
Local Definition rs_hold (A : Prop) : Prop := A.
Local Definition rs_holdm (A : Prop) : Prop := A.
Local Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Local Lemma rs_hidem : forall A : Prop, A -> rs_holdm A. Proof. intros A H. exact H. Qed.
Local Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hidem in H end.
Local Ltac rs_clear_dm := repeat match goal with
  | H : context [Z.div _ _] |- _ => clear H
  | H : context [Z.modulo _ _] |- _ => clear H end.
Local Ltac rs_show1 := match goal with H : rs_hold _ |- _ => unfold rs_hold in H; lia end.
Local Ltac rs_lia := first [ rs_clear_dm; lia
  | lia
  | rs_clear_dm; rs_show1
  | rs_show1
  | unfold rs_hold in *; lia
  | unfold rs_hold, rs_holdm in *; lia ].
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TSB : tsb_ch_spec B.
Section w. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Definition RLBx : sv := SOff 22 0.
Definition RLSPAN : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition RLSH : list shent := [].
Definition rl_regs (j N : Z) : list sv := sr_set (sr_set sr_atoms 20%bv (SLit j)) 24%bv (SLit N).
Definition rl_mem (j c : Z) : smem :=
  [ YP09.mkRegion (Some 21%nat) j (j + 1) j j [YP09.mkChunk j (CVal 1 (SLit c))];
    YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition rl_facts : facts :=
  mkFacts [ (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (21%nat, mkAF IMG_LO IMG_TOP 3); (32%nat, mkAF 0 7 0) ]
    []
    [ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) (SOff 22 0), SOff 33 0) ].
Definition rl_ss (pc j N c : Z) : sstate := mkSS pc (rl_regs j N) (rl_mem j c) None rl_facts.
Definition RLE (regsE : bvmap 5 word) (sv sa : Z) : env := Eimg (Ereg regsE (map (Z_to_bv 64) [sv; sa])).
Lemma rl_no_wrange : forall E j c a, ~ in_wrange E (rl_mem j c) a.
Proof.
intros E j c a (r & Hin & Hw). unfold rl_mem in Hin. cbn [In] in Hin.
destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; lia.
Qed.
Lemma rl_frame_eq : forall E (rs : smem) (m m' : word -> option byte),
  frame_of E rs m m' -> (forall a, ~ in_wrange E rs a) -> forall x : word, m' x = m x.
Proof. intros E rs m m' HF Hno x. apply HF. apply Hno. Qed.
Definition RLCL : list Z := rbn_cl5.
Definition RLKEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 25; 26; 27]%bv.
Lemma rl_keep_of : forall (r1 r2 : bvmap 5 word) (Nv : Z),
  (forall r : bv 5, In r RLKEPT -> getr r2 r = getr r1 r) ->
  getr r2 24 = w64 Nv -> getr r1 24 = w64 Nv -> rbn_keep_regs r1 r2 RLCL.
Proof.
intros r1 r2 Nv H H24a H24b z Hz Hnin.
assert (Hu : bv_unsigned (Z_to_bv 5 z : bv 5) = z)
  by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; lia).
assert (Hnc : ~ In z RLCL) by exact Hnin. unfold RLCL, rbn_cl5, rbn_clc in Hnc. cbn [app In] in Hnc.
destruct (Z.eq_dec z 0) as [->|Hz0].
- replace (Z_to_bv 5 0 : bv 5) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite !getr_zero. reflexivity.
- destruct (Z.eq_dec z 24) as [->|Hz24].
  + replace (Z_to_bv 5 24 : bv 5) with (24%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    rewrite H24a, H24b. reflexivity.
  + apply H. apply In_bv_eq. rewrite Hu.
    assert (Hm : map bv_unsigned RLKEPT = [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 25; 26; 27])
      by (vm_compute; reflexivity).
    rewrite Hm. cbn [In]. lia.
Qed.
Lemma rl_entry : forall (W : world SEGS) (regsE : bvmap 5 word) memE (pc j N c lit svv : Z),
  regions_wf (rl_mem j c) = true ->
  getr regsE 20 = w64 j -> getr regsE 24 = w64 N ->
  getr regsE 21 = w64 lit -> getr regsE 22 = w64 SHADOW_OFF ->
  0 <= j < 8 -> 0 <= c < 256 -> 0 <= N < 2 ^ 64 ->
  IMG_LO <= lit -> lit + 8 <= IMG_TOP -> lit mod 8 = 0 ->
  val_mem SEGS (mrestrict (w_H W) memE) (lit + j) 1 c ->
  aview SEGS (w_H W) memE (SHADOW_OFF + lit / 8) = Some svv -> 0 <= svv <= 7 ->
  st_ok_pi SEGS VAL (RLE regsE svv (SHADOW_OFF + lit / 8)) (rl_ss pc j N c)
    (restrict (w_H W) (mkst (fx := fx) regsE (Z_to_bv 64 (BASE + pc)) memE (seg_rom SEGS))).
Proof.
intros W regsE memE pc j N c lit svv Hwf G20 G24 G21 G22 Hj Hc HN Hlo Hhi Hal Vc Hsv Hsvr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; unfold IMG_LO in *; lia | apply Z.div_le_upper_bound; unfold IMG_LO in *; lia]).
unfold IMG_LO, IMG_TOP in Hlo, Hhi.
assert (Hsa : 2147450880 <= SHADOW_OFF + lit / 8 <= 2147450880 + 786432) by (unfold SHADOW_OFF; lia).
rewrite restrict_mkst_fx.
set (E := RLE regsE svv (SHADOW_OFF + lit / 8)).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8])) m)
  by (intros m Hm; subst E; unfold RLE; apply Eimg_low; exact Hm).
assert (E20 : ew E 20 = Z_to_bv 64 j)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsE _ 20 20%bv eq_refl); exact G20).
assert (E21 : ew E 21 = Z_to_bv 64 lit)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsE _ 21 21%bv eq_refl); exact G21).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsE _ 22 22%bv eq_refl); exact G22).
assert (E24 : ew E 24 = Z_to_bv 64 N)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsE _ 24 24%bv eq_refl); exact G24).
assert (E32 : ew E 32 = Z_to_bv 64 svv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (SHADOW_OFF + lit / 8))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
unfold rl_ss, rl_mem, rl_facts. apply pa_entry_st_ok_full.
- unfold rl_regs.
  apply regs_ok_pin; [| intros X; discriminate X | rewrite G24; cbn [sv_denot]; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite G20; cbn [sv_denot]; reflexivity].
  subst E. unfold RLE. apply regs_ok_Eimg_Ereg.
- exact Hwf.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 21%nat lit E21) by (unfold SHADOW_OFF in *; lia).
    split; [lia|]. split; [unfold SHADOW_OFF in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ lit j 1 (SLit c) c);
    [rewrite denot_lit_U, U_lit by lia; reflexivity | zside | zside |].
    change (N.to_nat 1) with 1%nat. exact Vc.
  + rewrite (VB 33%nat (SHADOW_OFF + lit / 8) E33) by (unfold SHADOW_OFF in *; lia).
    split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (SHADOW_OFF + lit / 8) 0 1 (SOff 32 0) svv);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r.
    exact (proj1 (val_mem1_of_aview SEGS (w_H W) memE (SHADOW_OFF + lit / 8) svv Hsv)).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 21%nat lit E21) by (unfold SHADOW_OFF in *; lia).
  rewrite (VB 33%nat (SHADOW_OFF + lit / 8) E33) by (unfold SHADOW_OFF in *; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SHADOW_OFF in *. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E21, E22, E32, !unsigned_lit_small by (unfold SHADOW_OFF, IMG_LO, IMG_TOP in *; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold IMG_LO, IMG_TOP. repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply (shadow_decl_ok E 21 22 33 lit SHADOW_OFF E21 ltac:(unfold SHADOW_OFF in *; lia) E22).
    exact E33.
Qed.
Definition rl_head_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memE : word -> option byte) (k : Z)
  (regsE : bvmap 5 word) (Rrec c retoff j N : Z) : world SEGS -> config -> Prop :=
  fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model),
    c1 = cfg_at (fx := fx) SEGS (BASE + AF_both3_sb_ch) regs1 mem1 md1 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k /\
    (forall x : word, mem1 x = memE x) /\
    getr regs1 1 = w64 (BASE + retoff) /\
    getr regs1 10 = w64 Rrec /\ getr regs1 11 = w64 c /\
    getr regs1 20 = w64 j /\ getr regs1 24 = w64 N /\
    rbn_keep_regs regsE regs1 RLCL.
Definition rl_head_stmt (Loff j c retoff : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) (memE : word -> option byte) mdE k
    (regsE : bvmap 5 word) (N lit Abase svv : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k ->
  getr regsE 20 = w64 j -> getr regsE 24 = w64 N -> getr regsE 21 = w64 lit ->
  getr regsE 22 = w64 SHADOW_OFF -> getr regsE 9 = w64 Abase ->
  0 <= N < 2 ^ 64 -> 0 <= Abase -> Abase + 88 < 2 ^ 64 ->
  IMG_LO <= lit -> lit + 8 <= IMG_TOP -> lit mod 8 = 0 ->
  val_mem SEGS (mrestrict (w_H W) memE) (lit + j) 1 c ->
  aview SEGS (w_H W) memE (SHADOW_OFF + lit / 8) = Some svv -> 0 <= svv <= 7 ->
  (svv = 0 \/ j < svv) ->
  SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + Loff) regsE memE mdE)
    (rl_head_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE k regsE (Abase + 88) c retoff j N).
Ltac rl_awr := repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac rl_keepmem HFx K :=
  lazymatch type of HFx with frame_of _ _ ?m0 ?m1 =>
    assert (K : forall x : word, m1 x = m0 x) by
      (intros x; apply HFx; intros (rr & Hin & Hw);
       lazymatch type of Hin with In _ ?lst => let l' := eval vm_compute in lst in change (In rr l') in Hin end;
       cbn [In] in Hin; repeat (destruct Hin as [<- | Hin]); try destruct Hin;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia) end.
Lemma rl5_head0 : rl_head_stmt (AF_both3_reac_box_name + RBN_L5) 0 32 (AF_both3_reac_box_name + RBN_L5 + 32).
Proof.
unfold rl_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE N lit Abase svv
  HJ G20 G24 G21 G22 G9 HN Ha0 Ha1 Hlo Hhi Hal Vc Hsv Hsvr Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rl_entry W regsE memE (AF_both3_reac_box_name + RBN_L5) 0 N 32 lit svv
  ltac:(vm_compute; reflexivity) G20 G24 G21 G22 ltac:(lia) ltac:(lia) HN Hlo Hhi Hal Vc Hsv Hsvr) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLE regsE svv (SHADOW_OFF + lit / 8)) (mrestrict (w_H W) memE))
  by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (unfold RLE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]))
                (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (split; [intros m Hm; unfold RLE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 32 = Z_to_bv 64 svv)
  by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L5)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L5))) by reflexivity.
paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |].
rl_keepmem HF K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RLSPAN;
[ lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (G32 : ew Ec 32 = Z_to_bv 64 svv) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact E32);
    rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
    rewrite (U_atom Ec 32 svv G32) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia end;
  assert (Hjs : 0 < svv) by (destruct Hsvc as [Hz | Hlt]; [exfalso; apply Hc; exact Hz | exact Hlt]);
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    pose proof (st_ok_pi_add_fact Ec _ _ 32%nat (mkAF 1 7 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS2 end;
  clear HS; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG
| paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG ].
all: pmkst HS; rewrite pa_sigma_sb_ch;
  assert (E9x : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 9 = Z_to_bv 64 Abase)
    by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regsE _ 9 9%bv eq_refl); exact G9);
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (20%bv : bv 5) Q20; prreg HS (24%bv : bv 5) Q24;
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]) RLKEPT HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr;
  cbn [ms_regs restrict] in HKr;
  apply SRr_ret; unfold rl_head_post; split; [reflexivity|];
  do 3 eexists; split; [reflexivity|];
  split; [exact HJ|];
  split; [intros xx; rewrite K2; apply K1|];
  split; [rewrite Q1; reflexivity|];
  split; [rewrite Q10, E9x, unsigned_lit_small by lia; reflexivity|];
  split; [rewrite Q11; reflexivity|];
  split; [rewrite Q20; reflexivity|];
  split; [rewrite Q24; reflexivity|];
  eapply rl_keep_of; [exact HKr | exact Q24 | exact G24].
Qed.
Lemma rl5_head1 : rl_head_stmt (AF_both3_reac_box_name + RBN_L5) 1 40 (AF_both3_reac_box_name + RBN_L5 + 32).
Proof.
unfold rl_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE N lit Abase svv
  HJ G20 G24 G21 G22 G9 HN Ha0 Ha1 Hlo Hhi Hal Vc Hsv Hsvr Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rl_entry W regsE memE (AF_both3_reac_box_name + RBN_L5) 1 N 40 lit svv
  ltac:(vm_compute; reflexivity) G20 G24 G21 G22 ltac:(lia) ltac:(lia) HN Hlo Hhi Hal Vc Hsv Hsvr) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLE regsE svv (SHADOW_OFF + lit / 8)) (mrestrict (w_H W) memE))
  by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (unfold RLE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]))
                (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (split; [intros m Hm; unfold RLE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 32 = Z_to_bv 64 svv)
  by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L5)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L5))) by reflexivity.
paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |].
rl_keepmem HF K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RLSPAN;
[ lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (G32 : ew Ec 32 = Z_to_bv 64 svv) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact E32);
    rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
    rewrite (U_atom Ec 32 svv G32) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia end;
  assert (Hjs : 1 < svv) by (destruct Hsvc as [Hz | Hlt]; [exfalso; apply Hc; exact Hz | exact Hlt]);
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    pose proof (st_ok_pi_add_fact Ec _ _ 32%nat (mkAF 2 7 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS2 end;
  clear HS; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG
| paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG ].
all: pmkst HS; rewrite pa_sigma_sb_ch;
  assert (E9x : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 9 = Z_to_bv 64 Abase)
    by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regsE _ 9 9%bv eq_refl); exact G9);
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (20%bv : bv 5) Q20; prreg HS (24%bv : bv 5) Q24;
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]) RLKEPT HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr;
  cbn [ms_regs restrict] in HKr;
  apply SRr_ret; unfold rl_head_post; split; [reflexivity|];
  do 3 eexists; split; [reflexivity|];
  split; [exact HJ|];
  split; [intros xx; rewrite K2; apply K1|];
  split; [rewrite Q1; reflexivity|];
  split; [rewrite Q10, E9x, unsigned_lit_small by lia; reflexivity|];
  split; [rewrite Q11; reflexivity|];
  split; [rewrite Q20; reflexivity|];
  split; [rewrite Q24; reflexivity|];
  eapply rl_keep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl6_head0 : rl_head_stmt (AF_both3_reac_box_name + RBN_L6) 0 32 (AF_both3_reac_box_name + RBN_L6 + 32).
Proof.
unfold rl_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE N lit Abase svv
  HJ G20 G24 G21 G22 G9 HN Ha0 Ha1 Hlo Hhi Hal Vc Hsv Hsvr Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rl_entry W regsE memE (AF_both3_reac_box_name + RBN_L6) 0 N 32 lit svv
  ltac:(vm_compute; reflexivity) G20 G24 G21 G22 ltac:(lia) ltac:(lia) HN Hlo Hhi Hal Vc Hsv Hsvr) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLE regsE svv (SHADOW_OFF + lit / 8)) (mrestrict (w_H W) memE))
  by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (unfold RLE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]))
                (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (split; [intros m Hm; unfold RLE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 32 = Z_to_bv 64 svv)
  by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L6)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L6))) by reflexivity.
paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |].
rl_keepmem HF K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RLSPAN;
[ lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (G32 : ew Ec 32 = Z_to_bv 64 svv) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact E32);
    rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
    rewrite (U_atom Ec 32 svv G32) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia end;
  assert (Hjs : 0 < svv) by (destruct Hsvc as [Hz | Hlt]; [exfalso; apply Hc; exact Hz | exact Hlt]);
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    pose proof (st_ok_pi_add_fact Ec _ _ 32%nat (mkAF 1 7 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS2 end;
  clear HS; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG
| paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG ].
all: pmkst HS; rewrite pa_sigma_sb_ch;
  assert (E9x : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 9 = Z_to_bv 64 Abase)
    by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regsE _ 9 9%bv eq_refl); exact G9);
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (20%bv : bv 5) Q20; prreg HS (24%bv : bv 5) Q24;
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]) RLKEPT HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr;
  cbn [ms_regs restrict] in HKr;
  apply SRr_ret; unfold rl_head_post; split; [reflexivity|];
  do 3 eexists; split; [reflexivity|];
  split; [exact HJ|];
  split; [intros xx; rewrite K2; apply K1|];
  split; [rewrite Q1; reflexivity|];
  split; [rewrite Q10, E9x, unsigned_lit_small by lia; reflexivity|];
  split; [rewrite Q11; reflexivity|];
  split; [rewrite Q20; reflexivity|];
  split; [rewrite Q24; reflexivity|];
  eapply rl_keep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl6_head1 : rl_head_stmt (AF_both3_reac_box_name + RBN_L6) 1 105 (AF_both3_reac_box_name + RBN_L6 + 32).
Proof.
unfold rl_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE N lit Abase svv
  HJ G20 G24 G21 G22 G9 HN Ha0 Ha1 Hlo Hhi Hal Vc Hsv Hsvr Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rl_entry W regsE memE (AF_both3_reac_box_name + RBN_L6) 1 N 105 lit svv
  ltac:(vm_compute; reflexivity) G20 G24 G21 G22 ltac:(lia) ltac:(lia) HN Hlo Hhi Hal Vc Hsv Hsvr) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLE regsE svv (SHADOW_OFF + lit / 8)) (mrestrict (w_H W) memE))
  by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (unfold RLE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]))
                (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (split; [intros m Hm; unfold RLE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 32 = Z_to_bv 64 svv)
  by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L6)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L6))) by reflexivity.
paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |].
rl_keepmem HF K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RLSPAN;
[ lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (G32 : ew Ec 32 = Z_to_bv 64 svv) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact E32);
    rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
    rewrite (U_atom Ec 32 svv G32) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia end;
  assert (Hjs : 1 < svv) by (destruct Hsvc as [Hz | Hlt]; [exfalso; apply Hc; exact Hz | exact Hlt]);
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    pose proof (st_ok_pi_add_fact Ec _ _ 32%nat (mkAF 2 7 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS2 end;
  clear HS; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG
| paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG ].
all: pmkst HS; rewrite pa_sigma_sb_ch;
  assert (E9x : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 9 = Z_to_bv 64 Abase)
    by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regsE _ 9 9%bv eq_refl); exact G9);
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (20%bv : bv 5) Q20; prreg HS (24%bv : bv 5) Q24;
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]) RLKEPT HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr;
  cbn [ms_regs restrict] in HKr;
  apply SRr_ret; unfold rl_head_post; split; [reflexivity|];
  do 3 eexists; split; [reflexivity|];
  split; [exact HJ|];
  split; [intros xx; rewrite K2; apply K1|];
  split; [rewrite Q1; reflexivity|];
  split; [rewrite Q10, E9x, unsigned_lit_small by lia; reflexivity|];
  split; [rewrite Q11; reflexivity|];
  split; [rewrite Q20; reflexivity|];
  split; [rewrite Q24; reflexivity|];
  eapply rl_keep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl6_head2 : rl_head_stmt (AF_both3_reac_box_name + RBN_L6) 2 110 (AF_both3_reac_box_name + RBN_L6 + 32).
Proof.
unfold rl_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE N lit Abase svv
  HJ G20 G24 G21 G22 G9 HN Ha0 Ha1 Hlo Hhi Hal Vc Hsv Hsvr Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rl_entry W regsE memE (AF_both3_reac_box_name + RBN_L6) 2 N 110 lit svv
  ltac:(vm_compute; reflexivity) G20 G24 G21 G22 ltac:(lia) ltac:(lia) HN Hlo Hhi Hal Vc Hsv Hsvr) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLE regsE svv (SHADOW_OFF + lit / 8)) (mrestrict (w_H W) memE))
  by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (unfold RLE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]))
                (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (split; [intros m Hm; unfold RLE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 32 = Z_to_bv 64 svv)
  by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L6)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L6))) by reflexivity.
paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |].
rl_keepmem HF K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RLSPAN;
[ lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (G32 : ew Ec 32 = Z_to_bv 64 svv) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact E32);
    rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
    rewrite (U_atom Ec 32 svv G32) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia end;
  assert (Hjs : 2 < svv) by (destruct Hsvc as [Hz | Hlt]; [exfalso; apply Hc; exact Hz | exact Hlt]);
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    pose proof (st_ok_pi_add_fact Ec _ _ 32%nat (mkAF 3 7 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS2 end;
  clear HS; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG
| paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG ].
all: pmkst HS; rewrite pa_sigma_sb_ch;
  assert (E9x : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 9 = Z_to_bv 64 Abase)
    by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regsE _ 9 9%bv eq_refl); exact G9);
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (20%bv : bv 5) Q20; prreg HS (24%bv : bv 5) Q24;
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]) RLKEPT HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr;
  cbn [ms_regs restrict] in HKr;
  apply SRr_ret; unfold rl_head_post; split; [reflexivity|];
  do 3 eexists; split; [reflexivity|];
  split; [exact HJ|];
  split; [intros xx; rewrite K2; apply K1|];
  split; [rewrite Q1; reflexivity|];
  split; [rewrite Q10, E9x, unsigned_lit_small by lia; reflexivity|];
  split; [rewrite Q11; reflexivity|];
  split; [rewrite Q20; reflexivity|];
  split; [rewrite Q24; reflexivity|];
  eapply rl_keep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl6_head3 : rl_head_stmt (AF_both3_reac_box_name + RBN_L6) 3 32 (AF_both3_reac_box_name + RBN_L6 + 32).
Proof.
unfold rl_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE N lit Abase svv
  HJ G20 G24 G21 G22 G9 HN Ha0 Ha1 Hlo Hhi Hal Vc Hsv Hsvr Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rl_entry W regsE memE (AF_both3_reac_box_name + RBN_L6) 3 N 32 lit svv
  ltac:(vm_compute; reflexivity) G20 G24 G21 G22 ltac:(lia) ltac:(lia) HN Hlo Hhi Hal Vc Hsv Hsvr) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLE regsE svv (SHADOW_OFF + lit / 8)) (mrestrict (w_H W) memE))
  by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (unfold RLE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]))
                (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (split; [intros m Hm; unfold RLE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 32 = Z_to_bv 64 svv)
  by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L6)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L6))) by reflexivity.
paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |].
rl_keepmem HF K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RLSPAN;
[ lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (G32 : ew Ec 32 = Z_to_bv 64 svv) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact E32);
    rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
    rewrite (U_atom Ec 32 svv G32) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia end;
  assert (Hjs : 3 < svv) by (destruct Hsvc as [Hz | Hlt]; [exfalso; apply Hc; exact Hz | exact Hlt]);
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    pose proof (st_ok_pi_add_fact Ec _ _ 32%nat (mkAF 4 7 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS2 end;
  clear HS; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG
| paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG ].
all: pmkst HS; rewrite pa_sigma_sb_ch;
  assert (E9x : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 9 = Z_to_bv 64 Abase)
    by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regsE _ 9 9%bv eq_refl); exact G9);
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (20%bv : bv 5) Q20; prreg HS (24%bv : bv 5) Q24;
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]) RLKEPT HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr;
  cbn [ms_regs restrict] in HKr;
  apply SRr_ret; unfold rl_head_post; split; [reflexivity|];
  do 3 eexists; split; [reflexivity|];
  split; [exact HJ|];
  split; [intros xx; rewrite K2; apply K1|];
  split; [rewrite Q1; reflexivity|];
  split; [rewrite Q10, E9x, unsigned_lit_small by lia; reflexivity|];
  split; [rewrite Q11; reflexivity|];
  split; [rewrite Q20; reflexivity|];
  split; [rewrite Q24; reflexivity|];
  eapply rl_keep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl6_head4 : rl_head_stmt (AF_both3_reac_box_name + RBN_L6) 4 47 (AF_both3_reac_box_name + RBN_L6 + 32).
Proof.
unfold rl_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE N lit Abase svv
  HJ G20 G24 G21 G22 G9 HN Ha0 Ha1 Hlo Hhi Hal Vc Hsv Hsvr Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rl_entry W regsE memE (AF_both3_reac_box_name + RBN_L6) 4 N 47 lit svv
  ltac:(vm_compute; reflexivity) G20 G24 G21 G22 ltac:(lia) ltac:(lia) HN Hlo Hhi Hal Vc Hsv Hsvr) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLE regsE svv (SHADOW_OFF + lit / 8)) (mrestrict (w_H W) memE))
  by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (unfold RLE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]))
                (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (split; [intros m Hm; unfold RLE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 32 = Z_to_bv 64 svv)
  by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L6)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L6))) by reflexivity.
paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |].
rl_keepmem HF K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RLSPAN;
[ lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (G32 : ew Ec 32 = Z_to_bv 64 svv) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact E32);
    rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
    rewrite (U_atom Ec 32 svv G32) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia end;
  assert (Hjs : 4 < svv) by (destruct Hsvc as [Hz | Hlt]; [exfalso; apply Hc; exact Hz | exact Hlt]);
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    pose proof (st_ok_pi_add_fact Ec _ _ 32%nat (mkAF 5 7 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS2 end;
  clear HS; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG
| paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG ].
all: pmkst HS; rewrite pa_sigma_sb_ch;
  assert (E9x : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 9 = Z_to_bv 64 Abase)
    by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regsE _ 9 9%bv eq_refl); exact G9);
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (20%bv : bv 5) Q20; prreg HS (24%bv : bv 5) Q24;
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]) RLKEPT HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr;
  cbn [ms_regs restrict] in HKr;
  apply SRr_ret; unfold rl_head_post; split; [reflexivity|];
  do 3 eexists; split; [reflexivity|];
  split; [exact HJ|];
  split; [intros xx; rewrite K2; apply K1|];
  split; [rewrite Q1; reflexivity|];
  split; [rewrite Q10, E9x, unsigned_lit_small by lia; reflexivity|];
  split; [rewrite Q11; reflexivity|];
  split; [rewrite Q20; reflexivity|];
  split; [rewrite Q24; reflexivity|];
  eapply rl_keep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl6_head5 : rl_head_stmt (AF_both3_reac_box_name + RBN_L6) 5 32 (AF_both3_reac_box_name + RBN_L6 + 32).
Proof.
unfold rl_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE N lit Abase svv
  HJ G20 G24 G21 G22 G9 HN Ha0 Ha1 Hlo Hhi Hal Vc Hsv Hsvr Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rl_entry W regsE memE (AF_both3_reac_box_name + RBN_L6) 5 N 32 lit svv
  ltac:(vm_compute; reflexivity) G20 G24 G21 G22 ltac:(lia) ltac:(lia) HN Hlo Hhi Hal Vc Hsv Hsvr) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLE regsE svv (SHADOW_OFF + lit / 8)) (mrestrict (w_H W) memE))
  by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (unfold RLE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]))
                (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (split; [intros m Hm; unfold RLE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 32 = Z_to_bv 64 svv)
  by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L6)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L6))) by reflexivity.
paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |].
rl_keepmem HF K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RLSPAN;
[ lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (G32 : ew Ec 32 = Z_to_bv 64 svv) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact E32);
    rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
    rewrite (U_atom Ec 32 svv G32) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia end;
  assert (Hjs : 5 < svv) by (destruct Hsvc as [Hz | Hlt]; [exfalso; apply Hc; exact Hz | exact Hlt]);
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    pose proof (st_ok_pi_add_fact Ec _ _ 32%nat (mkAF 6 7 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS2 end;
  clear HS; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG
| paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG ].
all: pmkst HS; rewrite pa_sigma_sb_ch;
  assert (E9x : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 9 = Z_to_bv 64 Abase)
    by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regsE _ 9 9%bv eq_refl); exact G9);
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (20%bv : bv 5) Q20; prreg HS (24%bv : bv 5) Q24;
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]) RLKEPT HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr;
  cbn [ms_regs restrict] in HKr;
  apply SRr_ret; unfold rl_head_post; split; [reflexivity|];
  do 3 eexists; split; [reflexivity|];
  split; [exact HJ|];
  split; [intros xx; rewrite K2; apply K1|];
  split; [rewrite Q1; reflexivity|];
  split; [rewrite Q10, E9x, unsigned_lit_small by lia; reflexivity|];
  split; [rewrite Q11; reflexivity|];
  split; [rewrite Q20; reflexivity|];
  split; [rewrite Q24; reflexivity|];
  eapply rl_keep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl7_head0 : rl_head_stmt (AF_both3_reac_box_name + RBN_L7) 0 32 (AF_both3_reac_box_name + RBN_L7 + 32).
Proof.
unfold rl_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE N lit Abase svv
  HJ G20 G24 G21 G22 G9 HN Ha0 Ha1 Hlo Hhi Hal Vc Hsv Hsvr Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rl_entry W regsE memE (AF_both3_reac_box_name + RBN_L7) 0 N 32 lit svv
  ltac:(vm_compute; reflexivity) G20 G24 G21 G22 ltac:(lia) ltac:(lia) HN Hlo Hhi Hal Vc Hsv Hsvr) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLE regsE svv (SHADOW_OFF + lit / 8)) (mrestrict (w_H W) memE))
  by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (unfold RLE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]))
                (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (split; [intros m Hm; unfold RLE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 32 = Z_to_bv 64 svv)
  by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L7)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L7))) by reflexivity.
paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |].
rl_keepmem HF K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RLSPAN;
[ lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (G32 : ew Ec 32 = Z_to_bv 64 svv) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact E32);
    rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
    rewrite (U_atom Ec 32 svv G32) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia end;
  assert (Hjs : 0 < svv) by (destruct Hsvc as [Hz | Hlt]; [exfalso; apply Hc; exact Hz | exact Hlt]);
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    pose proof (st_ok_pi_add_fact Ec _ _ 32%nat (mkAF 1 7 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS2 end;
  clear HS; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG
| paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG ].
all: pmkst HS; rewrite pa_sigma_sb_ch;
  assert (E9x : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 9 = Z_to_bv 64 Abase)
    by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regsE _ 9 9%bv eq_refl); exact G9);
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (20%bv : bv 5) Q20; prreg HS (24%bv : bv 5) Q24;
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]) RLKEPT HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr;
  cbn [ms_regs restrict] in HKr;
  apply SRr_ret; unfold rl_head_post; split; [reflexivity|];
  do 3 eexists; split; [reflexivity|];
  split; [exact HJ|];
  split; [intros xx; rewrite K2; apply K1|];
  split; [rewrite Q1; reflexivity|];
  split; [rewrite Q10, E9x, unsigned_lit_small by lia; reflexivity|];
  split; [rewrite Q11; reflexivity|];
  split; [rewrite Q20; reflexivity|];
  split; [rewrite Q24; reflexivity|];
  eapply rl_keep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl7_head1 : rl_head_stmt (AF_both3_reac_box_name + RBN_L7) 1 111 (AF_both3_reac_box_name + RBN_L7 + 32).
Proof.
unfold rl_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE N lit Abase svv
  HJ G20 G24 G21 G22 G9 HN Ha0 Ha1 Hlo Hhi Hal Vc Hsv Hsvr Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rl_entry W regsE memE (AF_both3_reac_box_name + RBN_L7) 1 N 111 lit svv
  ltac:(vm_compute; reflexivity) G20 G24 G21 G22 ltac:(lia) ltac:(lia) HN Hlo Hhi Hal Vc Hsv Hsvr) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLE regsE svv (SHADOW_OFF + lit / 8)) (mrestrict (w_H W) memE))
  by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (unfold RLE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]))
                (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (split; [intros m Hm; unfold RLE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 32 = Z_to_bv 64 svv)
  by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L7)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L7))) by reflexivity.
paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |].
rl_keepmem HF K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RLSPAN;
[ lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (G32 : ew Ec 32 = Z_to_bv 64 svv) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact E32);
    rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
    rewrite (U_atom Ec 32 svv G32) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia end;
  assert (Hjs : 1 < svv) by (destruct Hsvc as [Hz | Hlt]; [exfalso; apply Hc; exact Hz | exact Hlt]);
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    pose proof (st_ok_pi_add_fact Ec _ _ 32%nat (mkAF 2 7 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS2 end;
  clear HS; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG
| paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG ].
all: pmkst HS; rewrite pa_sigma_sb_ch;
  assert (E9x : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 9 = Z_to_bv 64 Abase)
    by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regsE _ 9 9%bv eq_refl); exact G9);
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (20%bv : bv 5) Q20; prreg HS (24%bv : bv 5) Q24;
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]) RLKEPT HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr;
  cbn [ms_regs restrict] in HKr;
  apply SRr_ret; unfold rl_head_post; split; [reflexivity|];
  do 3 eexists; split; [reflexivity|];
  split; [exact HJ|];
  split; [intros xx; rewrite K2; apply K1|];
  split; [rewrite Q1; reflexivity|];
  split; [rewrite Q10, E9x, unsigned_lit_small by lia; reflexivity|];
  split; [rewrite Q11; reflexivity|];
  split; [rewrite Q20; reflexivity|];
  split; [rewrite Q24; reflexivity|];
  eapply rl_keep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl7_head2 : rl_head_stmt (AF_both3_reac_box_name + RBN_L7) 2 117 (AF_both3_reac_box_name + RBN_L7 + 32).
Proof.
unfold rl_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE N lit Abase svv
  HJ G20 G24 G21 G22 G9 HN Ha0 Ha1 Hlo Hhi Hal Vc Hsv Hsvr Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rl_entry W regsE memE (AF_both3_reac_box_name + RBN_L7) 2 N 117 lit svv
  ltac:(vm_compute; reflexivity) G20 G24 G21 G22 ltac:(lia) ltac:(lia) HN Hlo Hhi Hal Vc Hsv Hsvr) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLE regsE svv (SHADOW_OFF + lit / 8)) (mrestrict (w_H W) memE))
  by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (unfold RLE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]))
                (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (split; [intros m Hm; unfold RLE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 32 = Z_to_bv 64 svv)
  by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L7)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L7))) by reflexivity.
paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |].
rl_keepmem HF K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RLSPAN;
[ lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (G32 : ew Ec 32 = Z_to_bv 64 svv) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact E32);
    rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
    rewrite (U_atom Ec 32 svv G32) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia end;
  assert (Hjs : 2 < svv) by (destruct Hsvc as [Hz | Hlt]; [exfalso; apply Hc; exact Hz | exact Hlt]);
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    pose proof (st_ok_pi_add_fact Ec _ _ 32%nat (mkAF 3 7 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS2 end;
  clear HS; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG
| paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG ].
all: pmkst HS; rewrite pa_sigma_sb_ch;
  assert (E9x : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 9 = Z_to_bv 64 Abase)
    by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regsE _ 9 9%bv eq_refl); exact G9);
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (20%bv : bv 5) Q20; prreg HS (24%bv : bv 5) Q24;
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]) RLKEPT HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr;
  cbn [ms_regs restrict] in HKr;
  apply SRr_ret; unfold rl_head_post; split; [reflexivity|];
  do 3 eexists; split; [reflexivity|];
  split; [exact HJ|];
  split; [intros xx; rewrite K2; apply K1|];
  split; [rewrite Q1; reflexivity|];
  split; [rewrite Q10, E9x, unsigned_lit_small by lia; reflexivity|];
  split; [rewrite Q11; reflexivity|];
  split; [rewrite Q20; reflexivity|];
  split; [rewrite Q24; reflexivity|];
  eapply rl_keep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl7_head3 : rl_head_stmt (AF_both3_reac_box_name + RBN_L7) 3 116 (AF_both3_reac_box_name + RBN_L7 + 32).
Proof.
unfold rl_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE N lit Abase svv
  HJ G20 G24 G21 G22 G9 HN Ha0 Ha1 Hlo Hhi Hal Vc Hsv Hsvr Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rl_entry W regsE memE (AF_both3_reac_box_name + RBN_L7) 3 N 116 lit svv
  ltac:(vm_compute; reflexivity) G20 G24 G21 G22 ltac:(lia) ltac:(lia) HN Hlo Hhi Hal Vc Hsv Hsvr) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLE regsE svv (SHADOW_OFF + lit / 8)) (mrestrict (w_H W) memE))
  by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (unfold RLE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]))
                (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (split; [intros m Hm; unfold RLE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 32 = Z_to_bv 64 svv)
  by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L7)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L7))) by reflexivity.
paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |].
rl_keepmem HF K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RLSPAN;
[ lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (G32 : ew Ec 32 = Z_to_bv 64 svv) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact E32);
    rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
    rewrite (U_atom Ec 32 svv G32) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia end;
  assert (Hjs : 3 < svv) by (destruct Hsvc as [Hz | Hlt]; [exfalso; apply Hc; exact Hz | exact Hlt]);
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    pose proof (st_ok_pi_add_fact Ec _ _ 32%nat (mkAF 4 7 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS2 end;
  clear HS; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG
| paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG ].
all: pmkst HS; rewrite pa_sigma_sb_ch;
  assert (E9x : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 9 = Z_to_bv 64 Abase)
    by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regsE _ 9 9%bv eq_refl); exact G9);
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (20%bv : bv 5) Q20; prreg HS (24%bv : bv 5) Q24;
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]) RLKEPT HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr;
  cbn [ms_regs restrict] in HKr;
  apply SRr_ret; unfold rl_head_post; split; [reflexivity|];
  do 3 eexists; split; [reflexivity|];
  split; [exact HJ|];
  split; [intros xx; rewrite K2; apply K1|];
  split; [rewrite Q1; reflexivity|];
  split; [rewrite Q10, E9x, unsigned_lit_small by lia; reflexivity|];
  split; [rewrite Q11; reflexivity|];
  split; [rewrite Q20; reflexivity|];
  split; [rewrite Q24; reflexivity|];
  eapply rl_keep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl7_head4 : rl_head_stmt (AF_both3_reac_box_name + RBN_L7) 4 41 (AF_both3_reac_box_name + RBN_L7 + 32).
Proof.
unfold rl_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE N lit Abase svv
  HJ G20 G24 G21 G22 G9 HN Ha0 Ha1 Hlo Hhi Hal Vc Hsv Hsvr Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rl_entry W regsE memE (AF_both3_reac_box_name + RBN_L7) 4 N 41 lit svv
  ltac:(vm_compute; reflexivity) G20 G24 G21 G22 ltac:(lia) ltac:(lia) HN Hlo Hhi Hal Vc Hsv Hsvr) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLE regsE svv (SHADOW_OFF + lit / 8)) (mrestrict (w_H W) memE))
  by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (unfold RLE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]))
                (RLE regsE svv (SHADOW_OFF + lit / 8)))
  by (split; [intros m Hm; unfold RLE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 32 = Z_to_bv 64 svv)
  by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L7)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L7))) by reflexivity.
paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |].
rl_keepmem HF K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RLSPAN;
[ lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (G32 : ew Ec 32 = Z_to_bv 64 svv) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact E32);
    rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
    rewrite (U_atom Ec 32 svv G32) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia end;
  assert (Hjs : 4 < svv) by (destruct Hsvc as [Hz | Hlt]; [exfalso; apply Hc; exact Hz | exact Hlt]);
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    pose proof (st_ok_pi_add_fact Ec _ _ 32%nat (mkAF 5 7 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS2 end;
  clear HS; rename HS2 into HS;
  paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG
| paj_run_tok RUN HS HJ SHOK RLSPAN; [ rl_awr |];
  rl_keepmem HF K2; clear HF HFr HG ].
all: pmkst HS; rewrite pa_sigma_sb_ch;
  assert (E9x : ew (RLE regsE svv (SHADOW_OFF + lit / 8)) 9 = Z_to_bv 64 Abase)
    by (unfold RLE; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regsE _ 9 9%bv eq_refl); exact G9);
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (20%bv : bv 5) Q20; prreg HS (24%bv : bv 5) Q24;
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsE (map (Z_to_bv 64) [svv; SHADOW_OFF + lit / 8]) RLKEPT HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr;
  cbn [ms_regs restrict] in HKr;
  apply SRr_ret; unfold rl_head_post; split; [reflexivity|];
  do 3 eexists; split; [reflexivity|];
  split; [exact HJ|];
  split; [intros xx; rewrite K2; apply K1|];
  split; [rewrite Q1; reflexivity|];
  split; [rewrite Q10, E9x, unsigned_lit_small by lia; reflexivity|];
  split; [rewrite Q11; reflexivity|];
  split; [rewrite Q20; reflexivity|];
  split; [rewrite Q24; reflexivity|];
  eapply rl_keep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Definition rl_tss (pc j N : Z) : sstate := mkSS pc (rl_regs j N) [] None (mkFacts [] [] []).
Definition RLTE (regsE : bvmap 5 word) : env := Eimg (Ereg regsE []).
Definition RLTTKEPT : list (bv 5) :=
  [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;21;22;23;25;26;27;28;29;30;31]%bv.
Lemma rl_tkeep_of : forall (r1 r2 : bvmap 5 word) (Nv : Z),
  (forall r : bv 5, In r RLTTKEPT -> getr r2 r = getr r1 r) ->
  getr r2 24 = w64 Nv -> getr r1 24 = w64 Nv -> rbn_keep_regs r1 r2 [20].
Proof.
intros r1 r2 Nv H H24a H24b z Hz Hnin. cbn [In] in Hnin.
assert (Hu : bv_unsigned (Z_to_bv 5 z : bv 5) = z)
  by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; lia).
destruct (Z.eq_dec z 0) as [->|Hz0].
- replace (Z_to_bv 5 0 : bv 5) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite !getr_zero. reflexivity.
- destruct (Z.eq_dec z 24) as [->|Hz24].
  + replace (Z_to_bv 5 24 : bv 5) with (24%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    rewrite H24a, H24b. reflexivity.
  + apply H. apply In_bv_eq. rewrite Hu.
    assert (Hm : map bv_unsigned RLTTKEPT =
      [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;21;22;23;25;26;27;28;29;30;31])
      by (vm_compute; reflexivity).
    rewrite Hm. cbn [In]. lia.
Qed.
Lemma rl_tentry : forall (W : world SEGS) (regsE : bvmap 5 word) memE (pc j N : Z),
  getr regsE 20 = w64 j -> getr regsE 24 = w64 N ->
  st_ok_pi SEGS VAL (RLTE regsE) (rl_tss pc j N)
    (restrict (w_H W) (mkst (fx := fx) regsE (Z_to_bv 64 (BASE + pc)) memE (seg_rom SEGS))).
Proof.
intros W regsE memE pc j N G20 G24. rewrite restrict_mkst_fx.
unfold rl_tss. apply pa_entry_st_ok_full.
- unfold rl_regs.
  apply regs_ok_pin; [| intros X; discriminate X | rewrite G24; cbn [sv_denot]; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite G20; cbn [sv_denot]; reflexivity].
  unfold RLTE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- cbn [f_atoms atoms_ok f_conds conds_ok f_alias alias_ok]. split; [exact I | split; [exact I | exact I]].
Qed.
Definition rl_tail_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memE : word -> option byte) (k : Z)
  (regsE : bvmap 5 word) (tgt jp1 N : Z) : world SEGS -> config -> Prop :=
  fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model),
    c1 = cfg_at (fx := fx) SEGS (BASE + tgt) regs1 mem1 md1 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k /\
    (forall x : word, mem1 x = memE x) /\
    getr regs1 20 = w64 jp1 /\ getr regs1 24 = w64 N /\
    rbn_keep_regs regsE regs1 [20].
Definition rl_tail_stmt (retpc tgt j N : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memE mdE k (regsE : bvmap 5 word),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k ->
  getr regsE 20 = w64 j -> getr regsE 24 = w64 N ->
  SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + retpc) regsE memE mdE)
    (rl_tail_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE k regsE tgt (j + 1) N).

Lemma rl5_tail0 : rl_tail_stmt (AF_both3_reac_box_name + RBN_L5 + 32) (AF_both3_reac_box_name + RBN_L5) 0 2.
Proof.
unfold rl_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE HJ G20 G24.
pose proof (rl_tentry W regsE memE (AF_both3_reac_box_name + RBN_L5 + 32) 0 2 G20 G24) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLTE regsE) (mrestrict (w_H W) memE)) by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLTE regsE)) by (unfold RLTE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE []) (RLTE regsE))
  by (split; [intros m Hm; unfold RLTE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L5 + 32)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L5 + 32))) by reflexivity.
paj_run_to_tok RUNTO HS HJ SHOK RLSPAN (AF_both3_reac_box_name + RBN_L5); [ rl_awr |].
rl_keepmem HF K. clear HF HFr HG.
pmkst HS.
prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE ([] : list word) RLTTKEPT HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
apply SRr_ret. unfold rl_tail_post. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at, w64; reflexivity|].
split; [exact HJ|].
split; [intros xx; apply K|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q24; reflexivity|].
eapply rl_tkeep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl5_tail1 : rl_tail_stmt (AF_both3_reac_box_name + RBN_L5 + 32) (AF_both3_reac_box_name + RBN_L5X) 1 2.
Proof.
unfold rl_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE HJ G20 G24.
pose proof (rl_tentry W regsE memE (AF_both3_reac_box_name + RBN_L5 + 32) 1 2 G20 G24) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLTE regsE) (mrestrict (w_H W) memE)) by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLTE regsE)) by (unfold RLTE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE []) (RLTE regsE))
  by (split; [intros m Hm; unfold RLTE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L5 + 32)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L5 + 32))) by reflexivity.
paj_run_to_tok RUNTO HS HJ SHOK RLSPAN (AF_both3_reac_box_name + RBN_L5X); [ rl_awr |].
rl_keepmem HF K. clear HF HFr HG.
pmkst HS.
prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE ([] : list word) RLTTKEPT HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
apply SRr_ret. unfold rl_tail_post. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at, w64; reflexivity|].
split; [exact HJ|].
split; [intros xx; apply K|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q24; reflexivity|].
eapply rl_tkeep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl6_tail0 : rl_tail_stmt (AF_both3_reac_box_name + RBN_L6 + 32) (AF_both3_reac_box_name + RBN_L6) 0 6.
Proof.
unfold rl_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE HJ G20 G24.
pose proof (rl_tentry W regsE memE (AF_both3_reac_box_name + RBN_L6 + 32) 0 6 G20 G24) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLTE regsE) (mrestrict (w_H W) memE)) by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLTE regsE)) by (unfold RLTE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE []) (RLTE regsE))
  by (split; [intros m Hm; unfold RLTE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L6 + 32)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L6 + 32))) by reflexivity.
paj_run_to_tok RUNTO HS HJ SHOK RLSPAN (AF_both3_reac_box_name + RBN_L6); [ rl_awr |].
rl_keepmem HF K. clear HF HFr HG.
pmkst HS.
prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE ([] : list word) RLTTKEPT HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
apply SRr_ret. unfold rl_tail_post. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at, w64; reflexivity|].
split; [exact HJ|].
split; [intros xx; apply K|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q24; reflexivity|].
eapply rl_tkeep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl6_tail1 : rl_tail_stmt (AF_both3_reac_box_name + RBN_L6 + 32) (AF_both3_reac_box_name + RBN_L6) 1 6.
Proof.
unfold rl_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE HJ G20 G24.
pose proof (rl_tentry W regsE memE (AF_both3_reac_box_name + RBN_L6 + 32) 1 6 G20 G24) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLTE regsE) (mrestrict (w_H W) memE)) by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLTE regsE)) by (unfold RLTE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE []) (RLTE regsE))
  by (split; [intros m Hm; unfold RLTE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L6 + 32)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L6 + 32))) by reflexivity.
paj_run_to_tok RUNTO HS HJ SHOK RLSPAN (AF_both3_reac_box_name + RBN_L6); [ rl_awr |].
rl_keepmem HF K. clear HF HFr HG.
pmkst HS.
prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE ([] : list word) RLTTKEPT HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
apply SRr_ret. unfold rl_tail_post. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at, w64; reflexivity|].
split; [exact HJ|].
split; [intros xx; apply K|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q24; reflexivity|].
eapply rl_tkeep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl6_tail2 : rl_tail_stmt (AF_both3_reac_box_name + RBN_L6 + 32) (AF_both3_reac_box_name + RBN_L6) 2 6.
Proof.
unfold rl_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE HJ G20 G24.
pose proof (rl_tentry W regsE memE (AF_both3_reac_box_name + RBN_L6 + 32) 2 6 G20 G24) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLTE regsE) (mrestrict (w_H W) memE)) by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLTE regsE)) by (unfold RLTE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE []) (RLTE regsE))
  by (split; [intros m Hm; unfold RLTE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L6 + 32)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L6 + 32))) by reflexivity.
paj_run_to_tok RUNTO HS HJ SHOK RLSPAN (AF_both3_reac_box_name + RBN_L6); [ rl_awr |].
rl_keepmem HF K. clear HF HFr HG.
pmkst HS.
prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE ([] : list word) RLTTKEPT HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
apply SRr_ret. unfold rl_tail_post. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at, w64; reflexivity|].
split; [exact HJ|].
split; [intros xx; apply K|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q24; reflexivity|].
eapply rl_tkeep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl6_tail3 : rl_tail_stmt (AF_both3_reac_box_name + RBN_L6 + 32) (AF_both3_reac_box_name + RBN_L6) 3 6.
Proof.
unfold rl_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE HJ G20 G24.
pose proof (rl_tentry W regsE memE (AF_both3_reac_box_name + RBN_L6 + 32) 3 6 G20 G24) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLTE regsE) (mrestrict (w_H W) memE)) by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLTE regsE)) by (unfold RLTE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE []) (RLTE regsE))
  by (split; [intros m Hm; unfold RLTE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L6 + 32)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L6 + 32))) by reflexivity.
paj_run_to_tok RUNTO HS HJ SHOK RLSPAN (AF_both3_reac_box_name + RBN_L6); [ rl_awr |].
rl_keepmem HF K. clear HF HFr HG.
pmkst HS.
prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE ([] : list word) RLTTKEPT HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
apply SRr_ret. unfold rl_tail_post. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at, w64; reflexivity|].
split; [exact HJ|].
split; [intros xx; apply K|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q24; reflexivity|].
eapply rl_tkeep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl6_tail4 : rl_tail_stmt (AF_both3_reac_box_name + RBN_L6 + 32) (AF_both3_reac_box_name + RBN_L6) 4 6.
Proof.
unfold rl_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE HJ G20 G24.
pose proof (rl_tentry W regsE memE (AF_both3_reac_box_name + RBN_L6 + 32) 4 6 G20 G24) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLTE regsE) (mrestrict (w_H W) memE)) by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLTE regsE)) by (unfold RLTE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE []) (RLTE regsE))
  by (split; [intros m Hm; unfold RLTE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L6 + 32)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L6 + 32))) by reflexivity.
paj_run_to_tok RUNTO HS HJ SHOK RLSPAN (AF_both3_reac_box_name + RBN_L6); [ rl_awr |].
rl_keepmem HF K. clear HF HFr HG.
pmkst HS.
prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE ([] : list word) RLTTKEPT HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
apply SRr_ret. unfold rl_tail_post. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at, w64; reflexivity|].
split; [exact HJ|].
split; [intros xx; apply K|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q24; reflexivity|].
eapply rl_tkeep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl6_tail5 : rl_tail_stmt (AF_both3_reac_box_name + RBN_L6 + 32) (AF_both3_reac_box_name + RBN_L6X) 5 6.
Proof.
unfold rl_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE HJ G20 G24.
pose proof (rl_tentry W regsE memE (AF_both3_reac_box_name + RBN_L6 + 32) 5 6 G20 G24) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLTE regsE) (mrestrict (w_H W) memE)) by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLTE regsE)) by (unfold RLTE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE []) (RLTE regsE))
  by (split; [intros m Hm; unfold RLTE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L6 + 32)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L6 + 32))) by reflexivity.
paj_run_to_tok RUNTO HS HJ SHOK RLSPAN (AF_both3_reac_box_name + RBN_L6X); [ rl_awr |].
rl_keepmem HF K. clear HF HFr HG.
pmkst HS.
prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE ([] : list word) RLTTKEPT HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
apply SRr_ret. unfold rl_tail_post. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at, w64; reflexivity|].
split; [exact HJ|].
split; [intros xx; apply K|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q24; reflexivity|].
eapply rl_tkeep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl7_tail0 : rl_tail_stmt (AF_both3_reac_box_name + RBN_L7 + 32) (AF_both3_reac_box_name + RBN_L7) 0 5.
Proof.
unfold rl_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE HJ G20 G24.
pose proof (rl_tentry W regsE memE (AF_both3_reac_box_name + RBN_L7 + 32) 0 5 G20 G24) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLTE regsE) (mrestrict (w_H W) memE)) by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLTE regsE)) by (unfold RLTE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE []) (RLTE regsE))
  by (split; [intros m Hm; unfold RLTE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L7 + 32)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L7 + 32))) by reflexivity.
paj_run_to_tok RUNTO HS HJ SHOK RLSPAN (AF_both3_reac_box_name + RBN_L7); [ rl_awr |].
rl_keepmem HF K. clear HF HFr HG.
pmkst HS.
prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE ([] : list word) RLTTKEPT HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
apply SRr_ret. unfold rl_tail_post. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at, w64; reflexivity|].
split; [exact HJ|].
split; [intros xx; apply K|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q24; reflexivity|].
eapply rl_tkeep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl7_tail1 : rl_tail_stmt (AF_both3_reac_box_name + RBN_L7 + 32) (AF_both3_reac_box_name + RBN_L7) 1 5.
Proof.
unfold rl_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE HJ G20 G24.
pose proof (rl_tentry W regsE memE (AF_both3_reac_box_name + RBN_L7 + 32) 1 5 G20 G24) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLTE regsE) (mrestrict (w_H W) memE)) by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLTE regsE)) by (unfold RLTE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE []) (RLTE regsE))
  by (split; [intros m Hm; unfold RLTE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L7 + 32)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L7 + 32))) by reflexivity.
paj_run_to_tok RUNTO HS HJ SHOK RLSPAN (AF_both3_reac_box_name + RBN_L7); [ rl_awr |].
rl_keepmem HF K. clear HF HFr HG.
pmkst HS.
prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE ([] : list word) RLTTKEPT HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
apply SRr_ret. unfold rl_tail_post. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at, w64; reflexivity|].
split; [exact HJ|].
split; [intros xx; apply K|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q24; reflexivity|].
eapply rl_tkeep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl7_tail2 : rl_tail_stmt (AF_both3_reac_box_name + RBN_L7 + 32) (AF_both3_reac_box_name + RBN_L7) 2 5.
Proof.
unfold rl_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE HJ G20 G24.
pose proof (rl_tentry W regsE memE (AF_both3_reac_box_name + RBN_L7 + 32) 2 5 G20 G24) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLTE regsE) (mrestrict (w_H W) memE)) by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLTE regsE)) by (unfold RLTE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE []) (RLTE regsE))
  by (split; [intros m Hm; unfold RLTE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L7 + 32)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L7 + 32))) by reflexivity.
paj_run_to_tok RUNTO HS HJ SHOK RLSPAN (AF_both3_reac_box_name + RBN_L7); [ rl_awr |].
rl_keepmem HF K. clear HF HFr HG.
pmkst HS.
prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE ([] : list word) RLTTKEPT HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
apply SRr_ret. unfold rl_tail_post. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at, w64; reflexivity|].
split; [exact HJ|].
split; [intros xx; apply K|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q24; reflexivity|].
eapply rl_tkeep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl7_tail3 : rl_tail_stmt (AF_both3_reac_box_name + RBN_L7 + 32) (AF_both3_reac_box_name + RBN_L7) 3 5.
Proof.
unfold rl_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE HJ G20 G24.
pose proof (rl_tentry W regsE memE (AF_both3_reac_box_name + RBN_L7 + 32) 3 5 G20 G24) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLTE regsE) (mrestrict (w_H W) memE)) by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLTE regsE)) by (unfold RLTE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE []) (RLTE regsE))
  by (split; [intros m Hm; unfold RLTE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L7 + 32)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L7 + 32))) by reflexivity.
paj_run_to_tok RUNTO HS HJ SHOK RLSPAN (AF_both3_reac_box_name + RBN_L7); [ rl_awr |].
rl_keepmem HF K. clear HF HFr HG.
pmkst HS.
prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE ([] : list word) RLTTKEPT HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
apply SRr_ret. unfold rl_tail_post. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at, w64; reflexivity|].
split; [exact HJ|].
split; [intros xx; apply K|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q24; reflexivity|].
eapply rl_tkeep_of; [exact HKr | exact Q24 | exact G24].
Qed.

Lemma rl7_tail4 : rl_tail_stmt (AF_both3_reac_box_name + RBN_L7 + 32) (AF_both3_reac_box_name + RBN_L7X) 4 5.
Proof.
unfold rl_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k regsE HJ G20 G24.
pose proof (rl_tentry W regsE memE (AF_both3_reac_box_name + RBN_L7 + 32) 4 5 G20 G24) as HS.
assert (SHOK : sh_ok SEGS RLBx RLSH (RLTE regsE) (mrestrict (w_H W) memE)) by (unfold sh_ok, RLSH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (RLTE regsE)) by (unfold RLTE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE []) (RLTE regsE))
  by (split; [intros m Hm; unfold RLTE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
replace (w64 (BASE + (AF_both3_reac_box_name + RBN_L7 + 32)))
  with (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L7 + 32))) by reflexivity.
paj_run_to_tok RUNTO HS HJ SHOK RLSPAN (AF_both3_reac_box_name + RBN_L7X); [ rl_awr |].
rl_keepmem HF K. clear HF HFr HG.
pmkst HS.
prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE ([] : list word) RLTTKEPT HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
apply SRr_ret. unfold rl_tail_post. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at, w64; reflexivity|].
split; [exact HJ|].
split; [intros xx; apply K|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q24; reflexivity|].
eapply rl_tkeep_of; [exact HKr | exact Q24 | exact G24].
Qed.
Lemma rl_lyF_eq : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  lyc2 Sc2 (W2 : world SEGS) mem2 md2 k2,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc2 Sc2 W2 mem2 md2 k2 ->
  ly_F lyc2 = ly_F lyc.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc2 Sc2 W2 mem2 md2 k2 HJ1 HJ2.
destruct HJ1 as (_ & Hle1 & _). destruct HJ2 as (_ & Hle2 & _).
destruct Hle1 as (_ & _ & _ & _ & _ & HF1 & _). destruct Hle2 as (_ & _ & _ & _ & _ & HF2 & _).
rewrite HF2, HF1. reflexivity.
Qed.
Lemma rl_awr_lyc : forall STK sp0 FP bl0 blc lyc lyc' own a,
  ly_F lyc' = ly_F lyc ->
  awr_byte STK sp0 FP bl0 blc lyc own a -> awr_byte STK sp0 FP bl0 blc lyc' own a.
Proof.
intros STK sp0 FP bl0 blc lyc lyc' own a HF H.
destruct H as [H|[H|[H|H]]].
- left. exact H.
- right. left. exact H.
- right. right. left. exact H.
- right. right. right. destruct H as (cid & pos & Hin & Hz). exists cid, pos. split; [exact Hin|].
  replace (frame_addr lyc' cid pos) with (frame_addr lyc cid pos) by (unfold frame_addr; rewrite HF; reflexivity).
  exact Hz.
Qed.
Lemma rl_ra_transfer : forall (W W2 : world SEGS) memc mem2 (Ex : Z -> Prop) (sp a n : Z),
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF a n ->
  (forall s, 0 <= s < 2 ^ 64 -> ~ (sp - TSB_CH_STK <= s < sp) -> ~ Ex s ->
     aview SEGS (w_H W2) mem2 s = aview SEGS (w_H W) memc s) ->
  (forall x, a <= x < a + n -> 0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\
     ~ (sp - TSB_CH_STK <= SHADOW_OFF + x / 8 < sp) /\ ~ Ex (SHADOW_OFF + x / 8)) ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF a n.
Proof.
intros W W2 memc mem2 Ex sp a n HRA Hkeep Hsep x Hx.
destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. destruct (Hsep x Hx) as (H1 & H2 & H3).
rewrite Hkeep by assumption. exact Hs.
Qed.
Lemma rl_shv_transfer : forall (W W2 : world SEGS) memc mem2 (Ex : Z -> Prop) (sp a n : Z),
  shadow_hull_vis (aview SEGS (w_H W) memc) a n ->
  (forall s, 0 <= s < 2 ^ 64 -> ~ (sp - TSB_CH_STK <= s < sp) -> ~ Ex s ->
     aview SEGS (w_H W2) mem2 s = aview SEGS (w_H W) memc s) ->
  (forall s, shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
     0 <= s < 2 ^ 64 /\ ~ (sp - TSB_CH_STK <= s < sp) /\ ~ Ex s) ->
  shadow_hull_vis (aview SEGS (w_H W2) mem2) a n.
Proof.
intros W W2 memc mem2 Ex sp a n HSV Hkeep Hsep s Hs.
destruct (Hsep s Hs) as (H1 & H2 & H3). rewrite Hkeep by assumption. exact (HSV s Hs).
Qed.
Lemma rl_vm_transfer : forall (W W2 : world SEGS) memc mem2 (Ex : Z -> Prop) (sp a : Z) (n : nat) v,
  val_mem SEGS (mrestrict (w_H W) memc) a n v ->
  (forall s, 0 <= s < 2 ^ 64 -> ~ (sp - TSB_CH_STK <= s < sp) -> ~ Ex s ->
     aview SEGS (w_H W2) mem2 s = aview SEGS (w_H W) memc s) ->
  (forall k, 0 <= k < Z.of_nat n -> 0 <= a + k < 2 ^ 64 /\ ~ (sp - TSB_CH_STK <= a + k < sp) /\ ~ Ex (a + k)) ->
  val_mem SEGS (mrestrict (w_H W2) mem2) a n v.
Proof.
intros W W2 memc mem2 Ex sp a n v HV Hkeep Hsep.
apply (val_mem_kept SEGS (w_H W) (w_H W2) memc mem2 a n v); [|exact HV].
intros kk Hk. destruct (Hsep kk Hk) as (H1 & H2 & H3). apply Hkeep; assumption.
Qed.
Lemma rl_aview_eqm : forall (W : world SEGS) (m1 m2 : word -> option byte),
  (forall x : word, m1 x = m2 x) ->
  forall a, aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m2 a.
Proof.
intros W m1 m2 Hm a. unfold aview, mbyte, mrestrict. rewrite Hm. reflexivity.
Qed.
Lemma rl_vm_eqv : forall (W : world SEGS) (m1 m2 : word -> option byte) a (n : nat) v,
  (forall x : word, m1 x = m2 x) ->
  val_mem SEGS (mrestrict (w_H W) m1) a n v -> val_mem SEGS (mrestrict (w_H W) m2) a n v.
Proof.
intros W m1 m2 a n v Hm HV.
apply (val_mem_kept SEGS (w_H W) (w_H W) m1 m2 a n v); [|exact HV].
intros kk Hk. apply (rl_aview_eqm W m2 m1). intros x. symmetry. apply Hm.
Qed.
Lemma rl_garr_eqv : forall (W : world SEGS) (m1 m2 : word -> option byte) a (L : list Z),
  (forall x : word, m1 x = m2 x) ->
  garr8 SEGS (mrestrict (w_H W) m1) a L -> garr8 SEGS (mrestrict (w_H W) m2) a L.
Proof.
intros W m1 m2 a L Hm HG.
apply (garr8_aview_kept SEGS (w_H W) (w_H W) m1 m2 a L); [|exact HG].
intros x Hx. apply (rl_aview_eqm W m2 m1). intros y. symmetry. apply Hm.
Qed.
Lemma rl_ra_eqv : forall (W : world SEGS) (m1 m2 : word -> option byte) a n,
  (forall x : word, m1 x = m2 x) ->
  range_addressable (aview SEGS (w_H W) m1) SHADOW_OFF a n ->
  range_addressable (aview SEGS (w_H W) m2) SHADOW_OFF a n.
Proof.
intros W m1 m2 a n Hm HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. apply (rl_aview_eqm W m2 m1). intros y. symmetry. apply Hm.
Qed.
Lemma rl_shv_eqv : forall (W : world SEGS) (m1 m2 : word -> option byte) a n,
  (forall x : word, m1 x = m2 x) ->
  shadow_hull_vis (aview SEGS (w_H W) m1) a n -> shadow_hull_vis (aview SEGS (w_H W) m2) a n.
Proof.
intros W m1 m2 a n Hm HV s Hs. rewrite (rl_aview_eqm W m2 m1 ltac:(intros y; symmetry; apply Hm) s).
exact (HV s Hs).
Qed.
Lemma rl_apres_eqv : forall (W : world SEGS) (m1 m2 : word -> option byte) a,
  (forall x : word, m1 x = m2 x) -> apresent (w_H W) m1 a -> apresent (w_H W) m2 a.
Proof.
intros W m1 m2 a Hm (H1 & b & Hb). split; [exact H1|]. exists b. rewrite <- Hm. exact Hb.
Qed.
Lemma rl_rod_eqv : forall (W : world SEGS) (m1 m2 : word -> option byte),
  (forall x : word, m1 x = m2 x) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m1) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m2).
Proof.
intros W m1 m2 Hm HR a Hro Ho He.
rewrite (rl_aview_eqm W m2 m1 ltac:(intros y; symmetry; apply Hm) a). exact (HR a Hro Ho He).
Qed.
Lemma rl_rec_eqv : forall STK sp0 FP ly S own lyc Sc (W : world SEGS) (m1 m2 : word -> option byte) sp R D cap n ov,
  (forall x : word, m1 x = m2 x) ->
  rbn_lrec B STK sp0 FP ly S own lyc Sc W m1 sp R D cap n ov ->
  rbn_lrec B STK sp0 FP ly S own lyc Sc W m2 sp R D cap n ov.
Proof.
intros STK sp0 FP ly S own lyc Sc W m1 m2 sp R D cap n ov Hm
  (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & V0 & V8 & V16 & V24 & RA & SV & HW).
unfold rbn_lrec. repeat (split; [assumption|]).
split; [exact (rl_vm_eqv W m1 m2 _ _ _ Hm V0)|].
split; [exact (rl_vm_eqv W m1 m2 _ _ _ Hm V8)|].
split; [exact (rl_vm_eqv W m1 m2 _ _ _ Hm V16)|].
split; [exact (rl_vm_eqv W m1 m2 _ _ _ Hm V24)|].
split; [exact (rl_ra_eqv W m1 m2 _ _ Hm RA)|].
split; [exact (rl_shv_eqv W m1 m2 _ _ Hm SV)|].
intros a Ha. destruct (HW a Ha) as (Hwr & Hpr). split; [exact Hwr | exact (rl_apres_eqv W m1 m2 a Hm Hpr)].
Qed.
Lemma rl_buf_eqv : forall STK sp0 FP ly S own lyc Sc (W : world SEGS) (m1 m2 : word -> option byte) sp R D cap,
  (forall x : word, m1 x = m2 x) ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W m1 sp R D cap ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W m2 sp R D cap.
Proof.
intros STK sp0 FP ly S own lyc Sc W m1 m2 sp R D cap Hm
  (A1 & A2 & A3 & A4 & A5 & A6 & A7 & RA & SV & HW).
unfold rbn_lbuf. repeat (split; [assumption|]).
split; [exact (rl_ra_eqv W m1 m2 _ _ Hm RA)|].
split; [exact (rl_shv_eqv W m1 m2 _ _ Hm SV)|].
intros a Ha. destruct (HW a Ha) as (Hwr & Hpr). split; [exact Hwr | exact (rl_apres_eqv W m1 m2 a Hm Hpr)].
Qed.
Lemma rl_src_eqv : forall (W : world SEGS) (m1 m2 : word -> option byte) P L,
  (forall x : word, m1 x = m2 x) -> rbn_lsrc W m1 P L -> rbn_lsrc W m2 P L.
Proof.
intros W m1 m2 P L Hm (HG & A1 & A2 & A3 & RA).
unfold rbn_lsrc. split; [exact (rl_garr_eqv W m1 m2 _ _ Hm HG)|].
split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
exact (rl_ra_eqv W m1 m2 _ _ Hm RA).
Qed.
Lemma rl_shadow_bound : forall a n x, 0 < a -> amem_range a n -> a <= x < a + n ->
  kLowMemEnd <= SHADOW_OFF + x / 8 < kHighShadowEnd.
Proof.
intros a n x Ha Hmr Hx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hd : 0 <= x / 8) by (apply Z.div_pos; lia).
unfold amem_range in Hmr. rewrite C5, C3, C4 in Hmr.
rewrite C5, C2. unfold SHADOW_OFF.
destruct Hmr as [Hlo | (Hhi1 & Hhi2)].
- assert (Hx8 : x / 8 < 268435456) by (apply Z.div_lt_upper_bound; lia). lia.
- assert (Hx8 : x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma rl_amem_sub : forall a n a' n', amem_range a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n ->
  amem_range a' n'.
Proof.
intros a n a' n' H H1 H2 H3. unfold amem_range in *. destruct H as [H | (H4 & H5)];
[left; lia | right; split; lia].
Qed.
Lemma rl_shv_sub : forall rd a n a' n', shadow_hull_vis rd a n -> a <= a' -> 0 < n' -> a' + n' <= a + n ->
  shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' H H1 H2 H3 s Hs. apply H.
pose proof (shadow_mono a a' H1) as M1.
pose proof (shadow_mono (a' + n' - 1) (a + n - 1) ltac:(lia)) as M2.
pose proof (Z.mul_div_le (shadow_addr a) 8 ltac:(lia)) as D1.
pose proof (Z.mul_div_le (shadow_addr a') 8 ltac:(lia)) as D2.
pose proof (Z.div_le_mono (shadow_addr a) (shadow_addr a') 8 ltac:(lia) M1) as D3.
pose proof (Z.div_le_mono (shadow_addr (a' + n' - 1)) (shadow_addr (a + n - 1)) 8 ltac:(lia) M2) as D4.
lia.
Qed.
Lemma rl_keep_chain : forall (r1 r2 r3 r4 : bvmap 5 word),
  rbn_keep_regs r1 r2 RLCL -> aregs_preserved r2 r3 -> rbn_keep_regs r3 r4 [20] ->
  rbn_keep_regs r1 r4 RLCL.
Proof.
intros r1 r2 r3 r4 H12 H23 H34 z Hz Hnin.
assert (Hnc : ~ In z RLCL) by exact Hnin. unfold RLCL, rbn_cl5, rbn_clc in Hnc. cbn [app In] in Hnc.
destruct (Z.eq_dec z 0) as [->|Hz0].
- replace (Z_to_bv 5 0 : bv 5) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite !getr_zero. reflexivity.
- rewrite (H34 z Hz ltac:(cbn [In]; lia)).
  rewrite (H23 z ltac:(unfold acallee_saved; lia)).
  exact (H12 z Hz Hnin).
Qed.
Lemma rl_kept_eqv : forall lyc Sc (W : world SEGS) memc (W2 : world SEGS) (m1 m2 : word -> option byte) sp Ex,
  (forall x : word, m1 x = m2 x) ->
  tsb_ch_kept B lyc Sc W memc W2 m1 sp Ex -> tsb_ch_kept B lyc Sc W memc W2 m2 sp Ex.
Proof.
intros lyc Sc W memc W2 m1 m2 sp Ex Hm (K1 & K2 & K3 & K4 & K5 & K6).
assert (HA : forall a, aview SEGS (w_H W2) m2 a = aview SEGS (w_H W2) m1 a)
  by (intros a; apply (rl_aview_eqm W2 m2 m1); intros y; symmetry; apply Hm).
split; [intros a H1 H2 H3; rewrite HA; exact (K1 a H1 H2 H3)|].
split; [intros b m i H1 H2 H3; rewrite HA; exact (K2 b m i H1 H2 H3)|].
split; [intros a H1 H2 H3; rewrite HA; exact (K3 a H1 H2 H3)|].
split; [intros cid pos a H1 H2 H3; rewrite HA; exact (K4 cid pos a H1 H2 H3)|].
split; [intros a H1 H2 H3; exact (rl_apres_eqv W2 m1 m2 a Hm (K5 a H1 H2 H3))|].
intros a Ha. exact (rl_apres_eqv W2 m1 m2 a Hm (K6 a Ha)).
Qed.
Lemma rl_kept_mono : forall lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 sp (E1 E2 : Z -> Prop),
  (forall a, E1 a -> E2 a) ->
  tsb_ch_kept B lyc Sc W memc W2 mem2 sp E1 -> tsb_ch_kept B lyc Sc W memc W2 mem2 sp E2.
Proof.
intros lyc Sc W memc W2 mem2 sp E1 E2 Hsub (K1 & K2 & K3 & K4 & K5 & K6).
split; [intros a H1 H2 H3; exact (K1 a H1 H2 ltac:(intros Hq; exact (H3 (Hsub a Hq))))|].
split; [intros b m i H1 H2 H3; exact (K2 b m i H1 H2 ltac:(intros Hq; exact (H3 (Hsub (b + i) Hq))))|].
split; [exact K3|].
split; [intros cid pos a H1 H2 H3; exact (K4 cid pos a H1 H2 ltac:(intros Hq; exact (H3 (Hsub a Hq))))|].
split; [exact K5 | exact K6].
Qed.
Lemma rl_kept_trans : forall lyc Sc lyc1 Sc1 (W : world SEGS) memc (W1 : world SEGS) m1 (W2 : world SEGS) m2 sp
  (E1 E2 : Z -> Prop),
  frames Sc1 = frames Sc -> ablocks B lyc1 Sc1 = ablocks B lyc Sc -> ly_F lyc1 = ly_F lyc ->
  tsb_ch_kept B lyc Sc W memc W1 m1 sp E1 ->
  tsb_ch_kept B lyc1 Sc1 W1 m1 W2 m2 sp E2 ->
  tsb_ch_kept B lyc Sc W memc W2 m2 sp (fun a => E1 a \/ E2 a).
Proof.
intros lyc Sc lyc1 Sc1 W memc W1 m1 W2 m2 sp E1 E2 Hfr Hbl HF
  (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6).
assert (Hfrng : forall cid pos, frame_rng lyc1 (cid, pos) = frame_rng lyc (cid, pos))
  by (intros cid pos; unfold frame_rng, frame_addr; cbn [fst snd]; rewrite HF; reflexivity).
assert (Hfad : forall cid pos, frame_addr lyc1 cid pos = frame_addr lyc cid pos)
  by (intros cid pos; unfold frame_addr; rewrite HF; reflexivity).
split.
{ intros a H1 H2 H3. rewrite (B1 a H1 H2 ltac:(intros Hq; apply H3; right; exact Hq)).
  exact (A1 a H1 H2 ltac:(intros Hq; apply H3; left; exact Hq)). }
split.
{ intros b m i H1 H2 H3.
  rewrite (B2 b m i ltac:(rewrite Hbl; exact H1) H2 ltac:(intros Hq; apply H3; right; exact Hq)).
  exact (A2 b m i H1 H2 ltac:(intros Hq; apply H3; left; exact Hq)). }
split.
{ intros a H1 H2 H3. rewrite (B3 a H1 H2 H3). exact (A3 a H1 H2 H3). }
split.
{ intros cid pos a H1 H2 H3.
  rewrite (B4 cid pos a ltac:(rewrite Hfr; exact H1)
    ltac:(rewrite Hfrng, Hfad; exact H2) ltac:(intros Hq; apply H3; right; exact Hq)).
  exact (A4 cid pos a H1 H2 ltac:(intros Hq; apply H3; left; exact Hq)). }
split.
{ intros a H1 H2 H3. exact (B5 a H1 H2 (A5 a H1 H2 H3)). }
intros a Ha. exact (B6 a Ha).
Qed.
Lemma rl_rod_kept : forall lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 sp Ex,
  tsb_ch_kept B lyc Sc W memc W2 mem2 sp Ex ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
intros lyc Sc W memc W2 mem2 sp Ex (_ & _ & K3 & _) HR a Hro Ho He.
assert (Hia : in_img SEGS a)
  by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr];
      [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
rewrite (K3 a Hia Ho He). exact (HR a Hro Ho He).
Qed.
Lemma rl_firstn_S : forall (ll : list Z) (n : nat) (d : Z), (n < length ll)%nat ->
  firstn (S n) ll = firstn n ll ++ [nth n ll d].
Proof.
induction ll as [|x t IH]; intros n d Hn.
- cbn [length] in Hn. lia.
- destruct n as [|n].
  + cbn [firstn nth app]. reflexivity.
  + cbn [length] in Hn. cbn [firstn nth].
    rewrite <- app_comm_cons. f_equal. apply IH. lia.
Qed.
Lemma rl_firstn_Z : forall (ll : list Z) (z d : Z), 0 <= z -> (Z.to_nat z < length ll)%nat ->
  firstn (Z.to_nat (z + 1)) ll = firstn (Z.to_nat z) ll ++ [nth (Z.to_nat z) ll d].
Proof.
intros ll z d Hz Hlt. replace (Z.to_nat (z + 1)) with (S (Z.to_nat z)) by lia.
apply rl_firstn_S. exact Hlt.
Qed.
Lemma rl_garr8_snoc : forall (W : world SEGS) m a (ll : list Z) v,
  garr8 SEGS (mrestrict (w_H W) m) a ll ->
  val_mem SEGS (mrestrict (w_H W) m) (a + Z.of_nat (length ll)) 1 v -> 0 <= v < 256 ->
  garr8 SEGS (mrestrict (w_H W) m) a (ll ++ [v]).
Proof.
intros W m a ll v HG HV HR j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length ll)) as [Hlt | Hge].
- rewrite app_nth1 by exact Hlt. exact (HG j Hlt).
- assert (Hje : j = length ll) by lia. subst j.
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. split; [exact HV | exact HR].
Qed.
Lemma rl_keep_trans2 : forall (r1 r2 r3 : bvmap 5 word) cl,
  rbn_keep_regs r1 r2 cl -> rbn_keep_regs r2 r3 cl -> rbn_keep_regs r1 r3 cl.
Proof. intros r1 r2 r3 cl H1 H2 z Hz Hn. rewrite (H2 z Hz Hn). exact (H1 z Hz Hn). Qed.
Section S.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (D n0 ov0 lit : Z) (l : list Z) (N : Z).
Hypothesis HCX : rbn_lcx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs.
Hypothesis HREC : rbn_lrec B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 n0 ov0.
Hypothesis HBUF : rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48.
Hypothesis HSRC : rbn_lsrc W memc lit (l ++ [0]).
Hypothesis HLAL : lit mod 8 = 0.
Hypothesis HSEP : rbn_lsep (spZ regs) (spZ regs + 88) D 48 lit (N + 1).
Hypothesis HN0 : 0 <= n0 <= 47.
Hypothesis HOV0 : ov0 = 0 \/ ov0 = 1.
Hypothesis HLEN : Z.of_nat (length l) = N.
Hypothesis HNN : 0 < N <= 7.
Hypothesis HCHR : Forall (fun c => 0 < c < 256) l.
Hypothesis HIMGL : IMG_LO <= lit.
Hypothesis HIMGH : lit + 8 <= IMG_TOP.
Hypothesis HR21 : getr regs 21 = w64 lit.
Hypothesis HR24 : getr regs 24 = w64 N.
Definition rl_cnt (j : Z) : Z := Z.min j (47 - n0).
Definition rl_nn (j : Z) : Z := n0 + rl_cnt j.
Definition rl_ovv (j : Z) : Z := if n0 + j <=? 47 then ov0 else 1.
Definition rl_wrl (j : Z) : list Z := firstn (Z.to_nat (rl_cnt j)) l.
Definition rl_Eset (j : Z) : Z -> Prop :=
  fun a => spZ regs + 88 + 16 <= a < spZ regs + 88 + 28 \/
           D + n0 <= a < D + n0 + Z.of_nat (length (rl_wrl j)).
Definition rl_inv (pc j : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists lyc2 Sc2 (regs2 : bvmap 5 word) mem2 md2,
    c2 = cfg_at (fx := fx) SEGS (BASE + pc) regs2 mem2 md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc2 Sc2 W2 mem2 md2 k /\
    frames Sc2 = frames Sc /\ ablocks B lyc2 Sc2 = ablocks B lyc Sc /\
    arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2) /\
    rbn_keep_regs regs regs2 RLCL /\ getr regs2 20 = w64 j /\
    rbn_lrec B STK sp0 FP ly S own lyc2 Sc2 W2 mem2 (spZ regs) (spZ regs + 88) D 48 (rl_nn j) (rl_ovv j) /\
    rbn_lbuf B STK sp0 FP ly S own lyc2 Sc2 W2 mem2 (spZ regs) (spZ regs + 88) D 48 /\
    rbn_lsrc W2 mem2 lit (l ++ [0]) /\
    garr8 SEGS (mrestrict (w_H W2) mem2) (D + n0) (rl_wrl j) /\
    tsb_ch_kept B lyc Sc W memc W2 mem2 (spZ regs) (rl_Eset j).
Lemma rl_step : forall (jj Loff retoff tgt : Z),
  0 <= jj < N ->
  YK0s.ret_ok (w64 (BASE + retoff)) -> 4096 <= BASE + retoff -> 0 <= BASE + retoff < 2 ^ 64 ->
  rl_head_stmt Loff jj (nth (Z.to_nat jj) l 0) retoff ->
  rl_tail_stmt retoff tgt jj N ->
  forall W1 c1, rl_inv Loff jj W1 c1 -> SRr SEGS W1 c1 (rl_inv tgt (jj + 1)).
Proof.
intros jj Loff retoff tgt Hjj HROK HRA4 HRB HHEAD HTAIL W1 c1
  (lyc1 & Sc1 & regs1 & mem1 & md1 & -> & HJ1 & Hfr1 & Hbl1 & Hro1 & HK1 & H20 & HREC1 & HBUF1 & HSRC1 & HG1 & KEPT1).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCX as (HJ0 & HRO0 & Hgp & Htp & Hs1 & Hs6 & Hsp16 & Hbudget & Hsple).
pose proof HJ1 as (HAR1 & Hle1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
assert (HSP : getr regs 2 = w64 (spZ regs)) by (unfold spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Rsp : 0 <= spZ regs < 2 ^ 64)
  by (pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hq;
      change (bv_modulus 64) with (2 ^ 64) in Hq; unfold spZ; lia).
assert (G24 : getr regs1 24 = w64 N).
{ replace (24%bv : bv 5) with (Z_to_bv 5 24 : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite (HK1 24 ltac:(lia) ltac:(unfold RLCL, rbn_cl5, rbn_clc; cbn [app In]; lia)).
  replace (Z_to_bv 5 24 : bv 5) with (24%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact HR24. }
assert (G21 : getr regs1 21 = w64 lit).
{ replace (21%bv : bv 5) with (Z_to_bv 5 21 : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite (HK1 21 ltac:(lia) ltac:(unfold RLCL, rbn_cl5, rbn_clc; cbn [app In]; lia)).
  replace (Z_to_bv 5 21 : bv 5) with (21%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact HR21. }
assert (G22 : getr regs1 22 = w64 SHADOW_OFF).
{ replace (22%bv : bv 5) with (Z_to_bv 5 22 : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite (HK1 22 ltac:(lia) ltac:(unfold RLCL, rbn_cl5, rbn_clc; cbn [app In]; lia)).
  replace (Z_to_bv 5 22 : bv 5) with (22%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact Hs6. }
assert (G9 : getr regs1 9 = w64 (spZ regs)).
{ replace (9%bv : bv 5) with (Z_to_bv 5 9 : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite (HK1 9 ltac:(lia) ltac:(unfold RLCL, rbn_cl5, rbn_clc; cbn [app In]; lia)).
  replace (Z_to_bv 5 9 : bv 5) with (9%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hs1. exact HSP. }
assert (G3 : getr regs1 3 = w64 (as_gp B)).
{ replace (3%bv : bv 5) with (Z_to_bv 5 3 : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite (HK1 3 ltac:(lia) ltac:(unfold RLCL, rbn_cl5, rbn_clc; cbn [app In]; lia)).
  replace (Z_to_bv 5 3 : bv 5) with (3%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact Hgp. }
assert (G4 : getr regs1 4 = w64 (as_tp B)).
{ replace (4%bv : bv 5) with (Z_to_bv 5 4 : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite (HK1 4 ltac:(lia) ltac:(unfold RLCL, rbn_cl5, rbn_clc; cbn [app In]; lia)).
  replace (Z_to_bv 5 4 : bv 5) with (4%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact Htp. }
assert (G2 : getr regs1 2 = w64 (spZ regs)).
{ replace (2%bv : bv 5) with (Z_to_bv 5 2 : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite (HK1 2 ltac:(lia) ltac:(unfold RLCL, rbn_cl5, rbn_clc; cbn [app In]; lia)).
  replace (Z_to_bv 5 2 : bv 5) with (2%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact HSP. }
assert (Gsp : spZ regs1 = spZ regs) by (unfold spZ at 1; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
set (cc := nth (Z.to_nat jj) l 0) in *.
assert (Hccr : 0 < cc < 256).
{ subst cc. apply (proj1 (Forall_forall _ _) HCHR). apply nth_In. lia. }
assert (Vcc : val_mem SEGS (mrestrict (w_H W1) mem1) (lit + jj) 1 cc).
{ destruct HSRC1 as (HGs & _).
  destruct (HGs (Z.to_nat jj) ltac:(rewrite length_app; cbn [length]; lia)) as (Hv & _).
  replace (lit + Z.of_nat (Z.to_nat jj)) with (lit + jj) in Hv by lia.
  rewrite app_nth1 in Hv by lia. exact Hv. }
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HLAL]).
destruct Hdv as (q & Hq).
assert (Hsh : SHADOW_OFF + (lit + jj) / 8 = SHADOW_OFF + lit / 8).
{ rewrite Hq. rewrite Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (jj / 8) with 0 by (symmetry; apply Z.div_small; lia). lia. }
destruct HSRC1 as (HGs & HP0 & HP63 & HP47 & HRAs).
destruct (HRAs (lit + jj) ltac:(rewrite length_app; cbn [length]; lia)) as (svv & Hsvv & Hok).
unfold shadow_of_addr in Hsvv. rewrite Hsh in Hsvv.
assert (Hmod : (lit + jj) mod 8 = jj)
  by (rewrite Hq, Z.add_comm, Z.mod_add by lia; apply Z.mod_small; lia).
assert (Hsvr : 0 <= svv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm1 & Hm2)]; [lia | rewrite Hmod in Hm1; lia]).
assert (Hsvc : svv = 0 \/ jj < svv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm1 & Hm2)];
      [left; reflexivity | right; rewrite Hmod in Hm1; lia]).
eapply SRr_bind.
{ exact (HHEAD STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem1 md1 k regs1 N lit (spZ regs) svv
    HJ1 H20 G24 G21 G22 G9 ltac:(lia) ltac:(lia) ltac:(lia) HIMGL HIMGH HLAL Vcc Hsvv Hsvr Hsvc). }
cbv beta. intros Wh ch _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hmem2 & Hra2 & Ha0 & Ha1 & H20b & H24b & HKh).
assert (Gsp2 : spZ regs2 = spZ regs).
{ unfold spZ at 1.
  replace (2%bv : bv 5) with (Z_to_bv 5 2 : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite (HKh 2 ltac:(lia) ltac:(unfold RLCL, rbn_cl5, rbn_clc; cbn [app In]; lia)).
  replace (Z_to_bv 5 2 : bv 5) with (2%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite G2. unfold w64. apply unsigned_lit_small. lia. }
assert (G3b : getr regs2 3 = w64 (as_gp B)).
{ replace (3%bv : bv 5) with (Z_to_bv 5 3 : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite (HKh 3 ltac:(lia) ltac:(unfold RLCL, rbn_cl5, rbn_clc; cbn [app In]; lia)).
  replace (Z_to_bv 5 3 : bv 5) with (3%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact G3. }
assert (G4b : getr regs2 4 = w64 (as_tp B)).
{ replace (4%bv : bv 5) with (Z_to_bv 5 4 : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite (HKh 4 ltac:(lia) ltac:(unfold RLCL, rbn_cl5, rbn_clc; cbn [app In]; lia)).
  replace (Z_to_bv 5 4 : bv 5) with (4%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact G4. }
pose proof (rl_rec_eqv STK sp0 FP ly S own lyc1 Sc1 W1 mem1 mem2 _ _ _ _ _ _
  ltac:(intros x; symmetry; apply Hmem2) HREC1) as HREC2.
pose proof (rl_buf_eqv STK sp0 FP ly S own lyc1 Sc1 W1 mem1 mem2 _ _ _ _
  ltac:(intros x; symmetry; apply Hmem2) HBUF1) as HBUF2.
pose proof (rl_rod_eqv W1 mem1 mem2 ltac:(intros x; symmetry; apply Hmem2) Hro1) as Hro2.
pose proof (rl_garr_eqv W1 mem1 mem2 _ _ ltac:(intros x; symmetry; apply Hmem2) HG1) as HG2.
pose proof (rl_src_eqv W1 mem1 mem2 lit (l ++ [0]) ltac:(intros x; symmetry; apply Hmem2)
  (conj HGs (conj HP0 (conj HP63 (conj HP47 HRAs))))) as HSRC2.
destruct HSRC2 as (HGs2 & HP02 & HP632 & HP472 & HRAs2).
assert (Hlen1 : Z.of_nat (length (l ++ [0])) = N + 1) by (rewrite length_app; cbn [length]; lia).
rewrite Hlen1 in HP632, HP472, HRAs2.
pose proof HSEP as HSEPx. unfold rbn_lsep in HSEPx. destruct HSEPx as (HSEPD & HSEPR & HSEPS).
pose proof (rl_kept_eqv lyc Sc W memc W1 mem1 mem2 (spZ regs) (rl_Eset jj)
  ltac:(intros x; symmetry; apply Hmem2) KEPT1) as KEPT2.
destruct HREC2 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & V0 & V8 & V16 & V24 & RRA & RSV & RWR).
destruct HBUF2 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & URA & USV & UWR).
assert (Hnr : 0 <= rl_nn jj <= 47) by (unfold rl_nn, rl_cnt; lia).
eapply SRr_bind.
{ apply (TSB fx STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem2 md2 k regs2
    (spZ regs + 88) cc D 48 (rl_nn jj) []).
  - exact HJ2.
  - exact Hro2.
  - rewrite Hra2. exact HROK.
  - unfold raZ. rewrite Hra2. unfold w64. rewrite unsigned_lit_small by lia. exact HRA4.
  - exact G3b.
  - exact G4b.
  - exact Ha0.
  - exact Ha1.
  - apply achain_low. unfold s0Z. rewrite getr_same by reg_neq_tac.
    rewrite unsigned_lit_small by lia. lia.
  - rewrite Gsp2. exact Hsp16.
  - rewrite Gsp2. exact Hbudget.
  - rewrite Gsp2. exact Hsple.
  - lia.
  - exact R1.
  - exact R2.
  - exact R3.
  - exact R4.
  - rewrite Gsp2. exact R6.
  - exact R5.
  - lia.
  - lia.
  - lia.
  - exact V0.
  - exact V8.
  - exact V16.
  - exact RRA.
  - exact RSV.
  - exact RWR.
  - intros Hlt.
    assert (Hrng : 0 <= rl_nn jj < 48) by lia.
    split; [lia|].
    split; [lia|].
    split; [exact (rl_amem_sub D 48 (D + rl_nn jj) 1 U4 ltac:(lia) ltac:(lia) ltac:(lia))|].
    split; [exact (range_addressable_sub (aview SEGS (w_H W1) mem2) SHADOW_OFF D 48 (D + rl_nn jj) 1
                     URA ltac:(lia) ltac:(lia))|].
    split; [exact (rl_shv_sub (aview SEGS (w_H W1) mem2) D 48 (D + rl_nn jj) 1 USV
                     ltac:(lia) ltac:(lia) ltac:(lia))|].
    split; [rewrite Gsp2; unfold off_img in *; lia|].
    split; [unfold off_img in *; lia|].
    split; [lia|].
    destruct (UWR (D + rl_nn jj) ltac:(lia)) as (Hwr & Hpr).
    split; [exact Hwr | exact Hpr]. }
cbv beta. intros Wt ct _ (ly3 & S3 & regs3 & mem3 & md3 & Hcfg3 & HJ3 & HPRES3 & Hfr3 & Hbl3 & HCASE).
assert (G20c : getr regs3 20 = w64 jj).
{ replace (20%bv : bv 5) with (Z_to_bv 5 20 : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite (HPRES3 20 ltac:(unfold acallee_saved; lia)).
  replace (Z_to_bv 5 20 : bv 5) with (20%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H20b. }
assert (G24c : getr regs3 24 = w64 N).
{ replace (24%bv : bv 5) with (Z_to_bv 5 24 : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite (HPRES3 24 ltac:(unfold acallee_saved; lia)).
  replace (Z_to_bv 5 24 : bv 5) with (24%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H24b. }
rewrite Hra2 in Hcfg3. subst ct.
assert (HlyF1 : ly_F lyc1 = ly_F lyc)
  by exact (rl_lyF_eq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc1 Sc1 W1 mem1 md1 k HJ0 HJ1).
assert (HlyF3 : ly_F ly3 = ly_F lyc1)
  by exact (rl_lyF_eq STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem1 md1 k ly3 S3 Wt mem3 md3 k HJ1 HJ3).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
assert (Hceil2 : alloc_ceiling <= spZ regs - TSB_CH_STK) by lia.
assert (HRlo : alloc_ceiling <= spZ regs + 88) by lia.
assert (Hwrlen : forall j, 0 <= j <= N -> Z.of_nat (length (rl_wrl j)) = rl_cnt j).
{ intros j Hj. unfold rl_wrl. rewrite length_firstn. unfold rl_cnt in *. lia. }
destruct HCASE as [(Hge & Vov & KT) | (Hlt & Vn & Vbyte & KT)];
rewrite Gsp2 in KT; destruct KT as (KT1 & KT2 & KT3 & KT4 & KT5 & KT6).
all: rs_hide_all.
- assert (HnF : rl_nn (jj + 1) = rl_nn jj) by (unfold rl_nn, rl_cnt in *; rs_lia).
  assert (HoF : rl_ovv (jj + 1) = 1)
    by (unfold rl_ovv; replace (n0 + (jj + 1) <=? 47) with false
          by (symmetry; apply Z.leb_gt; unfold rl_nn, rl_cnt in *; rs_lia); reflexivity).
  assert (HcF : rl_cnt (jj + 1) = rl_cnt jj) by (unfold rl_nn in HnF; rs_lia).
  assert (HwF : rl_wrl (jj + 1) = rl_wrl jj) by (unfold rl_wrl; rewrite HcF; reflexivity).
  assert (HKEEP : forall s, 0 <= s < 2 ^ 64 -> ~ (spZ regs - TSB_CH_STK <= s < spZ regs) ->
     ~ (spZ regs + 88 + 24 <= s < spZ regs + 88 + 28) ->
     aview SEGS (w_H Wt) mem3 s = aview SEGS (w_H W1) mem2 s)
    by (intros s Hz1 Hz2 Hz3; apply KT1; [exact Hz1 | exact Hz2 | cbv beta; rs_lia]).
  eapply SRr_bind.
  { exact (HTAIL STK sp0 FP ly S W0 mem0 md0 own ly3 S3 Wt mem3 md3 k regs3 HJ3 G20c G24c). }
  cbv beta. intros Wf cf _ (-> & regs4 & mem4 & md4 & -> & HJ4 & Hmem4 & G20d & G24d & HKt).
  apply SRr_ret. unfold rl_inv.
  exists ly3, S3, regs4, mem4, md4.
  split; [reflexivity|].
  split; [exact HJ4|].
  split; [rewrite Hfr3; exact Hfr1|].
  split; [rewrite Hbl3; exact Hbl1|].
  split; [exact (rl_rod_eqv Wt mem3 mem4 ltac:(intros x; symmetry; apply Hmem4)
            (rl_rod_kept lyc1 Sc1 W1 mem2 Wt mem3 (spZ regs) _
               (conj KT1 (conj KT2 (conj KT3 (conj KT4 (conj KT5 KT6))))) Hro2))|].
  split; [exact (rl_keep_chain regs regs2 regs3 regs4
            (rl_keep_trans2 regs regs1 regs2 RLCL HK1 HKh) HPRES3 HKt)|].
  split; [rewrite G20d; reflexivity|].
  split.
  { apply (rl_rec_eqv STK sp0 FP ly S own ly3 S3 Wt mem3 mem4 _ _ _ _ _ _
      ltac:(intros x; symmetry; apply Hmem4)).
    unfold rbn_lrec.
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
    split; [exact R5|]. split; [exact R6|]. split; [exact R7|]. split; [exact R8|].
    split; [unfold rl_nn, rl_cnt; rs_lia|]. split; [unfold rl_nn, rl_cnt; rs_lia|].
    split; [rewrite HoF; rs_lia|].
    split; [exact (rl_vm_transfer W1 Wt mem2 mem3 _ (spZ regs) _ 8 _ V0 HKEEP ltac:(intros kk Hk; repeat split; rs_lia))|].
    split; [exact (rl_vm_transfer W1 Wt mem2 mem3 _ (spZ regs) _ 8 _ V8 HKEEP ltac:(intros kk Hk; repeat split; rs_lia))|].
    split; [rewrite HnF; exact (rl_vm_transfer W1 Wt mem2 mem3 _ (spZ regs) _ 8 _ V16 HKEEP
              ltac:(intros kk Hk; repeat split; rs_lia))|].
    split; [rewrite HoF; exact Vov|].
    split.
    { apply (rl_ra_transfer W1 Wt mem2 mem3 _ (spZ regs) _ 28 RRA HKEEP).
      intros x Hx. pose proof (rl_shadow_bound (spZ regs + 88) 28 x ltac:(rs_lia) R4 Hx) as Hsb.
      repeat split; rs_lia. }
    split.
    { apply (rl_shv_transfer W1 Wt mem2 mem3 _ (spZ regs) _ 28 RSV HKEEP).
      intros s Hs.
      pose proof (rl_shadow_bound (spZ regs + 88) 28 (spZ regs + 88) ltac:(rs_lia) R4 ltac:(rs_lia)) as Hb1.
      pose proof (rl_shadow_bound (spZ regs + 88) 28 (spZ regs + 88 + 27) ltac:(rs_lia) R4 ltac:(rs_lia)) as Hb2.
      unfold shadow_addr in Hs.
      pose proof (Z.mul_div_le (SHADOW_OFF + (spZ regs + 88) / 8) 8 ltac:(rs_lia)) as M1.
      pose proof (Z.mul_div_le (SHADOW_OFF + (spZ regs + 88 + 28 - 1) / 8) 8 ltac:(rs_lia)) as M2.
      pose proof (Z.div_le_mono (SHADOW_OFF + (spZ regs + 88 + 28 - 1) / 8)
        (SHADOW_OFF + (spZ regs + 88 + 28 - 1) / 8) 8 ltac:(rs_lia) ltac:(rs_lia)) as M3.
      assert (Hd1 : 0 <= (SHADOW_OFF + (spZ regs + 88) / 8) / 8) by (apply Z.div_pos; rs_lia).
      repeat split; rs_lia. }
    intros a Ha. split.
    { rewrite Hbl3. apply (rl_awr_lyc STK sp0 FP (ablocks B ly S) (ablocks B lyc1 Sc1) lyc1 ly3 own a HlyF3).
      exact (proj1 (RWR a Ha)). }
    exact (proj1 (awr_byte_present SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own ly3 S3 Wt mem3 md3 k a HJ3
      ltac:(rewrite Hbl3;
            apply (rl_awr_lyc STK sp0 FP (ablocks B ly S) (ablocks B lyc1 Sc1) lyc1 ly3 own a HlyF3);
            exact (proj1 (RWR a Ha))))). }
  split.
  { apply (rl_buf_eqv STK sp0 FP ly S own ly3 S3 Wt mem3 mem4 _ _ _ _
      ltac:(intros x; symmetry; apply Hmem4)).
    unfold rbn_lbuf.
    split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|].
    split; [exact U5|]. split; [exact U6|]. split; [exact U7|].
    split.
    { apply (rl_ra_transfer W1 Wt mem2 mem3 _ (spZ regs) _ 48 URA HKEEP).
      intros x Hx. pose proof (rl_shadow_bound D 48 x ltac:(rs_lia) U4 Hx) as Hsb. repeat split; rs_lia. }
    split.
    { apply (rl_shv_transfer W1 Wt mem2 mem3 _ (spZ regs) _ 48 USV HKEEP).
      intros s Hs.
      pose proof (rl_shadow_bound D 48 D ltac:(rs_lia) U4 ltac:(rs_lia)) as Hb1.
      pose proof (rl_shadow_bound D 48 (D + 47) ltac:(rs_lia) U4 ltac:(rs_lia)) as Hb2.
      unfold shadow_addr in Hs.
      pose proof (Z.mul_div_le (SHADOW_OFF + D / 8) 8 ltac:(rs_lia)) as M1.
      pose proof (Z.mul_div_le (SHADOW_OFF + (D + 48 - 1) / 8) 8 ltac:(rs_lia)) as M2.
      assert (Hd1 : 0 <= (SHADOW_OFF + D / 8) / 8) by (apply Z.div_pos; rs_lia).
      assert (Hd2 : (SHADOW_OFF + (D + 48 - 1) / 8) / 8 * 8 <= SHADOW_OFF + (D + 48 - 1) / 8) by rs_lia.
      repeat split; rs_lia. }
    intros a Ha. split.
    { rewrite Hbl3. apply (rl_awr_lyc STK sp0 FP (ablocks B ly S) (ablocks B lyc1 Sc1) lyc1 ly3 own a HlyF3).
      exact (proj1 (UWR a Ha)). }
    exact (proj1 (awr_byte_present SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own ly3 S3 Wt mem3 md3 k a HJ3
      ltac:(rewrite Hbl3;
            apply (rl_awr_lyc STK sp0 FP (ablocks B ly S) (ablocks B lyc1 Sc1) lyc1 ly3 own a HlyF3);
            exact (proj1 (UWR a Ha))))). }
  split.
  { apply (rl_src_eqv Wt mem3 mem4 lit (l ++ [0]) ltac:(intros x; symmetry; apply Hmem4)).
    unfold rbn_lsrc. rewrite Hlen1.
    split.
    { apply (garr8_aview_kept SEGS (w_H W1) (w_H Wt) mem2 mem3 lit (l ++ [0])); [|exact HGs2].
      intros x Hx. rewrite Hlen1 in Hx. apply HKEEP; [rs_lia | rs_lia | rs_lia]. }
    split; [exact HP02|]. split; [exact HP632|]. split; [exact HP472|].
    apply (rl_ra_transfer W1 Wt mem2 mem3 _ (spZ regs) _ (N + 1) HRAs2 HKEEP).
    intros x Hx.
    assert (Hamr : amem_range lit (N + 1)).
    { unfold amem_range. left. unfold IMG_LO, IMG_TOP in *. rewrite C5. rs_lia. }
    pose proof (rl_shadow_bound lit (N + 1) x ltac:(unfold IMG_LO in *; rs_lia) Hamr ltac:(rs_lia)) as Hsb.
    repeat split; rs_lia. }
  split; [rewrite HwF; apply (rl_garr_eqv Wt mem3 mem4 _ _ ltac:(intros x; symmetry; apply Hmem4));
          apply (garr8_aview_kept SEGS (w_H W1) (w_H Wt) mem2 mem3 (D + n0) (rl_wrl jj)); [|exact HG2];
          intros x Hx; rewrite (Hwrlen jj ltac:(rs_lia)) in Hx; apply HKEEP; unfold rl_cnt in *; rs_lia|].
  apply (rl_kept_eqv lyc Sc W memc Wt mem3 mem4 (spZ regs) (rl_Eset (jj + 1))
    ltac:(intros x; symmetry; apply Hmem4)).
  apply (rl_kept_mono lyc Sc W memc Wt mem3 (spZ regs)
    (fun a => rl_Eset jj a \/ (fun a0 => spZ regs + 88 + 24 <= a0 < spZ regs + 88 + 28) a)).
  { cbv beta. unfold rl_Eset. rewrite HwF. intros a [Ha | Ha]; [exact Ha | left; rs_lia]. }
  apply (rl_kept_trans lyc Sc lyc1 Sc1 W memc W1 mem2 Wt mem3 (spZ regs) (rl_Eset jj) _
    Hfr1 Hbl1 HlyF1 KEPT2 (conj KT1 (conj KT2 (conj KT3 (conj KT4 (conj KT5 KT6)))))).
- assert (Hjlt : n0 + jj < 47) by (unfold rl_nn, rl_cnt in Hlt; rs_lia).
  assert (HcF : rl_cnt (jj + 1) = rl_cnt jj + 1) by (unfold rl_cnt; rs_lia).
  assert (HnF : rl_nn (jj + 1) = rl_nn jj + 1) by (unfold rl_nn; rs_lia).
  assert (HoF : rl_ovv (jj + 1) = rl_ovv jj)
    by (unfold rl_ovv;
        replace (n0 + (jj + 1) <=? 47) with true by (symmetry; apply Z.leb_le; rs_lia);
        replace (n0 + jj <=? 47) with true by (symmetry; apply Z.leb_le; rs_lia); reflexivity).
  assert (HwF : rl_wrl (jj + 1) = rl_wrl jj ++ [cc]).
  { assert (Hcceq : cc = nth (Z.to_nat jj) l 0) by reflexivity.
    assert (Hc0 : rl_cnt jj = jj) by (unfold rl_cnt; rs_lia).
    assert (Hc1 : rl_cnt (jj + 1) = jj + 1) by (unfold rl_cnt; rs_lia).
    unfold rl_wrl. rewrite Hc0, Hc1, Hcceq.
    apply (rl_firstn_Z l jj 0 ltac:(rs_lia) ltac:(rs_lia)). }
  assert (Hln : Z.of_nat (length (rl_wrl jj)) = rl_cnt jj) by (apply Hwrlen; rs_lia).
  assert (Hln1 : Z.of_nat (length (rl_wrl (jj + 1))) = rl_cnt jj + 1)
    by (rewrite (Hwrlen (jj + 1) ltac:(rs_lia)); exact HcF).
  assert (Hcb : 0 <= rl_cnt jj <= 47 - n0) by (unfold rl_cnt; rs_lia).
  assert (Hnb : rl_nn jj = n0 + rl_cnt jj) by reflexivity.
  assert (HDap : forall s, kLowMemEnd <= s < kHighShadowEnd -> ~ (D <= s < D + 48)).
  { intros s Hs Hc'. unfold in_app, kLowShadowBeg, ASAN_CEIL in U3.
    destruct U3 as (Hd4096 & [Hlo | (Hhi1 & Hhi2)]); rewrite ?C2, ?C3, ?C5 in *; rs_lia. }
  replace (cc mod 256) with cc in Vbyte by (symmetry; apply Z.mod_small; rs_lia).
  eapply SRr_bind.
  { exact (HTAIL STK sp0 FP ly S W0 mem0 md0 own ly3 S3 Wt mem3 md3 k regs3 HJ3 G20c G24c). }
  cbv beta. intros Wf cf _ (-> & regs4 & mem4 & md4 & -> & HJ4 & Hmem4 & G20d & G24d & HKt).
  apply SRr_ret. unfold rl_inv.
  exists ly3, S3, regs4, mem4, md4.
  split; [reflexivity|].
  split; [exact HJ4|].
  split; [rewrite Hfr3; exact Hfr1|].
  split; [rewrite Hbl3; exact Hbl1|].
  split; [exact (rl_rod_eqv Wt mem3 mem4 ltac:(intros x; symmetry; apply Hmem4)
            (rl_rod_kept lyc1 Sc1 W1 mem2 Wt mem3 (spZ regs) _
               (conj KT1 (conj KT2 (conj KT3 (conj KT4 (conj KT5 KT6))))) Hro2))|].
  split; [exact (rl_keep_chain regs regs2 regs3 regs4
            (rl_keep_trans2 regs regs1 regs2 RLCL HK1 HKh) HPRES3 HKt)|].
  split; [rewrite G20d; reflexivity|].
  split.
  { apply (rl_rec_eqv STK sp0 FP ly S own ly3 S3 Wt mem3 mem4 _ _ _ _ _ _
      ltac:(intros x; symmetry; apply Hmem4)).
    unfold rbn_lrec.
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
    split; [exact R5|]. split; [exact R6|]. split; [exact R7|]. split; [exact R8|].
    split; [unfold rl_nn, rl_cnt; rs_lia|]. split; [unfold rl_nn, rl_cnt; rs_lia|].
    split; [rewrite HoF; exact R11|].
    split.
    { apply (rl_vm_transfer W1 Wt mem2 mem3 _ (spZ regs) _ 8 _ V0 KT1).
      intros kk Hk. split; [rs_lia|]. split; [rs_lia|]. cbv beta. intros [Hqq | Hqq]; rs_lia. }
    split.
    { apply (rl_vm_transfer W1 Wt mem2 mem3 _ (spZ regs) _ 8 _ V8 KT1).
      intros kk Hk. split; [rs_lia|]. split; [rs_lia|]. cbv beta. intros [Hqq | Hqq]; rs_lia. }
    split; [rewrite HnF; exact Vn|].
    split.
    { rewrite HoF. apply (rl_vm_transfer W1 Wt mem2 mem3 _ (spZ regs) _ 4 _ V24 KT1).
      intros kk Hk. split; [rs_lia|]. split; [rs_lia|]. cbv beta. intros [Hqq | Hqq]; rs_lia. }
    split.
    { apply (rl_ra_transfer W1 Wt mem2 mem3 _ (spZ regs) _ 28 RRA KT1).
      intros x Hx. pose proof (rl_shadow_bound (spZ regs + 88) 28 x ltac:(rs_lia) R4 Hx) as Hsb.
      split; [rs_lia|]. split; [rs_lia|]. cbv beta. intros [Hqq | Hqq];
      [rs_lia | exact (HDap (SHADOW_OFF + x / 8) ltac:(rs_lia) ltac:(unfold rl_nn, rl_cnt in *; rs_lia))]. }
    split.
    { apply (rl_shv_transfer W1 Wt mem2 mem3 _ (spZ regs) _ 28 RSV KT1).
      intros s Hs.
      pose proof (rl_shadow_bound (spZ regs + 88) 28 (spZ regs + 88) ltac:(rs_lia) R4 ltac:(rs_lia)) as Hb1.
      pose proof (rl_shadow_bound (spZ regs + 88) 28 (spZ regs + 88 + 27) ltac:(rs_lia) R4 ltac:(rs_lia)) as Hb2.
      unfold shadow_addr in Hs.
      pose proof (Z.mul_div_le (SHADOW_OFF + (spZ regs + 88) / 8) 8 ltac:(rs_lia)) as M1.
      pose proof (Z.mul_div_le (SHADOW_OFF + (spZ regs + 88 + 28 - 1) / 8) 8 ltac:(rs_lia)) as M2.
      assert (Hd1 : 0 <= (SHADOW_OFF + (spZ regs + 88) / 8) / 8) by (apply Z.div_pos; rs_lia).
      split; [rs_lia|]. split; [rs_lia|]. cbv beta. intros [Hqq | Hqq];
      [rs_lia | exact (HDap s ltac:(rs_lia) ltac:(unfold rl_nn, rl_cnt in *; rs_lia))]. }
    intros a Ha. split.
    { rewrite Hbl3. apply (rl_awr_lyc STK sp0 FP (ablocks B ly S) (ablocks B lyc1 Sc1) lyc1 ly3 own a HlyF3).
      exact (proj1 (RWR a Ha)). }
    exact (proj1 (awr_byte_present SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own ly3 S3 Wt mem3 md3 k a HJ3
      ltac:(rewrite Hbl3;
            apply (rl_awr_lyc STK sp0 FP (ablocks B ly S) (ablocks B lyc1 Sc1) lyc1 ly3 own a HlyF3);
            exact (proj1 (RWR a Ha))))). }
  split.
  { apply (rl_buf_eqv STK sp0 FP ly S own ly3 S3 Wt mem3 mem4 _ _ _ _
      ltac:(intros x; symmetry; apply Hmem4)).
    unfold rbn_lbuf.
    split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|].
    split; [exact U5|]. split; [exact U6|]. split; [exact U7|].
    split.
    { apply (rl_ra_transfer W1 Wt mem2 mem3 _ (spZ regs) _ 48 URA KT1).
      intros x Hx. pose proof (rl_shadow_bound D 48 x ltac:(rs_lia) U4 Hx) as Hsb.
      split; [rs_lia|]. split; [rs_lia|]. cbv beta. intros [Hqq | Hqq];
      [rs_lia | exact (HDap (SHADOW_OFF + x / 8) ltac:(rs_lia) ltac:(unfold rl_nn, rl_cnt in *; rs_lia))]. }
    split.
    { apply (rl_shv_transfer W1 Wt mem2 mem3 _ (spZ regs) _ 48 USV KT1).
      intros s Hs.
      pose proof (rl_shadow_bound D 48 D ltac:(rs_lia) U4 ltac:(rs_lia)) as Hb1.
      pose proof (rl_shadow_bound D 48 (D + 47) ltac:(rs_lia) U4 ltac:(rs_lia)) as Hb2.
      unfold shadow_addr in Hs.
      pose proof (Z.mul_div_le (SHADOW_OFF + D / 8) 8 ltac:(rs_lia)) as M1.
      pose proof (Z.mul_div_le (SHADOW_OFF + (D + 48 - 1) / 8) 8 ltac:(rs_lia)) as M2.
      assert (Hd1 : 0 <= (SHADOW_OFF + D / 8) / 8) by (apply Z.div_pos; rs_lia).
      split; [rs_lia|]. split; [rs_lia|]. cbv beta. intros [Hqq | Hqq];
      [rs_lia | exact (HDap s ltac:(rs_lia) ltac:(unfold rl_nn, rl_cnt in *; rs_lia))]. }
    intros a Ha. split.
    { rewrite Hbl3. apply (rl_awr_lyc STK sp0 FP (ablocks B ly S) (ablocks B lyc1 Sc1) lyc1 ly3 own a HlyF3).
      exact (proj1 (UWR a Ha)). }
    exact (proj1 (awr_byte_present SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own ly3 S3 Wt mem3 md3 k a HJ3
      ltac:(rewrite Hbl3;
            apply (rl_awr_lyc STK sp0 FP (ablocks B ly S) (ablocks B lyc1 Sc1) lyc1 ly3 own a HlyF3);
            exact (proj1 (UWR a Ha))))). }
  split.
  { apply (rl_src_eqv Wt mem3 mem4 lit (l ++ [0]) ltac:(intros x; symmetry; apply Hmem4)).
    unfold rbn_lsrc. rewrite Hlen1.
    split.
    { apply (garr8_aview_kept SEGS (w_H W1) (w_H Wt) mem2 mem3 lit (l ++ [0])); [|exact HGs2].
      intros x Hx. rewrite Hlen1 in Hx. apply KT1; [rs_lia | rs_lia | cbv beta; intros [Hqq | Hqq]; rs_lia]. }
    split; [exact HP02|]. split; [exact HP632|]. split; [exact HP472|].
    apply (rl_ra_transfer W1 Wt mem2 mem3 _ (spZ regs) _ (N + 1) HRAs2 KT1).
    intros x Hx.
    assert (Hamr : amem_range lit (N + 1)).
    { unfold amem_range. left. unfold IMG_LO, IMG_TOP in *. rewrite C5. rs_lia. }
    pose proof (rl_shadow_bound lit (N + 1) x ltac:(unfold IMG_LO in *; rs_lia) Hamr ltac:(rs_lia)) as Hsb.
    split; [rs_lia|]. split; [rs_lia|]. cbv beta. intros [Hqq | Hqq];
    [rs_lia | exact (HDap (SHADOW_OFF + x / 8) ltac:(rs_lia) ltac:(unfold rl_nn, rl_cnt in *; rs_lia))]. }
  split.
  { rewrite HwF. apply (rl_garr_eqv Wt mem3 mem4 _ _ ltac:(intros x; symmetry; apply Hmem4)).
    apply rl_garr8_snoc; [| | rs_lia].
    - apply (garr8_aview_kept SEGS (w_H W1) (w_H Wt) mem2 mem3 (D + n0) (rl_wrl jj)); [|exact HG2].
      intros x Hx. rewrite Hln in Hx. apply KT1;
      [rs_lia | unfold rl_nn, rl_cnt in *; rs_lia | cbv beta; intros [Hqq | Hqq]; unfold rl_nn, rl_cnt in *; rs_lia].
    - rewrite Hln. replace (D + n0 + rl_cnt jj) with (D + rl_nn jj) by (unfold rl_nn; rs_lia). exact Vbyte. }
  apply (rl_kept_eqv lyc Sc W memc Wt mem3 mem4 (spZ regs) (rl_Eset (jj + 1))
    ltac:(intros x; symmetry; apply Hmem4)).
  apply (rl_kept_mono lyc Sc W memc Wt mem3 (spZ regs)
    (fun a => rl_Eset jj a \/ (fun a0 => spZ regs + 88 + 16 <= a0 < spZ regs + 88 + 24 \/
                                         a0 = D + rl_nn jj) a)).
  { cbv beta. unfold rl_Eset. rewrite Hln, Hln1. intros a [[Ha | Ha] | [Ha | Ha]];
    [left; rs_lia | right; rs_lia | left; rs_lia | right; unfold rl_nn in Ha; rs_lia]. }
  apply (rl_kept_trans lyc Sc lyc1 Sc1 W memc W1 mem2 Wt mem3 (spZ regs) (rl_Eset jj) _
    Hfr1 Hbl1 HlyF1 KEPT2 (conj KT1 (conj KT2 (conj KT3 (conj KT4 (conj KT5 KT6)))))).
Qed.
Hypothesis HR20 : getr regs 20 = w64 0.
Variables (Loff LXoff retoff : Z).
Hypothesis HROKt : YK0s.ret_ok (w64 (BASE + retoff)).
Hypothesis HRA4t : 4096 <= BASE + retoff.
Hypothesis HRBt : 0 <= BASE + retoff < 2 ^ 64.
Hypothesis HHEADS : forall jj, 0 <= jj < N -> rl_head_stmt Loff jj (nth (Z.to_nat jj) l 0) retoff.
Hypothesis HTAILM : forall jj, 0 <= jj < N - 1 -> rl_tail_stmt retoff Loff jj N.
Hypothesis HTAILE : rl_tail_stmt retoff LXoff (N - 1) N.
Lemma rl_base : rl_inv Loff 0 W (cfg_at (fx := fx) SEGS (BASE + Loff) regs memc mdc).
Proof.
pose proof HCX as (HJ0 & HRO0 & Hgp & Htp & Hs1 & Hs6 & Hsp16 & Hbudget & Hsple).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & _).
exists lyc, Sc, regs, memc, mdc.
split; [reflexivity|].
split; [exact HJ0|].
split; [reflexivity|]. split; [reflexivity|].
split; [exact HRO0|].
split; [intros z Hz Hn; reflexivity|].
split; [exact HR20|].
split.
{ replace (rl_nn 0) with n0 by (unfold rl_nn, rl_cnt; lia).
  replace (rl_ovv 0) with ov0
    by (unfold rl_ovv; replace (n0 + 0 <=? 47) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
  exact HREC. }
split; [exact HBUF|].
split; [exact HSRC|].
split.
{ replace (rl_wrl 0) with (@nil Z)
    by (unfold rl_wrl; replace (Z.to_nat (rl_cnt 0)) with 0%nat by (unfold rl_cnt; lia); reflexivity).
  apply garr8_nil. }
apply tsb_ch_kept_refl. intros a Ha. apply Hpres0. lia.
Qed.
Lemma rl_chain : forall m : nat, Z.of_nat m <= N - 1 ->
  forall W1 c1, rl_inv Loff 0 W1 c1 -> SRr SEGS W1 c1 (rl_inv Loff (Z.of_nat m)).
Proof.
induction m as [|m IH]; intros Hm W1 c1 Hinv.
- replace (Z.of_nat 0) with 0 by reflexivity. apply SRr_ret. exact Hinv.
- eapply SRr_bind; [exact (IH ltac:(rewrite Nat2Z.inj_succ in Hm; lia) W1 c1 Hinv)|].
  intros W2 c2 _ Hinv2.
  rewrite Nat2Z.inj_succ.
  replace (Z.succ (Z.of_nat m)) with (Z.of_nat m + 1) by lia.
  exact (rl_step (Z.of_nat m) Loff retoff Loff
    ltac:(rewrite Nat2Z.inj_succ in Hm; lia) HROKt HRA4t HRBt
    (HHEADS (Z.of_nat m) ltac:(rewrite Nat2Z.inj_succ in Hm; lia))
    (HTAILM (Z.of_nat m) ltac:(rewrite Nat2Z.inj_succ in Hm; lia)) W2 c2 Hinv2).
Qed.
Lemma rl_all : SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + Loff) regs memc mdc) (rl_inv LXoff N).
Proof.
assert (HNe : Z.of_nat (Z.to_nat (N - 1)) = N - 1) by lia.
eapply SRr_bind; [exact (rl_chain (Z.to_nat (N - 1)) ltac:(lia) W _ rl_base)|].
intros W2 c2 _ Hinv2. rewrite HNe in Hinv2.
replace (rl_inv LXoff N) with (rl_inv LXoff (N - 1 + 1)) by (f_equal; lia).
exact (rl_step (N - 1) Loff retoff LXoff ltac:(lia) HROKt HRA4t HRBt
  (HHEADS (N - 1) ltac:(lia)) HTAILE W2 c2 Hinv2).
Qed.
Lemma rl_post_of : forall exr, LXoff = AF_both3_reac_box_name + exr ->
  forall W2 c2, rl_inv LXoff N W2 c2 ->
  rbn_lpost B fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs exr RLCL
    (spZ regs + 88) D n0 (rl_nn N) (rl_ovv N) (rl_wrl N) W2 c2.
Proof.
intros exr Hexr W2 c2 (lyc2 & Sc2 & regs2 & mem2 & md2 & Hc & HJ & Hfr & Hbl & Hro & HK & H20 &
  HRECi & HBUFi & HSRCi & HGi & HKEPTi).
exists lyc2, Sc2, regs2, mem2, md2.
split; [rewrite Hc; unfold cfg_at; f_equal; f_equal; f_equal; rewrite Hexr; lia|].
split; [exact HJ|]. split; [exact Hfr|]. split; [exact Hbl|]. split; [exact Hro|].
split; [exact HK|].
destruct HRECi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V16 & V24 & _).
split; [exact V16|]. split; [exact V24|].
split; [exact HGi|].
exact HKEPTi.
Qed.
Lemma rl_final : forall (Lrel exr : Z) (nF ovF : Z) (wr : list Z),
  Loff = AF_both3_reac_box_name + Lrel ->
  LXoff = AF_both3_reac_box_name + exr ->
  rl_nn N = nF -> rl_ovv N = ovF -> rl_wrl N = wr ->
  SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + AF_both3_reac_box_name + Lrel) regs memc mdc)
    (rbn_lpost B fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs exr rbn_cl5
       (spZ regs + 88) D n0 nF ovF wr).
Proof.
intros Lrel exr nF ovF wr HL HX Hn Ho Hw.
replace (BASE + AF_both3_reac_box_name + Lrel) with (BASE + Loff) by (rewrite HL; lia).
eapply SRr_bind; [exact rl_all|].
intros W2 c2 _ Hinv. apply SRr_ret.
rewrite <- Hn, <- Ho, <- Hw.
exact (rl_post_of exr HX W2 c2 Hinv).
Qed.
End S.

Lemma rl5_fits_at : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) D n0 ov0,
  n0 + 2 <= 47 ->
  rbn_lcx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 n0 ov0 ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 ->
  rbn_lsrc W memc (VAL (A_OBJ 28)) (rbn_lit5 ++ [0]) -> VAL (A_OBJ 28) mod 8 = 0 ->
  rbn_lsep (spZ regs) (spZ regs + 88) D 48 (VAL (A_OBJ 28)) 3 ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 20 = w64 0 -> getr regs 21 = w64 (VAL (A_OBJ 28)) -> getr regs 24 = w64 2 ->
  SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + AF_both3_reac_box_name + RBN_L5) regs memc mdc)
    (rbn_lpost B fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L5X rbn_cl5
       (spZ regs + 88) D n0 (n0 + 2) ov0 rbn_lit5).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 Hg
  HCX HREC HBUF HSRC HAL HSEP HN0 HOV0 G20 G21 G24.
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof pa_base_lo as HBLO. unfold YImgTop.IMG_LO in HBLO.
pose proof (pa_obj_img_all 28%nat ltac:(cbv [tfib_nobj]; lia)) as (HOa & HOb).
eapply rl_final with (N := 2) (l := rbn_lit5) (lit := VAL (A_OBJ 28)) (ov0 := ov0)
  (Loff := AF_both3_reac_box_name + RBN_L5) (LXoff := AF_both3_reac_box_name + RBN_L5X)
  (retoff := AF_both3_reac_box_name + RBN_L5 + 32).
all: first
  [ solve [exact HCX] | solve [exact HREC] | solve [exact HBUF] | solve [exact HSRC] | solve [exact HAL]
  | solve [exact HSEP] | solve [exact HN0] | solve [exact HOV0] | solve [exact G20] | solve [exact G21]
  | solve [exact G24] | solve [exact HOa] | solve [exact HOb]
  | solve [intros jj Hjj; destruct (Z.eq_dec jj 0) as [-> | ?]; [exact rl5_head0 |]; destruct (Z.eq_dec jj 1) as [-> | ?]; [exact rl5_head1 |]; exfalso; lia]
  | solve [intros jj Hjj; assert (jj = 0) as -> by lia; exact rl5_tail0]
  | solve [exact rl5_tail1]
  | solve [unfold w64; apply ret_ok_codeptr_v; cbv [AF_both3_reac_box_name RBN_L5]; [lia | reflexivity]]
  | solve [unfold rbn_lit5; repeat apply Forall_cons; try apply Forall_nil; cbv beta; lia]
  | solve [reflexivity]
  | solve [unfold rl_nn, rl_cnt; lia]
  | solve [unfold rl_ovv; replace (n0 + 2 <=? 47) with true by (symmetry; apply Z.leb_le; lia); reflexivity]
  | solve [unfold rl_wrl; replace (rl_cnt n0 2) with 2 by (unfold rl_cnt; lia); reflexivity]
  | solve [cbv [AF_both3_reac_box_name RBN_L5]; lia]
  | solve [unfold IMG_LO, IMG_TOP, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia]
  | solve [lia] ].
Qed.

Lemma rl5_ovf_at : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) D n0 ov0,
  47 < n0 + 2 ->
  rbn_lcx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 n0 ov0 ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 ->
  rbn_lsrc W memc (VAL (A_OBJ 28)) (rbn_lit5 ++ [0]) -> VAL (A_OBJ 28) mod 8 = 0 ->
  rbn_lsep (spZ regs) (spZ regs + 88) D 48 (VAL (A_OBJ 28)) 3 ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 20 = w64 0 -> getr regs 21 = w64 (VAL (A_OBJ 28)) -> getr regs 24 = w64 2 ->
  SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + AF_both3_reac_box_name + RBN_L5) regs memc mdc)
    (rbn_lpost B fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L5X rbn_cl5
       (spZ regs + 88) D n0 47 1 (firstn (Z.to_nat (47 - n0)) rbn_lit5)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 Hg
  HCX HREC HBUF HSRC HAL HSEP HN0 HOV0 G20 G21 G24.
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof pa_base_lo as HBLO. unfold YImgTop.IMG_LO in HBLO.
pose proof (pa_obj_img_all 28%nat ltac:(cbv [tfib_nobj]; lia)) as (HOa & HOb).
eapply rl_final with (N := 2) (l := rbn_lit5) (lit := VAL (A_OBJ 28)) (ov0 := ov0)
  (Loff := AF_both3_reac_box_name + RBN_L5) (LXoff := AF_both3_reac_box_name + RBN_L5X)
  (retoff := AF_both3_reac_box_name + RBN_L5 + 32).
all: first
  [ solve [exact HCX] | solve [exact HREC] | solve [exact HBUF] | solve [exact HSRC] | solve [exact HAL]
  | solve [exact HSEP] | solve [exact HN0] | solve [exact HOV0] | solve [exact G20] | solve [exact G21]
  | solve [exact G24] | solve [exact HOa] | solve [exact HOb]
  | solve [intros jj Hjj; destruct (Z.eq_dec jj 0) as [-> | ?]; [exact rl5_head0 |]; destruct (Z.eq_dec jj 1) as [-> | ?]; [exact rl5_head1 |]; exfalso; lia]
  | solve [intros jj Hjj; assert (jj = 0) as -> by lia; exact rl5_tail0]
  | solve [exact rl5_tail1]
  | solve [unfold w64; apply ret_ok_codeptr_v; cbv [AF_both3_reac_box_name RBN_L5]; [lia | reflexivity]]
  | solve [unfold rbn_lit5; repeat apply Forall_cons; try apply Forall_nil; cbv beta; lia]
  | solve [reflexivity]
  | solve [unfold rl_nn, rl_cnt; lia]
  | solve [unfold rl_ovv; replace (n0 + 2 <=? 47) with false by (symmetry; apply Z.leb_gt; lia); reflexivity]
  | solve [unfold rl_wrl; replace (rl_cnt n0 2) with (47 - n0) by (unfold rl_cnt; lia); reflexivity]
  | solve [cbv [AF_both3_reac_box_name RBN_L5]; lia]
  | solve [unfold IMG_LO, IMG_TOP, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia]
  | solve [lia] ].
Qed.

Lemma rl6_fits_at : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) D n0 ov0,
  n0 + 6 <= 47 ->
  rbn_lcx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 n0 ov0 ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 ->
  rbn_lsrc W memc (VAL (A_OBJ 29)) (rbn_lit6 ++ [0]) -> VAL (A_OBJ 29) mod 8 = 0 ->
  rbn_lsep (spZ regs) (spZ regs + 88) D 48 (VAL (A_OBJ 29)) 7 ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 20 = w64 0 -> getr regs 21 = w64 (VAL (A_OBJ 29)) -> getr regs 24 = w64 6 ->
  SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + AF_both3_reac_box_name + RBN_L6) regs memc mdc)
    (rbn_lpost B fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L6X rbn_cl5
       (spZ regs + 88) D n0 (n0 + 6) ov0 rbn_lit6).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 Hg
  HCX HREC HBUF HSRC HAL HSEP HN0 HOV0 G20 G21 G24.
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof pa_base_lo as HBLO. unfold YImgTop.IMG_LO in HBLO.
pose proof (pa_obj_img_all 29%nat ltac:(cbv [tfib_nobj]; lia)) as (HOa & HOb).
eapply rl_final with (N := 6) (l := rbn_lit6) (lit := VAL (A_OBJ 29)) (ov0 := ov0)
  (Loff := AF_both3_reac_box_name + RBN_L6) (LXoff := AF_both3_reac_box_name + RBN_L6X)
  (retoff := AF_both3_reac_box_name + RBN_L6 + 32).
all: first
  [ solve [exact HCX] | solve [exact HREC] | solve [exact HBUF] | solve [exact HSRC] | solve [exact HAL]
  | solve [exact HSEP] | solve [exact HN0] | solve [exact HOV0] | solve [exact G20] | solve [exact G21]
  | solve [exact G24] | solve [exact HOa] | solve [exact HOb]
  | solve [intros jj Hjj; destruct (Z.eq_dec jj 0) as [-> | ?]; [exact rl6_head0 |]; destruct (Z.eq_dec jj 1) as [-> | ?]; [exact rl6_head1 |]; destruct (Z.eq_dec jj 2) as [-> | ?]; [exact rl6_head2 |]; destruct (Z.eq_dec jj 3) as [-> | ?]; [exact rl6_head3 |]; destruct (Z.eq_dec jj 4) as [-> | ?]; [exact rl6_head4 |]; destruct (Z.eq_dec jj 5) as [-> | ?]; [exact rl6_head5 |]; exfalso; lia]
  | solve [intros jj Hjj; destruct (Z.eq_dec jj 0) as [-> | ?]; [exact rl6_tail0 |]; destruct (Z.eq_dec jj 1) as [-> | ?]; [exact rl6_tail1 |]; destruct (Z.eq_dec jj 2) as [-> | ?]; [exact rl6_tail2 |]; destruct (Z.eq_dec jj 3) as [-> | ?]; [exact rl6_tail3 |]; destruct (Z.eq_dec jj 4) as [-> | ?]; [exact rl6_tail4 |]; exfalso; lia]
  | solve [exact rl6_tail5]
  | solve [unfold w64; apply ret_ok_codeptr_v; cbv [AF_both3_reac_box_name RBN_L6]; [lia | reflexivity]]
  | solve [unfold rbn_lit6; repeat apply Forall_cons; try apply Forall_nil; cbv beta; lia]
  | solve [reflexivity]
  | solve [unfold rl_nn, rl_cnt; lia]
  | solve [unfold rl_ovv; replace (n0 + 6 <=? 47) with true by (symmetry; apply Z.leb_le; lia); reflexivity]
  | solve [unfold rl_wrl; replace (rl_cnt n0 6) with 6 by (unfold rl_cnt; lia); reflexivity]
  | solve [cbv [AF_both3_reac_box_name RBN_L6]; lia]
  | solve [unfold IMG_LO, IMG_TOP, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia]
  | solve [lia] ].
Qed.

Lemma rl6_ovf_at : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) D n0 ov0,
  47 < n0 + 6 ->
  rbn_lcx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 n0 ov0 ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 ->
  rbn_lsrc W memc (VAL (A_OBJ 29)) (rbn_lit6 ++ [0]) -> VAL (A_OBJ 29) mod 8 = 0 ->
  rbn_lsep (spZ regs) (spZ regs + 88) D 48 (VAL (A_OBJ 29)) 7 ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 20 = w64 0 -> getr regs 21 = w64 (VAL (A_OBJ 29)) -> getr regs 24 = w64 6 ->
  SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + AF_both3_reac_box_name + RBN_L6) regs memc mdc)
    (rbn_lpost B fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L6X rbn_cl5
       (spZ regs + 88) D n0 47 1 (firstn (Z.to_nat (47 - n0)) rbn_lit6)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 Hg
  HCX HREC HBUF HSRC HAL HSEP HN0 HOV0 G20 G21 G24.
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof pa_base_lo as HBLO. unfold YImgTop.IMG_LO in HBLO.
pose proof (pa_obj_img_all 29%nat ltac:(cbv [tfib_nobj]; lia)) as (HOa & HOb).
eapply rl_final with (N := 6) (l := rbn_lit6) (lit := VAL (A_OBJ 29)) (ov0 := ov0)
  (Loff := AF_both3_reac_box_name + RBN_L6) (LXoff := AF_both3_reac_box_name + RBN_L6X)
  (retoff := AF_both3_reac_box_name + RBN_L6 + 32).
all: first
  [ solve [exact HCX] | solve [exact HREC] | solve [exact HBUF] | solve [exact HSRC] | solve [exact HAL]
  | solve [exact HSEP] | solve [exact HN0] | solve [exact HOV0] | solve [exact G20] | solve [exact G21]
  | solve [exact G24] | solve [exact HOa] | solve [exact HOb]
  | solve [intros jj Hjj; destruct (Z.eq_dec jj 0) as [-> | ?]; [exact rl6_head0 |]; destruct (Z.eq_dec jj 1) as [-> | ?]; [exact rl6_head1 |]; destruct (Z.eq_dec jj 2) as [-> | ?]; [exact rl6_head2 |]; destruct (Z.eq_dec jj 3) as [-> | ?]; [exact rl6_head3 |]; destruct (Z.eq_dec jj 4) as [-> | ?]; [exact rl6_head4 |]; destruct (Z.eq_dec jj 5) as [-> | ?]; [exact rl6_head5 |]; exfalso; lia]
  | solve [intros jj Hjj; destruct (Z.eq_dec jj 0) as [-> | ?]; [exact rl6_tail0 |]; destruct (Z.eq_dec jj 1) as [-> | ?]; [exact rl6_tail1 |]; destruct (Z.eq_dec jj 2) as [-> | ?]; [exact rl6_tail2 |]; destruct (Z.eq_dec jj 3) as [-> | ?]; [exact rl6_tail3 |]; destruct (Z.eq_dec jj 4) as [-> | ?]; [exact rl6_tail4 |]; exfalso; lia]
  | solve [exact rl6_tail5]
  | solve [unfold w64; apply ret_ok_codeptr_v; cbv [AF_both3_reac_box_name RBN_L6]; [lia | reflexivity]]
  | solve [unfold rbn_lit6; repeat apply Forall_cons; try apply Forall_nil; cbv beta; lia]
  | solve [reflexivity]
  | solve [unfold rl_nn, rl_cnt; lia]
  | solve [unfold rl_ovv; replace (n0 + 6 <=? 47) with false by (symmetry; apply Z.leb_gt; lia); reflexivity]
  | solve [unfold rl_wrl; replace (rl_cnt n0 6) with (47 - n0) by (unfold rl_cnt; lia); reflexivity]
  | solve [cbv [AF_both3_reac_box_name RBN_L6]; lia]
  | solve [unfold IMG_LO, IMG_TOP, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia]
  | solve [lia] ].
Qed.

Lemma rl7_fits_at : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) D n0 ov0,
  n0 + 5 <= 47 ->
  rbn_lcx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 n0 ov0 ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 ->
  rbn_lsrc W memc (VAL (A_OBJ 30)) (rbn_lit7 ++ [0]) -> VAL (A_OBJ 30) mod 8 = 0 ->
  rbn_lsep (spZ regs) (spZ regs + 88) D 48 (VAL (A_OBJ 30)) 6 ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 20 = w64 0 -> getr regs 21 = w64 (VAL (A_OBJ 30)) -> getr regs 24 = w64 5 ->
  SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + AF_both3_reac_box_name + RBN_L7) regs memc mdc)
    (rbn_lpost B fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L7X rbn_cl5
       (spZ regs + 88) D n0 (n0 + 5) ov0 rbn_lit7).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 Hg
  HCX HREC HBUF HSRC HAL HSEP HN0 HOV0 G20 G21 G24.
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof pa_base_lo as HBLO. unfold YImgTop.IMG_LO in HBLO.
pose proof (pa_obj_img_all 30%nat ltac:(cbv [tfib_nobj]; lia)) as (HOa & HOb).
eapply rl_final with (N := 5) (l := rbn_lit7) (lit := VAL (A_OBJ 30)) (ov0 := ov0)
  (Loff := AF_both3_reac_box_name + RBN_L7) (LXoff := AF_both3_reac_box_name + RBN_L7X)
  (retoff := AF_both3_reac_box_name + RBN_L7 + 32).
all: first
  [ solve [exact HCX] | solve [exact HREC] | solve [exact HBUF] | solve [exact HSRC] | solve [exact HAL]
  | solve [exact HSEP] | solve [exact HN0] | solve [exact HOV0] | solve [exact G20] | solve [exact G21]
  | solve [exact G24] | solve [exact HOa] | solve [exact HOb]
  | solve [intros jj Hjj; destruct (Z.eq_dec jj 0) as [-> | ?]; [exact rl7_head0 |]; destruct (Z.eq_dec jj 1) as [-> | ?]; [exact rl7_head1 |]; destruct (Z.eq_dec jj 2) as [-> | ?]; [exact rl7_head2 |]; destruct (Z.eq_dec jj 3) as [-> | ?]; [exact rl7_head3 |]; destruct (Z.eq_dec jj 4) as [-> | ?]; [exact rl7_head4 |]; exfalso; lia]
  | solve [intros jj Hjj; destruct (Z.eq_dec jj 0) as [-> | ?]; [exact rl7_tail0 |]; destruct (Z.eq_dec jj 1) as [-> | ?]; [exact rl7_tail1 |]; destruct (Z.eq_dec jj 2) as [-> | ?]; [exact rl7_tail2 |]; destruct (Z.eq_dec jj 3) as [-> | ?]; [exact rl7_tail3 |]; exfalso; lia]
  | solve [exact rl7_tail4]
  | solve [unfold w64; apply ret_ok_codeptr_v; cbv [AF_both3_reac_box_name RBN_L7]; [lia | reflexivity]]
  | solve [unfold rbn_lit7; repeat apply Forall_cons; try apply Forall_nil; cbv beta; lia]
  | solve [reflexivity]
  | solve [unfold rl_nn, rl_cnt; lia]
  | solve [unfold rl_ovv; replace (n0 + 5 <=? 47) with true by (symmetry; apply Z.leb_le; lia); reflexivity]
  | solve [unfold rl_wrl; replace (rl_cnt n0 5) with 5 by (unfold rl_cnt; lia); reflexivity]
  | solve [cbv [AF_both3_reac_box_name RBN_L7]; lia]
  | solve [unfold IMG_LO, IMG_TOP, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia]
  | solve [lia] ].
Qed.

Lemma rl7_ovf_at : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) D n0 ov0,
  47 < n0 + 5 ->
  rbn_lcx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 n0 ov0 ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 88) D 48 ->
  rbn_lsrc W memc (VAL (A_OBJ 30)) (rbn_lit7 ++ [0]) -> VAL (A_OBJ 30) mod 8 = 0 ->
  rbn_lsep (spZ regs) (spZ regs + 88) D 48 (VAL (A_OBJ 30)) 6 ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 20 = w64 0 -> getr regs 21 = w64 (VAL (A_OBJ 30)) -> getr regs 24 = w64 5 ->
  SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + AF_both3_reac_box_name + RBN_L7) regs memc mdc)
    (rbn_lpost B fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L7X rbn_cl5
       (spZ regs + 88) D n0 47 1 (firstn (Z.to_nat (47 - n0)) rbn_lit7)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 Hg
  HCX HREC HBUF HSRC HAL HSEP HN0 HOV0 G20 G21 G24.
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof pa_base_lo as HBLO. unfold YImgTop.IMG_LO in HBLO.
pose proof (pa_obj_img_all 30%nat ltac:(cbv [tfib_nobj]; lia)) as (HOa & HOb).
eapply rl_final with (N := 5) (l := rbn_lit7) (lit := VAL (A_OBJ 30)) (ov0 := ov0)
  (Loff := AF_both3_reac_box_name + RBN_L7) (LXoff := AF_both3_reac_box_name + RBN_L7X)
  (retoff := AF_both3_reac_box_name + RBN_L7 + 32).
all: first
  [ solve [exact HCX] | solve [exact HREC] | solve [exact HBUF] | solve [exact HSRC] | solve [exact HAL]
  | solve [exact HSEP] | solve [exact HN0] | solve [exact HOV0] | solve [exact G20] | solve [exact G21]
  | solve [exact G24] | solve [exact HOa] | solve [exact HOb]
  | solve [intros jj Hjj; destruct (Z.eq_dec jj 0) as [-> | ?]; [exact rl7_head0 |]; destruct (Z.eq_dec jj 1) as [-> | ?]; [exact rl7_head1 |]; destruct (Z.eq_dec jj 2) as [-> | ?]; [exact rl7_head2 |]; destruct (Z.eq_dec jj 3) as [-> | ?]; [exact rl7_head3 |]; destruct (Z.eq_dec jj 4) as [-> | ?]; [exact rl7_head4 |]; exfalso; lia]
  | solve [intros jj Hjj; destruct (Z.eq_dec jj 0) as [-> | ?]; [exact rl7_tail0 |]; destruct (Z.eq_dec jj 1) as [-> | ?]; [exact rl7_tail1 |]; destruct (Z.eq_dec jj 2) as [-> | ?]; [exact rl7_tail2 |]; destruct (Z.eq_dec jj 3) as [-> | ?]; [exact rl7_tail3 |]; exfalso; lia]
  | solve [exact rl7_tail4]
  | solve [unfold w64; apply ret_ok_codeptr_v; cbv [AF_both3_reac_box_name RBN_L7]; [lia | reflexivity]]
  | solve [unfold rbn_lit7; repeat apply Forall_cons; try apply Forall_nil; cbv beta; lia]
  | solve [reflexivity]
  | solve [unfold rl_nn, rl_cnt; lia]
  | solve [unfold rl_ovv; replace (n0 + 5 <=? 47) with false by (symmetry; apply Z.leb_gt; lia); reflexivity]
  | solve [unfold rl_wrl; replace (rl_cnt n0 5) with (47 - n0) by (unfold rl_cnt; lia); reflexivity]
  | solve [cbv [AF_both3_reac_box_name RBN_L7]; lia]
  | solve [unfold IMG_LO, IMG_TOP, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia]
  | solve [lia] ].
Qed.

End w.
Theorem rbn_l5_fits : rbn_L5_fits B.
Proof. unfold rbn_L5_fits, rbn_L5_run. intros fq. exact (@rl5_fits_at fq). Qed.
Theorem rbn_l5_ovf : rbn_L5_ovf B.
Proof. unfold rbn_L5_ovf, rbn_L5_run. intros fq. exact (@rl5_ovf_at fq). Qed.
Theorem rbn_l6_fits : rbn_L6_fits B.
Proof. unfold rbn_L6_fits, rbn_L6_run. intros fq. exact (@rl6_fits_at fq). Qed.
Theorem rbn_l6_ovf : rbn_L6_ovf B.
Proof. unfold rbn_L6_ovf, rbn_L6_run. intros fq. exact (@rl6_ovf_at fq). Qed.
Theorem rbn_l7_fits : rbn_L7_fits B.
Proof. unfold rbn_L7_fits, rbn_L7_run. intros fq. exact (@rl7_fits_at fq). Qed.
Theorem rbn_l7_ovf : rbn_L7_ovf B.
Proof. unfold rbn_L7_ovf, rbn_L7_run. intros fq. exact (@rl7_ovf_at fq). Qed.
End h.
End f.
End d.
