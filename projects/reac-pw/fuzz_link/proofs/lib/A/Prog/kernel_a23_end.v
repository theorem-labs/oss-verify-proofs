(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v, with its numbers changed; 214 of its 323 lines of code are new or changed and 377 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel's attribute cases a % 6 in {2, 3}: the nest's end, J7 (+0xdcc, after
   attr_text) -> kin_alat (+0xb44). Listing (internal path) (internal record, sha256 7bc02d6772b3),
   +0xdcc .. +0xe10: a1 := w2.n; `bltu a1, n0 + 2` -> +0xb44 (nothing was put since the nest's start); else the shadow
   checks of w2 + n0 and w2 + n0 + 1, the two bytes n - n0 at w2 + n0 (the nest's length), -> +0xb44.
   THE STATE: kernel_k3.v's registers (s9 = w2 + 4096), atoms 32 = n, 33 = full, 36 = w2 + n0 (the alias
   w2 + s10 = atom 36), s10 = n0 its own atom 26; w2's fields as a region, and in the store arm the two bytes at
   w2 + n0. The branch is a condition (BC_LTU / BC_GEU of n and n0 + 2), true by the case. ONE run each; the cut by
   kernel_kit.v kat_frame_w2 (the store is inside w2's data: n0 + 2 <= n <= 4096) and kw_move (the fields unchanged).
   Section hypotheses used: LAWS (the run instances).
   Released proofs (rule 24): none of kernel's walk (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by
   the rule-24 walk check at 14:56Z).
   Proves no function (kind: segment lemma of kernel's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
kernel_c kernel_defs kernel_kit kernel_next kernel_k3 kernel_a5 kernel_a23_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the state at J7 (b: the store arm) ---- *)
Definition a23E_st : YP09.region := YP09.mkRegion (Some 36%nat) 0 2 0 2 [].
Definition a23E_facts (b : bool) : facts :=
  mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (21%nat, mkAF 4096 (2 ^ 47 - 4113) 0);
           (32%nat, mkAF 0 4096 0); (33%nat, mkAF 0 1 0); (26%nat, mkAF 0 4096 0);
           (36%nat, mkAF 4096 (2 ^ 47 - 4113) 0)]
    [mkAC (if b then BC_GEU else BC_LTU) (SOff 32 0) (SOff 26 2)]
    [(SAlu ALU_ADD (SOff 21 0) (SOff 26 0), SOff 36 0)].
Definition a23E_ss (b : bool) : sstate :=
  mkSS (kpc A23_J7) k3_regs (k3_fl :: (if b then [a23E_st] else [])) None (a23E_facts b).
Definition a23E_SH (b : bool) : list shent :=
  mkSHE 21 4096 4112 :: (if b then [mkSHE 36 0 10] else []).

Lemma a23E_windows : forall (E : env) b w n0,
  base_val E (Some 21%nat) = w -> base_val E (Some 36%nat) = w + n0 -> 0 <= n0 -> n0 + 2 <= 4096 ->
  forall bb wlo whi a, In (bb, wlo, whi) (windows (ss_mem (a23E_ss b))) ->
    base_val E bb + wlo <= a < base_val E bb + whi -> w <= a < w + NW_SIZE.
Proof.
  intros E b w n0 H21 H36 Hn0 Hn2 bb wlo whi a Hin Ha.
  unfold a23E_ss, windows in Hin. unfold NW_SIZE.
  destruct b; cbn [ss_mem map In k3_fl a23E_st YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  - destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-.
    + rewrite H21 in Ha. lia.
    + rewrite H36 in Ha. lia.
  - destruct Hin as [Hq | []]; injection Hq as <- <- <-. rewrite H21 in Ha. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Definition a23E_ext (cx : kcx) (fpos n f n0 : Z) : list word :=
  [w64 n; w64 f; w64 0; w64 0; w64 (kW2 cx fpos + n0)].


(* the environment's values *)
Lemma a23E_env : forall cx fpos k2 ly3 S3 md3 (ms3 : machine_state) n f n0 (E : env),
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 -> kregs0 cx ms3 ->
  getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 21)) = w64 (kW2 cx fpos) ->
  getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 26)) = w64 n0 ->
  0 <= n0 <= n -> n <= 4096 -> 0 <= f <= 1 ->
  E = Eimg (Ereg (ms_regs ms3) (a23E_ext cx fpos n f n0)) ->
  bv_unsigned (ew E 20) = SHADOW_OFF /\ bv_unsigned (ew E 21) = kW2 cx fpos /\ bv_unsigned (ew E 32) = n /\
  bv_unsigned (ew E 33) = f /\ bv_unsigned (ew E 26) = n0 /\ bv_unsigned (ew E 36) = kW2 cx fpos + n0.
Proof.
  intros cx fpos k2 ly3 S3 md3 ms3 n f n0 E HB HJB HR0 R21 R26 Hn0 Hn Hf HEdef.
  destruct HR0 as (_ & _ & _ & _ & _ & _ & R20).
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  assert (ER : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E jn = getr (ms_regs ms3) r)
    by (intros jn r Hj; rewrite HEdef; exact (ew_Eimg_Ereg_nat _ _ jn r Hj)).
  assert (EXT : forall jn, (jn < 5)%nat -> ew E (32 + jn) = nth jn (a23E_ext cx fpos n f n0) (Z_to_bv 64 0))
    by (intros jn Hj; rewrite HEdef, Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EXT 0%nat ltac:(lia)) as E32. pose proof (EXT 1%nat ltac:(lia)) as E33.
  pose proof (EXT 4%nat ltac:(lia)) as E36.
  cbn [a23E_ext nth Nat.add] in E32, E33, E36.
  split; [rewrite (ER 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia|].
  split; [rewrite (ER 21%nat (Z_to_bv 5 (Z.of_nat 21)) eq_refl), R21; unfold w64; apply unsigned_lit_small; lia|].
  split; [rewrite E32; unfold w64; apply unsigned_lit_small; lia|].
  split; [rewrite E33; unfold w64; apply unsigned_lit_small; lia|].
  split; [rewrite (ER 26%nat (Z_to_bv 5 (Z.of_nat 26)) eq_refl), R26; unfold w64; apply unsigned_lit_small; lia|].
  rewrite E36; unfold w64; apply unsigned_lit_small; lia.
Qed.

(* ---- THE START ---- *)
Lemma a23E_start : forall cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3 rl sl adv g n f n0 (E : env) (b : bool),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos A23_J7 rl sl (kfsh 0xf8 0 0xf3) true adv g k2 ly3 S3 W3 ms3 md3 ->
  In (21%nat, kW2 cx fpos) rl -> In (25%nat, kW2 cx fpos + NW_N) rl -> In (26%nat, n0) rl ->
  0 <= n0 <= n ->
  E = Eimg (Ereg (ms_regs ms3) (a23E_ext cx fpos n f n0)) ->
  (if b then n0 + 2 <= n else n < n0 + 2) ->
  st_ok_pi SEGS pa_val E (a23E_ss b) (restrict (w_H W3) ms3) /\
  sh_ok SEGS k3_Bx (a23E_SH b) E (mrestrict (w_H W3) (ms_mem ms3)) /\
  awr_ok_x E (ss_mem (a23E_ss b)) (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 rl sl adv g n f n0 E b HB HJ HW HAT I21 I25 I26 Hn0 HEdef Hb.
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL I21) as R21.
  pose proof (kn_reg_of ms3 _ 25 (kW2 cx fpos + NW_N) HRL I25) as R25.
  pose proof (kn_reg_of ms3 _ 26 n0 HRL I26) as R26.
  pose proof HW as (Hw0 & Hwl & Hpres & Hnv & Hfv & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  destruct (a23E_env cx fpos k2 ly3 S3 md3 ms3 n f n0 E HB HJB HR0 R21 R26 Hn0 ltac:(lia) Hfr HEdef)
    as (B20 & B21 & B32 & B33 & B26 & B36).
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _ & HFsh).
  pose proof kn_band as (KB1 & KB2).
  assert (KLS : kLowShadowBeg = 2147446784) by reflexivity.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  assert (BV21 : base_val E (Some 21%nat) = kW2 cx fpos) by exact B21.
  assert (BV36 : base_val E (Some 36%nat) = kW2 cx fpos + n0) by exact B36.
  pose proof (a5_awf SK B LAWS cx fpos k2 ly3 S3 W3 _ _ HB HJ) as AWF.
  pose proof (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) as HRA.
  assert (HUB : U E k3_Bx = SHADOW_OFF) by (unfold k3_Bx; apply k3_U0; [exact B20 | unfold SHADOW_OFF; lia]).
  split; [|split].
  - (* the symbolic state *)
    rewrite (kn_ms_shape ms3 (BASE + kpc A23_J7) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold a23E_ss. apply pa_entry_st_ok_full.
    + unfold k3_regs.
      apply kn_regs_ok_set; [rewrite HEdef; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
      rewrite R25. cbn [sv_denot]. rewrite B21. reflexivity.
    + destruct b; vm_compute; reflexivity.
    + apply Forall_cons.
      * unfold k3_fl, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV21.
        split; [lia|]. split; [unfold NW_SIZE in Hwl; lia|]. split.
        { intros o Ho. exact (proj2 (Hpres o ltac:(unfold NW_SIZE; lia))). }
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val SEGS E _ (kW2 cx fpos) 4096 8 (SOff 32 0) n).
           ++ cbn [sv_denot]. rewrite B32, Z.add_0_r. reflexivity.
           ++ change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
           ++ change (Z.of_N 8) with 8. lia.
           ++ exact Hnv.
        -- apply (chunk_ok_val SEGS E _ (kW2 cx fpos) 4104 4 (SOff 33 0) f).
           ++ cbn [sv_denot]. rewrite B33, Z.add_0_r. reflexivity.
           ++ change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
           ++ change (Z.of_N 4) with 4. lia.
           ++ exact Hfv.
      * destruct b; [apply Forall_cons; [|apply Forall_nil] | apply Forall_nil].
        unfold a23E_st, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV36.
        split; [lia|]. split; [unfold NW_SIZE in Hwl; lia|]. split; [|apply Forall_nil].
        intros o Ho. replace (kW2 cx fpos + n0 + o) with (kW2 cx fpos + (n0 + o)) by lia.
        exact (proj2 (Hpres (n0 + o) ltac:(unfold NW_SIZE; lia))).
    + destruct b; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint, k3_fl, a23E_st;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite ?BV21, ?BV36; repeat split; lia.
    + unfold a23E_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok alias_ok conds_ok].
      split; [|split].
      * unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B20, B21, B32, B33, B26, B36.
        change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
        repeat split; lia.
      * split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
        destruct b; [rewrite branch_geu_U | rewrite branch_ltu_U]; rewrite !U_SOff, B32, B26;
          rewrite (zcanon_id (n + 0)), (zcanon_id (n0 + 2)) by (unfold M64; lia).
        -- apply negb_true_iff, Z.ltb_ge. lia.
        -- apply Z.ltb_lt. lia.
      * split; [|exact I].
        rewrite (denot_lit_U E (SAlu ALU_ADD (SOff 21 0) (SOff 26 0))), (denot_lit_U E (SOff 36 0)). f_equal.
        rewrite U_SAlu, !U_SOff. cbn [zalu_raw].
        rewrite B21, B26, B36, !Z.add_0_r.
        rewrite (zcanon_id (kW2 cx fpos)), (zcanon_id n0) by (unfold M64; lia). reflexivity.
  - (* the shadow entries *)
    unfold sh_ok, a23E_SH. apply Forall_cons.
    + apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E k3_Bx 21 (kW2 cx fpos) NW_SIZE (kW2 cx fpos)
               4096 4112 HRA HUB); [apply k3_U0; [exact B21 | lia] | lia | unfold NW_SIZE; lia |].
      intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF in *. lia.
    + destruct b; [apply Forall_cons; [|apply Forall_nil] | apply Forall_nil].
      apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E k3_Bx 36 (kW2 cx fpos) NW_SIZE (kW2 cx fpos + n0)
               0 10 HRA HUB); [apply k3_U0; [exact B36 | lia] | lia | unfold NW_SIZE; lia |].
      intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF in *. lia.
  - (* the writable windows lie in F *)
    unfold a23E_ss. cbn [ss_mem].
    apply awr_ok_x_cons.
    + intros x Hx. unfold k3_fl in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV21 in Hx.
      left. apply AWF. unfold NW_SIZE. lia.
    + destruct b; [apply awr_ok_x_cons; [|apply awr_ok_x_nil] | apply awr_ok_x_nil].
      intros x Hx. unfold a23E_st in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV36 in Hx.
      left. apply AWF. unfold NW_SIZE. lia.
Qed.

(* ---- THE PHASE: the nest's end ---- *)
Theorem a23_end_ph : forall POST (Rc Rm Ra : kcx -> Z -> Prop),
  kfrom SK B POST (kin_alat B Rc Rm Ra) -> kfrom SK B POST (a23_at B Rc Rm Ra A23_J7).
Proof.
  intros POST Rc Rm Ra HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (qc & qci & qj & qm & qk & qn & qf & qadv & qhd & qkd & ql & qa & qp & qn0 & HRc & HRm & HRa & Hc
    & Hci & Hj & Hm & Hk & Hkd & Hl & Hhd & Ha & Htx & Hka & Hn0 & HW & HAT).
  pose proof HAT as (_ & HR0 & HRL & _ & _ & HSH & _ & HJB & _).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL ltac:(unfold a23_rl; kn_in)) as R21.
  pose proof (kn_reg_of ms3 _ 26 qn0 HRL ltac:(unfold a23_rl; kn_in)) as R26.
  remember (Eimg (Ereg (ms_regs ms3) (a23E_ext cx fpos qn qf qn0))) as Eq3 eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM Eq3) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (a23E_ext cx fpos qn qf qn0)) Eq3)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (a23E_env cx fpos k2 ly3 S3 md3 ms3 qn qf qn0 Eq3 HB HJB HR0 R21 R26 Hn0 ltac:(lia) Hfr HEdef)
    as (B20 & B21 & B32 & B33 & B26 & B36).
  assert (BV21 : base_val Eq3 (Some 21%nat) = kW2 cx fpos) by exact B21.
  assert (BV36 : base_val Eq3 (Some 36%nat) = kW2 cx fpos + qn0) by exact B36.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  assert (Hok : kslots_okb (a23_sl cx fpos qc qci qm qk qhd qkd) = true) by reflexivity.
  (* the registers the run keeps *)
  assert (HKP : forall (msn : machine_state) ssx,
            st_ok_pi SEGS pa_val Eq3 ssx (restrict (w_H W3) msn) ->
            forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ssx) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
              (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [19; 21; 24; 22]%nat) = true ->
            forall r : nat, In r [19; 21; 24; 22]%nat ->
            getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r))).
  { intros msn ssx HSx Hb r Hr. exact (regs_kept_of_st_ok_pi Eq3 ssx _ _ _ _ HSx HAG Hb _ (kn_in_map5 r _ Hr)). }
  (* the cut after the run, for either arm *)
  assert (KEND : forall (b : bool), (if b then qn0 + 2 <= qn else qn < qn0 + 2) ->
            forall (ms4 : machine_state) md4 cs',
            region_ok SEGS Eq3 (mrestrict (w_H W3) (ms_mem ms4))
              (YP09.mkRegion (Some 21%nat) 4096 4112 4096 4112 cs') ->
            In (YP09.mkChunk 4096 (CVal 8 (SOff 32 0))) cs' -> In (YP09.mkChunk 4104 (CVal 4 (SOff 33 0))) cs' ->
            frame_of Eq3 (ss_mem (a23E_ss b)) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms4)) ->
            mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms4)) ->
            ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx)
              (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms4) md4 k2 ->
            kms KP_ALAT ms4 ->
            (forall r, In r nx_keep0 -> getr (ms_regs ms4) r = getr (ms_regs ms3) r) ->
            (forall r : nat, In r [19; 21; 24; 22]%nat ->
               getr (ms_regs ms4) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r))) ->
            getr (ms_regs ms4) (Z_to_bv 5 (Z.of_nat 25)) = sv_denot Eq3 (SOff 21 4096) ->
            m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
            SRr SEGS W3 (mkCfg ms4 md4) (POST cx)).
  { intros b Hb ms4 md4 cs' HR1 Hin1 Hin2 HFr4 HG4 HJ4 HMS4 HK0 HKr H25 Hfds Hfs.
    assert (HP : forall q, apresent (w_H W3) (ms_mem ms3) q -> apresent (w_H W3) (ms_mem ms4) q)
      by (intros q Hq; exact (k3_apres_grows _ _ _ q HG4 Hq)).
    assert (UN : forall q, 0 <= q < 2 ^ 64 -> ~ (kW2 cx fpos <= q < kW2 cx fpos + NW_SIZE) ->
              aview SEGS (w_H W3) (ms_mem ms4) q = aview SEGS (w_H W3) (ms_mem ms3) q).
    { intros q Hq Hnq.
      apply (kept_of_frame (segs := SEGS) Eq3 _ (w_H W3) (ms_mem ms3) (ms_mem ms4)
               (fun x => kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) HFr4); [|exact Hq | exact Hnq].
      destruct b.
      - exact (a23E_windows Eq3 true (kW2 cx fpos) qn0 BV21 BV36 ltac:(lia) ltac:(lia)).
      - intros bb wlo whi x Hin Hx. unfold a23E_ss, windows in Hin.
        cbn [ss_mem map In k3_fl YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
        destruct Hin as [Hq' | []]; injection Hq' as <- <- <-. rewrite BV21 in Hx. cbv beta. unfold NW_SIZE. lia. }
    apply (HN cx fpos k2 ly3 S3 W3 ms4 md4 HB HJ4 HFR).
    exists qc, qci, qj, qm, qk, qn, qf, qadv, qhd, qkd, ql.
    split; [exact HRc|]. split; [exact HRm|]. split; [exact HRa|]. split; [exact Hc|]. split; [exact Hci|].
    split; [exact Hj|]. split; [exact Hm|]. split; [exact Hk|]. split; [exact Hkd|]. split; [exact Hl|].
    split; [exact Hhd|].
    split.
    { apply (kw_move W3 ms3 W3 ms4 (kW2 cx fpos) qn qf qn qf HW HP).
      - exact (field_of_region Eq3 _ 21 (kW2 cx fpos) _ _ _ _ _ 4096 8 (SOff 32 0) qn HR1 B21 Hin1
                 ltac:(cbn [sv_denot]; rewrite B32, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
      - exact (field_of_region Eq3 _ 21 (kW2 cx fpos) _ _ _ _ _ 4104 4 (SOff 33 0) qf HR1 B21 Hin2
                 ltac:(cbn [sv_denot]; rewrite B33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
      - unfold NL_CHUNK_MAX. lia.
      - exact Hfr. }
    split; [exact I|].
    apply (kat_frame_w2 SK B LAWS 0 NW_SIZE cx fpos A23_J7 _ _ _ true qadv (Some qj) k2 ly3 S3 W3 ms3 md3 KP_ALAT _ _
             W3 ms4 md4 HB HAT HMS4 (kregs0_keep cx ms3 ms4 HK0 HR0)).
    - unfold kregs_eq. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + rewrite (HKr 19%nat) by kn_in. apply (kn_reg_of ms3 _ 19 _ HRL). unfold a23_rl. kn_in.
      + rewrite (HKr 21%nat) by kn_in. apply (kn_reg_of ms3 _ 21 _ HRL). unfold a23_rl. kn_in.
      + rewrite (HKr 24%nat) by kn_in. apply (kn_reg_of ms3 _ 24 _ HRL). unfold a23_rl. kn_in.
      + rewrite H25. cbn [sv_denot]. rewrite B21. reflexivity.
      + rewrite (HKr 22%nat) by kn_in. apply (kn_reg_of ms3 _ 22 _ HRL). unfold a23_rl. kn_in.
    - intros x Hx. unfold a23_sl in Hx. exact Hx.
    - exact Hok.
    - apply kfsh_fits.
    - exact Hfds.
    - exact Hfs.
    - lia.
    - unfold NW_SIZE. lia.
    - intros q Hq Hnq. apply UN; [exact Hq|]. intros Hc'. apply Hnq. lia.
    - exact HP. }
  destruct (Z_lt_ge_dec qn (qn0 + 2)) as [Lt | Ge].
  - (* nothing put since the nest's start: no store *)
    destruct (a23E_start cx fpos k2 ly3 S3 W3 ms3 md3 _ _ qadv (Some qj) qn qf qn0 Eq3 false HB HJ HW HAT
                ltac:(unfold a23_rl; kn_in) ltac:(unfold a23_rl; kn_in) ltac:(unfold a23_rl; kn_in) Hn0 HEdef Lt)
      as (HS & SHOK & HAWR).
    paj_run_to_tok RUNTO HS HJ SHOK k3_span (kpc KP_ALAT); [exact HAWR|].
    lazymatch goal with
    | HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msn),
      HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
      HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
      let HR1 := fresh "HR1" in
      spregion HS' 0%nat HR1;
      apply (KEND false Lt msn mdn _ HR1 ltac:(kn_in) ltac:(kn_in) HFr' HG' ltac:(assumption));
      [ apply (kn_kms_of _ Eq3 ssx msn KP_ALAT HS'); vm_compute; reflexivity
      | exact (regs_kept_of_st_ok_pi Eq3 ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity))
      | exact (HKP msn ssx HS' ltac:(vm_compute; reflexivity))
      | rewrite (st_ok_pi_restrict_reg _ Eq3 ssx msn _ HS'); f_equal; vm_compute; reflexivity
      | exact (proj1 (wvb_fds_fs _ _ _))
      | exact (proj2 (wvb_fds_fs _ _ _)) ]
    end.
  - (* the nest's length at w2 + n0 *)
    assert (Ge' : qn0 + 2 <= qn) by lia.
    destruct (a23E_start cx fpos k2 ly3 S3 W3 ms3 md3 _ _ qadv (Some qj) qn qf qn0 Eq3 true HB HJ HW HAT
                ltac:(unfold a23_rl; kn_in) ltac:(unfold a23_rl; kn_in) ltac:(unfold a23_rl; kn_in) Hn0 HEdef Ge')
      as (HS & SHOK & HAWR).
    paj_run_to_tok RUNTO HS HJ SHOK k3_span (kpc KP_ALAT); [exact HAWR|].
    lazymatch goal with
    | HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msn),
      HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
      HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
      let HR1 := fresh "HR1" in
      spregion HS' 0%nat HR1;
      apply (KEND true Ge' msn mdn _ HR1 ltac:(kn_in) ltac:(kn_in) HFr' HG' ltac:(assumption));
      [ apply (kn_kms_of _ Eq3 ssx msn KP_ALAT HS'); vm_compute; reflexivity
      | exact (regs_kept_of_st_ok_pi Eq3 ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity))
      | exact (HKP msn ssx HS' ltac:(vm_compute; reflexivity))
      | rewrite (st_ok_pi_restrict_reg _ Eq3 ssx msn _ HS'); f_equal; vm_compute; reflexivity
      | exact (proj1 (wvb_fds_fs _ _ _))
      | exact (proj2 (wvb_fds_fs _ _ _)) ]
    end.
Qed.

End b.
End a.
