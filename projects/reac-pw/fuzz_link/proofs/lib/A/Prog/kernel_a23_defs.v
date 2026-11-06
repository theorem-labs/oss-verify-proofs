(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v; 93 of its 253 lines of code are new or changed and 326 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel's attribute cases a % 6 in {2, 3} (the nest), +0xaa0 -> +0xb44.
   THIS FILE holds what the phases of this segment share: its own cut `a23_at` at its four internal joins, the
   symbolic state of a run that puts into w2 (kernel_k3.v's, at any pc, with extra conditions), its start
   (`a23_seat`) and the cut after such a run (`a23_landk`).

   THE CODE (listing (internal path) (internal record, sha256 7bc02d6772b3), offsets from 0x83d30):
     +0xaa0 .. +0xbf0  s10 := w2.n (the nest's start n0); the nest header's length (0, 0) and type (0x12, 0), each
                       behind a room test `bltu (2 ^ 64 - 4098), n - 4095` (room iff n <= 4094; no room: full := 1)
     +0xbf4            `bne a1, 3` -> +0xdb8 (a1 is not pinned by the cut: both arms are proved)
     +0xbfc .. +0xd64  the nested attribute's length (8, 0), type (2, 0) (room iff n <= 4094) and body "data"
                       (room iff n <= 4092)
     +0xd68 .. +0xdb4  NL_ALIGN: q := (n + 3) & ~3; checked_memset(w2 + n, 0, q - n) when q <> n; n := q;
                       s3 := the cursor + 8 again
     +0xdb8 .. +0xdc8  attr_text(w2, 1, p, a & 0x80)
     +0xdcc .. +0xe10  `bltu` w2.n, n0 + 2: -> +0xb44; else the nest's length (two bytes at w2 + n0) -> +0xb44
   THE CUTS of this lane: J2 = +0xbf4, J5 = +0xd68, J6 = +0xdb8, J7 = +0xdcc: kernel_defs.v's `kat` at the pc with
   w2's two fields, the attribute byte a in s7, the text p in s11, the nest's start n0 in s10 (0 <= n0 <= n) and
   `ktext cx p` and `ka_text cx a p` for the attr_text call.
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
kernel_c kernel_defs kernel_kit kernel_next kernel_k3 kernel_a5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the lane's internal cut pcs ---- *)
Definition A23_J2 : Z := 0xbf4.
Definition A23_J5 : Z := 0xd68.
Definition A23_J6 : Z := 0xdb8.
Definition A23_J7 : Z := 0xdcc.

Lemma a23_conds_app : forall E l1 l2, conds_ok E l1 -> conds_ok E l2 -> conds_ok E (l1 ++ l2).
Proof. intros E l1. induction l1 as [|c t IH]; cbn; intros l2 H1 H2; [exact H2|]. destruct H1; split; auto. Qed.

(* ---- a run that puts into w2: kernel_k3.v's state at pc, with extra conditions xc ---- *)
Definition a23_facts (lo hi : Z) (cs : list Z) (xc : list acond) : facts :=
  mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (21%nat, mkAF 4096 (2 ^ 47 - 4113) 0);
           (32%nat, mkAF lo hi 0); (33%nat, mkAF 0 1 0); (34%nat, mkAF 4096 (2 ^ 47 - 4113) 0)]
    (k3_conds cs ++ xc) [(SAlu ALU_ADD (SOff 21 0) (SOff 32 0), SOff 34 0)].
Definition a23_ss (pc lo hi pl : Z) (cs : list Z) (xc : list acond) : sstate :=
  mkSS (kpc pc) k3_regs [k3_sp; k3_fl; k3_pr pl] None (a23_facts lo hi cs xc).

Lemma a23_windows : forall (E : env) pc lo hi pl cs xc w n,
  base_val E (Some 21%nat) = w -> base_val E (Some 34%nat) = w + n -> 0 <= n -> 0 <= pl -> n + pl <= 4096 ->
  forall b wlo whi a, In (b, wlo, whi) (windows (ss_mem (a23_ss pc lo hi pl cs xc))) ->
    base_val E b + wlo <= a < base_val E b + whi -> w <= a < w + NW_SIZE.
Proof.
  intros E pc lo hi pl cs xc w n H21 H34 Hn Hpl Hnpl b wlo whi a Hin Ha.
  unfold a23_ss, windows in Hin.
  cbn [ss_mem map In k3_sp k3_fl k3_pr YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  unfold NW_SIZE.
  destruct Hin as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <- <-.
  - lia.
  - rewrite H21 in Ha. lia.
  - rewrite H34 in Ha. lia.
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

(* ---- THE CUT INVARIANT of this lane ---- *)
Definition a23_rl (cx : kcx) (fpos a p n0 left : Z) : list (nat * Z) :=
  [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N);
   (22%nat, left); (23%nat, a); (27%nat, p); (26%nat, n0)].

Definition a23_sl (cx : kcx) (fpos c ci m k hd kd : Z) : list (Z * Z) :=
  kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)].

Definition a23_at (Rc Rm Ra : kcx -> Z -> Prop) (pc : Z) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j m k n f adv hd kd left a p n0,
    Rc cx (c - ci) /\ Rm cx (m - k) /\ Ra cx left /\
    1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\ 1 <= m <= 5 /\ 0 <= k < m /\
    (kd = 0 \/ kd = 7) /\ 1 <= left <= 4 /\ 0 <= hd <= n /\
    0 <= a < 256 /\ ktext cx p /\ ka_text cx a p /\ 0 <= n0 <= n /\
    kw_at W3 ms3 (kW2 cx fpos) n f /\
    kat B cx fpos pc (a23_rl cx fpos a p n0 left) (a23_sl cx fpos c ci m k hd kd)
      (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

(* ---- THE START of a run that puts into w2: the state, its shadow entries and its windows ---- *)
Lemma a23_seat : forall cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3 pc rl sl adv g n f k (E : env),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos pc rl sl (kfsh 0xf8 0 0xf3) true adv g k2 ly3 S3 W3 ms3 md3 ->
  In (21%nat, kW2 cx fpos) rl -> In (25%nat, kW2 cx fpos + NW_N) rl ->
  In (KS_K, k) sl -> In (KS_W2F, kW2 cx fpos + NW_FULL) sl -> In (KS_M4098, 2 ^ 64 - 4098) sl ->
  In (KS_M4093, 2 ^ 64 - 4093) sl ->
  0 <= k < 5 ->
  E = Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos n f k)) ->
  forall lo hi pl cs xc,
  lo <= n <= hi -> 0 <= pl -> n + pl <= 4096 ->
  regions_wf [k3_sp; k3_fl; k3_pr pl] = true ->
  Forall (fun c => -4098 < n + c < 0) cs -> conds_ok E xc ->
  st_ok_pi SEGS pa_val E (a23_ss pc lo hi pl cs xc) (restrict (w_H W3) ms3) /\
  sh_ok SEGS k3_Bx (k3_SH pl) E (mrestrict (w_H W3) (ms_mem ms3)) /\
  awr_ok_x E (ss_mem (a23_ss pc lo hi pl cs xc)) (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 pc rl sl adv g n f k E HB HJ HW HAT I21 I25 IK IW2F I98 I93 Hk HEdef
    lo hi pl cs xc Hn Hpl Hnpl Hwf Hcs Hxc.
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL I21) as R21.
  pose proof (kn_reg_of ms3 _ 25 (kW2 cx fpos + NW_N) HRL I25) as R25.
  pose proof HW as (Hw0 & Hwl & Hpres & Hnv & Hfv & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  destruct (k3_env SK B LAWS cx fpos k2 ly3 S3 md3 ms3 n f k E HB HJB HR0 R21 ltac:(lia) Hfr Hk HEdef)
    as (B9 & B20 & B21 & B32 & B33 & B34 & B35).
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _ & HFsh).
  pose proof kn_band as (KB1 & KB2).
  assert (KLS : kLowShadowBeg = 2147446784) by reflexivity.
  pose proof (kn_sp SK B cx HB) as (Hac & _ & _ & Hs1 & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & Hs1b & _ & _ & Hsp47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : kernel_c.KERNEL_AK = 4640) by reflexivity.
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by exact B9.
  assert (BV21 : base_val E (Some 21%nat) = kW2 cx fpos) by exact B21.
  assert (BV34 : base_val E (Some 34%nat) = kW2 cx fpos + n) by exact B34.
  pose proof (kn_slot_of cx W3 ms3 _ KS_K k HSL IK) as SL_K.
  pose proof (kn_slot_of cx W3 ms3 _ KS_W2F (kW2 cx fpos + NW_FULL) HSL IW2F) as SL_W2F.
  pose proof (kn_slot_of cx W3 ms3 _ KS_M4098 (2 ^ 64 - 4098) HSL I98) as SL_M4098.
  pose proof (kn_slot_of cx W3 ms3 _ KS_M4093 (2 ^ 64 - 4093) HSL I93) as SL_M4093.
  pose proof (a5_awf SK B LAWS cx fpos k2 ly3 S3 W3 _ _ HB HJ) as AWF.
  pose proof (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) as HRA.
  split; [|split].
  - (* the symbolic state *)
    rewrite (kn_ms_shape ms3 (BASE + kpc pc) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold a23_ss. apply pa_entry_st_ok_full.
    + unfold k3_regs.
      apply kn_regs_ok_set; [rewrite HEdef; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
      rewrite R25. cbn [sv_denot]. rewrite B21. reflexivity.
    + exact Hwf.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * unfold k3_sp, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xa0 (SOff 35 0) k); [|exact SL_K].
           cbn [sv_denot]. rewrite B35, Z.add_0_r. reflexivity.
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xc8 (SOff 21 4104) (kW2 cx fpos + NW_FULL));
             [|exact SL_W2F].
           cbn [sv_denot]. rewrite B21. reflexivity.
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xd0 (SLit (2 ^ 64 - 4098)) (2 ^ 64 - 4098));
             [reflexivity | exact SL_M4098].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xd8 (SLit (2 ^ 64 - 4093)) (2 ^ 64 - 4093));
             [reflexivity | exact SL_M4093].
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
      * unfold k3_pr, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV34.
        split; [lia|]. split; [unfold NW_SIZE in Hwl; lia|]. split; [|apply Forall_nil].
        intros o Ho. replace (kW2 cx fpos + n + o) with (kW2 cx fpos + (n + o)) by lia.
        exact (proj2 (Hpres (n + o) ltac:(unfold NW_SIZE; lia))).
    + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, k3_sp, k3_fl, k3_pr.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV9, BV21, BV34. rewrite HKA in Hac.
      repeat split; lia.
    + unfold a23_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok alias_ok].
      split; [|split].
      * unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B20, B21, B32, B33, B34.
        change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
        refine (conj (conj _ (conj eq_refl _)) (conj (conj _ (conj eq_refl _)) (conj (conj _ (conj eq_refl _))
          (conj (conj _ (conj eq_refl _)) (conj (conj _ (conj eq_refl _)) I))))); lia.
      * apply a23_conds_app; [exact (k3_conds_ok E n cs B32 Hcs) | exact Hxc].
      * split; [|exact I].
        rewrite (denot_lit_U E (SAlu ALU_ADD (SOff 21 0) (SOff 32 0))), (denot_lit_U E (SOff 34 0)). f_equal.
        rewrite U_SAlu, !U_SOff. cbn [zalu_raw].
        rewrite B21, B32, B34, !Z.add_0_r.
        rewrite (zcanon_id (kW2 cx fpos)), (zcanon_id n) by (unfold M64; lia). reflexivity.
  - (* the shadow entries *)
    assert (HUB : U E k3_Bx = SHADOW_OFF)
      by (unfold k3_Bx; apply k3_U0; [exact B20 | unfold SHADOW_OFF; lia]).
    unfold sh_ok, k3_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E k3_Bx 21 (kW2 cx fpos) NW_SIZE (kW2 cx fpos)
               4096 4112 HRA HUB); [apply k3_U0; [exact B21 | lia] | lia | unfold NW_SIZE; lia |].
      intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF in *. lia.
    + apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E k3_Bx 34 (kW2 cx fpos) NW_SIZE (kW2 cx fpos + n)
               0 (pl + 8) HRA HUB); [apply k3_U0; [exact B34 | lia] | lia | unfold NW_SIZE; lia |].
      intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF in *. lia.
  - (* the writable windows lie in F *)
    unfold a23_ss. cbn [ss_mem].
    apply awr_ok_x_cons; [intros x Hx; unfold k3_sp in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    + intros x Hx. unfold k3_fl in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV21 in Hx.
      left. apply AWF. unfold NW_SIZE. lia.
    + intros x Hx. unfold k3_pr in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV34 in Hx.
      left. apply AWF. unfold NW_SIZE. lia.
Qed.

(* ---- THE CUT after a run that put into w2: w2's new fields and the cut at the new pc ---- *)
Lemma a23_landk : forall cx fpos pc rl sl adv j k2 ly3 S3 W3 (ms3 : machine_state) md3 n f (E : env)
    lo hi pl cs xc (ms : machine_state) md cs' fe f' pc' rl',
  kbase SK B cx ->
  kat B cx fpos pc rl sl (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  kslots_okb sl = true ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  bv_unsigned (ew E 21) = kW2 cx fpos -> bv_unsigned (ew E 32) = n -> bv_unsigned (ew E 33) = f ->
  bv_unsigned (ew E 34) = kW2 cx fpos + n ->
  0 <= pl -> n + pl <= 4096 ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 21%nat) 4096 4112 4096 4112 cs') ->
  frame_of E (ss_mem (a23_ss pc lo hi pl cs xc)) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  kms pc' ms -> kregs0 cx ms -> kregs_eq ms rl' ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  In (YP09.mkChunk 4096 (CVal 8 (SOff 32 pl))) cs' ->
  In (YP09.mkChunk 4104 (CVal 4 fe)) cs' ->
  (fe = SOff 33 0 /\ f' = f) \/ (fe = SLit 1 /\ f' = 1) ->
  kw_at W3 ms (kW2 cx fpos) (n + pl) f' /\
  kat B cx fpos pc' rl' sl (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms md.
Proof.
  intros cx fpos pc rl sl adv j k2 ly3 S3 W3 ms3 md3 n f E lo hi pl cs xc ms md cs' fe f' pc' rl' HB HAT Hok HW
    B21 B32 B33 B34 Hpl Hnpl HR1 HFr HG HMS HR0 HRL Hfds Hfs Hin1 Hin2 Hfe.
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (BV21 : base_val E (Some 21%nat) = kW2 cx fpos) by exact B21.
  assert (BV34 : base_val E (Some 34%nat) = kW2 cx fpos + n) by exact B34.
  assert (Hf' : 0 <= f' <= 1) by (destruct Hfe as [(_ & ->) | (_ & ->)]; lia).
  assert (HP : forall q, apresent (w_H W3) (ms_mem ms3) q -> apresent (w_H W3) (ms_mem ms) q)
    by (intros q Hq; exact (k3_apres_grows _ _ _ q HG Hq)).
  split.
  { apply (kw_move W3 ms3 W3 ms (kW2 cx fpos) n f (n + pl) f' HW HP).
    - exact (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4096 8 (SOff 32 pl) (n + pl) HR1 B21 Hin1
               ltac:(cbn [sv_denot]; rewrite B32; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
    - destruct Hfe as [(-> & ->) | (-> & ->)].
      + exact (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4104 4 (SOff 33 0) f HR1 B21 Hin2
                 ltac:(cbn [sv_denot]; rewrite B33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
      + exact (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4104 4 (SLit 1) 1 HR1 B21 Hin2
                 eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
    - unfold NL_CHUNK_MAX. lia.
    - exact Hf'. }
  apply (kat_frame_w2 SK B LAWS 0 NW_SIZE cx fpos pc rl sl _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 pc' rl' sl
           W3 ms md HB HAT HMS HR0 HRL (fun x Hx => Hx) Hok (kfsh_fits _ _ _) Hfds Hfs ltac:(lia)
           ltac:(unfold NW_SIZE; lia)).
  - intros q Hq Hnq.
    apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem ms)
             (fun x => kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) HFr); [|exact Hq | intros Hc'; apply Hnq; lia].
    exact (a23_windows E pc lo hi pl cs xc (kW2 cx fpos) n BV21 BV34 ltac:(lia) Hpl Hnpl).
  - exact HP.
Qed.

End b.
End a.
