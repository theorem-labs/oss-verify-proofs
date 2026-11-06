(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v, with its numbers changed; 279 of its 411 lines of code are new or changed and 354 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel's attribute cases a % 6 in {2, 3}: the nested attribute's NL_ALIGN,
   J5 (+0xd68) -> J6 (+0xdb8). Listing (internal path) (internal record, sha256 7bc02d6772b3),
   +0xd68 .. +0xdb4: q := (n + 3) & 0xfffffffc; `bltu q, 4097` (always taken: n <= 4096); s3 := q - n; when q <> n
   checked_memset(w2 + n, 0, s3) (+0xda4); n := n + s3; s3 := slot 0xb0 (the cursor + 8).
   The same code as kernel_a5.v's (B) phase at another pc: the state a5_sp / k3_fl with the conditions a5_pconds
   (a5B_facts); n a multiple of 4 is ONE run; else a run, the call (kernel_a5.v a5_call_ms over AMEMSET), and a run.
   The cut after: kernel_kit.v kat_frame_w2s and kw_move.
   Section hypotheses used: LAWS (the run instances), LV (the callee's pc), AMEMSET (checked_memset).
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

Definition a23P_ss (z : bool) : sstate := mkSS (kpc A23_J5) k3_regs [a5_sp; k3_fl] None (a5B_facts z).

Lemma a23P_windows : forall (E : env) z w,
  base_val E (Some 21%nat) = w ->
  forall b wlo whi a, In (b, wlo, whi) (windows (ss_mem (a23P_ss z))) ->
    base_val E b + wlo <= a < base_val E b + whi -> w <= a < w + NW_SIZE.
Proof.
  intros E z w H21 b wlo whi a Hin Ha.
  unfold a23P_ss, windows in Hin.
  cbn [ss_mem map In a5_sp k3_fl YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  unfold NW_SIZE.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-.
  - lia.
  - rewrite H21 in Ha. lia.
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
Hypothesis LV : LinkVals.
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet 0x53214.

(* ---- THE START: the symbolic state and its writable windows at J5 ---- *)
Lemma a23P_start : forall cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3 rl sl adv g n f k (E : env),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos A23_J5 rl sl (kfsh 0xf8 0 0xf3) true adv g k2 ly3 S3 W3 ms3 md3 ->
  In (21%nat, kW2 cx fpos) rl -> In (25%nat, kW2 cx fpos + NW_N) rl ->
  In (KS_MASK, 0xfffffffc) sl -> In (KS_ROOM, 4097) sl -> In (KS_CN, ka0 cx + 8) sl ->
  In (KS_W2F, kW2 cx fpos + NW_FULL) sl -> In (KS_M4098, 2 ^ 64 - 4098) sl -> In (KS_M4093, 2 ^ 64 - 4093) sl ->
  0 <= k < 5 ->
  E = Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos n f k)) ->
  bv_unsigned (ew E 18) = ka0 cx ->
  forall z : bool, (if z then n mod 4 = 0 else n mod 4 <> 0) ->
  st_ok_pi SEGS pa_val E (a23P_ss z) (restrict (w_H W3) ms3) /\
  awr_ok_x E (ss_mem (a23P_ss z)) (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 rl sl adv g n f k E HB HJ HW HAT I21 I25 IMASK IROOM ICN IW2F I98 I93 Hk
    HEdef E18 z Hz.
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL I21) as R21.
  pose proof (kn_reg_of ms3 _ 25 (kW2 cx fpos + NW_N) HRL I25) as R25.
  pose proof HW as (Hw0 & Hwl & Hpres & Hnv & Hfv & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  destruct (k3_env SK B LAWS cx fpos k2 ly3 S3 md3 ms3 n f k E HB HJB HR0 R21 ltac:(lia) Hfr Hk HEdef)
    as (B9 & B20 & B21 & B32 & B33 & B34 & B35).
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _).
  pose proof (kn_sp SK B cx HB) as (Hac & _ & _ & Hs1 & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & Hs1b & _ & _ & Hsp47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : kernel_c.KERNEL_AK = 4640) by reflexivity.
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by exact B9.
  assert (BV21 : base_val E (Some 21%nat) = kW2 cx fpos) by exact B21.
  pose proof (kn_slot_of cx W3 ms3 _ KS_MASK 0xfffffffc HSL IMASK) as SL_MASK.
  pose proof (kn_slot_of cx W3 ms3 _ KS_ROOM 4097 HSL IROOM) as SL_ROOM.
  pose proof (kn_slot_of cx W3 ms3 _ KS_CN (ka0 cx + 8) HSL ICN) as SL_CN.
  pose proof (kn_slot_of cx W3 ms3 _ KS_W2F (kW2 cx fpos + NW_FULL) HSL IW2F) as SL_W2F.
  pose proof (kn_slot_of cx W3 ms3 _ KS_M4098 (2 ^ 64 - 4098) HSL I98) as SL_M4098.
  pose proof (kn_slot_of cx W3 ms3 _ KS_M4093 (2 ^ 64 - 4093) HSL I93) as SL_M4093.
  pose proof (a5_awf SK B LAWS cx fpos k2 ly3 S3 W3 _ _ HB HJ) as AWF.
  split.
  - (* the symbolic state *)
    rewrite (kn_ms_shape ms3 (BASE + kpc A23_J5) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold a23P_ss. apply pa_entry_st_ok_full.
    + unfold k3_regs.
      apply kn_regs_ok_set; [rewrite HEdef; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
      rewrite R25. cbn [sv_denot]. rewrite B21. reflexivity.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold a5_sp, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; [..|apply Forall_nil].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x98 (SLit 0xfffffffc) 0xfffffffc);
             [reflexivity | exact SL_MASK].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xa8 (SLit 4097) 4097);
             [reflexivity | exact SL_ROOM].
        -- apply (k3_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xb0 (SOff 18 8) (ka0 cx + 8)); [|exact SL_CN].
           cbn [sv_denot]. rewrite E18. reflexivity.
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
    + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, a5_sp, k3_fl.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV9, BV21. rewrite HKA in Hac.
      repeat split; lia.
    + unfold a5B_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok alias_ok].
      split; [|split].
      * unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B20, B21, B32, B33, B34.
        change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
        refine (conj (conj _ (conj eq_refl _)) (conj (conj _ (conj eq_refl _)) (conj (conj _ (conj eq_refl _))
          (conj (conj _ (conj eq_refl _)) (conj (conj _ (conj eq_refl _)) I))))); lia.
      * exact (a5_conds_ok E n z B32 ltac:(lia) Hz).
      * split; [|exact I].
        rewrite (denot_lit_U E (SAlu ALU_ADD (SOff 21 0) (SOff 32 0))), (denot_lit_U E (SOff 34 0)). f_equal.
        rewrite U_SAlu, !U_SOff. cbn [zalu_raw].
        rewrite B21, B32, B34, !Z.add_0_r.
        rewrite (zcanon_id (kW2 cx fpos)), (zcanon_id n) by (unfold M64; lia). reflexivity.
  - (* the writable windows lie in F *)
    unfold a23P_ss. cbn [ss_mem].
    apply awr_ok_x_cons; [intros x Hx; unfold a5_sp in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros x Hx. unfold k3_fl in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV21 in Hx.
    left. apply AWF. unfold NW_SIZE. lia.
Qed.

(* ---- THE END: the cut J6, from the end state's field region, frame and registers ---- *)
Lemma a23P_end : forall POST (Rc Rm Ra : kcx -> Z -> Prop) cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3
    c ci j m k n f adv hd kd left a p n0,
  kfrom SK B POST (a23_at B Rc Rm Ra A23_J6) ->
  kbase SK B cx ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) -> Ra cx left ->
  1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m -> (kd = 0 \/ kd = 7) ->
  1 <= left <= 4 -> 0 <= hd <= n -> 0 <= a < 256 -> ktext cx p -> ka_text cx a p -> 0 <= n0 <= n ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos A23_J5 (a23_rl cx fpos a p n0 left) (a23_sl cx fpos c ci m k hd kd)
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  forall (E : env) (ms : machine_state) md cs',
  bv_unsigned (ew E 21) = kW2 cx fpos -> bv_unsigned (ew E 32) = n -> bv_unsigned (ew E 33) = f ->
  bv_unsigned (ew E 18) = ka0 cx ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 21%nat) 4096 4112 4096 4112 cs') ->
  (forall q, 0 <= q < 2 ^ 64 -> ~ ((kW2 cx fpos <= q < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx - ESTACK <= q < ksp1 cx)) ->
     aview SEGS (w_H W3) (ms_mem ms) q = aview SEGS (w_H W3) (ms_mem ms3) q) ->
  (forall q, apresent (w_H W3) (ms_mem ms3) q -> apresent (w_H W3) (ms_mem ms) q) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  kms A23_J6 ms ->
  (forall r, In r nx_keep0 -> getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  (forall r, In r (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 24; 22; 23; 27; 26]%nat) ->
     getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 25)) = sv_denot E (SOff 21 4096) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 19)) = sv_denot E (SOff 18 8) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  In (YP09.mkChunk 4096
        (CVal 8 (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SUB (SAlu ALU_AND (SOff 32 3) (SLit 0xfffffffc)) (SOff 32 0)))))
     cs' ->
  In (YP09.mkChunk 4104 (CVal 4 (SOff 33 0))) cs' ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd left a p n0 HN HB HFR HRc HRm HRa Hc Hci
    Hj Hm Hk Hkd Hl Hhd Ha Htx Hka Hn0 HW HAT E ms md cs' B21 B32 B33 B18 HR1 UN HP HJ HMS HK0 HKN H25 H19 Hfds Hfs Hin1
    Hin2.
  pose proof HAT as (_ & HR0 & HRL & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HK : forall r : nat, In r [21; 24; 22; 23; 27; 26]%nat ->
            getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
    by (intros r Hr; exact (HKN _ (kn_in_map5 r _ Hr))).
  assert (Hn' : U E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SUB (SAlu ALU_AND (SOff 32 3) (SLit 0xfffffffc)) (SOff 32 0)))
                = (n + 0 + 3) / 4 * 4) by exact (a5_U_fin E n 0 3 B32 eq_refl ltac:(lia)).
  rewrite Z.add_0_r in Hn'.
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFR).
  exists c, ci, j, m, k, ((n + 3) / 4 * 4), f, adv, hd, kd, left, a, p, n0.
  split; [exact HRc|]. split; [exact HRm|]. split; [exact HRa|]. split; [exact Hc|]. split; [exact Hci|].
  split; [exact Hj|]. split; [exact Hm|]. split; [exact Hk|]. split; [exact Hkd|]. split; [exact Hl|].
  split; [lia|]. split; [exact Ha|]. split; [exact Htx|]. split; [exact Hka|]. split; [lia|].
  split.
  { apply (kw_move W3 ms3 W3 ms (kW2 cx fpos) n f ((n + 3) / 4 * 4) f HW HP).
    - refine (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4096 8 _ ((n + 3) / 4 * 4) HR1 B21 Hin1 _
               ltac:(cbn; lia) ltac:(cbn; lia)).
      rewrite denot_lit_U, Hn'. reflexivity.
    - exact (field_of_region E _ 21 (kW2 cx fpos) _ _ _ _ _ 4104 4 (SOff 33 0) f HR1 B21 Hin2
               ltac:(cbn [sv_denot]; rewrite B33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
    - unfold NL_CHUNK_MAX. lia.
    - exact Hfr. }
  apply (kat_frame_w2s SK B LAWS 0 NW_SIZE cx fpos A23_J5 _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 A23_J6 _ _
           W3 ms md HB HAT HMS (kregs0_keep cx ms3 ms HK0 HR0)).
  - unfold kregs_eq, a23_rl. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    + rewrite H19. cbn [sv_denot]. rewrite B18. reflexivity.
    + rewrite (HK 21%nat) by kn_in. apply (kn_reg_of ms3 _ 21 _ HRL). kn_in.
    + rewrite (HK 24%nat) by kn_in. apply (kn_reg_of ms3 _ 24 _ HRL). kn_in.
    + rewrite H25. cbn [sv_denot]. rewrite B21. reflexivity.
    + rewrite (HK 22%nat) by kn_in. apply (kn_reg_of ms3 _ 22 _ HRL). kn_in.
    + rewrite (HK 23%nat) by kn_in. apply (kn_reg_of ms3 _ 23 _ HRL). kn_in.
    + rewrite (HK 27%nat) by kn_in. apply (kn_reg_of ms3 _ 27 _ HRL). kn_in.
    + rewrite (HK 26%nat) by kn_in. apply (kn_reg_of ms3 _ 26 _ HRL). kn_in.
  - intros x Hx. exact Hx.
  - reflexivity.
  - apply kfsh_fits.
  - exact Hfds.
  - exact Hfs.
  - lia.
  - lia.
  - intros q Hq Hnq. apply UN; [exact Hq|]. intros [Hc'|Hc']; apply Hnq; [left; lia | right; exact Hc'].
  - exact HP.
Qed.

Ltac a23_md := first [ exact (proj1 (wvb_fds_fs _ _ _)) | exact (proj2 (wvb_fds_fs _ _ _)) | reflexivity ].

(* ---- THE PHASE: NL_ALIGN of the nested attribute ---- *)
Theorem a23_pad : forall POST (Rc Rm Ra : kcx -> Z -> Prop),
  kfrom SK B POST (a23_at B Rc Rm Ra A23_J6) -> kfrom SK B POST (a23_at B Rc Rm Ra A23_J5).
Proof.
  intros POST Rc Rm Ra HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (qc & qci & qj & qm & qk & qn & qf & qadv & qhd & qkd & ql & qa & qp & qn0 & HRc & HRm & HRa & Hc
    & Hci & Hj & Hm & Hk & Hkd & Hl & Hhd & Ha & Htx & Hka & Hn0 & HW & HAT).
  pose proof HAT as (_ & HR0 & HRL & _ & HFRM & HSH & _ & HJB & _).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL ltac:(kn_in)) as R21.
  remember (Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk))) as Eq3 eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM Eq3) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk)) Eq3)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (k3_env SK B LAWS cx fpos k2 ly3 S3 md3 ms3 qn qf qk Eq3 HB HJB HR0 R21 ltac:(lia) Hfr ltac:(lia) HEdef)
    as (B9 & B20 & B21 & B32 & B33 & B34 & B35).
  assert (Hka0 : 0 <= ka0 cx < 2 ^ 47)
    by (destruct (kn_ard_bound SK B LAWS cx (ka0 cx) HB (kn_ard_cur cx (ka0 cx) ltac:(lia))) as (Hq & _); lia).
  assert (B18 : bv_unsigned (ew Eq3 18) = ka0 cx).
  { rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 18 18%bv eq_refl).
    destruct HR0 as (_ & _ & _ & _ & _ & R18 & _). rewrite R18. unfold w64. apply unsigned_lit_small. lia. }
  assert (BV21 : base_val Eq3 (Some 21%nat) = kW2 cx fpos) by exact B21.
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _).
  pose proof (kn_sp SK B cx HB) as (Hac & Hsp2 & _ & Hs1 & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & Hs1b & Hs1c & _ & Hsp47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : kernel_c.KERNEL_AK = 4640) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  pose proof (a23P_start cx fpos k2 ly3 S3 W3 ms3 md3 _ _ qadv (Some qj) qn qf qk Eq3 HB HJ HW HAT
                ltac:(kn_in) ltac:(kn_in)
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in) ltac:(apply in_or_app; right; kn_in)
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)
                ltac:(lia) HEdef B18) as KST.
  pose proof (a23P_end POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv qhd qkd ql qa qp qn0 HN HB
                HFR HRc HRm HRa Hc Hci Hj Hm Hk Hkd Hl Hhd Ha Htx Hka Hn0 HW HAT) as KFIN.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose proof (a5_shok_fl SK B LAWS cx fpos k2 ly3 S3 md3 W3 (ms_mem ms3) Eq3 HB HJB
                (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) B20 B21) as SHOK.
  destruct (Z.eq_dec (qn mod 4) 0) as [Hz|Hz].
  - (* n a multiple of 4: one run *)
    destruct (KST true Hz) as (HS & HAWR).
    paj_run_to_tok RUNTO HS HJ SHOK k3_span (kpc A23_J6); [exact HAWR|].
    lazymatch goal with
    | HS' : st_ok_pi _ _ ?E ?ssx (restrict _ ?msn),
      HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
      HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
      let HR1 := fresh "HR1" in
      spregion HS' 1%nat HR1;
      apply (KFIN E msn mdn _ B21 B32 B33 B18 HR1);
      [ intros q Hq Hnq;
        apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem msn)
                 (fun x => kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) HFr');
        [exact (a23P_windows E true (kW2 cx fpos) BV21) | exact Hq | intros Hc'; apply Hnq; left; exact Hc']
      | intros q Hq; exact (k3_apres_grows _ _ _ q HG' Hq)
      | assumption
      | apply (kn_kms_of _ E ssx msn A23_J6 HS'); vm_compute; reflexivity
      | exact (regs_kept_of_st_ok_pi E ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity))
      | exact (regs_kept_of_st_ok_pi E ssx _ _ _ (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 24; 22; 23; 27; 26]%nat)
                 HS' HAG ltac:(vm_compute; reflexivity))
      | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
      | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
      | a23_md
      | a23_md
      | kn_in
      | kn_in ]
    end.
  - (* else: a run to the call, checked_memset(w2 + n, 0, pad), a run to J6 *)
    destruct (KST false Hz) as (HS & HAWR).
    pose proof HS as HS0.
    paj_run_tok RUN HS HJ SHOK k3_span; [exact HAWR|].
    lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1; rename HSx into HS1 end.
    lazymatch goal with HFx : frame_of _ _ _ _ |- _ => rename HFx into HFr1 end.
    lazymatch goal with HGx : mem_grows _ _ |- _ => rename HGx into HG1 end.
    assert (UN1 : forall q, 0 <= q < 2 ^ 64 -> ~ (kW2 cx fpos <= q < kW2 cx fpos + NW_SIZE) ->
              aview SEGS (w_H W3) (ms_mem ms1) q = aview SEGS (w_H W3) (ms_mem ms3) q).
    { intros q Hq Hnq.
      apply (kept_of_frame (segs := SEGS) Eq3 _ (w_H W3) (ms_mem ms3) (ms_mem ms1)
               (fun x => kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) HFr1);
        [exact (a23P_windows Eq3 false (kW2 cx fpos) BV21) | exact Hq | exact Hnq]. }
    pose proof (fun q Hq => k3_apres_grows _ _ _ q HG1 Hq) as P1.
    pose proof (a5_reg_same Eq3 _ _ (w_H W3) ms3 ms1 [2; 3; 4] HS0 HS1 ltac:(vm_compute; reflexivity)) as KEEP.
    sreg HS1 (10%bv : bv 5) R10. sreg HS1 (11%bv : bv 5) R11. sreg HS1 (12%bv : bv 5) R12.
    prreg HS1 (1%bv : bv 5) R1.
    cbn [ms_regs restrict mkst] in R10, R11, R12.
    pmkst HS1.
    rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_memset) with 0x53214.
    eapply (a5_call_ms SK B LAWS AMEMSET cx fpos k2 ly3 S3 W3 ms3 md3 (ms_mem ms1) _ (ms_regs ms1) _ qn
              ((qn + 3) / 4 * 4 - qn) (POST cx) HB HJ HJB HSH UN1);
      [ lia | lia | unfold NW_SIZE; lia
      | rewrite R10; cbn [sv_denot]; rewrite B34, Z.add_0_r; reflexivity
      | rewrite R11; reflexivity
      | rewrite R12, denot_lit_U, (a5_U_len Eq3 qn 0 3 B32 eq_refl ltac:(lia)), !Z.add_0_r; reflexivity
      | rewrite (KEEP 2%bv) by reflexivity; exact (proj1 HR0)
      | rewrite (KEEP 3%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 HR0))))
      | rewrite (KEEP 4%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 (proj2 HR0)))))
      | exact R1
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | ].
    intros regs2 mem2 md2 HJ2 HP2 Hfr2 Hpres2 Hsbm.
    jafter_call_keep_pi HS1 40%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0; 1]%nat HS2.
    lazymatch type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
    { destruct HFRM as (_ & _ & _ & _ & HFP & _).
      cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite B9; intros q Hq.
        + apply kn_mbyte_of_aview. apply Hfr2; [lia | lia | rewrite HES; lia].
        + lia.
      - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite B21; intros q Hq.
        + apply kn_mbyte_of_aview. apply Hfr2; [lia | lia | rewrite HES; lia].
        + intros _. apply kn_apresent_writable. apply Hpres2, P1, HFP. rewrite kn_fsb8. lia. }
    rewrite <- restrict_mkst_fx in HS2.
    remember (havoc Eq3 40 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS2.
    assert (HEI2 : img_env pa_val A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
    assert (HAG2 : env_agree 32 (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk)) E2)
      by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAG]).
    assert (C21 : bv_unsigned (ew E2 21) = kW2 cx fpos) by (rewrite HE2, ew_havoc_old by lia; exact B21).
    assert (C32 : bv_unsigned (ew E2 32) = qn) by (rewrite HE2, ew_havoc_old by lia; exact B32).
    assert (C33 : bv_unsigned (ew E2 33) = qf) by (rewrite HE2, ew_havoc_old by lia; exact B33).
    assert (C18 : bv_unsigned (ew E2 18) = ka0 cx) by (rewrite HE2, ew_havoc_old by lia; exact B18).
    assert (C20 : bv_unsigned (ew E2 20) = SHADOW_OFF) by (rewrite HE2, ew_havoc_old by lia; exact B20).
    assert (CV21 : base_val E2 (Some 21%nat) = kW2 cx fpos) by exact C21.
    clear HE2.
    assert (UNc : forall q, 0 <= q < 2 ^ 64 ->
              ~ ((kW2 cx fpos <= q < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx - ESTACK <= q < ksp1 cx)) ->
              aview SEGS (w_H W3) mem2 q = aview SEGS (w_H W3) (ms_mem ms3) q).
    { intros q Hq Hnq.
      rewrite (Hfr2 q Hq ltac:(intros Hc'; apply Hnq; left; unfold NW_SIZE; lia)
                 ltac:(intros Hc'; apply Hnq; right; exact Hc')).
      apply UN1; [exact Hq | intros Hc'; apply Hnq; left; exact Hc']. }
    pose proof (a5_shok_fl SK B LAWS cx fpos k2 ly3 S3 md3 W3 mem2 E2 HB HJB
                  (a5_w2_ra SK B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 mem2 HB HJB HSH UNc) C20 C21) as SHOK2.
    paj_run_to_tok RUNTO HS2 HJ2 SHOK2 k3_span (kpc A23_J6).
    { cbn [ss_mem].
      apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
      apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite CV21 in Hx.
      left. apply (a5_awf SK B LAWS cx fpos k2 ly3 S3 W3 _ _ HB HJ2). unfold NW_SIZE. lia. }
    lazymatch goal with
    | HS' : st_ok_pi _ _ ?E ?ssx (restrict _ ?msn),
      HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
      HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
      let HR1 := fresh "HR1" in
      spregion HS' 1%nat HR1;
      apply (KFIN E msn mdn _ C21 C32 C33 C18 HR1);
      [ intros q Hq Hnq;
        rewrite (kept_of_frame (segs := SEGS) E _ (w_H W3) mem2 (ms_mem msn)
                   (fun x => kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) HFr' ltac:(
                     intros b wlo whi x Hin Hx; unfold windows in Hin;
                     cbn [ss_mem map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
                     destruct Hin as [Hq' | [Hq' | []]]; injection Hq' as <- <- <-;
                     [lia | rewrite CV21 in Hx; unfold NW_SIZE; lia])
                   q Hq ltac:(intros Hc'; apply Hnq; left; exact Hc'));
        exact (UNc q Hq Hnq)
      | intros q Hq; exact (k3_apres_grows _ _ _ q HG' (Hpres2 q (P1 q Hq)))
      | assumption
      | apply (kn_kms_of _ E ssx msn A23_J6 HS'); vm_compute; reflexivity
      | exact (regs_kept_of_st_ok_pi E ssx _ _ _ nx_keep0 HS' HAG2 ltac:(vm_compute; reflexivity))
      | exact (regs_kept_of_st_ok_pi E ssx _ _ _ (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [21; 24; 22; 23; 27; 26]%nat)
                 HS' HAG2 ltac:(vm_compute; reflexivity))
      | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
      | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
      | rewrite ?(proj1 (wvb_fds_fs _ _ _)), (proj1 (kn_sbm_fds_fs _ _ Hsbm)); a23_md
      | rewrite ?(proj2 (wvb_fds_fs _ _ _)), (proj2 (kn_sbm_fds_fs _ _ Hsbm)); a23_md
      | kn_in
      | kn_in ]
    end.
Qed.

End b.
End a.
