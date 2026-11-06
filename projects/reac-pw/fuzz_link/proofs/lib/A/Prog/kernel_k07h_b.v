(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v; 347 of its 537 lines of code are new or changed and 296 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), kinds 0 and 7, the head of the message
   (lib/A/Prog/kernel_defs.v kin_kind at kd = 0, 7, +0x6e4) to a private cut at +0x960 (k7_c960). Listing
   (internal path) (internal record, sha256 7bc02d6772b3), +0x6e4 .. +0x95c.

   THE CODE. slot 0x90 := n (hd, +0x6f4); five puts into w2 at w2 + n (u32 0, u16 0x10, u16 0, u32 1, u32 0), each
   behind a room test `bltu (2^64 - 4098), n + L - 4097` (taken when n + L <= 4096; not taken: w2.full := 1); slot
   0x88 := a6 = kd (+0x92c); a room test for 16 bytes and checked_memset(w2 + n, 0, 16) (+0x950); n += 16.
   THE STATE: kernel_k3.v's (registers sr_atoms but s9 = w2 + 4096; atoms 32 = n, 33 = full, 34 = w2 + n, 35 = k;
   w2's fields and the put bytes as regions; the alias w2 + n = atom 34), with the slots 0x88 .. 0x98 writable and
   s1's range (atom 9) in the facts. The taken room tests are in the facts' conditions (k3_conds, by k3_cond_ok).
   THE GROUPS (n at the cut; pl the bytes put; the taken tests' offsets c of `n + c`):
     n <= 4064: pl 16 and the memset | 4065..4080: 16 | 4081..4084: 12 | 4085..4088: 8 | 4089..4090: 6 |
     4091..4092: 4 | 4093..4094: 2 (the u16 0x10 only) | 4095..4096: 0.
   n <= 4064: a run to the call, the call (kernel_a5.v a5_call_ms), a run to +0x960; else one run to +0x960.
   THE CUT: kat_frame (kernel_kit.v) with X = w2, the callee's window and the slots 0x88 .. 0x98; the two new
   slots from the end state's slot region (kat_slots); kw_move for w2's fields.

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
kernel_c kernel_defs kernel_kit kernel_next kernel_k3 kernel_a5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Definition KP_K960 : Z := 0x960.   (* kinds 0, 7: `lbu a0, 0(s8)`, the cursor's check *)

(* ---- the symbolic state at +0x6e4 ---- *)
Definition k7_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x88 0xe0 0x88 0x98
    [YP09.mkChunk 0xc8 (CVal 8 (SOff 21 4104)); YP09.mkChunk 0xd0 (CVal 8 (SLit (2 ^ 64 - 4098)));
     YP09.mkChunk 0xd8 (CVal 8 (SLit (2 ^ 64 - 4093)))].
Definition k7B_facts (lo hi : Z) (cs : list Z) : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 0); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (21%nat, mkAF 4096 (2 ^ 47 - 4113) 0); (32%nat, mkAF lo hi 0); (33%nat, mkAF 0 1 0);
           (34%nat, mkAF 4096 (2 ^ 47 - 4113) 0)]
    (k3_conds cs) [(SAlu ALU_ADD (SOff 21 0) (SOff 32 0), SOff 34 0)].
Definition k7B_ss (lo hi pl : Z) (cs : list Z) : sstate :=
  mkSS (kpc KP_K07) k3_regs [k7_sp; k3_fl; k3_pr pl] None (k7B_facts lo hi cs).

Lemma k7B_windows : forall (E : env) lo hi pl cs w n s1,
  base_val E (Some 9%nat) = s1 -> base_val E (Some 21%nat) = w -> base_val E (Some 34%nat) = w + n ->
  0 <= n -> 0 <= pl -> n + pl <= 4096 ->
  forall b wlo whi a, In (b, wlo, whi) (windows (ss_mem (k7B_ss lo hi pl cs))) ->
    base_val E b + wlo <= a < base_val E b + whi -> (w <= a < w + NW_SIZE) \/ (s1 + 0x88 <= a < s1 + 0x98).
Proof.
  intros E lo hi pl cs w n s1 H9 H21 H34 Hn Hpl Hnpl b wlo whi a Hin Ha.
  unfold k7B_ss, windows in Hin.
  cbn [ss_mem map In k7_sp k3_fl k3_pr YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  unfold NW_SIZE.
  destruct Hin as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <- <-.
  - rewrite H9 in Ha. right. lia.
  - rewrite H21 in Ha. left. lia.
  - rewrite H34 in Ha. left. lia.
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

(* the private cut at +0x960: the message's start hd and its kind kd spilled, s6 = m *)
Definition k7_c960 (Rc Rm : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j m k n f adv hd kd, Rc cx (c - ci) /\ Rm cx (m - k) /\
  1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\ 1 <= m <= 5 /\ 0 <= k < m /\ (kd = 0 \/ kd = 7) /\ 0 <= hd <= n /\
  kw_at W3 ms3 (kW2 cx fpos) n f /\
  kat B cx fpos KP_K960
    [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (22%nat, m)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

(* the frame of a step that writes w2, the callee's window and the slots 0x88 .. 0x98 *)
Lemma k7_frame : forall cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4,
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms4 -> kregs0 cx ms4 -> kregs_eq ms4 rl' -> incl sl' sl -> kslots_okb sl' = true ->
  kslots_avoidb 0x88 0x98 sl' = true ->
  (length sh <= 2048)%nat -> m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ ((kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx - ESTACK <= a < ksp1 cx) \/
        (ksp1 cx + 0x88 <= a < ksp1 cx + 0x98)) ->
     aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  kat B cx fpos pc' rl' sl' sh live adv g k2 ly3 S3 W4 ms4 md4.
Proof.
  intros cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4
    HB HK HMS HR0 HRL Hsl Hok Hav Hsh Hfds Hfs UN HP.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & HJB & _).
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  apply (kat_frame SK B LAWS
           (fun a => (kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx - ESTACK <= a < ksp1 cx) \/
                     (ksp1 cx + 0x88 <= a < ksp1 cx + 0x98))
           cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4
           HB HK HMS HR0 HRL Hsl Hsh Hfds Hfs UN HP).
  - intros a [Ha | [Ha | Ha]].
    + apply (kX_in_F cx fpos KN_W2 (KN_W2 + NW_SIZE) a); [unfold KN_W2; lia | rewrite Hfb; unfold KN_W2, NW_SIZE; lia |].
      unfold kW2 in Ha. lia.
    + exact (kX_in_win SK B cx fpos a HB Ha).
    + exact (kX_in_sl SK B cx fpos 0x88 0x98 a HB ltac:(lia) ltac:(lia) Ha).
  - apply kX_miss_or; [|apply kX_miss_or].
    + apply (kX_miss_F SK B LAWS cx fpos k2 ly3 S3 md3 sl' _ KN_W2 (KN_W2 + NW_SIZE)); [exact HB | exact HJB | exact Hok
        | lia | unfold KN_W2; lia | rewrite Hfb; unfold KN_W2, NW_SIZE; lia |].
      intros a Ha. unfold kW2 in Ha. lia.
    + apply (kX_miss_win SK B LAWS cx fpos k2 ly3 S3 md3 sl' _); [exact HB | exact HJB | exact Hok | lia |].
      intros a Ha. exact Ha.
    + apply (kX_miss_sl SK B LAWS cx fpos k2 ly3 S3 md3 sl' _ 0x88 0x98); [exact HB | exact HJB | exact Hok | exact Hav
        | lia | lia | lia |].
      intros a Ha. exact Ha.
Qed.

(* a word of a region's chunk *)
Lemma k7_rd_of_region : forall E (H : word -> bool) (mm : word -> option byte) n b cs lo hi wlo whi off e v,
  region_ok SEGS E (mrestrict H mm) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H mm) (b + off) = Some v.
Proof.
  intros E H mm n b cs lo hi wlo whi off e v HR Hb Hin He Hv.
  apply (rdword_of_val_mem SEGS H mm (b + off) v); [|exact Hv].
  apply (field_of_region (segs := SEGS) E (mrestrict H mm) n b cs lo hi wlo whi off 8 e v HR Hb Hin He).
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  - change (Z.of_N 8) with 8. lia.
Qed.

(* ---- THE START: the symbolic state, its shadow entries and its writable windows at +0x6e4 ---- *)
Lemma k7B_start : forall cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3 c ci j m k n f adv kd (E : env),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_K07
    [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N);
     (22%nat, m); (16%nat, kd)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  0 <= k < 5 ->
  E = Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos n f k)) ->
  forall lo hi pl cs,
  lo <= n <= hi -> 0 <= pl -> n + pl <= 4096 ->
  regions_wf [k7_sp; k3_fl; k3_pr pl] = true ->
  Forall (fun c => -4098 < n + c < 0) cs ->
  st_ok_pi SEGS pa_val E (k7B_ss lo hi pl cs) (restrict (w_H W3) ms3) /\
  sh_ok SEGS k3_Bx (k3_SH pl) E (mrestrict (w_H W3) (ms_mem ms3)) /\
  awr_ok_x E (ss_mem (k7B_ss lo hi pl cs)) (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv kd E HB HJ HW HAT Hk HEdef lo hi pl cs Hn Hpl Hnpl Hwf
    Hcs.
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL ltac:(kn_in)) as R21.
  pose proof (kn_reg_of ms3 _ 25 (kW2 cx fpos + NW_N) HRL ltac:(kn_in)) as R25.
  pose proof HW as (Hw0 & Hwl & Hpres & Hnv & Hfv & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  destruct (k3_env SK B LAWS cx fpos k2 ly3 S3 md3 ms3 n f k E HB HJB HR0 R21 ltac:(lia) Hfr Hk HEdef)
    as (B9 & B20 & B21 & B32 & B33 & B34 & B35).
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _ & HFsh).
  pose proof kn_band as (KB1 & KB2).
  assert (KLS : kLowShadowBeg = 2147446784) by reflexivity.
  pose proof (kn_sp SK B cx HB) as (Hac & Hsp2 & _ & Hs1 & _ & Hstk & Hsp0 & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & Hs1b & Hs1c & _ & Hsp47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : kernel_c.KERNEL_AK = 4640) by reflexivity.
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by exact B9.
  assert (BV21 : base_val E (Some 21%nat) = kW2 cx fpos) by exact B21.
  assert (BV34 : base_val E (Some 34%nat) = kW2 cx fpos + n) by exact B34.
  pose proof (kn_slot_of cx W3 ms3 _ KS_W2F (kW2 cx fpos + NW_FULL) HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_W2F.
  pose proof (kn_slot_of cx W3 ms3 _ KS_M4098 (2 ^ 64 - 4098) HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_M4098.
  pose proof (kn_slot_of cx W3 ms3 _ KS_M4093 (2 ^ 64 - 4093) HSL
                ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_M4093.
  pose proof (a5_awf SK B LAWS cx fpos k2 ly3 S3 W3 _ _ HB HJ) as AWF.
  pose proof (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) as HRA.
  pose proof (kn_spill_wr SK B LAWS cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ) as HSW.
  split; [|split].
  - (* the symbolic state *)
    rewrite (kn_ms_shape ms3 (BASE + kpc KP_K07) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold k7B_ss. apply pa_entry_st_ok_full.
    + unfold k3_regs.
      apply kn_regs_ok_set; [rewrite HEdef; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
      rewrite R25. cbn [sv_denot]. rewrite B21. reflexivity.
    + exact Hwf.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * unfold k7_sp, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV9.
        split; [lia|]. split; [lia|]. split.
        { intros o Ho. replace (ksp1 cx + o) with (ksp1 cx + o) by lia. apply HSW. lia. }
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
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
    + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, k7_sp, k3_fl, k3_pr.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV9, BV21, BV34. rewrite HKA in Hac.
      repeat split; lia.
    + unfold k7B_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok alias_ok].
      split; [|split].
      * unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B9, B20, B21, B32, B33, B34.
        change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
        repeat split; lia.
      * exact (k3_conds_ok E n cs B32 Hcs).
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
  - (* the writable windows: the slots in the call's stack window, w2 in F *)
    unfold k7B_ss. cbn [ss_mem].
    apply awr_ok_x_cons.
    { intros x Hx. unfold k7_sp in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV9 in Hx.
      left. split; [left; lia | lia]. }
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    + intros x Hx. unfold k3_fl in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV21 in Hx.
      left. apply AWF. unfold NW_SIZE. lia.
    + intros x Hx. unfold k3_pr in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV34 in Hx.
      left. apply AWF. unfold NW_SIZE. lia.
Qed.

(* ---- THE END: the cut at +0x960 from the end state's regions, frame and registers ---- *)
Lemma k7B_fin : forall POST (Rc Rm : kcx -> Z -> Prop) cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3
    c ci j m k n f adv kd (E : env),
  kfrom SK B POST (k7_c960 Rc Rm) ->
  kbase SK B cx ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) ->
  1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m -> (kd = 0 \/ kd = 7) ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_K07
    [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N);
     (22%nat, m); (16%nat, kd)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  bv_unsigned (ew E 9) = ksp1 cx -> bv_unsigned (ew E 16) = kd ->
  bv_unsigned (ew E 21) = kW2 cx fpos -> bv_unsigned (ew E 32) = n -> bv_unsigned (ew E 33) = f ->
  forall pl, 0 <= pl -> n + pl <= 4096 ->
  forall (ms : machine_state) md cs0 cs1 fe f',
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 9%nat) 0x88 0xe0 0x88 0x98 cs0) ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 21%nat) 4096 4112 4096 4112 cs1) ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ ((kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx - ESTACK <= a < ksp1 cx) \/
        (ksp1 cx + 0x88 <= a < ksp1 cx + 0x98)) ->
     aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms) a) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  kms KP_K960 ms ->
  (forall r, In r nx_keep0 -> getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  (forall r, In r (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [19; 21; 24; 22]%nat) ->
     getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 25)) = sv_denot E (SOff 21 4096) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  In (YP09.mkChunk 0x88 (CVal 8 (SOff 16 0))) cs0 ->
  In (YP09.mkChunk 0x90 (CVal 8 (SOff 32 0))) cs0 ->
  In (YP09.mkChunk 4096 (CVal 8 (SOff 32 pl))) cs1 ->
  In (YP09.mkChunk 4104 (CVal 4 fe)) cs1 ->
  (fe = SOff 33 0 /\ f' = f) \/ (fe = SLit 1 /\ f' = 1) ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv kd E HN HB HFR HRc HRm Hc Hci Hj Hm Hk Hkd HW
    HAT B9 B16 B21 B32 B33 pl Hpl Hnpl ms md cs0 cs1 fe f' HR0' HR1 UN HP HJ HMS HK0 HKN H25 Hfds Hfs Hin88 Hin90
    Hin1 Hin2 Hfe.
  pose proof HAT as (_ & HR0 & HRL & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (Hf' : 0 <= f' <= 1) by (destruct Hfe as [(_ & ->) | (_ & ->)]; lia).
  assert (HK : forall r : nat, In r [19; 21; 24; 22]%nat ->
            getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
    by (intros r Hr; exact (HKN _ (kn_in_map5 r _ Hr))).
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFR).
  exists c, ci, j, m, k, (n + pl), f', adv, n, kd.
  split; [exact HRc|]. split; [exact HRm|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|].
  split; [exact Hm|]. split; [exact Hk|]. split; [exact Hkd|]. split; [lia|].
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
  (* the old slots by the frame, then the two new ones off the slot region *)
  apply (kat_slots B cx fpos KP_K960 _ (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])
           [(KS_HD, n); (KS_KD, kd)] _ _ true adv (Some j) k2 ly3 S3 W3 ms md).
  - apply (k7_frame cx fpos KP_K07 _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 KP_K960 _ _ W3 ms md HB HAT HMS
             (kregs0_keep cx ms3 ms HK0 HR0)); [| intros x Hx; exact Hx | reflexivity | reflexivity | apply kfsh_fits
             | exact Hfds | exact Hfs | exact UN | exact HP].
    unfold kregs_eq. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    + rewrite (HK 19%nat) by kn_in. apply (kn_reg_of ms3 _ 19 (ka0 cx + 8) HRL). kn_in.
    + rewrite (HK 21%nat) by kn_in. apply (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL). kn_in.
    + rewrite (HK 24%nat) by kn_in. apply (kn_reg_of ms3 _ 24 (kS8 cx) HRL). kn_in.
    + rewrite H25. cbn [sv_denot]. rewrite B21. reflexivity.
    + rewrite (HK 22%nat) by kn_in. apply (kn_reg_of ms3 _ 22 m HRL). kn_in.
  - unfold kslots_eq. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + exact (k7_rd_of_region E (w_H W3) (ms_mem ms) 9 (ksp1 cx) cs0 _ _ _ _ 0x90 (SOff 32 0) n HR0' B9 Hin90
               ltac:(cbn [sv_denot]; rewrite B32, Z.add_0_r; reflexivity) ltac:(lia)).
    + exact (k7_rd_of_region E (w_H W3) (ms_mem ms) 9 (ksp1 cx) cs0 _ _ _ _ 0x88 (SOff 16 0) kd HR0' B9 Hin88
               ltac:(cbn [sv_denot]; rewrite B16, Z.add_0_r; reflexivity) ltac:(lia)).
  - intros x Hx. exact Hx.
Qed.

(* the run of one group, from +0x6e4 to +0x960 (KST: k7B_start, KFIN: k7B_fin at the cut) *)
Ltac k7B_go cx fpos KST KFIN RUNTO HJ HAG B9 B21 B34 lo hi pl cs fv fe :=
  let HS := fresh "HS" in let SHOK := fresh "SHOK" in let HAWR := fresh "HAWR" in
  destruct (KST lo hi pl cs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              ltac:(repeat (apply Forall_cons; [cbv beta; lia|]); apply Forall_nil)) as (HS & SHOK & HAWR);
  paj_run_to_tok RUNTO HS HJ SHOK k3_span (kpc KP_K960); [exact HAWR|];
  lazymatch goal with
  | HS' : st_ok_pi _ _ ?E ?ssx (restrict _ ?msn),
    HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
    HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    let HR0 := fresh "HR0" in let HR1 := fresh "HR1" in
    spregion HS' 0%nat HR0; spregion HS' 1%nat HR1;
    apply (KFIN pl ltac:(lia) ltac:(lia) msn mdn _ _ fe fv HR0 HR1);
    [ intros q Hq Hnq;
      apply (kept_of_frame (segs := pa_segs) E _ _ _ _
               (fun x => (kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx + 0x88 <= x < ksp1 cx + 0x98)) HFr');
      [ exact (k7B_windows E lo hi pl cs _ _ _ B9 B21 B34 ltac:(lia) ltac:(lia) ltac:(lia))
      | exact Hq | intros [Hc'|Hc']; apply Hnq; [left; exact Hc' | right; right; exact Hc'] ]
    | intros q Hq; exact (k3_apres_grows _ _ _ q HG' Hq)
    | assumption
    | apply (kn_kms_of _ E ssx msn KP_K960 HS'); vm_compute; reflexivity
    | exact (regs_kept_of_st_ok_pi E ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity))
    | exact (regs_kept_of_st_ok_pi E ssx _ _ _ (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [19; 21; 24; 22]%nat)
               HS' HAG ltac:(vm_compute; reflexivity))
    | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
    | exact (proj1 (wvb_fds_fs _ _ _))
    | exact (proj2 (wvb_fds_fs _ _ _))
    | kn_in | kn_in | kn_in | kn_in
    | first [left; split; reflexivity | right; split; reflexivity] ]
  end.

Ltac a5_md := first [ exact (proj1 (wvb_fds_fs _ _ _)) | exact (proj2 (wvb_fds_fs _ _ _)) | reflexivity ].

(* ---- THE PHASE: the head ---- *)
Theorem k7_head : forall POST (Rc Rm : kcx -> Z -> Prop),
  kfrom SK B POST (k7_c960 Rc Rm) -> forall kd, kd = 0 \/ kd = 7 -> kfrom SK B POST (kin_kind B Rc Rm kd).
Proof.
  intros POST Rc Rm HN kd Hkd cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (qc & qci & qj & qm & qk & qn & qf & qadv & HRc & HRm & Hc & Hci & Hj & Hm & Hk & _ & HW & _ & HAT).
  assert (Hpc : kind_pc kd = KP_K07) by (destruct Hkd as [-> | ->]; reflexivity).
  rewrite Hpc in HAT.
  pose proof HAT as (_ & HR0 & HRL & _ & HFRM & HSH & _ & HJB & _).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL ltac:(kn_in)) as R21.
  pose proof (kn_reg_of ms3 _ 16 kd HRL ltac:(kn_in)) as R16.
  remember (Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk))) as Eq3 eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM Eq3) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk)) Eq3)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (k3_env SK B LAWS cx fpos k2 ly3 S3 md3 ms3 qn qf qk Eq3 HB HJB HR0 R21 ltac:(lia) Hfr ltac:(lia) HEdef)
    as (B9 & B20 & B21 & B32 & B33 & B34 & B35).
  assert (B16 : bv_unsigned (ew Eq3 16) = kd).
  { rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 16 (Z_to_bv 5 (Z.of_nat 16)) eq_refl), R16.
    unfold w64. apply unsigned_lit_small. destruct Hkd as [-> | ->]; lia. }
  assert (BV9 : base_val Eq3 (Some 9%nat) = ksp1 cx) by exact B9.
  assert (BV21 : base_val Eq3 (Some 21%nat) = kW2 cx fpos) by exact B21.
  assert (BV34 : base_val Eq3 (Some 34%nat) = kW2 cx fpos + qn) by exact B34.
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _).
  pose proof (kn_sp SK B cx HB) as (Hac & Hsp2 & _ & Hs1 & _ & Hstk & Hsp0 & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & Hs1b & Hs1c & _ & Hsp47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : kernel_c.KERNEL_AK = 4640) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
  assert (HW2 : kW2 cx fpos = kF cx fpos + 4400) by (unfold kW2, KN_W2; lia).
  pose proof (k7B_start cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv kd Eq3 HB HJ HW HAT ltac:(lia) HEdef)
    as KST.
  pose proof (k7B_fin POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv kd Eq3 HN HB HFR HRc HRm
                Hc Hci Hj Hm Hk Hkd HW HAT B9 B16 B21 B32 B33) as KFIN.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  destruct (Z_le_gt_dec qn 4064) as [G|G].
  2: destruct (Z_le_gt_dec qn 4080) as [G1|G1];
       [k7B_go cx fpos KST KFIN RUNTO HJ HAG BV9 BV21 BV34 4065 4080 16 ([-4093; -4091; -4089; -4085; -4081]) 1 (SLit 1)|].
  2: destruct (Z_le_gt_dec qn 4084) as [G2|G2];
       [k7B_go cx fpos KST KFIN RUNTO HJ HAG BV9 BV21 BV34 4081 4084 12 ([-4093; -4091; -4089; -4085]) 1 (SLit 1)|].
  2: destruct (Z_le_gt_dec qn 4088) as [G3|G3];
       [k7B_go cx fpos KST KFIN RUNTO HJ HAG BV9 BV21 BV34 4085 4088 8 ([-4093; -4091; -4089]) 1 (SLit 1)|].
  2: destruct (Z_le_gt_dec qn 4090) as [G4|G4];
       [k7B_go cx fpos KST KFIN RUNTO HJ HAG BV9 BV21 BV34 4089 4090 6 ([-4093; -4091]) 1 (SLit 1)|].
  2: destruct (Z_le_gt_dec qn 4092) as [G5|G5];
       [k7B_go cx fpos KST KFIN RUNTO HJ HAG BV9 BV21 BV34 4091 4092 4 ([-4093]) 1 (SLit 1)|].
  2: destruct (Z_le_gt_dec qn 4094) as [G6|G6];
       [k7B_go cx fpos KST KFIN RUNTO HJ HAG BV9 BV21 BV34 4093 4094 2 ([-4095]) 1 (SLit 1)|].
  2: k7B_go cx fpos KST KFIN RUNTO HJ HAG BV9 BV21 BV34 4095 4096 0 (@nil Z) 1 (SLit 1).
  (* n <= 4064: the five puts, checked_memset(w2 + n + 16, 0, 16), n += 16 *)
  destruct (KST 0 4064 16 ([-4093; -4091; -4089; -4085; -4081; -4065]) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(vm_compute; reflexivity) ltac:(repeat (apply Forall_cons; [cbv beta; lia|]); apply Forall_nil))
    as (HS & SHOK & HAWR).
  pose proof HS as HS0.
  paj_run_tok RUN HS HJ SHOK k3_span; [exact HAWR|].
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?mx) |- _ => rename mx into ms1; rename HSx into HS1 end.
  lazymatch goal with HFx : frame_of _ _ _ _ |- _ => rename HFx into HFr1 end.
  lazymatch goal with HGx : mem_grows _ _ |- _ => rename HGx into HG1 end.
  assert (UN1 : forall q, 0 <= q < 2 ^ 64 ->
            ~ ((kW2 cx fpos <= q < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx + 0x88 <= q < ksp1 cx + 0x98)) ->
            aview SEGS (w_H W3) (ms_mem ms1) q = aview SEGS (w_H W3) (ms_mem ms3) q).
  { intros q Hq Hnq.
    apply (kept_of_frame (segs := SEGS) Eq3 _ (w_H W3) (ms_mem ms3) (ms_mem ms1)
             (fun x => (kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx + 0x88 <= x < ksp1 cx + 0x98)) HFr1);
      [exact (k7B_windows Eq3 0 4064 16 _ _ _ _ BV9 BV21 BV34 ltac:(lia) ltac:(lia) ltac:(lia)) | exact Hq | exact Hnq]. }
  pose proof (fun q Hq => k3_apres_grows _ _ _ q HG1 Hq) as P1.
  pose proof (a5_reg_same Eq3 _ _ (w_H W3) ms3 ms1 [2; 3; 4] HS0 HS1 ltac:(vm_compute; reflexivity)) as KEEP.
  sreg HS1 (10%bv : bv 5) R10. sreg HS1 (11%bv : bv 5) R11. sreg HS1 (12%bv : bv 5) R12.
  prreg HS1 (1%bv : bv 5) R1.
  cbn [ms_regs restrict mkst] in R10, R11, R12.
  pmkst HS1.
  rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_memset) with 0x53214.
  (* F's shadow at the call: the run changed w2 and the two slots, none of them a shadow byte of F *)
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (_ & _ & _ & HFsh).
  pose proof kn_band as (KB1 & KB2).
  assert (KLS : kLowShadowBeg = 2147446784) by reflexivity.
  assert (HSH1 : kshadow cx fpos W3 (mkst (ms_regs ms3) (ms_pc_val ms3) (ms_mem ms1) (ms_rom ms3))
                   (kfsh 0xf8 0 0xf3)).
  { apply (kshadow_frame B LAWS
             (fun x => (kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx + 0x88 <= x < ksp1 cx + 0x98))
             cx fpos _ k2 ly3 S3 md3 W3 ms3 W3 _ HJB); [| rewrite kfsh_length; lia | | exact HSH].
    - intros q Hq Hn. cbn [ms_mem mkst]. exact (UN1 q Hq Hn).
    - intros q Hq Hw. rewrite kfsh_length in Hq.
      unfold kFSH, shadow_of_addr, kW2, KN_W2, NW_SIZE, SHADOW_OFF in *. lia. }
  eapply (a5_call_ms SK B LAWS AMEMSET cx fpos k2 ly3 S3 W3 _ md3 (ms_mem ms1) _ (ms_regs ms1) _ (qn + 16) 16
            (POST cx) HB HJ HJB HSH1);
    [ intros q Hq Hnq; reflexivity
    | lia | lia | unfold NW_SIZE; lia
    | rewrite R10; cbn [sv_denot]; rewrite B34; unfold w64; f_equal; lia
    | rewrite R11; reflexivity
    | rewrite R12; reflexivity
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
      + apply kn_mbyte_of_aview. apply Hfr2; [lia | unfold NW_SIZE in *; lia | rewrite HES; lia].
      + intros _. replace q with (ksp1 cx + (q - ksp1 cx)) by lia.
        exact (kn_spill_wr SK B LAWS cx fpos k2 ly3 S3 W3 (mkst regs2 (Z_to_bv 64 0) mem2 (seg_rom SEGS))
                 md2 HB HJ2 (q - ksp1 cx) ltac:(lia)).
    - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite B21; intros q Hq.
      + apply kn_mbyte_of_aview. apply Hfr2; [lia | lia | rewrite HES; lia].
      + intros _. apply kn_apresent_writable. apply Hpres2, P1, HFP. rewrite kn_fsb8. lia. }
  rewrite <- restrict_mkst_fx in HS2.
  remember (havoc Eq3 40 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS2.
  assert (HEI2 : img_env pa_val A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (HAG2 : env_agree 32 (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk)) E2)
    by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAG]).
  assert (C9 : bv_unsigned (ew E2 9) = ksp1 cx) by (rewrite HE2, ew_havoc_old by lia; exact B9).
  assert (C16 : bv_unsigned (ew E2 16) = kd) by (rewrite HE2, ew_havoc_old by lia; exact B16).
  assert (C21 : bv_unsigned (ew E2 21) = kW2 cx fpos) by (rewrite HE2, ew_havoc_old by lia; exact B21).
  assert (C32 : bv_unsigned (ew E2 32) = qn) by (rewrite HE2, ew_havoc_old by lia; exact B32).
  assert (C33 : bv_unsigned (ew E2 33) = qf) by (rewrite HE2, ew_havoc_old by lia; exact B33).
  assert (C20 : bv_unsigned (ew E2 20) = SHADOW_OFF) by (rewrite HE2, ew_havoc_old by lia; exact B20).
  assert (CV9 : base_val E2 (Some 9%nat) = ksp1 cx) by exact C9.
  assert (CV21 : base_val E2 (Some 21%nat) = kW2 cx fpos) by exact C21.
  clear HE2.
  (* the memory after the call, against the run's end: changed only in w2 and the callee's window *)
  assert (UNc : forall q, 0 <= q < 2 ^ 64 ->
            ~ ((kW2 cx fpos <= q < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx - ESTACK <= q < ksp1 cx)) ->
            aview SEGS (w_H W3) mem2 q =
            aview SEGS (w_H W3) (ms_mem (mkst (ms_regs ms3) (ms_pc_val ms3) (ms_mem ms1) (ms_rom ms3))) q).
  { intros q Hq Hnq. cbn [ms_mem mkst].
    apply Hfr2; [exact Hq | intros Hc'; apply Hnq; left; unfold NW_SIZE; lia | intros Hc'; apply Hnq; right; exact Hc']. }
  pose proof (a5_shok_fl SK B LAWS cx fpos k2 ly3 S3 md3 W3 mem2 E2 HB HJB
                (a5_w2_ra SK B LAWS cx fpos k2 ly3 S3 md3 W3 _ mem2 HB HJB HSH1 UNc) C20 C21) as SHOK2.
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 k3_span (kpc KP_K960).
  { cbn [ss_mem].
    apply awr_ok_x_cons.
    { intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite CV9 in Hx.
      left. split; [left; lia | lia]. }
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite CV21 in Hx.
    left. apply (a5_awf SK B LAWS cx fpos k2 ly3 S3 W3 _ _ HB HJ2). unfold NW_SIZE. lia. }
  lazymatch goal with
  | HS' : st_ok_pi _ _ ?E ?ssx (restrict _ ?msn),
    HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
    HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    let HR0 := fresh "HR0" in let HR1 := fresh "HR1" in
    spregion HS' 0%nat HR0; spregion HS' 1%nat HR1;
    apply (k7B_fin POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv kd E HN HB HFR HRc HRm
             Hc Hci Hj Hm Hk Hkd HW HAT C9 C16 C21 C32 C33 32 ltac:(lia) ltac:(lia) msn mdn _ _ (SOff 33 0) qf HR0 HR1);
    [ intros q Hq Hnq;
      rewrite (kept_of_frame (segs := SEGS) E _ (w_H W3) mem2 (ms_mem msn)
                 (fun x => (kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx + 0x88 <= x < ksp1 cx + 0x98)) HFr'
                 ltac:(
                   intros b wlo whi x Hin Hx; unfold windows in Hin;
                   cbn [ss_mem map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
                   destruct Hin as [Hq' | [Hq' | []]]; injection Hq' as <- <- <-;
                   [rewrite CV9 in Hx; right; lia | rewrite CV21 in Hx; left; unfold NW_SIZE; lia])
                 q Hq ltac:(intros [Hc'|Hc']; apply Hnq; [left; exact Hc' | right; right; exact Hc']));
      rewrite (UNc q Hq ltac:(intros [Hc'|Hc']; apply Hnq; [left; exact Hc' | right; left; exact Hc'])); cbn [ms_mem mkst];
      apply UN1; [exact Hq | intros [Hc'|Hc']; apply Hnq; [left; exact Hc' | right; right; exact Hc']]
    | intros q Hq; exact (k3_apres_grows _ _ _ q HG' (Hpres2 q (P1 q Hq)))
    | assumption
    | apply (kn_kms_of _ E ssx msn KP_K960 HS'); vm_compute; reflexivity
    | exact (regs_kept_of_st_ok_pi E ssx _ _ _ nx_keep0 HS' HAG2 ltac:(vm_compute; reflexivity))
    | exact (regs_kept_of_st_ok_pi E ssx _ _ _ (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [19; 21; 24; 22]%nat)
               HS' HAG2 ltac:(vm_compute; reflexivity))
    | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
    | rewrite ?(proj1 (wvb_fds_fs _ _ _)), (proj1 (kn_sbm_fds_fs _ _ Hsbm)); a5_md
    | rewrite ?(proj2 (wvb_fds_fs _ _ _)), (proj2 (kn_sbm_fds_fs _ _ Hsbm)); a5_md
    | kn_in | kn_in | kn_in | kn_in
    | left; split; reflexivity ]
  end.
Qed.

End b.
End a.
