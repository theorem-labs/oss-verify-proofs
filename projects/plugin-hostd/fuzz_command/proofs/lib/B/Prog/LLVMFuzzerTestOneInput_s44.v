(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment J of the inlined words_of of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x868bc .. the split loop's head 0x868e4: __asan_memcpy of the trimmed line from text into copy, s7 := copy, w.n := 0, UBSan's null test of copy, the inline check of copy's first byte), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s44.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (cl_seedX: the seed of a state inside the function, run to the next segment's statement) and A/ACh2.v (a step through a call and back, with a fresh seed after it). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB CmdGlob PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01
LLVMFuzzerTestOneInput_s40 LLVMFuzzerTestOneInput_s49 LLVMFuzzerTestOneInput_s42.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps SlotWords SlotWordsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* 0x868c8: back from __asan_memcpy (its return address) *)
Definition AW_J1 : Z := 0x398.

(* ---- the two symbolic states of this segment ----
   A, at 0x868bc (AW_J): every register is its own atom; atom 32 = text, atom 33 = copy, the frame words at
   120(sp) and 128(sp) (chunks of one read-only frame region, which `ld a1,120(sp); ld a0,128(sp)` read). It runs
   to the call of __asan_memcpy (0x868c4, ra = 0x868c8).
   B, at 0x868c8, seated afresh after the call: every register is its own atom; atom 32 = copy, the frame word at
   128(sp) (`ld s7,128(sp)` reads it); the frame region is writable at 144 .. 148 (w.n, `sw zero,144(sp)`). The
   fact copy >= 4096 decides UBSan's null test (0x868d0), and the shadow entry of copy's first byte makes the
   1-byte inline check (0x868d4 .. 0x868e0, slow path 0x86ac8) a token with no obligation; the run stops at the
   split loop's head 0x868e4. *)
Definition WJx : sv := SOff 25 0.
Definition WJspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition wj_frA : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 256 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 32 0)); YP09.mkChunk 128 (CVal 8 (SOff 33 0))].
Definition ss_wjA : sstate := mkSS AW_J sr_atoms [wj_frA] None (mkFacts [] [] []).
Definition wj_frB : YP09.region := YP09.mkRegion (Some 2%nat) 0 256 144 148 [YP09.mkChunk 128 (CVal 8 (SOff 32 0))].
Definition wj_factsB : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (25%nat, mkAF LT_SB LT_SB 0); (32%nat, mkAF 4096 (2 ^ 47 - 1) 0) ] [] [].
Definition ss_wjB : sstate := mkSS AW_J1 sr_atoms [wj_frB] None wj_factsB.
Definition wj_SHB : list shent := [mkSHE 32 0 1].

(* ---- lists and bytes ---- *)
(* a reader that holds a byte at each of n addresses holds a list of n bytes there *)
Lemma wj_bytes_of_rd_loc : forall (rd : reader) p (n : nat),
  (forall i, (i < n)%nat -> exists v, rd (p + Z.of_nat i) = Some v /\ 0 <= v < 256) ->
  exists C, length C = n /\ abytes_atR rd p C.
Proof.
intros rd p n H.
set (f := fun i : nat => Z_to_bv 8 (match rd (p + Z.of_nat i) with Some v => v | None => 0 end)).
exists (map f (seq 0 n)). split; [rewrite length_map, length_seq; reflexivity|].
intros i Hi. rewrite length_map, length_seq in Hi.
rewrite (nth_indep _ _ (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
rewrite map_nth, seq_nth by exact Hi. cbn [Nat.add]. unfold f.
destruct (H i Hi) as (v & Hv & Rv). rewrite Hv. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. symmetry. apply Z.mod_small. exact Rv.
Qed.
(* two byte lists at the same place agree on their common indices *)
Lemma wj_nth_of_bytes_loc : forall (rd : reader) p (C L : list byte) j,
  abytes_atR rd p C -> abytes_atR rd p L -> (j < length L)%nat -> (j < length C)%nat -> nth_error C j = nth_error L j.
Proof.
intros rd p C L j HC HL Hj1 Hj2.
rewrite (nth_error_nth' C (Z_to_bv 8 0) Hj2), (nth_error_nth' L (Z_to_bv 8 0) Hj1). f_equal.
pose proof (HC j Hj2) as E1. pose proof (HL j Hj1) as E2. rewrite E1 in E2. injection E2 as E2.
apply bv_eq. exact E2.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a field of the frame the symbolic state holds as a chunk, read back *)
Lemma wj_aval_of_val_loc : forall H (mem : word -> option byte) a n v,
  val_mem SEGS (mrestrict H mem) a n v -> aval_mem (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte, YG0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* B's environment: atoms 0 .. 31 the registers after the call, atom 32 = copy (A uses s42's wc_EB: 32 = text,
   33 = copy) *)
Definition wj_EB (regs : bvmap 5 word) (c : Z) : env := Eimg (Ereg regs [Z_to_bv 64 c]).
Lemma wj_EB_lo : forall regs c n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (wj_EB regs c) n = getr regs r.
Proof.
intros regs c n r Hr. pose proof (u5_range r) as R5. unfold wj_EB. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hr.
Qed.
Lemma wj_EB_32 : forall regs c, ew (wj_EB regs c) 32 = Z_to_bv 64 c.
Proof. intros regs c. unfold wj_EB. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma wj_EB_agree : forall regs c, env_agree 32 (Ereg regs [Z_to_bv 64 c]) (wj_EB regs c).
Proof. intros regs c. split; [intros n Hn; unfold wj_EB; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

(* the seed at 0x868bc *)
Lemma wj_seedA : forall (W : world SEGS) regs mem text copy,
  2 ^ 46 <= spZ regs -> spZ regs + 256 <= 2 ^ 47 -> 0 <= text < 2 ^ 64 -> 0 <= copy < 2 ^ 64 ->
  rdword (rdW W mem) (spZ regs + 120) = Some text -> rdword (rdW W mem) (spZ regs + 128) = Some copy ->
  st_ok_pi SEGS VAL (wc_EB regs text copy) ss_wjA
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AW_J)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS WJx [] (wc_EB regs text copy) (mrestrict (w_H W) mem).
Proof.
intros W regs mem text copy Hsp1 Hsp2 Ht Hc G120 G128.
set (E := wc_EB regs text copy).
assert (E2 : ew E 2 = getr regs 2) by (subst E; apply (wc_EB_lo regs _ _ 2%nat 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 text) by (subst E; apply wc_EB_32).
assert (E33 : ew E 33 = Z_to_bv 64 copy) by (subst E; apply wc_EB_33).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split.
- unfold ss_wjA. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold wc_EB. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, wj_frA.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS _ _ _ 120 8 (SOff 32 0) text);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | zside |].
      -- replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) by reflexivity. lia.
      -- exact (val_mem_of_rdword SEGS _ _ _ _ G120).
    * apply (chunk_ok_val SEGS _ _ _ 128 8 (SOff 33 0) copy);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | zside |].
      -- replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) by reflexivity. lia.
      -- exact (val_mem_of_rdword SEGS _ _ _ _ G128).
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
  + split; [exact I | split; exact I].
- unfold sh_ok. apply Forall_nil.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the walk's Section hypotheses, with the names of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis LAWS : AR_laws SEGS B.
(* the memory-checking runtime's memcpy entry, the statement's own hypothesis (LLVMFuzzerTestOneInput_c.v:215) *)
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

(* the seed at 0x868c8 *)
Lemma wj_seedB : forall ly S (W : world SEGS) regs mem md copy n,
  AR SEGS B ly S W mem md -> In (copy, n + 1) (ablocks B ly S) -> 0 <= n ->
  2 ^ 46 <= spZ regs -> spZ regs + 256 <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  (forall a, spZ regs + 144 <= a < spZ regs + 148 -> apresent (w_H W) mem a) ->
  getr regs 25 = w64 LT_SB -> rdword (rdW W mem) (spZ regs + 128) = Some copy ->
  st_ok_pi SEGS VAL (wj_EB regs copy) ss_wjB
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AW_J1)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS WJx wj_SHB (wj_EB regs copy) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md copy n HAR Hin Hn Hsp1 Hsp2 Hal Hpres R25 G128.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md copy (n + 1) HAR Hin) as (_ & Hc4096 & Hcceil & Hcapp & Hcpres & _ & _).
pose proof (req_size_pos (n + 1) ltac:(lia)) as [Hr1 Hr2].
pose proof alloc_ceiling_lt as HACL.
set (E := wj_EB regs copy).
assert (E2 : ew E 2 = getr regs 2) by (subst E; apply (wj_EB_lo regs _ 2%nat 2%bv eq_refl)).
assert (E25 : ew E 25 = Z_to_bv 64 LT_SB) by (subst E; rewrite (wj_EB_lo regs _ 25%nat 25%bv eq_refl); exact R25).
assert (E32 : ew E 32 = Z_to_bv 64 copy) by (subst E; apply wj_EB_32).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U25 : bv_unsigned (ew E 25) = LT_SB) by (rewrite E25; apply unsigned_lit_small; unfold LT_SB; lia).
assert (Hcr : 4096 <= copy < 2 ^ 47) by lia.
assert (U32 : bv_unsigned (ew E 32) = copy) by (rewrite E32; apply unsigned_lit_small; lia).
split.
- unfold ss_wjB. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold wj_EB. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, wj_frB.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ _ 128 8 (SOff 32 0) copy);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | zside |].
    * replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) by reflexivity. lia.
    * exact (val_mem_of_rdword SEGS _ _ _ _ G128).
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
  + split; [|split; [exact I | exact I]].
    cbn [wj_factsB f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U25, U32. change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold LT_SB.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
- unfold sh_ok, wj_SHB. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E WJx 32 copy 1 copy 0 1).
  + exact (range_addressable_of_block SEGS B LAWS ly S W mem md copy (n + 1) copy 1 HAR Hin ltac:(lia) ltac:(lia)).
  + unfold U, WJx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold LT_SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
    unfold in_app, kLowShadowBeg in Hcapp. rewrite C3 in Hcapp. unfold SHADOW_OFF. lia.
Qed.

(* ---- segment J: 0x868bc .. the split loop's head 0x868e4 ---- *)
Theorem aw_seg_J : forall m, (forall nm, AW_S_stmt B MT m nm) -> AW_J_stmt B MT m.
Proof.
intros m HSLp. unfold AW_J_stmt.
intros cx q ly S W regs mem md k acc text copy arr Hm HFRM HC HREC HWS HTX R12.
destruct HTX as (T & HT & HTl & HTf).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS : LTOI_STK = 32768) by reflexivity.
pose proof HC as ((HB0 & ((HJ & Hsp & R3 & R4 & HSV) & HSLt & R8 & R9 & R18 & R25 & R26 & R27 & Hmq) &
  (Hr & R19 & R20 & R21 & R22 & Hst & Hho & Hh)) & Hbud).
pose proof (lt_payload_live B MT cx (q_r q) HB0 Hr) as (Hn & Hp).
pose proof HB0 as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
rewrite WS in Hslo.
assert (Hs0 : alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47) by (unfold x_sp0; lia).
assert (Hs1 : x_sp1 cx = x_sp0 cx - 256) by (unfold x_sp1, x_sp0, LT_FRAME; lia).
pose proof (proj1 HJ) as HAR.
pose proof HREC as (HRR & Hspill & Hcalls & Hquit & Hq & HPERM).
(* the model: |LN| <= |U| = L0 <= |D| <= the message's length < 2^26 *)
pose proof (q_L0_U cx q) as HL0U.
assert (HLNU : (length (q_LN cx q) <= length (q_U cx q))%nat) by exact (SlotWords.sw_line_le (q_D cx q)).
assert (HUf : q_U cx q = firstn (length (q_U cx q)) (q_D cx q))
  by (unfold q_U, Verbs.upto0; apply SlotWords.sw_upto_prefix).
assert (HUD : (length (q_U cx q) <= length (q_D cx q))%nat)
  by (pose proof (f_equal (@length byte) HUf) as HL; rewrite length_firstn in HL; lia).
pose proof (lt_len_range (x_pl cx) (x_n cx) (q_r q) ltac:(lia)) as HLR.
assert (HDl : Z.of_nat (length (q_D cx q)) <= lt_len (x_pl cx) (x_n cx) (q_r q))
  by (unfold q_D, lt_D; rewrite length_firstn; lia).
assert (Hhdr : 0 < SlotSpec.hdr_n (q_r q) <= q_r q) by (unfold SlotSpec.hdr_n; lia).
assert (HL0r : 0 <= q_L0 cx q < 2 ^ 26) by lia.
assert (RQ : req_size (q_L0 cx q + 1) = q_L0 cx q + 1) by (apply wc_req_loc; lia).
(* the blocks: text and copy are made since the entry, apart from each other and off the image *)
assert (HtB : In (text, q_L0 cx q + 1) (aw_blocks cx q text copy arr)) by (rewrite aw_blocks_eq; left; reflexivity).
assert (HcB : In (copy, q_L0 cx q + 1) (aw_blocks cx q text copy arr)) by (rewrite aw_blocks_eq; right; left; reflexivity).
assert (HtIn : In (text, q_L0 cx q + 1) (ablocks B ly S))
  by exact (Permutation_in _ (Permutation_sym HPERM) (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror HtB))))).
assert (HcIn : In (copy, q_L0 cx q + 1) (ablocks B ly S))
  by exact (Permutation_in _ (Permutation_sym HPERM) (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror HcB))))).
pose proof (lt_ablocks_NoDup B LAWS ly S W mem md HAR) as HND.
pose proof (Permutation_NoDup HPERM HND) as HND2.
assert (Hcnot : ~ In (copy, q_L0 cx q + 1) (x_bl0 B cx)).
{ intros Hin. exact (wc_nodup_app_loc _ _ _ (wc_nodup_app_r_loc _ _ HND2) Hin HcB). }
assert (Hne : (text, q_L0 cx q + 1) <> (copy, q_L0 cx q + 1)).
{ pose proof (wc_nodup_app_r_loc _ _ (wc_nodup_app_r_loc _ _ HND2)) as HN3. rewrite aw_blocks_eq in HN3.
  apply NoDup_cons_iff in HN3 as [HN3 _]. intros Heq. apply HN3. rewrite Heq. left. reflexivity. }
pose proof (sep_blocks SEGS B LAWS ly S W mem md text (q_L0 cx q + 1) copy (q_L0 cx q + 1) HAR HtIn HcIn Hne) as HdTC.
unfold zdisjoint in HdTC. cbn [fst snd] in HdTC.
destruct (al_blocks _ _ LAWS ly S W mem md text _ HAR HtIn) as (_ & Ht4096 & Htceil & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md copy _ HAR HcIn) as (_ & Hc4096 & Hcceil & _ & _ & _ & _).
pose proof (blk_off_imgP B ly S W mem md copy _ HAR HcIn) as Hoffc. unfold off_img in Hoffc.
(* ---- 0x868bc .. 0x868c4: a1 := text, a0 := copy (from the frame), jal __asan_memcpy ---- *)
pose proof HWS as (HW0 & HW8 & HW16).
assert (G120 : rdword (rdW W mem) (spZ regs + 120) = Some text) by (rewrite Hsp; unfold LT_W in HW0; exact HW0).
assert (G128 : rdword (rdW W mem) (spZ regs + 128) = Some copy).
{ rewrite Hsp. unfold LT_W in HW8. replace (x_sp1 cx + 128) with (x_sp1 cx + 120 + 8) by lia. exact HW8. }
destruct (wj_seedA W regs mem text copy ltac:(rewrite Hsp; lia) ltac:(rewrite Hsp; lia) ltac:(lia) ltac:(lia)
  G120 G128) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (wc_EB regs text copy)) by (unfold wc_EB; apply Eimg_env).
pose proof (wc_EB_agree regs text copy) as HAE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (wc_EB regs text copy) n = getr regs rr)
  by (intros n rr Hrr; exact (wc_EB_lo regs _ _ n rr Hrr)).
assert (E32 : ew (wc_EB regs text copy) 32 = Z_to_bv 64 text) by apply wc_EB_32.
assert (E33 : ew (wc_EB regs text copy) 33 = Z_to_bv 64 copy) by apply wc_EB_33.
remember (wc_EB regs text copy) as E eqn:HE. clear HE.
paj_run_tok RUN HS HJ SHOK WJspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv1 := d) in *; clearbody mdv1 end.
(* the stretch writes no memory *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr); [|exact Ha | intros []].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; lia|]). destruct Hin. }
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
pose proof (aregs_preserved_of_st_ok SEGS _ E _ _ regs [Z_to_bv 64 text; Z_to_bv 64 copy] HS HAE
  ltac:(vm_compute; reflexivity)) as HPA.
cbn [ms_regs restrict] in HPA.
rename ms into msA.
assert (PA : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr (ms_regs msA) r = getr regs r)
  by (intros r z Hz Hr0; exact (wc_pres_loc regs (ms_regs msA) r z HPA Hz Hr0)).
assert (HspT : spZ (ms_regs msA) = x_sp0 cx + -256).
{ unfold spZ at 1. rewrite (PA 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  change (bv_unsigned (getr regs 2)) with (spZ regs). rewrite Hsp, Hs1. lia. }
assert (P3' : getr (ms_regs msA) 3 = w64 (as_gp B))
  by (rewrite (PA 3%bv 3 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), R3; exact Hgp).
assert (P4' : getr (ms_regs msA) 4 = w64 (as_tp B))
  by (rewrite (PA 4%bv 4 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), R4; exact Htp).
assert (P10' : getr (ms_regs msA) 10 = w64 copy) by (rewrite P10; exact E33).
assert (P11' : getr (ms_regs msA) 11 = w64 text) by (rewrite P11; exact E32).
assert (P12' : getr (ms_regs msA) 12 = w64 (Z.of_nat (length (q_LN cx q)) + 1))
  by (rewrite P12, (EEo 12%nat 12%bv eq_refl); exact R12).
assert (HraT : YK0s.ret_ok (Z_to_bv 64 (BASE + 920))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS ly S W (ms_mem msA) mdv1 text _ HAR1 HtIn) as (_ & _ & _ & _ & Htpres1 & _ & _).
(* ---- __asan_memcpy(copy, text, |line| + 1) ---- *)
eapply SRr_bind.
{ apply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIG CS___asan_memcpy) (AMEMCPY fx) W (ms_regs msA) (ms_mem msA)
    LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S mdv1 k
    copy text (Z.of_nat (length (q_LN cx q)) + 1) (-256) (Z_to_bv 64 (BASE + 920))
    HJ P10' P11' P12' ltac:(lia) ltac:(lia) ltac:(lia) HspT eq_refl ltac:(lia) ltac:(rewrite Hes, WS; lia) P3' P4' P1 HraT).
  - intros a Ha. split.
    + right; right; left. exists copy, (q_L0 cx q + 1). split; [exact HcIn | split; [exact Hcnot | lia]].
    + rewrite Hes. lia.
  - intros a Ha (r0 & Hr0 & Hlo & Hhi). exfalso. unfold cmd_PG in Hr0. cbn [In] in Hr0.
    destruct Hr0 as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hlo, Hhi; unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in *; lia.
  - exact (amem_range_of_block SEGS B LAWS ly S W mem md copy (q_L0 cx q + 1) copy (Z.of_nat (length (q_LN cx q)) + 1)
      HAR HcIn ltac:(lia) ltac:(lia)).
  - exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem msA) mdv1 copy (q_L0 cx q + 1) copy
      (Z.of_nat (length (q_LN cx q)) + 1) HAR1 HcIn ltac:(lia) ltac:(lia)).
  - intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem msA) mdv1 copy (q_L0 cx q + 1) copy
      (Z.of_nat (length (q_LN cx q)) + 1) HAR1 HcIn ltac:(lia) ltac:(lia) Hpos).
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - apply (aview_some_of_apresent SEGS). exact (proj1 (Htpres1 a ltac:(lia))).
      - rewrite HspT, Hes. lia. }
    split; [lia|].
    split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md text (q_L0 cx q + 1) text
              (Z.of_nat (length (q_LN cx q)) + 1) HAR HtIn ltac:(lia) ltac:(lia))|].
    split; [exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem msA) mdv1 text (q_L0 cx q + 1) text
              (Z.of_nat (length (q_LN cx q)) + 1) HAR1 HtIn ltac:(lia) ltac:(lia))|].
    intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem msA) mdv1 text (q_L0 cx q + 1) text
      (Z.of_nat (length (q_LN cx q)) + 1) HAR1 HtIn ltac:(lia) ltac:(lia) Hpos). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10b & HCPY & HKC & HPRS & HSAME).
clear H10b HPRS HSAME.
(* back at 0x868c8 *)
assert (HP12 : aregs_preserved regs regs2) by exact (aregs_preserved_trans _ _ _ HPA HP2).
assert (P2 : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr regs r)
  by (intros r z Hz Hr0; exact (wc_pres_loc regs regs2 r z HP12 Hz Hr0)).
assert (R25b : getr regs2 25 = w64 LT_SB)
  by (rewrite (P2 25%bv 25 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R25).
assert (Hsp2 : spZ regs2 = x_sp1 cx)
  by (unfold spZ; rewrite (P2 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact Hsp).
assert (G128b : rdword (rdW W mem2) (spZ regs2 + 128) = Some copy).
{ rewrite Hsp2. rewrite (rdword_ext (rdW W mem) (rdW W mem2)); [rewrite <- Hsp; exact G128|].
  intros kk Hk. rewrite (HKC (x_sp1 cx + 128 + kk) ltac:(lia) ltac:(lia) ltac:(rewrite Hes; lia)).
  apply KA. lia. }
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2j & _).
assert (HPR2 : forall a, spZ regs2 + 144 <= a < spZ regs2 + 148 -> apresent (w_H W) mem2 a).
{ intros a Ha. apply Hpres2j. rewrite Hsp2 in Ha. rewrite WS. lia. }
assert (Hal2 : spZ regs2 mod 16 = 0).
{ assert (Hsp0 : x_sp0 cx = spZ (x_regs cx)) by reflexivity. rewrite Hsp2, Hs1, Hsp0.
  replace (spZ (x_regs cx) - 256) with (spZ (x_regs cx) + (-16) * 16) by ring.
  rewrite Z_mod_plus_full. exact Hal16. }
clear HS SHOK.
destruct (wj_seedB ly S W regs2 mem2 md2 copy (q_L0 cx q) HAR2 HcIn ltac:(lia) ltac:(rewrite Hsp2; lia)
  ltac:(rewrite Hsp2; lia) Hal2 HPR2 R25b G128b) as [HS SHOK].
assert (HEIB : img_env VAL A_LIM (wj_EB regs2 copy)) by (unfold wj_EB; apply Eimg_env).
pose proof (wj_EB_agree regs2 copy) as HAEB.
assert (E32B : ew (wj_EB regs2 copy) 32 = Z_to_bv 64 copy) by apply wj_EB_32.
assert (UspB : bv_unsigned (ew (wj_EB regs2 copy) 2) = x_sp1 cx)
  by (rewrite (wj_EB_lo regs2 copy 2%nat 2%bv eq_refl); exact Hsp2).
assert (UspB' : bv_unsigned (ew (wj_EB regs2 copy) 2) = x_sp0 cx + -256) by (rewrite UspB; lia).
remember (wj_EB regs2 copy) as EB eqn:HEB. clear HEB.
(* 0x868c8 .. 0x868e4: s7 := copy, w.n := 0, UBSan's null test (decided), the inline check of copy[0] (a token) *)
paj_run_to_tok RUNTO HS HJ2 SHOK WJspan AW_S.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -256);
    [reflexivity | first [exact UspB' | cbn [ew ewset Nat.eqb]; exact UspB']
    | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
(* the stretch writes w.n only *)
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp1 cx + 144 <= a < x_sp1 cx + 148) ->
  rdW W (ms_mem ms) a = rdW W mem2 a).
{ intros a Ha Hna.
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => x_sp1 cx + 144 <= a < x_sp1 cx + 148) HFr);
    [|exact Ha | exact Hna].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq0 | Hin];
    [injection Hq0 as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?UspB in Hrr; lia|]).
  destruct Hin. }
clear HF HFr HG.
(* w.n holds 0 *)
assert (HWN : aw_wn cx (rdW W (ms_mem ms)) (Z.of_nat 0)).
{ pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
  pose proof (mem_ok_region SEGS _ _ _ _ HM (in_eq _ _)) as HR0.
  pose proof (region_ok_chunk SEGS _ _ _ (YP09.mkChunk 144 (CVal 4 (SLit 0))) HR0
    ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))) as HC144.
  cbn [YP09.r_base base_val ew ewset Nat.eqb] in HC144. rewrite UspB in HC144.
  pose proof (val_of_chunk_ok SEGS _ _ _ 144 4 (SLit 0) 0 HC144 eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V144.
  unfold aw_wn. change (Z.of_nat 0) with 0.
  replace (x_sp1 cx + LT_W + 24) with (x_sp1 cx + 144) by (unfold LT_W; lia).
  exact (wj_aval_of_val_loc _ _ _ 4 0 V144). }
pmkst HS.
prreg HS (23%bv : bv 5) F23.
lazymatch type of HS with st_ok_pi _ _ ?E4 _ _ =>
  assert (HAE4 : env_agree 32 (Ereg regs2 [Z_to_bv 64 copy]) E4)
end.
{ pose proof HAEB as [HA1 HA2]. split.
  - intros n Hn32. cbn [ew ewset].
    repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [lia|] end.
    exact (HA1 n Hn32).
  - cbn [ed ewset]. exact HA2. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 [Z_to_bv 64 copy]
  [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]%bv HS HAE4 ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
assert (HKall : forall r, In r AW_KEEPR -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr0. rewrite (HKR r Hr0). exact (aw_keepr_pres regs regs2 HP12 r Hr0). }
(* the memory: copy holds the line and its NUL; the rest differs from the entry's only in copy, w.n and the
   runtime's window below sp *)
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (copy <= a < copy + (Z.of_nat (length (q_LN cx q)) + 1)) ->
  ~ (x_sp1 cx - 4096 <= a < x_sp1 cx) -> ~ (x_sp1 cx + 144 <= a < x_sp1 cx + 148) ->
  rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha H1 H2 H3. rewrite (KB a Ha H3), (HKC a Ha H1 ltac:(rewrite Hes; lia)). exact (KA a Ha). }
destruct (aw_ctx_kept B MT LAWS cx q ly S W regs mem md k acc text copy arr (ms_regs ms) (ms_mem ms) mdv2
  HC HREC HWS HJ2 HKall ltac:(intros a Ha _ H2 _ H4 H5; apply KALL; [exact Ha | lia | lia | lia]))
  as (HC' & HREC' & HWS').
assert (HLN2 : abytes_atR (rdW W mem2) copy (q_LN cx q ++ [Z_to_bv 8 0])).
{ intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (HCPY (Z.of_nat i)) by lia. rewrite KA by lia. rewrite (HT i) by (rewrite HTl; lia).
  rewrite <- HTf. rewrite wc_nth_firstn_loc by lia. reflexivity. }
assert (HLN3 : abytes_atR (rdW W (ms_mem ms)) copy (q_LN cx q ++ [Z_to_bv 8 0])).
{ apply (abytes_atR_kept_r (rdW W mem2)); [|exact HLN2]. intros z Hz. rewrite length_app in Hz. cbn [length] in Hz.
  apply KB; lia. }
pose proof (proj1 HJ2) as HAR3.
destruct (al_blocks _ _ LAWS ly S W (ms_mem ms) mdv2 copy _ HAR3 HcIn) as (_ & _ & _ & _ & HcP3 & _).
destruct (wj_bytes_of_rd_loc (rdW W (ms_mem ms)) copy (Z.to_nat (q_L0 cx q + 1))) as (C & HCl & HCb).
{ intros i Hi. destruct (rdW W (ms_mem ms) (copy + Z.of_nat i)) as [v|] eqn:Ev.
  - exists v. split; [reflexivity|]. destruct (aview_byte SEGS _ _ _ _ Ev) as (_ & _ & _ & Rv). exact Rv.
  - exfalso. apply (aview_some_of_apresent SEGS (w_H W) (ms_mem ms) (copy + Z.of_nat i)); [|exact Ev].
    exact (proj1 (HcP3 (copy + Z.of_nat i) ltac:(lia))). }
assert (HCpre : forall j, (0 <= j <= length (q_LN cx q))%nat ->
  nth_error C j = nth_error (q_LN cx q ++ [Z_to_bv 8 0]) j).
{ intros j Hj. apply (wj_nth_of_bytes_loc (rdW W (ms_mem ms)) copy); [exact HCb | exact HLN3 | | ].
  - rewrite length_app. cbn [length]. lia.
  - rewrite HCl. lia. }
assert (F23' : getr (ms_regs ms) 23 = w64 (copy + Z.of_nat 0)).
{ rewrite F23. first [rewrite E32B | cbn [ew ewset Nat.eqb]; rewrite E32B]. unfold w64. f_equal. lia. }
assert (Harr : aw_arr (rdW W (ms_mem ms)) arr []) by (intros i0 p0 H0; destruct i0; discriminate H0).
assert (Hfound : aw_found copy (q_ws cx q) C [] 0) by (intros k' p0 w1 H0; destruct k'; discriminate H0).
assert (Hwords : Verbs.words_acc [] (skipn 0 (q_LN cx q)) = skipn 0 (q_ws cx q)) by reflexivity.
exact (HSLp (length (q_LN cx q) - 0)%nat cx q ly S W (ms_regs ms) (ms_mem ms) mdv2 k acc text copy arr 0%nat 0%nat C []
  Hm HFRM HC' HREC' HWS' F23' HWN eq_refl (Nat.le_0_l _) (le_n 0%nat) eq_refl (Nat.le_0_l _)
  Hwords HCb HCl HCpre Harr Hfound).
Qed.

End e.
End f.
End d.
