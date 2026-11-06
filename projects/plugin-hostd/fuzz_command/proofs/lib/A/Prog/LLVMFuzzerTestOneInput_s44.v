(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment J of the inlined words_of of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x8680c .. 0x86850 / 0x8693c: __asan_memcpy of the trimmed line into copy, the empty-line exit and the split loop's set-up), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (cl_seedX: the seed of a state inside the function, run to the next segment's statement) and A/ACh2.v (a step through a call and back, with a fresh seed after it). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaArt PaSB PaDenot CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s40 LLVMFuzzerTestOneInput_s49.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps SlotWords.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* 0x86818: back from __asan_memcpy (its return address) *)
Definition AW_J1 : Z := 0x334.

(* ---- the two symbolic states of the segment ----
   0x8680c: `mv a0,s7; mv a1,s8; jal __asan_memcpy` touch no memory: no region, no fact, no shadow entry.
   0x86818: the environment's atoms 0 .. 31 are the registers after the call, atom 32 is copy's first byte.
   Two windows of the frame at sp, each a region of its own so that the run keeps the frame words between them:
   the split loop's spills of s5 and s11 (sp + 88 .. 104) and w.n (sp + 144 .. 148); and copy's first byte (copy is
   s7, atom 23), which `lbu a0,0(s7)` reads. The 1-byte check of copy at 0x86818 has no shadow entry: it leaves the
   obligation that copy's byte is addressable. *)
Definition JBx : sv := SOff 9 0.
Definition JBspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition ss_ja : sstate := mkSS AW_J sr_atoms [] None (mkFacts [] [] []).
Definition jb_spill : YP09.region := YP09.mkRegion (Some 2%nat) 88 104 88 104 [].
Definition jb_wn : YP09.region := YP09.mkRegion (Some 2%nat) 144 148 144 148 [].
Definition jb_copy : YP09.region := YP09.mkRegion (Some 23%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition jb_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF LT_SB LT_SB 0); (23%nat, mkAF 4096 140737479966720 4);
    (32%nat, mkAF 0 255 0) ] [] [].
Definition ss_jb : sstate := mkSS AW_J1 sr_atoms [jb_spill; jb_wn; jb_copy] None jb_facts.

(* ---- lists and bytes ---- *)
Lemma jw_perm2 : forall {A} (l1 l2 l3 : list A) (x y : A),
  Permutation (l1 ++ x :: l2 ++ y :: l3) (x :: y :: l1 ++ l2 ++ l3).
Proof.
intros A l1 l2 l3 x y. apply Permutation_sym. apply Permutation_cons_app.
rewrite (app_assoc l1 l2 l3), (app_assoc l1 l2 (y :: l3)).
apply Permutation_cons_app. apply Permutation_refl.
Qed.
Lemma jw_nth_firstn : forall {A} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros A l. induction l as [|a l IH]; intros n i d Hi; destruct n as [|n]; try lia; [destruct i; reflexivity|].
destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
(* a reader that holds a byte at each of n addresses holds a list of n bytes there *)
Lemma jw_bytes_of_rd : forall (rd : reader) p (n : nat),
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
Lemma jw_nth_of_bytes : forall (rd : reader) p (C L : list byte) j,
  abytes_atR rd p C -> abytes_atR rd p L -> (j < length L)%nat -> (j < length C)%nat -> nth_error C j = nth_error L j.
Proof.
intros rd p C L j HC HL Hj1 Hj2.
rewrite (nth_error_nth' C (Z_to_bv 8 0) Hj2), (nth_error_nth' L (Z_to_bv 8 0) Hj1). f_equal.
pose proof (HC j Hj2) as E1. pose proof (HL j Hj1) as E2. rewrite E1 in E2. injection E2 as E2.
apply bv_eq. exact E2.
Qed.
Lemma jw_rdword_kept : forall (rd rd' : reader) a v,
  (forall z, a <= z < a + 8 -> rd' z = rd z) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
intros rd rd' a v HK H. unfold rdword in *.
rewrite (HK a), (HK (a + 1)), (HK (a + 2)), (HK (a + 3)), (HK (a + 4)), (HK (a + 5)), (HK (a + 6)), (HK (a + 7))
  by lia.
exact H.
Qed.
Lemma jw_slot_off : forall o v, In (o, v) LT_SLOTS -> 0 <= o <= 80.
Proof.
intros o v H.
assert (HF8 : forallb (fun p => (0 <=? fst p) && (fst p <=? 80)) LT_SLOTS = true) by (vm_compute; reflexivity).
rewrite forallb_forall in HF8. specialize (HF8 _ H). cbn [fst] in HF8.
apply andb_prop in HF8 as [H2 H3]. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.
(* the byte of a word, in the two copies of le_byte the readers (CmdRep's aval_mem) and the chunks (YI04's
   val_mem) use *)
Lemma jw_le_byte_0 : forall w k, YG0f.le_byte 0 w k = 0.
Proof. intros w k. unfold YG0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.
Lemma jw_le_byte_0o : forall w k, YO0f.le_byte 0 w k = 0.
Proof. intros w k. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.
Lemma jw_le_byte_1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. replace (8 * Z.of_nat 0) with 0 by reflexivity.
replace (8 * Z.of_nat 1) with 8 by reflexivity. rewrite Z.shiftr_0_r.
replace (2 ^ 8) with 256 by reflexivity. rewrite !(Z.mod_small v 256) by lia. reflexivity.
Qed.
Lemma jw_agree_ewset : forall k E0 E n v, env_agree k E0 E -> (k <= n)%nat -> env_agree k E0 (ewset E n v).
Proof.
intros k E0 E n v [H1 H2] Hn. split.
- intros i Hi. cbn [ew ewset]. destruct (Nat.eqb_spec i n); [lia | exact (H1 i Hi)].
- exact H2.
Qed.
Lemma jw_pres : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.

Ltac jw_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* the run's write windows from 0x86818 on: the two frame regions above sp1 = entry sp - 256, none in copy *)
Ltac jw_awr Usp WS :=
  lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  (apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat (-256));
    [reflexivity | cbn [ew ewset Nat.eqb]; rewrite Usp; unfold x_sp1, x_sp0, LT_FRAME; lia
    | cbn; rewrite WS; lia | cbn; lia |]);
  (apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat (-256));
    [reflexivity | cbn [ew ewset Nat.eqb]; rewrite Usp; unfold x_sp1, x_sp0, LT_FRAME; lia
    | cbn; rewrite WS; lia | cbn; lia |]);
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition ja_E (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Definition jb_E (regs : bvmap 5 word) (b0 : Z) : env := Eimg (Ereg regs [Z_to_bv 64 b0]).

(* the seed at 0x8680c *)
Lemma jw_seedA : forall (W : world SEGS) (regs : bvmap 5 word) mem,
  st_ok_pi SEGS VAL (ja_E regs) ss_ja (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AW_J)) mem (seg_rom SEGS))) /\
  sh_ok SEGS JBx [] (ja_E regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem. split.
- unfold ss_ja. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold ja_E. apply regs_ok_Eimg_Ereg.
  + reflexivity.
  + apply Forall_nil.
  + cbn [pairwise_disjoint]. exact I.
  + split; [exact I | split; exact I].
- unfold sh_ok. apply Forall_nil.
Qed.

(* the seed at 0x86818 *)
Lemma jw_seedB : forall (W : world SEGS) (regs : bvmap 5 word) mem copy b0,
  2 ^ 46 <= spZ regs -> spZ regs + 256 <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  (forall a, spZ regs + 88 <= a < spZ regs + 148 -> apresent (w_H W) mem a) ->
  getr regs 9 = w64 LT_SB -> getr regs 23 = w64 copy ->
  4096 <= copy -> copy + 1 <= spZ regs -> copy <= 140737479966720 -> copy mod 16 = 0 ->
  rdW W mem copy = Some b0 ->
  st_ok_pi SEGS VAL (jb_E regs b0) ss_jb
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AW_J1)) mem (seg_rom SEGS))) /\
  sh_ok SEGS JBx [] (jb_E regs b0) (mrestrict (w_H W) mem).
Proof.
intros W regs mem copy b0 Hlo Hhi Hal Hpres R9 R23 Hc1 Hc2 Hc3 Hc16 Hb0.
destruct (aview_byte SEGS _ _ _ _ Hb0) as (bb & Ebb & Eb & Rb).
assert (HV1 : val_mem SEGS (mrestrict (w_H W) mem) copy 1 b0).
{ intros k0 Hk0. assert (k0 = 0%nat) by lia. subst k0. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
  rewrite Ebb. f_equal. rewrite (jw_le_byte_1 b0 Rb). rewrite Eb. symmetry. apply Z_to_bv_bv_unsigned. }
set (E := jb_E regs b0).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 b0]) n)
  by (intros n Hn; subst E; unfold jb_E; apply Eimg_low; exact Hn).
assert (E2 : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 LT_SB)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E23 : ew E 23 = Z_to_bv 64 copy)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 b0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_jb. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold jb_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold jb_spill, jb_wn, jb_copy. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB 23%nat copy E23) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ copy 0 1 (SOff 32 0) b0);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact HV1.
  + apply pairwise_disjoint_of_extents. unfold jb_spill, jb_wn, jb_copy, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 23%nat copy E23) by lia. cbn [base_val]. rewrite E2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [jb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E9, E23, E32, !unsigned_lit_small by (unfold LT_SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold LT_SB.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
- unfold sh_ok. apply Forall_nil.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the runtime entry the segment calls: the statement's own hypothesis (LLVMFuzzerTestOneInput_c.v:186) *)
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIG CS___asan_memcpy).
(* the per-binary record *)
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the bytes the facts of aw_ctx, aw_rec and aw_wslots read: the eleven slots, the frame words host .. w.arr, the
   saved registers, g_rec, record.spill, g_quitting and the recorder's blocks *)
Definition jw_keep (cx : lcx) (O : list (Z * Z)) (a : Z) : Prop :=
  x_sp1 cx <= a < x_sp1 cx + 88 \/ x_sp1 cx + 104 <= a < x_sp1 cx + 144 \/ x_sp0 cx - 104 <= a < x_sp0 cx \/
  A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
  A_G_QUITTING <= a < A_G_QUITTING + 4 \/ inFP (ablocks_fp O) a.
Lemma jw_keep_cases : forall cx O a, jw_keep cx O a ->
  (x_sp1 cx <= a < x_sp1 cx + 88 \/ x_sp1 cx + 104 <= a < x_sp1 cx + 144 \/ x_sp1 cx + 152 <= a < x_sp1 cx + 256) \/
  (0x5e3740 <= a < 0x5e3c64) \/ (exists p n, In (p, n) O /\ p <= a < p + req_size n).
Proof.
intros cx O a H.
assert (Hs : x_sp1 cx = x_sp0 cx - 256) by reflexivity.
unfold jw_keep, A_G_REC, A_REC_SPILL, A_G_QUITTING, REC_SIZE, SC_SIZE in H.
destruct H as [H|[H|[H|[H|[H|[H|H]]]]]]; try (left; lia); try (right; left; lia).
right; right. destruct H as (r & Hr & Hlo & Hhi). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin).
exists p, n. cbn [fst snd] in *. split; [exact Hin | lia].
Qed.
(* the facts of the context carried to a memory that agrees on those bytes *)
Lemma jw_kept : forall cx q ly S (W : world SEGS) mem mem' X t c a,
  (forall z, jw_keep cx (q_O1 q) z -> rdW W mem' z = rdW W mem z) ->
  lt_slots cx (rdW W mem) -> lt_saved cx (rdW W mem) ->
  rdword (rdW W mem) (x_sp1 cx + LT_HOSTB) = Some (r_host (q_Rh q)) ->
  rdword (rdW W mem) (x_sp1 cx + LT_STATEB) = Some (r_state (q_Rh q)) ->
  aw_rec B cx q ly S W mem X -> aw_wslots cx (rdW W mem) t c a ->
  lt_slots cx (rdW W mem') /\ lt_saved cx (rdW W mem') /\
  rdword (rdW W mem') (x_sp1 cx + LT_HOSTB) = Some (r_host (q_Rh q)) /\
  rdword (rdW W mem') (x_sp1 cx + LT_STATEB) = Some (r_state (q_Rh q)) /\
  aw_rec B cx q ly S W mem' X /\ aw_wslots cx (rdW W mem') t c a.
Proof.
intros cx q ly S W mem mem' X t c a HK HSl HSv Hh Hs Hrec Hws.
assert (Hsp : x_sp1 cx = x_sp0 cx - 256) by reflexivity.
assert (KW : forall a0 v, (forall z, a0 <= z < a0 + 8 -> jw_keep cx (q_O1 q) z) ->
  rdword (rdW W mem) a0 = Some v -> rdword (rdW W mem') a0 = Some v).
{ intros a0 v Ha H. apply (jw_rdword_kept (rdW W mem)); [|exact H]. intros z Hz. apply HK, Ha, Hz. }
split; [|split; [|split; [|split; [|split]]]].
- intros o v Hin. pose proof (jw_slot_off o v Hin) as Ho. apply KW; [|exact (HSl o v Hin)].
  intros z Hz. left. lia.
- intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  change (length LT_SAVED) with 13%nat in Hi13.
  apply KW; [|exact (HSv i r Hi)]. intros z Hz. right; right; left. lia.
- apply KW; [|exact Hh]. intros z Hz. right; left. unfold LT_HOSTB in Hz. lia.
- apply KW; [|exact Hs]. intros z Hz. right; left. unfold LT_STATEB in Hz. lia.
- apply (aw_rec_kept B cx q ly S W mem mem' X Hrec). intros z Hz. apply HK. unfold jw_keep. right; right; right. exact Hz.
- destruct Hws as (W1 & W2 & W3). unfold aw_wslots.
  split; [|split]; (apply KW; [|eassumption]); intros z Hz; right; left; unfold LT_W in Hz; lia.
Qed.
Lemma jw_sep : forall ly S (W : world SEGS) mem md l1 l2 l3 x y,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (l1 ++ x :: l2 ++ y :: l3) ->
  zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md l1 l2 l3 x y HAR HP.
apply (sep_blocks_perm SEGS B LAWS ly S W mem md x y (l1 ++ l2 ++ l3) HAR).
eapply Permutation_trans; [exact HP | apply jw_perm2].
Qed.

(* ---- segment J: 0x8680c .. 0x86850 (the split loop's head) or 0x8693c (the empty line) ---- *)
Theorem aw_seg_J : forall m, (forall nm, AW_S_stmt B MT m nm) -> LT_K_stmt B MT m -> AW_J_stmt B MT m.
Proof.
intros m HSL HK cx q ly S W regs mem md k acc text copy arr Hm HFP0 HC HMG Hrec Hws R24 R23 R25 HTx R12 R26.
destruct HTx as (T & HT & HTl & HTf).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [[HAC0 HAC1] HAC2].
assert (WS : LTOI_STK = 32768) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp10 : x_sp1 cx = x_sp0 cx - 256) by reflexivity.
assert (Hsp00 : x_sp0 cx = spZ (x_regs cx)) by reflexivity.
pose proof HC as ((HB0 & HFRM & HSl & R8 & R9 & R22 & Hm32 & Hn & Hp & Hr & Hh & Hs) & Hbud).
pose proof HFRM as (HJ & Hsp & R3 & R4 & Hsv). clear HFRM.
pose proof HMG as (R18 & R19 & R20 & R21 & R27).
pose proof HB0 as (HPRE0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
rewrite WS in Hslo.
pose proof (proj1 HJ) as HAR.
(* the three blocks of the message *)
pose proof Hrec as Hrec0. unfold aw_rec, lt_rec in Hrec0. destruct Hrec0 as (_ & _ & _ & _ & _ & HPerm).
rewrite aw_blocks_eq in HPerm.
pose proof (q_L0_U cx q) as HL0.
pose proof (SlotWords.sw_line_le (q_D cx q)) as HLN.
change (Verbs.line (q_D cx q)) with (q_LN cx q) in HLN. change (Verbs.upto0 (q_D cx q)) with (q_U cx q) in HLN.
assert (RQ : req_size (q_L0 cx q + 1) = q_L0 cx q + 1)
  by (unfold req_size; rewrite (proj2 (Z.eqb_neq (q_L0 cx q + 1) 0)) by lia; reflexivity).
assert (HinT : In (text, q_L0 cx q + 1) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
assert (HinC : In (copy, q_L0 cx q + 1) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. apply in_or_app. right. right. left.
  reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md copy (q_L0 cx q + 1) HAR HinC) as (Hc16 & Hc4096 & Hcceil & _ & _ & _ & Hcmax).
destruct (al_blocks _ _ LAWS ly S W mem md text (q_L0 cx q + 1) HAR HinT) as (Ht16 & Ht4096 & Htceil & _).
rewrite RQ in Hcceil, Htceil. unfold MALLOC_MAX in Hcmax.
pose proof (blk_off_imgP B ly S W mem md copy _ HAR HinC) as Hcoff. rewrite RQ in Hcoff. unfold off_img in Hcoff.
(* copy is made since the entry, apart from text and from the recorder's blocks *)
assert (HnC : ~ In (copy, q_L0 cx q + 1) (x_bl0 B cx)).
{ intros Hin. apply in_split in Hin as (u1 & u2 & Hu). rewrite Hu in HPerm.
  assert (El : q_O1 q ++ (u1 ++ (copy, q_L0 cx q + 1) :: u2) ++
     [(text, q_L0 cx q + 1); (copy, q_L0 cx q + 1); (arr, SlotSpec.arr_size (q_L0 cx q))] =
     (q_O1 q ++ u1) ++ (copy, q_L0 cx q + 1) :: (u2 ++ [(text, q_L0 cx q + 1)]) ++ (copy, q_L0 cx q + 1) ::
     [(arr, SlotSpec.arr_size (q_L0 cx q))]) by (rewrite <- !app_assoc; reflexivity).
  rewrite El in HPerm. pose proof (jw_sep ly S W mem md _ _ _ _ _ HAR HPerm) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite RQ in Hd. lia. }
assert (HdTC : text + (q_L0 cx q + 1) <= copy \/ copy + (q_L0 cx q + 1) <= text).
{ assert (Hd : zdisjoint (block_rng (text, q_L0 cx q + 1)) (block_rng (copy, q_L0 cx q + 1))).
  { apply (jw_sep ly S W mem md (q_O1 q ++ x_bl0 B cx) [] [(arr, SlotSpec.arr_size (q_L0 cx q))] _ _ HAR).
    rewrite <- app_assoc. exact HPerm. }
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite RQ in Hd. exact Hd. }
assert (HdOC : forall p0 n0, In (p0, n0) (q_O1 q) -> p0 + req_size n0 <= copy \/ copy + (q_L0 cx q + 1) <= p0).
{ intros p0 n0 Hin. apply in_split in Hin as (u1 & u2 & Hu). rewrite Hu in HPerm.
  assert (El : (u1 ++ (p0, n0) :: u2) ++ x_bl0 B cx ++
     [(text, q_L0 cx q + 1); (copy, q_L0 cx q + 1); (arr, SlotSpec.arr_size (q_L0 cx q))] =
     u1 ++ (p0, n0) :: (u2 ++ x_bl0 B cx ++ [(text, q_L0 cx q + 1)]) ++ (copy, q_L0 cx q + 1) ::
     [(arr, SlotSpec.arr_size (q_L0 cx q))]) by (rewrite <- !app_assoc; reflexivity).
  rewrite El in HPerm. pose proof (jw_sep ly S W mem md _ _ _ _ _ HAR HPerm) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite RQ in Hd. exact Hd. }
assert (HO1 : forall pn, In pn (q_O1 q) -> In pn (ablocks B ly S)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. exact Hpn. }
(* ---- 0x8680c .. 0x86814: a0 := copy, a1 := text, jal __asan_memcpy ---- *)
destruct (jw_seedA W regs mem) as [HS SHOK].
assert (EL : forall n, (n < A_TEXT)%nat -> ew (ja_E regs) n = ew (Ereg regs []) n)
  by (intros n Hn0; unfold ja_E; apply Eimg_low; exact Hn0).
assert (HED : ed (ja_E regs) = ed (Ereg regs [])) by reflexivity.
assert (HEI : img_env VAL A_LIM (ja_E regs)) by (unfold ja_E; apply Eimg_env).
remember (ja_E regs) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn0. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn0. }
assert (HAE : env_agree 32 (Ereg regs []) E).
{ split; [intros n Hn0; rewrite EL by (unfold A_TEXT; lia); reflexivity | exact HED]. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
clear HE EL HED.
paj_run_tok RUN HS HJ SHOK JBspan.
{ awr_ok_tac. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv1 := d) in *; clearbody mdv1 end.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
by (intros a Ha; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) Hfr);
  [ intros b wlo whi a' Hin; vm_compute in Hin; destruct Hin | exact Ha | tauto ]) end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (HPA : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS); [exact HAE | vm_compute; reflexivity]. }
rename ms into ms1.
assert (P10' : getr (ms_regs ms1) 10 = w64 copy) by (rewrite P10, (EEo 23%nat 23%bv eq_refl); exact R23).
assert (P11' : getr (ms_regs ms1) 11 = w64 text) by (rewrite P11, (EEo 24%nat 24%bv eq_refl); exact R24).
assert (P12' : getr (ms_regs ms1) 12 = w64 (Z.of_nat (length (q_LN cx q)) + 1))
  by (rewrite P12, (EEo 12%nat 12%bv eq_refl); exact R12).
assert (HspT : spZ (ms_regs ms1) = x_sp0 cx + -256) by (unfold spZ at 1; rewrite P2, Usp; lia).
assert (P3' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3, (EEo 3%nat 3%bv eq_refl), R3; exact Hgp).
assert (P4' : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4, (EEo 4%nat 4%bv eq_refl), R4; exact Htp).
assert (P1' : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + AW_J1)) by (rewrite P1; reflexivity).
assert (HraT : YK0s.ret_ok (Z_to_bv 64 (BASE + AW_J1))) by (apply ret_ok_codeptr_v; unfold AW_J1; [lia | reflexivity]).
(* the memcpy's premises: copy is a block made since the entry, below the stack, apart from text *)
pose proof (proj1 HJ) as HAR1.
assert (HDEST : forall a, copy <= a < copy + (Z.of_nat (length (q_LN cx q)) + 1) ->
  awr_byte SEGS B LTOI_STK (x_sp0 cx) cmd_PG (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly S) (frames (x_S cx)) ly [] a /\
  ~ (x_sp0 cx + -256 - ESTACK <= a < x_sp0 cx + -256)).
{ intros a Ha. split.
  - right; right; left. exists copy, (q_L0 cx q + 1). split; [exact HinC|]. split; [exact HnC|]. rewrite RQ. lia.
  - lia. }
assert (HPCw : forall a, copy <= a < copy + (Z.of_nat (length (q_LN cx q)) + 1) -> inFP cmd_PG a ->
  (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a) \/ x_sp0 cx <= a < ly_top ly ->
  writable_at SEGS (mrestrict (w_H W) (ms_mem ms1)) a).
{ intros a Ha Hpg. exfalso. destruct Hpg as (r0 & Hr0 & Hr0a). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr0.
  cbn [In] in Hr0. destruct Hr0 as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr0a; lia. }
assert (HSRC : 0 <= text /\ text + (Z.of_nat (length (q_LN cx q)) + 1) <= 2 ^ 63 /\
  src_ok SEGS W (ms_regs ms1) (ms_mem ms1) text (Z.of_nat (length (q_LN cx q)) + 1) /\
  (copy + (Z.of_nat (length (q_LN cx q)) + 1) <= text \/ text + (Z.of_nat (length (q_LN cx q)) + 1) <= copy) /\
  amem_range text (Z.of_nat (length (q_LN cx q)) + 1) /\
  range_addressable (aview SEGS (w_H W) (ms_mem ms1)) SHADOW_OFF text (Z.of_nat (length (q_LN cx q)) + 1) /\
  (0 < Z.of_nat (length (q_LN cx q)) + 1 ->
     shadow_hull_vis (aview SEGS (w_H W) (ms_mem ms1)) text (Z.of_nat (length (q_LN cx q)) + 1))).
{ split; [lia|]. split; [lia|]. split.
  { intros a Ha. split.
    - destruct (al_blocks _ _ LAWS ly S W (ms_mem ms1) mdv1 text _ HAR1 HinT) as (_ & _ & _ & _ & HtP & _).
      apply (aview_some_of_apresent SEGS). apply (HtP a). rewrite RQ. lia.
    - rewrite HspT. lia. }
  split; [lia|].
  split; [apply (amem_range_of_block SEGS B LAWS ly S W (ms_mem ms1) mdv1 text (q_L0 cx q + 1));
    [exact HAR1 | exact HinT | lia | rewrite RQ; lia]|].
  split; [apply (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms1) mdv1 text (q_L0 cx q + 1));
    [exact HAR1 | exact HinT | lia | rewrite RQ; lia]|].
  intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem ms1) mdv1 text (q_L0 cx q + 1));
    [exact HAR1 | exact HinT | lia | rewrite RQ; lia | exact Hn0]. }
assert (HAMR : amem_range copy (Z.of_nat (length (q_LN cx q)) + 1)).
{ apply (amem_range_of_block SEGS B LAWS ly S W (ms_mem ms1) mdv1 copy (q_L0 cx q + 1));
    [exact HAR1 | exact HinC | lia | rewrite RQ; lia]. }
assert (HRAD : range_addressable (aview SEGS (w_H W) (ms_mem ms1)) SHADOW_OFF copy (Z.of_nat (length (q_LN cx q)) + 1)).
{ apply (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms1) mdv1 copy (q_L0 cx q + 1));
    [exact HAR1 | exact HinC | lia | rewrite RQ; lia]. }
assert (HHULL : 0 < Z.of_nat (length (q_LN cx q)) + 1 ->
  shadow_hull_vis (aview SEGS (w_H W) (ms_mem ms1)) copy (Z.of_nat (length (q_LN cx q)) + 1)).
{ intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem ms1) mdv1 copy (q_L0 cx q + 1));
    [exact HAR1 | exact HinC | lia | rewrite RQ; lia | exact Hn0]. }
(* ---- __asan_memcpy(copy, text, |line| + 1) ---- *)
eapply SRr_bind.
{ exact (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIG CS___asan_memcpy) AMEMCPY W (ms_regs ms1) (ms_mem ms1) LTOI_STK
    (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S mdv1 k copy text
    (Z.of_nat (length (q_LN cx q)) + 1) (-256) (Z_to_bv 64 (BASE + AW_J1)) HJ P10' P11' P12'
    ltac:(lia) ltac:(lia) ltac:(lia) HspT eq_refl ltac:(lia) ltac:(rewrite Hes, WS; lia) P3' P4' P1' HraT
    HDEST HPCw HAMR HRAD HHULL HSRC). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10b & Heff & Hkeep2 & Hpres2 & Hsame).
clear Hpres2 Hsame H10b.
assert (HPT : aregs_preserved regs regs2) by exact (aregs_preserved_trans _ _ _ HPA HP2).
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2j & _).
(* copy holds the line and its NUL *)
assert (HLN2 : abytes_atR (rdW W mem2) copy (q_LN cx q ++ [Z_to_bv 8 0])).
{ intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (Heff (Z.of_nat i)) by lia. rewrite K1 by lia. rewrite (HT i) by lia.
  rewrite <- HTf. rewrite jw_nth_firstn by lia. reflexivity. }
remember (bv_unsigned (nth 0 (q_LN cx q ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as b0 eqn:Eb0.
assert (Hb0 : rdW W mem2 copy = Some b0).
{ pose proof (HLN2 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as H0.
  change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r in H0. rewrite Eb0. exact H0. }
destruct (aview_byte SEGS _ _ _ _ Hb0) as (_ & _ & _ & Rb0).
(* ---- 0x86818 .. 0x86830: the check of copy, w.n := 0, a0 := copy[0], beqz a0 ---- *)
assert (HspR2 : spZ regs2 = x_sp1 cx).
{ unfold spZ. rewrite (jw_pres _ _ 2 2 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  fold (spZ (ms_regs ms1)). rewrite HspT. lia. }
assert (Hal1 : x_sp1 cx mod 16 = 0).
{ unfold x_sp1, LT_FRAME. rewrite Zminus_mod, Hal16. reflexivity. }
clear HS SHOK.
assert (SB1 : 2 ^ 46 <= spZ regs2) by (rewrite HspR2; lia).
assert (SB2 : spZ regs2 + 256 <= 2 ^ 47) by (rewrite HspR2; lia).
assert (SB3 : spZ regs2 mod 16 = 0) by (rewrite HspR2; exact Hal1).
assert (SB4 : forall a, spZ regs2 + 88 <= a < spZ regs2 + 148 -> apresent (w_H W) mem2 a).
{ intros a Ha. apply Hpres2j. rewrite HspR2 in Ha. rewrite WS. lia. }
assert (SB5 : getr regs2 9 = w64 LT_SB).
{ rewrite (jw_pres _ _ 9 9 HPT ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact R9. }
assert (SB6 : getr regs2 23 = w64 copy).
{ rewrite (jw_pres _ _ 23 23 HPT ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact R23. }
assert (SB7 : copy + 1 <= spZ regs2) by (rewrite HspR2; lia).
destruct (jw_seedB W regs2 mem2 copy b0 SB1 SB2 SB3 SB4 SB5 SB6 Hc4096 SB7 ltac:(lia) Hc16 Hb0) as [HS SHOK].
clear SB1 SB2 SB3 SB4 SB5 SB6 SB7.
assert (ELb : forall n, (n < A_TEXT)%nat -> ew (jb_E regs2 b0) n = ew (Ereg regs2 [Z_to_bv 64 b0]) n)
  by (intros n Hn0; unfold jb_E; apply Eimg_low; exact Hn0).
assert (HEDb : ed (jb_E regs2 b0) = ed (Ereg regs2 [Z_to_bv 64 b0])) by reflexivity.
assert (HEIb : img_env VAL A_LIM (jb_E regs2 b0)) by (unfold jb_E; apply Eimg_env).
remember (jb_E regs2 b0) as Eb eqn:HEb.
assert (EEb : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew Eb n = getr regs2 rr).
{ intros n rr Hn0. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite ELb by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn0. }
assert (HAEb : env_agree 32 (Ereg regs2 [Z_to_bv 64 b0]) Eb).
{ split; [intros n Hn0; rewrite ELb by (unfold A_TEXT; lia); reflexivity | exact HEDb]. }
assert (Eb32 : ew Eb 32 = Z_to_bv 64 b0) by (rewrite ELb by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (Eb9 : ew Eb 9 = Z_to_bv 64 LT_SB).
{ rewrite (EEb 9%nat 9%bv eq_refl), (jw_pres _ _ 9 9 HPT ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  exact R9. }
assert (Eb23 : ew Eb 23 = Z_to_bv 64 copy).
{ rewrite (EEb 23%nat 23%bv eq_refl), (jw_pres _ _ 23 23 HPT ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  exact R23. }
assert (Uspb : bv_unsigned (ew Eb 2) = x_sp1 cx) by (rewrite (EEb 2%nat 2%bv eq_refl); exact HspR2).
clear HEb ELb HEDb.
paj_run_tok RUN HS HJ2 SHOK JBspan.
{ (* the 1-byte check of copy: copy's byte is addressable *)
  rewrite (U_atom Eb 23 copy Eb23) by lia.
  apply (obl_of_block SEGS B LAWS ly S W mem2 md2 Eb JBx copy 1 copy (q_L0 cx q + 1) HAR2 HinC); [| lia | rewrite RQ; lia].
  unfold JBx. rewrite (U_atom Eb 9 LT_SB Eb9) by (unfold LT_SB; lia). reflexivity. }
{ jw_awr Uspb WS. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
lazymatch goal with Hfr : frame_of Eb _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KB1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (x_sp1 cx + 88 <= a < x_sp1 cx + 104 \/ x_sp1 cx + 144 <= a < x_sp1 cx + 148) -> rdW W (ms_mem ms) a = rdW W mem2 a)
by (intros a Ha Hna;
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _
    (fun a => x_sp1 cx + 88 <= a < x_sp1 cx + 104 \/ x_sp1 cx + 144 <= a < x_sp1 cx + 148) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Uspb in Hrr; lia|]);
    destruct Hin
  | exact Ha | exact Hna ]) end.
clear HF HFr HG.
rename ms into msB.
psrr_branch_tok RUN BR HS SHOK JBspan.
- (* copy[0] = 0: the line is empty; 0x86830 jumps to 0x8693c *)
  assert (Hz : b0 = 0).
  { rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
    rewrite (U_atom _ 32 b0) in Hc by (first [cbn [ew ewset Nat.eqb]; exact Eb32 | lia]).
    rewrite U_lit in Hc by lia. exact Hc. }
  clear Hc.
  assert (HLN0 : q_LN cx q = []).
  { rewrite Eb0 in Hz. revert Hz. pose proof (SlotWords.sw_line_nz (q_D cx q)) as Hnz.
    change (Verbs.line (q_D cx q)) with (q_LN cx q) in Hnz. revert Hnz.
    destruct (q_LN cx q) as [|x l]; intros Hnz Hz; [reflexivity|exfalso].
    cbn [app nth] in Hz. exact (Hnz x (or_introl eq_refl) Hz). }
  assert (HWS0 : q_ws cx q = []).
  { change (q_ws cx q) with (Verbs.words (q_LN cx q)). rewrite HLN0. reflexivity. }
  clear Hz.
  paj_run_to_tok RUNTO HS HJ2 SHOK JBspan LO_K.
  { jw_awr Uspb WS. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv3 := d) in *; clearbody mdv3 end.
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ (ms_mem msB)) (mrestrict _ _) |- _ =>
  assert (KB2 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (x_sp1 cx + 88 <= a < x_sp1 cx + 104 \/ x_sp1 cx + 144 <= a < x_sp1 cx + 148) ->
    rdW W (ms_mem ms) a = rdW W (ms_mem msB) a)
  by (intros a Ha Hna;
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _
      (fun a => x_sp1 cx + 88 <= a < x_sp1 cx + 104 \/ x_sp1 cx + 144 <= a < x_sp1 cx + 148) Hfr);
    [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq0 | Hin];
        [injection Hq0 as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?Uspb in Hrr; lia|]);
      destruct Hin
    | exact Ha | exact Hna ]) end.
  (* w.n holds 0 *)
  assert (HWN : aval_mem (rdW W (ms_mem ms)) (x_sp1 cx + LT_W + 24) 4 0).
  { pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
    pose proof (mem_ok_region SEGS _ _ _ _ HM (in_cons _ _ _ (in_eq _ _))) as HR1.
    pose proof (region_ok_chunk SEGS _ _ _ _ HR1 (in_eq _ _)) as HC1.
    cbn [YP09.r_base base_val ew ewset Nat.eqb] in HC1. rewrite Uspb in HC1.
    pose proof (val_of_chunk_ok SEGS _ _ _ 144 4 (SLit 0) 0 HC1 eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
    intros k0 Hk0. specialize (HV k0 Hk0). unfold aview.
    replace (x_sp1 cx + LT_W + 24) with (x_sp1 cx + 144) by (unfold LT_W; lia). rewrite HV. cbn [option_map].
    rewrite jw_le_byte_0, jw_le_byte_0o. reflexivity. }
  (* the memory the context reads is kept *)
  assert (HK3 : forall z, jw_keep cx (q_O1 q) z -> rdW W (ms_mem ms) z = rdW W mem z).
  { intros z Hzk. destruct (jw_keep_cases cx (q_O1 q) z Hzk) as [Hf | [Hi | (p0 & n0 & Hpn & Hpz)]].
    - rewrite KB2, KB1, Hkeep2, K1 by lia; reflexivity.
    - rewrite KB2, KB1, Hkeep2, K1 by lia; reflexivity.
    - destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR (HO1 _ Hpn)) as (_ & Hp4 & Hpc & _).
      pose proof (HdOC p0 n0 Hpn) as Hd.
      rewrite KB2, KB1, Hkeep2, K1 by lia; reflexivity. }
  destruct (jw_kept cx q ly S W mem (ms_mem ms) _ text copy arr HK3 HSl Hsv Hh Hs Hrec Hws)
    as (HSl3 & Hsv3 & Hh3 & Hs3 & Hrec3 & Hws3).
  pmkst HS.
  (* the registers at 0x8693c *)
  lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
    assert (HAE1 : env_agree 32 (Ereg regs2 [Z_to_bv 64 b0]) E1) by (repeat (apply jw_agree_ewset; [|lia]); exact HAEb)
  end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 [Z_to_bv 64 b0]
    [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv HS HAE1 ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  assert (RR : forall (r : bv 5) z, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv ->
    acallee_saved z -> Z_to_bv 5 z = r -> getr (ms_regs ms) r = getr regs r).
  { intros r z Hin Hz Er. rewrite (HKR r Hin). exact (jw_pres _ _ r z HPT Hz Er). }
  assert (G2 : getr (ms_regs ms) 2 = getr regs 2) by (apply (RR _ 2); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G3 : getr (ms_regs ms) 3 = getr regs 3) by (apply (RR _ 3); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G4 : getr (ms_regs ms) 4 = getr regs 4) by (apply (RR _ 4); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G8 : getr (ms_regs ms) 8 = getr regs 8) by (apply (RR _ 8); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G9 : getr (ms_regs ms) 9 = getr regs 9) by (apply (RR _ 9); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G18 : getr (ms_regs ms) 18 = getr regs 18) by (apply (RR _ 18); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G19 : getr (ms_regs ms) 19 = getr regs 19) by (apply (RR _ 19); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G20 : getr (ms_regs ms) 20 = getr regs 20) by (apply (RR _ 20); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G21 : getr (ms_regs ms) 21 = getr regs 21) by (apply (RR _ 21); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G22 : getr (ms_regs ms) 22 = getr regs 22) by (apply (RR _ 22); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G23 : getr (ms_regs ms) 23 = getr regs 23) by (apply (RR _ 23); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G24 : getr (ms_regs ms) 24 = getr regs 24) by (apply (RR _ 24); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G25 : getr (ms_regs ms) 25 = getr regs 25) by (apply (RR _ 25); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G27 : getr (ms_regs ms) 27 = getr regs 27) by (apply (RR _ 27); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (Hsp' : spZ (ms_regs ms) = x_sp1 cx) by (unfold spZ; rewrite G2; exact Hsp).
  assert (Hw3 : lt_words cx (ms_regs ms) (rdW W (ms_mem ms)) (q_D cx q) (q_ws cx q) text copy arr []).
  { destruct Hws3 as (W1 & W2 & W3). rewrite HWS0.
    split; [rewrite G24; exact R24|]. split; [rewrite G23; exact R23|]. split; [rewrite G25; exact R25|].
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
    split; [exact HWN|]. split; [reflexivity|].
    split; [intros i0 pt Hi0; destruct i0; discriminate Hi0 | intros i0 pt w1 Hi0; destruct i0; discriminate Hi0]. }
  exact (aw_LT_K B MT m HK cx q ly S W (ms_regs ms) (ms_mem ms) mdv3 k acc text copy arr [] Hm HFP0
    (conj (conj HB0 (conj (conj HJ2 (conj Hsp' (conj (eq_trans G3 R3) (conj (eq_trans G4 R4) Hsv3))))
      (conj HSl3 (conj (eq_trans G8 R8) (conj (eq_trans G9 R9) (conj (eq_trans G22 R22)
      (conj Hm32 (conj Hn (conj Hp (conj Hr (conj Hh3 Hs3))))))))))) Hbud)
    (conj (eq_trans G18 R18) (conj (eq_trans G19 R19) (conj (eq_trans G20 R20) (conj (eq_trans G21 R21)
      (eq_trans G27 R27)))))
    Hw3 Hrec3).
- (* copy[0] <> 0: 0x86834 .. 0x8684c, the spills and the split loop's registers *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK JBspan AW_S.
  { jw_awr Uspb WS. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv3 := d) in *; clearbody mdv3 end.
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ (ms_mem msB)) (mrestrict _ _) |- _ =>
  assert (KB2 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (x_sp1 cx + 88 <= a < x_sp1 cx + 104 \/ x_sp1 cx + 144 <= a < x_sp1 cx + 148) ->
    rdW W (ms_mem ms) a = rdW W (ms_mem msB) a)
  by (intros a Ha Hna;
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _
      (fun a => x_sp1 cx + 88 <= a < x_sp1 cx + 104 \/ x_sp1 cx + 144 <= a < x_sp1 cx + 148) Hfr);
    [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq0 | Hin];
        [injection Hq0 as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?Uspb in Hrr; lia|]);
      destruct Hin
    | exact Ha | exact Hna ]) end.
  (* the registers at 0x86850 *)
  lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
    assert (HAE1 : env_agree 32 (Ereg regs2 [Z_to_bv 64 b0]) E1) by (repeat (apply jw_agree_ewset; [|lia]); exact HAEb)
  end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 [Z_to_bv 64 b0]
    [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25]%bv HS HAE1 ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  assert (RR : forall (r : bv 5) z, In r [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25]%bv ->
    acallee_saved z -> Z_to_bv 5 z = r -> getr (ms_regs ms) r = getr regs r).
  { intros r z Hin Hz Er. rewrite (HKR r Hin). exact (jw_pres _ _ r z HPT Hz Er). }
  (* the spills and w.n, from the two frame regions *)
  assert (HR5 : 0 <= q_r q - SlotSpec.hdr_n (q_r q) < 2 ^ 64) by (unfold SlotSpec.hdr_n; lia).
  assert (HRm : 0 <= Z.of_nat (q_m q) < 2 ^ 64) by lia.
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
  pose proof (mem_ok_region SEGS _ _ _ _ HM (in_eq _ _)) as HR0.
  pose proof (mem_ok_region SEGS _ _ _ _ HM (in_cons _ _ _ (in_eq _ _))) as HR1.
  pose proof (region_ok_chunk SEGS _ _ _ _ HR0 (in_eq _ _)) as HC96.
  pose proof (region_ok_chunk SEGS _ _ _ _ HR0 (in_cons _ _ _ (in_eq _ _))) as HC88.
  pose proof (region_ok_chunk SEGS _ _ _ _ HR1 (in_eq _ _)) as HC144.
  cbn [YP09.r_base base_val ew ewset Nat.eqb] in HC96, HC88, HC144. rewrite Uspb in HC96, HC88, HC144.
  assert (V88 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (x_sp1 cx + 88) (N.to_nat 8) (q_r q - SlotSpec.hdr_n (q_r q))).
  { apply (val_of_chunk_ok SEGS _ _ _ 88 8 (SOff 21 0) _ HC88).
    - cbn [sv_denot ew ewset Nat.eqb]. rewrite (EEb 21%nat 21%bv eq_refl).
      rewrite (jw_pres _ _ 21 21 HPT ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), R21.
      rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
    - change (8 * Z.of_N 8) with 64. exact HR5.
    - zside. }
  assert (V96 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (x_sp1 cx + 96) (N.to_nat 8) (Z.of_nat (q_m q))).
  { apply (val_of_chunk_ok SEGS _ _ _ 96 8 (SOff 27 0) _ HC96).
    - cbn [sv_denot ew ewset Nat.eqb]. rewrite (EEb 27%nat 27%bv eq_refl).
      rewrite (jw_pres _ _ 27 27 HPT ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), R27.
      rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
    - change (8 * Z.of_N 8) with 64. exact HRm.
    - zside. }
  pose proof (val_of_chunk_ok SEGS _ _ _ 144 4 (SLit 0) 0 HC144 eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V144.
  assert (Hsp5 : rdword (rdW W (ms_mem ms)) (x_sp1 cx + LT_SPILL5) = Some (q_r q - SlotSpec.hdr_n (q_r q))).
  { apply (PaLibF.rdword_of_val_mem SEGS (w_H W) (ms_mem ms)); [|exact HR5]. unfold LT_SPILL5. exact V88. }
  assert (Hsp11 : rdword (rdW W (ms_mem ms)) (x_sp1 cx + LT_SPILL11) = Some (Z.of_nat (q_m q))).
  { apply (PaLibF.rdword_of_val_mem SEGS (w_H W) (ms_mem ms)); [|exact HRm]. unfold LT_SPILL11. exact V96. }
  assert (HWN : aval_mem (rdW W (ms_mem ms)) (x_sp1 cx + LT_W + 24) 4 0).
  { intros k0 Hk0. specialize (V144 k0 Hk0). unfold aview.
    replace (x_sp1 cx + LT_W + 24) with (x_sp1 cx + 144) by (unfold LT_W; lia). rewrite V144. cbn [option_map].
    rewrite jw_le_byte_0, jw_le_byte_0o. reflexivity. }
  (* the memory the context reads is kept, and copy holds the line *)
  assert (HK3 : forall z, jw_keep cx (q_O1 q) z -> rdW W (ms_mem ms) z = rdW W mem z).
  { intros z Hzk. destruct (jw_keep_cases cx (q_O1 q) z Hzk) as [Hf | [Hi | (p0 & n0 & Hpn & Hpz)]].
    - rewrite KB2, KB1, Hkeep2, K1 by lia; reflexivity.
    - rewrite KB2, KB1, Hkeep2, K1 by lia; reflexivity.
    - destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR (HO1 _ Hpn)) as (_ & Hp4 & Hpc & _).
      pose proof (HdOC p0 n0 Hpn) as Hd.
      rewrite KB2, KB1, Hkeep2, K1 by lia; reflexivity. }
  destruct (jw_kept cx q ly S W mem (ms_mem ms) _ text copy arr HK3 HSl Hsv Hh Hs Hrec Hws)
    as (HSl3 & Hsv3 & Hh3 & Hs3 & Hrec3 & Hws3).
  assert (HLN3 : abytes_atR (rdW W (ms_mem ms)) copy (q_LN cx q ++ [Z_to_bv 8 0])).
  { apply (abytes_atR_kept_r (rdW W mem2)); [|exact HLN2]. intros z Hz. rewrite length_app in Hz. cbn [length] in Hz.
    rewrite KB2, KB1 by lia. reflexivity. }
  pose proof (proj1 HJ2) as HAR3.
  destruct (al_blocks _ _ LAWS ly S W (ms_mem ms) mdv3 copy _ HAR3 HinC) as (_ & _ & _ & _ & HcP3 & _).
  destruct (jw_bytes_of_rd (rdW W (ms_mem ms)) copy (Z.to_nat (q_L0 cx q + 1))) as (C & HCl & HCb).
  { intros i Hi. destruct (rdW W (ms_mem ms) (copy + Z.of_nat i)) as [v|] eqn:Ev.
    - exists v. split; [reflexivity|]. destruct (aview_byte SEGS _ _ _ _ Ev) as (_ & _ & _ & Rv). exact Rv.
    - exfalso. apply (aview_some_of_apresent SEGS (w_H W) (ms_mem ms) (copy + Z.of_nat i)); [|exact Ev].
      exact (proj1 (HcP3 (copy + Z.of_nat i) ltac:(rewrite RQ; lia))). }
  assert (HCpre : forall j, (0 <= j <= length (q_LN cx q))%nat ->
    nth_error C j = nth_error (q_LN cx q ++ [Z_to_bv 8 0]) j).
  { intros j Hj. apply (jw_nth_of_bytes (rdW W (ms_mem ms)) copy); [exact HCb | exact HLN3 | | ].
    - rewrite length_app. cbn [length]. lia.
    - rewrite HCl. lia. }
  pmkst HS.
  prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  assert (G2 : getr (ms_regs ms) 2 = getr regs 2) by (apply (RR _ 2); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G3 : getr (ms_regs ms) 3 = getr regs 3) by (apply (RR _ 3); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G4 : getr (ms_regs ms) 4 = getr regs 4) by (apply (RR _ 4); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G8 : getr (ms_regs ms) 8 = getr regs 8) by (apply (RR _ 8); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G9 : getr (ms_regs ms) 9 = getr regs 9) by (apply (RR _ 9); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G19 : getr (ms_regs ms) 19 = getr regs 19) by (apply (RR _ 19); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G20 : getr (ms_regs ms) 20 = getr regs 20) by (apply (RR _ 20); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G22 : getr (ms_regs ms) 22 = getr regs 22) by (apply (RR _ 22); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G23 : getr (ms_regs ms) 23 = getr regs 23) by (apply (RR _ 23); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G24 : getr (ms_regs ms) 24 = getr regs 24) by (apply (RR _ 24); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (G25 : getr (ms_regs ms) 25 = getr regs 25) by (apply (RR _ 25); [jw_in | unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  assert (Q10' : getr (ms_regs ms) 10 = w64 (Z.of_nat 0)) by (rewrite Q10; reflexivity).
  assert (Q18' : getr (ms_regs ms) 18 = w64 (arr + 8 * Z.of_nat 0)).
  { rewrite Q18, (EEb 25%nat 25%bv eq_refl).
    rewrite (jw_pres _ _ 25 25 HPT ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), R25.
    f_equal. lia. }
  assert (Q26' : getr (ms_regs ms) 26 = w64 (arr + 8 * Z.of_nat 0)).
  { rewrite Q26, (EEb 25%nat 25%bv eq_refl).
    rewrite (jw_pres _ _ 25 25 HPT ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), R25.
    f_equal. lia. }
  assert (Q27' : getr (ms_regs ms) 27 = w64 (copy + Z.of_nat 0)).
  { rewrite Q27, (EEb 23%nat 23%bv eq_refl).
    rewrite (jw_pres _ _ 23 23 HPT ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), R23.
    f_equal. lia. }
  assert (Hsp' : spZ (ms_regs ms) = x_sp1 cx) by (unfold spZ; rewrite G2; exact Hsp).
  assert (Harr : aw_arr (rdW W (ms_mem ms)) arr []) by (intros i0 p0 H0; destruct i0; discriminate H0).
  assert (Hfound : aw_found copy (q_ws cx q) C [] 0) by (intros k' p0 w1 H0; destruct k'; discriminate H0).
  assert (Hwords : Verbs.words_acc [] (skipn 0 (q_LN cx q)) = skipn 0 (q_ws cx q)) by reflexivity.
  exact (HSL (length (q_LN cx q) - 0)%nat cx q ly S W (ms_regs ms) (ms_mem ms) mdv3 k acc text copy arr 0%nat 0%nat C [] Hm HFP0
    (conj (conj HB0 (conj (conj HJ2 (conj Hsp' (conj (eq_trans G3 R3) (conj (eq_trans G4 R4) Hsv3))))
      (conj HSl3 (conj (eq_trans G8 R8) (conj (eq_trans G9 R9) (conj (eq_trans G22 R22)
      (conj Hm32 (conj Hn (conj Hp (conj Hr (conj Hh3 Hs3))))))))))) Hbud)
    Hrec3 Hws3 (eq_trans G24 R24) (eq_trans G23 R23) (eq_trans G25 R25) Q10' Q18' Q26' Q27'
    (eq_trans G19 R19) (eq_trans G20 R20) Hsp5 Hsp11 eq_refl (Nat.le_0_l _) (le_n 0%nat) eq_refl (Nat.le_0_l _)
    Hwords HCb HCl HCpre Harr Hfound HWN).
Qed.

End e.
End f.
End d.
