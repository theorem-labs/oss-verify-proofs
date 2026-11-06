(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the trim loop of the inlined words_of in LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x867a4 .. 0x867e4, back to its head or on to 0x8680c), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (a seed, the symbolic engine's runs and their branches) and A/ACfj.v (rt_G_allX: a loop by induction on its counter), over the plain proof's lib/Prog/SlotWordsRun.v sw_trim. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaArt PaSB CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaDenot PaLibG PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s40.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps SlotWords SlotWordsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* The trim loop (listing offsets from BASE = 0x864e4):
     0x2c0  srli/add/lb  the shadow byte of a0 = text + j - 1; `bnez` to the slow check 0x304 (the shadow entry of the
                         byte makes both vanish)
     0x2d0  lbu a3,0(a1) the byte; `bltu s0,a3` (s0 = 32) on to 0x31c: a byte above 32 is not trailing
     0x2d8  srl/andi     bit a3 of the mask s6; `beqz` on to 0x31c: not trailing
     0x2e4  lb, bnez     the shadow byte again (vanishes); `sb zero,0(a1)`; s10, a0, a1 down by one
     0x2fc  `bnez s10` back to 0x2c0, else `j 0x31c`
     0x31c  a2 = s10 + 1; `j 0x328` = AW_J.
   One pass is one induction step on j (the plain proof's sw_trim); each run starts from the seed below, which holds
   only the byte the pass reads and writes (atom 10 = a0 = a1, atom 26 = s10 = j, atom 32 = the byte). *)

(* ---- the text buffer during the loop (the plain proof's tz) ---- *)
Lemma tl_tz_ge : forall U j i, (j <= i <= length U)%nat -> nth_error (SlotWordsRun.tz U j) i = Some (Z_to_bv 8 0).
Proof.
intros U j i H. unfold SlotWordsRun.tz. rewrite nth_error_app2 by (rewrite firstn_length_le by lia; lia).
rewrite firstn_length_le by lia. apply nth_error_repeat. lia.
Qed.
Lemma tl_nth : forall {A} (l : list A) n x d, nth_error l n = Some x -> nth n l d = x.
Proof. intros A l n x d H. apply nth_error_nth. exact H. Qed.
(* the store of a 0 at byte j turns tz U (j + 1) into tz U j *)
Lemma tl_tz_store : forall (rd rd' : reader) text U j,
  (S j <= length U)%nat -> 0 <= text -> text + Z.of_nat (length U) + 1 <= 2 ^ 64 ->
  abytes_atR rd text (SlotWordsRun.tz U (S j)) ->
  (forall x, 0 <= x < 2 ^ 64 -> x <> text + Z.of_nat j -> rd' x = rd x) -> rd' (text + Z.of_nat j) = Some 0 ->
  abytes_atR rd' text (SlotWordsRun.tz U j).
Proof.
intros rd rd' text U j Hj Ht Hhi H HK H0 i Hi.
rewrite SlotWordsRun.tz_len in Hi by lia.
destruct (Nat.eq_dec i j) as [->|Hne].
- rewrite H0, (tl_nth _ _ _ _ (tl_tz_ge U j j ltac:(lia))). reflexivity.
- rewrite HK by lia. rewrite (H i ltac:(rewrite SlotWordsRun.tz_len by lia; lia)).
  assert (E : nth_error (SlotWordsRun.tz U (S j)) i = nth_error (SlotWordsRun.tz U j) i).
  { destruct (Nat.lt_ge_cases i j) as [Hlt|Hge].
    - rewrite !SlotWordsRun.tz_nth_lt by lia. reflexivity.
    - rewrite !tl_tz_ge by lia. reflexivity. }
  destruct (nth_error (SlotWordsRun.tz U j) i) as [v|] eqn:Ev.
  + rewrite (tl_nth _ _ _ _ E), (tl_nth _ _ _ _ Ev). reflexivity.
  + apply nth_error_None in Ev. rewrite SlotWordsRun.tz_len in Ev by lia. lia.
Qed.
(* a one-byte field from a byte *)
Lemma tl_aval1 : forall (rd : reader) a b, 0 <= b < 256 -> rd a = Some b -> aval_mem rd a 1 b.
Proof.
intros rd a b Hb H k Hk. replace k with 0%nat by lia. rewrite Z.add_0_r, H. f_equal.
unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small b 256) by lia. symmetry. apply Z.mod_small. lia.
Qed.
Lemma tl_perm2_loc : forall {A} (l1 l2 l3 : list A) x y, Permutation (l1 ++ x :: l2 ++ y :: l3) (x :: y :: l1 ++ l2 ++ l3).
Proof.
intros A l1 l2 l3 x y.
eapply perm_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
rewrite app_assoc. eapply perm_trans; [apply Permutation_sym, Permutation_middle|]. rewrite <- app_assoc.
apply Permutation_refl.
Qed.
(* the mask test of 0x867bc .. 0x867c4, through the engine's term for it *)
Lemma tl_mask_U : forall E b, ew E 32 = Z_to_bv 64 b -> 0 <= b <= 32 ->
  U E (SAlu ALU_AND (SAlu ALU_SRL (SLit 4294977024) (SOff 32 0)) (SLit 1)) =
  if SlotWords.sw_trail_z b then 1 else 0.
Proof.
intros E b H Hb. rewrite U_and_lit by lia. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_lit by lia. rewrite (U_atom E 32 b H) by lia.
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6) with 64.
assert (Hs : 0 <= b mod 64 < 64) by (apply Z.mod_pos_bound; lia).
rewrite zcanon_id.
- apply SlotWords.sw_trail_mask. exact Hb.
- rewrite Z.shiftr_div_pow2 by lia. unfold M64. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply (Z.le_lt_trans _ 4294977024); [|lia]. apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  assert (H1 : 2 ^ 0 <= 2 ^ (b mod 64)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 0) with 1 in H1.
  set (t := 2 ^ (b mod 64)) in *. clearbody t.
  replace 4294977024 with (1 * 4294977024) at 1 by reflexivity. apply Z.mul_le_mono_nonneg_r; lia.
Qed.
Lemma tl_den_atom : forall E n v off, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n off) = Z_to_bv 64 (v + off).
Proof.
intros E n v off Hn. cbn [sv_denot]. rewrite Hn. apply Z_to_bv64_eq_mod. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma tl_EV_ewset : forall E k w (regs : bvmap 5 word), (32 <= k)%nat ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
  forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ewset E k w) n = getr regs r.
Proof.
intros E k w regs Hk H n r Hr. pose proof (bv_unsigned_in_range 5 r) as R. change (bv_modulus 5) with 32 in R.
rewrite ew_ewset_other by lia. exact (H n r Hr).
Qed.
Ltac tl_EV EV := repeat (apply tl_EV_ewset; [lia|]); exact EV.
Ltac tl_ew0 := repeat (rewrite ew_ewset_other by lia).

(* ---- the seed at 0x867a4 ---- *)
Definition TBx : sv := SOff 9 0.
Definition TBspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition tl_reg (x : sv) : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 x)].
Definition tl_facts : facts :=
  mkFacts [ (9%nat, mkAF LT_SB LT_SB 0); (10%nat, mkAF 4096 0x7fffff800000 0); (26%nat, mkAF 1 (2 ^ 47) 0);
            (32%nat, mkAF 0 255 0) ] [] [].
Definition tl_sregs : list sv :=
  sr_set (sr_set (sr_set sr_atoms (8%bv : bv 5) (SLit 32)) (22%bv : bv 5) (SLit LT_MASK)) (11%bv : bv 5) (SOff 10 0).
Definition ss_tl : sstate := mkSS AW_T tl_sregs [tl_reg (SOff 32 0)] None tl_facts.
Definition tl_SH : list shent := [mkSHE 10 0 1].
(* the registers a pass leaves as they were *)
Definition tl_keep_shape (sr : list sv) : Prop :=
  sr_get sr (2%bv : bv 5) = SOff 2 0 /\ sr_get sr (3%bv : bv 5) = SOff 3 0 /\ sr_get sr (4%bv : bv 5) = SOff 4 0 /\
  sr_get sr (8%bv : bv 5) = SLit 32 /\ sr_get sr (9%bv : bv 5) = SOff 9 0 /\ sr_get sr (18%bv : bv 5) = SOff 18 0 /\
  sr_get sr (19%bv : bv 5) = SOff 19 0 /\ sr_get sr (20%bv : bv 5) = SOff 20 0 /\
  sr_get sr (21%bv : bv 5) = SOff 21 0 /\ sr_get sr (22%bv : bv 5) = SLit LT_MASK /\
  sr_get sr (23%bv : bv 5) = SOff 23 0 /\ sr_get sr (24%bv : bv 5) = SOff 24 0 /\
  sr_get sr (25%bv : bv 5) = SOff 25 0 /\ sr_get sr (27%bv : bv 5) = SOff 27 0.
Definition tl_regs_kept (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
  getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\
  getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\
  getr regs' 25 = getr regs 25 /\ getr regs' 27 = getr regs 27.

Ltac tl_preg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma tl_val_of_aval : forall H (m : word -> option byte) a n v,
  aval_mem (aview SEGS H m) a n v -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
Lemma tl_EE : forall (regs : bvmap 5 word) extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma tl_E32 : forall (regs : bvmap 5 word) v, ew (Eimg (Ereg regs [Z_to_bv 64 v])) 32 = Z_to_bv 64 v.
Proof. intros regs v. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.

Lemma tl_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem a j b,
  getr regs 8 = w64 32 -> getr regs 9 = w64 LT_SB -> getr regs 22 = w64 LT_MASK ->
  getr regs 10 = w64 a -> getr regs 11 = w64 a -> getr regs 26 = w64 j ->
  4096 <= a <= 0x7fffff800000 -> 1 <= j <= 2 ^ 47 -> 0 <= b <= 255 ->
  aval_mem (rdW W mem) a 1 b -> apresent (w_H W) mem a ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 b])) ss_tl
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AW_T)) mem (seg_rom SEGS))).
Proof.
intros W regs mem a j b H8 H9 H22 H10 H11 H26 Ra Rj Rb HV HP.
set (E := Eimg (Ereg regs [Z_to_bv 64 b])).
assert (E9 : ew E 9 = Z_to_bv 64 LT_SB) by (subst E; rewrite (tl_EE regs _ 9%nat 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = Z_to_bv 64 a) by (subst E; rewrite (tl_EE regs _ 10%nat 10%bv eq_refl); exact H10).
assert (E26 : ew E 26 = Z_to_bv 64 j) by (subst E; rewrite (tl_EE regs _ 26%nat 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 b) by (subst E; apply tl_E32).
unfold ss_tl. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold tl_sregs.
  apply regs_ok_rereg; [|reflexivity|].
  2: { rewrite H11. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  apply regs_ok_rereg; [|reflexivity|].
  2: { rewrite H22. reflexivity. }
  apply regs_ok_rereg; [|reflexivity|].
  2: { rewrite H8. reflexivity. }
  subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, tl_reg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E10, unsigned_lit_small by lia. split; [lia|]. split; [lia|].
  split; [intros o Ho; replace o with 0 by lia; rewrite Z.add_0_r; apply (apresent_writable SEGS); exact HP|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ a 0 1 (SOff 32 0) b);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
  rewrite Z.add_0_r. exact (tl_val_of_aval _ _ _ _ _ HV).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok tl_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E10, E26, E32, !unsigned_lit_small by (unfold LT_SB; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold LT_SB. repeat split; lia.
Qed.

(* the shadow entry of the byte: its granule is addressable for one byte, and the byte is not in the shadow band *)
Lemma tl_shok : forall (W : world SEGS) (regs : bvmap 5 word) mem a b,
  getr regs 9 = w64 LT_SB -> getr regs 10 = w64 a -> 0 <= a < 2 ^ 64 ->
  range_addressable (rdW W mem) SHADOW_OFF a 1 ->
  (a < SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= a) ->
  sh_ok SEGS TBx tl_SH (Eimg (Ereg regs [Z_to_bv 64 b])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem a b H9 H10 Ra RA Hband. unfold sh_ok, tl_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem _ TBx 10 a 1 a 0 1 RA).
- unfold TBx. replace SHADOW_OFF with LT_SB by reflexivity.
  apply U_atom; [rewrite (tl_EE regs _ 9%nat 9%bv eq_refl); exact H9 | unfold LT_SB; lia].
- apply U_atom; [rewrite (tl_EE regs _ 10%nat 10%bv eq_refl); exact H10 | lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. lia.
Qed.

(* the byte the region at atom 10 holds at a later state *)
Lemma tl_byte_now : forall E ss (ms : machine_state) (H : word -> bool) X a v,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) 0 = Some (tl_reg X) ->
  ew E 10 = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> sv_denot E X = Z_to_bv 64 v -> 0 <= v < 256 ->
  aview SEGS H (ms_mem ms) a = Some v.
Proof.
intros E ss ms H X a v HS Hn Ha Ra HX Rv.
pose proof (st_ok_pi_region_nth E ss _ 0 _ HS Hn) as Hr.
pose proof (region_ok_chunk SEGS E _ (tl_reg X) (YP09.mkChunk 0 (CVal 1 X)) Hr (or_introl eq_refl)) as Hc.
cbn [tl_reg YP09.r_base base_val] in Hc. rewrite Ha, unsigned_lit_small in Hc by lia.
pose proof (val_of_chunk_ok SEGS E _ a 0 1 X v Hc HX ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
specialize (Hv 0%nat ltac:(cbn; lia)). cbn [ms_mem restrict] in Hv. rewrite !Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal.
assert (Hl : YG0f.le_byte v (N.to_nat 1) 0 = v).
{ unfold YG0f.le_byte. change (8 * Z.of_nat (N.to_nat 1)) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia. }
transitivity (bv_unsigned (Z_to_bv 8 v)); [do 2 f_equal; exact Hl|].
rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.

(* the frame of a run from a state whose one region is the byte: every other byte is as it was *)
Lemma tl_kept1 : forall E X (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E [tl_reg X] (mrestrict H m) (mrestrict H m') -> bv_unsigned (ew E 10) = a ->
  forall y, 0 <= y < 2 ^ 64 -> y <> a -> aview SEGS H m' y = aview SEGS H m y.
Proof.
intros E X H m m' a Hf Ha y Hy Hne.
apply (kept_of_frame (segs:=SEGS) E [tl_reg X] H m m' (fun z => z = a) Hf); [|exact Hy|exact Hne].
intros bb wlo whi a' Hin Hr. cbn [windows map tl_reg YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
destruct Hin as [Heq|[]]. injection Heq as <- <- <-. cbn [base_val] in Hr. lia.
Qed.

Lemma tl_reg_atom : forall E ss (ms : machine_state) (H : word -> bool) (regs : bvmap 5 word) n (r : bv 5),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> ew E n = getr regs r -> sr_get (ss_regs ss) r = SOff n 0 ->
  getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms H regs n r HS Hn Hs. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hs.
cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma tl_reg_lit : forall E ss (ms : machine_state) (H : word -> bool) z (r : bv 5),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros E ss ms H z r HS Hs. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hs. reflexivity. Qed.
Lemma tl_keep_of : forall E ss (ms : machine_state) (H : word -> bool) (regs : bvmap 5 word),
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
  getr regs 8 = w64 32 -> getr regs 22 = w64 LT_MASK ->
  tl_keep_shape (ss_regs ss) -> tl_regs_kept regs (ms_regs ms).
Proof.
intros E ss ms H regs HS EV R8 R22 (S2 & S3 & S4 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S27).
split; [exact (tl_reg_atom E ss ms H regs 2 2%bv HS (EV 2%nat 2%bv eq_refl) S2)|].
split; [exact (tl_reg_atom E ss ms H regs 3 3%bv HS (EV 3%nat 3%bv eq_refl) S3)|].
split; [exact (tl_reg_atom E ss ms H regs 4 4%bv HS (EV 4%nat 4%bv eq_refl) S4)|].
split; [rewrite (tl_reg_lit E ss ms H 32 8%bv HS S8), R8; reflexivity|].
split; [exact (tl_reg_atom E ss ms H regs 9 9%bv HS (EV 9%nat 9%bv eq_refl) S9)|].
split; [exact (tl_reg_atom E ss ms H regs 18 18%bv HS (EV 18%nat 18%bv eq_refl) S18)|].
split; [exact (tl_reg_atom E ss ms H regs 19 19%bv HS (EV 19%nat 19%bv eq_refl) S19)|].
split; [exact (tl_reg_atom E ss ms H regs 20 20%bv HS (EV 20%nat 20%bv eq_refl) S20)|].
split; [exact (tl_reg_atom E ss ms H regs 21 21%bv HS (EV 21%nat 21%bv eq_refl) S21)|].
split; [rewrite (tl_reg_lit E ss ms H LT_MASK 22%bv HS S22), R22; reflexivity|].
split; [exact (tl_reg_atom E ss ms H regs 23 23%bv HS (EV 23%nat 23%bv eq_refl) S23)|].
split; [exact (tl_reg_atom E ss ms H regs 24 24%bv HS (EV 24%nat 24%bv eq_refl) S24)|].
split; [exact (tl_reg_atom E ss ms H regs 25 25%bv HS (EV 25%nat 25%bv eq_refl) S25)|].
exact (tl_reg_atom E ss ms H regs 27 27%bv HS (EV 27%nat 27%bv eq_refl) S27).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the write window of a pass: the byte, in the block text the first malloc made since the entry *)
Lemma tl_awr : forall E X a text n STK sp0 FP bl0 blc fr0 ly own,
  bv_unsigned (ew E 10) = a -> text <= a -> a + 1 <= text + req_size n ->
  In (text, n) blc -> ~ In (text, n) bl0 ->
  awr_ok SEGS B E [tl_reg X] STK sp0 FP bl0 blc fr0 ly own.
Proof.
intros E X a text n STK sp0 FP bl0 blc fr0 ly own Ha H1 H2 Hin Hn0.
apply awr_ok_cons_gen with (n := 10%nat) (b := a); [reflexivity | exact Ha | |].
- intros a' Ha'. cbn [YP09.r_wlo YP09.r_whi tl_reg] in Ha'. right; right; left.
  exists text, n. split; [exact Hin|]. split; [exact Hn0|]. lia.
- apply awr_ok_nil.
Qed.

(* what holds at every point of the loop, with the three registers of the blocks *)
Definition tl_ctx (cx : lcx) (q : awm) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc text copy arr : Z) :
  Prop :=
  aw_ctx B MT cx q ly S W regs mem md k acc /\ aw_msgregs cx q regs /\
  aw_rec B cx q ly S W mem (aw_blocks cx q text copy arr) /\ aw_wslots cx (rdW W mem) text copy arr /\
  getr regs 24 = w64 text /\ getr regs 23 = w64 copy /\ getr regs 25 = w64 arr.

(* the context is kept by a stretch that keeps the registers and every byte outside the block text *)
Lemma tl_ctx_kept : forall cx q ly S W regs mem md k acc text copy arr regs' mem' md',
  tl_ctx cx q ly S W regs mem md k acc text copy arr ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem' md' k ->
  tl_regs_kept regs regs' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (text <= x < text + req_size (q_L0 cx q + 1)) -> rdW W mem' x = rdW W mem x) ->
  tl_ctx cx q ly S W regs' mem' md' k acc text copy arr.
Proof.
intros cx q ly S W regs mem md k acc text copy arr regs' mem' md' HC HJ' HR HK.
destruct HC as ((HC0 & Hbud) & HMG & Hrec & Hws & R24 & R23 & R25).
destruct HC0 as (HB & (HJ & Hsp & R3 & R4 & Hsv) & HSl & R8 & R9 & R22 & Hm & Hn & Hp & Hr & Hh & Hs).
destruct HR as (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K27).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : 256 <= LTOI_STK) by (unfold LTOI_STK, LLVMF_STK; lia).
pose proof asan_consts as (C1 & _).
pose proof Hrec as (HRA & Hsp0 & Hcl & Hq & Rq & Hperm). rewrite aw_blocks_eq in Hperm.
assert (Htin : In (text, q_L0 cx q + 1) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md text _ HAR Htin) as (_ & Ht4096 & Htceil & _ & _ & _ & _).
pose proof (blk_off_imgP B ly S W mem md text _ HAR Htin) as Htimg. unfold off_img in Htimg.
(* the frame lies above the allocator's ceiling *)
assert (KS : forall x, x_sp0 cx - LTOI_STK <= x < x_sp0 cx -> rdW W mem' x = rdW W mem x)
  by (intros x Hx; apply HK; lia).
(* the program's statics lie in the image *)
assert (KI : forall x, 0x10000 <= x < 0x606000 -> rdW W mem' x = rdW W mem x)
  by (intros x Hx; apply HK; lia).
(* the recorder's blocks are apart from text *)
assert (KO : forall x, inFP (ablocks_fp (q_O1 q)) x -> rdW W mem' x = rdW W mem x).
{ intros x ((lo, hi) & Hin & Hx). unfold ablocks_fp in Hin. apply in_map_iff in Hin as ([p n] & Heq & Hpn).
  injection Heq as <- <-. cbn [fst snd] in Hx.
  destruct (in_split _ _ Hpn) as (O1 & O2 & EO).
  assert (Hd : zdisjoint (block_rng (p, n)) (block_rng (text, q_L0 cx q + 1))).
  { apply (sep_blocks_perm SEGS B LAWS ly S W mem md _ _
      (O1 ++ (O2 ++ x_bl0 B cx) ++ [(copy, q_L0 cx q + 1); (arr, SlotSpec.arr_size (q_L0 cx q))]) HAR).
    eapply perm_trans; [exact Hperm|]. rewrite EO.
    replace ((O1 ++ (p, n) :: O2) ++ x_bl0 B cx ++
        [(text, q_L0 cx q + 1); (copy, q_L0 cx q + 1); (arr, SlotSpec.arr_size (q_L0 cx q))])
      with (O1 ++ (p, n) :: (O2 ++ x_bl0 B cx) ++ (text, q_L0 cx q + 1) ::
        [(copy, q_L0 cx q + 1); (arr, SlotSpec.arr_size (q_L0 cx q))])
      by (rewrite <- !app_assoc; reflexivity).
    apply tl_perm2_loc. }
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  assert (Hpin : In (p, n) (ablocks B ly S))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hpn).
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hpin) as (_ & Hp4096 & Hpceil & _).
  apply HK; lia. }
assert (Hsp1 : x_sp1 cx = x_sp0 cx - 256) by (unfold x_sp1, x_sp0, LT_FRAME; lia).
assert (KW : forall o, 0 <= o <= 248 -> rdword (rdW W mem') (x_sp1 cx + o) = rdword (rdW W mem) (x_sp1 cx + o)).
{ intros o Ho. apply rdword_ext. intros kk Hk. apply KS. lia. }
unfold tl_ctx, aw_ctx, aw_ctx0.
split; [split; [|exact Hbud]|].
{ split; [exact HB|]. split.
  { split; [exact HJ'|]. split; [unfold spZ in *; rewrite K2; exact Hsp|].
    split; [rewrite K3; exact R3|]. split; [rewrite K4; exact R4|].
    intros i r Hi. assert (Hi13 : (i < 13)%nat).
    { assert (Hne : nth_error LT_SAVED i <> None) by congruence. apply nth_error_Some in Hne. exact Hne. }
    rewrite (rdword_ext (rdW W mem) (rdW W mem')); [exact (Hsv i r Hi)|].
    intros kk Hk. apply KS. lia. }
  split.
  { intros o v Hin.
    assert (Ho : 0 <= o <= 80).
    { unfold LT_SLOTS in Hin. repeat (destruct Hin as [Heq|Hin]; [injection Heq as <- _; lia|]). destruct Hin. }
    rewrite KW by lia. exact (HSl o v Hin). }
  split; [rewrite K8; exact R8|]. split; [rewrite K9; exact R9|]. split; [rewrite K22; exact R22|].
  split; [exact Hm|]. split; [exact Hn|]. split; [exact Hp|]. split; [exact Hr|].
  split; [unfold LT_HOSTB in *; rewrite KW by lia; exact Hh | unfold LT_STATEB in *; rewrite KW by lia; exact Hs]. }
split.
{ unfold aw_msgregs in *. destruct HMG as (M18 & M19 & M20 & M21 & M27).
  rewrite K18, K19, K20, K21, K27. tauto. }
split.
{ unfold aw_rec, lt_rec. split.
  - apply (rec_repA_kept B ly S (rdW W mem) ly S (rdW W mem') _ _ HRA).
    + intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hpn.
    + intros x [Hx|[Hx|Hx]];
        [apply KI; unfold A_G_REC, REC_SIZE in *; lia | apply KI; unfold A_REC_SPILL, SC_SIZE in *; lia | exact (KO x Hx)].
  - split; [exact Hsp0|]. split; [exact Hcl|].
    split; [apply (aval_mem_kept_r (rdW W mem));
      [intros x Hx; apply KI; change (Z.of_nat 4) with 4 in Hx; unfold A_G_QUITTING in Hx; lia | exact Hq]|].
    split; [exact Rq|]. rewrite aw_blocks_eq. exact Hperm. }
split.
{ unfold aw_wslots, LT_W in *. destruct Hws as (W1 & W2 & W3).
  replace (x_sp1 cx + 120 + 8) with (x_sp1 cx + 128) in * by lia.
  replace (x_sp1 cx + 120 + 16) with (x_sp1 cx + 136) in * by lia.
  rewrite (KW 120), (KW 128), (KW 136) by lia.
  split; [exact W1|]. split; [exact W2 | exact W3]. }
rewrite K24, K23, K25. tauto.
Qed.

(* the two ways out of a pass *)
Lemma tl_exit_J : forall m cx q ly S W regs mem md k acc text copy arr regs' mem' md' T,
  AW_J_stmt B MT m -> q_m q = m -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  tl_ctx cx q ly S W regs mem md k acc text copy arr ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem' md' k ->
  tl_regs_kept regs regs' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (text <= x < text + req_size (q_L0 cx q + 1)) -> rdW W mem' x = rdW W mem x) ->
  abytes_atR (rdW W mem') text T -> length T = Z.to_nat (q_L0 cx q + 1) ->
  firstn (length (q_LN cx q) + 1) T = q_LN cx q ++ [Z_to_bv 8 0] ->
  getr regs' 12 = w64 (Z.of_nat (length (q_LN cx q)) + 1) -> getr regs' 26 = w64 (Z.of_nat (length (q_LN cx q))) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + AW_J)) mem' (seg_rom SEGS)) md') (lt_post B MT cx).
Proof.
intros m cx q ly S W regs mem md k acc text copy arr regs' mem' md' T HJS Hm HFRM HC HJ HR HK HT1 HT2 HT3 R12 R26.
destruct (tl_ctx_kept cx q ly S W regs mem md k acc text copy arr regs' mem' md' HC HJ HR HK)
  as (HC' & HMG' & Hrec' & Hws' & R24' & R23' & R25').
exact (HJS cx q ly S W regs' mem' md' k acc text copy arr Hm HFRM HC' HMG' Hrec' Hws' R24' R23' R25'
  (ex_intro _ T (conj HT1 (conj HT2 HT3))) R12 R26).
Qed.
Lemma tl_exit_T : forall m j cx q ly S W regs mem md k acc text copy arr regs' mem' md',
  AW_T_stmt B MT m j -> q_m q = m -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  tl_ctx cx q ly S W regs mem md k acc text copy arr ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem' md' k ->
  tl_regs_kept regs regs' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (text <= x < text + req_size (q_L0 cx q + 1)) -> rdW W mem' x = rdW W mem x) ->
  (1 <= j <= length (q_U cx q))%nat ->
  Verbs.trim (q_U cx q) = Verbs.trim (firstn j (q_U cx q)) ->
  abytes_atR (rdW W mem') text (SlotWordsRun.tz (q_U cx q) j) ->
  getr regs' 10 = w64 (text + Z.of_nat j - 1) -> getr regs' 11 = w64 (text + Z.of_nat j - 1) ->
  getr regs' 26 = w64 (Z.of_nat j) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + AW_T)) mem' (seg_rom SEGS)) md') (lt_post B MT cx).
Proof.
intros m j cx q ly S W regs mem md k acc text copy arr regs' mem' md' HIH Hm HFRM HC HJ HR HK Hj HT Htz R10 R11 R26.
destruct (tl_ctx_kept cx q ly S W regs mem md k acc text copy arr regs' mem' md' HC HJ HR HK)
  as (HC' & HMG' & Hrec' & Hws' & R24' & R23' & R25').
exact (HIH cx q ly S W regs' mem' md' k acc text copy arr Hm HFRM HC' HMG' Hrec' Hws' R24' R23' R25' Hj HT Htz R10 R11 R26).
Qed.

(* the memory a run left, over the start of the pass: the byte at a is the only one it may change *)
Ltac tl_mem W mem a EA0 KK :=
  lazymatch goal with HFr : frame_of ?E ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    let rs' := eval vm_compute in rs in change rs with rs' in HFr;
    let K := fresh "K" in
    pose proof (tl_kept1 E _ (w_H W) m1 m2 a HFr ltac:(tl_ew0; rewrite EA0; apply unsigned_lit_small; lia)) as K;
    let KK2 := fresh "KK" in
    assert (KK2 : forall y, 0 <= y < 2 ^ 64 -> y <> a -> aview SEGS (w_H W) m2 y = aview SEGS (w_H W) mem y)
      by (intros y Hy Hne; rewrite (K y Hy Hne); exact (KK y Hy Hne));
    clear K KK HFr; rename KK2 into KK
  end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end.
Ltac tl_awr EA0 Htin Hnot0 :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc fr ly own)
  end;
  eapply tl_awr; [tl_ew0; rewrite EA0; apply unsigned_lit_small; lia | | | exact Htin | exact Hnot0]; lia.
Ltac tl_mdv name :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (name := d) in *; clearbody name end.

(* one pass: from 0x867a4 with j + 1 bytes left to 0x867a4 with j left, or out to 0x8680c *)
Lemma tl_step : forall m j, AW_J_stmt B MT m -> AW_T_stmt B MT m j -> AW_T_stmt B MT m (S j).
Proof.
intros m j HJS HIH cx q ly St W regs mem md k acc text copy arr Hm HFRM HC HMG Hrec Hws R24 R23 R25 Hj HT Htz R10 R11 R26.
pose proof (conj HC (conj HMG (conj Hrec (conj Hws (conj R24 (conj R23 R25)))))) as HCT.
change (tl_ctx cx q ly St W regs mem md k acc text copy arr) in HCT.
pose proof (q_L0_U cx q) as HL0.
pose proof HC as ((HB & (HJ & Hsp & G3 & G4 & Hsv) & HSl & R8 & R9 & R22 & _) & _).
pose proof (proj1 HJ) as HAR.
pose proof Hrec as (_ & _ & _ & _ & _ & Hperm). rewrite aw_blocks_eq in Hperm.
assert (Htin : In (text, q_L0 cx q + 1) (ablocks B ly St))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly St W mem md text _ HAR Htin) as (_ & Ht4096 & Htceil & Htapp & Htpres & _ & _).
pose proof (req_size_pos (q_L0 cx q + 1) ltac:(lia)) as [Hreq1 Hreq].
pose proof asan_consts as (C1 & _).
(* text is made since the entry: it is not one of the entry's blocks *)
assert (Hnot0 : ~ In (text, q_L0 cx q + 1) (ablocks B (x_ly cx) (x_S cx))).
{ intros Hin. destruct (in_split _ _ Hin) as (B1 & B2 & EB). unfold x_bl0 in Hperm. rewrite EB in Hperm.
  assert (Hd : zdisjoint (block_rng (text, q_L0 cx q + 1)) (block_rng (text, q_L0 cx q + 1))).
  { apply (sep_blocks_perm SEGS B LAWS ly St W mem md _ _
      ((q_O1 q ++ B1) ++ B2 ++ [(copy, q_L0 cx q + 1); (arr, SlotSpec.arr_size (q_L0 cx q))]) HAR).
    eapply perm_trans; [exact Hperm|].
    replace (q_O1 q ++ (B1 ++ (text, q_L0 cx q + 1) :: B2) ++
        [(text, q_L0 cx q + 1); (copy, q_L0 cx q + 1); (arr, SlotSpec.arr_size (q_L0 cx q))])
      with ((q_O1 q ++ B1) ++ (text, q_L0 cx q + 1) :: B2 ++ (text, q_L0 cx q + 1) ::
        [(copy, q_L0 cx q + 1); (arr, SlotSpec.arr_size (q_L0 cx q))])
      by (rewrite <- !app_assoc; reflexivity).
    apply tl_perm2_loc. }
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia. }
(* the byte of this pass *)
assert (HjU : (S j <= length (q_U cx q))%nat) by lia.
destruct (nth_error (q_U cx q) j) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
pose proof (bv_unsigned_in_range 8 x) as Rx. change (bv_modulus 8) with 256 in Rx.
remember (bv_unsigned x) as b eqn:Eb.
replace (text + Z.of_nat (S j) - 1) with (text + Z.of_nat j) in R10, R11 by lia.
assert (Hlen : length (SlotWordsRun.tz (q_U cx q) (S j)) = S (length (q_U cx q))) by (apply SlotWordsRun.tz_len; lia).
assert (Hrdb : rdW W mem (text + Z.of_nat j) = Some b).
{ rewrite (Htz j ltac:(rewrite Hlen; lia)). rewrite Eb. f_equal. f_equal. apply nth_error_nth.
  rewrite SlotWordsRun.tz_nth_lt by lia. exact Ex. }
assert (HV : aval_mem (rdW W mem) (text + Z.of_nat j) 1 b) by (apply tl_aval1; [lia | exact Hrdb]).
pose proof (proj1 (Htpres (text + Z.of_nat j) ltac:(lia))) as HP.
pose proof (tl_seed W regs mem (text + Z.of_nat j) (Z.of_nat (S j)) b R8 R9 R22 R10 R11 R26
  ltac:(lia) ltac:(lia) ltac:(lia) HV HP) as HS.
assert (RA : range_addressable (rdW W mem) SHADOW_OFF (text + Z.of_nat j) 1)
  by (apply (range_addressable_of_block SEGS B LAWS ly St W mem md text (q_L0 cx q + 1)); [exact HAR | exact Htin | lia | lia]).
assert (Hband : text + Z.of_nat j < SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= text + Z.of_nat j)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia).
pose proof (tl_shok W regs mem (text + Z.of_nat j) b R9 R10 ltac:(lia) RA Hband) as SHOK.
pose proof (Eimg_env (Ereg regs [Z_to_bv 64 b])) as HEI.
pose proof (tl_EE regs [Z_to_bv 64 b]) as EV.
pose proof (tl_E32 regs b) as E32.
remember (Eimg (Ereg regs [Z_to_bv 64 b])) as E0 eqn:HE0. clear HE0.
assert (EA0 : ew E0 10 = Z_to_bv 64 (text + Z.of_nat j)) by (rewrite (EV 10%nat 10%bv eq_refl); exact R10).
assert (EJ0 : ew E0 26 = Z_to_bv 64 (Z.of_nat (S j))) by (rewrite (EV 26%nat 26%bv eq_refl); exact R26).
assert (KK : forall y, 0 <= y < 2 ^ 64 -> y <> text + Z.of_nat j -> rdW W mem y = rdW W mem y) by reflexivity.
assert (Hblk : forall y, ~ (text <= y < text + req_size (q_L0 cx q + 1)) -> y <> text + Z.of_nat j) by lia.
clear HC HMG Hrec Hws HSl Hsv Hperm.
(* 0x867a4 .. 0x867b8: the check of the byte (the shadow entry), lbu, `bltu s0,a3` *)
paj_run_tok RUN HS HJ SHOK TBspan.
{ tl_awr EA0 Htin Hnot0. }
tl_mdv mdv1. tl_mem W mem (text + Z.of_nat j) EA0 KK.
psrr_branch_tok RUN BR HS SHOK TBspan.
- (* the byte is above 32: not trailing; the line is the first j + 1 bytes *)
  assert (Hgt : 32 < b).
  { rewrite branch_ltu_U, U_lit, (U_atom _ 32 b) in Hc by first [lia | (tl_ew0; exact E32)].
    apply Z.ltb_lt in Hc. exact Hc. }
  assert (Hnt : Verbs.is_trail x = false)
    by (rewrite SlotWords.sw_is_trail_z, <- Eb; apply SlotWords.sw_trail_big; exact Hgt).
  assert (ELN : q_LN cx q = firstn (S j) (q_U cx q))
    by (change (q_LN cx q) with (Verbs.trim (q_U cx q)); rewrite HT; exact (SlotWordsRun.sw_trim_line _ j x Ex Hnt)).
  (* 0x867bc .. 0x86808: a2 = s10 + 1, on to 0x8680c *)
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x328.
  { tl_awr EA0 Htin Hnot0. }
  tl_mdv mdv2. tl_mem W mem (text + Z.of_nat j) EA0 KK.
  pmkst HS.
  lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?mF) |- _ =>
    pose proof (tl_byte_now E ss mF (w_H W) (SOff 32 0) (text + Z.of_nat j) b HS eq_refl
      ltac:(tl_ew0; exact EA0) ltac:(lia)
      ltac:(rewrite (tl_den_atom _ 32 b 0) by (tl_ew0; exact E32); rewrite Z.add_0_r; reflexivity) ltac:(lia)) as HbF;
    pose proof (tl_keep_of E ss mF (w_H W) regs HS ltac:(tl_EV EV) R8 R22 ltac:(vm_compute; repeat split)) as HRK;
    tl_preg HS (12%bv : bv 5) Q12; tl_preg HS (26%bv : bv 5) Q26;
    rewrite (tl_den_atom _ 26 (Z.of_nat (S j)) 1) in Q12 by (tl_ew0; exact EJ0);
    rewrite (tl_den_atom _ 26 (Z.of_nat (S j)) 0) in Q26 by (tl_ew0; exact EJ0);
    assert (KA : forall y, 0 <= y < 2 ^ 64 -> rdW W (ms_mem mF) y = rdW W mem y)
      by (intros y Hy; destruct (Z.eq_dec y (text + Z.of_nat j)) as [->|Hne]; [rewrite HbF, Hrdb; reflexivity | exact (KK y Hy Hne)]);
    apply (tl_exit_J m cx q ly St W regs mem md k acc text copy arr (ms_regs mF) (ms_mem mF) _
      (SlotWordsRun.tz (q_U cx q) (S j)) HJS Hm HFRM HCT HJ HRK)
  end.
  + intros y Hy Hn. exact (KA y Hy).
  + apply (abytes_atR_kept_r (rdW W mem)); [intros y Hy; apply KA; rewrite Hlen in Hy; lia | exact Htz].
  + rewrite Hlen, HL0. lia.
  + rewrite ELN, firstn_length_le by lia. apply SlotWordsRun.tz_firstn. lia.
  + rewrite Q12, ELN, firstn_length_le by lia. reflexivity.
  + rewrite Q26, ELN, firstn_length_le by lia. unfold w64. f_equal; lia.
- (* the byte is 32 or below: its bit of the mask *)
  assert (Hle : b <= 32).
  { rewrite branch_ltu_U, U_lit, (U_atom _ 32 b) in Hc by first [lia | (tl_ew0; exact E32)].
    apply Z.ltb_ge in Hc. exact Hc. }
  clear Hc. paj_run_tok RUN HS HJ SHOK TBspan.
  { tl_awr EA0 Htin Hnot0. }
  tl_mdv mdv2. tl_mem W mem (text + Z.of_nat j) EA0 KK.
  psrr_branch_tok RUN BR HS SHOK TBspan.
  + (* the bit is 0: not trailing *)
    assert (Hnt : Verbs.is_trail x = false).
    { rewrite branch_eq_U, (tl_mask_U _ b), U_lit in Hc by first [lia | (tl_ew0; exact E32)].
      rewrite SlotWords.sw_is_trail_z, <- Eb. destruct (SlotWords.sw_trail_z b); cbn in Hc; [discriminate Hc | reflexivity]. }
    assert (ELN : q_LN cx q = firstn (S j) (q_U cx q))
      by (change (q_LN cx q) with (Verbs.trim (q_U cx q)); rewrite HT; exact (SlotWordsRun.sw_trim_line _ j x Ex Hnt)).
    paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x328.
    { tl_awr EA0 Htin Hnot0. }
    tl_mdv mdv3. tl_mem W mem (text + Z.of_nat j) EA0 KK.
    pmkst HS.
    lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?mF) |- _ =>
      pose proof (tl_byte_now E ss mF (w_H W) (SOff 32 0) (text + Z.of_nat j) b HS eq_refl
        ltac:(tl_ew0; exact EA0) ltac:(lia)
        ltac:(rewrite (tl_den_atom _ 32 b 0) by (tl_ew0; exact E32); rewrite Z.add_0_r; reflexivity) ltac:(lia)) as HbF;
      pose proof (tl_keep_of E ss mF (w_H W) regs HS ltac:(tl_EV EV) R8 R22 ltac:(vm_compute; repeat split)) as HRK;
      tl_preg HS (12%bv : bv 5) Q12; tl_preg HS (26%bv : bv 5) Q26;
      rewrite (tl_den_atom _ 26 (Z.of_nat (S j)) 1) in Q12 by (tl_ew0; exact EJ0);
      rewrite (tl_den_atom _ 26 (Z.of_nat (S j)) 0) in Q26 by (tl_ew0; exact EJ0);
      assert (KA : forall y, 0 <= y < 2 ^ 64 -> rdW W (ms_mem mF) y = rdW W mem y)
        by (intros y Hy; destruct (Z.eq_dec y (text + Z.of_nat j)) as [->|Hne]; [rewrite HbF, Hrdb; reflexivity | exact (KK y Hy Hne)]);
      apply (tl_exit_J m cx q ly St W regs mem md k acc text copy arr (ms_regs mF) (ms_mem mF) _
        (SlotWordsRun.tz (q_U cx q) (S j)) HJS Hm HFRM HCT HJ HRK)
    end.
    * intros y Hy Hn. exact (KA y Hy).
    * apply (abytes_atR_kept_r (rdW W mem)); [intros y Hy; apply KA; rewrite Hlen in Hy; lia | exact Htz].
    * rewrite Hlen, HL0. lia.
    * rewrite ELN, firstn_length_le by lia. apply SlotWordsRun.tz_firstn. lia.
    * rewrite Q12, ELN, firstn_length_le by lia. reflexivity.
    * rewrite Q26, ELN, firstn_length_le by lia. unfold w64. f_equal; lia.
  + (* the bit is 1: a trailing byte; zero it and go down *)
    assert (Htr : Verbs.is_trail x = true).
    { rewrite branch_eq_U, (tl_mask_U _ b), U_lit in Hc by first [lia | (tl_ew0; exact E32)].
      rewrite SlotWords.sw_is_trail_z, <- Eb. destruct (SlotWords.sw_trail_z b); cbn in Hc; [reflexivity | discriminate Hc]. }
    assert (HT' : Verbs.trim (q_U cx q) = Verbs.trim (firstn j (q_U cx q)))
      by (rewrite HT; exact (SlotWordsRun.sw_trim_step _ j x Ex Htr)).
    (* 0x867c8 .. 0x867e0: the check again (the shadow entry), the store, s10, a0, a1 down, `bnez s10` *)
    clear Hc. paj_run_tok RUN HS HJ SHOK TBspan.
    { tl_awr EA0 Htin Hnot0. }
    tl_mdv mdv3. tl_mem W mem (text + Z.of_nat j) EA0 KK.
    assert (Uj : forall E, ew E 26 = ew E0 26 -> U E (SOff 26 (-1)) = Z.of_nat j).
    { intros E HE. rewrite (U_atom_off E 26 (Z.of_nat (S j)) (-1)); [lia | rewrite HE; exact EJ0 | lia | lia]. }
    psrr_branch_tok RUN BR HS SHOK TBspan.
    * (* j <> 0: the next pass *)
      assert (Hj1 : (1 <= j)%nat).
      { rewrite branch_ne_U, Uj, U_lit in Hc by first [lia | (tl_ew0; reflexivity)].
        apply negb_true_iff, Z.eqb_neq in Hc. lia. }
      paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x2c0.
      { tl_awr EA0 Htin Hnot0. }
      tl_mdv mdv4. tl_mem W mem (text + Z.of_nat j) EA0 KK.
      pmkst HS.
      lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?mF) |- _ =>
        pose proof (tl_byte_now E ss mF (w_H W) (SLit 0) (text + Z.of_nat j) 0 HS eq_refl
          ltac:(tl_ew0; exact EA0) ltac:(lia) eq_refl ltac:(lia)) as HbF;
        pose proof (tl_keep_of E ss mF (w_H W) regs HS ltac:(tl_EV EV) R8 R22 ltac:(vm_compute; repeat split)) as HRK;
        tl_preg HS (10%bv : bv 5) Q10; tl_preg HS (11%bv : bv 5) Q11; tl_preg HS (26%bv : bv 5) Q26;
        rewrite (tl_den_atom _ 10 (text + Z.of_nat j) (-1)) in Q10 by (tl_ew0; exact EA0);
        rewrite (tl_den_atom _ 10 (text + Z.of_nat j) (-1)) in Q11 by (tl_ew0; exact EA0);
        rewrite (tl_den_atom _ 26 (Z.of_nat (S j)) (-1)) in Q26 by (tl_ew0; exact EJ0);
        apply (tl_exit_T m j cx q ly St W regs mem md k acc text copy arr (ms_regs mF) (ms_mem mF) _
          HIH Hm HFRM HCT HJ HRK);
        [ intros y Hy Hn; exact (KK y Hy (Hblk y Hn)) | lia | exact HT'
        | apply (tl_tz_store (rdW W mem) _ text (q_U cx q) j HjU ltac:(lia) ltac:(lia) Htz KK HbF)
        | rewrite Q10; unfold w64; f_equal; lia | rewrite Q11; unfold w64; f_equal; lia
        | rewrite Q26; unfold w64; f_equal; lia ]
      end.
    * (* j = 0: every byte was trailing; the line is empty *)
      assert (Hj0 : j = 0%nat).
      { rewrite branch_ne_U, Uj, U_lit in Hc by first [lia | (tl_ew0; reflexivity)].
        apply negb_false_iff, Z.eqb_eq in Hc. lia. }
      subst j.
      assert (ELN : q_LN cx q = []) by (change (q_LN cx q) with (Verbs.trim (q_U cx q)); rewrite HT'; reflexivity).
      paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x328.
      { tl_awr EA0 Htin Hnot0. }
      tl_mdv mdv4. tl_mem W mem (text + Z.of_nat 0) EA0 KK.
      pmkst HS.
      lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?mF) |- _ =>
        pose proof (tl_byte_now E ss mF (w_H W) (SLit 0) (text + Z.of_nat 0) 0 HS eq_refl
          ltac:(tl_ew0; exact EA0) ltac:(lia) eq_refl ltac:(lia)) as HbF;
        pose proof (tl_keep_of E ss mF (w_H W) regs HS ltac:(tl_EV EV) R8 R22 ltac:(vm_compute; repeat split)) as HRK;
        tl_preg HS (12%bv : bv 5) Q12; tl_preg HS (26%bv : bv 5) Q26;
        rewrite (tl_den_atom _ 26 (Z.of_nat 1) 0) in Q12 by (tl_ew0; exact EJ0);
        rewrite (tl_den_atom _ 26 (Z.of_nat 1) (-1)) in Q26 by (tl_ew0; exact EJ0);
        apply (tl_exit_J m cx q ly St W regs mem md k acc text copy arr (ms_regs mF) (ms_mem mF) _
          (SlotWordsRun.tz (q_U cx q) 0) HJS Hm HFRM HCT HJ HRK);
        [ intros y Hy Hn; exact (KK y Hy (Hblk y Hn))
        | apply (tl_tz_store (rdW W mem) _ text (q_U cx q) 0 HjU ltac:(lia) ltac:(lia) Htz KK HbF)
        | rewrite SlotWordsRun.tz_len, HL0 by lia; lia
        | rewrite ELN; apply (SlotWordsRun.tz_firstn _ 0); lia
        | rewrite Q12, ELN; reflexivity
        | rewrite Q26, ELN; reflexivity ]
      end.
Qed.

(* the trim loop: from its head with any j, by induction on j (the base j = 0 is outside the loop's premise) *)
Lemma aw_seg_Tloop : forall m, AW_J_stmt B MT m -> forall j, AW_T_stmt B MT m j.
Proof.
intros m HJS j. induction j as [|j IH].
- intros cx q ly S W regs mem md k acc text copy arr _ _ _ _ _ _ _ _ _ Hj. exfalso. lia.
- exact (tl_step m j HJS IH).
Qed.

End e.
End f.
End d.
