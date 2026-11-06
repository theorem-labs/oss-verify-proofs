(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the symbolic state of descriptors_panel_get's walk (plugin-hostd/fuzz_command.asan) at the point where the two arms of the inlined record() meet, and its seed, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_seed: the frame's saved registers as chunks, the object as a region) and lib/A/Prog/sup_reply_code_s1.v. *)

(* descriptors_panel_get (recorder.c:554-560, entry 0x8d10c, 91 instructions). The two arms of the inlined record()
   (the slot g_rec.calls[n], or record.spill after rec_calls_free) meet at 0x8d180 with s0 = the slot c, s1 = uri,
   s3 = the shadow base and the frame holding ra, s0 .. s4 of the entry. From there the walk is one path up to the
   call of xstrdup. This file gives that point's symbolic state: atoms 0 .. 31 are the registers at 0x8d180, atoms
   32 .. 37 the entry values of ra, s0, s1, s2, s3, s4 that the frame holds; the regions are the frame [sp, sp + 48)
   (read only, six 8-byte chunks) and the first 16 bytes of the slot (written: fn, nargs, args[0]); the one token
   entry covers those 16 bytes, whose shadow is 0 by the record's zero-shadow ranges of g_rec / record.spill. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the program's own writable statics: the kit's recb_PG (lib/A/Prog/RecBLemmas.v:33) is what CmdBSyms' ts_prog
   gives *)
Lemma dpg_PG_tfib : recb_PG = TFIB_PROG_STATIC.
Proof. reflexivity. Qed.
(* listing offsets (from BASE): the entry, the join of the two record() arms (0x8d180) *)
Definition DPG_FRAME : Z := 48.
Definition DPG_JOIN : Z := AF_descriptors_panel_get + 0x74.
(* the callee-saved registers the prologue stores, in the order of their slots below the entry sp: ra at sp0 - 8,
   s0 at sp0 - 16, .., s4 at sp0 - 48 *)
Definition dpg_saved : list Z := [1; 8; 9; 18; 19; 20].
Definition dpg_extra (regs : bvmap 5 word) : list word := map (fun r => getr regs (Z_to_bv 5 r)) dpg_saved.
(* the slot record() picks: g_rec.calls[n] while the table has room, record.spill once it holds 16 calls *)
Definition dpg_c (R : rstate) : Z :=
if Nat.ltb (length (r_calls R)) 16 then A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) else A_REC_SPILL.
Definition dpg_frame_r : YP09.region := YP09.mkRegion (Some 2%nat) 0 48 0 0
[YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0));
 YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 8 (CVal 8 (SOff 36 0)); YP09.mkChunk 0 (CVal 8 (SOff 37 0))].
Definition dpg_slot_r : YP09.region := YP09.mkRegion (Some 8%nat) 0 16 0 8 [].
(* the listing offsets of the call of xstrdup (0x8d1c0) and of its return (0x8d1c4) *)
Definition DPG_CALL_X : Z := AF_descriptors_panel_get + 0xb4.
Definition DPG_RET_X : Z := AF_descriptors_panel_get + 0xb8.
(* the state after xstrdup returns: s2 = the slot + 4 and s4 = its shadow byte's address, as the code computed them
   before the call; the slot's nargs word is 0 and the words nargs, args[0] are written next *)
Definition dpg_shx (o : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 o) (SLit 3)) (SOff 19 0).
Definition dpg_regsX : list sv := Eval vm_compute in sr_set (sr_set sr_atoms 18 (SOff 8 4)) 20 (dpg_shx 4).
Definition dpg_slotX_r : YP09.region := YP09.mkRegion (Some 8%nat) 0 16 4 16 [YP09.mkChunk 4 (CVal 4 (SLit 0))].
Definition dpg_jfacts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3); (19%nat, mkAF SB SB 0)] [] [].
Definition dpg_Bx : sv := SOff 19 0.
Definition dpg_SH : list shent := [mkSHE 8 0 16].
Definition ss_join : sstate := mkSS DPG_JOIN sr_atoms [dpg_frame_r; dpg_slot_r] None dpg_jfacts.
Definition ss_retx : sstate := mkSS DPG_RET_X dpg_regsX [dpg_frame_r; dpg_slotX_r] None dpg_jfacts.
(* the state after rec_shape_of returns (0x8d208): only the frame is read, by the epilogue's restores *)
Definition DPG_RET_R : Z := AF_descriptors_panel_get + 0xfc.
Definition dpg_tfacts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_tail : sstate := mkSS DPG_RET_R sr_atoms [dpg_frame_r] None dpg_tfacts.

Lemma dpg_c_ok : forall R, (length (r_calls R) <= 16)%nat ->
A_G_REC + OFF_CALLS <= dpg_c R /\ dpg_c R + 16 <= A_REC_SPILL + SC_SIZE /\ dpg_c R mod 8 = 0 /\
((dpg_c R + CALL_SIZE <= A_G_REC + REC_SIZE /\ dpg_c R + CALL_SIZE <= A_G_REC + OFF_ANSWER) \/ dpg_c R = A_REC_SPILL).
Proof.
intros R HL. unfold dpg_c. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [H|H].
- unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE, REC_SIZE, OFF_ANSWER.
  split; [lia|]. split; [lia|]. split; [|left; lia].
  match goal with |- ?e mod 8 = 0 =>
    replace e with ((771818 + 7 * Z.of_nat (length (r_calls R))) * 8) by lia end.
  apply Z_mod_mult.
- unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE. split; [lia|]. split; [lia|]. split; [reflexivity | right; reflexivity].
Qed.

(* a range of addresses outside every range of a list *)
Lemma dpg_not_in_ranges : forall (L : list (Z * Z)) lo hi,
forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo)) L = true ->
forall a, lo <= a < hi -> ~ Exists (in_zr a) L.
Proof.
intros L lo hi H a Ha HE. apply Exists_exists in HE as (r & Hr & Hin). rewrite forallb_forall in H.
specialize (H r Hr). unfold in_zr in Hin. apply orb_true_iff in H as [H|H]; apply Z.leb_le in H; lia.
Time Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* the bytes of g_rec, record.spill and "(null)" are outside the runtime's owned statics and the errno cell *)
Lemma dpg_unowned : forall a,
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/ 0x22480 <= a < 0x22480 + 7) ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB). unfold TFIB_ERRNO.
destruct Ha as [Ha | [Ha | Ha]]; unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; (split; [|lia]);
[ apply (dpg_not_in_ranges _ 0x5e3740 (0x5e3740 + 960)) | apply (dpg_not_in_ranges _ 0x5e3be0 (0x5e3be0 + 56))
| apply (dpg_not_in_ranges _ 0x22480 (0x22480 + 7)) ]; first [vm_compute; reflexivity | lia].
Time Qed.

(* the record's zero-shadow ranges that hold g_rec's call table and record.spill (AF0m.v Tfib_zero_shadow) *)
Lemma dpg_zsh_grec : In (0xada00, 0x5e3b00 - 0xada00) Tfib_zero_shadow.
Proof. unfold Tfib_zero_shadow. repeat (first [left; reflexivity | right]). Qed.
Lemma dpg_zsh_spill : In (0x5e3be0, 0x5e3c18 - 0x5e3be0) Tfib_zero_shadow.
Proof. unfold Tfib_zero_shadow. repeat (first [left; reflexivity | right]). Qed.

Lemma dpg_slot_addressable : forall ly S (W : world SEGS) mem md c,
AR SEGS B ly S W mem md -> A_G_REC + OFF_CALLS <= c -> c + 16 <= A_REC_SPILL + SC_SIZE ->
((c + CALL_SIZE <= A_G_REC + REC_SIZE) \/ c = A_REC_SPILL) ->
range_addressable (rdW W mem) SHADOW_OFF c 16.
Proof.
intros ly S W mem md c HAR H1 H2 [H3 | ->].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00) c 16 HAR dpg_zsh_grec);
  cbn [fst snd]; [reflexivity | reflexivity | unfold A_G_REC, OFF_CALLS in *; lia | unfold A_G_REC, REC_SIZE, CALL_SIZE in *; lia].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x5e3c18 - 0x5e3be0) A_REC_SPILL 16 HAR dpg_zsh_spill);
  cbn [fst snd]; [reflexivity | reflexivity | unfold A_REC_SPILL; lia | unfold A_REC_SPILL; lia].
Qed.

Lemma dpg_in_PG : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
Exists (in_zr a) recb_PG.
Proof.
intros a [Ha | Ha]; apply Exists_exists.
- exists (A_G_REC, REC_SIZE). split; [left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
- exists (A_REC_SPILL, SC_SIZE). split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
Qed.

Lemma dpg_slot_PG : forall c a, A_G_REC + OFF_CALLS <= c -> c + 16 <= A_REC_SPILL + SC_SIZE ->
((c + CALL_SIZE <= A_G_REC + REC_SIZE) \/ c = A_REC_SPILL) -> c <= a < c + 16 ->
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.
Proof.
intros c a H1 H2 [H3 | ->] Ha; unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE, A_REC_SPILL, SC_SIZE in *; lia.
Qed.

Lemma dpg_join_seed : forall ly S (W : world SEGS) mem md (regs1 regs : bvmap 5 word) c,
AR SEGS B ly S W mem md ->
2 ^ 46 <= spZ regs1 <= 2 ^ 47 - 48 -> spZ regs1 mod 16 = 0 ->
getr regs1 8 = w64 c -> A_G_REC + OFF_CALLS <= c -> c + 16 <= A_REC_SPILL + SC_SIZE -> c mod 8 = 0 ->
((c + CALL_SIZE <= A_G_REC + REC_SIZE) \/ c = A_REC_SPILL) ->
getr regs1 19 = w64 SB ->
(forall j r, nth_error dpg_saved j = Some r ->
 aval_mem (rdW W mem) (spZ regs1 + 40 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (dpg_extra regs))) ss_join
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + DPG_JOIN)) mem (seg_rom SEGS)))
/\ sh_ok SEGS dpg_Bx dpg_SH (Eimg (Ereg regs1 (dpg_extra regs))) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs1 regs c HAR Hsp Hsp16 H8 Hc1 Hc2 Hc8 Hc3 H19 HFR.
set (E := Eimg (Ereg regs1 (dpg_extra regs))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (dpg_extra regs) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : bv_unsigned (ew E 2) = spZ regs1) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E8 : ew E 8 = Z_to_bv 64 c) by (rewrite (EE 8%nat 8%bv eq_refl); exact H8).
assert (E19 : ew E 19 = Z_to_bv 64 SB) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
assert (Hcr : 0 <= c < 2 ^ 64) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *; lia).
assert (E8u : bv_unsigned (ew E 8) = c) by (rewrite E8; apply unsigned_lit_small; exact Hcr).
assert (E19u : bv_unsigned (ew E 19) = SB) by (rewrite E19; apply unsigned_lit_small; unfold SB; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_join. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold dpg_frame_r, dpg_slot_r.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      assert (HC : forall j off, (j < 6)%nat -> off = 40 - 8 * Z.of_nat j ->
        YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) (spZ regs1) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
      { intros j off Hj ->.
        destruct (nth_error dpg_saved j) as [r|] eqn:Hr; [|apply nth_error_None in Hr; cbn in Hr; lia].
        apply (chunk_ok_val SEGS E _ (spZ regs1) (40 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
        - cbn [sv_denot]. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned, (EX j ltac:(lia)).
          assert (Hx : nth_error (dpg_extra regs) j = Some (getr regs (Z_to_bv 5 r)))
            by (unfold dpg_extra; rewrite nth_error_map, Hr; reflexivity).
          rewrite (nth_error_nth _ _ _ Hx). reflexivity.
        - pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR.
          change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HR.
        - cbn. lia.
        - change (N.to_nat 8) with 8%nat. replace (spZ regs1 + (40 - 8 * Z.of_nat j)) with (spZ regs1 + 40 - 8 * Z.of_nat j) by lia.
          apply (val_mem_view SEGS). exact (HFR j r Hr). }
      apply Forall_cons; [exact (HC 0%nat 40 ltac:(lia) eq_refl)|].
      apply Forall_cons; [exact (HC 1%nat 32 ltac:(lia) eq_refl)|].
      apply Forall_cons; [exact (HC 2%nat 24 ltac:(lia) eq_refl)|].
      apply Forall_cons; [exact (HC 3%nat 16 ltac:(lia) eq_refl)|].
      apply Forall_cons; [exact (HC 4%nat 8 ltac:(lia) eq_refl)|].
      apply Forall_cons; [exact (HC 5%nat 0 ltac:(lia) eq_refl)|].
      apply Forall_nil.
    * rewrite E8u. unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in Hc1, Hc2.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|].
      apply dpg_in_PG. apply (dpg_slot_PG c); [exact Hc1 | exact Hc2 | exact Hc3 | lia].
  + apply pairwise_disjoint_of_extents. unfold dpg_frame_r, dpg_slot_r, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E8u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *. repeat split; lia.
  + unfold facts_ok, dpg_jfacts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I].
    split; [|split; [|split; [|exact I]]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    * rewrite E2. change (2 ^ 4) with 16. split; [lia|]. split; [exact Hsp16 | lia].
    * rewrite E8u. change (2 ^ 3) with 8.
      split; [destruct Hc3 as [Hc3 | ->]; unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE, REC_SIZE in *; lia|].
      split; [exact Hc8 | lia].
    * rewrite E19u. rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
- unfold sh_ok, dpg_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) mem E dpg_Bx 8 c 16 c 0 16).
  + exact (dpg_slot_addressable ly S W mem md c HAR Hc1 Hc2 Hc3).
  + unfold dpg_Bx. rewrite (U_atom E 19 SB E19) by (unfold SB; lia). reflexivity.
  + exact (U_atom E 8 c E8 Hcr).
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF.
    unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *. lia.
Qed.

Lemma dpg_retx_seed : forall ly S (W : world SEGS) mem md (regs1 regs : bvmap 5 word) c,
AR SEGS B ly S W mem md ->
2 ^ 46 <= spZ regs1 <= 2 ^ 47 - 48 -> spZ regs1 mod 16 = 0 ->
getr regs1 8 = w64 c -> A_G_REC + OFF_CALLS <= c -> c + 16 <= A_REC_SPILL + SC_SIZE -> c mod 8 = 0 ->
((c + CALL_SIZE <= A_G_REC + REC_SIZE) \/ c = A_REC_SPILL) ->
getr regs1 19 = w64 SB -> getr regs1 18 = w64 (c + 4) -> getr regs1 20 = w64 (SB + (c + 4) / 8) ->
(forall j r, nth_error dpg_saved j = Some r ->
 aval_mem (rdW W mem) (spZ regs1 + 40 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
aval_mem (rdW W mem) (c + 4) 4 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (dpg_extra regs))) ss_retx
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + DPG_RET_X)) mem (seg_rom SEGS)))
/\ sh_ok SEGS dpg_Bx dpg_SH (Eimg (Ereg regs1 (dpg_extra regs))) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs1 regs c HAR Hsp Hsp16 H8 Hc1 Hc2 Hc8 Hc3 H19 H18 H20 HFR HNA.
destruct (dpg_join_seed ly S W mem md regs1 regs c HAR Hsp Hsp16 H8 Hc1 Hc2 Hc8 Hc3 H19 HFR) as [HJS SHOK].
split; [|exact SHOK].
set (E := Eimg (Ereg regs1 (dpg_extra regs))) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E8 : ew E 8 = Z_to_bv 64 c) by (rewrite (EE 8%nat 8%bv eq_refl); exact H8).
assert (E19 : ew E 19 = Z_to_bv 64 SB) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
assert (Hcr : 0 <= c < 2 ^ 64) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *; lia).
assert (E8u : bv_unsigned (ew E 8) = c) by (rewrite E8; apply unsigned_lit_small; exact Hcr).
rewrite restrict_mkst_fx in HJS |- *. unfold ss_join, ss_retx in *.
pose proof HJS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8' & H9).
unfold st_ok_pi, abs_ss, setpc, st_ok in *.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
  ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts resv_denot] in *.
repeat (split; [first [assumption | reflexivity] |]).
split.
- apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [<- | Hr];
   [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) =>
       let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
     first [ rewrite (denot_shx E 8 19 4 c SB E8 E19) by (unfold SB, A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *; lia);
             exact H20
           | cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
             first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
                   | rewrite E8u; exact H18 ] ]
   | ]); try (destruct Hr; fail).
- split; [|exact H9].
  destruct H8' as (Hwf & Hrs & Hpd). split; [vm_compute; reflexivity|].
  split; [| exact Hpd].
  pose proof (Forall_inv Hrs) as Hr0. pose proof (Forall_inv (Forall_inv_tail Hrs)) as Hr1.
  pose proof (Forall_inv_tail (Forall_inv_tail Hrs)) as Hrs2.
  apply Forall_cons; [exact Hr0|]. apply Forall_cons; [|exact Hrs2].
  unfold region_ok, dpg_slotX_r, dpg_slot_r in *.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in Hr1 |- *.
  rewrite E8u in Hr1 |- *. destruct Hr1 as (B1 & B2 & B3 & _).
  split; [exact B1|]. split; [exact B2|]. split.
  + intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|].
    apply dpg_in_PG. apply (dpg_slot_PG c); [exact Hc1 | exact Hc2 | exact Hc3 | lia].
  + apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ c 4 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H W) mem (c + 4) 4 0 HNA).
Qed.

Lemma dpg_tail_seed : forall (W : world SEGS) mem (regs1 regs : bvmap 5 word),
2 ^ 46 <= spZ regs1 <= 2 ^ 47 - 48 -> spZ regs1 mod 16 = 0 ->
(forall j r, nth_error dpg_saved j = Some r ->
 aval_mem (rdW W mem) (spZ regs1 + 40 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (dpg_extra regs))) ss_tail
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + DPG_RET_R)) mem (seg_rom SEGS)))
/\ sh_ok SEGS dpg_Bx [] (Eimg (Ereg regs1 (dpg_extra regs))) (mrestrict (w_H W) mem).
Proof.
intros W mem regs1 regs Hsp Hsp16 HFR.
set (E := Eimg (Ereg regs1 (dpg_extra regs))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (dpg_extra regs) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : bv_unsigned (ew E 2) = spZ regs1) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold ss_tail. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dpg_frame_r. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  assert (HC : forall j off, (j < 6)%nat -> off = 40 - 8 * Z.of_nat j ->
    YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) (spZ regs1) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
  { intros j off Hj ->.
    destruct (nth_error dpg_saved j) as [r|] eqn:Hr; [|apply nth_error_None in Hr; cbn in Hr; lia].
    apply (chunk_ok_val SEGS E _ (spZ regs1) (40 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
    - cbn [sv_denot]. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned, (EX j ltac:(lia)).
      assert (Hx : nth_error (dpg_extra regs) j = Some (getr regs (Z_to_bv 5 r)))
        by (unfold dpg_extra; rewrite nth_error_map, Hr; reflexivity).
      rewrite (nth_error_nth _ _ _ Hx). reflexivity.
    - pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR.
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HR.
    - cbn. lia.
    - change (N.to_nat 8) with 8%nat. replace (spZ regs1 + (40 - 8 * Z.of_nat j)) with (spZ regs1 + 40 - 8 * Z.of_nat j) by lia.
      apply (val_mem_view SEGS). exact (HFR j r Hr). }
  apply Forall_cons; [exact (HC 0%nat 40 ltac:(lia) eq_refl)|].
  apply Forall_cons; [exact (HC 1%nat 32 ltac:(lia) eq_refl)|].
  apply Forall_cons; [exact (HC 2%nat 24 ltac:(lia) eq_refl)|].
  apply Forall_cons; [exact (HC 3%nat 16 ltac:(lia) eq_refl)|].
  apply Forall_cons; [exact (HC 4%nat 8 ltac:(lia) eq_refl)|].
  apply Forall_cons; [exact (HC 5%nat 0 ltac:(lia) eq_refl)|].
  apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- unfold facts_ok, dpg_tfacts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|exact I]. unfold afact_ok; cbn [af_lo af_hi af_al2].
  rewrite E2. change (2 ^ 4) with 16. split; [lia|]. split; [exact Hsp16 | lia].
Qed.

End e.
End f.
End d.
