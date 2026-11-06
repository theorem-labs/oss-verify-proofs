(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the symbolic state of descriptors_get's ASan walk (plugin-hostd/fuzz_command) at
   the join of record()'s two arms, after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_seedX: a walk segment's
   symbolic state built from the facts of a concrete one) over fuzz_command's listing. *)

(* descriptors_get (recorder.c:546-552, entry 0x8cfa0) at 0x8d014, where the inlined record()'s two arms meet:
   sp = the entry sp - 48, s0 = the slot c of the call, s1 = the argument uri, s3 = the shadow base; the frame holds
   the caller's ra, s0 .. s4. The symbolic state takes every register as its own atom and the six saved values as
   atoms 32 .. 37, two regions (the frame, the slot's 56 bytes) and one shadow entry: the slot lies in g_rec or
   record.spill, whose shadow the allocator record keeps at zero (lib/A/Prog/CmdZsh.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import descriptors_get_s1 RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the join of record()'s two arms (0x8d014) *)
Definition DG_J : Z := AF_descriptors_get + 0x74.
(* the registers the prologue saves, in the order of their slots from the top of the 48-byte frame:
   ra at sp0 - 8, s0 at sp0 - 16, s1, s2, s3, s4 at sp0 - 48 *)
Definition dg_saved : list Z := [1; 8; 9; 18; 19; 20].
Definition dg_extra (regs : bvmap 5 word) : list word := map (fun r => getr regs (Z_to_bv 5 r)) dg_saved.
(* the frame, relative to the join's sp (atom 2): the six saved values; the walk from the join only reads it *)
Definition dg_frame : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 48 0 0
[YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0));
 YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 8 (CVal 8 (SOff 36 0)); YP09.mkChunk 0 (CVal 8 (SOff 37 0))].
(* the first 16 bytes of the call's slot (atom 8, the register s0: g_rec.calls[n] or record.spill), which the walk
   writes: fn, nargs and args[0] *)
Definition dg_slot : YP09.region := YP09.mkRegion (Some 8%nat) 0 16 0 16 [].
Definition dg_regions : smem := [dg_frame; dg_slot].
(* sp in the stack band, the slot between g_rec's table and record.spill, s3 the shadow base; for a non-null
   argument, s1 is not 0 *)
Definition dg_atoms : list (nat * afact) :=
[(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3); (19%nat, mkAF SB SB 0)].
Definition dg_facts (nz : bool) : facts :=
mkFacts (if nz then dg_atoms ++ [(9%nat, mkAF 1 (2 ^ 64 - 1) 0)] else dg_atoms) [] [].
(* s1 as a literal 0 for a null argument *)
Definition dg_sregs (nz : bool) : list sv := if nz then sr_atoms else sr_set sr_atoms 9 (SLit 0).
Definition ss_dgJ (nz : bool) : sstate := mkSS DG_J (dg_sregs nz) dg_regions None (dg_facts nz).
Definition dg_Bx : sv := SOff 19 0.
Definition dg_SH : list shent := [mkSHE 8 0 CALL_SIZE].
Definition dg_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the caller's saved registers at the frame's slots *)
Definition dg_frame_ok (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error dg_saved j = Some r -> aval_mem rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* the registers at the join (ra is not among them: the spill arm's call of rec_calls_free sets it, and the walk
   from the join reloads it from the frame) *)
Definition dg_regs_ok (regs regs1 : bvmap 5 word) (c pu : Z) : Prop :=
getr regs1 2 = w64 (spZ regs - 48) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 8 = w64 c /\ getr regs1 9 = w64 pu /\ getr regs1 19 = w64 SB /\
(forall r, (r = 18 \/ 20 <= r <= 27) -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
(* the slot the call records: an entry of g_rec's table, or record.spill *)
Definition dg_slot_ok (c : Z) : Prop :=
(A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + OFF_ANSWER /\ c mod 8 = 0) \/ c = A_REC_SPILL.

Lemma dg_slot_bounds : forall c, dg_slot_ok c -> A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0.
Proof.
intros c [(H1 & H2 & H3) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *;
[split; [lia | exact H3] | split; [lia | reflexivity]].
Qed.

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
(* a shared recorder-walk hypothesis: the program's statics are bytes the allocator record keeps present *)
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

Lemma dg_in_PG : forall c a, dg_slot_ok c -> c <= a < c + CALL_SIZE -> Exists (in_zr a) recb_PG.
Proof.
intros c a Hc Ha. unfold recb_PG. apply Exists_exists.
destruct Hc as [(H1 & H2 & _) | ->].
- exists (A_G_REC, REC_SIZE). split; [left; reflexivity | unfold in_zr; cbn [fst snd]].
  unfold A_G_REC, REC_SIZE, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *. lia.
- exists (A_REC_SPILL, SC_SIZE). split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]].
  unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
Qed.

(* the slot's 56 bytes are marked usable: they lie in g_rec's or record.spill's range of the record's zero
   shadow (lib/A/AF0m.v Tfib_zero_shadow) *)
Lemma dg_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> dg_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR Hc. destruct Hc as [(H1 & H2 & _) | ->].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00) c CALL_SIZE HAR);
  [vm_compute; tauto | reflexivity | reflexivity | cbn [fst snd]; unfold A_G_REC, OFF_CALLS in H1; lia
  | cbn [fst snd]; unfold A_G_REC, OFF_ANSWER in H2; lia].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x5e3c18 - 0x5e3be0) A_REC_SPILL CALL_SIZE HAR);
  [vm_compute; tauto | reflexivity | reflexivity | cbn [fst snd]; unfold A_REC_SPILL; lia
  | cbn [fst snd]; unfold A_REC_SPILL, CALL_SIZE; lia].
Qed.

Lemma dg_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.

Lemma dg_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

(* the symbolic state at the join, from the facts of the concrete one (every register its own atom) *)
Lemma dg_seedJ0 : forall ly S (W : world SEGS) mem md regs (regs1 : bvmap 5 word) sp0 c pu (nz : bool),
AR SEGS B ly S W mem md ->
2 ^ 46 + 48 <= sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
(forall a, sp0 - 48 <= a < sp0 -> apresent (w_H W) mem a) ->
getr regs1 2 = w64 (sp0 - 48) -> getr regs1 8 = w64 c -> getr regs1 9 = w64 pu -> getr regs1 19 = w64 SB ->
dg_slot_ok c -> (nz = true -> pu <> 0) -> 0 <= pu < 2 ^ 64 ->
dg_frame_ok (rdW W mem) sp0 regs ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (dg_extra regs))) (mkSS DG_J sr_atoms dg_regions None (dg_facts nz))
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + DG_J)) mem (seg_rom SEGS)))
/\ sh_ok SEGS dg_Bx dg_SH (Eimg (Ereg regs1 (dg_extra regs))) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs regs1 sp0 c pu nz HAR Hsp Hsp16 Hpres R2 R8 R9 R19 Hc Hnz Hpu HFR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (dg_slot_bounds c Hc) as [Hcb Hc8].
set (E := Eimg (Ereg regs1 (dg_extra regs))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (dg_extra regs) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 48)) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E8 : ew E 8 = Z_to_bv 64 c) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 pu) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E19 : ew E 19 = Z_to_bv 64 SB) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (U2 : bv_unsigned (ew E 2) = sp0 - 48) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = c) by (rewrite E8; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (USB : SB = 0x7fff8000) by reflexivity.
assert (HSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold dg_regions, dg_frame, dg_slot. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
    unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U2. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
      assert (CH : forall j r off, nth_error dg_saved j = Some r -> off = 40 - 8 * Z.of_nat j ->
        YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) (sp0 - 48) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
      { intros j r off Hj Hoff.
        assert (Hj6 : (j < 6)%nat) by (change 6%nat with (length dg_saved); apply nth_error_Some; rewrite Hj; discriminate).
        apply (chunk_ok_val SEGS E _ (sp0 - 48) off 8 (SOff (32 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
        - cbn [sv_denot]. rewrite (EX j Hj6), Z.add_0_r, Z_to_bv_bv_unsigned.
          unfold dg_extra.
          erewrite nth_error_nth; [|exact (@map_nth_error Z word (fun r0 : Z => getr regs (Z_to_bv 5 r0)) j dg_saved r Hj)].
          rewrite Z_to_bv_bv_unsigned. reflexivity.
        - pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
          cbn. lia.
        - cbn. lia.
        - replace (sp0 - 48 + off) with (sp0 - 8 - 8 * Z.of_nat j) by lia.
          exact (val_mem_view SEGS (w_H W) mem _ 8 _ (HFR j r Hj)). }
      repeat apply Forall_cons; try apply Forall_nil.
      { exact (CH 0%nat 1 40 eq_refl eq_refl). } { exact (CH 1%nat 8 32 eq_refl eq_refl). }
      { exact (CH 2%nat 9 24 eq_refl eq_refl). } { exact (CH 3%nat 18 16 eq_refl eq_refl). }
      { exact (CH 4%nat 19 8 eq_refl eq_refl). } { exact (CH 5%nat 20 0 eq_refl eq_refl). }
    * rewrite U8. split; [unfold A_G_REC, OFF_CALLS in *; lia|].
      split; [unfold CALL_SIZE, A_REC_SPILL in *; lia|]. split; [|constructor].
      intros o Ho. apply (cmd_prog_writable ly S W mem md _ HAR). apply (dg_in_PG c); [exact Hc | unfold CALL_SIZE; lia].
  + apply pairwise_disjoint_of_extents. unfold dg_regions, dg_frame, dg_slot, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold CALL_SIZE, A_G_REC, A_REC_SPILL, OFF_CALLS in *. repeat split; lia.
  + unfold facts_ok, dg_facts, dg_atoms. destruct nz; cbn [app f_atoms f_conds f_alias atoms_ok conds_ok alias_ok];
    (split; [|split; [exact I | exact I]]).
    * split; [|split; [|split; [|split; [|exact I]]]].
      -- apply (dg_afact E 2%nat (sp0 - 48)); [exact E2 | lia | lia | change (2 ^ 4) with 16; rewrite Zminus_mod, Hsp16; reflexivity | lia].
      -- apply (dg_afact E 8%nat c); [exact E8 | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia | exact Hcb | change (2 ^ 3) with 8; exact Hc8 | lia].
      -- apply (dg_afact E 19%nat SB); [exact E19 | rewrite USB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      -- apply (dg_afact E 9%nat pu); [exact E9 | lia | specialize (Hnz eq_refl); lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
    * split; [|split; [|split; [|exact I]]].
      -- apply (dg_afact E 2%nat (sp0 - 48)); [exact E2 | lia | lia | change (2 ^ 4) with 16; rewrite Zminus_mod, Hsp16; reflexivity | lia].
      -- apply (dg_afact E 8%nat c); [exact E8 | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia | exact Hcb | change (2 ^ 3) with 8; exact Hc8 | lia].
      -- apply (dg_afact E 19%nat SB); [exact E19 | rewrite USB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
- unfold sh_ok, dg_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E dg_Bx 8%nat c CALL_SIZE c 0 CALL_SIZE).
  + exact (dg_slot_addressable ly S W mem md c HAR Hc).
  + unfold dg_Bx. rewrite (dg_U_atom E 19%nat SB E19) by (rewrite USB; lia). rewrite USB, HSO. reflexivity.
  + apply dg_U_atom; [exact E8 | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia].
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. rewrite HSO.
    unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

(* the same with s1 a literal 0 when the argument is null *)
Lemma dg_seedJ : forall ly S (W : world SEGS) mem md regs (regs1 : bvmap 5 word) sp0 c pu (nz : bool),
AR SEGS B ly S W mem md ->
2 ^ 46 + 48 <= sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
(forall a, sp0 - 48 <= a < sp0 -> apresent (w_H W) mem a) ->
getr regs1 2 = w64 (sp0 - 48) -> getr regs1 8 = w64 c -> getr regs1 9 = w64 pu -> getr regs1 19 = w64 SB ->
dg_slot_ok c -> (if nz then pu <> 0 else pu = 0) -> 0 <= pu < 2 ^ 64 ->
dg_frame_ok (rdW W mem) sp0 regs ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (dg_extra regs))) (ss_dgJ nz)
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + DG_J)) mem (seg_rom SEGS)))
/\ sh_ok SEGS dg_Bx dg_SH (Eimg (Ereg regs1 (dg_extra regs))) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs regs1 sp0 c pu nz HAR Hsp Hsp16 Hpres R2 R8 R9 R19 Hc Hnz Hpu HFR.
destruct (dg_seedJ0 ly S W mem md regs regs1 sp0 c pu nz HAR Hsp Hsp16 Hpres R2 R8 R9 R19 Hc
  ltac:(intros ->; exact Hnz) Hpu HFR) as [HS SHOK].
split; [|exact SHOK]. destruct nz; [exact HS|].
pose proof (st_ok_pi_pin_reg' _ _ _ (9%bv : bv 5) 0 HS) as HS'.
unfold ss_dgJ, dg_sregs. apply HS'; [|reflexivity].
cbn [restrict ms_regs mkst]. rewrite R9, Hnz. reflexivity.
Qed.

End e.
End f.
End d.
