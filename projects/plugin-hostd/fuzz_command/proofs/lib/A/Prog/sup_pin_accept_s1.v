(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the symbolic state of sup_pin_accept's ASan walk (plugin-hostd/fuzz_command) at
   the end of its inlined record(), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_seed: a mid-function state
   rebuilt from concrete facts, the frame's saved registers as chunks) over fuzz_command's listing. *)

(* sup_pin_accept (recorder.c:428-434, entry 0x8bb90, 91 instructions) is block P of
   the recorder-call walk plan template (prologue and the inlined record(13) with its two slot checks), then block S
   (arg_s of uri: xstrdup and its two checks) and the tail TA ("pin_accept", 10, 1). This file holds the state at
   the meeting point of P and S, JOIN = 0x8bc34 (just after `sw zero,4(s0)`): s0 = the slot c, s1 = uri,
   s2 = c + 4, s3 = the shadow base, s4 = the shadow byte address of c + 4, sp = the entry sp - 48, and the frame
   holding the entry's ra, s0 .. s4. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the offsets of the walk's points in the listing *)
Definition SPA_FRAME : Z := 48.
Definition SPA_JOIN : Z := AF_sup_pin_accept + 0xa4.   (* bnez s1 (0x8bc34) *)
Definition SPA_XRET : Z := AF_sup_pin_accept + 0xb8.   (* after the call of xstrdup (0x8bc48) *)
Definition SPA_SRET : Z := AF_sup_pin_accept + 0xfc.   (* after the call of rec_shape_of (0x8bc8c) *)
(* the atoms the join state adds above the 32 registers: the shadow base, the slot, and the entry's values of the
   six registers the frame holds *)
Definition SA_SB : nat := 32.
Definition SA_C : nat := 33.
Definition spa_saved : list Z := [1; 8; 9; 18; 19; 20].
Definition spa_extra (regs : bvmap 5 word) (c : Z) : list word :=
map (Z_to_bv 64) [SB; c] ++ map (fun r => getr regs (Z_to_bv 5 r)) spa_saved.
Definition spa_Bx : sv := SOff SA_SB 0.
Definition spa_SH : list shent := [mkSHE SA_C 0 CALL_SIZE].
Definition spa_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition spa_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (SA_SB, mkAF SB SB 0); (SA_C, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3)] [] [].
(* the frame at the join: [sp, sp + 48) above the join sp (atom 2), read only from here on, its six words the entry's
   ra, s0, s1, s2, s3, s4 (atoms 34 .. 39) *)
Definition spa_stack : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 SPA_FRAME 0 0
  [YP09.mkChunk 40 (CVal 8 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0));
   YP09.mkChunk 16 (CVal 8 (SOff 37 0)); YP09.mkChunk 8 (CVal 8 (SOff 38 0)); YP09.mkChunk 0 (CVal 8 (SOff 39 0))].
(* the slot record() picked (a g_rec.calls entry or record.spill), its nargs field 0; writable only in the bytes
   arg_s stores, nargs and args[0] *)
Definition spa_slot : YP09.region :=
YP09.mkRegion (Some SA_C) 0 CALL_SIZE CALL_OFF_NARGS (CALL_OFF_ARGS + 8) [YP09.mkChunk CALL_OFF_NARGS (CVal 4 (SLit 0))].
Definition spa_rs : smem := [spa_stack; spa_slot].
(* the shadow byte address of x, as the instrumentation computes it *)
Definition spa_shx (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) spa_Bx.
Definition spa_jregs : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set sr_atoms 8 (SOff SA_C 0)) 18 (SOff SA_C 4)) 19 spa_Bx) 20 (spa_shx (SOff SA_C 4)).
Definition ss_at (pc : Z) : sstate := mkSS pc spa_jregs spa_rs None spa_facts.
Definition SPA_B0 : Z := AF_sup_pin_accept + 0xb0.   (* mv a0,s1 before the call of xstrdup (0x8bc40) *)

(* the slot record() picked *)
Definition spa_slot_ok (c : Z) : Prop :=
(A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + REC_SIZE /\ c mod 8 = 0) \/ c = A_REC_SPILL.
Lemma spa_slot_bounds : forall c, spa_slot_ok c ->
A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0 /\ c + CALL_SIZE <= A_REC_SPILL + SC_SIZE.
Proof.
intros c [(H1 & H2 & H3) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, CALL_SIZE, SC_SIZE in *;
[split; [lia | split; [exact H3 | lia]] | split; [lia | split; [reflexivity | lia]]].
Qed.
(* the record's zero-shadow ranges that hold g_rec and record.spill (AF0m.v Tfib_zero_shadow) *)
Lemma spa_In_pair : forall (a b : Z) (l : list (Z * Z)), existsb (fun r => (fst r =? a) && (snd r =? b)) l = true -> In (a, b) l.
Proof.
intros a b l H. apply existsb_exists in H as ([x y] & Hin & E). cbn [fst snd] in E.
apply andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst. exact Hin.
Qed.
Lemma spa_zsh_grec : In (0xada00, 0x5e3b00 - 0xada00) Tfib_zero_shadow.
Proof. apply spa_In_pair. vm_compute. reflexivity. Qed.
Lemma spa_zsh_spill : In (0x5e3be0, 0x5e3c18 - 0x5e3be0) Tfib_zero_shadow.
Proof. apply spa_In_pair. vm_compute. reflexivity. Qed.

(* the 8-byte word of a string's terminator e lies in a range of whole words exactly when e does *)
Lemma spa_word_in : forall lo len e a, lo mod 8 = 0 -> len mod 8 = 0 ->
e < a < e - e mod 8 + 8 -> lo <= a < lo + len -> lo <= e < lo + len.
Proof.
intros lo len e a Hlo Hlen Ha Hin.
pose proof (Z.div_mod e 8 ltac:(lia)) as De. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Me.
pose proof (Z.div_mod lo 8 ltac:(lia)) as Dl. pose proof (Z.div_mod len 8 ltac:(lia)) as Dn.
rewrite Hlo in Dl. rewrite Hlen in Dn. nia.
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
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis HB : CmdBSyms B.
(* the walks' shared program-static facts (RecBTemplate.v's forms) *)
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.

Lemma spa_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> spa_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR Hc. destruct Hc as [(H1 & H2 & _) | ->].
- exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md _ c CALL_SIZE HAR spa_zsh_grec ltac:(reflexivity) ltac:(reflexivity)
    ltac:(cbn [fst]; unfold A_G_REC, OFF_CALLS in H1; lia) ltac:(cbn [fst snd]; unfold A_G_REC, REC_SIZE in H2; lia)).
- exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md _ A_REC_SPILL CALL_SIZE HAR spa_zsh_spill ltac:(reflexivity)
    ltac:(reflexivity) ltac:(cbn [fst]; unfold A_REC_SPILL; lia) ltac:(cbn [fst snd]; unfold A_REC_SPILL, CALL_SIZE; lia)).
Qed.

Lemma spa_in_PG : forall c a, spa_slot_ok c -> c <= a < c + CALL_SIZE -> Exists (in_zr a) recb_PG.
Proof.
intros c a Hc Ha. apply Exists_exists. destruct Hc as [(H1 & H2 & _) | ->].
- exists (A_G_REC, REC_SIZE). split; [left; reflexivity | unfold in_zr; cbn [fst snd]].
  unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *. lia.
- exists (A_REC_SPILL, SC_SIZE). split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]].
  unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.

(* the state at JOIN (and at B0, where both arms of `bnez s1` meet), rebuilt from concrete facts: the registers, the
   frame's six words and the slot's nargs field *)
Lemma spa_join_seed : forall pc ly S (W : world SEGS) mem md (regs regs1 : bvmap 5 word) c sp0,
AR SEGS B ly S W mem md ->
2 ^ 46 <= sp0 - SPA_FRAME -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 -> spa_slot_ok c ->
spZ regs1 = sp0 - SPA_FRAME ->
getr regs1 8 = w64 c -> getr regs1 18 = w64 (c + 4) -> getr regs1 19 = w64 SB ->
getr regs1 20 = w64 (SB + (c + 4) / 8) ->
(forall j r, nth_error spa_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
aval_mem (rdW W mem) (c + CALL_OFF_NARGS) 4 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (spa_extra regs c))) (ss_at pc)
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS spa_Bx spa_SH (Eimg (Ereg regs1 (spa_extra regs c))) (mrestrict (w_H W) mem).
Proof.
intros pc ly S W mem md regs regs1 c sp0 HAR Hsp Hsp47 Hsp16 Hc Hsp1 R8 R18 R19 R20 HFR HNA.
destruct (spa_slot_bounds c Hc) as (Hcb & Hc8 & Hce).
assert (Hcr : 0x5e3750 <= c <= 0x5e3be0 /\ c + 56 <= 0x5e3c18)
  by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, CALL_SIZE, SC_SIZE in Hcb, Hce; lia).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs1 (spa_extra regs c))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 8)%nat -> ew E (32 + j) = nth j (spa_extra regs c) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (ESB : ew E SA_SB = Z_to_bv 64 SB) by (exact (EX 0%nat ltac:(lia))).
assert (EC : ew E SA_C = Z_to_bv 64 c) by (exact (EX 1%nat ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = sp0 - SPA_FRAME) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp1).
assert (UC : bv_unsigned (ew E SA_C) = c) by (rewrite EC; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E SA_SB) = SB) by (rewrite ESB; apply unsigned_lit_small; unfold SB; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_at. apply pa_entry_st_ok_full.
  + apply regs_ok_by_cases. intros r Hr. cbv [YP01.all_regs In] in Hr.
    clear HFR HNA.
    assert (EC' : ew E 33 = Z_to_bv 64 c) by exact EC. assert (ESB' : ew E 32 = Z_to_bv 64 SB) by exact ESB.
    assert (UC' : bv_unsigned (ew E 33) = c) by exact UC.
    repeat (destruct Hr as [<- | Hr];
      [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) =>
          let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
        first [ rewrite (denot_shx E 33 32 4 c SB EC' ESB') by (unfold SB; lia); exact R20
              | cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
                first [ apply getr_zero
                      | symmetry; apply EE; reflexivity
                      | rewrite ESB'; exact R19
                      | rewrite EC'; exact R8
                      | rewrite UC'; exact R18 ] ]
      | ]); try (destruct Hr; fail).
  + vm_compute. reflexivity.
  + unfold spa_rs, spa_stack, spa_slot.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold YP09.region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. unfold SPA_FRAME in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
        let j := eval compute in (n - 34)%nat in let r := eval compute in (nth j spa_saved 0) in
        let m := eval compute in (n - 32)%nat in
        apply (chunk_ok_val SEGS E _ (sp0 - 48) off 8 (SOff n 0) (bv_unsigned (getr regs (Z_to_bv 5 r))));
        [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
          change (ew E n) with (ew E (32 + m)%nat); rewrite (EX m ltac:(cbv; lia));
          cbn [spa_extra nth map app spa_saved]; symmetry; apply Z_to_bv_bv_unsigned
        | let HR := fresh in pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR;
          change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
        | cbn; lia
        | replace (sp0 - 48 + off) with (sp0 - 8 - 8 * Z.of_nat j) by (cbn; lia); exact (HFR j r eq_refl) ] end.
    * rewrite UC. split; [lia|]. split; [unfold CALL_SIZE; lia|].
      split.
      { intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|]. apply (spa_in_PG c); [exact Hc|].
        unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *. lia. }
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ c CALL_OFF_NARGS 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      intros kk Hkk. pose proof (HNA kk Hkk) as Hv. unfold aview in Hv.
      destruct (mbyte SEGS (mrestrict (w_H W) mem) (c + CALL_OFF_NARGS + Z.of_nat kk)) as [b|] eqn:Eb;
        cbn [option_map] in Hv; [|discriminate Hv].
      injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hv.
      unfold bv_wrap, bv_modulus. cbn [Z.of_N]. cbv [YO0f.le_byte YG0f.le_byte]. symmetry. apply Z.mod_mod. lia.
  + apply pairwise_disjoint_of_extents. unfold spa_rs, spa_stack, spa_slot, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, UC.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SPA_FRAME, CALL_SIZE in *. repeat split; lia.
  + split; [|split; exact I].
    cbn [spa_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, UC, USB. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold SPA_FRAME in *. split; [split; [lia | split; [|lia]]|].
    { replace (sp0 - 48) with (sp0 + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
    split; [unfold SB; lia | split; [|exact I]]. split; [unfold A_G_REC, OFF_CALLS, A_REC_SPILL; lia | split; [exact Hc8 | lia]].
- unfold sh_ok, spa_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E spa_Bx SA_C c CALL_SIZE c 0 CALL_SIZE).
  + exact (spa_slot_addressable ly S W mem md c HAR Hc).
  + unfold spa_Bx. rewrite (U_atom E SA_SB SB ESB) by (unfold SB; lia). reflexivity.
  + apply (U_atom E SA_C c EC). lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE, SHADOW_OFF in *. lia.
Qed.

(* the shadow of an image or heap byte lies far above the slot *)
Lemma spa_shadow_above : forall x, 0 <= x < 2 ^ 47 -> 0x606000 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64.
Proof. intros x Hx. unfold shadow_of_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma spa_range_addressable_kept : forall (rd rd' : reader) a n,
(forall y, 0x606000 <= y < 2 ^ 64 -> rd' y = rd y) -> 0 <= a -> a + n <= 2 ^ 47 ->
range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n HK Ha Han HR x Hx. destruct (HR x Hx) as (sh & Hs & Hok). exists sh. split; [|exact Hok].
rewrite HK; [exact Hs | apply spa_shadow_above; lia].
Qed.

Lemma spa_hull_kept : forall (rd rd' : reader) a n,
(forall y, 0x606000 <= y < 2 ^ 64 -> rd' y = rd y) -> 0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof.
intros rd rd' a n HK Ha Han Hn HV s Hs. rewrite HK; [exact (HV s Hs)|].
unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (a + n - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + a / 8) 8 ltac:(lia)). pose proof (Z.mul_div_le (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z_div_mod_eq_full (2147450880 + a / 8) 8). pose proof (Z.mod_pos_bound (2147450880 + a / 8) 8 ltac:(lia)). lia.
Qed.

(* a string argument survives a change of memory confined to the slot *)
Lemma spa_str_kept : forall ly S (W : world SEGS) mem md (rd' : reader) (ro : Z -> Prop) c s x,
AR SEGS B ly S W mem md -> spa_slot_ok c ->
(forall a, ro a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG) ->
astr_argA B ly S (rdW W mem) ro [] s (Some x) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + CALL_SIZE) -> rd' a = rdW W mem a) ->
astr_argA B ly S rd' ro [] s (Some x) /\
(forall i, 0 <= i < Z.of_nat (length x) + 1 -> ~ (c <= s + i < c + CALL_SIZE) /\ 0 <= s + i < 2 ^ 47).
Proof.
intros ly S W mem md rd' ro c s x HAR Hc Hro (Hnz & Hstr & Hn & Harm) HK.
destruct (spa_slot_bounds c Hc) as (Hcb & Hc8 & Hce).
assert (Hcr : 0x5e3750 <= c /\ c + 56 <= 0x5e3c18)
  by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, CALL_SIZE, SC_SIZE in Hcb, Hce; lia).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HOUT : forall i, 0 <= i < Z.of_nat (length x) + 1 -> ~ (c <= s + i < c + CALL_SIZE) /\ 0 <= s + i < 2 ^ 47).
{ intros i Hi. destruct Harm as [((p & k & Hpk & Hps & Hse) & _) | (Hb & _)].
  - pose proof (blk_off_imgP B ly S W mem md p k HAR Hpk) as Hoff.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR Hpk) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos k ltac:(lia)) as [_ Hq]. unfold off_img in Hoff. unfold CALL_SIZE. lia.
  - destruct (Hb i Hi) as (Hr & _). destruct (Hro _ Hr) as [Himg HnP].
    pose proof (pa_img_range _ Himg) as Hrg.
    split; [|lia]. intros Hin. apply HnP. apply (spa_in_PG c); [exact Hc | exact Hin]. }
split; [|exact HOUT].
assert (HKs : forall i, 0 <= i < Z.of_nat (length x) + 1 -> rd' (s + i) = rdW W mem (s + i)).
{ intros i Hi. destruct (HOUT i Hi) as [H1 H2]. apply HK; [lia | exact H1]. }
assert (HKh : forall y, 0x606000 <= y < 2 ^ 64 -> rd' y = rdW W mem y).
{ intros y Hy. apply HK; [lia|]. unfold CALL_SIZE. lia. }
assert (Hs0 : 0 <= s /\ s + (Z.of_nat (length x) + 1) <= 2 ^ 47)
  by (pose proof (HOUT 0 ltac:(lia)) as [_ A]; pose proof (HOUT (Z.of_nat (length x)) ltac:(lia)) as [_ A']; lia).
split; [exact Hnz|]. split.
{ destruct Hstr as [Hb Hn0]. split; [|exact Hn0]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite HKs by lia. exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)). }
split; [exact Hn|].
destruct Harm as [Hh | Hro']; [left; exact Hh | right; exact Hro'].
Qed.

(* a string's tail stays visible when memory changes only in the slot *)
Lemma spa_tail_kept : forall (W W' : world SEGS) mem mem' c e,
spa_slot_ok c -> atail_vis SEGS W mem e -> ~ (c <= e < c + CALL_SIZE) -> 0 <= e < 2 ^ 47 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + CALL_SIZE) -> rdW W' mem' a = rdW W mem a) ->
atail_vis SEGS W' mem' e.
Proof.
intros W W' mem mem' c e Hc HT He He0 HK a Ha.
destruct (spa_slot_bounds c Hc) as (_ & Hc8 & _).
assert (Hn : ~ (c <= a < c + CALL_SIZE)).
{ intros Hin. apply He. exact (spa_word_in c CALL_SIZE e a Hc8 ltac:(reflexivity) Ha Hin). }
pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
rewrite HK; [exact (HT a Ha) | lia | exact Hn].
Qed.

(* arodata_okP reads only the read-only bytes *)
Lemma spa_aro_kept : forall (RLO RHI : Z) (rd rd' : reader), arodata_okP SEGS RLO RHI B rd ->
(forall a, in_roP SEGS RLO RHI a -> rd' a = rd a) -> arodata_okP SEGS RLO RHI B rd'.
Proof. intros RLO RHI rd rd' H HK a Hr Ho He. rewrite HK by exact Hr. exact (H a Hr Ho He). Qed.

(* the shadow entry of the slot, at any AR state of an environment whose atoms 32 and 33 are SB and the slot *)
Lemma spa_shok : forall ly S (W : world SEGS) mem md E c, AR SEGS B ly S W mem md -> spa_slot_ok c ->
ew E 32 = Z_to_bv 64 SB -> ew E 33 = Z_to_bv 64 c -> sh_ok SEGS spa_Bx spa_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E c HAR Hc ESB EC.
destruct (spa_slot_bounds c Hc) as (Hcb & _ & Hce).
assert (Hcr : 0x5e3750 <= c /\ c + 56 <= 0x5e3c18)
  by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, CALL_SIZE, SC_SIZE in Hcb, Hce; lia).
unfold sh_ok, spa_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E spa_Bx SA_C c CALL_SIZE c 0 CALL_SIZE).
- exact (spa_slot_addressable ly S W mem md c HAR Hc).
- unfold spa_Bx. rewrite (U_atom E SA_SB SB ESB) by (unfold SB; lia). reflexivity.
- apply (U_atom E SA_C c EC). lia.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE, SHADOW_OFF in *. lia.
Qed.

End e.
End f.
End d.
