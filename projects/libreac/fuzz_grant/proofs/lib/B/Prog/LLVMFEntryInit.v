(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryInit), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntryInit.v. *)
(* Image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantEntryInit.v (a working branch
   7c8c67da870, blob c94a1a65482, 1541 lines; that file carries no licence line): image
   B's cut offsets, registers, spill slots and shadow base, and the two UBSan branches
   image A's code has not got (the pointer-overflow guard at 0x80eac, whose trap is
   0x81f48, and the out-of-line shadow test at 0x80ec4, whose report call is 0x81f70). *)
(* The phase of fuzz_grant's entry function LLVMFuzzerTestOneInput (image B 0x80a3c)
   that allocates and clears the head-amp table: slots 0x80db0 .. 0x80ef8 / 0x81224
   (GP_mallocT .. GP_set / GP_unset0), fuzz_grant.c:189-200.

   The slots call the malloc wrapper for the 460-byte table (the abort at 0x81d98 is not
   reached: the wrapper gives back a block at 4096 or above), call reac_headamp_tx_init
   on it, mark `was_set` and `set_to` usable (18 shadow bytes each) and clear them with
   __asan_memset, keep the frame's addresses in the spill slots, and read the count of
   cells to set, the input byte at the cursor (its pointer-overflow guard at 0x80eac,
   its shadow check at 0x80ec4 and that check's slow path at 0x81f60, which the proof
   shows does not go to the error path). With no input byte left, or a count of 0, the
   next phase is the one at 0x81224; otherwise it is the set loop at 0x80ef8. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g GrantFrame YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantACjr HeadampTxInit.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts LLVMFEntryDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* Proof speed: `lia` case-splits on every disjunction and every `mod`/`/` fact in its
   context, and each case costs time in proportion to the whole context. rs_hold hides a
   hypothesis from `lia`; `exact`, `destruct` and application still see through it.
   rs_lia clears every hypothesis that is not an arithmetic fact, then calls `lia`.
   ge_init uses both. *)
Local Definition rs_hold (A : Prop) : Prop := A.
Local Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Local Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide in H end.
Local Ltac rs_lia := repeat match goal with H : ?T |- _ =>
  lazymatch T with
  | @eq Z _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | Z.ge _ _ => fail | Z.gt _ _ => fail
  | _ /\ _ => fail | _ \/ _ => fail | ~ _ => fail
  | _ => clear H
  end end; lia.

(* The symbolic state at 0x80db0: every register is its own atom (atoms 0..31 are the
   registers at the cut). The regions are the bytes the phase's first part touches: the
   spill slots 0..15, 32..39, 72..79 and 128..159 above s1 (atom 9), of which 72 holds
   the frame F (atom 21) and 144 the shadow offset, and the shadow bytes 4..21
   (`was_set`) and 30..47 (`set_to`) of the frame, at s3 (atom 19). *)
Definition rsI : smem :=
  [ YP09.mkRegion (Some 9%nat) 0 16 0 16 [];
    YP09.mkRegion (Some 9%nat) 32 40 32 40 [];
    YP09.mkRegion (Some 9%nat) 72 80 72 80 [YP09.mkChunk 72 (CVal 8 (SOff 21 0))];
    YP09.mkRegion (Some 9%nat) 128 160 128 160 [YP09.mkChunk 144 (CVal 8 (SLit SHADOW_OFF))];
    YP09.mkRegion (Some 19%nat) 4 22 4 22 [];
    YP09.mkRegion (Some 19%nat) 30 48 30 48 [] ].
Definition ss_i0 : sstate := mkSS GP_mallocT sr_atoms rsI None (mkFacts [] [] []).

(* The symbolic state at 0x80ecc, after the shadow check of the input byte: the two
   complement slots 112 and 120 writable, slots 128 and 136 holding the two tables, and
   the byte at the cursor s8 (atom 24) as atom 32. *)
Definition rsT : smem :=
  [ YP09.mkRegion (Some 9%nat) 112 128 112 128 [];
    YP09.mkRegion (Some 9%nat) 128 144 128 128
      [YP09.mkChunk 128 (CVal 8 (SOff 21 240)); YP09.mkChunk 136 (CVal 8 (SOff 21 32))];
    YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition GP_byte : Z := 0x490.
Definition ss_t0 : sstate := mkSS GP_byte sr_atoms rsT None (mkFacts [(32%nat, mkAF 0 255 0)] [] []).
(* The symbolic state at 0x80ea0, the test of the bytes left: only the shadow offset in
   slot 144, which the shadow check reads; this stretch writes nothing. *)
Definition rsM : smem :=
  [ YP09.mkRegion (Some 9%nat) 144 152 144 144 [YP09.mkChunk 144 (CVal 8 (SLit SHADOW_OFF))] ].
Definition GP_left : Z := 0x464.
Definition ss_m0 : sstate := mkSS GP_left sr_atoms rsM None (mkFacts [] [] []).

(* ---- the model of the count of cells to set (lib/Prog/GrantSlotPlan.v) ---- *)
Lemma gm_short : forall pl, (length pl <= GrantSlotPlan.h_pos (GrantSlotPlan.header pl))%nat ->
  GrantSlotPlan.nset pl = 0 /\ GrantSlotPlan.pos_cells pl = GrantSlotPlan.h_pos (GrantSlotPlan.header pl).
Proof.
intros pl H. unfold GrantSlotPlan.nset, GrantSlotPlan.pos_cells. rewrite (SegSetModel.rd8_ge pl _ H). split; reflexivity.
Qed.
Lemma gm_byte : forall pl, (GrantSlotPlan.h_pos (GrantSlotPlan.header pl) < length pl)%nat ->
  GrantSlotPlan.nset pl = GrantSlotPlan.pbz pl (GrantSlotPlan.h_pos (GrantSlotPlan.header pl)) /\
  GrantSlotPlan.pos_cells pl = S (GrantSlotPlan.h_pos (GrantSlotPlan.header pl)).
Proof.
intros pl H. unfold GrantSlotPlan.nset, GrantSlotPlan.pos_cells. rewrite (SegSetModel.rd8_lt pl _ H). split; reflexivity.
Qed.
Lemma gm_end0 : forall pl, GrantSlotPlan.nset pl = 0 ->
  GrantSlotPlan.pos_end pl = GrantSlotPlan.pos_cells pl /\ GrantSlotPlan.T_end pl = GrantSlotPlan.T0 /\
  GrantSlotPlan.ws_end pl = GrantSlotPlan.Z144 /\ GrantSlotPlan.st_end pl = GrantSlotPlan.Z144.
Proof.
intros pl H. unfold GrantSlotPlan.pos_end, GrantSlotPlan.T_end, GrantSlotPlan.ws_end, GrantSlotPlan.st_end,
  GrantSlotPlan.tables_end. rewrite H. cbn [Z.to_nat]. rewrite SegSetModel.tables_at_0.
unfold GrantSlotPlan.cells_upto. cbn [GrantSlotPlan.cells snd fst]. auto.
Qed.
Lemma gm_cells0 : forall pl, snd (GrantSlotPlan.cells_upto pl 0) = GrantSlotPlan.pos_cells pl.
Proof. reflexivity. Qed.
(* A byte the input model reads is a byte. *)
Lemma gm_rd8 : forall pl pos, 0 <= fst (GrantSlotPlan.rd8 pl pos) < 256.
Proof.
intros pl pos. unfold GrantSlotPlan.rd8. destruct (Nat.ltb_spec pos (length pl)); cbn [fst]; [|lia].
unfold GrantSlotPlan.pbz. pose proof (bv_unsigned_in_range 8 (nth pos pl (Z_to_bv 8 0))) as Hr.
change (bv_modulus 8) with 256 in Hr. lia.
Qed.
Lemma gm_hdr_bytes : forall pl,
  0 <= GrantSlotPlan.h_in (GrantSlotPlan.header pl) < 256 /\
  0 <= GrantSlotPlan.h_rows (GrantSlotPlan.header pl) < 256.
Proof.
intros pl. unfold GrantSlotPlan.header.
destruct (GrantSlotPlan.rd16 pl 0) as [u p1] eqn:E1.
destruct (GrantSlotPlan.rd8 pl p1) as [i p2] eqn:E2.
destruct (GrantSlotPlan.rd8 pl p2) as [r p3] eqn:E3.
cbn [GrantSlotPlan.h_in GrantSlotPlan.h_rows].
pose proof (gm_rd8 pl p1) as H1. rewrite E2 in H1. cbn [fst] in H1.
pose proof (gm_rd8 pl p2) as H2. rewrite E3 in H2. cbn [fst] in H2.
split; assumption.
Qed.

(* The frame's shadow after the two markings: `was_set` (4..21) and `set_to` (30..47)
   usable, every other byte as the prologue left it. *)
Lemma gsh_tables_nth : forall i, (i < 104)%nat ->
  nth i GSH_tables 0 = if ((4 <=? i) && (i <? 22) || (30 <=? i) && (i <? 48))%nat then 0 else nth i GSH_entry 0.
Proof.
intros i Hi.
assert (Hb : forallb (fun j => Z.eqb (nth j GSH_tables 0)
  (if ((4 <=? j) && (j <? 22) || (30 <=? j) && (j <? 48))%nat then 0 else nth j GSH_entry 0)) (seq 0 104) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb i ltac:(apply in_seq; lia)). apply Z.eqb_eq in Hb. exact Hb.
Qed.
Lemma gsh_tables_nth1 : forall i, (4 <= i < 22 \/ 30 <= i < 48)%nat -> nth i GSH_tables 0 = 0.
Proof.
intros i Hi. rewrite gsh_tables_nth by lia.
destruct (Nat.leb_spec 4 i), (Nat.ltb_spec i 22), (Nat.leb_spec 30 i), (Nat.ltb_spec i 48); cbn [andb orb];
  first [reflexivity | lia].
Qed.
Lemma gsh_tables_nth2 : forall i, (i < 104)%nat -> ~ (4 <= i < 22 \/ 30 <= i < 48)%nat ->
  nth i GSH_tables 0 = nth i GSH_entry 0.
Proof.
intros i Hi Hn. rewrite gsh_tables_nth by lia.
destruct (Nat.leb_spec 4 i), (Nat.ltb_spec i 22), (Nat.leb_spec 30 i), (Nat.ltb_spec i 48); cbn [andb orb];
  first [reflexivity | lia].
Qed.
(* The shadow byte of an address of an 8-aligned object, from the object's shadow base. *)
Lemma gi_sh_of : forall F x, F mod 8 = 0 -> shadow_of_addr SHADOW_OFF x = shadow_addr F + (x - F) / 8.
Proof.
intros F x HF. unfold shadow_of_addr, shadow_addr. pose proof (Z.div_mod F 8 ltac:(lia)) as D.
replace x with (F / 8 * 8 + (x - F)) at 1 by lia. rewrite Z.div_add_l by lia. ring.
Qed.
(* The `not` of a 64-bit value: the two complement slots the set loop reads. *)
Lemma gi_lxor_m1 : forall v, 0 <= v < 2 ^ 64 -> Z.lxor v (zcanon (-1)) = 2 ^ 64 - 1 - v.
Proof.
intros v Hv.
assert (Em : zcanon (-1) = 2 ^ 64 - 1).
{ unfold zcanon, M64. rewrite <- (Z.mod_add (-1) 1 (2 ^ 64)) by lia. apply Z.mod_small. lia. }
rewrite Em.
assert (Eo : 2 ^ 64 - 1 = Z.ones 64) by (rewrite Z.ones_equiv; lia).
assert (En : 2 ^ 64 - 1 - v = Z.lnot v mod 2 ^ 64).
{ unfold Z.lnot. rewrite <- (Z.mod_add (Z.pred (- v)) 1 (2 ^ 64)) by lia.
  rewrite Z.mod_small by (unfold Z.pred; lia). unfold Z.pred. ring. }
rewrite En, Eo. apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec.
destruct (Z.lt_ge_cases n 64) as [Hlt|Hge].
- rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia.
  rewrite Z.ones_spec_low by lia. apply Bool.xorb_true_r.
- rewrite Z.mod_pow2_bits_high by lia. rewrite Z.ones_spec_high by lia.
  rewrite Bool.xorb_false_r. apply Z.testbit_false; [lia|].
  rewrite Z.div_small; [reflexivity|]. split; [lia|].
  apply (Z.lt_le_trans _ (2 ^ 64)); [lia | apply Z.pow_le_mono_r; lia].
Qed.
(* The value of an atom with an offset. *)
Lemma gi_U_off : forall (E : env) n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  U E (SOff n c) = v + c.
Proof.
intros E n c v H Hv Hvc. rewrite U_SOff, H.
rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma gi_denot_of_U : forall (E : env) e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma gi_sv0 : forall (E : env) n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Lemma gi_seat : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) sp1 sh F,
  getr regs 9 = w64 sp1 -> getr regs 19 = w64 sh -> getr regs 21 = w64 F ->
  0 <= sp1 -> sp1 + 160 < 2 ^ 64 -> 0 <= sh -> sh + 48 < 2 ^ 64 -> 0 <= F -> F + 1024 < 2 ^ 64 ->
  (forall o, 0 <= o < 160 -> writable_at SEGS (mrestrict (w_H W) mem) (sp1 + o)) ->
  (forall o, 4 <= o < 48 -> writable_at SEGS (mrestrict (w_H W) mem) (sh + o)) ->
  sh + 48 <= sp1 ->
  rdword (aview SEGS (w_H W) mem) (sp1 + 72) = Some F ->
  rdword (aview SEGS (w_H W) mem) (sp1 + 144) = Some SHADOW_OFF ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_i0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + GP_mallocT)) mem (seg_rom SEGS))).
Proof.
intros W regs mem sp1 sh F R9 R19 R21 H1 H2 H3 H4 H5 H6 Wst Wsh Hsep S72 S144.
assert (E9 : bv_unsigned (ew (Eimg (Ereg regs [])) 9) = sp1)
  by (rewrite (ew_Eimg_Ereg_nat regs [] 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E19 : bv_unsigned (ew (Eimg (Ereg regs [])) 19) = sh)
  by (rewrite (ew_Eimg_Ereg_nat regs [] 19 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (E21 : ew (Eimg (Ereg regs [])) 21 = Z_to_bv 64 F)
  by (rewrite (ew_Eimg_Ereg_nat regs [] 21 21%bv eq_refl), R21; reflexivity).
assert (HSO : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; lia).
rewrite restrict_mkst_fx. unfold ss_i0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rsI. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  rewrite ?E9, ?E19.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wst; lia | constructor].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wst; lia | constructor].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wst; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ sp1 72 8%N (SOff 21 0) F).
    * rewrite gi_sv0, E21. reflexivity.
    * cbn [Z.of_N]. lia.
    * cbn [Z.of_N]. lia.
    * exact (val_mem_of_rdword SEGS (w_H W) mem (sp1 + 72) F S72).
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wst; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ sp1 144 8%N (SLit SHADOW_OFF) SHADOW_OFF).
    * reflexivity.
    * cbn [Z.of_N]. lia.
    * cbn [Z.of_N]. lia.
    * exact (val_mem_of_rdword SEGS (w_H W) mem (sp1 + 144) SHADOW_OFF S144).
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wsh; lia | constructor].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wsh; lia | constructor].
- apply pairwise_disjoint_of_extents. unfold rsI, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E19.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [exact I | split; exact I].
Qed.

(* The callee chain at s1: the caller's frame record (its sp, ra and s0) is on the chain
   when it lies under the layout's top, as `gch` says. *)
Lemma gi_chain : forall ly (rd rd' : reader) (regs : bvmap 5 word) sp',
  achain ly rd (spZ regs) (s0Z regs) [] -> ly_top ly <= 2 ^ 64 ->
  (forall a, spZ regs <= a < 2 ^ 64 -> rd' a = rd a) ->
  rdword rd' (spZ regs - 8) = Some (raZ regs) -> rdword rd' (spZ regs - 16) = Some (s0Z regs) -> 4096 <= raZ regs ->
  alloc_ceiling <= spZ regs -> spZ regs mod 8 = 0 -> sp' + 16 <= spZ regs ->
  achain ly rd' sp' (spZ regs) (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []).
Proof.
intros ly rd rd' regs sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal Hsp'.
destruct (Z.ltb_spec (spZ regs + 16) (ly_top ly)) as [Hlt | Hge].
- apply (achain_push ly rd rd' (spZ regs) (s0Z regs) (raZ regs) [] sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal);
  [lia | exact Hsp'].
- left. split; [right; left; lia | reflexivity].
Qed.

(* The writable windows a symbolic state may hold, as (base atom, lo, hi) triples: a
   region's window lies inside one of them, or is empty. *)
Definition win_in (ws : list (nat * Z * Z)) (r : YP09.region) : bool :=
  (YP09.r_whi r <=? YP09.r_wlo r) ||
  match YP09.r_base r with
  | Some n => existsb (fun w => match w with (m, lo, hi) =>
                Nat.eqb n m && (lo <=? YP09.r_wlo r) && (YP09.r_whi r <=? hi) end) ws
  | None => false
  end.
Definition in_wins (E : env) (ws : list (nat * Z * Z)) (a : Z) : Prop :=
  Exists (fun w => match w with (m, lo, hi) => bv_unsigned (ew E m) + lo <= a < bv_unsigned (ew E m) + hi end) ws.
(* The windows of the phase's first part: the spill slots 0..15, 32..39, 72..79 and
   128..159 above s1, and the frame's shadow bytes 4..21 and 30..47 at s3. *)
Definition WS_I : list (nat * Z * Z) :=
  [(9%nat, 0, 16); (9%nat, 32, 40); (9%nat, 72, 80); (9%nat, 128, 160); (19%nat, 4, 22); (19%nat, 30, 48)].
(* The window of the phase's end: the two complement slots 112 and 120. *)
Definition WS_T : list (nat * Z * Z) := [(9%nat, 112, 128)].

Lemma gi_wrange : forall E rs ws a,
  forallb (win_in ws) rs = true -> in_wrange E rs a -> in_wins E ws a.
Proof.
intros E rs ws a Hok (r & Hin & Ha).
pose proof (proj1 (forallb_forall _ _) Hok r Hin) as Hr. unfold win_in in Hr.
destruct r as [b lo hi wlo whi cs]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hr, Ha.
destruct (Z.leb_spec whi wlo) as [Hle|Hgt]; [lia|]. cbn [orb] in Hr.
destruct b as [n|]; [|discriminate]. cbn [base_val] in Ha.
apply existsb_exists in Hr as ([[m lo'] hi'] & Hw & Hc). apply Exists_exists. exists (m, lo', hi'). split; [exact Hw|].
apply andb_true_iff in Hc as [Hc H2]. apply andb_true_iff in Hc as [H0 H1].
apply Nat.eqb_eq in H0. subst m. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma gi_awr : forall E rs ws STK sp0 FP bl0 blc ly own,
  forallb (win_in ws) rs = true -> (forall a, in_wins E ws a -> awr_byte STK sp0 FP bl0 blc ly own a) ->
  awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof. intros E rs ws STK sp0 FP bl0 blc ly own Hok Hw a Ha. apply Hw. exact (gi_wrange E rs ws a Hok Ha). Qed.

Lemma gi_run_keep : forall E rs ws H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb (win_in ws) rs = true ->
  forall a, 0 <= a < 2 ^ 64 -> ~ in_wins E ws a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs ws H m m' HF Hok a Ha Hn. apply aview_eq_of. apply HF.
rewrite unsigned_lit_small by lia. intros Hw. exact (Hn (gi_wrange E rs ws a Hok Hw)).
Qed.

Lemma not_in_WS_I : forall E a sp1 sh, bv_unsigned (ew E 9) = sp1 -> bv_unsigned (ew E 19) = sh ->
  ~ (sp1 <= a < sp1 + 16) -> ~ (sp1 + 32 <= a < sp1 + 40) -> ~ (sp1 + 72 <= a < sp1 + 80) ->
  ~ (sp1 + 128 <= a < sp1 + 160) ->
  ~ (sh + 4 <= a < sh + 22) -> ~ (sh + 30 <= a < sh + 48) -> ~ in_wins E WS_I a.
Proof.
intros E a sp1 sh E9 E19 N1 N2 N3 N4 N5 N6 H. apply Exists_exists in H as ([[m lo] hi] & Hin & Hw).
cbn [WS_I In] in Hin. destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]]]; injection Hin as <- <- <-;
  cbn beta iota in Hw; rewrite ?E9, ?E19 in Hw; lia.
Qed.
Lemma not_in_WS_T : forall E a sp1, bv_unsigned (ew E 9) = sp1 ->
  ~ (sp1 + 112 <= a < sp1 + 128) -> ~ in_wins E WS_T a.
Proof.
intros E a sp1 E9 N H. apply Exists_exists in H as ([[m lo] hi] & Hin & Hw).
cbn [WS_T In] in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <- <-. cbn beta iota in Hw. rewrite E9 in Hw. lia.
Qed.
Lemma not_in_nil_ws : forall E a, ~ in_wins E [] a.
Proof. intros E a H. apply Exists_exists in H as (w & [] & _). Qed.

Lemma gi_kept : forall E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hv Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hv. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

(* Two memories that read the same at the addresses P names. *)
Definition gi_same (P : Z -> Prop) (W : world SEGS) (m : word -> option byte) (W' : world SEGS) (m' : word -> option byte) : Prop :=
  forall a, P a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a.

Lemma gi_saved_same : forall cx W ms W' ms',
  gsaved cx W ms ->
  gi_same (fun a => spZ (c_regs cx) - 104 <= a < spZ (c_regs cx)) W (ms_mem ms) W' (ms_mem ms') ->
  gsaved cx W' ms'.
Proof.
intros cx W ms W' ms' (H8 & Hj) Hs. split.
- rewrite (rdword_ext (aview SEGS (w_H W) (ms_mem ms))); [exact H8|]. intros kk Hkk. apply Hs. lia.
- intros j Hj'. rewrite (rdword_ext (aview SEGS (w_H W) (ms_mem ms))); [exact (Hj j Hj')|]. intros kk Hkk. apply Hs. lia.
Qed.

(* The bytes the phase keeps from the cut at 0x80db0 to the cut it lands in: the saved
   registers, the spill slots 24 and 88, the frame's shadow bytes it does not write, the
   frame's flag word and the input. The slots in its own windows (0, 8, 32, 72, 128,
   136, 144, 152) are kept by the symbolic chunks instead. *)
Definition gkeep (cx : ecx) (fp : Z) (a : Z) : Prop :=
  (spZ (c_regs cx) - 104 <= a < spZ (c_regs cx)) \/
  (c_sp1 cx + 24 <= a < c_sp1 cx + 32) \/ (c_sp1 cx + 88 <= a < c_sp1 cx + 96) \/
  (gSH cx fp <= a < gSH cx fp + 4) \/ (gSH cx fp + 22 <= a < gSH cx fp + 30) \/
  (gSH cx fp + 48 <= a < gSH cx fp + 104) \/
  (gF cx fp + 1016 <= a < gF cx fp + 1024) \/ (c_p cx <= a < c_p cx + c_n cx).

(* Where the phase's objects lie: the machine stack above the allocator's ceiling, the
   frame and the input block in application memory, the frame's shadow in shadow
   memory. *)
Definition gi_geo0 (cx : ecx) (fp : Z) : Prop :=
  alloc_ceiling + 32768 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 320 < c_sp1 cx <= spZ (c_regs cx) - 288 /\
  4096 <= gF cx fp /\ gF cx fp + 1024 <= alloc_ceiling /\
  (gF cx fp + 1024 <= 0x7fff8000 \/ 0x10007fff8000 <= gF cx fp) /\
  0x7fff8000 <= gSH cx fp /\ gSH cx fp + 128 <= 0x10007fff8000 /\
  (c_n cx = 0 \/ (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\
     (c_p cx + c_n cx <= 0x7fff8000 \/ 0x10007fff8000 <= c_p cx))) /\
  (c_n cx = 0 \/ c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 1024 <= c_p cx) /\
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.

Lemma gkeep_cat : forall cx fp a, gi_geo0 cx fp -> gkeep cx fp a ->
  (c_sp1 cx <= a < spZ (c_regs cx) /\ alloc_ceiling <= a) \/ (gSH cx fp <= a < gSH cx fp + 128) \/
  (gF cx fp + 1016 <= a < gF cx fp + 1024) \/ (c_n cx <> 0 /\ c_p cx <= a < c_p cx + c_n cx).
Proof.
intros cx fp a G Ha. unfold gi_geo0 in G. unfold gkeep in Ha.
destruct Ha as [H|[H|[H|[H|[H|[H|[H|H]]]]]]];
  [left; lia | left; lia | left; lia | right; left; lia | right; left; lia | right; left; lia
  | right; right; left; lia | right; right; right; split; lia].
Qed.

Lemma gkeep_win : forall cx fp a, gi_geo0 cx fp -> gkeep cx fp a ->
  0 <= a < 2 ^ 64 /\ ~ (c_sp1 cx <= a < c_sp1 cx + 16) /\ ~ (c_sp1 cx + 32 <= a < c_sp1 cx + 40) /\
  ~ (c_sp1 cx + 72 <= a < c_sp1 cx + 80) /\ ~ (c_sp1 cx + 128 <= a < c_sp1 cx + 160) /\
  ~ (gSH cx fp + 4 <= a < gSH cx fp + 22) /\ ~ (gSH cx fp + 30 <= a < gSH cx fp + 48) /\
  ~ (gF cx fp + 32 <= a < gF cx fp + 176) /\
  ~ (gF cx fp + 240 <= a < gF cx fp + 384) /\ ~ (c_sp1 cx - 16384 <= a < c_sp1 cx).
Proof.
intros cx fp a G Ha. unfold gi_geo0 in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G9' & G10).
unfold gkeep in Ha. destruct Ha as [H|[H|[H|[H|[H|[H|[H|H]]]]]]];
  [ lia | lia | lia | destruct G6 as [G6|G6]; lia | destruct G6 as [G6|G6]; lia | destruct G6 as [G6|G6]; lia
  | lia | destruct G9 as [G9|(G9a & G9b & [G9c|G9c])]; [lia | destruct G9' as [G9'|[G9'|G9']]; lia ..] ].
Qed.

Lemma achain_top : forall ly ly' rd sp v ch, ly_top ly' = ly_top ly -> achain ly rd sp v ch -> achain ly' rd sp v ch.
Proof. intros ly ly' rd sp v ch Ht H. unfold achain in *. rewrite Ht. exact H. Qed.

Lemma gi_pw_app : forall {X : Type} (R : X -> X -> Prop) l1 l2 x y,
  YG0f.pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|z l1 IH]; intros l2 x y HP Hx Hy; [destruct Hx|].
cbn [app YG0f.pairwise] in HP. destruct HP as [HF HP]. destruct Hx as [<-|Hx].
- rewrite Forall_forall in HF. apply HF. apply in_app_iff. right. exact Hy.
- exact (IH l2 x y HP Hx Hy).
Qed.

Lemma wins_I_cases : forall E a sp1 sh, bv_unsigned (ew E 9) = sp1 -> bv_unsigned (ew E 19) = sh ->
  in_wins E WS_I a -> (sp1 <= a < sp1 + 160) \/ (sh + 4 <= a < sh + 48).
Proof.
intros E a sp1 sh E9 E19 H. apply Exists_exists in H as ([[m lo] hi] & Hin & Hw).
cbn [WS_I In] in Hin. destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]]]; injection Hin as <- <- <-;
  cbn beta iota in Hw; rewrite ?E9, ?E19 in Hw; lia.
Qed.

(* A zero byte the engine stored: chunk `o` of a region holds 1-byte literal 0. *)
Definition has0 (cs : list YP09.chunk) (o : Z) : bool :=
  existsb (fun c => (YP09.c_off c =? o) &&
    match YP09.c_val c with CVal w (SLit z) => N.eqb w 1 && (z =? 0) | _ => false end) cs.
Lemma has0_In : forall cs o, has0 cs o = true -> In (YP09.mkChunk o (CVal 1 (SLit 0))) cs.
Proof.
intros cs o H. apply existsb_exists in H as (c & Hin & Hc). destruct c as [oc cv]. cbn [YP09.c_off YP09.c_val] in Hc.
apply andb_true_iff in Hc as [Ho Hv]. apply Z.eqb_eq in Ho. subst oc.
destruct cv as [w v | | |]; try discriminate. destruct v; try discriminate. apply andb_true_iff in Hv as [Hw Hz].
apply N.eqb_eq in Hw. apply Z.eqb_eq in Hz. subst. exact Hin.
Qed.
Lemma gi_zero_range : forall E H (m : word -> option byte) n b lo hi wlo whi cs lo' len,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  forallb (has0 cs) (map (fun i => lo' + Z.of_nat i) (seq 0 len)) = true ->
  forall o, lo' <= o < lo' + Z.of_nat len -> aview SEGS H m (b + o) = Some 0.
Proof.
intros E H m n b lo hi wlo whi cs lo' len HR Hn Hall o Ho.
assert (Hino : In o (map (fun i => lo' + Z.of_nat i) (seq 0 len))).
{ apply in_map_iff. exists (Z.to_nat (o - lo')). split; [lia | apply in_seq; lia]. }
pose proof (has0_In cs o (proj1 (forallb_forall _ _) Hall o Hino)) as Hc.
apply (aview_of_val_mem1 SEGS H m); [|lia].
exact (field_of_region E (mrestrict H m) n b cs lo hi wlo whi o 1%N (SLit 0) 0 HR Hn Hc eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma gi_slot8 : forall E H (m : word -> option byte) n b lo hi wlo whi cs od e v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H m) (b + od) = Some v.
Proof.
intros E H m n b lo hi wlo whi cs od e v HR Hn Hc He Hv.
apply (rdword_of_val_mem SEGS H m); [|exact Hv].
exact (field_of_region E (mrestrict H m) n b cs lo hi wlo whi od 8%N e v HR Hn Hc He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma gi_slot_move : forall cx W ms W' ms' off v,
  gslot cx W ms off v ->
  (forall i, 0 <= i < 8 -> aview SEGS (w_H W') (ms_mem ms') (c_sp1 cx + off + i) = aview SEGS (w_H W) (ms_mem ms) (c_sp1 cx + off + i)) ->
  gslot cx W' ms' off v.
Proof. intros cx W ms W' ms' off v Hs Hm. unfold gslot in *. rewrite (rdword_ext (aview SEGS (w_H W) (ms_mem ms))); [exact Hs|]. exact Hm. Qed.

(* The machine-state part of a cut at 0x80ea0 or 0x80ecc. *)
Definition gi_pc (pc : Z) (ms : machine_state) : Prop :=
  ms_pc_val ms = w64 (BASE + pc) /\ ms_resv ms = None /\ ms_svc_pending ms = None /\
  ms_rom ms = seg_rom SEGS /\ ms_fregs ms = fp_regs /\ ms_fcsr ms = fp_csr.
(* Its registers: the frame's shadow base in s3, the table in s4, the frame in s5, the
   bytes left in s7, the input cursor in s8. *)
Definition gi_regs (cx : ecx) (fp t : Z) (ms : machine_state) : Prop :=
  gregs cx ms /\
  getr (ms_regs ms) 19 = w64 (gSH cx fp) /\ getr (ms_regs ms) 20 = w64 t /\
  getr (ms_regs ms) 21 = w64 (gF cx fp) /\
  getr (ms_regs ms) 23 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.h_pos (ge_hdr cx))) /\
  getr (ms_regs ms) 24 = w64 (c_p cx + Z.of_nat (GrantSlotPlan.h_pos (ge_hdr cx))).
(* Where the phase's addresses lie: every object below s1, the saved words above the
   spill slots. *)
Definition gi_geo (cx : ecx) (fp t : Z) : Prop :=
  0 <= gSH cx fp /\ gSH cx fp + 128 <= c_sp1 cx /\ 0 <= gF cx fp /\ gF cx fp + 1024 <= c_sp1 cx /\
  0 <= t /\ t + 460 <= c_sp1 cx /\ 0 <= c_p cx /\ (c_n cx = 0 \/ c_p cx + c_n cx <= c_sp1 cx) /\
  0 <= c_sp1 cx /\ c_sp1 cx + 184 <= spZ (c_regs cx) - 104 /\ spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 320 < c_sp1 cx /\ c_p cx + c_n cx <= 2 ^ 47.

(* The ten spill slots image B's body keeps from the two calls of __asan_memset of the
   prologue on (0x80dc4, 0x80e98, 0x811d8, 0x80e9c, 0x80d00, 0x811d4, 0x80e84, 0x80e28,
   0x80aa0, 0x80e94), in the order LLVMFEntryDefs.v's GI_set and GI_unset0 name them. *)
Definition gi_slots (cx : ecx) (fp t : Z) (W : world SEGS) (ms : machine_state) : Prop :=
  gslot cx W ms 0 (GrantSlotPlan.h_rows (ge_hdr cx)) /\
  gslot cx W ms 8 (gF cx fp) /\
  gslot cx W ms 24 (256 * (GrantSlotPlan.h_u16 (ge_hdr cx) / 256)) /\
  gslot cx W ms 32 (GrantSlotPlan.h_in (ge_hdr cx)) /\
  gslot cx W ms 72 (gF cx fp) /\
  gslot cx W ms 88 (GrantSlotPlan.h_base (ge_hdr cx) mod 2 ^ 64) /\
  gslot cx W ms 128 (gF cx fp + GO_SET) /\
  gslot cx W ms 136 (gF cx fp + GO_WAS) /\
  gslot cx W ms 144 SHADOW_OFF /\
  gslot cx W ms 152 t.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset).
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis TXI : HeadampTxInit.treac_headamp_tx_init_spec B.

(* The memory part of a cut at 0x80ea0 or 0x80ecc. *)
Definition gi_mem (cx : ecx) (fp t : Z) (ly : alayout) (S : astate) (W : world SEGS) (ms : machine_state) : Prop :=
  gsaved cx W ms /\ gshadow cx fp W ms GSH_tables /\
  rdword (aview SEGS (w_H W) (ms_mem ms)) (gF cx fp + 1016) = Some (gFL cx fp) /\
  garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  gi_slots cx fp t W ms /\
  gtab B cx ly S W ms t GrantSlotPlan.T0 /\
  gfarr cx fp W ms GO_WAS GrantSlotPlan.Z144 /\ gfarr cx fp W ms GO_SET GrantSlotPlan.Z144.
Definition gi_st (cx : ecx) (fp pc t : Z) (ly : alayout) (S : astate) (W : world SEGS) (ms : machine_state) : Prop :=
  gi_pc pc ms /\ gi_regs cx fp t ms /\ gi_mem cx fp t ly S W ms.

Lemma gi_mem_move : forall cx fp t ly S W ms W' ms',
  gi_mem cx fp t ly S W ms -> gi_geo cx fp t ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 112 <= a < c_sp1 cx + 128) ->
     aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  gi_mem cx fp t ly S W' ms'.
Proof.
intros cx fp t ly S W ms W' ms' (HSV & HSH & HFL & HIN & SMID & HTAB & HWAS & HSET) HG Hm.
destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
assert (HL : length GSH_tables = 104%nat) by reflexivity.
destruct SMID as (S0 & S8 & S24 & S32 & S72 & S88 & S128 & S136 & S144 & S152).
split; [apply (gi_saved_same cx W ms W' ms' HSV); intros a Ha; apply Hm; lia|].
split; [intros i Hi; unfold gshadow in HSH; rewrite Hm; [apply HSH; exact Hi | lia | lia]|].
split; [rewrite (rdword_ext (aview SEGS (w_H W) (ms_mem ms))); [exact HFL|]; intros kk Hkk; apply Hm; lia|].
split; [eapply (garr8_aview_kept SEGS (w_H W) (w_H W') (ms_mem ms) (ms_mem ms')); [|exact HIN];
  intros a Ha; rewrite length_map in Ha; fold (c_n cx) in Ha; apply Hm; lia|].
split; [unfold gi_slots; repeat split; (eapply gi_slot_move; [eassumption|]); intros i Hi; apply Hm; lia|].
split.
{ destruct HTAB as (Hin & Ht0 & Hlen & Hb). split; [exact Hin|]. split; [exact Ht0|]. split; [exact Hlen|].
  intros i Hi H1 H2 H3. rewrite Hm; [apply Hb; assumption | lia | lia]. }
split; unfold gfarr in *;
  (eapply (garr8_aview_kept SEGS (w_H W) (w_H W') (ms_mem ms) (ms_mem ms')); [|eassumption]);
  intros a Ha; rewrite length_map in Ha; cbn [GrantSlotPlan.Z144 length repeat] in Ha;
  unfold GO_WAS, GO_SET in Ha; apply Hm; lia.
Qed.

Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- 0x80ecc .. 0x80ef8 / 0x81224: the count of cells to set ---- *)
(* lbu s5,0(s8); a2 := s7 - 1; beqz s5: with a count of 0 the next cut is 0x81224,
   otherwise the two complement slots are written and the set loop at 0x80ef8 starts
   with i = 0. *)
Lemma gi_tail : forall POST, ge_from B MT POST (GI_set B MT) -> ge_from B MT POST (GI_unset0 B MT) ->
  forall cx fp k acc ly S W ms md t,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly S W (ms_mem ms) md k ->
  frames S = [(GE_CID, fp)] -> mo_le MT (c_S cx) S acc ->
  k <= 1 -> acc <= GE_A1 MT -> gblk1 B cx ly S t -> c_n cx < 2 ^ 26 ->
  Z.of_nat (GrantSlotPlan.h_pos (ge_hdr cx)) < c_n cx ->
  getr (ms_regs ms) 10 = w64 (c_p cx + Z.of_nat (GrantSlotPlan.h_pos (ge_hdr cx)) + 1) ->
  gi_geo cx fp t -> gi_st cx fp GP_byte t ly S W ms ->
  SRr SEGS W (mkCfg ms md) (POST cx).
Proof.
intros POST HSET HUNS cx fp k acc ly S W ms md t HB HJ HFR HMLE Hk Hacc Hbl Hn26 Hhp R10 HG (HPC & HRG & HM).
unfold ge_hdr in *.
pose proof HPC as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr).
pose proof HRG as ((R2 & R8 & R9 & R3 & R4) & R19 & R20 & R21 & R23 & R24). unfold ge_hdr in R23, R24.
pose proof HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JPRES & _).
assert (FFS : GE_STK = 32768) by reflexivity.
set (hp := GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx))) in *.
assert (Hlt : (hp < length (c_pl cx))%nat) by (unfold c_n in Hhp; lia).
destruct (gm_byte (c_pl cx) Hlt) as (Hns & Hpcells). fold hp in Hns, Hpcells.
assert (Hcp : 0 <= c_p cx + Z.of_nat hp < 2 ^ 64) by (destruct G8 as [G8|G8]; lia).
assert (Hcp1 : 0 <= c_p cx + Z.of_nat hp + 1 < 2 ^ 64) by (destruct G8 as [G8|G8]; lia).
assert (Hcn : 0 <= c_n cx - Z.of_nat hp < 2 ^ 64) by lia.
assert (Hcn1 : 0 <= c_n cx - Z.of_nat (Datatypes.S hp) < 2 ^ 64) by (rewrite Nat2Z.inj_succ; lia).
set (b := GrantSlotPlan.pbz (c_pl cx) hp) in *.
assert (Hb256 : 0 <= b < 256).
{ unfold b, GrantSlotPlan.pbz. pose proof (bv_unsigned_in_range 8 (nth hp (c_pl cx) (Z_to_bv 8 0))) as Hr.
  change (bv_modulus 8) with 256 in Hr. exact Hr. }
assert (Hbyte : aview SEGS (w_H W) (ms_mem ms) (c_p cx + Z.of_nat hp) = Some b).
{ pose proof HM as (_ & _ & _ & HIN & _).
  destruct (HIN hp ltac:(rewrite length_map; exact Hlt)) as [Hv _].
  assert (Hnth : nth hp (map (fun b0 : byte => bv_unsigned b0) (c_pl cx)) 0 = b).
  { unfold b, GrantSlotPlan.pbz. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hlt).
    apply (map_nth (fun b0 : byte => bv_unsigned b0)). }
  rewrite Hnth in Hv. exact (aview_of_val_mem1 SEGS (w_H W) (ms_mem ms) _ b Hv Hb256). }
pose proof HM as (HSV0 & HSH0 & HFL0 & HIN0 & SMID0 & HTAB0 & HWAS0 & HSET0).
destruct SMID0 as (Q0 & Q8 & Q24 & Q32 & Q72 & Q88 & Q128 & Q136 & Q144 & Q152).
assert (Ems : ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + GP_byte)) (ms_mem ms) (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfrg Hfcsr. destruct ms; cbn in *; subst; reflexivity. }
rewrite Ems. rewrite Ems in HJ. cbn [ms_mem mkst] in HJ.
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 b])) ss_t0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + GP_byte)) mem (seg_rom SEGS)))).
{ assert (E9u : bv_unsigned (ew (Eimg (Ereg regs [w64 b])) 9) = c_sp1 cx)
    by (rewrite (ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (E21u : ew (Eimg (Ereg regs [w64 b])) 21 = Z_to_bv 64 (gF cx fp))
    by (rewrite (ew_Eimg_Ereg_nat regs _ 21 21%bv eq_refl), R21; reflexivity).
  assert (E24u : bv_unsigned (ew (Eimg (Ereg regs [w64 b])) 24) = c_p cx + Z.of_nat hp)
    by (rewrite (ew_Eimg_Ereg_nat regs _ 24 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
  assert (E32 : ew (Eimg (Ereg regs [w64 b])) 32 = w64 b)
    by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  rewrite restrict_mkst_fx. unfold ss_t0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold rsT. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E9u. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply JPRES. lia.
    + rewrite E9u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS _ _ (c_sp1 cx) 128 8%N (SOff 21 240) (gF cx fp + GO_SET)).
        { cbn [sv_denot]. rewrite E21u, unsigned_lit_small by lia. unfold GO_SET. reflexivity. }
        { cbn [Z.of_N]. unfold GO_SET. lia. }
        { cbn [Z.of_N]. lia. }
        { exact (val_mem_of_rdword SEGS (w_H W) mem (c_sp1 cx + 128) _ Q128). }
      * apply (chunk_ok_val SEGS _ _ (c_sp1 cx) 136 8%N (SOff 21 32) (gF cx fp + GO_WAS)).
        { cbn [sv_denot]. rewrite E21u, unsigned_lit_small by lia. unfold GO_WAS. reflexivity. }
        { cbn [Z.of_N]. unfold GO_WAS. lia. }
        { cbn [Z.of_N]. lia. }
        { exact (val_mem_of_rdword SEGS (w_H W) mem (c_sp1 cx + 136) _ Q136). }
    + rewrite E24u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (c_p cx + Z.of_nat hp) 0 1%N (SOff 32 0) b).
      * rewrite gi_sv0, E32. reflexivity.
      * cbn [Z.of_N]. lia.
      * cbn [Z.of_N]. lia.
      * rewrite Z.add_0_r. exact (proj1 (val_mem1_of_aview SEGS (w_H W) mem _ _ Hbyte)).
  - apply pairwise_disjoint_of_extents. unfold rsT, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9u, E24u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
remember (Eimg (Ereg regs [w64 b])) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros nn r Hnn; subst E; apply ew_Eimg_Ereg_nat; exact Hnn).
assert (E32 : ew E 32 = w64 b) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
clear HE.
assert (E9u : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E21u : ew E 21 = Z_to_bv 64 (gF cx fp)) by (rewrite (EE 21%nat 21%bv eq_refl), R21; reflexivity).
(* lbu s5,0(s8); addi a2,s7,-1; beqz s5 *)
paj_run_shc RUNP RUNC HS HJ.
{ eapply (gi_awr _ _ WS_T); [vm_compute; reflexivity|]. intros a Ha. apply Exists_exists in Ha as ([[mm lo] hi] & Hin & Hw).
  cbn [WS_T In] in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <- <-. cbn beta iota in Hw. rewrite E9u in Hw. left. lia. }
lazymatch goal with H1 : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
rename HF into HF1. rename HFr into HFr1. rename mat into mat1.
assert (MV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 112 <= a < c_sp1 cx + 128) ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. apply (gi_run_keep E _ WS_T _ _ _ HFr1); [vm_compute; reflexivity | exact Ha | exact (not_in_WS_T E a _ E9u Hn)]. }
psrr_branch_pi RUNP BR HS.
- (* a count of 0: on to 0x81224 *)
  rewrite branch_eq_U, (U_atom _ 32 b), U_SLit in Hc by (first [exact E32 | lia]). change (zcanon 0) with 0 in Hc.
  apply Z.eqb_eq in Hc.
  paj_run_to_sh RUNTOP HS HJ GP_unset0.
  { eapply (gi_awr _ _ WS_T); [vm_compute; reflexivity|]. intros a Ha. apply Exists_exists in Ha as ([[mm lo] hi] & Hin & Hw).
    cbn [WS_T In] in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <- <-. cbn beta iota in Hw. rewrite E9u in Hw. left. lia. }
  lazymatch goal with H1 : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  assert (MV : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 112 <= a < c_sp1 cx + 128) ->
    aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) (ms_mem ms) a).
  { intros a Ha Hn. rewrite (gi_run_keep E _ WS_T _ _ _ HFr); [exact (MV1 a Ha Hn) | vm_compute; reflexivity | exact Ha
      | exact (not_in_WS_T E a _ E9u Hn)]. }
  pose proof (gi_mem_move cx fp t ly S W ms W ms2 HM HG MV) as (HSV2 & HSH2 & HFL2 & HIN2 & SMID2 & HTAB2 & HWAS2 & HSET2).
  norm_ss HS.
  pose proof (st_ok_pi_restrict_mkst (w_H W) E _ ms2 HS eq_refl) as Ems2. cbn [ss_pc] in Ems2.
  prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (19%bv : bv 5) P19. prreg HS (12%bv : bv 5) P12. prreg HS (23%bv : bv 5) P23.
  apply (HUNS cx fp k acc ly S W ms2 _ HB HJ HFR HMLE).
  exists t.
  assert (Hns0 : GrantSlotPlan.nset (c_pl cx) = 0) by (rewrite Hns; exact Hc).
  destruct (gm_end0 (c_pl cx) Hns0) as (Epe & ET & Ews & Est).
  rewrite Epe, Hpcells, ET, Ews, Est.
  split.
  { split; [rewrite Ems2; reflexivity|]. split; [rewrite Ems2; reflexivity|]. split; [rewrite Ems2; reflexivity|].
    split; [rewrite Ems2; reflexivity|]. split; [rewrite Ems2; reflexivity|]. split; [rewrite Ems2; reflexivity|].
    split; [unfold gregs; rewrite P2, P8, P9, P3, P4, (EE 2%nat 2%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 9%nat 9%bv eq_refl),
      (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl); repeat split; assumption|].
    split; [exact HSV2|]. split; [exact HSH2|]. split; [exact HFL2|]. split; [reflexivity | exact HIN2]. }
  split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hbl|]. split; [exact Hn26|].
  split; [rewrite P19, (EE 19%nat 19%bv eq_refl); exact R19|].
  split.
  { rewrite P12. cbn [sv_denot]. rewrite (EE 23%nat 23%bv eq_refl), R23. unfold w64.
    rewrite (unsigned_lit_small _ Hcn). f_equal. rewrite Nat2Z.inj_succ. ring. }
  split.
  { rewrite P23, (EE 10%nat 10%bv eq_refl), R10. unfold w64. f_equal. rewrite Nat2Z.inj_succ. ring. }
  destruct SMID2 as (D0 & D8 & D24 & D32 & D72 & D88 & D128 & D136 & D144 & D152).
  split; [exact D0|]. split; [exact D8|]. split; [exact D24|]. split; [exact D32|].
  split; [exact D72|]. split; [exact D88|]. split; [exact D128|]. split; [exact D136|].
  split; [exact D144|]. split; [exact D152|].
  split; [exact HTAB2|]. split; [exact HWAS2|]. split; [exact HSET2|].
  split; [exact SegSetModel.Hrel_T0 | exact SegSetModel.I1_T0].
- rewrite branch_eq_U, (U_atom _ 32 b), U_SLit in Hc by (first [exact E32 | lia]). change (zcanon 0) with 0 in Hc.
  apply Z.eqb_neq in Hc.
  paj_run_to_sh RUNTOP HS HJ GP_set.
  { eapply (gi_awr _ _ WS_T); [vm_compute; reflexivity|]. intros a Ha. apply Exists_exists in Ha as ([[mm lo] hi] & Hin & Hw).
    cbn [WS_T In] in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <- <-. cbn beta iota in Hw. rewrite E9u in Hw. left. lia. }
  lazymatch goal with H1 : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  assert (MV : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 112 <= a < c_sp1 cx + 128) ->
    aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) (ms_mem ms) a).
  { intros a Ha Hn. rewrite (gi_run_keep E _ WS_T _ _ _ HFr); [exact (MV1 a Ha Hn) | vm_compute; reflexivity | exact Ha
      | exact (not_in_WS_T E a _ E9u Hn)]. }
  pose proof (gi_mem_move cx fp t ly S W ms W ms2 HM HG MV) as (HSV2 & HSH2 & HFL2 & HIN2 & SMID2 & HTAB2 & HWAS2 & HSET2).
  norm_ss HS.
  pose proof (st_ok_pi_restrict_mkst (w_H W) E _ ms2 HS eq_refl) as Ems2. cbn [ss_pc] in Ems2.
  prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (19%bv : bv 5) P19. prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
  prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (23%bv : bv 5) P23.
  pose proof (st_ok_pi_region_nth E _ _ 0%nat _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  apply (HSET cx fp k acc ly S W ms2 _ HB HJ HFR HMLE).
  exists 0%nat, t.
  rewrite gm_cells0, Hpcells, SegSetModel.tables_at_0. cbv beta iota.
  split.
  { split; [rewrite Ems2; reflexivity|]. split; [rewrite Ems2; reflexivity|]. split; [rewrite Ems2; reflexivity|].
    split; [rewrite Ems2; reflexivity|]. split; [rewrite Ems2; reflexivity|]. split; [rewrite Ems2; reflexivity|].
    split; [unfold gregs; rewrite P2, P8, P9, P3, P4, (EE 2%nat 2%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 9%nat 9%bv eq_refl),
      (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl); repeat split; assumption|].
    split; [exact HSV2|]. split; [exact HSH2|]. split; [exact HFL2|]. split; [reflexivity | exact HIN2]. }
  split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hbl|]. split; [exact Hn26|].
  split; [rewrite Hns; cbn [Z.of_nat]; lia|].
  split; [rewrite P19, (EE 19%nat 19%bv eq_refl); exact R19|].
  split; [rewrite P20, (EE 20%nat 20%bv eq_refl); exact R20|].
  split; [rewrite P21, E32, Hns; unfold w64; f_equal; cbn [Z.of_nat]; ring|].
  split.
  { rewrite P23, (EE 10%nat 10%bv eq_refl), R10. unfold w64. f_equal. rewrite Nat2Z.inj_succ. ring. }
  split.
  { rewrite P12. cbn [sv_denot]. rewrite (EE 23%nat 23%bv eq_refl), R23. unfold w64.
    rewrite (unsigned_lit_small _ Hcn). f_equal. rewrite Nat2Z.inj_succ. ring. }
  split; [rewrite P13; reflexivity|].
  destruct SMID2 as (D0 & D8 & D24 & D32 & D72 & D88 & D128 & D136 & D144 & D152).
  split; [exact D0|]. split; [exact D8|]. split; [exact D24|]. split; [exact D32|].
  split; [exact D72|]. split; [exact D88|].
  split.
  { unfold gslot. apply (gi_slot8 E (w_H W) (ms_mem ms2) 9 (c_sp1 cx) _ _ _ _ _ 112 (SAlu ALU_XOR (SOff 21 240) (SLit (-1))) _ RG0 E9u);
      [cbn; tauto | | unfold GO_SET; lia].
    unfold GO_SET. apply gi_denot_of_U.
    rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
    rewrite (gi_U_off E 21 240 (gF cx fp) E21u ltac:(lia) ltac:(lia)).
    rewrite gi_lxor_m1 by lia. apply zcanon_id. unfold M64. lia. }
  split.
  { unfold gslot. apply (gi_slot8 E (w_H W) (ms_mem ms2) 9 (c_sp1 cx) _ _ _ _ _ 120 (SAlu ALU_XOR (SOff 21 32) (SLit (-1))) _ RG0 E9u);
      [cbn; tauto | | unfold GO_WAS; lia].
    unfold GO_WAS. apply gi_denot_of_U.
    rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
    rewrite (gi_U_off E 21 32 (gF cx fp) E21u ltac:(lia) ltac:(lia)).
    rewrite gi_lxor_m1 by lia. apply zcanon_id. unfold M64. lia. }
  split; [exact D128|]. split; [exact D136|]. split; [exact D144|]. split; [exact D152|].
  split; [exact HTAB2|]. split; [exact HWAS2|]. split; [exact HSET2|].
  split; [exact SegSetModel.Hrel_T0 | exact SegSetModel.I1_T0].
Qed.

(* The slow path of the shadow check at 0x81f60 (`andi a2,s8,7; bge a2,a1`): a byte in
   the last, partial granule of a block lies below the granule's shadow value. *)
Lemma gi_slow : forall p h n, p mod 8 = 0 -> 0 <= p -> 0 <= h < n ->
  (if h / 8 <? n / 8 then 0 else n mod 8) <> 0 ->
  Z.land (p + h) 7 < (if h / 8 <? n / 8 then 0 else n mod 8).
Proof.
intros p h n Hp Hp0 Hh Hs. destruct (Z.ltb_spec (h / 8) (n / 8)) as [Hlt|Hge]; [exfalso; apply Hs; reflexivity|].
assert (Hle : h / 8 <= n / 8) by (apply Z.div_le_mono; lia).
assert (Heq : h / 8 = n / 8) by lia.
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
replace ((p + h) mod 8) with (h mod 8).
- pose proof (Z.div_mod h 8 ltac:(lia)) as Dh. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn.
  pose proof (Z.mod_pos_bound h 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia.
- rewrite Z.add_mod by lia. rewrite Hp, Z.add_0_l, Z.mod_mod by lia. reflexivity.
Qed.
Lemma gi_branch_ge : forall E a b, 0 <= U E a < 2 ^ 63 -> 0 <= U E b < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (U E a <? U E b).
Proof.
intros E a b Ha Hb. rewrite YO0c.branch_ge. unfold U in Ha, Hb |- *.
rewrite (YO0b.s64_small _ Ha), (YO0b.s64_small _ Hb). reflexivity.
Qed.

(* ---- 0x80ea0 .. 0x80ecc / 0x81224: the test of the bytes left, the pointer-overflow
   guard and the shadow check of the input byte ---- *)
Lemma gi_mid : forall POST, ge_from B MT POST (GI_set B MT) -> ge_from B MT POST (GI_unset0 B MT) ->
  forall cx fp k acc ly S W ms md t,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly S W (ms_mem ms) md k ->
  frames S = [(GE_CID, fp)] -> mo_le MT (c_S cx) S acc ->
  k <= 1 -> acc <= GE_A1 MT -> gblk1 B cx ly S t -> c_n cx < 2 ^ 26 ->
  gi_geo cx fp t -> gi_st cx fp GP_left t ly S W ms ->
  SRr SEGS W (mkCfg ms md) (POST cx).
Proof.
intros POST HSET HUNS cx fp k acc ly S W ms md t HB HJ HFR HMLE Hk Hacc Hbl Hn26 HG HST.
pose proof HST as (HPC & HRG & HM).
pose proof HPC as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr).
pose proof HRG as ((R2 & R8 & R9 & R3 & R4) & R19 & R20 & R21 & R23 & R24). unfold ge_hdr in R23, R24.
pose proof HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JPRES & _).
pose proof HB as (_ & _ & _ & Hpn & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : GE_STK = 32768) by reflexivity.
set (hp := GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx))) in *.
assert (Hhl : (hp <= length (c_pl cx))%nat) by apply SegSetModel.header_le.
assert (Hcp : 0 <= c_p cx + Z.of_nat hp < 2 ^ 64) by (unfold c_n in *; lia).
assert (Hcn : 0 <= c_n cx - Z.of_nat hp < 2 ^ 64) by (unfold c_n in *; lia).
pose proof HM as (HSV0 & HSH0 & HFL0 & HIN0 & SMID0 & HTAB0 & HWAS0 & HSET0).
destruct SMID0 as (Q0 & Q8 & Q24 & Q32 & Q72 & Q88 & Q128 & Q136 & Q144 & Q152).
assert (Ems : ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + GP_left)) (ms_mem ms) (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfrg Hfcsr. destruct ms; cbn in *; subst; reflexivity. }
rewrite Ems. rewrite Ems in HJ. cbn [ms_mem mkst] in HJ.
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
assert (HSO : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; lia).
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_m0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + GP_left)) mem (seg_rom SEGS)))).
{ assert (E9u : bv_unsigned (ew (Eimg (Ereg regs [])) 9) = c_sp1 cx)
    by (rewrite (ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold ss_m0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold rsM. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (c_sp1 cx) 144 8%N (SLit SHADOW_OFF) SHADOW_OFF).
    + reflexivity.
    + cbn [Z.of_N]. lia.
    + cbn [Z.of_N]. lia.
    + exact (val_mem_of_rdword SEGS (w_H W) mem (c_sp1 cx + 144) SHADOW_OFF Q144).
  - split; exact I.
  - split; [exact I | split; exact I]. }
remember (Eimg (Ereg regs [])) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros nn r Hnn; subst E; apply ew_Eimg_Ereg_nat; exact Hnn).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (E9u : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E24u : ew E 24 = Z_to_bv 64 (c_p cx + Z.of_nat hp)) by (rewrite (EE 24%nat 24%bv eq_refl), R24; reflexivity).
(* beqz s7 *)
psrr_branch_pi RUNP BR HS.
- (* no input byte left: 0x81190, then 0x81224 *)
  rewrite branch_eq_U, (U_atom _ 23 (c_n cx - Z.of_nat hp)), U_SLit in Hc
    by (first [rewrite (EE 23%nat 23%bv eq_refl); exact R23 | exact Hcn]).
  change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc.
  paj_run_to_sh RUNTOP HS HJ GP_unset0.
  { eapply (gi_awr _ _ []); [vm_compute; reflexivity|]. intros a Ha. destruct (not_in_nil_ws E a Ha). }
  lazymatch goal with H1 : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  assert (MV : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 112 <= a < c_sp1 cx + 128) ->
    aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) (ms_mem ms) a).
  { intros a Ha Hn. apply (gi_run_keep E _ [] _ _ _ HFr); [vm_compute; reflexivity | exact Ha | apply not_in_nil_ws]. }
  pose proof (gi_mem_move cx fp t ly S W ms W ms2 HM HG MV) as (HSV2 & HSH2 & HFL2 & HIN2 & SMID2 & HTAB2 & HWAS2 & HSET2).
  norm_ss HS.
  pose proof (st_ok_pi_restrict_mkst (w_H W) E _ ms2 HS eq_refl) as Ems2. cbn [ss_pc] in Ems2.
  prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (19%bv : bv 5) P19. prreg HS (12%bv : bv 5) P12. prreg HS (23%bv : bv 5) P23.
  apply (HUNS cx fp k acc ly S W ms2 _ HB HJ HFR HMLE).
  exists t.
  assert (Hshort : (length (c_pl cx) <= hp)%nat) by (unfold c_n in Hc; lia).
  destruct (gm_short (c_pl cx) Hshort) as (Hns0 & Hpcells). fold hp in Hpcells.
  destruct (gm_end0 (c_pl cx) Hns0) as (Epe & ET & Ews & Est).
  rewrite Epe, Hpcells, ET, Ews, Est.
  split.
  { split; [rewrite Ems2; reflexivity|]. split; [rewrite Ems2; reflexivity|]. split; [rewrite Ems2; reflexivity|].
    split; [rewrite Ems2; reflexivity|]. split; [rewrite Ems2; reflexivity|]. split; [rewrite Ems2; reflexivity|].
    split; [unfold gregs; rewrite P2, P8, P9, P3, P4, (EE 2%nat 2%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 9%nat 9%bv eq_refl),
      (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl); repeat split; assumption|].
    split; [exact HSV2|]. split; [exact HSH2|]. split; [exact HFL2|]. split; [reflexivity | exact HIN2]. }
  split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hbl|]. split; [exact Hn26|].
  split; [rewrite P19, (EE 19%nat 19%bv eq_refl); exact R19|].
  split; [rewrite P12; unfold w64; rewrite Hc; reflexivity|].
  split; [rewrite P23, (EE 24%nat 24%bv eq_refl); exact R24|].
  destruct SMID2 as (D0 & D8 & D24 & D32 & D72 & D88 & D128 & D136 & D144 & D152).
  split; [exact D0|]. split; [exact D8|]. split; [exact D24|]. split; [exact D32|].
  split; [exact D72|]. split; [exact D88|]. split; [exact D128|]. split; [exact D136|].
  split; [exact D144|]. split; [exact D152|].
  split; [exact HTAB2|]. split; [exact HWAS2|]. split; [exact HSET2|].
  split; [exact SegSetModel.Hrel_T0 | exact SegSetModel.I1_T0].
- (* an input byte is left: the pointer-overflow guard and the shadow check *)
  rewrite branch_eq_U, (U_atom _ 23 (c_n cx - Z.of_nat hp)), U_SLit in Hc
    by (first [rewrite (EE 23%nat 23%bv eq_refl); exact R23 | exact Hcn]).
  change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
  assert (Hhp : Z.of_nat hp < c_n cx) by (unfold c_n in *; lia). clear Hc.
  (* The input block: it exists, because at least one byte is left. *)
  assert (Hpn' : In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))
    by (destruct Hpn as [[Hn0 _] | [_ Hin]]; [unfold c_n in *; lia | exact Hin]).
  assert (HinS : In (c_p cx, c_n cx) (ablocks B ly S)) by (unfold gblk1 in Hbl; rewrite Hbl; apply in_app_iff; left; exact Hpn').
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) HinS) as (Hp16 & Hp4096 & Hpceil & Hpapp & _).
  destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) HinS) as ((Hp8 & _ & Hbs) & _).
  assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hrq in Hpceil, Hbs.
  (* addi a0,s8,1; addi a1,zero,1; bltu a1,a0: the UBSan pointer-overflow guard. *)
  paj_run_shc RUNP RUNC HS HJ.
  { eapply (gi_awr _ _ []); [vm_compute; reflexivity|]. intros a Ha. destruct (not_in_nil_ws E a Ha). }
  lazymatch goal with H1 : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms0 end.
  rename HFr into HFr0. rename HF into HF0. rename mat into mat0.
  assert (MV0 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
  { intros a Ha. apply (gi_run_keep E _ [] _ _ _ HFr0); [vm_compute; reflexivity | exact Ha | apply not_in_nil_ws]. }
  psrr_branch_pi RUNP BR HS.
  2:{ (* the trap at 0x81f48 is not reached: the cursor plus one is above 1 *)
      exfalso. rewrite branch_ltu_U, U_SLit, (gi_U_off E 24 1 (c_p cx + Z.of_nat hp) E24u ltac:(lia) ltac:(lia)) in Hc.
      change (zcanon 1) with 1 in Hc.
      destruct (Z.ltb_spec 1 (c_p cx + Z.of_nat hp + 1)) as [Hl|Hl]; cbn [negb] in Hc; [discriminate Hc | lia]. }
  clear Hc.
  (* srli a1,s8,3; ld a2,144(s1); add a1,a1,a2: the engine stops at the shadow load. *)
  paj_run_shc RUNP RUNC HS HJ.
  { eapply (gi_awr _ _ []); [vm_compute; reflexivity|]. intros a Ha. destruct (not_in_nil_ws E a Ha). }
  lazymatch goal with H1 : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  rename HFr into HFr1. rename HF into HF1. rename mat into mat1.
  assert (MV1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
  { intros a Ha. rewrite (gi_run_keep E _ [] _ _ _ HFr1); [exact (MV0 a Ha) | vm_compute; reflexivity | exact Ha
      | apply not_in_nil_ws]. }
  set (i0 := Z.of_nat hp / 8).
  assert (Hi0 : 0 <= i0 < (c_n cx + 7) / 8).
  { assert (H1 : Z.of_nat hp / 8 <= (c_n cx - 1) / 8) by (apply Z.div_le_mono; lia).
    assert (H2 : (c_n cx + 7) / 8 = (c_n cx - 1) / 8 + 1)
      by (replace (c_n cx + 7) with ((c_n cx - 1) + 1 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
    assert (H3 : 0 <= Z.of_nat hp / 8) by (apply Z.div_pos; lia).
    unfold i0. lia. }
  set (s := if i0 <? c_n cx / 8 then 0 else c_n cx mod 8).
  pose proof (Hbs i0 Hi0) as Hs0. fold s in Hs0.
  assert (Hs8 : 0 <= s < 8) by (unfold s; destruct (i0 <? c_n cx / 8); [lia | apply Z.mod_pos_bound; lia]).
  set (sa := SHADOW_OFF + (c_p cx + Z.of_nat hp) / 8).
  assert (Hsa : shadow_of_addr SHADOW_OFF (c_p cx) + i0 = sa).
  { unfold shadow_of_addr, sa, i0. pose proof (Z.div_mod (c_p cx) 8 ltac:(lia)) as Dp.
    replace (c_p cx + Z.of_nat hp) with (c_p cx / 8 * 8 + Z.of_nat hp) by lia. rewrite Z.div_add_l by lia. ring. }
  rewrite Hsa in Hs0.
  assert (Hs : aview SEGS (w_H W) (ms_mem ms1) sa = Some s).
  { rewrite (MV1 sa ltac:(unfold sa, SHADOW_OFF; split;
      [pose proof (Z.div_pos (c_p cx + Z.of_nat hp) 8 ltac:(lia) ltac:(lia)); lia
      | pose proof (Z.div_le_upper_bound (c_p cx + Z.of_nat hp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia])). exact Hs0. }
  pose proof HB as (HPRE0 & _). pose proof HPRE0 as (_ & _ & _ & _ & _ & (_ & _ & Hceil0 & Hslo0 & _) & _).
  assert (Hsar : 0 <= sa /\ sa + 1 <= c_sp1 cx).
  { assert (Hq : (c_p cx + Z.of_nat hp) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
    assert (Hq0 : 0 <= (c_p cx + Z.of_nat hp) / 8) by (apply Z.div_pos; lia).
    unfold sa, SHADOW_OFF. lia. }
  (* atoms 32 and 33: the shadow byte's address and its value; a1 is the address. *)
  norm_ss HS.
  pose proof (st_ok_pi_havoc 32 E _ _ [w64 sa; w64 s] HS ltac:(vm_compute; reflexivity) ltac:(cbv; lia)) as HS'.
  remember (havoc E 32 [w64 sa; w64 s]) as E' eqn:HE' in HS'.
  assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (E'o : forall n, (n < 32)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite HE'; apply YN3v.ew_havoc_old; exact Hn).
  assert (E'32 : ew E' 32 = w64 sa) by (rewrite HE'; reflexivity).
  assert (E'33 : ew E' 33 = w64 s) by (rewrite HE'; reflexivity).
  assert (HAE' : env_agree 32 (Ereg regs []) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
  clear HE'. clear HS.
  assert (E'9u : bv_unsigned (ew E' 9) = c_sp1 cx) by (rewrite E'o by lia; exact E9u).
  assert (E'24u : ew E' 24 = Z_to_bv 64 (c_p cx + Z.of_nat hp)) by (rewrite E'o by lia; exact E24u).
  lazymatch type of HS' with st_ok_pi _ _ _ ?ssx _ =>
    pose proof (st_ok_pi_restrict_reg (w_H W) E' ssx ms1 11%bv HS') as Ra1;
    let e := eval vm_compute in (sr_get (ss_regs ssx) 11%bv) in change (sr_get (ss_regs ssx) 11%bv) with e in Ra1 end.
  rewrite denot_lit_U, U_SAlu, U_srl3, (U_atom E' 24 (c_p cx + Z.of_nat hp)), U_SLit in Ra1
    by (first [exact E'24u | exact Hcp]).
  cbn [zalu_raw] in Ra1.
  pose proof (st_ok_pi_set_reg E' _ _ 11%bv (SOff 32 0) HS'
    ltac:(intros Hr0; apply (f_equal bv_unsigned) in Hr0; vm_compute in Hr0; discriminate Hr0)) as HS2.
  match type of HS2 with ?A -> _ => assert (HA2 : A); [|specialize (HS2 HA2); clear HA2] end.
  { cbn [restrict ms_regs]. rewrite Ra1, gi_sv0, E'32. unfold w64, sa, SHADOW_OFF.
    assert (Hq : (c_p cx + Z.of_nat hp) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
    assert (Hq0 : 0 <= (c_p cx + Z.of_nat hp) / 8) by (apply Z.div_pos; lia).
    change (zcanon 2147450880) with 2147450880.
    rewrite zcanon_id by (unfold M64; lia). f_equal. ring. }
  clear HS' Ra1.
  pose proof (st_ok_pi_add_region E' _ _ (YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))]) HS2
    ltac:(vm_compute; reflexivity)) as HS3.
  match type of HS3 with ?A -> ?A2 -> _ => assert (HA3 : A); [|specialize (HS3 HA3); clear HA3];
    [|assert (HA4 : A2); [|specialize (HS3 HA4); clear HA4]] end.
  { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
    rewrite E'32. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E' _ sa 0 1%N (SOff 33 0) s).
    - rewrite gi_sv0, E'33. reflexivity.
    - cbn [Z.of_N]. lia.
    - cbn [Z.of_N]. lia.
    - rewrite Z.add_0_r. exact (proj1 (val_mem1_of_aview SEGS (w_H W) (ms_mem ms1) _ _ Hs)). }
  { cbn [ss_mem YP09.all_disjoint]. split; [|exact I]. hnf.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E'32, E'9u. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  clear HS2.
  pose proof (st_ok_pi_add_fact E' _ _ 33 (mkAF 0 7 0) HS3) as HS4.
  match type of HS4 with ?A -> _ => assert (HA5 : A); [|specialize (HS4 HA5); clear HA5] end.
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E'33. unfold w64. rewrite unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  clear HS3. rename HS4 into HS. norm_ss HS.
  (* At 0x80ecc the cut is gi_tail's: the registers of 0x80ea0, plus a0 = cursor + 1. *)
  assert (TAIL : forall ms3 md3 ss3,
    st_ok_pi SEGS VAL E' ss3 (restrict (w_H W) ms3) -> ss_pc ss3 = GP_byte -> ss_resv ss3 = None ->
    forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss3) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
      [2; 3; 4; 8; 9; 19; 20; 21; 23; 24]%bv = true ->
    sr_get (ss_regs ss3) 10%bv = SOff 24 1 ->
    ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(GE_CID, fp)] ly S W (ms_mem ms3) md3 k ->
    (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a) ->
    SRr SEGS W (mkCfg ms3 md3) (POST cx)).
  { intros ms3 md3 ss3 HS3 Hpc3 Hrv3 Hregs3 Ha03 HJ3 MV3.
    pose proof (st_ok_pi_restrict_mkst (w_H W) E' ss3 ms3 HS3 Hrv3) as Ems3. rewrite Hpc3 in Ems3.
    pose proof (regs_kept_of_st_ok_pi E' ss3 _ regs [] _ HS3 HAE' Hregs3) as RK. cbn [ms_regs restrict] in RK.
    pose proof (st_ok_pi_restrict_reg (w_H W) E' ss3 ms3 10%bv HS3) as Ra0.
    rewrite Ha03 in Ra0. cbn [ms_regs restrict] in Ra0.
    apply (gi_tail POST HSET HUNS cx fp k acc ly S W ms3 md3 t HB HJ3 HFR HMLE Hk Hacc Hbl Hn26
      ltac:(unfold ge_hdr; exact Hhp)).
    - rewrite Ra0. cbn [sv_denot]. rewrite E'24u, unsigned_lit_small by lia. reflexivity.
    - exact HG.
    - split; [|split].
      + unfold gi_pc. rewrite Ems3. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
        repeat split; reflexivity.
      + unfold gi_regs, gregs.
        rewrite !RK by (repeat (first [left; reflexivity | right])).
        repeat split; assumption.
      + apply (gi_mem_move cx fp t ly S W ms W ms3 HM HG). intros a Ha Hn. exact (MV3 a Ha). }
  (* lb a1,0(a1); beqz a1: the shadow byte of the granule *)
  paj_run_shc RUNP RUNC HS HJ.
  { eapply (gi_awr _ _ []); [vm_compute; reflexivity|]. intros a Ha. destruct (not_in_nil_ws E' a Ha). }
  lazymatch goal with H1 : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  rename HFr into HFr2.
  assert (MV2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
  { intros a Ha. rewrite (gi_run_keep E' _ [] _ _ _ HFr2); [exact (MV1 a Ha) | vm_compute; reflexivity | exact Ha
      | apply not_in_nil_ws]. }
  psrr_branch_pi RUNP BR HS.
  + (* the granule is wholly usable: on to 0x80ecc *)
    paj_run_to_sh RUNTOP HS HJ GP_byte.
    { eapply (gi_awr _ _ []); [vm_compute; reflexivity|]. intros a Ha. destruct (not_in_nil_ws E' a Ha). }
    lazymatch goal with H1 : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
    norm_ss HS.
    apply (TAIL ms3 _ _ HS eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ).
    intros a Ha. rewrite (gi_run_keep E' _ [] _ _ _ HFr); [exact (MV2 a Ha) | vm_compute; reflexivity | exact Ha
      | apply not_in_nil_ws].
  + (* the last, partial granule: j 0x81f60, andi a2,s8,7; bge a2,a1 *)
    rewrite branch_eq_U, (U_atom _ 33 s), U_SLit in Hc by (first [exact E'33 | lia]).
    change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc. rename Hc into Hs0'.
    paj_run_shc RUNP RUNC HS HJ.
    { eapply (gi_awr _ _ []); [vm_compute; reflexivity|]. intros a Ha. destruct (not_in_nil_ws E' a Ha). }
    lazymatch goal with H1 : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
    rename HFr into HFr3.
    assert (MV3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a).
    { intros a Ha. rewrite (gi_run_keep E' _ [] _ _ _ HFr3); [exact (MV2 a Ha) | vm_compute; reflexivity | exact Ha
        | apply not_in_nil_ws]. }
    assert (Uand : U E' (SAlu ALU_AND (SOff 24 0) (SLit 7)) = Z.land (c_p cx + Z.of_nat hp) 7).
    { rewrite U_SAlu, (U_atom E' 24 (c_p cx + Z.of_nat hp)), U_SLit; [| exact E'24u | exact Hcp].
      cbn [zalu_raw]. change (zcanon 7) with 7. apply zcanon_id.
      change 7 with (Z.ones 3). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (c_p cx + Z.of_nat hp) (2 ^ 3) ltac:(lia)).
      unfold M64. lia. }
    assert (Hland : 0 <= Z.land (c_p cx + Z.of_nat hp) 7 < 8).
    { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
    psrr_branch_pi RUNP BR HS.
    * (* the error path, a call of __asan_report_load1: not reached *)
      exfalso. rewrite gi_branch_ge, Uand, (U_atom _ 33 s) in Hc by (first [exact E'33 | lia | rewrite Uand; lia | rewrite (U_atom _ 33 s); [lia | exact E'33 | lia]]).
      apply negb_true_iff, Z.ltb_ge in Hc.
      pose proof (gi_slow (c_p cx) (Z.of_nat hp) (c_n cx) Hp8 ltac:(lia) ltac:(lia) Hs0') as Hslow.
      fold i0 s in Hslow. lia.
    * paj_run_to_sh RUNTOP HS HJ GP_byte.
      { eapply (gi_awr _ _ []); [vm_compute; reflexivity|]. intros a Ha. destruct (not_in_nil_ws E' a Ha). }
      lazymatch goal with H1 : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms4 end.
      norm_ss HS.
      apply (TAIL ms4 _ _ HS eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ).
      intros a Ha. rewrite (gi_run_keep E' _ [] _ _ _ HFr); [exact (MV3 a Ha) | vm_compute; reflexivity | exact Ha
        | apply not_in_nil_ws].
Qed.

(* The writes of a run of the phase's first part are its own: the spill slots are in the
   machine stack window, the frame's shadow bytes in its frame. *)
Ltac awr_I E9 E19 HSF :=
  eapply (gi_awr _ _ WS_I); [vm_compute; reflexivity|];
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  apply Exists_exists in Ha;
  let mm := fresh "mm" in let lo := fresh "lo" in let hi := fresh "hi" in let Hin := fresh "Hin" in let Hw := fresh "Hw" in
  destruct Ha as [[[mm lo] hi] [Hin Hw]]; cbn [WS_I In] in Hin;
  destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]]]; injection Hin as <- <- <-; cbn beta iota in Hw;
  [ rewrite E9 in Hw; left; lia | rewrite E9 in Hw; left; lia | rewrite E9 in Hw; left; lia
  | rewrite E9 in Hw; left; lia
  | rewrite E19 in Hw; right; right; right; eexists GE_CID, _; split; [left; reflexivity|];
    right; unfold in_zr; cbn [fst snd]; rewrite <- HSF; change (fs_frame_bytes GE_CID / 8) with 128; lia
  | rewrite E19 in Hw; right; right; right; eexists GE_CID, _; split; [left; reflexivity|];
    right; unfold in_zr; cbn [fst snd]; rewrite <- HSF; change (fs_frame_bytes GE_CID / 8) with 128; lia ].

Lemma gi_fa : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity. Qed.
Lemma gi_top : forall n ly ly', layout_le n ly ly' -> ly_top ly' = ly_top ly.
Proof. intros n ly ly' (_ & _ & _ & _ & _ & _ & _ & _ & Ht & _). exact Ht. Qed.

Lemma gsaved_words : forall cx W ms, gsaved cx W ms ->
  rdword (aview SEGS (w_H W) (ms_mem ms)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) /\
  rdword (aview SEGS (w_H W) (ms_mem ms)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)).
Proof.
intros cx W ms (H8 & Hj). split; [exact H8|].
pose proof (Hj 0 ltac:(lia)) as H0. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
exact H0.
Qed.

(* The call chain at s1 for the functions this phase calls (cgif lib/A/ACf5.v:172). *)
Lemma gi_chain_at : forall cx ly (W : world SEGS) (m : word -> option byte), ge_base B MT cx -> ly_top ly = ly_top (c_ly cx) ->
  (forall a, spZ (c_regs cx) <= a < 2 ^ 64 -> aview SEGS (w_H W) m a = aview SEGS (w_H (c_W cx)) (c_mem cx) a) ->
  rdword (aview SEGS (w_H W) m) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W) m) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  achain ly (aview SEGS (w_H W) m) (c_sp1 cx) (spZ (c_regs cx)) (gch cx).
Proof.
intros cx ly W m HB Ht Hk H8 H16.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1d & _).
pose proof HPRE as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hal8 : spZ (c_regs cx) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. exists (2 * q). lia. }
pose proof (Z.mul_div_le (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hmd.
apply (achain_top (c_ly cx)); [exact Ht|]. unfold gch.
apply (gi_chain (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) _ (c_regs cx) (c_sp1 cx) Hch);
  [lia | exact Hk | exact H8 | exact H16 | exact Hra4 | unfold GE_STK, STK_LLVMFuzzerTestOneInput in *; lia | exact Hal8 | unfold GE_STK, STK_LLVMFuzzerTestOneInput in *; lia].
Qed.

(* The new block t lies apart from the blocks before it and from the frame. *)
Lemma gi_sep_t : forall ly S W m md lyo So t fp,
  AR SEGS B ly S W m md -> ablocks B ly S = ablocks B lyo So ++ [(t, 460)] -> frames S = [(GE_CID, fp)] ->
  (forall p n, In (p, n) (ablocks B lyo So) -> p + req_size n <= t \/ t + 460 <= p) /\
  (frame_addr ly GE_CID fp + 1024 <= t \/ t + 460 <= frame_addr ly GE_CID fp).
Proof.
intros ly S W m md lyo So t fp HAR Ebl Efr.
destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as [Hsep _].
rewrite Ebl, Efr, map_app in Hsep. cbn [map fst snd] in Hsep.
change (req_size 460) with 460 in Hsep. change (fs_frame_bytes GE_CID) with 1024 in Hsep.
split.
- intros p n Hin. rewrite <- app_assoc in Hsep.
  pose proof (gi_pw_app zdisjoint _ _ (p, req_size n) (t, 460) Hsep
    ltac:(apply in_map_iff; exists (p, n); split; [reflexivity | exact Hin])
    ltac:(left; reflexivity)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
- pose proof (gi_pw_app zdisjoint _ _ (t, 460) (frame_addr ly GE_CID fp, 1024) Hsep
    ltac:(apply in_app_iff; right; left; reflexivity) ltac:(left; reflexivity)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* A block lies apart from the frame. *)
Lemma gi_sep_in : forall ly S W m md fp p n,
  AR SEGS B ly S W m md -> frames S = [(GE_CID, fp)] -> In (p, n) (ablocks B ly S) ->
  p + req_size n <= frame_addr ly GE_CID fp \/ frame_addr ly GE_CID fp + 1024 <= p.
Proof.
intros ly S W m md fp p n HAR Efr Hin.
destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as [Hsep _].
rewrite Efr in Hsep. cbn [map fst snd] in Hsep. change (fs_frame_bytes GE_CID) with 1024 in Hsep.
pose proof (gi_pw_app zdisjoint _ _ (p, req_size n) (frame_addr ly GE_CID fp, 1024) Hsep
  ltac:(apply in_map_iff; exists (p, n); split; [reflexivity | exact Hin]) ltac:(left; reflexivity)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* The bytes the phase keeps, across a run that writes only its windows. *)
Lemma gi_kp_run : forall cx fp E rs W0 m0 W m m',
  gi_geo0 cx fp -> gi_same (gkeep cx fp) W0 m0 W m ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> forallb (win_in WS_I) rs = true ->
  bv_unsigned (ew E 9) = c_sp1 cx -> bv_unsigned (ew E 19) = gSH cx fp ->
  gi_same (gkeep cx fp) W0 m0 W m'.
Proof.
intros cx fp E rs W0 m0 W m m' G K HF Hok E9 E19 a Ha. rewrite <- (K a Ha).
destruct (gkeep_win cx fp a G Ha) as (Ha64 & N1 & N2 & N3 & N4 & N5 & N6 & _).
apply (gi_run_keep E rs WS_I _ _ _ HF Hok a Ha64). exact (not_in_WS_I E a _ _ E9 E19 N1 N2 N3 N4 N5 N6).
Qed.

Lemma gi_bv_mod : forall a, Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof.
intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* The shadow bytes __asan_memset looks at for a range of the frame: the granules from
   the one of its first byte to the one of its last. *)
Lemma gi_hull_rng : forall F k1 k2 s, F mod 64 = 0 -> 0 <= F -> 0 <= k1 -> 0 <= k2 ->
  shadow_addr (F + 8 * k1) / 8 * 8 <= s < shadow_addr (F + 8 * k2 + 7) / 8 * 8 + 8 ->
  shadow_addr F + k1 / 8 * 8 <= s < shadow_addr F + k2 / 8 * 8 + 8.
Proof.
intros F k1 k2 s HF HF0 Hk1 Hk2 Hs.
assert (Fq : F = 8 * (F / 64) * 8) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
set (q := F / 64) in *. clearbody q.
unfold shadow_addr, SHADOW_OFF in *.
assert (E0 : F / 8 = 8 * q) by (rewrite Fq; apply Z.div_mul; lia).
assert (E1 : (F + 8 * k1) / 8 = 8 * q + k1)
  by (rewrite Fq; replace (8 * q * 8 + 8 * k1) with ((8 * q + k1) * 8) by ring; apply Z.div_mul; lia).
assert (E2 : (F + 8 * k2 + 7) / 8 = 8 * q + k2)
  by (rewrite Fq; replace (8 * q * 8 + 8 * k2 + 7) with ((8 * q + k2) * 8 + 7) by ring;
      rewrite Z.div_add_l by lia; change (7 / 8) with 0; lia).
assert (E3 : forall k, (2147450880 + (8 * q + k)) / 8 * 8 = 2147450880 + 8 * q + k / 8 * 8)
  by (intros k; replace (2147450880 + (8 * q + k)) with ((268431360 + q) * 8 + k) by ring;
      rewrite Z.div_add_l by lia; ring).
rewrite E1, E2, !E3 in Hs. rewrite E0. lia.
Qed.

(* The windows of the phase's first part are present after a call that keeps the frame. *)
Lemma gi_wins_present : forall cx fp ly S (W : world SEGS) m md k E,
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly S W m md k ->
  frames S = [(GE_CID, fp)] -> frame_addr ly GE_CID fp = gF cx fp ->
  spZ (c_regs cx) - 32768 <= c_sp1 cx -> c_sp1 cx + 160 <= spZ (c_regs cx) ->
  bv_unsigned (ew E 9) = c_sp1 cx -> bv_unsigned (ew E 19) = gSH cx fp ->
  forall a, in_wins E WS_I a -> apresent (w_H W) m a.
Proof.
intros cx fp ly S W m md k E HJx Hfr EFx H1 H2 E9 E19 a Ha.
pose proof HJx as (HARx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JPx & _).
destruct (wins_I_cases E a _ _ E9 E19 Ha) as [Hs|Hs].
- apply JPx. unfold GE_STK, STK_LLVMFuzzerTestOneInput. lia.
- assert (Hin : In (GE_CID, fp) (frames S)) by (rewrite Hfr; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HARx Hin) as (_ & _ & _ & HFS).
  rewrite EFx in HFS. change (fs_frame_bytes GE_CID / 8) with 128 in HFS.
  assert (ESx : gSH cx fp = shadow_addr (gF cx fp)) by reflexivity.
  replace a with (shadow_addr (gF cx fp) + (a - gSH cx fp)) by lia.
  exact (proj1 (HFS (a - gSH cx fp) ltac:(lia))).
Qed.

(* A region whose window is all of it, inside one of the windows `ws`; such regions are
   kept across a call that keeps every byte of the windows. *)
Definition win_full (ws : list (nat * Z * Z)) (r : YP09.region) : bool :=
  (YP09.r_lo r =? YP09.r_wlo r) && (YP09.r_hi r =? YP09.r_whi r) && win_in ws r.
Lemma gi_rk : forall E rs ws H (m : word -> option byte) H2 (m2 : word -> option byte),
  forallb (win_full ws) rs = true ->
  (forall a, in_wins E ws a -> aview SEGS H2 m2 a = aview SEGS H m a /\ apresent H2 m2 a) ->
  Forall (region_kept SEGS E (mrestrict H m) (mrestrict H2 m2)) rs.
Proof.
intros E rs ws H m H2 m2 Hok Hk. apply Forall_forall. intros r Hin.
pose proof (proj1 (forallb_forall _ _) Hok r Hin) as Hr. unfold win_full in Hr.
apply andb_true_iff in Hr as [Hr Hw]. apply andb_true_iff in Hr as [Hl Hh]. apply Z.eqb_eq in Hl. apply Z.eqb_eq in Hh.
assert (HW : forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
  in_wins E ws a).
{ intros a Ha. apply (gi_wrange E [r] ws a); [cbn [forallb]; rewrite Hw; reflexivity|]. exists r. split; [left; reflexivity | exact Ha]. }
split; intros a Ha.
- rewrite Hl, Hh in Ha. destruct (Hk a (HW a Ha)) as [Hv _]. apply (mbyte_of_aview SEGS). exact Hv.
- intros _. destruct (Hk a (HW a Ha)) as [_ Hp]. apply (apresent_writable SEGS). exact Hp.
Qed.

Theorem ge_init : forall POST,
  ge_from B MT POST (GI_set B MT) -> ge_from B MT POST (GI_unset0 B MT) -> ge_from B MT POST (GI_mallocT B).
Proof.
intros POST HSET HUNS cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMLE HGI.
destruct HGI as (HBODY & Hk & Hacc & Hbl & Hn26 & R19 & R21 & R24 & R23 & R22 & R25 & SL88 & SL24 & SL72 & SL144 & SL176).
destruct HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HLEN & HINP).
destruct HREGS as (R2 & R8 & R9 & R3 & R4).
pose proof HB as (HPRE & H10 & H11 & Hpn & HPL & Hfr0 & Hev & Hlive & HROD & Hsp1d & HE0 & HE02 & HE032 & HMOK & HTR & HNEED).
pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HAR3 & Hly3 & Hsecs3 & Hwle3 & Hio3 & Hfrs3 & Hnev3 & Hk0 & JST & JBLK & JIMG & JFRM & JGONE & JPRES & _ & JEXT & JQT).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (L := grant_listing)) as HBLO.
(* IMG_LO_B is opaque in GrantTop.v; every `lia` over the image base needs its value. *)
rewrite IMG_LO_B_val in HBLO.
assert (FFS : GE_STK = 32768) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
assert (Hin3 : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (EFA : frame_addr ly3 GE_CID fp = gF cx fp).
{ unfold gF, frame_addr. destruct Hly3 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR3 Hin3) as (HF32 & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ GE_CID fp HAR3 Hin3) as (HF4096 & HFceil & _).
rewrite EFA in HF32, HFapp, HFpres, HFSpres, HF4096, HFceil.
change (fs_frame_bytes GE_CID) with 1024 in *. change (1024 / 8) with 128 in HFSpres.
assert (Ems3 : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_mallocT)) (ms_mem ms3) (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfrg Hfcsr. destruct ms3; cbn in *; subst; reflexivity. }
rewrite Ems3.
set (sp0 := spZ (c_regs cx)) in *. set (sp1 := c_sp1 cx) in *.
set (F := gF cx fp) in *. set (SHB := gSH cx fp) in *.
assert (ESH : SHB = shadow_addr F) by reflexivity.
assert (Hsp1 : sp0 - 320 < sp1 <= sp0 - 288 /\ sp1 mod 32 = 0).
{ rewrite Hsp1d. pose proof (Z.div_mod (sp0 + -288) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0 + -288) 32 ltac:(lia)).
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult. }
destruct (frame_al64 SEGS B _ _ _ _ _ GE_CID fp HAR3 Hin3) as (HF64 & _ & _). rewrite EFA in HF64.
assert (HSHr : SHADOW_OFF <= SHB /\ SHB + 128 <= kHighShadowEnd /\ SHB mod 8 = 0).
{ assert (Fq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
  assert (F8 : F / 8 = 8 * (F / 64)) by (rewrite Fq at 1; replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia; apply Z.div_mul; lia).
  assert (Fb : F < 2 ^ 47) by lia.
  assert (F8b : 0 <= F / 64 < 2 ^ 41) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite ESH. unfold shadow_addr. rewrite F8, C2. unfold SHADOW_OFF.
  split; [lia|]. split; [lia|].
  replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by lia. apply Z_mod_mult. }
set (regs := ms_regs ms3) in *. set (mem := ms_mem ms3) in *.
pose proof (gi_seat W3 regs mem sp1 SHB F R9 R19 R21 ltac:(lia) ltac:(lia) ltac:(unfold SHADOW_OFF in *; lia) ltac:(lia)
  ltac:(lia) ltac:(lia)
  ltac:(intros o Ho; apply (apresent_writable SEGS); apply JPRES; lia)
  ltac:(intros o Ho; apply (apresent_writable SEGS); rewrite ESH; apply (proj1 (HFSpres o ltac:(lia))))
  ltac:(lia) SL72 SL144) as HS.
remember (Eimg (Ereg regs [])) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros nn r Hnn; subst E; apply ew_Eimg_Ereg_nat; exact Hnn).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (E9u : bv_unsigned (ew E 9) = sp1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E19u : bv_unsigned (ew E 19) = SHB) by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (HSHF : forall ly', frame_addr ly' GE_CID fp = F -> SHB = shadow_addr (frame_addr ly' GE_CID fp)) by (intros ly' ->; exact ESH).
assert (G0 : gi_geo0 cx fp).
{ unfold gi_geo0. fold sp0 sp1 F SHB.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [unfold SHADOW_OFF in HSHr; lia|]. split; [lia|].
  destruct Hpn as [[Hn0 _] | [Hn Hinp]]; [split; [left; exact Hn0 | split; [left; exact Hn0 | exact C1]] |].
  rewrite <- Hbl in Hinp. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinp) as (_ & Hp4 & Hpce & Hpa & _).
  pose proof (gi_sep_in _ _ _ _ _ _ _ _ HAR3 HFR Hinp) as Dpf. rewrite EFA in Dpf.
  assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hrq in Hpce, Hpa, Dpf. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpa.
  split; [right; lia|]. split; [right; lia | exact C1]. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
destruct (gm_hdr_bytes (c_pl cx)) as [HIN256 HROW256].
(* li a0,460; jal: the call of the malloc wrapper. *)
paj_run_shc RUNP RUNC HS HJ.
{ awr_I E9u E19u (HSHF ly3 EFA). }
lazymatch goal with HS1 : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
rename HJ into HJ1. rename HF into HF1. rename HFr into HFr1. rename mat into mat1. rename HG into HG1.
(* The memory the phase keeps, from the cut to the call. *)
assert (KP1 : gi_same (gkeep cx fp) W3 mem W3 (ms_mem ms1)).
{ intros a Ha. destruct (gkeep_win cx fp a G0 Ha) as (Ha64 & N1 & N2 & N3 & N4 & N5 & N6 & _).
  apply (gi_run_keep E (ss_mem ss_i0) WS_I _ _ _ HFr1); [vm_compute; reflexivity | exact Ha64 |].
  exact (not_in_WS_I E a sp1 SHB E9u E19u N1 N2 N3 N4 N5 N6). }
pmkst HS. ppcs.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (10%bv : bv 5) Ra0.
assert (HMOK1 : mo_ok MT S3 (mo_malloc MT 460)).
{ apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_malloc MT 460) MTL HMOK HMLE).
  - apply (mo_malloc_nonneg MT MTL). lia.
  - unfold GE_NEED, GE_A3, GE_A2, GE_A1 in HNEED. pose proof (mo_malloc_nonneg MT MTL 8670 ltac:(lia)).
    pose proof (mo_malloc_nonneg MT MTL 4352 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia. }
assert (HSV1 : gsaved cx W3 ms1) by exact (gi_saved_same cx W3 ms3 W3 ms1 HSAVED (fun a Ha => KP1 a (or_introl Ha))).
assert (HCH1 : achain ly3 (aview SEGS (w_H W3) (ms_mem ms1)) sp1 sp0 (gch cx)).
{ pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & JST1 & _).
  destruct (gsaved_words cx W3 ms1 HSV1) as [H8 H16].
  apply (gi_chain_at cx ly3 W3 (ms_mem ms1) HB (gi_top _ _ _ Hly3)); [|exact H8 | exact H16].
  intros a Ha. apply JST1; unfold GE_STK, STK_LLVMFuzzerTestOneInput in *; lia. }
prreg HS (8%bv : bv 5) Rs0.
assert (Hsp1o : spZ (ms_regs ms1) = sp0 + (sp1 - sp0)) by (unfold spZ; rewrite Rsp, (EE 2%nat 2%bv eq_refl), R2, unsigned_lit_small by lia; lia).
assert (Hoff : (sp1 - sp0) mod 16 = 0).
{ destruct Hsp1 as [_ H32]. pose proof (Z.div_mod sp1 32 ltac:(lia)). pose proof (Z.div_mod sp0 16 ltac:(lia)).
  replace (sp1 - sp0) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by lia. apply Z_mod_mult. }
(* The malloc wrapper: a block of 460 bytes at t >= 4096, the blocks so far kept. *)
eapply SRr_bind.
{ eapply (AMALLOC4 W3 (ms_regs ms1) (ms_mem ms1) GE_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 _ k 460 (sp1 - sp0) _ (gch cx) HJ1).
  - rewrite Ra0. reflexivity.
  - vm_compute. split; congruence.
  - rewrite (blocks_bytes_bsum B ly3 S3), Hbl, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)). unfold GE_LIVE, LIVE_LIB_B in Hlive. lia.
  - exact Hsp1o.
  - exact Hoff.
  - lia.
  - lia.
  - rewrite Rgp, (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
  - rewrite Rtp, (EE 4%nat 4%bv eq_refl), R4. exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold GE_EV, EV_LIB_B in Hev. lia.
  - apply (achain_chain_pre ly3 _ sp1 sp0 (gch cx) _ HCH1).
    + rewrite Hsp1o. lia.
    + unfold s0Z. rewrite Rs0, (EE 8%nat 8%bv eq_refl), R8. apply unsigned_lit_small. lia.
    + unfold raZ. rewrite Rra, unsigned_lit_small by lia. lia.
  - apply HTR. left. split; [reflexivity|]. unfold raZ. rewrite Rra, unsigned_lit_small by lia.
    replace (BASE + 892 - BASE) with 892 by lia.
    unfold GE_MSITES, TB_LLVMF_MSITES. cbn [In]. left. reflexivity.
  - exact HMOK1. }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & t & -> & HJ5 & HP5 & Ha05 & Hfrs5 & Ht4096 & Ebl5 & HK5 & MLE5).
assert (Hin5 : In (t, 460) (ablocks B ly5 S5)) by (rewrite Ebl5; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ t 460 (proj1 HJ5) Hin5) as (Ht16 & _ & Htceil & Htapp & Htpres & _ & _).
change (req_size 460) with 460 in Htceil, Htapp, Htpres.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Htapp.
pose proof HJ5 as (HAR5 & Hly5 & _ & _ & _ & _ & _ & _ & JST5 & _ & _ & _ & _ & JPRES5 & _).
assert (EFA5 : frame_addr ly5 GE_CID fp = F) by exact (gi_fa _ _ _ _ _ Hly5).
assert (Hfr5 : frames S5 = [(GE_CID, fp)]) by (rewrite Hfrs5; exact HFR).
assert (Hin5f : In (GE_CID, fp) (frames S5)) by (rewrite Hfr5; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR5 Hin5f) as (_ & _ & HFpres5 & HFSpres5).
rewrite EFA5 in HFpres5, HFSpres5. change (fs_frame_bytes GE_CID) with 1024 in HFpres5, HFSpres5.
change (1024 / 8) with 128 in HFSpres5.
destruct (gi_sep_t _ _ _ _ _ _ _ _ _ HAR5 Ebl5 Hfr5) as (Dbl & DtF). rewrite EFA5 in DtF.
pose proof HK5 as (K1 & K2 & K3 & K4 & K5 & K6).
assert (HSHr' : 0x7fff8000 <= SHB /\ SHB + 128 <= 0x10007fff8000) by (unfold SHADOW_OFF in HSHr; lia).
(* No `lia` from here on needs the divisibility facts, the input block's case split Hpn,
   HSHr (HSHr' keeps its bounds), Hsp1d or Hrq: hide them (each `lia` took up to 200 s
   with them in the context). A `lia` that needs DtF, HFapp (the frame in application
   memory) or Htapp (the table in application memory) unhides it in its own goal. *)
destruct Hsp1 as [Hsp1 Hsp1m]. destruct HBASE as (HBASE0 & HBASE1 & HBASEm).
apply rs_hide in HSHr. apply rs_hide in Hsp1d. apply rs_hide in HFapp. apply rs_hide in Htapp.
rs_hide_all.
assert (Hrq : c_n cx <> 0 -> req_size (c_n cx) = c_n cx) by (intros Hn0; unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); rs_lia).
apply rs_hide in Hrq.
(* The bytes the phase keeps, across the malloc wrapper. *)
assert (KP2 : gi_same (gkeep cx fp) W3 mem W5 mem5).
{ intros a Ha. rewrite <- (KP1 a Ha). destruct (gkeep_cat cx fp a G0 Ha) as [Hc|[Hc|[Hc|Hc]]]; fold sp0 sp1 F SHB in Hc.
  - apply K1; [lia|]. intros Hc'. lia.
  - apply (K4 GE_CID fp a Hin3); [right; unfold in_zr; cbn [fst snd]; rewrite EFA; rewrite <- ESH; change (fs_frame_bytes GE_CID / 8) with 128; lia|].
    intros He. cbv beta in He. change (req_size 460) with 460 in He. unfold rs_hold in Htapp. rs_lia.
  - apply (K4 GE_CID fp a Hin3); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes GE_CID) with 1024; lia|].
    intros He. cbv beta in He. change (req_size 460) with 460 in He. unfold rs_hold in DtF. rs_lia.
  - destruct Hc as [Hn0 Hc]. destruct Hpn as [[Hn _]|[_ Hinp]]; [lia|]. rewrite <- Hbl in Hinp.
    pose proof (Dbl _ _ Hinp) as Dp. rewrite (Hrq Hn0) in Dp.
    replace a with (c_p cx + (a - c_p cx)) by lia. apply (K2 _ _ _ Hinp); [rewrite (Hrq Hn0); lia|].
    intros He. cbv beta in He. change (req_size 460) with 460 in He. rs_lia. }
jafter_call_keep_pi HS 32%nat regs5 (mrestrict (w_H W5) mem5) HP5 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. apply (gi_rk E _ WS_I); [vm_compute; reflexivity|].
  - intros a Ha. destruct (wins_I_cases E a sp1 SHB E9u E19u Ha) as [Hs|Hs].
    + split; [apply K1; [lia|]; intros Hc'; lia | apply JPRES5; unfold GE_STK, STK_LLVMFuzzerTestOneInput in *; lia].
    + split.
      * apply (K4 GE_CID fp a Hin3); [right; unfold in_zr; cbn [fst snd]; rewrite EFA; rewrite <- ESH; change (fs_frame_bytes GE_CID / 8) with 128; lia|].
        intros He. cbv beta in He. change (req_size 460) with 460 in He. unfold rs_hold in Htapp. rs_lia.
      * replace a with (shadow_addr F + (a - SHB)) by (rewrite <- ESH; lia). exact (proj1 (HFSpres5 (a - SHB) ltac:(lia))).
  }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 32 (map (getr regs5) CLOB)) as E5 eqn:HE5 in HS.
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (E5o : forall n, (n < 32)%nat -> ew E5 n = ew E n) by (intros n Hn; rewrite HE5; apply YN3v.ew_havoc_old; exact Hn).
assert (E5t : ew E5 36 = w64 t) by (rewrite HE5; cbn; exact Ha05).
clear HE5.
assert (E59 : bv_unsigned (ew E5 9) = sp1) by (rewrite E5o by lia; exact E9u).
assert (E519 : bv_unsigned (ew E5 19) = SHB) by (rewrite E5o by lia; exact E19u).
(* bnez a0: the block is not null, so the abort at 0x81d98 is not reached. *)
paj_run_shc RUNP RUNC HS HJ5.
{ awr_I E59 E519 (HSHF ly5 EFA5). }
rename ms into msb. rename HF into HFb. rename HFr into HFrb. rename HG into HGb. rename mat into matb.
assert (KP3 : gi_same (gkeep cx fp) W3 mem W5 (ms_mem msb))
  by exact (gi_kp_run cx fp E5 _ W3 mem W5 mem5 (ms_mem msb) G0 KP2 HFrb ltac:(vm_compute; reflexivity) E59 E519).
psrr_branch_pi RUNP BR HS.
2:{ exfalso. rewrite branch_ne_U, (U_atom _ 36 t), U_SLit in Hc by (first [exact E5t | lia]).
    change (zcanon 0) with 0 in Hc. destruct (Z.eqb_spec t 0); [lia | discriminate]. }
clear Hc.
(* mv s4,a0; sd s6,0(s1); ld a0,72(s1); addi s2,a0,32; addi s6,a0,240; mv a0,s4; jal reac_headamp_tx_init. *)
paj_run_shc RUNP RUNC HS HJ5.
{ awr_I E59 E519 (HSHF ly5 EFA5). }
lazymatch goal with HS1 : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms5 end.
rename HJ5 into HJ5a. rename HF into HF5. rename HFr into HFr5. rename HG into HG5. rename mat into mat5.
assert (KP4 : gi_same (gkeep cx fp) W3 mem W5 (ms_mem ms5))
  by exact (gi_kp_run cx fp E5 _ W3 mem W5 (ms_mem msb) (ms_mem ms5) G0 KP3 HFr5 ltac:(vm_compute; reflexivity) E59 E519).
assert (HSV5 : gsaved cx W5 ms5) by exact (gi_saved_same cx W3 ms3 W5 ms5 HSAVED (fun a Ha => KP4 a (or_introl Ha))).
pmkst HS. rewrite pa_sigma_reac_headamp_tx_init.
prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
prreg HS (8%bv : bv 5) Qs0. prreg HS (10%bv : bv 5) Qa0.
assert (Qsp' : spZ (ms_regs ms5) = sp0 + (sp1 - sp0))
  by (unfold spZ; rewrite Qsp, E5o, (EE 2%nat 2%bv eq_refl), R2, unsigned_lit_small by lia; lia).
assert (Qs0' : s0Z (ms_regs ms5) = sp0)
  by (unfold s0Z; rewrite Qs0, E5o, (EE 8%nat 8%bv eq_refl), R8 by lia; apply unsigned_lit_small; lia).
assert (HCH5 : achain ly5 (aview SEGS (w_H W5) (ms_mem ms5)) (sp0 + (sp1 - sp0)) (s0Z (ms_regs ms5)) (gch cx)).
{ pose proof HJ5a as (_ & _ & _ & _ & _ & _ & _ & _ & JST5a & _).
  destruct (gsaved_words cx W5 ms5 HSV5) as [H8 H16].
  replace (sp0 + (sp1 - sp0)) with sp1 by lia. rewrite Qs0'.
  apply (gi_chain_at cx ly5 W5 (ms_mem ms5) HB (gi_top _ _ _ Hly5)); [|exact H8 | exact H16].
  intros a Ha. apply JST5a; unfold GE_STK, STK_LLVMFuzzerTestOneInput in *; lia. }
assert (Hfresh : ~ In (t, 460) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hc. rewrite <- Hbl in Hc. pose proof (Dbl _ _ Hc) as D. change (req_size 460) with 460 in D. lia. }
eapply SRr_bind.
{ eapply (cl_callS B LAWS W5 (ms_regs ms5) (ms_mem ms5) _ GE_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly5 S5 _ (k + 1) HeadampTxInit.REAC_HEADAMP_TX_INIT_STK [(t, t + HeadampTxInit.TX_SIZE)] 0 (sp1 - sp0) _ (gch cx)
    (fun ly' S' W' regs' mem' md' => ly' = ly5 /\ S' = S5 /\ W' = W5 /\ Permutation (ablocks B ly' S') (ablocks B ly5 S5) /\
       (forall i, 0 <= i < HeadampTxInit.TX_SIZE -> aview SEGS (w_H W') mem' (t + i) = Some 0)) HJ5a).
  - exact Qsp'.
  - exact Hoff.
  - lia.
  - unfold HeadampTxInit.REAC_HEADAMP_TX_INIT_STK, ESTACK. lia.
  - unfold HeadampTxInit.REAC_HEADAMP_TX_INIT_STK, ESTACK. lia.
  - rewrite Qgp, E5o, (EE 3%nat 3%bv eq_refl), R3 by lia. exact Hgp.
  - rewrite Qtp, E5o, (EE 4%nat 4%bv eq_refl), R4 by lia. exact Htp.
  - reflexivity.
  - rewrite Qra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Qra, unsigned_lit_small by lia. lia.
  - exact HCH5.
  - intros HPRE5. exact (TXI ly5 S5 W5 _ _ _ (gch cx) t HPRE5 (eq_trans Qa0 E5t) Hin5).
  - intros a (r & [<- | []] & Ha). right. exists t, 460. split; [exact Hin5|]. split; [exact Hfresh|].
    cbn [fst snd] in Ha. change (req_size 460) with 460. unfold HeadampTxInit.TX_SIZE in Ha. lia. }
cbv beta. intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HJc6 & HP6 & (-> & -> & -> & Hperm6 & TZ6)).
rewrite Qra.
pose proof HJc6 as (_ & _ & _ & _ & _ & _ & _ & _ & TC1 & TC2 & _ & TC4 & _).
assert (NFP : forall a, ~ (t <= a < t + 460) -> ~ inFP [(t, t + HeadampTxInit.TX_SIZE)] a).
{ intros a Ha Hf. apply inFP_cons in Hf. destruct Hf as [Hf|Hf]; [unfold HeadampTxInit.TX_SIZE in Hf; lia | exact (inFP_nil _ Hf)]. }
(* The bytes the phase keeps, across reac_headamp_tx_init. *)
assert (KP5 : gi_same (gkeep cx fp) W3 mem W5 mem6).
{ intros a Ha. rewrite <- (KP4 a Ha). destruct (gkeep_cat cx fp a G0 Ha) as [Hc|[Hc|[Hc|Hc]]]; fold sp0 sp1 F SHB in Hc.
  - apply TC1; [lia|]. intros Hc'. unfold HeadampTxInit.REAC_HEADAMP_TX_INIT_STK in Hc'. lia.
  - apply (TC4 GE_CID fp a Hin5f); [right; unfold in_zr; cbn [fst snd]; rewrite EFA5, <- ESH; change (fs_frame_bytes GE_CID / 8) with 128; lia|].
    apply NFP. unfold rs_hold in Htapp. rs_lia.
  - apply (TC4 GE_CID fp a Hin5f); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA5; change (fs_frame_bytes GE_CID) with 1024; lia|].
    apply NFP. unfold rs_hold in DtF. rs_lia.
  - destruct Hc as [Hn0 Hc]. destruct Hpn as [[Hn _]|[_ Hinp]]; [lia|]. rewrite <- Hbl in Hinp.
    assert (Hinp5 : In (c_p cx, c_n cx) (ablocks B ly5 S5)) by (rewrite Ebl5; apply in_app_iff; left; exact Hinp).
    pose proof (Dbl _ _ Hinp) as Dp. rewrite (Hrq Hn0) in Dp.
    replace a with (c_p cx + (a - c_p cx)) by lia. apply (TC2 _ _ _ Hinp5 Hinp5); [rewrite (Hrq Hn0); lia|].
    apply NFP. rs_lia. }
jafter_call_keep_pi HS 48%nat regs6 (mrestrict (w_H W5) mem6) HP6 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. apply (gi_rk E5 _ WS_I); [vm_compute; reflexivity|].
  - intros a Ha. split; [|exact (gi_wins_present cx fp ly5 S5 W5 mem6 _ _ E5 HJ6 Hfr5 EFA5 ltac:(unfold GE_STK, STK_LLVMFuzzerTestOneInput in *; lia) ltac:(lia) E59 E519 a Ha)].
    destruct (wins_I_cases E5 a sp1 SHB E59 E519 Ha) as [Hs|Hs].
    + apply TC1; [lia|]. intros Hc'. lia.
    + apply (TC4 GE_CID fp a Hin5f); [right; unfold in_zr; cbn [fst snd]; rewrite EFA5, <- ESH; change (fs_frame_bytes GE_CID / 8) with 128; lia|].
      apply NFP. unfold rs_hold in Htapp. rs_lia.
  }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E5 48 (map (getr regs6) CLOB)) as E6 eqn:HE6 in HS.
assert (HEI6 : img_env VAL A_LIM E6) by (rewrite HE6; apply img_env_havoc; [exact HEI5 | cbv; lia]).
assert (E6o : forall n, (n < 48)%nat -> ew E6 n = ew E5 n) by (intros n Hn; rewrite HE6; apply YN3v.ew_havoc_old; exact Hn).
clear HE6.
assert (E69 : bv_unsigned (ew E6 9) = sp1) by (rewrite E6o by lia; exact E59).
assert (E619 : bv_unsigned (ew E6 19) = SHB) by (rewrite E6o by lia; exact E519).
assert (HF8 : F mod 8 = 0).
{ unfold rs_hold in HF64. replace F with (8 * (F / 64) * 8) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia). apply Z_mod_mult. }
apply rs_hide in HF8.
(* The shadow of `was_set` marked usable, slot 136, and __asan_memset (F + 32, 0, 144). *)
paj_run_shc RUNP RUNC HS HJ6.
{ awr_I E69 E619 (HSHF ly5 EFA5). }
lazymatch goal with HS1 : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms7 end.
rename HJ6 into HJ7a. rename HF into HF7. rename HFr into HFr7. rename HG into HG7. rename mat into mat7.
assert (KP6 : gi_same (gkeep cx fp) W3 mem W5 (ms_mem ms7))
  by exact (gi_kp_run cx fp E6 _ W3 mem W5 mem6 (ms_mem ms7) G0 KP5 HFr7 ltac:(vm_compute; reflexivity) E69 E619).
assert (T7 : forall i, 0 <= i < 460 -> aview SEGS (w_H W5) (ms_mem ms7) (t + i) = Some 0).
{ intros i Hi. rewrite (gi_run_keep E6 _ WS_I _ _ _ HFr7 ltac:(vm_compute; reflexivity) (t + i) ltac:(lia)).
  - apply TZ6. unfold HeadampTxInit.TX_SIZE. lia.
  - unfold rs_hold in Htapp. apply (not_in_WS_I E6 (t + i) sp1 SHB E69 E619); rs_lia. }
pmkst HS.
prreg HS (1%bv : bv 5) Mra. prreg HS (2%bv : bv 5) Msp. prreg HS (3%bv : bv 5) Mgp. prreg HS (4%bv : bv 5) Mtp.
prreg HS (10%bv : bv 5) Ma0. prreg HS (11%bv : bv 5) Ma1. prreg HS (12%bv : bv 5) Ma2.
assert (WSH1 : forall o, 4 <= o < 22 -> aview SEGS (w_H W5) (ms_mem ms7) (SHB + o) = Some 0).
{ pose proof (st_ok_region_nth E6 _ _ 4%nat _ HS eq_refl) as RG4. cbn [ms_mem restrict mkst] in RG4.
  intros o Ho. exact (gi_zero_range E6 (w_H W5) (ms_mem ms7) 19 SHB _ _ _ _ _ 4 18 RG4 E619
    ltac:(vm_compute; reflexivity) o ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)). }
eapply SRr_bind.
{ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA GS___asan_memset) AMEMSET W5 (ms_regs ms7) (ms_mem ms7)
    GE_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly5 S5 _ _ (F + 32) 0 144 (sp1 - sp0) _ HJ7a).
  - rewrite Ma0. cbn [sv_denot]. rewrite E6o, E5o, (EE 21%nat 21%bv eq_refl), R21 by lia.
    unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - rewrite Ma1. reflexivity.
  - rewrite Ma2. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite Msp, E6o, E5o, (EE 2%nat 2%bv eq_refl), R2 by lia. rewrite unsigned_lit_small by lia. lia.
  - exact Hoff.
  - lia.
  - lia.
  - rewrite Mgp, E6o, E5o, (EE 3%nat 3%bv eq_refl), R3 by lia. exact Hgp.
  - rewrite Mtp, E6o, E5o, (EE 4%nat 4%bv eq_refl), R4 by lia. exact Htp.
  - exact Mra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [|lia]. right. right. right. exists GE_CID, fp. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA5. change (fs_frame_bytes GE_CID) with 1024. lia.
  - unfold rs_hold in HFapp. unfold amem_range. rewrite C4, C5. unfold kHighMemBeg. rs_lia.
  - intros x Hx. exists 0. split; [|left; reflexivity]. rewrite (gi_sh_of F x HF8), <- ESH. apply WSH1. split.
    + apply Z.div_le_lower_bound; lia.
    + apply Z.div_lt_upper_bound; lia.
  - intros _ s Hs. replace (F + 32 + 144 - 1) with (F + 8 * 21 + 7) in Hs by lia.
    replace (F + 32) with (F + 8 * 4) in Hs by lia.
    apply (gi_hull_rng F 4 21 s HF64 ltac:(lia) ltac:(lia) ltac:(lia)) in Hs. rewrite <- ESH in Hs.
    change (4 / 8 * 8) with 0 in Hs. change (21 / 8 * 8) with 16 in Hs.
    destruct (Z_lt_le_dec (s - SHB) 4) as [Hl|Hl]; [|destruct (Z_lt_le_dec (s - SHB) 22) as [Hm|Hm]].
    + rewrite (KP6 s ltac:(unfold gkeep; right; right; right; left; fold SHB; lia)).
      replace s with (SHB + Z.of_nat (Z.to_nat (s - SHB))) by lia. replace (aview SEGS (w_H W3) mem (SHB + Z.of_nat (Z.to_nat (s - SHB)))) with (Some (nth (Z.to_nat (s - SHB)) GSH_entry 0))
        by (symmetry; exact (HSH (Z.to_nat (s - SHB)) ltac:(rewrite HLEN; unfold GE_NSH; lia))). discriminate.
    + replace s with (SHB + (s - SHB)) by lia. rewrite (WSH1 (s - SHB) ltac:(lia)). discriminate.
    + rewrite (KP6 s ltac:(unfold gkeep; right; right; right; right; left; fold SHB; lia)).
      replace s with (SHB + Z.of_nat (Z.to_nat (s - SHB))) by lia. replace (aview SEGS (w_H W3) mem (SHB + Z.of_nat (Z.to_nat (s - SHB)))) with (Some (nth (Z.to_nat (s - SHB)) GSH_entry 0))
        by (symmetry; exact (HSH (Z.to_nat (s - SHB)) ltac:(rewrite HLEN; unfold GE_NSH; lia))). discriminate.
  - exact I. }
cbv beta. intros W8 c8 Hwle8 (-> & regs8 & mem8 & md8 & -> & HJ8 & HP8 & Ha08 & Heff8 & Hfr8 & Hpres8).
assert (KP7 : gi_same (gkeep cx fp) W3 mem W5 mem8).
{ intros a Ha. rewrite <- (KP6 a Ha). destruct (gkeep_win cx fp a G0 Ha) as (Ha64 & _ & _ & _ & _ & _ & _ & N7 & _ & N9).
  fold sp0 sp1 F SHB in N7, N9. apply Hfr8; [exact Ha64 | rs_lia | rs_lia]. }
assert (T8 : forall i, 0 <= i < 460 -> aview SEGS (w_H W5) mem8 (t + i) = Some 0).
{ intros i Hi. unfold rs_hold in DtF. rewrite Hfr8; [exact (T7 i Hi) | rs_lia | rs_lia | rs_lia]. }
jafter_call_keep_pi HS 64%nat regs8 (mrestrict (w_H W5) mem8) HP8 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. apply (gi_rk E6 _ WS_I); [vm_compute; reflexivity|].
  - intros a Ha. split; [|exact (gi_wins_present cx fp ly5 S5 W5 mem8 _ _ E6 HJ8 Hfr5 EFA5 ltac:(unfold GE_STK, STK_LLVMFuzzerTestOneInput in *; lia) ltac:(lia) E69 E619 a Ha)].
    unfold rs_hold in HFapp. destruct (wins_I_cases E6 a sp1 SHB E69 E619 Ha) as [Hs|Hs]; apply Hfr8; rs_lia.
  }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E6 64 (map (getr regs8) CLOB)) as E8 eqn:HE8 in HS.
assert (HEI8 : img_env VAL A_LIM E8) by (rewrite HE8; apply img_env_havoc; [exact HEI6 | cbv; lia]).
assert (E8o : forall n, (n < 64)%nat -> ew E8 n = ew E6 n) by (intros n Hn; rewrite HE8; apply YN3v.ew_havoc_old; exact Hn).
clear HE8.
assert (E89 : bv_unsigned (ew E8 9) = sp1) by (rewrite E8o by lia; exact E69).
assert (E819 : bv_unsigned (ew E8 19) = SHB) by (rewrite E8o by lia; exact E619).
(* The shadow of `set_to` marked usable, slot 128, and __asan_memset (F + 240, 0, 144). *)
paj_run_shc RUNP RUNC HS HJ8.
{ awr_I E89 E819 (HSHF ly5 EFA5). }
lazymatch goal with HS1 : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms9 end.
rename HJ8 into HJ9a. rename HF into HF9. rename HFr into HFr9. rename HG into HG9. rename mat into mat9.
assert (KP8 : gi_same (gkeep cx fp) W3 mem W5 (ms_mem ms9))
  by exact (gi_kp_run cx fp E8 _ W3 mem W5 mem8 (ms_mem ms9) G0 KP7 HFr9 ltac:(vm_compute; reflexivity) E89 E819).
assert (T9 : forall i, 0 <= i < 460 -> aview SEGS (w_H W5) (ms_mem ms9) (t + i) = Some 0).
{ intros i Hi. rewrite (gi_run_keep E8 _ WS_I _ _ _ HFr9 ltac:(vm_compute; reflexivity) (t + i) ltac:(lia)).
  - exact (T8 i Hi).
  - unfold rs_hold in Htapp. apply (not_in_WS_I E8 (t + i) sp1 SHB E89 E819); rs_lia. }
assert (A9 : forall i, 0 <= i < 144 -> aview SEGS (w_H W5) (ms_mem ms9) (F + 32 + i) = Some (0 mod 256)).
{ intros i Hi. rewrite (gi_run_keep E8 _ WS_I _ _ _ HFr9 ltac:(vm_compute; reflexivity) (F + 32 + i) ltac:(lia)).
  - exact (Heff8 i Hi).
  - unfold rs_hold in HFapp. apply (not_in_WS_I E8 (F + 32 + i) sp1 SHB E89 E819); rs_lia. }
pmkst HS.
prreg HS (1%bv : bv 5) Nra. prreg HS (2%bv : bv 5) Nsp. prreg HS (3%bv : bv 5) Ngp. prreg HS (4%bv : bv 5) Ntp.
prreg HS (10%bv : bv 5) Na0. prreg HS (11%bv : bv 5) Na1. prreg HS (12%bv : bv 5) Na2.
assert (WSH2 : forall o, 30 <= o < 48 -> aview SEGS (w_H W5) (ms_mem ms9) (SHB + o) = Some 0).
{ pose proof (st_ok_region_nth E8 _ _ 5%nat _ HS eq_refl) as RG5. cbn [ms_mem restrict mkst] in RG5.
  intros o Ho. exact (gi_zero_range E8 (w_H W5) (ms_mem ms9) 19 SHB _ _ _ _ _ 30 18 RG5 E819
    ltac:(vm_compute; reflexivity) o ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)). }
eapply SRr_bind.
{ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA GS___asan_memset) AMEMSET W5 (ms_regs ms9) (ms_mem ms9)
    GE_STK sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly5 S5 _ _ (F + 240) 0 144 (sp1 - sp0) _ HJ9a).
  - rewrite Na0. cbn [sv_denot]. rewrite E8o, E6o, E5o, (EE 21%nat 21%bv eq_refl), R21 by lia.
    unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - rewrite Na1. reflexivity.
  - rewrite Na2. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite Nsp, E8o, E6o, E5o, (EE 2%nat 2%bv eq_refl), R2 by lia. rewrite unsigned_lit_small by lia. lia.
  - exact Hoff.
  - lia.
  - lia.
  - rewrite Ngp, E8o, E6o, E5o, (EE 3%nat 3%bv eq_refl), R3 by lia. exact Hgp.
  - rewrite Ntp, E8o, E6o, E5o, (EE 4%nat 4%bv eq_refl), R4 by lia. exact Htp.
  - exact Nra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [|lia]. right. right. right. exists GE_CID, fp. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA5. change (fs_frame_bytes GE_CID) with 1024. lia.
  - unfold rs_hold in HFapp. unfold amem_range. rewrite C4, C5. unfold kHighMemBeg. rs_lia.
  - intros x Hx. exists 0. split; [|left; reflexivity]. rewrite (gi_sh_of F x HF8), <- ESH. apply WSH2. split.
    + apply Z.div_le_lower_bound; lia.
    + apply Z.div_lt_upper_bound; lia.
  - intros _ s Hs. replace (F + 240 + 144 - 1) with (F + 8 * 47 + 7) in Hs by lia.
    replace (F + 240) with (F + 8 * 30) in Hs by lia.
    apply (gi_hull_rng F 30 47 s HF64 ltac:(lia) ltac:(lia) ltac:(lia)) in Hs. rewrite <- ESH in Hs.
    change (30 / 8 * 8) with 24 in Hs. change (47 / 8 * 8) with 40 in Hs.
    destruct (Z_lt_le_dec (s - SHB) 30) as [Hl|Hl].
    + rewrite (KP8 s ltac:(unfold gkeep; right; right; right; right; left; fold SHB; lia)).
      replace s with (SHB + Z.of_nat (Z.to_nat (s - SHB))) by lia. replace (aview SEGS (w_H W3) mem (SHB + Z.of_nat (Z.to_nat (s - SHB)))) with (Some (nth (Z.to_nat (s - SHB)) GSH_entry 0))
        by (symmetry; exact (HSH (Z.to_nat (s - SHB)) ltac:(rewrite HLEN; unfold GE_NSH; lia))). discriminate.
    + replace s with (SHB + (s - SHB)) by lia. rewrite (WSH2 (s - SHB) ltac:(lia)). discriminate.
  - exact I. }
cbv beta. intros W10 c10 Hwle10 (-> & regs10 & mem10 & md10 & -> & HJ10 & HP10 & Ha010 & Heff10 & Hfr10 & Hpres10).
assert (KP9 : gi_same (gkeep cx fp) W3 mem W5 mem10).
{ intros a Ha. rewrite <- (KP8 a Ha). destruct (gkeep_win cx fp a G0 Ha) as (Ha64 & _ & _ & _ & _ & _ & _ & _ & N8 & N9).
  fold sp0 sp1 F SHB in N8, N9. apply Hfr10; [exact Ha64 | rs_lia | rs_lia]. }
assert (T10 : forall i, 0 <= i < 460 -> aview SEGS (w_H W5) mem10 (t + i) = Some 0).
{ intros i Hi. unfold rs_hold in DtF. rewrite Hfr10; [exact (T9 i Hi) | rs_lia | rs_lia | rs_lia]. }
assert (A10 : forall i, 0 <= i < 144 -> aview SEGS (w_H W5) mem10 (F + 32 + i) = Some (0 mod 256)).
{ intros i Hi. rewrite Hfr10; [exact (A9 i Hi) | lia | lia | lia]. }
jafter_call_keep_pi HS 80%nat regs10 (mrestrict (w_H W5) mem10) HP10 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. apply (gi_rk E8 _ WS_I); [vm_compute; reflexivity|].
  - intros a Ha. split; [|exact (gi_wins_present cx fp ly5 S5 W5 mem10 _ _ E8 HJ10 Hfr5 EFA5 ltac:(unfold GE_STK, STK_LLVMFuzzerTestOneInput in *; lia) ltac:(lia) E89 E819 a Ha)].
    unfold rs_hold in HFapp. destruct (wins_I_cases E8 a sp1 SHB E89 E819 Ha) as [Hs|Hs]; apply Hfr10; rs_lia.
  }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E8 80 (map (getr regs10) CLOB)) as E10 eqn:HE10 in HS.
assert (HEI10 : img_env VAL A_LIM E10) by (rewrite HE10; apply img_env_havoc; [exact HEI8 | cbv; lia]).
assert (E10o : forall n, (n < 80)%nat -> ew E10 n = ew E8 n) by (intros n Hn; rewrite HE10; apply YN3v.ew_havoc_old; exact Hn).
clear HE10.
assert (E10E : forall n, (n < 32)%nat -> ew E10 n = ew E n) by (intros n Hn; rewrite E10o, E8o, E6o, E5o by lia; reflexivity).
assert (E109 : bv_unsigned (ew E10 9) = sp1) by (rewrite E10E by lia; exact E9u).
assert (E1019 : bv_unsigned (ew E10 19) = SHB) by (rewrite E10E by lia; exact E19u).
(* Slots 152, 8 and 32, up to the test of the bytes left, beqz s7 at 0x80ea0. *)
paj_run_shc RUNP RUNC HS HJ10.
{ awr_I E109 E1019 (HSHF ly5 EFA5). }
rename ms into msF. rename HF into HFF. rename HFr into HFrF. rename HG into HGF. rename mat into matF.
assert (KPF : gi_same (gkeep cx fp) W3 mem W5 (ms_mem msF))
  by exact (gi_kp_run cx fp E10 _ W3 mem W5 mem10 (ms_mem msF) G0 KP9 HFrF ltac:(vm_compute; reflexivity) E109 E1019).
assert (TF : forall i, 0 <= i < 460 -> aview SEGS (w_H W5) (ms_mem msF) (t + i) = Some 0).
{ intros i Hi. rewrite (gi_run_keep E10 _ WS_I _ _ _ HFrF ltac:(vm_compute; reflexivity) (t + i) ltac:(lia)).
  - exact (T10 i Hi).
  - unfold rs_hold in Htapp. apply (not_in_WS_I E10 (t + i) sp1 SHB E109 E1019); rs_lia. }
assert (AF : forall i, 0 <= i < 144 -> aview SEGS (w_H W5) (ms_mem msF) (F + 32 + i) = Some (0 mod 256)).
{ intros i Hi. rewrite (gi_run_keep E10 _ WS_I _ _ _ HFrF ltac:(vm_compute; reflexivity) (F + 32 + i) ltac:(lia)).
  - exact (A10 i Hi).
  - unfold rs_hold in HFapp. apply (not_in_WS_I E10 (F + 32 + i) sp1 SHB E109 E1019); rs_lia. }
assert (BF : forall i, 0 <= i < 144 -> aview SEGS (w_H W5) (ms_mem msF) (F + 240 + i) = Some (0 mod 256)).
{ intros i Hi. rewrite (gi_run_keep E10 _ WS_I _ _ _ HFrF ltac:(vm_compute; reflexivity) (F + 240 + i) ltac:(lia)).
  - exact (Heff10 i Hi).
  - unfold rs_hold in HFapp. apply (not_in_WS_I E10 (F + 240 + i) sp1 SHB E109 E1019); rs_lia. }
(* The cut at 0x80ea0: the registers, the slots and the frame's shadow as gi_mid wants them. *)
norm_ss HS.
pose proof (st_ok_pi_restrict_mkst (w_H W5) E10 _ msF HS eq_refl) as EmsF. cbn [ss_pc] in EmsF.
prreg HS (2%bv : bv 5) Z2. prreg HS (8%bv : bv 5) Z8. prreg HS (9%bv : bv 5) Z9. prreg HS (3%bv : bv 5) Z3.
prreg HS (4%bv : bv 5) Z4. prreg HS (19%bv : bv 5) Z19. prreg HS (20%bv : bv 5) Z20. prreg HS (21%bv : bv 5) Z21.
prreg HS (23%bv : bv 5) Z23. prreg HS (24%bv : bv 5) Z24.
pose proof (st_ok_pi_region_nth E10 _ _ 0%nat _ HS eq_refl) as RF0.
pose proof (st_ok_pi_region_nth E10 _ _ 1%nat _ HS eq_refl) as RF1.
pose proof (st_ok_pi_region_nth E10 _ _ 2%nat _ HS eq_refl) as RF2.
pose proof (st_ok_pi_region_nth E10 _ _ 3%nat _ HS eq_refl) as RF3.
pose proof (st_ok_pi_region_nth E10 _ _ 4%nat _ HS eq_refl) as RF4.
pose proof (st_ok_pi_region_nth E10 _ _ 5%nat _ HS eq_refl) as RF5.
cbn [ms_mem restrict] in RF0, RF1, RF2, RF3, RF4, RF5.
assert (GEO : gi_geo cx fp t).
{ unfold gi_geo. fold sp0 sp1 F SHB.
  assert (Hcp : 0 <= c_p cx /\ (c_n cx = 0 \/ c_p cx + c_n cx <= sp1) /\ c_p cx + c_n cx <= 2 ^ 47).
  { destruct Hpn as [[Hn0 Hp0] | [Hn Hinp]]; [rewrite Hn0, Hp0; unfold GE_EMPTY, A_EMPTY_B; lia|].
    rewrite <- Hbl in Hinp. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinp) as (_ & Hp4 & Hpce & _).
    rewrite (Hrq ltac:(lia)) in Hpce. lia. }
  rs_lia. }
apply (gi_mid POST HSET HUNS cx fp _ _ ly5 S5 W5 msF _ t HB HJ10 Hfr5 (mle_station MT _ _ _ _ _ MTL HMLE MLE5));
  [lia | unfold GE_A1; lia | unfold gblk1; rewrite Ebl5, Hbl; reflexivity | exact Hn26 | exact GEO |].
split; [|split].
- unfold gi_pc. rewrite EmsF. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
  repeat split; reflexivity.
- unfold gi_regs, gregs.
  rewrite Z2, Z8, Z9, Z3, Z4, Z19, Z21, Z23, Z24, !E10E by lia.
  rewrite (EE 2%nat 2%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 9%nat 9%bv eq_refl), (EE 3%nat 3%bv eq_refl),
    (EE 4%nat 4%bv eq_refl), (EE 19%nat 19%bv eq_refl), (EE 21%nat 21%bv eq_refl),
    (EE 23%nat 23%bv eq_refl), (EE 24%nat 24%bv eq_refl).
  rewrite Z20, E10o, E8o, E6o by lia. rewrite E5t.
  unfold ge_hdr. repeat split; assumption.
- split; [exact (gi_saved_same cx W3 ms3 W5 msF HSAVED (fun a Ha => KPF a (or_introl Ha)))|].
  split.
  { intros i Hi. change (length GSH_tables) with 104%nat in Hi.
    destruct (Nat.lt_ge_cases i 4) as [H1|H1]; [|destruct (Nat.lt_ge_cases i 22) as [H2|H2]];
    [| | destruct (Nat.lt_ge_cases i 30) as [H3|H3]; [|destruct (Nat.lt_ge_cases i 48) as [H4|H4]]].
    - rewrite (gsh_tables_nth2 i ltac:(lia) ltac:(lia)).
      rewrite (KPF (gSH cx fp + Z.of_nat i) ltac:(unfold gkeep; right; right; right; left; fold SHB; lia)). apply HSH. rewrite HLEN. unfold GE_NSH. lia.
    - rewrite (gsh_tables_nth1 i ltac:(lia)).
      exact (gi_zero_range E10 (w_H W5) (ms_mem msF) 19 SHB _ _ _ _ _ 4 18 RF4 E1019
        ltac:(vm_compute; reflexivity) (Z.of_nat i) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
    - rewrite (gsh_tables_nth2 i ltac:(lia) ltac:(lia)).
      rewrite (KPF (gSH cx fp + Z.of_nat i) ltac:(unfold gkeep; right; right; right; right; left; fold SHB; lia)). apply HSH. rewrite HLEN. unfold GE_NSH. lia.
    - rewrite (gsh_tables_nth1 i ltac:(lia)).
      exact (gi_zero_range E10 (w_H W5) (ms_mem msF) 19 SHB _ _ _ _ _ 30 18 RF5 E1019
        ltac:(vm_compute; reflexivity) (Z.of_nat i) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
    - rewrite (gsh_tables_nth2 i ltac:(lia) ltac:(lia)).
      rewrite (KPF (gSH cx fp + Z.of_nat i) ltac:(unfold gkeep; right; right; right; right; right; left; fold SHB; lia)). apply HSH. rewrite HLEN. unfold GE_NSH. lia. }
  split; [rewrite (rdword_ext (aview SEGS (w_H W3) mem)); [exact HFLAG|];
    intros kk Hkk; apply KPF; unfold gkeep; right; right; right; right; right; right; left; fold F; lia|].
  split; [eapply (garr8_aview_kept SEGS (w_H W3) (w_H W5) mem (ms_mem msF)); [|exact HINP];
    intros a Ha; rewrite length_map in Ha; fold (c_n cx) in Ha; apply KPF; unfold gkeep; do 7 right; lia|].
  split.
  { unfold gi_slots. split.
    { unfold gslot. apply (gi_slot8 E10 (w_H W5) (ms_mem msF) 9 sp1 _ _ _ _ _ 0 (SOff 22 0) _ RF0 E109); [cbn; tauto | | unfold ge_hdr; lia].
      rewrite gi_sv0, E10E, (EE 22%nat 22%bv eq_refl), R22 by lia. reflexivity. }
    split.
    { unfold gslot. apply (gi_slot8 E10 (w_H W5) (ms_mem msF) 9 sp1 _ _ _ _ _ 8 (SOff 21 0) _ RF0 E109); [cbn; tauto | | lia].
      rewrite gi_sv0, E10E, (EE 21%nat 21%bv eq_refl), R21 by lia. reflexivity. }
    split; [apply (gi_slot_move cx W3 ms3 W5 msF 24 _ SL24); intros i Hi; apply KPF; unfold gkeep; right; left; fold sp1; lia|].
    split.
    { unfold gslot. apply (gi_slot8 E10 (w_H W5) (ms_mem msF) 9 sp1 _ _ _ _ _ 32 (SOff 25 0) _ RF1 E109); [cbn; tauto | | unfold ge_hdr; lia].
      rewrite gi_sv0, E10E, (EE 25%nat 25%bv eq_refl), R25 by lia. reflexivity. }
    split.
    { unfold gslot. apply (gi_slot8 E10 (w_H W5) (ms_mem msF) 9 sp1 _ _ _ _ _ 72 (SOff 21 0) _ RF2 E109); [cbn; tauto | | lia].
      rewrite gi_sv0, E10E, (EE 21%nat 21%bv eq_refl), R21 by lia. reflexivity. }
    split; [apply (gi_slot_move cx W3 ms3 W5 msF 88 _ SL88); intros i Hi; apply KPF; unfold gkeep; right; right; left; fold sp1; lia|].
    split.
    { unfold gslot. apply (gi_slot8 E10 (w_H W5) (ms_mem msF) 9 sp1 _ _ _ _ _ 128 (SOff 21 240) _ RF3 E109); [cbn; tauto | | unfold GO_SET; lia].
      cbn [sv_denot]. rewrite E10E, (EE 21%nat 21%bv eq_refl), R21 by lia. unfold w64. rewrite unsigned_lit_small by lia. unfold GO_SET. reflexivity. }
    split.
    { unfold gslot. apply (gi_slot8 E10 (w_H W5) (ms_mem msF) 9 sp1 _ _ _ _ _ 136 (SOff 21 32) _ RF3 E109); [cbn; tauto | | unfold GO_WAS; lia].
      cbn [sv_denot]. rewrite E10E, (EE 21%nat 21%bv eq_refl), R21 by lia. unfold w64. rewrite unsigned_lit_small by lia. unfold GO_WAS. reflexivity. }
    split.
    { unfold gslot. apply (gi_slot8 E10 (w_H W5) (ms_mem msF) 9 sp1 _ _ _ _ _ 144 (SLit SHADOW_OFF) _ RF3 E109); [cbn; tauto | reflexivity | unfold SHADOW_OFF; lia]. }
    { unfold gslot. apply (gi_slot8 E10 (w_H W5) (ms_mem msF) 9 sp1 _ _ _ _ _ 152 (SOff 36 0) _ RF3 E109); [cbn; tauto | | lia].
      rewrite gi_sv0, E10o, E8o, E6o by lia. rewrite E5t. reflexivity. } }
  split.
  { split; [exact Hin5|]. split; [lia|]. split; [reflexivity|].
    intros i Hi _ _ _. rewrite (TF i Hi). unfold HeadampModel.tb, GrantSlotPlan.T0. rewrite nth_repeat. reflexivity. }
  split.
  { unfold gfarr, GO_WAS. change (map (fun b : byte => bv_unsigned b) GrantSlotPlan.Z144) with (repeat (0 mod 256) (Z.to_nat 144)).
    apply (garr8_of_memset SEGS (w_H W5) (ms_mem msF) (F + 32) 0 144); [lia | exact AF]. }
  { unfold gfarr, GO_SET. change (map (fun b : byte => bv_unsigned b) GrantSlotPlan.Z144) with (repeat (0 mod 256) (Z.to_nat 144)).
    apply (garr8_of_memset SEGS (w_H W5) (ms_mem msF) (F + 240) 0 144); [lia | exact BF]. }
Qed.

End c.
End b.
End a.
