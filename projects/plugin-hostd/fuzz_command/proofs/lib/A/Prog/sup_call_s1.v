(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of sup_call's ASan walk (plugin-hostd/fuzz_command), in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v: the symbolic entry state of sup_call (0x8a95c) with its seed, the
   call slot of g_rec's table, and the per-binary facts the walk reads of the program's statics. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaSB PaDenot PaLibG PaLibH PaCall CmdBase CmdRep CmdObj CmdZsh CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecCells.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* aval_mem over aview and YI04's val_mem over the restricted memory are the same statement; the two read
   le_byte from two copies of the same definition (YG0f, YO0f). *)
Lemma sc_le_byte_range : forall v n k, 0 <= YO0f.le_byte v n k < 256.
Proof. intros v n k. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma sc_val_mem_of_aval : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; cbn in Hv; [|discriminate].
injection Hv as Hb. f_equal. change (YO0f.le_byte v n k) with (YG0f.le_byte v n k). rewrite <- Hb.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma sc_aval_of_val_mem : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by apply sc_le_byte_range. reflexivity.
Qed.

(* the call slot the record is written into: a slot of g_rec's table, or record.spill *)
Definition sc_slot (c : Z) : Prop :=
(exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL.

Lemma sc_slot_facts : forall c, sc_slot c ->
c mod 8 = 0 /\ A_G_REC + 16 <= c /\ c + 56 <= A_REC_SPILL + 56 /\ (forall a, c <= a < c + 56 -> inFP cmd_PG a).
Proof.
unfold sc_slot, cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX.
intros c [(i & Hi & ->) | ->].
- split; [|split; [lia | split; [lia|]]].
  + replace (6174528 + 16 + 56 * i) with ((771818 + 7 * i) * 8) by lia. apply Z_mod_mult.
  + intros a Ha. exists (6174528, 6174528 + 960). split; [left; reflexivity | cbn [fst snd]; lia].
- split; [reflexivity|]. split; [lia|]. split; [lia|].
  intros a Ha. exists (6175712, 6175712 + 56). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* The symbolic state at sup_call's entry. Atoms 0..31 are the entry registers (a0 = id is atom 10, a1 = line is
   atom 11, sp is atom 2), atom 32 is the shadow base, A_OBJ 0 / A_OBJ 12 are the GOT word of the shadow base and
   the cell, A_OBJ 44 is g_rec. Regions: the 48-byte frame below the entry sp, the GOT word and the cell
   (read-only), and g_rec's ncalls field [g_rec + 8, g_rec + 12), writable, holding n. The function makes no
   inline check before the join at 0x8a9d0, so the entry token list is empty. *)
Definition sc_Bx : sv := SOff 32 0.
Definition sc_SH : list shent := [].
Definition sc_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition sc_extra : list word := map (Z_to_bv 64) [SB].
Definition sc_E (regs : bvmap 5 word) : env := Eimg (Ereg regs sc_extra).
Definition sc_ncalls (n : Z) : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) 8 12 8 12 [YP09.mkChunk 8 (CVal 4 (SLit n))].
Definition sc_regions (n : Z) : smem :=
[stack_region 48; got_regionP; bcell_regionP 32; sc_ncalls n].
Definition sc_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0)] [] [].
Definition sc_ss (n : Z) : sstate := mkSS AF_sup_call sr_atoms (sc_regions n) None sc_facts.

Section e.
Variable B : asyms.
(* the per-binary facts *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis VOBJS : cmd_val_objs.
(* the core's prog_rw: CmdRecCells' PROG_WRITABLE SEGS B LAWS HB PRW *)
Hypothesis PRW : prog_rw SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

Lemma sc_obj0 : VAL (A_OBJ 0) = 0xa63f0.
Proof. rewrite (VOBJS 0%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sc_obj12 : VAL (A_OBJ 12) = 0xb10b8.
Proof. rewrite (VOBJS 12%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sc_obj44 : VAL (A_OBJ 44) = A_G_REC.
Proof. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sc_obj51 : VAL (A_OBJ 51) = A_REC_SPILL.
Proof. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sc_obj42 : VAL (A_OBJ 42) = 0x21ce0.
Proof. rewrite (VOBJS 42%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* HPROG: every byte of g_rec, record.spill and g_quitting is one of the program's writable statics. It is
   CmdBSyms' ts_prog (lib/A/AF0m.v), so a lemma, not a hypothesis. *)
Lemma HPROG : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a (r & Hin & Hr). rewrite (ts_prog B HB). unfold cmd_PG in Hin. unfold TFIB_PROG_STATIC.
cbn [In] in Hin. unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* a byte of the program's statics is writable at every AR state *)
Lemma sc_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> inFP cmd_PG a -> writable_at SEGS (mrestrict (w_H W) mem) a.
Proof.
intros ly S W mem md a _ Ha. exact (PROG_WRITABLE SEGS B LAWS HB PRW _ a Ha).
Qed.

(* the shadow of a call slot: g_rec's table lies in the record's zero-shadow range [0xada00, 0x5e3b00) and
   record.spill is a zero-shadow range of its own [0x5e3be0, 0x5e3c18) (lib/A/AF0m.v, Tfib_zero_shadow 133, 134) *)
Lemma sc_slot_addressable : forall ly S (W : world SEGS) mem md c a n,
AR SEGS B ly S W mem md -> sc_slot c -> c <= a -> a + n <= c + 56 ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md c a n HAR Hsl Ha Hn.
destruct Hsl as [(i & Hi & ->) | ->].
- assert (HIN : In (0xada00, 0x5e3b00 - 0xada00) Tfib_zero_shadow)
    by (apply (nth_error_In _ 133%nat); vm_compute; reflexivity).
  apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00) a n HAR HIN);
  [reflexivity | reflexivity | cbn [fst snd] | cbn [fst snd]];
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX in *; lia.
- assert (HIN : In (A_REC_SPILL, 0x5e3c18 - A_REC_SPILL) Tfib_zero_shadow)
    by (apply (nth_error_In _ 134%nat); vm_compute; reflexivity).
  apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (A_REC_SPILL, 0x5e3c18 - A_REC_SPILL) a n HAR HIN);
  [reflexivity | reflexivity | cbn [fst snd]; lia | cbn [fst snd]; unfold A_REC_SPILL in *; lia].
Qed.

(* The entry state: the registers are their own atoms, the frame is the 48 bytes below the entry sp, the GOT word
   and the cell carry the shadow base, and g_rec's ncalls field holds n. *)
Lemma sc_entry : forall W ly S (regs : bvmap 5 word) mem md ch (n : Z),
afn_pre SEGS B SUP_CALL_STK ly S W regs mem md ch ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n -> 0 <= n <= 16 ->
st_ok_pi SEGS VAL (sc_E regs) (sc_ss n)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_call)) mem (seg_rom SEGS)))
/\ sh_ok SEGS sc_Bx sc_SH (sc_E regs) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch n HPRE Hn Hn16.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := sc_E regs). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; unfold sc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; unfold sc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E240 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold sc_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E252 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold sc_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E284 : ew E (A_OBJ 44) = Z_to_bv 64 (VAL (A_OBJ 44)))
  by (subst E; unfold sc_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof sc_obj0 as V0. pose proof sc_obj12 as V12. pose proof sc_obj44 as V44.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (HW : forall o, 8 <= o < 12 -> writable_at SEGS (mrestrict (w_H W) mem) (A_G_REC + o)).
{ intros o Ho. apply (sc_prog_writable ly S W mem md); [exact HAR|].
  exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia]. }
assert (CK : YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) A_G_REC (YP09.mkChunk 8 (CVal 4 (SLit n)))).
{ apply (chunk_ok_val SEGS E _ A_G_REC 8 4 (SLit n) n); [reflexivity | cbn; lia | lia |].
  exact (sc_val_mem_of_aval SEGS (w_H W) mem (A_G_REC + OFF_NCALLS) 4 n Hn). }
assert (RG : forall r, In r [got_regionP; bcell_regionP 32] -> YP09.region_ok SEGS E (mrestrict (w_H W) mem) r).
{ intros r [<- | [<- | []]]; unfold region_ok, got_regionP, bcell_regionP;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  - rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E240) by (rewrite V0; lia). split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E252, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | rewrite V12; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E252) by (rewrite V12; lia). split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 sc_Bx SB);
    [cbn [sv_denot sc_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell). }
assert (WS : 48 <= SUP_CALL_STK) by (vm_compute; intros Hx; discriminate Hx).
assert (RS : YP09.region_ok SEGS E (mrestrict (w_H W) mem) (stack_region 48)).
{ unfold region_ok, stack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
assert (RN : YP09.region_ok SEGS E (mrestrict (w_H W) mem) (sc_ncalls n)).
{ unfold region_ok, sc_ncalls.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 44) (VAL (A_OBJ 44)) E284) by (rewrite V44; unfold A_G_REC; lia).
  rewrite V44. unfold A_G_REC. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply HW; lia|].
  constructor; [exact CK | constructor]. }
assert (HG : facts_ok E sc_facts).
{ split; [|split; [exact I | exact I]].
  cbn [sc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hal16 C1 Hstk0. clear. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
split; [|unfold sh_ok, sc_SH; apply Forall_nil].
unfold sc_ss. apply pa_entry_st_ok_full.
- subst E. unfold sc_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sc_regions. constructor; [exact RS|]. constructor; [apply RG; left; reflexivity|].
  constructor; [apply RG; right; left; reflexivity|]. constructor; [exact RN | constructor].
- apply pairwise_disjoint_of_extents.
  unfold sc_regions, stack_region, got_regionP, bcell_regionP, sc_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E240) by (rewrite V0; lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E252) by (rewrite V12; lia).
  rewrite (VB (A_OBJ 44) (VAL (A_OBJ 44)) E284) by (rewrite V44; unfold A_G_REC; lia).
  cbn [base_val]. rewrite Usp, V0, V12, V44. unfold A_G_REC.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 C3 Hstk0. clear. intros.
  repeat split; lia.
- exact HG.
Qed.

(* The symbolic state at the join 0x8a9d0, where the two arms meet with the call slot in s1. The registers are
   their own atoms again: s1 (x9) is the slot c, s3 (x19) is the shadow base, s0 (x8) the line, s2 (x18) the id,
   and the frame is the 48 bytes at the current sp holding the five saved registers as literals. The one shadow
   entry [c, c + 56) removes the two inline checks of the stores of c->fn and c->nargs. *)
Definition sc_mid_pc : Z := AF_sup_call + 0x74.
Definition sc_mid_Bx : sv := SOff 19 0.
Definition sc_mid_SH : list shent := [mkSHE 9%nat 0 56].
Definition sc_mid_E (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Definition sc_mid_slot : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 8 [].
Definition sc_mid_frame (ra0 s00 s10 s20 s30 : Z) : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 48 0 48
[YP09.mkChunk 8 (CVal 8 (SLit s30)); YP09.mkChunk 16 (CVal 8 (SLit s20));
 YP09.mkChunk 24 (CVal 8 (SLit s10)); YP09.mkChunk 32 (CVal 8 (SLit s00));
 YP09.mkChunk 40 (CVal 8 (SLit ra0))].
Definition sc_mid_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF A_G_REC A_REC_SPILL 3); (19%nat, mkAF SB SB 0)] [] [].
Definition sc_mid_ss (ra0 s00 s10 s20 s30 : Z) : sstate :=
mkSS sc_mid_pc sr_atoms [sc_mid_frame ra0 s00 s10 s20 s30; sc_mid_slot] None sc_mid_facts.

Lemma sc_mid_entry : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md c ra0 s00 s10 s20 s30,
AR SEGS B ly S W mem md -> sc_slot c ->
getr regs 9 = w64 c -> getr regs 19 = w64 SB ->
2 ^ 46 <= spZ regs -> spZ regs + 48 <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs <= a < spZ regs + 48 -> apresent (w_H W) mem a) ->
aval_mem (rdW W mem) (spZ regs + 8) 8 s30 -> aval_mem (rdW W mem) (spZ regs + 16) 8 s20 ->
aval_mem (rdW W mem) (spZ regs + 24) 8 s10 -> aval_mem (rdW W mem) (spZ regs + 32) 8 s00 ->
aval_mem (rdW W mem) (spZ regs + 40) 8 ra0 ->
0 <= ra0 < 2 ^ 64 -> 0 <= s00 < 2 ^ 64 -> 0 <= s10 < 2 ^ 64 -> 0 <= s20 < 2 ^ 64 -> 0 <= s30 < 2 ^ 64 ->
st_ok_pi SEGS VAL (sc_mid_E regs) (sc_mid_ss ra0 s00 s10 s20 s30)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + sc_mid_pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS sc_mid_Bx sc_mid_SH (sc_mid_E regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md c ra0 s00 s10 s20 s30 HAR Hsl H9 H19 Hsp1 Hsp2 Hsp16 Hpres
  M30 M20 M10 M00 Mra Rra R00 R10 R20 R30.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (sc_slot_facts c Hsl) as (Hc8 & Hclo & Hchi & Hcfp).
unfold A_G_REC, A_REC_SPILL in Hclo, Hchi.
rewrite restrict_mkst_fx.
set (E := sc_mid_E regs).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. unfold sc_mid_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 c) by (rewrite (EEo 9%nat 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = Z_to_bv 64 SB) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs))
  by (rewrite E2; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (CH : forall o v, aval_mem (rdW W mem) (spZ regs + o) 8 v -> 0 <= v < 2 ^ 64 ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) (spZ regs) (YP09.mkChunk o (CVal 8 (SLit v)))).
{ intros o v Hv Hr. apply (chunk_ok_val SEGS E _ (spZ regs) o 8 (SLit v) v);
  [reflexivity | cbn; lia | lia | exact (sc_val_mem_of_aval SEGS (w_H W) mem (spZ regs + o) 8 v Hv)]. }
assert (RF : YP09.region_ok SEGS E (mrestrict (w_H W) mem) (sc_mid_frame ra0 s00 s10 s20 s30)).
{ unfold region_ok, sc_mid_frame.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 2%nat (spZ regs) E2' ltac:(lia)). split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia|].
  constructor; [exact (CH 8 s30 M30 R30)|]. constructor; [exact (CH 16 s20 M20 R20)|].
  constructor; [exact (CH 24 s10 M10 R10)|]. constructor; [exact (CH 32 s00 M00 R00)|].
  constructor; [exact (CH 40 ra0 Mra Rra) | constructor]. }
assert (RL : YP09.region_ok SEGS E (mrestrict (w_H W) mem) sc_mid_slot).
{ unfold region_ok, sc_mid_slot.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 9%nat c E9 ltac:(lia)). split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (sc_prog_writable ly S W mem md); [exact HAR | apply Hcfp; lia]. }
assert (HG : facts_ok E sc_mid_facts).
{ split; [|split; [exact I | exact I]].
  cbn [sc_mid_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E9, E19, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold A_G_REC, A_REC_SPILL, SB.
  revert Hsp1 Hsp2 Hsp16 Hc8 Hclo Hchi. clear. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
split.
- unfold sc_mid_ss. apply pa_entry_st_ok_full.
  + subst E. unfold sc_mid_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor; [exact RF|]. constructor; [exact RL | constructor].
  + apply pairwise_disjoint_of_extents.
    unfold sc_mid_frame, sc_mid_slot, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 2%nat (spZ regs) E2' ltac:(lia)), (VB 9%nat c E9 ltac:(lia)).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hsp1 Hsp2 Hclo Hchi. clear. intros. repeat split; lia.
  + exact HG.
- unfold sh_ok, sc_mid_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E sc_mid_Bx 9%nat c 56 c 0 56).
  + exact (sc_slot_addressable ly S W mem md c c 56 HAR Hsl ltac:(lia) ltac:(lia)).
  + unfold U, sc_mid_Bx. cbn [sv_denot]. rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF. lia.
Qed.

End e.
End f.
End w.
