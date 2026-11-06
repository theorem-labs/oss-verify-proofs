(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryUnset), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntryUnset.v. *)
(* Ported from lib/A/Prog/GrantEntryUnset.v at a working branch 5651bf66924, blob 6b0a9d01723 (the bytes first read; lib/A/AB01.v there is the current 1e6f4323d1e). *)
(* The walk of LLVMFuzzerTestOneInput's phase UNSET on image B (fuzz_grant.asan-ubsan, entry 0x80a3c):
   slots 0x81224 (GP_unset0, offset 0x7e8) .. 0x81300 (GP_admit, offset 0x8c4). The block at 0x81224
   writes the bytes left (a2) and the input cursor (s7) and the address of every remaining object of
   the frame into the machine frame's spill slots 104 48 120 80 56 16 40 64 112 96; then two nested
   loops run over the 48 channels (s5) and the 3 parameters (s9, bound s6 = 3), and for each cell the
   input never set (`was_set[c][p] = 0`, the byte at s2) call reac_headamp_tx_effective (t, c, p)
   (0x812b8; t is read back from slot 152) and reac_headamp_default (p) (0x812c4): the two must agree
   (0x812c8), and the default must be legal for the parameter (zero for the two switches 0x812d0,
   1..55 for SENS 0x812ec). The model facts are fuzz_grant's own (SegSetModel.tables_end_inv,
   HeadampModel.eff_cell), so the block at 0x81d98 (__asan_handle_no_return, then abort) is not
   reached.
   Image B's code differs from image A's (0x80cd0 .. 0x80d90) in three points: (1) the inner loop's
   head 0x812a0 is UBSan's pointer-overflow check `bltu s4,s9,0x81f48` with s4 = ~(was_set + 3c)
   (computed at the outer head 0x81294), which image A does not have; it is refuted at every turn
   from the frame's bound; (2) the table's address is read back from slot 152 before each call of
   reac_headamp_tx_effective (image A keeps it in s4); (3) the registers and the spill slots are
   renamed (image B: c s5, p s9, 2 s8, 3 s6, the row s7, the cell s2, c & 255 s11, the answer s10). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib YC85 YC1g GrantFrame GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
HeadampDefault GrantBContracts LLVMFEntryDefs LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require HeadampLayout GrantSlotPlan SlotNeeds_c SegSetModel SegCLib.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The slot of the inner loop's head, as an offset in the listing: 0x812a0 - 0x80a3c. *)
Definition GU_in : Z := 0x864.

Local Ltac zbool :=
repeat match goal with
| H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
| H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
end.

(* `xori rd, rs, -1` (`not`) on a 64-bit value. *)
Lemma lxor_m1 : forall a m, m = 2 ^ 64 - 1 -> 0 <= a < 2 ^ 64 -> Z.lxor a m = 2 ^ 64 - 1 - a.
Proof.
intros a m -> Ha.
change (2 ^ 64 - 1) with (Z.ones 64).
assert (HL : Z.land (Z.lxor a (Z.ones 64)) a = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 64) as [Hlt | Hge].
  - rewrite Z.testbit_ones_nonneg by lia. replace (n <? 64) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (Z.testbit a n); reflexivity.
  - replace (Z.testbit a n) with false; [destruct (Z.testbit (Z.ones 64) n); reflexivity|].
    symmetry. rewrite <- (Z.mod_small a (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
pose proof (Z.add_nocarry_lxor _ _ HL) as E.
rewrite Z.lxor_assoc, (Z.lxor_comm (Z.ones 64) a), <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in E.
change (Z.ones 64) with (2 ^ 64 - 1) in *. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* ---- memory kept across the loops ---- *)

(* A byte read through aview as a byte of a list gives the byte itself. *)
Lemma mbyte_of_aview_tb : forall (H : word -> bool) (m : word -> option byte) a (T : list byte) i,
  aview SEGS H m a = Some (tb T i) -> mbyte SEGS (mrestrict H m) a = Some (nth (Z.to_nat i) T (Z_to_bv 8 0)).
Proof.
intros H m a T i E. unfold aview in E. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; [|discriminate].
cbn in E. injection E as E. f_equal. unfold tb in E. apply bv_eq. exact E.
Qed.
(* A register of the image environment built from a register file. *)
Lemma ewR : forall (regs : bvmap 5 word) extra n (r : bv 5),
  Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
(* The unsigned value of a symbolic word whose atom is known, without a modulo. *)
Lemma zcanon_in : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. exact Hz. Qed.
Lemma zcanon_neg : forall z, - 2 ^ 64 <= z < 0 -> zcanon z = z + 2 ^ 64.
Proof.
intros z Hz. unfold zcanon, M64.
replace (z mod 2 ^ 64) with ((z + 1 * 2 ^ 64) mod 2 ^ 64) by (apply Z.mod_add; lia).
apply Z.mod_small. lia.
Qed.
Lemma U_off_val : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  U E (SOff n x) = v + x.
Proof. intros E n v x F Hv Hx. rewrite U_SOff, F, unsigned_lit_small by exact Hv. apply zcanon_in. exact Hx. Qed.
Lemma U_off_neg : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> - 2 ^ 64 <= v + x < 0 ->
  U E (SOff n x) = v + x + 2 ^ 64.
Proof. intros E n v x F Hv Hx. rewrite U_SOff, F, unsigned_lit_small by exact Hv. apply zcanon_neg. exact Hx. Qed.
Lemma U_lit_val : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. rewrite U_SLit. apply zcanon_in. exact Hz. Qed.
Lemma U_lit_neg : forall E z, - 2 ^ 64 <= z < 0 -> U E (SLit z) = z + 2 ^ 64.
Proof. intros E z Hz. rewrite U_SLit. apply zcanon_neg. exact Hz. Qed.
Lemma U_zext8_val : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> U E (SExt false 8 (SOff n 0)) = v.
Proof.
intros E n v F Hv. rewrite U_zext, (U_off_val E n v 0 F) by lia. rewrite Z.add_0_r.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hv.
Qed.
Lemma U_zext8_off : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 256 ->
  U E (SExt false 8 (SOff n x)) = v + x.
Proof.
intros E n v x F Hv Hx. rewrite U_zext, (U_off_val E n v x F) by lia.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hx.
Qed.
Lemma denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
(* The value of a symbolic word whose atom is known. *)
Lemma denot_off_val : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof.
intros E n v x F Hv. rewrite denot_lit_U, U_SOff, F, unsigned_lit_small by exact Hv.
unfold zcanon, M64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma sub_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia]. apply Z.mod_divide; [lia|].
destruct Ha as [x Hx]. destruct Hb as [y Hy]. exists (2 * x - y). lia.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
(* The two callees, as hypotheses of walk_LLVMFuzzerTestOneInput (GrantBContracts.v). *)
Hypothesis HEFF : tb_reac_headamp_tx_effective_spec B.
Hypothesis HDFLT : tb_reac_headamp_default_spec B.

(* The callee chain at the realigned machine stack pointer (the seat's ge_achain), seen
   through the layout of the phase, whose top is the caller's. *)
Lemma ge_achain_ly : forall cx ly3 S3 W3 mem md own k sp',
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    own ly3 S3 W3 mem md k ->
  rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  sp' + 16 <= spZ (c_regs cx) ->
  achain ly3 (aview SEGS (w_H W3) mem) sp' (spZ (c_regs cx)) (gch cx).
Proof.
intros cx ly3 S3 W3 mem md own k sp' HB HJ H8 H16 Hsp.
pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop).
eapply ge_achain;
  first [ exact HB | exact H8 | exact H16 | exact Hsp
        | (intros a Ha; apply F1; unfold GE_STK, STK_LLVMFuzzerTestOneInput in *; lia) ].
Qed.

(* An unset cell of the input's tables carries the default (Pau's model). *)
Lemma unset_eff : forall pl t c p, 0 <= c < 48 -> 0 <= p < 3 -> t <> 0 ->
  tb (GrantSlotPlan.ws_end pl) (3 * c + p) = 0 ->
  eff (GrantSlotPlan.T_end pl) t c p = dflt p.
Proof.
intros pl t c p Hc Hp Ht Hw. rewrite eff_cell by lia.
destruct (SegSetModel.tables_end_inv pl) as (_ & _ & _ & _ & HR).
destruct (HR c p ltac:(lia) ltac:(lia)) as [H1 _]. rewrite <- H1, Hw. reflexivity.
Qed.
Lemma eff_range : forall T t c p, 0 <= eff T t c p < 256.
Proof.
intros T t c p. unfold eff, dflt.
repeat match goal with |- context [if ?b then _ else _] => destruct b end; try lia; apply HeadampLayout.tb_range.
Qed.

(* The machine stack pointer the entry function was called with, and the realigned one. *)
Lemma gsp : forall cx, ge_base B MT cx ->
  alloc_ceiling + GE_STK <= spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 320 < c_sp1 cx <= spZ (c_regs cx) - 288 /\
  c_sp1 cx mod 32 = 0 /\ spZ (c_regs cx) mod 16 = 0.
Proof.
intros cx HB.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (Z.div_mod (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hmp.
rewrite Hsp1. split; [lia|]. split; [lia|]. split; [|exact Hal16].
rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

(* A branch fact as a fact on Z: the unsigned value of each side, from the atom facts. *)
Local Ltac uvals_in H :=
  repeat match type of H with
  | context [U ?Ex (SExt false 8 (SOff ?n 0))] =>
      match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ => rewrite (U_zext8_val Ex n v F) in H by lia end
  | context [U ?Ex (SOff ?n ?x)] =>
      match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ =>
        first [ rewrite (U_off_val Ex n v x F) in H by lia | rewrite (U_off_neg Ex n v x F) in H by lia ] end
  | context [U ?Ex (SLit ?z)] =>
      first [ rewrite (U_lit_val Ex z) in H by lia | rewrite (U_lit_neg Ex z) in H by lia ]
  end.
Local Ltac uvals_goal :=
  repeat match goal with
  | |- context [U ?Ex (SExt false 8 (SOff ?n ?x))] =>
      match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ => rewrite (U_zext8_off Ex n v x F) by lia end
  | |- context [U ?Ex (SOff ?n ?x)] =>
      match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ =>
        first [ rewrite (U_off_val Ex n v x F) by lia | rewrite (U_off_neg Ex n v x F) by lia ] end
  | |- context [U ?Ex (SLit ?z)] =>
      first [ rewrite (U_lit_val Ex z) by lia | rewrite (U_lit_neg Ex z) by lia ]
  end.
(* The arithmetic of the outer head 0x81284 .. 0x81294, which the engine folds into
   `~(was_set + (3 * c + 3))` (an SMd product, two adds, then `not`): innermost first. *)
Local Ltac zsimpl :=
  repeat match goal with
  | |- context [Z.lxor ?x ?y] => rewrite (lxor_m1 x y) by lia
  | |- context [zcanon ?z] =>
      lazymatch z with context [zcanon _] => fail | _ => rewrite (zcanon_in z) by lia end
  end.
Local Ltac bnum H :=
  first [rewrite branch_ne_U in H | rewrite branch_eq_U in H | rewrite branch_ltu_U in H | rewrite branch_geu_U in H];
  uvals_in H; zbool.
(* The branch condition of this path as a fact on Z; [kill] closes a path whose facts contradict. *)
Local Ltac bfact := match goal with H : branch_taken _ (sv_denot _ _) (sv_denot _ _) = _ |- _ => bnum H end.
Local Ltac kill := exfalso; lia.
Local Ltac Fall :=
  repeat match goal with |- context [ew ?Ex ?n] =>
    match goal with F : ew Ex n = Z_to_bv 64 _ |- _ => rewrite F end end.
(* The value of a register of the symbolic state, as the invariant states it. *)
Local Ltac regval HS :=
  cbn [ms_regs mkst];
  lazymatch goal with |- getr _ ?r = w64 ?v =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?H ?ms) =>
    let R := fresh "R" in pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [ms_regs restrict mkst] in R; rewrite R; clear R;
    lazymatch e with
    | SOff ?n 0 =>
        rewrite denot_off0;
        match goal with F : ew Ex n = Z_to_bv 64 ?u |- _ => rewrite F; unfold w64; first [reflexivity | f_equal; lia] end
    | SOff ?n ?x =>
        match goal with F : ew Ex n = Z_to_bv 64 ?u |- _ =>
          rewrite (denot_off_val Ex n u x F) by lia; unfold w64; f_equal; lia end
    | SLit ?z => cbn [sv_denot]; unfold w64; f_equal; lia
    | SExt false 8 (SOff ?n ?x) =>
        match goal with F : ew Ex n = Z_to_bv 64 ?u |- _ =>
          rewrite denot_lit_U, (U_zext8_off Ex n u x F) by lia; unfold w64; f_equal; lia end
    | _ => rewrite denot_lit_U; unfold w64; f_equal;
        repeat first [rewrite U_SAlu | rewrite U_SMd]; uvals_goal; cbn [zalu_raw zmd_raw];
        first
        [ solve [ try (change 255 with (Z.ones 8); rewrite Z.land_ones by lia);
                  rewrite ?zcanon_in by (rewrite ?Z.mod_small by lia; lia); rewrite ?Z.mod_small by lia; lia ]
        | solve [ zsimpl; lia ] ]
    end end end.
Section d.
Variables (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (t : Z).
Hypothesis HB : ge_base B MT cx.

(* The memory facts the admission phase reads, over a memory m: GI_admit's memory part. *)
Definition ums (m : word -> option byte) : machine_state := mkst (c_regs cx) (Z_to_bv 64 0) m (seg_rom SEGS).
Definition uslots (ms : machine_state) : Prop :=
  gslot cx W3 ms 0 (GrantSlotPlan.h_rows (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms 8 (gF cx fp) /\ gslot cx W3 ms 16 (gF cx fp + GO_RAW) /\
  gslot cx W3 ms 24 (256 * (GrantSlotPlan.h_u16 (GrantSlotPlan.header (c_pl cx)) / 256)) /\
  gslot cx W3 ms 32 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms 40 (gF cx fp + GO_UNSET) /\
  gslot cx W3 ms 48 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms 56 (gF cx fp + GO_LIT) /\ gslot cx W3 ms 64 (gF cx fp + GO_CH) /\
  gslot cx W3 ms 72 (gF cx fp) /\ gslot cx W3 ms 80 (gF cx fp + GO_POLL) /\
  gslot cx W3 ms 88 (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx)) mod 2 ^ 64) /\
  gslot cx W3 ms 96 (gF cx fp + GO_VAL) /\
  gslot cx W3 ms 104 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms 112 (gF cx fp + GO_PAR) /\ gslot cx W3 ms 120 (gF cx fp + GO_A) /\
  gslot cx W3 ms 128 (gF cx fp + GO_SET) /\ gslot cx W3 ms 136 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms 144 SHADOW_OFF /\ gslot cx W3 ms 152 t.
Definition umem (m : word -> option byte) : Prop :=
  gsaved cx W3 (ums m) /\ gshadow cx fp W3 (ums m) GSH_tables /\
  rdword (aview SEGS (w_H W3) m) (gF cx fp + 1016) = Some (gFL cx fp) /\
  garr8 SEGS (mrestrict (w_H W3) m) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  uslots (ums m) /\
  gtab B cx ly3 S3 W3 (ums m) t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 (ums m) GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 (ums m) GO_SET (GrantSlotPlan.st_end (c_pl cx)).

Lemma umem_keep : forall m m', umem m -> ge_keep cx fp W3 [(t, 460)] m m' -> umem m'.
Proof.
intros m m' HM HK.
pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (_ & Lws & Lst & _).
assert (HKs : ge_keep cx fp W3 [(t, 460)] (ms_mem (ums m)) (ms_mem (ums m'))) by exact HK.
destruct HM as (GSV & SH & FL & GI &
  (L0 & L8 & L16 & L24 & L32 & L40 & L48 & L56 & L64 & L72 & L80 & L88 & L96 & L104 & L112 & L120 &
   L128 & L136 & L144 & L152) & GT & GW & GS).
unfold umem, uslots.
repeat match goal with |- _ /\ _ => split end.
all: first
  [ (eapply ge_gslot_keep; first [exact HB | exact HKs | lia | eassumption])
  | (eapply ge_gsaved_keep; first [exact HB | exact HKs | exact GSV])
  | (eapply ge_gshadow_keep; first [exact HKs | exact SH | (lazymatch goal with |- (_ <= _)%Z => vm_compute; discriminate end)])
  | exact (ge_flag_keep cx fp W3 _ (ums m) (ums m') HKs FL)
  | exact (ge_input_keep cx fp W3 _ (ums m) (ums m') HKs GI)
  | (eapply ge_gtab_keep; first [exact HKs | (left; reflexivity) | exact GT])
  | (eapply ge_gfarr_keep; first [exact HKs | eassumption | (lazymatch goal with |- (0 <= _)%Z => unfold GO_WAS, GO_SET; lia end)
      | (lazymatch goal with |- (_ + Z.of_nat (length _) <= _)%Z =>
           rewrite ?length_map, ?Lws, ?Lst; vm_compute; discriminate end)])
  ].
Qed.

Lemma nth_map_tb : forall (l : list byte) j, (j < length l)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = tb l (Z.of_nat j).
Proof.
intros l j Hj. unfold tb. rewrite Nat2Z.id. revert j Hj.
induction l as [|x l IH]; intros [|j] Hj; cbn [length] in Hj; try lia.
- reflexivity.
- cbn [map nth]. apply IH. lia.
Qed.
Lemma gsaved_s0 : forall ms, gsaved cx W3 ms ->
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)).
Proof.
intros ms [_ H]. specialize (H 0 ltac:(lia)). rewrite Z.mul_0_r, Z.sub_0_r in H. rewrite H.
unfold s0Z. do 3 f_equal; apply bv_eq; reflexivity.
Qed.
Lemma gtab_obj : forall ms T, gtab B cx ly3 S3 W3 ms t T ->
  obj_at SEGS (mrestrict (w_H W3) (ms_mem ms)) t HeadampLayout.LAY_TX (HeadampLayout.tx_vals T).
Proof.
intros ms T (_ & _ & _ & HT). apply HeadampLayout.tx_obj_bytes. intros i Hi.
pose proof (HeadampLayout.tx_fbyte_range i Hi) as Hr. apply mbyte_of_aview_tb. apply HT; [lia | | |];
intros ->; vm_compute in Hi; discriminate.
Qed.

Variable POST : ecx -> world SEGS -> config -> Prop.
Hypothesis HADM : ge_from B MT POST (GI_admit B MT).
Hypothesis HFR : frames S3 = [(GE_CID, fp)].
Hypothesis HMO : mo_le MT (c_S cx) S3 acc.
Hypothesis Hk : k <= 1.
Hypothesis Hacc : acc <= GE_A1 MT.
Hypothesis HBLK : gblk1 B cx ly3 S3 t.
Hypothesis HCN : c_n cx < 2 ^ 26.
Variable m1 : word -> option byte.
Hypothesis HM1 : umem m1.
Hypothesis HRELt : GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx))
  (GrantSlotPlan.st_end (c_pl cx)).
Hypothesis HI1t : SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* The head of the inner loop, slot 0x812a0: channel c, parameter p. s2 the cell
   was_set[c][p], s4 = ~(was_set + 3c) (UBSan's bound), s5 = s11 = c, s6 = 3, s7 the row
   was_set + 3c, s8 = 2, s9 = p; s3 the frame's shadow base. *)
Definition UINV (c p : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  0 <= c < 48 /\ 0 <= p < 3 /\
  getr regs 2 = w64 (c_sp1 cx) /\ getr regs 8 = w64 (spZ (c_regs cx)) /\ getr regs 9 = w64 (c_sp1 cx) /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 19 = w64 (gSH cx fp) /\
  getr regs 18 = w64 (gF cx fp + GO_WAS + 3 * c + p) /\
  getr regs 20 = w64 (2 ^ 64 - 1 - (gF cx fp + GO_WAS + 3 * c)) /\
  getr regs 21 = w64 c /\ getr regs 22 = w64 3 /\ getr regs 23 = w64 (gF cx fp + GO_WAS + 3 * c) /\
  getr regs 24 = w64 2 /\ getr regs 25 = w64 p /\ getr regs 27 = w64 c /\
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem md k /\
  ge_keep cx fp W3 [(t, 460)] m1 mem.

Definition SB_U : Z := 0x7fff8000.
Definition Bx_U : sv := SLit SB_U.
Definition Bspan_U : Z * Z := (SB_U, SB_U + 2 ^ 44 - 1).
(* The byte was_set[c][p], which the inner loop reads at s2 (atom 32), and the two spill
   slots the loops read: 136 (was_set, atom 34) at the outer head, 152 (the table, atom 33)
   before each call of reac_headamp_tx_effective. *)
Definition R_byte : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition R_sl : YP09.region :=
  YP09.mkRegion (Some 9%nat) 136 160 0 0
    [YP09.mkChunk 136 (CVal 8 (SOff 34 0)); YP09.mkChunk 152 (CVal 8 (SOff 33 0))].
Definition ss_in : sstate := mkSS GU_in sr_atoms [R_byte; R_sl] None (mkFacts [] [] []).

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* A run that wrote no byte keeps every byte. *)
Local Ltac upd_uk :=
  repeat match goal with H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with HF : frame_of ?Ex ?rs ?mprev ?mnew, HUK : ge_keep _ _ _ _ _ ?mprev |- _ =>
    let HUK' := fresh "HUK" in
    assert (HUK' : ge_keep cx fp W3 [(t, 460)] m1 mnew) by
      (apply (ge_keep_trans cx fp W3 [(t, 460)] _ mprev); [exact HUK | apply ge_keep_pointwise; intros x; apply HF;
        let rs' := eval vm_compute in rs in change rs with rs';
        intros (r & Hr & Hb); repeat (destruct Hr as [Hr | Hr]; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hb; lia |]);
        destruct Hr]);
    clear HUK HF; rename HUK' into HUK end.
(* A call keeps the region of the spill slots at s1 (atom 9): its bytes lie above the
   realigned stack pointer, which both memories keep from m1. *)
Local Ltac rkept HUK HUK1 :=
  constructor; [|constructor]; split;
  [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
    lazymatch type of Ha with context [ew ?Ex 9] =>
      match goal with F : ew Ex 9 = Z_to_bv 64 _ |- _ => rewrite F in Ha end end;
    rewrite unsigned_lit_small in Ha by lia;
    apply (mbyte_of_aview SEGS);
    rewrite (HUK1 a) by (left; lia); rewrite (HUK a) by (left; lia); reflexivity
  | intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia ].
(* After a call: the facts on the atoms below k hold in the new environment. *)
Local Ltac restate OLD :=
  lazymatch type of OLD with forall q, (q < ?K)%nat -> ew ?En q = ew ?Eo q =>
  repeat match goal with
  | F : ew Eo ?n = Z_to_bv 64 ?v |- _ =>
      lazymatch goal with
      | _ : ew En n = Z_to_bv 64 v |- _ => fail
      | _ => let F' := fresh "F" in assert (F' : ew En n = Z_to_bv 64 v) by (rewrite OLD by (cbv; lia); exact F)
      end
  end end.
(* The ends of one turn of the inner loop. [at_head c p]: the run is at the loop head
   0x812a0 for the cell (c, p); the induction hypothesis takes over. *)
Local Ltac at_head HS HJ HUK c' p' :=
  pmkst HS;
  lazymatch goal with IH : forall (c p : Z) (regs : bvmap 5 word) mem md, _ -> UINV c p regs mem md -> _ |- _ =>
    apply (IH c' p'); [lia|] end;
  unfold UINV, GO_WAS; split; [lia|]; split; [lia|];
  repeat (split; [regval HS|]);
  split; [exact HJ | exact HUK].
(* [at_admit]: the run is at 0x81300, after the last cell; GI_admit holds there. *)
Local Ltac at_admit HS HJ HUK :=
  pmkst HS;
  repeat rewrite wvb_collapse in HJ;
  eapply HADM; [exact HB | exact HJ | exact HFR | exact HMO |];
  unfold GI_admit; exists t;
  let m := lazymatch type of HUK with ge_keep _ _ _ _ _ ?m => m end in
  let GSV := fresh "GSV" in let GSH := fresh "GSH" in let GFL := fresh "GFL" in let GIN := fresh "GIN" in
  let US := fresh "US" in let GT := fresh "GT" in let GW := fresh "GW" in let GS := fresh "GS" in
  destruct (umem_keep m1 m HM1 HUK) as (GSV & GSH & GFL & GIN & US & GT & GW & GS);
  let U0 := fresh "U" in let U8 := fresh "U" in let U16 := fresh "U" in let U24 := fresh "U" in
  let U32 := fresh "U" in let U40 := fresh "U" in let U48 := fresh "U" in let U56 := fresh "U" in
  let U64 := fresh "U" in let U72 := fresh "U" in let U80 := fresh "U" in let U88 := fresh "U" in
  let U96 := fresh "U" in let U104 := fresh "U" in let U112 := fresh "U" in let U120 := fresh "U" in
  let U128 := fresh "U" in let U136 := fresh "U" in let U144 := fresh "U" in let U152 := fresh "U" in
  destruct US as (U0 & U8 & U16 & U24 & U32 & U40 & U48 & U56 & U64 & U72 & U80 & U88 & U96 & U104 &
    U112 & U120 & U128 & U136 & U144 & U152);
  let Hgp0 := fresh "Hgp0" in let Htp0 := fresh "Htp0" in
  pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _);
  split;
  [ unfold ge_body, gregs;
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
    split; [reflexivity|]; split; [reflexivity|];
    split; [ split; [regval HS|]; split; [regval HS|]; split; [regval HS|];
             split; [rewrite Hgp0; regval HS | rewrite Htp0; regval HS] |];
    split; [exact GSV|]; split; [exact GSH|]; split; [exact GFL|]; split; [reflexivity|]; exact GIN
  | split; [exact Hk|]; split; [exact Hacc|]; split; [exact HBLK|]; split; [exact HCN|];
    split; [regval HS|];
    split; [exact U0|]; split; [exact U8|]; split; [exact U16|]; split; [exact U24|];
    split; [exact U32|]; split; [exact U40|]; split; [exact U48|]; split; [exact U56|];
    split; [exact U64|]; split; [exact U72|]; split; [exact U80|]; split; [exact U88|];
    split; [exact U96|]; split; [exact U104|]; split; [exact U112|]; split; [exact U120|];
    split; [exact U128|]; split; [exact U136|]; split; [exact U144|]; split; [exact U152|];
    split; [exact GT|]; split; [exact GW|]; split; [exact GS|];
    split; [exact HRELt | exact HI1t] ].
(* From a branch whose path goes on at 0x812f0: the next channel, or the end of the loops. *)
Local Ltac next_chan HS HJ SHOK HUK c p :=
  paj_run_tok RUN HS HJ SHOK Bspan_U; [first [apply awr_ok_nil | awr_ok_tac] |]; upd_uk;
  psrr_branch_tok RUN BR HS SHOK Bspan_U;
  [ bfact; tryif solve [kill] then idtac else
      (paj_run_to_tok RUNTO HS HJ SHOK Bspan_U GU_in; [first [apply awr_ok_nil | awr_ok_tac] |]; upd_uk;
       at_head HS HJ HUK (c + 1) 0)
  | bfact; tryif solve [kill] then idtac else
      (paj_run_to_tok RUNTO HS HJ SHOK Bspan_U GP_admit; [first [apply awr_ok_nil | awr_ok_tac] |]; upd_uk;
       at_admit HS HJ HUK) ].
(* From a branch whose path goes on at 0x812d4: the next parameter, or the next channel. *)
Local Ltac next_cell HS HJ SHOK HUK c p :=
  paj_run_tok RUN HS HJ SHOK Bspan_U; [first [apply awr_ok_nil | awr_ok_tac] |]; upd_uk;
  psrr_branch_tok RUN BR HS SHOK Bspan_U;
  [ bfact; tryif solve [kill] then idtac else
      (paj_run_to_tok RUNTO HS HJ SHOK Bspan_U GU_in; [first [apply awr_ok_nil | awr_ok_tac] |]; upd_uk;
       at_head HS HJ HUK c (p + 1))
  | bfact; tryif solve [kill] then idtac else next_chan HS HJ SHOK HUK c p ].

Lemma uloop : forall n c p regs mem md, (Z.to_nat (3 * (48 - c) - p) <= n)%nat ->
  UINV c p regs mem md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + GU_in)) mem (seg_rom SEGS)) md) (POST cx).
Proof.
induction n as [|n IH]; intros c p regs mem md Hn HI.
{ destruct HI as (Hc & Hp & _). lia. }
pose proof HI as (Hc & Hp & G2 & G8 & G9 & G3 & G4 & G19 & G18 & G20 & G21 & G22 & G23 & G24 & G25 & G27 & HJ & HUK).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_grant) (PI := PI)) as HBLO. rewrite IMG_LO_B_val in HBLO.
pose proof (gsp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16). unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp.
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hfin) as (HF1 & HF2 & _).
assert (EgF : gF cx fp = frame_addr ly3 GE_CID fp) by (unfold gF, frame_addr; rewrite HlyF; reflexivity).
rewrite <- EgF in HF1, HF2. change (fs_frame_bytes GE_CID) with 1024 in HF2.
assert (Htin : In (t, 460) (ablocks B ly3 S3)) by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ t 460 HAR Htin) as (_ & Ht4096 & Htceil & _). change (req_size 460) with 460 in Htceil.
pose proof (umem_keep m1 mem HM1 HUK) as HMc.
pose proof HMc as (_ & _ & _ & _ & HUS & HGT & HGW & _).
pose proof HUS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U136 & _ & U152).
pose proof (HGT) as (_ & Htpos & Htlen & _).
set (pl := c_pl cx) in *.
set (wb := tb (GrantSlotPlan.ws_end pl) (3 * c + p)).
assert (Hwbr : 0 <= wb < 256) by apply HeadampLayout.tb_range.
assert (Hwbm : val_mem SEGS (mrestrict (w_H W3) mem) (gF cx fp + GO_WAS + 3 * c + p) 1 wb).
{ unfold gfarr, ums in HGW. cbn [ms_mem mkst] in HGW.
  pose proof (SegSetModel.tables_end_inv pl) as (_ & Lws & _).
  destruct (HGW (Z.to_nat (3 * c + p)) ltac:(rewrite length_map, Lws; lia)) as [Hv _].
  rewrite nth_map_tb, Z2Nat.id in Hv by (try rewrite Lws; lia).
  replace (gF cx fp + GO_WAS + 3 * c + p) with (gF cx fp + GO_WAS + (3 * c + p)) by lia. exact Hv. }
assert (Hm : wb = 0 -> eff (GrantSlotPlan.T_end pl) t c p = dflt p) by (intros H0; apply unset_eff; lia).
assert (Hdf : (p = 2 /\ dflt p = 32) \/ (p <> 2 /\ dflt p = 0)) by (unfold dflt; destruct (Z.eqb_spec p 2); [left | right]; lia).
pose proof (eff_range (GrantSlotPlan.T_end pl) t c p) as Hef.
unfold gslot, ums in U136, U152. cbn [ms_mem mkst] in U136, U152.
(* The symbolic state at the head of the inner loop: atom 32 the byte was_set[c][p], 33 the
   table, 34 the address of was_set. *)
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 wb; Z_to_bv 64 t; Z_to_bv 64 (gF cx fp + GO_WAS)])) ss_in
  (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + GU_in)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_in. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold R_byte, region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (ewR regs _ 18 18%bv eq_refl), G18. unfold w64. rewrite unsigned_lit_small by (unfold GO_WAS; lia).
      unfold GO_WAS in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ _ 0 1 (SOff 32 0) wb); [| lia | lia | rewrite Z.add_0_r; exact Hwbm].
      cbn [sv_denot]. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs _ 0).
      cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + unfold R_sl, region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (ewR regs _ 9 9%bv eq_refl), G9. unfold w64. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS _ _ _ 136 8 (SOff 34 0) (gF cx fp + GO_WAS)).
        -- cbn [sv_denot]. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs _ 2).
           cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        -- cbn [Z.of_N]. unfold GO_WAS. lia.
        -- cbn [Z.of_N]. lia.
        -- apply (val_mem_of_rdword SEGS (w_H W3) mem). exact U136.
      * apply (chunk_ok_val SEGS _ _ _ 152 8 (SOff 33 0) t).
        -- cbn [sv_denot]. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs _ 1).
           cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        -- cbn [Z.of_N]. lia.
        -- cbn [Z.of_N]. lia.
        -- apply (val_mem_of_rdword SEGS (w_H W3) mem). exact U152.
  - unfold R_byte, R_sl. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold YP09.extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
    rewrite (ewR regs _ 18 18%bv eq_refl), G18, (ewR regs _ 9 9%bv eq_refl), G9. unfold w64.
    rewrite !unsigned_lit_small by (unfold GO_WAS; lia). unfold GO_WAS. lia.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS Bx_U [] (Eimg (Ereg regs [Z_to_bv 64 wb; Z_to_bv 64 t; Z_to_bv 64 (gF cx fp + GO_WAS)]))
  (mrestrict (w_H W3) mem)) by constructor.
remember (Eimg (Ereg regs [Z_to_bv 64 wb; Z_to_bv 64 t; Z_to_bv 64 (gF cx fp + GO_WAS)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr regs r)
  by (intros q r Hq; subst E; apply ewR; exact Hq).
assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
assert (F3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact G3).
assert (F4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact G4).
assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
assert (F18 : ew E 18 = Z_to_bv 64 (gF cx fp + GO_WAS + 3 * c + p)) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
assert (F19 : ew E 19 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 19%nat 19%bv eq_refl); exact G19).
assert (F20 : ew E 20 = Z_to_bv 64 (2 ^ 64 - 1 - (gF cx fp + GO_WAS + 3 * c)))
  by (rewrite (EE 20%nat 20%bv eq_refl); exact G20).
assert (F21 : ew E 21 = Z_to_bv 64 c) by (rewrite (EE 21%nat 21%bv eq_refl); exact G21).
assert (F22 : ew E 22 = Z_to_bv 64 3) by (rewrite (EE 22%nat 22%bv eq_refl); exact G22).
assert (F23 : ew E 23 = Z_to_bv 64 (gF cx fp + GO_WAS + 3 * c)) by (rewrite (EE 23%nat 23%bv eq_refl); exact G23).
assert (F24 : ew E 24 = Z_to_bv 64 2) by (rewrite (EE 24%nat 24%bv eq_refl); exact G24).
assert (F25 : ew E 25 = Z_to_bv 64 p) by (rewrite (EE 25%nat 25%bv eq_refl); exact G25).
assert (F27 : ew E 27 = Z_to_bv 64 c) by (rewrite (EE 27%nat 27%bv eq_refl); exact G27).
assert (F32 : ew E 32 = Z_to_bv 64 wb)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (F33 : ew E 33 = Z_to_bv 64 t)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (F34 : ew E 34 = Z_to_bv 64 (gF cx fp + GO_WAS))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
clear HE EE G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G27.
unfold GO_WAS in *.
(* 0x812a0: UBSan's check that was_set + 3c + p does not pass 2^64 (into the trap 0x81f48). *)
psrr_branch_tok RUN BR HS SHOK Bspan_U; [bfact; kill|].
bfact.
paj_run_tok RUN HS HJ SHOK Bspan_U; [first [apply awr_ok_nil | awr_ok_tac] |].
upd_uk.
psrr_branch_tok RUN BR HS SHOK Bspan_U.
{ (* was_set[c][p] <> 0: the cell is set, nothing to check *)
  bfact. assert (Hw1 : wb <> 0) by lia.
  next_cell HS HJ SHOK HUK c p. }
{ (* was_set[c][p] = 0: the cell is unset; its effective value must be the default *)
  bfact. assert (Hw0 : wb = 0) by lia.
  pose proof (Hm Hw0) as Heff.
  paj_run_tok RUN HS HJ SHOK Bspan_U; [first [apply awr_ok_nil | awr_ok_tac] |].
  upd_uk.
  (* The call of reac_headamp_tx_effective (t, c, p) at 0x812b8. *)
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  rewrite pa_sigma_reac_headamp_tx_effective.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    pose proof (umem_keep m1 mm HM1 HUK) as HMm;
    pose proof HMm as ((S8 & Sj) & _ & _ & _ & _ & HGTm & _);
    assert (S16 : rdword (aview SEGS (w_H W3) mm) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)))
      by exact (gsaved_s0 (ums mm) (conj S8 Sj));
    assert (Qsp : spZ rg = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)))
      by (unfold spZ at 1; rewrite Q2, F2, unsigned_lit_small by lia; lia);
    eapply SRr_bind;
    [ eapply (cl_callS B LAWS W3 rg mm _ GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
        [(GE_CID, fp)] ly3 S3 mdq k STK_reac_headamp_tx_effective [] 0 (c_sp1 cx - spZ (c_regs cx)) (getr rg 1) (gch cx)
        (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ W2 = W3 /\
           getr regs2 10 = w64 (eff (GrantSlotPlan.T_end pl) t c p) /\
           (t <> 0 -> obj_at SEGS (mrestrict (w_H W3) mem2) t HeadampLayout.LAY_TX
                        (HeadampLayout.tx_vals (GrantSlotPlan.T_end pl)))) HJ Qsp);
      [ apply sub_mod16; [exact Hsp32 | exact Hsp16]
      | lia
      | unfold STK_reac_headamp_tx_effective, ESTACK; lia
      | unfold STK_reac_headamp_tx_effective, ESTACK, GE_STK, STK_LLVMFuzzerTestOneInput; lia
      | rewrite Q3, F3; reflexivity
      | rewrite Q4, F4; reflexivity
      | reflexivity
      | rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]
      | rewrite Q1, unsigned_lit_small by lia; lia
      | replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia;
        unfold s0Z at 1; rewrite Q8, F8, unsigned_lit_small by lia;
        exact (ge_achain_ly cx ly3 S3 W3 mm _ _ _ (c_sp1 cx) HB HJ S8 S16 ltac:(lia))
      | intros HPRE1;
        exact (HEFF ly3 S3 W3 rg mm mdq (gch cx) t c p (GrantSlotPlan.T_end pl) HPRE1
          ltac:(rewrite Q10, F33; reflexivity) ltac:(rewrite Q11, F27; reflexivity) ltac:(rewrite Q12, F25; reflexivity)
          ltac:(lia) ltac:(lia) Htlen (or_intror (conj Htin (gtab_obj (ums mm) _ HGTm))))
      | intros a (rgx & [] & _) ]
    | ] end.
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (-> & -> & -> & Ha0 & _)).
  rewrite ?Z.add_0_r in HJ2.
  (* The call keeps every byte the loops rely on. *)
  assert (HUK1 : ge_keep cx fp W3 [(t, 460)] m1 mem2).
  { eapply ge_keep_trans; [exact HUK|].
    replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJc by lia.
    eapply ge_keep_call;
      first [ exact LAWS | exact HB | exact HJ | exact HFR | lia | exact HJc
            | (intros p0 n0 Hp0; unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hp0)
            | (constructor; [|constructor]; exists 460; cbn [fst snd];
               split; [exact Htin | change (req_size 460) with 460; lia]) ]. }
  (* Region 1, the spill slots 136 .. 160 the outer head reads back, survives the call. *)
  jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W3) mem2) HP2 [1%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { rkept HUK HUK1. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  rewrite Q1.
  remember (havoc E 35 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
  assert (HEIx1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDx1 : forall q, (q < 35)%nat -> ew E1 q = ew E q)
    by (intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq).
  assert (Fe39 : ew E1 39 = Z_to_bv 64 (dflt p)).
  { rewrite HE1. change 39%nat with (35 + 4)%nat.
    rewrite (YN3v.ew_havoc_new E 35 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia).
    cbn [nth map]. rewrite <- Heff. exact Ha0. }
  clear HE1.
  restate OLDx1.
  assert (SHOK1 : sh_ok SEGS Bx_U [] E1 (mrestrict (w_H W3) mem2)) by constructor.
  clear SHOK HJ HJc. rename SHOK1 into SHOK. rename HJ2 into HJ.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
  clear HUK. rename HUK1 into HUK.
  paj_run_tok RUN HS HJ SHOK Bspan_U; [first [apply awr_ok_nil | awr_ok_tac] |].
  upd_uk.
  (* The call of reac_headamp_default (p) at 0x812c4. *)
  pmkst HS.
  clear Q1 Q2 Q3 Q4 Q8 Q10 Q11 Q12.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
  rewrite pa_sigma_reac_headamp_default.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    pose proof (umem_keep m1 mm HM1 HUK) as HMm2;
    pose proof HMm2 as ((S8b & Sjb) & _);
    assert (S16b : rdword (aview SEGS (w_H W3) mm) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)))
      by exact (gsaved_s0 (ums mm) (conj S8b Sjb));
    assert (Qsp2 : spZ rg = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)))
      by (unfold spZ at 1; rewrite Q2; Fall; rewrite unsigned_lit_small by lia; lia);
    eapply SRr_bind;
    [ eapply (cl_callS B LAWS W3 rg mm _ GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
        [(GE_CID, fp)] ly3 S3 mdq k REAC_HEADAMP_DEFAULT_STK [] 0 (c_sp1 cx - spZ (c_regs cx)) (getr rg 1) (gch cx)
        (fun ly2 S2 W2 regs4 mem4 md4 => getr regs4 10 = w64 (dflt p) /\ ly2 = ly3 /\ S2 = S3 /\ W2 = W3 /\
           (forall x, mem4 x = mm x) /\ Permutation (ablocks B ly2 S2) (ablocks B ly3 S3)) HJ Qsp2);
      [ apply sub_mod16; [exact Hsp32 | exact Hsp16]
      | lia
      | unfold REAC_HEADAMP_DEFAULT_STK, ESTACK; lia
      | unfold REAC_HEADAMP_DEFAULT_STK, ESTACK, GE_STK, STK_LLVMFuzzerTestOneInput; lia
      | rewrite Q3; Fall; reflexivity
      | rewrite Q4; Fall; reflexivity
      | reflexivity
      | rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]
      | rewrite Q1, unsigned_lit_small by lia; lia
      | replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia;
        unfold s0Z at 1; rewrite Q8; Fall; rewrite unsigned_lit_small by lia;
        exact (ge_achain_ly cx ly3 S3 W3 mm _ _ _ (c_sp1 cx) HB HJ S8b S16b ltac:(lia))
      | intros HPRE2;
        exact (HDFLT ly3 S3 W3 rg mm mdq (gch cx) p HPRE2 ltac:(rewrite Q10; Fall; reflexivity) ltac:(lia))
      | intros a (rgx & [] & _) ]
    | ] end.
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs4 & mem4 & md4 & -> & HJ2 & HJc & HP4 & (Hd0 & -> & -> & -> & Hmem2 & _)).
  rewrite ?Z.add_0_r in HJ2.
  assert (HUK1 : ge_keep cx fp W3 [(t, 460)] m1 mem4) by (eapply ge_keep_trans; [exact HUK | apply ge_keep_pointwise; exact Hmem2]).
  (* The spill slots, now region 0, survive this call too. *)
  jafter_call_keep_pi HS 51%nat regs4 (mrestrict (w_H W3) mem4) HP4 [0%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { rkept HUK HUK1. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  rewrite Q1.
  remember (havoc E1 51 (map (getr regs4) CLOB)) as E2 eqn:HE2 in HS.
  assert (HEIx2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEIx1 | cbv; lia]).
  assert (OLDx2 : forall q, (q < 51)%nat -> ew E2 q = ew E1 q)
    by (intros q Hq; rewrite HE2; apply YN3v.ew_havoc_old; exact Hq).
  assert (Fd55 : ew E2 55 = Z_to_bv 64 (dflt p)).
  { rewrite HE2. change 55%nat with (51 + 4)%nat.
    rewrite (YN3v.ew_havoc_new E1 51 (map (getr regs4) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia).
    cbn [nth map]. exact Hd0. }
  clear HE2.
  restate OLDx2.
  assert (SHOK1 : sh_ok SEGS Bx_U [] E2 (mrestrict (w_H W3) mem4)) by constructor.
  clear SHOK HJ HJc. rename SHOK1 into SHOK. rename HJ2 into HJ.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
  clear HUK. rename HUK1 into HUK.
  (* 0x812c8: bne s10, a0 into the abort block 0x81d98: the effective value is the default. *)
  psrr_branch_tok RUN BR HS SHOK Bspan_U; [bfact; kill|].
  bfact.
  (* 0x812cc: beq s9, s8 — SENS (p = 2) or a switch. *)
  paj_run_tok RUN HS HJ SHOK Bspan_U; [first [apply awr_ok_nil | awr_ok_tac] |]. upd_uk.
  psrr_branch_tok RUN BR HS SHOK Bspan_U.
  { (* p = 2: 0x812ec bltu (s10 - 56) (-55) into 0x81d98: the default 32 is in 1..55. *)
    bfact.
    paj_run_tok RUN HS HJ SHOK Bspan_U; [first [apply awr_ok_nil | awr_ok_tac] |]. upd_uk.
    psrr_branch_tok RUN BR HS SHOK Bspan_U; [bfact; kill|].
    bfact. next_chan HS HJ SHOK HUK c p. }
  { (* p <> 2: 0x812d0 bnez s10 into 0x81d98: the default of a switch is 0. *)
    bfact.
    paj_run_tok RUN HS HJ SHOK Bspan_U; [first [apply awr_ok_nil | awr_ok_tac] |]. upd_uk.
    psrr_branch_tok RUN BR HS SHOK Bspan_U; [bfact; kill|].
    bfact. next_cell HS HJ SHOK HUK c p. } }
Qed.

End d.

(* ---- the block at 0x81224 and the whole phase ---- *)

Let RUNTO0 := paj_run_to B LAWS.

(* The spill slots the block writes, as windows of the machine frame at s1, and the two
   slots it reads back: 72 (the frame, atom 32) and 136 (was_set, atom 32 + 32). *)
Definition R_w16 : YP09.region := YP09.mkRegion (Some 9%nat) 16 24 16 24 [].
Definition R_w40 : YP09.region := YP09.mkRegion (Some 9%nat) 40 72 40 72 [].
Definition R_r72 : YP09.region := YP09.mkRegion (Some 9%nat) 72 80 0 0 [YP09.mkChunk 72 (CVal 8 (SOff 32 0))].
Definition R_w80 : YP09.region := YP09.mkRegion (Some 9%nat) 80 88 80 88 [].
Definition R_w96 : YP09.region := YP09.mkRegion (Some 9%nat) 96 128 96 128 [].
Definition R_r136 : YP09.region := YP09.mkRegion (Some 9%nat) 136 144 0 0 [YP09.mkChunk 136 (CVal 8 (SOff 32 32))].
Definition ss_u0 : sstate :=
  mkSS GP_unset0 sr_atoms [R_w16; R_w40; R_r72; R_w80; R_w96; R_r136] None
    (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).

(* A run that writes only into its windows keeps every byte outside them. *)
Lemma keep_outside : forall E rs (m m' : word -> option byte) (H : word -> bool) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs m m' H a HF Ha Hn. unfold aview, mbyte, mrestrict.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.
(* A word the run wrote into a window of the machine frame at s1 (atom 9). *)
Lemma slot_of_region9 : forall E ss ms (W : world SEGS) i lo hi wlo whi cs od e v sp1,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 9) = sp1 ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS (w_H W) (ms_mem ms)) (sp1 + od) = Some v.
Proof.
intros E ss ms W i lo hi wlo whi cs od e v sp1 HS Hi Hb Hin He Hv.
apply (rdword_of_val_mem SEGS (w_H W) (ms_mem ms)); [|exact Hv].
pose proof (st_ok_pi_region_nth E ss (restrict (w_H W) ms) i _ HS Hi) as Hr.
exact (field_of_region E _ 9%nat sp1 cs lo hi wlo whi od 8%N e v Hr Hb Hin He
  ltac:(cbn [Z.of_N]; change (8 * 8) with 64; exact Hv) ltac:(cbn [Z.of_N]; lia)).
Qed.

Theorem ge_unset : forall POST, ge_from B MT POST (GI_admit B MT) -> ge_from B MT POST (GI_unset0 B MT).
Proof.
intros POST HADM cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (t & HBODY & Hk & Hacc & HBLK & HCN & R19 & R12 & R23 & S0 & S8 & S24 & S32 & S72 & S88 &
  S128 & S136 & S144 & S152 & HGT & HGW & HGS & HREL & HI1).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G3 & G4) & HSV & HSH & HFL & Hlen & HIN).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_grant) (PI := PI)) as HBLO. rewrite IMG_LO_B_val in HBLO.
pose proof (gsp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16). unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp.
pose proof asan_consts as (C1 & _).
pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _ & _ & Hinp & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hfin) as (HF1 & HF2 & _).
assert (EgF : gF cx fp = frame_addr ly3 GE_CID fp) by (unfold gF, frame_addr; rewrite HlyF; reflexivity).
rewrite <- EgF in HF1, HF2. change (fs_frame_bytes GE_CID) with 1024 in HF2.
assert (Htin : In (t, 460) (ablocks B ly3 S3)) by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ t 460 HAR Htin) as (_ & Ht4096 & Htceil & _). change (req_size 460) with 460 in Htceil.
(* The input block lies below the allocator's ceiling, or is empty. *)
assert (Hinlo : c_n cx = 0 \/ (0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)).
{ destruct Hinp as [(Hn0 & _) | (Hn & Hin)]; [left; exact Hn0 | right].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & Hp4096 & Hpceil & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. lia. }
assert (Hpe : (GrantSlotPlan.pos_end (c_pl cx) <= length (c_pl cx))%nat) by apply SegCLib.pos_end_le.
assert (Hpv : 0 <= c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx)) < 2 ^ 64).
{ unfold c_n in Hinlo. destruct Hinp as [(Hn0 & Hp0) | (Hn & _)].
  - unfold c_n in Hn0. rewrite Hp0. unfold GE_EMPTY, A_EMPTY_B. lia.
  - unfold c_n in Hn. destruct Hinlo as [Hn0 | Hb]; lia. }
assert (Hbl : 0 <= c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx)) < 2 ^ 64)
  by (pose proof HCN as HCN'; unfold c_n in HCN' |- *; lia).
assert (HSHb : 0 <= gSH cx fp /\ gSH cx fp + 104 < alloc_ceiling).
{ unfold gSH, shadow_of_addr, SHADOW_OFF.
  pose proof (Z.div_lt_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (gF cx fp) 8 ltac:(lia) ltac:(lia)). lia. }
pose proof HSV as (Sra & Ssv).
(* The machine state as the engine's symbolic state at 0x81224. *)
assert (Hms : restrict (w_H W3) ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_unset0))
  (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hsvc, Hrom, Hfr, Hfcsr.
  subst. reflexivity. }
assert (U9 : bv_unsigned (ew (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (gF cx fp)])) 9) = c_sp1 cx)
  by (rewrite (ewR _ _ 9 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
(* The two slots the block reads, as chunks of the machine frame at s1. *)
assert (CK72 : Forall (YP09.chunk_ok SEGS (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (gF cx fp)]))
                 (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx)) [YP09.mkChunk 72 (CVal 8 (SOff 32 0))]).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ _ 72 8 (SOff 32 0) (gF cx fp)).
  - rewrite denot_off0, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ _ 0).
  - cbn [Z.of_N]. lia.
  - cbn [Z.of_N]. lia.
  - apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S72. }
assert (CK136 : Forall (YP09.chunk_ok SEGS (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (gF cx fp)]))
                 (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx)) [YP09.mkChunk 136 (CVal 8 (SOff 32 32))]).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ _ 136 8 (SOff 32 32) (gF cx fp + 32)).
  - cbn [sv_denot]. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra _ _ 0). cbn [nth].
    rewrite unsigned_lit_small by lia. reflexivity.
  - cbn [Z.of_N]. lia.
  - cbn [Z.of_N]. lia.
  - apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S136. }
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (gF cx fp)])) ss_u0 (restrict (w_H W3) ms3)).
{ rewrite Hms. unfold ss_u0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - assert (WR : forall o, 16 <= o < 128 -> writable_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + o))
      by (intros o Ho; apply (apresent_writable SEGS); apply HPRES; unfold GE_STK, STK_LLVMFuzzerTestOneInput; lia).
    unfold R_w16, R_w40, R_r72, R_w80, R_w96, R_r136.
    repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok; cbv zeta;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val]; rewrite U9;
      (split; [lia|]); (split; [lia|]); (split; [intros o Ho; first [apply WR; lia | lia] |]);
      first [apply Forall_nil | exact CK72 | exact CK136].
  - unfold R_w16, R_w40, R_r72, R_w80, R_w96, R_r136.
    cbn [YP09.pairwise_disjoint YP09.all_disjoint]; repeat split;
      unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32. split; [lia|]. split; [exact Hsp32 | lia]. }
assert (SHOK : sh_ok SEGS Bx_U [] (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (gF cx fp)])) (mrestrict (w_H W3) (ms_mem ms3)))
  by constructor.
clear CK72 CK136.
remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (gF cx fp)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r Hq; subst E; apply ewR; exact Hq).
assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
assert (F3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), G3; exact Hgp0).
assert (F4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), G4; exact Htp0).
assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
assert (F12 : ew E 12 = Z_to_bv 64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))))
  by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (F19 : ew E 19 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (F23 : ew E 23 = Z_to_bv 64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))))
  by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (F32 : ew E 32 = Z_to_bv 64 (gF cx fp))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
clear HE EE.
(* The block: ten spill slots written, slots 72 and 136 read back, then the outer head for
   channel 0, up to the inner loop's head 0x812a0. *)
paj_run_to_tok RUNTO0 HS HJ SHOK Bspan_U GU_in;
[ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
  repeat first [ apply awr_ok_nil
               | apply awr_ok_cons_ro; [cbn; lia|]
               | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                 [reflexivity | rewrite U9; lia | cbn; unfold GE_STK, STK_LLVMFuzzerTestOneInput; lia | cbn; lia | ] ]
| ].
repeat match goal with H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
lazymatch goal with
| HFx : frame_of _ ?rsB (ms_mem ms3) (ms_mem ?msN), HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ =>
  (* The block writes only its four windows of the machine frame. *)
  assert (KOUT : forall a, 0 <= a < 2 ^ 64 ->
    ~ (c_sp1 cx + 16 <= a < c_sp1 cx + 24) -> ~ (c_sp1 cx + 40 <= a < c_sp1 cx + 72) ->
    ~ (c_sp1 cx + 80 <= a < c_sp1 cx + 88) -> ~ (c_sp1 cx + 96 <= a < c_sp1 cx + 128) ->
    aview SEGS (w_H W3) (ms_mem msN) a = aview SEGS (w_H W3) (ms_mem ms3) a);
  [ intros a Ha N1 N2 N3 N4; apply (keep_outside E rsB _ _ (w_H W3) a HFx Ha);
    let rs' := eval vm_compute in rsB in change rsB with rs';
    intros (r & Hr & Hb); cbn [In] in Hr;
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite U9 in Hb; lia |]);
    destruct Hr
  | ];
  assert (AVK : forall a, 0 <= a < c_sp1 cx + 16 ->
    aview SEGS (w_H W3) (ms_mem msN) a = aview SEGS (w_H W3) (ms_mem ms3) a)
    by (intros a Ha; apply KOUT; lia);
  assert (RK : forall a v, rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
    (forall i, 0 <= i < 8 -> ~ (c_sp1 cx + 16 <= a + i < c_sp1 cx + 24) /\ ~ (c_sp1 cx + 40 <= a + i < c_sp1 cx + 72) /\
       ~ (c_sp1 cx + 80 <= a + i < c_sp1 cx + 88) /\ ~ (c_sp1 cx + 96 <= a + i < c_sp1 cx + 128)) ->
    rdword (aview SEGS (w_H W3) (ms_mem msN)) a = Some v);
  [ intros a v H Ha0 Ha1 Hn; rewrite <- H; apply rdword_ext; intros i Hi;
    destruct (Hn i Hi) as (N1 & N2 & N3 & N4); apply KOUT; [lia | exact N1 | exact N2 | exact N3 | exact N4]
  | ];
  rename msN into msF; rename HSx into HSF; rename HFx into HFF
end.
assert (Hgf : 0 <= gF cx fp < 2 ^ 64) by lia.
(* The words the block wrote, read back from its windows (region 0: [16, 24); 1: [40, 72);
   3: [80, 88); 4: [96, 128)). *)
assert (W16 : gslot cx W3 msF 16 (gF cx fp + GO_RAW)) by
  exact (slot_of_region9 E _ msF W3 0%nat _ _ _ _ _ 16 (SOff 32 560) (gF cx fp + 560) (c_sp1 cx) HSF eq_refl U9
    ltac:(cbn [In]; tauto) (denot_off_val E 32 _ 560 F32 Hgf) ltac:(lia)).
assert (W40 : gslot cx W3 msF 40 (gF cx fp + GO_UNSET)) by
  exact (slot_of_region9 E _ msF W3 1%nat _ _ _ _ _ 40 (SOff 32 576) (gF cx fp + 576) (c_sp1 cx) HSF eq_refl U9
    ltac:(cbn [In]; tauto) (denot_off_val E 32 _ 576 F32 Hgf) ltac:(lia)).
assert (W48 : gslot cx W3 msF 48 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx)))) by
  exact (slot_of_region9 E _ msF W3 1%nat _ _ _ _ _ 48 (SOff 23 0) _ (c_sp1 cx) HSF eq_refl U9
    ltac:(cbn [In]; tauto) ltac:(rewrite denot_off0; exact F23) Hpv).
assert (W56 : gslot cx W3 msF 56 (gF cx fp + GO_LIT)) by
  exact (slot_of_region9 E _ msF W3 1%nat _ _ _ _ _ 56 (SOff 32 544) (gF cx fp + 544) (c_sp1 cx) HSF eq_refl U9
    ltac:(cbn [In]; tauto) (denot_off_val E 32 _ 544 F32 Hgf) ltac:(lia)).
assert (W64 : gslot cx W3 msF 64 (gF cx fp + GO_CH)) by
  exact (slot_of_region9 E _ msF W3 1%nat _ _ _ _ _ 64 (SOff 32 784) (gF cx fp + 784) (c_sp1 cx) HSF eq_refl U9
    ltac:(cbn [In]; tauto) (denot_off_val E 32 _ 784 F32 Hgf) ltac:(lia)).
assert (W80 : gslot cx W3 msF 80 (gF cx fp + GO_POLL)) by
  exact (slot_of_region9 E _ msF W3 3%nat _ _ _ _ _ 80 (SOff 32 464) (gF cx fp + 464) (c_sp1 cx) HSF eq_refl U9
    ltac:(cbn [In]; tauto) (denot_off_val E 32 _ 464 F32 Hgf) ltac:(lia)).
assert (W96 : gslot cx W3 msF 96 (gF cx fp + GO_VAL)) by
  exact (slot_of_region9 E _ msF W3 4%nat _ _ _ _ _ 96 (SOff 32 816) (gF cx fp + 816) (c_sp1 cx) HSF eq_refl U9
    ltac:(cbn [In]; tauto) (denot_off_val E 32 _ 816 F32 Hgf) ltac:(lia)).
assert (W104 : gslot cx W3 msF 104 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx)))) by
  exact (slot_of_region9 E _ msF W3 4%nat _ _ _ _ _ 104 (SOff 12 0) _ (c_sp1 cx) HSF eq_refl U9
    ltac:(cbn [In]; tauto) ltac:(rewrite denot_off0; exact F12) Hbl).
assert (W112 : gslot cx W3 msF 112 (gF cx fp + GO_PAR)) by
  exact (slot_of_region9 E _ msF W3 4%nat _ _ _ _ _ 112 (SOff 32 800) (gF cx fp + 800) (c_sp1 cx) HSF eq_refl U9
    ltac:(cbn [In]; tauto) (denot_off_val E 32 _ 800 F32 Hgf) ltac:(lia)).
assert (W120 : gslot cx W3 msF 120 (gF cx fp + GO_A)) by
  exact (slot_of_region9 E _ msF W3 4%nat _ _ _ _ _ 120 (SOff 32 448) (gF cx fp + 448) (c_sp1 cx) HSF eq_refl U9
    ltac:(cbn [In]; tauto) (denot_off_val E 32 _ 448 F32 Hgf) ltac:(lia)).
(* What GI_admit reads of the memory, after the block. *)
assert (HUM : umem cx fp ly3 S3 W3 t (ms_mem msF)).
{ pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (_ & Lws & Lst & _).
  unfold gslot in W16, W40, W48, W56, W64, W80, W96, W104, W112, W120,
    S0, S8, S24, S32, S72, S88, S128, S136, S144, S152.
  destruct HGT as (Tin & Tpos & Tlen & Tb). unfold gfarr in HGW, HGS. cbn [ms_mem] in HGW, HGS.
  unfold umem, uslots, ums, gsaved, gshadow, gslot, gtab, gfarr. cbn [ms_mem mkst].
  repeat match goal with |- _ /\ _ => split end;
  first
  [ exact W16 | exact W40 | exact W48 | exact W56 | exact W64 | exact W80 | exact W96 | exact W104
  | exact W112 | exact W120 | exact Tin | exact Tpos | exact Tlen
  | (intros j Hj; apply (RK _ _ (Ssv j Hj)); [lia | lia | intros i Hi; repeat split; lia])
  | (apply (RK _ _ Sra); [lia | lia | intros i Hi; repeat split; lia])
  | (apply (RK _ _ HFL); [lia | lia | intros i Hi; repeat split; lia])
  | (apply (RK _ _ S0); [lia | lia | intros i Hi; repeat split; lia])
  | (apply (RK _ _ S8); [lia | lia | intros i Hi; repeat split; lia])
  | (apply (RK _ _ S24); [lia | lia | intros i Hi; repeat split; lia])
  | (apply (RK _ _ S32); [lia | lia | intros i Hi; repeat split; lia])
  | (apply (RK _ _ S72); [lia | lia | intros i Hi; repeat split; lia])
  | (apply (RK _ _ S88); [lia | lia | intros i Hi; repeat split; lia])
  | (apply (RK _ _ S128); [lia | lia | intros i Hi; repeat split; lia])
  | (apply (RK _ _ S136); [lia | lia | intros i Hi; repeat split; lia])
  | (apply (RK _ _ S144); [lia | lia | intros i Hi; repeat split; lia])
  | (apply (RK _ _ S152); [lia | lia | intros i Hi; repeat split; lia])
  | (intros i Hi; assert (Hl : length GSH_tables = 104%nat) by reflexivity;
     rewrite AVK; [exact (HSH i Hi) | lia])
  | (intros i Hi H1 H2 H3; rewrite AVK; [exact (Tb i Hi H1 H2 H3) | lia])
  | (apply (garr8_frame SEGS _ _ _ _ HIN); intros a Ha; apply (mbyte_of_aview SEGS); apply AVK;
     rewrite length_map in Ha; unfold c_n in Hinlo; destruct Hinlo as [Hn0 | Hb]; lia)
  | (apply (garr8_frame SEGS _ _ _ _ HGW); intros a Ha; apply (mbyte_of_aview SEGS); apply AVK;
     rewrite length_map, Lws in Ha; unfold GO_WAS in Ha; lia)
  | (apply (garr8_frame SEGS _ _ _ _ HGS); intros a Ha; apply (mbyte_of_aview SEGS); apply AVK;
     rewrite length_map, Lst in Ha; unfold GO_SET in Ha; lia)
  ]. }
(* The loops' head, cell (0, 0). *)
pmkst HSF.
repeat rewrite wvb_collapse in HJ.
apply (uloop cx fp k acc ly3 S3 W3 t HB POST HADM HFR HMO Hk Hacc HBLK HCN (ms_mem msF) HUM HREL HI1 144%nat 0 0).
- vm_compute. lia.
- unfold UINV, GO_WAS. split; [lia|]. split; [lia|].
  repeat (split; [regval HSF|]).
  split; [exact HJ | apply ge_keep_refl].
Qed.

End c.
End b.
End a.
