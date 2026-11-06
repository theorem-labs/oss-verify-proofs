(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_cmp_st: the symbolic cut states of image B's LLVMFuzzerTestOneInput cmp segment
   (llvm_b_cmp_stmt, +0x6f0 .. +0x83c), built from the interface's frame invariant and the cut point's memory clauses
   (cm_mem, lib/B/Prog/LLVMFuzzerTestOneInput_segX_cmp_kit.v):
     cm_stok   at +0x6f0 (and any pc): the spill area at s1 with its one write window 48(s1);
     cm_stokL2 at +0x718, the head of the scan loop L2: the read-only spill slots, the byte out + i and its shadow;
     cm_stokL  at the bcmp loops' cuts (+0x7c0, +0x7d4, +0x7f4): the read-only spill slots with 48(s1) = 3 * ns.
   The form is cgif lib/A/ACf5.v:207 entry_st_ok_full and a Theorem Labs lane's GrantEntrySweepS2.v:305 (a turn's state with
   the row as an atom, its alias and its shadow entry), on this unit's Pa kit. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YN1y.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YC5d YI16 YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal YC1g YC1h YC1i YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
DecodeBSyms DecodeBList DecodeBAddr DecodeBPa DecodeBImg DecodeBPaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_segX_cmp_defs
LLVMFuzzerTestOneInput_segX_cmp_kit.
Import ListNotations.
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* The listing's base is the function's entry: decodeb_val A_TEXT = decodeb_text = DEC_A_LLVMF. *)
Lemma cm_base_eqS : decodeb_val A_TEXT = DEC_A_LLVMF.
Proof. vm_compute. reflexivity. Qed.

(* lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_a.v awr_ro / up_memeq / up_memchain: a run over read-only regions
   writes nothing, so the memory after it is the one before it (lib/Reusable/YN1y.v:94 frame_of_nowin). *)
Ltac cm_awr_ro := lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac cm_memeq HF :=
  lazymatch type of HF with frame_of _ ?rs ?m0 ?m1 =>
    let H := fresh "Hmn" in
    pose proof (frame_of_nowin _ rs m0 m1 ltac:(vm_compute; repeat constructor) HF) as H;
    try (lazymatch goal with Hm : m0 = _ |- _ => rewrite Hm in H; clear Hm end);
    rename H into Hmem
  end; clear HF; try (lazymatch goal with H : frame_of _ _ _ _ |- _ => clear H end);
  try (lazymatch goal with H : mem_grows _ _ |- _ => clear H end).

(* A register of the state the walk stopped in, by its value (a Theorem Labs lane's GrantEntrySweepS2.v:142 rw_reg / rw_close). *)
Ltac cm_val HS :=
  lazymatch goal with |- YK11.getr (ms_regs ?m) ?r = _ =>
    let R := fresh "R" in prreg HS r R; rewrite R; clear R end;
  repeat match goal with H : ew ?E ?n = _ |- context [ew ?E ?n] => rewrite H end;
  first [ lazymatch goal with |- ?x = ?x => reflexivity end
        | unfold w64; rewrite ?unsigned_lit_small by lia; rewrite ?alu64_add_lit; f_equal; ring
        | lazymatch goal with |- ?g => stdpp.tactics.is_closed_term g end; apply bv_eq; vm_compute; reflexivity ].

(* A register of the state the walk stopped in, as the U value of its expression (for the expressions cm_val's
   rewriting does not reach: xor -1, mul). *)
Ltac cm_valU HS :=
  lazymatch goal with |- YK11.getr (ms_regs ?m) ?r = _ =>
    lazymatch type of HS with
    | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?H ?msx) =>
        rewrite (st_ok_pi_restrict_reg H Ex ssx msx r HS);
        let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e
    end
  end;
  rewrite denot_lit_U; unfold w64; f_equal.
(* The engine's branch conditions at concrete words. *)
Lemma cm_bne : forall x y : word, branch_taken BC_NE x y = negb (bv_unsigned x =? bv_unsigned y).
Proof. reflexivity. Qed.
Lemma cm_beq : forall x y : word, branch_taken BC_EQ x y = (bv_unsigned x =? bv_unsigned y).
Proof. reflexivity. Qed.
Lemma cm_bltu : forall x y : word, branch_taken BC_LTU x y = (bv_unsigned x <? bv_unsigned y).
Proof. intros x y. cbn [branch_taken]. unfold bv_ltu. reflexivity. Qed.
Lemma cm_signed_lit : forall v, - 2 ^ 63 <= v < 2 ^ 63 -> bv_signed (Z_to_bv 64 v) = v.
Proof.
intros v Hv. unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite Z.add_mod_idemp_l by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma cm_bge : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. unfold bv_lts. rewrite !cm_signed_lit by lia. reflexivity. Qed.
Lemma cm_or0 : forall z, alu64 ALU_OR (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
intros z. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (0 mod 2 ^ 64) with 0. rewrite Z.lor_0_l. apply Z.mod_mod. lia.
Qed.
Lemma cm_or_m1 : forall z, alu64 ALU_OR (Z_to_bv 64 (-1)) (Z_to_bv 64 z) = Z_to_bv 64 (-1).
Proof.
intros z. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite cm_lor_ones by (apply Z.mod_pos_bound; lia). reflexivity.
Qed.
(* A hypothesis about the state the walk stopped in, at the values of the atoms (prreg_norm of
   lib/B/Prog/DecodeBPaLib.v, then the env's equations). *)
Ltac cm_norm H :=
  cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add] in H;
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in H;
  repeat match goal with Eq : ew ?E ?n = _ |- _ => rewrite Eq in H end.
(* ra of the state the walk stopped in: a code pointer of the listing (lib/B/Prog/DecodeBPaLib.v codeptr_val). *)
Ltac cm_ra HS :=
  lazymatch type of HS with
  | st_ok ?sg ?Ex ?ssx (restrict ?H ?msx) =>
      rewrite (st_ok_restrict_reg sg H Ex ssx msx (1%bv : bv 5) HS);
      let e := eval vm_compute in (sr_get (ss_regs ssx) (1%bv : bv 5)) in change (sr_get (ss_regs ssx) (1%bv : bv 5)) with e;
      lazymatch goal with HEIx : img_env _ _ Ex |- _ => rewrite (codeptr_val (PI := PI_decodeb) Ex _ HEIx) end
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?H ?msx) =>
      rewrite (st_ok_pi_restrict_reg H Ex ssx msx (1%bv : bv 5) HS);
      let e := eval vm_compute in (sr_get (ss_regs ssx) (1%bv : bv 5)) in change (sr_get (ss_regs ssx) (1%bv : bv 5)) with e;
      lazymatch goal with HEIx : img_env _ _ Ex |- _ => rewrite (codeptr_val (PI := PI_decodeb) Ex _ HEIx) end
  end.
(* bv_unsigned (Z_to_bv 64 z) = z, innermost first. *)
Ltac cm_unlit H :=
  repeat match type of H with context [bv_unsigned (Z_to_bv 64 ?z)] =>
    lazymatch z with context [bv_unsigned _] => fail | _ => rewrite (unsigned_lit_small z) in H by lia end end.

Section Cmp.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := decodesegsB0.
#[local] Notation VAL := decodeb_val.
#[local] Notation SK := dec_B_sink_head.
#[local] Notation PID := (@PI_decodeb rc).

(* every byte a view shows is a byte *)
Lemma cm_aview_byte : forall (H : word -> bool) mem x,
  match aview SEGS H mem x with Some b => 0 <= b < 256 | None => True end.
Proof.
intros H mem x. unfold aview. destruct (mbyte SEGS (mrestrict H mem) x) as [b|] eqn:E; cbn; [|exact I].
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr. exact Hr.
Qed.

Lemma cm_rdword_range : forall (H : word -> bool) mem a v,
  rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw.
pose proof (cm_aview_byte H mem a) as B0.
pose proof (cm_aview_byte H mem (a + 1)) as B1.
pose proof (cm_aview_byte H mem (a + 2)) as B2.
pose proof (cm_aview_byte H mem (a + 3)) as B3.
pose proof (cm_aview_byte H mem (a + 4)) as B4.
pose proof (cm_aview_byte H mem (a + 5)) as B5.
pose proof (cm_aview_byte H mem (a + 6)) as B6.
pose proof (cm_aview_byte H mem (a + 7)) as B7.
unfold rdword in Hw.
destruct (aview SEGS H mem a) as [b0|]; [|discriminate].
destruct (aview SEGS H mem (a + 1)) as [b1|]; [|discriminate].
destruct (aview SEGS H mem (a + 2)) as [b2|]; [|discriminate].
destruct (aview SEGS H mem (a + 3)) as [b3|]; [|discriminate].
destruct (aview SEGS H mem (a + 4)) as [b4|]; [|discriminate].
destruct (aview SEGS H mem (a + 5)) as [b5|]; [|discriminate].
destruct (aview SEGS H mem (a + 6)) as [b6|]; [|discriminate].
destruct (aview SEGS H mem (a + 7)) as [b7|]; [|discriminate].
injection Hw as <-. change (2 ^ 64) with 18446744073709551616. lia.
Qed.

(* A view byte as a one-byte val_mem. *)
Lemma cm_val_mem1 : forall (H : word -> bool) mem a v,
  aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H mem) a) as [b|] eqn:E; [|discriminate].
cbn in Hv. injection Hv as Hv. f_equal. subst v.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
rewrite (le_byte_small (bv_unsigned b) 1 0) by (cbn; lia).
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Section Walk.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Variable cx : dctx.

(* The env of every cut: the registers, then atoms 32.. the segment's spilled values, 44 the byte the scan loop
   reads and 45 the 48(s1) slot, then the image's own atoms above A_TEXT. *)
Definition cm_extra (out res len ns64 nch32 ns32 x44 x45 : Z) : list word :=
  [w64 SHADOW_OFF; w64 out; w64 res; w64 len; w64 ns64; w64 nch32; w64 ns32;
   w64 (res + 50); w64 (d_F cx); w64 (d_SH cx); w64 0; w64 0; w64 x44; w64 x45].
Definition cm_env (regs : bvmap 5 word) (out res len ns64 nch32 ns32 x44 x45 : Z) : env :=
  @Eimg rc decodeb_listing PID (Ereg regs (cm_extra out res len ns64 nch32 ns32 x44 x45)).
Definition cm_ss (pc : Z) : sstate := mkSS pc sr_atoms [cm_spill] None cm_facts0.

Lemma cm_env_reg : forall regs out res len ns64 nch32 ns32 x44 x45 n (r : bv 5),
  Z.of_nat n = bv_unsigned r -> ew (cm_env regs out res len ns64 nch32 ns32 x44 x45) n = YK11.getr regs r.
Proof.
intros regs out res len ns64 nch32 ns32 x44 x45 n r Hnr. unfold cm_env.
pose proof (u5_range r). rewrite (@Eimg_low rc decodeb_listing PID) by (unfold A_TEXT; lia).
exact (ew_Ereg_nat regs _ n r Hnr).
Qed.

Lemma cm_env_img : forall regs out res len ns64 nch32 ns32 x44 x45,
  img_env VAL A_LIM (cm_env regs out res len ns64 nch32 ns32 x44 x45).
Proof. intros. unfold cm_env. apply (@Eimg_env rc decodeb_listing PID). Qed.

Lemma cm_env_agree : forall regs out res len ns64 nch32 ns32 x44 x45,
  env_agree 32 (Ereg regs (cm_extra out res len ns64 nch32 ns32 x44 x45)) (cm_env regs out res len ns64 nch32 ns32 x44 x45).
Proof.
intros. split; [|reflexivity]. intros n Hn. unfold cm_env.
first [ symmetry; apply (@Eimg_low rc decodeb_listing PID) | apply (@Eimg_low rc decodeb_listing PID) ]; unfold A_TEXT; lia.
Qed.

Ltac cm_extra_tac i :=
  unfold cm_env; rewrite (@Eimg_low rc decodeb_listing PID) by (unfold A_TEXT; lia);
  exact (ew_Ereg_extra _ _ i).

Lemma cm_env_32 : forall regs out res len ns64 nch32 ns32 x44 x45,
  ew (cm_env regs out res len ns64 nch32 ns32 x44 x45) 32 = w64 SHADOW_OFF.
Proof. intros. cm_extra_tac 0%nat. Qed.
Lemma cm_env_33 : forall regs out res len ns64 nch32 ns32 x44 x45,
  ew (cm_env regs out res len ns64 nch32 ns32 x44 x45) 33 = w64 out.
Proof. intros. cm_extra_tac 1%nat. Qed.
Lemma cm_env_34 : forall regs out res len ns64 nch32 ns32 x44 x45,
  ew (cm_env regs out res len ns64 nch32 ns32 x44 x45) 34 = w64 res.
Proof. intros. cm_extra_tac 2%nat. Qed.
Lemma cm_env_35 : forall regs out res len ns64 nch32 ns32 x44 x45,
  ew (cm_env regs out res len ns64 nch32 ns32 x44 x45) 35 = w64 len.
Proof. intros. cm_extra_tac 3%nat. Qed.
Lemma cm_env_36 : forall regs out res len ns64 nch32 ns32 x44 x45,
  ew (cm_env regs out res len ns64 nch32 ns32 x44 x45) 36 = w64 ns64.
Proof. intros. cm_extra_tac 4%nat. Qed.
Lemma cm_env_37 : forall regs out res len ns64 nch32 ns32 x44 x45,
  ew (cm_env regs out res len ns64 nch32 ns32 x44 x45) 37 = w64 nch32.
Proof. intros. cm_extra_tac 5%nat. Qed.
Lemma cm_env_38 : forall regs out res len ns64 nch32 ns32 x44 x45,
  ew (cm_env regs out res len ns64 nch32 ns32 x44 x45) 38 = w64 ns32.
Proof. intros. cm_extra_tac 6%nat. Qed.
Lemma cm_env_39 : forall regs out res len ns64 nch32 ns32 x44 x45,
  ew (cm_env regs out res len ns64 nch32 ns32 x44 x45) 39 = w64 (res + 50).
Proof. intros. cm_extra_tac 7%nat. Qed.
Lemma cm_env_40 : forall regs out res len ns64 nch32 ns32 x44 x45,
  ew (cm_env regs out res len ns64 nch32 ns32 x44 x45) 40 = w64 (d_F cx).
Proof. intros. cm_extra_tac 8%nat. Qed.
Lemma cm_env_41 : forall regs out res len ns64 nch32 ns32 x44 x45,
  ew (cm_env regs out res len ns64 nch32 ns32 x44 x45) 41 = w64 (d_SH cx).
Proof. intros. cm_extra_tac 9%nat. Qed.
Lemma cm_env_44 : forall regs out res len ns64 nch32 ns32 x44 x45,
  ew (cm_env regs out res len ns64 nch32 ns32 x44 x45) 44 = w64 x44.
Proof. intros. cm_extra_tac 12%nat. Qed.
Lemma cm_env_45 : forall regs out res len ns64 nch32 ns32 x44 x45,
  ew (cm_env regs out res len ns64 nch32 ns32 x44 x45) 45 = w64 x45.
Proof. intros. cm_extra_tac 13%nat. Qed.

(* The realigned stack of this frame: above the allocator ceiling, 32-aligned, and present. *)
Lemma cm_sp1 : forall ly S W regs mem md k,
  dec_b_core B cx ly S W regs mem md k ->
  alloc_ceiling < d_sp1 cx /\ d_sp1 cx + 120 <= 2 ^ 47 /\ d_sp1 cx mod 32 = 0 /\
  (forall a, d_sp1 cx <= a < d_sp1 cx + 120 -> apresent (w_H W) mem a).
Proof.
intros ly S W regs mem md k HC.
destruct HC as (HJ & Hfrms & R8 & R9 & Hspz & Hsp0b & Hal32 & Rgp & Rtp & HSAV
                & HF4096 & HFal & HFpres & HFL & HPin & HPL).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
destruct Hstk as (Hal16 & HSTK & Hceil & Hlo2 & Hhi2 & H47 & _ & _ & _).
assert (HS : DEC_LLVMF_STK = 32768) by reflexivity.
split; [clear - Hsp0b Hceil Hlo2 HS; lia|].
split; [clear - Hsp0b Hhi2 H47 Hlo2 HS; lia|].
split; [exact Hal32|].
intros a Ha. apply Hpres. clear - Ha Hsp0b HS; lia.
Qed.

(* The frame invariant at the same memory after a run that kept sp, gp, tp, s0 and s1 (the journal comes from the
   run). *)
Lemma cm_core_regs : forall ly S W regs mem md k regs2 md2,
  dec_b_core B cx ly S W regs mem md k ->
  @ajournal rc dec_B_sink_head SEGS B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S W mem md2 k ->
  YK11.getr regs2 2 = YK11.getr regs 2 -> YK11.getr regs2 3 = YK11.getr regs 3 ->
  YK11.getr regs2 4 = YK11.getr regs 4 -> YK11.getr regs2 8 = YK11.getr regs 8 ->
  YK11.getr regs2 9 = YK11.getr regs 9 ->
  dec_b_core B cx ly S W regs2 mem md2 k.
Proof.
intros ly S W regs mem md k regs2 md2 HC HJ2 E2 E3 E4 E8 E9.
destruct HC as (_ & Hfrs & Hs0 & Hs1 & Hsp & Hr1 & Hr2 & Hgp & Htp & REST).
split; [exact HJ2|]. split; [exact Hfrs|]. split; [rewrite E8; exact Hs0|]. split; [rewrite E9; exact Hs1|].
split; [unfold spZ in *; rewrite E2; exact Hsp|].
split; [exact Hr1|]. split; [exact Hr2|]. split; [rewrite E3; exact Hgp|]. split; [rewrite E4; exact Htp|].
exact REST.
Qed.

(* The value of the spill area's base atom. *)
Lemma cm_E9 : forall regs out res len ns64 nch32 ns32 x44 x45,
  YK11.getr regs 9 = w64 (d_sp1 cx) -> 0 <= d_sp1 cx < 2 ^ 64 ->
  bv_unsigned (ew (cm_env regs out res len ns64 nch32 ns32 x44 x45) 9) = d_sp1 cx.
Proof.
intros regs out res len ns64 nch32 ns32 x44 x45 R9 H64.
rewrite (cm_env_reg regs _ _ _ _ _ _ _ _ 9%nat (9%bv : bv 5) eq_refl), R9.
unfold w64. apply unsigned_lit_small. exact H64.
Qed.

Ltac cm_chunk H EV :=
  lazymatch type of H with dec_b_slot _ _ _ ?v =>
  apply (chunk_ok_val SEGS _ _ _ _ 8%N _ v);
  [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EV
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (cm_rdword_range _ _ _ _ H)
  | cbn; lia | exact (val_mem_of_rdword SEGS _ _ _ _ H) ] end.

(* +0x6f0: the spill area at s1, every slot as a chunk over an atom, its one write window 48(s1), the shadow base as
   atom 32 (cgif lib/A/ACf5.v:207 entry_st_ok_full, a Theorem Labs lane's GrantEntrySweepS2.v:305). *)
Lemma cm_stok : forall (W : world SEGS) ly S regs mem md k out res mode nch ns pc x44 x45,
  dec_b_core B cx ly S W regs mem md k ->
  cm_mem cx out res mode nch ns W mem ->
  4096 <= out <= alloc_ceiling -> 4096 <= res <= alloc_ceiling ->
  st_ok_pi SEGS VAL
    (cm_env regs out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) x44 x45)
    (cm_ss pc)
    (restrict (w_H W) (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + pc)) mem (YK11.seg_rom SEGS))).
Proof.
intros W ly S regs mem md k out res mode nch ns pc x44 x45 HC HM Hout Hres.
destruct (cm_sp1 ly S W regs mem md k HC) as (Hsp1lo & Hsp1hi & Hsp1al & Hsp1pres).
pose proof (@alloc_ceiling_val rc) as [ACR _].
assert (Hsp64 : 0 <= d_sp1 cx < 2 ^ 64).
{ revert Hsp1lo Hsp1hi. generalize (d_sp1 cx). intros z H1 H2. lia. }
pose proof HC as (_ & _ & _ & R9 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
destruct HM as (HFRS & HFSH & HMODE & HBODY & H24 & H32 & H40 & H56 & H64 & H72 & H80 & H88 & H112).
destruct HFRS as (H0 & H8 & H16).
set (E := cm_env regs out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) x44 x45).
assert (E9 : bv_unsigned (ew E 9) = d_sp1 cx) by (subst E; apply cm_E9; [exact R9 | exact Hsp64]).
assert (E32 : ew E 32 = w64 SHADOW_OFF) by (subst E; apply cm_env_32).
assert (E33 : ew E 33 = w64 out) by (subst E; apply cm_env_33).
assert (E34 : ew E 34 = w64 res) by (subst E; apply cm_env_34).
rewrite restrict_mkst_fx. unfold cm_ss.
apply (@pa_entry_st_ok_full fx rc decodeb_listing PID E pc sr_atoms regs [cm_spill] cm_facts0
         (mrestrict (w_H W) mem)).
- subst E. unfold cm_env. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold cm_spill, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
  split; [lia|]. split; [lia|].
  split.
  { intros o Ho. apply (apresent_writable SEGS). apply Hsp1pres. lia. }
  repeat apply Forall_cons; try apply Forall_nil.
  + cm_chunk H0 cm_env_40.
  + cm_chunk H8 cm_env_41.
  + cm_chunk H16 cm_env_40.
  + cm_chunk H24 cm_env_35.
  + cm_chunk H32 cm_env_32.
  + cm_chunk H40 cm_env_34.
  + cm_chunk H56 cm_env_38.
  + cm_chunk H64 cm_env_37.
  + cm_chunk H72 cm_env_36.
  + cm_chunk H80 cm_env_39.
  + cm_chunk H88 cm_env_33.
  + cm_chunk H112 cm_env_40.
- cbn. split; exact I.
- split; [|split; [exact I | exact I]].
  cbn [cm_facts0 cm_atoms0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  unfold CM_SP_LO, CM_BLK_HI.
  split; [| split; [| split; [| split; [|exact I]]]].
  + rewrite E32. unfold w64, SHADOW_OFF.
    rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
  + rewrite E9. change (2 ^ 5) with 32. rewrite Hsp1al. lia.
  + rewrite E33. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
  + rewrite E34. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

(* The one write window of the head state, 48(s1), is this frame's own stack: what the run may change
   (lib/Reusable/YCbq.v:2170 awr_ok_cons_stack_off). *)
Lemma cm_awr : forall regs out res len ns64 nch32 ns32 x44 x45 ly S pc,
  YK11.getr regs 9 = w64 (d_sp1 cx) -> 0 <= d_sp1 cx < 2 ^ 64 ->
  d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 ->
  awr_ok (cm_env regs out res len ns64 nch32 ns32 x44 x45) (ss_mem (cm_ss pc)) DEC_LLVMF_STK (d_sp0 cx) []
    (ablocks B (d_ly cx) (d_S cx)) (ablocks B ly S) ly [(DEC_FCLASS, d_fpos cx)].
Proof.
intros regs out res len ns64 nch32 ns32 x44 x45 ly S pc R9 H64 Hsp0b.
assert (HS : DEC_LLVMF_STK = 32768) by reflexivity.
unfold cm_ss. cbn [ss_mem].
apply (awr_ok_cons_stack_off (cm_env regs out res len ns64 nch32 ns32 x44 x45) cm_spill []
         DEC_LLVMF_STK (d_sp0 cx) [] (ablocks B (d_ly cx) (d_S cx)) (ablocks B ly S) ly
         [(DEC_FCLASS, d_fpos cx)] 9%nat (d_sp1 cx - d_sp0 cx)).
- reflexivity.
- rewrite (cm_E9 regs out res len ns64 nch32 ns32 x44 x45 R9 H64). lia.
- cbn [cm_spill YP09.r_wlo]. rewrite HS. lia.
- cbn [cm_spill YP09.r_whi]. lia.
- apply awr_ok_nil.
Qed.

(* +0x718, the head of the scan loop L2 at turn i (the refused-decode path): the read-only spill slots, the byte
   out + i of the buffer (atom 44, the alias of out + a3) holding the 0xa5 fill, and its shadow entry, which the
   buffer's block gives (a Theorem Labs lane's GrantEntrySweepS2.v:305 / :342, a row of the sweep at its turn). *)
Lemma cm_stokL2 : forall (W : world SEGS) ly S regs mem md k out res mode nch ns m i,
  dec_b_core B cx ly S W regs mem md k ->
  cm_mem cx out res mode nch ns W mem ->
  In (out, m) (ablocks B ly S) -> dec_b_filled W mem out m -> 0 <= i < m ->
  YK11.getr regs 17 = w64 SHADOW_OFF -> YK11.getr regs 13 = w64 i ->
  st_ok_pi SEGS VAL
    (cm_env regs out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) (out + i) 0)
    cm_ssL2
    (restrict (w_H W) (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x718)) mem (YK11.seg_rom SEGS))) /\
  sh_ok SEGS cm_BxL2 cm_SHL2
    (cm_env regs out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) (out + i) 0)
    (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md k out res mode nch ns m i HC HM Hin HFILL Hi R17 R13.
destruct (cm_sp1 ly S W regs mem md k HC) as (Hsp1lo & Hsp1hi & Hsp1al & Hsp1pres).
pose proof (@alloc_ceiling_val rc) as [ACR _].
assert (Hsp64 : 0 <= d_sp1 cx < 2 ^ 64).
{ revert Hsp1lo Hsp1hi. generalize (d_sp1 cx). intros z H1 H2. lia. }
pose proof HC as (HJ & _ & _ & R9 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ out m HAR Hin) as (_ & Ho4096 & Hoceil & Hoapp & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
destruct HM as (HFRS & HFSH & HMODE & HBODY & H24 & H32 & H40 & H56 & H64 & H72 & H80 & H88 & H112).
set (E := cm_env regs out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) (out + i) 0).
assert (E9 : bv_unsigned (ew E 9) = d_sp1 cx) by (subst E; apply cm_E9; [exact R9 | exact Hsp64]).
assert (E13 : ew E 13 = w64 i) by (subst E; rewrite (cm_env_reg regs _ _ _ _ _ _ _ _ 13%nat (13%bv : bv 5) eq_refl); exact R13).
assert (E17 : ew E 17 = w64 SHADOW_OFF)
  by (subst E; rewrite (cm_env_reg regs _ _ _ _ _ _ _ _ 17%nat (17%bv : bv 5) eq_refl); exact R17).
assert (E33 : ew E 33 = w64 out) by (subst E; apply cm_env_33).
assert (E44 : ew E 44 = w64 (out + i)) by (subst E; apply cm_env_44).
assert (U44 : bv_unsigned (ew E 44) = out + i) by (rewrite E44; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. split.
- unfold cm_ssL2.
  apply (@pa_entry_st_ok_full fx rc decodeb_listing PID E 0x718 sr_atoms regs [cm_spillL2; cm_byte44] cm_factsL2
           (mrestrict (w_H W) mem)).
  + subst E. unfold cm_env. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold cm_spillL2, cm_spill_chunks, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- cm_chunk H24 cm_env_35.
      -- cm_chunk H32 cm_env_32.
      -- cm_chunk H40 cm_env_34.
      -- cm_chunk H56 cm_env_38.
      -- cm_chunk H64 cm_env_37.
      -- cm_chunk H72 cm_env_36.
      -- cm_chunk H80 cm_env_39.
      -- cm_chunk H88 cm_env_33.
    * unfold cm_byte44, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U44.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (out + i) 0 1%N (SLit 165) 165); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply cm_val_mem1. exact (HFILL i Hi).
  + apply pairwise_disjoint_of_extents.
    unfold cm_spillL2, cm_byte44, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, U44.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + split; [|split; [exact I|]].
    * cbn [cm_factsL2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      unfold CM_SP_LO, CM_BLK_HI.
      split; [| split; [| split; [| split; [|exact I]]]].
      -- rewrite E17. unfold w64, SHADOW_OFF.
         rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
      -- rewrite E9. change (2 ^ 5) with 32. rewrite Hsp1al. lia.
      -- rewrite E33. unfold w64.
         rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
      -- rewrite U44. rewrite Z.pow_0_r, Z.mod_1_r. lia.
    * cbn [cm_factsL2 f_alias alias_ok]. split; [|exact I]. apply U_inj.
      rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 33 out) by first [exact E33 | lia].
      rewrite (U_atom E 13 i) by first [exact E13 | lia].
      rewrite (U_atom E 44 (out + i)) by first [exact E44 | lia].
      apply zcanon_id. unfold M64. lia.
- unfold sh_ok, cm_SHL2. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) mem E cm_BxL2 44 out m (out + i) 0 1).
  + exact (range_addressable_of_block SEGS B LAWS ly S W mem md out m out m HAR Hin ltac:(lia) ltac:(lia)).
  + unfold cm_BxL2. apply U_atom; [exact E17 | unfold SHADOW_OFF; lia].
  + apply U_atom; [exact E44 | lia].
  + lia.
  + lia.
  + intros x Hx. revert Hoapp Hx Hrq. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.

(* The bcmp loops' cuts: the read-only spill slots and 48(s1) = 3 * ns (atom 45). *)
Lemma cm_stokL : forall (W : world SEGS) ly S regs mem md k out res mode nch ns pc,
  dec_b_core B cx ly S W regs mem md k ->
  cm_mem cx out res mode nch ns W mem ->
  dec_b_slot cx (aview SEGS (w_H W) mem) 48 (3 * ns) -> 0 < ns <= 127 ->
  4096 <= out <= alloc_ceiling -> 4096 <= res <= alloc_ceiling ->
  st_ok_pi SEGS VAL
    (cm_env regs out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) 0 (3 * ns))
    (cm_ssL pc)
    (restrict (w_H W) (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + pc)) mem (YK11.seg_rom SEGS))).
Proof.
intros W ly S regs mem md k out res mode nch ns pc HC HM H48 Hns Hout Hres.
destruct (cm_sp1 ly S W regs mem md k HC) as (Hsp1lo & Hsp1hi & Hsp1al & Hsp1pres).
pose proof (@alloc_ceiling_val rc) as [ACR _].
assert (Hsp64 : 0 <= d_sp1 cx < 2 ^ 64).
{ revert Hsp1lo Hsp1hi. generalize (d_sp1 cx). intros z H1 H2. lia. }
pose proof HC as (_ & _ & _ & R9 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
destruct HM as (HFRS & HFSH & HMODE & HBODY & H24 & H32 & H40 & H56 & H64 & H72 & H80 & H88 & H112).
set (E := cm_env regs out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) 0 (3 * ns)).
assert (E9 : bv_unsigned (ew E 9) = d_sp1 cx) by (subst E; apply cm_E9; [exact R9 | exact Hsp64]).
assert (E32 : ew E 32 = w64 SHADOW_OFF) by (subst E; apply cm_env_32).
assert (E33 : ew E 33 = w64 out) by (subst E; apply cm_env_33).
assert (E34 : ew E 34 = w64 res) by (subst E; apply cm_env_34).
rewrite restrict_mkst_fx. unfold cm_ssL.
apply (@pa_entry_st_ok_full fx rc decodeb_listing PID E pc sr_atoms regs [cm_spillL] cm_facts0
         (mrestrict (w_H W) mem)).
- subst E. unfold cm_env. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold cm_spillL, cm_spill_chunks, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + cm_chunk H48 cm_env_45.
  + cm_chunk H24 cm_env_35.
  + cm_chunk H32 cm_env_32.
  + cm_chunk H40 cm_env_34.
  + cm_chunk H56 cm_env_38.
  + cm_chunk H64 cm_env_37.
  + cm_chunk H72 cm_env_36.
  + cm_chunk H80 cm_env_39.
  + cm_chunk H88 cm_env_33.
- cbn. split; exact I.
- split; [|split; [exact I | exact I]].
  cbn [cm_facts0 cm_atoms0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  unfold CM_SP_LO, CM_BLK_HI.
  split; [| split; [| split; [| split; [|exact I]]]].
  + rewrite E32. unfold w64, SHADOW_OFF.
    rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
  + rewrite E9. change (2 ^ 5) with 32. rewrite Hsp1al. lia.
  + rewrite E33. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
  + rewrite E34. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

(* A region of a state the walk stopped in (lib/A/Prog/YC1g.v:67 st_ok_pi_region_nth, at image B's listing). *)
Lemma cm_region_nth : forall E ss ms i r,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth E (abs_ss VAL ss) ms i r HS ltac:(destruct ss; exact Hi)). Qed.

(* +0x6f0 read-only: the spill slots 24 .. 88 but 48, for the head's runs that store nothing (to +0x718 and to +0x7bc). *)
Definition cm_ssR (pc : Z) : sstate := mkSS pc sr_atoms [cm_spillL2] None cm_facts0.
Lemma cm_stokR : forall (W : world SEGS) ly S regs mem md k out res mode nch ns pc,
  dec_b_core B cx ly S W regs mem md k ->
  cm_mem cx out res mode nch ns W mem ->
  4096 <= out <= alloc_ceiling -> 4096 <= res <= alloc_ceiling ->
  st_ok_pi SEGS VAL
    (cm_env regs out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) 0 0)
    (cm_ssR pc)
    (restrict (w_H W) (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + pc)) mem (YK11.seg_rom SEGS))).
Proof.
intros W ly S regs mem md k out res mode nch ns pc HC HM Hout Hres.
destruct (cm_sp1 ly S W regs mem md k HC) as (Hsp1lo & Hsp1hi & Hsp1al & Hsp1pres).
pose proof (@alloc_ceiling_val rc) as [ACR _].
assert (Hsp64 : 0 <= d_sp1 cx < 2 ^ 64).
{ revert Hsp1lo Hsp1hi. generalize (d_sp1 cx). intros z H1 H2. lia. }
pose proof HC as (_ & _ & _ & R9 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
destruct HM as (HFRS & HFSH & HMODE & HBODY & H24 & H32 & H40 & H56 & H64 & H72 & H80 & H88 & H112).
set (E := cm_env regs out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) 0 0).
assert (E9 : bv_unsigned (ew E 9) = d_sp1 cx) by (subst E; apply cm_E9; [exact R9 | exact Hsp64]).
assert (E32 : ew E 32 = w64 SHADOW_OFF) by (subst E; apply cm_env_32).
assert (E33 : ew E 33 = w64 out) by (subst E; apply cm_env_33).
assert (E34 : ew E 34 = w64 res) by (subst E; apply cm_env_34).
rewrite restrict_mkst_fx. unfold cm_ssR.
apply (@pa_entry_st_ok_full fx rc decodeb_listing PID E pc sr_atoms regs [cm_spillL2] cm_facts0
         (mrestrict (w_H W) mem)).
- subst E. unfold cm_env. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold cm_spillL2, cm_spill_chunks, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + cm_chunk H24 cm_env_35.
  + cm_chunk H32 cm_env_32.
  + cm_chunk H40 cm_env_34.
  + cm_chunk H56 cm_env_38.
  + cm_chunk H64 cm_env_37.
  + cm_chunk H72 cm_env_36.
  + cm_chunk H80 cm_env_39.
  + cm_chunk H88 cm_env_33.
- cbn. split; exact I.
- split; [|split; [exact I | exact I]].
  cbn [cm_facts0 cm_atoms0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  unfold CM_SP_LO, CM_BLK_HI.
  split; [| split; [| split; [| split; [|exact I]]]].
  + rewrite E32. unfold w64, SHADOW_OFF.
    rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
  + rewrite E9. change (2 ^ 5) with 32. rewrite Hsp1al. lia.
  + rewrite E33. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
  + rewrite E34. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

End Walk.
End Cmp.
