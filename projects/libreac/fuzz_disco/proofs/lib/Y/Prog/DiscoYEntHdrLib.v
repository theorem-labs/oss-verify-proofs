(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 733 of its 792 lines of code are new or changed and 1219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntR27.v; 134 of its 180 lines of code are new or changed and 746 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition hd_sr : list sv :=
  [SLit 0; SOff 535 0; SOff AT_A 0; SOff 3 0; SOff 4 0; SOff 536 0; SOff 537 0; SOff 538 0;
   SOff AT_STK 0; SOff AT_A 0; SOff 539 0; SOff 540 0; SOff 541 0; SOff 542 0; SOff 531 0; SOff 543 0;
   SOff 544 0; SOff 545 0; SLit WS_MASK; SOff 32 0; SLit 32; SOff 532 0; SLit 1; SOff 546 0;
   SOff 533 0; SOff 547 0; SOff 534 0; SOff AT_SH 0; SOff 548 0; SOff 549 0; SOff 550 0; SOff 551 0].
Definition hd_acs : list YP09.chunk :=
  map (fun kv => YP09.mkChunk (fst kv) (CVal 8 (snd kv)))
  [(184, SOff 552 0); (120, SOff 552 440); (136, SLit 0); (376, SOff 553 0); (280, SOff 554 0);
   (232, SOff 555 0); (264, SOff 556 0)].
Definition hd_cell (q v : nat) : YP09.region := YP09.mkRegion (Some q) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff v 0))].
Definition hd_byte (j : Z) (v : nat) : YP09.region :=
  YP09.mkRegion (Some 533%nat) j (j + 1) 0 0 [YP09.mkChunk j (CVal 1 (SOff v 0))].
Definition hd_join (r : bv 5) (a : nat) (ss : sstate) : sstate :=
  mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff a 0)) (tl (ss_mem ss)) (ss_resv ss)
    (mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss))).
Definition hd_retgt (r : bv 5) (q v : nat) (ss : sstate) : sstate :=
  mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff q 0)) (hd_cell q v :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition hd_addb (j : Z) (v : nat) (ss : sstate) : sstate :=
  mkSS (ss_pc ss) (ss_regs ss) (hd_byte j v :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition hd_rw (rs : smem) : smem :=
  map (fun r => match YP09.r_base r with
                | Some b => if (Nat.eqb b AT_F || Nat.eqb b AT_SH)%bool then set_window r 0 0 else r
                | None => r end) rs.
Definition hd_run (ss : sstate) : sstate := fst (sym_runN_pi both3_0_tpi FUEL ss).
Definition hd_ss0 : sstate := Eval vm_compute in
  let ss := ss_d HDR_OFF hd_sr dsh_loop hd_acs [] [] (d_facts [] []) in
  mkSS (ss_pc ss) (ss_regs ss) (hd_rw (ss_mem ss)) (ss_resv ss) (ss_facts ss).
Definition hd_ssJ1 : sstate := Eval vm_compute in
  hd_join 11 566 (hd_run (add_cond (hd_run (hd_retgt 10 557 558 (hd_run (add_cond
    (hd_run (add_cond hd_ss0 (mkAC BC_NE (SOff 531 0) (SLit 0)))) (mkAC BC_LTU (SLit 1) (SOff 533 1))))))
    (mkAC BC_EQ (SExt true 8 (SOff 558 0)) (SLit 0)))).
Definition hd_ssJ2 : sstate := Eval vm_compute in
  hd_join 11 567 (hd_run (add_cond (hd_run (hd_retgt 10 559 560 (hd_run (add_cond
    (hd_run (add_cond (hd_run (hd_addb 0 563 hd_ssJ1)) (mkAC BC_NE (SOff 531 0) (SLit 1))))
    (mkAC BC_LTU (SLit 1) (SOff 533 2))))))
    (mkAC BC_EQ (SExt true 8 (SOff 560 0)) (SLit 0)))).
Definition hd_ssJ3 : sstate := Eval vm_compute in
  hd_join 13 568 (hd_run (add_cond (hd_run (hd_retgt 12 561 562 (hd_run (add_cond
    (hd_run (add_cond (hd_run (hd_addb 1 564 hd_ssJ2)) (mkAC BC_NE (SOff 531 0) (SLit 2))))
    (mkAC BC_LTU (SLit 1) (SOff 533 3))))))
    (mkAC BC_EQ (SExt true 8 (SOff 562 0)) (SLit 0)))).

Definition hd_wrb (rs : smem) : bool :=
  forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
    (obase_eqb (YP09.r_base r) (Some AT_A) && (0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 472))) rs.
Definition hd_fregs : list (bv 5 * sv) :=
  [(2%bv, SOff 60 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (8%bv, SOff 2 0); (9%bv, SOff 60 0);
   (18%bv, SLit WS_MASK); (19%bv, SOff 32 0); (20%bv, SLit 32); (22%bv, SLit 1); (27%bv, SOff 529 0);
   (21%bv, SOff 532 0); (16%bv, SExt true 8 (SOff 563 0)); (23%bv, SAlu ALU_AND (SExt true 8 (SOff 563 0)) (SLit 3));
   (15%bv, SLit (STALE_NS + 1))].
Definition hd_need (ss : sstate) : list (Z * sv) :=
  [(184, SOff 552 0); (120, SOff 552 440); (136, SLit 0); (376, SOff 553 0); (280, SOff 554 0);
   (232, SOff 555 0); (264, SOff 556 0); (208, SOff 532 0); (320, sr_get (ss_regs ss) 26);
   (352, SExt true 8 (SOff 563 0)); (360, SAlu ALU_AND (SExt true 8 (SOff 563 0)) (SLit 255))].
Definition hd_has (cs : list YP09.chunk) (o : Z) (e : sv) : bool :=
  existsb (fun c => (YP09.c_off c =? o) &&
    match YP09.c_val c with CVal w e' => N.eqb w 8 && sv_eqb e' e | _ => false end) cs.
Definition hd_slotb (ss : sstate) : bool :=
  existsb (fun r => obase_eqb (YP09.r_base r) (Some AT_A) &&
    forallb (fun oe => hd_has (YP09.r_chunks r) (fst oe) (snd oe)) (hd_need ss)) (ss_mem ss).
Definition hd_leafb (ss : sstate) : bool :=
  d_land_chk dsh_loop (ss_mem ss) && hd_slotb ss &&
  forallb (fun re => sv_eqb (sr_get (ss_regs ss) (fst re)) (snd re)) hd_fregs.

Definition yh_cell (p n x : Z) : Z := if (x - p) / 8 <? n / 8 then 0 else n mod 8.
Definition yh_caddr (x : Z) : Z := SHADOW_OFF + x / 8.

Lemma yh_div8_shift : forall p d, p mod 8 = 0 -> (p + d) / 8 = p / 8 + d / 8.
Proof.
intros p d Hp. pose proof (Z.div_mod p 8 ltac:(lia)) as D.
replace (p + d) with (8 * (p / 8) + d) by lia. rewrite Z.mul_comm, Z.div_add_l by lia. lia.
Qed.

Lemma yh_cell_range : forall p n x, 0 <= yh_cell p n x < 8.
Proof.
intros p n x. unfold yh_cell. destruct ((x - p) / 8 <? n / 8); [lia|].
pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia.
Qed.

Lemma yh_cell_lt : forall p n x,
  p mod 8 = 0 -> 0 <= n -> p <= x < p + n -> yh_cell p n x <> 0 -> x mod 8 < yh_cell p n x.
Proof.
intros p n x Hp Hn Hx Hne. unfold yh_cell in *.
destruct ((x - p) / 8 <? n / 8) eqn:Hlt; [lia|]. apply Z.ltb_ge in Hlt.
assert (Hdiv : (x - p) / 8 = n / 8).
{ pose proof (Z.div_le_mono (x - p) n 8 ltac:(lia) ltac:(lia)). lia. }
pose proof (Z.div_mod (x - p) 8 ltac:(lia)) as D1.
pose proof (Z.div_mod n 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (x - p) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
assert (Hm : (x - p) mod 8 < n mod 8) by lia.
replace (x mod 8) with ((x - p) mod 8); [exact Hm|].
rewrite <- (Z.add_0_r (x - p)) at 1. rewrite <- Hp.
rewrite Zplus_mod_idemp_r. f_equal. lia.
Qed.

Lemma yh_caddr_range : forall x, 0 <= x < 2 ^ 47 -> SHADOW_OFF <= yh_caddr x < SHADOW_OFF + 2 ^ 44.
Proof.
intros x Hx. unfold yh_caddr. split; [pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); lia|].
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma yh_caddr_ne : forall x F, 0 <= x -> 0 <= F -> F mod 8 = 0 -> (x < F \/ F + 4096 <= x) ->
  yh_caddr x + 1 <= SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 512 <= yh_caddr x.
Proof.
intros x F Hx HF HF8 Hd. unfold yh_caddr.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
destruct Hd as [Hd | Hd].
- left. assert (x / 8 < F / 8) by (apply Z.div_lt_upper_bound; lia). lia.
- right. assert (F / 8 + 512 <= x / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma yh_bv_range : forall (pl : list byte) j, 0 <= nth j (map (fun b : byte => bv_unsigned b) pl) 0 < 256.
Proof.
induction pl as [|b pl IH]; intros j; destruct j as [|j]; cbn [map nth]; try lia.
- pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb. exact Hb.
- apply IH.
Qed.

Lemma yh_val_mem_mod : forall segs (m : word -> option byte) a v v',
  v mod 2 ^ 64 = v' mod 2 ^ 64 -> val_mem segs m a 8 v -> val_mem segs m a 8 v'.
Proof.
intros segs m a v v' Hv H k Hk. rewrite (H k Hk).
repeat match goal with |- context [?f v 8%nat k] => let t := eval unfold f in (f v 8%nat k) in change (f v 8%nat k) with t end.
repeat match goal with |- context [?f v' 8%nat k] => let t := eval unfold f in (f v' 8%nat k) in change (f v' 8%nat k) with t end.
assert (E8 : 2 ^ (8 * Z.of_nat 8) = 2 ^ 64) by reflexivity. rewrite E8, Hv. reflexivity.
Qed.

Lemma yh_swrap8 : forall op, 0 <= op < 256 -> bv_swrap 8 op = if op <? 128 then op else op - 256.
Proof.
intros op Hop. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
assert (E1 : 2 ^ Z.of_N 8 = 256) by reflexivity. rewrite E1. change (256 / 2) with 128.
destruct (Z.ltb_spec op 128); lia.
Qed.

Lemma yh_sext8 : forall E (q : nat) op, ew E q = Z_to_bv 64 op -> 0 <= op < 256 ->
  sv_denot E (SExt true 8 (SOff q 0)) = Z_to_bv 64 (if op <? 128 then op else op - 256).
Proof.
intros E q op Hq Hop. rewrite denot_lit_U, U_SExt, (U_atom E q op Hq) by lia.
assert (E1 : 2 ^ Z.of_N 8 = 256) by reflexivity. rewrite E1, (Z.mod_small op 256) by lia.
rewrite (yh_swrap8 op Hop). apply Z_to_bv64_eq_mod. unfold zcanon, M64. apply Z.mod_mod. lia.
Qed.

Lemma yh_and3 : forall E (q : nat) op, ew E q = Z_to_bv 64 op -> 0 <= op < 256 ->
  U E (SAlu ALU_AND (SExt true 8 (SOff q 0)) (SLit 3)) = op mod 4.
Proof.
intros E q op Hq Hop. rewrite U_and_lit by lia.
assert (HU : U E (SExt true 8 (SOff q 0)) = (if op <? 128 then op else op - 256) mod 2 ^ 64).
{ unfold U. rewrite (yh_sext8 E q op Hq Hop). rewrite Z_to_bv_unsigned. reflexivity. }
rewrite HU. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
destruct (op <? 128); [rewrite (Z.mod_small op) by lia; reflexivity|].
rewrite Z.mod_mod_divide by (exists (2 ^ 62); reflexivity).
replace (op - 256) with (op + (-64) * 4) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma yh_and255 : forall E (q : nat) op, ew E q = Z_to_bv 64 op -> 0 <= op < 256 ->
  U E (SAlu ALU_AND (SExt true 8 (SOff q 0)) (SLit 255)) = op.
Proof.
intros E q op Hq Hop. rewrite U_and_lit by lia.
assert (HU : U E (SExt true 8 (SOff q 0)) = (if op <? 128 then op else op - 256) mod 2 ^ 64).
{ unfold U. rewrite (yh_sext8 E q op Hq Hop). rewrite Z_to_bv_unsigned. reflexivity. }
rewrite HU. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
rewrite Z.mod_mod_divide by (exists (2 ^ 56); reflexivity).
destruct (op <? 128); [apply Z.mod_small; lia|].
replace (op - 256) with (op + (-1) * 256) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
