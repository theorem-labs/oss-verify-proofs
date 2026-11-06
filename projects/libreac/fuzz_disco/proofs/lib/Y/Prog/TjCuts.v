(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 165 of its 199 lines of code are new or changed and 511 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YP0c YP07 YI0w YI0z YI12 YC4a YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Definition tj_KD : Z := 4835703278458516699.
Definition tj_s_open : list Z := [91].
Definition tj_s_close : list Z := [93].
Definition tj_s_comma : list Z := [44].
Definition tj_s_empty : list Z := (@nil Z).
Definition tj_f_mac : list Z := [37; 115; 123; 34; 109; 97; 99; 34; 58; 34; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 34].
Definition tj_f_role : list Z := [44; 34; 114; 111; 108; 101; 34; 58; 34; 37; 115; 34].
Definition tj_f_model : list Z := [44; 34; 109; 111; 100; 101; 108; 34; 58; 34; 37; 115; 34].
Definition tj_f_width : list Z := [44; 34; 119; 105; 100; 116; 104; 34; 58; 34; 37; 100; 120; 37; 100; 34].
Definition tj_f_model_unk : list Z := [44; 34; 109; 111; 100; 101; 108; 34; 58; 34; 117; 110; 107; 110; 111; 119; 110; 34].
Definition tj_f_width_0 : list Z := [44; 34; 119; 105; 100; 116; 104; 34; 58; 34; 48; 120; 48; 34].
Definition tj_f_owned : list Z := [44; 34; 111; 119; 110; 101; 100; 34; 58; 37; 115].
Definition tj_f_age : list Z := [44; 34; 97; 103; 101; 95; 109; 115; 34; 58; 37; 108; 108; 117; 125].
Definition ss_tjX : sstate :=
(mkSS 25204
[SLit 0; SOff 640 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 641 0; SOff 642 0; SOff 643 0; SOff 2 0; SOff 60 0; SOff 644 0; SOff 645 0; SOff 646 0; SOff 647 0; SOff 648 0; SOff 649 0; SOff 650 0; SOff 651 0; SOff 516 0; SOff 516 0; SOff 652 0; SOff 654 0; SOff 529 0; SOff 653 0; SOff 655 0; SOff 32 0; SOff 656 0; SOff 657 0; SOff 658 0; SOff 659 0; SOff 660 0; SOff 661 0]
[YP09.mkRegion (Some 529%nat) 0 32 0 32 [];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 184 0 184 [];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]]
None
(mkFacts
[(529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0)]
[]
[(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)])).
Definition ss_tjC : sstate :=
(mkSS 25076
[SLit 0; SOff 680 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 681 0; SOff 682 0; SOff 683 0; SOff 2 0; SOff 60 0; SOff 684 0; SOff 685 0; SOff 686 0; SOff 687 0; SOff 688 0; SOff 689 0; SOff 690 0; SOff 691 0; SOff 516 0; SOff 692 0; SOff 13 0; SOff 12 0; SOff 529 0; SOff 693 0; SOff 694 0; SOff 32 0; SOff 695 0; SOff 696 0; SOff 697 0; SOff 698 0; SOff 699 0; SOff 700 0]
[YP09.mkRegion (Some 529%nat) 0 32 0 32 [];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 184 0 184 [YP09.mkChunk 80 (CVal 8 (SOff 516 0))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]]
None
(mkFacts
[(529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0); (13%nat, mkAF 0 2147483647 0); (12%nat, mkAF 4096 140737479966720 4)]
[]
[(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)])).
Definition ss_tjL : sstate :=
(mkSS 23700
[SLit 0; SOff 720 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 723 0; SOff 724 0; SOff 725 0; SOff 2 0; SOff 60 0; SOff 726 0; SOff 727 0; SOff 728 0; SOff 10 384; SOff 722 0; SOff 729 0; SOff 730 0; SOff 731 0; SOff 516 0; SOff 721 0; SOff 13 0; SOff 12 0; SOff 529 0; SOff 732 0; SOff 734 0; SOff 32 0; SOff 733 0; SOff 735 0; SOff 736 0; SOff 737 0; SOff 738 0; SOff 739 0]
[YP09.mkRegion (Some 529%nat) 0 32 0 32 [];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 184 0 184 [YP09.mkChunk 40 (CVal 8 (SOff 281 0)); YP09.mkChunk 48 (CVal 8 (SLit 4835703278458516699)); YP09.mkChunk 56 (CVal 8 (SOff 516 160)); YP09.mkChunk 64 (CVal 8 (SOff 516 32)); YP09.mkChunk 72 (CVal 8 (SOff 10 384)); YP09.mkChunk 80 (CVal 8 (SOff 516 0)); YP09.mkChunk 88 (CVal 8 (SOff 516 96)); YP09.mkChunk 96 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 384) (SLit 3)) (SOff 32 0))); YP09.mkChunk 104 (CVal 8 (SOff 282 0)); YP09.mkChunk 112 (CVal 8 (SOff 10 0)); YP09.mkChunk 120 (CVal 8 (SOff 11 0)); YP09.mkChunk 128 (CVal 8 (SAlu ALU_XOR (SOff 10 0) (SLit 18446744073709551615))); YP09.mkChunk 152 (CVal 8 (SLit 1))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]]
None
(mkFacts
[(529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0); (13%nat, mkAF 0 2147483647 0); (12%nat, mkAF 4096 140737479966720 4); (10%nat, mkAF 4096 140737479966720 3)]
[]
[(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)])).
Definition tj_rom_bytes (a : Z) (bs : list Z) : Prop :=
forall i, (i < length bs)%nat ->
option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 (a + Z.of_nat i))) = Some (nth i bs 0).
Definition tj_ro_at (k : nat) (s : list Z) : Prop :=
In (VAL (A_OBJ k), Z.of_nat (length s) + 1) tfib_globs /\
(forall x, VAL (A_OBJ k) <= x < VAL (A_OBJ k) + Z.of_nat (length s) + 1 -> in_roP SEGS pa_relro_lo pa_relro_hi x) /\
IMG_LO + 64 <= VAL (A_OBJ k) /\ VAL (A_OBJ k) + Z.of_nat (length s) + 1 + 64 <= IMG_TOP /\
Forall (fun c => 0 < c < 256) s /\ tj_rom_bytes (VAL (A_OBJ k)) (s ++ [0]).
Lemma tj_ro_fmt_rng : forall k s, tj_ro_at k s -> Z.of_nat (length s) <> 23 ->
disco_fmt_lo <= VAL (A_OBJ k) /\ VAL (A_OBJ k) + Z.of_nat (length s) + 1 <= disco_fmt_hi.
Proof.
intros k s (Hg & _) Hs.
assert (E : forallb (fun r => (snd r =? 24) || ((disco_fmt_lo <=? fst r) && (fst r + snd r <=? disco_fmt_hi))) tfib_globs = true)
by reflexivity.
pose proof (proj1 (forallb_forall _ _) E _ Hg) as H. cbn [fst snd] in H.
apply orb_prop in H. destruct H as [H | H]; [apply Z.eqb_eq in H; lia|].
apply andb_prop in H. destruct H as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma tj_ro_amem8 : forall k s, tj_ro_at k s -> amem_range (VAL (A_OBJ k)) (Z.of_nat (length s) + 8).
Proof.
intros k s (_ & _ & Hlo & Hhi & _). unfold amem_range, IMG_LO, IMG_TOP, kLowMemEnd in *. left. lia.
Qed.
Definition tj_ro_kd : Prop :=
In (VAL (A_OBJ 17), 8) tfib_ro_extra /\
(forall x, VAL (A_OBJ 17) <= x < VAL (A_OBJ 17) + 8 -> in_roP SEGS pa_relro_lo pa_relro_hi x) /\
tj_rom_bytes (VAL (A_OBJ 17)) [219; 52; 182; 215; 130; 222; 27; 67].
Definition tj_strs : Prop :=
tj_ro_at 39 tj_s_open /\ tj_ro_at 55 tj_s_close /\ tj_ro_at 42 tj_f_mac /\ tj_ro_at 46 tj_f_role /\
tj_ro_at 49 tj_f_model /\ tj_ro_at 50 tj_f_width /\ tj_ro_at 47 tj_f_model_unk /\ tj_ro_at 48 tj_f_width_0 /\
tj_ro_at 53 tj_f_owned /\ tj_ro_at 54 tj_f_age /\ tj_ro_at 40 tj_s_comma /\ tj_ro_at 41 tj_s_empty /\
tj_ro_at 45 s_box /\ tj_ro_at 44 s_master /\ tj_ro_at 43 s_unknown /\ tj_ro_at 51 s_true /\ tj_ro_at 52 s_false /\
tj_ro_kd.
Definition tj_tail_end (q n : Z) : Z := q + n - 1 - (q + n - 1) mod 8 + 8.
Definition tj_tails_b : bool :=
forallb (fun r => (tj_tail_end (fst r) (snd r) <=? fst r + snd r) ||
existsb (fun t => (fst t =? fst r + snd r) && (tj_tail_end (fst r) (snd r) <=? fst t + snd t)) YXcalls.tfib_glob_tails)
tfib_globs.
Lemma tj_tails_b_true : tj_tails_b = true.
Proof. vm_compute. reflexivity. Qed.
Context {PRP : YXcalls.PARoPresent lib_both3_0_listing}.
Lemma tj_pad_ro : forall k s, tj_ro_at k s -> forall x, VAL (A_OBJ k) + Z.of_nat (length s) < x < SnShared.str_end (VAL (A_OBJ k)) s ->
seg_rom SEGS (Z_to_bv 64 x) <> None.
Proof.
intros k s (Hg & _) x Hx.
pose proof (proj1 (forallb_forall _ _) tj_tails_b_true _ Hg) as H. cbn [fst snd] in H.
unfold SnShared.str_end in Hx. unfold tj_tail_end in H.
apply orb_prop in H. destruct H as [H | H].
- apply Z.leb_le in H. lia.
- apply existsb_exists in H. destruct H as ((tq & tsz) & Ht & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb. destruct Hb as (H1 & H2). apply Z.eqb_eq in H1. apply Z.leb_le in H2.
apply (YXcalls.pa_ro_present tq tsz x Ht). lia.
Qed.
Section h.
Variable B : asyms.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Definition tj_keep (cx : tjcx) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem3) /\
garr8 SEGS (mrestrict (w_H W3) mem3) (c_t cx) (map bv_unsigned (c_T cx)) /\
afobj SEGS B (c_ly cx) (c_S cx) W3 mem3 (c_t cx) 400.
Definition INV_tjX : tjcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= 0 /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
exists r : Z, ew E 653 = w64 r /\
(c_cap cx < 3 -> r = -1) /\
(3 <= c_cap cx -> tj_len (c_T cx) (c_now cx) < c_cap cx ->
r = tj_len (c_T cx) (c_now cx) /\
garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_buf cx)
(reac_disco_table_json_c.tj_text (c_T cx) (c_now cx) ++ [0])) /\
(3 <= c_cap cx -> c_cap cx <= tj_len (c_T cx) (c_now cx) -> r = -1).
Definition INV_tjC : tjcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= 0 /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
tj_keep cx W3 (ms_mem ms3) /\ 3 <= c_cap cx /\
exists acc : list Z,
ew E 695 = w64 (Z.of_nat (length acc)) /\ 0 < Z.of_nat (length acc) < c_cap cx /\
reac_disco_table_json_c.tj_text (c_T cx) (c_now cx) = acc ++ [93] /\
garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_buf cx) (acc ++ [0]).
Definition INV_tjL (i : Z) : tjcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= 0 /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
tj_keep cx W3 (ms_mem ms3) /\ 3 <= c_cap cx /\
0 <= i < disco_table_c.n_of (c_T cx) /\
ew E 721 = w64 (48 * i) /\ ew E 722 = w64 i /\
exists acc : list Z,
ew E 733 = w64 (Z.of_nat (length acc)) /\ 0 < Z.of_nat (length acc) < c_cap cx /\
reac_disco_table_json_c.tj_text (c_T cx) (c_now cx) =
acc ++ tj_lemmas.tj_rest (c_T cx) (c_now cx) i /\
garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_buf cx) (acc ++ [0]).
Definition tj_fromX : Prop := tj_from0 B IMG ss_tjX INV_tjX.
Definition tj_fromC : Prop := tj_from0 B IMG ss_tjC INV_tjC.
Definition tj_fromL (i : Z) : Prop := tj_from0 B IMG ss_tjL (INV_tjL i).
End h.
End f.
End d.
