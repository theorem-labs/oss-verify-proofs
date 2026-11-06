(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated from the walk of the same function of libreac's fuzz_grant (the two are the same code at other addresses); the entry lemma is restated on fuzz_disco's premises for f and o, which name no frame. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin, for fuzz_disco.asan-ubsan (lib_both3_0_listing, entry 0x874a4): relocated from fuzz_grant image B's walk of the same code (a working branch edc3e948664, lib/B/Prog/CtrlParseLib.v; the two are the same 673 instructions at other addresses) on the fuzz_disco premises of lib/A/Prog/CtrlParseLib.v (26523666011); the cut pcs and cut B's s6 are image B's (the UBSan build adds 16 to s6 before the bcmp wrapper); the image objects are fuzz_disco.asan-ubsan's (GOT word of the shadow-base cell object 0, atom 241; GOT word of the side-stack flag object 1, atom 242; shadow-base cell object 12, atom 253) and the side-stack flag cell as_uar_cell B is the entry atom 34, as the classify_core walk of this image takes it. *)
(* The symbolic state of reac_ctrl_parse (0x874a4) of fuzz_disco's asan-ubsan build at its entry, and the facts
   its walk (CtrlParseWalk.v) needs about the caller's memory it keeps. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YM05 YI16 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC81 YC4b YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
Ltac pz_vside := lazymatch goal with
| |- 0 <= _ < 2 ^ (8 * Z.of_N ?w) => let k := eval vm_compute in (8 * Z.of_N w) in change (8 * Z.of_N w) with k; lia
| |- Z.of_N ?w <= 8 => let k := eval vm_compute in (Z.of_N w) in change (Z.of_N w) with k; lia
end.
(* ---- The cuts of the walk ---------------------------------------------------------------------
   Atoms: 2 the entry sp, 3/4 gp/tp, 1, 8, 9, 18..27 the entry registers, 10/11/12 the arguments f, n, o,
   32 the shadow base, 33 sp realigned to 32 bytes below the 128-byte frame, 34 the side-stack flag cell,
   40 + i the frame byte i, 516 the side-stack frame F, 528 its flag FL, 529 its shadow SHADOW_OFF + F / 8. *)
(* The cut pcs, as offsets from the function's entry (the same offsets as fuzz_grant image B's: the code is the same). *)
Definition AF_CUTA : Z := AF_both3_reac_ctrl_parse + 0x74.    (* after __asan_stack_malloc_1 returns (its call is at +0x70) *)
Definition AF_CUTB : Z := AF_both3_reac_ctrl_parse + 0x1fc.   (* after the bcmp wrapper returns (its call is at +0x1f8) *)
Definition AF_JOIN : Z := AF_both3_reac_ctrl_parse + 0x420.   (* every path's join before the epilogue *)
Definition pz_saved_chunks : list YP09.chunk :=
map (fun x => YP09.mkChunk (fst x) (CVal 8 (SOff (snd x) 0)))
[(-96, 26%nat); (-88, 25%nat); (-80, 24%nat); (-72, 23%nat); (-64, 22%nat); (-56, 21%nat); (-48, 20%nat); (-40, 19%nat);
 (-32, 18%nat); (-24, 9%nat); (-16, 8%nat); (-8, 1%nat)].
Definition pz_frame_chunks : list YP09.chunk :=
map (fun i => YP09.mkChunk (Z.of_nat i) (CVal 1 (SOff (40 + i) 0))) (seq 0 23 ++ seq 32 7).
Definition pz_out_cutB : list YP09.chunk :=
[YP09.mkChunk 0 (CZero 4)] ++ map (fun i => YP09.mkChunk (4 + Z.of_nat i) (CVal 1 (SOff (46 + i) 0))) (seq 0 6)
++ map (fun i => YP09.mkChunk (10 + Z.of_nat i) (CVal 1 (SOff (40 + i) 0))) (seq 0 6) ++ [YP09.mkChunk 16 (CZero 20)].
Definition pz_alias : list (sv * sv) := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)].
Definition pz_own_atoms : list (nat * afact) :=
[(516%nat, mkAF 4096 140737479966720 5); (528%nat, mkAF 4096 140737479966720 0); (529%nat, mkAF 2147451392 17594333495296 2)].
(* Cut M, at AF_both3_reac_ctrl_parse + 0x140 (after the memset of the out struct, called at +0x13c, returns): the out struct is zero, the frame and its
   shadow are read-only, the registers the walk overwrites are fresh atoms (ra_join from 560 over pz_deadM). *)
Definition AF_CUTM : Z := AF_both3_reac_ctrl_parse + 0x140.
Definition pz_deadM : list (bv 5) := [10; 1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition ss_cutM : sstate := Eval vm_compute in
mkSS AF_CUTM
[SLit 0; SOff 561 0; SOff 33 0; SOff 3 0; SOff 4 0; SOff 562 0; SOff 563 0; SOff 564 0;
 SOff 2 0; SOff 33 0; SOff 560 0; SOff 565 0; SOff 566 0; SOff 567 0; SOff 568 0; SOff 569 0;
 SOff 570 0; SOff 571 0; SOff 516 0; SOff 12 0; SOff 12 0; SOff 10 0; SOff 11 0; SOff 529 0;
 SOff 516 0; SOff 32 0; SOff 516 32; SOff 27 0; SOff 572 0; SOff 573 0; SOff 574 0; SOff 575 0]
[YP09.mkRegion (Some 12%nat) 0 36 0 36 [YP09.mkChunk 0 (CZero 36)];
 YP09.mkRegion (Some 529%nat) 0 16 0 0 [];
 YP09.mkRegion (Some 516%nat) 0 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 528 0))];
 YP09.mkRegion (Some 33%nat) 0 32 0 32 [];
 YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 pz_saved_chunks;
 YP09.mkRegion (Some 10%nat) 0 50 0 0 pz_frame_chunks]
None
(mkFacts (pz_own_atoms ++
  [(33%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4);
   (10%nat, mkAF 1 (2 ^ 47 - 50) 0); (11%nat, mkAF 0 18446744073709551615 0);
   (12%nat, mkAF 4096 (2 ^ 47 - 36) 3); (32%nat, mkAF 2147450880 2147450880 0)]
  ++ map (fun i => ((40 + i)%nat, mkAF 0 255 0)) (seq 0 23 ++ seq 32 7)) [] pz_alias).
(* Cut B, at AF_CUTB: the out struct holds the two copies; the bcmp result is atom 640; s6 is o + 16 (the
   asan-ubsan build adds 16 to s6 before the bcmp wrapper, at +0x1e4). The registers the rest of the walk
   reloads or overwrites are fresh atoms (ra_join from 640 over pz_deadB). The frame and its shadow are
   read-only here (the shadow-checked part of the walk needs every writable window apart from the shadow
   span); the epilogue makes them writable again. *)
Definition pz_deadB : list (bv 5) := [10; 1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition ss_cutB : sstate := Eval vm_compute in
mkSS AF_CUTB
[SLit 0; SOff 641 0; SOff 33 0; SOff 3 0; SOff 4 0; SOff 642 0; SOff 643 0; SOff 644 0;
 SOff 2 0; SOff 33 0; SOff 640 0; SOff 645 0; SOff 646 0; SOff 647 0; SOff 648 0; SOff 649 0;
 SOff 650 0; SOff 651 0; SOff 516 0; SOff 12 0; SOff 12 0; SOff 10 0; SOff 12 16; SOff 529 0;
 SOff 516 0; SOff 32 0; SOff 516 32; SOff 27 0; SOff 652 0; SOff 653 0; SOff 654 0; SOff 655 0]
[YP09.mkRegion (Some 12%nat) 0 36 0 36 pz_out_cutB;
 YP09.mkRegion (Some 529%nat) 0 16 0 0 [];
 YP09.mkRegion (Some 516%nat) 0 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 528 0))];
 YP09.mkRegion (Some 33%nat) 0 32 0 32 [];
 YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 pz_saved_chunks;
 YP09.mkRegion (Some 10%nat) 0 50 0 0 pz_frame_chunks]
None
(mkFacts (pz_own_atoms ++
  [(33%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4);
   (10%nat, mkAF 1 (2 ^ 47 - 50) 0); (11%nat, mkAF 0 18446744073709551615 0);
   (12%nat, mkAF 4096 (2 ^ 47 - 36) 3); (32%nat, mkAF 2147450880 2147450880 0)]
  ++ map (fun i => ((40 + i)%nat, mkAF 0 255 0)) (seq 0 23 ++ seq 32 7)) [] pz_alias).
(* Cut J, at AF_JOIN: a0 is atom 700 (the return code); everything else the epilogue does not read is a
   fresh atom (ra_join from 700 over pz_deadJ). *)
Definition pz_deadJ : list (bv 5) := [10; 1; 2; 5; 6; 7; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 25; 26; 28; 29; 30; 31]%bv.
Definition ss_cutJ : sstate := Eval vm_compute in
mkSS AF_JOIN
[SLit 0; SOff 701 0; SOff 702 0; SOff 3 0; SOff 4 0; SOff 703 0; SOff 704 0; SOff 705 0;
 SOff 2 0; SOff 706 0; SOff 700 0; SOff 707 0; SOff 708 0; SOff 709 0; SOff 710 0; SOff 711 0;
 SOff 712 0; SOff 713 0; SOff 516 0; SOff 714 0; SOff 715 0; SOff 716 0; SOff 717 0; SOff 529 0;
 SOff 516 0; SOff 718 0; SOff 719 0; SOff 27 0; SOff 720 0; SOff 721 0; SOff 722 0; SOff 723 0]
[YP09.mkRegion (Some 529%nat) 0 16 0 16 [];
 YP09.mkRegion (Some 516%nat) 0 128 0 128 [YP09.mkChunk 120 (CVal 8 (SOff 528 0))];
 YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 pz_saved_chunks]
None
(mkFacts (pz_own_atoms ++ [(2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0)]) [] pz_alias).
Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
(* ---- The symbolic state at the entry ---------------------------------------------------------
   Atoms: 0..31 the registers at entry, 32 the shadow base (SB), 33 the stack pointer realigned to 32 bytes
   below the 128-byte frame (pz_sp1), 34 the side-stack flag cell (as_uar_cell B), 40 + i the frame byte i
   (i < 39), 240 the code base, 241 + i the listing's objects. *)
Definition pz_sp1 (sp : Z) : Z := 32 * ((sp - 128) / 32).
Definition pz_extra (uc sp : Z) (fr : list byte) : list word :=
map (Z_to_bv 64) (SB :: pz_sp1 sp :: uc :: repeat 0 5 ++ map (cp_v fr) (seq 0 39)).
Definition pz_frame_region : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 50 0 0 (map (fun i => YP09.mkChunk (Z.of_nat i) (CVal 1 (SOff (40 + i) 0))) (seq 0 23 ++ seq 32 7)).
Definition pz_out_region (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 12%nat) 0 36 0 36 cs.
(* The entry state of the short walk (n < 50): the frame f is not read on that path and the contract says
   nothing about it, so neither its region nor its atom's fact is there. *)
Definition pz_regions0 : smem :=
[ stack_region 144; uar_got_regionP 34; uar_cell_regionP 34; got_regionP; bcell_regionP 32;
pz_out_region [] ].
Definition pz_regions : smem :=
[ stack_region 144; uar_got_regionP 34; uar_cell_regionP 34; got_regionP; bcell_regionP 32;
pz_frame_region; pz_out_region [] ].
(* The out struct may lie on the machine stack, above the allocation ceiling that PTR's upper bound is,
   and the contract gives the frame f no alignment; hence the two atoms' bounds here. *)
Definition pz_facts0 : facts :=
mkFacts ([(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 0 (2 ^ 64 - 1) 0); (12%nat, mkAF 4096 (2 ^ 47 - 36) 3); (32%nat, mkAF SB SB 0);
  (34%nat, mkAF YImgTop.IMG_LO YImgTop.IMG_TOP 2)]
++ map (fun i => ((40 + i)%nat, mkAF 0 255 0)) (seq 0 39)) [] [].
Definition pz_facts : facts :=
mkFacts ([(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 (2 ^ 47 - 50) 0); (11%nat, mkAF 0 (2 ^ 64 - 1) 0); (12%nat, mkAF 4096 (2 ^ 47 - 36) 3); (32%nat, mkAF SB SB 0);
  (34%nat, mkAF YImgTop.IMG_LO YImgTop.IMG_TOP 2)]
++ map (fun i => ((40 + i)%nat, mkAF 0 255 0)) (seq 0 39)) [] [].
Definition ss_pz0 : sstate := mkSS AF_both3_reac_ctrl_parse sr_atoms pz_regions0 None pz_facts0.
Definition ss_pz : sstate := mkSS AF_both3_reac_ctrl_parse sr_atoms pz_regions None pz_facts.
Definition PZx : sv := SOff 32 0.
Definition PZ_SH0 : list shent := [mkSHE 12 0 36].
Definition PZ_SH : list shent := [mkSHE 10 0 50; mkSHE 12 0 36].
Lemma pz_extra_nth : forall uc sp fr j, (j < 47)%nat ->
nth j (pz_extra uc sp fr) (Z_to_bv 64 0) = Z_to_bv 64 (nth j (SB :: pz_sp1 sp :: uc :: repeat 0 5 ++ map (cp_v fr) (seq 0 39)) 0).
Proof.
intros uc sp fr j Hj. unfold pz_extra. rewrite map_nth. reflexivity.
Qed.
Lemma cp_v_range : forall fr i, 0 <= cp_v fr i < 256.
Proof. intros fr i. unfold cp_v. pose proof (bv_unsigned_in_range 8 (cp_b fr i)) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.
Lemma atoms_ok_app_intro : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[n f] l1 IH]; cbn in *; [exact H2|]. destruct H1 as [Ha Hb]. split; [exact Ha | exact (IH Hb)]. Qed.
Lemma atoms_ok_fb : forall E fr, (forall i, (i < 39)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i)) ->
forall l, (forall i, In i l -> (i < 39)%nat) -> atoms_ok E (map (fun i => ((40 + i)%nat, mkAF 0 255 0)) l).
Proof.
intros E fr HE l. induction l as [|i l IH]; intros Hl; cbn [map atoms_ok]; [exact I|]. split.
- unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (HE i (Hl i (or_introl eq_refl))).
pose proof (cp_v_range fr i). rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
- apply IH. intros j Hj. apply Hl. right. exact Hj.
Qed.
(* The values of the entry valuation's atoms. *)
Lemma pz_env : forall uc (regs : bvmap 5 word) fr f n o,
getr regs 10 = w64 f -> getr regs 11 = w64 n -> getr regs 12 = w64 o ->
let E := Eimg (Ereg regs (pz_extra uc (spZ regs) fr)) in
(forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r) /\
ew E 10 = Z_to_bv 64 f /\ ew E 11 = Z_to_bv 64 n /\ ew E 12 = Z_to_bv 64 o /\
ew E 32 = Z_to_bv 64 SB /\ ew E 33 = Z_to_bv 64 (pz_sp1 (spZ regs)) /\ ew E 34 = Z_to_bv 64 uc /\
(forall i, (i < 39)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i)) /\
(forall j, (j < 68)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j))).
Proof.
intros uc regs fr f n o H10 H11 H12 E.
assert (EL : forall n0, (n0 < A_TEXT)%nat -> ew E n0 = ew (Ereg regs (pz_extra uc (spZ regs) fr)) n0)
by (intros n0 Hn0; subst E; apply Eimg_low; exact Hn0).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r)
by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
split; [exact EE|].
split; [rewrite (EE 10%nat 10%bv eq_refl); exact H10|].
split; [rewrite (EE 11%nat 11%bv eq_refl); exact H11|].
split; [rewrite (EE 12%nat 12%bv eq_refl); exact H12|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)|].
split.
- intros i Hi. rewrite EL by (unfold A_TEXT; lia). replace (40 + i)%nat with (32 + (8 + i))%nat by lia.
rewrite ew_Ereg_extra, pz_extra_nth by lia. f_equal. clear - Hi. do 39 (destruct i as [|i]; [reflexivity|]). lia.
- intros j Hj. subst E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia.
Qed.
(* A zero chunk from zero bytes. *)
Lemma pz_chunk_zero : forall E H m base off n,
(forall i, 0 <= i < n -> aview SEGS H m (base + off + i) = Some 0) ->
YP09.chunk_ok SEGS E (mrestrict H m) base (YP09.mkChunk off (CZero n)).
Proof.
intros E H m base off n Hz i Hi. cbn [YP09.c_len YP09.cv_len YP09.c_val YP09.c_off] in Hi |- *.
destruct (aview_byte SEGS H m (base + off + i) 0 (Hz i Hi)) as (b & Hb & Hv & _).
exists b. split; [|exact Hb]. cbn [YP09.cbyte]. f_equal. apply bv_eq. rewrite <- Hv. reflexivity.
Qed.
(* The byte a region's chunks give at offset off (the first chunk that covers it). *)
Fixpoint pz_chunk_at (E : env) (base : Z) (cs : list YP09.chunk) (off : Z) : option byte :=
match cs with
| [] => None
| c :: t => if (YP09.c_off c <=? off) && (off <? YP09.c_off c + YP09.c_len c)
  then YP09.cbyte SEGS E (base + YP09.c_off c) (YP09.c_val c) (off - YP09.c_off c)
  else pz_chunk_at E base t off
end.
Lemma pz_chunk_at_ok : forall E m base cs off v,
Forall (YP09.chunk_ok SEGS E m base) cs -> pz_chunk_at E base cs off = Some v ->
YP09.mbyte SEGS m (base + off) = Some v.
Proof.
intros E m base cs off v Hok. induction Hok as [|c t Hc Ht IH]; cbn [pz_chunk_at]; [discriminate|].
destruct ((YP09.c_off c <=? off) && (off <? YP09.c_off c + YP09.c_len c)) eqn:Hin; [|exact IH].
apply andb_prop in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
intros Hv. destruct (Hc (off - YP09.c_off c) ltac:(lia)) as (b & Hb & Hm).
rewrite Hv in Hb. injection Hb as <-. replace (base + off) with (base + YP09.c_off c + (off - YP09.c_off c)) by lia. exact Hm.
Qed.
(* A byte of a region of the walk's state, read back from its chunks. *)
Lemma pz_region_byte : forall E H mem r off v,
region_ok SEGS E (mrestrict H mem) r ->
pz_chunk_at E (base_val E (YP09.r_base r)) (YP09.r_chunks r) off = Some v ->
aview SEGS H mem (base_val E (YP09.r_base r) + off) = Some (bv_unsigned v).
Proof.
intros E H mem r off v (_ & _ & _ & Hcs) Hv. unfold aview.
rewrite (pz_chunk_at_ok E _ _ _ off v Hcs Hv). reflexivity.
Qed.
(* A shadow byte of an address below 2^47 is never an application byte. *)
Lemma pz_sh_app : forall x p n, 0 <= x < 2 ^ 47 -> in_app p n -> ~ (p <= shadow_addr x < p + n).
Proof.
intros x p n Hx [H0 [H|[H1 H2]]] Hs; unfold shadow_addr, SHADOW_OFF in Hs;
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia));
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); unfold kLowShadowBeg, kHighMemBeg in *; lia.
Qed.
Lemma pz_region_kept : forall E H (m m' : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m' a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m' a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m') (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m' n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* Where the caller's two objects lie: in one of its frames, in one of its blocks, or on the machine
   stack. fuzz_disco's contract names no frame for f and o (fuzz_grant's named one for each); this is the
   premise the caller (classify_core) carries, and it is what the walk needs to keep them apart from the
   side-stack frame the call takes. *)
Definition pz_loc (lyc : alayout) (Sc : astate) (p n : Z) : Prop :=
(exists cid pos, In (cid, pos) (frames Sc) /\
   frame_addr lyc cid pos <= p /\ p + n <= frame_addr lyc cid pos + fs_frame_bytes cid) \/
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= p /\ p + n <= b + req_size m) \/
(ly_stk_lo lyc <= p /\ p + n <= ly_stk_hi lyc).
(* The contract's premises about the frame f (under 50 <= n) and about the out struct o, as one Prop each;
   they are the conjunctions of treac_ctrl_parse_spec, in its order. *)
Definition pz_fok (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
(sp f o : Z) (fr : list byte) : Prop :=
0 < f /\ f + 50 <= 2 ^ 47 /\ amem_range f 50 /\ off_img f 50 /\
(f + 50 <= kLowShadowBeg \/ kHighMemBeg <= f) /\
(sp <= f \/ f + 50 <= sp - REAC_CTRL_PARSE_STK) /\
(forall a, f <= a < f + 50 -> apresent (w_H W) memc a) /\
pz_loc lyc Sc f 50 /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF f 50 /\
shadow_hull_vis (aview SEGS (w_H W) memc) f 50 /\
garr8 SEGS (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) fr) /\
(o + 36 <= f \/ f + 50 <= o).
Definition pz_ook (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(lyc : alayout) (Sc : astate) (own : list (Z * Z)) (W : world SEGS) (memc : word -> option byte)
(sp o : Z) : Prop :=
o mod 32 = 0 /\ 4096 <= o /\ o + 36 <= 2 ^ 47 /\ amem_range o 36 /\ off_img o 36 /\
(o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) /\
o + 36 <= alloc_ceiling /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF o 36 /\
shadow_hull_vis (aview SEGS (w_H W) memc) o 36 /\
(forall a, o <= a < o + 36 ->
   awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a).
(* The entry of the short walk (n < 50): the out struct's region only. *)
Lemma pz_entry0 : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
(regs : bvmap 5 word) (f n o : Z) (fr : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 f -> getr regs 11 = w64 n -> getr regs 12 = w64 o -> 0 <= n < 2 ^ 64 ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_CTRL_PARSE_STK -> spZ regs <= sp0 ->
pz_ook STK sp0 FP ly S lyc Sc own W memc (spZ regs) o ->
st_ok_pi (fx := fq) SEGS VAL (Eimg (Ereg regs (pz_extra (as_uar_cell B) (spZ regs) fr))) ss_pz0
  (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_both3_reac_ctrl_parse)) memc (seg_rom SEGS)))
/\ sh_ok SEGS PZx PZ_SH0 (Eimg (Ereg regs (pz_extra (as_uar_cell B) (spZ regs) fr))) (mrestrict (w_H W) memc).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n o fr HJ H10 H11 H12 Hn Hal16 Hwin Hsp0 Hook.
destruct Hook as (Ho32 & Ho4096 & Ho47 & Hoam & Hoimg & Hosh & Howin & HRo & HHo & HOW).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : REAC_CTRL_PARSE_STK = 8336) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Hobu. pose proof (palf_uar_al B TLF) as Huar4.
pose proof pa_B_ok as HBASE.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (pz_extra (as_uar_cell B) (spZ regs) fr))).
assert (EL : forall n0, (n0 < A_TEXT)%nat -> ew E n0 = ew (Ereg regs (pz_extra (as_uar_cell B) (spZ regs) fr)) n0)
by (intros n0 Hn0; subst E; apply Eimg_low; exact Hn0).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 o) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pz_sp1 (spZ regs))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (as_uar_cell B)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EFB : forall i, (i < 39)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i)).
{ intros i Hi. rewrite EL by (unfold A_TEXT; lia). replace (40 + i)%nat with (32 + (8 + i))%nat by lia.
rewrite ew_Ereg_extra, pz_extra_nth by lia. f_equal. clear - Hi. do 39 (destruct i as [|i]; [reflexivity|]). lia. }
assert (EOB : forall j, (j < 68)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j))) by (intros j Hj; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n0 v, ew E n0 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n0) = v).
{ intros n0 v Hn0 Hv. cbn [base_val]. rewrite Hn0. apply unsigned_lit_small. exact Hv. }
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as HCE.
split.
- unfold ss_pz0. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold pz_regions0, stack_region, uar_got_regionP, uar_cell_regionP, got_regionP, bcell_regionP, pz_out_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o0 Ho0. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|]. constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 34 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pz_vside | pz_vside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
* rewrite (VB 34%nat (as_uar_cell B) E34) by lia.
split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|]. constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | pz_vside | pz_vside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (EOB 0%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 0)); lia).
split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|]. constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite (EOB 12%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); pz_vside | pz_vside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) (EOB 12%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 12)); lia).
split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|]. constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 PZx SB);
[cbn [sv_denot PZx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; pz_vside | pz_vside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
* rewrite (VB 12%nat o E12) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o0 Ho0. apply (apresent_writable SEGS). apply (proj2 (HOW (o + o0) ltac:(lia))).
+ apply pairwise_disjoint_of_extents.
unfold pz_regions0, stack_region, uar_got_regionP, uar_cell_regionP, got_regionP, bcell_regionP, pz_out_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 12%nat o E12) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (EOB 0%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) (EOB 12%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB 34%nat (as_uar_cell B) E34) by lia.
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hsep Hob0 Hob1 Hob12 Hobu Hoimg Howin Hosh Ho4096 Ho47 Hsp0. clear.
unfold off_img. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
unfold pz_facts0. cbn [f_atoms]. apply atoms_ok_app_intro.
* cbn [atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
rewrite Usp, E11, E12, E32, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hal16 Hsp0 Hsp0al Ho4096 Ho47 Ho32 Hn HCE Hobu Huar4. clear.
unfold SB. intros. repeat split; first [lia | match goal with |- ?g => idtac "FACTFAIL" g; fail end].
* apply (atoms_ok_fb E fr EFB). intros i Hi. apply in_seq in Hi. lia.
- unfold sh_ok, PZ_SH0. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) memc E PZx 12 o 36 o 0 36 HRo).
* unfold U, PZx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia. * lia.
* intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* The entry of the walk proper (50 <= n): the frame f's region as well. *)
Lemma pz_entry : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
(regs : bvmap 5 word) (f n o : Z) (fr : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 f -> getr regs 11 = w64 n -> getr regs 12 = w64 o -> 0 <= n < 2 ^ 64 ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_CTRL_PARSE_STK -> spZ regs <= sp0 ->
length fr = 50%nat ->
pz_fok lyc Sc W memc (spZ regs) f o fr ->
pz_ook STK sp0 FP ly S lyc Sc own W memc (spZ regs) o ->
st_ok_pi (fx := fq) SEGS VAL (Eimg (Ereg regs (pz_extra (as_uar_cell B) (spZ regs) fr))) ss_pz
  (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_both3_reac_ctrl_parse)) memc (seg_rom SEGS)))
/\ sh_ok SEGS PZx PZ_SH (Eimg (Ereg regs (pz_extra (as_uar_cell B) (spZ regs) fr))) (mrestrict (w_H W) memc).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n o fr HJ H10 H11 H12 Hn Hal16 Hwin Hsp0 Hflen Hfok Hook.
destruct Hfok as (Hf0 & Hf47 & Hfam & Hfimg & Hfsh & Hfwin & Hfpres & Hfloc & HRf & HHf & HGf & Hdfo).
destruct Hook as (Ho32 & Ho4096 & Ho47 & Hoam & Hoimg & Hosh & Howin & HRo & HHo & HOW).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : REAC_CTRL_PARSE_STK = 8336) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Hobu. pose proof (palf_uar_al B TLF) as Huar4.
pose proof pa_B_ok as HBASE.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (pz_extra (as_uar_cell B) (spZ regs) fr))).
assert (EL : forall n0, (n0 < A_TEXT)%nat -> ew E n0 = ew (Ereg regs (pz_extra (as_uar_cell B) (spZ regs) fr)) n0)
by (intros n0 Hn0; subst E; apply Eimg_low; exact Hn0).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 o) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pz_sp1 (spZ regs))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (as_uar_cell B)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EFB : forall i, (i < 39)%nat -> ew E (40 + i) = Z_to_bv 64 (cp_v fr i)).
{ intros i Hi. rewrite EL by (unfold A_TEXT; lia). replace (40 + i)%nat with (32 + (8 + i))%nat by lia.
rewrite ew_Ereg_extra, pz_extra_nth by lia. f_equal. clear - Hi. do 39 (destruct i as [|i]; [reflexivity|]). lia. }
assert (EOB : forall j, (j < 68)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j))) by (intros j Hj; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n0 v, ew E n0 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n0) = v).
{ intros n0 v Hn0 Hv. cbn [base_val]. rewrite Hn0. apply unsigned_lit_small. exact Hv. }
assert (Hfb : forall i, (i < 50)%nat -> val_mem SEGS (mrestrict (w_H W) memc) (f + Z.of_nat i) 1 (cp_v fr i)).
{ intros i Hi. assert (Hl : (i < length (map (fun b : byte => bv_unsigned b) fr))%nat) by (rewrite length_map, Hflen; lia).
pose proof (proj1 (HGf i Hl)) as Hv.
replace (nth i (map (fun b : byte => bv_unsigned b) fr) 0) with (cp_v fr i) in Hv; [exact Hv|].
unfold cp_v, cp_b. rewrite (nth_indep _ 0 (bv_unsigned cp_z)) by (rewrite length_map, Hflen; lia).
symmetry. apply (map_nth (fun b : byte => bv_unsigned b) fr cp_z i). }
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as HCE.
split.
- unfold ss_pz. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold pz_regions, stack_region, uar_got_regionP, uar_cell_regionP, got_regionP, bcell_regionP, pz_frame_region, pz_out_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o0 Ho0. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|]. constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 34 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pz_vside | pz_vside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
* rewrite (VB 34%nat (as_uar_cell B) E34) by lia.
split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|]. constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | pz_vside | pz_vside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (EOB 0%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 0)); lia).
split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|]. constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite (EOB 12%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); pz_vside | pz_vside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) (EOB 12%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 12)); lia).
split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|]. constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 PZx SB);
[cbn [sv_denot PZx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; pz_vside | pz_vside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
* rewrite (VB 10%nat f E10) by lia. split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
(cbn [seq app map]; repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk (Z.of_nat ?i) (CVal 1 (SOff ?a 0))) =>
apply (chunk_ok_val SEGS E _ f (Z.of_nat i) 1 (SOff a 0) (cp_v fr i));
[ cbn [sv_denot]; replace a with (40 + i)%nat by reflexivity; rewrite (EFB i ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (cp_v_range fr i); pz_vside | pz_vside
| exact (Hfb i ltac:(lia)) ] end).
* rewrite (VB 12%nat o E12) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o0 Ho0. apply (apresent_writable SEGS). apply (proj2 (HOW (o + o0) ltac:(lia))).
+ apply pairwise_disjoint_of_extents.
unfold pz_regions, stack_region, uar_got_regionP, uar_cell_regionP, got_regionP, bcell_regionP, pz_frame_region, pz_out_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat f E10), (VB 12%nat o E12) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (EOB 0%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) (EOB 12%nat ltac:(lia))) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB 34%nat (as_uar_cell B) E34) by lia.
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hsep Hob0 Hob1 Hob12 Hobu Hfimg Hoimg Hfwin Howin Hfsh Hosh
Hf0 Hf47 Ho4096 Ho47 Hdfo Hsp0. clear.
unfold off_img. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
unfold pz_facts. cbn [f_atoms]. apply atoms_ok_app_intro.
* cbn [atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E12, E32, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hal16 Hsp0 Hsp0al Hf0 Hf47 Ho4096 Ho47 Ho32 Hn HCE Hobu Huar4. clear.
unfold SB. intros. repeat split; first [lia | match goal with |- ?g => idtac "FACTFAIL" g; fail end].
* apply (atoms_ok_fb E fr EFB). intros i Hi. apply in_seq in Hi. lia.
- unfold sh_ok, PZ_SH. constructor; [|constructor; [|constructor]].
+ apply (shent_ok_of_range SEGS (w_H W) memc E PZx 10 f 50 f 0 50 HRf).
* unfold U, PZx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia. * lia.
* intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
+ apply (shent_ok_of_range SEGS (w_H W) memc E PZx 12 o 36 o 0 36 HRo).
* unfold U, PZx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia. * lia.
* intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* The shadow entries of the two objects, from their shadow bytes at the current memory. *)
Lemma pz_shok : forall E H mem f o,
ew E 10 = Z_to_bv 64 f -> ew E 12 = Z_to_bv 64 o -> ew E 32 = Z_to_bv 64 SB ->
4096 <= f -> (f + 50 <= kLowShadowBeg \/ kHighMemBeg <= f /\ f + 50 <= ASAN_CEIL) ->
4096 <= o -> (o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o /\ o + 36 <= ASAN_CEIL) ->
range_addressable (aview SEGS H mem) SHADOW_OFF f 50 -> range_addressable (aview SEGS H mem) SHADOW_OFF o 36 ->
sh_ok SEGS PZx PZ_SH E (mrestrict H mem).
Proof.
intros E H mem f o E10 E12 E32 Hf0 Hfap Ho0 Hoap HRf HRo.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as HCE.
unfold sh_ok, PZ_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS H mem E PZx 10 f 50 f 0 50 HRf).
+ unfold U, PZx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia). reflexivity.
+ lia. + lia.
+ intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
- apply (shent_ok_of_range SEGS H mem E PZx 12 o 36 o 0 36 HRo).
+ unfold U, PZx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia). reflexivity.
+ lia. + lia.
+ intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* ---- What the walk keeps of the caller's memory ------------------------------------------------
   pz_kept is the six memory clauses of treac_ctrl_parse_post, in its order: fuzz_grant's acall_kept
   with the out struct o excepted from the first clause as well, because fuzz_disco's contract lets o
   lie above the allocation ceiling (on the machine stack). It is no stronger than what the runtime
   gives across __asan_stack_malloc_1 (acall_kept, see pz_kept_trans): bytes the runtime owns below the
   ceiling (the shadow band among them) are not in it. *)
Definition pz_nf (F FL a : Z) : Prop :=
(F <= a < F + 128) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) \/ a = FL.
Definition pz_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc mem2 : word -> option byte) (slo shi o : Z) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ (o <= a < o + 36) ->
   aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (o <= b + i < o + 36) ->
   aview SEGS (w_H W) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
   (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
   ~ (o <= a < o + 36) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) ->
   apresent (w_H W) memc a -> apresent (w_H W) mem2 a) /\
(forall a, slo <= a < shi -> apresent (w_H W) mem2 a).
Lemma pz_kept_refl : forall lyc Sc W memc slo shi o,
(forall a, slo <= a < shi -> apresent (w_H W) memc a) -> pz_kept lyc Sc W memc memc slo shi o.
Proof.
intros lyc Sc W memc slo shi o Hp.
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros a _ _ H; exact H|]. intros a Ha; exact (Hp a Ha).
Qed.
(* Across a call that gives acall_kept (__asan_stack_malloc_1: aj_stack_malloc_atS, YC85.v:291) whose
   window is inside the walk's and whose excepted bytes are in the out struct. *)
Lemma pz_kept_trans : forall lyc Sc W memc memX memY slo shi slo' shi' o (Eo' : Z -> Prop),
alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
pz_kept lyc Sc W memc memX slo shi o ->
acall_kept SEGS B lyc Sc W memX W memY slo' shi' Eo' ->
slo <= slo' -> shi' <= shi -> (forall a, Eo' a -> o <= a < o + 36) ->
pz_kept lyc Sc W memc memY slo shi o.
Proof.
intros lyc Sc W memc memX memY slo shi slo' shi' o Eo' Hce Hshi (K1 & K2 & K3 & K4 & K5 & K6) (L1 & L2 & L3 & L4 & L5 & L6) Hlo Hhi HE.
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw Ho. rewrite L1 by lia. apply K1; assumption.
- intros b m i Hb Hi Hn. rewrite (L2 b m i Hb Hi) by (intros X; exact (Hn (HE _ X))). apply (K2 b m i Hb Hi Hn).
- intros a Hi Hno He. rewrite L3 by assumption. apply K3; assumption.
- intros cid pos a Hin Hr Hn. rewrite (L4 cid pos a Hin Hr) by (intros X; exact (Hn (HE _ X))). apply (K4 cid pos a Hin Hr Hn).
- intros a Ha Hw Hp. apply L5; [lia | intros [? ?]; apply Hw; lia |]. apply K5; assumption.
- intros a Ha. destruct (Z_lt_ge_dec a slo') as [H1|H1]; [|destruct (Z_lt_ge_dec a shi') as [H2|H2]].
+ apply L5; [lia | intros [? ?]; lia |]. apply K6. lia.
+ apply L6. lia.
+ apply L5; [lia | intros [? ?]; lia |]. apply K6. lia.
Qed.
(* One step of the walk (a run, or a call that gives every byte outside its windows unchanged and
   presence that only grows) keeps it when every byte the step may change is in the call's stack window,
   in the out struct or in NF, a set apart from the caller's blocks, the image and the caller's frames
   and below the allocation ceiling (the own frame: pz_kept_own). *)
Lemma pz_kept_run : forall lyc Sc W memc mdc memX memY slo shi o (NF Zs : Z -> Prop),
AR SEGS B lyc Sc W memc mdc ->
alloc_ceiling <= slo -> shi <= 2 ^ 64 -> off_img o 36 ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> NF (b + i) -> False) ->
(forall a, NF a -> in_img SEGS a -> False) ->
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) -> NF a -> False) ->
(forall a, NF a -> a < alloc_ceiling) ->
(forall a, Zs a -> (slo <= a < shi) \/ (o <= a < o + 36) \/ NF a) ->
pz_kept lyc Sc W memc memX slo shi o ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) memY a = aview SEGS (w_H W) memX a) ->
(forall a, apresent (w_H W) memX a -> apresent (w_H W) memY a) ->
pz_kept lyc Sc W memc memY slo shi o.
Proof.
intros lyc Sc W memc mdc memX memY slo shi o NF Zs HAR Hce Hshi Hoimg HNb HNi HNf HNc HZ (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold off_img in Hoimg.
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw Ho. rewrite Hkp; [apply K1; assumption | lia |].
intros HZa. destruct (HZ a HZa) as [H|[H|H]]; [exact (Hw H) | exact (Ho H) | pose proof (HNc a H); lia].
- intros b m i Hb Hi Ho. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
rewrite Hkp; [apply (K2 b m i Hb Hi Ho) | lia |].
intros HZa. destruct (HZ _ HZa) as [H|[H|H]]; [lia | exact (Ho H) | exact (HNb b m i Hb Hi H)].
- intros a Hi Hno He. pose proof (pa_segs_low a Hi) as Hlow. pose proof (pa_img_range a Hi) as Hr. unfold kLowMemEnd in Hlow.
rewrite Hkp; [apply K3; assumption | lia |].
intros HZa. destruct (HZ a HZa) as [H|[H|H]]; [lia | lia | exact (HNi a H Hi)].
- intros cid pos a Hin Hr Ho.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (G4096 & Gce & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs.
assert (Ha : 0 <= a < alloc_ceiling).
{ destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
rewrite Hkp; [apply (K4 cid pos a Hin Hr Ho) | lia |].
intros HZa. destruct (HZ a HZa) as [H|[H|H]]; [lia | exact (Ho H) | exact (HNf cid pos a Hin Hr H)].
- intros a Ha Hw Hp. apply Hgr. apply K5; assumption.
- intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.
(* A caller frame's bytes and shadow bytes outside the out struct are those at entry; so an object in
   a caller frame stays addressable. An object in a caller block: range_addressable_of_block and
   shadow_hull_vis_of_block (YCbq.v) at the current state; in a frame, its hull: shadow_hull_vis_of_frame. *)
Lemma pz_kept_frame_byte : forall lyc Sc W memc memX slo shi o cid pos a,
pz_kept lyc Sc W memc memX slo shi o -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> ~ (o <= a < o + 36) ->
aview SEGS (w_H W) memX a = aview SEGS (w_H W) memc a.
Proof.
intros lyc Sc W memc memX slo shi o cid pos a (_ & _ & _ & K4 & _) Hin Ha Hn.
apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hn].
Qed.
Lemma pz_kept_ra : forall lyc Sc W memc mdc memX slo shi o cid pos a n,
AR SEGS B lyc Sc W memc mdc ->
pz_kept lyc Sc W memc memX slo shi o -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= a -> a + n <= frame_addr lyc cid pos + fs_frame_bytes cid ->
(forall x, a <= x < a + n -> ~ (o <= shadow_addr x < o + 36)) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF a n ->
range_addressable (aview SEGS (w_H W) memX) SHADOW_OFF a n.
Proof.
intros lyc Sc W memc mdc memX slo shi o cid pos a n HAR (_ & _ & _ & K4 & _) Hin Hlo Hhi Hn HRA x Hx.
destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hal & _ & _ & _).
destruct (frame_al64 SEGS B lyc Sc W memc mdc cid pos HAR Hin) as (_ & Hfs64 & Hfs).
set (F := frame_addr lyc cid pos) in *.
assert (HR : in_zr (shadow_of_addr SHADOW_OFF x) (shadow_addr F, fs_frame_bytes cid / 8)).
{ unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as DS.
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D32. rewrite Hal, Z.add_0_r in D32. rewrite D32. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. apply Z_mod_mult. }
assert (HS8 : fs_frame_bytes cid mod 8 = 0).
{ pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as D64. rewrite Hfs64, Z.add_0_r in D64. rewrite D64. replace (64 * (fs_frame_bytes cid / 64)) with ((8 * (fs_frame_bytes cid / 64)) * 8) by lia. apply Z_mod_mult. }
split.
- assert (F / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
- assert (x / 8 < F / 8 + fs_frame_bytes cid / 8) by (apply Z.div_lt_upper_bound; lia). lia. }
rewrite <- Hs. apply (K4 cid pos _ Hin (or_intror HR)). unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x). apply Hn. exact Hx.
Qed.
(* The own side-stack frame (class 1: 128 bytes at F), its 16 shadow bytes and its flag byte FL, is
   pz_nf above. *)
Lemma pz_awr_cons : forall STK sp0 FP bl0 blc ly own x a,
awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly (x :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own x a [H|[H|[H|(cid & pos & Hin & Hr)]]];
[left; exact H | right; left; exact H | right; right; left; exact H |].
right; right; right. exists cid, pos. split; [right; exact Hin | exact Hr].
Qed.
Lemma pz_own_sep : forall ly S W mem md c p Sc c' p',
AR SEGS B ly S W mem md -> frames S = (c, p) :: frames Sc -> In (c', p') (frames Sc) ->
zdisjoint (frame_rng ly (c, p)) (frame_rng ly (c', p')).
Proof.
intros ly S W mem md c p Sc c' p' HAR Hfr Hin.
destruct (in_split _ _ Hin) as (l2 & l3 & E). rewrite E in Hfr.
exact (sep_frames_pos SEGS B LAWS ly S W mem md (c, p) (c', p') [] l2 l3 HAR Hfr).
Qed.
(* The own frame is apart from everything acall_kept keeps: the caller's blocks, the image, the caller's
   frames and their shadow bytes; and it lies below the allocation ceiling. *)
Lemma pz_nf_sep : forall lyc Sc S2 W mem2 md2 fpos F FL,
AR SEGS B lyc S2 W mem2 md2 ->
frames S2 = (1, fpos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
F = frame_addr lyc 1 fpos -> FL = flag_addr lyc 1 fpos ->
frame_flag_lawP SEGS B ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> pz_nf F FL (b + i) -> False) /\
(forall a, pz_nf F FL a -> in_img SEGS a -> False) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) -> pz_nf F FL a -> False) /\
(forall a, pz_nf F FL a -> a < alloc_ceiling).
Proof.
intros lyc Sc S2 W mem2 md2 fpos F FL HAR2 Hfrs Eab -> -> FFL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin : In (1, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin) as (HF4096 & HFceil & _).
pose proof (frm_off_imgP B _ _ _ _ _ 1 fpos HAR2 Hfin) as HFimg.
destruct (FFL _ _ _ _ _ 1 fpos HAR2 Hfin) as (_ & HFLown & (HFLapp & HFLimg) & (HFL4096 & _ & HFLce)).
destruct (frame_al64 SEGS B _ _ _ _ _ 1 fpos HAR2 Hfin) as (HF64 & _ & _).
change (fs_frame_bytes 1) with 128 in HFapp, HFceil, HFimg, HFpres.
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, HFimg.
assert (HFS : SHADOW_OFF + F / 8 + 16 <= kHighShadowEnd /\ kLowShadowBeg < SHADOW_OFF + F / 8).
{ assert (Hd : (F + 16 * 8) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia).
rewrite Z.div_add in Hd by lia. change (140737479966720 / 8) with 17592184995840 in Hd.
assert (0 <= F / 8) by (apply Z.div_pos; lia).
unfold SHADOW_OFF, kHighShadowEnd, kLowShadowBeg. lia. }
unfold kHighShadowEnd, kLowShadowBeg, SHADOW_OFF in HFS.
split; [|split; [|split]].
- intros b m i Hb Hi Hn. rewrite <- Eab in Hb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & Hb4096 & Hbce & Hbapp & Hbown & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 1 fpos HAR2 Hb Hfin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. fold F in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
destruct Hn as [Hn|[Hn|Hn]]; [lia | unfold SHADOW_OFF in Hn; lia |].
exact (proj2 (Hbown (b + i) ltac:(lia)) ltac:(rewrite Hn; exact HFLown)).
- intros a Hn Hi. pose proof (pa_img_range a Hi) as Hr.
destruct Hn as [Hn|[Hn|Hn]]; [lia | unfold SHADOW_OFF in Hn; lia | subst a; exact (HFLimg Hi)].
- intros cid pos a Hin Hr Hn.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; right; exact Hin).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 Hin2) as (HGal & HGapp & HGpres & HGSpres).
destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HAR2 Hin2) as (HG64 & HGs64 & HGs).
pose proof (pz_own_sep _ _ _ _ _ 1 fpos Sc cid pos HAR2 Hfrs Hin) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. fold F in Hd.
set (G := frame_addr lyc cid pos) in *. set (gs := fs_frame_bytes cid) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp.
destruct Hn as [Hn|[Hn|Hn]].
+ destruct Hr as [Hr|Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
pose proof (shadow_range_end G gs ltac:(lia)) as Hse. unfold shadow_addr in Hse, Hr. fold G in Hr.
assert ((G + gs) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). assert (0 <= G / 8) by (apply Z.div_pos; lia).
change (2 ^ 47 / 8) with (2 ^ 44) in *. unfold SHADOW_OFF in Hr, Hse. lia.
+ destruct Hr as [Hr|Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [unfold SHADOW_OFF in Hn; lia|].
unfold shadow_addr in Hr. fold G in Hr.
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. pose proof (Z.div_mod G 64 ltac:(lia)) as DG.
pose proof (Z.div_mod gs 64 ltac:(lia)) as DS. rewrite HF64, Z.add_0_r in DF. rewrite HG64, Z.add_0_r in DG. rewrite HGs64, Z.add_0_r in DS.
assert (EF : F / 8 = 8 * (F / 64)) by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (EG : G / 8 = 8 * (G / 64)) by (rewrite DG at 1; replace (64 * (G / 64)) with ((8 * (G / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (ES : gs / 8 = 8 * (gs / 64)) by (rewrite DS at 1; replace (64 * (gs / 64)) with ((8 * (gs / 64)) * 8) by lia; apply Z.div_mul; lia).
unfold SHADOW_OFF in Hn, Hr. lia.
+ subst a. destruct Hr as [Hr|Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
* exact (proj2 (HGpres FL ltac:(fold G gs; lia)) HFLown).
* unfold shadow_addr in Hr. fold G in Hr.
exact (proj2 (HGSpres (FL - shadow_addr G) ltac:(unfold shadow_addr; fold G; lia))
ltac:(replace (shadow_addr G + (FL - shadow_addr G)) with FL by lia; exact HFLown)).
- intros a [Hn|[Hn|Hn]]; [lia | unfold SHADOW_OFF in Hn; lia | lia].
Qed.
(* One step of the walk keeps the caller's memory when each byte it may change is in the call's stack
   window, in the out struct or in the own frame (fuzz_grant's pz_kept_own without the caller frame of
   o: off_img o 36 takes its place). *)
Lemma pz_kept_own : forall lyc Sc S2 W memc mdc mem2 md2 memX memY slo shi o fpos F FL (Zs : Z -> Prop),
AR SEGS B lyc Sc W memc mdc -> AR SEGS B lyc S2 W mem2 md2 ->
frames S2 = (1, fpos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
F = frame_addr lyc 1 fpos -> FL = flag_addr lyc 1 fpos -> frame_flag_lawP SEGS B ->
alloc_ceiling <= slo -> shi <= 2 ^ 64 -> off_img o 36 ->
(forall a, Zs a -> (slo <= a < shi) \/ (o <= a < o + 36) \/ pz_nf F FL a) ->
pz_kept lyc Sc W memc memX slo shi o ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) memY a = aview SEGS (w_H W) memX a) ->
(forall a, apresent (w_H W) memX a -> apresent (w_H W) memY a) ->
pz_kept lyc Sc W memc memY slo shi o.
Proof.
intros lyc Sc S2 W memc mdc mem2 md2 memX memY slo shi o fpos F FL Zs HAR HAR2 Hfrs Eab EF EFL FFL Hce Hshi Hoimg HZ KP Hkp Hgr.
destruct (pz_nf_sep lyc Sc S2 W mem2 md2 fpos F FL HAR2 Hfrs Eab EF EFL FFL) as (N1 & N2 & N3 & N4).
exact (pz_kept_run lyc Sc W memc mdc memX memY slo shi o (pz_nf F FL) Zs HAR Hce Hshi Hoimg N1 N2 N3 N4 HZ KP Hkp Hgr).
Qed.
(* An object the caller may write (the out struct) is apart from the own frame: each case of awr_byte
   is - the machine stack is above the allocation ceiling, a caller block and a caller frame are apart
   from the frame the call took, and the own frames of the journal are frames of Sc. *)
Lemma pz_awr_nf : forall STK sp0 FP ly S lyc Sc own W memc mdc a F FL,
AR SEGS B lyc Sc W memc mdc ->
(forall cid pos, In (cid, pos) own -> In (cid, pos) (frames Sc)) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> pz_nf F FL (b + i) -> False) ->
(forall cid pos x, In (cid, pos) (frames Sc) ->
(in_zr x (frame_rng lyc (cid, pos)) \/ in_zr x (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) -> pz_nf F FL x -> False) ->
(forall x, pz_nf F FL x -> x < alloc_ceiling) ->
alloc_ceiling <= sp0 - STK ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a -> ~ pz_nf F FL a.
Proof.
intros STK sp0 FP ly S lyc Sc own W memc mdc a F FL HAR Hown N1 N3 N4 Hstk Hw Hn.
pose proof (N4 a Hn) as Hlt.
destruct Hw as [H|[(HFP & b & m & Hb & Hab)|[(b & m & Hb & _ & Hab)|(cid & pos & Hin & Hr)]]].
- lia.
- exact (N1 b m (a - b) Hb ltac:(lia) ltac:(replace (b + (a - b)) with a by lia; exact Hn)).
- exact (N1 b m (a - b) Hb ltac:(lia) ltac:(replace (b + (a - b)) with a by lia; exact Hn)).
- exact (N3 cid pos a (Hown cid pos Hin) Hr Hn).
Qed.
(* The same for an object that is only read (the frame f): its place is one of the three the contract
   names, and each is apart from the own frame. *)
Lemma pz_loc_nf : forall lyc Sc W memc mdc p n a F FL,
AR SEGS B lyc Sc W memc mdc -> pz_loc lyc Sc p n ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> pz_nf F FL (b + i) -> False) ->
(forall cid pos x, In (cid, pos) (frames Sc) ->
(in_zr x (frame_rng lyc (cid, pos)) \/ in_zr x (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) -> pz_nf F FL x -> False) ->
(forall x, pz_nf F FL x -> x < alloc_ceiling) ->
alloc_ceiling <= ly_stk_lo lyc ->
p <= a < p + n -> ~ pz_nf F FL a.
Proof.
intros lyc Sc W memc mdc p n a F FL HAR Hloc N1 N3 N4 Hstk Ha Hn.
pose proof (N4 a Hn) as Hlt.
destruct Hloc as [(cid & pos & Hin & Hlo & Hhi)|[(b & m & Hb & Hlo & Hhi)|(Hlo & Hhi)]].
- exact (N3 cid pos a Hin ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; lia) Hn).
- exact (N1 b m (a - b) Hb ltac:(lia) ltac:(replace (b + (a - b)) with a by lia; exact Hn)).
- lia.
Qed.
End h.
End d.
End b.
