(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_Klib.v:146-200
   (aj_strlen_at) at origin/ossv/recipes f26f9fbd8777 [Apache-2.0]; proofs/reac-pw/fuzz_pin/lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at)
   [Apache-2.0 OR MIT]; proofs/reac-pw/fuzz_qdisc/lib/A/QPgSlots.v, QPgCheck.v, QPgRt.v [Apache-2.0] and QPgLoop0.v [Apache-2.0 OR MIT]
   at 160c9b4d5750 (walk tactics and plumbing lemmas); proofs/reac-pw/fuzz_pin/lib/A/ACep.v (reseat) [Apache-2.0]; for
   reac-pw/fuzz_pin's image A walk of fuzz_catalogue_row: the two call lemmas keep the wrappers' same_but_materialized
   clause, the copied tactics carry the rw_ prefix, and the walk, its loop and its call-site lemmas are new. The
   [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgRow.v, with its module paths, module names and numbers changed; 539 of its 613 lines of code are new or changed and 843 lines of the source are left out. *)
(* Segment S2 of the walk of reac-pw/fuzz_pin's LLVMFuzzerTestOneInput (0x806b4, fuzz_pin.asan sha256
   3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16): from the cut ss_Q (0x8082c, malloc returned the
   block q) to ss_C (0x80868, the string is not empty) or ss_D (0x808bc, the empty string). rule 24 (reuse): no
   function is proved here; the callee contracts __asan_memcpy (aintrin_realizes OCpy 0x51a40) and the strlen wrapper
   (astrlen_realizes 0x41908) are Section hypotheses.

   The code (the neutral disassembly of the function):
     0x8082c mv s3,a0 (s3 = q); 0x80830 beqz s5 (k = 0 -> 0x80844);
     0x80834-0x80840 a0 = q, a1 = r (the rest pointer), a2 = k, __asan_memcpy(q, r, k);
     0x80844 a0 = q + k; 0x80848-0x80854 the instrumented check of the byte q + k (shadow byte, slow path 0x80a74,
     error path 0x80a7c not reached: the block (q, k + 1) has req_size k + 1); 0x80858 sb zero,0(a0);
     0x8085c-0x80860 strlen(q) through the wrapper's jump 0x41908 (it returns k: the string pin_str has no NUL and
     q[k] = 0); 0x80864 beqz a0 -> 0x808b4 (s4 = s5 = 0) -> 0x808bc = ss_D; else 0x80868 = ss_C.
   The two paths of 0x80830 meet at the local cut ss_M (0x80844), with INV_M: the first k bytes of the block are the
   string's. pm_S2q proves Q -> M (with the call site pin_memcpy_site), pm_S2m proves M -> C / D (the byte q + k is a
   one-byte region on slot 530, the call through aj_strlen_atS with the call site pin_strlen_site_main), pm_S2 is
   their composition. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw1 AWalkFw2 ACfm PPgBase PPgCSpec PPgMainCall PPgMainRt PPgMainSt.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.Rt Require Import StrlenDef WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgWrap.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.Prog Require Import PinBlkTail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* the walk's local cut ss_M at 0x80844: ss_Q's frame part and atoms, s3 = q (slot 100), s5 = k (slot 102), s9 = the
   flags (slot 103); the rest pointer and every temporary dead (slots 540 ..) *)
Definition pm_M_deads : list nat := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 20; 26; 27; 28; 29; 30; 31]%nat.
Definition pm_M_deads_bv : list (bv 5) := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 20; 26; 27; 28; 29; 30; 31]%bv.
Definition pm_M_regs : list sv :=
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 9 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 75 0; SOff 100 0; SOff 20 0; SOff 102 0; SOff 32 0; SOff 88 0;
 SOff 75 0; SOff 103 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition ss_M : sstate := Eval vm_compute in
ss_havoc_regs (mkSS 0x80844 pm_M_regs pm_mem None
(mkFacts (pm_atoms ++ [(100%nat, HPTR 4); (102%nat, mkAF 0 (2 ^ 26 - 1) 0); (103%nat, mkAF 0 255 0)]) [] pm_alias))
540 pm_M_deads.
Lemma nth_firstn_lt : forall (A : Type) (l : list A) (k j : nat) (d : A), (j < k)%nat -> nth j (firstn k l) d = nth j l d.
Proof.
intros A l. induction l as [|x l IH]; intros k j d Hj.
- rewrite firstn_nil. reflexivity.
- destruct k as [|k]; [lia|]. destruct j as [|j]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma pin_str_nth : forall pl j, (j < pin_k pl)%nat ->
nth j (pin_zbytes (pin_str pl)) 0 = nth (S j) (map (fun b : byte => bv_unsigned b) pl) 0.
Proof.
intros pl j Hj. unfold pin_zbytes, pin_str, pin_rest. rewrite <- firstn_map. rewrite nth_firstn_lt by exact Hj.
destruct pl as [|b pl]; cbn [tl map]; [destruct j; reflexivity | reflexivity].
Qed.
Lemma pin_k_le : forall pl, (pl = [] -> pin_k pl = 0%nat) /\ (Z.of_nat (pin_k pl) <= Z.of_nat (length pl) - 1 \/ pl = []).
Proof.
intros pl. pose proof (nul_idx_le (pin_rest pl)) as H. unfold pin_k. destruct pl as [|b pl]; cbn [pin_rest tl length] in *.
- split; [reflexivity | right; reflexivity].
- split; [discriminate | left; lia].
Qed.
Lemma garr8_of_aview : forall H m base l,
(forall j, (j < length l)%nat -> aview tfibsegs H m (base + Z.of_nat j) = Some (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
garr8 tfibsegs (mrestrict H m) base l.
Proof. intros H m base l Hv j Hj. destruct (Hv j Hj) as [Ha Hr]. split; [apply val_mem1_of_aview; exact Ha | exact Hr]. Qed.
Lemma pin_str_byte_nz : forall pl j, (j < pin_k pl)%nat -> nth j (pin_zbytes (pin_str pl)) 0 <> 0.
Proof.
intros pl j Hj HC.
assert (Hlen : (j < length (pin_str pl))%nat) by (rewrite pin_str_length; exact Hj).
pose proof (map_nth (fun b : byte => bv_unsigned b) (pin_str pl) NUL j) as HM. cbn beta in HM.
replace (bv_unsigned NUL) with 0 in HM by (vm_compute; reflexivity).
unfold pin_zbytes in HC. rewrite HM in HC.
apply (pin_str_no_nul pl).
assert (HE : nth j (pin_str pl) NUL = NUL)
by (apply (f_equal (Z_to_bv 8)) in HC; rewrite Z_to_bv_bv_unsigned in HC; exact HC).
rewrite <- HE. apply nth_In. exact Hlen.
Qed.
Lemma U_add2 : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = x + y.
Proof.
intros E a b x y Ha Hb Hx Hy Hxy. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E a x Ha) by lia. rewrite (U_atom E b y Hb) by lia. apply zcanon_id. unfold M64; lia.
Qed.
Lemma garr8_of_frame : forall E rs H (m m' : word -> option byte) base l,
garr8 tfibsegs (mrestrict H m) base l ->
(forall a, base <= a < base + Z.of_nat (length l) -> 0 <= a < 2 ^ 64 /\ ~ in_wrange E rs a) ->
frame_of E rs (mrestrict H m) (mrestrict H m') ->
garr8 tfibsegs (mrestrict H m') base l.
Proof.
intros E rs H m m' base l HG Hno HF.
apply (garr8_frame tfibsegs _ _ base l HG). intros a Ha.
destruct (Hno a Ha) as [Hr Hn]. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Definition INV_M (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k = 1 /\ acc <= mo_malloc MT (2 ^ 26) /\
exists q kk fl,
ew E 100 = Z_to_bv 64 q /\ ew E 102 = Z_to_bv 64 kk /\ ew E 103 = Z_to_bv 64 fl /\
kk = Z.of_nat (pin_k (c_pl cx)) /\ fl = pin_flags (c_pl cx) /\
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(q, kk + 1)] /\
garr8 tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) q (pin_zbytes (pm_s cx)).
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis FP0 : FP = [].
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy 0x51a40.
Hypothesis ASTRLEN : astrlen_realizes tfibsegs B 0x41908.
(* the input bytes p + 1 + j (j < k) at any state the journal reaches: the spec string's bytes *)
Lemma pin_rest_view : forall cx own ly3 S3 W3 mem3 md3 kj q kk j,
rt_base B MT cx ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 kj ->
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(q, kk)] ->
(j < pin_k (c_pl cx))%nat ->
aview tfibsegs (w_H W3) mem3 (c_p cx + 1 + Z.of_nat j) = Some (nth j (pin_zbytes (pm_s cx)) 0) /\
0 <= nth j (pin_zbytes (pm_s cx)) 0 < 256.
Proof.
intros cx own ly3 S3 W3 mem3 md3 kj q kk j HB HJ Eab Hj.
destruct cx as [ly S W regs mem md p n pl fpos sp1 E0 T]. unfold pm_s. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl] in *.
unfold rt_base in HB. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_fpos c_sp1 c_E0 c_T] in HB.
destruct HB as (HPRE & Hra & Hp & Hn & Hpn & Hnpl & HPL & _).
destruct (pin_k_le pl) as [Hk_nil [Hle | Hpl0]]; [| subst pl; rewrite (Hk_nil eq_refl) in Hj; lia].
destruct Hpn as [[Hn0 _] | [Hnr Hpin]]; [exfalso; lia|].
assert (Hpin3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab; apply in_or_app; left; exact Hpin).
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite <- Z.add_assoc. rewrite (F2 p n (1 + Z.of_nat j) Hpin Hpin3); [| rewrite Hrq; lia | rewrite FP0; apply inFP_nil].
pose proof (HPL (Datatypes.S j) ltac:(rewrite length_map; lia)) as [Hv Hr].
replace (p + Z.of_nat (Datatypes.S j)) with (p + (1 + Z.of_nat j)) in Hv by lia.
rewrite pin_str_nth by exact Hj. split; [apply aview_of_val_mem1; [exact Hv | exact Hr] | exact Hr].
Qed.
(* the call site 0x80840: the state there gives every premise of aintrin_realizes OCpy at (q, r, k) *)
Lemma pin_memcpy_site : forall cx ly3 S3 W3 mem3 md3 kj regsT q r kk o,
rt_base B MT cx ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, c_fpos cx)] ly3 S3 W3 mem3 md3 kj ->
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(q, kk + 1)] ->
kk = Z.of_nat (pin_k (c_pl cx)) -> 0 < kk ->
r = (if c_n cx =? 0 then c_p cx else c_p cx + 1) ->
spZ regsT = spZ (c_regs cx) + o -> -144 <= o <= 0 ->
0 <= kk < 2 ^ 32 /\ 0 <= q /\ q + kk <= 2 ^ 63 /\
(forall a, q <= a < q + kk ->
 awr_byte LLVMF_STK (spZ (c_regs cx)) FP (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(1, c_fpos cx)] a /\
 ~ (spZ (c_regs cx) + o - ESTACK <= a < spZ (c_regs cx) + o)) /\
amem_range q kk /\
range_addressable (aview tfibsegs (w_H W3) mem3) SHADOW_OFF q kk /\
(0 < kk -> shadow_hull_vis (aview tfibsegs (w_H W3) mem3) q kk) /\
(0 <= r /\ r + kk <= 2 ^ 63 /\ src_ok tfibsegs W3 regsT mem3 r kk /\ (q + kk <= r \/ r + kk <= q) /\ amem_range r kk /\
 range_addressable (aview tfibsegs (w_H W3) mem3) SHADOW_OFF r kk /\ (0 < kk -> shadow_hull_vis (aview tfibsegs (w_H W3) mem3) r kk)).
Proof.
intros cx ly3 S3 W3 mem3 md3 kj regsT q r kk o HB HJ Eab Hkk Hk0 Hr Hsp Ho.
destruct cx as [ly S W regs mem md p n pl fpos sp1 E0 T]. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_fpos] in *.
unfold rt_base in HB. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_fpos c_sp1 c_E0 c_T] in HB.
destruct HB as (HPRE & Hra & Hp & Hn & Hpn & Hnpl & HPL & _).
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (pin_k_le pl) as [Hk_nil [Hle | Hpl0]]; [| subst pl; rewrite (Hk_nil eq_refl) in Hkk; cbn in Hkk; lia].
destruct Hpn as [[Hn0 _] | [Hnr Hpin]]; [exfalso; lia|].
rewrite (proj2 (Z.eqb_neq n 0) ltac:(lia)) in Hr.
pose proof (proj1 HJ) as HAR3.
assert (Hq3 : In (q, kk + 1) (ablocks B ly3 S3)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
assert (Hp3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab; apply in_or_app; left; exact Hpin).
assert (Hrq : req_size (kk + 1) = kk + 1) by (unfold req_size; destruct (Z.eqb_spec (kk + 1) 0); lia).
assert (Hrqn : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q (kk + 1) HAR3 Hq3) as (_ & Hq4096 & Hqceil & _ & _ & _ & _). rewrite Hrq in Hqceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR3 Hp3) as (_ & Hp4096 & Hpceil & _ & Hppres & _ & _). rewrite Hrqn in Hpceil, Hppres.
pose proof (sep_tmp_entry B LAWS ly3 S3 W3 mem3 md3 (ablocks B ly S) q (kk + 1) p n HAR3 ltac:(rewrite Eab; apply Permutation_refl) Hpin) as Hdj.
rewrite Hrq, Hrqn in Hdj.
pose proof (ajournal_init tfibsegs B LLVMF_STK FP ly S W regs mem md [] HPRE) as HJ0.
split; [lia|]. split; [lia|]. split; [lia|].
split.
{ intros a Ha. split.
  - replace a with (q + (a - q)) by lia.
    apply (awr_new_block_any tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q (kk + 1) (ablocks B ly3 S3) (a - q) ly3 [(1, fpos)] HJ0 HAR3 Eab ltac:(lia) Hq3).
    rewrite Hrq. lia.
  - rewrite Hes. lia. }
split; [apply (amem_range_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 q (kk + 1)); [exact HAR3 | exact Hq3 | lia | rewrite Hrq; lia]|].
split; [apply (range_addressable_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 q (kk + 1)); [exact HAR3 | exact Hq3 | lia | rewrite Hrq; lia]|].
split; [intros Hk; apply (shadow_hull_vis_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 q (kk + 1)); [exact HAR3 | exact Hq3 | lia | rewrite Hrq; lia | exact Hk]|].
subst r. split; [lia|]. split; [lia|].
split.
{ intros a Ha. split.
  - apply (aview_some_of_apresent tfibsegs). apply (proj1 (Hppres a ltac:(lia))).
  - rewrite Hsp, Hes. lia. }
split; [lia|].
split; [apply (amem_range_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 p n); [exact HAR3 | exact Hp3 | lia | rewrite Hrqn; lia]|].
split; [apply (range_addressable_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 p n); [exact HAR3 | exact Hp3 | lia | rewrite Hrqn; lia]|].
intros Hk; apply (shadow_hull_vis_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 p n); [exact HAR3 | exact Hp3 | lia | rewrite Hrqn; lia | exact Hk].
Qed.
(* Q -> M: 0x8082c .. 0x80844, the k = 0 branch and the __asan_memcpy branch *)
Lemma pm_S2q : rt_from B MT FP POST ss_M (INV_M B MT) -> rt_from B MT FP POST ss_Q (INV_Q B MT).
Proof.
intros RM. rt_prelude.
pose proof HINV as (Hk0 & Hacc & q & r & kk & fl & E100 & E101 & E102 & E103 & Hkk & Hfl & Hr & Eab3).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
assert (Hq3 : In (q, kk + 1) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; left; reflexivity).
destruct (pin_k_le pl) as [Hk_nil Hk_le].
assert (Hkk0 : 0 <= kk < 2 ^ 26) by (rewrite Hkk; destruct Hk_le as [Hle | ->]; [clear - Hle Hnpl Hn26; lia | rewrite (Hk_nil eq_refl); cbn; lia]).
reshok HS.
aj_run_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan.
{ awrRT AG fpos F EFA3. }
clear_frames.
reshok HS.
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tfibtbl_lib_ok HS SH RTBspan end.
all: lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
all: hc_bool Hc ltac:(fun H => hc_atom H 102%nat kk E102 ltac:(lia)).
all: hc_prop Hc.
- (* k = 0: 0x80830 beqz taken, to 0x80844 *)
  norm_ss HS. reshok HS.
  aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan 0x80844.
  { awrRT AG fpos F EFA3. }
  clear_frames.
  ra_join_win HS ss_M 540%nat pm_M_deads_bv ltac:(idtac).
  let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv.
  rt_hand RM HS.
  split; [exact Hk0|]. split; [exact Hacc|].
  exists q, kk, fl.
  split; [exact E100|]. split; [exact E102|]. split; [exact E103|].
  split; [exact Hkk|]. split; [exact Hfl|]. split; [exact Eab3|].
  assert (Hpk : pin_k pl = 0%nat) by lia.
  unfold pm_s, pin_str. cbn [c_pl]. rewrite Hpk. apply garr8_nil.
- (* k <> 0: 0x80834-0x80840, __asan_memcpy(q, r, k) *)
  norm_ss HS. reshok HS.
  aj_run_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan.
  { awrRT AG fpos F EFA3. }
  clear_frames.
  rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
  rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2.
  lazymatch type of Rsp with getr ?rg 2 = _ =>
  assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp; ewpeel; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia) end.
  assert (Hk0' : 0 < kk) by lia.
  pose proof HJ3 as HJc.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msX) _) ?mdX) _ =>
  pose proof (pin_memcpy_site (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX) q r kk (sp1 - spZ regs)
    HBASE0 HJ3 Eab3 Hkk Hk0' Hr ltac:(cbn [c_regs]; rewrite EspX; lia) ltac:(clear - Hsp1; lia)) as SITE end.
  cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_fpos] in SITE.
  destruct SITE as (Sn & Sd0 & Sdn & Sdest & Samr & Sra & Shull & Sx0 & Sxn & Ssrc & Sdj & Samx & Srax & Shx).
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msX) _) ?mdX) _ =>
    eapply (aj_intrin_atS tfibsegs B LAWS Hsegs OCpy 0x51a40 AICPY W3 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly3 S3 mdX k q r kk (sp1 - spZ regs) _ HJ3) end.
    - rewrite Ra0. ewpeel. rewrite E100. reflexivity.
    - rewrite Ra1. ewpeel. rewrite E101. reflexivity.
    - rewrite Ra2. ewpeel. rewrite E102. reflexivity.
    - exact Sn. - exact Sd0. - exact Sdn.
    - rewrite EspX. clear; lia.
    - rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
    - clear - Hsp1; lia.
    - rewrite FFS, Hes. clear - Hsp1; lia.
    - rewrite Rgp. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite Rtp. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact Rra.
    - first [vm_compute; reflexivity | apply ret_ok_even; vm_compute; reflexivity].
    - exact Sdest. - exact Samr. - exact Sra. - exact Shull.
    - exact (conj Sx0 (conj Sxn (conj Ssrc (conj Sdj (conj Samx (conj Srax Shx)))))). }
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Hcopy & Hfr4 & Hpres4 & Hsame4).
  cbv beta iota in Hcopy.
  replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr4 by (clear; lia).
  assert (Hn0 : n <> 0) by (intros Hn0; destruct Hk_le as [Hle | Hpl0]; [clear - Hn0 Hnpl Hle Hk0'; lia | rewrite (Hk_nil Hpl0) in Hkk; cbn in Hkk; lia]).
  rewrite (proj2 (Z.eqb_neq n 0) Hn0) in Hr.
  assert (HdQF : q + (kk + 1) <= F \/ F + 128 <= q).
  { pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 _ _ _ q (kk + 1) 1 fpos HAR3 Hq3 Hfin3) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. change (fs_frame_bytes 1) with 128 in D. rewrite EFA3 in D. fold F in D.
    assert (Hrq : req_size (kk + 1) = kk + 1) by (unfold req_size; destruct (Z.eqb_spec (kk + 1) 0); lia). rewrite Hrq in D. exact D. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q (kk + 1) HAR3 Hq3) as (_ & Hq4096 & Hqceil & Hqapp & _ & _ & _).
  assert (Hrq1 : req_size (kk + 1) = kk + 1) by (unfold req_size; destruct (Z.eqb_spec (kk + 1) 0); lia).
  rewrite Hrq1 in Hqceil, Hqapp.
  reseat HS HJ4 HP4 [0; 1; 2]%nat AG
  ltac:(idtac; eapply region_kept_aview; [ evalE AG | intros a Ha; apply Hfr4;
     clear - Ha Hq4096 Hqceil Hqapp HdQF Hkk0 HF4096 HFceil HFhigh HF8lo HF8hi HF8c Hceil Hslo Hstk0 Hsp1 FFS C1 C3 Hshi H47;
     unfold in_app, SB, ESTACK, kLowShadowBeg, kHighMemBeg in *; lia | exact Hpres4 ]).
  ra_join_win HS ss_M 540%nat pm_M_deads_bv ltac:(idtac).
  let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv.
  rt_hand RM HS.
  split; [exact Hk0|]. split; [exact Hacc|].
  exists q, kk, fl.
  split; [exact E100|]. split; [exact E102|]. split; [exact E103|].
  split; [exact Hkk|]. split; [exact Hfl|]. split; [exact Eab3|].
  apply garr8_of_aview. intros j Hj.
  unfold pin_zbytes, pm_s in Hj. cbn [c_pl] in Hj. rewrite length_map, pin_str_length in Hj.
  cbn [ms_mem mkst].
  assert (Hjk : 0 <= Z.of_nat j < kk) by lia.
  rewrite (Hcopy (Z.of_nat j) Hjk).
  replace (r + Z.of_nat j) with (p + 1 + Z.of_nat j) by lia.
  exact (pin_rest_view (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) [(1, fpos)] ly3 S3 W3 _ _ k q (kk + 1) j HBASE0 HJc Eab3 Hj).
Qed.
(* The journal-threaded form of astrlen_realizes: the wrapper's window is 2 * ESTACK below sp. *)
Lemma aj_strlen_atS : forall pc, astrlen_realizes tfibsegs B pc ->
forall W regsT memT STK sp0 FPx ly S W0 mem md own lyc Sc mdc kj x kx (o : Z) raw,
ajournal tfibsegs B STK sp0 FPx ly S W0 mem md own lyc Sc W memT mdc kj ->
getr regsT 10 = w64 x -> 0 < x ->
0 <= kx -> kx + 1 < 2 ^ 32 -> x + kx + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte tfibsegs W memT x (kx + 1) 0 kx ->
src_ok tfibsegs W regsT memT x (kx + 1) ->
(forall a, x <= a <= x + kx -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x (kx + 1) ->
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF x (kx + 1) ->
shadow_hull_vis (aview tfibsegs (w_H W) memT) x (kx + 1) ->
(forall a, x + kx < a < x + kx - (x + kx) mod 8 + 8 -> aview tfibsegs (w_H W) memT a <> None) ->
aro_unowned tfibsegs B (aview tfibsegs (w_H W) memT) ->
SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom tfibsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK sp0 FPx ly S W0 mem md own lyc Sc W mem2 md2 kj /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 kx /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof.
intros pc AS W regsT memT STK sp0 FPx ly S W0 mem md own lyc Sc mdc kj x kx o raw
HJ Ha0 Hx0 Hk0 Hk32 Hxk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsrc Hoff Hamr Hrad Hhull Htail Hro.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HPRE : ecall_pre tfibsegs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
  split; [rewrite Hsp', Z.add_mod, Hal16, Hal by lia; reflexivity|].
  split; [rewrite Eslo, Hsp'; lia|]. split; [rewrite Eshi, Hsp'; lia|].
  split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; lia|].
  split; [exact Hgp | exact Htp]. }
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; lia).
assert (HpresE : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; lia).
eapply SRr_mono.
{ exact (AS lyc Sc W regsT memT mdc x kx HPRE Hlo2 HpresE Ha0 Hx0 Hk0 Hk32 Hxk Hfb Hsrc
    ltac:(rewrite Hsp'; exact Hoff) Hamr Hrad Hhull Htail Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write tfibsegs B LAWS tfib_segs_low STK sp0 FPx ly S W0 mem md own lyc Sc W memT mdc kj mem2 md2
  (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2. - exact Hsame.
  - intros a Ha. left. left. lia.
  - exact HAR2. - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact Hpres2 | exact Hsame].
Qed.
(* The call site 0x80860: the state there gives every premise of astrlen_realizes at x = q, k = kk. *)
Lemma pin_strlen_site_main : forall cx ly3 S3 W3 mem3 md3 kj regsT q kk o,
rt_base B MT cx ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, c_fpos cx)] ly3 S3 W3 mem3 md3 kj ->
In (q, kk + 1) (ablocks B ly3 S3) ->
kk = Z.of_nat (pin_k (c_pl cx)) ->
garr8 tfibsegs (mrestrict (w_H W3) mem3) q (pin_zbytes (pm_s cx) ++ [0]) ->
spZ regsT = spZ (c_regs cx) + o -> -144 <= o <= 0 ->
0 < q /\ 0 <= kk /\ kk + 1 < 2 ^ 32 /\ q + kk + 1 <= 2 ^ 63 /\
first_byte tfibsegs W3 mem3 q (kk + 1) 0 kk /\
src_ok tfibsegs W3 regsT mem3 q (kk + 1) /\
(forall a, q <= a <= q + kk -> ~ (spZ (c_regs cx) + o - 2 * ESTACK <= a < spZ (c_regs cx) + o)) /\
amem_range q (kk + 1) /\
range_addressable (aview tfibsegs (w_H W3) mem3) SHADOW_OFF q (kk + 1) /\
shadow_hull_vis (aview tfibsegs (w_H W3) mem3) q (kk + 1) /\
(forall a, q + kk < a < q + kk - (q + kk) mod 8 + 8 -> aview tfibsegs (w_H W3) mem3 a <> None) /\
aro_unowned tfibsegs B (aview tfibsegs (w_H W3) mem3).
Proof.
intros cx ly3 S3 W3 mem3 md3 kj regsT q kk o HB HJ Hq3 Hkk HG Hsp Ho.
destruct cx as [ly S W regs mem md p n pl fpos sp1 E0 T].
unfold rt_base in HB. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_fpos c_sp1 c_E0 c_T] in HB, HJ, Hkk, HG, Hsp |- *.
unfold pm_s in HG |- *. cbn [c_pl] in HG |- *.
destruct HB as (HPRE & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROD & _).
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (proj1 HJ) as HAR3.
destruct (pin_k_le pl) as [Hk_nil Hk_le].
assert (Hn26 : 0 <= n < 2 ^ 26) by (clear - Hpn; destruct Hpn as [[-> _] | [? _]]; lia).
assert (Hkk0 : 0 <= kk < 2 ^ 26) by (rewrite Hkk; destruct Hk_le as [Hle | Hpl0]; [clear - Hle Hnpl Hn26; lia | rewrite (Hk_nil Hpl0); cbn; lia]).
assert (Hrq1 : req_size (kk + 1) = kk + 1) by (unfold req_size; destruct (Z.eqb_spec (kk + 1) 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q (kk + 1) HAR3 Hq3) as (Hq16 & Hq4096 & Hqceil & Hqapp & Hqpres & _ & _).
rewrite Hrq1 in Hqceil, Hqapp, Hqpres.
assert (Hlen : length (pin_zbytes (pin_str pl)) = pin_k pl) by (unfold pin_zbytes; rewrite length_map; apply pin_str_length).
assert (HlenA : Z.of_nat (length (pin_zbytes (pin_str pl) ++ [0])) = kk + 1)
by (rewrite length_app, Hlen; cbn [length]; lia).
split; [clear - Hq4096; lia|]. split; [lia|]. split; [lia|]. split; [clear - Hqceil C1; lia|].
split.
{ split; [lia|]. split.
  - intros i Hi.
    destruct (garr8_nthZ tfibsegs _ q _ i HG ltac:(lia) ltac:(lia)) as [Hv Hr].
    exists (nth (Z.to_nat i) (pin_zbytes (pin_str pl) ++ [0]) 0).
    split; [apply aview_of_val_mem1; [exact Hv | exact Hr]|].
    rewrite app_nth1 by lia. apply pin_str_byte_nz. lia.
  - intros _.
    destruct (garr8_nthZ tfibsegs _ q _ kk HG ltac:(lia) ltac:(lia)) as [Hv Hr].
    rewrite app_nth2 in Hv by lia.
    replace (Z.to_nat kk - length (pin_zbytes (pin_str pl)))%nat with 0%nat in Hv by lia.
    cbn [nth] in Hv. apply aview_of_val_mem1; [exact Hv | lia]. }
split.
{ intros a Ha. split.
  - apply (aview_some_of_apresent tfibsegs). apply (proj1 (Hqpres a ltac:(lia))).
  - rewrite Hsp, Hes. clear - Ha Hqceil Hceil Hslo Ho FFS C1; unfold LLVMF_STK in *; lia. }
split; [intros a Ha; rewrite Hes; clear - Ha Hqceil Hceil Hslo Ho FFS C1; unfold LLVMF_STK in *; lia|].
split; [apply (amem_range_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 q (kk + 1)); [exact HAR3 | exact Hq3 | lia | rewrite Hrq1; lia]|].
split; [apply (range_addressable_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 q (kk + 1)); [exact HAR3 | exact Hq3 | lia | rewrite Hrq1; lia]|].
split; [apply (shadow_hull_vis_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 q (kk + 1)); [exact HAR3 | exact Hq3 | lia | rewrite Hrq1; lia | lia]|].
split.
{ intros a Ha. apply (blk_tail_present tfibsegs B LAWS ly3 S3 W3 mem3 md3 q (kk + 1) kk a HAR3 Hq3 ltac:(rewrite Hrq1; lia) Ha). }
eapply (aro_unowned_keep tfibsegs B (aview tfibsegs (w_H W) mem)).
- apply (aro_unowned_of_arodataP tfibsegs B PM_RLO PM_RHI). apply pm_arodataP. exact HROD.
- intros a Harom Hown Herr.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  apply F3; [ destruct Harom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]
            | exact Hown | exact Herr | rewrite FP0; apply fp_spares_closed; intros (r0 & [] & _) ].
Qed.
Ltac pin_nowr AG :=
  let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
  intros (rg & Hin & Hrg);
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia | ]);
  destruct Hin.
(* M -> C / D: 0x80844 .. 0x80864 and 0x808b4 / 0x808b8 *)
Lemma pm_S2m : rt_from B MT FP POST ss_C (INV_C B MT) -> rt_from B MT FP POST ss_D (INV_D B MT) -> rt_from B MT FP POST ss_M (INV_M B MT).
Proof.
intros RC RD. rt_prelude.
pose proof HINV as (Hk0 & Hacc & q & kk & fl & E100 & E102 & E103 & Hkk & Hfl & Eab3 & HGs).
unfold pm_s in HGs. cbn [c_pl] in HGs.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
assert (Hq3 : In (q, kk + 1) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; left; reflexivity).
destruct (pin_k_le pl) as [Hk_nil Hk_le].
assert (Hkk0 : 0 <= kk < 2 ^ 26) by (rewrite Hkk; destruct Hk_le as [Hle | Hpl0]; [clear - Hle Hnpl Hn26; lia | rewrite (Hk_nil Hpl0); cbn; lia]).
assert (Hrq1 : req_size (kk + 1) = kk + 1) by (unfold req_size; destruct (Z.eqb_spec (kk + 1) 0); lia).
assert (Hlen : length (pin_zbytes (pin_str pl)) = pin_k pl) by (unfold pin_zbytes; rewrite length_map; apply pin_str_length).
assert (HlenA : Z.of_nat (length (pin_zbytes (pin_str pl) ++ [0])) = kk + 1) by (rewrite length_app, Hlen; cbn [length]; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q (kk + 1) HAR3 Hq3) as (Hq16 & Hq4096 & Hqceil & Hqapp & Hqpres & _ & _).
rewrite Hrq1 in Hqceil, Hqapp, Hqpres.
assert (HdQF : q + (kk + 1) <= F \/ F + 128 <= q).
{ pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 _ _ _ q (kk + 1) 1 fpos HAR3 Hq3 Hfin3) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. change (fs_frame_bytes 1) with 128 in D. rewrite EFA3 in D. fold F in D.
  rewrite Hrq1 in D. exact D. }
assert (HF8u : 8 * (F / 8) <= 140737479966720) by (clear - HF8c HFceil C1; lia).
assert (Hq88 : q + (kk + 1) <= SB + F / 8 \/ SB + F / 8 + 16 <= q).
{ destruct Hqapp as (Hq0 & [Hlow | [Hhigh _]]).
  - left. clear - Hlow HF8lo. unfold SB, kLowShadowBeg in *. lia.
  - right. clear - Hhigh HF8u HF8lo. unfold SB, kHighMemBeg in *. lia. }
clear Hqapp.
assert (HqS : q + (kk + 1) <= spZ regs - 32768) by (clear - Hqceil Hceil Hslo FFS; unfold LLVMF_STK in *; lia).
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan 0x80848.
{ awrRT AG fpos F EFA3. }
lazymatch goal with HFx : frame_of ?Ef ?rsX _ (mrestrict _ (ms_mem ?msX)) |- _ =>
assert (HG1 : garr8 tfibsegs (mrestrict (w_H W3) (ms_mem msX)) q (pin_zbytes (pin_str pl)))
by (apply (garr8_of_frame Ef rsX _ _ _ q _ HGs); [ intros a Ha; rewrite Hlen, <- Hkk in Ha;
      split; [clear - Ha Hq4096 Hqceil Hkk0 C1; lia|]; pin_nowr AG | exact HFx ]) end.
clear_frames.
rb HS AG E10 E11 E32 E10n E11n E32n.
clear Hqpres HAR3.
pose proof (proj1 HJ3) as HAR3.
destruct (al_blocks _ _ LAWS _ _ _ _ _ q (kk + 1) HAR3 Hq3) as (_ & _ & _ & _ & Hqpres & _ & _).
rewrite Hrq1 in Hqpres.
pin_reg HS (10%bv : bv 5) 530%nat vq Hvq E530.
lazymatch type of Hvq with _ = U ?Ex _ =>
rewrite (U_add2 Ex 100 102 q kk ltac:(ewpeel; exact E100) ltac:(ewpeel; exact E102)
  ltac:(clear - Hq4096; lia) ltac:(clear - Hkk0; lia) ltac:(clear - Hq4096 Hqceil Hkk0 C1; lia)) in Hvq end.
subst vq.
add_fact HS 530%nat 4096 140737479966720 E530 ltac:(clear - Hq4096 Hqceil Hkk0 C1; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 530%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E530, unsigned_lit_small by (clear - Hq4096 Hqceil Hkk0 C1; lia);
split; [clear - Hq4096 Hkk0; lia|]; split; [clear - Hqceil Hkk0 C1; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (Hqpres (q + kk + o) ltac:(clear - Ho Hkk0 Hq4096; lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E530; evalE AG;
clear - Hq4096 Hqceil Hkk0 HdQF Hq88 HqS HF4096 HFceil HF8lo HF8u Hceil Hslo Hstk0 Hsp1 FFS C1 C3 Hshi H47;
unfold SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
reshok HS.
aj_run_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan.
all: lazymatch goal with
| |- range_addressable _ (U ?Ex _) _ _ =>
  rewrite (U_atom Ex 530 (q + kk) ltac:(ewpeel; exact E530) ltac:(clear - Hq4096 Hqceil Hkk0 C1; lia));
  eapply (obl_of_block tfibsegs B LAWS ly3 S3 W3 _ _ Ex (SOff 32 0) (q + kk) 1 q (kk + 1) HAR3 Hq3);
  [ rewrite (U_atom Ex 32 SB ltac:(ewpeel; exact E32n) ltac:(unfold SB; clear; lia)); exact SB_SHADOW_OFF
  | clear - Hkk0; lia | rewrite Hrq1; clear; lia ]
| |- awr_ok _ _ _ _ _ _ _ _ _ =>
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 530%nat (q + kk));
  [ reflexivity
  | ewpeel; rewrite E530; apply unsigned_lit_small; clear - Hq4096 Hqceil Hkk0 C1; lia
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with (q + kk) by (clear - Ha; lia);
    apply (awr_new_block_any tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q (kk + 1) (ablocks B ly3 S3) kk ly3 [(1, fpos)]
      (ajournal_init tfibsegs B LLVMF_STK FP ly S W regs mem md [] HPRE) HAR3 Eab3 ltac:(clear - Hkk0; lia) Hq3 ltac:(rewrite Hrq1; clear - Hkk0; lia))
  | awrRT AG fpos F EFA3 ]
| |- _ => idtac
end.
(* the string and its NUL are in the block, at the memory the call sees *)
lazymatch goal with HFx : frame_of ?Ef ?rsX _ (mrestrict _ (ms_mem ?msX)) |- _ =>
assert (HG2 : garr8 tfibsegs (mrestrict (w_H W3) (ms_mem msX)) q (pin_zbytes (pin_str pl)))
by (apply (garr8_of_frame Ef rsX _ _ _ q _ HG1); [ intros a Ha; rewrite Hlen, <- Hkk in Ha;
      split; [clear - Ha Hq4096 Hqceil Hkk0 C1; lia|]; pin_nowr AG | exact HFx ]) end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 530%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HR530;
cbn [ms_mem restrict] in HR530;
assert (Hz : aview tfibsegs (w_H W3) (ms_mem msX) (q + kk) = Some 0);
[ replace (q + kk) with (q + kk + 0) by (clear; lia);
  apply (zs_chunk1 Ex (w_H W3) (ms_mem msX) r (q + kk) 0 HR530
    ltac:(cbn [YP09.r_base base_val]; ewpeel; rewrite E530; apply unsigned_lit_small; clear - Hq4096 Hqceil Hkk0 C1; lia)
    ltac:(cbn [YP09.r_chunks]; left; reflexivity) ltac:(clear - Hq4096 Hkk0; lia) ltac:(clear - Hqceil Hkk0 C1; lia))
| clear HR530 ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HG3 : garr8 tfibsegs (mrestrict (w_H W3) (ms_mem msX)) q (pin_zbytes (pin_str pl) ++ [0]))
by (apply (garr8_app1 tfibsegs _ _ q _ 0 HG2); [ rewrite Hlen; replace (q + Z.of_nat (pin_k pl)) with (q + kk) by lia;
    apply val_mem1_of_aview; exact Hz | clear; lia | intros a Ha; reflexivity ]) end.
clear HG1 HG2 Hz.
clear_frames.
rreg HS (1%bv : bv 5) Yra. rreg HS (2%bv : bv 5) Ysp. rreg HS (3%bv : bv 5) Ygp. rreg HS (4%bv : bv 5) Ytp.
rreg HS (10%bv : bv 5) Ya0.
lazymatch type of Ysp with getr ?rg 2 = _ =>
assert (EspY : spZ rg = sp1) by (unfold spZ; rewrite Ysp; ewpeel; rewrite E70; apply unsigned_lit_small;
  clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia) end.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msX) _) ?mdX) _ =>
pose proof (pin_strlen_site_main (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX) q kk (sp1 - spZ regs)
  HBASE0 HJ3 Hq3 Hkk HG3 ltac:(cbn [c_regs]; rewrite EspY; clear; lia) ltac:(clear - Hsp1; lia)) as SITE end.
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_fpos] in SITE.
destruct SITE as (Sq0 & Sk0 & Sk32 & Sqk & Sfb & Ssrc & Soff & Samr & Srad & Shull & Stail & Sro).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msX) _) ?mdX) _ =>
  eapply (aj_strlen_atS 0x41908 ASTRLEN W3 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly3 S3 mdX k q kk (sp1 - spZ regs) _ HJ3) end.
  - rewrite Ya0. ewpeel. rewrite E100. reflexivity.
  - exact Sq0. - exact Sk0. - exact Sk32. - exact Sqk.
  - rewrite EspY. clear; lia.
  - rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
  - clear - Hsp1; lia.
  - rewrite FFS, Hes. clear - Hsp1; lia.
  - rewrite Ygp. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Ytp. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact Yra.
  - first [vm_compute; reflexivity | apply ret_ok_even; vm_compute; reflexivity].
  - exact Sfb. - exact Ssrc. - exact Soff. - exact Samr. - exact Srad. - exact Shull. - exact Stail. - exact Sro. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Hres5 & Hfr5 & Hpres5 & Hsame5).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr5 by (clear; lia).
assert (HG4 : garr8 tfibsegs (mrestrict (w_H W3) mem5) q (pin_zbytes (pin_str pl) ++ [0])).
{ apply (garr8_frame tfibsegs _ _ q _ HG3). intros a Ha. rewrite HlenA in Ha.
  apply (mbyte_of_aview tfibsegs). apply Hfr5;
  clear - Ha Hq4096 Hqceil Hkk0 Hceil Hslo Hstk0 Hsp1 FFS C1 Hshi H47; unfold ESTACK, LLVMF_STK in *; lia. }
reseatL HS HJ5 HP5 [1; 2; 3]%nat AG
ltac:(idtac; eapply region_kept_aview;
  [ evalE AG
  | intros a Ha; apply Hfr5;
    clear - Ha HF4096 HFceil HF8lo HF8u Hceil Hslo Hstk0 Hsp1 FFS C1 C3 Hshi H47 Usp;
    unfold ESTACK, LLVMF_STK, SB in *; lia
  | exact Hpres5 ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pin_rege Ev ssx msx (10%bv : bv 5) (SOff 102 0) HS ltac:(intros X; discriminate X)
  ltac:(rewrite sv_denot_SOff0; ewpeel; rewrite E102; cbn [ms_regs restrict mkst]; rewrite Hres5; unfold w64; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
reshok HS.
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tfibtbl_lib_ok HS SH RTBspan end.
all: lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc2 end.
all: hc_bool Hc2 ltac:(fun H => hc_atom H 102%nat kk E102 ltac:(clear - Hkk0; lia)).
all: hc_prop Hc2.
- (* len = 0: 0x808b4 s4 = 0, 0x808b8 s5 = 0, join at 0x808bc = ss_D *)
  norm_ss HS. reshok HS.
  aj_run_to_tok tfibtbl_lib_ok HS HJ5 SHOK RTBspan 0x808bc.
  { awrRT AG fpos F EFA3. }
  lazymatch goal with HFx : frame_of ?Ef ?rsX _ (mrestrict _ (ms_mem ?msX)) |- _ =>
  assert (HG5 : garr8 tfibsegs (mrestrict (w_H W3) (ms_mem msX)) q (pin_zbytes (pin_str pl) ++ [0]))
  by (apply (garr8_of_frame Ef rsX _ _ _ q _ HG4); [ intros a Ha; rewrite HlenA in Ha;
        split; [clear - Ha Hq4096 Hqceil Hkk0 C1; lia|]; pin_nowr AG | exact HFx ]) end.
  clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  pin_reg HS (20%bv : bv 5) 104%nat w4 Hw4 E104.
  pin_reg HS (21%bv : bv 5) 105%nat w5 Hw5 E105.
  rewrite U_lit0 in Hw4. rewrite U_lit0 in Hw5. subst w4. subst w5.
  ra_join_win HS ss_D 700%nat pm_D_deads_bv ltac:(idtac).
  let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv.
  rt_hand RD HS.
  assert (Hpk0 : pin_str pl = []) by (unfold pin_str; replace (pin_k pl) with 0%nat by lia; reflexivity).
  assert (HW : harness_want fl (pin_str pl) = None)
  by (rewrite Hpk0; unfold harness_want; cbn [length Nat.eqb negb]; rewrite Bool.andb_false_r; reflexivity).
  split; [exact Hk0|]. split; [exact Hacc|].
  exists q, fl, 0, 0.
  split; [exact E100|]. split; [exact E103|]. split; [exact E104|]. split; [exact E105|].
  split; [exact Hfl|].
  split; [rewrite Eab3, <- Hkk; apply Permutation_refl|].
  split; [exact HG5|].
  unfold pm_want, pm_wlab, pm_s. cbn [c_pl]. rewrite HW. split; reflexivity.
- (* len <> 0: 0x80864 not taken, the state at 0x80868 is ss_C *)
  norm_ss HS. reshok HS.
  aj_run_to_tok tfibtbl_lib_ok HS HJ5 SHOK RTBspan 0x80868.
  { awrRT AG fpos F EFA3. }
  lazymatch goal with HFx : frame_of ?Ef ?rsX _ (mrestrict _ (ms_mem ?msX)) |- _ =>
  assert (HG5 : garr8 tfibsegs (mrestrict (w_H W3) (ms_mem msX)) q (pin_zbytes (pin_str pl) ++ [0]))
  by (apply (garr8_of_frame Ef rsX _ _ _ q _ HG4); [ intros a Ha; rewrite HlenA in Ha;
        split; [clear - Ha Hq4096 Hqceil Hkk0 C1; lia|]; pin_nowr AG | exact HFx ]) end.
  clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  lazymatch type of HS with st_ok _ ?Ev _ _ => assert (E102c : ew Ev 102 = Z_to_bv 64 kk) by (ewpeel; exact E102) end.
  add_fact HS 102%nat 1 (2 ^ 26 - 1) E102c ltac:(clear - Hc2 Hkk0; lia).
  ra_join_win HS ss_C 600%nat pm_C_deads_bv ltac:(idtac).
  let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv.
  rt_hand RC HS.
  split; [exact Hk0|]. split; [exact Hacc|].
  exists q, kk, fl.
  split; [exact E100|]. split; [exact E102|]. split; [exact E103|].
  split; [exact Hkk|]. split; [clear - Hc2 Hkk0; lia|]. split; [exact Hfl|].
  split; [exact Eab3 | exact HG5].
Qed.
(* S2: ss_Q (0x8082c) -> ss_C (0x80868) or ss_D (0x808bc) *)
Lemma pm_S2 : rt_from B MT FP POST ss_C (INV_C B MT) -> rt_from B MT FP POST ss_D (INV_D B MT) -> rt_from B MT FP POST ss_Q (INV_Q B MT).
Proof. intros RC RD. exact (pm_S2q (pm_S2m RC RD)). Qed.
End d.
End b.
