(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b for
   reac-pw/fuzz_headamp image A: its start-fact record hd_c3 / hd_c3_of, its bounds lemma hd_bounds and its walk hd_A
   (a nonzero test of a block, a register move, a zero test of the length, the __asan_memcpy, its return) restated for
   headamp's segment M04a (C7 0x83744 -> C8 0x83764) as h4a_c7 / h4a_c7_of / h4a_bounds / h4a_copy over HPgSeg.hs_scx,
   with headamp's registers and real-frame cells; its helpers hd_getr_z, hd_reg_atom, hd_aview_some and hd_frame_ro
   taken renamed (h4a_); role's own memcpy step replaced by the shared lib/A/HPgIntrin.v hd_memcpy_at; the arm with
   no copy (h4a_zero), the extra-atom register lemma h4a_reg_at and the post construction h4a_close are new; role's
   parse step, .rodata zone and string lemmas are not taken (M04a calls no parse). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04a.v, with its module paths and module names changed; 579 of its 631 lines of code are new or changed and 417 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, the same loaded bytes except .note.gnu.build-id): the piece "the cell
   write" of the walk of LLVMFuzzerTestOneInput, lib/A/HPgSegM.v hq_piece_M3e_cell_stmt. Proves no function (kind:
   segment lemma).

   THE CODE (CELL 0x83548 .. 0x835e4, fuzz_headamp.c:149-153, with R = s1, x = F + 0x1a0 the frame object)
     0x83548 .. 0x83550  a0 := [R+0x108] (x); a0 := lw [x+0x7c] (x->n, no check); bge a0,s6 (s6 = cap) -> RC 0x83694
     0x83554 .. 0x83564  a0 := [R+0xb8] (x + 4) + 12 n
     0x83568 .. 0x83574  the instrumented check of a0 (shadow byte of a0 >> 3 + s7; bnez to the slow block 0x83634)
     0x83578 .. 0x8357c  sw [R+0xa0] (the channel) at x + 4 + 12 n
     0x83580 .. 0x835b4  a1 := lw [x+0x7c] again; a2 := x + 4 + 12 n; the check of a2 + 4; sw [R+0x98] (the param)
                         at a2 + 4
     0x835b8 .. 0x835cc  the check of a2 + 8; sw s4 (the value) at a2 + 8
     0x835d0 .. 0x835d8  a1 := n + 1; sw a1 at x + 0x7c (x->n := n + 1, no check)
     0x835dc .. 0x835e4  t2 := [R+0xe0] (n_ent); t6 := [R+0xd8] (&ent[0]); j LATCH 0x83474
   x is in scope (the frame's shadow pattern is hq_shX, so x's 17 shadow granules are 0): each check reads 0 and
   falls through; the slow blocks are never reached.

   HOW. hc_blk is the piece as a block lemma over the machine state at CELL (lib/Reusable: the token engine YCbn.v,
   the journal YCbq.v), for any float state. Its entry state has the registers as atoms and five more atoms: x (32),
   the channel (33), the param (34), n_ent (35) and &ent[0] (36). The six real-frame cells R+0x98 .. R+0x108 are one
   read-only region based at s1 (atom 9); x's bytes [4 + 12 n, 0x80) are one region based at atom 32 whose window is
   all of it, with two chunks: the zero cells (CZero) and x->n (the literal n). n is split into its ten values, so
   every address the code forms is atom 32 plus a literal. The shadow base is s7 (atom 23, the fact SHADOW_OFF), and
   the shadow entry [x, x + 136) (YCbq.shent_ok_of_range from HPgMem.hm_A_ra_x) decides each check. The engine
   splits the `bge` and runs each arm to its end pc. The post is HPgSteps.hd_blk_postE's: at RC no byte changed
   (the window's two chunks are still there); at LATCH only the 12 cell bytes and x->n changed, to the channel, the
   param, the value and n + 1, and t2, t6 hold n_ent and &ent[0]. he_cell reads the CELL cut, runs hc_blk at the
   run's own float state and rebuilds the end cut of the arm: RC (cap <= n: the fold stops on this cell, so x holds
   expect_of's answer) or LATCH at S (S m) (the fold appends the cell; x holds hq_x_open of the longer list). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps HPgMem HPgCalls HPgM3eBase HPgM3bBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* ================================ x's bytes and the fold ================================ *)
(* x before the write, n = |cs| <= 9: the cells, the next (zero) cell, the zero cells after it, x->n, keys, refusal *)
Lemma hc_open_old : forall (cs : list cell) K rf, (length cs <= 9)%nat ->
hq_x_open cs K rf =
(repeat (Z_to_bv 8 0) 4 ++ x_cells_bytes cs) ++
(repeat (Z_to_bv 8 0) 12 ++ repeat (Z_to_bv 8 0) (12 * (9 - length cs))) ++
(Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 (Z.of_nat (length cs)))) ++
 (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 K)) ++ Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 rf)))).
Proof.
intros cs K rf Hl. unfold hq_x_open, ha_res_bytes, X_CELLS.
rewrite <- repeat_app. replace (12 * (10 - length cs))%nat with (12 + 12 * (9 - length cs))%nat by lia.
rewrite <- !app_assoc. reflexivity.
Qed.

(* x after it: the cell c in place of the next zero cell, and x->n one more *)
Lemma hc_open_new : forall (cs : list cell) c K rf, (length cs <= 9)%nat ->
hq_x_open (cs ++ [c]) K rf =
(repeat (Z_to_bv 8 0) 4 ++ x_cells_bytes cs) ++
(x_cell_bytes c ++ repeat (Z_to_bv 8 0) (12 * (9 - length cs))) ++
(Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 (Z.of_nat (length cs) + 1))) ++
 (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 K)) ++ Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 rf)))).
Proof.
intros cs c K rf Hl. unfold hq_x_open, ha_res_bytes, X_CELLS.
rewrite length_app. cbn [length].
replace (12 * (10 - (length cs + 1)))%nat with (12 * (9 - length cs))%nat by lia.
rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
unfold x_cells_bytes. rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r.
rewrite <- !app_assoc. reflexivity.
Qed.

Lemma hc_lenA : forall (cs : list cell),
length (repeat (Z_to_bv 8 0) 4 ++ x_cells_bytes cs) = (4 + 12 * length cs)%nat.
Proof. intros cs. rewrite length_app, repeat_length, length_x_cells_bytes. reflexivity. Qed.

Lemma hc_len_cell : forall c, length (x_cell_bytes c) = 12%nat.
Proof. intros [[ch p] v]. reflexivity. Qed.

(* one pair whose key has the prefix and whose value gives a cell (Pod/Headamp.v ha_fold) *)
Lemma hc_fold_cell : forall cap k v rest cs keys rf c, ha_prefix k = true -> expect_cell k v = inr c ->
ha_fold expect_cell cap ((k, v) :: rest) cs keys rf =
if cap <=? Z.of_nat (length cs) then (cs, keys + 1, rf) else ha_fold expect_cell cap rest (cs ++ [c]) (keys + 1) rf.
Proof. intros cap k v rest cs keys rf c Hp He. cbn [ha_fold]. rewrite Hp, He. reflexivity. Qed.

Lemma hc_shX : hq_shX = HPgMem.hm_sh false false false false true true.
Proof. vm_compute. reflexivity. Qed.

(* ================================ bytes at an address ================================ *)
Section bytes. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a list of five parts where the second and the fourth were rewritten and the others kept *)
Lemma hc_bytes_5 : forall H mem H' mem' a (A Bo Bn C Do Dn E : list byte),
HPgMem.hm_bytes rsegs H mem a (A ++ (Bo ++ C) ++ (Do ++ E)) ->
length Bn = length Bo -> length Dn = length Do ->
HPgMem.hm_bytes rsegs H' mem' (a + Z.of_nat (length A)) Bn ->
HPgMem.hm_bytes rsegs H' mem' (a + Z.of_nat (length A) + Z.of_nat (length Bo) + Z.of_nat (length C)) Dn ->
(forall y, (a <= y < a + Z.of_nat (length A)) \/
  (a + Z.of_nat (length A) + Z.of_nat (length Bo) <= y <
   a + Z.of_nat (length A) + Z.of_nat (length Bo) + Z.of_nat (length C)) \/
  (a + Z.of_nat (length A) + Z.of_nat (length Bo) + Z.of_nat (length C) + Z.of_nat (length Do) <= y <
   a + Z.of_nat (length A) + Z.of_nat (length Bo) + Z.of_nat (length C) + Z.of_nat (length Do) +
   Z.of_nat (length E)) ->
  aview rsegs H' mem' y = aview rsegs H mem y) ->
HPgMem.hm_bytes rsegs H' mem' a (A ++ (Bn ++ C) ++ (Dn ++ E)).
Proof.
intros H mem H' mem' a A Bo Bn C Do Dn E HB LB LD HBn HDn K.
apply HPgMem.hm_bytes_app in HB as [HA HB]. apply HPgMem.hm_bytes_app in HB as [HBC HDE].
apply HPgMem.hm_bytes_app in HBC as [_ HC]. apply HPgMem.hm_bytes_app in HDE as [_ HE].
rewrite length_app, Nat2Z.inj_add in HE.
apply HPgMem.hm_bytes_app. split.
{ apply (HPgMem.hm_bytes_kept rsegs H mem); [exact HA|]. intros y Hy. apply K. left. exact Hy. }
apply HPgMem.hm_bytes_app. split.
{ apply HPgMem.hm_bytes_app. split; [exact HBn|]. rewrite LB.
  apply (HPgMem.hm_bytes_kept rsegs H mem); [exact HC|]. intros y Hy. apply K. right. left. lia. }
rewrite length_app, Nat2Z.inj_add, LB.
apply HPgMem.hm_bytes_app. split.
{ replace (a + Z.of_nat (length A) + (Z.of_nat (length Bo) + Z.of_nat (length C)))
    with (a + Z.of_nat (length A) + Z.of_nat (length Bo) + Z.of_nat (length C)) by lia. exact HDn. }
rewrite LD.
replace (a + Z.of_nat (length A) + (Z.of_nat (length Bo) + Z.of_nat (length C)) + Z.of_nat (length Do))
  with (a + Z.of_nat (length A) + (Z.of_nat (length Bo) + Z.of_nat (length C)) + Z.of_nat (length Do)) by reflexivity.
apply (HPgMem.hm_bytes_kept rsegs H mem); [exact HE|]. intros y Hy. apply K. right. right. lia.
Qed.

(* a cell's 12 bytes from its three 4-byte stores *)
Lemma hc_cell_bytes : forall H mem b ch p v,
val_mem rsegs (mrestrict H mem) b 4 ch -> val_mem rsegs (mrestrict H mem) (b + 4) 4 p ->
val_mem rsegs (mrestrict H mem) (b + 8) 4 v ->
0 <= ch < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
HPgMem.hm_bytes rsegs H mem b (x_cell_bytes (ch, p, v)).
Proof.
intros H mem b ch p v V1 V2 V3 R1 R2 R3.
change (x_cell_bytes (ch, p, v)) with (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 ch)) ++
  Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 p)) ++ Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 v))).
rewrite !unsigned_lit_small by lia.
apply HPgMem.hm_bytes_app. split; [apply HPgMem.hm_bytes_of_val; exact V1|].
rewrite length_Z_to_le_bytes. apply HPgMem.hm_bytes_app. split.
- apply HPgMem.hm_bytes_of_val. exact V2.
- rewrite length_Z_to_le_bytes. replace (b + Z.of_nat 4 + Z.of_nat 4) with (b + 8) by lia.
  apply HPgMem.hm_bytes_of_val. exact V3.
Qed.
End bytes.

(* ================================ the cut lists ================================ *)
Section lists. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma hc_at_get : forall H mem regs e L r v, hs_at rsegs H mem regs e L -> In (LReg r, v) L ->
getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HL Hin. unfold hs_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.
Lemma hc_at_cell : forall H mem regs e L b o v, hs_at rsegs H mem regs e L -> In (LCell b o, v) L ->
val_mem rsegs (mrestrict H mem) (hd_xv e b + o) 8 (v mod 2 ^ 64).
Proof. intros H mem regs e L b o v HL Hin. unfold hs_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.
Lemma hc_at_sub : forall H mem regs e L L', hs_at rsegs H mem regs e L -> (forall y, In y L' -> In y L) ->
hs_at rsegs H mem regs e L'.
Proof.
intros H mem regs e L L' HL Hs. unfold hs_at in *. rewrite Forall_forall in *. intros y Hy. exact (HL y (Hs y Hy)).
Qed.
Lemma hc_notin : forall (r : bv 5) (l : list (bv 5)), existsb (fun c => bv_eqb c r) l = false -> ~ In r l.
Proof.
intros r l Hb Hin.
assert (Ht : existsb (fun c => bv_eqb c r) l = true) by (apply existsb_exists; exists r; split; [exact Hin | apply bv_eqb_refl]).
congruence.
Qed.
(* a list of facts over registers outside clob and real-frame cells [R, R + 0x120), after a run that kept both *)
Definition hc_locb (clob : list (bv 5)) (f : hd_loc * Z) : bool :=
match fst f with
| LReg r => negb (bv_unsigned (Z_to_bv 5 r) =? 0) && negb (existsb (fun c => bv_eqb c (Z_to_bv 5 r)) clob)
| LCell XR o => (0 <=? o) && (o <=? 0x118)
| LCell _ _ => false
end.
Lemma hc_at_move : forall H mem H' mem' regs regs' e L (clob : list (bv 5)) (Wr : Z -> Prop),
hs_at rsegs H mem regs e L ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs H' mem' a = aview rsegs H mem a) ->
forallb (hc_locb clob) L = true ->
(forall a, hd_xv e XR <= a < hd_xv e XR + 0x120 -> 0 <= a < 2 ^ 64 /\ ~ Wr a) ->
hs_at rsegs H' mem' regs' e L.
Proof.
intros H mem H' mem' regs regs' e L clob Wr HL Hk Hm Hb Hc. unfold hs_at in *. rewrite Forall_forall in HL |- *.
intros [l w] Hin. pose proof (HL _ Hin) as Hv. pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Hf.
unfold hc_locb in Hf. cbn [fst snd] in Hv, Hf |- *. destruct l as [rr|b o].
- cbn [hd_at] in Hv |- *. apply andb_prop in Hf as [H1 H2]. rewrite Hk; [exact Hv| |].
  + apply negb_true_iff, Z.eqb_neq in H1. exact H1.
  + apply hc_notin. apply negb_true_iff in H2. exact H2.
- destruct b; try discriminate Hf. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1, H2.
  cbn [hd_at] in Hv |- *. intros kk Hkk.
  destruct (Hc (hd_xv e XR + o + Z.of_nat kk) ltac:(lia)) as [Ha1 Ha2].
  rewrite (mbyte_of_aview rsegs H H' mem mem') by exact (Hm _ Ha1 Ha2). exact (Hv kk Hkk).
Qed.
End lists.

Ltac hc_unf := unfold hq_L_seg, hq_L_frame, hq_L_loopc, hq_L_body.
Ltac hc_in := hc_unf; cbv zeta; cbn [In app]; repeat (first [left; reflexivity | right]).
Ltac hc_sub HL :=
apply (hc_at_sub _ _ _ _ _ _ HL);
let y := fresh "y" in let Hy := fresh "Hy" in
intros y Hy; hc_unf; cbv zeta in Hy |- *; cbn [In app] in Hy |- *;
repeat (destruct Hy as [<-|Hy]; [repeat (first [left; reflexivity | right]) |]); destruct Hy.

(* ================================ the engine's state ================================ *)
(* the 40 words 0x83548 .. 0x835e4; RC 0x83694 and LATCH 0x83474 lie outside them, and so do the slow blocks *)
Definition hc_tbl : ctable := build_table rsegs HQ_CELL 40 TEmpty.
Lemma hc_tbl_ok : table_ok rsegs hc_tbl.
Proof. apply build_table_ok0. unfold HQ_CELL. lia. Qed.

(* the real-frame cells: the param, the channel, &x.cell[0], &ent[0], n_ent, x *)
Definition hc_RR : YP09.region := YP09.mkRegion (Some 9%nat) 0x98 0x110 0 0
  [YP09.mkChunk 0x98 (CVal 8 (SOff 34 0)); YP09.mkChunk 0xa0 (CVal 8 (SOff 33 0));
   YP09.mkChunk 0xb8 (CVal 8 (SOff 32 4)); YP09.mkChunk 0xd8 (CVal 8 (SOff 36 0));
   YP09.mkChunk 0xe0 (CVal 8 (SOff 35 0)); YP09.mkChunk 0x108 (CVal 8 (SOff 32 0))].
(* x's bytes from cell n on: the zero cells, then x->n = n *)
Definition hc_RX (n : Z) : YP09.region := YP09.mkRegion (Some 32%nat) (4 + 12 * n) 0x80 (4 + 12 * n) 0x80
  [YP09.mkChunk (4 + 12 * n) (CZero (120 - 12 * n)); YP09.mkChunk 0x7c (CVal 4 (SLit n))].
Definition hc_facts : facts :=
  mkFacts [(23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 4096 0x7fffff800000 0)] [] [].
Definition hc_ss0 (n : Z) : sstate := mkSS HQ_CELL sr_atoms [hc_RR; hc_RX n] None hc_facts.
Definition hc_SH : list shent := [mkSHE 32 0 136].
Definition hc_Bx : sv := SOff 23 0.
Definition hc_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition hc_extra (x ch p nent t6 : Z) : list word := [w64 x; w64 ch; w64 p; w64 nent; w64 t6].

Lemma hc_wf : forall n, 0 <= n <= 9 -> regions_wf [hc_RR; hc_RX n] = true.
Proof.
intros n Hn.
assert (H : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9) by lia.
destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; vm_compute; reflexivity.
Qed.

(* the bytes the arm to LATCH writes, and what it leaves *)
Definition hc_Wr (x n : Z) (a : Z) : Prop := (x + 4 + 12 * n <= a < x + 16 + 12 * n) \/ (x + 0x7c <= a < x + 0x80).

Section ar. Context {fx : YK11.FPState}.
Lemma hc_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma hc_bge : forall E (a : Z) (n : nat) b, ew E n = Z_to_bv 64 b -> 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E (SLit a)) (sv_denot E (SOff n 0)) = negb (a <? b).
Proof.
intros E a n b Hn Ha Hb. rewrite hc_denot0, Hn. cbn [sv_denot].
rewrite YO0c.branch_ge, !unsigned_lit_small by lia. rewrite !YO0b.s64_small by lia. reflexivity.
Qed.
(* a region's chunk read back *)
Lemma hc_czero : forall E m b off l a, YP09.chunk_ok rsegs E m b (YP09.mkChunk off (CZero l)) ->
b + off <= a < b + off + l -> YP09.mbyte rsegs m a = Some (Z_to_bv 8 0).
Proof.
intros E m b off l a Hc Ha. destruct (Hc (a - (b + off)) ltac:(cbn; lia)) as (bb & Hcb & Hmb).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hcb, Hmb. injection Hcb as <-.
replace a with (b + off + (a - (b + off))) by lia. exact Hmb.
Qed.
Lemma hc_cval4 : forall E m b off e v a, YP09.chunk_ok rsegs E m b (YP09.mkChunk off (CVal 4 e)) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> a = b + off -> val_mem rsegs m a 4 v.
Proof.
intros E m b off e v a Hc He Hv ->. intros k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (bb & Hcb & Hmb).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hcb, Hmb. injection Hcb as <-. rewrite Hmb. f_equal.
rewrite He. unfold YP09.byte_of_word. rewrite unsigned_lit_small by lia.
symmetry. apply HPgMem.hm_le_byte_bv. exact Hk.
Qed.
(* the bytes outside a run's write windows *)
Lemma hc_frame_keep : forall E rs (H : word -> bool) (m m' : word -> option byte) (P : Z -> Prop),
YP09.frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, YP09.in_wrange E rs a -> P a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' P HF HP a Ha Hn. unfold aview, YP09.mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros Hw. exact (Hn (HP a Hw)).
Qed.
End ar.

(* ================================ the run tactics ================================ *)
Ltac hc_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply HPgSteps.same_io_wvb]; kio] in kio.
Ltac hc_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.
(* the write-window obligation: the real-frame cells are read-only, x's window lies in the frame for locals *)
Ltac hc_awr Hawr E32u :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
apply awr_ok_cons_ro; [cbn; lia|];
eapply awr_ok_cons_gen; [reflexivity | exact E32u | | apply awr_ok_nil];
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply Hawr; lia.
(* the run's write windows: x's region only *)
Ltac hc_inw E32u :=
let a := fresh "a" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (rg & Hin & Hr); cbn [In ss_mem hc_ss0] in Hin; destruct Hin as [<-|[<-|[]]];
cbn [hc_RR hc_RX YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr; [lia | rewrite E32u in Hr; lia].
(* the chunk at offset off of a region's chunk list *)
Ltac hc_get_chunk Hch off name :=
lazymatch type of Hch with Forall _ ?cs =>
  let r := eval vm_compute in (List.find (fun c => Z.eqb (YP09.c_off c) off) cs) in
  lazymatch r with Some ?c =>
    pose proof (proj1 (Forall_forall _ _) Hch c ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as name
  end end.
(* x's region (index 1) at the end of the run, with its base x *)
Ltac hc_rx Hch E32u :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ _) |- _ =>
  let HRX := fresh "HRX" in
  pose proof (HPgSteps.st_ok_region_at _ _ _ 1%nat _ HS ltac:(vm_compute; reflexivity)) as HRX;
  destruct HRX as (_ & _ & _ & Hch);
  cbn [YP09.r_base YP09.r_chunks YP09.base_val] in Hch; rewrite E32u in Hch end.
(* what the arm to LATCH leaves: the cell, x->n + 1, t2 and t6 *)
Section rl. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition hc_RL (x n ch p val nent t6 : Z) (W2 : world rsegs) (regs2 : bvmap 5 word)
(mem2 : word -> option byte) : Prop :=
val_mem rsegs (mrestrict (w_H W2) mem2) (x + 4 + 12 * n) 4 ch /\
val_mem rsegs (mrestrict (w_H W2) mem2) (x + 8 + 12 * n) 4 p /\
val_mem rsegs (mrestrict (w_H W2) mem2) (x + 12 + 12 * n) 4 val /\
val_mem rsegs (mrestrict (w_H W2) mem2) (x + 0x7c) 4 (n + 1) /\
getr regs2 (Z_to_bv 5 7) = w64 nent /\ getr regs2 (Z_to_bv 5 31) = w64 t6.
End rl.

(* the clauses of the block's post every arm proves the same way: the config, the journal, the kept registers,
   the frames, the blocks, the I/O state and the meter *)
Ltac hc_post_common lyc Sc W regs ex HAE HJ :=
lazymatch goal with HS : st_ok _ _ ?ssf (restrict _ ?msf) |- _ =>
  red; exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HS eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [eapply (HPgSteps.regs_kept_of_st_ok rsegs _ _ msf regs ex (w_H W) _ HS HAE); vm_compute; reflexivity|];
  split; [reflexivity|]; split; [apply Permutation_refl|]; split; [hc_io|];
  split; [apply mo_le_refl; assumption|]
end.
(* the bytes a run left as they were: every byte outside x's window *)
Ltac hc_keep KM x nn E32u :=
lazymatch goal with HFr : YP09.frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (hc_frame_keep _ _ _ _ _ (fun a => x + (4 + 12 * nn) <= a < x + 128) HFr ltac:(hc_inw E32u)) as KM;
  cbv beta in KM end;
repeat match goal with H : YP09.frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* RC: every byte as it was (the window's two chunks are still there) *)
Ltac hc_mem_rc x nn Hch KM1 KM2 HZ Vn :=
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha _;
lazymatch type of Hch with Forall _ ?cs =>
lazymatch cs with context [YP09.mkChunk ?oz (CZero ?lz)] =>
  let Cz := fresh "Cz" in let Cn := fresh "Cn" in let Vf := fresh "Vf" in
  hc_get_chunk Hch oz Cz; hc_get_chunk Hch 124 Cn;
  destruct (Z_lt_le_dec a (x + oz)) as [?|?];
  [ rewrite (KM2 a Ha ltac:(lia)), (KM1 a Ha ltac:(lia)); reflexivity |];
  destruct (Z_lt_le_dec a (x + 128)) as [?|?];
  [| rewrite (KM2 a Ha ltac:(lia)), (KM1 a Ha ltac:(lia)); reflexivity ];
  destruct (Z_lt_le_dec a (x + 124)) as [?|?];
  [ unfold aview; f_equal; etransitivity;
    [ exact (hc_czero _ _ _ _ _ a Cz ltac:(lia))
    | symmetry; replace a with (x + (a - x)) by lia; apply HZ; lia ]
  | pose proof (hc_cval4 _ _ _ _ _ nn (x + 0x7c) Cn eq_refl ltac:(lia) ltac:(lia)) as Vf;
    unfold aview; f_equal; replace a with (x + 0x7c + (a - (x + 0x7c))) by lia;
    exact (val_mem_agree rsegs _ _ (x + 0x7c) 4 nn Vn Vf (a - (x + 0x7c)) ltac:(lia)) ]
end end.
(* LATCH: every byte outside the cell and x->n as it was (the zero cells after it are still a chunk) *)
Ltac hc_mem_latch x nn Hch KM1 KM2 HZ :=
let a := fresh "a" in let Ha := fresh "Ha" in let HW := fresh "HW" in
intros a Ha HW; unfold hc_Wr in HW;
lazymatch type of Hch with Forall _ ?cs =>
lazymatch cs with context [YP09.mkChunk ?oz (CZero ?lz)] =>
  let Cz := fresh "Cz" in
  hc_get_chunk Hch oz Cz;
  destruct (Z_lt_le_dec a (x + (4 + 12 * nn))) as [?|?];
  [ rewrite (KM2 a Ha ltac:(lia)), (KM1 a Ha ltac:(lia)); reflexivity |];
  destruct (Z_lt_le_dec a (x + 128)) as [?|?];
  [| rewrite (KM2 a Ha ltac:(lia)), (KM1 a Ha ltac:(lia)); reflexivity ];
  unfold aview; f_equal; etransitivity;
  [ exact (hc_czero _ _ _ _ _ a Cz ltac:(lia))
  | symmetry; replace a with (x + (a - x)) by lia; apply HZ; lia ]
end end.
(* LATCH: the four stores and t2, t6 *)
Ltac hc_rl Hch W E33 E34 E20 E35 E36 :=
unfold hc_RL;
lazymatch type of Hch with Forall _ ?cs =>
lazymatch cs with context [YP09.mkChunk ?o1 (CVal 4 (SOff 33 0))] =>
lazymatch cs with context [YP09.mkChunk ?o2 (CVal 4 (SOff 34 0))] =>
lazymatch cs with context [YP09.mkChunk ?o3 (CVal 4 (SOff 20 0))] =>
  let C1 := fresh "C1" in let C2 := fresh "C2" in let C3 := fresh "C3" in let C4 := fresh "C4" in
  hc_get_chunk Hch o1 C1; hc_get_chunk Hch o2 C2; hc_get_chunk Hch o3 C3; hc_get_chunk Hch 124 C4;
  split; [eapply hc_cval4; [exact C1 | rewrite hc_denot0; exact E33 | lia | lia]|];
  split; [eapply hc_cval4; [exact C2 | rewrite hc_denot0; exact E34 | lia | lia]|];
  split; [eapply hc_cval4; [exact C3 | rewrite hc_denot0; exact E20 | lia | lia]|];
  split; [eapply hc_cval4; [exact C4 | reflexivity | lia | lia]|];
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msf) |- _ =>
  split;
  [ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ msf _ HS); hc_sv; rewrite hc_denot0; exact E35
  | rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ msf _ HS); hc_sv; rewrite hc_denot0; exact E36 ] end
end end end end.
(* one value of n: the run to the `bge`, its split, and each arm's run and post *)
Ltac hc_arm HS HJ SHOK Hawr E32u E22 E33 E34 E20 E35 E36 HZ Vn lyc Sc W regs ex HAE :=
lazymatch goal with |- context [hc_Wr ?x ?nn] =>
let KM1 := fresh "KM1" in let KM2 := fresh "KM2" in let Hch := fresh "Hch" in
(aj_run_tok hc_tbl_ok HS HJ SHOK hc_span; [hc_awr Hawr E32u | ]);
hc_keep KM1 x nn E32u;
srr_branch_tok hc_tbl_ok HS SHOK hc_span;
lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
rewrite (hc_bge _ _ 22 _ E22) in Hc by lia;
lazymatch type of Hc with
| _ = true =>
  (* taken: n >= cap, to RC 0x83694 *)
  apply negb_true_iff, Z.ltb_ge in Hc;
  (aj_run_to_tok hc_tbl_ok HS HJ SHOK hc_span HQ_RC; [hc_awr Hawr E32u | ]);
  hc_keep KM2 x nn E32u; hc_rx Hch E32u;
  apply SRr_ret; left; split; [lia|];
  hc_post_common lyc Sc W regs ex HAE HJ; split; [|exact I]; hc_mem_rc x nn Hch KM1 KM2 HZ Vn
| _ = false =>
  (* not taken: n < cap, the three stores and x->n, to LATCH 0x83474 (n = 9 is dead: cap <= 9) *)
  apply negb_false_iff, Z.ltb_lt in Hc;
  tryif (exfalso; lia) then idtac else
  ((aj_run_to_tok hc_tbl_ok HS HJ SHOK hc_span HQ_LATCH; [hc_awr Hawr E32u | ]);
   hc_keep KM2 x nn E32u; hc_rx Hch E32u;
   apply SRr_ret; right; split; [lia|];
   hc_post_common lyc Sc W regs ex HAE HJ;
   split; [hc_mem_latch x nn Hch KM1 KM2 HZ | hc_rl Hch W E33 E34 E20 E35 E36])
end end
end.

Section blk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Lemma hc_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R x n cap ch p val nent t6 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 22) = w64 cap ->
getr regs (Z_to_bv 5 23) = w64 SHADOW_OFF -> getr regs (Z_to_bv 5 20) = w64 val ->
0 <= R -> R + 0x110 <= 2 ^ 64 -> 4096 <= x -> x + 136 <= 0x7fffff800000 -> x + 0x80 <= R + 0x98 ->
0 <= n <= 9 -> 0 <= cap <= 9 -> 0 <= ch < 2 ^ 32 -> 0 <= p < 2 ^ 32 -> 0 <= val < 2 ^ 32 ->
0 <= nent < 2 ^ 64 -> 0 <= t6 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x98) 8 p ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa0) 8 ch ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb8) 8 (x + 4) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd8) 8 t6 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 nent ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 x ->
val_mem rsegs (mrestrict (w_H W) memc) (x + 0x7c) 4 n ->
(forall i, 4 + 12 * n <= i < 124 -> YP09.mbyte rsegs (mrestrict (w_H W) memc) (x + i) = Some (Z_to_bv 8 0)) ->
(forall a, x + 4 <= a < x + 0x80 -> apresent (w_H W) memc a) ->
(forall a, x + 4 <= a < x + 0x80 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF x 136 ->
(forall a, x <= a < x + 136 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)) ->
SRr rsegs W (cfg_at rsegs HQ_CELL regs memc mdc)
(fun W2 c2 =>
 (cap <= n /\ HPgSteps.hd_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc HQ_RC
   [10]%bv (fun _ => False) (fun _ _ _ => True) W2 c2) \/
 (n < cap /\ HPgSteps.hd_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc HQ_LATCH
   [7; 10; 11; 12; 13; 31]%bv (hc_Wr x n) (hc_RL x n ch p val nent t6) W2 c2)).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R x n cap ch p val nent t6 HJ
  H9 H22 H23 H20 HR0 HR1 Hx0 Hx1 HxR Hn Hcap Hch Hp Hval Hnent Ht6
  V98 Va0 Vb8 Vd8 Ve0 V108 Vn HZ Hpres Hawr HRA Happ.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hc_extra x ch p nent t6) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E22 : ew (Ereg regs ex) 22 = Z_to_bv 64 cap) by (rewrite (EA 22%nat (Z_to_bv 5 22) eq_refl); exact H22).
assert (E23 : ew (Ereg regs ex) 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EA 23%nat (Z_to_bv 5 23) eq_refl); exact H23).
assert (E20 : ew (Ereg regs ex) 20 = Z_to_bv 64 val) by (rewrite (EA 20%nat (Z_to_bv 5 20) eq_refl); exact H20).
assert (E32 : ew (Ereg regs ex) 32 = Z_to_bv 64 x) by (subst ex; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 ch) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 p) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew (Ereg regs ex) 35 = Z_to_bv 64 nent) by (subst ex; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew (Ereg regs ex) 36 = Z_to_bv 64 t6) by (subst ex; exact (ew_Ereg_extra regs _ 4)).
assert (E9u : bv_unsigned (ew (Ereg regs ex) 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (E23u : bv_unsigned (ew (Ereg regs ex) 23) = SHADOW_OFF)
  by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E32u : bv_unsigned (ew (Ereg regs ex) 32) = x) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs ex) (hc_ss0 n)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HQ_CELL) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hc_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - exact (hc_wf n Hn).
  - constructor; [|constructor; [|constructor]].
    + unfold hc_RR. apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R); [exact E9u | lia | lia |].
      repeat apply Forall_cons; [..|apply Forall_nil].
      * apply (chunk_ok_val rsegs _ _ R 0x98 8 (SOff 34 0) p); [rewrite hc_denot0; exact E34 | cbn; lia | cbn; lia | exact V98].
      * apply (chunk_ok_val rsegs _ _ R 0xa0 8 (SOff 33 0) ch); [rewrite hc_denot0; exact E33 | cbn; lia | cbn; lia | exact Va0].
      * apply (chunk_ok_val rsegs _ _ R 0xb8 8 (SOff 32 4) (x + 4)); [| cbn; lia | cbn; lia | exact Vb8].
        cbn [sv_denot]. rewrite E32u. reflexivity.
      * apply (chunk_ok_val rsegs _ _ R 0xd8 8 (SOff 36 0) t6); [rewrite hc_denot0; exact E36 | cbn; lia | cbn; lia | exact Vd8].
      * apply (chunk_ok_val rsegs _ _ R 0xe0 8 (SOff 35 0) nent); [rewrite hc_denot0; exact E35 | cbn; lia | cbn; lia | exact Ve0].
      * apply (chunk_ok_val rsegs _ _ R 0x108 8 (SOff 32 0) x); [rewrite hc_denot0; exact E32 | cbn; lia | cbn; lia | exact V108].
    + unfold hc_RX. apply (HPgMem.hm_rw_region rsegs _ (w_H W) memc 32 x); [exact E32u | lia | lia | |].
      { intros o Ho. apply Hpres. lia. }
      constructor; [|constructor; [|constructor]].
      * intros i Hi. cbn [YP09.c_len YP09.cv_len YP09.c_val YP09.c_off] in Hi |- *.
        exists (Z_to_bv 8 0). split; [reflexivity|].
        replace (x + (4 + 12 * n) + i) with (x + (4 + 12 * n + i)) by ring. apply HZ. lia.
      * apply (chunk_ok_val rsegs _ _ x 0x7c 4 (SLit n) n); [reflexivity | cbn; lia | cbn; lia | exact Vn].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, hc_RR, hc_RX. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
    rewrite E9u, E32u. lia.
  - split; [|split; exact I]. cbn [hc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E23u, E32u. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia. }
assert (U23 : U (Ereg regs ex) hc_Bx = SHADOW_OFF) by (apply U_atom; [exact E23 | unfold SHADOW_OFF; lia]).
assert (U32 : U (Ereg regs ex) (SOff 32 0) = x) by (apply U_atom; [exact E32 | lia]).
assert (SHOK : sh_ok rsegs hc_Bx hc_SH (Ereg regs ex) (mrestrict (w_H W) memc)).
{ unfold sh_ok, hc_SH. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H W) memc _ hc_Bx 32 x 136 x 0 136 HRA U23 U32); [lia | lia |].
  intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply Happ. lia. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex U23 U32.
unfold cfg_at. change (w64 HQ_CELL) with (Z_to_bv 64 HQ_CELL).
assert (Hn10 : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9) by lia.
destruct Hn10 as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]];
  hc_arm HS HJ SHOK Hawr E32u E22 E33 E34 E20 E35 E36 HZ Vn lyc Sc W regs ex HAE.
Qed.
End blk.

(* ================================ the piece ================================ *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis errno_low : api_env rsegs B.

Theorem he_cell : hq_piece_M3e_cell_stmt rsegs B MT.
Proof.
unfold hq_piece_M3e_cell_stmt. intros cx POST r ev at0 m HS HL HRC.
unfold hq_from_CELL. intros fx2 ly2 S2 W2 regs2 mem2 md2 k v ch p val cs keys rf Hcut.
pose proof Hcut as (Hb3 & Hat & Hf1 & Hf2 & Hlive & Ham & Hec & Hcv & Hpi & Hks & Hx).
pose proof Hb3 as (Hcore & Hfxk & Hfsh & _).
pose proof Hcore as (HJ & _ & Hfr2 & _).
pose proof HS as (HP & _).
pose proof HP as (HJ0 & _).
destruct (HPgM3eBase.he_seg B cx _ HP) as (Hfin & Hown & HeF & HF32 & HF4 & HFc & HFapp & _ & HRlo & HR47 & _ & Hcap & _).
pose proof (HPgM3eBase.he_fsh_rng B cx _ HP) as (Hs1 & Hs2).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
destruct Hcv as (Hch & Hpv & Hvv). unfold HA_CHANNELS, HA_SENS, HA_SENS_MAX in Hch, Hpv, Hvv.
assert (Hvv' : 0 <= val <= 0x37) by (destruct (p =? 2); lia). clear Hvv.
destruct Hx as (Hxb & HxL & HxC & HxK & HxK2 & Hxrf). unfold X_CELLS in HxL. unfold HQ_XO in Hxb.
assert (HL9 : (length cs <= 9)%nat) by lia.
unfold T_SEG_STK, ASTACK in HRlo.
(* the frame for locals at the cut *)
assert (FA : frame_addr ly2 4 (x_pos cx) = e_F (x_e cx)).
{ rewrite (HPgCalls.hc_frame_addr_j rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 (x_pos cx) HJ), HeF.
  symmetry. exact (HPgCalls.hc_frame_addr_j rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 (x_pos cx) HJ0). }
assert (Hfin2 : In (4, x_pos cx) (frames S2)) by (rewrite Hfr2; exact Hfin).
destruct (al_frames _ _ (AR_laws_ok rsegs B) _ _ _ _ _ _ _ (proj1 HJ) Hfin2) as (_ & _ & Hfb & _).
rewrite FA in Hfb. change (fs_frame_bytes 4) with 1024 in Hfb.
(* the values at CELL *)
unfold hs_at_cx in Hat.
pose proof (hc_at_get _ _ _ _ _ 9 _ Hat ltac:(hc_in)) as R9.
pose proof (hc_at_get _ _ _ _ _ 22 _ Hat ltac:(hc_in)) as R22.
pose proof (hc_at_get _ _ _ _ _ 23 _ Hat ltac:(hc_in)) as R23.
pose proof (hc_at_get _ _ _ _ _ 20 _ Hat ltac:(hc_in)) as R20.
pose proof (hc_at_get _ _ _ _ _ 21 _ Hat ltac:(hc_in)) as R21.
pose proof (hc_at_cell _ _ _ _ _ XR 0x98 _ Hat ltac:(hc_in)) as C98.
pose proof (hc_at_cell _ _ _ _ _ XR 0xa0 _ Hat ltac:(hc_in)) as Ca0.
pose proof (hc_at_cell _ _ _ _ _ XR 0xb8 _ Hat ltac:(hc_in)) as Cb8.
pose proof (hc_at_cell _ _ _ _ _ XR 0xd8 _ Hat ltac:(hc_in)) as Cd8.
pose proof (hc_at_cell _ _ _ _ _ XR 0xe0 _ Hat ltac:(hc_in)) as Ce0.
pose proof (hc_at_cell _ _ _ _ _ XR 0x108 _ Hat ltac:(hc_in)) as C108.
cbn [hd_xv] in C98, Ca0, Cb8, Cd8, Ce0, C108. unfold HQ_X_CELL0, HQ_XO in Cb8, C108.
rewrite (Z.mod_small p) in C98 by lia. rewrite (Z.mod_small ch) in Ca0 by lia.
rewrite (Z.mod_small (e_F (x_e cx) + 0x1a0 + 4)) in Cb8 by lia.
rewrite (Z.mod_small (e_F (x_e cx) + 0x1a0)) in C108 by lia.
(* x's bytes at CELL *)
pose proof (proj2 (HPgMem.hm_bytes_zbytes rsegs (w_H W2) mem2 _ _) Hxb) as HB0.
rewrite (hc_open_old cs (keys + 1) rf HL9) in HB0.
pose proof HB0 as HB1.
apply HPgMem.hm_bytes_app in HB1 as [HA HB1]. apply HPgMem.hm_bytes_app in HB1 as [HZr HDE].
apply HPgMem.hm_bytes_app in HDE as [HDn _]. rewrite hc_lenA in HZr, HDn.
rewrite length_app, !repeat_length in HDn.
assert (Vn : val_mem rsegs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0x1a0 + 0x7c) 4 (Z.of_nat (length cs))).
{ apply HPgMem.hm_val_of_bytes in HDn. rewrite unsigned_lit_small in HDn by lia.
  replace (e_F (x_e cx) + 0x1a0 + 0x7c)
    with (e_F (x_e cx) + 0x1a0 + Z.of_nat (4 + 12 * length cs) + Z.of_nat (12 + 12 * (9 - length cs))) by lia.
  exact HDn. }
assert (HZ : forall i, 4 + 12 * Z.of_nat (length cs) <= i < 124 ->
  YP09.mbyte rsegs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + 0x1a0 + i) = Some (Z_to_bv 8 0)).
{ intros i Hi. pose proof HZr as HZ'. rewrite <- repeat_app in HZ'.
  pose proof (proj1 (HPgMem.hm_bytes_aview rsegs _ _ _ _) HZ' (Z.to_nat (i - 4 - 12 * Z.of_nat (length cs)))) as Hv.
  rewrite repeat_length in Hv. specialize (Hv ltac:(lia)). rewrite nth_repeat in Hv.
  apply (HPgMem.hm_aview_mbyte rsegs). rewrite <- Hv. f_equal. lia. }
(* the block *)
assert (Hpres : forall a, e_F (x_e cx) + 0x1a0 + 4 <= a < e_F (x_e cx) + 0x1a0 + 0x80 -> apresent (w_H W2) mem2 a)
  by (intros a Ha; apply (proj1 (Hfb a ltac:(lia)))).
assert (Hawr : forall a, e_F (x_e cx) + 0x1a0 + 4 <= a < e_F (x_e cx) + 0x1a0 + 0x80 ->
  awr_byte (x_STK cx) (x_sp0 cx) (x_FP cx) (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly2 S2) ly2 (x_own cx) a).
{ intros a Ha. right. right. right. exists 4, (x_pos cx). split; [exact Hown|]. left.
  unfold in_zr. cbn [fst snd]. rewrite FA. change (fs_frame_bytes 4) with 1024. lia. }
assert (HRA : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_F (x_e cx) + 0x1a0) 136).
{ unfold hs_fsh_at in Hfsh. rewrite hc_shX in Hfsh.
  pose proof (HPgMem.hm_A_ra_x rsegs (w_H W2) mem2 (e_F (x_e cx)) false false false false true 0 136 Hfsh
    ltac:(rewrite <- (Z.mod_mod_divide _ 32 8) by (exists 4; reflexivity); rewrite HF32; reflexivity)
    ltac:(lia) ltac:(lia)) as H0.
  unfold HPgMem.HM_X in H0. rewrite Z.add_0_r in H0. exact H0. }
assert (Happ : forall a, e_F (x_e cx) + 0x1a0 <= a < e_F (x_e cx) + 0x1a0 + 136 ->
  ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)).
{ intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold SHADOW_OFF. lia. }
pose proof (Z.mod_pos_bound (hq_nent r) (2 ^ 64) ltac:(lia)) as Hnm.
pose proof (Z.mod_pos_bound (e_pp (x_e cx) + HQ_ENT0) (2 ^ 64) ltac:(lia)) as Htm.
eapply SRr_bind.
{ refine (hc_blk (fx := fx2) B MT MTL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (e_F (x_e cx) + 0x1a0)
    (Z.of_nat (length cs)) (e_cap (x_e cx)) ch p val (hq_nent r mod 2 ^ 64) ((e_pp (x_e cx) + HQ_ENT0) mod 2 ^ 64)
    HJ R9 R22 R23 R20 _ _ _ _ _ _ _ _ _ _ Hnm Htm C98 Ca0 Cb8 Cd8 Ce0 C108 Vn HZ Hpres Hawr HRA Happ); lia. }
intros W3 c3 _ [(Hge & Hpost) | (Hlt & Hpost)];
destruct Hpost as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hk3 & Hfr3 & Hperm3 & Hio3 & Hmo3 & Hmem3 & HR3).
- (* RC: the cap break, no byte written; the fold stops on this cell *)
  assert (Hfin' : hq_fin rsegs cx r = (cs, keys + 1, rf)).
  { destruct Hpi as (_ & Hpref & _ & Hfold). rewrite <- Hfold.
    rewrite (hc_fold_cell _ k v _ cs keys rf (ch, p, val) Hpref Hec).
    replace (e_cap (x_e cx) <=? Z.of_nat (length cs)) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  unfold hq_fin in Hfin'. injection Hfin' as Ecs Ekeys Erf.
  assert (Hcore3 : hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
  { apply (HPgM3eBase.he_core_blk B MT MTL cx (hq_E3 rsegs B cx) (fun _ => False) [10]%bv
      ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hcore HJ3 Hk3);
    [ intros rr [->|[->| ->]]; apply hc_notin; vm_compute; reflexivity
    | exact Hfr3 | exact Hperm3 | exact Hio3 | exact Hmo3 | exact Hmem3 | intros a [] ]. }
  assert (Hm3 : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a)
    by (intros a Ha; apply Hmem3; [exact Ha | exact (fun H => H)]).
  apply (HRC fx2 ly3 S3 W3 regs3 mem3 md3).
  split.
  { apply (HPgM3eBase.he_base3_kept B MT errno_low cx r ev fx2 fx2 hq_shX hq_shX
      ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HS Hb3 Hcore3);
    [ intros a Ha _; exact (Hm3 a Ha)
    | unfold hs_fsh_at in Hfsh |- *; apply (HPgMem.hm_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 _ hq_shX Hfsh);
      intros i Hi; rewrite hq_shX_len in Hi; apply Hm3; lia
    | exact Hfxk ]. }
  split.
  { unfold hs_at_cx.
    pose proof (hc_at_move _ _ _ _ _ _ _ _ [10]%bv (fun _ => False) Hat Hk3 Hmem3 ltac:(vm_compute; reflexivity)
      ltac:(intros a Ha; split; [cbn [hd_xv] in Ha; lia | exact (fun H => H)])) as Hat3.
    hc_sub Hat3. }
  split; [exact (proj1 (proj2 Hlive))|].
  split; [exact (HPgM3bBase.hb_exp_rc cx r Hlive)|].
  rewrite Ecs, Ekeys, Erf. unfold HQ_XO.
  split; [|repeat split; first [exact HxL | lia | exact Hxrf]].
  apply (proj1 (HPgMem.hm_bytes_zbytes rsegs (w_H W3) mem3 _ _)).
  apply (HPgMem.hm_bytes_kept rsegs (w_H W2) mem2); [exact (proj2 (HPgMem.hm_bytes_zbytes rsegs _ _ _ _) Hxb)|].
  intros y Hy. rewrite hq_x_open_len in Hy by (unfold X_CELLS; lia). apply Hm3. unfold HQ_XO in Hy. lia.
- (* LATCH at S (S m): the cell appended *)
  destruct HR3 as (V1 & V2 & V3 & V4 & Q7 & Q31).
  assert (HWE : forall a, hc_Wr (e_F (x_e cx) + 0x1a0) (Z.of_nat (length cs)) a -> hq_E3 rsegs B cx a).
  { intros a Ha. left. unfold hd_inw. cbn [hi_w3 headamp_himg_A]. apply Exists_cons_hd. cbn [hd_xv fst snd].
    unfold hc_Wr in Ha. lia. }
  assert (Hcore3 : hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
  { apply (HPgM3eBase.he_core_blk B MT MTL cx (hq_E3 rsegs B cx) (hc_Wr (e_F (x_e cx) + 0x1a0) (Z.of_nat (length cs)))
      [7; 10; 11; 12; 13; 31]%bv
      ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hcore HJ3 Hk3);
    [ intros rr [->|[->| ->]]; apply hc_notin; vm_compute; reflexivity
    | exact Hfr3 | exact Hperm3 | exact Hio3 | exact Hmo3 | exact Hmem3 | exact HWE ]. }
  apply (HL fx2 ly3 S3 W3 regs3 mem3 md3 (cs ++ [(ch, p, val)]) (keys + 1) rf).
  split.
  { apply (HPgM3eBase.he_base3_kept B MT errno_low cx r ev fx2 fx2 hq_shX hq_shX
      ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HS Hb3 Hcore3);
    [ intros a Ha Hw; apply Hmem3; [exact Ha|]; intros HW; apply Hw; unfold HPgM3eBase.he_wz; right; left;
      unfold hc_Wr in HW; unfold HQ_XO; lia
    | unfold hs_fsh_at in Hfsh |- *; apply (HPgMem.hm_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 _ hq_shX Hfsh);
      intros i Hi; rewrite hq_shX_len in Hi; apply Hmem3; [lia|]; unfold hc_Wr;
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia
    | exact Hfxk ]. }
  split.
  { unfold hs_at_cx.
    pose proof (hc_at_move _ _ _ _ _ _ _ _ [7; 10; 11; 12; 13; 31]%bv _ Hat Hk3 Hmem3 ltac:(vm_compute; reflexivity)
      ltac:(intros a Ha; split; [cbn [hd_xv] in Ha; lia | unfold hc_Wr; cbn [hd_xv] in Ha; lia])) as Hat3.
    unfold hs_at in Hat3 |- *. rewrite !Forall_app in Hat3 |- *.
    destruct Hat3 as (HA1 & HA2 & HA3 & HA4).
    split; [exact HA1|]. split; [exact HA2|]. split; [exact HA3|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    - rewrite Q31. unfold w64. apply HPgSteps.Z_to_bv_mod64.
    - rewrite Q7. unfold w64. apply HPgSteps.Z_to_bv_mod64.
    - rewrite Hk3; [rewrite R21; unfold w64; f_equal; lia | let Hx := fresh in vm_compute; intros Hx; discriminate Hx
                   | apply hc_notin; vm_compute; reflexivity]. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hlive|].
  destruct Hpi as (_ & Hpref & HSm & Hfold).
  split; [unfold hq_nent; lia|].
  split; [lia|].
  split.
  { unfold hq_x_at. rewrite length_app. cbn [length]. unfold HQ_XO.
    split; [|repeat split; first [unfold X_CELLS; lia | exact Hxrf]].
    apply (proj1 (HPgMem.hm_bytes_zbytes rsegs (w_H W3) mem3 _ _)).
    refine (eq_ind_r (fun l => HPgMem.hm_bytes rsegs (w_H W3) mem3 (e_F (x_e cx) + 0x1a0) l) _
      (hc_open_new cs (ch, p, val) (keys + 1) rf HL9)).
    apply (hc_bytes_5 (w_H W2) mem2 (w_H W3) mem3 _ _ (repeat (Z_to_bv 8 0) 12) _ _
      (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 (Z.of_nat (length cs))))) _ _ HB0).
    - rewrite hc_len_cell, repeat_length. reflexivity.
    - rewrite !length_Z_to_le_bytes. reflexivity.
    - rewrite hc_lenA. apply hc_cell_bytes; try lia.
      + replace (e_F (x_e cx) + 0x1a0 + Z.of_nat (4 + 12 * length cs))
          with (e_F (x_e cx) + 0x1a0 + 4 + 12 * Z.of_nat (length cs)) by lia. exact V1.
      + replace (e_F (x_e cx) + 0x1a0 + Z.of_nat (4 + 12 * length cs) + 4)
          with (e_F (x_e cx) + 0x1a0 + 8 + 12 * Z.of_nat (length cs)) by lia. exact V2.
      + replace (e_F (x_e cx) + 0x1a0 + Z.of_nat (4 + 12 * length cs) + 8)
          with (e_F (x_e cx) + 0x1a0 + 12 + 12 * Z.of_nat (length cs)) by lia. exact V3.
    - rewrite hc_lenA, !repeat_length. apply HPgMem.hm_bytes_of_val. rewrite unsigned_lit_small by lia.
      replace (e_F (x_e cx) + 0x1a0 + Z.of_nat (4 + 12 * length cs) + Z.of_nat 12 + Z.of_nat (12 * (9 - length cs)))
        with (e_F (x_e cx) + 0x1a0 + 0x7c) by lia. exact V4.
    - rewrite hc_lenA, !repeat_length, !length_Z_to_le_bytes, !length_app, !length_Z_to_le_bytes.
      intros y Hy. apply Hmem3; [lia|]. unfold hc_Wr. lia. }
  unfold hq_fold_inv. rewrite (hc_fold_cell _ k v _ cs keys rf (ch, p, val) Hpref Hec) in Hfold.
  replace (e_cap (x_e cx) <=? Z.of_nat (length cs)) with false in Hfold by (symmetry; apply Z.leb_gt; lia).
  exact Hfold.
Qed.

End d.
End b.

Print Assumptions hc_blk.
Print Assumptions he_cell.
About he_cell.
