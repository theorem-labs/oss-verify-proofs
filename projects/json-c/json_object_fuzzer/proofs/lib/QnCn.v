(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QCcH Q0Ek QJjn Qsw7 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QCcH Q0Ek QJjn Qsw7.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition slots (ps : list Z) : list cell := map (fun p => C8 (Z_to_bv 64 p)) ps.
Definition wl (ps : list Z) : list word := map (Z_to_bv 64) ps.

#[using="Type"] Lemma slots_bytes : forall ps, cells_bytes (slots ps) = u64s (wl ps).
Proof. induction ps as [|p ps IH]; [reflexivity|]. cbn -[le8]. f_equal. exact IH. Qed.
#[using="Type"] Lemma slots_size : forall ps, cells_size (slots ps) = (8 * length ps)%nat.
Proof.
induction ps as [|p ps IH]; [reflexivity|].
change (cells_size (slots (p :: ps))) with (8 + cells_size (slots ps))%nat. rewrite IH. cbn [length]. lia.
Qed.
#[using="Type"] Lemma slots_wf : forall ps, cells_wf (slots ps).
Proof. induction ps as [|p ps IH]; [exact I|]. split; [exact I | exact IH]. Qed.
#[using="Type"] Lemma wl_length : forall ps, length (wl ps) = length ps.
Proof. intros. unfold wl. apply length_map. Qed.
#[using="Type"] Lemma slots_length : forall ps, length (slots ps) = length ps.
Proof. intros. unfold slots. apply length_map. Qed.
#[using="Type"] Lemma slots_app : forall a b, slots (a ++ b) = slots a ++ slots b.
Proof. intros. unfold slots. apply map_app. Qed.
#[using="Type"] Lemma wl_app : forall a b, wl (a ++ b) = wl a ++ wl b.
Proof. intros. unfold wl. apply map_app. Qed.
#[using="Type"] Lemma wl_upd : forall ps i x, wl (upd ps i x) = upd (wl ps) i (Z_to_bv 64 x).
Proof.
intros ps i x. unfold wl. revert i. induction ps as [|p ps IH]; intros [|i]; cbn; try reflexivity.
rewrite IH. reflexivity.
Qed.
#[using="Type"] Lemma nth_error_wl : forall ps i p, nth_error ps i = Some p -> nth_error (wl ps) i = Some (Z_to_bv 64 p).
Proof. intros ps i p H. unfold wl. rewrite nth_error_map, H. reflexivity. Qed.

Definition al_nth (ps : list Z) (i : Z) : Z := nth (Z.to_nat i) ps 0.
#[using="Type"] Lemma al_nth_in : forall ps i, 0 <= i < Z.of_nat (length ps) -> nth_error ps (Z.to_nat i) = Some (al_nth ps i).
Proof. intros ps i Hi. unfold al_nth. apply nth_error_nth'. lia. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.

#[using="Type"] Lemma u64arr_of_slots : forall m A ps, rw_cells segs m A (slots ps) -> u64arr segs m A (wl ps).
Proof.
intros m A ps [[W B] R]. split.
- rewrite <- slots_bytes. exact B.
- rewrite slots_size in R. rewrite wl_length.
replace (8 * Z.of_nat (length ps)) with (Z.of_nat (8 * length ps)) by lia. exact R.
Qed.
#[using="Type"] Lemma slots_of_u64arr : forall m A ps, u64arr segs m A (wl ps) -> rw_cells segs m A (slots ps).
Proof.
intros m A ps [B R]. split; [split; [apply slots_wf | rewrite slots_bytes; exact B]|].
rewrite slots_size. rewrite wl_length in R.
replace (Z.of_nat (8 * length ps)) with (8 * Z.of_nat (length ps)) by lia. exact R.
Qed.

Definition al_hdr (m : word -> option byte) (a arr len size : Z) : Prop :=
rw_cells segs m a [C8 (Z_to_bv 64 arr); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 (fn_arr_entry_free fn))].
Definition al_tail (m : word -> option byte) (arr size : Z) (n : nat) (junk : list byte) : Prop :=
rw_cells segs m (arr + 8 * Z.of_nat n) [CB (Z.to_nat (8 * (size - Z.of_nat n))) junk].
Definition al_open (m : word -> option byte) (a arr size : Z) (ps : list Z) (junk : list byte) : Prop :=
al_hdr m a arr (Z.of_nat (length ps)) size
/\ u64arr segs m arr (wl ps)
/\ al_tail m arr size (length ps) junk
/\ Z.of_nat (length ps) <= size /\ (1 <= size /\ 8 * size < 2^64).

#[using="Type"] Lemma alist_open : forall m BS a ps, alist segs fn m BS a ps ->
exists arr size junk, BS = [(a, 32); (arr, 8 * size)] /\ al_open m a arr size ps junk.
Proof.
intros m BS a ps (arr & size & junk & HBS & Hlen & Hsz & HDR & ARR).
exists arr, size, junk. split; [exact HBS|].
apply (proj1 (rw_cells_app segs m arr _ _)) in ARR. destruct ARR as [SL JK].
change (map _ ps) with (slots ps) in SL, JK. rewrite slots_size in JK.
replace (Z.of_nat (8 * length ps)) with (8 * Z.of_nat (length ps)) in JK by lia.
split; [exact HDR|]. split; [apply u64arr_of_slots; exact SL|]. split; [exact JK|]. split; [exact Hlen | exact Hsz].
Qed.

#[using="Type"] Lemma alist_openx : forall m a arr size ps, alist segs fn m [(a, AL_SZ); (arr, 8 * size)] a ps ->
exists junk, al_open m a arr size ps junk.
Proof.
intros m a arr size ps AL. destruct (alist_open m _ a ps AL) as (arr' & size' & junk & E & OP).
injection E as E1 E2. assert (size' = size) by lia. subst arr' size'. exists junk. exact OP.
Qed.

#[using="Type"] Lemma alist_close : forall m a arr size ps junk, al_open m a arr size ps junk ->
alist segs fn m [(a, 32); (arr, 8 * size)] a ps.
Proof.
intros m a arr size ps junk (HDR & ARR & JK & Hlen & Hsz).
exists arr, size, junk. split; [reflexivity|]. split; [exact Hlen|]. split; [exact Hsz|]. split; [exact HDR|].
apply (proj2 (rw_cells_app segs m arr _ _)). change (map _ ps) with (slots ps).
split; [apply slots_of_u64arr; exact ARR|].
rewrite slots_size. replace (Z.of_nat (8 * length ps)) with (8 * Z.of_nat (length ps)) by lia. exact JK.
Qed.

#[using="Type"] Lemma u64arr_snoc : forall m A ps (v : Z),
u64arr segs m A (wl ps) -> rw_cells segs m (A + 8 * Z.of_nat (length ps)) [C8 (Z_to_bv 64 v)] ->
u64arr segs m A (wl (ps ++ [v])).
Proof.
intros m A ps v ARR C.
apply u64arr_of_slots. rewrite slots_app. apply (proj2 (rw_cells_app segs m A _ _)).
split; [apply slots_of_u64arr; exact ARR|]. rewrite slots_size.
replace (Z.of_nat (8 * length ps)) with (8 * Z.of_nat (length ps)) by lia. exact C.
Qed.

#[using="Type"] Lemma al_arr_join : forall m arr size ps junk,
u64arr segs m arr (wl ps) -> al_tail m arr size (length ps) junk -> Z.of_nat (length ps) <= size ->
rw_cells segs m arr [CB (Z.to_nat (8 * size)) ((u64s (wl ps) ++ junk) ++ [])].
Proof.
intros m arr size ps junk ARR JK Hlen. unfold al_tail in JK.
assert (LJ : length junk = Z.to_nat (8 * (size - Z.of_nat (length ps)))) by (destruct JK as [[[W _] _] _]; exact W).
rewrite app_nil_r.
eapply (rw_cells_recast segs m arr (slots ps ++ [CB (Z.to_nat (8 * (size - Z.of_nat (length ps)))) junk])).
- apply (proj2 (rw_cells_app segs m arr _ _)). split; [apply slots_of_u64arr; exact ARR|].
rewrite slots_size. replace (Z.of_nat (8 * length ps)) with (8 * Z.of_nat (length ps)) by lia. exact JK.
- cbn. rewrite length_app, u64s_length, wl_length, LJ. lia.
- rewrite cells_bytes_app, slots_bytes. cbn. rewrite !app_nil_r. reflexivity.
- rewrite cells_size_app, slots_size. cbn. lia.
Qed.

#[using="Type"] Lemma al_arr_split : forall m r size size' ps junk junk',
rw_cells segs m r [CB (Z.to_nat (8 * size')) ((u64s (wl ps) ++ junk) ++ junk')] ->
length junk = Z.to_nat (8 * (size - Z.of_nat (length ps))) -> Z.of_nat (length ps) <= size <= size' ->
u64arr segs m r (wl ps) /\ al_tail m r size' (length ps) (junk ++ junk').
Proof.
intros m r size size' ps junk junk' BLK LJ Hsz.
assert (LA : length ((u64s (wl ps) ++ junk) ++ junk') = Z.to_nat (8 * size')) by (destruct BLK as [[[W _] _] _]; exact W).
rewrite !length_app, u64s_length, wl_length in LA.
eapply (rw_cells_recast segs m r _ (slots ps ++ [CB (Z.to_nat (8 * (size' - Z.of_nat (length ps)))) (junk ++ junk')])) in BLK.
- apply (proj1 (rw_cells_app segs m r _ _)) in BLK. destruct BLK as [SL JK].
split; [apply u64arr_of_slots; exact SL|]. unfold al_tail.
rewrite slots_size in JK. replace (Z.of_nat (8 * length ps)) with (8 * Z.of_nat (length ps)) in JK by lia. exact JK.
- apply cells_wf_app. split; [apply slots_wf|]. cbn. rewrite length_app, LJ. lia.
- rewrite cells_bytes_app, slots_bytes. cbn. rewrite !app_nil_r, !app_assoc. reflexivity.
- rewrite cells_size_app, slots_size. cbn. lia.
Qed.

#[using="Type"] Lemma al_tail_absorb : forall m arr size ps qs junk,
u64arr segs m arr (wl (ps ++ qs)) -> al_tail m arr size (length (ps ++ qs)) junk ->
Z.of_nat (length (ps ++ qs)) <= size ->
u64arr segs m arr (wl ps) /\ al_tail m arr size (length ps) (u64s (wl qs) ++ junk).
Proof.
intros m arr size ps qs junk ARR JK Hlen. unfold al_tail in *.
assert (LJ : length junk = Z.to_nat (8 * (size - Z.of_nat (length (ps ++ qs))))) by (destruct JK as [[[W _] _] _]; exact W).
rewrite length_app in LJ, Hlen.
apply slots_of_u64arr in ARR. rewrite slots_app in ARR.
apply (proj1 (rw_cells_app segs m arr _ _)) in ARR. destruct ARR as [SL1 SL2].
split; [apply u64arr_of_slots; exact SL1|].
rewrite slots_size in SL2. replace (Z.of_nat (8 * length ps)) with (8 * Z.of_nat (length ps)) in SL2 by lia.
eapply (rw_cells_recast segs m _ (slots qs ++ [CB (Z.to_nat (8 * (size - Z.of_nat (length (ps ++ qs))))) junk])).
- apply (proj2 (rw_cells_app segs m _ _ _)). split; [exact SL2|].
rewrite slots_size, length_app.
replace (arr + 8 * Z.of_nat (length ps) + Z.of_nat (8 * length qs)) with (arr + 8 * Z.of_nat (length ps + length qs)) by lia.
rewrite length_app in JK. exact JK.
- cbn. rewrite length_app, u64s_length, wl_length, LJ. lia.
- rewrite cells_bytes_app, slots_bytes. cbn. rewrite !app_nil_r. reflexivity.
- rewrite cells_size_app, slots_size, length_app. cbn. lia.
Qed.

#[using="Type"] Lemma al_slot_read : forall m arr ps i a8,
u64arr segs m arr (wl ps) -> 0 <= i < Z.of_nat (length ps) -> a8 = wa (arr + 8 * i) ->
ov_read_bytes segs m a8 8 = Some (le8 (Z_to_bv 64 (al_nth ps i))).
Proof.
intros m arr ps i a8 ARR Hi ->.
eapply (u64arr_read segs m arr (wl ps) i); [exact ARR | | lia | reflexivity].
apply nth_error_wl. apply al_nth_in. exact Hi.
Qed.
End WithSegs.

#[using="Type"] Lemma al_blocks : forall L (HIx : heap_iface L) A a arr size LB m md,
HEAP L HIx A ((a, 32) :: (arr, 8 * size) :: LB) m md ->
(a mod 16 = 0 /\ 0 < a /\ a + 32 <= alloc_ceiling /\ (a + 32 <= hl_img_lo L \/ hl_img_hi L <= a))
/\ (arr mod 16 = 0 /\ 0 < arr /\ arr + 8 * size <= alloc_ceiling /\ (arr + 8 * size <= hl_img_lo L \/ hl_img_hi L <= arr))
/\ (a + 32 <= arr \/ arr + 8 * size <= a).
Proof.
intros L HIx A a arr size LB m md HP.
pose proof (heap_blk L HIx _ _ _ _ a 32 HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img L HIx _ _ _ _ a 32 HP ltac:(left; reflexivity)) as Hia.
pose proof (heap_blk L HIx _ _ _ _ arr (8 * size) HP ltac:(right; left; reflexivity)) as (_ & Hal2 & Hlo2 & Hhi2 & _).
pose proof (heap_blk_img L HIx _ _ _ _ arr (8 * size) HP ltac:(right; left; reflexivity)) as Hia2.
pose proof (blk_ne_01 L HIx _ _ _ _ _ _ _ _ HP) as Hne.
pose proof (heap_blk_disjoint L HIx _ _ _ _ a 32 arr (8 * size) HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne) as Hdj.
repeat split; try assumption.
Qed.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Lemma land7_of_mod8 : forall p, p mod 8 = 0 -> Z.land p 7 = 0.
Proof. intros p Hp. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. exact Hp. Qed.

Lemma slot_mod8 : forall arr k, arr mod 16 = 0 -> (arr + k * 8) mod 8 = 0.
Proof. intros arr k H. rewrite Z.add_mod, Z.mod_mul by lia. replace (arr mod 8) with 0; [reflexivity|].
symmetry. apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ 16); [exists 2; reflexivity | apply Z.mod_divide; lia]. Qed.
Lemma slot_mod8' : forall arr k, arr mod 16 = 0 -> (arr + 8 * k) mod 8 = 0.
Proof. intros. replace (8 * k) with (k * 8) by lia. apply slot_mod8. assumption. Qed.
Lemma slot_mod8'' : forall arr k, arr mod 16 = 0 -> (k * 8 + arr) mod 8 = 0.
Proof. intros. replace (k * 8 + arr) with (arr + k * 8) by lia. apply slot_mod8. assumption. Qed.

Ltac div8_atom :=
first [ match goal with
| H : ?p mod 16 = 0 |- (8 | ?p) => apply (Z.divide_trans 8 16 p); [exists 2; reflexivity | apply Z.mod_divide; [lia | exact H]]
| |- (8 | 8 * ?k) => exists k; lia
| |- (8 | ?k * 8) => exists k; lia
| |- (8 | 8) => exists 1; reflexivity
end
| exists 0; lia ].

Ltac mod8_tac := apply Z.mod_divide; [lia|]; repeat apply Z.divide_add_r; div8_atom.
Ltac ubsan_align8 p :=
rewrite ?(unsigned_lit p) by lia;
rewrite (land7_of_mod8 p) by mod8_tac;
if_false.

Lemma idx_chk_zero : forall i, 0 <= i < 2^60 -> Z.shiftr (i + 1152921504606846976) 61 = 0.
Proof. intros i Hi. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Lemma lor_bound64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof.
intros a b Ha Hb.
assert (H0 : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
split; [exact H0|].
destruct (Z.eq_dec (Z.lor a b) 0) as [->|Hnz]; [lia|].
apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia.
assert (La : Z.log2 a < 64) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
assert (Lb : Z.log2 b < 64) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
lia.
Qed.
