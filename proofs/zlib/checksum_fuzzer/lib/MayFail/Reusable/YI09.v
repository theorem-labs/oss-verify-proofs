(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI09.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition layout_t := list (Z * N).
Definition LAY_Config : layout_t :=
[(0, 8%N)    ; (8, 8%N)  ; (16, 4%N)  ; (20, 4%N)  ;
(24, 2%N)   ; (26, 2%N)  ; (28, 2%N)  ; (30, 2%N)  ;
(32, 8%N)   ; (40, 8%N)  ].
Definition LAY_CGIF : layout_t :=
[(0, 8%N)  ; (8, 8%N)  ; (16, 8%N)  ;
(24, 8%N)  ; (32, 8%N)  ;
(40, 4%N)  ; (44, 4%N)  ;
(48, 2%N)  ; (50, 2%N)  ;
(52, 2%N)  ; (54, 2%N)  ;
(56, 8%N)  ; (64, 8%N)  ;
(72, 8%N)  ; (80, 8%N)  ; (88, 4%N)  ; (92, 4%N)  ].
Definition CGIF_SIZE : Z := 96.
Definition CG_fr0 := 0%nat.  Definition CG_fr1 := 1%nat.  Definition CG_fr2 := 2%nat.
Definition CG_pal := 3%nat.  Definition CG_path := 4%nat. Definition CG_attr := 5%nat. Definition CG_gen := 6%nat.
Definition CG_w := 7%nat.    Definition CG_h := 8%nat.    Definition CG_ngp := 9%nat.  Definition CG_loops := 10%nat.
Definition CG_wfn := 11%nat. Definition CG_ctx := 12%nat.  Definition CG_raw := 13%nat. Definition CG_file := 14%nat.
Definition CG_cur := 15%nat. Definition CG_ihead := 16%nat.
Definition LAY_FrameConfig : layout_t :=
[(0, 8%N)  ; (8, 8%N)  ; (16, 4%N)  ; (20, 4%N)  ;
(24, 2%N)  ; (26, 2%N)  ; (28, 1%N)  ].
Definition LAY_Frame : layout_t := LAY_FrameConfig ++ [(32, 1%N)  ; (33, 1%N)  ].
Definition FRAME_SIZE : Z := 40.
Definition FR_lpal := 0%nat. Definition FR_img := 1%nat. Definition FR_attr := 2%nat. Definition FR_gen := 3%nat.
Definition FR_delay := 4%nat. Definition FR_nlp := 5%nat. Definition FR_ctidx := 6%nat. Definition FR_disp := 7%nat.
Definition FR_tidx := 8%nat.
Definition LAY_RawConfig : layout_t :=
[(0, 8%N)  ; (8, 8%N)  ; (16, 8%N)  ; (24, 4%N)  ;
(28, 2%N)  ; (30, 2%N)  ; (32, 2%N)  ; (34, 2%N)  ].
Definition LAY_Raw : layout_t := LAY_RawConfig ++ [(40, 4%N)  ].
Definition RAW_SIZE : Z := 48.
Definition RW_wfn := 0%nat. Definition RW_ctx := 1%nat. Definition RW_gct := 2%nat. Definition RW_attr := 3%nat.
Definition RW_w := 4%nat. Definition RW_h := 5%nat. Definition RW_sgct := 6%nat. Definition RW_loops := 7%nat.
Definition RW_cur := 8%nat.
Definition LAY_RawFrameConfig : layout_t :=
[(0, 8%N)  ; (8, 8%N)  ; (16, 4%N)  ; (20, 2%N)  ;
(22, 2%N)  ; (24, 2%N)  ; (26, 2%N)  ; (28, 2%N)  ;
(30, 2%N)  ; (32, 1%N)  ; (33, 1%N)  ].
Definition LAY_LZWResult : layout_t := [(0, 8%N)  ; (8, 4%N)  ].
Definition LAY_LZWGenState : layout_t :=
[(0, 8%N)  ; (8, 8%N)  ; (16, 8%N)  ; (24, 8%N)  ;
(32, 8%N)  ; (40, 8%N)  ; (48, 8%N)  ; (56, 4%N)  ;
(60, 4%N)  ; (64, 2%N)  ; (66, 2%N)  ].
Definition R_ERROR : Z := 2 ^ 32 - 1.  Definition R_OK : Z := 0.  Definition R_EWRITE : Z := 1.
Definition R_EALLOC : Z := 2.  Definition R_ECLOSE : Z := 3.  Definition R_EOPEN : Z := 4.
Definition R_EINDEX : Z := 5.  Definition R_PENDING : Z := 6.
Section d.
Variable segs : list Segment.
Definition field_ok (mem : word -> option byte) (a : Z) (f : Z * N) (v : Z) : Prop :=
val_mem segs mem (a + fst f) (N.to_nat (snd f)) v /\ 0 <= v < 2 ^ (8 * Z.of_N (snd f)).
Fixpoint obj_at (mem : word -> option byte) (a : Z) (lay : layout_t) (vals : list Z) : Prop :=
match lay, vals with
| [], [] => True
| f :: lay', v :: vals' => field_ok mem a f v /\ obj_at mem a lay' vals'
| _, _ => False
end.
Lemma obj_at_length : forall mem a lay vals, obj_at mem a lay vals -> length vals = length lay.
Proof.
intros mem a lay. induction lay as [|f lay IH]; intros [|v vals] H; cbn in *; try tauto.
f_equal. apply IH. tauto.
Qed.
Lemma obj_at_nth : forall mem a lay vals j f v,
obj_at mem a lay vals -> nth_error lay j = Some f -> nth_error vals j = Some v -> field_ok mem a f v.
Proof.
intros mem a lay. induction lay as [|f0 lay IH]; intros [|v0 vals] j f v H Hf Hv; cbn in H; try tauto.
- destruct j; discriminate.
- destruct j as [|j]; cbn in Hf, Hv.
+ injection Hf as <-. injection Hv as <-. tauto.
+ eapply IH; [apply (proj2 H) | exact Hf | exact Hv].
Qed.
Lemma obj_at_transport : forall mem mem' a lay vals,
obj_at mem a lay vals ->
(forall f i, In f lay -> 0 <= i < Z.of_N (snd f) -> mbyte segs mem' (a + fst f + i) = mbyte segs mem (a + fst f + i)) ->
obj_at mem' a lay vals.
Proof.
intros mem mem' a lay. induction lay as [|f lay IH]; intros [|v vals] H Heq; cbn in *; try tauto.
destruct H as [[Hv Hr] H]. split.
- split; [|exact Hr]. intros k Hk. pose proof (N_nat_Z (snd f)). rewrite Heq; [apply Hv; exact Hk | left; reflexivity | lia].
- apply IH; [exact H|]. intros f' i Hin Hi. apply Heq; [right; exact Hin | exact Hi].
Qed.
Definition lay_inside (lay : layout_t) (sz : Z) : bool :=
forallb (fun f => (0 <=? fst f) && (fst f + Z.of_N (snd f) <=? sz)) lay.
Lemma obj_at_transport_range : forall mem mem' a lay vals sz,
obj_at mem a lay vals -> lay_inside lay sz = true ->
(forall i, 0 <= i < sz -> mbyte segs mem' (a + i) = mbyte segs mem (a + i)) ->
obj_at mem' a lay vals.
Proof.
intros mem mem' a lay vals sz H Hin Heq. eapply obj_at_transport; [exact H|].
intros f i Hf Hi. pose proof (proj1 (forallb_forall _ _) Hin f Hf) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
replace (a + fst f + i) with (a + (fst f + i)) by lia. apply Heq. lia.
Qed.
Fixpoint list_set {X : Type} (l : list X) (j : nat) (x : X) : list X :=
match l, j with
| [], _ => []
| _ :: l', O => x :: l'
| y :: l', S j' => y :: list_set l' j' x
end.
Lemma nth_error_list_set_same : forall {X} (l : list X) j x, (j < length l)%nat -> nth_error (list_set l j x) j = Some x.
Proof. induction l; intros [|j] x Hj; cbn in *; try lia; [reflexivity | apply IHl; lia]. Qed.
Lemma nth_error_list_set_other : forall {X} (l : list X) j i x, i <> j -> nth_error (list_set l j x) i = nth_error l i.
Proof. induction l; intros [|j] [|i] x Hij; cbn in *; try reflexivity; [congruence | apply IHl; congruence]. Qed.
Fixpoint obj_chunks_gen (lay : layout_t) (k : nat) (lits : list (option Z)) : list chunk :=
match lay with
| [] => []
| f :: lay' =>
mkChunk (fst f) (CVal (snd f) (match lits with Some z :: _ => SLit z | _ => SOff k 0 end))
:: obj_chunks_gen lay' (S k) (tl lits)
end.
Definition obj_chunks_from (lay : layout_t) (k : nat) : list chunk := obj_chunks_gen lay k [].
Definition lay_widths_ok (lay : layout_t) : bool := forallb (fun f => (Z.of_N (snd f) <=? 8)) lay.
Lemma obj_chunks_gen_ok : forall E mem a lay vals k lits,
obj_at mem a lay vals -> lay_widths_ok lay = true ->
(forall j v, nth_error vals j = Some v -> ew E (k + j) = Z_to_bv 64 v) ->
(forall j z, nth_error lits j = Some (Some z) -> nth_error vals j = Some z) ->
Forall (chunk_ok segs E mem a) (obj_chunks_gen lay k lits).
Proof.
intros E mem a lay. induction lay as [|f lay IH]; intros [|v vals] k lits H Hw HE HL; cbn in H; try tauto; [constructor|].
cbn [obj_chunks_gen]. unfold lay_widths_ok in Hw. cbn [forallb] in Hw. apply andb_prop in Hw as [Hw1 Hw].
apply Z.leb_le in Hw1. destruct H as [[Hv Hr] H]. constructor.
- destruct f as [o w]. cbn [fst snd] in *. eapply chunk_ok_val; [| exact Hr | exact Hw1 | exact Hv].
assert (HEv : sv_denot E (SOff k 0) = Z_to_bv 64 v).
{ cbn [sv_denot]. rewrite Z.add_0_r. specialize (HE 0%nat v eq_refl). rewrite Nat.add_0_r in HE. rewrite HE.
rewrite Z_to_bv_unsigned. apply Z_to_bv64_eq_mod. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity. }
destruct lits as [|[z|] lits']; [exact HEv | | exact HEv].
specialize (HL 0%nat z eq_refl). cbn in HL. injection HL as ->. reflexivity.
- apply (IH vals (S k) (tl lits)); [exact H | exact Hw | |].
+ intros j v' Hj. replace (S k + j)%nat with (k + S j)%nat by lia. apply HE. exact Hj.
+ intros j z Hj. apply (HL (S j) z). destruct lits as [|x lits']; [destruct j; discriminate | exact Hj].
Qed.
Lemma obj_chunks_ok : forall E mem a lay vals k,
obj_at mem a lay vals -> lay_widths_ok lay = true ->
(forall j v, nth_error vals j = Some v -> ew E (k + j) = Z_to_bv 64 v) ->
Forall (chunk_ok segs E mem a) (obj_chunks_from lay k).
Proof.
intros E mem a lay vals k H Hw HE. apply (obj_chunks_gen_ok E mem a lay vals k [] H Hw HE).
intros j z Hj. destruct j; discriminate.
Qed.
Lemma obj_at_of_chunks_gen : forall E mem a lay vals k lits,
Forall (chunk_ok segs E mem a) (obj_chunks_gen lay k lits) -> lay_widths_ok lay = true ->
length vals = length lay ->
(forall j v, nth_error vals j = Some v ->
0 <= v < 2 ^ (8 * Z.of_N (snd (nth j lay (0, 8%N)))) /\
match nth_error lits j with Some (Some z) => z = v | _ => ew E (k + j) = Z_to_bv 64 v end) ->
obj_at mem a lay vals.
Proof.
intros E mem a lay. induction lay as [|f lay IH]; intros [|v vals] k lits H Hw Hlen HE; cbn in Hlen; try discriminate; [exact I|].
cbn [obj_chunks_gen] in H. inversion H as [|c cs Hc Hcs]; subst.
unfold lay_widths_ok in Hw. cbn [forallb] in Hw. apply andb_prop in Hw as [Hw1 Hw]. apply Z.leb_le in Hw1.
destruct (HE 0%nat v eq_refl) as [Hr0 HE0]. cbn [nth] in Hr0.
cbn [obj_at]. split.
- split; [|exact Hr0]. destruct f as [o w]. cbn [fst snd] in *.
eapply val_of_chunk_ok; [exact Hc | | exact Hr0 | exact Hw1].
assert (HA : ew E (k + 0) = Z_to_bv 64 v -> sv_denot E (SOff k 0) = Z_to_bv 64 v).
{ intros HE1. rewrite Nat.add_0_r in HE1. cbn [sv_denot]. rewrite Z.add_0_r, HE1, Z_to_bv_unsigned. apply Z_to_bv64_eq_mod.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
destruct lits as [|[z|] lits']; cbn [nth_error] in HE0; [apply HA; exact HE0 | subst; reflexivity | apply HA; exact HE0].
- apply (IH vals (S k) (tl lits)); [exact Hcs | exact Hw | lia |]. intros j v' Hj.
destruct (HE (S j) v' Hj) as [Hr Hm]. split; [exact Hr|].
replace (S k + j)%nat with (k + S j)%nat by lia.
destruct lits as [|x lits']; cbn [tl nth_error] in *; [destruct j; exact Hm | exact Hm].
Qed.
Lemma region_ok_obj_gen : forall E mem n a sz wlo whi lay vals k lits,
bv_unsigned (ew E n) = a -> 0 <= a -> a + sz <= 2 ^ 64 ->
obj_at mem a lay vals -> lay_widths_ok lay = true ->
(forall j v, nth_error vals j = Some v -> ew E (k + j) = Z_to_bv 64 v) ->
(forall j z, nth_error lits j = Some (Some z) -> nth_error vals j = Some z) ->
(forall i, wlo <= i < whi -> writable_at segs mem (a + i)) ->
region_ok segs E mem (YP09.mkRegion (Some n) 0 sz wlo whi (obj_chunks_gen lay k lits)).
Proof.
intros E mem n a sz wlo whi lay vals k lits Hn Ha Hsz Hobj Hw HE HL Hwr.
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite Hn.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; exact Ho|].
eapply obj_chunks_gen_ok; eauto.
Qed.
Lemma region_ok_obj : forall E mem n a sz wlo whi lay vals k,
bv_unsigned (ew E n) = a -> 0 <= a -> a + sz <= 2 ^ 64 ->
obj_at mem a lay vals -> lay_widths_ok lay = true ->
(forall j v, nth_error vals j = Some v -> ew E (k + j) = Z_to_bv 64 v) ->
(forall i, wlo <= i < whi -> writable_at segs mem (a + i)) ->
region_ok segs E mem (YP09.mkRegion (Some n) 0 sz wlo whi (obj_chunks_from lay k)).
Proof.
intros E mem n a sz wlo whi lay vals k Hn Ha Hsz Hobj Hw HE Hwr.
eapply region_ok_obj_gen; eauto. intros j z Hj. destruct j; discriminate.
Qed.
Lemma Ereg_vals : forall regs vals more j v,
nth_error vals j = Some v -> ew (Ereg regs (map (Z_to_bv 64) vals ++ more)) (32 + j) = Z_to_bv 64 v.
Proof.
intros regs vals more j v Hj. rewrite ew_Ereg_extra.
assert (Hl : (j < length vals)%nat) by (apply nth_error_Some; congruence).
rewrite app_nth1 by (rewrite length_map; exact Hl).
apply nth_error_nth. apply map_nth_error. exact Hj.
Qed.
Lemma Ereg_more : forall regs vals more j v,
nth_error more j = Some v -> ew (Ereg regs (map (Z_to_bv 64) vals ++ map (Z_to_bv 64) more)) (32 + (length vals + j)) = Z_to_bv 64 v.
Proof.
intros regs vals more j v Hj. rewrite ew_Ereg_extra.
replace (length vals) with (length (map (Z_to_bv 64) vals)) by apply length_map.
rewrite app_nth2_plus. apply nth_error_nth. apply map_nth_error. exact Hj.
Qed.
End d.
Lemma LAY_CGIF_ok : lay_inside LAY_CGIF CGIF_SIZE = true /\ lay_widths_ok LAY_CGIF = true.
Proof. split; reflexivity. Qed.
Lemma LAY_Frame_ok : lay_inside LAY_Frame FRAME_SIZE = true /\ lay_widths_ok LAY_Frame = true.
Proof. split; reflexivity. Qed.
Lemma LAY_Raw_ok : lay_inside LAY_Raw RAW_SIZE = true /\ lay_widths_ok LAY_Raw = true.
Proof. split; reflexivity. Qed.
End b.
