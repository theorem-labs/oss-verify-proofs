(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI67.v, with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YI09 YI08 YI0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section J.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Local Notation segs := (ms_segs B).
Lemma jcall_tmp : forall E ss ms STK sp0 FP L A mem md Lc Ac mdc STK1 FP1
(K : layout -> astate -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) raw,
st_ok segs E ss ms -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 1 = raw ->
(fn_pre B MR STK1 Lc Ac (ms_regs ms) (ms_mem ms) mdc ->
SR segs (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK1 (spZ (ms_regs ms)) FP1 Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ K L2 A2 regs2 mem2 md2)) ->
YK0s.ret_ok raw -> spZ (ms_regs ms) mod 16 = 0 -> 0 <= STK1 ->
sp0 - STK <= spZ (ms_regs ms) - STK1 -> spZ (ms_regs ms) <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
(forall a, inFP FP1 a -> (inFP FP a /\ a < alloc_ceiling) \/
(exists b n, In (b, n) (blocks Lc Ac) /\ ~ In (b, n) (blocks L A) /\ b <= a < b + n)) ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
journal B MR STK1 (spZ (ms_regs ms)) FP1 Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ K L2 A2 regs2 mem2 md2).
Proof.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc STK1 FP1 K raw HS Hrv HJ Hra Hcallee Hraw Hal16 Hstk1 Hlo Hhi Htp HF.
rewrite (st_ok_mkst segs E ss ms HS Hrv).
eapply SR_mono.
{ apply Hcallee. eapply (fn_pre_of_journal B MR); [exact HJ | rewrite Hra; exact Hraw | exact Hal16 | exact Hstk1 | exact Hlo | exact Hhi | exact Htp]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
eapply (journal_sub_gen B MR LAWS); [exact HJ | exact HJ1 | exact Hlo | exact Hhi | exact HF].
Qed.
End J.
Lemma le_byte_wh_0 : forall W H, 0 <= W < 65536 -> 0 <= H < 65536 -> le_byte (W + 65536 * H) 4 0 = le_byte W 2 0.
Proof. intros. unfold le_byte. rewrite !Z.shiftr_div_pow2 by lia. cbn -[Z.add Z.mul Z.modulo Z.div]. lia. Qed.
Lemma le_byte_wh_1 : forall W H, 0 <= W < 65536 -> 0 <= H < 65536 -> le_byte (W + 65536 * H) 4 1 = le_byte W 2 1.
Proof. intros. unfold le_byte. rewrite !Z.shiftr_div_pow2 by lia. cbn -[Z.add Z.mul Z.modulo Z.div]. lia. Qed.
Lemma le_byte_wh_2 : forall W H, 0 <= W < 65536 -> 0 <= H < 65536 -> le_byte (W + 65536 * H) 4 2 = le_byte H 2 0.
Proof. intros. unfold le_byte. rewrite !Z.shiftr_div_pow2 by lia. cbn -[Z.add Z.mul Z.modulo Z.div]. lia. Qed.
Lemma le_byte_wh_3 : forall W H, 0 <= W < 65536 -> 0 <= H < 65536 -> le_byte (W + 65536 * H) 4 3 = le_byte H 2 1.
Proof. intros. unfold le_byte. rewrite !Z.shiftr_div_pow2 by lia. cbn -[Z.add Z.mul Z.modulo Z.div]. lia. Qed.
Lemma sext32_low : forall x, 0 <= x < 2 ^ 32 -> (zcanon (bv_swrap 32 (x mod 2 ^ 32))) mod 2 ^ 32 = x.
Proof.
intros x Hx. unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
cbn -[Z.add Z.mul Z.modulo Z.div Z.sub]. lia.
Qed.
Lemma sext16_low : forall x, 0 <= x < 2 ^ 16 -> (zcanon (bv_swrap 16 (x mod 2 ^ 16))) mod 2 ^ 16 = x.
Proof.
intros x Hx. unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
cbn -[Z.add Z.mul Z.modulo Z.div Z.sub]. lia.
Qed.
Section h.
Variable segs : list Segment.
Lemma val_mem_wh_split : forall m a W H,
val_mem segs m a 4 (W + 65536 * H) -> 0 <= W < 65536 -> 0 <= H < 65536 ->
val_mem segs m a 2 W /\ val_mem segs m (a + 2) 2 H.
Proof.
intros m a W H Hv HW HH. split; intros k Hk.
- rewrite (Hv k) by lia. destruct k as [|[|k]]; [| | lia].
+ rewrite le_byte_wh_0 by lia. reflexivity.
+ rewrite le_byte_wh_1 by lia. reflexivity.
- replace (a + 2 + Z.of_nat k) with (a + Z.of_nat (2 + k)) by lia. rewrite (Hv (2 + k)%nat) by lia.
destruct k as [|[|k]]; [| | lia].
+ change (2 + 0)%nat with 2%nat. rewrite le_byte_wh_2 by lia. reflexivity.
+ change (2 + 1)%nat with 3%nat. rewrite le_byte_wh_3 by lia. reflexivity.
Qed.
Lemma val_mem_wh_join : forall m a W H,
val_mem segs m a 2 W -> val_mem segs m (a + 2) 2 H -> 0 <= W < 65536 -> 0 <= H < 65536 ->
val_mem segs m a 4 (W + 65536 * H).
Proof.
intros m a W H HvW HvH HW HH k Hk.
destruct k as [|[|[|[|k]]]]; [| | | | lia].
- rewrite (HvW 0%nat) by lia. rewrite le_byte_wh_0 by lia. reflexivity.
- rewrite (HvW 1%nat) by lia. rewrite le_byte_wh_1 by lia. reflexivity.
- replace (a + Z.of_nat 2) with (a + 2 + Z.of_nat 0) by lia. rewrite (HvH 0%nat) by lia. rewrite le_byte_wh_2 by lia. reflexivity.
- replace (a + Z.of_nat 3) with (a + 2 + Z.of_nat 1) by lia. rewrite (HvH 1%nat) by lia. rewrite le_byte_wh_3 by lia. reflexivity.
Qed.
Lemma val_mem_low_of_chunk : forall E mem base off (n : N) (e : sv),
chunk_ok segs E mem base (mkChunk off (CVal n e)) -> (Z.of_N n <= 8) ->
val_mem segs mem (base + off) (N.to_nat n) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n)).
Proof.
intros E mem base off n e H Hn k Hk. unfold chunk_ok in H. cbn [c_off c_val c_len cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1.
unfold byte_of_word in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
unfold le_byte. rewrite N_nat_Z. rewrite Z.mod_mod by lia.
set (v := bv_unsigned (sv_denot E e)).
rewrite !Z.shiftr_div_pow2 by lia.
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hm8|Hm8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.div_pow2_bits by lia.
assert (Hlt : m + 8 * Z.of_nat k < 8 * Z.of_N n) by nia.
rewrite !(Z.mod_pow2_bits_low _ _ _ Hlt). reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma obj_at_app : forall mem a l1 l2 v1 v2,
length v1 = length l1 ->
obj_at segs mem a (l1 ++ l2) (v1 ++ v2) <-> obj_at segs mem a l1 v1 /\ obj_at segs mem a l2 v2.
Proof.
intros mem a l1. induction l1 as [|f l1 IH]; intros l2 [|x v1] v2 Hlen; cbn in Hlen |- *; try lia; [tauto|].
rewrite IH by lia. tauto.
Qed.
Definition lay_shift (d : Z) (lay : layout_t) : layout_t := map (fun f => (d + fst f, snd f)) lay.
Lemma obj_at_shift : forall mem a d lay vals,
obj_at segs mem (a + d) lay vals <-> obj_at segs mem a (lay_shift d lay) vals.
Proof.
intros mem a d lay. induction lay as [|f lay IH]; intros [|v vals]; cbn; try tauto.
unfold field_ok. cbn [fst snd]. rewrite Z.add_assoc. rewrite IH. tauto.
Qed.
Lemma chunk_present : forall E mem base c i,
chunk_ok segs E mem base c -> 0 <= i < c_len c -> exists b, mbyte segs mem (base + c_off c + i) = Some b.
Proof. intros E mem base c i H Hi. destruct (H i Hi) as (b & _ & Hb). exists b. exact Hb. Qed.
Lemma st_region_chunks : forall E ss ms i rg p a,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p -> bv_unsigned (ew E p) = a ->
Forall (chunk_ok segs E (ms_mem ms) a) (r_chunks rg).
Proof.
intros E ss ms i rg p a HS Hi Hb Hp.
pose proof (mem_ok_region segs E (ms_mem ms) (ss_mem ss) rg (st_ok_mem_ok segs E ss ms HS) ltac:(eapply nth_error_In; exact Hi)) as HR.
destruct HR as (_ & _ & _ & Hcs). rewrite Hb in Hcs. cbn [base_val] in Hcs. rewrite Hp in Hcs. exact Hcs.
Qed.
Lemma st_obj_at : forall E ss ms i rg p a lay vals k lits,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p -> bv_unsigned (ew E p) = a ->
incl (obj_chunks_gen lay k lits) (r_chunks rg) -> lay_widths_ok lay = true -> length vals = length lay ->
(forall j v, nth_error vals j = Some v ->
0 <= v < 2 ^ (8 * Z.of_N (snd (nth j lay (0, 8%N)))) /\
match nth_error lits j with Some (Some z) => z = v | _ => ew E (k + j) = Z_to_bv 64 v end) ->
obj_at segs (ms_mem ms) a lay vals.
Proof.
intros E ss ms i rg p a lay vals k lits HS Hi Hb Hp Hincl Hw Hlen HV.
eapply obj_at_of_chunks_gen; [| exact Hw | exact Hlen | exact HV].
eapply incl_Forall; [exact Hincl|]. eapply st_region_chunks; eauto.
Qed.
Lemma region_kept_gen : forall E (mem mem' : word -> option byte) r,
(forall a, base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
mem_grows mem mem' -> r_lo r <= r_wlo r -> r_whi r <= r_hi r ->
region_kept segs E mem mem' r.
Proof.
intros E mem mem' r Hsame Hgr Hw1 Hw2. split; intros a Ha.
- unfold mbyte. rewrite (Hsame a Ha). reflexivity.
- apply (writable_at_grows segs mem mem'); assumption.
Qed.
Lemma region_kept_out : forall E (mem mem' : word -> option byte) r d n,
(forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> mem' x = mem x) ->
mem_grows mem mem' ->
0 <= base_val E (r_base r) + r_lo r -> base_val E (r_base r) + r_hi r <= 2 ^ 64 ->
(forall a, base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r -> a < d \/ d + n <= a) ->
r_lo r <= r_wlo r -> r_whi r <= r_hi r ->
region_kept segs E mem mem' r.
Proof.
intros E mem mem' r d n Hout Hgr Hlo Hhi Hdis Hw1 Hw2. apply region_kept_gen; [|exact Hgr|exact Hw1|exact Hw2].
intros a Ha. apply Hout. rewrite unsigned_lit_small by lia. apply Hdis. exact Ha.
Qed.
End h.
Definition cval_eqb (a b : cval) : bool :=
match a, b with
| CVal w v, CVal w' v' => N.eqb w w' && sv_eqb v v'
| CZero n, CZero n' => Z.eqb n n'
| CImg n, CImg n' => Z.eqb n n'
| CData d s n, CData d' s' n' => Nat.eqb d d' && Z.eqb s s' && Z.eqb n n'
| _, _ => false
end.
Lemma cval_eqb_eq : forall a b, cval_eqb a b = true -> a = b.
Proof.
intros [w v|n|n|d s0 n] [w' v'|n'|n'|d' s' n'] H; cbn in H; try discriminate.
- apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1. apply sv_eqb_eq in H2. subst. reflexivity.
- apply Z.eqb_eq in H. subst. reflexivity.
- apply Z.eqb_eq in H. subst. reflexivity.
- apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.
Definition chunk_eqb (a b : YP09.chunk) : bool := Z.eqb (c_off a) (c_off b) && cval_eqb (c_val a) (c_val b).
Lemma chunk_eqb_eq : forall a b, chunk_eqb a b = true -> a = b.
Proof.
intros [oa va] [ob vb] H. unfold chunk_eqb in H. cbn in H. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply cval_eqb_eq in H2. subst. reflexivity.
Qed.
Definition incl_chunks (l1 l2 : list YP09.chunk) : bool :=
forallb (fun c => existsb (chunk_eqb c) l2) l1.
Lemma incl_chunks_sound : forall l1 l2, incl_chunks l1 l2 = true -> incl l1 l2.
Proof.
intros l1 l2 H c Hc. pose proof (proj1 (forallb_forall _ _) H c Hc) as Hx. cbn beta in Hx.
apply existsb_exists in Hx as (c' & Hin & Heq). apply chunk_eqb_eq in Heq. subst. exact Hin.
Qed.
Section l.
Variable segs : list Segment.
Definition lay_covers (lay : layout_t) (sz : nat) : bool :=
forallb (fun i => existsb (fun f => (fst f <=? Z.of_nat i) && (Z.of_nat i <? fst f + Z.of_N (snd f))) lay) (seq 0 sz).
Lemma obj_at_readable : forall mem a lay vals (sz : nat),
obj_at segs mem a lay vals -> lay_covers lay sz = true ->
forall i, 0 <= i < Z.of_nat sz -> exists b, mbyte segs mem (a + i) = Some b.
Proof.
intros mem a lay vals sz Hobj Hcov i Hi.
pose proof (proj1 (forallb_forall _ _) Hcov (Z.to_nat i) ltac:(apply in_seq; lia)) as Hx. cbn beta in Hx.
apply existsb_exists in Hx as (f & Hf & Hr). apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
rewrite Z2Nat.id in H1, H2 by lia.
destruct (In_nth_error _ _ Hf) as [j Hj].
pose proof (obj_at_length _ _ _ _ _ Hobj) as Hlen.
destruct (nth_error vals j) as [v|] eqn:Hv.
2:{ exfalso. apply nth_error_None in Hv. assert (j < length lay)%nat by (apply nth_error_Some; rewrite Hj; discriminate). lia. }
destruct (obj_at_nth _ _ _ _ _ _ _ _ Hobj Hj Hv) as [Hval _].
pose proof (Hval (Z.to_nat (i - fst f)) ltac:(pose proof (N_nat_Z (snd f)); lia)) as Hb.
rewrite Z2Nat.id in Hb by lia. replace (a + fst f + (i - fst f)) with (a + i) in Hb by lia.
eexists. exact Hb.
Qed.
End l.
Section q.
Variable segs : list Segment.
Lemma st_chunk_val : forall E ss ms i rg p off (n : N) e a v,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CVal n e)) (r_chunks rg) ->
bv_unsigned (ew E p) = a -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem segs (ms_mem ms) (a + off) (N.to_nat n) v.
Proof.
intros E ss ms i rg p off n e a v HS Hi Hb Hin Hp He Hv Hn.
pose proof (st_region_chunks segs E ss ms i rg p a HS Hi Hb Hp) as Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
exact (val_of_chunk_ok segs E (ms_mem ms) a off n e v Hc He Hv Hn).
Qed.
Lemma val_mem_zero : forall m a n,
(forall i, 0 <= i < Z.of_nat n -> mbyte segs m (a + i) = Some (Z_to_bv 8 0)) -> val_mem segs m a n 0.
Proof.
intros m a n H k Hk. rewrite H by lia. f_equal. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma st_chunk_zero_val : forall E ss ms i rg p off len a o n,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CZero len)) (r_chunks rg) ->
bv_unsigned (ew E p) = a -> off <= o -> o + Z.of_nat n <= off + len ->
val_mem segs (ms_mem ms) (a + o) n 0.
Proof.
intros E ss ms i rg p off len a o n HS Hi Hb Hin Hp Ho1 Ho2. apply val_mem_zero. intros j Hj.
pose proof (st_region_chunks segs E ss ms i rg p a HS Hi Hb Hp) as Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
destruct (Hc (o - off + j) ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [cbyte c_val c_off] in Hb1, Hb2. injection Hb1 as <-.
replace (a + o + j) with (a + off + (o - off + j)) by lia. exact Hb2.
Qed.
End q.
Section t.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Lemma blocks_range : forall L A mem md a n,
heap_ok MR L A mem md -> In (a, n) (blocks L A) -> 4096 <= a /\ a + n <= alloc_ceiling.
Proof.
intros L A mem md a n (HM & _) Hin. apply blocks_In in Hin as (p & <- & Hin).
exact (mr_blocks_range B MR LAWS L A mem md p n HM Hin).
Qed.
Lemma present_mbyte : forall (m : word -> option byte) a, present m a -> exists b, mbyte (ms_segs B) m a = Some b.
Proof. intros m a [b Hb]. exists b. unfold mbyte. rewrite Hb. reflexivity. Qed.
End t.
End g.
