(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA0q.v, with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition shadow_rd (segs : list Segment) (H : word -> bool) (mem : word -> option byte) : Z -> option Z :=
fun a => option_map (fun b : byte => bv_unsigned b) (mbyte segs (mrestrict H mem) a).
Lemma shadow_rd_hsub : forall segs (H H' : word -> bool) mem,
H_off_segments segs H -> hsub H' H -> rd_ext (shadow_rd segs H mem) (shadow_rd segs H' mem).
Proof.
intros segs H H' mem HH Hs c v Hv. unfold shadow_rd in *.
destruct (mbyte segs (mrestrict H mem) c) as [b|] eqn:Hb; [|discriminate].
rewrite (mbyte_mrestrict_hsub segs H H' mem c b HH Hs Hb). exact Hv.
Qed.
Lemma shadow_rd_byte : forall segs H mem c v,
shadow_rd segs H mem c = Some v -> mbyte segs (mrestrict H mem) c = Some (Z_to_bv 8 v) /\ 0 <= v < 256.
Proof.
intros segs H mem c v Hv. unfold shadow_rd in Hv.
destruct (mbyte segs (mrestrict H mem) c) as [b|]; [|discriminate]. cbn in Hv. injection Hv as <-.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [f_equal; symmetry; apply Z_to_bv_bv_unsigned | lia].
Qed.
Definition zdisj (a b : Z * Z) : Prop := snd a <= fst b \/ snd b <= fst a.
Fixpoint zall_disjoint (a : Z * Z) (l : list (Z * Z)) : Prop :=
match l with [] => True | b :: l' => zdisj a b /\ zall_disjoint a l' end.
Fixpoint zpairwise_disjoint (l : list (Z * Z)) : Prop :=
match l with [] => True | a :: l' => zall_disjoint a l' /\ zpairwise_disjoint l' end.
Definition shadow_decl (p b s : nat) : sv * sv :=
(SAlu ALU_ADD (SAlu ALU_SRL (SOff p 0) (SLit 3)) (SOff b 0), SOff s 0).
Section d. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Definition extent_of_region (E : env) (r : YP09.region) : Z * Z :=
(base_val E (YP09.r_base r) + YP09.r_lo r, base_val E (YP09.r_base r) + YP09.r_hi r).
Lemma all_disjoint_of_extents : forall E r rs,
zall_disjoint (extent_of_region E r) (map (extent_of_region E) rs) -> all_disjoint E r rs.
Proof.
intros E r rs. induction rs as [|r' rs IH]; cbn; intros H; [exact I|].
destruct H as [H1 H2]. split; [|exact (IH H2)].
unfold extent_of_region, zdisj in H1. cbn in H1. unfold extent_disjoint. lia.
Qed.
Lemma pairwise_disjoint_of_extents : forall E rs,
zpairwise_disjoint (map (extent_of_region E) rs) -> pairwise_disjoint E rs.
Proof.
intros E rs. induction rs as [|r rs IH]; cbn; intros H; [exact I|].
destruct H as [H1 H2]. split; [exact (all_disjoint_of_extents E r rs H1) | exact (IH H2)].
Qed.
Lemma chunk_ok_zero_shadow : forall (H : word -> bool) mem E B p len Sv off,
zero_shadow (shadow_rd segs H mem) B p len ->
Sv + off = B + p / 8 ->
chunk_ok segs E (mrestrict H mem) Sv (YP09.mkChunk off (CZero (len / 8))).
Proof.
intros H mem E B p len Sv off Hz Heq. apply chunk_ok_zero. intros i Hi.
destruct (shadow_rd_byte segs H mem (shadow_of_addr B p + i) 0 (Hz i Hi)) as [Hb _].
unfold shadow_of_addr in Hb. rewrite Heq. exact Hb.
Qed.
Lemma chunks_ok_block_shadow : forall (H : word -> bool) mem E B p n Sv,
block_shadow (shadow_rd segs H mem) B p n ->
Sv = B + p / 8 ->
Forall (chunk_ok segs E (mrestrict H mem) Sv)
(YP09.mkChunk 0 (CZero (n / 8)) ::
if n mod 8 =? 0 then [] else [YP09.mkChunk (n / 8) (CVal 1 (SLit (n mod 8)))]).
Proof.
intros H mem E B p n Sv (Hp & Hn & Hc) ->.
pose proof (Z.div_mod n 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hmb.
assert (Hq : 0 <= n / 8) by (apply Z.div_pos; lia).
constructor.
- apply chunk_ok_zero. intros i Hi.
assert (Hi' : 0 <= i < (n + 7) / 8).
{ split; [lia|]. apply Z.lt_le_trans with (m := n / 8); [lia|]. apply Z.div_le_mono; lia. }
pose proof (Hc i Hi') as Hci. replace (i <? n / 8) with true in Hci by (symmetry; apply Z.ltb_lt; lia).
destruct (shadow_rd_byte segs H mem _ 0 Hci) as [Hb _]. unfold shadow_of_addr in Hb.
rewrite Z.add_0_r. exact Hb.
- destruct (n mod 8 =? 0) eqn:Hz; [constructor|]. apply Z.eqb_neq in Hz.
constructor; [|constructor]. intros i Hi. cbn [YP09.c_off YP09.c_val c_len cv_len Z.of_N cbyte] in Hi |- *.
assert (Hi0 : i = 0) by lia. subst i. rewrite Z.add_0_r.
assert (Hlast : 0 <= n / 8 < (n + 7) / 8).
{ assert (n / 8 + 1 <= (n + 7) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
pose proof (Hc (n / 8) Hlast) as Hcl. replace (n / 8 <? n / 8) with false in Hcl by (symmetry; apply Z.ltb_irrefl).
destruct (shadow_rd_byte segs H mem _ _ Hcl) as [Hb _]. unfold shadow_of_addr in Hb.
exists (Z_to_bv 8 (n mod 8)). split; [|exact Hb].
cbn [sv_denot]. unfold YP09.byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
reflexivity.
Qed.
Lemma range_addressable_of_zero_chunk : forall (H : word -> bool) mem E B p Sv off k,
chunk_ok segs E (mrestrict H mem) Sv (YP09.mkChunk off (CZero k)) ->
Sv + off = B + p / 8 -> p mod 8 = 0 -> 0 <= k ->
range_addressable (shadow_rd segs H mem) B p (8 * k).
Proof.
intros H mem E B p Sv off k Hc Heq Hp Hk.
apply zero_shadow_range; [exact Hp | rewrite Z.mul_comm; apply Z_mod_mult |].
intros i Hi. rewrite (Z.mul_comm 8 k), Z.div_mul in Hi by lia.
destruct (Hc i ltac:(cbn [YP09.c_off YP09.c_val c_len cv_len]; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2. injection Hb1 as <-.
unfold shadow_rd, shadow_of_addr. rewrite <- Heq. rewrite Hb2. reflexivity.
Qed.
Definition windows (rs : smem) : list (option nat * Z * Z) :=
map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs.
Lemma in_wrange_windows : forall E rs a,
in_wrange E rs a ->
exists b wlo whi, In (b, wlo, whi) (windows rs) /\ base_val E b + wlo <= a < base_val E b + whi.
Proof.
intros E rs a (r & Hin & Hr). exists (YP09.r_base r), (YP09.r_wlo r), (YP09.r_whi r).
split; [|exact Hr]. unfold windows.
exact (in_map (fun r0 => (YP09.r_base r0, YP09.r_wlo r0, YP09.r_whi r0)) rs r Hin).
Qed.
Definition win_eqb (t u : option nat * Z * Z) : bool :=
match t, u with
| (b1, l1, h1), (b2, l2, h2) => obase_eqb b1 b2 && (l1 =? l2) && (h1 =? h2)
end.
Lemma win_eqb_eq : forall t u, win_eqb t u = true -> t = u.
Proof.
intros [[b1 l1] h1] [[b2 l2] h2] H. cbn in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst.
destruct b1 as [x|], b2 as [y|]; cbn in H1; try discriminate; [|reflexivity].
apply Nat.eqb_eq in H1. subst. reflexivity.
Qed.
Lemma in_wrange_single_b : forall E rs a n wlo whi spv,
forallb (fun t => win_eqb t (Some n, wlo, whi) || (snd t <=? snd (fst t))) (windows rs) = true ->
bv_unsigned (ew E n) = spv ->
in_wrange E rs a -> spv + wlo <= a < spv + whi.
Proof.
intros E rs a n wlo whi spv Hb Hn Hin.
destruct (in_wrange_windows E rs a Hin) as (b & lo & hi & Ht & Hr).
rewrite forallb_forall in Hb. specialize (Hb _ Ht). apply orb_prop in Hb as [Hb|Hb].
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. rewrite Hn in Hr. exact Hr.
- cbn [fst snd] in Hb. apply Z.leb_le in Hb. lia.
Qed.
Lemma in_wrange_single : forall E rs a n wlo whi spv,
(forall t, In t (windows rs) -> t = (Some n, wlo, whi) \/ snd t <= snd (fst t)) ->
bv_unsigned (ew E n) = spv ->
in_wrange E rs a -> spv + wlo <= a < spv + whi.
Proof.
intros E rs a n wlo whi spv Hw Hn Hin.
destruct (in_wrange_windows E rs a Hin) as (b & lo & hi & Ht & Hr).
destruct (Hw _ Ht) as [Heq | Hempty].
- injection Heq as -> -> ->. cbn [base_val] in Hr. rewrite Hn in Hr. exact Hr.
- cbn [fst snd] in Hempty. lia.
Qed.
End d.
Ltac simp_off0 v :=
lazymatch v with
| context C [Z_to_bv 64 (bv_unsigned ?w + 0)] => let t := context C [w] in simp_off0 t
| _ => v
end.
Ltac rreg HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let v := eval cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in (sv_denot E e) in
let v := simp_off0 v in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (Hr : getr rg r = v)
by (refine (eq_trans (st_ok_restrict_reg segs H E ss ms r HS) _);
change (sv_denot E e = v);
cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity)
end.
Ltac zside := cbn [Z.of_N N.to_nat Pos.to_nat Z.mul Pos.mul Pos.iter_op Nat.add Nat.mul]; lia.
Ltac zdisj_pairwise H :=
cbn [zpairwise_disjoint zall_disjoint] in H |- *; unfold zdisj in H |- *; cbn [fst snd] in H |- *;
let rec par H :=
lazymatch type of H with
| _ /\ _ => let H1 := fresh "D" in let H2 := fresh "D" in destruct H as [H1 H2]; split; [par H1 | par H2]
| True => exact I
| _ => revert H; repeat match goal with K : _ |- _ => clear K end; intros H; lia
end in par H.
