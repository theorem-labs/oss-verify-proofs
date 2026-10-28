(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFhy.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma st_ok_add_alias : forall E ss ms (a b : sv),
st_ok tfibsegs E ss ms -> sv_denot E a = sv_denot E b ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss)
(mkFacts (f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) ((a, b) :: f_alias (ss_facts ss)))) ms.
Proof.
intros E ss ms a b (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & (G1 & G2 & G3)) Hab.
unfold st_ok; cbn. repeat (split; [assumption|]). exact G3.
Qed.
Lemma st_ok_drop_regions : forall E ss ms (pre rest : smem),
st_ok tfibsegs E ss ms -> ss_mem ss = pre ++ rest -> regions_wf rest = true ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) rest (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms pre rest HS Hm Hwf.
pose proof HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold st_ok; cbn. repeat (split; [assumption|]). split; [| exact H9].
rewrite Hm in H8. apply (mem_ok_sub tfibsegs E _ (pre ++ rest) rest); [| exact Hwf | exact H8].
clear. induction pre as [|r pre IH]; cbn; [apply submem_refl | apply submem_drop; exact IH].
Qed.
Lemma aview_range : forall H mem a v, aview tfibsegs H mem a = Some v -> 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as X. unfold bv_modulus in X. cbn in X. lia.
Qed.
Lemma rdword_range : forall H mem a v, rdword (aview tfibsegs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview tfibsegs H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview tfibsegs H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview tfibsegs H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview tfibsegs H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview tfibsegs H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview tfibsegs H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview tfibsegs H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview tfibsegs H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
pose proof (aview_range _ _ _ _ E0). pose proof (aview_range _ _ _ _ E1). pose proof (aview_range _ _ _ _ E2). pose proof (aview_range _ _ _ _ E3).
pose proof (aview_range _ _ _ _ E4). pose proof (aview_range _ _ _ _ E5). pose proof (aview_range _ _ _ _ E6). pose proof (aview_range _ _ _ _ E7).
lia.
Qed.
Lemma region_ok_window : forall E (m : word -> option byte) n b lo hi wlo whi,
bv_unsigned (ew E n) = b -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
(forall a, b + wlo <= a < b + whi -> writable_at tfibsegs m a) ->
region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi []).
Proof.
intros E m n b lo hi wlo whi Hn Hlo Hhi Hw. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hn. split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply Hw. lia.
Qed.
Lemma region_ok_lit : forall E (m : word -> option byte) a (w : N) v,
val_mem tfibsegs m a (N.to_nat w) v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 -> 0 <= a -> a + Z.of_N w <= 2 ^ 64 ->
region_ok tfibsegs E m (YP09.mkRegion None a (a + Z.of_N w) 0 0 [YP09.mkChunk a (CVal w (SLit v))]).
Proof.
intros E m a w v Hv Hr Hw Ha Hh. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | exact Hr | exact Hw | rewrite Z.add_0_l; exact Hv].
Qed.
Lemma region_ok_atom8 : forall E (m : word -> option byte) a k v,
val_mem tfibsegs m a 8 v -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
region_ok tfibsegs E m (atom8 a k).
Proof.
intros E m a k v Hv Hk Hr Ha Hh. unfold region_ok, atom8. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E m 0 a 8 (SOff k 0) v); [| exact Hr | cbn; lia | rewrite Z.add_0_l; exact Hv].
cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hr. f_equal. lia.
Qed.
Lemma regs_preserved_intro : forall regs regs' : bvmap 5 word,
getr regs' 2%bv = getr regs 2%bv ->
getr regs' 3%bv = getr regs 3%bv ->
getr regs' 4%bv = getr regs 4%bv ->
getr regs' 8%bv = getr regs 8%bv ->
getr regs' 9%bv = getr regs 9%bv ->
getr regs' 18%bv = getr regs 18%bv ->
getr regs' 19%bv = getr regs 19%bv ->
getr regs' 20%bv = getr regs 20%bv ->
getr regs' 21%bv = getr regs 21%bv ->
getr regs' 22%bv = getr regs 22%bv ->
getr regs' 23%bv = getr regs 23%bv ->
getr regs' 24%bv = getr regs 24%bv ->
getr regs' 25%bv = getr regs 25%bv ->
getr regs' 26%bv = getr regs 26%bv ->
getr regs' 27%bv = getr regs 27%bv ->
regs_preserved regs regs'.
Proof.
intros regs regs'. intros. intros r Hr. unfold callee_saved in Hr.
assert (X : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hr.
destruct X as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
{ replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
Qed.
Definition in_wrangeb (E : env) (rs : smem) (a : Z) : bool :=
existsb (fun r => (base_val E (YP09.r_base r) + YP09.r_wlo r <=? a) && (a <? base_val E (YP09.r_base r) + YP09.r_whi r))%bool rs.
Lemma in_wrangeb_false : forall E rs a, in_wrangeb E rs a = false -> ~ in_wrange E rs a.
Proof.
intros E rs a H (r & Hin & Ha). unfold in_wrangeb in H.
assert (X : existsb (fun r => (base_val E (YP09.r_base r) + YP09.r_wlo r <=? a) && (a <? base_val E (YP09.r_base r) + YP09.r_whi r))%bool rs = true).
{ apply existsb_exists. exists r. split; [exact Hin|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite X in H. discriminate H.
Qed.
Lemma in_wrangeb_true : forall E rs a, in_wrangeb E rs a = true ->
exists i r, nth_error rs i = Some r /\ base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r.
Proof.
intros E rs a H. unfold in_wrangeb in H. apply existsb_exists in H as (r & Hin & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
destruct (In_nth_error _ _ Hin) as [i Hi]. exists i, r. split; [exact Hi | lia].
Qed.
Lemma in_wrange_of_windows : forall E rs rs' a, windows rs' = windows rs -> in_wrange E rs a -> in_wrange E rs' a.
Proof.
intros E rs rs' a Hw (r & Hin & Hr).
assert (X : In (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r) (windows rs')).
{ rewrite Hw. unfold windows. exact (in_map (fun r0 => (YP09.r_base r0, YP09.r_wlo r0, YP09.r_whi r0)) rs r Hin). }
unfold windows in X. apply in_map_iff in X as (r' & Heq & Hin'). injection Heq as H1 H2 H3.
exists r'. split; [exact Hin'|]. rewrite H1, H2, H3. exact Hr.
Qed.
Lemma pres_after_run : forall (H : word -> bool) E ss' rs (ms ms' : machine_state),
st_ok tfibsegs E ss' (restrict H ms') -> frame_of E rs (ms_mem ms) (ms_mem ms') -> windows (ss_mem ss') = windows rs ->
(forall a, in_wrange E rs a -> TFIB_IMG_END <= a < 2 ^ 64) ->
forall a, apresent H (ms_mem ms) a -> apresent H (ms_mem ms') a.
Proof.
intros H E ss' rs ms ms' HS HF Hws Hhi a Ha.
set (x := Z_to_bv 64 a). assert (Ex : Z_to_bv 64 (bv_unsigned x) = x) by apply Z_to_bv_bv_unsigned.
destruct (in_wrangeb E (ss_mem ss') (bv_unsigned x)) eqn:Hb.
- destruct (in_wrangeb_true E _ _ Hb) as (i & r & Hi & Hr).
assert (P : apresent H (ms_mem ms') (bv_unsigned x)).
{ apply (st_ok_window_apresent H E ss' ms' i r _ HS Hi Hr). apply Hhi.
apply (in_wrange_of_windows E (ss_mem ss') rs); [symmetry; exact Hws|]. exists r. split; [exact (nth_error_In _ _ Hi) | exact Hr]. }
unfold apresent in P |- *. rewrite Ex in P. exact P.
- apply (apresent_same H (ms_mem ms)); [| exact Ha]. apply (HF x). intros Hw.
exact (in_wrangeb_false E _ _ Hb (in_wrange_of_windows E rs (ss_mem ss') _ Hws Hw)).
Qed.
Lemma chunk_val_at : forall (H : word -> bool) E ss ms i j r off (n : BinNums.N) e v a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal n e)) ->
a = base_val E (YP09.r_base r) + off ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof. intros H E ss ms i j r off n e v a HS Hi Hj -> He Hv Hn. eapply st_ok_chunk_val; eassumption. Qed.
End c.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ reflexivity | reflexivity | cbn [base_val YP09.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := eval vm_compute in p in change p with q end
| cbn; lia ]
end
end.
