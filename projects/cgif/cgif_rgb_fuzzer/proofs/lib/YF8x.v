(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma st_ok_add_alias {imgk : img} : forall E ss ms (a b : sv),
st_ok tfxsegs E ss ms -> sv_denot E a = sv_denot E b ->
st_ok tfxsegs E (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss)
(mkFacts (f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) ((a, b) :: f_alias (ss_facts ss)))) ms.
Proof.
intros E ss ms a b (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & (G1 & G2 & G3)) Hab.
unfold st_ok; cbn. repeat (split; [img_try (assumption)|]). img_exact G3.
Qed.
Lemma st_ok_drop_regions {imgk : img} : forall E ss ms (pre rest : smem),
st_ok tfxsegs E ss ms -> ss_mem ss = pre ++ rest -> regions_wf rest = true ->
st_ok tfxsegs E (mkSS (ss_pc ss) (ss_regs ss) rest (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms pre rest HS Hm Hwf.
pose proof HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold st_ok; cbn. repeat (split; [img_try (assumption)|]). split; [| img_try (img_exact H9)].
rewrite Hm in H8. img_apply (mem_ok_sub tfxsegs E _ (pre ++ rest) rest); [| img_try (img_exact Hwf) | img_try (img_exact H8)].
clear. induction pre as [|r pre IH]; cbn; [img_try (img_apply submem_refl) | img_try (img_apply submem_drop; img_exact IH)].
Qed.
Lemma aview_range {imgk : img} : forall H mem a v, aview tfxsegs H mem a = Some v -> 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte tfxsegs (mrestrict H mem) a) as [b|]; [|img_try (discriminate)].
cbn in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as X. unfold bv_modulus in X. cbn in X. img_lia.
Qed.
Lemma rdword_range {imgk : img} : forall H mem a v, rdword (aview tfxsegs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview tfxsegs H mem a) as [b0|] eqn:E0; [|img_try (discriminate)].
destruct (aview tfxsegs H mem (a + 1)) as [b1|] eqn:E1; [|img_try (discriminate)].
destruct (aview tfxsegs H mem (a + 2)) as [b2|] eqn:E2; [|img_try (discriminate)].
destruct (aview tfxsegs H mem (a + 3)) as [b3|] eqn:E3; [|img_try (discriminate)].
destruct (aview tfxsegs H mem (a + 4)) as [b4|] eqn:E4; [|img_try (discriminate)].
destruct (aview tfxsegs H mem (a + 5)) as [b5|] eqn:E5; [|img_try (discriminate)].
destruct (aview tfxsegs H mem (a + 6)) as [b6|] eqn:E6; [|img_try (discriminate)].
destruct (aview tfxsegs H mem (a + 7)) as [b7|] eqn:E7; [|img_try (discriminate)].
injection Hw as <-.
pose proof (aview_range _ _ _ _ E0). pose proof (aview_range _ _ _ _ E1). pose proof (aview_range _ _ _ _ E2). pose proof (aview_range _ _ _ _ E3).
pose proof (aview_range _ _ _ _ E4). pose proof (aview_range _ _ _ _ E5). pose proof (aview_range _ _ _ _ E6). pose proof (aview_range _ _ _ _ E7).
img_lia.
Qed.
Lemma region_ok_window {imgk : img} : forall E (m : word -> option byte) n b lo hi wlo whi,
bv_unsigned (ew E n) = b -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
(forall a, b + wlo <= a < b + whi -> writable_at tfxsegs m a) ->
region_ok tfxsegs E m (YQ0b.mkRegion (Some n) lo hi wlo whi []).
Proof.
intros E m n b lo hi wlo whi Hn Hlo Hhi Hw. unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite Hn. split; [img_lia|]. split; [img_lia|]. split; [|img_try (constructor)]. intros o Ho. img_apply Hw. img_lia.
Qed.
Lemma region_ok_lit {imgk : img} : forall E (m : word -> option byte) a (w : N) v,
val_mem tfxsegs m a (N.to_nat w) v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 -> 0 <= a -> a + Z.of_N w <= 2 ^ 64 ->
region_ok tfxsegs E m (YQ0b.mkRegion None a (a + Z.of_N w) 0 0 [YQ0b.mkChunk a (CVal w (SLit v))]).
Proof.
intros E m a w v Hv Hr Hw Ha Hh. unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply chunk_ok_val; [img_refl | img_try (img_exact Hr) | img_try (img_exact Hw) | img_try (rewrite Z.add_0_l; img_exact Hv)].
Qed.
Lemma region_ok_atom8 {imgk : img} : forall E (m : word -> option byte) a k v,
val_mem tfxsegs m a 8 v -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
region_ok tfxsegs E m (atom8 a k).
Proof.
intros E m a k v Hv Hk Hr Ha Hh. unfold region_ok, atom8. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs E m 0 a 8 (SOff k 0) v); [| img_try (img_exact Hr) | img_try (cbn; img_lia) | img_try (rewrite Z.add_0_l; img_exact Hv)].
cbn [sv_denot]. rewrite Hk, unsigned_lit_small by img_exact Hr. f_equal. img_lia.
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
assert (X : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia.
clear Hr.
destruct X as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
{ replace (Z_to_bv 5 2) with (2%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
{ replace (Z_to_bv 5 3) with (3%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
{ replace (Z_to_bv 5 4) with (4%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
{ replace (Z_to_bv 5 8) with (8%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
{ replace (Z_to_bv 5 9) with (9%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
{ replace (Z_to_bv 5 18) with (18%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
{ replace (Z_to_bv 5 19) with (19%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
{ replace (Z_to_bv 5 20) with (20%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
{ replace (Z_to_bv 5 21) with (21%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
{ replace (Z_to_bv 5 22) with (22%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
{ replace (Z_to_bv 5 23) with (23%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
{ replace (Z_to_bv 5 24) with (24%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
{ replace (Z_to_bv 5 25) with (25%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
{ replace (Z_to_bv 5 26) with (26%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
{ replace (Z_to_bv 5 27) with (27%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). assumption. }
Qed.
Definition in_wrangeb (E : env) (rs : smem) (a : Z) : bool :=
existsb (fun r => (base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <=? a) && (a <? base_val E (YQ0b.r_base r) + YQ0b.r_whi r))%bool rs.
Lemma in_wrangeb_false : forall E rs a, in_wrangeb E rs a = false -> ~ in_wrange E rs a.
Proof.
intros E rs a H (r & Hin & Ha). unfold in_wrangeb in H.
assert (X : existsb (fun r => (base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <=? a) && (a <? base_val E (YQ0b.r_base r) + YQ0b.r_whi r))%bool rs = true).
{ img_apply existsb_exists. exists r. split; [img_try (img_exact Hin)|]. img_apply andb_true_iff. split; [img_try (img_apply Z.leb_le) | img_try (img_apply Z.ltb_lt)]; img_lia. }
rewrite X in H. discriminate H.
Qed.
Lemma in_wrangeb_true : forall E rs a, in_wrangeb E rs a = true ->
exists i r, nth_error rs i = Some r /\ base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r.
Proof.
intros E rs a H. unfold in_wrangeb in H. apply existsb_exists in H as (r & Hin & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
destruct (In_nth_error _ _ Hin) as [i Hi]. exists i, r. split; [img_try (img_exact Hi) | img_lia].
Qed.
Lemma in_wrange_of_windows : forall E rs rs' a, windows rs' = windows rs -> in_wrange E rs a -> in_wrange E rs' a.
Proof.
intros E rs rs' a Hw (r & Hin & Hr).
assert (X : In (YQ0b.r_base r, YQ0b.r_wlo r, YQ0b.r_whi r) (windows rs')).
{ rewrite Hw. unfold windows. img_exact (in_map (fun r0 => (YQ0b.r_base r0, YQ0b.r_wlo r0, YQ0b.r_whi r0)) rs r Hin). }
unfold windows in X. apply in_map_iff in X as (r' & Heq & Hin'). injection Heq as H1 H2 H3.
exists r'. split; [img_try (img_exact Hin')|]. rewrite H1, H2, H3. img_exact Hr.
Qed.

Lemma chunk_val_at {imgk : img} : forall (H : word -> bool) E ss ms i j r off (n : BinNums.N) e v a,
st_ok tfxsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YQ0b.r_chunks r) j = Some (YQ0b.mkChunk off (CVal n e)) ->
a = base_val E (YQ0b.r_base r) + off ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfxsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof. intros H E ss ms i j r off n e v a HS Hi Hj -> He Hv Hn. eapply st_ok_chunk_val; eassumption. Qed.
End c.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ img_refl | img_refl | cbn [base_val YQ0b.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := img_ev constr:(p) in img_change p with q end
| cbn; img_lia ]
end
end.
