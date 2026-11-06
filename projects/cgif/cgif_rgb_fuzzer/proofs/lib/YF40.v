(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG03 YG07 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Open Scope am_scope.
Definition st_popped (S : astate) (cl : Z) (l : list Z) : astate :=
set_cache (zupd cl (mkPC (pc_max (cache S cl)) l) (st_cache S)) S.
Definition pop_part (c : Z) : M (option Z) :=
p <- get_pc c ;;
match pc_chunks p with
| [] => ret None
| l => let off := last l 0 in
set_pc c (mkPC (pc_max p) (removelast l)) ;;
ret (Some (region_off c + off))
end.
Definition malloc_K (n : Z) (trace : list Z) (ob : option sptr) : M sptr :=
match ob with
| None => ret PNull
| Some beg =>
depot_put trace ;;
let k := mkChunk beg n CAllocated in
(if needs_remap (ck_n k) then
z <- askz (KShadowRemap (ck_user k) (8 * (ck_n k / 8))) ;;
if aGranted z then ret tt else spin 449796
else ret tt) ;;
modify (fun s => set_chunks (upd_chunk (st_chunks s) k) s) ;;
ret (ck_user k)
end.
Definition malloc_join (n : Z) (trace : list Z) (c : Z) : M sptr :=
ob <- (o <- pop_part c ;; ret (match o with Some off => Some (PPrim off) | None => None end)) ;;
malloc_K n trace ob.
Definition new_chunk (cl off n : Z) : chunk := mkChunk (PPrim (region_off cl + off)) n CAllocated.
Definition st_final (S : astate) (cl : Z) (l : list Z) (off n : Z) (tr : list Z) (z : Z) : astate :=
let s1 := depot_after z tr (st_popped S cl l) in
set_chunks (upd_chunk (st_chunks s1) (new_chunk cl off n)) s1.
Lemma amreal_pure {imgk : img} {A R} : forall (m : M A) (f : A -> M R) s a s' (W : world tfxsegs) c Q,
m s = IRet (a, s') -> amreal tfxsegs (f a s') W c Q -> amreal tfxsegs (bind m f s) W c Q.
Proof. intros m f s a s' W c Q E H. unfold bind. rewrite E. cbn [ibind]. img_exact H. Qed.
Lemma bind_assoc_eq {A B C} : forall (m : M A) (f : A -> M B) (g : B -> M C) s,
bind (bind m f) g s = bind m (fun a => bind (f a) g) s.
Proof.
intros m f g s. unfold bind. generalize (m s). clear m. intros t.
induction t as [[a s1] | q snap k IH | pc | e]; cbn; try img_refl.
f_equal. img_apply FunctionalExtensionality.functional_extensionality. intros b. img_apply IH.
Qed.
Lemma bind_cong {A R} : forall (m : M A) (f g : A -> M R) s, (forall a s', f a s' = g a s') -> bind m f s = bind m g s.
Proof.
intros m f g s H. unfold bind. f_equal. img_apply FunctionalExtensionality.functional_extensionality. intros [a s']. img_apply H.
Qed.

Lemma malloc_primary_eq : forall n trace s, from_primary n = true ->
malloc n trace s = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) 202196   ;; refill_tree (chunk_class n) ;; malloc_join n trace (chunk_class n)) s.
Proof.
intros n trace s FP. unfold malloc, malloc_join, malloc_K, refill_tree, cache_alloc, pop_part. rewrite FP.
img_apply bind_cong. intros u1 s1. img_apply bind_cong. intros u2 s2. rewrite !bind_assoc_eq.
img_apply bind_cong. intros a s3. cbv beta. rewrite !bind_assoc_eq. img_apply bind_cong. intros b s4. cbv beta. rewrite !bind_assoc_eq. img_refl.
Qed.
Lemma refill_tree_ready : forall c S, st_cache_inited S = true -> pc_chunks (cache S c) <> [] -> refill_tree c S = IRet (tt, S).
Proof.
intros c S Hi Hne. unfold refill_tree, init_cache_if_needed, refill_if_empty, get_pc, bind, get, ret, put. cbn [ibind]. rewrite Hi. cbn [ibind].
img_change (znth pclass0 c (st_cache S)) with (cache S c). destruct (pc_chunks (cache S c)) as [|x t]; [img_try (exfalso; img_apply Hne; img_refl)|]. img_refl.
Qed.
Lemma pop_hit : forall S cl l off, pc_chunks (cache S cl) = l ++ [off] ->
pop_part cl S = IRet (Some (region_off cl + off), st_popped S cl l).
Proof.
intros S cl l off Hcache. unfold pop_part, get_pc, set_pc, bind, get, ret, modify. cbn [ibind].
img_change (znth pclass0 cl (st_cache S)) with (cache S cl). rewrite Hcache.
destruct (l ++ [off]) as [|x t] eqn:El; [img_try (destruct l; discriminate)|]. cbn [ibind].
rewrite <- El, last_last, removelast_last'. img_refl.
Qed.
Lemma pop_miss : forall S cl, pc_chunks (cache S cl) = [] -> pop_part cl S = IRet (None, S).
Proof.
intros S cl Hc. unfold pop_part, get_pc, bind, get, ret. cbn [ibind]. img_change (znth pclass0 cl (st_cache S)) with (cache S cl). rewrite Hc. img_refl.
Qed.
Lemma ARm_tick : forall B ly S rd, ARm B ly S rd -> aregime S -> ARm B ly (set_nev (st_nev S + 1) S) rd.
Proof.
intros B ly S rd M Hev. destruct M. constructor; try assumption.
unfold Wf. eapply WfP_weaken; [img_try (img_exact (WfP_tick _ S am_wf Hev)) | img_lia | img_lia | img_lia].
Qed.
Lemma AR_tick {imgk : img} : forall B ly S (W : world tfxsegs) mem md, AR tfxsegs B ly S W mem md -> aregime S ->
AR tfxsegs B ly (set_nev (st_nev S + 1) S) W mem md.
Proof.
intros B ly S W mem md (M & L & BUD & MW & HS) Hev. split; [img_try (img_exact (ARm_tick B ly S _ M Hev))|].
split; [img_try (destruct L; constructor; assumption)|].
split; [|img_try (split; [img_exact MW | img_exact HS])].
destruct BUD as [BUD PIN]. split; [| img_try (img_exact PIN)].
unfold abudget in *. cbn [st_nev set_nev]. img_change (sec_live_bytes (set_nev (st_nev S + 1) S)) with (sec_live_bytes S).
img_change (sec_hulls (set_nev (st_nev S + 1) S)) with (sec_hulls S)  . unfold EV_A in *. img_lia.
Qed.
Lemma shadow_apart : forall g x y, g mod 8 = 0 -> 0 <= g -> 0 <= x -> (g + 8 <= x \/ y <= g) ->
shadow_addr g + 1 <= shadow_addr x \/ SHADOW_OFF + y / 8 <= shadow_addr g.
Proof.
intros g x y Hg H0 Hx HD. unfold shadow_addr. apply Z.mod_divide in Hg as [q Hq]; [|img_lia]. (subst g; cbv beta). rewrite Z.div_mul by img_lia.
destruct HD as [HD|HD].
- left. assert (q + 1 <= x / 8) by (img_try (img_apply Z.div_le_lower_bound; img_lia)). img_lia.
- right. assert (y / 8 <= q * 8 / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). rewrite Z.div_mul in H by img_lia. img_lia.
Qed.

Lemma amrealE_atok {imgk : img} {R} : forall (t : itree astate R) ns (P : bool -> R -> Prop) (W : world tfxsegs) c (Q : R -> world tfxsegs -> config -> Prop),
atok ns t P -> amrealE tfxsegs t W c (fun r W' c' => (exists ns', P ns' r) -> Q r W' c') -> amrealE tfxsegs t W c Q.
Proof.
induction t as [r | q snap k IH | pc | f]; intros ns P W c Q AT AM; cbn in *.
- eapply SRrF_mono; [img_try (img_exact AM)|]. intros W' c' _ H. img_apply H. exists ns. img_exact AT.
- destruct AT as [_ Hk]. eapply SRrF_mono; [img_try (img_exact AM)|]. intros W1 c1 _ H. cbv beta in H.
destruct q;
try (destruct H as (z & Hz & H); exists z; split; [img_try (img_exact Hz)|]; eapply IH; [img_try (img_exact (Hk z Hz)) | img_try (img_exact H)]);
(destruct H as (I & nx & bit & sp & i0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8); exists I, nx, bit, sp, i0;
repeat (split; [img_try (assumption)|]); intros i Hi; eapply IH; [img_try (img_apply Hk; img_apply N3) | img_try (img_exact (N8 i Hi))]).
- img_exact AM.
- img_exact AM.
Qed.
Lemma amreal_atok {imgk : img} {R} : forall (t : itree astate R) ns (P : bool -> R -> Prop) (W : world tfxsegs) c (Q : R -> world tfxsegs -> config -> Prop),
atok ns t P -> amreal tfxsegs t W c (fun r W' c' => (exists ns', P ns' r) -> Q r W' c') -> amreal tfxsegs t W c Q.
Proof.
induction t as [r | q snap k IH | pc | f]; intros ns P W c Q AT AM; cbn in *.
- eapply SRr_mono; [img_try (img_exact AM)|]. intros W' c' _ H. img_apply H. exists ns. img_exact AT.
- destruct AT as [_ Hk]. eapply SRr_mono; [img_try (img_exact AM)|]. intros W1 c1 _ H. cbv beta in H.
destruct q;
try (destruct H as (z & Hz & H); exists z; split; [img_try (img_exact Hz)|]; eapply IH; [img_try (img_exact (Hk z Hz)) | img_try (img_exact H)]);
(destruct H as (I & nx & bit & sp & i0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N9 & N8); exists I, nx, bit, sp, i0;
repeat (split; [img_try (assumption)|]); intros i Hi; specialize (N8 i Hi); destruct (Z.eqb (bit i) 1);
[eapply IH; [img_try (img_apply Hk; img_apply N3) | img_try (img_exact N8)]
|eapply amrealE_atok; [img_try (img_apply Hk; img_apply N3) | img_try (img_exact N8)]]).
- img_exact AM.
- img_exact AM.
Qed.
End d.
