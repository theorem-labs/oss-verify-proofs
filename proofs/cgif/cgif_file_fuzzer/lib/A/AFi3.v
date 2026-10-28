(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG03 YG07 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
if aGranted z then ret tt else spin 449860
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
Lemma amreal_pure {A R} : forall (m : M A) (f : A -> M R) s a s' (W : world tfibsegs) c Q,
m s = IRet (a, s') -> amreal tfibsegs (f a s') W c Q -> amreal tfibsegs (bind m f s) W c Q.
Proof. intros m f s a s' W c Q E H. unfold bind. rewrite E. cbn [ibind]. exact H. Qed.
Lemma bind_assoc_eq {A B C} : forall (m : M A) (f : A -> M B) (g : B -> M C) s,
bind (bind m f) g s = bind m (fun a => bind (f a) g) s.
Proof.
intros m f g s. unfold bind. generalize (m s). clear m. intros t.
induction t as [[a s1] | q snap k IH | pc | e]; cbn; try reflexivity.
f_equal. apply FunctionalExtensionality.functional_extensionality. intros b. apply IH.
Qed.
Lemma bind_cong {A R} : forall (m : M A) (f g : A -> M R) s, (forall a s', f a s' = g a s') -> bind m f s = bind m g s.
Proof.
intros m f g s H. unfold bind. f_equal. apply FunctionalExtensionality.functional_extensionality. intros [a s']. apply H.
Qed.
Lemma malloc_after_checks_eq : forall n trace s,
(ob <- (o <- cache_alloc (chunk_class n) ;; ret (match o with Some off => Some (PPrim off) | None => None end)) ;; malloc_K n trace ob) s
= (refill_tree (chunk_class n) ;; malloc_join n trace (chunk_class n)) s.
Proof.
intros n trace s. unfold cache_alloc, refill_tree, malloc_join, pop_part. rewrite !bind_assoc_eq.
apply bind_cong. intros a s1. cbv beta. rewrite !bind_assoc_eq. apply bind_cong. intros b s2. cbv beta. rewrite !bind_assoc_eq. reflexivity.
Qed.
Lemma malloc_primary_eq : forall n trace s, from_primary n = true ->
malloc n trace s = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) 202260   ;; refill_tree (chunk_class n) ;; malloc_join n trace (chunk_class n)) s.
Proof.
intros n trace s FP. unfold malloc, malloc_join, malloc_K, refill_tree, cache_alloc, pop_part. rewrite FP.
apply bind_cong. intros u1 s1. apply bind_cong. intros u2 s2. rewrite !bind_assoc_eq.
apply bind_cong. intros a s3. cbv beta. rewrite !bind_assoc_eq. apply bind_cong. intros b s4. cbv beta. rewrite !bind_assoc_eq. reflexivity.
Qed.
Lemma refill_tree_ready : forall c S, st_cache_inited S = true -> pc_chunks (cache S c) <> [] -> refill_tree c S = IRet (tt, S).
Proof.
intros c S Hi Hne. unfold refill_tree, init_cache_if_needed, refill_if_empty, get_pc, bind, get, ret, put. cbn [ibind]. rewrite Hi. cbn [ibind].
change (znth pclass0 c (st_cache S)) with (cache S c). destruct (pc_chunks (cache S c)) as [|x t]; [exfalso; apply Hne; reflexivity|]. reflexivity.
Qed.
Lemma pop_hit : forall S cl l off, pc_chunks (cache S cl) = l ++ [off] ->
pop_part cl S = IRet (Some (region_off cl + off), st_popped S cl l).
Proof.
intros S cl l off Hcache. unfold pop_part, get_pc, set_pc, bind, get, ret, modify. cbn [ibind].
change (znth pclass0 cl (st_cache S)) with (cache S cl). rewrite Hcache.
destruct (l ++ [off]) as [|x t] eqn:El; [destruct l; discriminate|]. cbn [ibind].
rewrite <- El, last_last, removelast_last'. reflexivity.
Qed.
Lemma pop_miss : forall S cl, pc_chunks (cache S cl) = [] -> pop_part cl S = IRet (None, S).
Proof.
intros S cl Hc. unfold pop_part, get_pc, bind, get, ret. cbn [ibind]. change (znth pclass0 cl (st_cache S)) with (cache S cl). rewrite Hc. reflexivity.
Qed.
Lemma ARm_tick : forall B ly S rd, ARm B ly S rd -> aregime S -> ARm B ly (set_nev (st_nev S + 1) S) rd.
Proof.
intros B ly S rd M Hev. destruct M. constructor; try assumption.
unfold Wf. eapply WfP_weaken; [exact (WfP_tick _ S am_wf Hev) | lia | lia | lia].
Qed.
Lemma AR_tick : forall B ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md -> aregime S ->
AR tfibsegs B ly (set_nev (st_nev S + 1) S) W mem md.
Proof.
intros B ly S W mem md (M & L & BUD & MW & HS) Hev. split; [exact (ARm_tick B ly S _ M Hev)|].
split; [destruct L; constructor; assumption|].
split; [|split; [exact MW | exact HS]].
destruct BUD as [BUD PIN]. split; [| exact PIN].
unfold abudget in *. cbn [st_nev set_nev]. change (sec_live_bytes (set_nev (st_nev S + 1) S)) with (sec_live_bytes S).
change (sec_hulls (set_nev (st_nev S + 1) S)) with (sec_hulls S)  . unfold EV_A in *. lia.
Qed.
Lemma shadow_apart : forall g x y, g mod 8 = 0 -> 0 <= g -> 0 <= x -> (g + 8 <= x \/ y <= g) ->
shadow_addr g + 1 <= shadow_addr x \/ SHADOW_OFF + y / 8 <= shadow_addr g.
Proof.
intros g x y Hg H0 Hx HD. unfold shadow_addr. apply Z.mod_divide in Hg as [q Hq]; [|lia]. subst g. rewrite Z.div_mul by lia.
destruct HD as [HD|HD].
- left. assert (q + 1 <= x / 8) by (apply Z.div_le_lower_bound; lia). lia.
- right. assert (y / 8 <= q * 8 / 8) by (apply Z.div_le_mono; lia). rewrite Z.div_mul in H by lia. lia.
Qed.
Lemma cache_alloc_hit : forall S cl l off, st_cache_inited S = true -> pc_chunks (cache S cl) = l ++ [off] ->
cache_alloc cl S = IRet (Some (region_off cl + off), set_cache (zupd cl (mkPC (pc_max (cache S cl)) l) (st_cache S)) S).
Proof.
intros S cl l off Hinit Hcache.
cbn [cache_alloc bind init_cache_if_needed get ret ibind]. rewrite Hinit.
cbn [bind get ret ibind refill_if_empty get_pc set_pc modify put].
change (znth pclass0 cl (st_cache S)) with (cache S cl). rewrite Hcache.
destruct (l ++ [off]) as [|x t] eqn:El; [destruct l; discriminate|]. cbn [ret ibind].
change (znth pclass0 cl (st_cache S)) with (cache S cl). rewrite Hcache. cbn [bind set_pc modify ret ibind].
rewrite <- El, last_last, removelast_last'. reflexivity.
Qed.
Lemma amreal_atok {R} : forall (t : itree astate R) ns (P : bool -> R -> Prop) (W : world tfibsegs) c (Q : R -> world tfibsegs -> config -> Prop),
atok ns t P -> amreal tfibsegs t W c (fun r W' c' => (exists ns', P ns' r) -> Q r W' c') -> amreal tfibsegs t W c Q.
Proof.
induction t as [r | q snap k IH | pc | f]; intros ns P W c Q AT AM; cbn in *.
- eapply SRr_mono; [exact AM|]. intros W' c' _ H. apply H. exists ns. exact AT.
- destruct AT as [_ Hk]. eapply SRr_mono; [exact AM|]. intros W1 c1 _ H. cbv beta in H.
destruct q;
try (destruct H as (z & Hz & H); exists z; split; [exact Hz|]; eapply IH; [exact (Hk z Hz) | exact H]);
(destruct H as (I & nx & bit & sp & i0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8); exists I, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; eapply IH; [apply Hk; apply N3 | exact (N8 i Hi)]).
- exact AM.
- exact AM.
Qed.
End d.
