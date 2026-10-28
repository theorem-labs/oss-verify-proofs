(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI1h
UI1i YP14 YI08 YI0c UI3h UI4v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Lemma optb_nz : forall p n, p <> 0 -> optb p n = [(p, n)].
Proof. intros p n Hp. unfold optb. rewrite (proj2 (Z.eqb_neq p 0) Hp). reflexivity. Qed.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma u64_range8 : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in H. lia. Qed.
Section e.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Lemma tmp_not_entry : forall Lc Ac memc mdc b n restb,
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) ((b, n) :: restb) ->
(forall x, In x (blocks L A) -> In x restb) -> 0 < n -> ~ In (b, n) (blocks L A).
Proof.
intros Lc Ac memc mdc b n restb HH HP Hsub Hn Hin. apply Hsub in Hin.
pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (b, n) restb (b, n) HH HP Hin) as Hs. cbn [fst snd] in Hs. lia.
Qed.
Lemma heap_sep_app' : forall Lc Ac memc mdc (l1 l2 : list (Z * Z)) x y,
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) (l1 ++ l2) -> In x l1 -> In y l2 ->
fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
intros Lc Ac memc mdc l1 l2 x y HH HP Hx Hy. destruct (in_split _ _ Hx) as (a & b & ->).
apply (heap_sep_perm _ _ LAWS Lc Ac memc mdc x (a ++ b ++ l2) y HH).
- eapply Permutation_trans; [exact HP|]. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
- apply in_app_iff. right. apply in_app_iff. right. exact Hy.
Qed.
Lemma tmp_of_station : forall Lc Ac memc mdc (keep tmp : list (Z * Z)) b n,
heap_ok MR Lc Ac memc mdc ->
Permutation (blocks Lc Ac) (keep ++ tmp) ->
Permutation (blocks L A) (BASE r g N img fmt rest s bef beffmt) ->
(forall x, In x (BASE r g N img fmt rest s bef beffmt) -> In x keep) ->
In (b, n) tmp -> 0 < n ->
In (b, n) (blocks Lc Ac) /\ ~ In (b, n) (blocks L A).
Proof.
intros Lc Ac memc mdc keep tmp b n HH HP HBe Hsub Hin Hn.
split; [eapply Permutation_in; [apply Permutation_sym; exact HP | apply in_app_iff; right; exact Hin]|].
apply in_split in Hin as (T1 & T2 & ->).
eapply (tmp_not_entry Lc Ac memc mdc b n (keep ++ T1 ++ T2)); [exact HH | | | exact Hn].
- eapply Permutation_trans; [exact HP|]. rewrite app_assoc. apply Permutation_sym.
replace (keep ++ T1 ++ T2) with ((keep ++ T1) ++ T2) by (rewrite app_assoc; reflexivity). apply Permutation_middle.
- intros x Hx. apply in_app_iff. left. apply Hsub. eapply Permutation_in; [exact HBe | exact Hx].
Qed.
Lemma kept_across_call : forall STK1 sp1 Lc Ac memc mdc L2 A2 mem2 md2 (keep tmp : list (Z * Z)),
heap_ok MR Lc Ac memc mdc ->
Permutation (blocks Lc Ac) (keep ++ tmp) ->
journal ubs2_msyms MR STK1 sp1 (blocks_fp tmp) Lc Ac memc mdc L2 A2 mem2 md2 ->
Permutation (blocks L2 A2) keep ->
forall b m i, In (b, m) keep -> 0 <= i < m -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs memc (b + i).
Proof.
intros STK1 sp1 Lc Ac memc mdc L2 A2 mem2 md2 keep tmp HH HP HJc HB2 b m i Hbm Hi.
pose proof HJc as (_ & _ & _ & Hblk & _).
apply (Hblk b m i).
- eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hbm.
- eapply Permutation_in; [apply Permutation_sym; exact HB2|]. exact Hbm.
- exact Hi.
- intros HF1. apply inFP_blocks_fp in HF1 as (b' & m' & Hbm' & Hab').
pose proof (heap_sep_app' Lc Ac memc mdc keep tmp (b, m) (b', m') HH HP Hbm Hbm') as Hsep. cbn [fst snd] in Hsep. lia.
Qed.
Lemma init_of_live_r : forall L2 A2 mem2 md2 l,
heap_ok MR L2 A2 mem2 md2 -> Permutation (blocks L2 A2) (BASE r g N img fmt rest s bef beffmt ++ l) -> st_init_done A2 = true.
Proof.
intros L2 A2 mem2 md2 l HH HB.
assert (Hin : In (r, RGB_SIZE) (blocks L2 A2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. left. reflexivity. }
apply blocks_In in Hin as (q & _ & Hq). exact (init_done_of_block A2 (q, RGB_SIZE) (proj1 (proj2 HH)) Hq).
Qed.
Lemma ra_saved_kept : forall (m m' : word -> option byte) lo,
ra_saved_ok regs0 m -> lo <= sp0 regs0 - 104 -> alloc_ceiling <= sp0 regs0 - 104 -> sp0 regs0 < 2 ^ 63 ->
(forall x, alloc_ceiling <= x < 2 ^ 64 -> lo <= x -> mbyte ubs2segs m' x = mbyte ubs2segs m x) ->
ra_saved_ok regs0 m'.
Proof.
intros m m' lo HR Hlo Hc H63 HK j rr Hj k Hk.
assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some RA_SAVED j)); congruence).
rewrite HK; [apply (HR j rr Hj); exact Hk | lia | lia].
Qed.
Lemma slot_kept : forall (m m' : word -> option byte) off v,
slot regs0 m off v -> 0 <= off -> alloc_ceiling <= sp regs0 -> sp regs0 + off + 8 <= 2 ^ 64 ->
(forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte ubs2segs m' x0 = mbyte ubs2segs m x0) ->
slot regs0 m' off v.
Proof. intros m m' off v Hs Hoff Hlo Hhi HI k Hk. rewrite HI; [apply Hs; exact Hk | lia | lia]. Qed.
Lemma slots_mid_kept : forall (m m' : word -> option byte) pnew fimg,
slots_mid regs0 cfp N m pnew fimg -> alloc_ceiling <= sp regs0 -> sp regs0 + RGBA_FRAME <= 2 ^ 64 ->
(forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> sp regs0 <= x0 -> mbyte ubs2segs m' x0 = mbyte ubs2segs m x0) ->
slots_mid regs0 cfp N m' pnew fimg.
Proof.
intros m m' pnew fimg (S1 & S2 & S3 & S4) Hlo Hhi HI. unfold RGBA_FRAME in Hhi.
unfold slots_mid, SL_N, SL_cfp, SL_new, SL_fimg in *.
repeat split; (eapply slot_kept; [eassumption | lia | exact Hlo | lia | exact HI]).
Qed.
Lemma chtq_ok_kept : forall (m m' : word -> option byte) C cnt pal,
chtq_ok m C cnt pal ->
(forall i, 0 <= i < CHT_SIZE -> mbyte ubs2segs m' (ch_c C + i) = mbyte ubs2segs m (ch_c C + i)) ->
(forall i, 0 <= i < 3 * ch_T C -> mbyte ubs2segs m' (ch_p C + i) = mbyte ubs2segs m (ch_p C + i)) ->
chtq_ok m' C cnt pal.
Proof.
intros m m' C cnt pal (Ho & Ha & Hl & Hin & Hlow) Kc Kp.
split; [|split; [|split; [exact Hl | split; [exact Hin | exact Hlow]]]].
- eapply (obj_at_transport_range ubs2segs _ _ _ _ _ CHT_SIZE); [exact Ho | reflexivity | exact Kc].
- eapply arr8_frame; [exact Ha|]. intros a Ha'. replace a with (ch_p C + (a - ch_p C)) by lia. apply Kp. lia.
Qed.
End e.
End d.
