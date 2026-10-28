(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK0s YK15 YK18 YP0m YP09 YI04 YI00 YI16.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbq YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AD1y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Local Notation segs := tfibsegs.
Lemma owned_off : forall lo hi a, forallb (ext_avoids lo hi) Tfib_owned_static = true -> lo <= a < hi ->
~ Exists (in_zr a) (as_owned_static B).
Proof. intros lo hi a Hc Ha. rewrite (ts_owned B HB). exact (ext_avoids_sound lo hi _ a Hc Ha). Qed.
Lemma const_abs_in : forall ly c, In c Tfib_const_abs -> In c (as_const B ly).
Proof. intros ly c Hc. rewrite (ts_const B HB). unfold Tfib_const. apply in_app_iff. right. apply in_app_iff. left. exact Hc. Qed.
Ltac in_list := cbn; repeat (first [left; reflexivity | right]).
Ltac kcst := unfold A_threaded, A_need_locks, A_ofl_lock, A_ofl_head, A_PATH, A_WB, A_RWA, A_TRAILER, FF_canary, FF_got_canary,
FF_meta_ptr, FF_meta_mem, A_stdio_read, A_stdio_write, A_stdio_seek, A_stdio_close in *.
Lemma tfib_AIL : asink_img_laws segs B tfib_K.
Proof.
pose proof (ts_errno B HB) as EE. unfold TFIB_ERRNO in EE.
constructor.
- reflexivity.
- intros a Ha. unfold aenv_addr in Ha. cbn -[Z.add Z.lt Z.le] in Ha. kcst.
split; [apply in_img_hull; lia|]. split; [| rewrite EE; lia].
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]].
+ apply (owned_off A_threaded (A_threaded + 1)); [vm_compute; reflexivity | kcst; lia].
+ apply (owned_off A_need_locks (A_need_locks + 1)); [vm_compute; reflexivity | kcst; lia].
+ apply (owned_off A_ofl_lock (A_ofl_lock + 16)); [vm_compute; reflexivity | kcst; lia].
+ apply (owned_off A_PATH (A_PATH + 13)); [vm_compute; reflexivity | kcst; lia].
+ apply (owned_off A_WB (A_WB + 3)); [vm_compute; reflexivity | kcst; lia].
+ apply (owned_off A_RWA (A_RWA + 4)); [vm_compute; reflexivity | kcst; lia].
+ apply (owned_off A_TRAILER (A_TRAILER + 2)); [vm_compute; reflexivity | kcst; lia].
+ apply (owned_off FF_canary (FF_canary + 8)); [vm_compute; reflexivity | kcst; lia].
- intros a Ha. unfold aenv_addr, ak_ofl_head in *. cbn -[Z.add Z.lt Z.le] in Ha. cbn -[Z.add Z.lt Z.le]. kcst. lia.
- intros a Ha. unfold ak_ofl_head in *. cbn -[Z.add Z.lt Z.le] in Ha. cbn -[Z.add Z.lt Z.le]. kcst. lia.
- intros ly. apply const_abs_in. in_list.
- intros a Ha. unfold ak_ofl_head in *. cbn -[Z.add Z.lt Z.le] in Ha. cbn -[Z.add Z.lt Z.le]. kcst.
split; [apply in_img_hull; lia|]. split; [apply (owned_off FF_meta_mem (FF_meta_mem + 8)); [vm_compute; reflexivity | kcst; lia]|]. rewrite EE. lia.
- intros ly. apply const_abs_in. in_list.
- intros a Ha. rewrite EE in Ha. apply in_img_hull. lia.
- intros ly c Hc. cbn in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; apply const_abs_in; in_list.
Qed.
Definition FINV (ly : alayout) (H : word -> bool) (mem : word -> option byte) : Prop :=
(exists M, ameta_inv segs tfib_K ly (mrestrict H mem) M) /\
astdio_env segs tfib_K (mrestrict H mem) /\
val_mem segs (mrestrict H mem) A_ofl_head 8 0.
Definition finv_img (a : Z) : Prop :=
(FF_meta_ptr <= a < FF_meta_ptr + 16) \/ aenv_addr tfib_K a \/ (A_ofl_head <= a < A_ofl_head + 8).
Definition FINV_IVS : list (Z * Z) :=
[(FF_meta_ptr, FF_meta_ptr + 16); (A_RWA, A_RWA + 4); (A_PATH, A_PATH + 13); (A_WB, A_WB + 3); (A_TRAILER, A_TRAILER + 2);
(FF_canary, FF_canary + 8); (A_threaded, A_threaded + 1); (A_need_locks, A_need_locks + 1); (A_ofl_lock, A_ofl_lock + 16)].
Lemma finv_img_ivs : forall a, finv_img a -> exists lo hi, In (lo, hi) FINV_IVS /\ lo <= a < hi.
Proof.
intros a Ha. unfold finv_img, aenv_addr, ak_ofl_head in Ha. cbn -[Z.add Z.lt Z.le] in Ha. unfold FINV_IVS.
assert (MM : FF_meta_mem = FF_meta_ptr + 8) by reflexivity. assert (OH : A_ofl_head = A_ofl_lock + 8) by reflexivity.
destruct Ha as [Ha|[[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]|Ha]];
[ exists FF_meta_ptr, (FF_meta_ptr + 16) | exists A_threaded, (A_threaded + 1) | exists A_need_locks, (A_need_locks + 1)
| exists A_ofl_lock, (A_ofl_lock + 16) | exists A_PATH, (A_PATH + 13) | exists A_WB, (A_WB + 3) | exists A_RWA, (A_RWA + 4)
| exists A_TRAILER, (A_TRAILER + 2) | exists FF_canary, (FF_canary + 8) | exists A_ofl_lock, (A_ofl_lock + 16) ];
(split; [cbn; tauto | lia]).
Qed.
Definition ivs_avoid (lo hi : Z) : bool := forallb (fun iv => (hi <=? fst iv) || (snd iv <=? lo))%bool FINV_IVS.
Lemma ivs_avoid_sound : forall lo hi a, ivs_avoid lo hi = true -> lo <= a < hi -> ~ finv_img a.
Proof.
intros lo hi a Hc Ha Hf. destruct (finv_img_ivs a Hf) as (l & h & Hin & Hlh).
pose proof (proj1 (forallb_forall _ _) Hc (l, h) Hin) as X. cbn [fst snd] in X.
apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
Qed.
Lemma ivs_avoid_sub : forall lo hi lo' hi', ivs_avoid lo hi = true -> lo <= lo' -> hi' <= hi -> ivs_avoid lo' hi' = true.
Proof.
intros lo hi lo' hi' Hc H1 H2. unfold ivs_avoid in *. apply forallb_forall. intros iv Hiv.
pose proof (proj1 (forallb_forall _ _) Hc iv Hiv) as X. apply orb_prop in X as [X|X]; apply Z.leb_le in X; apply orb_true_intro; [left | right]; apply Z.leb_le; lia.
Qed.
Lemma FINV_IVS_img : forallb (fun iv => (0x10000 <=? fst iv) && (snd iv <=? 0x5fb000))%bool FINV_IVS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma finv_img_range : forall a, finv_img a -> 0x10000 <= a < 0x5fb000.
Proof.
intros a Hf. destruct (finv_img_ivs a Hf) as (l & h & Hin & Hlh).
pose proof (proj1 (forallb_forall _ _) FINV_IVS_img (l, h) Hin) as X. cbn [fst snd] in X. apply andb_prop in X as [X1 X2].
apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.
Lemma finv_img_img : forall a, finv_img a -> in_img segs a.
Proof. intros a Ha. apply in_img_hull. exact (finv_img_range a Ha). Qed.
Lemma FINV_IVS_unowned : forallb (fun iv => forallb (ext_avoids (fst iv) (snd iv)) Tfib_owned_static) (tl FINV_IVS ++ [(FF_meta_mem, FF_meta_mem + 8)]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma finv_img_not_owned : forall a, finv_img a -> ~ (FF_meta_ptr <= a < FF_meta_ptr + 8) -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros a Ha Hnp. destruct (finv_img_ivs a Ha) as (l & h & Hin & Hlh).
assert (CASE : In (l, h) (tl FINV_IVS ++ [(FF_meta_mem, FF_meta_mem + 8)]) \/ (FF_meta_mem <= a < FF_meta_mem + 8)).
{ cbn [FINV_IVS tl] in Hin |- *. destruct Hin as [E | Hin].
- right. injection E as <- <-. unfold FF_meta_mem, FF_meta_ptr in *. lia.
- left. apply in_app_iff. left. exact Hin. }
destruct CASE as [Hin' | Hm].
- pose proof (proj1 (forallb_forall _ _) FINV_IVS_unowned (l, h) Hin') as X. cbn [fst snd] in X. exact (owned_off l h a X Hlh).
- assert (Hin' : In (FF_meta_mem, FF_meta_mem + 8) (tl FINV_IVS ++ [(FF_meta_mem, FF_meta_mem + 8)])) by (apply in_app_iff; right; left; reflexivity).
pose proof (proj1 (forallb_forall _ _) FINV_IVS_unowned _ Hin') as X. cbn [fst snd] in X. exact (owned_off _ _ a X Hm).
Qed.
Lemma FINV_IVS_drvw : forallb (fun d => ivs_avoid (fst d) (snd d)) DRV_IVS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma finv_img_not_drvw : forall a, finv_img a -> DRVW a = true -> False.
Proof.
intros a Ha Hw. unfold DRVW in Hw. apply existsb_exists in Hw as (d & Hd & Hb). apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (proj1 (forallb_forall _ _) FINV_IVS_drvw d Hd) as X. exact (ivs_avoid_sound (fst d) (snd d) a X ltac:(lia) Ha).
Qed.
Lemma FINV_IVS_errno : ivs_avoid TFIB_ERRNO (TFIB_ERRNO + 4) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma finv_img_not_errno : forall a, finv_img a -> ~ (as_errno B <= a < as_errno B + 4).
Proof. intros a Ha He. rewrite (ts_errno B HB) in He. exact (ivs_avoid_sound _ _ a FINV_IVS_errno He Ha). Qed.
Lemma finv_frame : forall ly H H' (mem mem' : word -> option byte),
(forall a, finv_img a \/ Exists (in_zr a) (ly_extra ly) -> mbyte segs (mrestrict H' mem') a = mbyte segs (mrestrict H mem) a) ->
FINV ly H mem -> FINV ly H' mem'.
Proof.
intros ly H H' mem mem' Hfr ((M & HX & Himg & Hok) & Henv & Hhead). split; [|split].
- exists M. split; [exact HX|]. split; [exact Himg|].
apply (ameta_ok_frame segs tfib_K (mrestrict H mem)); [|exact Hok].
intros a Ha. apply Hfr. cbn -[Z.add Z.lt Z.le] in Ha. destruct Ha as [Ha|[Ha|Ha]].
+ left. unfold finv_img. kcst. lia.
+ left. unfold finv_img. kcst. lia.
+ right. apply Exists_exists. exists (M, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
- apply (astdio_env_frame segs tfib_K (mrestrict H mem)); [|exact Henv]. intros a Ha. apply Hfr. left. right. left. exact Ha.
- eapply val_mem_frame; [|exact Hhead]. intros a Ha. apply Hfr. left. right. right. cbn in Ha. lia.
Qed.
Lemma finv_aview : forall ly H H' (mem mem' : word -> option byte),
(forall a, finv_img a \/ Exists (in_zr a) (ly_extra ly) -> aview segs H' mem' a = aview segs H mem a) ->
FINV ly H mem -> FINV ly H' mem'.
Proof. intros ly H H' mem mem' Hfr HF. apply (finv_frame ly H H' mem mem'); [|exact HF]. intros a Ha. apply mbyte_of_aview. exact (Hfr a Ha). Qed.
Lemma finv_lyle : forall n ly ly' H mem, layout_le n ly ly' -> FINV ly H mem -> FINV ly' H mem.
Proof.
intros n ly ly' H mem Hle ((M & HX & Himg & Hok) & Henv & Hhead).
pose proof Hle as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
split; [| exact (conj Henv Hhead)]. exists M. split; [rewrite Eextra; exact HX | exact (conj Himg Hok)].
Qed.
Lemma extra_place : forall ly S W mem md a, AR segs B ly S W mem md -> Exists (in_zr a) (ly_extra ly) ->
~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_img segs a /\ ~ aowned B ly S a /\
(forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n)).
Proof.
intros ly S W mem md a HAR HX. destruct (AR_extra_law_ok segs B ly S W mem md a HAR HX) as (Ho & Hb & _ & Hs & Hi & _). tauto.
Qed.
Lemma finv_stretch : forall ly S W mem0 md (H : word -> bool) E rs (m m' : word -> option byte) usp,
AR segs B ly S W mem0 md ->
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb drv_win_ok rs = true -> bv_unsigned (ew E 0) = usp ->
ly_stk_lo ly <= usp - 65536 -> usp <= ly_stk_hi ly -> sp_window_lo <= usp ->
FINV ly H m -> FINV ly H m'.
Proof.
intros ly S W mem0 md H E rs m m' usp HAR HF Hok E0 Hlo Hhi Husp HFI. apply (finv_frame ly H H m m'); [|exact HFI].
intros a Ha. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. intros Hw.
apply (in_wrange_drv E rs) in Hw; [|exact Hok]. rewrite E0 in Hw.
assert (Hr : 0 <= a < 2 ^ 64).
{ destruct Ha as [Ha|Ha]; [pose proof (finv_img_range a Ha); lia|].
destruct (AR_extra_law_ok segs B ly S W mem0 md a HAR Ha) as (_ & _ & _ & _ & _ & _ & Happ).
pose proof (app_addr_below_ceil a Happ). pose proof (proj1 (@YG0f.ASAN_CEIL_range _)). lia. }
rewrite u64_lit in Hw by exact Hr.
destruct Ha as [Ha|Ha].
- pose proof (finv_img_range a Ha). destruct Hw as [Hw|Hw]; [unfold sp_window_lo in Husp; lia | exact (finv_img_not_drvw a Ha Hw)].
- destruct (extra_place ly S W mem0 md a HAR Ha) as (Hs & Hi & _). destruct Hw as [Hw|Hw]; [lia|].
apply Hi. apply in_img_rw. pose proof (DRVW_lo a Hw). lia.
Qed.
Lemma finv_acall_post : forall stk ly S W regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md',
AR segs B ly S W mem md ->
acall_post segs B stk ly S W regs mem md E ly' S' W' regs' mem' md' ->
(forall a, E a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(exists p n, In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n)) ->
ly_stk_lo ly <= spZ regs - stk -> spZ regs <= ly_stk_hi ly -> 2 ^ 24 <= spZ regs - stk ->
FINV ly (w_H W) mem -> FINV ly' (w_H W') mem'.
Proof.
intros stk ly S W regs mem md E ly' S' W' regs' mem' md' HAR HP HE Hlo Hhi H24 ((M & HX & Himg & Hok) & Henv & Hhead).
destruct HP as (HAR' & Hle & Hwle & Hregs & Hio & Hfr & Hpres).
pose proof Hle as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Estklo & Estkhi & _ & _ & Eextra & _).
pose proof (ts_errno B HB) as EE. unfold TFIB_ERRNO in EE.
assert (HX' : In (M, AMETA_SIZE) (ly_extra ly')) by (rewrite Eextra; exact HX).
assert (FR : forall a, (finv_img a /\ ~ (FF_meta_ptr <= a < FF_meta_ptr + 8)) \/ Exists (in_zr a) (ly_extra ly) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
{ intros a Ha. destruct Ha as [[Ha Hnp] | Ha].
- pose proof (finv_img_range a Ha) as R. pose proof (finv_img_img a Ha) as Hi. pose proof (finv_img_not_owned a Ha Hnp) as Hns.
apply Hfr; [lia | | | |].
+ intros Ho. exact (Hns (proj1 (al_owned_image _ _ ARL ly S W mem md a HAR Hi) Ho)).
+ intros Ho. exact (Hns (proj1 (al_owned_image _ _ ARL ly' S' W' mem' md' a HAR' Hi) Ho)).
+ unfold ascratch. intros [Hsc | Her]; [lia | exact (finv_img_not_errno a Ha Her)].
+ intros Ea. destruct (HE a Ea) as [(p & n & Hin & Hpa) | (p & n & Hin & Hpa)].
* exact (proj2 (al_client_img _ _ ARL ly S W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa))))) Hi).
* exact (proj2 (al_client_img _ _ ARL ly' S' W' mem' md' a HAR' (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa))))) Hi).
- destruct (extra_place ly S W mem md a HAR Ha) as (Hs & Hi & Ho & Hb).
assert (Ha' : Exists (in_zr a) (ly_extra ly')) by (rewrite Eextra; exact Ha).
destruct (extra_place ly' S' W' mem' md' a HAR' Ha') as (_ & _ & Ho' & Hb').
destruct (AR_extra_law_ok segs B ly S W mem md a HAR Ha) as (_ & _ & _ & _ & _ & _ & Happ).
pose proof (app_addr_below_ceil a Happ). pose proof (proj1 (@YG0f.ASAN_CEIL_range _)).
apply Hfr; [lia | exact Ho | exact Ho' | |].
+ unfold ascratch. rewrite EE. intros [Hsc | Her]; [lia|]. apply Hi. apply in_img_hull. lia.
+ intros Ea. destruct (HE a Ea) as [(p & n & Hin & Hpa) | (p & n & Hin & Hpa)]; [exact (Hb p n Hin Hpa) | exact (Hb' p n Hin Hpa)]. }
split; [|split].
- exists M. split; [exact HX'|]. split; [exact Himg|].
destruct Hok as (Hp & Hm & H0 & H47 & Hal & HZ). split; [exact (ameta_ptr_of_AR segs B tfib_K tfib_AIL ly' S' W' mem' md' HAR')|].
split.
+ eapply val_mem_frame; [|exact Hm]. intros x Hx. apply mbyte_of_aview. apply FR. left. cbn -[Z.add Z.lt Z.le] in Hx. unfold finv_img. kcst. lia.
+ split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
intros a Ha. rewrite <- (HZ a Ha). apply mbyte_of_aview. apply FR. right.
apply Exists_exists. exists (M, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
- apply (astdio_env_frame segs tfib_K (mrestrict (w_H W) mem)); [|exact Henv].
intros a Ha. apply mbyte_of_aview. apply FR. left. split; [right; left; exact Ha|].
unfold aenv_addr in Ha. cbn -[Z.add Z.lt Z.le] in Ha. kcst. lia.
- eapply val_mem_frame; [|exact Hhead]. intros a Ha. apply mbyte_of_aview. apply FR. left. cbn in Ha. unfold finv_img. kcst. lia.
Qed.
Lemma finv_off : forall ly S W mem md (mem' : word -> option byte) (X1 X2 : Z -> Prop),
AR segs B ly S W mem md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ X1 a -> ~ X2 a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, finv_img a \/ Exists (in_zr a) (ly_extra ly) -> ~ X1 a /\ ~ X2 a) ->
FINV ly (w_H W) mem -> FINV ly (w_H W) mem'.
Proof.
intros ly S W mem md mem' X1 X2 HAR Hfr HX HF. apply (finv_aview ly (w_H W) (w_H W) mem mem'); [|exact HF].
intros a Ha. destruct (HX a Ha) as [H1 H2]. apply Hfr; [|exact H1|exact H2].
destruct Ha as [Ha|Ha]; [pose proof (finv_img_range a Ha); lia|].
destruct (AR_extra_law_ok segs B ly S W mem md a HAR Ha) as (_ & _ & _ & _ & _ & _ & Happ).
pose proof (app_addr_below_ceil a Happ). pose proof (proj1 (@YG0f.ASAN_CEIL_range _)). lia.
Qed.
Lemma finv_avoids_block : forall ly S W mem md p n a,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
finv_img a \/ Exists (in_zr a) (ly_extra ly) -> ~ (p <= a < p + req_size n).
Proof.
intros ly S W mem md p n a HAR Hin Ha Hpa. destruct Ha as [Ha|Ha].
- exact (proj2 (al_client_img _ _ ARL ly S W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa))))) (finv_img_img a Ha)).
- destruct (extra_place ly S W mem md a HAR Ha) as (_ & _ & _ & Hb). exact (Hb p n Hin Hpa).
Qed.
Lemma finv_avoids_stack : forall ly S W mem md lo hi a,
AR segs B ly S W mem md -> ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly -> 2 ^ 24 <= lo ->
finv_img a \/ Exists (in_zr a) (ly_extra ly) -> ~ (lo <= a < hi).
Proof.
intros ly S W mem md lo hi a HAR Hlo Hhi H24 Ha Hr. destruct Ha as [Ha|Ha].
- pose proof (finv_img_range a Ha). lia.
- destruct (extra_place ly S W mem md a HAR Ha) as (Hs & _). lia.
Qed.
Lemma finv_avoids_img : forall ly S W mem md lo hi a,
AR segs B ly S W mem md -> (forall x, lo <= x < hi -> in_img segs x) -> ivs_avoid lo hi = true ->
finv_img a \/ Exists (in_zr a) (ly_extra ly) -> ~ (lo <= a < hi).
Proof.
intros ly S W mem md lo hi a HAR Himg Hc Ha Hr. destruct Ha as [Ha|Ha].
- exact (ivs_avoid_sound lo hi a Hc Hr Ha).
- destruct (extra_place ly S W mem md a HAR Ha) as (_ & Hi & _). exact (Hi (Himg a Hr)).
Qed.
Lemma finv_fp_u64 : forall ly S W mem md a, AR segs B ly S W mem md ->
finv_img a \/ Exists (in_zr a) (ly_extra ly) -> 0 <= a < 2 ^ 64.
Proof.
intros ly S W mem md a HAR [Ha|Ha]; [pose proof (finv_img_range a Ha); lia|].
destruct (AR_extra_law_ok segs B ly S W mem md a HAR Ha) as (_ & _ & _ & _ & _ & _ & Happ).
pose proof (app_addr_below_ceil a Happ). pose proof (proj1 (@YG0f.ASAN_CEIL_range _)). lia.
Qed.
Lemma finv_img_write : forall ly S W mem0 md (H : word -> bool) (m m' : word -> option byte) lo hi,
AR segs B ly S W mem0 md ->
(forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> m' x = m x) ->
(forall x, lo <= x < hi -> in_img segs x) -> ivs_avoid lo hi = true ->
FINV ly H m -> FINV ly H m'.
Proof.
intros ly S W mem0 md H m m' lo hi HAR Hout Himg Hc HF. apply (finv_frame ly H H m m'); [|exact HF].
intros a Ha. pose proof (finv_fp_u64 ly S W mem0 md a HAR Ha) as Hr.
pose proof (finv_avoids_img ly S W mem0 md lo hi a HAR Himg Hc Ha) as Hna.
unfold mbyte, mrestrict. rewrite (Hout (Z_to_bv 64 a)) by (rewrite u64_lit by exact Hr; lia). reflexivity.
Qed.
End e.
End b.
