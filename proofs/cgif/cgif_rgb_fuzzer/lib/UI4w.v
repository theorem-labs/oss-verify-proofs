(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p YK1j.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI07
UI1e UI1i UI57 YI0x YP14 YI08 YI0c YI0g YI0f YI0d
UI3h UI4v UIZm.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Lemma ubs2_find_segment_high : forall a n, 0x60000 <= a -> 0 < n -> find_segment ubs2segs a n = None.
Proof.
intros a n Ha Hn. destruct (find_segment ubs2segs a n) as [sg|] eqn:Hf; [|reflexivity]. exfalso.
pose proof (find_segment_in _ _ _ _ Hf) as Hin. pose proof (find_segment_range _ _ _ _ Hf) as [Hlo Hhi].
assert (Hall : forallb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? 0x60000) ubs2segs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hall sg Hin) as Hb. cbn beta in Hb. apply Z.leb_le in Hb. lia.
Qed.
Lemma ubs2_writable_high_present : forall (m : word -> option byte) a,
0x60000 <= a < 2 ^ 64 -> writable_at ubs2segs m a -> present m a.
Proof.
intros m a Ha Hw. unfold writable_at, wview in Hw. unfold present.
destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|]. exfalso. apply Hw.
rewrite unsigned_lit_small by lia. rewrite ubs2_find_segment_high by lia. reflexivity.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation BASEv := (BASE r g N img fmt rest s bef beffmt).
Local Notation FPv := (FPfoot r g bef beffmt s N).
Local Notation spv := (sp regs0).
Local Notation sp0v := (sp0 regs0).
Lemma qfacts_kept : forall (m m' : word -> option byte) ha pnew fimg imgl C cnt pal t,
alloc_ceiling + RGBA_STK <= sp0v -> sp0v < 2 ^ 63 -> (fmt = 3 \/ fmt = 4) ->
(forall x, alloc_ceiling <= x < 2 ^ 64 -> spv <= x -> ~ (spv + OFF_apal <= x < spv + OFF_apal + 768) -> mbyte ubs2segs m' x = mbyte ubs2segs m x) ->
(forall b n i, In (b, n) (BASEv ++ cht_blks C ++ tree_blocks t) -> 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs m (b + i)) ->
(ra_saved_ok regs0 m -> ra_saved_ok regs0 m') /\
(slots_mid regs0 cfp N m pnew fimg -> slots_mid regs0 cfp N m' pnew fimg) /\
(slots_q regs0 W bef beffmt img fmt fattr m ha -> slots_q regs0 W bef beffmt img fmt fattr m' ha) /\
(fcfg_at regs0 fattr delay m fimg 0 0 -> fcfg_at regs0 fattr delay m' fimg 0 0) /\
(rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur m -> rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur m') /\
(cgif_at m g s -> cgif_at m' g s) /\
(img_at N img fmt m imgl -> img_at N img fmt m' imgl) /\
(chtq_ok m C cnt pal -> chtq_ok m' C cnt pal) /\
(tree_ok m t -> tree_ok m' t).
Proof.
intros m m' ha pnew fimg imgl C cnt pal t Hceil H63 Hfmt KH KB.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (KF : forall lo hi, 0 <= lo -> hi <= OFF_apal \/ (OFF_apal + 768 <= lo /\ hi <= RGBA_FRAME) ->
forall x, spv + lo <= x < spv + hi -> mbyte ubs2segs m' x = mbyte ubs2segs m x).
{ intros lo hi Hlo Hhi x Hx. apply KH; unfold OFF_apal, sp, sp0, RGBA_FRAME in *; lia. }
assert (KS : forall off v, 0 <= off -> off + 8 <= OFF_apal -> slot regs0 m off v -> slot regs0 m' off v).
{ intros off v Ho1 Ho2 Hs k Hk. rewrite (KF off (off + 8) Ho1 ltac:(lia)) by lia. apply Hs. exact Hk. }
assert (KB' : forall b n, In (b, n) (BASEv ++ cht_blks C ++ tree_blocks t) -> forall i, 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs m (b + i)).
{ intros b n Hbn i Hi. exact (KB b n i Hbn Hi). }
split. { intros HR j rr Hj k Hk. assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some RA_SAVED j)); congruence).
rewrite KH; [apply (HR j rr Hj); exact Hk | unfold sp, sp0, RGBA_FRAME, OFF_apal in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, OFF_apal, RGBA_FRAME in *; lia]. }
split. { intros (S1 & S2 & S3 & S4). unfold slots_mid, SL_N, SL_cfp, SL_new, SL_fimg in *.
repeat split; (eapply KS; [| |eassumption]; unfold OFF_apal; lia). }
split. { intros ((S1 & S2 & S3 & S4 & S5) & S6 & S7). unfold slots_q, slots_h, SL_64, SL_88, SL_104, SL_112, SL_120, SL_32, SL_40 in *.
repeat split; (eapply KS; [| |eassumption]; unfold OFF_apal; lia). }
split. { intros Hf. eapply obj_at_transport; [exact Hf|]. intros f i Hf' Hi. unfold LAY_FrameConfig in Hf'. cbv [In] in Hf'.
repeat (destruct Hf' as [<-|Hf']; [cbn [fst snd] in *; apply (KF OFF_fcfg OFF_apal); unfold OFF_fcfg, OFF_apal; lia|]). destruct Hf'. }
split. { intros Ho. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Ho | reflexivity |]. apply KB'. apply in_app_iff. left. left. reflexivity. }
split. { intros Hc. eapply (cgif_at_kept _ _ g s N (cgif_blocks g s N) []); [rewrite app_nil_r; apply Permutation_refl | exact Hc |].
intros b n i Hbn Hi. apply (KB b n i); [|exact Hi]. apply in_app_iff. left. right. apply in_app_iff. left. exact Hbn. }
split. { intros [Ha Hl]. split; [|exact Hl]. eapply arr8_frame; [exact Ha|]. intros a Hx. replace a with (img + (a - img)) by lia.
apply (KB' img (fmt * N)); [|lia]. apply in_app_iff. left. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
unfold img_block. replace (fmt_okb fmt) with true; [left; reflexivity|]. unfold fmt_okb. destruct Hfmt as [-> | ->]; reflexivity. }
split. { intros Hq. eapply chtq_ok_kept; [exact Hq | |].
- apply KB'. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
- apply KB'. apply in_app_iff. right. apply in_app_iff. left. right. right. right. right. left. reflexivity. }
intros (Ht & Hfull & Hh & Hwf' & Hmo & Hnd). split; [|split; [exact Hfull | split; [exact Hh | split; [exact Hwf' | split; [exact Hmo | exact Hnd]]]]].
eapply tree_at_frame; [exact Ht|]. intros n a Hn Ha. replace a with (tn_addr n + (a - tn_addr n)) by lia.
apply (KB' (tn_addr n) NODE_SIZE); [|lia]. apply in_app_iff. right. apply in_app_iff. right. apply tree_blocks_in_nodes. exists n. auto.
Qed.
Lemma qfacts_kept_di : forall (m m' : word -> option byte) pnew fimg imgl C cnt pal t,
alloc_ceiling + RGBA_STK <= sp0v -> sp0v < 2 ^ 63 -> (fmt = 3 \/ fmt = 4) ->
(forall x, alloc_ceiling <= x < 2 ^ 64 -> spv <= x -> ~ (spv + OFF_apal <= x < spv + OFF_apal + 768) -> ~ (spv + SL_104 <= x < spv + SL_120) ->
 mbyte ubs2segs m' x = mbyte ubs2segs m x) ->
(forall b n i, In (b, n) (BASEv ++ cht_blks C ++ tree_blocks t) -> 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs m (b + i)) ->
(ra_saved_ok regs0 m -> ra_saved_ok regs0 m') /\
(slots_mid regs0 cfp N m pnew fimg -> slots_mid regs0 cfp N m' pnew fimg) /\
(forall off v, 0 <= off -> off + 8 <= SL_104 -> slot regs0 m off v -> slot regs0 m' off v) /\
(fcfg_at regs0 fattr delay m fimg 0 0 -> fcfg_at regs0 fattr delay m' fimg 0 0) /\
(rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur m -> rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur m') /\
(cgif_at m g s -> cgif_at m' g s) /\
(img_at N img fmt m imgl -> img_at N img fmt m' imgl) /\
(chtq_ok m C cnt pal -> chtq_ok m' C cnt pal) /\
(tree_ok m t -> tree_ok m' t).
Proof.
intros m m' pnew fimg imgl C cnt pal t Hceil H63 Hfmt KH KB.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (KF : forall lo hi, 0 <= lo -> hi <= SL_104 \/ (SL_120 <= lo /\ hi <= OFF_apal) \/ (OFF_apal + 768 <= lo /\ hi <= RGBA_FRAME) ->
forall x, spv + lo <= x < spv + hi -> mbyte ubs2segs m' x = mbyte ubs2segs m x).
{ intros lo hi Hlo Hhi x Hx. apply KH; unfold OFF_apal, SL_104, SL_120, sp, sp0, RGBA_FRAME in *; lia. }
assert (KS : forall off v, 0 <= off -> off + 8 <= SL_104 -> slot regs0 m off v -> slot regs0 m' off v).
{ intros off v Ho1 Ho2 Hs k Hk. rewrite (KF off (off + 8) Ho1 ltac:(lia)) by lia. apply Hs. exact Hk. }
assert (KB' : forall b n, In (b, n) (BASEv ++ cht_blks C ++ tree_blocks t) -> forall i, 0 <= i < n -> mbyte ubs2segs m' (b + i) = mbyte ubs2segs m (b + i)).
{ intros b n Hbn i Hi. exact (KB b n i Hbn Hi). }
split. { intros HR j rr Hj k Hk. assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some RA_SAVED j)); congruence).
rewrite KH; [apply (HR j rr Hj); exact Hk|..]; unfold sp, sp0, RGBA_FRAME, OFF_apal, SL_104, SL_120 in *; lia. }
split. { intros (S1 & S2 & S3 & S4). unfold slots_mid, SL_N, SL_cfp, SL_new, SL_fimg in *.
repeat split; (eapply KS; [| |eassumption]; unfold SL_104; lia). }
split; [exact KS|].
split. { intros Hf. eapply obj_at_transport; [exact Hf|]. intros f i Hf' Hi. unfold LAY_FrameConfig in Hf'. cbv [In] in Hf'.
repeat (destruct Hf' as [<-|Hf']; [cbn [fst snd] in *; apply (KF OFF_fcfg OFF_apal); unfold OFF_fcfg, OFF_apal, SL_104, SL_120; lia|]). destruct Hf'. }
split. { intros Ho. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Ho | reflexivity |]. apply KB'. apply in_app_iff. left. left. reflexivity. }
split. { intros Hc. eapply (cgif_at_kept _ _ g s N (cgif_blocks g s N) []); [rewrite app_nil_r; apply Permutation_refl | exact Hc |].
intros b n i Hbn Hi. apply (KB b n i); [|exact Hi]. apply in_app_iff. left. right. apply in_app_iff. left. exact Hbn. }
split. { intros [Ha Hl]. split; [|exact Hl]. eapply arr8_frame; [exact Ha|]. intros a Hx. replace a with (img + (a - img)) by lia.
apply (KB' img (fmt * N)); [|lia]. apply in_app_iff. left. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
unfold img_block. replace (fmt_okb fmt) with true; [left; reflexivity|]. unfold fmt_okb. destruct Hfmt as [-> | ->]; reflexivity. }
split. { intros Hq. eapply chtq_ok_kept; [exact Hq | |].
- apply KB'. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
- apply KB'. apply in_app_iff. right. apply in_app_iff. left. right. right. right. right. left. reflexivity. }
intros (Ht & Hfull & Hh & Hwf' & Hmo & Hnd). split; [|split; [exact Hfull | split; [exact Hh | split; [exact Hwf' | split; [exact Hmo | exact Hnd]]]]].
eapply tree_at_frame; [exact Ht|]. intros n a Hn Ha. replace a with (tn_addr n + (a - tn_addr n)) by lia.
apply (KB' (tn_addr n) NODE_SIZE); [|lia]. apply in_app_iff. right. apply in_app_iff. right. apply tree_blocks_in_nodes. exists n. auto.
Qed.
End d.
End c.
