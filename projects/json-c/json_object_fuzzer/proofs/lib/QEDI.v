(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUvT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUvT.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsJM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsJM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition fsmalloc3_entry : Z := 0x4ae5c.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Local Notation FS := (ae_fs_base RE).

Lemma land_2047 : forall x, Z.land x 2047 = x mod 2048.
Proof. intros x. change 2047 with (Z.ones 11). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma mod2048_of_64 : forall x, (x mod 2^64) mod 2048 = x mod 2048.
Proof. intros x. apply Z.mod_mod_divide. exists (2^53); reflexivity. Qed.

Lemma fs3_scan : forall mc fl FS0 (u : Z) (k : nat) (i : Z) (cur : word)
(ra sp gp tp t0 t1 t2 s0 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
u8arr asegs mc (FS + 32768) fl -> fl = flags_of FS0 FS 3 ->
Z.of_nat (length (filter (fun f => ff_cls f =? 3) FS0)) < fs_N 3 ->
0 <= FS -> FS + 11571200 <= 2^64 ->
k = Z.to_nat (2048 - i) -> 0 <= i < 2048 ->
bv_unsigned cur mod 2048 = (u + i) mod 2048 ->
(forall j, 0 <= j < i -> live_b FS0 3 (fs_frame FS 3 ((u + j) mod 2048)) = true) ->
evt asegs (fun ms' => exists (pos i' : Z) (cur' : word),
ms' = MS (mkR ra sp gp tp (wz 0) t1 t2 s0 (wz FS) (wz (2048 - i')) (wz (FS + 4096)) cur' (wz (FS + 32768)) (wz 2047)
(wz (FS + 32768 + pos)) a6 (wz pos) (wz 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4af68) fc None mc (seg_rom asegs)
/\ 0 <= pos < 2048 /\ live_b FS0 3 (fs_frame FS 3 pos) = false /\ 0 <= i' < 2048)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (wz FS) (wz (2048 - i)) (wz (FS + 4096)) cur (wz (FS + 32768)) (wz 2047) a5 a6 a7
(wz 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4aef0) fc None mc (seg_rom asegs)).
Proof.
intros mc fl FS0 u k. induction k as [k IH] using lt_wf_ind.
intros i cur; intros until fc; intros FLc Efl ROOM B1 B2 Hk Hi Hcur BUSY.
pose proof (bv_unsigned_in_range 64 cur) as CR. change (bv_modulus 64) with (2^64) in CR.
set (pos := Z.land (bv_unsigned cur) 2047).
assert (Hpos : pos = (u + i) mod 2048) by (subst pos; rewrite land_2047; exact Hcur).
assert (PR : 0 <= pos < 2048) by (rewrite Hpos; apply Z.mod_pos_bound; lia).
destruct (live_b FS0 3 (fs_frame FS 3 pos)) eqn:LB.
-
pose proof (u8arr_read asegs mc (FS + 32768) fl pos (b8 1) (wa (FS + 32768 + pos)) FLc
ltac:(subst fl; rewrite flags_of_nth by (unfold fs_N; cbn; lia); rewrite LB; reflexivity) ltac:(lia) eq_refl) as RD.
subst pos. do 4 istep. if_false. istep. rewrite addiw_small by lia. do 2 istep.
destruct (Z.lt_ge_cases (i + 1) 2048) as [LT|GE].
+ if_true_u. replace (2048 - i + -1) with (2048 - (i + 1)) by lia.
eapply (IH (Z.to_nat (2048 - (i + 1))) ltac:(lia) (i + 1) (wz (bv_unsigned cur + 1)));
[exact FLc| exact Efl| exact ROOM| lia| lia| reflexivity| lia| |].
* rewrite unsigned_lit_wrap, mod2048_of_64, <- Zplus_mod_idemp_l, Hcur, Zplus_mod_idemp_l. f_equal. lia.
* intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [rewrite <- Hpos; exact LB| apply BUSY; lia].
+ exfalso.
assert (ALL : forall p, 0 <= p < fs_N 3 -> live_b FS0 3 (fs_frame FS 3 p) = true).
{ apply (scan_exhausts FS0 FS 3 u (i + 1)); try change (fs_N 3) with 2048; [lia| lia| lia| | lia].
intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [rewrite <- Hpos; exact LB| apply BUSY; lia]. }
pose proof (all_live_count FS0 FS 3 ltac:(lia) ALL) as CNT. change (fs_N 3) with 2048 in CNT, ROOM.
rewrite filter_cls_length in ROOM. lia.
-
pose proof (u8arr_read asegs mc (FS + 32768) fl pos (b8 0) (wa (FS + 32768 + pos)) FLc
ltac:(subst fl; rewrite flags_of_nth by (unfold fs_N; cbn; lia); rewrite LB; reflexivity) ltac:(lia) eq_refl) as RD.
subst pos. do 4 istep. if_true. apply evt_done. exists (Z.land (bv_unsigned cur) 2047), i, cur.
split; [reflexivity|]. split; [exact PR|]. split; [exact LB| exact Hi].
Qed.

Lemma fsmalloc3_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo FS0 (size : Z),
RTconst RE X m -> rlay_ok RE X -> RFake FS0 RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 224 ->
Z.of_nat (length (filter (fun f => ff_cls f =? 3) FS0)) < fs_N 3 ->
a0 = wz size ->
evt asegs (rpost ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(FS, FS + A_FS_MAP_SIZE); (SH FS, SH (FS + A_FS_MAP_SIZE)); (bv_unsigned sp - 224, bv_unsigned sp)] lo m
(fun a0' m' => exists f pos junk,
a0' = wz f /\ f = fs_frame FS 3 pos /\ 0 <= pos < fs_N 3 /\ ~ In f (map ff_addr FS0)
/\ fframe_rangeA RE 3 f
/\ RTconst RE X m' /\ RFake ((3, f) :: FS0) RE X m'
/\ rw_cells asegs m' f [CB (Z.to_nat (ff_size 3 - 8)) junk]
/\ rw_cells asegs m' (SH f) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
/\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (FS + 24, FS + 24 + 8); (fs_flag FS 3 pos, fs_flag FS 3 pos + 1);
(f, f + ff_size 3); (SH f, SH f + ff_size 3 / 8)] m m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz fsmalloc3_entry) fc None m (seg_rom asegs)).
Proof.
intros until size; intros RT RL RF MI ST CEIL LO ROOM Ha0. pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
unfold fsmalloc3_entry, fsmalloc_stack, tls_fs_stack, A_TP, A_FS_MAP_SIZE in *. subst a0.
obj_facts RL.

pose proof RF as RF0.
destruct RF as (ALf & K1f & K2f & SHP & SSL & GC & HI & FL & SL & J1 & J2).
destruct (HI 3 ltac:(unfold kFsClasses; lia)) as [h0 HINT]. unfold fs_hint in HINT. change (8 * 3) with 24 in HINT.
pose proof (FL 3 ltac:(unfold kFsClasses; lia)) as FL0.
remember (flags_of FS0 FS 3) as fl eqn:Efl.
assert (LENF : Z.of_nat (length fl) = 2048) by (subst fl; rewrite flags_of_length; reflexivity).
replace (fs_flag FS 3 0) with (FS + 32768) in FL0 by (unfold fs_flag, fs_foff; cbn; lia).
pose proof (munch_refl [(FS, FS + 11571200); (SH FS, SH (FS + 11571200)); (bv_unsigned sp - 224, bv_unsigned sp)] m) as MU.
pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MUs.
pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
step_until 0x55798.

call_u (tls_fs_spec RE X).
{ rt_cur RT RL RTn. exact RTn. } { exact RL. } { assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. }
unfold A_TP in *.

rt_now RT RL 30%nat K30. step_until 0. clear K30. if_false_u.

step_until 0. if_true_u.

step_until 0. if_false. step_until 0x4aef0.

eapply evt_cut.
{ eapply (fs3_scan _ fl FS0 (bv_unsigned h0) _ 0 h0);
[exact FL0| exact Efl| exact ROOM| lia| lia| reflexivity| lia| f_equal; lia| intros j Hj; lia]. }
cbv beta. intros ms' (pos & i' & cur' & -> & PR & LB & Hi').
match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eassert (MU2 : munch [(bv_unsigned sp - 224, bv_unsigned sp); (FS + 24, FS + 24 + 8); (FS + 32768 + pos, FS + 32768 + pos + 1);
(FS + 3182592 + pos * 512, FS + 3182592 + pos * 512 + 512); (SH (FS + 3182592 + pos * 512), SH (FS + 3182592 + pos * 512) + 64)] m mc)
by (eapply munch_weaken; [| exact MUs]; intros y Hy; cbn [outside fst snd] in Hy |- *; tauto) end.
clear MUs.

do 3 istep.
istep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u8arr_store_ok asegs mc (FS + 32768) fl pos (wa (FS + 32768 + pos)) FL0 ltac:(lia) eq_refl) as SOK end.
step. rewrite le1_lit.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u8arr_write asegs mc (FS + 32768) fl pos (b8 1) FL0 ltac:(lia)) as FL1 end.
clear FL0. store_done.

do 7 istep. rewrite ?(unsigned_lit pos), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 9) with 512.
replace (FS + 36864 + (3145728 + pos * 512)) with (FS + 3182592 + pos * 512) by lia.
remember (FS + 3182592 + pos * 512) as f eqn:Ef in *.
assert (FB : FS + 3182592 <= f /\ f + 512 <= FS + 3182592 + 1048576) by (subst f; lia).
pose proof (hjunk_wmono _ _ _ _ J1 WM) as J1c. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in J1c.
pose proof (fun Hm => proj2 (hjunk_split _ _ f _ J1c Hm)) as J1r. specialize (J1r ltac:(lia)).
pose proof (fun Hm => proj1 (hjunk_split _ f (f + Z.of_nat 512) _ J1r Hm)) as J1f. specialize (J1f ltac:(cbn; lia)).
destruct (hjunk_cells _ f 512 J1f) as [junkf FRM]. clear J1c J1r J1f.
do 2 istep.

do 2 istep. call0 (mem_to_shadow_spec RE X).
{ rt_solve RT RL. } { assumption. } { rewrite ?KHI_eq. lia. }
match goal with H : @eq (bv 64) ?v (wz (SH f)) |- _ => subst v end.
do 3 istep.

assert (SHf8 : SH (f + 512) = SH f + 64) by (rewrite !SH_eq; replace (f + 512) with (f + 64 * 8) by lia; rewrite Z.div_add by lia; lia).
assert (SHK : 0x7fff8000 <= SH FS /\ SH (FS + 11571200) <= 0x10007fff8000)
by (clear - OF; rewrite !SH_eq; Z.div_mod_to_equations; lia).
assert (SB : SH FS <= SH f /\ SH (f + 512) <= SH (FS + 11571200)) by (split; apply SH_mono; lia).
pose proof (hjunk_wmono _ _ _ _ J2 WM) as J2c. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in J2c.
pose proof (fun Hm => proj2 (hjunk_split _ _ (SH f) _ J2c Hm)) as J2r. specialize (J2r ltac:(split; apply SH_mono; lia)).
pose proof (fun Hm => proj1 (hjunk_split _ (SH f) (SH f + Z.of_nat 64) _ J2r Hm)) as J2f. specialize (J2f ltac:(cbn; lia)).

lazymatch type of J2f with hjunk ?mj _ _ =>
assert (JW : forall k, 0 <= k < 8 -> exists junk, rw_cells asegs mj (SH f + 8 * k) [CB 8 junk]) end.
{ intros k Hk.
pose proof (fun Hm => proj2 (hjunk_split _ (SH f) (SH f + 8 * k) _ J2f Hm)) as Ja. specialize (Ja ltac:(cbn; lia)).
pose proof (fun Hm => proj1 (hjunk_split _ (SH f + 8 * k) (SH f + 8 * k + Z.of_nat 8) _ Ja Hm)) as Jb. specialize (Jb ltac:(cbn; lia)).
exact (hjunk_cells _ (SH f + 8 * k) 8 Jb). }
destruct (JW 0 ltac:(lia)) as [junks1 SHC1]. rewrite Z.mul_0_r, Z.add_0_r in SHC1.
destruct (JW 1 ltac:(lia)) as [junks2 SHC2]. destruct (JW 2 ltac:(lia)) as [junks3 SHC3]. destruct (JW 3 ltac:(lia)) as [junks4 SHC4].
destruct (JW 4 ltac:(lia)) as [junks5 SHC5]. destruct (JW 5 ltac:(lia)) as [junks6 SHC6]. destruct (JW 6 ltac:(lia)) as [junks7 SHC7]. destruct (JW 7 ltac:(lia)) as [junks8 SHC8].
change (8 * 1) with 8 in SHC2. change (8 * 2) with 16 in SHC3. change (8 * 3) with 24 in SHC4. change (8 * 4) with 32 in SHC5. change (8 * 5) with 40 in SHC6. change (8 * 6) with 48 in SHC7. change (8 * 7) with 56 in SHC8.
clear J2c J2r J2f JW.
istep. istep. istep. istep. istep. istep. istep. istep.

step_until 0.
release_frame FR STK (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STK|].

pose proof (rw_cells_merge asegs _ f [] [CB 24 (take 24 junkf); C8 sp; CB 472 (take 472 (drop 32 junkf))] [C8 (wz (FS + 32768 + pos))] FRM) as FRM'.
cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRM'.
rewrite app_nil_r in FRM'.
destruct (proj1 (rw_cells_app asegs _ f [CB 504 (take 24 junkf ++ le8 sp ++ take 472 (drop 32 junkf))] [C8 (wz (FS + 32768 + pos))]) FRM') as [BODY SLOT].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SLOT. clear FRM FRM'.
assert (Ef' : f = fs_frame FS 3 pos) by (subst f; unfold fs_frame, ff_size; cbn; lia).
assert (FLG : fs_flag FS 3 pos = FS + 32768 + pos) by (unfold fs_flag, fs_foff; cbn; lia).
assert (FLG0 : fs_flag FS 3 0 = FS + 32768) by (unfold fs_flag, fs_foff; cbn; lia).
edestruct (RFake_take RE X FS0 m _ 3 pos f (wz (bv_unsigned cur' + 1)) RF0 ltac:(unfold kFsClasses; lia) ltac:(change (fs_N 3) with 2048; lia) Ef'
ltac:(rewrite Ef'; exact LB) WM) as [RF' FRESH].
{ eapply agree_on_of_munch; [exact MU2| exact WM|]. intros y [Fy NT] Hy. apply outside_intro. intros lo' hi' Hin [Y1 Y2].
apply (fp_RFake_zone RE X) in Fy. unfold in_iv, in_sh, A_FS_MAP_SIZE in Fy. cbn [fst snd] in Fy.
unfold fs_touched, fs_hint in NT. rewrite FLG in NT. change (ff_size 3) with 512 in NT. change (512 / 8) with 64 in NT. change (8 * 3) with 24 in NT.
change (11571200 / 8) with 1446400 in Fy. cbn in Hin.
assert (SHD : SH (FS + 11571200) = SH FS + 1446400)
by (rewrite !SH_eq; replace (FS + 11571200) with (FS + 1446400 * 8) by lia; rewrite Z.div_add by lia; lia).
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia. }
{ unfold fs_hint. change (8 * 3) with 24. exact HINT. }
{ rewrite FLG0, <- Efl. exact FL1. }
{ replace (f + ff_size 3 - 8) with (f + 504) by (change (ff_size 3) with 512; lia). rewrite FLG. exact SLOT. }
exists f, pos, (take 24 junkf ++ le8 sp ++ take 472 (drop 32 junkf)).
split; [reflexivity|]. split; [exact Ef'|]. split; [change (fs_N 3) with 2048; lia|]. split; [exact FRESH|].
split. { unfold fframe_rangeA. rewrite ?KHI_eq. change (ff_size 3) with 512. subst f. repeat split; lia. }
split; [rt_solve RT RL|]. split; [exact RF'|]. split; [exact BODY|]. split.
{ apply (proj2 (rw_cells_app asegs _ (SH f) [C8 (wz 0)] [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)])). split; [exact SHC1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
apply (proj2 (rw_cells_app asegs _ (SH f + 8) [C8 (wz 0)] [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)])). split; [exact SHC2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
replace (SH f + 8 + 8) with (SH f + 16) by lia.
apply (proj2 (rw_cells_app asegs _ (SH f + 16) [C8 (wz 0)] [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)])). split; [exact SHC3|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
replace (SH f + 16 + 8) with (SH f + 24) by lia.
apply (proj2 (rw_cells_app asegs _ (SH f + 24) [C8 (wz 0)] [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)])). split; [exact SHC4|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
replace (SH f + 24 + 8) with (SH f + 32) by lia.
apply (proj2 (rw_cells_app asegs _ (SH f + 32) [C8 (wz 0)] [C8 (wz 0); C8 (wz 0); C8 (wz 0)])). split; [exact SHC5|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
replace (SH f + 32 + 8) with (SH f + 40) by lia.
apply (proj2 (rw_cells_app asegs _ (SH f + 40) [C8 (wz 0)] [C8 (wz 0); C8 (wz 0)])). split; [exact SHC6|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
replace (SH f + 40 + 8) with (SH f + 48) by lia.
apply (proj2 (rw_cells_app asegs _ (SH f + 48) [C8 (wz 0)] [C8 (wz 0)])). split; [exact SHC7|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
replace (SH f + 48 + 8) with (SH f + 56) by lia. exact SHC8. }
rewrite FLG. change (ff_size 3) with 512. change (512 / 8) with 64.
eapply munch_weaken; [| exact MU2]. intros y Hy. cbn [outside fst snd] in Hy |- *. lia.
Qed.
End Walk.
