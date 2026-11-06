(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE23.v, with its module paths changed, names TfibSyms -> CmdBSyms, its addresses moved to plugin-hostd/fuzz_command's ASan build, and the module destructor's write set XW2 stated with the shadow of the whole image ([0x7fffa000, 0x800b8c00)) instead of the shadow bytes of cgif's three registered globals (fuzz_command registers 180), plus the odr indicator bytes of the four globals that have one (0x5e3c40..0x5e3c42, 0x5e3c80), which __asan_unregister_globals clears. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/AE23.v; 161 of its 206 lines of code are new or changed and 1630 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtSStrtok1.v, with its module paths changed; 939 of its 977 lines of code are new or changed and 168 lines of the source are left out. *)
(* amcspn_realizes at MCSPN_ENTRY = 0x9ee10 (lib/B/Rt/RtSStrcspnDef.v): the contract of musl's strcspn on
   plugin-hostd/fuzz_command's ASan+UBSan build, at the window MCSPN_K = 80 + 16 + ESTACK; the image-B twin of
   lib/A/Rt/RtSStrcspnM.v.

   The walk itself is lib/B/Rt/RtSStrcspnMW.v (the plain-model walk of lib/Prog/strcspn.v readdressed to this
   image) and lib/B/Rt/RtSStrcspnMChr.v (musl strchrnul).  That walk cannot step through the two interceptor
   calls the ASan+UBSan image puts inside musl's code, so it is cut into segments; this file joins them in cgif's
   SRr model with lib/B/Rt/RtBzLift.v and lib/B/Rt/RtSStrcspnMLift.v:

     |set| >= 2 : cspn_entry_big -> the memset interceptor 0x57674 (AMEMSET) -> cspn_after_mset
     |set| =  1 : cspn_entry_one (strchrnul returns without calling anything)
     |set| =  0 : cspn_entry_nil -> the strlen interceptor 0x4517c (RtSStrlen.cmd_strlen) -> cspn_after_strlen

   The premises of each segment are read off the contract's: astr_at and aread_ok give the two strings as lib/Lib
   bytes, atail_vis the slack of the first string's last word (musl's word loop inside strchrnul reads it),
   ecall_pre_stk the stack window, aguard_ok the stack-protector pair, and rt_rom_view musl's two word-loop
   constants.  The post of each segment is read back by art_post_comp, whose AR comes from the frame law. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK14 YK15 YK18 YP03 YP09 YK04 YK0i YI04 YA0i YA0n YA0o YG00 YG0a YG01 YG0f YG0v YG0n YG0d YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YF0m YF0x YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import
RtDefs RtString RtAPI RtSStrcspnDef RtSStrcspnMImg RtBzLift RtSStrcspnMLift RtSStrcspnMW.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtSStrlen.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strcspn_c.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.PropExec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Regs6ss.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module LP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.PropExec.
Module LMS := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.MState.
Module LM := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Mem.
Module LC := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Cells.
Module LSt := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Step.
Module LF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Frame.
Module LE := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Exec.
Module R6 := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Regs6ss.

(* ---- the eight lib/Lib bytes of a word ---- *)
Lemma nth_le_bytes : forall n z k, (k < n)%nat ->
nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. lia.
Qed.

Lemma le8_nth : forall (v : Z) i, 0 <= v < 2 ^ 64 -> (i < 8)%nat ->
nth_error (LM.le8 (Z_to_bv 64 v)) i = Some (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat i))).
Proof.
intros v i Hv Hi. unfold LM.le8, word_to_le_bytes.
rewrite unsigned_lit_small by lia. apply nth_le_bytes. exact Hi.
Qed.

Lemma bytes_at_join : forall (m : word -> option byte) a l1 l2,
LM.bytes_at rsegs m a l1 -> LM.bytes_at rsegs m (a + Z.of_nat (length l1)) l2 ->
LM.bytes_at rsegs m a (l1 ++ l2).
Proof.
intros m a l1 l2 (H0 & H1 & HB1) (_ & H2 & HB2). split; [exact H0|].
rewrite length_app. split; [lia|].
intros i Hi.
destruct (Nat.lt_ge_cases i (length l1)) as [Hlt|Hge].
- rewrite nth_error_app1 by exact Hlt. exact (HB1 i Hlt).
- rewrite nth_error_app2 by exact Hge.
replace (a + Z.of_nat i) with (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) by lia.
apply HB2. lia.
Qed.

Lemma nth_rep0 : forall (n k : nat) (d : byte), (k < n)%nat -> nth k (repeat (Z_to_bv 8 0) n) d = Z_to_bv 8 0.
Proof.
induction n as [|n IH]; intros k d Hk; [lia|].
destruct k as [|k]; cbn [repeat nth]; [reflexivity | apply IH; lia].
Qed.

(* the callee-saved registers of a walk, read by conversion: the state carries the image table, so a
   vm_compute here would normalise the whole image *)
Ltac keep_regs_r :=
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; unfold acallee_saved in Hr;
assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
clear Hr;
repeat (destruct Hr' as [Hr'|Hr']; [subst r; reflexivity|]);
subst r; reflexivity.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma rdword_rng_view : forall (H : word -> bool) mem a v,
rdword (aview tfibsegs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview tfibsegs H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview tfibsegs H mem (a+1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview tfibsegs H mem (a+2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview tfibsegs H mem (a+3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview tfibsegs H mem (a+4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview tfibsegs H mem (a+5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview tfibsegs H mem (a+6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview tfibsegs H mem (a+7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
assert (R : forall q w, aview tfibsegs H mem q = Some w -> 0 <= w < 256).
{ intros q w Hq. destruct (view_mrd H mem q w Hq) as (b & _ & <-).
pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb. exact Rb. }
pose proof (R _ _ E0). pose proof (R _ _ E1). pose proof (R _ _ E2). pose proof (R _ _ E3).
pose proof (R _ _ E4). pose proof (R _ _ E5). pose proof (R _ _ E6). pose proof (R _ _ E7).
change (2 ^ 64) with 18446744073709551616. lia.
Qed.

Lemma word_cells_of_rdword : forall (H : word -> bool) mem a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
rdword (aview tfibsegs H mem) a = Some v ->
LSt.ro_cells rsegs (mrestrict H mem) a [LC.C8 (Z_to_bv 64 v)].
Proof.
intros H mem a v Ha Ha8 Hw.
pose proof (rdword_rng_view H mem a v Hw) as Hv.
apply RtSStrcspnMW.ro8.
pose proof (YE2y.val_mem_of_rdword H mem a v Hw) as Hvm.
split; [exact Ha|]. rewrite LM.length_le8. split; [exact Ha8|].
intros i Hi.
pose proof (Hvm i Hi) as Hk.
change (mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat i))
with (LM.mrd rsegs (mrestrict H mem) (LM.wa (a + Z.of_nat i))) in Hk.
rewrite Hk, (le8_nth v i Hv Hi). f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite <- YF0x.le_byte_eq. unfold YG0f.le_byte.
rewrite (Z.mod_small v) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma bytes_at_view_eq : forall (H : word -> bool) (m1 m2 : word -> option byte) A bs,
(forall a, A <= a < A + Z.of_nat (length bs) -> aview tfibsegs H m2 a = aview tfibsegs H m1 a) ->
LM.bytes_at rsegs (mrestrict H m1) A bs -> LM.bytes_at rsegs (mrestrict H m2) A bs.
Proof.
intros H m1 m2 A bs HE (HA & HL & HB). split; [exact HA|]. split; [exact HL|].
intros i Hi.
pose proof (YE2y.mbyte_of_aview H H m1 m2 (A + Z.of_nat i) (HE (A + Z.of_nat i) ltac:(lia))) as Em.
change (mbyte tfibsegs (mrestrict H m2) (A + Z.of_nat i))
with (LM.mrd rsegs (mrestrict H m2) (LM.wa (A + Z.of_nat i))) in Em.
change (mbyte tfibsegs (mrestrict H m1) (A + Z.of_nat i))
with (LM.mrd rsegs (mrestrict H m1) (LM.wa (A + Z.of_nat i))) in Em.
rewrite Em. exact (HB i Hi).
Qed.

Lemma ro_cells_view_eq : forall (H : word -> bool) (m1 m2 : word -> option byte) A cs,
(forall a, A <= a < A + Z.of_nat (LC.cells_size cs) -> aview tfibsegs H m2 a = aview tfibsegs H m1 a) ->
LSt.ro_cells rsegs (mrestrict H m1) A cs -> LSt.ro_cells rsegs (mrestrict H m2) A cs.
Proof.
intros H m1 m2 A cs HE (Hwf & HB). split; [exact Hwf|].
apply (bytes_at_view_eq H m1 m2 A (LC.cells_bytes cs)); [|exact HB].
intros a Ha. apply HE. rewrite (LC.cells_bytes_length cs Hwf) in Ha. exact Ha.
Qed.


(* a read-only byte of the image lies below its end 0x606000 (YF0x.TFIB_IMG_END; fuzz_command.asan-ubsan's last
   LOAD ends at 0x6059f8) *)
Lemma cspn_in_rom_low : forall a, in_rom tfibsegs a -> 0 <= a < TFIB_IMG_END.
Proof.
intros a (sg & Hin & _ & Hr).
assert (Hm : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs))
by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin).
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in Hm. unfold TFIB_IMG_END.
repeat (destruct Hm as [Hm|Hm]; [injection Hm as <- <-; lia|]). destruct Hm.
Qed.

End w.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet 0x57674.

(* ---- musl's two word-loop constants, out of rt_rom_view (the range is RtSStrlen's) ---- *)
Lemma rom_const : forall (W : world tfibsegs) mem (a : Z) (v : Z),
rt_rom_view tfibsegs B W mem -> 0x10358 <= a -> a + 8 <= 0x10378 ->
(forall i, (i < 8)%nat -> seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error (LM.le8 (Z_to_bv 64 v)) i) ->
LSt.ro_cells rsegs (mrestrict (w_H W) mem) a [LC.C8 (Z_to_bv 64 v)].
Proof.
intros W mem a v HROM Hlo Hhi HR. apply RtSStrcspnMW.ro8.
apply (rom_bytes_at W mem a (LM.le8 (Z_to_bv 64 v))); [lia| rewrite LM.length_le8; lia | exact HR |].
intros i Hi. rewrite LM.length_le8 in Hi.
destruct (RtSStrlen.sl_rom_unowned B TB (a + Z.of_nat i) ltac:(lia)) as (U1 & U2).
exact (HROM (a + Z.of_nat i) (RtSStrlen.sl_rom_in (a + Z.of_nat i) ltac:(lia)) U1 U2).
Qed.

Lemma rom_cmagic : forall (W : world tfibsegs) mem, rt_rom_view tfibsegs B W mem ->
LSt.ro_cells rsegs (mrestrict (w_H W) mem) 0x10370 [LC.C8 (Z_to_bv 64 CM_CMAGIC)].
Proof.
intros W mem HROM. apply (rom_const W mem 0x10370 CM_CMAGIC HROM ltac:(lia) ltac:(lia)).
intros i Hi.
assert (Hc : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%nat) by lia.
destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; f_equal; apply bv_eq; reflexivity.
Qed.

Lemma rom_highs : forall (W : world tfibsegs) mem, rt_rom_view tfibsegs B W mem ->
LSt.ro_cells rsegs (mrestrict (w_H W) mem) 0x10358 [LC.C8 (Z_to_bv 64 CM_HIGHS)].
Proof.
intros W mem HROM. apply (rom_const W mem 0x10358 CM_HIGHS HROM ltac:(lia) ltac:(lia)).
intros i Hi.
assert (Hc : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%nat) by lia.
destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; f_equal; apply bv_eq; reflexivity.
Qed.

(* ---- the stack's shadow is zero, so a stack range is addressable and its hull is visible ---- *)
Lemma stk_shadow0 : forall ly S (W : world tfibsegs) mem md a, AR tfibsegs B ly S W mem md ->
ly_stk_lo ly <= a < ly_stk_hi ly -> aview tfibsegs (w_H W) mem (shadow_addr a) = Some 0.
Proof.
intros ly S W mem md a HAR Ha.
pose proof (am_zshadow B ly S _ (proj1 HAR)) as HZ. unfold zshadow_ok in HZ. rewrite Forall_forall in HZ.
pose proof (HZ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)
ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ0.
cbn [fst snd] in HZ0. unfold zero_shadow in HZ0.
pose proof (lo_top ly (am_layout B ly S _ (proj1 HAR))) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
unfold page_aligned in T5, T6.
assert (E : shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (a / 8 - ly_stk_lo ly / 8) = shadow_addr a)
by (unfold shadow_of_addr, shadow_addr; lia).
rewrite <- E. apply HZ0. Z.div_mod_to_equations. lia.
Qed.

Lemma bitset_ok : forall ly S (W : world tfibsegs) mem md (sp0 : Z), AR tfibsegs B ly S W mem md ->
sp0 mod 16 = 0 -> ly_stk_lo ly + 4192 <= sp0 -> sp0 <= ly_stk_hi ly ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (sp0 - 80) 32 /\
shadow_hull_vis (aview tfibsegs (w_H W) mem) (sp0 - 80) 32.
Proof.
intros ly S W mem md sp0 HAR Hal Hlo Hhi.
pose proof (lo_top ly (am_layout B ly S _ (proj1 HAR))) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
unfold page_aligned in T5, T6.
split.
- intros z Hz. exists 0. split; [|left; reflexivity].
replace (shadow_of_addr SHADOW_OFF z) with (shadow_addr z)
by (unfold shadow_of_addr, shadow_addr; lia).
apply (stk_shadow0 ly S W mem md z HAR). lia.
- intros s Hs.
assert (Ea : shadow_addr (8 * (s - SHADOW_OFF)) = s)
by (unfold shadow_addr, SHADOW_OFF in *; Z.div_mod_to_equations; lia).
assert (Ha : ly_stk_lo ly <= 8 * (s - SHADOW_OFF) < ly_stk_hi ly).
{ unfold shadow_addr, SHADOW_OFF in Hs. unfold SHADOW_OFF.
clear - Hs Hal Hlo Hhi T5 T6. Z.div_mod_to_equations. lia. }
rewrite <- Ea, (stk_shadow0 ly S W mem md _ HAR Ha). discriminate.
Qed.


Section t.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model).
Variables (x y canv : Z) (str set sl : list byte).
Hypothesis HGOT : rdword (aview tfibsegs (w_H W) mem) A_SSP_GOT = Some A_SSP_GUARD.
Hypothesis HCAN : rdword (aview tfibsegs (w_H W) mem) A_SSP_GUARD = Some canv.
Hypothesis HPRE : ecall_pre_stk tfibsegs B MCSPN_K ly S W regs mem md.
Hypothesis G10 : getr regs 10 = w64 x.
Hypothesis G11 : getr regs 11 = w64 y.
Hypothesis Hx0 : 0 < x.
Hypothesis Hy0 : 0 < y.
Hypothesis HSTR : astr_at tfibsegs W mem x str.
Hypothesis HSET : astr_at tfibsegs W mem y set.
Hypothesis RDX : aread_ok tfibsegs MCSPN_K W regs mem x (astr_len str + 1).
Hypothesis RDY : aread_ok tfibsegs MCSPN_K W regs mem y (astr_len set + 1).
Hypothesis TLX : atail_vis tfibsegs W mem (x + astr_len str).
Hypothesis HROM : rt_rom_view tfibsegs B W mem.
Hypothesis SLL : Z.of_nat (length sl) = 7 - (x + astr_len str) mod 8.
Hypothesis SLB : LM.bytes_at rsegs (mrestrict (w_H W) mem) (x + astr_len str + 1) sl.

Local Notation HH := (w_H W).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation sp0 := (spZ regs).
Local Notation lo0 := (spZ regs - MCSPN_K).
Local Notation RROW :=
(LF.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
(getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
(getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
(getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
(getr regs 29) (getr regs 30) (getr regs 31)).
Local Notation QRET :=
(fun (regs' : bvmap 5 word) (_ : word -> option byte) =>
getr regs' 10 = w64 (Z.of_nat (strcspn_c.cspn_len set str))).
Local Notation POSTQ := (art_post tfibsegs B MCSPN_K ly S W regs mem md (fun _ => False) QRET).
Local Notation PST base :=
(cspn_post (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 8) (getr regs 9) (getr regs 18)
(getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
(getr regs 26) (getr regs 27) fp_regs fp_csr str set lo0 (mrestrict (w_H W) base)).
Local Notation MEMB base :=
(cspn_mem (getr regs 2) lo0 (bv_unsigned (getr regs 10)) (bv_unsigned (getr regs 11))
(str ++ Z_to_bv 8 0 :: sl) (set ++ [Z_to_bv 8 0]) (Z_to_bv 64 canv)
(getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (mrestrict (w_H W) base)).

Lemma canon_eq : forall (R : bvmap 5 word) pc mm,
canon_at R pc mm = LMS.MS (R6.mkR_of R) fp_regs (Z_to_bv 64 pc) fp_csr None mm (LP.seg_rom rsegs).
Proof. intros R pc mm. reflexivity. Qed.

Lemma nums : AR tfibsegs B ly S W mem md /\ YK0s.ret_ok (getr regs 1) /\ sp0 mod 16 = 0 /\
ly_stk_lo ly + MCSPN_K <= sp0 /\ sp0 <= ly_stk_hi ly /\ kHighMemBeg <= ly_stk_lo ly /\
ly_stk_hi ly <= kHighMemEnd /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
(forall a, ascratch_stk MCSPN_K regs a -> apresent HH mem a).
Proof.
destruct HPRE as ((HAR & Hra & Hal & Hslo & Htop & Hpr & Hgp & Htp) & Hlo4 & Hscr).
pose proof (lo_top ly (am_layout B ly S _ (proj1 HAR))) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
split; [exact HAR|]. split; [exact Hra|]. split; [exact Hal|]. split; [exact Hlo4|]. split; [exact Htop|].
split; [exact T7|]. split; [exact T4|]. split; [exact Hgp|]. split; [exact Htp | exact Hscr].
Qed.

Lemma spb : 0x10007fff8000 + 4192 <= sp0 /\ sp0 <= 0x800000000000 /\ sp0 mod 16 = 0.
Proof.
pose proof nums as (_ & _ & Hal & H1 & H2 & H3 & H4 & _).
unfold kHighMemBeg, kHighMemEnd, MCSPN_K, ESTACK in *. split; [lia|]. split; [lia | exact Hal].
Qed.

Lemma xbnd : 0 <= x /\ x + Z.of_nat (length str) + 1 <= 2 ^ 63 /\
0 <= y /\ y + Z.of_nat (length set) + 1 <= 2 ^ 63.
Proof.
pose proof RDX as (A0 & A1 & _). pose proof RDY as (C0 & C1 & _). unfold astr_len in *.
split; [exact A0|]. split; [lia|]. split; [exact C0 | lia].
Qed.

Lemma EA : bv_unsigned (getr regs 10) = x.
Proof. pose proof xbnd as (H0 & H1 & _). rewrite G10. unfold w64. apply unsigned_lit_small. lia. Qed.

Lemma EB : bv_unsigned (getr regs 11) = y.
Proof. pose proof xbnd as (_ & _ & H0 & H1). rewrite G11. unfold w64. apply unsigned_lit_small. lia. Qed.

Lemma strW : forall a, x <= a <= x + Z.of_nat (length str) -> ~ (lo0 <= a < sp0).
Proof.
intros a Ha. pose proof RDX as (_ & _ & _ & Hsrc & _). unfold astr_len in Hsrc.
pose proof (proj2 (Hsrc a ltac:(lia))) as Hn. unfold ascratch_stk in Hn. exact Hn.
Qed.

Lemma setW : forall a, y <= a <= y + Z.of_nat (length set) -> ~ (lo0 <= a < sp0).
Proof.
intros a Ha. pose proof RDY as (_ & _ & _ & Hsrc & _). unfold astr_len in Hsrc.
pose proof (proj2 (Hsrc a ltac:(lia))) as Hn. unfold ascratch_stk in Hn. exact Hn.
Qed.

Lemma hDS : bv_unsigned (getr regs 10) + Z.of_nat (length str) + 1 + Z.of_nat (length sl) <= lo0 \/
sp0 <= bv_unsigned (getr regs 10).
Proof.
rewrite EA. pose proof spb as (P1 & P2 & P3). pose proof xbnd as (X0 & X1 & _). pose proof SLL as HS.
unfold astr_len in HS. unfold MCSPN_K, ESTACK in *.
destruct (Z_le_gt_dec x (sp0 - 4192)) as [Hle|Hgt].
- left. assert (HxL : x + Z.of_nat (length str) < sp0 - 4192).
{ destruct (Z_lt_le_dec (x + Z.of_nat (length str)) (sp0 - 4192)) as [HH1|HH2]; [lia|].
exfalso. apply (strW (sp0 - 4192) ltac:(lia)). unfold MCSPN_K, ESTACK. lia. }
clear - HxL HS P3. Z.div_mod_to_equations. lia.
- right. destruct (Z_lt_le_dec x sp0) as [H2|H2]; [exfalso; apply (strW x ltac:(lia)); unfold MCSPN_K, ESTACK; lia | lia].
Qed.

Lemma hDC : bv_unsigned (getr regs 11) + Z.of_nat (length set) + 1 <= lo0 \/
sp0 <= bv_unsigned (getr regs 11).
Proof.
rewrite EB. pose proof spb as (P1 & P2 & P3). unfold MCSPN_K, ESTACK in *.
destruct (Z_le_gt_dec y (sp0 - 4192)) as [Hle|Hgt].
- left. destruct (Z_lt_le_dec (y + Z.of_nat (length set)) (sp0 - 4192)) as [HH1|HH2]; [lia|].
exfalso. apply (setW (sp0 - 4192) ltac:(lia)). unfold MCSPN_K, ESTACK. lia.
- right. destruct (Z_lt_le_dec y sp0) as [H2|H2]; [exfalso; apply (setW y ltac:(lia)); unfold MCSPN_K, ESTACK; lia | lia].
Qed.

Lemma hSLK : (length set <= 1)%nat ->
(- (bv_unsigned (getr regs 10) + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length sl).
Proof.
intros _. rewrite EA. pose proof SLL as HS. unfold astr_len in HS.
clear - HS. Z.div_mod_to_equations. lia.
Qed.

Lemma hSB : bv_unsigned (getr regs 10) + Z.of_nat (length str) + 1 + Z.of_nat (length sl) <= 2 ^ 64.
Proof.
rewrite EA. pose proof xbnd as (X0 & X1 & _). pose proof SLL as HS. unfold astr_len in HS.
assert (Hsl : Z.of_nat (length sl) <= 7) by (pose proof (Z.mod_pos_bound (x + Z.of_nat (length str)) 8); lia).
change (2 ^ 63) with 9223372036854775808 in X1. change (2 ^ 64) with 18446744073709551616. lia.
Qed.

Lemma hCB : bv_unsigned (getr regs 11) + Z.of_nat (length set) + 1 <= 2 ^ 64.
Proof.
rewrite EB. pose proof xbnd as (_ & _ & Y0 & Y1).
change (2 ^ 63) with 9223372036854775808 in Y1. change (2 ^ 64) with 18446744073709551616. lia.
Qed.

Lemma hLO0 : 0 <= lo0.
Proof. pose proof spb as (P1 & _). unfold MCSPN_K, ESTACK. lia. Qed.

Lemma hLOS : lo0 + 96 <= sp0.
Proof. unfold MCSPN_K, ESTACK. lia. Qed.

Lemma hHLO : 0x606000 <= lo0.
Proof. pose proof spb as (P1 & _). unfold MCSPN_K, ESTACK. lia. Qed.

Lemma hDG : 0xa6bf8 + 8 <= lo0 \/ sp0 <= 0xa6bf8.
Proof. left. pose proof hHLO. lia. Qed.

Lemma hDK : 0x604158 + 8 <= lo0 \/ sp0 <= 0x604158.
Proof. left. pose proof hHLO. lia. Qed.

(* ---- the lib/Lib memory the walk reads, at any store that agrees with [mem] outside the window ---- *)
Definition LIBM (mm : word -> option byte) : Prop :=
LM.bytes_at rsegs mm x (str ++ Z_to_bv 8 0 :: sl) /\ LM.bytes_at rsegs mm y (set ++ [Z_to_bv 8 0])
/\ LSt.ro_cells rsegs mm 0xa6bf8 [LC.C8 (Z_to_bv 64 0x604158)]
/\ LSt.ro_cells rsegs mm 0x604158 [LC.C8 (Z_to_bv 64 canv)]
/\ LSt.ro_cells rsegs mm 0x10370 [LC.C8 (Z_to_bv 64 CM_CMAGIC)]
/\ LSt.ro_cells rsegs mm 0x10358 [LC.C8 (Z_to_bv 64 CM_HIGHS)].

Lemma lib0 : LIBM m0.
Proof.
pose proof xbnd as (X0 & X1 & Y0 & Y1). pose proof hSB. pose proof hCB. pose proof EA. pose proof EB.
destruct HSTR as (HBX & HNX). destruct HSET as (HBY & HNY).
split; [|split; [|split; [|split; [|split]]]].
- replace (str ++ Z_to_bv 8 0 :: sl) with ((str ++ [Z_to_bv 8 0]) ++ sl)
by (rewrite <- app_assoc; reflexivity).
apply bytes_at_join.
+ apply (bytes_of_view HH mem x (str ++ [Z_to_bv 8 0]));
[lia | rewrite length_app; cbn [length]; change (2 ^ 64) with 18446744073709551616;
change (2 ^ 63) with 9223372036854775808 in X1; lia |].
intros i Hi. exact (HBX i Hi).
+ rewrite length_app. cbn [length].
replace (x + Z.of_nat (length str + 1)) with (x + astr_len str + 1) by (unfold astr_len; lia).
exact SLB.
- apply (bytes_of_view HH mem y (set ++ [Z_to_bv 8 0]));
[lia | rewrite length_app; cbn [length]; change (2 ^ 64) with 18446744073709551616;
change (2 ^ 63) with 9223372036854775808 in Y1; lia |].
intros i Hi. exact (HBY i Hi).
- exact (word_cells_of_rdword HH mem 0xa6bf8 0x604158 ltac:(lia) ltac:(lia) HGOT).
- exact (word_cells_of_rdword HH mem 0x604158 canv ltac:(lia) ltac:(lia) HCAN).
- exact (rom_cmagic W mem HROM).
- exact (rom_highs W mem HROM).
Qed.

Lemma lib_keep : forall mem1,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo0 <= a < sp0) -> aview tfibsegs HH mem1 a = aview tfibsegs HH mem a) ->
LIBM (mrestrict HH mem1).
Proof.
intros mem1 HV. pose proof lib0 as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof spb as (P1 & P2 & P3). pose proof xbnd as (X0 & X1 & Y0 & Y1).
pose proof hDS as DS. pose proof hDC as DC. pose proof hSB. pose proof hCB.
pose proof EA as EAx. pose proof EB as EBy. pose proof hHLO.
rewrite EAx in DS. rewrite EBy in DC.
split; [|split; [|split; [|split; [|split]]]].
- apply (bytes_at_view_eq HH mem mem1 x _); [|exact B1].
intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
apply HV; [change (2 ^ 64) with 18446744073709551616; lia | lia].
- apply (bytes_at_view_eq HH mem mem1 y _); [|exact B2].
intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
apply HV; [change (2 ^ 64) with 18446744073709551616; lia | lia].
- apply (ro_cells_view_eq HH mem mem1 0xa6bf8 _); [|exact B3].
intros a Ha. cbn [LC.cells_size LC.csize Nat.add] in Ha.
apply HV; [change (2 ^ 64) with 18446744073709551616; lia | lia].
- apply (ro_cells_view_eq HH mem mem1 0x604158 _); [|exact B4].
intros a Ha. cbn [LC.cells_size LC.csize Nat.add] in Ha.
apply HV; [change (2 ^ 64) with 18446744073709551616; lia | lia].
- apply (ro_cells_view_eq HH mem mem1 0x10370 _); [|exact B5].
intros a Ha. cbn [LC.cells_size LC.csize Nat.add] in Ha.
apply HV; [change (2 ^ 64) with 18446744073709551616; lia | lia].
- apply (ro_cells_view_eq HH mem mem1 0x10358 _); [|exact B6].
intros a Ha. cbn [LC.cells_size LC.csize Nat.add] in Ha.
apply HV; [change (2 ^ 64) with 18446744073709551616; lia | lia].
Qed.

Lemma stk_keep : forall mem1 (hi : Z), lo0 <= hi <= sp0 ->
(forall a, lo0 <= a < sp0 -> apresent HH mem1 a) -> LF.stk rsegs (mrestrict HH mem1) lo0 hi.
Proof.
intros mem1 hi Hhi HP. pose proof spb as (P1 & P2 & _). pose proof hLO0.
apply stk_of_apresent; [lia | change (2 ^ 64) with 18446744073709551616; lia |].
intros a Ha. apply HP. lia.
Qed.

(* ---- a byte list the walk left in the lib store, as the donor's view of the lifted store ---- *)
Lemma view_of_lib : forall (mem_b m1 : word -> option byte) A bs,
(forall a : word, HH a = true -> m1 a = None) -> LM.bytes_at rsegs m1 A bs ->
forall i, (i < length bs)%nat ->
aview tfibsegs HH (munrestrict HH mem_b m1) (A + Z.of_nat i) = Some (bv_unsigned (nth i bs (Z_to_bv 8 0))).
Proof.
intros mem_b m1 A bs Hc (H0 & H1 & HB) i Hi.
assert (Em : mrestrict HH (munrestrict HH mem_b m1) (Z_to_bv 64 (A + Z.of_nat i))
= m1 (Z_to_bv 64 (A + Z.of_nat i))).
{ unfold mrestrict, munrestrict. destruct (HH (Z_to_bv 64 (A + Z.of_nat i))) eqn:E;
[symmetry; apply Hc; exact E | reflexivity]. }
assert (EM2 : LM.mrd rsegs (mrestrict HH (munrestrict HH mem_b m1)) (LM.wa (A + Z.of_nat i))
= LM.mrd rsegs m1 (LM.wa (A + Z.of_nat i))) by (unfold LM.mrd, LM.wa; rewrite Em; reflexivity).
unfold aview.
change (mbyte tfibsegs (mrestrict HH (munrestrict HH mem_b m1)) (A + Z.of_nat i))
with (LM.mrd rsegs (mrestrict HH (munrestrict HH mem_b m1)) (LM.wa (A + Z.of_nat i))).
rewrite EM2, (HB i Hi), (nth_err_nth bs (Z_to_bv 8 0) i Hi). reflexivity.
Qed.

Lemma cells_keep : forall (mem_b m1 mem2 : word -> option byte) A cs,
(forall a : word, HH a = true -> m1 a = None) -> LSt.rw_cells rsegs m1 A cs ->
(forall a, A <= a < A + Z.of_nat (LC.cells_size cs) ->
 aview tfibsegs HH mem2 a = aview tfibsegs HH (munrestrict HH mem_b m1) a) ->
(forall a, A <= a < A + Z.of_nat (LC.cells_size cs) -> apresent HH mem2 a) ->
LSt.rw_cells rsegs (mrestrict HH mem2) A cs.
Proof.
intros mem_b m1 mem2 A cs Hc HR HV HP.
pose proof (LSt.rw_cells_bound rsegs _ _ _ HR) as HBnd.
destruct HR as ((Hwf & HB) & _).
pose proof (LC.cells_bytes_length cs Hwf) as Hlen.
split; [split; [exact Hwf|]|].
- apply (bytes_of_view HH mem2 A (LC.cells_bytes cs)); [lia | lia |].
intros i Hi. rewrite (HV (A + Z.of_nat i) ltac:(lia)).
exact (view_of_lib mem_b m1 A (LC.cells_bytes cs) Hc HB i Hi).
- apply wr_at_of_apresent; [lia | lia | exact HP].
Qed.

(* ---- the premises of the two interceptor contracts, at a store that keeps [mem] outside the window ---- *)
Lemma keep_A : forall (mem1 : word -> option byte) (regs1 : bvmap 5 word) (stk1 : Z),
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo0 <= a < sp0) -> aview tfibsegs HH mem1 a = aview tfibsegs HH mem a) ->
(forall a, ascratch_stk stk1 regs1 a -> lo0 <= a < sp0) ->
astr_at tfibsegs W mem1 x str /\ aread_ok tfibsegs stk1 W regs1 mem1 x (astr_len str + 1)
/\ atail_vis tfibsegs W mem1 (x + astr_len str) /\ rt_rom_view tfibsegs B W mem1.
Proof.
intros mem1 regs1 stk1 HV Hsub.
pose proof spb as (P1 & P2 & P3). pose proof xbnd as (X0 & X1 & Y0 & Y1). pose proof hHLO.
pose proof SLL as HS. unfold astr_len in *.
pose proof hDS as DS. pose proof EA as EAx. rewrite EAx in DS.
destruct HSTR as (HBX & HNX). destruct RDX as (A0 & A1 & A2 & A3 & A4 & A5 & A6).
assert (VX : forall a, x <= a < x + (Z.of_nat (length str) + 1 + Z.of_nat (length sl)) ->
aview tfibsegs HH mem1 a = aview tfibsegs HH mem a).
{ intros a Ha. apply HV; [change (2 ^ 64) with 18446744073709551616; lia | lia]. }
assert (SH : forall z, 0 <= z < kHighMemEnd -> ~ (lo0 <= shadow_addr z < sp0)).
{ intros z Hz. pose proof (YE2y.shadow_addr_bounds z Hz) as (S1 & S2).
unfold kHighShadowEnd, kLowMemEnd, MCSPN_K, ESTACK in *. lia. }
split; [|split; [|split]].
- split; [|exact HNX]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite VX by lia. exact (HBX i ltac:(rewrite length_app; cbn [length]; lia)).
- split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split; [|split; [exact A4|split]].
+ intros a Ha. split.
* rewrite VX by lia. exact (proj1 (A3 a Ha)).
* intros Hs. exact (proj2 (A3 a Ha) ltac:(unfold ascratch_stk; exact (Hsub a Hs))).
+ eapply range_addressable_agree; [|exact A5]. intros z Hz.
change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
apply HV; [pose proof (YE2y.shadow_addr_bounds z ltac:(unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia)) as (S1 & S2);
unfold kHighShadowEnd, kLowMemEnd in *; change (2 ^ 64) with 18446744073709551616; lia
| apply SH; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia].
+ intros Hn s Hs. rewrite HV.
* exact (A6 Hn s Hs).
* assert (Hq : 0 <= 8 * (s - SHADOW_OFF) < kHighMemEnd).
{ unfold shadow_addr, SHADOW_OFF, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
clear - Hs A0 A1 A4 Hn. Z.div_mod_to_equations. lia. }
pose proof (YE2y.shadow_addr_bounds _ Hq) as (S1 & S2).
assert (Es : shadow_addr (8 * (s - SHADOW_OFF)) = s)
by (unfold shadow_addr, SHADOW_OFF in *; Z.div_mod_to_equations; lia).
rewrite Es in S1, S2. unfold kHighShadowEnd, kLowMemEnd in *.
change (2 ^ 64) with 18446744073709551616. lia.
* assert (Hq : 0 <= 8 * (s - SHADOW_OFF) < kHighMemEnd).
{ unfold shadow_addr, SHADOW_OFF, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
clear - Hs A0 A1 A4 Hn. Z.div_mod_to_equations. lia. }
assert (Es : shadow_addr (8 * (s - SHADOW_OFF)) = s)
by (unfold shadow_addr, SHADOW_OFF in *; Z.div_mod_to_equations; lia).
rewrite <- Es. apply SH. exact Hq.
- intros a Ha. rewrite HV.
+ exact (TLX a Ha).
+ pose proof (Z.mod_pos_bound (x + Z.of_nat (length str)) 8 ltac:(lia)).
change (2 ^ 64) with 18446744073709551616. lia.
+ pose proof (Z.mod_pos_bound (x + Z.of_nat (length str)) 8 ltac:(lia)).
unfold MCSPN_K, ESTACK in *. clear - Ha DS HS P3 P1 X0 X1. Z.div_mod_to_equations. lia.
- apply (rt_rom_view_keep tfibsegs B W mem mem1 HROM). intros a Hr _ _.
pose proof (cspn_in_rom_low a Hr) as Hb. unfold TFIB_IMG_END in Hb.
apply HV; [change (2 ^ 64) with 18446744073709551616; lia | lia].
Qed.

Lemma canon_eqR : forall pc mm,
canon_at regs pc mm = LMS.MS RROW fp_regs (Z_to_bv 64 pc) fp_csr None mm (LP.seg_rom rsegs).
Proof. intros pc mm. reflexivity. Qed.

Lemma entry_facts : RtSStrcspnMW.ENTRY (getr regs 2) (getr regs 10) (getr regs 11) m0 str sl set lo0
(Z_to_bv 64 canv) m0.
Proof.
unfold RtSStrcspnMW.ENTRY. pose proof lib0 as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof nums as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hscr). pose proof EA as EAx. pose proof EB as EBy.
rewrite EAx, EBy.
split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
split; [exact B5|]. split; [exact B6|].
split; [apply (stk_keep mem sp0); [unfold MCSPN_K, ESTACK; lia | intros a Ha; apply Hscr;
unfold ascratch_stk; exact Ha]|].
split; [apply LF.munch_refl | apply LF.wmono_refl].
Qed.

(* ---- the store a segment leaves, lifted into the donor's model ---- *)
Lemma lift_bridge : forall ms0 ms' model',
R6.ms_eqv ms0 ms' -> same_but_materialized md model' ->
(forall xw : word, ~ (sp0 - 96 <= bv_unsigned xw < sp0) -> ms_mem ms0 xw = m0 xw) ->
(forall a, sp0 - 96 <= a < sp0 -> ms_mem ms0 (Z_to_bv 64 a) <> None) ->
AR tfibsegs B ly S W (munrestrict HH mem (ms_mem ms')) model'
/\ (forall a, 0 <= a < 2 ^ 64 -> ~ (lo0 <= a < sp0) ->
 aview tfibsegs HH (munrestrict HH mem (ms_mem ms')) a = aview tfibsegs HH mem a)
/\ (forall a, apresent HH mem a -> apresent HH (munrestrict HH mem (ms_mem ms')) a)
/\ (forall a, lo0 <= a < sp0 -> apresent HH (munrestrict HH mem (ms_mem ms')) a).
Proof.
intros ms0 ms' model' Heqv Hsbm MOUT MIN.
pose proof nums as (HAR & _ & _ & Hlo4 & Htop & T7 & T4 & _ & _ & Hscr).
pose proof Heqv as (_ & _ & _ & _ & _ & _ & Emem & _). rewrite Emem in MOUT, MIN.
destruct (win_mem HH mem (ms_mem ms') (sp0 - 96) sp0 MOUT MIN
ltac:(intros a Ha; apply Hscr; unfold ascratch_stk, MCSPN_K, ESTACK; lia)) as (AV & VIS & HB & PRS).
destruct (same_but_materialized_frame md model' Hsbm)
as (_ & E1 & E2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
split.
- apply (al_frame _ _ LAWS ly S W mem md _ model' HAR); [| exact VIS | exact E1 | exact E2 | exact E3 |].
+ intros a Hr Hown. apply AV; [exact Hr|]. intros Hw.
exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold MCSPN_K, ESTACK in *; lia) Hown).
+ intros a _ Hh. exact (HB a Hh).
- split; [intros a Ha Hn; apply AV; [exact Ha | unfold MCSPN_K, ESTACK in *; lia]|].
split; [exact PRS|]. intros a Ha. apply PRS. apply Hscr. unfold ascratch_stk. exact Ha.
Qed.

(* ---- the post of a segment that returns, as art_post at MCSPN_K ---- *)
Lemma post_of : forall (base : word -> option byte) mdb ms0 ms' model',
AR tfibsegs B ly S W base mdb -> same_but_materialized md mdb -> same_but_materialized mdb model' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo0 <= a < sp0) ->
 aview tfibsegs HH base a = aview tfibsegs HH mem a) ->
(forall a, apresent HH mem a -> apresent HH base a) ->
R6.ms_eqv ms0 ms' -> PST base ms0 ->
POSTQ W (mkCfg (unrestrict HH base ms') model').
Proof.
intros base mdb ms0 ms' model' HARb Hsb1 Hsb2 AVb PRb Heqv HQ.
destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E
& MUc & WMc & STKc).
pose proof spb as (P1 & P2 & P3). pose proof hHLO.
apply (art_post_comp B LAWS MCSPN_K 96 ly S W regs mem base md mdb (fun _ => False) QRET ms0 ms' model'
HPRE ltac:(unfold MCSPN_K, ESTACK; lia) HARb Hsb1 Hsb2 AVb PRb Heqv).
- rewrite E. reflexivity.
- rewrite E. reflexivity.
- rewrite E. reflexivity.
- rewrite E. reflexivity.
- rewrite E. reflexivity.
- rewrite E. reflexivity.
- rewrite E. keep_regs_r.
- intros xw Hxw. rewrite E. cbn [ms_mem LMS.MS]. apply MUc. cbn [LF.outside]. split; [exact Hxw | exact I].
- intros a Ha. rewrite E. cbn [ms_mem LMS.MS].
apply (nz_of_stk m' lo0 sp0 a STKc ltac:(unfold MCSPN_K, ESTACK; lia) ltac:(lia)).
- rewrite (ms_eqv_getr ms0 ms' 10 Heqv), E. reflexivity.
Qed.

(* ---- |set| = 1: the walk returns without leaving this model ---- *)
Lemma case_one : Z.of_nat (length set) = 1 -> SRr tfibsegs W (cfg_at tfibsegs MCSPN_ENTRY regs mem md) POSTQ.
Proof.
intros HK1.
pose proof nums as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & Hscr).
pose proof (proj2 HSTR) as HSN. pose proof (proj2 HSET) as HAN.
pose proof hSLK. pose proof hLO0. pose proof hLOS. pose proof hDS. pose proof hDC. pose proof hDG.
pose proof hDK. pose proof hSB. pose proof hCB. pose proof hHLO. pose proof entry_facts as HE.
apply (srr_of_canon W MCSPN_ENTRY regs mem md (PST mem) POSTQ).
- rewrite canon_eqR. apply cspn_entry_one with (slack := sl) (can := Z_to_bv 64 canv); try assumption.
- intros ms0 ms' model' HQ Heqv Hsbm Hcl.
apply (post_of mem md ms0 ms' model' HAR (same_but_materialized_refl md) Hsbm
ltac:(intros a _ _; reflexivity) ltac:(intros a Hp; exact Hp) Heqv HQ).
Qed.

(* ---- set = []: strchrnul calls the strlen interceptor ---- *)
Lemma case_nil : Z.of_nat (length set) = 0 -> SRr tfibsegs W (cfg_at tfibsegs MCSPN_ENTRY regs mem md) POSTQ.
Proof.
intros HK0.
pose proof nums as (HAR & Hra & Hal & Hlo4 & Htop & T7 & T4 & Hgp & Htp & Hscr).
pose proof spb as (P1 & P2 & P3). pose proof hHLO as HLO. pose proof xbnd as (X0 & X1 & Y0 & Y1).
pose proof (proj2 HSTR) as HSN. pose proof (proj2 HSET) as HAN.
pose proof hSLK. pose proof hLO0. pose proof hLOS. pose proof hDS. pose proof hDC. pose proof hDG.
pose proof hDK. pose proof hSB. pose proof hCB. pose proof entry_facts as HE.
apply (srr_of_canon_cont W MCSPN_ENTRY regs mem md
(cspn_strlen_call (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 10) (getr regs 11) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
(getr regs 27) fp_regs fp_csr lo0 (MEMB mem)) POSTQ).
- rewrite canon_eqR. apply cspn_entry_nil; try assumption.
- intros ms0 ms' model' HQ Heqv Hsbm Hcl.
destruct HQ as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & junk
& E & MEM1 & FR1 & FB1 & ST1).
pose proof MEM1 as (LB1 & LB2 & LG1 & LG2 & LK1 & LK2 & STK1 & MU1 & WM1 & FT1).
assert (MOUT : forall xw : word, ~ (sp0 - 96 <= bv_unsigned xw < sp0) -> ms_mem ms0 xw = m0 xw).
{ intros xw Hxw. rewrite E. cbn [ms_mem LMS.MS]. apply MU1. cbn [LF.outside]. split; [exact Hxw | exact I]. }
assert (MIN : forall a, sp0 - 96 <= a < sp0 -> ms_mem ms0 (Z_to_bv 64 a) <> None).
{ intros a Ha. rewrite E. cbn [ms_mem LMS.MS].
destruct (Z_lt_le_dec a (sp0 + -80)) as [Hl|Hl].
- exact (nz_of_cells m1 (sp0 + -96) [LC.C8 (getr regs 10); LC.C8 (Z_to_bv 64 0x9eee8)] a FR1
ltac:(cbn [LC.cells_size LC.csize Nat.add]; lia) ltac:(lia)).
- destruct (Z_lt_le_dec a (sp0 + -48)) as [Hl2|Hl2].
+ exact (nz_of_cells m1 (sp0 + -80) [LC.CB 32 junk] a FB1
ltac:(cbn [LC.cells_size LC.csize Nat.add]; lia) ltac:(lia)).
+ exact (nz_of_cells m1 (sp0 + -48)
[LC.C8 (Z_to_bv 64 canv); LC.C8 (getr regs 19); LC.C8 (getr regs 18); LC.C8 (getr regs 9);
LC.C8 (getr regs 8); LC.C8 (getr regs 1)] a FT1
ltac:(cbn [LC.cells_size LC.csize Nat.add]; lia) ltac:(lia)). }
destruct (lift_bridge ms0 ms' model' Heqv Hsbm MOUT MIN) as (HAR1 & AV1 & PR1 & PW1).
assert (Em1 : m1 = ms_mem ms').
{ pose proof Heqv as HQE. destruct HQE as (_ & _ & _ & _ & _ & _ & Hmm & _).
rewrite <- Hmm, E. reflexivity. }
rewrite Em1 in FT1, FR1, FB1.
assert (R1 : getr (ms_regs ms') 1 = Z_to_bv 64 0x9ecb4)
by (rewrite (ms_eqv_getr ms0 ms' 1 Heqv), E; reflexivity).
assert (R2 : getr (ms_regs ms') 2 = Z_to_bv 64 (sp0 + -96))
by (rewrite (ms_eqv_getr ms0 ms' 2 Heqv), E; reflexivity).
assert (R3 : getr (ms_regs ms') 3 = getr regs 3)
by (rewrite (ms_eqv_getr ms0 ms' 3 Heqv), E; reflexivity).
assert (R4 : getr (ms_regs ms') 4 = getr regs 4)
by (rewrite (ms_eqv_getr ms0 ms' 4 Heqv), E; reflexivity).
assert (R8 : getr (ms_regs ms') 8 = getr regs 10)
by (rewrite (ms_eqv_getr ms0 ms' 8 Heqv), E; reflexivity).
assert (R9 : getr (ms_regs ms') 9 = getr regs 11)
by (rewrite (ms_eqv_getr ms0 ms' 9 Heqv), E; reflexivity).
assert (R10 : getr (ms_regs ms') 10 = getr regs 10)
by (rewrite (ms_eqv_getr ms0 ms' 10 Heqv), E; reflexivity).
assert (R18 : getr (ms_regs ms') 18 = Z_to_bv 64 0x604158)
by (rewrite (ms_eqv_getr ms0 ms' 18 Heqv), E; reflexivity).
assert (R19 : getr (ms_regs ms') 19 = getr regs 19)
by (rewrite (ms_eqv_getr ms0 ms' 19 Heqv), E; reflexivity).
assert (R20 : getr (ms_regs ms') 20 = getr regs 20)
by (rewrite (ms_eqv_getr ms0 ms' 20 Heqv), E; reflexivity).
assert (R21 : getr (ms_regs ms') 21 = getr regs 21)
by (rewrite (ms_eqv_getr ms0 ms' 21 Heqv), E; reflexivity).
assert (R22 : getr (ms_regs ms') 22 = getr regs 22)
by (rewrite (ms_eqv_getr ms0 ms' 22 Heqv), E; reflexivity).
assert (R23 : getr (ms_regs ms') 23 = getr regs 23)
by (rewrite (ms_eqv_getr ms0 ms' 23 Heqv), E; reflexivity).
assert (R24 : getr (ms_regs ms') 24 = getr regs 24)
by (rewrite (ms_eqv_getr ms0 ms' 24 Heqv), E; reflexivity).
assert (R25 : getr (ms_regs ms') 25 = getr regs 25)
by (rewrite (ms_eqv_getr ms0 ms' 25 Heqv), E; reflexivity).
assert (R26 : getr (ms_regs ms') 26 = getr regs 26)
by (rewrite (ms_eqv_getr ms0 ms' 26 Heqv), E; reflexivity).
assert (R27 : getr (ms_regs ms') 27 = getr regs 27)
by (rewrite (ms_eqv_getr ms0 ms' 27 Heqv), E; reflexivity).
assert (SP1 : spZ (ms_regs ms') = sp0 - 96).
{ unfold spZ in *. rewrite R2. apply unsigned_lit_small.
change (2 ^ 64) with 18446744073709551616. lia. }
assert (RA1 : raZ (ms_regs ms') = 0x9ecb4).
{ unfold raZ. rewrite R1. apply unsigned_lit_small.
change (2 ^ 64) with 18446744073709551616. lia. }
assert (SUB1 : forall a, ascratch_stk ESTACK (ms_regs ms') a -> lo0 <= a < sp0).
{ intros a Ha. unfold ascratch_stk in Ha. rewrite SP1 in Ha. unfold MCSPN_K, ESTACK in *. lia. }
destruct (keep_A (munrestrict HH mem (ms_mem ms')) (ms_regs ms') ESTACK AV1 SUB1)
as (KSTR & KRD & KTL & KROM).
assert (CFG : mkCfg (unrestrict HH mem ms') model'
= cfg_at tfibsegs 0x4517c (ms_regs ms') (munrestrict HH mem (ms_mem ms')) model').
{ unfold cfg_at. f_equal. exact (unrestrict_at 0x4517c HH mem ms0 ms' Heqv
ltac:(rewrite E; reflexivity) ltac:(rewrite E; reflexivity) ltac:(rewrite E; reflexivity)
ltac:(rewrite E; reflexivity) ltac:(rewrite E; reflexivity) ltac:(rewrite E; reflexivity)). }
rewrite CFG.
eapply SRr_bind.
{ change 0x4517c with PC_strlen.
apply (RtSStrlen.cmd_strlen B LAWS TB ly S W (ms_regs ms') (munrestrict HH mem (ms_mem ms')) model' x str).
- split; [split; [exact HAR1|]|].
+ split; [rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity|].
split; [rewrite SP1; replace (sp0 - 96) with (sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
split; [rewrite SP1; unfold MCSPN_K, ESTACK in *; lia|].
split; [rewrite SP1; lia|].
split; [intros a Ha; apply PW1; unfold ascratch_stk in Ha; rewrite SP1 in Ha;
unfold MCSPN_K, ESTACK in *; lia|].
split; [rewrite R3; exact Hgp | rewrite R4; exact Htp].
+ split; [rewrite SP1; unfold MCSPN_K, ESTACK in *; lia|].
intros a Ha. apply PW1. exact (SUB1 a Ha).
- rewrite R10. exact G10.
- exact Hx0.
- exact KSTR.
- exact KRD.
- exact KTL.
- exact KROM. }
cbv beta. intros W2 c2 Hle (-> & regs2 & mem2 & md2 & Ec & HAR2 & KP2 & SBM2 & A102 & FR2 & PR2 & PW2).
rewrite Ec, RA1.
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lo0 <= a < sp0) ->
aview tfibsegs HH mem2 a = aview tfibsegs HH mem a).
{ intros a Ha Hn.
rewrite (FR2 a Ha ltac:(unfold ascratch_stk; rewrite SP1; unfold MCSPN_K, ESTACK in *; lia)
ltac:(intros HF; exact HF)).
exact (AV1 a Ha Hn). }
assert (PR2' : forall a, apresent HH mem a -> apresent HH mem2 a)
by (intros a Hp; apply PR2; apply PR1; exact Hp).
assert (PW2' : forall a, lo0 <= a < sp0 -> apresent HH mem2 a)
by (intros a Ha; apply PR2; apply PW1; exact Ha).
assert (VEQ : forall a, sp0 + -96 <= a < sp0 ->
aview tfibsegs HH mem2 a = aview tfibsegs HH (munrestrict HH mem (ms_mem ms')) a).
{ intros a Ha. apply FR2; [unfold MCSPN_K, ESTACK in *; lia| |intros HF; exact HF].
unfold ascratch_stk. rewrite SP1. unfold ESTACK. lia. }
assert (S2 : getr regs2 2 = Z_to_bv 64 (sp0 + -96))
by (rewrite <- R2; exact (KP2 2 ltac:(unfold acallee_saved; lia))).
assert (S3 : getr regs2 3 = getr regs 3)
by (rewrite <- R3; exact (KP2 3 ltac:(unfold acallee_saved; lia))).
assert (S4 : getr regs2 4 = getr regs 4)
by (rewrite <- R4; exact (KP2 4 ltac:(unfold acallee_saved; lia))).
assert (S8 : getr regs2 8 = getr regs 10)
by (rewrite <- R8; exact (KP2 8 ltac:(unfold acallee_saved; lia))).
assert (S9 : getr regs2 9 = getr regs 11)
by (rewrite <- R9; exact (KP2 9 ltac:(unfold acallee_saved; lia))).
assert (S18 : getr regs2 18 = Z_to_bv 64 0x604158)
by (rewrite <- R18; exact (KP2 18 ltac:(unfold acallee_saved; lia))).
assert (S19 : getr regs2 19 = getr regs 19)
by (rewrite <- R19; exact (KP2 19 ltac:(unfold acallee_saved; lia))).
assert (S20 : getr regs2 20 = getr regs 20)
by (rewrite <- R20; exact (KP2 20 ltac:(unfold acallee_saved; lia))).
assert (S21 : getr regs2 21 = getr regs 21)
by (rewrite <- R21; exact (KP2 21 ltac:(unfold acallee_saved; lia))).
assert (S22 : getr regs2 22 = getr regs 22)
by (rewrite <- R22; exact (KP2 22 ltac:(unfold acallee_saved; lia))).
assert (S23 : getr regs2 23 = getr regs 23)
by (rewrite <- R23; exact (KP2 23 ltac:(unfold acallee_saved; lia))).
assert (S24 : getr regs2 24 = getr regs 24)
by (rewrite <- R24; exact (KP2 24 ltac:(unfold acallee_saved; lia))).
assert (S25 : getr regs2 25 = getr regs 25)
by (rewrite <- R25; exact (KP2 25 ltac:(unfold acallee_saved; lia))).
assert (S26 : getr regs2 26 = getr regs 26)
by (rewrite <- R26; exact (KP2 26 ltac:(unfold acallee_saved; lia))).
assert (S27 : getr regs2 27 = getr regs 27)
by (rewrite <- R27; exact (KP2 27 ltac:(unfold acallee_saved; lia))).
apply (srr_of_canon W 0x9ecb4 regs2 mem2 md2 (PST mem2) POSTQ).
+ rewrite canon_eq.
assert (ER2 : R6.mkR_of regs2 = LF.mkR (getr regs2 1) (Z_to_bv 64 (sp0 + -96)) (getr regs 3) (getr regs 4)
(getr regs2 5) (getr regs2 6) (getr regs2 7) (getr regs 10) (getr regs 11)
(Z_to_bv 64 (astr_len str)) (getr regs2 11) (getr regs2 12) (getr regs2 13) (getr regs2 14)
(getr regs2 15) (getr regs2 16) (getr regs2 17) (Z_to_bv 64 0x604158) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
(getr regs 26) (getr regs 27) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31)).
{ unfold R6.mkR_of. f_equal; try reflexivity; try assumption. }
rewrite ER2.
apply cspn_after_strlen with (junk := junk) (slack := sl) (can := Z_to_bv 64 canv);
try assumption; try lia; try reflexivity.
* pose proof (lib_keep mem2 AV2) as (M1 & M2 & M3 & M4 & M5 & M6).
pose proof EA as EAx. pose proof EB as EBy. rewrite EAx, EBy.
split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
split; [exact M5|]. split; [exact M6|].
split; [apply (stk_keep mem2 (sp0 + -80)); [unfold MCSPN_K, ESTACK; lia | exact PW2']|].
split; [apply LF.munch_refl | split; [apply LF.wmono_refl|]].
apply (cells_keep mem (ms_mem ms') mem2 (sp0 + -48)); [exact Hcl | exact FT1 | | ];
intros a Ha; cbn [LC.cells_size LC.csize Nat.add] in Ha;
[apply VEQ; lia | apply PW2'; unfold MCSPN_K, ESTACK; lia].
* apply (cells_keep mem (ms_mem ms') mem2 (sp0 + -96)); [exact Hcl | exact FR1 | | ];
intros a Ha; cbn [LC.cells_size LC.csize Nat.add] in Ha;
[apply VEQ; lia | apply PW2'; unfold MCSPN_K, ESTACK; lia].
* apply (cells_keep mem (ms_mem ms') mem2 (sp0 + -80)); [exact Hcl | exact FB1 | | ];
intros a Ha; cbn [LC.cells_size LC.csize Nat.add] in Ha;
[apply VEQ; lia | apply PW2'; unfold MCSPN_K, ESTACK; lia].
* apply (stk_keep mem2 (sp0 + -96)); [unfold MCSPN_K, ESTACK; lia | exact PW2'].
+ intros ms2 ms2' model2' HQ2 Heqv2 Hsbm2 Hcl2.
apply (post_of mem2 md2 ms2 ms2' model2' HAR2
(same_but_materialized_trans _ _ _ Hsbm SBM2) Hsbm2 AV2 PR2' Heqv2 HQ2).
Qed.

(* ---- |set| >= 2: the walk builds the 256-bit set with the memset interceptor ---- *)
Lemma case_big : (2 <= Z.of_nat (length set))%Z ->
SRr tfibsegs W (cfg_at tfibsegs MCSPN_ENTRY regs mem md) POSTQ.
Proof.
intros HK2.
pose proof nums as (HAR & Hra & Hal & Hlo4 & Htop & T7 & T4 & Hgp & Htp & Hscr).
pose proof spb as (P1 & P2 & P3). pose proof hHLO as HLO. pose proof xbnd as (X0 & X1 & Y0 & Y1).
pose proof (proj2 HSTR) as HSN. pose proof (proj2 HSET) as HAN.
pose proof hSLK. pose proof hLO0. pose proof hLOS. pose proof hDS. pose proof hDC. pose proof hDG.
pose proof hDK. pose proof hSB. pose proof hCB. pose proof entry_facts as HE.
apply (srr_of_canon_cont W MCSPN_ENTRY regs mem md
(cspn_mset_call (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 10) (getr regs 11)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
(getr regs 27) fp_regs fp_csr (MEMB mem)) POSTQ).
- rewrite canon_eqR. apply cspn_entry_big; try assumption.
- intros ms0 ms' model' HQ Heqv Hsbm Hcl.
destruct HQ as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & junk & E & MEM1 & FB1).
pose proof MEM1 as (LB1 & LB2 & LG1 & LG2 & LK1 & LK2 & STK1 & MU1 & WM1 & FT1).
assert (MOUT : forall xw : word, ~ (sp0 - 96 <= bv_unsigned xw < sp0) -> ms_mem ms0 xw = m0 xw).
{ intros xw Hxw. rewrite E. cbn [ms_mem LMS.MS]. apply MU1. cbn [LF.outside]. split; [exact Hxw | exact I]. }
assert (MIN : forall a, sp0 - 96 <= a < sp0 -> ms_mem ms0 (Z_to_bv 64 a) <> None).
{ intros a Ha. rewrite E. cbn [ms_mem LMS.MS].
destruct (Z_lt_le_dec a (sp0 + -80)) as [Hl|Hl].
- exact (nz_of_stk m1 lo0 (sp0 + -80) a STK1 ltac:(unfold MCSPN_K, ESTACK in *; lia) ltac:(lia)).
- destruct (Z_lt_le_dec a (sp0 + -48)) as [Hl2|Hl2].
+ exact (nz_of_cells m1 (sp0 + -80) [LC.CB 32 junk] a FB1
ltac:(cbn [LC.cells_size LC.csize Nat.add]; lia) ltac:(lia)).
+ exact (nz_of_cells m1 (sp0 + -48)
[LC.C8 (Z_to_bv 64 canv); LC.C8 (getr regs 19); LC.C8 (getr regs 18); LC.C8 (getr regs 9);
LC.C8 (getr regs 8); LC.C8 (getr regs 1)] a FT1
ltac:(cbn [LC.cells_size LC.csize Nat.add]; lia) ltac:(lia)). }
destruct (lift_bridge ms0 ms' model' Heqv Hsbm MOUT MIN) as (HAR1 & AV1 & PR1 & PW1).
assert (Em1 : m1 = ms_mem ms').
{ pose proof Heqv as HQE. destruct HQE as (_ & _ & _ & _ & _ & _ & Hmm & _).
rewrite <- Hmm, E. reflexivity. }
rewrite Em1 in FT1.
assert (R1 : getr (ms_regs ms') 1 = Z_to_bv 64 0x9ee64)
by (rewrite (ms_eqv_getr ms0 ms' 1 Heqv), E; reflexivity).
assert (R2 : getr (ms_regs ms') 2 = Z_to_bv 64 (sp0 + -80))
by (rewrite (ms_eqv_getr ms0 ms' 2 Heqv), E; reflexivity).
assert (R3 : getr (ms_regs ms') 3 = getr regs 3)
by (rewrite (ms_eqv_getr ms0 ms' 3 Heqv), E; reflexivity).
assert (R4 : getr (ms_regs ms') 4 = getr regs 4)
by (rewrite (ms_eqv_getr ms0 ms' 4 Heqv), E; reflexivity).
assert (R8 : getr (ms_regs ms') 8 = getr regs 10)
by (rewrite (ms_eqv_getr ms0 ms' 8 Heqv), E; reflexivity).
assert (R9 : getr (ms_regs ms') 9 = getr regs 11)
by (rewrite (ms_eqv_getr ms0 ms' 9 Heqv), E; reflexivity).
assert (R10 : getr (ms_regs ms') 10 = Z_to_bv 64 (sp0 + -80))
by (rewrite (ms_eqv_getr ms0 ms' 10 Heqv), E; reflexivity).
assert (R11 : getr (ms_regs ms') 11 = Z_to_bv 64 0)
by (rewrite (ms_eqv_getr ms0 ms' 11 Heqv), E; reflexivity).
assert (R12 : getr (ms_regs ms') 12 = Z_to_bv 64 32)
by (rewrite (ms_eqv_getr ms0 ms' 12 Heqv), E; reflexivity).
assert (R18 : getr (ms_regs ms') 18 = Z_to_bv 64 0x604158)
by (rewrite (ms_eqv_getr ms0 ms' 18 Heqv), E; reflexivity).
assert (R19 : getr (ms_regs ms') 19 = Z_to_bv 64 (sp0 + -80))
by (rewrite (ms_eqv_getr ms0 ms' 19 Heqv), E; reflexivity).
assert (R20 : getr (ms_regs ms') 20 = getr regs 20)
by (rewrite (ms_eqv_getr ms0 ms' 20 Heqv), E; reflexivity).
assert (R21 : getr (ms_regs ms') 21 = getr regs 21)
by (rewrite (ms_eqv_getr ms0 ms' 21 Heqv), E; reflexivity).
assert (R22 : getr (ms_regs ms') 22 = getr regs 22)
by (rewrite (ms_eqv_getr ms0 ms' 22 Heqv), E; reflexivity).
assert (R23 : getr (ms_regs ms') 23 = getr regs 23)
by (rewrite (ms_eqv_getr ms0 ms' 23 Heqv), E; reflexivity).
assert (R24 : getr (ms_regs ms') 24 = getr regs 24)
by (rewrite (ms_eqv_getr ms0 ms' 24 Heqv), E; reflexivity).
assert (R25 : getr (ms_regs ms') 25 = getr regs 25)
by (rewrite (ms_eqv_getr ms0 ms' 25 Heqv), E; reflexivity).
assert (R26 : getr (ms_regs ms') 26 = getr regs 26)
by (rewrite (ms_eqv_getr ms0 ms' 26 Heqv), E; reflexivity).
assert (R27 : getr (ms_regs ms') 27 = getr regs 27)
by (rewrite (ms_eqv_getr ms0 ms' 27 Heqv), E; reflexivity).
assert (SP1 : spZ (ms_regs ms') = sp0 - 80).
{ unfold spZ in *. rewrite R2. apply unsigned_lit_small.
change (2 ^ 64) with 18446744073709551616. lia. }
assert (RA1 : raZ (ms_regs ms') = 0x9ee64).
{ unfold raZ. rewrite R1. apply unsigned_lit_small.
change (2 ^ 64) with 18446744073709551616. lia. }
assert (CFG : mkCfg (unrestrict HH mem ms') model'
= cfg_at tfibsegs 0x57674 (ms_regs ms') (munrestrict HH mem (ms_mem ms')) model').
{ unfold cfg_at. f_equal. exact (unrestrict_at 0x57674 HH mem ms0 ms' Heqv
ltac:(rewrite E; reflexivity) ltac:(rewrite E; reflexivity) ltac:(rewrite E; reflexivity)
ltac:(rewrite E; reflexivity) ltac:(rewrite E; reflexivity) ltac:(rewrite E; reflexivity)). }
rewrite CFG.
destruct (bitset_ok ly S W (munrestrict HH mem (ms_mem ms')) model' sp0 HAR1 Hal
ltac:(unfold MCSPN_K, ESTACK in *; lia) Htop) as (HRA & HHULL).
eapply SRr_bind.
{ apply (AMEMSET ly S W (ms_regs ms') (munrestrict HH mem (ms_mem ms')) model' (sp0 + -80) 0 32).
- split; [exact HAR1|].
split; [rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity|].
split; [rewrite SP1; replace (sp0 - 80) with (sp0 + (-5) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
split; [rewrite SP1; unfold MCSPN_K, ESTACK in *; lia|].
split; [rewrite SP1; lia|].
split; [intros a Ha; apply PW1; unfold ascratch_stk in Ha; rewrite SP1 in Ha;
unfold MCSPN_K, ESTACK in *; lia|].
split; [rewrite R3; exact Hgp | rewrite R4; exact Htp].
- exact R10.
- exact R11.
- exact R12.
- lia.
- lia.
- change (2 ^ 63) with 9223372036854775808. unfold kHighMemEnd in P2. lia.
- intros a Ha. split; [|split].
+ apply writable_of_apresent. apply PW1. unfold MCSPN_K, ESTACK in *. lia.
+ exact (al_stack _ _ LAWS ly S W (munrestrict HH mem (ms_mem ms')) model' a HAR1
ltac:(unfold MCSPN_K, ESTACK in *; lia)).
+ rewrite SP1. unfold ESTACK. lia.
- right. unfold kHighMemBeg, kHighMemEnd in *. lia.
- exact HRA.
- intros _. exact HHULL.
- exact I. }
cbv beta. intros W2 c2 Hle (-> & regs2 & mem2 & md2 & Ec & HAR2 & KP2 & SBM2 & A102 & ZER & FR2 & PR2).
rewrite Ec, RA1.
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lo0 <= a < sp0) ->
aview tfibsegs HH mem2 a = aview tfibsegs HH mem a).
{ intros a Ha Hn.
rewrite (FR2 a Ha ltac:(unfold MCSPN_K, ESTACK in *; lia)
ltac:(rewrite SP1; unfold MCSPN_K, ESTACK in *; lia)).
exact (AV1 a Ha Hn). }
assert (PR2' : forall a, apresent HH mem a -> apresent HH mem2 a)
by (intros a Hp; apply PR2; apply PR1; exact Hp).
assert (PW2' : forall a, lo0 <= a < sp0 -> apresent HH mem2 a)
by (intros a Ha; apply PR2; apply PW1; exact Ha).
assert (VEQ : forall a, sp0 + -48 <= a < sp0 ->
aview tfibsegs HH mem2 a = aview tfibsegs HH (munrestrict HH mem (ms_mem ms')) a).
{ intros a Ha. apply FR2; [unfold MCSPN_K, ESTACK in *; lia | lia |].
rewrite SP1. unfold ESTACK. lia. }
(* the 32 bytes the interceptor zeroed, as the walk's empty set *)
assert (BM0 : LSt.rw_cells rsegs (mrestrict HH mem2) (sp0 + -80) (RtSStrcspnMW.bm [])).
{ apply (RtSStrcspnMW.bm0_of (mrestrict HH mem2) (sp0 + -80) 32 (repeat (Z_to_bv 8 0) 32));
[| reflexivity | vm_compute; reflexivity].
split; [split; [cbn [LC.cells_wf LC.cell_wf]; split; [apply repeat_length | exact I]|]|].
- apply (bytes_of_view HH mem2 (sp0 + -80) (LC.cells_bytes [LC.CB 32 (repeat (Z_to_bv 8 0) 32)]));
[unfold MCSPN_K, ESTACK in *; lia
| cbn [LC.cells_bytes LC.cbytes]; rewrite app_nil_r, repeat_length;
change (2 ^ 64) with 18446744073709551616; lia |].
intros i Hi. cbn [LC.cells_bytes LC.cbytes] in Hi |- *. rewrite app_nil_r in Hi |- *.
rewrite repeat_length in Hi.
rewrite (ZER (Z.of_nat i) ltac:(lia)), (nth_rep0 32 i (Z_to_bv 8 0) Hi). reflexivity.
- apply wr_at_of_apresent; [unfold MCSPN_K, ESTACK in *; lia
| cbn [LC.cells_size LC.csize Nat.add]; change (2 ^ 64) with 18446744073709551616; lia |].
intros a Ha. cbn [LC.cells_size LC.csize Nat.add] in Ha. apply PW2'.
unfold MCSPN_K, ESTACK in *. lia. }
assert (S2 : getr regs2 2 = Z_to_bv 64 (sp0 + -80))
by (rewrite <- R2; exact (KP2 2 ltac:(unfold acallee_saved; lia))).
assert (S3 : getr regs2 3 = getr regs 3)
by (rewrite <- R3; exact (KP2 3 ltac:(unfold acallee_saved; lia))).
assert (S4 : getr regs2 4 = getr regs 4)
by (rewrite <- R4; exact (KP2 4 ltac:(unfold acallee_saved; lia))).
assert (S8 : getr regs2 8 = getr regs 10)
by (rewrite <- R8; exact (KP2 8 ltac:(unfold acallee_saved; lia))).
assert (S9 : getr regs2 9 = getr regs 11)
by (rewrite <- R9; exact (KP2 9 ltac:(unfold acallee_saved; lia))).
assert (S18 : getr regs2 18 = Z_to_bv 64 0x604158)
by (rewrite <- R18; exact (KP2 18 ltac:(unfold acallee_saved; lia))).
assert (S19 : getr regs2 19 = Z_to_bv 64 (sp0 + -80))
by (rewrite <- R19; exact (KP2 19 ltac:(unfold acallee_saved; lia))).
assert (S20 : getr regs2 20 = getr regs 20)
by (rewrite <- R20; exact (KP2 20 ltac:(unfold acallee_saved; lia))).
assert (S21 : getr regs2 21 = getr regs 21)
by (rewrite <- R21; exact (KP2 21 ltac:(unfold acallee_saved; lia))).
assert (S22 : getr regs2 22 = getr regs 22)
by (rewrite <- R22; exact (KP2 22 ltac:(unfold acallee_saved; lia))).
assert (S23 : getr regs2 23 = getr regs 23)
by (rewrite <- R23; exact (KP2 23 ltac:(unfold acallee_saved; lia))).
assert (S24 : getr regs2 24 = getr regs 24)
by (rewrite <- R24; exact (KP2 24 ltac:(unfold acallee_saved; lia))).
assert (S25 : getr regs2 25 = getr regs 25)
by (rewrite <- R25; exact (KP2 25 ltac:(unfold acallee_saved; lia))).
assert (S26 : getr regs2 26 = getr regs 26)
by (rewrite <- R26; exact (KP2 26 ltac:(unfold acallee_saved; lia))).
assert (S27 : getr regs2 27 = getr regs 27)
by (rewrite <- R27; exact (KP2 27 ltac:(unfold acallee_saved; lia))).
apply (srr_of_canon W 0x9ee64 regs2 mem2 md2 (PST mem2) POSTQ).
+ rewrite canon_eq.
assert (ER2 : R6.mkR_of regs2 = LF.mkR (getr regs2 1) (Z_to_bv 64 (sp0 + -80)) (getr regs 3) (getr regs 4)
(getr regs2 5) (getr regs2 6) (getr regs2 7) (getr regs 10) (getr regs 11)
(getr regs2 10) (getr regs2 11) (getr regs2 12) (getr regs2 13) (getr regs2 14)
(getr regs2 15) (getr regs2 16) (getr regs2 17) (Z_to_bv 64 0x604158) (Z_to_bv 64 (sp0 + -80))
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
(getr regs 26) (getr regs 27) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31)).
{ unfold R6.mkR_of. f_equal; try reflexivity; try assumption. }
rewrite ER2.
apply cspn_after_mset with (slack := sl) (can := Z_to_bv 64 canv); try assumption; try lia; try reflexivity.
* pose proof (lib_keep mem2 AV2) as (M1 & M2 & M3 & M4 & M5 & M6).
pose proof EA as EAx. pose proof EB as EBy. rewrite EAx, EBy.
split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
split; [exact M5|]. split; [exact M6|].
split; [apply (stk_keep mem2 (sp0 + -80)); [unfold MCSPN_K, ESTACK; lia | exact PW2']|].
split; [apply LF.munch_refl | split; [apply LF.wmono_refl|]].
apply (cells_keep mem (ms_mem ms') mem2 (sp0 + -48)); [exact Hcl | exact FT1 | | ];
intros a Ha; cbn [LC.cells_size LC.csize Nat.add] in Ha;
[apply VEQ; lia | apply PW2'; unfold MCSPN_K, ESTACK; lia].
+ intros ms2 ms2' model2' HQ2 Heqv2 Hsbm2 Hcl2.
apply (post_of mem2 md2 ms2 ms2' model2' HAR2
(same_but_materialized_trans _ _ _ Hsbm SBM2) Hsbm2 AV2 PR2' Heqv2 HQ2).
Qed.

Lemma main : SRr tfibsegs W (cfg_at tfibsegs MCSPN_ENTRY regs mem md) POSTQ.
Proof.
destruct (Z.eq_dec (Z.of_nat (length set)) 0) as [H0|H0]; [exact (case_nil H0)|].
destruct (Z.eq_dec (Z.of_nat (length set)) 1) as [H1|H1]; [exact (case_one H1)|].
apply case_big. lia.
Qed.

End t.

Theorem cmd_mcspn : amcspn_realizes B MCSPN_ENTRY A_SSP_GOT A_SSP_GUARD.
Proof.
intros ly S W regs mem md x y str set GRD HPRE G10 G11 Hx0 Hy0 HSTR HSET RDX RDY TLX HROM.
destruct GRD as (HGOT & canv & HCAN).
pose proof RDX as (A0 & A1 & _).
pose proof (Z.mod_pos_bound (x + astr_len str) 8 ltac:(lia)) as Hmd.
destruct (bytes_exist_view (w_H W) mem (x + astr_len str + 1) (Z.to_nat (7 - (x + astr_len str) mod 8)))
as (sl & Lsl & Bsl).
- unfold astr_len in *. lia.
- rewrite Z2Nat.id by lia. unfold astr_len in *.
change (2 ^ 63) with 9223372036854775808 in A1. change (2 ^ 64) with 18446744073709551616. lia.
- intros i Hi. apply TLX. unfold astr_len in *. split; [lia|].
assert (Hi' : Z.of_nat i <= 6 - (x + Z.of_nat (length str)) mod 8) by lia.
clear - Hi' Hmd. unfold astr_len in *. Z.div_mod_to_equations. lia.
- exact (main ly S W regs mem md x y canv str set sl HGOT HCAN HPRE G10 G11 Hx0 Hy0 HSTR HSET RDX RDY TLX
HROM ltac:(rewrite Lsl, Z2Nat.id by lia; reflexivity) Bsl).
Qed.

End c.
