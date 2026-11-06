(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: amreal_then_SRr as in cgif_file_fuzzer's lib/A/AFeu.v, and the lemmas that move a malloc leaf (lib/A/Rt/RtDDefs.v malloc_leaf_w) between the scratch windows and the register files of plugin-hostd/fuzz_command's inner malloc entries: the model's malloc_post puts a new block below the stack, so a wider window keeps its bytes present. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtDMallocLeaf.v (donor image sha256 c0661b96b5bd), with its module paths changed, names CmdBSyms -> SegBSyms. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/RtDMallocLeaf.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG07 YG0k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YFfk.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* A model step whose post is followed by a run of the machine (cgif lib/A/AFeu.v amreal_then_SRr). *)
Lemma dm_amreal_then_SRr {R} : forall (t : itree astate R) (W : world tfibsegs) c
(P Q : R -> world tfibsegs -> config -> Prop),
amreal tfibsegs t W c P -> (forall r W' c', P r W' c' -> SRr tfibsegs W' c' (Q r)) ->
amreal tfibsegs t W c Q.
Proof.
induction t as [r | q s k IH | pc | f]; intros W c P Q H HK; cbn [amreal] in *.
- eapply SRr_bind; [exact H|]. intros W' c' _ HP. exact (HK r W' c' HP).
- eapply SRr_mono; [exact H|]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; intros i Hi; eapply IH; [apply Hc, Hi | exact HK]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact Hc | exact HK].
- exact H.
- exact I.
Qed.

(* Every path of the model's malloc ends with the new block (if any) in the block list (YG07.v malloc_ok). *)
Lemma dm_malloc_apost : forall U S n tr,
universe_ok U -> Wf U S -> aregime S -> 0 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX -> tr_admit U S tr ->
apost (malloc n tr S) (fun r => fst r <> PNull -> In (fst r, n) (blocks (snd r))).
Proof.
intros U S n tr HU HW HR Hn Hl Ht trc [p s'] Hy.
pose proof (atok_apath_flag (malloc n tr S) true (malloc_post U S n) trc (p, s')
(malloc_ok U S n tr HU HW HR Hn Hl Ht) Hy) as HP.
unfold malloc_post in HP. cbn [fst snd]. intros Hp.
destruct HP as (_ & _ & _ & _ & Hb & _).
destruct p; first [ exfalso; apply Hp; reflexivity
| destruct Hb as [Hb _]; rewrite Hb; apply in_or_app; right; left; reflexivity ].
Qed.

(* A present byte at a high address whose view is unchanged stays present (YCbq.v apresent_transfer, for
   addresses above the image). *)
Lemma dm_apresent_hi : forall (H H' : word -> bool) (m m' : word -> option byte) a,
TFIB_IMG_END <= a < 2 ^ 64 -> aview tfibsegs H' m' a = aview tfibsegs H m a -> apresent H m a -> apresent H' m' a.
Proof.
intros H H' m m' a Ha E [Hh [b Hb]].
unfold aview, mbyte, mrestrict in E. rewrite Hh, Hb in E. rewrite (seg_rom_none_high a Ha) in E.
destruct (H' (Z_to_bv 64 a)) eqn:Hh'; [cbn in E; discriminate E|].
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Hm'; [|cbn in E; discriminate E].
split; [exact Hh' | exists b'; exact Hm'].
Qed.

Variable B : asyms.
Hypothesis TB : SegBSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* A live block lies below the stack (AR_blocks_law, layout_ok lo_stk_ceil). *)
Lemma dm_blocks_below : forall ly S W mem md p n,
AR tfibsegs B ly S W mem md -> In (p, n) (blocks S) -> sptr_addr B ly p + req_size n <= ly_stk_lo ly.
Proof.
intros ly S W mem md p n HAR Hin.
assert (Hin' : In (sptr_addr B ly p, n) (map (fun b => (sptr_addr B ly (fst b), snd b)) (blocks S)))
by exact (in_map (fun b => (sptr_addr B ly (fst b), snd b)) (blocks S) (p, n) Hin).
destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hin') as (_ & _ & Hc & _).
pose proof (lo_stk_ceil ly (am_layout B ly S _ (proj1 HAR))) as SC. unfold ASAN_CEIL in SC. lia.
Qed.

(* The window of a malloc leaf widened from k1 to k2: the bytes between the two were present before the call,
   and the call leaves them alone (they are stack bytes, not owned, not scratch, not in the new block). *)
Lemma dm_leaf_widen : forall k1 k2 ly S W regs mem md n r W' c',
k1 <= k2 -> AR tfibsegs B ly S W mem md ->
ly_stk_lo ly + k2 <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - k2 <= a < spZ regs -> apresent (w_H W) mem a) ->
(fst r <> PNull -> In (fst r, n) (blocks (snd r))) ->
malloc_leaf_w tfibsegs B k1 ly S W regs mem md n r W' c' ->
malloc_leaf_w tfibsegs B k2 ly S W regs mem md n r W' c'.
Proof.
intros k1 k2 ly S W regs mem md n r W' c' Hk HAR Hlo Hhi Hpres HB
(ly' & regs' & mem' & md' & Hc & (HAR' & Hle & Hwle & Hrp & Hio & Hfr & Hp) & H10 & Hqt).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [|split; [exact H10 | exact Hqt]].
pose proof Hle as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof (lo_top ly (am_layout B ly S _ (proj1 HAR))) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (STK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly ->
~ (fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)).
{ intros a Ha [Hnn Hin]. pose proof (dm_blocks_below ly' (snd r) W' mem' md' (fst r) n HAR' (HB Hnn)) as X.
rewrite Elo in X. lia. }
split; [exact HAR'|]. split; [exact Hle|]. split; [exact Hwle|]. split; [exact Hrp|]. split; [exact Hio|]. split.
- intros a Ha Ho Ho' Hs HE. apply Hfr; try assumption. intros Hs1. apply Hs. unfold ascratch in *.
destruct Hs1 as [Hs1|Hs1]; [left; lia | right; exact Hs1].
- intros a Ha. destruct (Z_lt_le_dec a (spZ regs - k1)) as [Hgap|Hin]; [|apply Hp; lia].
assert (Hst : ly_stk_lo ly <= a < ly_stk_hi ly) by lia.
apply (dm_apresent_hi (w_H W) (w_H W') mem mem' a); [unfold TFIB_IMG_END; lia | | apply Hpres; lia].
apply Hfr; [lia | exact (al_stack _ _ LAWS ly S W mem md a HAR Hst)
| apply (al_stack _ _ LAWS ly' (snd r) W' mem' md' a HAR'); rewrite Elo, Ehi; exact Hst | | apply STK; exact Hst].
unfold ascratch. rewrite (ts_errno B TB). unfold TFIB_ERRNO. intros [X|X]; lia.
Qed.

(* A malloc leaf stated for a register file that agrees with another on every register but x0, and a model that
   differs only in its materialized pages, is the leaf of the other. *)
Lemma dm_bv5 : forall q, 0 <= q < 32 -> bv_unsigned (Z_to_bv 5 q) = q.
Proof.
intros q Hq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. exact Hq.
Qed.
Lemma dm_leaf_regs : forall k ly S W regs regs1 mem md md1 n r W' c',
(forall x : bv 5, 1 <= bv_unsigned x -> getr regs1 x = getr regs x) ->
same_but_materialized md md1 ->
malloc_leaf_w tfibsegs B k ly S W regs1 mem md1 n r W' c' ->
malloc_leaf_w tfibsegs B k ly S W regs mem md n r W' c'.
Proof.
intros k ly S W regs regs1 mem md md1 n r W' c' GA SBM
(ly' & regs' & mem' & md' & Hc & (HAR' & Hle & Hwle & Hrp & Hio & Hfr & Hp) & H10 & Hqt).
assert (G1 : getr regs1 1%bv = getr regs 1%bv) by (apply GA; vm_compute; discriminate).
assert (G2 : getr regs1 2%bv = getr regs 2%bv) by (apply GA; vm_compute; discriminate).
assert (SP : spZ regs1 = spZ regs) by (unfold spZ; rewrite G2; reflexivity).
exists ly', regs', mem', md'.
split; [unfold raZ in Hc |- *; rewrite G1 in Hc; exact Hc|].
split; [|split; [exact H10 | exact Hqt]].
split; [exact HAR'|]. split; [exact Hle|]. split; [exact Hwle|].
split.
{ intros q Hq. rewrite (Hrp q Hq). apply GA. unfold acallee_saved in Hq. rewrite dm_bv5 by lia. lia. }
split.
{ destruct Hio as (F1 & F2 & F3 & F4).
destruct (same_but_materialized_frame md md1 SBM) as (M1 & _ & _ & M4 & M5 & M6 & _).
unfold same_io. rewrite F1, F2, F3, F4, M1, M4, M5, M6. repeat split; reflexivity. }
split.
{ intros a Ha Ho Ho' Hs HE. apply Hfr; try assumption. unfold ascratch in *. rewrite SP. exact Hs. }
intros a Ha. apply Hp. rewrite SP. exact Ha.
Qed.

(* same_io composes with a materialization on either side *)
Lemma dm_same_io_trans : forall md1 md2 md3, same_io md1 md2 -> same_io md2 md3 -> same_io md1 md3.
Proof. intros md1 md2 md3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold same_io. rewrite B1, B2, B3, B4. auto. Qed.
Lemma dm_same_io_sbm : forall md md', same_but_materialized md md' -> same_io md md'.
Proof.
intros md md' S. destruct (same_but_materialized_frame md md' S) as (M1 & _ & _ & M4 & M5 & M6 & _).
unfold same_io. rewrite M1, M4, M5, M6. repeat split; reflexivity.
Qed.

(* lib/A/AFl3.v aview_range, rdword_range *)
Lemma dm_aview_range : forall H mem a v, aview tfibsegs H mem a = Some v -> 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as X. unfold bv_modulus in X. cbn in X. lia.
Qed.
Lemma dm_rdword_range : forall H mem a v, rdword (aview tfibsegs H mem) a = Some v -> 0 <= v < 2 ^ 64.
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
pose proof (dm_aview_range _ _ _ _ E0). pose proof (dm_aview_range _ _ _ _ E1). pose proof (dm_aview_range _ _ _ _ E2).
pose proof (dm_aview_range _ _ _ _ E3). pose proof (dm_aview_range _ _ _ _ E4). pose proof (dm_aview_range _ _ _ _ E5).
pose proof (dm_aview_range _ _ _ _ E6). pose proof (dm_aview_range _ _ _ _ E7).
lia.
Qed.
(* the return addresses of a frame chain read through the view are words *)
Lemma dm_fpchain_bound : forall H mem bp top ch,
fpchain (rdword (aview tfibsegs H mem)) bp top ch -> Forall (fun r => 0 <= snd (fst r) < 2 ^ 64) ch.
Proof.
intros H mem bp top ch. revert bp. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hc; [constructor|].
cbn [fpchain] in Hc. destruct Hc as (_ & _ & Hra & _ & _ & Hrest).
constructor; [cbn [fst snd]; exact (dm_rdword_range _ _ _ _ Hra)|].
destruct (bad_next fp top nfp); [subst rest; constructor | exact (IH nfp Hrest)].
Qed.
(* an inner entry's trace holds at least the unwinder pc *)
Lemma dm_trace_len1 : forall ly pc0 regs ch, (1 <= length (inner_trace ly pc0 regs ch))%nat.
Proof.
intros ly pc0 regs ch. unfold inner_trace, call_trace.
destruct (spZ regs <=? ly_bot ly); [cbn; lia|].
destruct (frame0_ok ly regs); [|cbn; lia].
unfold unwind_of_chain, kUnwindMax. cbn [firstn length]. lia.
Qed.
(* every frame of an inner entry's trace is a word *)
Lemma dm_trace_bound : forall ly pc0 regs ch,
0 <= pc0 < 2 ^ 64 -> Forall (fun r => 0 <= snd (fst r) < 2 ^ 64) ch ->
forall x, In x (inner_trace ly pc0 regs ch) -> 0 <= x < 2 ^ 64.
Proof.
intros ly pc0 regs ch Hp HF x Hx. unfold inner_trace, call_trace in Hx.
destruct (spZ regs <=? ly_bot ly); [destruct Hx as [<-|[]]; exact Hp|].
destruct (frame0_ok ly regs); [|destruct Hx as [<-|[]]; exact Hp].
unfold unwind_of_chain in Hx.
set (l := pc0 :: flat_map (fun r => match r with (_, ra, _) => if ra =? pc0 then [] else [ra] end)
((spZ regs, raZ regs, s0Z regs) :: ch)) in Hx.
assert (Hx' : In x (firstn kUnwindMax l ++ skipn kUnwindMax l)) by (apply in_or_app; left; exact Hx).
rewrite firstn_skipn in Hx'. subst l. destruct Hx' as [<-|Hx']; [exact Hp|].
apply in_flat_map in Hx' as ([[fp ra] nfp] & Hin & Hx').
destruct (ra =? pc0); [destruct Hx'|]. destruct Hx' as [<-|[]].
destruct Hin as [Heq|Hin].
- injection Heq as _ <- _. unfold raZ. apply u64_range.
- exact (proj1 (Forall_forall _ _) HF _ Hin).
Qed.
Lemma dm_rd32_of_val_mem : forall H mem a v, val_mem tfibsegs (mrestrict H mem) a 4 v -> rd32 (aview tfibsegs H mem) a v.
Proof.
intros H mem a v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.
(* bytes outside a changed range keep their value *)
Lemma dm_val_mem_out : forall H (mem mem' : word -> option byte) lo hi a n v,
(forall x : word, ~ (lo <= bv_unsigned x < hi) -> mem' x = mem x) ->
0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= lo \/ hi <= a) ->
val_mem tfibsegs (mrestrict H mem) a n v -> val_mem tfibsegs (mrestrict H mem') a n v.
Proof.
intros H mem mem' lo hi a n v MEQ Ha Hn Hout Hv. apply (val_mem_frame H mem mem' a n v); [|exact Hv].
intros k Hk. apply MEQ. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma dm_mbyte_of_aview : forall H H' (m m' : word -> option byte) a,
aview tfibsegs H' m' a = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H' m') a) as [b'|], (mbyte tfibsegs (mrestrict H m) a) as [b|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
(* a stack region kept by a call that changed only bytes below it *)
Lemma dm_kept_of_eq : forall E (H : word -> bool) (mem mem' : word -> option byte) n lo hi wlo whi cs sp xlo xhi,
bv_unsigned (ew E n) = sp ->
(forall z : word, ~ (xlo <= bv_unsigned z < xhi) -> mem' z = mem z) ->
alloc_ceiling <= sp + lo -> sp + hi <= 2 ^ 64 -> xhi <= sp + lo -> lo <= wlo -> whi <= hi ->
region_kept tfibsegs E (mrestrict H mem) (mrestrict H mem') (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H mem mem' n lo hi wlo whi cs sp xlo xhi Hn MEQ Hc Hh Hx Hw1 Hw2.
apply (region_kept_stack tfibsegs E (mrestrict H mem) (mrestrict H mem') n lo hi wlo whi cs sp xlo xhi Hn); try assumption.
intros x Hx1 Hx2. pose proof alloc_ceiling_val as AC.
assert (E1 : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) by (apply MEQ; rewrite unsigned_lit_small by lia; exact Hx2).
split.
- unfold mbyte, mrestrict. rewrite E1. reflexivity.
- unfold writable_at, wview, mrestrict. rewrite E1. tauto.
Qed.
(* a stack region kept by a call whose post says only that its bytes look the same and stay present *)
Lemma dm_kept_of_view : forall E (H H' : word -> bool) (mem mem' : word -> option byte) n lo hi wlo whi cs b,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview tfibsegs H' mem' a = aview tfibsegs H mem a) ->
(forall a, b + wlo <= a < b + whi -> TFIB_IMG_END <= a < 2 ^ 64 /\ apresent H' mem' a) ->
region_kept tfibsegs E (mrestrict H mem) (mrestrict H' mem') (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H' mem mem' n lo hi wlo whi cs b Hn HV HP. unfold region_kept.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]. rewrite Hn. split.
- intros a Ha. apply dm_mbyte_of_aview. apply HV. exact Ha.
- intros a Ha _. destruct (HP a Ha) as [Hr Hp]. exact (apresent_writable H' mem' a Hr Hp).
Qed.

End l.
