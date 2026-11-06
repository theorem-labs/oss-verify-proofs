(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACf3.v, with its module paths, module names, addresses and numbers changed; 237 of its 313 lines of code are new or changed and 235 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgMain4b.v of this library, for reac-pw/fuzz_pin's
   image B (fuzz_pin.asan-ubsan, sha256 d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f). What
   differs: the imports are image B's lib/AU twins (the core's Y files, lib/AU/PPgSat.v, PPgMainCall.v, PPgMainRt.v,
   PPgMainSt.v; the shared texts lib/A/PPgBase.v, PPgCSpec.v and lib/A/Prog/PinBlkTail.v are the same); the bridge
   is at image B's table (PM_CAT = lib/AU/PPgSat.v's PIN_CAT 0x98000, the same 11 display pointers); the tail is
   image B's: ss_F at 0x80960 (`mv a0,s3`), the call of free at 0x80964 (`jal 52b50`, the same wrapper address in
   both images) and its return address 0x80968 (RT_free_ra, lib/AU/PPgMainRt.v), where ss_X is. The text below is
   the A file's; where it names image A's addresses 0x8092c / 0x80930 / 0x80934, image B's are 0x80960 / 0x80964 /
   0x80968. *)
(* Two self-contained parts of segment S4 of reac-pw/fuzz_pin's ASan harness walk (LLVMFuzzerTestOneInput 0x806b4,
   fuzz_pin.asan sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16), used by lib/A/PPgMain4.v:
   (1) the pure bridge: the three argument words the harness hands reac_box_pin_parse at 0x80900 (flag bit 0 clears
   the spec pointer, bit 1 the model cell, bit 2 the label cell) make the contract's result pin_parse_res at image
   A's table the harness's own expectation (pin_spec.harness_agrees / harness_known / harness_row_label, at the
   display pointers PM_DP), and the spec string is the whole heap block (q, |s| + 1) (CP1.2);
   (2) the tail of S4: the state ss_F at 0x8092c (a0 = q, then the call of free at 0x80930) and its run through
   free into ss_X (0x80934).
   This file proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk, S4: its bridge and its tail). *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05 YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import PPgSat PPgMainCall PPgMainRt PPgMainSt.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.Prog Require Import PinBlkTail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the three argument words of the call at 0x80900, as functions of the flags byte *)
Definition pm_arg (fl : Z) (bit : Z) (x : Z) : Z := if Z.testbit fl bit then 0 else x.

(* helpers (local) *)
Lemma pm_arg_live0 : forall fl x, fl_live fl = true -> pm_arg fl 0 x = x.
Proof.
intros fl x H. unfold pm_arg. destruct (Z.testbit fl 0) eqn:E; [|reflexivity].
unfold fl_live in H. rewrite E in H. cbn in H. discriminate.
Qed.
Lemma harness_want_lt : forall fl s i, harness_want fl s = Some i -> (i < CAT_N)%nat.
Proof.
intros fl s i. unfold harness_want. destruct (_ && _); [|discriminate].
intros H. exact (proj1 (row_of_some _ _ H)).
Qed.
Lemma harness_label_off_le : forall s k, harness_label_off s = Some k -> (k <= length s)%nat.
Proof.
intros s k. unfold harness_label_off. destruct (colon_idx s <? length s)%nat eqn:E; cbn [andb]; [|discriminate].
destruct (negb _); [|discriminate]. intros H. injection H as <-. apply Nat.ltb_lt in E. lia.
Qed.
Lemma pin_dp_range : forall i, 0 <= PIN_DP i < 2 ^ 64.
Proof.
intros i. unfold PIN_DP, PIN_DISPP. do 11 (destruct i as [|i]; [cbn [nth]; lia|]). destruct i; cbn [nth]; lia.
Qed.

Lemma pm_parse_live_eq : forall q mo lb fl, 0 <= fl < 256 -> q <> 0 -> mo <> 0 -> lb <> 0 ->
pin_parse_live (pm_arg fl 0 q) (pm_arg fl 1 mo) (pm_arg fl 2 lb) = fl_live fl.
Proof.
intros q mo lb fl Hfl Hq Hm Hl. unfold pm_arg, pin_parse_live, fl_live.
apply Z.eqb_neq in Hq, Hm, Hl.
destruct (Z.testbit fl 0), (Z.testbit fl 1), (Z.testbit fl 2); rewrite ?Hq, ?Hm, ?Hl; reflexivity.
Qed.

Lemma pm_parse_res_harness : forall q mo lb fl (s : list byte),
0 <= fl < 256 -> ~ In NUL s -> q <> 0 -> mo <> 0 -> lb <> 0 ->
pin_parse_res PM_CAT PM_DP (pm_arg fl 0 q) (pm_arg fl 1 mo) (pm_arg fl 2 lb) s =
match harness_want fl s with
| Some i => Some (row_addr PM_CAT i, match harness_label_off s with Some k => q + Z.of_nat k | None => PM_DP i end)
| None => None
end.
Proof.
intros q mo lb fl s Hfl Hs Hq Hm Hl. unfold pin_parse_res. rewrite (pm_parse_live_eq q mo lb fl Hfl Hq Hm Hl).
rewrite (harness_label_off_eq s Hs). unfold harness_want. rewrite (land7_live fl Hfl).
destruct (fl_live fl) eqn:EL; cbn [andb]; [|reflexivity].
rewrite (pm_arg_live0 fl q EL).
destruct s as [|x s'].
- rewrite pin_row_nil. reflexivity.
- cbn [length Nat.eqb negb]. unfold pin_row, pin_token, pin_label_at. destruct (row_of _); reflexivity.
Qed.

Lemma pm_parse_known : forall q mo lb fl (s : list byte),
0 <= fl < 256 -> ~ In NUL s -> q <> 0 -> mo <> 0 -> lb <> 0 ->
(parse_rc (pin_parse_res PM_CAT PM_DP (pm_arg fl 0 q) (pm_arg fl 1 mo) (pm_arg fl 2 lb) s) = 0 <-> pm_want fl s <> 0).
Proof.
intros q mo lb fl s Hfl Hs Hq Hm Hl. rewrite (pm_parse_res_harness q mo lb fl s Hfl Hs Hq Hm Hl). unfold pm_want.
destruct (harness_want fl s) as [i|]; cbn [parse_rc]; split; intros H; try lia.
pose proof (row_addr_pos PM_CAT i ltac:(unfold PIN_CAT; lia)). lia.
Qed.

Lemma pm_parse_row_label : forall q mo lb fl (s : list byte) row lab,
0 <= fl < 256 -> ~ In NUL s -> q <> 0 -> mo <> 0 -> lb <> 0 ->
pin_parse_res PM_CAT PM_DP (pm_arg fl 0 q) (pm_arg fl 1 mo) (pm_arg fl 2 lb) s = Some (row, lab) ->
row = pm_want fl s /\ lab = pm_wlab q fl s.
Proof.
intros q mo lb fl s row lab Hfl Hs Hq Hm Hl H. rewrite (pm_parse_res_harness q mo lb fl s Hfl Hs Hq Hm Hl) in H.
unfold pm_want, pm_wlab. destruct (harness_want fl s) as [i|]; [|discriminate].
injection H as <- <-. split; reflexivity.
Qed.

Lemma pm_want_range : forall fl (s : list byte), 0 <= pm_want fl s < 2 ^ 64.
Proof.
intros fl s. unfold pm_want. destruct (harness_want fl s) as [i|] eqn:E; [|lia].
pose proof (harness_want_lt fl s i E) as Hi. unfold row_addr, PIN_CAT, CAT_ROW. unfold CAT_N in Hi. lia.
Qed.

Lemma pm_wlab_range : forall q fl (s : list byte), 0 <= q -> q + Z.of_nat (length s) < 2 ^ 64 ->
0 <= pm_wlab q fl s < 2 ^ 64.
Proof.
intros q fl s Hq Hqs. unfold pm_wlab. destruct (harness_want fl s) as [i|] eqn:E; [|lia].
destruct (harness_label_off s) as [k|] eqn:EK.
- pose proof (harness_label_off_le s k EK). lia.
- exact (pin_dp_range i).
Qed.

(* the spec string the harness hands reac_box_pin_parse is the whole heap block (q, |s| + 1): CP1.2 from the
   allocator relation's block, shadow and tail laws *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Lemma pm_spec_str_blk : forall ly S (W : world segs) mem md (regs : bvmap 5 word) q (s : list byte),
AR segs B ly S W mem md -> In (q, Z.of_nat (length s) + 1) (ablocks B ly S) -> ~ In NUL s ->
garr8 segs (mrestrict (w_H W) mem) q (pin_zbytes s ++ [0]) ->
(forall x, q <= x <= q + Z.of_nat (length s) -> ~ (spZ regs - T_parse_STK <= x < spZ regs)) ->
pin_spec_str segs (mrestrict (w_H W) mem) (aview segs (w_H W) mem) regs T_parse_STK q s /\
exists b m, In (b, m) (ablocks B ly S) /\ b <= q /\ q + Z.of_nat (length s) + 1 <= b + req_size m.
Proof using LAWS.
intros ly S W mem md regs q s HAR Hin Hs Hg Hoff.
destruct (al_blocks _ _ LAWS ly S W mem md q (Z.of_nat (length s) + 1) HAR Hin)
as (Hq16 & Hq4096 & Hceil & Happ & Hpres & Hdisj & Hmax).
assert (Hreq : req_size (Z.of_nat (length s) + 1) = Z.of_nat (length s) + 1)
by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length s) + 1) 0); lia).
pose proof asan_consts as (C1 & _).
rewrite Hreq in Hceil. unfold MALLOC_MAX in Hmax.
split.
- unfold pin_spec_str.
  split; [exact Hs|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hg|].
  split; [apply (range_addressable_of_block segs B LAWS ly S W mem md q (Z.of_nat (length s) + 1)); [exact HAR | exact Hin | lia | rewrite Hreq; lia]|].
  split; [apply (shadow_hull_vis_of_block segs B LAWS ly S W mem md q (Z.of_nat (length s) + 1)); [exact HAR | exact Hin | lia | rewrite Hreq; lia | lia]|].
  split.
  { unfold pin_str_tail. intros a Ha.
    apply (blk_tail_present segs B LAWS ly S W mem md q (Z.of_nat (length s) + 1) (Z.of_nat (length s)) a HAR Hin);
    [rewrite Hreq; lia | exact Ha]. }
  split; [apply (amem_range_of_block segs B LAWS ly S W mem md q (Z.of_nat (length s) + 1)); [exact HAR | exact Hin | lia | rewrite Hreq; lia]|].
  exact Hoff.
- exists q, (Z.of_nat (length s) + 1). split; [exact Hin|]. split; [lia|]. rewrite Hreq. lia.
Qed.
End b.

(* ------------------------------ the tail of S4: ss_F at 0x8092c ------------------------------
   0x8092c mv a0,s3 ; 0x80930 jal 52b50 <free wrapper> (ra 0x80934). ss_F is ss_X's frame part with s3 = q
   (slot 100) live; every other register outside the frame part is dead (slots 860 ..). *)
Definition pm_F_deads : list nat := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 22; 25; 26; 27; 28; 29; 30; 31]%nat.
Definition pm_F_deads_bv : list (bv 5) := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 22; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition pm_F_regs : list sv :=
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 9 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 75 0; SOff 100 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 88 0;
 SOff 75 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition ss_F : sstate := Eval vm_compute in
ss_havoc_regs (mkSS 0x80960 pm_F_regs pm_mem None (mkFacts (pm_atoms ++ [(100%nat, HPTR 4)]) [] pm_alias)) 860 pm_F_deads.
Section inv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
(* ss_F: the malloc'd block (q, k + 1) is still held; one event so far *)
Definition INV_F (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k = 1 /\ acc <= mo_malloc MT (2 ^ 26) /\
exists q, ew E 100 = Z_to_bv 64 q /\
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(q, Z.of_nat (pin_k (c_pl cx)) + 1)]).
End inv.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis FP0 : FP = [].
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AFREE4 : afree04_rule tfibsegs B MT.
(* The call site 0x80930 (free(q) through its wrapper 0x52b50, ra 0x80934): the walk's facts there (rt_base, the
   journal with the frame, k = 1, a0 = q, sp = sp1, s0 = sp0, ra, gp / tp, the frame chain, INV_F's block list and
   meter bound) give every premise of lib/A/PPgMainCall.v afree04_sub at the block (q, k + 1) and o = sp1 - sp0. *)
Lemma pin_free_site : forall (cx : rtcx) k acc ly3 S3 W3 (memT : word -> option byte) mdc (regsT : bvmap 5 word) q,
rt_base B MT cx ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, c_fpos cx)] ly3 S3 W3 memT mdc k ->
k = 1 -> mo_le MT (c_S cx) S3 acc -> acc <= mo_malloc MT (2 ^ 26) ->
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(q, Z.of_nat (pin_k (c_pl cx)) + 1)]) ->
getr regsT 10 = w64 q -> spZ regsT = c_sp1 cx -> s0Z regsT = spZ (c_regs cx) -> getr regsT 1 = Z_to_bv 64 RT_free_ra ->
getr regsT 3 = getr (c_regs cx) 3 -> getr regsT 4 = getr (c_regs cx) 4 ->
achain ly3 (aview tfibsegs (w_H W3) memT) (c_sp1 cx) (spZ (c_regs cx)) (rt_ch cx) ->
In (q, Z.of_nat (pin_k (c_pl cx)) + 1) (ablocks B ly3 S3) /\
getr regsT 10 = w64 q /\
spZ regsT = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)) /\ (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0 /\
c_sp1 cx - spZ (c_regs cx) <= 0 /\ ASTACK - (c_sp1 cx - spZ (c_regs cx)) <= LLVMF_STK /\
getr regsT 3 = w64 (as_gp B) /\ getr regsT 4 = w64 (as_tp B) /\
getr regsT 1 = Z_to_bv 64 RT_free_ra /\ YK0s.ret_ok (Z_to_bv 64 RT_free_ra) /\
st_nev S3 < EV_MAX /\
chain_pre ly3 (aview tfibsegs (w_H W3) memT) regsT (rt_ch cx) /\
In (call_trace0 (pc_free_ra0 (as_code B)) regsT (rt_ch cx)) (as_universe B) /\
(In (q, Z.of_nat (pin_k (c_pl cx)) + 1) (ablocks B (c_ly cx) (c_S cx)) ->
 forall i, 0 <= i < req_size (Z.of_nat (pin_k (c_pl cx)) + 1) -> inFP FP (q + i)) /\
mo_ok MT S3 (mo_free MT).
Proof.
intros cx k acc ly3 S3 W3 memT mdc regsT q HB HJ Hk HMLE Hacc HP Ha0 Hsp Hs0 Hra Hgp3 Htp3 Hch.
pose proof HB as (HPRE & Hra0 & _ & _ & _ & _ & _ & _ & Hev & _ & _ & Esp1 & _ & _ & _ & HMOK & HT0).
destruct cx as [ly S W regs mem md p n pl fpos sp1 E0 T].
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_fpos c_sp1 c_E0 c_T] in *.
pose proof HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct (sp1_facts (spZ regs + -128) ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Esp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hin3 : In (q, Z.of_nat (pin_k pl) + 1) (ablocks B ly3 S3))
by (eapply Permutation_in; [apply Permutation_sym; exact HP | apply in_or_app; right; left; reflexivity]).
pose proof (proj1 HJ) as HAR3.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (Hraz : raZ regsT = RT_free_ra) by (unfold raZ; rewrite Hra; apply unsigned_lit_small; unfold RT_free_ra; lia).
split; [exact Hin3|]. split; [exact Ha0|]. split; [lia|].
split; [rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity|].
split; [lia|]. split; [rewrite FFS; unfold ASTACK; lia|].
split; [rewrite Hgp3; exact Hgp|]. split; [rewrite Htp3; exact Htp|].
split; [exact Hra|]. split; [apply ret_ok_even; vm_compute; reflexivity|].
split; [unfold RT_EV in Hev; lia|].
split; [apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ _ Hch); [rewrite Hsp; lia | exact Hs0 | rewrite Hraz; unfold RT_free_ra; lia]|].
split.
{ replace (pc_free_ra0 (as_code B)) with 0x52c90 by (rewrite (tl_code B TL); reflexivity). rewrite (tl_universe B TL).
apply (rt_trace_in 0x52c90 RT_free_ra regsT (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)); [exact Hra0 | exact Hraz | right; split; reflexivity]. }
split.
{ intros Hin0. exfalso.
destruct (sep_tmp_entry B LAWS ly3 S3 W3 memT mdc (ablocks B ly S) q (Z.of_nat (pin_k pl) + 1) q (Z.of_nat (pin_k pl) + 1) HAR3 HP Hin0) as [X | X];
pose proof (le_req_size (Z.of_nat (pin_k pl) + 1) ltac:(lia)); lia. }
apply (mok_station MT S S3 T acc (mo_free MT) MTL HMOK HMLE); [apply (mo_free_nonneg MT MTL)|].
unfold PIN_NEED in HT0. lia.
Qed.
(* 0x8092c .. 0x80930: free(q) through AFREE4 (lib/A/PPgMainCall.v afree04_sub; the call trace by rt_trace_in;
   the meter spends mo_free MT), then the join into ss_X with INV_X (two events, the block given back) *)
Lemma pm_S4F : rt_from B MT FP POST ss_X (INV_X B MT) -> rt_from B MT FP POST ss_F (INV_F B MT).
Proof using MTL FP0 TL LAWS AFREE4.
intros RX. rt_prelude.
pose proof HINV as (Hk1 & Hacc & q & E100 & HPerm3). cbn [c_ly c_S c_pl] in HPerm3.
relowRT HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan.
{ awrRT AG fpos F EFA3. }
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 HF8hi; lia). clear_frames.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rreg HS (8%bv : bv 5) Rs0. rreg HS (10%bv : bv 5) Ra0.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat 3%bv eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat 4%bv eq_refl)).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x80968) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3);
assert (Ra0v : getr rg 10 = w64 q) by (rewrite Ra0; rewrite ?sv_denot_SOff0; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E100);
assert (Rgp' : getr rg 3 = getr regs 3) by (rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Ugp);
assert (Rtp' : getr rg 4 = getr regs 4) by (rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Utp) end.
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview tfibsegs (w_H W3) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| ] end.
pose proof (pin_free_site (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) k acc ly3 S3 W3 _ _ _ q HBASE0 HJ3 Hk1 HMLE Hacc HPerm3
Ra0v EspX Es0X Rra Rgp' Rtp' Hch1) as (Hin3 & Ha0' & Hspo & Ho16 & Ho0 & Hostk & Hgp3 & Htp3 & Hra3 & Hraw & Hnev & Hchp & HU & Hcov & MOK).
cbn [c_regs c_sp1 c_pl c_ly c_S] in Hin3, Hspo, Ho16, Ho0, Hostk, Hcov.
pose proof (proj1 HJ3) as HARx.
destruct (al_blocks _ _ LAWS _ _ _ _ _ q (Z.of_nat (pin_k pl) + 1) HARx Hin3) as (_ & _ & _ & Hph_ia & _ & _).
pose proof (sep_block_frame tfibsegs _ LAWS ly3 S3 _ _ _ q (Z.of_nat (pin_k pl) + 1) 1 fpos HARx Hin3 Hfin3) as HdFP.
unfold zdisjoint in HdFP; cbn [fst snd] in HdFP; change (fs_frame_bytes 1) with 128 in HdFP; rewrite EFA3 in HdFP. fold F in HdFP.
assert (HErLo : forall a, SB <= a < 17594333495296 -> ~ (q <= a < q + req_size (Z.of_nat (pin_k pl) + 1)))
by (intros a Ha Hx; clear - Ha Hx Hph_ia C3; unfold SB in *; zone_lia).
assert (HErF : forall a, F <= a < F + 128 -> ~ (q <= a < q + req_size (Z.of_nat (pin_k pl) + 1)))
by (intros a Ha Hx; clear - Ha Hx HdFP; lia).
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 338768 with (pc_wrap_free (as_code B)) by (rewrite (tl_code B TL); reflexivity).
eapply SRr_bind.
{ eapply (afree04_sub tfibsegs B LAWS tfib_segs_low MT AFREE4 W3 _ _ LLVMF_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly3 S3 _ k q
(Z.of_nat (pin_k pl) + 1) (sp1 - spZ regs) (Z_to_bv 64 RT_free_ra) (rt_ch (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T))
HJ3 Hin3 Ha0' Hspo Ho16 Ho0 Hostk Hgp3 Htp3 Hra3 Hraw Hnev Hchp HU Hcov MOK). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Ebl3 & Ebl4) & Hfrs4 & HK & HMLEc & _).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1 Hchp HU.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia).
pose proof (proj1 HJ4) as HAR4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfrs4' : frames S4 = [(1, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4'; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4. change (128 / 8) with 16 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
unfold RT_free_ra.
reseatL HS HJ4 HP4 [0; 1; 2]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 1 / 8) with 16; unfold SB; clear; lia
| intros a Ha Hx; exact (HErLo a ltac:(clear - Ha HF8c HF8lo HFceil C1; unfold SB in *; lia) Hx)
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; clear; lia
| intros a Ha Hx; exact (HErF a ltac:(clear - Ha; lia) Hx)
| intros a Ha; first [exfalso; clear - Ha; lia | apply (proj1 (HFpres4 a ltac:(clear - Ha; lia)))] ] end
| keptRT HK HJ4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 ltac:(idtac; fail) ltac:(idtac; fail)
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
ra_join_win HS ss_X 900%nat pm_X_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv.
assert (HMLE4 : mo_le MT S S4 (acc + mo_free MT)) by exact (mle_station MT S S3 S4 acc (mo_free MT) MTL HMLE HMLEc).
rt_hand RX HS.
split; [rewrite Hk1; unfold RT_EV; clear; lia|].
split; [cbn [c_T]; unfold PIN_NEED in HT0; clear - Hacc HT0; lia|].
cbn [c_ly c_S]. rewrite Ebl4.
pose proof (@Permutation_app_inv _ l1 l2 (ablocks B ly S) [] (q, Z.of_nat (pin_k pl) + 1)) as HPI. rewrite app_nil_r in HPI.
apply HPI. rewrite <- Ebl3. exact HPerm3.
Qed.
End f.
