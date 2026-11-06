(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value's NUMBER SEGMENT: the generic, journal-free engine helpers of lib/B/Prog/ex_ws_x.v (its Section h lemmas
   exw_st_ok_full / exw_region_nth / exw_field / exw_kept / exw_garr8_kept / exw_val_kept / exw_ra_kept, exw_denot_shx,
   exw_nth_skipn, exw_awr_cons, exw_agree2, exw_skipn_S and the Ltacs exw_awr / exw_ew / exw_after_run / exw_run /
   exw_run_to / exw_branch / exw_kept_of), RESTATED under the SAME names so the number segment's sub-pieces do not
   Require ex_ws_x: on the old-pin kit (rebind base) ex_ws_x waits for ExWsOldpin's rebind, and these helpers name no
   callee text. Copied verbatim from ex_ws_x.v (cold/h-rw-pre-7-b-ex_ws 923049cc881) lines 106-179 and 191-285; only
   exw_mask_U (ex_ws's own whitespace mask) is left out, and EXW_TBL is the whole-range table B_prog_tbl.
   Numerals: those of the copied lines (ex_ws_x.v's header classifies them: 8, 3, 2 ^ 63, 2 ^ 60, 2 ^ 64, 2 ^ 32, 63, 64
   LENGTH / DERIVED widths and bounds). No ADDRESS. Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition EXW_TBL : ctable := B_prog_tbl.

(* ---- journal-free helpers (skip_ws_x.v's, unchanged) ---- *)
Section h. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Lemma exw_st_ok_full : forall E pc sr regs (rs : smem) (G : facts) mem,
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok segs E mem) rs -> pairwise_disjoint E rs -> facts_ok E G ->
st_ok segs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)).
Proof.
intros E pc sr regs rs G mem Hsr Hwf Hrs Hpd HG.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG]. split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
Lemma exw_region_nth : forall E ss ms i r,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok segs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok segs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma exw_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem segs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok segs E m b od w e v Hck He Hv Hw).
Qed.
Lemma exw_kept : forall E rs H (m m' : word -> option byte) (Zs : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs H m' a = aview segs H m a.
Proof.
intros E rs H m m' Zs HFR Hw a Ha Hn. apply (aview_eq_of segs). apply HFR. rewrite unsigned_lit_small by lia.
intros Hin. destruct (in_wrange_windows E rs a Hin) as (b & wlo & whi & Hi & Hr). exact (Hn (Hw b wlo whi a Hi Hr)).
Qed.
Lemma exw_garr8_kept : forall H (m m' : word -> option byte) p L,
(forall a, p <= a < p + Z.of_nat (length L) -> aview segs H m' a = aview segs H m a) ->
garr8 segs (mrestrict H m) p L -> garr8 segs (mrestrict H m') p L.
Proof.
intros H m m' p L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. cbn in Hk. rewrite (mbyte_of_aview segs H H m m' (p + Z.of_nat j + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.
Lemma exw_val_kept : forall H (m m' : word -> option byte) a n v,
(forall x, a <= x < a + Z.of_nat n -> aview segs H m' x = aview segs H m x) ->
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v.
Proof.
intros H m m' a n v HE Hv kk Hk. rewrite (mbyte_of_aview segs H H m m' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.
Lemma exw_ra_kept : forall H (m m' : word -> option byte) a n,
(forall x, a <= x < a + n -> aview segs H m' (shadow_of_addr SHADOW_OFF x) = aview segs H m (shadow_of_addr SHADOW_OFF x)) ->
range_addressable (aview segs H m) SHADOW_OFF a n -> range_addressable (aview segs H m') SHADOW_OFF a n.
Proof. intros H m m' a n HE HR x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite (HE x Hx). auto. Qed.
End h.
Lemma exw_denot_shx : forall E n m v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb -> 0 <= v < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (sb + v / 8).
Proof.
intros E n m v sb Hn Hm Hv Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)))). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) = sb + v / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound v 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id v) by (unfold M64; lia). rewrite (zcanon_id (v / 8)) by (unfold M64; lia). rewrite (zcanon_id sb) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma exw_nth_skipn : forall (l : list Z) k b rest, skipn k l = b :: rest -> nth k l 0 = b.
Proof.
induction l as [|x l IH]; intros [|k] b rest H; cbn in H; try discriminate.
- injection H as -> ->. reflexivity.
- cbn. exact (IH k b rest H).
Qed.
Lemma exw_awr_cons : forall E r rs STK sp0 FP bl0 blc ly own,
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof. intros E r rs STK sp0 FP bl0 blc ly own Hw H a (r' & [<-|Hin] & Ha); [exact (Hw a Ha) | apply H; exists r'; auto]. Qed.
Lemma exw_agree2 : forall E a b, env_agree 32 E (ewset (ewset E 33 a) 34 b).
Proof. intros E a b. split; [intros nn Hnn; rewrite !ew_ewset_other by lia; reflexivity | reflexivity]. Qed.
Lemma exw_skipn_S : forall (l : list Z) k b rest, skipn k l = b :: rest -> skipn (S k) l = rest.
Proof. induction l as [|x l IH]; intros [|k] b rest H; cbn in H |- *; try discriminate; [injection H as -> ->; reflexivity | exact (IH k b rest H)]. Qed.
Ltac exw_awr Hqw Usp Uq :=
lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ =>
let rs' := eval vm_compute in rs in change rs with rs' end;
repeat (apply exw_awr_cons; [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
cbn [ew ewset Nat.eqb] in Ha; rewrite ?Usp, ?Uq in Ha;
first [ lia | left; lia | exact (proj1 (Hqw a ltac:(lia))) ] | ]);
apply awr_ok_nil.
Ltac exw_ew E1 :=
cbn [ew ewset Nat.eqb]; first [exact E1 | rewrite !ew_ewset_other by lia; exact E1].
Ltac exw_after_run HS HJ SHOK :=
let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ws ms' mat' Hlen HS SHOK HJ HF HFr HG;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (let w := fresh "w" in
destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK;
cbn [ms_mem mkst] in HF, HFr, HG, HJ;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
Ltac exw_run RUN HS HJ SHOK :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_runN_tok sg EXW_TBL K Bx BAND_SPAN SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_tok sg EXW_TBL K Bx BAND_SPAN SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUN W FUEL E K Bx BAND_SPAN SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
exw_after_run HS HJ SHOK ]
end end
end.
Ltac exw_run_to RUNTO HS HJ SHOK stop :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_tok sg EXW_TBL K Bx BAND_SPAN SH FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_tok sg EXW_TBL K Bx BAND_SPAN SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUNTO W FUEL stop E K Bx BAND_SPAN SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
exw_after_run HS HJ SHOK ]
end end
end.
Ltac exw_branch HS SHOK :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (snd (sym_runN_tok sg EXW_TBL K Bx BAND_SPAN SH 1 ss)) in
lazymatch r with
| TS_stopped (SR_branch ?c ?a ?b) =>
apply (SRr_sym_branch sg W E ss ms _ _ c a b HS); clear HS;
let Hc := fresh "Hc" in intros Hc HS
| _ => fail "exw_branch: not stuck at a branch:" r
end end
end.
Ltac exw_kept_of HFr Zs ev :=
lazymatch type of HFr with frame_of ?E ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
let KP := fresh "KEPT" in
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview rsegs H m' a = aview rsegs H m a);
[ apply (exw_kept rsegs E rs H m m' Zs HFr); intros b_ wlo_ whi_ a0_ Hin_ Hrr_; vm_compute in Hin_;
repeat (destruct Hin_ as [Hq_ | Hin_]; [injection Hq_ as <- <- <-; cbn [base_val] in Hrr_; ev Hrr_; cbv beta; lia|]);
destruct Hin_
| cbv beta in KP ]
end.
