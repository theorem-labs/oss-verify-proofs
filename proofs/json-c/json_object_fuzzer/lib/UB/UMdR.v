(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq Lib.SepCache QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QgoP Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM UPZI UC8c UG8z Udyh ULbz UIsM UXfU U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UPZI.Mq0 UC8c.Mq0.
Import Qsw7 QJjn QRUw.Mq2 QkMG.
Import UG8z Udyh.Mq0 ULbz UIsM.Mq2 UXfU.Mq4 U2Sr.Mq0 UXfU.Mq0.
Import QgoP.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition litbytes := Eval vm_compute in match image_bytes rsegs 0x13922 20 with Some bs => bs | None => [] end.
Definition infbytes := Eval vm_compute in match image_bytes rsegs 0x13910 9 with Some bs => bs | None => [] end.
Definition invbytes := Eval vm_compute in match image_bytes rsegs 0x13919 9 with Some bs => bs | None => [] end.
Definition nullstr : list byte := Eval vm_compute in firstn 4 litbytes.
Definition nanstr : list byte := Eval vm_compute in firstn 3 (skipn 5 litbytes).
Definition truestr : list byte := Eval vm_compute in firstn 4 (skipn 9 litbytes).
Definition falsestr : list byte := Eval vm_compute in firstn 5 (skipn 14 litbytes).
Definition infstr : list byte := Eval vm_compute in firstn 8 infbytes.
Definition invstr : list byte := Eval vm_compute in firstn 8 invbytes.
Definition NANW : Z := 0x7FF8000000000000.
Definition PINFW : Z := 0x7FF0000000000000.
Definition NINFW : Z := 0xFFF0000000000000.

#[using="Type"] Lemma ro_cells_bytes_at'' : forall segs m A cs, ro_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [_ H]. exact H. Qed.

#[using="Type"] Lemma lit_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x13922 [CB 20 litbytes].
Proof.
intros m MI. change 20%nat with (length litbytes).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length litbytes)) with 20%Z. lia.
Qed.
#[using="Type"] Lemma inf_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x13910 [CB 9 infbytes].
Proof.
intros m MI. change 9%nat with (length infbytes).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length infbytes)) with 9%Z. lia.
Qed.
#[using="Type"] Lemma inv_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x13919 [CB 9 invbytes].
Proof.
intros m MI. change 9%nat with (length invbytes).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length invbytes)) with 9%Z. lia.
Qed.
Definition nanbytes := Eval vm_compute in match image_bytes rsegs 0x13458 8 with Some bs => bs | None => [] end.
Definition inftab := Eval vm_compute in match image_bytes rsegs 0x134b0 16 with Some bs => bs | None => [] end.
Definition pinfbytes := Eval vm_compute in match image_bytes rsegs 0x133d0 8 with Some bs => bs | None => [] end.
#[using="Type"] Lemma nan_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x13458 [CB 8 nanbytes].
Proof.
intros m MI. change 8%nat with (length nanbytes).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length nanbytes)) with 8%Z. lia.
Qed.

#[using="Type"] Lemma pinf_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x133d0 [CB 8 pinfbytes].
Proof.
intros m MI. change 8%nat with (length pinfbytes).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length pinfbytes)) with 8%Z. lia.
Qed.

#[using="RC__"] Lemma lit_sub : forall m k (s : list byte), mem_inv rsegs m -> (k + length s + 1 <= 20)%nat ->
firstn (length s + 1) (skipn k litbytes) = s ++ [b0] -> bytes_at rsegs m (0x13922 + Z.of_nat k) (s ++ [b0]).
Proof.
intros m k s MI Hk E. rewrite <- E.
pose proof (ro_cells_bytes_at'' _ _ _ _ (lit_ro m MI)) as B. cbn [cells_bytes cbytes app pf_mxd] in B. rewrite app_nil_r in B.
apply (bytes_at_sub S4L m 0x13922 litbytes k (length s + 1) B). change (length litbytes) with 20%nat. lia.
Qed.
#[using="RC__"] Lemma null_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x13922 (nullstr ++ [b0]).
Proof. intros m MI. apply (lit_sub m 0 nullstr MI); [cbn; lia | vm_compute; reflexivity]. Qed.
#[using="RC__"] Lemma nan_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x13927 (nanstr ++ [b0]).
Proof. intros m MI. apply (lit_sub m 5 nanstr MI); [cbn; lia | vm_compute; reflexivity]. Qed.
#[using="RC__"] Lemma true_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x1392b (truestr ++ [b0]).
Proof. intros m MI. apply (lit_sub m 9 truestr MI); [cbn; lia | vm_compute; reflexivity]. Qed.
#[using="RC__"] Lemma false_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x13930 (falsestr ++ [b0]).
Proof. intros m MI. apply (lit_sub m 14 falsestr MI); [cbn; lia | vm_compute; reflexivity]. Qed.

#[using="Type"] Lemma nonul_null : ~ In b0 nullstr.   Proof. vm_compute. intuition discriminate. Qed.
#[using="Type"] Lemma nonul_nan : ~ In b0 nanstr.     Proof. vm_compute. intuition discriminate. Qed.
#[using="Type"] Lemma nonul_true : ~ In b0 truestr.   Proof. vm_compute. intuition discriminate. Qed.
#[using="Type"] Lemma nonul_false : ~ In b0 falsestr. Proof. vm_compute. intuition discriminate. Qed.

#[using="Type"] Lemma sx32_small_mod : forall w : word, bv_unsigned w mod 2^32 < 2^31 -> sx32 w = Z_to_bv 64 (bv_unsigned w mod 2^32).
Proof.
intros w Hw. unfold sx32. f_equal.
pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)) as B.
transitivity (bv_swrap 32 (bv_unsigned w mod 2^32 + (bv_unsigned w / 2^32) * 4294967296)).
- f_equal. change 4294967296 with (2^32). pose proof (Z.div_mod (bv_unsigned w) (2^32) ltac:(lia)). lia.
- rewrite swrap32_shift. apply swrap32_id. lia.
Qed.

#[using="Type"] Lemma spv_lit : forall z, 0 <= z < 2^32 -> bv_unsigned (Z_to_bv 64 z) mod 2^32 = z.
Proof. intros z Hz. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.

#[using="Type"] Lemma fsaved_set10 : forall F v, fsaved F (bvmap_set (Z_to_bv 5 10) v F).
Proof.
intros F v k Hk. apply QEpW.reg_get_set_other. intros E.
assert (Hk10 : k = 10).
{ unfold FSAVED in Hk. cbn in Hk.
assert (R : 0 <= k < 32 -> bv_unsigned (Z_to_bv 5 k) = k) by (intros; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
apply (f_equal bv_unsigned) in E. rewrite R in E by (intuition lia). vm_compute in E. lia. }
unfold FSAVED in Hk. cbn in Hk. lia.
Qed.

#[using="Type"] Lemma reg_get_set_same_u : forall (F : bvmap 5 word) (k1 k2 : bv 5) (v : word),
bv_unsigned k1 = bv_unsigned k2 -> Sem.reg_get (bvmap_set k1 v F) k2 = v.
Proof. intros F k1 k2 v E. replace k2 with k1 by (apply bv_eq; exact E). apply QEpW.reg_get_set_same. Qed.

#[using="Type"] Lemma strncmp_walk_cstr : forall ls rs k, exists v, strncmp_walk (ls ++ [b0]) (rs ++ [b0]) k = Some v.
Proof.
induction ls as [|a ls IH]; intros rs k.
- cbn [app pf_mxd]. destruct (rs ++ [b0]) as [|b r] eqn:E; [destruct rs; discriminate E|]. cbn. eexists; reflexivity.
- cbn [app pf_mxd]. destruct rs as [|b rs].
+ cbn [app pf_mxd]. cbn. rewrite Bool.orb_true_r. cbn. eexists; reflexivity.
+ cbn [app pf_mxd]. cbn [strncmp_walk pf_mxd].
destruct ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || (k =? 0)%nat || negb (bv_unsigned a =? bv_unsigned b))%bool; [eexists; reflexivity|].
destruct k as [|k]; [eexists; reflexivity | apply IH].
Qed.
#[using="Type"] Lemma strncmp_model_cstr : forall ls rs n, exists v, strncmp_model (ls ++ [b0]) (rs ++ [b0]) n = Some v.
Proof. intros. unfold strncmp_model. destruct (n =? 0); [eexists; reflexivity | apply strncmp_walk_cstr]. Qed.

#[using="Type"] Lemma null_mode : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_null ss = Some (c, hn) -> c = CNone /\ hn = false.
Proof. intros ss c hn R Hm. enum_z R ss; vm_compute in Hm; first [discriminate Hm | injection Hm as <- <-; split; reflexivity]. Qed.
#[using="Type"] Lemma bool_mode : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_boolean ss = Some (c, hn) -> c = CNone /\ hn = false.
Proof. intros ss c hn R Hm. enum_z R ss; vm_compute in Hm; first [discriminate Hm | injection Hm as <- <-; split; reflexivity]. Qed.
#[using="Type"] Lemma inf_mode : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_inf ss = Some (c, hn) -> c = CNone /\ hn = false.
Proof. intros ss c hn R Hm. enum_z R ss; vm_compute in Hm; first [discriminate Hm | injection Hm as <- <-; split; reflexivity]. Qed.

#[using="Type"] Lemma pbuf_cstr : forall m pbs pb, pbuf rsegs m pbs pb ->
exists buf bpos cap str rest,
pbs = [(pb, 16); (buf, cap)] /\ 0 <= bpos < cap /\ cap < 2^31 /\
rw_cells rsegs m pb [C8 (Z_to_bv 64 buf); C4 (Z_to_bv 64 bpos); C4 (Z_to_bv 64 cap)] /\
bytes_at rsegs m buf (str ++ b0 :: rest) /\ ~ In b0 str /\ Z.of_nat (length str) <= bpos /\
Z.of_nat (length str) + 1 + Z.of_nat (length rest) = cap.
Proof.
intros m pbs pb (buf & bpos & cap & pre & post & E & L & (H1 & H2 & H3 & H4 & H5)). cbn [hl_segs S4L pf_mxd] in H4, H5.
destruct (first_nul_split pre post) as (str & rest & Es & Hn & Hl).
exists buf, bpos, cap, str, rest. split; [exact E|].
pose proof H3 as H3'. rewrite Es, length_app in H3'. cbn [length pf_mxd] in H3'.
rewrite length_app in H3. cbn [length app pf_mxd] in H3.
split; [lia|]. split; [lia|]. split; [exact H4|]. split; [| split; [exact Hn | lia]].
pose proof (rw_cells_bytes_at' _ _ _ _ H5) as X. cbn [cells_bytes cbytes pf_mxd] in X. rewrite app_nil_r in X. rewrite Es in X. exact X.
Qed.

Section PeLit.
Variable HIx : heap_iface S4L.

#[using="Type"] Lemma PE_INV_stackw : forall pf q LB0 payload me lo m m' md A ts cb j1 j2 utf sv errv W,
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
Forall (fun iv => lo <= fst iv /\ snd iv <= pf_spf pf) W ->
stk rsegs m' lo (pf_spf pf) ->
PE_INV HIx pf q LB0 payload me lo m' md A ts cb j1 j2 utf sv errv.
Proof.
intros until W. intros STC [CORE REST] MU WM MI HW ST'.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
destruct REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO.

assert (BLO : forall a k, In (a, k) (pe_blocks pf q LB0 ts) -> 0 < a /\ a + k <= lo).
{ intros a k Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP Hin) as (_ & _ & H0 & Hhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia. }
assert (DJ : forall a n, a + n <= lo -> disjoint_from W a n).
{ intros a n Han. clear - HW Han. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [fst snd pf_mxd] in H1. cbn. split; [lia | apply IH; exact HW]. }
assert (INtk : In (pf_tk pf, 72) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * pf_mxd pf)) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (BLO _ _ INtk) as [Htk0 Htkhi]. pose proof (BLO _ _ INq) as [Hq0 Hqhi].
assert (AGall : agree_on rsegs (pe_blocks pf q LB0 ts) m m').
{ eapply agree_of_munch; [exact MU | exact WM |]. intros a n Hin. apply DJ. exact (proj2 (BLO a n Hin)). }
assert (DJF : disjoint_from W (pf_spf pf) PE_FRAME).
{ clear - HW. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [fst snd pf_mxd] in H1. cbn. split; [lia | apply IH; exact HW]. }
split.
- split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [eapply rw_cells_transport; [exact TOK | exact MU | exact WM | apply DJ; unfold tok_cells, tok_cells_g; cbn -[Z.add Z.le]; lia]|].
split; [eapply pbuf_agree; [exact PB | exact AGall | intros b Hb; unfold pe_blocks, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact Hb]|].
split; [exact Hpb|].
split; [eapply tstack_transport; [exact TSK | exact MU | exact WM | intros j Hj; rewrite LEN32 in Hj; apply DJ; lia]|].
eapply rw_cells_transport; [exact FR | exact MU | exact WM |]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add pf_mxd]. unfold PE_FRAME in DJF. exact DJF.
- split.
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU).
eapply Forall_impl; [| exact HW]. intros [lo' hi'] [H1 H2]. cbn [fst snd pf_mxd] in *. left.
unfold alloc_ceiling, sp_window_lo, stack_max_size. unfold PE_FRAME in HT. lia. }
split.
{ intros i l Hl. eapply (lvl_cur_agree rsegs S4F); [exact (LV i l Hl) | exact AGall |].
intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks l). split; [apply in_map; eapply nth_error_In; exact Hl | exact Hb]. }
split.
{ destruct (zin (cur_st ts) [ST_array_add; ST_ovadd]); [| exact OBJ].
eapply jopt_agree; [exact OBJ | exact AGall |]. intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb. }
split; [exact ST'|].
split; [eapply rw_cells_transport; [exact ERR | exact MU | exact WM | apply DJ; cbn; lia]|].
split.
{ eapply (payload_transport HIx); [exact STC | exact HP | intros x Hx; unfold pe_blocks; apply in_or_app; right; right; right; exact Hx | exact STR | exact PLEN | exact SBin | exact MU |].
eapply Forall_impl; [| exact HW]. intros [lo' hi'] [H1 H2]. unfold payload_safe. cbn [fst snd pf_mxd] in *. left. unfold PE_FRAME, alloc_ceiling, sp_window_lo, stack_max_size in *. lia. }
split; [exact PLEN|]. split; [exact SBin|].
split.
{ eapply heap_presx_trans; [exact HPR|]. eapply (heap_presx_of_munch S4L); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; unfold pe_blocks; apply in_or_app; right; right; right; exact Hb | unfold PE_FRAME; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia |].
eapply Forall_impl; [| exact HW]. intros [lo' hi'] [H1 H2]. cbn [fst snd pf_mxd] in *. left. unfold PE_FRAME, alloc_ceiling, sp_window_lo, stack_max_size. lia. }
split; [exact MDV|].
eapply jc_glob_P_outside; [exact JCG | exact MU | exact WM |].
eapply Forall_impl; [| exact HW]. intros [lo' hi'] [H1 H2]. cbn [fst snd pf_mxd] in *. right. lia.
Qed.

Definition jres (cs : option jshape) (m : word -> option byte) (NB : list blk) (r : Z) : Prop :=
match cs with
| None => r = 0 /\ NB = []
| Some s => r <> 0 /\ jval rsegs S4F s m NB r 1
end.

#[using="Type"] Lemma setcur_inv : forall pf q LB0 payload me lo m mp mc md md2 A A2 ts l cb j1 j2 utf sv errv errv2 NB r cs bse,
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
tl_cur l = 0 -> tl_cbs l = [] -> tl_name l = 0 -> tl_nbs l = [] -> t_objbs ts = [] ->
heap_pres S4L (pe_blocks pf q LB0 ts) (pf_spf pf) m mp -> model_vm_only md md2 ->
HEAP S4L HIx A2 (NB ++ pe_blocks pf q LB0 ts) mp md2 ->
stk rsegs mp lo (pf_spf pf) -> rw_cells rsegs mp (0x77c00 - 164) [C4 errv2] ->
jres cs mp NB r ->
bse = q + 32 * Z.of_nat (t_depth ts) ->
munch [(bse, bse + 32)] mp mc -> wmono rsegs mp mc -> mem_inv rsegs mc ->
rw_cells rsegs mc bse (srec_cells (TL ST_eatws ST_finish r cs NB 0 [])) ->
rw_cells rsegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
pe_frame rsegs mc (pf_spf pf) (t_obj ts) cb j1 j2 utf sv ->
PE_INV HIx pf q LB0 payload me lo mc md2 A2
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_eatws ST_finish r cs NB 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv2.
Proof.
intros until bse. intros STC INV Hl Hc0 Hcbs0 Hn0 Hnbs0 Eobjbs HPR2 VM2 HP2 ST2 ERR2 JR Hbse MU WM MI L5 TOK' FR'.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply (PE_REST_base HIx) in REST as (BASE & LV & OBJ).
pose proof (proj1 BASE) as HP.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
subst objbs.
set (ts0 := TST depth levels co pb pbs x obj objs []) in *.
assert (INtk : In (pf_tk pf, 72) (pe_blocks pf q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * pf_mxd pf)) (pe_blocks pf q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ _ _ HP INq) as (_ & Hqal & Hqlo & Hqhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (NQ0 : forall k, ~ In (q, k) LB0).
{ intros k. generalize ND; intros ND'. unfold pe_blocks in ND'. rewrite map_app in ND'. apply NoDup_app_remove_l in ND'. cbn [map blk_addr fst pf_mxd] in ND'.
apply List.NoDup_cons_iff in ND' as [_ ND']. apply List.NoDup_cons_iff in ND' as [Hnq _]. intros Hin. apply Hnq.
change q with (blk_addr (q, k)). apply in_map. exact Hin. }
assert (INCL0 : incl LB0 (pe_blocks pf q LB0 ts0)) by (unfold pe_blocks; intros b Hb; apply in_or_app; right; right; right; exact Hb).
pose proof (LV depth l Hl) as LVd.
assert (LB0l : lvl_blocks l = []) by (unfold lvl_blocks; rewrite Hcbs0, Hnbs0; reflexivity).
set (BL := concat (map lvl_blocks levels)).
assert (ALLf : forall a k, In (a, k) (pbs ++ BL) -> In (a, k) (pe_blocks pf q LB0 ts0) /\ a <> q).
{ intros a k Hin.
assert (HinT : In (a, k) (tstate_blocks ts0)) by (unfold tstate_blocks, ts0; cbn [t_pbs t_objbs t_levels app pf_mxd]; apply in_app_or in Hin; destruct Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin | right; exact Hin]).
assert (HinL : In (a, k) (pe_blocks pf q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; left; exact HinT).
split; [exact HinL|]. generalize ND; intros ND'. unfold pe_blocks in ND'.
eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). right; left; reflexivity. }

apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq) in TSK; [| exact LEN32]. cbn [hl_segs S4L pf_mxd] in TSK.
assert (PB2 : pbuf rsegs mp pbs pb).
{ eapply pbuf_agree; [exact PB | | apply incl_refl]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity |].
intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (AGL2 : agree_on rsegs BL m mp).
{ eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity |].
intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; right. cbn [app pf_mxd]. exact Hb. }
assert (LV2 : forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mp depth i li).
{ intros i li Hli Hne. eapply (lvl_cur_agree rsegs S4F); [exact (LV i li Hli) | exact AGL2 |].
intros b Hb. unfold BL. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In. exact Hli. }
assert (BASE2 : PE_BASE HIx pf LB0 payload me lo mp md2 A2 (NB ++ pe_blocks pf q LB0 ts0) errv2)
by (eapply (PE_BASE_call HIx); [exact BASE | exact HPR2 | exact INCL0 | exact VM2 | exact HP2 | exact ST2 | exact ERR2]).
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP2) as ND2.
assert (NEq : forall a k, In (a, k) (NB ++ pbs ++ BL) -> In (a, k) (NB ++ pe_blocks pf q LB0 ts0) /\ a <> q).
{ intros a k Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
- split; [apply in_or_app; left; exact Hin|]. intros ->. rewrite map_app in ND2.
eapply (NoDup_app_in2 _ _ q ND2); [exact (in_map blk_addr _ _ Hin) | exact (in_map blk_addr _ _ INq)].
- destruct (ALLf a k Hin) as (H1 & H3). split; [apply in_or_app; right; exact H1 | exact H3]. }
assert (AGY : forall BS, (forall a k, In (a, k) BS -> In (a, k) (NB ++ pe_blocks pf q LB0 ts0) /\ a <> q) -> agree_on rsegs BS mp mc).
{ intros BS HBS. eapply agree_of_munch; [exact MU | exact WM |]. intros a k Hin. destruct (HBS a k Hin) as (HinL & Hnq).
pose proof (heap_blk S4L HIx _ _ _ _ a k HP2 HinL) as (Hk0 & _).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k q (32 * pf_mxd pf) HP2 HinL ltac:(apply in_or_app; right; exact INq) Hnq). cbn. subst bse. lia. }
assert (BASE3 : PE_BASE HIx pf LB0 payload me lo mc md2 A2 (NB ++ pe_blocks pf q LB0 ts0) errv2).
{ eapply (PE_BASE_write HIx); [exact STC | exact BASE2 | intros b Hb; apply in_or_app; right; exact (INCL0 _ Hb) | exact MU | exact WM | exact MI |].
apply Forall_cons; [| apply Forall_nil]. unfold base_w; cbn [fst snd pf_mxd]. left. exists q, (32 * pf_mxd pf).
split; [apply in_or_app; right; exact INq|]. split; [exact NQ0 | subst bse; lia]. }
assert (PB3 : pbuf rsegs mc pbs pb)
by (eapply pbuf_agree; [exact PB2 | apply AGY | apply incl_refl]; intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; left; exact Hin).
assert (AGL3 : agree_on rsegs BL mp mc)
by (apply AGY; intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; right; exact Hin).
assert (AGN : agree_on rsegs NB mp mc)
by (apply AGY; intros a k Hin; eapply NEq; apply in_or_app; left; exact Hin).
assert (LV3 : forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mc depth i li)
by (intros i li Hli Hne; eapply (lvl_cur_agree rsegs S4F); [exact (LV2 i li Hli Hne) | exact AGL3 |];
intros b Hb; unfold BL; apply in_concat; exists (lvl_blocks li); split; [| exact Hb]; apply in_map; eapply nth_error_In; exact Hli).
set (l' := TL ST_eatws ST_finish r cs NB 0 []) in *.
assert (TSK3 : tstack rsegs mc q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs mp mc q levels depth l' []); [exact TSK | lia | exact MU | exact WM | intros; exact I | exact L5]).
split.
- unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_mxd].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK'|]. split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | exact FR'].
- apply (PE_REST_of_base HIx).
+ eapply (PE_BASE_perm HIx); [exact BASE3|].
unfold pe_blocks, tstate_blocks, ts0. cbn [t_pbs t_objbs t_levels app pf_mxd]. rewrite <- !app_assoc.
apply (Permutation_trans (l' := pbs ++ (NB ++ (concat (map lvl_blocks levels) ++ (pf_tk pf, 72) :: (q, (32 * pf_mxd pf)) :: LB0)))); [apply Permutation_app_swap_app|].
apply Permutation_app_head. rewrite (app_assoc NB). apply Permutation_app_tail.
replace (NB ++ concat (map lvl_blocks levels)) with (lvl_blocks l' ++ concat (map lvl_blocks levels)) by (unfold lvl_blocks, l'; cbn; rewrite app_nil_r; reflexivity).
apply (concat_lupd_fill levels depth l); [exact Hl | exact LB0l].
+ cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
split; [cbn; unfold ST_eatws; lia|]. split; [cbn; unfold ST_finish; lia|]. split.
{ cbn [tl_cs tl_cbs tl_cur l' pf_mxd]. destruct cs as [s|]; cbn [jres pf_mxd] in JR.
- destruct JR as [Hr J2]. cbn [jopt pf_mxd]. split; [exact Hr|]. eapply jval_agree; [exact J2 | exact AGN | apply incl_refl].
- destruct JR as [-> ->]. cbn [jopt pf_mxd]. split; reflexivity. }
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CAny, false. split; [reflexivity|]. split; [exact I|]. cbn. split; reflexivity.
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV3 i li Hli NE).
+ unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn. reflexivity.
Qed.

#[using="Type"] Lemma keep_inv : forall pf q LB0 payload me lo m mp mc md md2 A A2 ts l cb j1 j2 utf sv errv errv2 bse,
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
tl_cbs l = [] -> tl_nbs l = [] ->
heap_pres S4L (pe_blocks pf q LB0 ts) (pf_spf pf) m mp -> model_vm_only md md2 ->
HEAP S4L HIx A2 (pe_blocks pf q LB0 ts) mp md2 ->
stk rsegs mp lo (pf_spf pf) -> rw_cells rsegs mp (0x77c00 - 164) [C4 errv2] ->
bse = q + 32 * Z.of_nat (t_depth ts) ->
munch [(bse, bse + 32)] mp mc -> wmono rsegs mp mc -> mem_inv rsegs mc ->
rw_cells rsegs mc bse (srec_cells l) ->
rw_cells rsegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
pe_frame rsegs mc (pf_spf pf) (t_obj ts) cb j1 j2 utf sv ->
PE_INV HIx pf q LB0 payload me lo mc md2 A2 ts cb j1 j2 utf sv errv2.
Proof.
intros until bse. intros STC INV Hl Hcbs0 Hnbs0 HPR2 VM2 HP2 ST2 ERR2 Hbse MU WM MI L5 TOK' FR'.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply (PE_REST_base HIx) in REST as (BASE & LV & OBJ).
pose proof (proj1 BASE) as HP.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
set (ts0 := TST depth levels co pb pbs x obj objs objbs) in *.
assert (INtk : In (pf_tk pf, 72) (pe_blocks pf q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * pf_mxd pf)) (pe_blocks pf q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ _ _ HP INq) as (_ & Hqal & Hqlo & Hqhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (NQ0 : forall k, ~ In (q, k) LB0).
{ intros k. generalize ND; intros ND'. unfold pe_blocks in ND'. rewrite map_app in ND'. apply NoDup_app_remove_l in ND'. cbn [map blk_addr fst pf_mxd] in ND'.
apply List.NoDup_cons_iff in ND' as [_ ND']. apply List.NoDup_cons_iff in ND' as [Hnq _]. intros Hin. apply Hnq.
change q with (blk_addr (q, k)). apply in_map. exact Hin. }
assert (INCL0 : incl LB0 (pe_blocks pf q LB0 ts0)) by (unfold pe_blocks; intros b Hb; apply in_or_app; right; right; right; exact Hb).
pose proof (LV depth l Hl) as LVd.
assert (LB0l : lvl_blocks l = []) by (unfold lvl_blocks; rewrite Hcbs0, Hnbs0; reflexivity).
set (BL := objbs ++ concat (map lvl_blocks levels)).
assert (ALLf : forall a k, In (a, k) (pbs ++ BL) -> In (a, k) (pe_blocks pf q LB0 ts0) /\ a <> q).
{ intros a k Hin.
assert (HinT : In (a, k) (tstate_blocks ts0)) by (unfold tstate_blocks, ts0; cbn [t_pbs t_objbs t_levels pf_mxd]; exact Hin).
assert (HinL : In (a, k) (pe_blocks pf q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; left; exact HinT).
split; [exact HinL|]. generalize ND; intros ND'. unfold pe_blocks in ND'.
eapply (nodup_app_ne _ _ _ _ _ _ ND' HinT). right; left; reflexivity. }
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq) in TSK; [| exact LEN32]. cbn [hl_segs S4L pf_mxd] in TSK.
assert (AG2 : agree_on rsegs (pbs ++ BL) m mp).
{ eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity |]. intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. exact Hb. }
assert (BASE2 : PE_BASE HIx pf LB0 payload me lo mp md2 A2 (pe_blocks pf q LB0 ts0) errv2)
by (eapply (PE_BASE_call HIx); [exact BASE | exact HPR2 | exact INCL0 | exact VM2 | exact HP2 | exact ST2 | exact ERR2]).
assert (AG3 : agree_on rsegs (pbs ++ BL) mp mc).
{ eapply agree_of_munch; [exact MU | exact WM |]. intros a k Hin. destruct (ALLf a k Hin) as (HinL & Hnq).
pose proof (heap_blk S4L HIx _ _ _ _ a k HP2 HinL) as (Hk0 & _).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k q (32 * pf_mxd pf) HP2 HinL INq Hnq). cbn. subst bse. lia. }
pose proof (agree_on_trans _ _ _ _ _ AG2 AG3) as AG.
assert (BASE3 : PE_BASE HIx pf LB0 payload me lo mc md2 A2 (pe_blocks pf q LB0 ts0) errv2).
{ eapply (PE_BASE_write HIx); [exact STC | exact BASE2 | exact INCL0 | exact MU | exact WM | exact MI |].
apply Forall_cons; [| apply Forall_nil]. unfold base_w; cbn [fst snd pf_mxd]. left. exists q, (32 * pf_mxd pf).
split; [exact INq|]. split; [exact NQ0 | subst bse; lia]. }
assert (TSK3 : tstack rsegs mc q levels).
{ rewrite <- (lupd_same levels depth l Hl) at 1. subst bse.
eapply (tstack_put rsegs mp mc q levels depth l []); [exact TSK | lia | exact MU | exact WM | intros; exact I | exact L5]. }
split.
- unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_mxd].
split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK'|]. split; [| split; [exact Hpb | split; [exact TSK3 | exact FR']]].
eapply pbuf_agree; [exact PB | exact AG | intros b Hb; apply in_or_app; left; exact Hb].
- apply (PE_REST_of_base HIx); [exact BASE3 | |].
+ cbn [t_levels t_depth pf_mxd]. intros i li Hli. eapply (lvl_cur_agree rsegs S4F); [exact (LV i li Hli) | exact AG |].
intros b Hb. apply in_or_app; right. unfold BL. apply in_or_app; right. apply in_concat. exists (lvl_blocks li).
split; [apply in_map; eapply nth_error_In; exact Hli | exact Hb].
+ destruct (zin (cur_st ts0) [ST_array_add; ST_ovadd]); [| exact OBJ].
eapply jopt_agree; [exact OBJ | exact AG |]. intros b Hb. apply in_or_app; right. unfold BL. apply in_or_app; left. exact Hb.
Qed.
End PeLit.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfOM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtMn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG8z. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ub4w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ub4w.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULbz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ua8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ua8x.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ua8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ua8x.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ua8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ua8x.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ua8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ua8x. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U2Sr.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ua8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ua8x.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlCE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlCE.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ua8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ua8x.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U2Sr. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlCE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlCE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Tac.
Import TopUbTac Tk1Tac.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeMaster.
Variable HIx : heap_iface S4L.
Hypothesis PUT : put_stmt_P HIx.
Hypothesis USE : uselocale_stmt.
Hypothesis FREEL : freelocale_stmt HIx.
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis STRDUP : strdup_stmt HIx.
Hypothesis AADD : jo_array_add_P HIx.
Hypothesis SHRINK : jo_array_shrink_P HIx.
Hypothesis OADD : jo_object_add_P HIx.
Hypothesis NEWO : jo_new_object_P HIx.
Hypothesis NEWA : jo_new_array_P HIx.

Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (fc0 : bv 32) (md0 : Model).

Hypothesis STC : PE_STATIC HIx pf lo.

#[using="RC__ HIx lo STC"] Lemma len_le32 : forall (levels : list tlevel), length levels = Z.to_nat (pf_mxd pf) -> (length levels <= 32)%nat.
Proof. intros levels E. pose proof (PE_STATIC_mxd _ _ _ STC). lia. Qed.
Hypothesis OLDL : pf_oldl pf = LC_GLOBAL.
Hypothesis LOCME : rw_cells rsegs me LOCCELL [C8 (Z_to_bv 64 (pf_newl pf))].
Hypothesis NEWLR : 0 <= pf_newl pf < 2^64.
Hypothesis RAE : bv_unsigned (pe_ra sv) mod 2 = 0.
Hypothesis UTF : bytes_at rsegs me UTF8REP_ADDR utf8rep.
Hypothesis GOTF : bytes_at rsegs me GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))).
Hypothesis CSTR : CSTR_OK pf payload.
Hypothesis VM01 : model_vm_only md0 (pf_md pf).
Hypothesis KRET : forall ms' md', pe_post_g HIx pf sv F0 fc0 md0 LBc me lo ms' md' -> realizes rsegs (mkCfg ms' md') T.

Notation KOUTx := (KOUT HIx pf q LBc payload me lo sv T F0).
Notation KERRx := (KERR HIx pf q LBc payload me lo sv T F0).
Notation KOUT7x := (KOUT7 HIx pf q LBc payload me lo sv T F0).
Notation KERR7x := (KERR7 HIx pf q LBc payload me lo sv T F0).
Notation KALLx := (KALL HIx pf q LBc payload me lo sv T F0).
Notation CASEx := (CASE HIx pf q LBc payload me lo sv T F0 utf8rep).
Notation LB0x := (LB0 pf LBc).

Hypothesis HC_null : CASEx ST_null.
Hypothesis HC_bool : CASEx ST_boolean.
Hypothesis HC_number : CASEx ST_number.
Hypothesis HC_inf : CASEx ST_inf.

#[using="Type"] Lemma pe_post_weak : forall F fc md ms' md',
fsaved F0 F -> (frm0 fc0 -> frm0 fc) -> model_vm_only md0 md ->
pe_post_g HIx pf sv F fc md LBc me lo ms' md' -> pe_post_g HIx pf sv F0 fc0 md0 LBc me lo ms' md'.
Proof.
intros F fc md ms' md' FS FRM VM P.
destruct P as (m' & A' & gp & r & errv' & RBS & TBS & LK & RS & VM' & REST).
exists m', A', gp, r, errv', RBS, TBS, LK. split; [| split; [eapply model_vm_only_trans; [exact VM | exact VM'] | exact REST]].
destruct RS as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & fc' & E & FS' & FRM').
exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F', fc'.
split; [exact E|]. split; [eapply fsaved_trans; [exact FS | exact FS'] | intros Hf; exact (FRM' (FRM Hf))].
Qed.

#[using="PUT USE FREEL fc0 md0 STC OLDL LOCME NEWLR RAE VM01 KRET"] Lemma kout7 : KOUT7x.
Proof.
intros ts LK cop m md A cb j1 j2 utf errv x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc INVW TDK FS FRM.
pose proof INVW as (_ & (_ & _ & _ & _ & _ & _ & _ & MDV & _) & _).
eapply (seg_out HIx PUT USE FREEL); [exact STC | exact INVW | exact TDK | exact OLDL | exact LOCME | exact NEWLR | exact RAE |].
intros ms' md' P. apply KRET. eapply pe_post_weak; [exact FS | intros _; exact FRM | eapply model_vm_only_trans; [exact VM01 | exact MDV] | exact P].
Qed.

#[using="PUT USE FREEL fc0 md0 STC OLDL LOCME NEWLR RAE VM01 KRET"] Lemma kout : KOUTx.
Proof. exact (KOUT_of_7 _ _ _ _ _ _ _ _ _ _ kout7). Qed.

#[using="PUT USE FREEL fc0 md0 STC OLDL LOCME NEWLR RAE VM01 KRET"] Lemma kerr7 : KERR7x.
Proof.
intros ts LK cop e m md A cb j1 j2 utf errv x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc INVW TDK FS FRM.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INVW as (CORE & BASE & LVW).
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (proj1 BASE) as HP.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
set (tk := pf_tk pf) in *. set (spf := pf_spf pf) in *. set (len := pf_len pf) in *. set (sb := pf_sb pf) in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (LBall := pe_blocks pf q LB0x ts0 ++ LK) in *.
assert (INtk : In (tk, 72) LBall) by (unfold LBall, pe_blocks; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * pf_mxd pf)) LBall) by (unfold LBall, pe_blocks; apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.

assert (TSB : forall a n, In (a, n) (tstate_blocks ts0) -> In (a, n) LBall /\ a <> tk).
{ intros a n Hin. split; [unfold LBall, pe_blocks; apply in_or_app; left; apply in_or_app; left; exact Hin|].
intros ->. generalize ND; intros ND'. unfold LBall, pe_blocks in ND'. rewrite !map_app in ND'. apply NoDup_app_remove_r in ND'.
eapply (NoDup_app_in2 _ _ tk ND'); [exact (in_map blk_addr _ _ Hin) | left; reflexivity]. }
assert (Htq : tk <> q).
{ generalize ND; intros ND'. unfold LBall, pe_blocks in ND'. rewrite !map_app in ND'. apply NoDup_app_remove_r in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_mxd] in ND'. fold tk in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * pf_mxd pf) HP INtk INq Htq) as Hdtq.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(tk + 36, tk + 40)] m) as MU.
stash PB. stash BASE. stash LVW.
apply rz_evt; [exact MOK|]. unfold pe_ms7, PE_ERR. fold tk spf len sb.
step.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
assert (AG : agree_on rsegs (tstate_blocks ts0) m mc)
by (eapply agree_of_munch; [exact MU | exact WM |]; intros a n Hin; destruct (TSB a n Hin) as [HinL Hne];
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n tk 72 HP HinL INtk Hne); pose proof (heap_blk S4L HIx _ _ _ _ a n HP HinL) as (Hn0 & _); cbn; lia);
eapply (kout7 (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) e ucs high quote) obj objs objbs) LK cop)
end; [| eapply tdepth_ok_same; [reflexivity | reflexivity | reflexivity | exact TDK] | exact FS | exact FRM].
unstash PB. unstash BASE. unstash LVW.
split; [| split].
- unfold PE_CORE; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK|]. split; [| split; [exact Hpb | split; [| exact FR]]].
+ eapply pbuf_agree; [exact PB | exact AG | intros b Hb; unfold tstate_blocks, ts0; cbn [t_pbs pf_mxd]; apply in_or_app; left; exact Hb].
+ eapply (tstack_transport rsegs); [exact TSK | exact MU | exact WM |]. intros j Hj. rewrite LEN32 in Hj. cbn. lia.
- eapply (PE_BASE_write HIx); [exact STC | exact BASE | | exact MU | exact WM | assumption |].
+ intros b Hb. unfold LBall, pe_blocks. apply in_or_app; left. apply in_or_app; right. right; right. exact Hb.
+ apply Forall_cons; [| apply Forall_nil]. unfold base_w. cbn [fst snd pf_mxd]. left. exists tk, 72. split; [exact INtk|]. split; [| lia].
intros k Hin. generalize ND; intros ND'. unfold LBall, pe_blocks in ND'. rewrite !map_app in ND'. apply NoDup_app_remove_r in ND'. apply NoDup_app_remove_l in ND'.
cbn [map app blk_addr fst pf_mxd] in ND'. fold tk in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. apply Hni. unfold LB0. right. exact (in_map blk_addr _ _ Hin).
- cbn [t_levels t_depth pf_mxd]. intros i li Hli. eapply lvl_weak_agree; [exact (LVW i li Hli) | exact AG |].
intros b Hb. unfold tstate_blocks, ts0; cbn [t_pbs t_objbs t_levels pf_mxd]. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks li). split; [apply in_map; eapply nth_error_In; exact Hli | exact Hb].
Qed.

#[using="PUT USE FREEL fc0 md0 STC OLDL LOCME NEWLR RAE VM01 KRET"] Lemma kerr : KERRx.
Proof. exact (KERR_of_7 _ _ _ _ _ _ _ _ _ _ kerr7). Qed.

#[using="pf sv NEWLR"] Lemma cur_st_lupd : forall depth levels l co pb pbs x o os obs,
(depth < length levels)%nat ->
cur_st (TST depth (lupd levels depth l) co pb pbs x o os obs) = tl_st l.
Proof. intros. unfold cur_st. cbn [t_levels t_depth pf_mxd]. rewrite nth_error_lupd_eq by lia. reflexivity. Qed.
#[using="pf sv NEWLR"] Lemma cur_ss_lupd : forall depth levels l co pb pbs x o os obs,
(depth < length levels)%nat ->
cur_ss (TST depth (lupd levels depth l) co pb pbs x o os obs) = tl_ss l.
Proof. intros. unfold cur_ss. cbn [t_levels t_depth pf_mxd]. rewrite nth_error_lupd_eq by lia. reflexivity. Qed.
#[using="pf sv NEWLR"] Lemma rank_ge1 : forall st ss, (1 <= rank st ss)%nat.
Proof. intros. unfold rank. lia. Qed.
#[using="Type"] Lemma cur_st_of : forall ts l, nth_error (t_levels ts) (t_depth ts) = Some l -> cur_st ts = tl_st l.
Proof. intros ts l H. unfold cur_st. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma cur_ss_of : forall ts l, nth_error (t_levels ts) (t_depth ts) = Some l -> cur_ss ts = tl_ss l.
Proof. intros ts l H. unfold cur_ss. rewrite H. reflexivity. Qed.

Local Ltac tdsame TD := first [ exact TD
| lazymatch type of TD with tdepth_ok ?tsd => eapply (tdepth_ok_same tsd); [ | | | exact TD]; unfold ts_set_co, ts_set_err, UIsM.Mq2.ts_set_pbs, UIsM.Mq2.ts_set_level; cbn [t_levels t_depth t_objs pf_mxd]; reflexivity end ].

#[using="PUT USE FREEL MEMMOVE STRDUP AADD SHRINK OADD NEWO NEWA fc0 md0 STC OLDL LOCME NEWLR RAE UTF GOTF CSTR VM01 KRET HC_null HC_bool HC_number HC_inf"] Theorem pe_master : forall n, KALLx n.
Proof.
induction n as [|n IH].
- split; [| split; [| split]]; intros until fc; intros M; exfalso; lia.
- pose proof IH as IHall. destruct IH as (IHL & IHR & IHB & IHB2).
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
split; [| split; [| split]].
+
intros ts m md A cb j1 j2 utf errv x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc M INV NN SP TD CLT FS FRM.
pose proof INV as [(LEN32 & D32 & CO & _) _].
eapply (seg_loop HIx); [exact STC | exact INV | exact CLT | | |].
*
intros m' c a0' j2' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' Hco Hc INV' FS' FRM'.
eapply IHR; [| exact INV' | exact Hco | exact Hc | intros E; exfalso; exact (NN E) | exact SP | exact TD | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
unfold mloop, mredo in *. pose proof (rank_le (cur_st ts) (cur_ss ts)). lia.
*
intros m' e x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' Hco INV' FS' FRM'.
eapply kout; [apply PE_INV_W; exact INV' | tdsame TD | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
*
intros x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' Hco.
eapply kerr; [apply PE_INV_W; exact INV | exact TD | exact FS | exact FRM].
+
intros ts m md A cb j1 j2 utf errv x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc M INV Hco Hcb NUM SP TD FS FRM.
pose proof INV as [(LEN32 & D32 & CO & _) REST]. pose proof REST as (HP & LV & _).
destruct (nth_error (t_levels ts) (t_depth ts)) as [l|] eqn:Hl; [| exfalso; apply nth_error_None in Hl; lia].
pose proof (LV _ _ Hl) as (ST26 & SS26 & JO & MODE). rewrite Nat.ltb_irrefl, Nat.eqb_refl in MODE.
destruct MODE as (cc & hn & HM & CLS & NMK).
pose proof (cur_st_of ts l Hl) as Est. pose proof (cur_ss_of ts l Hl) as Ess.
unfold mredo in M. rewrite Est, Ess in M.
assert (KO := kout). assert (KE := kerr).
eapply (seg_redo HIx); [exact STC | exact INV | exact Hl |]. intros a3r a4r.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.

assert (MB : forall co', co <= co' <= pf_len pf -> (mbase pf (TST depth levels co' pb pbs x obj objs objbs) <= mbase pf (TST depth levels co pb pbs x obj objs objbs))%nat).
{ intros co' Hc. unfold mbase. cbn [t_co pf_mxd]. lia. }
set (ts0 := TST depth levels co pb pbs x obj objs objbs) in INV.

pose proof (rank_ge1 (tl_st l) (tl_ss l)) as RG1.
Local Ltac kfs FS := first [exact FS | eapply fsaved_trans; [exact FS | eassumption]].
Local Ltac kfrm FRM := first [exact FRM | match goal with H : frm0 _ -> frm0 _ |- _ => exact (H FRM) end].

Local Ltac drop := repeat match goal with
| H : KALL _ _ _ _ _ _ _ _ _ _ _ |- _ => clear H  | H : KLOOP _ _ _ _ _ _ _ _ _ _ _ |- _ => clear H
| H : KREDO _ _ _ _ _ _ _ _ _ _ _ |- _ => clear H | H : KBRK _ _ _ _ _ _ _ _ _ _ _ |- _ => clear H
| H : KBRK2 _ _ _ _ _ _ _ _ _ _ _ |- _ => clear H | H : KOUT _ _ _ _ _ _ _ _ _ _ |- _ => clear H
| H : KERR _ _ _ _ _ _ _ _ _ _ |- _ => clear H end.

Local Ltac clearN := repeat match goal with H : tl_st _ <> _ |- _ => clear H end.

Local Ltac tdok Hl :=
first [ match goal with TD' : tdepth_ok _ |- _ => exact TD' end
| match goal with TD' : tdepth_ok ?tsd |- _ => eapply (tdepth_ok_same tsd); [reflexivity | reflexivity | reflexivity | exact TD'] end
| match goal with TD' : tdepth_ok ?tsd |- _ =>
eapply (tdepth_ok_upd tsd); [exact TD' | exact Hl
| cbn [tl_cs t_objs pf_mxd]; lazymatch type of Hl with nth_error _ _ = Some ?lv => pose proof (odep_nonneg (tl_cs lv)) end; first [lia | cbn [odep sdepth pf_mxd]; lia]
| cbn [t_depth pf_mxd]; lia
| first [ reflexivity
| match goal with Z1 : zin _ [ST_array_add; ST_ovadd] = false |- _ => exact Z1 end
| lazymatch goal with |- zin ?stv _ = false =>
repeat match goal with Hor : _ \/ _ |- _ => lazymatch type of Hor with context [stv] => destruct Hor as [Hor|Hor] end end;
repeat match goal with Hc : _ /\ _ |- _ => lazymatch type of Hc with context [stv] => destruct Hc as [? Hc] end end;
subst; first [reflexivity | match goal with Z1 : zin _ [ST_array_add; ST_ovadd] = false |- _ => exact Z1 end] end ] ] end
| match goal with TD' : tdepth_ok ?tsd |- _ =>
eapply (tdepth_ok_absorb tsd); [exact TD' | exact Hl
| match goal with E : tl_st _ = _ |- _ => rewrite E; reflexivity end
| cbn [tl_cs t_objs pf_mxd]; match goal with E : tl_cs _ = Some _ |- _ => rewrite E end;
first [apply odep_absorb_arr | eapply odep_absorb_obj; eassumption]
| reflexivity] end
| match goal with TD' : tdepth_ok ?tsd |- _ =>
eapply (tdepth_ok_push tsd); [exact TD' | exact Hl | cbn [t_depth t_levels pf_mxd]; lia | cbn [t_levels pf_mxd]; apply len_le32; assumption | reflexivity | reflexivity] end
| idtac ].

Local Ltac spok_a :=
first [ intros HH; discriminate HH
| intros HH; exfalso; match goal with Z0 : zin _ [ST_null; ST_boolean; ST_inf] = false |- _ => rewrite Z0 in HH; discriminate HH end
| lazymatch goal with |- zin ?stv _ = true -> _ =>
is_var stv; intros HH; exfalso;
repeat match goal with Hor : _ \/ _ |- _ => lazymatch type of Hor with context [stv] => destruct Hor as [Hor|Hor] end end;
repeat match goal with Hc : _ /\ _ |- _ => lazymatch type of Hc with context [stv] => destruct Hc as [? Hc] end end;
subst; first [ discriminate HH
| match goal with Z0 : zin _ [ST_null; ST_boolean; ST_inf] = false |- _ => rewrite Z0 in HH; discriminate HH end
| congruence ] end
| rewrite ?unsigned_lit by lia; rewrite ?Zmod_0_l; intros _; lia
| intros HH; exfalso; congruence
| idtac ].

Local Ltac spok_b Hl :=
first [ intros HH; discriminate HH
| intros _; assumption
| rewrite ?unsigned_lit by lia; intros _; lia
| intros HH; exfalso; match goal with Z0 : zin _ [ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false |- _ => rewrite Z0 in HH; discriminate HH end
| lazymatch goal with |- zin ?stv _ = true -> _ =>
is_var stv; intros HH; exfalso;
repeat match goal with Hor : _ \/ _ |- _ => lazymatch type of Hor with context [stv] => destruct Hor as [Hor|Hor] end end;
repeat match goal with Hc : _ /\ _ |- _ => lazymatch type of Hc with context [stv] => destruct Hc as [? Hc] end end;
subst; first [ discriminate HH
| match goal with Z0 : zin _ [ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false |- _ => rewrite Z0 in HH; discriminate HH end
| congruence ] end
| intros _; match goal with SP0 : SPOK _ _ |- _ => apply (proj2 SP0); unfold cur_st; cbn [t_levels t_depth pf_mxd]; rewrite Hl;
match goal with E : tl_st _ = _ |- _ => rewrite E; reflexivity end end
| intros HH; exfalso; congruence
| idtac ].

Local Ltac spok Hl :=
unfold SPOK, SPV, cur_st; cbn [t_levels t_depth t_x t_co ts_stpos pf_mxd];
rewrite ?nth_error_lupd_eq by (rewrite ?lupd_length; lia); try rewrite Hl; cbn [tl_st tl_ss pf_mxd];
split; [spok_a | spok_b Hl].

Local Ltac pre t Hl := unfold t; unfold UIsM.Mq2.ts_set_level, UIsM.Mq2.ts_set_pbs, Udyh.Mq3.ts_set_level, Udyh.Mq4.ts_set_level, ts_set_co, ts_set_err, ts_esc_pop, ts_esc_set, ts_ws;
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd];
try rewrite Hl; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].

Local Ltac msr MB M RG1 :=
unfold mredo, mbrk, mloop;
try (rewrite cur_st_lupd by (rewrite ?lupd_length; lia)); try (rewrite cur_ss_lupd by (rewrite ?lupd_length; lia));
cbn [tl_st tl_ss pf_mxd]; unfold mbase, rank; unfold mbase, rank in M; cbn -[Nat.mul Nat.add Z.to_nat Z.sub] in M |- *;
first [ lia
| match goal with |- context [Z.to_nat (_ - ?c')] =>
pose proof (MB c' ltac:(lia)) as MBq; unfold mbase in MBq; cbn [t_co pf_mxd] in MBq; unfold rank in RG1; lia end ].

Local Ltac notnum Hl :=
first [ intros Ecs; exfalso; revert Ecs | idtac ];
unfold NUMC, cur_st; cbn [t_levels t_depth t_pbs t_pb pf_mxd];
rewrite ?nth_error_lupd_eq by (rewrite ?lupd_length; lia); try rewrite Hl; cbn [tl_st pf_mxd];
unfold ST_eatws, ST_start, ST_finish, ST_null, ST_comment_start, ST_comment, ST_comment_eol, ST_comment_end,
ST_string, ST_string_escape, ST_escape_unicode, ST_esc_need_escape, ST_esc_need_u, ST_boolean, ST_number,
ST_array, ST_array_add, ST_array_sep, ST_ofs, ST_ofield, ST_ofend, ST_ovalue, ST_ovadd, ST_osep,
ST_array_after_sep, ST_ofs_after_sep, ST_inf in *;

first [ discriminate | assumption | congruence | intros E; first [discriminate E | congruence | lia] | lia ].
Local Ltac withINV k := lazymatch goal with I' : PE_INV _ _ _ _ _ _ _ _ _ _ ?ts' _ _ _ _ _ _ |- _ => k I' ts' end.
Local Ltac KR IHR ts0 Hl FS FRM MB M RG1 := pre ts0 Hl; intros; withINV ltac:(fun I' ts' => eapply (IHR ts'); drop;
[ msr MB M RG1 | exact I' | cbn [t_co pf_mxd]; lia | first [eassumption | cbn [t_co pf_mxd]; eassumption] | notnum Hl | spok Hl | tdok Hl | kfs FS | kfrm FRM ]).
Local Ltac KB IHB ts0 Hl FS FRM MB M RG1 := pre ts0 Hl; intros; withINV ltac:(fun I' ts' => eapply (IHB ts'); drop;
[ msr MB M RG1 | exact I' | cbn [t_co pf_mxd]; lia | first [eassumption | cbn [t_co t_levels t_depth pf_mxd]; eassumption] | notnum Hl | spok Hl | tdok Hl | kfs FS | kfrm FRM ]).
Local Ltac KB2 IHB2 ts0 Hl FS FRM MB M RG1 := pre ts0 Hl; intros; withINV ltac:(fun I' ts' => eapply (IHB2 ts'); drop;
[ msr MB M RG1 | exact I' | cbn [t_co pf_mxd]; lia | first [eassumption | cbn [t_co t_levels t_depth pf_mxd]; eassumption] | notnum Hl | spok Hl | tdok Hl | kfs FS | kfrm FRM ]).
Local Ltac KOW KO ts0 Hl FS FRM := pre ts0 Hl; intros; eapply KO; drop; [ first [ apply PE_INV_W; eassumption | apply PE_INVK_W; eassumption | eassumption ] | tdok Hl | kfs FS | kfrm FRM ].
Local Ltac KEW KE ts0 Hl FS FRM := pre ts0 Hl; intros; eapply KE; drop; [ first [ apply PE_INV_W; eassumption | apply PE_INVK_W; eassumption | eassumption ] | tdok Hl | kfs FS | kfrm FRM ].

destruct (Z.eq_dec (tl_st l) ST_eatws) as [E0|N0].
{ clearN.
replace (pe_jt (tl_st l)) with (pe_jt ST_eatws) by (rewrite E0; reflexivity). rewrite E0 in M.
assert (MF : tl_ss l <> ST_number /\ tl_ss l <> ST_eatws /\ (rank (tl_ss l) (tl_ss l) < rank ST_eatws (tl_ss l))%nat /\ zin (tl_ss l) [ST_null; ST_boolean; ST_inf] = false /\ zin (tl_ss l) [ST_array_add; ST_ovadd] = false /\ zin (tl_ss l) [ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false).
{ rewrite E0 in HM. clear - HM SS26. enum_from (tl_ss l) 0 27%nat; cbv in HM; try discriminate; (split; [cbv; discriminate|]); (split; [cbv; discriminate|]); (split; [cbv; lia|]); (split; [reflexivity | split; reflexivity]). }
destruct MF as (SSn & SSe & RK & SSZ & SSA & SSE).
eapply (seg_eatws HIx MEMMOVE) with (ts := ts0); [exact STC | exact INV | exact CSTR | exact Hl | exact E0 | exact Hco | exact Hcb | | | | |].
-
pre ts0 Hl. intros m' co' cb' j2' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' Hco' Hcb' Hws INV'.
eapply (IHR (TST depth (lupd levels depth (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co' pb pbs
(TS (ts_isd x) (ts_stpos x) (Z_to_bv 64 co') (ts_err x) (ts_ucs x) (ts_high x) (ts_quote x)) obj objs objbs));
[| exact INV' | cbn [t_co pf_mxd]; lia | exact Hcb' | | spok Hl | tdok Hl | exact FS | exact FRM]. all: drop.
+ unfold mredo. rewrite cur_st_lupd, cur_ss_lupd by lia. cbn [tl_st tl_ss pf_mxd].
pose proof (MB co' ltac:(lia)) as MB'. unfold mbase in MB', M |- *. cbn [t_co pf_mxd] in MB', M |- *. unfold rank in RK, M |- *. cbn -[Nat.mul Nat.add Z.to_nat Z.sub] in RK, M |- *. lia.
+ intros Ecs. exfalso. rewrite cur_st_lupd in Ecs by lia. cbn [tl_st pf_mxd] in Ecs. exact (SSn Ecs).
-  KB IHB ts0 Hl FS FRM MB M RG1.
-  KEW KE ts0 Hl FS FRM.
-  KOW KO ts0 Hl FS FRM.
-  KEW KE ts0 Hl FS FRM. }
destruct (Z.eq_dec (tl_st l) ST_start) as [E1|N1].
{ clearN.
replace (pe_jt (tl_st l)) with (pe_jt ST_start) by (rewrite E1; reflexivity). rewrite E1 in M.
eapply (seg_start_dispatch HIx) with (ts := ts0); [exact STC | exact INV |]. intros a1' a3'. cbn [t_co t_depth pf_mxd].
assert (MODE1 : tl_ss l = ST_start /\ cc = CNone /\ hn = false) by (eapply start_mode; [exact SS26 | rewrite <- E1; exact HM]).
destruct MODE1 as (Ess1 & -> & ->).
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.

assert (KSC : forall stn, (stn = ST_boolean \/ stn = ST_inf \/ stn = ST_null) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22b7c co x1 gp t0 t1 t2 (Z_to_bv 64 stn) a1' (Z_to_bv 64 (q + 32 * Z.of_nat depth)) a3' a4r a5 a6 a7 (Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat depth)) s10 t3 t4 t5 t6 F fc m) md) T).
{ intros stn Hstn. eapply (seg_start_scalar HIx) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E1 | exact Hstn |].
pre ts0 Hl. intros m' x1' a0y a1y INV'.
withINV ltac:(fun I' ts' => eapply (IHR ts'); [ | exact I' | cbn [t_co pf_mxd]; lia | exact Hcb | | spok Hl | tdok Hl | exact FS | exact FRM ]). all: drop.
- unfold mredo. rewrite cur_st_lupd, cur_ss_lupd by lia. cbn [tl_st tl_ss pf_mxd]. unfold mbase, rank in M |- *. cbn -[Nat.mul Nat.add Z.to_nat Z.sub] in M |- *.
destruct Hstn as [-> | [-> | ->]]; cbn -[Nat.mul Nat.add Z.to_nat Z.sub]; lia.
- intros Ecs. exfalso. rewrite cur_st_lupd in Ecs by lia. cbn [tl_st pf_mxd] in Ecs. destruct Hstn as [-> | [-> | ->]]; discriminate Ecs. }
assert (KUNX : forall a0x a1x : word, realizes rsegs (mkCfg (pe_ms rsegs pf 0x23db4 co x1 gp t0 t1 t2 a0x a1x (Z_to_bv 64 (q + 32 * Z.of_nat depth)) a3' a4r a5 a6 a7 (Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat depth)) s10 t3 t4 t5 t6 F fc m) md) T).
{ intros a0x a1x. pose proof (proj1 (proj2 INV)) as HPi. pose proof (heap_model_ok _ _ _ _ _ _ HPi) as MOKi.
apply rz_evt; [exact MOKi|]. unfold pe_ms. step. step. apply evt_RZ_done.
eapply KE; [apply PE_INV_W; exact INV | exact TD | exact FS | exact FRM]. }

pose proof (proj1 (proj2 INV)) as HPi. pose proof (heap_model_ok _ _ _ _ _ _ HPi) as MOKi.
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocks pf q LB0x ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * pf_mxd pf) HPi INq) as (_ & Hqal & _).
assert (HA2 : (q + 32 * Z.of_nat depth) mod 16 = 0) by lia.
destruct (pe_jt2_cases (bv_unsigned cb) CBR) as [[E C]|[[E C]|[[E C]|[[E C]|[[E C]|[[E C]|[[E C]|[[E C]|E]]]]]]]]; rewrite E.
-
eapply (seg_start_string HIx) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E1 |].
KB2 IHB2 ts0 Hl FS FRM MB M RG1.
-
apply rz_evt; [exact MOKi|]. unfold pe_ms.
pose proof INV as [(_ & _ & _ & _ & TOKi & _) _]. destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *.
pose proof (tok_flags_byte_g _ _ _ _ _ _ _ _ TOKi) as FLB. pose proof (PE_STATIC_mxd _ _ _ STC) as MXB.
step. rewrite (zxb_byte (pf_fl pf)). step.
rewrite (unsigned_lit (pf_fl pf mod 256)) by (pose proof (Z.mod_pos_bound (pf_fl pf) 256 ltac:(lia)); lia). rewrite (land_mod256 (pf_fl pf) 1) by lia.
destruct (land1_cases (pf_fl pf)) as [F1 | F1]; rewrite F1.
+ step. if_false. apply evt_RZ_done.
eapply (seg_start_string HIx) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E1 |].
KB2 IHB2 ts0 Hl FS FRM MB M RG1.
+ step. if_true. apply evt_RZ_done. apply KUNX.
-
eapply (seg_start_number HIx) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E1 |].
pre ts0 Hl. intros m' x1' a0y a1y INV' PBC.
withINV ltac:(fun I' ts' => eapply (IHR ts'); [ | exact I' | cbn [t_co pf_mxd]; lia | exact Hcb | | spok Hl | tdok Hl | exact FS | exact FRM ]). all: drop.
+ unfold mredo. rewrite cur_st_lupd, cur_ss_lupd by lia. cbn [tl_st tl_ss pf_mxd]. unfold mbase, rank in M |- *. cbn -[Nat.mul Nat.add Z.to_nat Z.sub] in M |- *. lia.
+ intros _. cbn [t_pbs t_pb pf_mxd]. exact PBC.
-
apply rz_evt; [exact MOKi|]. unfold pe_ms. tk1_walk 0x229b0 0x22b7c 8%nat Hcb. apply evt_RZ_done. apply (KSC ST_boolean). left; reflexivity.
-
apply rz_evt; [exact MOKi|]. unfold pe_ms. tk1_walk 0x22b6c 0x22b7c 8%nat Hcb. apply evt_RZ_done. apply (KSC ST_inf). right; left; reflexivity.
-
apply rz_evt; [exact MOKi|]. unfold pe_ms. tk1_walk 0x22b58 0x22b7c 8%nat Hcb. apply evt_RZ_done. apply (KSC ST_null). right; right; reflexivity.
-
eapply (seg_start_array HIx NEWA) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E1 | |].
+ KB IHB ts0 Hl FS FRM MB M RG1.
+ KEW KE ts0 Hl FS FRM.
-
eapply (seg_start_object HIx NEWO) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E1 | |].
+ KB IHB ts0 Hl FS FRM MB M RG1.
+ KEW KE ts0 Hl FS FRM.
-
apply KUNX. }

destruct (Z.eq_dec (tl_st l) ST_finish) as [E2|N2].
{ clearN.
replace (pe_jt (tl_st l)) with (pe_jt ST_finish) by (rewrite E2; reflexivity). rewrite E2 in M.
eapply (seg_finish HIx PUT) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E2 | |].
-  intros. eapply KO; [apply PE_INV_W; exact INV | exact TD | exact FS | exact FRM].
-
pre ts0 Hl. intros m' md' A' errv' dp lp x1' gp' t0' t1' t2' a0' a1' a2x a3x a4x a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' Hdp Hlp Hstp INV' FS' FRM'.
eapply (IHR (TST dp (lupd levels (S dp) lvl_reset) co pb pbs x (tl_cur l) (tl_cs l) (tl_cbs l)));
[| exact INV' | cbn [t_co pf_mxd]; lia | exact Hcb | | | | kfs FS | kfrm FRM]. all: drop.
+ unfold mredo, cur_st, cur_ss. cbn [t_levels t_depth t_co pf_mxd]. rewrite nth_error_lupd_neq by lia. rewrite Hlp.
unfold mbase, rank in M |- *. cbn [t_co pf_mxd] in M |- *. destruct Hstp as [-> | ->]; cbn -[Nat.mul Nat.add Z.to_nat Z.sub] in M |- *; lia.
+ intros Ecs. exfalso. unfold cur_st in Ecs. cbn [t_levels t_depth pf_mxd] in Ecs. rewrite nth_error_lupd_neq in Ecs by lia. rewrite Hlp in Ecs. destruct Hstp as [E|E]; rewrite E in Ecs; discriminate Ecs.
+ unfold SPOK, cur_st. cbn [t_levels t_depth pf_mxd]. rewrite nth_error_lupd_neq by lia. rewrite Hlp. split; intros HH; exfalso; destruct Hstp as [E|E]; rewrite E in HH; discriminate HH.
+ eapply (tdepth_ok_pop ts0); [exact TD | exact Hl | unfold ts0; cbn [t_depth pf_mxd]; exact Hdp | unfold ts0; cbn [t_levels pf_mxd]; exact Hlp | reflexivity | unfold ts0; cbn [t_levels pf_mxd]; exact (len_le32 _ LEN32)]. }
destruct (Z.eq_dec (tl_st l) ST_null) as [E3|N3]. { clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_null) by (rewrite E3; reflexivity).
eapply (HC_null n) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E3 | exact Hco | exact Hcb | exact NUM | exact SP | exact TD | exact UTF | exact GOTF | exact CSTR | exact FS | exact FRM
| unfold ts0, mredo, cur_st, cur_ss; cbn [t_levels t_depth pf_mxd]; rewrite Hl; unfold mbase in M |- *; cbn [t_co pf_mxd] in M |- *; lia
| exact IHall | exact kout7 | exact kerr7 ]. }
destruct (Z.eq_dec (tl_st l) ST_comment_start) as [E4|N4].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_comment_start) by (rewrite E4; reflexivity). rewrite E4 in M.
eapply (seg_cstart HIx MEMMOVE) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E4 | exact Hco | | |].
- KB IHB ts0 Hl FS FRM MB M RG1. - KEW KE ts0 Hl FS FRM. - KEW KE ts0 Hl FS FRM. }
destruct (Z.eq_dec (tl_st l) ST_comment) as [E5|N5].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_comment) by (rewrite E5; reflexivity). rewrite E5 in M.
eapply (seg_comment HIx MEMMOVE) with (ts := ts0); [exact STC | exact INV | exact CSTR | exact Hl | exact E5 | exact Hco | exact Hcb | | |].
- KB IHB ts0 Hl FS FRM MB M RG1. - KOW KO ts0 Hl FS FRM. - KEW KE ts0 Hl FS FRM. }
destruct (Z.eq_dec (tl_st l) ST_comment_eol) as [E6|N6].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_comment_eol) by (rewrite E6; reflexivity). rewrite E6 in M.
eapply (seg_ceol HIx MEMMOVE) with (ts := ts0); [exact STC | exact INV | exact CSTR | exact Hl | exact E6 | exact Hco | exact Hcb | | |].
- KB IHB ts0 Hl FS FRM MB M RG1. - KOW KO ts0 Hl FS FRM. - KEW KE ts0 Hl FS FRM. }
destruct (Z.eq_dec (tl_st l) ST_comment_end) as [E7|N7].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_comment_end) by (rewrite E7; reflexivity). rewrite E7 in M.
eapply (seg_cend HIx MEMMOVE) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E7 | exact Hco | | ].
- KB IHB ts0 Hl FS FRM MB M RG1. - KEW KE ts0 Hl FS FRM. }
destruct (Z.eq_dec (tl_st l) ST_string) as [E8|N8].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_string) by (rewrite E8; reflexivity). rewrite E8 in M.
eapply (seg_string HIx MEMMOVE) with (ts := ts0); [exact STC | exact INV | exact CSTR | exact Hl | exact E8 | exact Hco | exact Hcb | | | | |].
- KB IHB ts0 Hl FS FRM MB M RG1. - KB IHB ts0 Hl FS FRM MB M RG1. - KOW KO ts0 Hl FS FRM. - KEW KE ts0 Hl FS FRM.
-  KEW KE ts0 Hl FS FRM. }
destruct (Z.eq_dec (tl_st l) ST_string_escape) as [E9|N9].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_string_escape) by (rewrite E9; reflexivity). rewrite E9 in M.
assert (MF : tl_ss l <> ST_number /\ zin (tl_ss l) [ST_null; ST_boolean; ST_inf] = false /\ zin (tl_ss l) [ST_array_add; ST_ovadd] = false /\ zin (tl_ss l) [ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false).
{ rewrite E9 in HM. clear - HM SS26. enum_from (tl_ss l) 0 27%nat; cbv in HM; try discriminate; (split; [cbv; discriminate | split; [reflexivity | split; reflexivity]]). }
destruct MF as (MF & SSZ & SSA & SSE).
eapply (seg_sesc HIx MEMMOVE) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E9 | | | |].
- KB IHB ts0 Hl FS FRM MB M RG1. - KB IHB ts0 Hl FS FRM MB M RG1. - KEW KE ts0 Hl FS FRM. - KEW KE ts0 Hl FS FRM. }
destruct (Z.eq_dec (tl_st l) ST_escape_unicode) as [E10|N10].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_escape_unicode) by (rewrite E10; reflexivity). rewrite E10 in M.
assert (MF : tl_ss l <> ST_number /\ zin (tl_ss l) [ST_null; ST_boolean; ST_inf] = false /\ zin (tl_ss l) [ST_array_add; ST_ovadd] = false).
{ rewrite E10 in HM. clear - HM SS26. enum_from (tl_ss l) 0 27%nat; cbv in HM; try discriminate; (split; [cbv; discriminate | split; reflexivity]). }
destruct MF as (MF & SSZ & SSA).
eapply (seg_euni HIx MEMMOVE) with (ts := ts0); [exact STC | exact INV | apply (proj2 SP); unfold cur_st; cbn [t_levels t_depth pf_mxd]; rewrite Hl, E10; reflexivity | exact CSTR | exact Hl | exact E10 | exact Hco | exact Hcb | exact UTF | | | | |].
- KB IHB ts0 Hl FS FRM MB M RG1. - KEW KE ts0 Hl FS FRM. - KEW KE ts0 Hl FS FRM. - KOW KO ts0 Hl FS FRM.
-  KEW KE ts0 Hl FS FRM. }
destruct (Z.eq_dec (tl_st l) ST_esc_need_escape) as [E11|N11].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_esc_need_escape) by (rewrite E11; reflexivity). rewrite E11 in M.
assert (MF : tl_ss l <> ST_number /\ (rank (tl_ss l) (tl_ss l) < rank ST_esc_need_escape (tl_ss l))%nat /\
(forall c hn, lvl_mode ST_esc_need_escape (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) /\
zin (tl_ss l) [ST_null; ST_boolean; ST_inf] = false /\ zin (tl_ss l) [ST_array_add; ST_ovadd] = false /\ zin (tl_ss l) [ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false).
{ rewrite E11 in HM. clear - HM SS26. enum_from (tl_ss l) 0 27%nat; cbv in HM; try discriminate;
(split; [cbv; discriminate|]); (split; [cbv; lia|]); (split; [intros c' hn' H'; cbv in H' |- *; exact H' | split; [reflexivity | split; reflexivity]]). }
destruct MF as (SSn & RK & HMODE & SSZ & SSA & SSE).
eapply (seg_needesc HIx MEMMOVE) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E11 | exact Hco | exact UTF | rewrite E11; exact HMODE | | |].
- KB2 IHB2 ts0 Hl FS FRM MB M RG1.
- pre ts0 Hl. intros. withINV ltac:(fun I' ts' => eapply (IHR ts'); [ | exact I' | cbn [t_co pf_mxd]; lia | exact Hcb | | spok Hl | tdok Hl | kfs FS | kfrm FRM ]). all: drop.
+ unfold mredo. rewrite cur_st_lupd, cur_ss_lupd by lia. cbn [tl_st tl_ss pf_mxd]. unfold mbase in M |- *. cbn [t_co pf_mxd] in M |- *.
unfold rank in RK, M |- *. cbn -[Nat.mul Nat.add Z.to_nat Z.sub] in RK, M |- *. lia.
+ intros Ecs. exfalso. rewrite cur_st_lupd in Ecs by lia. cbn [tl_st pf_mxd] in Ecs. exact (SSn Ecs).
- KEW KE ts0 Hl FS FRM. }
destruct (Z.eq_dec (tl_st l) ST_esc_need_u) as [E12|N12].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_esc_need_u) by (rewrite E12; reflexivity). rewrite E12 in M.
eapply (seg_needu HIx MEMMOVE) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E12 | exact Hco | exact UTF | | |].
- KB2 IHB2 ts0 Hl FS FRM MB M RG1. - KR IHR ts0 Hl FS FRM MB M RG1. - KEW KE ts0 Hl FS FRM. }
destruct (Z.eq_dec (tl_st l) ST_boolean) as [E13|N13]. { clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_boolean) by (rewrite E13; reflexivity).
eapply (HC_bool n) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E13 | exact Hco | exact Hcb | exact NUM | exact SP | exact TD | exact UTF | exact GOTF | exact CSTR | exact FS | exact FRM
| unfold ts0, mredo, cur_st, cur_ss; cbn [t_levels t_depth pf_mxd]; rewrite Hl; unfold mbase in M |- *; cbn [t_co pf_mxd] in M |- *; lia
| exact IHall | exact kout7 | exact kerr7 ]. }
destruct (Z.eq_dec (tl_st l) ST_number) as [E14|N14]. { clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_number) by (rewrite E14; reflexivity).
eapply (HC_number n) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E14 | exact Hco | exact Hcb | exact NUM | exact SP | exact TD | exact UTF | exact GOTF | exact CSTR | exact FS | exact FRM
| unfold ts0, mredo, cur_st, cur_ss; cbn [t_levels t_depth pf_mxd]; rewrite Hl; unfold mbase in M |- *; cbn [t_co pf_mxd] in M |- *; lia
| exact IHall | exact kout7 | exact kerr7 ]. }

assert (ARR : tl_st l = ST_array \/ tl_st l = ST_array_after_sep ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt (tl_st l)) co x1 gp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat depth)) a3r a4r a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat depth)) s10 t3 t4 t5 t6 F fc m) md) T).
{ intros Hst. clearN.
assert (RKa : rank (tl_st l) (tl_ss l) = 12%nat) by (destruct Hst as [E|E]; rewrite E; reflexivity). rewrite RKa in M.
eapply (seg_array HIx PUT SHRINK) with (ts := ts0); [exact STC | exact INV | exact Hl | exact Hst | | | |].
- KB IHB ts0 Hl FS FRM MB M RG1.
- KR IHR ts0 Hl FS FRM MB M RG1.
- intros. eapply KE; [apply PE_INV_W; exact INV | exact TD | exact FS | exact FRM].
-  pre ts0 Hl; intros; eapply KE; drop; [apply PE_INV_W; eassumption | | kfs FS | kfrm FRM].
eapply (tdepth_ok_upd ts0); [exact TD | exact Hl | cbn [tl_cs t_objs pf_mxd]; pose proof (odep_nonneg (tl_cs l)); lia | unfold ts0; cbn [t_depth pf_mxd]; pose proof (PE_STATIC_mxd _ _ _ STC); lia
| destruct Hst as [E|E]; rewrite E; reflexivity]. }
destruct (Z.eq_dec (tl_st l) ST_array) as [E15|N15]. { apply ARR. left; exact E15. }
destruct (Z.eq_dec (tl_st l) ST_array_add) as [E16|N16].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_array_add) by (rewrite E16; reflexivity). rewrite E16 in M.
assert (CS : exists kids, tl_cs l = Some (Sarr kids)).
{ rewrite E16 in HM. assert (Hcc : cc = CArr) by (clear - HM SS26; enum_from (tl_ss l) 0 27%nat; cbv in HM; try discriminate; injection HM as <- <-; reflexivity).
subst cc. destruct (tl_cs l) as [[| | | |k|k]|]; cbn in CLS; try contradiction. exists k; reflexivity. }
destruct CS as [kids Ecs].
eapply (seg_aadd HIx AADD) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E16 | exact Ecs | |].
- KR IHR ts0 Hl FS FRM MB M RG1. - KEW KE ts0 Hl FS FRM. }
destruct (Z.eq_dec (tl_st l) ST_array_sep) as [E17|N17].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_array_sep) by (rewrite E17; reflexivity). rewrite E17 in M.
eapply (seg_asep HIx SHRINK) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E17 | exact Hco | | |].
- KB2 IHB2 ts0 Hl FS FRM MB M RG1. - KB IHB ts0 Hl FS FRM MB M RG1.
- intros. eapply KE; [apply PE_INV_W; exact INV | exact TD | exact FS | exact FRM]. }

assert (OFS : tl_st l = ST_ofs \/ tl_st l = ST_ofs_after_sep ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt (tl_st l)) co x1 gp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat depth)) a3r a4r a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat depth)) s10 t3 t4 t5 t6 F fc m) md) T).
{ intros Hst. clearN.
replace (pe_jt (tl_st l)) with (pe_jt ST_ofs) by (destruct Hst as [E|E]; rewrite E; reflexivity).
assert (RKo : rank (tl_st l) (tl_ss l) = 1%nat) by (destruct Hst as [E|E]; rewrite E; reflexivity). rewrite RKo in M.
eapply (seg_ofs HIx) with (ts := ts0); [exact STC | exact INV | exact Hl | exact Hst | exact Hco | | |].
- KB IHB ts0 Hl FS FRM MB M RG1. - KB IHB ts0 Hl FS FRM MB M RG1.
- intros. eapply KE; [apply PE_INV_W; exact INV | exact TD | exact FS | exact FRM]. }
destruct (Z.eq_dec (tl_st l) ST_ofs) as [E18|N18]. { apply OFS. left; exact E18. }
destruct (Z.eq_dec (tl_st l) ST_ofield) as [E19|N19].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_ofield) by (rewrite E19; reflexivity). rewrite E19 in M.
eapply (seg_ofield HIx MEMMOVE STRDUP) with (ts := ts0); [exact STC | exact INV | exact CSTR | exact Hl | exact E19 | exact Hco | exact Hcb | | | | |].
- KB IHB ts0 Hl FS FRM MB M RG1. - KB IHB ts0 Hl FS FRM MB M RG1. - KOW KO ts0 Hl FS FRM. - KEW KE ts0 Hl FS FRM.
-  KEW KE ts0 Hl FS FRM. }
destruct (Z.eq_dec (tl_st l) ST_ofend) as [E20|N20].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_ofend) by (rewrite E20; reflexivity). rewrite E20 in M.
eapply (seg_ofend HIx) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E20 | exact Hco | |].
- KB IHB ts0 Hl FS FRM MB M RG1.
- intros. eapply KE; [apply PE_INV_W; exact INV | exact TD | exact FS | exact FRM]. }
destruct (Z.eq_dec (tl_st l) ST_ovalue) as [E21|N21].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_ovalue) by (rewrite E21; reflexivity). rewrite E21 in M.
eapply (seg_oval HIx PUT) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E21 | |].
- KR IHR ts0 Hl FS FRM MB M RG1.
- intros. eapply KE; [apply PE_INV_W; exact INV | exact TD | exact FS | exact FRM]. }
destruct (Z.eq_dec (tl_st l) ST_ovadd) as [E22|N22].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_ovadd) by (rewrite E22; reflexivity). rewrite E22 in M.
assert (CS : exists kids, tl_cs l = Some (Sobj kids)).
{ rewrite E22 in HM. assert (Hcc : cc = CObj) by (clear - HM SS26; enum_from (tl_ss l) 0 27%nat; cbv in HM; try discriminate; injection HM as <- <-; reflexivity).
subst cc. destruct (tl_cs l) as [[| | | |k|k]|]; cbn in CLS; try contradiction. exists k; reflexivity. }
destruct CS as [kids Ecs].
eapply (seg_ovadd HIx OADD) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E22 | exact Ecs | exact FRM | |].
- KR IHR ts0 Hl FS FRM MB M RG1. - KEW KE ts0 Hl FS FRM. }
destruct (Z.eq_dec (tl_st l) ST_osep) as [E23|N23].
{ clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_osep) by (rewrite E23; reflexivity). rewrite E23 in M.
eapply (seg_osep HIx) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E23 | exact Hco | |].
- KB2 IHB2 ts0 Hl FS FRM MB M RG1.
- intros. eapply KE; [apply PE_INV_W; exact INV | exact TD | exact FS | exact FRM]. }
destruct (Z.eq_dec (tl_st l) ST_array_after_sep) as [E24|N24]. { apply ARR. right; exact E24. }
destruct (Z.eq_dec (tl_st l) ST_ofs_after_sep) as [E25|N25]. { apply OFS. right; exact E25. }
destruct (Z.eq_dec (tl_st l) ST_inf) as [E26|N26]. { clearN. replace (pe_jt (tl_st l)) with (pe_jt ST_inf) by (rewrite E26; reflexivity).
eapply (HC_inf n) with (ts := ts0); [exact STC | exact INV | exact Hl | exact E26 | exact Hco | exact Hcb | exact NUM | exact SP | exact TD | exact UTF | exact GOTF | exact CSTR | exact FS | exact FRM
| unfold ts0, mredo, cur_st, cur_ss; cbn [t_levels t_depth pf_mxd]; rewrite Hl; unfold mbase in M |- *; cbn [t_co pf_mxd] in M |- *; lia
| exact IHall | exact kout7 | exact kerr7 ]. }
exfalso. unfold ST_eatws, ST_start, ST_finish, ST_null, ST_comment_start, ST_comment, ST_comment_eol, ST_comment_end, ST_string, ST_string_escape,
ST_escape_unicode, ST_esc_need_escape, ST_esc_need_u, ST_boolean, ST_number, ST_array, ST_array_add, ST_array_sep, ST_ofs, ST_ofield, ST_ofend,
ST_ovalue, ST_ovadd, ST_osep, ST_array_after_sep, ST_ofs_after_sep, ST_inf in *.

clear - ST26 N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12 N13 N14 N15 N16 N17 N18 N19 N20 N21 N22 N23 N24 N25 N26. lia.
+
intros ts m md A cb j1 j2 utf errv x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc M INV Hco Hcb NN SP TD FS FRM.
eapply (seg_break HIx); [exact STC | exact INV | exact Hco | |].
* intros m' a0' a1' Hz INV'.
eapply kout; [apply PE_INV_W; exact INV' | tdsame TD | exact FS | exact FRM].
* intros m' a1' Hnz INV'.
eapply (IHL (ts_set_co ts (t_co ts + 1))); [| exact INV' | exact NN | | | | exact FS | exact FRM].
{ unfold mbrk, mloop, mbase, ts_set_co in *. cbn [t_co pf_mxd]. lia. }
{ revert SP. unfold SPOK, ts_set_co, cur_st. destruct ts as [dp9 lv9 co9 pb9 pbs9 x9 ob9 os9 obs9]; cbn [t_levels t_depth t_x t_co pf_mxd]. intros [SPa SPb]. split; [intros Hz; specialize (SPa Hz); unfold SPV in *; cbn [ts_stpos pf_mxd] in *; lia | exact SPb]. }
{ eapply tdepth_ok_same; [| | | exact TD]; unfold ts_set_co; destruct ts; reflexivity. }
{
unfold ts_set_co; cbn [t_co pf_mxd]. intros NE. pose proof INV as [(_ & _ & CO & _) _].
destruct (peek_cases pf payload (t_co ts) cb LENR CSTR (proj1 RR) ltac:(lia) ltac:(lia) Hcb Hnz) as [[E _] | [_ LT]]; [exfalso; exact (NE E) | exact LT]. }
+
intros ts m md A cb j1 j2 utf errv x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc M INV Hco Hcb NN SP TD FS FRM.
eapply (seg_break HIx); [exact STC | exact INV | exact Hco | |].
* intros m' a0' a1' Hz INV'.
eapply kout; [apply PE_INV_W; exact INV' | tdsame TD | exact FS | exact FRM].
* intros m' a1' Hnz INV'.
eapply (IHL (ts_set_co ts (t_co ts + 1))); [| exact INV' | exact NN | | | | exact FS | exact FRM].
{ unfold mbrk, mloop, mbase, ts_set_co in *. cbn [t_co pf_mxd]. lia. }
{ revert SP. unfold SPOK, ts_set_co, cur_st. destruct ts as [dp9 lv9 co9 pb9 pbs9 x9 ob9 os9 obs9]; cbn [t_levels t_depth t_x t_co pf_mxd]. intros [SPa SPb]. split; [intros Hz; specialize (SPa Hz); unfold SPV in *; cbn [ts_stpos pf_mxd] in *; lia | exact SPb]. }
{ eapply tdepth_ok_same; [| | | exact TD]; unfold ts_set_co; destruct ts; reflexivity. }
{
unfold ts_set_co; cbn [t_co pf_mxd]. intros NE. pose proof INV as [(_ & _ & CO & _) _].
destruct (peek_cases pf payload (t_co ts) cb LENR CSTR (proj1 RR) ltac:(lia) ltac:(lia) Hcb Hnz) as [[E _] | [_ LT]]; [exfalso; exact (NE E) | exact LT]. }
Qed.

End PeMaster.

End RC__1.
