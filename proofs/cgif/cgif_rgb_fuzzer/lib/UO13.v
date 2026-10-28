(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK15 YK0o YK0v YQ0k YN06 YK0s YN02 YK1j YK1a.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09 YP0a YP0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YP0j YP0g YP0h YP0q YP0m YP0o YP10 YP0v
YP0n YP0r YP0u YP0c YP0e YP0f.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YO02 YO03 YQ01 YO2f
YO29 YO2a YO2c YO30
UO0c UO08 UO0b UO16 UO0y UO0z
UO14.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma rdn_of_present : forall (m : word -> option byte) n a,
(forall i, 0 <= i < Z.of_nat n -> present m (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
exists bs, rdn ubs2segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
intros m n. induction n as [|n IH]; intros a Hp Ha Hnw.
- exists []. split; reflexivity.
- destruct (Hp 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
destruct (IH (a + 1)) as (bs & Hbs & Hlen); [intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply Hp; lia | lia | lia |].
exists (b :: bs). split; [|cbn; lia]. cbn [rdn]. rewrite Hb.
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)); [rewrite Hbs; reflexivity|].
apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_unsigned 1) with 1. rewrite <- Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma store_ok_of_present : forall (m : word -> option byte) n a,
(forall i, 0 <= i < Z.of_nat n -> present m (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
store_ok ubs2segs m (Z_to_bv 64 a) n = true.
Proof.
intros m n a Hp Ha Hnw. destruct n as [|n']; [reflexivity|].
apply store_ok_of_all; [rewrite lit64_small by lia; lia|].
intros x Hx. rewrite lit64_small in Hx by lia.
destruct (Hp (bv_unsigned x - a) ltac:(lia)) as [b Hb]. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hb by lia.
rewrite Z_to_bv_bv_unsigned in Hb. unfold wview. rewrite Hb. discriminate.
Qed.
Lemma same_byte_views2 m m' x : m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
mbyte ubs2segs m' x = mbyte ubs2segs m x /\ (writable_at ubs2segs m x <-> writable_at ubs2segs m' x).
Proof. intros E. unfold mbyte, writable_at, wview. rewrite E. tauto. Qed.
Lemma present_same m m' x : m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) -> present m x -> present m' x.
Proof. intros E [b Hb]. exists b. rewrite E. exact Hb. Qed.
Lemma writable_same2 m m' x : m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) -> writable_at ubs2segs m x -> writable_at ubs2segs m' x.
Proof. intros E. apply (proj1 (proj2 (same_byte_views2 m m' x E))). Qed.
Lemma ubs2_img_range a : in_img ubs2_msyms a -> in_img1 a.
Proof.
intros [_ (s & Hs & Ha)].
assert (H : forallb (fun s : word * word => (0x10000 <=? bv_unsigned (fst s)) && (bv_unsigned (fst s) + bv_unsigned (snd s) <=? 0x54000))
(segments_reserved ubs2segs) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H s Hs). apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. unfold in_img1. lia.
Qed.
Lemma writable_off_img_present2 m a : 0 <= a < 2 ^ 64 -> ~ in_img1 a -> writable_at ubs2segs m a -> present m a.
Proof.
intros Ha Hni Hw. unfold writable_at, wview in Hw. unfold present.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity|]. exfalso.
destruct (find_segment ubs2segs (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Ef; [|apply Hw; reflexivity].
pose proof (find_segment_in _ _ _ _ Ef) as Hin. pose proof (find_segment_range _ _ _ _ Ef) as Hr.
rewrite lit64_small in Hr by lia.
assert (H : forallb (fun s => (0x10000 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x54000)) ubs2segs = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H seg Hin). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply Hni. unfold in_img1. lia.
Qed.
Lemma mbyte_off_img2 m a : 0 <= a < 2 ^ 64 -> ~ in_img1 a -> mbyte ubs2segs m a = m (Z_to_bv 64 a).
Proof.
intros Ha Hni. unfold mbyte. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [reflexivity|].
destruct (seg_rom ubs2segs (Z_to_bv 64 a)) as [b|] eqn:Er; [|reflexivity]. exfalso.
unfold seg_rom, memory_read in Er.
destruct (find_segment ubs2segs (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [seg|] eqn:Ef; [|discriminate].
pose proof (find_segment_in _ _ _ _ Ef) as Hin. pose proof (find_segment_range _ _ _ _ Ef) as Hr.
rewrite lit64_small in Hr by lia.
assert (H : forallb (fun s => (0x10000 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x54000)) ubs2segs = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H seg Hin). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply Hni. unfold in_img1. lia.
Qed.
Lemma ubs2_errno_img x : ERRNO2 <= x < ERRNO2 + 4 -> in_img ubs2_msyms x.
Proof.
intros Hx. eapply (covered_sound ubs2_msyms 0x22000 0x32000); [vm_compute; reflexivity|].
rewrite ERRNO2_val in Hx. unfold ubs2_tp in Hx. lia.
Qed.
Lemma ubs2_errno_not_footprint : forall L A mem md x,
MRc ubs2_msyms L A mem md -> ERRNO2 <= x < ERRNO2 + 4 -> ~ in_footprint L A x.
Proof.
intros L A mem md x M Hx (rg & Hrg & Hin).
destruct (In_footprint_inv A rg Hrg) as [-> | [(ar & Har & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hin.
- rewrite (mc_ctx _ _ _ _ _ M) in Hin. cbn in Hin. rewrite ERRNO2_val in Hx. unfold CTX_SIZE, ubs2_D_malloc_context, ubs2_tp in *. lia.
- destruct (inv_areas (mc_wf _ _ _ _ _ M)) as (_ & Hareas & _).
destruct (Hareas ar Har) as (r & o & rg & -> & _ & Ho & Hr & Hl & Hlen & _). cbn [loc_addr] in Hin.
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) r rg Hr Hl) as (_ & _ & _ & Himg).
apply (Himg x); [unfold PGSZ in *; lia|]. apply ubs2_errno_img. exact Hx.
- destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k r Hr Hl) as (_ & _ & _ & Himg).
apply (Himg x); [lia|]. apply ubs2_errno_img. exact Hx.
Qed.
Lemma ubs2_errno_not_owned : forall L A mem md x,
MRc ubs2_msyms L A mem md -> ERRNO2 <= x < ERRNO2 + 4 -> ~ owned ubs2_msyms L A x.
Proof.
intros L A mem md x M Hx [[Hfp Hnb] | Hs].
- exact (ubs2_errno_not_footprint L A mem md x M Hx Hfp).
- unfold static_owned in Hs. cbn in Hs. rewrite ERRNO2_val in Hx. unfold ubs2_tp, ubs2_D_malloc_lock, ubs2_D_libc, ubs2_D_got_stack_chk_guard,
ubs2_D_stack_chk_guard, ubs2_D_debruijn32, ubs2_D_size_classes, ubs2_D_small_cnt_tab, ubs2_D_med_cnt_tab in *. lia.
Qed.
Lemma init_done_of_block : forall A b, WF A -> In b (user_blocks A) -> st_init_done A = true.
Proof.
intros A b HW Hin. destruct (st_init_done A) eqn:E; [reflexivity|]. exfalso.
destruct HW as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinit) & _).
destruct (Hinit E) as (Hm & _). unfold user_blocks, used_metas in Hin. rewrite Hm in Hin. cbn in Hin. exact Hin.
Qed.
Lemma fetch_realloc_ret : fetch_word ubs2segs (Z_to_bv 64 REALLOC_RET) = Some (0x00008067%bv : bv 32).
Proof. rewrite <- (Z_to_bv_bv_unsigned 32 (0x00008067%bv : bv 32)). apply ubs2tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_ret : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma SR_realloc_ret E ss ms md Q :
st_ok ubs2segs E ss ms -> ss_resv ss = None -> ss_pc ss = REALLOC_RET ->
sr_get (ss_regs ss) 1 = SOff 1 0 -> YK0s.ret_ok (ew E 1) ->
m_halted md = None -> m_vm_lazy md = [] ->
Q (mkCfg (mkst (ms_regs ms) (ew E 1) (ms_mem ms) (seg_rom ubs2segs)) md) ->
SR ubs2segs (mkCfg ms md) Q.
Proof.
intros HS Hrv Hpc Hra Hret Hh Hlz HQ.
pose proof (st_ok_reg ubs2segs E ss ms 1 HS) as R1. rewrite Hra in R1. cbn [sv_denot] in R1.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R1.
rewrite (st_ok_mkst ubs2segs E ss ms HS Hrv). rewrite Hpc.
eapply SR_step; [exact Hh | exact Hlz | reflexivity | |].
- eapply step_jalr_x0; [apply fetch_realloc_ret | reflexivity | apply decode_ret | exact R1].
- cbn [ms_regs ms_mem mkst]. change (bv_signed (0%bv : bv 12)) with 0. unfold YK0s.ret_ok in Hret. rewrite Hret.
apply SR_ret. exact HQ.
Qed.
Lemma Z_to_bv5_nat_to_reg r : 0 <= r < 32 -> Z_to_bv 5 r = nat_to_reg (Z.to_nat r).
Proof.
intros Hr. rewrite <- (nat_to_reg_ridx (Z_to_bv 5 r)). f_equal. f_equal.
rewrite Z_to_bv_unsigned. rewrite bv_wrap_small; [reflexivity|]. change (bv_modulus 5) with 32. lia.
Qed.
Lemma callee_saved_cases r : callee_saved r ->
0 <= r < 32 /\ In (Z.to_nat r) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Proof.
intros Hr. unfold callee_saved in Hr. split; [lia|].
destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [cbn; tauto | cbn; tauto | cbn; tauto | cbn; tauto | cbn; tauto |].
assert (H : (18 <= Z.to_nat r <= 27)%nat) by lia. revert H. generalize (Z.to_nat r) as m. intros m H.
do 18 (destruct m as [|m]; [lia|]).
do 10 (destruct m as [|m]; [cbn; tauto|]). lia.
Qed.
Lemma skel_S2 : forall r, skeleton (ss_mem (S2 r)) = skeleton (entry_mem r).
Proof. intros r. rewrite S2_mem. destruct r; reflexivity. Qed.

Lemma mem_S2no : forall r, ss_mem (S2no r) = ss_mem (S2 r).
Proof.
intros r. rewrite S2_mem. destruct r; vm_compute; reflexivity. Qed.
Lemma wr_entry : forall E r x, in_wrange E (entry_mem r) x ->
(base_val E (Some aSP) - 8256 <= x < base_val E (Some aSP)) \/ (base_val E (Some aTP) - 164 <= x < base_val E (Some aTP) - 160).
Proof.
intros E r x (rg & Hin & Hx). unfold entry_mem in Hin. apply in_app_iff in Hin as [Hin|Hin].
- destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
cbn [r_base r_wlo r_whi reg_hdr0 reg_grp reg_meta0 reg_area reg_ctx reg_nl reg_stkR reg_got reg_guard reg_errnoR] in Hx; lia.
- assert (H0 : r_wlo rg = 0 /\ r_whi rg = 0).
{ destruct r; cbn [r_mem] in Hin;
repeat (destruct Hin as [<-|Hin]; [split; reflexivity|]); destruct Hin. }
lia.
Qed.
Lemma wr_after : forall E x, in_wrange E after_memR x -> base_val E (Some aSP) - 8256 <= x < base_val E (Some aSP).
Proof. intros E x (rg & [<-|[]] & Hx). cbn [r_base r_wlo r_whi] in Hx. lia. Qed.
Lemma S4_view2 : forall r, view [19; 20; 21; 22]%nat (S4 r) = [SOff aB16 0; SLit 4095; SOff aP 0; SOff aN 0].
Proof. intros r. destruct r; vm_compute; reflexivity. Qed.
Lemma S8_view2 : view [19; 20; 21; 22]%nat S8 = [SOff aB16 0; SLit 4095; SOff aP 0; SOff aN 0].
Proof. vm_compute. reflexivity. Qed.
Lemma S10_view2 : view [19; 20; 21; 22]%nat S10 = [SOff aB16 0; SLit 4095; SOff aP 0; SOff aN 0].
Proof. vm_compute. reflexivity. Qed.
Lemma app_mid_cases {T} (x y : T) : forall l1 l2 k1 k2,
l1 ++ x :: l2 = k1 ++ y :: k2 -> x <> y ->
(exists u, k1 = l1 ++ x :: u /\ l2 = u ++ y :: k2) \/ (exists u, l1 = k1 ++ y :: u /\ k2 = u ++ x :: l2).
Proof.
induction l1 as [|a l1 IH]; intros l2 k1 k2 H Hne.
- destruct k1 as [|b k1]; cbn in H.
+ injection H as -> ->. exfalso. exact (Hne eq_refl).
+ injection H as -> ->. left. exists k1. auto.
- destruct k1 as [|b k1]; cbn in H.
+ injection H as -> <-. right. exists l1. auto.
+ injection H as -> H. destruct (IH l2 k1 k2 H Hne) as [(u & -> & ->) | (u & -> & ->)].
* left. exists u. auto.
* right. exists u. auto.
Qed.
Lemma with_vmmaps_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md. reflexivity. Qed.
End c.
