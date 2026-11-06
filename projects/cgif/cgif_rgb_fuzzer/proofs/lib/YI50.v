(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YO3m YI00 YI02 YI01 YI03
YI1e YI1i YI59 YI56 YI0x YL0e YI08 YI0c YI3h YI3d
YI39 YI2p YI26 YI57 YI58 YI4y YI55 YI4z YI51 YI53
YO0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition RL_HDR0 : Z := Eval vm_compute in (src2_A_LLVMFuzzerTestOneInput + 0x38).
Definition rlh_cnt (k : nat) : nat := nth k [0; 2; 4; 8; 12; 14]%nat 14%nat.
Definition rlh_lo (k : nat) : Z := nth k [0; 2; 4; 8; 12; 14] 14.
Definition rlh_hi (k : nat) : Z := nth k [1; 3; 7; 11; 13; CEIL_MAX] CEIL_MAX.
Definition rlh_breg (k : nat) : list YQ0b.region :=
match k with O => [] | _ => [YQ0b.mkRegion (Some 10%nat) 0 (Z.of_nat (rlh_cnt k)) 0 0 (byte_chunks 32 (rlh_cnt k))] end.
Definition rlh_bfacts (k : nat) : list (nat * afact) := map (fun i => ((32 + i)%nat, mkAF 0 255 0)) (seq 0 (rlh_cnt k)).
Definition rlh_pfact (k : nat) : list (nat * afact) := match k with O => [] | _ => [(10%nat, mkAF 4096 CEIL_MAX 0)] end.
Definition ss_rlhdr (k : nat) : sstate :=
mkSS RLLVM sr_atoms
([ YQ0b.mkRegion (Some 2%nat) (-128) (-72) (-128) (-72) [] ;
YQ0b.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [] ] ++ rlh_breg k)
None
(mkFacts ([ (2%nat, mkAF (CEIL_MIN + LIB_STACK_RGB) (2^63) 4); (11%nat, mkAF (rlh_lo k) (rlh_hi k) 0) ] ++ rlh_pfact k ++ rlh_bfacts k) [] []).
Lemma byte_at_range_of : forall {E n m a}, ew E n = Z_to_bv 64 (byte_at m a) -> 0 <= byte_at m a < 256.
Proof. intros. apply byte_at_range. Qed.
Lemma U_or_shl8 : forall E n1 n0 b1 b0,
ew E n1 = Z_to_bv 64 b1 -> ew E n0 = Z_to_bv 64 b0 -> 0 <= b1 < 256 -> 0 <= b0 < 256 ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SOff n0 0)) = b0 + 256 * b1.
Proof.
intros E n1 n0 b1 b0 H1 H0 R1 R0. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
change (Z.land (zcanon 8) 63) with 8. rewrite (U_atom E n1 b1 H1), (U_atom E n0 b0 H0) by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (b1 * 256)) by (unfold M64; lia). rewrite lor_shl8 by lia. apply zcanon_id. unfold M64; lia.
Qed.
Lemma denot_or_shl8 : forall E n1 n0 b1 b0,
ew E n1 = Z_to_bv 64 b1 -> ew E n0 = Z_to_bv 64 b0 -> 0 <= b1 < 256 -> 0 <= b0 < 256 ->
sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SOff n0 0)) = Z_to_bv 64 (b0 + 256 * b1).
Proof. intros. rewrite denot_lit_U. f_equal. apply (U_or_shl8 E n1 n0 b1 b0); assumption. Qed.
Lemma st_chunk_low : forall E ss ms i rg p off (n : N) e a (k : nat) (m : Z),
st_ok src2segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CVal n e)) (r_chunks rg) -> bv_unsigned (ew E p) = a -> Z.of_N n <= 8 ->
k = N.to_nat n -> m = 2 ^ (8 * Z.of_N n) ->
val_mem src2segs (ms_mem ms) (a + off) k (U E e mod m).
Proof.
intros E ss ms i rg p off n e a k m HS Hi Hb Hin Hp Hn -> ->.
pose proof (st_region_chunks src2segs E ss ms i rg p a HS Hi Hb Hp) as Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
unfold U. exact (val_mem_low_of_chunk src2segs E (ms_mem ms) a off n e Hc Hn).
Qed.
Lemma U_range : forall E e, 0 <= U E e < 2 ^ 64.
Proof. intros E e. unfold U. pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
End c.
Ltac rcfg_zero HS HU2 off len :=
lazymatch goal with |- val_mem _ _ (?b - 72 + ?k) ?n ?v =>
unify v 0;
let o := eval vm_compute in (-72 + k) in
replace (b - 72 + k) with (b + o) by lia;
eapply (st_chunk_zero_val src2segs _ _ _ 0%nat _ 2%nat off len b o n HS);
[ reflexivity | reflexivity | cbv; solve [auto 80] | ew_havocA; exact HU2 | lia | lia ]
end.
Ltac rcfg_val2 HS HU2 n1 n0 H1 H0 :=
lazymatch goal with |- val_mem _ _ (?b - 72 + ?k) 2%nat ?v =>
let o := eval vm_compute in (-72 + k) in
replace (b - 72 + k) with (b + o) by lia;
eapply (st_chunk_val src2segs _ _ _ 0%nat _ 2%nat o 2%N _ b v HS);
[ reflexivity | reflexivity | cbv; solve [auto 80] | ew_havocA; exact HU2
| apply (denot_or_shl8 _ n1 n0); [ew_havocA; exact H1 | ew_havocA; exact H0 | apply byte_at_range | apply byte_at_range]
| pose proof (byte_at_range_of H1); pose proof (byte_at_range_of H0); cbn; lia | cbn; lia ]
end.
Ltac rcfg_low HS HU2 n k m :=
lazymatch goal with |- val_mem _ _ (?b - 72 + ?kk) _ ?v =>
let o := eval vm_compute in (-72 + kk) in
replace (b - 72 + kk) with (b + o) by lia;
eapply (st_chunk_low _ _ _ 0%nat _ 2%nat o n _ b k m HS);
[ reflexivity | reflexivity | cbv; solve [auto 80] | ew_havocA; exact HU2 | cbn; lia | reflexivity | reflexivity ]
end.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Hypothesis NEWG : rgb_newgif_spec API.
Hypothesis CLOSE : forall fx', rgb_close_spec (fx:=fx') API.
Hypothesis ADDF : forall fx', rgb_addframe_spec (fx:=fx') API.
Lemma rlh_case_5 : forall L A (regs : bvmap 5 word) mem md (p n : Z),
14 <= n -> In (p, n) (blocks L A) ->
frm_zero fp_csr ->
fn_pre src2_msyms MR LIB_STACK_RGB L A regs mem md -> st_init_done A = true ->
src2_rgb_rodata_ok mem ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs)) md) (rllvm_post API regs L A mem md).
Proof.
intros L A regs mem md p n HC Hpn HFZ HPRE Hid HRO G10 G11.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HLSv : LIB_STACK_RGB = 61440) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
destruct (blocks_range _ _ LAWS L A mem md p n HH Hpn) as [Hp0 Hp1].
assert (Hpres : forall i, 0 <= i < n -> present mem (p + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS L A mem md p n i HH Hpn Hi)). }
set (bvals := map (fun i => byte_at mem (p + Z.of_nat i)) (seq 0 14)).
set (E := Ereg regs (map (Z_to_bv 64) bvals ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error bvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HB : forall j, (j < 14)%nat -> ew E (32 + j) = Z_to_bv 64 (byte_at mem (p + Z.of_nat j))).
{ intros j Hj. apply HX. subst bvals. rewrite nth_error_map, nth_error_seq. rewrite (proj2 (Nat.ltb_lt j 14) Hj). reflexivity. }
assert (HBr : forall j, (j < 14)%nat -> 0 <= bv_unsigned (ew E (32 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range mem (p + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = p) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = n) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : st_ok src2segs E (ss_rlhdr 5) (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs))).
{ unfold ss_rlhdr. replace src2_A_LLVMFuzzerTestOneInput with RLLVM by reflexivity. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- cbn [rlh_breg rlh_cnt nth app]. constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hstw. lia.
+ apply (region_ok_stack src2segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
+ apply (region_ok_bytes _ mem 10 p 14 32); [exact HU10 | lia | lia |].
intros j Hj. split; [apply HB; exact Hj|]. apply Hpres. lia.
- cbn [rlh_breg rlh_cnt nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, ?HU10. repeat split; lia.
- cbn [f_atoms rlh_bfacts rlh_pfact rlh_cnt rlh_lo rlh_hi nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2. pose proof (HBr 3%nat ltac:(lia)) as B3. pose proof (HBr 4%nat ltac:(lia)) as B4. pose proof (HBr 5%nat ltac:(lia)) as B5. pose proof (HBr 6%nat ltac:(lia)) as B6. pose proof (HBr 7%nat ltac:(lia)) as B7. pose proof (HBr 8%nat ltac:(lia)) as B8. pose proof (HBr 9%nat ltac:(lia)) as B9. pose proof (HBr 10%nat ltac:(lia)) as B10. pose proof (HBr 11%nat ltac:(lia)) as B11. pose proof (HBr 12%nat ltac:(lia)) as B12. pose proof (HBr 13%nat ltac:(lia)) as B13.
cbn [Nat.add] in B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13.
repeat split; try lia; assumption. }
pose proof (journal_init src2_msyms MR LIB_STACK_RGB [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs))) in HJ. fold sp0 in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset src2_msyms MR LAWS IMG src2_A_memset src2_memset_spec E _ _ LIB_STACK_RGB sp0 [] L A mem md L A _ (sp0 - 72) 0 40);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 72) with (sp0 + -72) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 46%nat regs2 mem2 MEMSET_CLOB RL_HDR0 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU10; lia | cbn [r_base r_hi base_val]; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YQ0b.mkRegion (Some 2%nat) (-72) (-32) (-72) (-32) [mkChunk (-72) (CZero 40)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows src2segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows src2segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -72 + i) with (sp0 - 72 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, ?HU10. repeat split; lia. }
jrun_to LAWS src2tbl_ok HS HJ2 RL_MUL.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (HB0 : ew E 32 = Z_to_bv 64 (byte_at mem (p + 0))) by (etransitivity; [apply (HB 0%nat); lia | f_equal; f_equal; lia]).
assert (HB1 : ew E 33 = Z_to_bv 64 (byte_at mem (p + 1))) by (etransitivity; [apply (HB 1%nat); lia | f_equal; f_equal; lia]).
assert (HB2 : ew E 34 = Z_to_bv 64 (byte_at mem (p + 2))) by (etransitivity; [apply (HB 2%nat); lia | f_equal; f_equal; lia]).
assert (HB3 : ew E 35 = Z_to_bv 64 (byte_at mem (p + 3))) by (etransitivity; [apply (HB 3%nat); lia | f_equal; f_equal; lia]).
assert (HB12 : ew E 44 = Z_to_bv 64 (byte_at mem (p + 12))) by (etransitivity; [apply (HB 12%nat); lia | f_equal; f_equal; lia]).
assert (HB13 : ew E 45 = Z_to_bv 64 (byte_at mem (p + 13))) by (etransitivity; [apply (HB 13%nat); lia | f_equal; f_equal; lia]).
pose proof (byte_at_range mem (p + 0)) as R0. pose proof (byte_at_range mem (p + 1)) as R1.
pose proof (byte_at_range mem (p + 2)) as R2. pose proof (byte_at_range mem (p + 3)) as R3.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch type of HS with st_ok _ ?Ef _ _ =>
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rl_main API IMG NEWG CLOSE ADDF L A mem md regs rg L A mm md p n
(byte_at mem (p + 0) + 256 * byte_at mem (p + 1)) (byte_at mem (p + 2) + 256 * byte_at mem (p + 3))
(U Ef (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SExt true 8 (SOff 39 0)) (SLit 24)) (SAlu ALU_SLL (SOff 38 0) (SLit 16))) (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 8)) (SOff 36 0))) mod 2 ^ 32)
(U Ef (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SExt true 8 (SOff 43 0)) (SLit 24)) (SAlu ALU_SLL (SOff 42 0) (SLit 16))) (SAlu ALU_OR (SAlu ALU_SLL (SOff 41 0) (SLit 8)) (SOff 40 0))) mod 2 ^ 32)
(U Ef (SAlu ALU_OR (SAlu ALU_SLL (SOff 45 0) (SLit 8)) (SOff 44 0)) mod 2 ^ 16))
end end.
+ exact HFZ. + exact HJ2. + exact Hid. + exact Hra. + exact Htp. + exact Hal16. + exact HRO.
+ intros b Hb. exact Hb. + exact Hpn. + exact HC. + lia. + lia.
+ fold sp0. unfold rsaved_ok.
repeat match goal with |- _ /\ _ => split end;
[ frame_wordI HS 2%nat HU2 HE 1%nat (1%bv:reg) | frame_wordI HS 2%nat HU2 HE 8%nat (8%bv:reg)
| frame_wordI HS 2%nat HU2 HE 9%nat (9%bv:reg) | frame_wordI HS 2%nat HU2 HE 18%nat (18%bv:reg) ].
+ fold sp0. replace (sp0 - 120) with (sp0 + -120) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-120) (SOff 10 0) sp0 p HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HU10; reflexivity | lia].
+ fold sp0. replace (sp0 - 112) with (sp0 + -112) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-112) (SOff 11 0) sp0 n HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HU11; reflexivity | lia].
+ fold sp0. replace (sp0 - 104) with (sp0 + -104) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-104) (SLit 14) sp0 14 HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | reflexivity | lia].
+ fold sp0. cbn [obj_at LAY_RgbConfig]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
try change (2 ^ (8 * 8)) with 18446744073709551616. try change (2 ^ (8 * 4)) with 4294967296. try change (2 ^ (8 * 2)) with 65536.
try change (N.to_nat 8) with 8%nat. try change (N.to_nat 4) with 4%nat. try change (N.to_nat 2) with 2%nat.
repeat match goal with |- _ /\ _ => split end;
first [ rcfg_zero HS HU2 (-72) 24
| rcfg_val2 HS HU2 33%nat 32%nat HB1 HB0
| rcfg_val2 HS HU2 35%nat 34%nat HB3 HB2
| rcfg_low HS HU2 4%N 4%nat (2 ^ 32)
| rcfg_low HS HU2 2%N 2%nat (2 ^ 16)
| exact I
| lia
| match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)); lia end
| match goal with |- ?G => idtac "CFGLEFT"; idtac G end ].
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(rewrite HU10; reflexivity).
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src2segs Ec ssc msc 10%bv HS) as T; eval_sr_get_in T;
rewrite (denot_or_shl8 _ 33 32 (byte_at mem (p + 1)) (byte_at mem (p + 0))) in T;
[ exact T | ew_havocA; exact HB1 | ew_havocA; exact HB0 | apply byte_at_range | apply byte_at_range ] end.
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src2segs Ec ssc msc 13%bv HS) as T; eval_sr_get_in T;
rewrite (denot_or_shl8 _ 35 34 (byte_at mem (p + 3)) (byte_at mem (p + 2))) in T;
[ exact T | ew_havocA; exact HB3 | ew_havocA; exact HB2 | apply byte_at_range | apply byte_at_range ] end.
+ runtouched_tac HS HE ltac:(idtac) ltac:(idtac) ltac:(idtac) ltac:(idtac) ltac:(idtac) ltac:(idtac) ltac:(idtac) ltac:(idtac) ltac:(idtac) ltac:(idtac) ltac:(idtac) ||
(unfold runtouched_ok; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)).
Qed.
Lemma rlh_case_4 : forall L A (regs : bvmap 5 word) mem md (p n : Z),
12 <= n <= 13 -> In (p, n) (blocks L A) ->
frm_zero fp_csr ->
fn_pre src2_msyms MR LIB_STACK_RGB L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 <= p < 2 ^ 64 ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs)) md) (rllvm_post API regs L A mem md).
Proof.
intros L A regs mem md p n HC Hpn HFZ HPRE Hid G10 G11 Hp64.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HLSv : LIB_STACK_RGB = 61440) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
destruct (blocks_range _ _ LAWS L A mem md p n HH Hpn) as [Hp0 Hp1].
assert (Hpres : forall i, 0 <= i < n -> present mem (p + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS L A mem md p n i HH Hpn Hi)). }
set (bvals := map (fun i => byte_at mem (p + Z.of_nat i)) (seq 0 12)).
set (E := Ereg regs (map (Z_to_bv 64) bvals ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error bvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HB : forall j, (j < 12)%nat -> ew E (32 + j) = Z_to_bv 64 (byte_at mem (p + Z.of_nat j))).
{ intros j Hj. apply HX. subst bvals. rewrite nth_error_map, nth_error_seq. rewrite (proj2 (Nat.ltb_lt j 12) Hj). reflexivity. }
assert (HBr : forall j, (j < 12)%nat -> 0 <= bv_unsigned (ew E (32 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range mem (p + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HU10 : bv_unsigned (ew E 10) = p) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU11 : bv_unsigned (ew E 11) = n) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : st_ok src2segs E (ss_rlhdr 4) (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs))).
{ unfold ss_rlhdr. replace src2_A_LLVMFuzzerTestOneInput with RLLVM by reflexivity. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- cbn [rlh_breg rlh_cnt nth app]. constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hstw. lia.
+ apply (region_ok_stack src2segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
+ apply (region_ok_bytes _ mem 10 p 12 32); [exact HU10 | lia | lia |].
intros j Hj. split; [apply HB; exact Hj|]. apply Hpres. lia.
- cbn [rlh_breg rlh_cnt nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, ?HU10. repeat split; lia.
- cbn [f_atoms rlh_bfacts rlh_pfact rlh_cnt rlh_lo rlh_hi nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2. pose proof (HBr 3%nat ltac:(lia)) as B3. pose proof (HBr 4%nat ltac:(lia)) as B4. pose proof (HBr 5%nat ltac:(lia)) as B5. pose proof (HBr 6%nat ltac:(lia)) as B6. pose proof (HBr 7%nat ltac:(lia)) as B7. pose proof (HBr 8%nat ltac:(lia)) as B8. pose proof (HBr 9%nat ltac:(lia)) as B9. pose proof (HBr 10%nat ltac:(lia)) as B10. pose proof (HBr 11%nat ltac:(lia)) as B11.
cbn [Nat.add] in B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11.
repeat split; try lia; assumption. }
pose proof (journal_init src2_msyms MR LIB_STACK_RGB [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs))) in HJ. fold sp0 in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset src2_msyms MR LAWS IMG src2_A_memset src2_memset_spec E _ _ LIB_STACK_RGB sp0 [] L A mem md L A _ (sp0 - 72) 0 40);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 72) with (sp0 + -72) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 46%nat regs2 mem2 MEMSET_CLOB RL_HDR0 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU10; lia | cbn [r_base r_hi base_val]; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YQ0b.mkRegion (Some 2%nat) (-72) (-32) (-72) (-32) [mkChunk (-72) (CZero 40)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows src2segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows src2segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -72 + i) with (sp0 - 72 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, ?HU10. repeat split; lia. }
jrun_to LAWS src2tbl_ok HS HJ2 RL_RET0.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ => eapply (rl_ret0 API IMG L A mem md regs rg L A mm md) end.
+ exact HFZ. + exact HJ2. + exact Hid. + exact Hra. + exact Hal16. + intros b Hb; exact Hb.
+ fold sp0. unfold rsaved_ok.
repeat match goal with |- _ /\ _ => split end;
[ frame_wordI HS 2%nat HU2 HE 1%nat (1%bv:reg) | frame_wordI HS 2%nat HU2 HE 8%nat (8%bv:reg)
| frame_wordI HS 2%nat HU2 HE 9%nat (9%bv:reg) | frame_wordI HS 2%nat HU2 HE 18%nat (18%bv:reg) ].
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ unfold runtouched_ok; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
Qed.
Lemma rlh_case_3 : forall L A (regs : bvmap 5 word) mem md (p n : Z),
8 <= n <= 11 -> In (p, n) (blocks L A) ->
frm_zero fp_csr ->
fn_pre src2_msyms MR LIB_STACK_RGB L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 <= p < 2 ^ 64 ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs)) md) (rllvm_post API regs L A mem md).
Proof.
intros L A regs mem md p n HC Hpn HFZ HPRE Hid G10 G11 Hp64.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HLSv : LIB_STACK_RGB = 61440) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
destruct (blocks_range _ _ LAWS L A mem md p n HH Hpn) as [Hp0 Hp1].
assert (Hpres : forall i, 0 <= i < n -> present mem (p + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS L A mem md p n i HH Hpn Hi)). }
set (bvals := map (fun i => byte_at mem (p + Z.of_nat i)) (seq 0 8)).
set (E := Ereg regs (map (Z_to_bv 64) bvals ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error bvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HB : forall j, (j < 8)%nat -> ew E (32 + j) = Z_to_bv 64 (byte_at mem (p + Z.of_nat j))).
{ intros j Hj. apply HX. subst bvals. rewrite nth_error_map, nth_error_seq. rewrite (proj2 (Nat.ltb_lt j 8) Hj). reflexivity. }
assert (HBr : forall j, (j < 8)%nat -> 0 <= bv_unsigned (ew E (32 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range mem (p + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HU10 : bv_unsigned (ew E 10) = p) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU11 : bv_unsigned (ew E 11) = n) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : st_ok src2segs E (ss_rlhdr 3) (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs))).
{ unfold ss_rlhdr. replace src2_A_LLVMFuzzerTestOneInput with RLLVM by reflexivity. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- cbn [rlh_breg rlh_cnt nth app]. constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hstw. lia.
+ apply (region_ok_stack src2segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
+ apply (region_ok_bytes _ mem 10 p 8 32); [exact HU10 | lia | lia |].
intros j Hj. split; [apply HB; exact Hj|]. apply Hpres. lia.
- cbn [rlh_breg rlh_cnt nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, ?HU10. repeat split; lia.
- cbn [f_atoms rlh_bfacts rlh_pfact rlh_cnt rlh_lo rlh_hi nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2. pose proof (HBr 3%nat ltac:(lia)) as B3. pose proof (HBr 4%nat ltac:(lia)) as B4. pose proof (HBr 5%nat ltac:(lia)) as B5. pose proof (HBr 6%nat ltac:(lia)) as B6. pose proof (HBr 7%nat ltac:(lia)) as B7.
cbn [Nat.add] in B0, B1, B2, B3, B4, B5, B6, B7.
repeat split; try lia; assumption. }
pose proof (journal_init src2_msyms MR LIB_STACK_RGB [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs))) in HJ. fold sp0 in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset src2_msyms MR LAWS IMG src2_A_memset src2_memset_spec E _ _ LIB_STACK_RGB sp0 [] L A mem md L A _ (sp0 - 72) 0 40);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 72) with (sp0 + -72) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 46%nat regs2 mem2 MEMSET_CLOB RL_HDR0 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU10; lia | cbn [r_base r_hi base_val]; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YQ0b.mkRegion (Some 2%nat) (-72) (-32) (-72) (-32) [mkChunk (-72) (CZero 40)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows src2segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows src2segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -72 + i) with (sp0 - 72 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, ?HU10. repeat split; lia. }
jrun_to LAWS src2tbl_ok HS HJ2 RL_RET0.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ => eapply (rl_ret0 API IMG L A mem md regs rg L A mm md) end.
+ exact HFZ. + exact HJ2. + exact Hid. + exact Hra. + exact Hal16. + intros b Hb; exact Hb.
+ fold sp0. unfold rsaved_ok.
repeat match goal with |- _ /\ _ => split end;
[ frame_wordI HS 2%nat HU2 HE 1%nat (1%bv:reg) | frame_wordI HS 2%nat HU2 HE 8%nat (8%bv:reg)
| frame_wordI HS 2%nat HU2 HE 9%nat (9%bv:reg) | frame_wordI HS 2%nat HU2 HE 18%nat (18%bv:reg) ].
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ unfold runtouched_ok; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
Qed.
Lemma rlh_case_2 : forall L A (regs : bvmap 5 word) mem md (p n : Z),
4 <= n <= 7 -> In (p, n) (blocks L A) ->
frm_zero fp_csr ->
fn_pre src2_msyms MR LIB_STACK_RGB L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 <= p < 2 ^ 64 ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs)) md) (rllvm_post API regs L A mem md).
Proof.
intros L A regs mem md p n HC Hpn HFZ HPRE Hid G10 G11 Hp64.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HLSv : LIB_STACK_RGB = 61440) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
destruct (blocks_range _ _ LAWS L A mem md p n HH Hpn) as [Hp0 Hp1].
assert (Hpres : forall i, 0 <= i < n -> present mem (p + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS L A mem md p n i HH Hpn Hi)). }
set (bvals := map (fun i => byte_at mem (p + Z.of_nat i)) (seq 0 4)).
set (E := Ereg regs (map (Z_to_bv 64) bvals ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error bvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HB : forall j, (j < 4)%nat -> ew E (32 + j) = Z_to_bv 64 (byte_at mem (p + Z.of_nat j))).
{ intros j Hj. apply HX. subst bvals. rewrite nth_error_map, nth_error_seq. rewrite (proj2 (Nat.ltb_lt j 4) Hj). reflexivity. }
assert (HBr : forall j, (j < 4)%nat -> 0 <= bv_unsigned (ew E (32 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range mem (p + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HU10 : bv_unsigned (ew E 10) = p) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU11 : bv_unsigned (ew E 11) = n) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : st_ok src2segs E (ss_rlhdr 2) (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs))).
{ unfold ss_rlhdr. replace src2_A_LLVMFuzzerTestOneInput with RLLVM by reflexivity. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- cbn [rlh_breg rlh_cnt nth app]. constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hstw. lia.
+ apply (region_ok_stack src2segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
+ apply (region_ok_bytes _ mem 10 p 4 32); [exact HU10 | lia | lia |].
intros j Hj. split; [apply HB; exact Hj|]. apply Hpres. lia.
- cbn [rlh_breg rlh_cnt nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, ?HU10. repeat split; lia.
- cbn [f_atoms rlh_bfacts rlh_pfact rlh_cnt rlh_lo rlh_hi nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2. pose proof (HBr 3%nat ltac:(lia)) as B3.
cbn [Nat.add] in B0, B1, B2, B3.
repeat split; try lia; assumption. }
pose proof (journal_init src2_msyms MR LIB_STACK_RGB [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs))) in HJ. fold sp0 in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset src2_msyms MR LAWS IMG src2_A_memset src2_memset_spec E _ _ LIB_STACK_RGB sp0 [] L A mem md L A _ (sp0 - 72) 0 40);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 72) with (sp0 + -72) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 46%nat regs2 mem2 MEMSET_CLOB RL_HDR0 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU10; lia | cbn [r_base r_hi base_val]; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YQ0b.mkRegion (Some 2%nat) (-72) (-32) (-72) (-32) [mkChunk (-72) (CZero 40)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows src2segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows src2segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -72 + i) with (sp0 - 72 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, ?HU10. repeat split; lia. }
jrun_to LAWS src2tbl_ok HS HJ2 RL_RET0.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ => eapply (rl_ret0 API IMG L A mem md regs rg L A mm md) end.
+ exact HFZ. + exact HJ2. + exact Hid. + exact Hra. + exact Hal16. + intros b Hb; exact Hb.
+ fold sp0. unfold rsaved_ok.
repeat match goal with |- _ /\ _ => split end;
[ frame_wordI HS 2%nat HU2 HE 1%nat (1%bv:reg) | frame_wordI HS 2%nat HU2 HE 8%nat (8%bv:reg)
| frame_wordI HS 2%nat HU2 HE 9%nat (9%bv:reg) | frame_wordI HS 2%nat HU2 HE 18%nat (18%bv:reg) ].
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ unfold runtouched_ok; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
Qed.
Lemma rlh_case_1 : forall L A (regs : bvmap 5 word) mem md (p n : Z),
2 <= n <= 3 -> In (p, n) (blocks L A) ->
frm_zero fp_csr ->
fn_pre src2_msyms MR LIB_STACK_RGB L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 <= p < 2 ^ 64 ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs)) md) (rllvm_post API regs L A mem md).
Proof.
intros L A regs mem md p n HC Hpn HFZ HPRE Hid G10 G11 Hp64.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HLSv : LIB_STACK_RGB = 61440) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
destruct (blocks_range _ _ LAWS L A mem md p n HH Hpn) as [Hp0 Hp1].
assert (Hpres : forall i, 0 <= i < n -> present mem (p + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS L A mem md p n i HH Hpn Hi)). }
set (bvals := map (fun i => byte_at mem (p + Z.of_nat i)) (seq 0 2)).
set (E := Ereg regs (map (Z_to_bv 64) bvals ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error bvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HB : forall j, (j < 2)%nat -> ew E (32 + j) = Z_to_bv 64 (byte_at mem (p + Z.of_nat j))).
{ intros j Hj. apply HX. subst bvals. rewrite nth_error_map, nth_error_seq. rewrite (proj2 (Nat.ltb_lt j 2) Hj). reflexivity. }
assert (HBr : forall j, (j < 2)%nat -> 0 <= bv_unsigned (ew E (32 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range mem (p + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HU10 : bv_unsigned (ew E 10) = p) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU11 : bv_unsigned (ew E 11) = n) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : st_ok src2segs E (ss_rlhdr 1) (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs))).
{ unfold ss_rlhdr. replace src2_A_LLVMFuzzerTestOneInput with RLLVM by reflexivity. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- cbn [rlh_breg rlh_cnt nth app]. constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hstw. lia.
+ apply (region_ok_stack src2segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
+ apply (region_ok_bytes _ mem 10 p 2 32); [exact HU10 | lia | lia |].
intros j Hj. split; [apply HB; exact Hj|]. apply Hpres. lia.
- cbn [rlh_breg rlh_cnt nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, ?HU10. repeat split; lia.
- cbn [f_atoms rlh_bfacts rlh_pfact rlh_cnt rlh_lo rlh_hi nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1.
cbn [Nat.add] in B0, B1.
repeat split; try lia; assumption. }
pose proof (journal_init src2_msyms MR LIB_STACK_RGB [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs))) in HJ. fold sp0 in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset src2_msyms MR LAWS IMG src2_A_memset src2_memset_spec E _ _ LIB_STACK_RGB sp0 [] L A mem md L A _ (sp0 - 72) 0 40);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 72) with (sp0 + -72) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 46%nat regs2 mem2 MEMSET_CLOB RL_HDR0 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU10; lia | cbn [r_base r_hi base_val]; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YQ0b.mkRegion (Some 2%nat) (-72) (-32) (-72) (-32) [mkChunk (-72) (CZero 40)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows src2segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows src2segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -72 + i) with (sp0 - 72 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, ?HU10. repeat split; lia. }
jrun_to LAWS src2tbl_ok HS HJ2 RL_RET0.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ => eapply (rl_ret0 API IMG L A mem md regs rg L A mm md) end.
+ exact HFZ. + exact HJ2. + exact Hid. + exact Hra. + exact Hal16. + intros b Hb; exact Hb.
+ fold sp0. unfold rsaved_ok.
repeat match goal with |- _ /\ _ => split end;
[ frame_wordI HS 2%nat HU2 HE 1%nat (1%bv:reg) | frame_wordI HS 2%nat HU2 HE 8%nat (8%bv:reg)
| frame_wordI HS 2%nat HU2 HE 9%nat (9%bv:reg) | frame_wordI HS 2%nat HU2 HE 18%nat (18%bv:reg) ].
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ unfold runtouched_ok; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
Qed.
Lemma rlh_case_0 : forall L A (regs : bvmap 5 word) mem md (p n : Z),
0 <= n <= 1 ->
frm_zero fp_csr ->
fn_pre src2_msyms MR LIB_STACK_RGB L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 <= p < 2 ^ 64 ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs)) md) (rllvm_post API regs L A mem md).
Proof.
intros L A regs mem md p n HC HFZ HPRE Hid G10 G11 Hp64.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HLSv : LIB_STACK_RGB = 61440) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
set (E := Ereg regs ([] : list word)).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU11 : bv_unsigned (ew E 11) = n) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : st_ok src2segs E (ss_rlhdr 0) (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs))).
{ unfold ss_rlhdr. replace src2_A_LLVMFuzzerTestOneInput with RLLVM by reflexivity. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- cbn [rlh_breg rlh_cnt nth app]. constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hstw. lia.
+ apply (region_ok_stack src2segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
- cbn [rlh_breg rlh_cnt nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2. repeat split; lia.
- cbn [f_atoms rlh_bfacts rlh_pfact rlh_cnt rlh_lo rlh_hi nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU11.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
pose proof (journal_init src2_msyms MR LIB_STACK_RGB [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom src2segs))) in HJ. fold sp0 in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset src2_msyms MR LAWS IMG src2_A_memset src2_memset_spec E _ _ LIB_STACK_RGB sp0 [] L A mem md L A _ (sp0 - 72) 0 40);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 72) with (sp0 + -72) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 46%nat regs2 mem2 MEMSET_CLOB RL_HDR0 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YQ0b.mkRegion (Some 2%nat) (-72) (-32) (-72) (-32) [mkChunk (-72) (CZero 40)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows src2segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows src2segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -72 + i) with (sp0 - 72 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2. repeat split; lia. }
jrun_to LAWS src2tbl_ok HS HJ2 RL_RET0.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_nil. }
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ => eapply (rl_ret0 API IMG L A mem md regs rg L A mm md) end.
+ exact HFZ. + exact HJ2. + exact Hid. + exact Hra. + exact Hal16. + intros b Hb; exact Hb.
+ fold sp0. unfold rsaved_ok.
repeat match goal with |- _ /\ _ => split end;
[ frame_wordI HS 2%nat HU2 HE 1%nat (1%bv:reg) | frame_wordI HS 2%nat HU2 HE 8%nat (8%bv:reg)
| frame_wordI HS 2%nat HU2 HE 9%nat (9%bv:reg) | frame_wordI HS 2%nat HU2 HE 18%nat (18%bv:reg) ].
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ unfold runtouched_ok; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
Qed.
End S.
End d.
