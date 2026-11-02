(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN08.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition REGS_F : list sv := Eval vm_compute in ss_regs (SSF K1 R0).
Lemma SSF_regs k r : ss_regs (SSF k r) = REGS_F /\ ss_pc (SSF k r) = FREE_RET /\ ss_resv (SSF k r) = None.
Proof. destruct k, r; vm_compute; repeat split; reflexivity. Qed.
Lemma some_inj {A} (x y : A) : Some x = Some y -> x = y.
Proof. intros H. exact (f_equal (fun o => match o with Some z => z | None => x end) H). Qed.
Lemma byte_sx32 y kk : 0 <= y -> (kk < 4)%nat ->
Z_to_bv 8 (Z.shiftr (sx32 y) (8 * Z.of_nat kk)) = Z_to_bv 8 (le_byte y 4 kk).
Proof.
intros Hy Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia.
rewrite <- (sx32_lo32 y). unfold lo32. set (y' := y mod 2 ^ 32).
assert (Hy' : 0 <= y' < 2 ^ 32) by (subst y'; apply Z.mod_pos_bound; lia).
destruct (sx32_cases y') as [[_ E]|[_ E]]; rewrite E; rewrite (Z.mod_small y' (2 ^ 32)) by lia; [reflexivity|].
rewrite !Z.shiftr_div_pow2 by lia.
destruct kk as [|[|[|[|]]]]; [| | | | lia]; cbn [Z.of_nat Z.mul Pos.of_succ_nat Pos.mul].
- change (2 ^ 0) with 1. rewrite !Z.div_1_r.
replace (y' + 2 ^ 64 - 2 ^ 32) with (y' + 72057594021150720 * 256) by lia. rewrite Z_mod_plus_full. reflexivity.
- change (2 ^ 8) with 256. replace (y' + 2 ^ 64 - 2 ^ 32) with (y' + 72057594021150720 * 256) by lia.
rewrite Z.div_add by lia. replace (72057594021150720) with (281474976645120 * 256) by reflexivity. rewrite Z_mod_plus_full. reflexivity.
- change (2 ^ 16) with 65536. replace (y' + 2 ^ 64 - 2 ^ 32) with (y' + 281474976645120 * 65536) by lia.
rewrite Z.div_add by lia. replace (281474976645120) with (1099511627520 * 256) by reflexivity. rewrite Z_mod_plus_full. reflexivity.
- change (2 ^ 24) with 16777216. replace (y' + 2 ^ 64 - 2 ^ 32) with (y' + 1099511627520 * 16777216) by lia.
rewrite Z.div_add by lia. replace (1099511627520) with (4294967295 * 256) by reflexivity. rewrite Z_mod_plus_full. reflexivity.
Qed.
Section f.
Variables (k : kcase) (r : rcase) (v : fvals) (mem : word -> option byte) (ms1 : machine_state).
Hypothesis FP : free_pre k r v mem.
Hypothesis HS1 : st_ok src0segs (EV (xvf v)) (SSF k r) ms1.
Let regs := fv_regs v.
Lemma ff_shape : ms1 = mkst (ms_regs ms1) (Z_to_bv 64 FREE_RET) (ms_mem ms1) (seg_rom src0segs).
Proof.
destruct (SSF_regs k r) as (_ & Hpc & Hrv).
destruct HS1 as (H1 & H2 & H3 & H4 & H5 & H6 & _). destruct ms1; cbn in *. unfold mkst. rewrite Hrv in H4. cbn in H4. subst. rewrite Hpc. reflexivity.
Qed.
Lemma ff_reg (i : nat) : In i [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
getr (ms_regs ms1) (nat_to_reg i) = getr regs (nat_to_reg i).
Proof.
intros Hi. destruct (SSF_regs k r) as (Hregs & _).
pose proof (st_ok_regs_ok _ _ _ _ HS1 (nat_to_reg i)) as R. rewrite Hregs in R. rewrite R.
assert (E : sr_get REGS_F (nat_to_reg i) = SOff i 0).
{ repeat (destruct Hi as [<-|Hi]; [reflexivity|]). destruct Hi. }
rewrite E. cbn [sv_denot EV ew]. rewrite Z.add_0_r. rewrite xvf_reg by (repeat (destruct Hi as [<-|Hi]; [lia|]); destruct Hi).
rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma ff_mem :
mbyte src0segs (ms_mem ms1) (fv_p v - 3) = Some (Z_to_bv 8 255) /\
mbyte src0segs (ms_mem ms1) (fv_p v - 2) = Some (Z_to_bv 8 0) /\
mbyte src0segs (ms_mem ms1) (fv_p v - 1) = Some (Z_to_bv 8 0) /\
(forall kk, (kk < 4)%nat -> mbyte src0segs (ms_mem ms1) (fv_g v + 28 + Z.of_nat kk) = Some (Z_to_bv 8 (le_byte (fv_fr v + 2 ^ fv_idx v) 4 kk))) /\
(forall a, fv_sp v - 8192 <= a < fv_sp v -> writable_at src0segs (ms_mem ms1) a).
Proof.
pose proof (st_ok_mem_ok _ _ _ _ HS1) as (_ & ROK & _).
rewrite (proj2 (proj2 (proj2 (SSF_shape k r)))) in ROK.
pose proof (xvf_range _ _ _ _ FP) as XR.
apply Forall_cons_iff in ROK as [Rhdr ROK]. apply Forall_cons_iff in ROK as [_ ROK]. apply Forall_cons_iff in ROK as [Rmeta ROK].
apply Forall_cons_iff in ROK as [_ ROK]. apply Forall_cons_iff in ROK as [_ ROK]. apply Forall_cons_iff in ROK as [_ ROK]. apply Forall_cons_iff in ROK as [Rstk _].
destruct Rhdr as (_ & _ & _ & Chdr). destruct Rmeta as (_ & _ & _ & Cmeta). destruct Rstk as (_ & _ & Wstk & _).
cbn [r_base r_chunks r_wlo r_whi] in *. rewrite !(base_val_EV (xvf v) XR) in *.
change (xvf v aP) with (fv_p v) in *. change (xvf v aG) with (fv_g v) in *. change (xvf v aSP) with (fv_sp v) in *.
apply Forall_cons_iff in Chdr as [C2 Chdr]. apply Forall_cons_iff in Chdr as [C3 Chdr]. apply Forall_cons_iff in Chdr as [C4 _].
apply Forall_cons_iff in Cmeta as [C28 _].
assert (B3 := C3 0 ltac:(cbn; lia)). assert (B2a := C2 0 ltac:(cbn; lia)). assert (B2b := C2 1 ltac:(cbn; lia)).
cbn [c_off c_val cbyte byte_of_word sv_denot] in B3, B2a, B2b.
destruct B3 as (b3 & E3 & M3). destruct B2a as (b2 & E2 & M2). destruct B2b as (b1 & E1 & M1).
injection E3 as E3'. injection E2 as E2'. injection E1 as E1'. subst b3 b2 b1.
split; [|split; [|split; [|split]]].
- replace (fv_p v - 3) with (fv_p v + -3 + 0) by lia. rewrite M3. f_equal; try (apply bv_eq; vm_compute; reflexivity).
- replace (fv_p v - 2) with (fv_p v + -2 + 0) by lia. rewrite M2. f_equal; try (apply bv_eq; vm_compute; reflexivity).
- replace (fv_p v - 1) with (fv_p v + -2 + 1) by lia. rewrite M1. f_equal; try (apply bv_eq; vm_compute; reflexivity).
- intros kk Hkk. destruct (C28 (Z.of_nat kk) ltac:(cbn; lia)) as (b & Eb & Mb). cbn [c_off c_val cbyte] in Eb, Mb.
rewrite Mb. apply some_inj in Eb. subst b. f_equal.
unfold byte_of_word.
change (sv_denot (EV (xvf v)) (SAluw ALU_ADD FREED SELF)) with
(sext 64 (alu32 ALU_ADD (low32 (sv_denot (EV (xvf v)) FREED)) (low32 (sv_denot (EV (xvf v)) SELF)))).
rewrite addw_rr_unsigned, (U_SELF _ _ _ _ FP). unfold FREED. rewrite U_sext32. rewrite (den_off0 (xvf v) XR). rewrite lit64_small by (apply XR).
change (xvf v aFR) with (fv_fr v). rewrite addw_masks.
apply byte_sx32; [| exact Hkk]. pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L. pose proof (Z.pow_nonneg 2 (fv_idx v)). lia.
- intros a Ha. replace a with (fv_sp v + (a - fv_sp v)) by lia. apply Wstk. lia.
Qed.
End f.
Section h.
Variables (k : kcase) (r : rcase) (v : fvals) (m : word -> option byte).
Hypothesis FP : free_pre k r v m.
Let XR := xvf_range _ _ _ _ FP.
Lemma U_FREED : bv_unsigned (sv_denot (EV (xvf v)) FREED) = sx32 (fv_fr v).
Proof. unfold FREED. rewrite U_sext32. rewrite (den_off0 _ XR), lit64_small by (apply XR). reflexivity. Qed.
Lemma U_MASKSELF : bv_unsigned (sv_denot (EV (xvf v)) (SAluw ALU_ADD MASK SELF)) = sx32 (Z.lor (fv_av v) (fv_fr v) + 2 ^ fv_idx v).
Proof.
change (sv_denot (EV (xvf v)) (SAluw ALU_ADD MASK SELF)) with
(sext 64 (alu32 ALU_ADD (low32 (sv_denot (EV (xvf v)) MASK)) (low32 (sv_denot (EV (xvf v)) SELF)))).
rewrite addw_rr_unsigned, (U_MASK _ _ _ _ FP), (U_SELF _ _ _ _ FP). apply addw_masks.
Qed.
Lemma U_ALL : bv_unsigned (sv_denot (EV (xvf v)) ALL) = sx32 (ones (fv_last v)).
Proof.
change (sv_denot (EV (xvf v)) ALL) with
(sext 64 (alu32 ALU_ADD (low32 (sext 64 (alu32 ALU_SLL (low32 (sv_denot (EV (xvf v)) (SLit 2))) (low32 (sv_denot (EV (xvf v)) (SOff aBITS 0))))))
(low32 (sv_denot (EV (xvf v)) (SLit (-1)))))).
rewrite addw_rr_unsigned, sllw_rr_unsigned. rewrite (den_off0 _ XR). cbn [sv_denot].
rewrite (lit64_unsigned (-1)), !lit64_small by (try apply XR; lia). change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L.
rewrite (proj2 (addiw_sllw2_m1 (xvf v aBITS) ltac:(apply XR))).
change (xvf v aBITS) with (fv_bits v). rewrite (fp_bits _ _ _ _ FP), bits_mod32 by lia. reflexivity.
Qed.
Lemma mask_self_u32 : 0 <= Z.lor (fv_av v) (fv_fr v) + 2 ^ fv_idx v < 2 ^ 32.
Proof.
pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L.
assert (Hl : 0 <= Z.lor (fv_av v) (fv_fr v) < 2 ^ 32) by (apply lor_range; lia).
assert (Hb : 0 < 2 ^ fv_idx v < 2 ^ 32) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
assert (D : Z.land (Z.lor (fv_av v) (fv_fr v)) (2 ^ fv_idx v) = 0).
{ apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.lor_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec (fv_idx v) j); [subst; rewrite (fp_avbit _ _ _ _ FP), (fp_frbit _ _ _ _ FP); reflexivity | apply andb_false_r]. }
rewrite (Z.add_nocarry_lxor _ _ D). apply lxor_range; lia.
Qed.
Lemma ones_u32 : 0 <= ones (fv_last v) < 2 ^ 32.
Proof.
pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L. unfold ones.
assert (0 < 2 ^ (fv_last v + 1) <= 2 ^ 32) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]). lia.
Qed.
Lemma taken_fastA : fv_fr v <> 0 -> branch_taken BC_NE (sv_denot (EV (xvf v)) FREED) (sv_denot (EV (xvf v)) (SLit 0)) = true.
Proof.
intros H. rewrite branch_ne, U_FREED. cbn [sv_denot]. change (bv_unsigned (Z_to_bv 64 0)) with 0.
pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L.
destruct (Z.eqb_spec (sx32 (fv_fr v)) 0) as [E|E]; [|reflexivity]. exfalso. apply (sx32_nonzero_u32 (fv_fr v)); lia.
Qed.
Lemma taken_slowA : fv_fr v = 0 -> branch_taken BC_EQ (sv_denot (EV (xvf v)) FREED) (sv_denot (EV (xvf v)) (SLit 0)) = true.
Proof. intros H. rewrite branch_eq, U_FREED, H. reflexivity. Qed.
Lemma taken_fastB : Z.lor (fv_av v) (fv_fr v) + 2 ^ fv_idx v <> ones (fv_last v) ->
branch_taken BC_NE (sv_denot (EV (xvf v)) (SAluw ALU_ADD MASK SELF)) (sv_denot (EV (xvf v)) ALL) = true.
Proof.
intros H. rewrite branch_ne, U_MASKSELF, U_ALL.
destruct (Z.eqb_spec (sx32 (Z.lor (fv_av v) (fv_fr v) + 2 ^ fv_idx v)) (sx32 (ones (fv_last v)))) as [E|E]; [|reflexivity].
exfalso. apply H. apply (proj1 (sx32_inj_u32 _ _ mask_self_u32 ones_u32) E).
Qed.
Lemma taken_slowB : Z.lor (fv_av v) (fv_fr v) + 2 ^ fv_idx v = ones (fv_last v) ->
branch_taken BC_EQ (sv_denot (EV (xvf v)) (SAluw ALU_ADD MASK SELF)) (sv_denot (EV (xvf v)) ALL) = true.
Proof. intros H. rewrite branch_eq, U_MASKSELF, U_ALL, H. apply Z.eqb_refl. Qed.
Lemma in_wrange_free a : in_wrange (EV (xvf v)) (free_mem k r) a ->
(fv_p v - 3 <= a < fv_p v) \/ (fv_g v + 28 <= a < fv_g v + 32) \/ (fv_sp v - 8192 <= a < fv_sp v).
Proof.
intros (rg & Hin & Ha). unfold free_mem, common_mem in Hin.
assert (CASES : rg = reg_hdr \/ rg = reg_meta \/ rg = reg_stk \/ r_wlo rg = r_whi rg).
{ apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
- cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; auto; right; right; right; reflexivity.
- destruct k; cbn [k_mem In] in Hin; (destruct Hin as [<-|[]] || destruct Hin); right; right; right; reflexivity.
- destruct r; cbn [r_mem In] in Hin;
repeat (destruct Hin as [<-|Hin]; [right; right; right; reflexivity|]); destruct Hin. }
destruct CASES as [-> | [-> | [-> | E]]]; cbn [r_base r_wlo r_whi reg_hdr reg_meta reg_stk] in Ha;
rewrite ?(base_val_EV (xvf v) XR) in Ha.
- left. change (xvf v aP) with (fv_p v) in Ha. lia.
- right; left. change (xvf v aG) with (fv_g v) in Ha. lia.
- right; right. change (xvf v aSP) with (fv_sp v) in Ha. lia.
- rewrite E in Ha. lia.
Qed.
End h.
Lemma writable_off_img_present m a : 0 <= a < 2 ^ 64 -> ~ in_img1 a -> writable_at src0segs m a -> present m a.
Proof.
intros Ha Hni Hw. unfold writable_at, wview in Hw. unfold present.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity|]. exfalso.
destruct (find_segment src0segs (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Ef; [|apply Hw; reflexivity].
pose proof (find_segment_in _ _ _ _ Ef) as Hin. pose proof (find_segment_range _ _ _ _ Ef) as Hr.
rewrite lit64_small in Hr by lia.
assert (H : forallb (fun s => (0x10000 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x51000)) src0segs = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H seg Hin). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply Hni. unfold in_img1. lia.
Qed.
Lemma with_vmmaps_self md : m_vm_lazy md = [] -> m_vm_materialized md = [] -> md = with_vmmaps (m_vmmaps md) md.
Proof.
destruct md as [fd [maps lazy mat] io fs proc lim tm]. intros Hl Hm. unfold with_vmmaps, m_vmmaps, m_vm_lazy, m_vm_materialized in *.
cbn in *. subst. reflexivity.
Qed.
Lemma B1_img_range a : in_img B1 a -> 0x10000 <= a < 0x51000.
Proof.
intros [_ (s & Hs & Ha)].
assert (H : forallb (fun s : word * word => (0x10000 <=? bv_unsigned (fst s)) && (bv_unsigned (fst s) + bv_unsigned (snd s) <=? 0x51000))
(segments_reserved src0segs) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H s Hs). apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma B1_errno_img x : errno_addr B1 <= x < errno_addr B1 + 4 -> in_img1 x.
Proof. unfold errno_addr, in_img1. change (ms_tp B1) with src0_tp. change (ms_errno_off B1) with (-164). unfold src0_tp. lia. Qed.
Lemma loc_addr_padd L p d : loc_addr L (LMem (padd p d)) = ptr_addr L p + d.
Proof. destruct p as [rr o]. unfold ptr_addr, loc_addr, padd. lia. Qed.
Lemma yields_ret {R} (r : R) : yields (IRet r : itree astate R) [] r.
Proof. reflexivity. Qed.
Lemma same_byte_views m m' x : m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
mbyte src0segs m' x = mbyte src0segs m x /\ (writable_at src0segs m x <-> writable_at src0segs m' x).
Proof. intros E. unfold mbyte, writable_at, wview. rewrite E. tauto. Qed.
Lemma writable_same m m' x : m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) -> writable_at src0segs m x -> writable_at src0segs m' x.
Proof. intros E. apply (proj1 (proj2 (same_byte_views m m' x E))). Qed.
Lemma Z_to_bv5_nat_to_reg r : 0 <= r < 32 -> Z_to_bv 5 r = nat_to_reg (Z.to_nat r).
Proof.
intros Hr. rewrite <- (nat_to_reg_ridx (Z_to_bv 5 r)). f_equal. f_equal.
rewrite Z_to_bv_unsigned. rewrite bv_wrap_small; [reflexivity|]. change (bv_modulus 5) with 32. lia.
Qed.
Lemma callee_saved_cases r : callee_saved r ->
0 <= r < 32 /\ In (Z.to_nat r) [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Proof.
intros Hr. unfold callee_saved in Hr. split; [lia|].
destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [cbn; tauto | cbn; tauto | cbn; tauto | cbn; tauto | cbn; tauto |].
assert (H : (18 <= Z.to_nat r <= 27)%nat) by lia. revert H. generalize (Z.to_nat r) as m. intros m H.
do 18 (destruct m as [|m]; [lia|]).
do 10 (destruct m as [|m]; [cbn; tauto|]). lia.
Qed.
Lemma mreal_IRet {R} segs c (r : R) Q : SR segs c (Q r) -> mreal segs c (IRet r) Q.
Proof. intros H. exact H. Qed.
Lemma fetch_free_ret : fetch_word src0segs (Z_to_bv 64 FREE_RET) = Some (0x00008067%bv : bv 32).
Proof. rewrite <- (Z_to_bv_bv_unsigned 32 (0x00008067%bv : bv 32)). apply src0tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_ret : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma SR_free_ret E ss ms md Q :
st_ok src0segs E ss ms -> ss_resv ss = None -> ss_pc ss = FREE_RET ->
sr_get (ss_regs ss) 1 = SOff 1 0 -> YK0s.ret_ok (ew E 1) ->
m_halted md = None -> m_vm_lazy md = [] ->
Q (mkCfg (mkst (ms_regs ms) (ew E 1) (ms_mem ms) (seg_rom src0segs)) md) ->
SR src0segs (mkCfg ms md) Q.
Proof.
intros HS Hrv Hpc Hra Hret Hh Hlz HQ.
pose proof (st_ok_reg src0segs E ss ms 1 HS) as R1. rewrite Hra in R1. cbn [sv_denot] in R1.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R1.
rewrite (st_ok_mkst src0segs E ss ms HS Hrv). rewrite Hpc.
eapply SR_step; [exact Hh | exact Hlz | reflexivity | |].
- eapply step_jalr_x0; [apply fetch_free_ret | reflexivity | apply decode_ret | exact R1].
- cbn [ms_regs ms_mem mkst]. change (bv_signed (0%bv : bv 12)) with 0. unfold YK0s.ret_ok in Hret. rewrite Hret.
apply SR_ret. exact HQ.
Qed.
Lemma REGS_F_ra : sr_get REGS_F 1 = SOff 1 0.
Proof. vm_compute. reflexivity. Qed.
Record free_ctx (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(g : sptr) (am : ameta) (idx : Z) (fr : frame) (a : sptr) (ka : Z) (rg : YO0i.region) : Prop := FCX {
fc_pre : call_pre B1 (MRx B1) L A regs mem md;
fc_used : usedX [] A g am;
fc_idx : 0 <= idx <= am_last am;
fc_fr : ss_fr (nth_slot am idx) = Some fr;
fc_kind : fr_kind fr = FUser;
fc_in : In (frame_ptr am idx fr, fr_n fr) (user_blocks A);
fc_a0 : getr regs 10 = Z_to_bv 64 (ptr_addr L (frame_ptr am idx fr));
fc_area : In a (st_areas A) /\ 0 <= ka < METAS_PER_AREA /\ g = padd a (AREA_HDR + META_SIZE * ka);
fc_rg : region_of A (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
0 <= poff (am_mem am) /\ poff (am_mem am) + group_extent am + IB <= rg_len rg }.
Section l.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (idx : Z) (fr : frame).
Variables (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : free_ctx L A regs mem md g am idx fr a ka rg.
Let PRE : call_pre B1 (MRx B1) L A regs mem md := fc_pre _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hu : usedX [] A g am := fc_used _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hidx : 0 <= idx <= am_last am := fc_idx _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hfr : ss_fr (nth_slot am idx) = Some fr := fc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hk : fr_kind fr = FUser := fc_kind _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hin : In (frame_ptr am idx fr, fr_n fr) (user_blocks A) := fc_in _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Ha0 : getr regs 10 = Z_to_bv 64 (ptr_addr L (frame_ptr am idx fr)) := fc_a0 _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Harea : In a (st_areas A) /\ 0 <= ka < METAS_PER_AREA /\ g = padd a (AREA_HDR + META_SIZE * ka) := fc_area _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let Hrg : region_of A (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
0 <= poff (am_mem am) /\ poff (am_mem am) + group_extent am + IB <= rg_len rg := fc_rg _ _ _ _ _ _ _ _ _ _ _ _ HC.
Definition kc : kcase := kcase_of am.
Definition rcv : rcase := rcase_of (reserved_of am fr).
Definition vv : fvals := fv_of regs L g am idx fr a (rg_len rg).
Let p := frame_ptr am idx fr.
Let P := ptr_addr L p.
Let G := ptr_addr L g.
Let SP := spZ regs.
Lemma MX : MRx B1 L A mem md. Proof. exact (proj1 PRE). Qed.
Lemma M : MRc B1 L A mem md. Proof. exact (MRx_MRc _ _ _ _ _ MX). Qed.
Lemma HW : WF A. Proof. exact (mc_wf _ _ _ _ _ M). Qed.
Lemma HL : layout_ok L A. Proof. exact (mc_layout _ _ _ _ _ M). Qed.
Lemma Mg : MT A g = Some (MUsed am). Proof. exact (proj1 (usedX_MT _ _ _ _ Hu)). Qed.
Lemma Hframes : In (g, am, idx, fr) (frames A). Proof. exact (frames_intro A g am idx fr HW Mg Hidx Hfr). Qed.
Lemma FP : free_pre kc rcv vv mem.
Proof.
pose proof PRE as (MX' & _ & _ & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & _).
unfold kc, rcv, vv. eapply free_pre_intro; try eassumption.
- exact M. - exact (MRx_rsv _ _ _ _ _ MX). - auto.
Qed.
Lemma HS0 : st_ok src0segs (EV (xvf vv)) (ss_free kc rcv) (mkst regs (Z_to_bv 64 src0_A_free) mem (seg_rom src0segs)).
Proof. exact (free_entry_st_ok _ _ _ _ FP). Qed.
Lemma P_range : 4096 <= P /\ P + fr_n fr <= alloc_ceiling /\ 0 <= fr_n fr.
Proof.
destruct (block_region A p (fr_n fr) HW Hin) as (kr & o & rg0 & Ep & Hrg0 & _ & Hl0 & Ho & Hn & Hon & _).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) kr rg0 Hrg0 Hl0) as (_ & H1 & H2 & _).
unfold P, ptr_addr. rewrite Ep. cbn [loc_addr]. lia.
Qed.
Lemma E_P : fv_p vv = P.
Proof.
unfold fv_p, vv, fv_of. cbn [fv_regs]. rewrite Ha0. pose proof P_range. pose proof alloc_ceiling_lt. apply lit64_small. unfold P in *. lia.
Qed.
Lemma E_SP : fv_sp vv = SP. Proof. reflexivity. Qed.
Lemma E_G : fv_g vv = G. Proof. reflexivity. Qed.
Lemma E_FR : fv_fr vv = am_freed am. Proof. reflexivity. Qed.
Lemma E_AV : fv_av vv = am_avail am. Proof. reflexivity. Qed.
Lemma E_IDX : fv_idx vv = idx. Proof. reflexivity. Qed.
Lemma E_LAST : fv_last vv = am_last am. Proof. reflexivity. Qed.
Lemma E_regs : fv_regs vv = regs. Proof. reflexivity. Qed.
Lemma win_owned x : (P - 3 <= x < P) \/ (G + 28 <= x < G + 32) -> alloc_owned L A x.
Proof.
pose proof (get_meta_ok A g am idx fr HW Hframes) as GM. cbn zeta in GM.
destruct GM as (_ & C3 & C2 & _ & _ & _ & C28 & _).
intros [Hx|Hx].
- destruct (Z.eq_dec x (P - 3)) as [->|Hne].
+ pose proof (image_cell_owned L A _ 0 HW HL C3 ltac:(cbn [mc_w]; lia)) as O. cbn [mc_loc] in O.
rewrite loc_addr_padd in O. unfold P. replace (ptr_addr L p - 3) with (ptr_addr L p + -3 + Z.of_nat 0) by lia. exact O.
+ pose proof (image_cell_owned L A _ (Z.to_nat (x - (P - 2))) HW HL C2 ltac:(cbn [mc_w]; unfold P in *; lia)) as O. cbn [mc_loc] in O.
rewrite loc_addr_padd in O. unfold P in *. replace x with (ptr_addr L p + -2 + Z.of_nat (Z.to_nat (x - (ptr_addr L p - 2)))) by lia. exact O.
- pose proof (image_cell_owned L A _ (Z.to_nat (x - (G + 28))) HW HL C28 ltac:(cbn [mc_w]; unfold G in *; lia)) as O. cbn [mc_loc] in O.
rewrite loc_addr_padd in O. unfold G, META_freed in *. replace x with (ptr_addr L g + 28 + Z.of_nat (Z.to_nat (x - (ptr_addr L g + 28)))) by lia. exact O.
Qed.
Lemma win_off_img x : (P - 3 <= x < P) \/ (G + 28 <= x < G + 32) -> ~ in_img1 x /\ 0 <= x < alloc_ceiling.
Proof.
intros Hx. pose proof (fp_grp _ _ _ _ FP) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GI). pose proof (fp_ar _ _ _ _ FP) as (A1 & A2 & _ & A4 & A5 & AI & _).
rewrite E_P in *. rewrite E_G in *. unfold CEIL in *. pose proof (proj1 alloc_ceiling_val).
destruct Hx as [Hx|Hx].
- split; [apply GI; lia | lia].
- split; [apply AI; lia | lia].
Qed.
Lemma SP_facts : alloc_ceiling + 8192 <= SP /\ SP < 2 ^ 63.
Proof. pose proof PRE as (_ & _ & _ & _ & _ & Hceil & Hsp63 & _). unfold ALLOC_STACK in Hceil. unfold SP. lia. Qed.
Let A2 := upd_meta g (MUsed (am_fast idx am)) A.
Lemma fast_yields : fast_cond idx am = true -> yields (free (Some p) A) [] (tt, A2).
Proof.
intros FC. pose proof (get_meta_ok A g am idx fr HW Hframes) as GM. cbn zeta in GM.
destruct GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hff).
pose proof (inv_groups HW g am Hu) as GG. destruct GG as ((_ & _ & Glen & _) & _ & Gsl & _).
pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (Hal & _).
assert (Hmask : Z.land (mask0 am) (bit idx) = 0).
{ unfold allocated in Hal. unfold mask0, bit. apply Z.bits_inj'. intros j Hj.
rewrite Z.land_spec, Z.lor_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec idx j); [subst | apply andb_false_r].
rewrite Z.lor_spec in Hal. destruct (Z.testbit (am_avail am) j), (Z.testbit (am_freed am) j); cbn in Hal |- *; try discriminate; reflexivity. }
unfold p. rewrite (free_tree A (frame_ptr am idx fr) g idx am Hff Mg Hmask). rewrite FC.
unfold A2. rewrite <- A_fast_eq. apply yields_ret.
Qed.
Lemma HW2 : fast_cond idx am = true -> WF A2.
Proof. intros FC. exact (free_wf A p (fr_n fr) [] A2 HW Hin (fast_yields FC)). Qed.
Lemma fast_blocks : fast_cond idx am = true ->
exists l1 l2, user_blocks A = l1 ++ (p, fr_n fr) :: l2 /\ user_blocks A2 = l1 ++ l2.
Proof. intros FC. exact (free_blocks A p (fr_n fr) [] A2 HW Hin (fast_yields FC)). Qed.
Lemma shape2 : shape_eq am (am_fast idx am) idx /\ ss_fr (nth_slot (am_fast idx am) idx) = None.
Proof.
pose proof (inv_groups HW g am Hu) as GG. destruct GG as ((_ & _ & Glen & _) & _).
split; [apply shape_eq_fast; [exact Hidx | exact Glen]|].
rewrite nth_slot_fast, nth_slot_rel by (exact Hidx || exact Glen). apply released_slot_fr. rewrite Hfr. discriminate.
Qed.
Lemma fast_leaf ms1 :
fast_cond idx am = true ->
st_ok src0segs (EV (xvf vv)) (SSF kc rcv) ms1 ->
frame_of (EV (xvf vv)) (free_mem kc rcv) mem (ms_mem ms1) ->
free_leaf B1 (MRx B1) L A regs mem md p (fr_n fr) (tt, A2)
(mkCfg (mkst (ms_regs ms1) (getr regs 1) (ms_mem ms1) (seg_rom src0segs)) md).
Proof.
intros FC HS1 HFR.
pose proof PRE as (_ & _ & HB & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & _).
pose proof M as MR. pose proof HW as HWA. pose proof HL as HLA. pose proof (HW2 FC) as HW2'.
destruct (mc_md _ _ _ _ _ MR) as (Hh & Hlz & Hmat).
pose proof SP_facts as [SP1 SP2]. pose proof (proj1 alloc_ceiling_val) as HCV. pose proof P_range as (PR1 & PR2 & PR3).
set (mem1 := ms_mem ms1).
assert (F1 : forall x, 0 <= x < 2 ^ 64 -> ~ (P - 3 <= x < P) -> ~ (G + 28 <= x < G + 32) -> ~ (SP - 8192 <= x < SP) ->
mem1 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ intros x Hx N1 N2 N3. apply HFR. rewrite lit64_small by lia. intros W.
apply (in_wrange_free _ _ _ _ FP) in W. rewrite E_P, E_G, E_SP in W. tauto. }
destruct (ff_mem kc rcv vv mem ms1 FP HS1) as (B3 & B2 & B1' & B28 & WSTK). rewrite E_P in B3, B2, B1'. rewrite E_G in B28. rewrite E_SP in WSTK.
rewrite E_FR, E_IDX in B28.
assert (F4 : forall x, (P - 3 <= x < P) \/ (G + 28 <= x < G + 32) -> present mem1 x).
{ intros x Hx. destruct (win_off_img x Hx) as [NI LOW].
apply writable_off_img_present; [lia | exact NI |].
pose proof (st_ok_mem_ok _ _ _ _ HS1) as (_ & ROK & _). rewrite (proj2 (proj2 (proj2 (SSF_shape kc rcv)))) in ROK.
apply Forall_cons_iff in ROK as [Rhdr ROK]. apply Forall_cons_iff in ROK as [_ ROK]. apply Forall_cons_iff in ROK as [Rmeta _].
destruct Rhdr as (_ & _ & Wh & _). destruct Rmeta as (_ & _ & Wm & _).
cbn [r_base r_wlo r_whi] in Wh, Wm. rewrite !(base_val_EV (xvf vv) (xvf_range _ _ _ _ FP)) in Wh, Wm.
change (xvf vv aP) with (fv_p vv) in Wh. change (xvf vv aG) with (fv_g vv) in Wm. rewrite E_P in Wh. rewrite E_G in Wm.
destruct Hx as [Hx|Hx].
- replace x with (P + (x - P)) by lia. apply Wh. lia.
- replace x with (G + (x - G)) by lia. apply Wm. lia. }
destruct (memrep_fast B1 L A mem md g am idx fr mem1 SP MR Hu Hidx Hfr HW2' ltac:(lia) F1 (conj B3 (conj B2 B1')) B28 F4) as [MREP TG].
assert (WOWN : forall x, (P - 3 <= x < P) \/ (G + 28 <= x < G + 32) -> owned B1 L A x) by (intros x Hx; left; apply win_owned; exact Hx).
assert (UNCH : forall x, 0 <= x < 2 ^ 64 -> ~ owned B1 L A x -> ~ (SP - 8192 <= x < SP) -> mem1 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ intros x Hx NO NS. apply F1; [exact Hx | intros W; apply NO; apply WOWN; auto | intros W; apply NO; apply WOWN; auto | exact NS]. }
assert (MRX2 : MRx B1 L A2 mem1 md).
{ apply MRx_intro.
+ apply MRc_intro; try assumption.
* exact (mc_syms _ _ _ _ _ MR).
* exact (mc_ctx _ _ _ _ _ MR).
* exact (mc_sec _ _ _ _ _ MR).
* apply (statics_ok_ext B1 mem mem1 (mc_statics _ _ _ _ _ MR)). intros x Hs.
pose proof (so_img_hi _ (mc_syms _ _ _ _ _ MR) x (so_statics_img _ (mc_syms _ _ _ _ _ MR) x Hs)) as Hxr.
pose proof (B1_img_range x (so_statics_img _ (mc_syms _ _ _ _ _ MR) x Hs)) as Hxi.
unfold mbyte. cbn [ms_segs src0_msyms]. rewrite F1; [reflexivity | lia | | | lia].
-- intros W. apply (proj1 (win_off_img x (or_introl W))). unfold in_img1. lia.
-- intros W. apply (proj1 (win_off_img x (or_intror W))). unfold in_img1. lia.
* unfold A2. apply ledger_ok_upd_meta. exact (mc_ledger _ _ _ _ _ MR).
+ eapply ledger_x_same_regions; [exact (MRx_ledger_x _ _ _ _ _ MX) | reflexivity | reflexivity | reflexivity].
+ intros g0 am0 i fr0 Hin0 Hk0. destruct shape2 as [SE Hnone].
destruct (frames_upd A g am (am_fast idx am) idx g0 am0 i fr0 Mg SE Hnone Hin0) as (am1 & Hin1 & Hst).
unfold reserved_of. rewrite <- Hst. exact (MRx_rsv _ _ _ _ _ MX g0 am1 i fr0 Hin1 Hk0).
+ pose proof (MRx_ama _ _ _ _ _ MX) as AM. exact AM.
+   unfold A2. apply (span_ok_upd_same3 A g am); [exact (MRx_span _ _ _ _ _ MX) | exact Mg | reflexivity | reflexivity | reflexivity]. }
assert (RP : regs_preserved regs (ms_regs ms1)).
{ intros r0 Hr0. destruct (callee_saved_cases r0 Hr0) as [Rr RI].
rewrite (Z_to_bv5_nat_to_reg r0 Rr). rewrite (ff_reg kc rcv vv ms1 HS1 _ RI). rewrite E_regs. reflexivity. }
assert (FRM : forall x, (alloc_ceiling <= x < 2 ^ 64 \/ in_img B1 x) -> ~ owned B1 L A x -> ~ owned B1 L A2 x -> ~ scratch B1 regs x ->
~ (ptr_addr L p <= x < ptr_addr L p + fr_n fr) ->
mbyte (ms_segs B1) mem1 x = mbyte (ms_segs B1) mem x /\ (writable_at (ms_segs B1) mem x <-> writable_at (ms_segs B1) mem1 x)).
{ intros x Hhi NO NO2 NS NE.
assert (Hx : 0 <= x < 2 ^ 64) by (destruct Hhi as [Hhi|Hhi]; [lia | apply B1_img_range in Hhi; lia]).
apply same_byte_views. apply UNCH; [exact Hx | exact NO |]. intros W. apply NS. left. unfold ALLOC_STACK. unfold SP in W. lia. }
assert (BLK : forall q n i, In (q, n) (user_blocks A) -> In (q, n) (user_blocks A2) -> 0 <= i < n ->
mbyte (ms_segs B1) mem1 (ptr_addr L q + i) = mbyte (ms_segs B1) mem (ptr_addr L q + i)).
{ intros q n i Hq _ Hi. destruct (blocks_facts B1 L A mem md q n i MR Hq Hi) as (_ & Hlo & Hhi & HNO).
apply same_byte_views. apply UNCH; [lia | exact HNO | lia]. }
assert (SCR : forall x, scratch B1 regs x -> writable_at (ms_segs B1) mem1 x).
{ intros x [Hs|Hs].
- apply WSTK. unfold ALLOC_STACK in Hs. unfold SP. lia.
- apply (writable_same mem mem1 x); [| exact (Herr x Hs)]. pose proof (B1_errno_img x Hs) as Hxi. unfold in_img1 in Hxi.
apply F1; [lia | | | lia].
+ intros W. apply (proj1 (win_off_img x (or_introl W))). unfold in_img1. lia.
+ intros W. apply (proj1 (win_off_img x (or_intror W))). unfold in_img1. lia. }
exists L, (ms_regs ms1), mem1, md. split; [reflexivity|]. split; [| apply fast_blocks; exact FC].
refine (conj MRX2 (conj HW2' (conj _ (conj (layout_le_refl _ _) (conj _ (conj RP (conj _ (conj FRM (conj BLK SCR))))))))).
- unfold A2. apply (proj2 (bounded_upd_meta _ _ _)). exact HB.
- intros; reflexivity.
- exists (m_vmmaps md). apply with_vmmaps_self; assumption.
Qed.
Lemma ew_ra : ew (EV (xvf vv)) 1 = getr regs 1.
Proof. cbn [ew EV]. rewrite xvf_reg by lia. rewrite E_regs. apply Z_to_bv_bv_unsigned. Qed.
Lemma fast_cond_facts : fast_cond idx am = true ->
fv_fr vv <> 0 /\ Z.lor (fv_av vv) (fv_fr vv) + 2 ^ fv_idx vv <> ones (fv_last vv).
Proof.
intros FC. unfold fast_cond, mask0 in FC. apply andb_prop in FC as [F1 F2].
rewrite E_FR, E_AV, E_IDX, E_LAST. split.
- intros E. rewrite E in F1. discriminate.
- intros E. rewrite Z.lor_comm in E. unfold bit in F2. rewrite E, Z.eqb_refl in F2. discriminate.
Qed.
Theorem fast_mreal : fast_cond idx am = true ->
mreal src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_free) mem (seg_rom src0segs)) md) (IRet (tt, A2))
(free_leaf B1 (MRx B1) L A regs mem md p (fr_n fr)).
Proof.
intros FC. apply mreal_IRet. destruct (mc_md _ _ _ _ _ M) as (Hh & Hlz & Hmat).
pose proof PRE as (_ & _ & _ & Hret & _).
destruct (fast_cond_facts FC) as [C1 C2].
assert (HSF : st_ok src0segs (EV (xvf vv)) (ss_fast kc rcv) (mkst regs (Z_to_bv 64 src0_A_free) mem (seg_rom src0segs))).
{ unfold ss_fast, cond_fastA, cond_fastB. apply st_ok_add_cond; [apply st_ok_add_cond; [exact HS0 | exact (taken_fastA _ _ _ _ FP C1)] | exact (taken_fastB _ _ _ _ FP C2)]. }
eapply SR_bind; [exact (free_fast_run kc rcv _ _ md HSF Hh Hlz)|].
intros c' (ms1 & -> & HS1 & HFR). cbn [ms_mem] in HFR.
destruct (SSF_regs kc rcv) as (Hregs & Hpc & Hrv).
eapply (SR_free_ret (EV (xvf vv)) (SSF kc rcv) ms1 md); [exact HS1 | exact Hrv | exact Hpc | rewrite Hregs; apply REGS_F_ra | rewrite ew_ra; exact Hret | exact Hh | exact Hlz |].
rewrite ew_ra. apply fast_leaf; [exact FC | exact HS1 | exact HFR].
Qed.
End l.
End e.
