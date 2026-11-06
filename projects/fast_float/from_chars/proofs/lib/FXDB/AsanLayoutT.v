(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec SeqExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg AsanAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChStart FxChSep FxWvC FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanImgScan AsanImg AsanEntry AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxSNodes FxSFam AsanRdErr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanUsageT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCoNFT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanUsageT AsanCoNFT FxCarve AsanRdErrT AsanRdConvT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageT.AsanUsage OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCoNFT.AsanCoNFDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCoNFT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxCarve OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdErrT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdConvT.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma uE_ladd_small : forall E a b, uE E a + uE E b < two64 -> uE E (ladd a b) = uE E a + uE E b.
Proof. intros E a b H. unfold uE. rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  apply Z.mod_small. pose proof (uE_range E a). pose proof (uE_range E b). unfold uE in *. lia. Qed.
Lemma uE_lsub_small : forall E a b, uE E b <= uE E a -> uE E (lsub a b) = uE E a - uE E b.
Proof. intros E a b H. rewrite u_lsub_mod. apply Z.mod_small. pose proof (uE_range E a). pose proof (uE_range E b). unfold two64 in *. lia. Qed.
Lemma RANDP16_eq : laddc RANDP16 (-16) = RANDP. Proof. vm_compute. reflexivity. Qed.
Lemma M1_frz : sm_frz M1 = [(ENVP, laddc (lscale 8 ENVC) 8); (P0, lsub RANDP P0)]. Proof. vm_compute. reflexivity. Qed.
Lemma M1_sp : sm_sp M1 = SP. Proof. vm_compute. reflexivity. Qed.
Lemma MMAIN_sp : sm_sp MMAIN = SP. Proof. vm_compute. reflexivity. Qed.

Section Lay.
Variables (sp brk0 mb : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk ASEGS brk0.
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hid : valid_id (in_uid inp).
Variables (olo ohi : Z).
Hypothesis HC : olo <= OFS sp <= ohi.
Variable E : valu.
Hypothesis Hag : agree 17 (E0 sp brk0 draw inp) E.

Let E0' := E0 sp brk0 draw inp.
Let PP : Z := usp sp + 8 * AC inp + 8 * EC inp + 184.
Let L : Z := L0 inp.

#[using="Hag"] Lemma uag : forall l, lwf 17 l = true -> uE E l = uE E0' l.
Proof. LiaFast.lf_pins (fun (Hag : LiaFast.U) => LiaFast.u0). intros l Hl. unfold uE. rewrite (lden_agree 17 E0' E l Hl Hag). reflexivity. Qed.
#[using="brk0 draw Hsp Hfit Hva Hve olo ohi HC Hag E0'"] Lemma uP0 : uE E P0 = PP.
Proof. LiaFast.lf_pins (fun (brk0 draw Hsp Hfit Hva Hve olo ohi HC Hag E0' : LiaFast.U) => LiaFast.u0). rewrite uag by (vm_compute; reflexivity). exact (u_P0 sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC). Qed.
#[using="sp brk0 draw Hva Hag E0'"] Lemma uL : uE E (lvar 11) = L.
Proof. LiaFast.lf_pins (fun (sp brk0 draw Hva Hag E0' : LiaFast.U) => LiaFast.u0). rewrite uag by (vm_compute; reflexivity). unfold uE. rewrite lden_lvar. exact (vz11 sp brk0 draw inp Hva). Qed.
#[using="brk0 draw inp Hsp Hfit Hva Hve olo ohi HC Hag E0'"] Lemma uSP : uE E SP = usp sp.
Proof. LiaFast.lf_pins (fun (brk0 draw inp Hsp Hfit Hva Hve olo ohi HC Hag E0' : LiaFast.U) => LiaFast.u0). rewrite uag by (vm_compute; reflexivity). exact (u_SP sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC). Qed.
#[using="brk0 draw Hsp Hfit Hva Hve olo ohi HC Hag E0'"] Lemma uRANDP : uE E RANDP = RP sp inp.
Proof. LiaFast.lf_pins (fun (brk0 draw Hsp Hfit Hva Hve olo ohi HC Hag E0' : LiaFast.U) => LiaFast.u0). rewrite uag by (vm_compute; reflexivity). exact (u_RANDP sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC). Qed.
#[using="sp brk0 draw Hva Hag E0'"] Lemma uARGC : uE E (lvar 5) = AC inp.
Proof. LiaFast.lf_pins (fun (sp brk0 draw Hva Hag E0' : LiaFast.U) => LiaFast.u0). rewrite uag by (vm_compute; reflexivity). unfold uE. rewrite lden_lvar. exact (vz5 sp brk0 draw inp Hva). Qed.

(* [comment removed for export] *)
#[using="draw Hsp Hfit Hva Hve"] Lemma lay_nums : 0x7fff80000000 <= usp sp /\ 1 <= AC inp <= 1024 /\ 0 <= EC inp <= 256 /\ 0 <= L <= 131071 /\
  PP + L + 1 <= RP sp inp /\ RP sp inp + 16 <= 0x800000000000 /\ RP sp inp mod 8 = 0 /\ RP sp inp - PP <= 2240000.
Proof. LiaFast.lf_pins (fun (draw Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  pose proof (usp_b sp inp Hsp Hfit Hva Hve) as (U1 & _).
  pose proof (argc_b inp Hva) as A1.
  pose proof (envc_b inp Hve) as A2.
  pose proof (valid_argv_str_len (in_argv inp) 0 Hva ltac:(unfold AC in A1; lia)) as Hl0.
  pose proof (rp_str sp draw inp Hsp Hfit Hva Hve) as Rs.
  pose proof (rp_b sp draw inp Hsp Hfit Hva Hve) as (R1 & R2 & R3).
  pose proof (blk_top sp draw inp Hsp Hfit Hva Hve) as Bt.
  pose proof (bsb_b sp draw inp Hva Hve) as Bb.
  unfold PP, L, L0, AC, EC in *. repeat split; lia.
Qed.

(* [comment removed for export] *)
#[using="sp brk0 draw Hsp Hfit Hva Hve olo ohi HC Hag E0' PP L"] Theorem usage_facts : length (in_argv inp) <> 2%nat -> Forall (fact_ok E) FSU.
Proof. LiaFast.lf_pins (fun (sp brk0 draw Hsp Hfit Hva Hve olo ohi HC Hag E0' PP L : LiaFast.U) => LiaFast.u0).
  intros Hn2. pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof (uE_range E (lvar 5)) as R5.
  assert (HPL : uE E (ladd P0 (lvar 11)) = PP + L) by (rewrite uE_ladd_small; rewrite uP0, uL; [reflexivity | unfold two64; lia]).
  assert (HSP : uE E (sm_sp M1) = usp sp) by (rewrite M1_sp; exact uSP).
  unfold FSU. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [fact_ok FARGC_U]. unfold branch_taken. rewrite lden_lconst. cbn.
    destruct (bv_eqb (lden E (lvar 5)) (Z_to_bv 64 2)) eqn:He; [|reflexivity].
    apply bv_eqb_eq in He. exfalso. apply Hn2. apply (f_equal bv_unsigned) in He. fold (uE E (lvar 5)) in He. rewrite uARGC in He.
    change (bv_unsigned (Z_to_bv 64 2)) with 2 in He. unfold AC in He. fold (in_argv inp) in He. lia.
  - cbn [fact_ok FEND0]. fold (uE E (ladd P0 (lvar 11))). rewrite HPL. unfold PP in *. lia.
  - cbn [fact_ok FEND1]. fold (uE E (lsub P0 (sm_sp M1))). rewrite uE_lsub_small; rewrite ?uP0, ?HSP; unfold PP in *; lia.
  - cbn [fact_ok FEND2]. fold (uE E (lsub (ladd P0 (lvar 11)) (sm_sp M1))). rewrite uE_lsub_small; rewrite ?HPL, ?HSP; unfold PP in *; lia.
  - cbn [fact_ok FRZU]. rewrite RANDP16_eq. fold (uE E (lsub RANDP (ladd P0 (lvar 11)))). rewrite uE_lsub_small; rewrite ?uRANDP, ?HPL; lia.
Qed.

(* [comment removed for export] *)
#[using="brk0 Hsp Hfit Hva Hve olo ohi HC Hag E0' PP L"] Theorem usage_ha3 : forall path0, HA3 (sarg path0 (nth 0 (in_argv inp) [])) E M1 A0 (m0 sp draw inp).
Proof. LiaFast.lf_pins (fun (brk0 Hsp Hfit Hva Hve olo ohi HC Hag E0' PP L : LiaFast.U) => LiaFast.u0).
  intros path0. pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  assert (Hwe : wend PP L <= RP sp inp).
  { unfold wend. pose proof (Z.div_mod (PP + L) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (PP + L) 8 ltac:(lia)).
    pose proof (Z.div_mod (RP sp inp) 8 ltac:(lia)). lia. }
  assert (Hbyte : forall j, (j <= length (nth 0 (in_argv inp) []))%nat ->
            m0 sp draw inp (Z_to_bv 64 (PP + Z.of_nat j)) = Some (nth j (nth 0 (in_argv inp) [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
  { intros j Hj. pose proof (argv0_byte sp draw inp Hsp Hfit Hva Hve j Hj) as X. fold PP in X.
    destruct (m0_in sp draw inp (Z_to_bv 64 (PP + Z.of_nat j))) as (b & Hb & _).
    - rewrite u_small64 by (unfold two64, L, L0 in *; lia).
      pose proof (rp_b sp draw inp Hsp Hfit Hva Hve) as (R1 & _). unfold PP, L, L0 in *. lia.
    - unfold rd1 in X. rewrite Hb in X. rewrite Hb. exact X. }
  split; [|constructor].
  apply Forall_cons; [|apply Forall_nil]. cbn [fst snd A0 sf_strs].
  split.
  - (* [comment removed for export] *)
    unfold cstr_ok. rewrite uP0, uL. refine (conj _ (conj _ (conj _ _))).
    + lia.
    + intros w Hw. split.
      * exists (P0, lsub RANDP P0). split; [rewrite M1_frz; right; left; reflexivity|]. cbn [fst snd].
        rewrite uP0, uE_lsub_small, uRANDP, uP0 by (rewrite uRANDP, uP0; lia). lia.
      * destruct (m0_in sp draw inp (Z_to_bv 64 w)) as (b & Hb & _); [|rewrite Hb; discriminate].
        rewrite u_small64 by (unfold two64; lia).
        pose proof (rp_b sp draw inp Hsp Hfit Hva Hve) as (R1 & _). unfold PP in *. lia.
    + intros k Hk. rewrite <- (Z2Nat.id k) by lia. rewrite (Hbyte (Z.to_nat k) ltac:(unfold L, L0 in *; lia)).
      eexists. split; [reflexivity|]. intros Hc.
      apply (argv0_nz inp Hva (Z.to_nat k) ltac:(unfold L, L0 in *; lia)).
      apply bv_eq. rewrite Hc. reflexivity.
    + replace (PP + L) with (PP + Z.of_nat (length (nth 0 (in_argv inp) []))) by (unfold L, L0; reflexivity).
      rewrite (Hbyte (length (nth 0 (in_argv inp) [])) ltac:(lia)). rewrite (argv0_nul inp). reflexivity.
  - (* [comment removed for export] *)
    unfold sbytes_ok. cbn [sarg]. rewrite uP0, uL. split; [unfold L, L0; reflexivity|].
    intros i Hi. rewrite <- (Z2Nat.id i) at 1 by lia. rewrite (Hbyte (Z.to_nat i) ltac:(unfold L, L0 in *; lia)).
    rewrite app_nth1 by (unfold L, L0 in *; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Section Argv1.
Hypothesis H2 : length (in_argv inp) = 2%nat.
Let A1 : Z := PP + L + 1.
Let L1 : Z := Z.of_nat (length (nth 1 (in_argv inp) [])).

#[using="brk0 draw Hsp Hfit Hva Hve Hag E0' H2 L1"] Lemma uPV2T : uE E PV = A1.
Proof. LiaFast.lf_pins (fun (brk0 draw Hsp Hfit Hva Hve Hag E0' H2 L1 : LiaFast.U) => LiaFast.u0).
  rewrite uag by (vm_compute; reflexivity). unfold uE, PV. rewrite lden_lvar. unfold E0'. unfold E0.
  change (List.nth (Pos.to_nat 8) (vals sp brk0 draw inp) (Z_to_bv 64 0)) with (if Nat.leb 2 (length (in_argv inp)) then cat_argv_ptr sp (in_argv inp) (in_envp inp) 1 else Z_to_bv 64 0).
  rewrite H2. cbn [Nat.leb].
  destruct Hsp as (Hs1 & Hs2 & _).
  rewrite (u_cat_argv_ptr APH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) Hva Hve Hs1 Hs2 1 ltac:(lia)).
  unfold cat_struct_size, auxv_size. destruct (in_argv inp) as [|a0 [|a1 r]] eqn:Hav; cbn in H2; try lia.
  cbn [firstn total_arg_bytes_nat fold_right]. unfold A1, PP, L, L0, usp, AC, EC. rewrite Hav. cbn [nth length]. lia.
Qed.
#[using="draw Hsp Hfit Hva Hve H2"] Lemma lay1_numsT : 0 <= L1 <= 131071 /\ A1 + L1 + 1 <= RP sp inp.
Proof. LiaFast.lf_pins (fun (draw Hsp Hfit Hva Hve H2 : LiaFast.U) => LiaFast.u0).
  pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof (valid_argv_str_len (in_argv inp) 1 Hva ltac:(lia)) as Hl1.
  split; [unfold L1; lia|].
  pose proof (usp_b sp inp Hsp Hfit Hva Hve) as (U1 & _).
  destruct Hva as (_ & Hta & _). destruct Hve as (_ & Hte & _). rewrite total_arg_bytes_Z in Hta, Hte.
  unfold RP, at_random_ptr. cbv zeta. rewrite word_add_nat. unfold nat_to_word.
  rewrite !length_flatten_strings. unfold auxv_size.
  set (len := (8 + (length (in_argv inp) + 1) * 8 + (length (in_envp inp) + 1) * 8 + 160 + total_arg_bytes_nat (in_argv inp) + total_arg_bytes_nat (in_envp inp))%nat).
  set (pad := Z.to_nat ((8 - Z.of_nat len mod 8) mod 8)).
  assert (Hp8 : (pad < 8)%nat) by (unfold pad; pose proof (Z.mod_pos_bound (8 - Z.of_nat len mod 8) 8 ltac:(lia)); lia).
  assert (Ha : (length (nth 0 (in_argv inp) []) + 1 + length (nth 1 (in_argv inp) []) + 1 <= total_arg_bytes_nat (in_argv inp))%nat).
  { destruct (in_argv inp) as [|a0 [|a1 r]] eqn:Hav; cbn in H2; try lia. cbn [nth total_arg_bytes_nat fold_right]. lia. }
  rewrite uZ; unfold A1, L1, PP, L, L0, len, AC, EC, usp in *; lia.
Qed.

#[using="Hsp Hfit Hva Hve H2 L1"] Lemma argv1_byteT : forall j, (j <= length (nth 1 (in_argv inp) []))%nat ->
  m0 sp draw inp (Z_to_bv 64 (A1 + Z.of_nat j)) = Some (nth j (nth 1 (in_argv inp) [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve H2 L1 : LiaFast.U) => LiaFast.u0).
  intros j Hj. pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). pose proof lay1_numsT as (M1' & M2').
  pose proof (rp_b sp draw inp Hsp Hfit Hva Hve) as (R1 & R2 & R3).
  pose proof (blk_top sp draw inp Hsp Hfit Hva Hve) as Bt.
  assert (Hb2 : usp sp + Z.of_nat (length (build_stack_bytes APH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw)) < 2 ^ 64).
  { unfold usp in *. lia. }
  pose proof (read_argv_byte_k APH ASEGS sp (in_argv inp) (in_envp inp) 1 j (in_uid inp) (in_hwcap inp) draw ltac:(lia) Hj Hb2) as Hr.
  destruct Hsp as (Hs1 & Hs2 & _).
  rewrite word_add_nat, (u_cat_argv_ptr APH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) Hva Hve Hs1 Hs2 1 ltac:(lia)) in Hr.
  assert (HA1 : bv_unsigned sp + Z.of_nat (cat_struct_size (in_argv inp) (in_envp inp) + total_arg_bytes_nat (firstn 1 (in_argv inp))) = A1).
  { unfold cat_struct_size, auxv_size. destruct (in_argv inp) as [|a0 [|a1 r]] eqn:Hav; cbn in H2; try lia.
    cbn [firstn total_arg_bytes_nat fold_right]. unfold A1, PP, L, L0, usp, AC, EC. rewrite Hav. cbn [nth length]. lia. }
  rewrite HA1 in Hr.
  assert (Hrd : rd1 ASEGS (m0 sp draw inp) (Z_to_bv 64 (A1 + Z.of_nat j)) = Some (nth j (nth 1 (in_argv inp) [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
  { rewrite rd1_m0_stk by (rewrite u_small64 by (unfold two64, A1, PP, L, L1 in *; lia); unfold A1, PP, usp in *; lia).
    pose proof (rdn_rd1' (stk sp draw inp) (A1 + Z.of_nat j) 1 _ ltac:(unfold A1, PP, L in *; lia) ltac:(unfold two64, A1, PP, L, L1 in *; lia) Hr O _ eq_refl) as X.
    rewrite Z.add_0_r in X. exact X. }
  destruct (m0_in sp draw inp (Z_to_bv 64 (A1 + Z.of_nat j))) as (b & Hb & _).
  - rewrite u_small64 by (unfold two64, A1, PP, L, L1 in *; lia). unfold A1, PP, L, L1, usp in *. lia.
  - unfold rd1 in Hrd. rewrite Hb in Hrd. rewrite Hb. exact Hrd.
Qed.

(* [comment removed for export] *)
Let E1 : valu := upd E NNFT (Z_to_bv 64 L1).
#[using="Type"] Lemma ag1T : agree NNFT E E1. Proof. LiaFast.lf_pins LiaFast.u0. exact (agree_upd NNFT E _). Qed.
#[using="Type"] Lemma u1T : forall l, lwf 17 l = true -> uE E1 l = uE E l.
Proof. LiaFast.lf_pins LiaFast.u0. intros l Hl. unfold uE. rewrite (lden_agree NNFT E E1 l (lwf_mono 17 NNFT l ltac:(apply Pos.leb_le; vm_compute; reflexivity) Hl) ag1T). reflexivity. Qed.
#[using="sp draw Hsp Hfit Hva Hve PP L H2 A1"] Lemma uLPT : uE E1 LPNFT = L1.
Proof. LiaFast.lf_pins (fun (sp draw Hsp Hfit Hva Hve PP L H2 A1 : LiaFast.U) => LiaFast.u0). unfold uE, LPNFT, E1. rewrite lden_lvar. unfold upd. rewrite Pos.eqb_refl. pose proof lay1_numsT as (X & _). rewrite u_small64 by (unfold two64; lia). reflexivity. Qed.

#[using="sp brk0 draw Hsp Hfit Hva Hve olo ohi HC Hag E0' PP L H2 A1"] Theorem nf_factsT : Forall (fact_ok E1) FSNFT.
Proof. LiaFast.lf_pins (fun (sp brk0 draw Hsp Hfit Hva Hve olo ohi HC Hag E0' PP L H2 A1 : LiaFast.U) => LiaFast.u0).
  pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). pose proof lay1_numsT as (K1 & K2).
  assert (HPV : uE E1 PV = A1) by (rewrite u1T by (vm_compute; reflexivity); exact uPV2T).
  assert (HPL : uE E1 (ladd PV LPNFT) = A1 + L1) by (rewrite uE_ladd_small; rewrite ?HPV, ?uLPT; [reflexivity | unfold two64, A1, PP, L in *; lia]).
  assert (HSP : uE E1 (sm_sp MMAIN) = usp sp) by (rewrite MMAIN_sp, u1T by (vm_compute; reflexivity); exact uSP).
  assert (HP0 : uE E1 P0 = PP) by (rewrite u1T by (vm_compute; reflexivity); exact uP0).
  assert (HRP : uE E1 RANDP = RP sp inp) by (rewrite u1T by (vm_compute; reflexivity); exact uRANDP).
  assert (HA5 : uE E1 (lvar 5) = AC inp) by (rewrite u1T by (vm_compute; reflexivity); exact uARGC).
  unfold FSNFT. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [fact_ok FARGC2N]. fold (uE E1 (lvar 5)). rewrite HA5. unfold AC. rewrite H2. lia.
  - cbn [fact_ok FV8N]. fold (uE E1 PV). rewrite HPV. unfold A1, PP, L in *. lia.
  - cbn [fact_ok FV8SPNT]. fold (uE E1 (lsub PV (sm_sp MMAIN))). rewrite uE_lsub_small; rewrite ?HPV, ?HSP; unfold A1, PP, L in *; lia.
  - cbn [fact_ok FLPNT]. fold (uE E1 LPNFT). rewrite uLPT. lia.
  - cbn [fact_ok FENDN0T]. fold (uE E1 (ladd PV LPNFT)). rewrite HPL. unfold A1, PP, L in *. lia.
  - cbn [fact_ok FENDN2T]. fold (uE E1 (lsub (ladd PV LPNFT) (sm_sp MMAIN))). rewrite uE_lsub_small; rewrite ?HPL, ?HSP; unfold A1, PP, L in *; lia.
  - cbn [fact_ok FRZNT]. rewrite RANDP16_eq. fold (uE E1 (lsub RANDP (ladd PV LPNFT))). rewrite uE_lsub_small; rewrite ?HRP, ?HPL; unfold A1, PP, L in *; lia.
  - cbn [fact_ok FPV0N]. fold (uE E1 (lsub PV P0)). rewrite uE_lsub_small; rewrite ?HPV, ?HP0; unfold A1, PP, L in *; lia.
Qed.

#[using="brk0 Hsp Hfit Hva Hve olo ohi HC Hag E0' PP L H2 A1"] Theorem nf_ha3T : forall path0, HA3 (sarg path0 (nth 1 (in_argv inp) [])) E1 M1 (snd ANFT) (m0 sp draw inp).
Proof. LiaFast.lf_pins (fun (brk0 Hsp Hfit Hva Hve olo ohi HC Hag E0' PP L H2 A1 : LiaFast.U) => LiaFast.u0).
  intros path0. pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). pose proof lay1_numsT as (K1 & K2).
  assert (HPV : uE E1 PV = A1) by (rewrite u1T by (vm_compute; reflexivity); exact uPV2T).
  assert (HP0 : uE E1 P0 = PP) by (rewrite u1T by (vm_compute; reflexivity); exact uP0).
  assert (HRP : uE E1 RANDP = RP sp inp) by (rewrite u1T by (vm_compute; reflexivity); exact uRANDP).
  assert (Hwe : wend A1 L1 <= RP sp inp).
  { unfold wend. pose proof (Z.div_mod (A1 + L1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (A1 + L1) 8 ltac:(lia)).
    pose proof (Z.div_mod (RP sp inp) 8 ltac:(lia)). lia. }
  split; [|constructor].
  apply Forall_cons; [|apply Forall_nil]. cbn [fst snd ANFT sf_strs].
  split.
  - unfold cstr_ok. rewrite HPV, uLPT. refine (conj _ (conj _ (conj _ _))).
    + lia.
    + intros w Hw. split.
      * exists (P0, lsub RANDP P0). split; [rewrite M1_frz; right; left; reflexivity|]. cbn [fst snd].
        rewrite HP0, uE_lsub_small, HRP, HP0 by (rewrite HRP, HP0; lia). unfold A1, PP, L in *. lia.
      * destruct (m0_in sp draw inp (Z_to_bv 64 w)) as (b & Hb & _); [|rewrite Hb; discriminate].
        rewrite u_small64 by (unfold two64; lia).
        pose proof (rp_b sp draw inp Hsp Hfit Hva Hve) as (R1 & _). unfold A1, PP, L in *. lia.
    + intros k Hk. rewrite <- (Z2Nat.id k) by lia. rewrite (argv1_byteT (Z.to_nat k) ltac:(unfold L1 in *; lia)).
      eexists. split; [reflexivity|]. intros Hc.
      destruct Hva as (_ & _ & _ & Hnz & _). rewrite Forall_forall in Hnz.
      assert (Hin : In (nth 1 (in_argv inp) []) (in_argv inp)) by (apply nth_In; lia).
      apply (Hnz _ Hin). rewrite app_nth1 in Hc by (unfold L1 in *; lia).
      assert (Hc' : nth (Z.to_nat k) (nth 1 (in_argv inp) []) (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite Hc; reflexivity).
      rewrite <- Hc'. apply nth_In. unfold L1 in *. lia.
    + replace (A1 + L1) with (A1 + Z.of_nat (length (nth 1 (in_argv inp) []))) by (unfold L1; reflexivity).
      rewrite (argv1_byteT (length (nth 1 (in_argv inp) [])) ltac:(lia)). rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - unfold sbytes_ok. cbn [sarg]. rewrite HPV, uLPT. split; [unfold L1; reflexivity|].
    intros i Hi. rewrite <- (Z2Nat.id i) at 1 by lia. rewrite (argv1_byteT (Z.to_nat i) ltac:(unfold L1 in *; lia)).
    rewrite app_nth1 by (unfold L1 in *; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Hypothesis Hdot : nth 1 (in_argv inp) [] = [Z_to_bv 8 46].
#[using="sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC Hag E0' PP L H2 A1 L1 Hdot"] Theorem rd_factsT : Forall (fact_ok E) FSRT.
Proof. LiaFast.lf_pins (fun (sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC Hag E0' PP L H2 A1 L1 Hdot : LiaFast.U) => LiaFast.u0).
  pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). pose proof lay1_numsT as (K1 & K2).
  assert (HL1 : L1 = 1) by (unfold L1; rewrite Hdot; reflexivity).
  assert (HSP : uE E (sm_sp MMAIN) = usp sp) by (rewrite MMAIN_sp; exact uSP).
  pose proof (rp_b sp draw inp Hsp Hfit Hva Hve) as (R1 & R2 & R3).
  assert (HR16 : uE E RANDP16 = RP sp inp + 16).
  { assert (Hq : RANDP16 = laddc RANDP 16) by (vm_compute; reflexivity). rewrite Hq.
    rewrite uE_laddc; [rewrite uRANDP; reflexivity | lia | rewrite uRANDP; unfold two64, PP, L in *; lia]. }
  unfold FSRT. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [fact_ok FARGC]. fold (uE E (lvar 5)). rewrite uARGC. unfold AC. rewrite H2. lia.
  - cbn [fact_ok FV8]. fold (uE E PV). rewrite uPV2T. unfold A1, PP, L in *. lia.
  - cbn [fact_ok FV8SPT]. fold (uE E (lsub PV (sm_sp MMAIN))). rewrite uE_lsub_small; rewrite ?uPV2T, ?HSP; unfold A1, PP, L in *; lia.
  - cbn [fact_ok FRND]. unfold SZR. fold (uE E (lsub RANDP16 PV)). rewrite uE_lsub_small; rewrite ?HR16, ?uPV2T; unfold A1, PP, L in *; lia.
Qed.
#[using="sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC Hag E0' PP L H2 A1 L1"] Lemma rd_p0T : uE E (fst FRZT) <= uE E PV.
Proof. LiaFast.lf_pins (fun (sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC Hag E0' PP L H2 A1 L1 : LiaFast.U) => LiaFast.u0).
  pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). change (fst FRZT) with P0. rewrite uP0, uPV2T. unfold A1, PP, L in *. lia.
Qed.
#[using="brk0 Hsp Hfit Hva Hve Hag E0' PP L H2 A1 L1 Hdot"] Lemma rd_bytesT : m0 sp draw inp (Z_to_bv 64 (uE E PV)) = Some (Z_to_bv 8 46) /\ m0 sp draw inp (Z_to_bv 64 (uE E PV + 1)) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins (fun (brk0 Hsp Hfit Hva Hve Hag E0' PP L H2 A1 L1 Hdot : LiaFast.U) => LiaFast.u0).
  rewrite uPV2T. split.
  - pose proof (argv1_byteT 0 ltac:(rewrite Hdot; cbn; lia)) as X. rewrite Hdot in X. rewrite Z.add_0_r in X. exact X.
  - pose proof (argv1_byteT 1 ltac:(rewrite Hdot; cbn; lia)) as X. rewrite Hdot in X. exact X.
Qed.
End Argv1.
End Lay.
(* [comment removed for export] *)
