(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput; the launch premises valid_launch and entry_launch_ok_va; the channel-reader premise of writev; the start-up stack layout (the strings above the random bytes, up to ed_top)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require Import AsanImgScan AsanImg AsanEntry AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require Import AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxSNodes FxSFam AsanRdErr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanUsageT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanCoNFT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanUsageT AsanCoNFT FxCarve AsanRdErrT AsanRdConvT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT.AsanUsage OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCoNFT.AsanCoNFDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCoNFT OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxCarve OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdErrT OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdConvT.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma uE_ladd_small : forall E a b, uE E a + uE E b < two64 -> uE E (ladd a b) = uE E a + uE E b.
Proof. intros E a b H. unfold uE. rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  apply Z.mod_small. pose proof (uE_range E a). pose proof (uE_range E b). unfold uE in *. lia. Qed.
Lemma uE_lsub_small : forall E a b, uE E b <= uE E a -> uE E (lsub a b) = uE E a - uE E b.
Proof. intros E a b H. rewrite u_lsub_mod. apply Z.mod_small. pose proof (uE_range E a). pose proof (uE_range E b). unfold two64 in *. lia. Qed.
Lemma RANDP16_eq : laddc RANDP16 (-16) = RANDP. Proof. vm_compute. reflexivity. Qed.
Lemma M1_frz : sm_frz M1 = [(ENVP, laddc (lscale 8 ENVC) 8); (P0, lsub TOPS P0)]. Proof. vm_compute. reflexivity. Qed.
Lemma M1_sp : sm_sp M1 = SP. Proof. vm_compute. reflexivity. Qed.
Lemma MMAIN_sp : sm_sp MMAIN = SP. Proof. vm_compute. reflexivity. Qed.

Section Lay.
Variables (sp brk0 mb : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk ASEGS brk0.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hid : valid_id (in_uid inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mb draw) inp.
Variables (olo ohi : Z).
Hypothesis HC : olo <= OFS sp <= ohi.
Variable E : valu.
Hypothesis Hag : agree 19 (E0 sp brk0 draw inp) E.

Let E0' := E0 sp brk0 draw inp.
(* 75d69e00: argv[0] is the lowest string byte, [ed_top - 8 - L] (AsanEntry.rel_str), above the random bytes *)
Let PP : Z := S0P draw inp.
Let L : Z := L0 inp.

#[using="Hag"] Lemma uag : forall l, lwf 19 l = true -> uE E l = uE E0' l.
Proof. LiaFast.lf_pins (fun (Hag : LiaFast.U) => LiaFast.u0). intros l Hl. unfold uE. rewrite (lden_agree 19 E0' E l Hl Hag). reflexivity. Qed.
#[using="brk0 draw Hag E0'"] Lemma uP0 : uE E P0 = PP.
Proof. LiaFast.lf_pins (fun (brk0 draw Hag E0' : LiaFast.U) => LiaFast.u0). rewrite uag by (vm_compute; reflexivity). exact (u_P0 sp brk0 draw inp). Qed.
#[using="sp brk0 draw Hva Hag E0'"] Lemma uL : uE E (lvar 11) = L.
Proof. LiaFast.lf_pins (fun (sp brk0 draw Hva Hag E0' : LiaFast.U) => LiaFast.u0). rewrite uag by (vm_compute; reflexivity). unfold uE. rewrite lden_lvar. exact (vz11 sp brk0 draw inp Hva). Qed.
#[using="brk0 mb draw inp Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0'"] Lemma uSP : uE E SP = usp sp.
Proof. LiaFast.lf_pins (fun (brk0 mb draw inp Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' : LiaFast.U) => LiaFast.u0). rewrite uag by (vm_compute; reflexivity). exact (u_SP sp brk0 mb draw inp Hsp Hva Hve Hvl Hlau olo ohi HC). Qed.
#[using="brk0 mb draw Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0'"] Lemma uRANDP : uE E RANDP = RP sp inp.
Proof. LiaFast.lf_pins (fun (brk0 mb draw Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' : LiaFast.U) => LiaFast.u0). rewrite uag by (vm_compute; reflexivity). exact (u_RANDP sp brk0 mb draw inp Hsp Hva Hve Hvl Hlau olo ohi HC). Qed.
(* [TOPS] (AsanRdErr) and [TOP] (AsanEntry) are the same lin, [4096 * v14] = ed_top *)
#[using="brk0 mb draw Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0'"] Lemma uTOPS : uE E TOPS = PTOP draw.
Proof. LiaFast.lf_pins (fun (brk0 mb draw Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' : LiaFast.U) => LiaFast.u0). rewrite uag by (vm_compute; reflexivity). exact (u_TOP sp brk0 mb draw inp Hsp Hva Hve Hvl Hlau olo ohi HC). Qed.
#[using="sp brk0 draw Hva Hag E0'"] Lemma uARGC : uE E (lvar 5) = AC inp.
Proof. LiaFast.lf_pins (fun (sp brk0 draw Hva Hag E0' : LiaFast.U) => LiaFast.u0). rewrite uag by (vm_compute; reflexivity). unfold uE. rewrite lden_lvar. exact (vz5 sp brk0 draw inp Hva). Qed.

(* the launch's numbers at 75d69e00: the random bytes sit at least 16 below argv[0] and argv[0]'s NUL with the
   exec name's NUL and the 8-byte slot fit below ed_top (AsanEntry.rel_str: [S0P = PTOP - 8 - LZ], [L0 + 2 <= LZ]);
   the block runs from sp to ed_top (AsanEntry.rel_top) *)
#[using="brk0 mb draw Hsp Hva Hve Hvl Hlau"] Lemma lay_nums : 0x7fff80000000 <= usp sp /\ 1 <= AC inp <= 1024 /\ 0 <= EC inp <= 256 /\ 0 <= L <= 131071 /\
  RP sp inp + 16 <= PP /\ PP + L + 2 <= PTOP draw - 8 /\ PTOP draw <= 0x800000000000 /\ PTOP draw mod 8 = 0 /\
  PTOP draw = usp sp + LB sp mb draw inp /\ PTOP draw - usp sp <= 2101782 /\ usp sp + 8 * AC inp + 8 * EC inp + 24 <= RP sp inp.
Proof. LiaFast.lf_pins (fun (brk0 mb draw Hsp Hva Hve Hvl Hlau : LiaFast.U) => LiaFast.u0).
  pose proof (usp_b sp brk0 mb draw inp Hsp Hvl Hlau) as (U1 & _).
  pose proof (argc_b inp Hva) as A1.
  pose proof (envc_b inp Hve) as A2.
  pose proof (valid_argv_str_len (in_argv inp) 0 Hva ltac:(unfold AC in A1; lia)) as Hl0.
  pose proof (rel_rp sp brk0 mb draw inp Hsp Hva Hve Hvl Hlau) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  pose proof (rel_top sp brk0 mb draw inp Hsp Hvl Hlau) as (T1 & T2 & T3 & T4 & T5).
  pose proof (rel_str sp brk0 mb draw inp Hsp Hva Hvl Hlau) as (Q1 & Q2 & Q3).
  assert (Hm : PTOP draw mod 8 = 0) by (rewrite T2; replace (4096 * TG draw) with ((512 * TG draw) * 8) by lia; apply Z_mod_mult).
  unfold PP, L, L0, AC, EC in *. repeat split; lia.
Qed.

(* [comment removed for export] *)
#[using="sp brk0 mb draw Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' PP L"] Theorem usage_facts : length (in_argv inp) <> 2%nat -> Forall (fact_ok E) FSU.
Proof. LiaFast.lf_pins (fun (sp brk0 mb draw Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' PP L : LiaFast.U) => LiaFast.u0).
  intros Hn2. pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11).
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
  - cbn [fact_ok FRZU]. fold (uE E (lsub TOPS (ladd P0 (lvar 11)))). rewrite uE_lsub_small; rewrite ?uTOPS, ?HPL; unfold PP in *; lia.
Qed.

(* [comment removed for export] *)
#[using="brk0 mb Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' PP L"] Theorem usage_ha3 : forall path0, HA3 (sarg path0 (nth 0 (in_argv inp) [])) E M1 A0 (m0 sp mb draw inp).
Proof. LiaFast.lf_pins (fun (brk0 mb Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' PP L : LiaFast.U) => LiaFast.u0).
  intros path0. pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11).
  assert (Hwe : wend PP L <= PTOP draw).
  { unfold wend. pose proof (Z.div_mod (PP + L) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (PP + L) 8 ltac:(lia)).
    pose proof (Z.div_mod (PTOP draw) 8 ltac:(lia)). lia. }
  assert (Hbyte : forall j, (j <= length (nth 0 (in_argv inp) []))%nat ->
            m0 sp mb draw inp (Z_to_bv 64 (PP + Z.of_nat j)) = Some (nth j (nth 0 (in_argv inp) [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
  { intros j Hj. pose proof (argv0_byte sp brk0 mb draw inp Hsp Hva Hvl Hlau j Hj) as X. fold PP in X.
    destruct (m0_in sp mb draw inp (Z_to_bv 64 (PP + Z.of_nat j))) as (b & Hb & _).
    - rewrite u_small64 by (unfold two64, L, L0 in *; lia). unfold PP, L, L0 in *. lia.
    - unfold rd1 in X. rewrite Hb in X. rewrite Hb. exact X. }
  split; [|constructor].
  apply Forall_cons; [|apply Forall_nil]. cbn [fst snd A0 sf_strs].
  split.
  - (* [comment removed for export] *)
    unfold cstr_ok. rewrite uP0, uL. refine (conj _ (conj _ (conj _ _))).
    + lia.
    + intros w Hw. split.
      * exists (P0, lsub TOPS P0). split; [rewrite M1_frz; right; left; reflexivity|]. cbn [fst snd].
        rewrite uP0, uE_lsub_small, uTOPS, uP0 by (rewrite uTOPS, uP0; lia). lia.
      * destruct (m0_in sp mb draw inp (Z_to_bv 64 w)) as (b & Hb & _); [|rewrite Hb; discriminate].
        rewrite u_small64 by (unfold two64; lia). unfold PP in *. lia.
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

(* argv[0] and argv[1] with their NULs and the exec name's NUL are all in [LZ] (StackLayout.launch_string_bytes) *)
#[using="H2 L L1"] Lemma lz2 : L + L1 + 3 <= LZ inp.
Proof. LiaFast.lf_pins (fun (H2 L L1 : LiaFast.U) => LiaFast.u0).
  unfold L, L1, L0, LZ, launch_string_bytes, flatten_strings.
  (* the case split on [in_argv inp] below would otherwise generalize the section's hypotheses and
     definitions that mention it, and the proof would use them *)
  clear - H2.
  destruct (in_argv inp) as [|a0 [|a1 [|a2 r]]] eqn:Hav; cbn in H2; try lia.
  cbn [flat_map nth]. rewrite !length_app. cbn [length]. lia.
Qed.

(* argv[1]'s address: the string base plus argv[0] and its NUL *)
#[using="brk0 mb draw Hsp Hva Hve Hvl Hlau H2 PP L A1 L1"] Lemma uA1 :
  bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) 1) = A1.
Proof. LiaFast.lf_pins (fun (brk0 mb draw Hsp Hva Hve Hvl Hlau H2 PP L A1 L1 : LiaFast.U) => LiaFast.u0).
  pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11).
  pose proof (s0p_eq sp brk0 mb draw inp Hva Hlau) as Hs.
  rewrite (cat_argv_ptr_offset (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) 1 ltac:(lia)), word_add_nat_Z2bv.
  rewrite (u_cat_string_base Sv48 inp mb sp brk0 draw Hlau).
  assert (Hf1 : total_arg_bytes_nat (firstn 1 (in_argv inp)) = (length (nth 0 (in_argv inp) []) + 1)%nat).
  { destruct (in_argv inp) as [|a0 r]; [cbn in H2; lia|]. cbn [firstn nth]. rewrite firstn_O. unfold total_arg_bytes_nat. cbn [fold_right]. lia. }
  rewrite Hf1. unfold A1, PP, L, L0, PTOP, LZ in *. rewrite uZ by lia. lia.
Qed.

#[using="brk0 mb draw Hsp Hva Hve Hvl Hlau Hag E0' H2 PP L A1 L1"] Lemma uPV2T : uE E PV = A1.
Proof. LiaFast.lf_pins (fun (brk0 mb draw Hsp Hva Hve Hvl Hlau Hag E0' H2 PP L A1 L1 : LiaFast.U) => LiaFast.u0).
  rewrite uag by (vm_compute; reflexivity). unfold uE, PV. rewrite lden_lvar. unfold E0'. unfold E0.
  change (List.nth (Pos.to_nat 8) (vals sp brk0 draw inp) (Z_to_bv 64 0)) with
    (if Nat.leb 2 (length (in_argv inp)) then cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) 1 else Z_to_bv 64 0).
  rewrite H2. cbn [Nat.leb]. exact uA1.
Qed.
#[using="brk0 mb draw Hsp Hva Hve Hvl Hlau H2 PP L A1 L1"] Lemma lay1_numsT : 0 <= L1 <= 131071 /\ A1 + L1 + 2 <= PTOP draw - 8.
Proof. LiaFast.lf_pins (fun (brk0 mb draw Hsp Hva Hve Hvl Hlau H2 PP L A1 L1 : LiaFast.U) => LiaFast.u0).
  pose proof lz2 as Z2.
  pose proof (valid_argv_str_len (in_argv inp) 1 Hva ltac:(lia)) as Hl1.
  pose proof (rel_str sp brk0 mb draw inp Hsp Hva Hvl Hlau) as (Q1 & Q2 & Q3).
  split; [unfold L1; lia|]. unfold A1, PP, L, L1 in *. lia.
Qed.

#[using="brk0 mb draw Hsp Hva Hve Hvl Hlau H2 PP L A1 L1"] Lemma argv1_byteT : forall j, (j <= length (nth 1 (in_argv inp) []))%nat ->
  m0 sp mb draw inp (Z_to_bv 64 (A1 + Z.of_nat j)) = Some (nth j (nth 1 (in_argv inp) [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (brk0 mb draw Hsp Hva Hve Hvl Hlau H2 PP L A1 L1 : LiaFast.U) => LiaFast.u0).
  intros j Hj. pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11). pose proof lay1_numsT as (M1' & M2').
  pose proof (read_argv_byte_k Sv48 ASEGS inp mb APH (Z_to_bv 64 (Z.of_N Asan.M.init_pc)) sp brk0 draw 1 j Hlau ltac:(lia) Hj) as Hr.
  rewrite word_add_nat_Z2bv, uA1 in Hr.
  assert (Hrd : rd1 ASEGS (m0 sp mb draw inp) (Z_to_bv 64 (A1 + Z.of_nat j)) = Some (nth j (nth 1 (in_argv inp) [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
  { rewrite rd1_m0_stk by (rewrite u_small64 by (unfold two64, A1, PP, L, L1 in *; lia); unfold A1, PP, L in *; lia).
    pose proof (rdn_rd1' (stk sp mb draw inp) (A1 + Z.of_nat j) 1 _ ltac:(unfold A1, PP, L in *; lia) ltac:(unfold two64, A1, PP, L, L1 in *; lia) Hr O _ eq_refl) as X.
    rewrite Z.add_0_r in X. exact X. }
  destruct (m0_in sp mb draw inp (Z_to_bv 64 (A1 + Z.of_nat j))) as (b & Hb & _).
  - rewrite u_small64 by (unfold two64, A1, PP, L, L1 in *; lia). unfold A1, PP, L, L1 in *. lia.
  - unfold rd1 in Hrd. rewrite Hb in Hrd. rewrite Hb. exact Hrd.
Qed.

(* [comment removed for export] *)
Let E1 : valu := upd E NNFT (Z_to_bv 64 L1).
#[using="Type"] Lemma ag1T : agree NNFT E E1. Proof. LiaFast.lf_pins LiaFast.u0. exact (agree_upd NNFT E _). Qed.
#[using="Type"] Lemma u1T : forall l, lwf 19 l = true -> uE E1 l = uE E l.
Proof. LiaFast.lf_pins LiaFast.u0. intros l Hl. unfold uE. rewrite (lden_agree NNFT E E1 l (lwf_mono 19 NNFT l ltac:(apply Pos.leb_le; vm_compute; reflexivity) Hl) ag1T). reflexivity. Qed.
#[using="sp brk0 mb draw Hsp Hva Hve Hvl Hlau PP L H2 A1"] Lemma uLPT : uE E1 LPNFT = L1.
Proof. LiaFast.lf_pins (fun (sp brk0 mb draw Hsp Hva Hve Hvl Hlau PP L H2 A1 : LiaFast.U) => LiaFast.u0). unfold uE, LPNFT, E1. rewrite lden_lvar. unfold upd. rewrite Pos.eqb_refl. pose proof lay1_numsT as (X & _). rewrite u_small64 by (unfold two64; lia). reflexivity. Qed.

#[using="sp brk0 mb draw Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' PP L H2 A1"] Theorem nf_factsT : Forall (fact_ok E1) FSNFT.
Proof. LiaFast.lf_pins (fun (sp brk0 mb draw Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' PP L H2 A1 : LiaFast.U) => LiaFast.u0).
  pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11). pose proof lay1_numsT as (K1 & K2).
  assert (HPV : uE E1 PV = A1) by (rewrite u1T by (vm_compute; reflexivity); exact uPV2T).
  assert (HPL : uE E1 (ladd PV LPNFT) = A1 + L1) by (rewrite uE_ladd_small; rewrite ?HPV, ?uLPT; [reflexivity | unfold two64, A1, PP, L in *; lia]).
  assert (HSP : uE E1 (sm_sp MMAIN) = usp sp) by (rewrite MMAIN_sp, u1T by (vm_compute; reflexivity); exact uSP).
  assert (HP0 : uE E1 P0 = PP) by (rewrite u1T by (vm_compute; reflexivity); exact uP0).
  assert (HTP : uE E1 TOPS = PTOP draw) by (rewrite u1T by (vm_compute; reflexivity); exact uTOPS).
  assert (HA5 : uE E1 (lvar 5) = AC inp) by (rewrite u1T by (vm_compute; reflexivity); exact uARGC).
  unfold FSNFT. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [fact_ok FARGC2N]. fold (uE E1 (lvar 5)). rewrite HA5. unfold AC. rewrite H2. lia.
  - cbn [fact_ok FV8N]. fold (uE E1 PV). rewrite HPV. unfold A1, PP, L in *. lia.
  - cbn [fact_ok FV8SPNT]. fold (uE E1 (lsub PV (sm_sp MMAIN))). rewrite uE_lsub_small; rewrite ?HPV, ?HSP; unfold A1, PP, L in *; lia.
  - cbn [fact_ok FLPNT]. fold (uE E1 LPNFT). rewrite uLPT. lia.
  - cbn [fact_ok FENDN0T]. fold (uE E1 (ladd PV LPNFT)). rewrite HPL. unfold A1, PP, L in *. lia.
  - cbn [fact_ok FENDN2T]. fold (uE E1 (lsub (ladd PV LPNFT) (sm_sp MMAIN))). rewrite uE_lsub_small; rewrite ?HPL, ?HSP; unfold A1, PP, L in *; lia.
  - cbn [fact_ok FRZNT]. fold (uE E1 (lsub TOPS (ladd PV LPNFT))). rewrite uE_lsub_small; rewrite ?HTP, ?HPL; unfold A1, PP, L in *; lia.
  - cbn [fact_ok FPV0N]. fold (uE E1 (lsub PV P0)). rewrite uE_lsub_small; rewrite ?HPV, ?HP0; unfold A1, PP, L in *; lia.
Qed.

#[using="brk0 mb Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' PP L H2 A1"] Theorem nf_ha3T : forall path0, HA3 (sarg path0 (nth 1 (in_argv inp) [])) E1 M1 (snd ANFT) (m0 sp mb draw inp).
Proof. LiaFast.lf_pins (fun (brk0 mb Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' PP L H2 A1 : LiaFast.U) => LiaFast.u0).
  intros path0. pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11). pose proof lay1_numsT as (K1 & K2).
  assert (HPV : uE E1 PV = A1) by (rewrite u1T by (vm_compute; reflexivity); exact uPV2T).
  assert (HP0 : uE E1 P0 = PP) by (rewrite u1T by (vm_compute; reflexivity); exact uP0).
  assert (HTP : uE E1 TOPS = PTOP draw) by (rewrite u1T by (vm_compute; reflexivity); exact uTOPS).
  assert (Hwe : wend A1 L1 <= PTOP draw).
  { unfold wend. pose proof (Z.div_mod (A1 + L1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (A1 + L1) 8 ltac:(lia)).
    pose proof (Z.div_mod (PTOP draw) 8 ltac:(lia)). lia. }
  split; [|constructor].
  apply Forall_cons; [|apply Forall_nil]. cbn [fst snd ANFT sf_strs].
  split.
  - unfold cstr_ok. rewrite HPV, uLPT. refine (conj _ (conj _ (conj _ _))).
    + lia.
    + intros w Hw. split.
      * exists (P0, lsub TOPS P0). split; [rewrite M1_frz; right; left; reflexivity|]. cbn [fst snd].
        rewrite HP0, uE_lsub_small, HTP, HP0 by (rewrite HTP, HP0; lia). unfold A1, PP, L in *. lia.
      * destruct (m0_in sp mb draw inp (Z_to_bv 64 w)) as (b & Hb & _); [|rewrite Hb; discriminate].
        rewrite u_small64 by (unfold two64; lia). unfold A1, PP, L in *. lia.
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
#[using="sp brk0 mb draw inp Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' PP L H2 A1 L1 Hdot"] Theorem rd_factsT : Forall (fact_ok E) FSRT.
Proof. LiaFast.lf_pins (fun (sp brk0 mb draw inp Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' PP L H2 A1 L1 Hdot : LiaFast.U) => LiaFast.u0).
  pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11). pose proof lay1_numsT as (K1 & K2).
  assert (HL1 : L1 = 1) by (unfold L1; rewrite Hdot; reflexivity).
  assert (HSP : uE E (sm_sp MMAIN) = usp sp) by (rewrite MMAIN_sp; exact uSP).
  unfold FSRT. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [fact_ok FARGC]. fold (uE E (lvar 5)). rewrite uARGC. unfold AC. rewrite H2. lia.
  - cbn [fact_ok FV8]. fold (uE E PV). rewrite uPV2T. unfold A1, PP, L in *. lia.
  - cbn [fact_ok FV8SPT]. fold (uE E (lsub PV (sm_sp MMAIN))). rewrite uE_lsub_small; rewrite ?uPV2T, ?HSP; unfold A1, PP, L in *; lia.
  - cbn [fact_ok FRND]. unfold SZR. fold (uE E (lsub TOPS PV)). rewrite uE_lsub_small; rewrite ?uTOPS, ?uPV2T; unfold A1, PP, L in *; lia.
Qed.
#[using="sp brk0 mb draw inp Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' PP L H2 A1 L1"] Lemma rd_p0T : uE E (fst FRZT) <= uE E PV.
Proof. LiaFast.lf_pins (fun (sp brk0 mb draw inp Hsp Hva Hve Hvl Hlau olo ohi HC Hag E0' PP L H2 A1 L1 : LiaFast.U) => LiaFast.u0).
  pose proof lay_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11). change (fst FRZT) with P0. rewrite uP0, uPV2T. unfold A1, PP, L in *. lia.
Qed.
#[using="brk0 mb Hsp Hva Hve Hvl Hlau Hag E0' PP L H2 A1 L1 Hdot"] Lemma rd_bytesT : m0 sp mb draw inp (Z_to_bv 64 (uE E PV)) = Some (Z_to_bv 8 46) /\ m0 sp mb draw inp (Z_to_bv 64 (uE E PV + 1)) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins (fun (brk0 mb Hsp Hva Hve Hvl Hlau Hag E0' PP L H2 A1 L1 Hdot : LiaFast.U) => LiaFast.u0).
  rewrite uPV2T. split.
  - pose proof (argv1_byteT 0 ltac:(rewrite Hdot; cbn; lia)) as X. rewrite Hdot in X. rewrite Z.add_0_r in X. exact X.
  - pose proof (argv1_byteT 1 ltac:(rewrite Hdot; cbn; lia)) as X. rewrite Hdot in X. exact X.
Qed.
End Argv1.
End Lay.
