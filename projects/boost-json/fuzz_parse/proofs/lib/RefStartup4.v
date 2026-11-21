(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  StartupTac ArgvEnv RefLayout RefImg RefStartupDefs RefMemcpyLib
 Ref_code_47284_47870 Ref_code_d9dac_da94c Ref_code_eacac_eb420 Ref_code_7126c_712a8 Ref_code_9c8c0_9c8d4 LibAmo.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Set Default Proof Using "All".

(* LPS 75d69e00: written explicitly over the ProcInput (was zQ statements + KReplay terms).
   STATEMENTS: the decoded old boost-json statements, retargeted (J_aux/J_lsm/D_libc/pn_w/
   argc_w/rnd_w/wrap_mem take inp; rnd_w is at_random_ptr .. (kb_rseq ..)); their constants are
   boost-json's own.  PROOFS: boost-beast's RefStartup4 translated per instruction (93 words
   used, 83 identical, 10 differing in immediates; code +0x72f54 / +0x72e7c / +0x1c768, libc
   data +0x79068, .init_array 0x7a128/0x7a178 -> 0xf1200/0xf1210 read from boost-json's ELF).
   fin_c9 (static constructors and libc's init loop) is stepped by hand against this binary's
   own instruction modules (two init_array entries, read from the ELF). *)

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Ltac OSSVerify.Proofs.boost_json.fuzz_parse.lib.StartupTac.peel ::=
  repeat first [ rewrite rdn_wbytes_out_Z by (len_simpl; lia)
               | rewrite rdn_wbytes_out by region_side
               | rewrite rdn_J_rseq_out by (unorm; lia) ].
#[local] Ltac OSSVerify.Proofs.boost_json.fuzz_parse.lib.StartupTac.ok_win HJ ::=
  apply store_ok_cmem_win;
  [ repeat first [ apply wfJ_wbytes | apply wfJ_J_rseq ]; exact HJ | region_side | region_side ].

Section CanaryFacts.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable rnd : EntryDraw.

  (* [comment removed for export] *)
    Lemma lez_rnd4a : (lez [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat] = bv_unsigned (Z_to_bv 64 (lez [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]))).
  Proof. symmetry. apply u_lez4. reflexivity.
  Qed.
  Lemma lez_rnd4b : (lez [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat] = bv_unsigned (Z_to_bv 64 (lez [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]))).
  Proof. symmetry. apply u_lez4. reflexivity.
  Qed.
  Lemma rd_guard8_gen : (forall (segs : list Segment) (D : word -> option byte) (g : Z) (l0 l1 : list byte), length l0 = 4%nat -> length l1 = 4%nat -> (0 <= g)%Z -> (g + 8 <= 2 ^ 64)%Z -> rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 g) l0) (Z_to_bv 64 (g + 4)) l1) (Z_to_bv 64 (g + 1)) [Z_to_bv 8 0]) (Z_to_bv 64 g) 8 = Some (@firstn byte 1 l0 ++ [Z_to_bv 8 0] ++ @skipn byte 2 l0 ++ l1)).
  Proof.
    intros segs D g l0 l1 L0 L1 G0 G8.
    change 8%nat with (1 + (1 + (2 + 4)))%nat.
    apply rdn_app.
    { rewrite rdn_wbytes_out_Z by (cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite rdn_wbytes_out_Z by (rewrite L1; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      eapply (SeqExec.rdn_firstn segs _ 4); [| lia]. rewrite <- L0. apply rdn_wbytes_hit.
      rewrite L0, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    rewrite word_add_nat, u_Z2bv by lia. change (Z.of_nat 1) with 1%Z.
    apply rdn_app.
    { change 1%nat with (length [Z_to_bv 8 0]). apply rdn_wbytes_hit.
      rewrite u_Z2bv by lia. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    rewrite word_add_nat, u_Z2bv by lia. replace (g + 1 + Z.of_nat 1)%Z with (g + 2)%Z by lia.
    apply rdn_app.
    { rewrite rdn_wbytes_out_Z by (cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite rdn_wbytes_out_Z by (rewrite L1; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      replace (Z_to_bv 64 (g + 2)) with (Z_to_bv 64 g + nat_to_word 2)%bv
        by (rewrite word_add_nat, u_Z2bv by lia; reflexivity).
      replace 2%nat with (4 - 2)%nat at 2 by reflexivity. rewrite <- L0.
      apply (SeqExec.rdn_skipn segs _ (length l0)); [| lia]. apply rdn_wbytes_hit.
      rewrite L0, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    rewrite word_add_nat, u_Z2bv by lia. replace (g + 2 + Z.of_nat 2)%Z with (g + 4)%Z by lia.
    rewrite rdn_wbytes_out_Z by (cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    rewrite <- L1. apply rdn_wbytes_hit. rewrite L1, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  Qed.
  Lemma rd_guard8 : (forall D : word -> option byte, rdn SEGS (wbytes (wbytes (wbytes D (Z_to_bv 64 1226488) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1226492) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1226489) [Z_to_bv 8 0]) (Z_to_bv 64 1226488) 8 = Some (canary_bytes rnd)).
  Proof.
    intros D.
    exact (rd_guard8_gen SEGS D 0x12b6f8 [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]
             eq_refl eq_refl ltac:(lia) ltac:(lia)).
  Qed.
  Lemma lez_canary : (lez (canary_bytes rnd) = bv_unsigned (canary_w rnd)).
  Proof.
    unfold canary_w. symmetry.
    pose proof (lez_bound_len (canary_bytes rnd) 8 eq_refl) as B. change (8 * Z.of_nat 8)%Z with 64%Z in B.
    apply u_Z2bv; lia.
  Qed.
End CanaryFacts.

(* A 4-byte read of a data-region cell an earlier store wrote (the amoadd.w counter in
   fin_c9); the data-side analogue of StartupTac.rd_hit8. *)
#[local] Ltac rd_hit4 :=
  addr_norm; rewrite rdn_cmem_data by region_side; peel;
  lazymatch goal with
  | |- rdn ?sg (wbytes _ ?a' ?bs) ?a _ = _ =>
      first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ];
      let Hh := fresh "Hh" in
      pose proof (rdn_wbytes_hit sg bs) as Hh; rewrite length_N_to_le_bytes in Hh;
      apply Hh; unorm; lia
  end.

Section P6.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable v : VaSize.
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable entry : word.
  Variable sp0 brk : word.
  Variable Jb : word -> option byte.
  Variable rnd : EntryDraw.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp0 brk mbase rnd) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd)) (only parsing).

    Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z.
  Proof. exact Hlo.
  Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z.
  Proof. exact Hhi.
  Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia.
  Qed.
  Lemma rnd_bounds : ((bv_unsigned sp0 <= bv_unsigned (rnd_w inp sp0))%Z /\ (bv_unsigned (rnd_w inp sp0) + 16 < 2 ^ 64)%Z /\ (bv_unsigned (rnd_w inp sp0) mod 8)%Z = 0%Z).
  Proof.
    pose proof (rnd_facts SEGS v inp mbase RPH entry sp0 brk rnd) as RF.
    repeat match type of RF with ?P -> _ =>
      let H := fresh in
      assert (H : P) by first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hsp_lo' | exact Hsp_hi' | exact Hal];
      specialize (RF H) end.
    destruct RF as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.
  Lemma rd_rnd : (forall (J D : word -> option byte) (j n : nat), (j + n <= 16)%nat -> rdn SEGS (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) J D) (Z_to_bv 64 (bv_unsigned (rnd_w inp sp0) + Z.of_nat j)) n = Some (@firstn byte n (@skipn byte j (rb rnd)))).
  Proof.
    intros J D j n Hjn.
    pose proof (rnd_facts SEGS v inp mbase RPH entry sp0 brk rnd) as RF.
    repeat match type of RF with ?P -> _ =>
      let H := fresh in
      assert (H : P) by first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hsp_lo' | exact Hsp_hi' | exact Hal];
      specialize (RF H) end.
    destruct RF as (A & B & C & D' & E).
    unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). unfold rb. apply E. exact Hjn.
  Qed.
  Lemma rd_rnd4a : (forall J D : word -> option byte, rdn SEGS (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) J D) (rnd_w inp sp0) 4 = Some [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]).
  Proof.
    intros J D. rewrite <- (firstn4_rb rnd).
    rewrite <- (Z_to_bv_bv_unsigned 64 (rnd_w inp sp0)) at 1.
    rewrite <- (Z.add_0_r (bv_unsigned (rnd_w inp sp0))). change 0%Z with (Z.of_nat 0).
    exact (rd_rnd J D 0 4 ltac:(lia)).
  Qed.
  Lemma rd_rnd4b : (forall J D : word -> option byte, rdn SEGS (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) J D) (Z_to_bv 64 (bv_unsigned (rnd_w inp sp0) + 4)) 4 = Some [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]).
  Proof.
    intros J D. rewrite <- (firstn4_skipn4_rb rnd). change 4%Z with (Z.of_nat 4) at 1.
    exact (rd_rnd J D 4 4 ltac:(lia)).
  Qed.
  Lemma rdn_addr : (forall (segs : list Segment) (m : word -> option byte) (a a' : word) (n : nat) (r : option (list byte)), rdn segs m a' n = r -> a = a' -> rdn segs m a n = r).
  Proof. intros; subst; reflexivity.
  Qed.

  Ltac RD_RNDa := first [ apply rd_rnd4a | eapply rdn_addr; [apply rd_rnd4a | symmetry; apply Z_to_bv_bv_unsigned] ].
  Ltac RD_RNDb := apply rd_rnd4b.
  Ltac RD_GUARD := rewrite rdn_cmem_data by region_side; apply rd_guard8.

  Lemma slli_argc : (v_slli (argc_w inp) 3 = Z_to_bv 64 (8 * Z.of_nat (length av))).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN inp Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.
  Lemma fin_c6 : (forall G : machine_state -> Prop,
                  bwd SEGS G
                  -> forall (regs : bvmap 5 word) (rom : word -> option byte) (s1v tid : word),
                      wfJ sp0 Jb
                      -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
                        -> getr regs 3 = Z_to_bv 64 67584
                          -> getr regs 4 = Z_to_bv 64 1095352
                            -> getr regs 19 = Z_to_bv 64 0
                              -> getr regs 20 = Z_to_bv 64 0
                                -> getr regs 21 = Z_to_bv 64 0
                                  -> getr regs 22 = Z_to_bv 64 0
                                    -> getr regs 23 = Z_to_bv 64 0
                                      -> getr regs 24 = Z_to_bv 64 0
                                        -> getr regs 25 = Z_to_bv 64 0
                                          -> getr regs 26 = Z_to_bv 64 0
                                            -> getr regs 27 = Z_to_bv 64 0
                                              -> (forall regs' : bvmap 5 word, getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) -> getr regs' 3 = Z_to_bv 64 67584 -> getr regs' 4 = Z_to_bv 64 1095352 -> getr regs' 19 = Z_to_bv 64 0 -> getr regs' 20 = Z_to_bv 64 0 -> getr regs' 21 = Z_to_bv 64 0 -> getr regs' 22 = Z_to_bv 64 0 -> getr regs' 23 = Z_to_bv 64 0 -> getr regs' 24 = Z_to_bv 64 0 -> getr regs' 25 = Z_to_bv 64 0 -> getr regs' 26 = Z_to_bv 64 0 -> getr regs' 27 = Z_to_bv 64 0 -> regs_agree (fun r : reg => In r [1; 2; 10; 11; 12; 13; 14; 15]) regs regs' -> G (mkst regs' (892616 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892616))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1226464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226480) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226472) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1227104) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1227112) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1095368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1095344) (word_to_le_bytes 8 (Z_to_bv 64 1095368))) (Z_to_bv 64 1095152) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1227080) [Z_to_bv 8 1]) (Z_to_bv 64 1095192) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1095184) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1095304) (word_to_le_bytes 8 (Z_to_bv 64 1227136))) (Z_to_bv 64 1095272) (word_to_le_bytes 8 (Z_to_bv 64 1095272))) (Z_to_bv 64 1095160) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095168) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226488) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1226492) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1226489) [Z_to_bv 8 0]) (Z_to_bv 64 1095336) (word_to_le_bytes 8 (canary_w rnd)))) rom))
                                                -> G (mkst regs (892608 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1226464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226480) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226472) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1227104) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1227112) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1095368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1095344) (word_to_le_bytes 8 (Z_to_bv 64 1095368))) (Z_to_bv 64 1095152) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1227080) [Z_to_bv 8 1]) (Z_to_bv 64 1095192) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1095184) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1095304) (word_to_le_bytes 8 (Z_to_bv 64 1227136))) (Z_to_bv 64 1095272) (word_to_le_bytes 8 (Z_to_bv 64 1095272))) (Z_to_bv 64 1095160) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095168) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095176) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_d9ec0 D_d9ec0 (word_to_le_bytes 8 (rnd_w inp sp0)) (rnd_w inp sp0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_d9ec4 D_d9ec4.  (* [comment removed for export] *)
      sv F_da380 D_da380 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_da384 D_da384 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 892616) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_da388 D_da388 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_da38c D_da38c ((rnd_w inp sp0)).  (* [comment removed for export] *)
      sn F_da390 D_da390.  (* [comment removed for export] *)
      ld_step F_da394 D_da394 (word_to_le_bytes 8 (Z_to_bv 64 1226488)) (Z_to_bv 64 1226488) ltac:(rd_img img_f8770_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_da398 D_da398.  (* [comment removed for export] *)
      sn F_da39c D_da39c.  (* [comment removed for export] *)
      stepiv F_eada8 D_eada8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_eadac D_eadac ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_eaebc D_eaebc.  (* [comment removed for export] *)
      sn F_eaec0 D_eaec0.  (* [comment removed for export] *)
      stepb_ft F_eaec4 D_eaec4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_eaec8 D_eaec8.  (* [comment removed for export] *)
      stepb_tk F_eaecc D_eaecc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_eaf04 D_eaf04.  (* [comment removed for export] *)
      stepb_ft F_eaf08 D_eaf08 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_eaf0c D_eaf0c [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] (Z_to_bv 64 (bytes_le_to_Z [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3])) ltac:(RD_RNDa) ltac:(apply lez_rnd4a).  (* [comment removed for export] *)
      ld_step F_eaf10 D_eaf10 [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7] (Z_to_bv 64 (bytes_le_to_Z [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7])) ltac:(RD_RNDb) ltac:(apply lez_rnd4b).  (* [comment removed for export] *)
      stw F_eaf14 D_eaf14 (Z_to_bv 64 1226488) (LWv [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (sw_bytes_LWv [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] eq_refl).
      stw F_eaf18 D_eaf18 (Z_to_bv 64 1226492) (LWv [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (sw_bytes_LWv [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7] eq_refl).
      sn F_eaf1c D_eaf1c.  (* [comment removed for export] *)
      sv F_eaf20 D_eaf20 (Z_to_bv 64 (bv_unsigned (rnd_w inp sp0) + 8)).  (* [comment removed for export] *)
      sn F_eaf24 D_eaf24.  (* [comment removed for export] *)
      stepb_tk F_eaf28 D_eaf28 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_eb168 D_eb168.  (* [comment removed for export] *)
      stepb_ft F_eb16c D_eb16c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_eb170 D_eb170.  (* [comment removed for export] *)
      stepb_ft F_eb174 D_eb174 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_eb178 D_eb178 (0xda3a0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_da3a0 D_da3a0.  (* [comment removed for export] *)
      sn F_da3bc D_da3bc.  (* [comment removed for export] *)
      ld_step F_da3c0 D_da3c0 (word_to_le_bytes 8 (Z_to_bv 64 1226488)) (Z_to_bv 64 1226488) ltac:(rd_img img_f8770_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_da3c4 D_da3c4 (Z_to_bv 64 1226489) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_da3c8 D_da3c8 (canary_bytes rnd) (canary_w rnd) ltac:(RD_GUARD) ltac:(apply lez_canary).  (* [comment removed for export] *)
      sn F_da3cc D_da3cc.  (* [comment removed for export] *)
      stw F_da3d0 D_da3d0 (Z_to_bv 64 1095336) (canary_w rnd) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_da3d4 D_da3d4 (word_to_le_bytes 8 (Z_to_bv 64 892616)) (Z_to_bv 64 892616) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_da3d8 D_da3d8 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_da3dc D_da3dc (0xd9ec8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
  Lemma fin_c7 : (forall G : machine_state -> Prop,
                  bwd SEGS G
                  -> forall (regs : bvmap 5 word) (rom : word -> option byte) (s1v tid : word),
                      wfJ sp0 Jb
                      -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
                        -> getr regs 3 = Z_to_bv 64 67584
                          -> getr regs 4 = Z_to_bv 64 1095352
                            -> getr regs 19 = Z_to_bv 64 0
                              -> getr regs 20 = Z_to_bv 64 0
                                -> getr regs 21 = Z_to_bv 64 0
                                  -> getr regs 22 = Z_to_bv 64 0
                                    -> getr regs 23 = Z_to_bv 64 0
                                      -> getr regs 24 = Z_to_bv 64 0
                                        -> getr regs 25 = Z_to_bv 64 0
                                          -> getr regs 26 = Z_to_bv 64 0
                                            -> getr regs 27 = Z_to_bv 64 0
                                              -> (forall regs' : bvmap 5 word, getr regs' 1 = Z_to_bv 64 0 -> getr regs' 2 = sp0 -> getr regs' 3 = Z_to_bv 64 67584 -> getr regs' 4 = Z_to_bv 64 1095352 -> getr regs' 8 = Z_to_bv 64 0 -> getr regs' 9 = Z_to_bv 64 0 -> getr regs' 10 = Z_to_bv 64 291792 -> getr regs' 11 = argc_w inp -> getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 8) -> getr regs' 18 = Z_to_bv 64 0 -> getr regs' 19 = Z_to_bv 64 0 -> getr regs' 20 = Z_to_bv 64 0 -> getr regs' 21 = Z_to_bv 64 0 -> getr regs' 22 = Z_to_bv 64 0 -> getr regs' 23 = Z_to_bv 64 0 -> getr regs' 24 = Z_to_bv 64 0 -> getr regs' 25 = Z_to_bv 64 0 -> getr regs' 26 = Z_to_bv 64 0 -> getr regs' 27 = Z_to_bv 64 0 -> regs_agree (fun r : reg => In r [1; 2; 6; 8; 9; 10; 11; 12; 18]) regs regs' -> G (mkst regs' (893064 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892616))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1226464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226480) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226472) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1227104) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1227112) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1095368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1095344) (word_to_le_bytes 8 (Z_to_bv 64 1095368))) (Z_to_bv 64 1095152) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1227080) [Z_to_bv 8 1]) (Z_to_bv 64 1095192) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1095184) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1095304) (word_to_le_bytes 8 (Z_to_bv 64 1227136))) (Z_to_bv 64 1095272) (word_to_le_bytes 8 (Z_to_bv 64 1095272))) (Z_to_bv 64 1095160) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095168) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226488) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1226492) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1226489) [Z_to_bv 8 0]) (Z_to_bv 64 1095336) (word_to_le_bytes 8 (canary_w rnd)))) rom))
                                                -> G (mkst regs (892616 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892616))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1226464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226480) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226472) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1227104) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1227112) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1095368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1095344) (word_to_le_bytes 8 (Z_to_bv 64 1095368))) (Z_to_bv 64 1095152) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1227080) [Z_to_bv 8 1]) (Z_to_bv 64 1095192) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1095184) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1095304) (word_to_le_bytes 8 (Z_to_bv 64 1227136))) (Z_to_bv 64 1095272) (word_to_le_bytes 8 (Z_to_bv 64 1095272))) (Z_to_bv 64 1095160) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095168) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226488) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1226492) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1226489) [Z_to_bv 8 0]) (Z_to_bv 64 1095336) (word_to_le_bytes 8 (canary_w rnd)))) rom)).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_d9ec8 D_d9ec8 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_d9ecc D_d9ecc (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_d9ed0 D_d9ed0 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_d9ed4 D_d9ed4 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_d9ed8 D_d9ed8 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_d9edc D_d9edc ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_d9ee0 D_d9ee0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_d9ee4 D_d9ee4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_d9fc4 D_d9fc4 (word_to_le_bytes 8 (Z_to_bv 64 893020)) (Z_to_bv 64 893020) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_d9fc8 D_d9fc8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_d9fcc D_d9fcc (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_d9fd0 D_d9fd0 (word_to_le_bytes 8 (Z_to_bv 64 291792)) (Z_to_bv 64 291792) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_d9fd4 D_d9fd4 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_d9fd8 D_d9fd8 (0xda05c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_da05c D_da05c.  (* [comment removed for export] *)
      sn F_da060 D_da060.  (* [comment removed for export] *)
      sn F_da064 D_da064.  (* [comment removed for export] *)
      sv F_da068 D_da068 (argc_w inp).  (* [comment removed for export] *)
      sv F_da06c D_da06c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_da070 D_da070 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_da074 D_da074 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_da078 D_da078 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_da07c D_da07c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_da080 D_da080 (sp0).  (* [comment removed for export] *)
      stepret F_da084 D_da084 (0xda088 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
  Lemma fin_c8 : (forall G : machine_state -> Prop,
                  bwd SEGS G
                  -> forall (regs : bvmap 5 word) (rom : word -> option byte) (s1v tid : word),
                      wfJ sp0 Jb
                      -> getr regs 1 = Z_to_bv 64 0
                        -> getr regs 2 = sp0
                          -> getr regs 3 = Z_to_bv 64 67584
                            -> getr regs 4 = Z_to_bv 64 1095352
                              -> getr regs 8 = Z_to_bv 64 0
                                -> getr regs 9 = Z_to_bv 64 0
                                  -> getr regs 10 = Z_to_bv 64 291792
                                    -> getr regs 11 = argc_w inp
                                      -> getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 8)
                                        -> getr regs 18 = Z_to_bv 64 0
                                          -> getr regs 19 = Z_to_bv 64 0
                                            -> getr regs 20 = Z_to_bv 64 0
                                              -> getr regs 21 = Z_to_bv 64 0
                                                -> getr regs 22 = Z_to_bv 64 0
                                                  -> getr regs 23 = Z_to_bv 64 0
                                                    -> getr regs 24 = Z_to_bv 64 0
                                                      -> getr regs 25 = Z_to_bv 64 0
                                                        -> getr regs 26 = Z_to_bv 64 0
                                                          -> getr regs 27 = Z_to_bv 64 0
                                                            -> (forall regs' : bvmap 5 word, getr regs' 1 = Z_to_bv 64 892940 -> getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) -> getr regs' 3 = Z_to_bv 64 67584 -> getr regs' 4 = Z_to_bv 64 1095352 -> getr regs' 8 = Z_to_bv 64 987664 -> getr regs' 9 = Z_to_bv 64 987648 -> getr regs' 18 = Z_to_bv 64 291792 -> getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) -> getr regs' 20 = Z_to_bv 64 0 -> getr regs' 21 = Z_to_bv 64 0 -> getr regs' 22 = Z_to_bv 64 0 -> getr regs' 23 = Z_to_bv 64 0 -> getr regs' 24 = Z_to_bv 64 0 -> getr regs' 25 = Z_to_bv 64 0 -> getr regs' 26 = Z_to_bv 64 0 -> getr regs' 27 = Z_to_bv 64 0 -> regs_agree (fun r : reg => In r [1; 2; 8; 9; 10; 11; 18; 19]) regs regs' -> G (mkst regs' (291532 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892616))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 893116))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1226464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226480) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226472) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1227104) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1227112) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1095368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1095344) (word_to_le_bytes 8 (Z_to_bv 64 1095368))) (Z_to_bv 64 1095152) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1227080) [Z_to_bv 8 1]) (Z_to_bv 64 1095192) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1095184) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1095304) (word_to_le_bytes 8 (Z_to_bv 64 1227136))) (Z_to_bv 64 1095272) (word_to_le_bytes 8 (Z_to_bv 64 1095272))) (Z_to_bv 64 1095160) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095168) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226488) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1226492) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1226489) [Z_to_bv 8 0]) (Z_to_bv 64 1095336) (word_to_le_bytes 8 (canary_w rnd)))) rom))
                                                              -> G (mkst regs (893064 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892616))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1226464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226480) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226472) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1227104) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1227112) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1095368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1095344) (word_to_le_bytes 8 (Z_to_bv 64 1095368))) (Z_to_bv 64 1095152) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1227080) [Z_to_bv 8 1]) (Z_to_bv 64 1095192) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1095184) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1095304) (word_to_le_bytes 8 (Z_to_bv 64 1227136))) (Z_to_bv 64 1095272) (word_to_le_bytes 8 (Z_to_bv 64 1095272))) (Z_to_bv 64 1095160) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095168) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226488) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1226492) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1226489) [Z_to_bv 8 0]) (Z_to_bv 64 1095336) (word_to_le_bytes 8 (canary_w rnd)))) rom)).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_da088 D_da088 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_da08c D_da08c (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_da090 D_da090 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_da094 D_da094 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_da098 D_da098 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_da09c D_da09c (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_da0a0 D_da0a0 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_da0a4 D_da0a4 (argc_w inp).  (* [comment removed for export] *)
      sn F_da0a8 D_da0a8.  (* [comment removed for export] *)
      stepiv F_da0ac D_da0ac (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_da0b0 D_da0b0 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_da0b4 D_da0b4 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_da0b8 D_da0b8.  (* [comment removed for export] *)
      sv F_d9fdc D_d9fdc (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_d9fe0 D_d9fe0 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 893116) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_d9fe4 D_d9fe4 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_d9fe8 D_d9fe8 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_d9fec D_d9fec.  (* [comment removed for export] *)
      stepret F_d9dac D_d9dac (0xd9ff0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_d9ff0 D_d9ff0.  (* [comment removed for export] *)
      sn F_d9ff4 D_d9ff4.  (* [comment removed for export] *)
      ld_step F_d9ff8 D_d9ff8 (word_to_le_bytes 8 (Z_to_bv 64 987664)) (Z_to_bv 64 987664) ltac:(rd_img img_f8790_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_d9ffc D_d9ffc (word_to_le_bytes 8 (Z_to_bv 64 987648)) (Z_to_bv 64 987648) ltac:(rd_img img_f8798_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_da000 D_da000 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_da004 D_da004 (word_to_le_bytes 8 (Z_to_bv 64 291532)) (Z_to_bv 64 291532) ltac:(rd_img img_f1200_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_da008 D_da008 (0x472cc : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
  (* fin_c9: both static constructors and libc's init loop, 0x472cc -> main 0x473d0, stepped by
     hand against this binary's own code (init_array has two entries, read from the ELF);
     the statement is the decoded old one, retargeted onto inp. *)
  Lemma fin_c9 : (forall G : machine_state -> Prop,
                  bwd SEGS G
                  -> forall (regs : bvmap 5 word) (rom : word -> option byte) (s1v tid : word),
                      wfJ sp0 Jb
                      -> getr regs 1 = Z_to_bv 64 892940
                        -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80)
                          -> getr regs 3 = Z_to_bv 64 67584
                            -> getr regs 4 = Z_to_bv 64 1095352
                              -> getr regs 8 = Z_to_bv 64 987664
                                -> getr regs 9 = Z_to_bv 64 987648
                                  -> getr regs 18 = Z_to_bv 64 291792
                                    -> getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))
                                      -> getr regs 20 = Z_to_bv 64 0
                                        -> getr regs 21 = Z_to_bv 64 0
                                          -> getr regs 22 = Z_to_bv 64 0
                                            -> getr regs 23 = Z_to_bv 64 0
                                              -> getr regs 24 = Z_to_bv 64 0
                                                -> getr regs 25 = Z_to_bv 64 0
                                                  -> getr regs 26 = Z_to_bv 64 0
                                                    -> getr regs 27 = Z_to_bv 64 0
                                                      -> (forall regs' : bvmap 5 word,
                                                           getr regs' 1 = Z_to_bv 64 893132
                                                           -> getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48)
                                                             -> getr regs' 3 = Z_to_bv 64 67584
                                                               -> getr regs' 4 = Z_to_bv 64 1095352
                                                                 -> getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8)
                                                                   -> getr regs' 9 = argc_w inp
                                                                     -> getr regs' 10 = argc_w inp
                                                                       -> getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8)
                                                                         -> getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))
                                                                           -> getr regs' 18 = Z_to_bv 64 291792
                                                                             -> getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))
                                                                               -> getr regs' 20 = Z_to_bv 64 0
                                                                                 -> getr regs' 21 = Z_to_bv 64 0
                                                                                   -> getr regs' 22 = Z_to_bv 64 0
                                                                                     -> getr regs' 23 = Z_to_bv 64 0
                                                                                       -> getr regs' 24 = Z_to_bv 64 0
                                                                                         -> getr regs' 25 = Z_to_bv 64 0 -> getr regs' 26 = Z_to_bv 64 0 -> getr regs' 27 = Z_to_bv 64 0 -> regs_agree (fun r : reg => In r [1; 2; 8; 9; 10; 11; 12]) regs regs' -> G (mkst regs' (291792 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892616))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 893116))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 892940))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 987664))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 892940))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 987664))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1226464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226480) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226472) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1227104) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1227112) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1095368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1095344) (word_to_le_bytes 8 (Z_to_bv 64 1095368))) (Z_to_bv 64 1095152) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1227080) [Z_to_bv 8 1]) (Z_to_bv 64 1095192) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1095184) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1095304) (word_to_le_bytes 8 (Z_to_bv 64 1227136))) (Z_to_bv 64 1095272) (word_to_le_bytes 8 (Z_to_bv 64 1095272))) (Z_to_bv 64 1095160) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095168) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226488) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1226492) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1226489) [Z_to_bv 8 0]) (Z_to_bv 64 1095336) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 1022896) [Z_to_bv 8 1]) (Z_to_bv 64 1089256) (word_to_le_bytes 4 (Z_to_bv 64 1))) (Z_to_bv 64 1088608) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 1089256) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1088612) (word_to_le_bytes 4 (Z_to_bv 64 1))) (Z_to_bv 64 1089256) (word_to_le_bytes 4 (Z_to_bv 64 3))) (Z_to_bv 64 1088616) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom))
                                                        -> G (mkst regs (291532 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892608))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1227080))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 892616))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 893116))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1226464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226480) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226472) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1227104) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1227112) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1095368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1095344) (word_to_le_bytes 8 (Z_to_bv 64 1095368))) (Z_to_bv 64 1095152) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1227080) [Z_to_bv 8 1]) (Z_to_bv 64 1095192) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1095184) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1095304) (word_to_le_bytes 8 (Z_to_bv 64 1227136))) (Z_to_bv 64 1095272) (word_to_le_bytes 8 (Z_to_bv 64 1095272))) (Z_to_bv 64 1095160) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095168) (word_to_le_bytes 8 (Z_to_bv 64 1095152))) (Z_to_bv 64 1095176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1226488) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1226492) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1226489) [Z_to_bv 8 0]) (Z_to_bv 64 1095336) (word_to_le_bytes 8 (canary_w rnd)))) rom)).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { (* init_array[0] = frame_dummy (0x472cc), entered by fin_c8's jalr; ra = 0xda00c *)
      sv F_472cc D_472cc (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_472d0 D_472d0 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 892940) ltac:(ok_win HJ).
      stw F_472d4 D_472d4 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 987664) ltac:(ok_win HJ).
      sv F_472d8 D_472d8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      sn F_472dc D_472dc.
      sn F_472e0 D_472e0.
      lb_step F_472e4 D_472e4 (Z_to_bv 8 0) ltac:(rd_img img_f9bb0_1).
      sn F_472e8 D_472e8.
      stepb_tk F_472ec D_472ec ltac:(pin; cond_compute).
      sn F_472f8 D_472f8.
      sn F_472fc D_472fc.
      sn F_47300 D_47300.
      stw F_47304 D_47304 (Z_to_bv 64 1022896) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_47308 D_47308.
      ld_step F_4730c D_4730c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_f8638_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_47310 D_47310 ltac:(pin; cond_compute).
      ld_step F_47330 D_47330 (word_to_le_bytes 8 (Z_to_bv 64 892940)) (Z_to_bv 64 892940) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_47334 D_47334 (word_to_le_bytes 8 (Z_to_bv 64 987664)) (Z_to_bv 64 987664) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_47338 D_47338 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_4733c D_4733c (0xda00c : word) ltac:(pin; first [reflexivity | bveq]).
      (* __libc_start_init's loop: x9 := 0xf1208 <> x8 = 0xf1210, load init_array[1] = 0x7126c *)
      sn F_da00c D_da00c.
      stepb_tk F_da010 D_da010 ltac:(pin; cond_compute).
      ld_step F_da004 D_da004 (word_to_le_bytes 8 (Z_to_bv 64 463468)) (Z_to_bv 64 463468) ltac:(rd_img img_f1208_8) ltac:(apply bytes_le_to_Z_8).
      stepjr F_da008 D_da008 (0x7126c : word) ltac:(gres; pin; first [reflexivity | bveq]).
      (* init_array[1] (0x7126c): three calls of 0x9c8c0 = amoadd.w x10, 1, (0x109ee8) *)
      sv F_7126c D_7126c (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_71270 D_71270 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 892940) ltac:(ok_win HJ).
      stw F_71274 D_71274 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 987664) ltac:(ok_win HJ).
      sn F_71278 D_71278.
      sn F_9c8c0 D_9c8c0.
      sn F_9c8c4 D_9c8c4.
      sn F_9c8c8 D_9c8c8.
      amo_step F_9c8cc D_9c8cc (Z_to_bv 64 1089256) (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 1)
        ltac:(rd_img img_109ee8_4) ltac:(vm_compute; reflexivity) ltac:(ok_data).
      stepret F_9c8d0 D_9c8d0 (0x7127c : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_7127c D_7127c.
      sn F_71280 D_71280.
      stw F_71284 D_71284 (Z_to_bv 64 1088608) (Z_to_bv 64 0) ltac:(ok_data).
      sn F_71288 D_71288.
      sn F_9c8c0 D_9c8c0.
      sn F_9c8c4 D_9c8c4.
      sn F_9c8c8 D_9c8c8.
      amo_step F_9c8cc D_9c8cc (Z_to_bv 64 1089256) (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 2)
        ltac:(rd_hit4) ltac:(vm_compute; reflexivity) ltac:(ok_data).
      stepret F_9c8d0 D_9c8d0 (0x7128c : word) ltac:(pin; first [reflexivity | bveq]).
      stw F_7128c D_7128c (Z_to_bv 64 1088612) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_71290 D_71290.
      sn F_9c8c0 D_9c8c0.
      sn F_9c8c4 D_9c8c4.
      sn F_9c8c8 D_9c8c8.
      amo_step F_9c8cc D_9c8cc (Z_to_bv 64 1089256) (word_to_le_bytes 4 (Z_to_bv 64 2)) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 3)
        ltac:(rd_hit4) ltac:(vm_compute; reflexivity) ltac:(ok_data).
      stepret F_9c8d0 D_9c8d0 (0x71294 : word) ltac:(pin; first [reflexivity | bveq]).
      stw F_71294 D_71294 (Z_to_bv 64 1088616) (Z_to_bv 64 2) ltac:(ok_data).
      ld_step F_71298 D_71298 (word_to_le_bytes 8 (Z_to_bv 64 892940)) (Z_to_bv 64 892940) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_7129c D_7129c (word_to_le_bytes 8 (Z_to_bv 64 987664)) (Z_to_bv 64 987664) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_712a0 D_712a0 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_712a4 D_712a4 (0xda00c : word) ltac:(pin; first [reflexivity | bveq]).
      (* loop exit (x9 = x8 = 0xf1210), __libc_start_init's epilogue, return to stage 2 *)
      sn F_da00c D_da00c.
      stepb_ft F_da010 D_da010 ltac:(pin; cond_compute).
      ld_step F_da014 D_da014 (word_to_le_bytes 8 (Z_to_bv 64 893116)) (Z_to_bv 64 893116) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_da018 D_da018 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_da01c D_da01c (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_da020 D_da020 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stepret F_da024 D_da024 (0xda0bc : word) ltac:(pin; first [reflexivity | bveq]).
      (* stage 2: a0 = argc, a1 = argv, a2 = envp; call main through s2 *)
      sn F_da0bc D_da0bc.
      sn F_da0c0 D_da0c0.
      sn F_da0c4 D_da0c4.
      stepjr F_da0c8 D_da0c8 (0x473d0 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
