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
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import StartupTac ArgvEnv RefLayout RefMemcpyLib LibAmo.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefImg RefStartupDefs Ub_code_46e98_47484 Ub_code_726ec_72728 Ub_code_9fd68_9fd7c Ub_code_dd254_dddf4 Ub_code_ee154_ee8c8.
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

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

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
  Lemma rd_guard8 : (forall D : word -> option byte, rdn SEGS (wbytes (wbytes (wbytes D (Z_to_bv 64 1240120) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1240124) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1240121) [Z_to_bv 8 0]) (Z_to_bv 64 1240120) 8 = Some (canary_bytes rnd)).
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
                          -> getr regs 4 = Z_to_bv 64 1108984
                            -> getr regs 19 = Z_to_bv 64 0
                              -> getr regs 20 = Z_to_bv 64 0
                                -> getr regs 21 = Z_to_bv 64 0
                                  -> getr regs 22 = Z_to_bv 64 0
                                    -> getr regs 23 = Z_to_bv 64 0
                                      -> getr regs 24 = Z_to_bv 64 0
                                        -> getr regs 25 = Z_to_bv 64 0
                                          -> getr regs 26 = Z_to_bv 64 0
                                            -> getr regs 27 = Z_to_bv 64 0
                                              -> (forall regs' : bvmap 5 word, getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) -> getr regs' 3 = Z_to_bv 64 67584 -> getr regs' 4 = Z_to_bv 64 1108984 -> getr regs' 19 = Z_to_bv 64 0 -> getr regs' 20 = Z_to_bv 64 0 -> getr regs' 21 = Z_to_bv 64 0 -> getr regs' 22 = Z_to_bv 64 0 -> getr regs' 23 = Z_to_bv 64 0 -> getr regs' 24 = Z_to_bv 64 0 -> getr regs' 25 = Z_to_bv 64 0 -> getr regs' 26 = Z_to_bv 64 0 -> getr regs' 27 = Z_to_bv 64 0 -> regs_agree (fun r : reg => In r [1; 2; 10; 11; 12; 13; 14; 15]) regs regs' -> G (mkst regs' (906096 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906096))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1240096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240112) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240104) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1240736) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1240744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1109000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1108976) (word_to_le_bytes 8 (Z_to_bv 64 1109000))) (Z_to_bv 64 1108784) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1240712) [Z_to_bv 8 1]) (Z_to_bv 64 1108824) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1108816) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1108936) (word_to_le_bytes 8 (Z_to_bv 64 1240768))) (Z_to_bv 64 1108904) (word_to_le_bytes 8 (Z_to_bv 64 1108904))) (Z_to_bv 64 1108792) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108800) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240120) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1240124) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1240121) [Z_to_bv 8 0]) (Z_to_bv 64 1108968) (word_to_le_bytes 8 (canary_w rnd)))) rom))
                                                -> G (mkst regs (906088 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1240096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240112) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240104) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1240736) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1240744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1109000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1108976) (word_to_le_bytes 8 (Z_to_bv 64 1109000))) (Z_to_bv 64 1108784) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1240712) [Z_to_bv 8 1]) (Z_to_bv 64 1108824) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1108816) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1108936) (word_to_le_bytes 8 (Z_to_bv 64 1240768))) (Z_to_bv 64 1108904) (word_to_le_bytes 8 (Z_to_bv 64 1108904))) (Z_to_bv 64 1108792) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108800) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108808) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_dd368 D_dd368 (word_to_le_bytes 8 (rnd_w inp sp0)) (rnd_w inp sp0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_dd36c D_dd36c.  (* [comment removed for export] *)
      sv F_dd828 D_dd828 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_dd82c D_dd82c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 906096) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_dd830 D_dd830 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_dd834 D_dd834 ((rnd_w inp sp0)).  (* [comment removed for export] *)
      sn F_dd838 D_dd838.  (* [comment removed for export] *)
      ld_step F_dd83c D_dd83c (word_to_le_bytes 8 (Z_to_bv 64 1240120)) (Z_to_bv 64 1240120) ltac:(rd_img img_fbc78_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_dd840 D_dd840.  (* [comment removed for export] *)
      sn F_dd844 D_dd844.  (* [comment removed for export] *)
      stepiv F_ee250 D_ee250 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_ee254 D_ee254 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_ee364 D_ee364.  (* [comment removed for export] *)
      sn F_ee368 D_ee368.  (* [comment removed for export] *)
      stepb_ft F_ee36c D_ee36c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_ee370 D_ee370.  (* [comment removed for export] *)
      stepb_tk F_ee374 D_ee374 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_ee3ac D_ee3ac.  (* [comment removed for export] *)
      stepb_ft F_ee3b0 D_ee3b0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_ee3b4 D_ee3b4 [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] (Z_to_bv 64 (bytes_le_to_Z [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3])) ltac:(RD_RNDa) ltac:(apply lez_rnd4a).  (* [comment removed for export] *)
      ld_step F_ee3b8 D_ee3b8 [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7] (Z_to_bv 64 (bytes_le_to_Z [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7])) ltac:(RD_RNDb) ltac:(apply lez_rnd4b).  (* [comment removed for export] *)
      stw F_ee3bc D_ee3bc (Z_to_bv 64 1240120) (LWv [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (sw_bytes_LWv [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] eq_refl).
      stw F_ee3c0 D_ee3c0 (Z_to_bv 64 1240124) (LWv [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (sw_bytes_LWv [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7] eq_refl).
      sn F_ee3c4 D_ee3c4.  (* [comment removed for export] *)
      sv F_ee3c8 D_ee3c8 (Z_to_bv 64 (bv_unsigned (rnd_w inp sp0) + 8)).  (* [comment removed for export] *)
      sn F_ee3cc D_ee3cc.  (* [comment removed for export] *)
      stepb_tk F_ee3d0 D_ee3d0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_ee610 D_ee610.  (* [comment removed for export] *)
      stepb_ft F_ee614 D_ee614 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_ee618 D_ee618.  (* [comment removed for export] *)
      stepb_ft F_ee61c D_ee61c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_ee620 D_ee620 (0xdd848 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_dd848 D_dd848.  (* [comment removed for export] *)
      sn F_dd864 D_dd864.  (* [comment removed for export] *)
      ld_step F_dd868 D_dd868 (word_to_le_bytes 8 (Z_to_bv 64 1240120)) (Z_to_bv 64 1240120) ltac:(rd_img img_fbc78_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_dd86c D_dd86c (Z_to_bv 64 1240121) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_dd870 D_dd870 (canary_bytes rnd) (canary_w rnd) ltac:(RD_GUARD) ltac:(apply lez_canary).  (* [comment removed for export] *)
      sn F_dd874 D_dd874.  (* [comment removed for export] *)
      stw F_dd878 D_dd878 (Z_to_bv 64 1108968) (canary_w rnd) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_dd87c D_dd87c (word_to_le_bytes 8 (Z_to_bv 64 906096)) (Z_to_bv 64 906096) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_dd880 D_dd880 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_dd884 D_dd884 (0xdd370 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
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
                          -> getr regs 4 = Z_to_bv 64 1108984
                            -> getr regs 19 = Z_to_bv 64 0
                              -> getr regs 20 = Z_to_bv 64 0
                                -> getr regs 21 = Z_to_bv 64 0
                                  -> getr regs 22 = Z_to_bv 64 0
                                    -> getr regs 23 = Z_to_bv 64 0
                                      -> getr regs 24 = Z_to_bv 64 0
                                        -> getr regs 25 = Z_to_bv 64 0
                                          -> getr regs 26 = Z_to_bv 64 0
                                            -> getr regs 27 = Z_to_bv 64 0
                                              -> (forall regs' : bvmap 5 word, getr regs' 1 = Z_to_bv 64 0 -> getr regs' 2 = sp0 -> getr regs' 3 = Z_to_bv 64 67584 -> getr regs' 4 = Z_to_bv 64 1108984 -> getr regs' 8 = Z_to_bv 64 0 -> getr regs' 9 = Z_to_bv 64 0 -> getr regs' 10 = Z_to_bv 64 290788 -> getr regs' 11 = argc_w inp -> getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 8) -> getr regs' 18 = Z_to_bv 64 0 -> getr regs' 19 = Z_to_bv 64 0 -> getr regs' 20 = Z_to_bv 64 0 -> getr regs' 21 = Z_to_bv 64 0 -> getr regs' 22 = Z_to_bv 64 0 -> getr regs' 23 = Z_to_bv 64 0 -> getr regs' 24 = Z_to_bv 64 0 -> getr regs' 25 = Z_to_bv 64 0 -> getr regs' 26 = Z_to_bv 64 0 -> getr regs' 27 = Z_to_bv 64 0 -> regs_agree (fun r : reg => In r [1; 2; 6; 8; 9; 10; 11; 12; 18]) regs regs' -> G (mkst regs' (906544 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906096))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1240096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240112) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240104) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1240736) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1240744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1109000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1108976) (word_to_le_bytes 8 (Z_to_bv 64 1109000))) (Z_to_bv 64 1108784) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1240712) [Z_to_bv 8 1]) (Z_to_bv 64 1108824) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1108816) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1108936) (word_to_le_bytes 8 (Z_to_bv 64 1240768))) (Z_to_bv 64 1108904) (word_to_le_bytes 8 (Z_to_bv 64 1108904))) (Z_to_bv 64 1108792) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108800) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240120) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1240124) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1240121) [Z_to_bv 8 0]) (Z_to_bv 64 1108968) (word_to_le_bytes 8 (canary_w rnd)))) rom))
                                                -> G (mkst regs (906096 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906096))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1240096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240112) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240104) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1240736) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1240744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1109000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1108976) (word_to_le_bytes 8 (Z_to_bv 64 1109000))) (Z_to_bv 64 1108784) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1240712) [Z_to_bv 8 1]) (Z_to_bv 64 1108824) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1108816) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1108936) (word_to_le_bytes 8 (Z_to_bv 64 1240768))) (Z_to_bv 64 1108904) (word_to_le_bytes 8 (Z_to_bv 64 1108904))) (Z_to_bv 64 1108792) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108800) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240120) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1240124) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1240121) [Z_to_bv 8 0]) (Z_to_bv 64 1108968) (word_to_le_bytes 8 (canary_w rnd)))) rom)).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_dd370 D_dd370 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_dd374 D_dd374 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_dd378 D_dd378 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_dd37c D_dd37c (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_dd380 D_dd380 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_dd384 D_dd384 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_dd388 D_dd388 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_dd38c D_dd38c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_dd46c D_dd46c (word_to_le_bytes 8 (Z_to_bv 64 906500)) (Z_to_bv 64 906500) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_dd470 D_dd470 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_dd474 D_dd474 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_dd478 D_dd478 (word_to_le_bytes 8 (Z_to_bv 64 290788)) (Z_to_bv 64 290788) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_dd47c D_dd47c (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_dd480 D_dd480 (0xdd504 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_dd504 D_dd504.  (* [comment removed for export] *)
      sn F_dd508 D_dd508.  (* [comment removed for export] *)
      sn F_dd50c D_dd50c.  (* [comment removed for export] *)
      sv F_dd510 D_dd510 (argc_w inp).  (* [comment removed for export] *)
      sv F_dd514 D_dd514 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_dd518 D_dd518 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_dd51c D_dd51c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_dd520 D_dd520 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_dd524 D_dd524 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_dd528 D_dd528 (sp0).  (* [comment removed for export] *)
      stepret F_dd52c D_dd52c (0xdd530 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
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
                            -> getr regs 4 = Z_to_bv 64 1108984
                              -> getr regs 8 = Z_to_bv 64 0
                                -> getr regs 9 = Z_to_bv 64 0
                                  -> getr regs 10 = Z_to_bv 64 290788
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
                                                            -> (forall regs' : bvmap 5 word, getr regs' 1 = Z_to_bv 64 906420 -> getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) -> getr regs' 3 = Z_to_bv 64 67584 -> getr regs' 4 = Z_to_bv 64 1108984 -> getr regs' 8 = Z_to_bv 64 1001144 -> getr regs' 9 = Z_to_bv 64 1001128 -> getr regs' 18 = Z_to_bv 64 290788 -> getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) -> getr regs' 20 = Z_to_bv 64 0 -> getr regs' 21 = Z_to_bv 64 0 -> getr regs' 22 = Z_to_bv 64 0 -> getr regs' 23 = Z_to_bv 64 0 -> getr regs' 24 = Z_to_bv 64 0 -> getr regs' 25 = Z_to_bv 64 0 -> getr regs' 26 = Z_to_bv 64 0 -> getr regs' 27 = Z_to_bv 64 0 -> regs_agree (fun r : reg => In r [1; 2; 8; 9; 10; 11; 18; 19]) regs regs' -> G (mkst regs' (290528 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906096))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 906596))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1240096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240112) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240104) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1240736) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1240744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1109000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1108976) (word_to_le_bytes 8 (Z_to_bv 64 1109000))) (Z_to_bv 64 1108784) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1240712) [Z_to_bv 8 1]) (Z_to_bv 64 1108824) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1108816) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1108936) (word_to_le_bytes 8 (Z_to_bv 64 1240768))) (Z_to_bv 64 1108904) (word_to_le_bytes 8 (Z_to_bv 64 1108904))) (Z_to_bv 64 1108792) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108800) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240120) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1240124) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1240121) [Z_to_bv 8 0]) (Z_to_bv 64 1108968) (word_to_le_bytes 8 (canary_w rnd)))) rom))
                                                              -> G (mkst regs (906544 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906096))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1240096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240112) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240104) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1240736) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1240744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1109000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1108976) (word_to_le_bytes 8 (Z_to_bv 64 1109000))) (Z_to_bv 64 1108784) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1240712) [Z_to_bv 8 1]) (Z_to_bv 64 1108824) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1108816) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1108936) (word_to_le_bytes 8 (Z_to_bv 64 1240768))) (Z_to_bv 64 1108904) (word_to_le_bytes 8 (Z_to_bv 64 1108904))) (Z_to_bv 64 1108792) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108800) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240120) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1240124) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1240121) [Z_to_bv 8 0]) (Z_to_bv 64 1108968) (word_to_le_bytes 8 (canary_w rnd)))) rom)).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_dd530 D_dd530 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_dd534 D_dd534 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_dd538 D_dd538 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_dd53c D_dd53c (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_dd540 D_dd540 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_dd544 D_dd544 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_dd548 D_dd548 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_dd54c D_dd54c (argc_w inp).  (* [comment removed for export] *)
      sn F_dd550 D_dd550.  (* [comment removed for export] *)
      stepiv F_dd554 D_dd554 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_dd558 D_dd558 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_dd55c D_dd55c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_dd560 D_dd560.  (* [comment removed for export] *)
      sv F_dd484 D_dd484 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_dd488 D_dd488 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 906596) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_dd48c D_dd48c (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_dd490 D_dd490 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_dd494 D_dd494.  (* [comment removed for export] *)
      stepret F_dd254 D_dd254 (0xdd498 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_dd498 D_dd498.  (* [comment removed for export] *)
      sn F_dd49c D_dd49c.  (* [comment removed for export] *)
      ld_step F_dd4a0 D_dd4a0 (word_to_le_bytes 8 (Z_to_bv 64 1001144)) (Z_to_bv 64 1001144) ltac:(rd_img img_fbc98_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_dd4a4 D_dd4a4 (word_to_le_bytes 8 (Z_to_bv 64 1001128)) (Z_to_bv 64 1001128) ltac:(rd_img img_fbca0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_dd4a8 D_dd4a8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_dd4ac D_dd4ac (word_to_le_bytes 8 (Z_to_bv 64 290528)) (Z_to_bv 64 290528) ltac:(rd_img img_f46a8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_dd4b0 D_dd4b0 (0x46ee0 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
  (* fin_c9: both static constructors and libc's init loop, 0x46ee0 -> main 0x46fe4, stepped by
     hand against this binary's own code (init_array has two entries, read from the ELF);
     the statement is the decoded old one, retargeted onto inp. *)
  Lemma fin_c9 : (forall G : machine_state -> Prop,
                  bwd SEGS G
                  -> forall (regs : bvmap 5 word) (rom : word -> option byte) (s1v tid : word),
                      wfJ sp0 Jb
                      -> getr regs 1 = Z_to_bv 64 906420
                        -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80)
                          -> getr regs 3 = Z_to_bv 64 67584
                            -> getr regs 4 = Z_to_bv 64 1108984
                              -> getr regs 8 = Z_to_bv 64 1001144
                                -> getr regs 9 = Z_to_bv 64 1001128
                                  -> getr regs 18 = Z_to_bv 64 290788
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
                                                           getr regs' 1 = Z_to_bv 64 906612
                                                           -> getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48)
                                                             -> getr regs' 3 = Z_to_bv 64 67584
                                                               -> getr regs' 4 = Z_to_bv 64 1108984
                                                                 -> getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8)
                                                                   -> getr regs' 9 = argc_w inp
                                                                     -> getr regs' 10 = argc_w inp
                                                                       -> getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8)
                                                                         -> getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))
                                                                           -> getr regs' 18 = Z_to_bv 64 290788
                                                                             -> getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))
                                                                               -> getr regs' 20 = Z_to_bv 64 0
                                                                                 -> getr regs' 21 = Z_to_bv 64 0
                                                                                   -> getr regs' 22 = Z_to_bv 64 0
                                                                                     -> getr regs' 23 = Z_to_bv 64 0
                                                                                       -> getr regs' 24 = Z_to_bv 64 0
                                                                                         -> getr regs' 25 = Z_to_bv 64 0 -> getr regs' 26 = Z_to_bv 64 0 -> getr regs' 27 = Z_to_bv 64 0 -> regs_agree (fun r : reg => In r [1; 2; 8; 9; 10; 11; 12]) regs regs' -> G (mkst regs' (290788 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906096))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 906596))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 906420))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 1001144))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 906420))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 1001144))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1240096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240112) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240104) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1240736) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1240744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1109000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1108976) (word_to_le_bytes 8 (Z_to_bv 64 1109000))) (Z_to_bv 64 1108784) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1240712) [Z_to_bv 8 1]) (Z_to_bv 64 1108824) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1108816) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1108936) (word_to_le_bytes 8 (Z_to_bv 64 1240768))) (Z_to_bv 64 1108904) (word_to_le_bytes 8 (Z_to_bv 64 1108904))) (Z_to_bv 64 1108792) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108800) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240120) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1240124) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1240121) [Z_to_bv 8 0]) (Z_to_bv 64 1108968) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 1036528) [Z_to_bv 8 1]) (Z_to_bv 64 1102888) (word_to_le_bytes 4 (Z_to_bv 64 1))) (Z_to_bv 64 1102240) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 1102888) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1102244) (word_to_le_bytes 4 (Z_to_bv 64 1))) (Z_to_bv 64 1102888) (word_to_le_bytes 4 (Z_to_bv 64 3))) (Z_to_bv 64 1102248) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom))
                                                        -> G (mkst regs (290528 : word) (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906088))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rnd))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1240712))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 906096))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 906596))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rnd) (Z_to_bv 64 1240096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240112) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240104) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1240736) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1240744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1109000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1108976) (word_to_le_bytes 8 (Z_to_bv 64 1109000))) (Z_to_bv 64 1108784) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1240712) [Z_to_bv 8 1]) (Z_to_bv 64 1108824) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1108816) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1108936) (word_to_le_bytes 8 (Z_to_bv 64 1240768))) (Z_to_bv 64 1108904) (word_to_le_bytes 8 (Z_to_bv 64 1108904))) (Z_to_bv 64 1108792) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108800) (word_to_le_bytes 8 (Z_to_bv 64 1108784))) (Z_to_bv 64 1108808) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1240120) [rbn rnd 0%nat; rbn rnd 1%nat; rbn rnd 2%nat; rbn rnd 3%nat]) (Z_to_bv 64 1240124) [rbn rnd 4%nat; rbn rnd 5%nat; rbn rnd 6%nat; rbn rnd 7%nat]) (Z_to_bv 64 1240121) [Z_to_bv 8 0]) (Z_to_bv 64 1108968) (word_to_le_bytes 8 (canary_w rnd)))) rom)).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { (* init_array[0] = frame_dummy (0x46ee0), entered by fin_c8's jalr; ra = 0xdd4b4 *)
      sv F_46ee0 D_46ee0 (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_46ee4 D_46ee4 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 906420) ltac:(ok_win HJ).
      stw F_46ee8 D_46ee8 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 1001144) ltac:(ok_win HJ).
      sv F_46eec D_46eec (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      sn F_46ef0 D_46ef0.
      sn F_46ef4 D_46ef4.
      lb_step F_46ef8 D_46ef8 (Z_to_bv 8 0) ltac:(rd_img img_fd0f0_1).
      sn F_46efc D_46efc.
      stepb_tk F_46f00 D_46f00 ltac:(pin; cond_compute).
      sn F_46f0c D_46f0c.
      sn F_46f10 D_46f10.
      sn F_46f14 D_46f14.
      stw F_46f18 D_46f18 (Z_to_bv 64 1036528) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_46f1c D_46f1c.
      ld_step F_46f20 D_46f20 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_fbb40_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_46f24 D_46f24 ltac:(pin; cond_compute).
      ld_step F_46f44 D_46f44 (word_to_le_bytes 8 (Z_to_bv 64 906420)) (Z_to_bv 64 906420) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_46f48 D_46f48 (word_to_le_bytes 8 (Z_to_bv 64 1001144)) (Z_to_bv 64 1001144) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_46f4c D_46f4c (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_46f50 D_46f50 (0xdd4b4 : word) ltac:(pin; first [reflexivity | bveq]).
      (* __libc_start_init's loop: x9 := 0xf1208 <> x8 = 0xf1210, load init_array[1] = 0x726ec *)
      sn F_dd4b4 D_dd4b4.
      stepb_tk F_dd4b8 D_dd4b8 ltac:(pin; cond_compute).
      ld_step F_dd4ac D_dd4ac (word_to_le_bytes 8 (Z_to_bv 64 468716)) (Z_to_bv 64 468716) ltac:(rd_img img_f46b0_8) ltac:(apply bytes_le_to_Z_8).
      stepjr F_dd4b0 D_dd4b0 (0x726ec : word) ltac:(gres; pin; first [reflexivity | bveq]).
      (* init_array[1] (0x726ec): three calls of 0x9fd68 = amoadd.w x10, 1, (0x109ee8) *)
      sv F_726ec D_726ec (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_726f0 D_726f0 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 906420) ltac:(ok_win HJ).
      stw F_726f4 D_726f4 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 1001144) ltac:(ok_win HJ).
      sn F_726f8 D_726f8.
      sn F_9fd68 D_9fd68.
      sn F_9fd6c D_9fd6c.
      sn F_9fd70 D_9fd70.
      amo_step F_9fd74 D_9fd74 (Z_to_bv 64 1102888) (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 1)
        ltac:(rd_img img_10d428_4) ltac:(vm_compute; reflexivity) ltac:(ok_data).
      stepret F_9fd78 D_9fd78 (0x726fc : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_726fc D_726fc.
      sn F_72700 D_72700.
      stw F_72704 D_72704 (Z_to_bv 64 1102240) (Z_to_bv 64 0) ltac:(ok_data).
      sn F_72708 D_72708.
      sn F_9fd68 D_9fd68.
      sn F_9fd6c D_9fd6c.
      sn F_9fd70 D_9fd70.
      amo_step F_9fd74 D_9fd74 (Z_to_bv 64 1102888) (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 2)
        ltac:(rd_hit4) ltac:(vm_compute; reflexivity) ltac:(ok_data).
      stepret F_9fd78 D_9fd78 (0x7270c : word) ltac:(pin; first [reflexivity | bveq]).
      stw F_7270c D_7270c (Z_to_bv 64 1102244) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_72710 D_72710.
      sn F_9fd68 D_9fd68.
      sn F_9fd6c D_9fd6c.
      sn F_9fd70 D_9fd70.
      amo_step F_9fd74 D_9fd74 (Z_to_bv 64 1102888) (word_to_le_bytes 4 (Z_to_bv 64 2)) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 3)
        ltac:(rd_hit4) ltac:(vm_compute; reflexivity) ltac:(ok_data).
      stepret F_9fd78 D_9fd78 (0x72714 : word) ltac:(pin; first [reflexivity | bveq]).
      stw F_72714 D_72714 (Z_to_bv 64 1102248) (Z_to_bv 64 2) ltac:(ok_data).
      ld_step F_72718 D_72718 (word_to_le_bytes 8 (Z_to_bv 64 906420)) (Z_to_bv 64 906420) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_7271c D_7271c (word_to_le_bytes 8 (Z_to_bv 64 1001144)) (Z_to_bv 64 1001144) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_72720 D_72720 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_72724 D_72724 (0xdd4b4 : word) ltac:(pin; first [reflexivity | bveq]).
      (* loop exit (x9 = x8 = 0xf1210), __libc_start_init's epilogue, return to stage 2 *)
      sn F_dd4b4 D_dd4b4.
      stepb_ft F_dd4b8 D_dd4b8 ltac:(pin; cond_compute).
      ld_step F_dd4bc D_dd4bc (word_to_le_bytes 8 (Z_to_bv 64 906596)) (Z_to_bv 64 906596) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_dd4c0 D_dd4c0 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_dd4c4 D_dd4c4 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_dd4c8 D_dd4c8 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stepret F_dd4cc D_dd4cc (0xdd564 : word) ltac:(pin; first [reflexivity | bveq]).
      (* stage 2: a0 = argc, a1 = argv, a2 = envp; call main through s2 *)
      sn F_dd564 D_dd564.
      sn F_dd568 D_dd568.
      sn F_dd56c D_dd56c.
      stepjr F_dd570 D_dd570 (0x46fe4 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
