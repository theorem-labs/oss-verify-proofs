(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanStartLoops. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanStartLoops.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlan AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import EntryKn StdioSymDrive.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import EntryGlue.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boot1_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  (* [comment removed for export] *)
  Definition E7 : env := E0 PH sp rdraw argv envp uid hw.
  Definition MEM0 : word -> option byte := M0 PH sp rdraw argv envp uid hw.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).

  (* [comment removed for export] *)
  Definition above_ok (M : word -> option byte) : Prop :=
    forall x : word, usp <= bv_unsigned x -> M x = MEM0 x.

  #[using="Hsp"] Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. destruct Hsp as (H & _ & _). unfold sp_window_lo in H. exact H. Qed.
  #[using="Hsp"] Lemma usp_hi : usp <= 0x800000000000.
  Proof. destruct Hsp as (_ & H & _). unfold sp_window_hi in H. exact H. Qed.
  #[using="Hsp"] Lemma usp_al : usp mod 16 = 0.
  Proof. destruct Hsp as (_ & _ & H). exact H. Qed.
  #[using="sp envp Hva usp envc"] Lemma len_av : 1 <= argc <= 1024. Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  #[using="sp argv Hve usp argc"] Lemma len_ev : 0 <= envc <= 256. Proof. unfold envc. destruct Hve as [H _]. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma kx_ok : know_ok SEGS E7 MEM0 kx.
  Proof. unfold kx. constructor. Qed.

  #[using="Hsp Hva Hve Hfit Huid"] Lemma KN0_ok : know_ok SEGS E7 MEM0 KN0.
  Proof.
    unfold KN0, E7, MEM0. apply kn0_ok; try assumption.
    - exact img_hull.
    - exact rw_window.
    - exact kx_ok.
  Qed.

  #[using="Type"] Lemma R0_ok : regs_ok E7 sr_init (R0 sp).
  Proof. unfold E7. apply regs0_ok. Qed.

  (* [comment removed for export] *)
  Let bsb := build_stack_bytes PH sp argv envp uid hw rdraw.
  Let stk := stack_to_mem sp (entry_stack_image PH sp argv envp uid hw rdraw).

  #[using="Hfit argc envc"] Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    pose proof (build_stack_bytes_within_span PH sp argv envp uid hw rdraw) as B. fold bsb in B.
    unfold entry_stack_fits, sp_window_hi in Hfit. unfold usp. lia.
  Qed.
  #[using="argv envp Hsp usp argc envc"] Lemma Hhi' : bv_unsigned sp <= sp_window_hi. Proof. pose proof usp_hi. unfold sp_window_hi, usp in *. lia. Qed.
  #[using="argv envp Hsp usp argc envc"] Lemma Hlo' : sp_window_lo <= bv_unsigned sp. Proof. pose proof usp_lo. unfold sp_window_lo, usp in *. lia. Qed.

  #[using="argc envc"] Lemma rdn_above : forall M (a : word) n,
    above_ok M -> usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    rdn SEGS M a n = rdn SEGS stk a n.
  Proof.
    intros M a n HA Ha Hn. unfold stk.
    rewrite <- (rdn_wrap_stack_above SEGS PH sp argv envp a n uid hw rdraw) by (unfold usp in *; lia).
    apply rdn_ext; [exact Hn|]. intros x Hx. rewrite (HA x) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Hsp argc envc"] Lemma above_ok_block : forall M log,
    above_ok M -> log_below_b 0%nat [] log = true -> above_ok (mem_denot E7 M log).
  Proof.
    intros M log HA Hb x Hx. pose proof usp_lo. pose proof usp_hi.
    rewrite (mem_denot_above E7 M log 0%nat [] usp x Hb); try (cbn [ev E7 E0 vals_ev vals0 nth]; unfold usp in *; lia).
    - apply HA. exact Hx.
    - constructor.
  Qed.

  (* [comment removed for export] *)
  Ltac vmc := lazymatch goal with |- log_below_b _ _ _ = true => vmeq_refl end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ENVP : Z := usp + 8 * argc + 16.

  #[using="rdraw uid hw Hsp Hva Hve envc"] Lemma ENVP_range : 0 <= ENVP /\ ENVP + 8 * Z.of_nat (length envp) + 16 < 2 ^ 64.
  Proof.
    pose proof (lay_bsb_nw PH sp rdraw argv envp uid hw Hva Hve Hhi') as NW.
    pose proof (auxv_off_bound PH sp rdraw argv envp uid hw) as AB.
    pose proof usp_lo. unfold auxv_off, envp_off in AB. unfold ENVP, usp, argc. lia.
  Qed.

  #[using="envp envc"] Lemma envp_slot_eq : forall k,
    (sp + nat_to_word (envp_off argv + 8 * k))%bv = Z_to_bv 64 (ENVP + 8 * Z.of_nat k).
  Proof.
    intros k. apply bv_eq. rewrite word_add_nat. f_equal. f_equal. unfold envp_off, ENVP, usp, argc. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit Huid argc envc bsb stk"] Lemma phase1 : exists R M,
      msteps SEGS (mkst (R0 sp) (Z_to_bv 64 A_start) MEM0 ROM) (mkst R (Z_to_bv 64 A_envloop_exit) M ROM)
      /\ regs_ok E7 SR2 R /\ know_ok SEGS E7 M KN1 /\ above_ok M /\ mem_grows MEM0 M.
  Proof.
    pose proof R0_ok as HR. pose proof KN0_ok as HK.
    pose proof usp_lo as SL. pose proof usp_fit as SF. pose proof len_av as LA. pose proof len_ev as LE.
    pose proof ENVP_range as ER.
    (* [comment removed for export] *)
    ms_block_with HR HK FUEL [A_envloop] noscr 7%nat R1 HR1 HK1 MS1.
    lazymatch type of HK1 with know_ok _ _ ?m _ => set (M1 := m) in * end.
    assert (A1 : above_ok M1).
    { unfold M1. apply above_ok_block; [intros x Hx; reflexivity | vmc]. }
    assert (G1 : mem_grows MEM0 M1) by (unfold M1; apply mem_denot_grows).
    clearbody M1.
    (* [comment removed for export] *)
    destruct (fetchd_some _ _ envloop_code_0) as (w1 & F1 & E1 & D1).
    destruct (fetchd_some _ _ envloop_code_4) as (w2 & F2 & E2 & D2).
    destruct (fetchd_some _ _ envloop_code_8) as (w3 & F3 & E3 & D3).
    assert (He9 : getr R1 9%bv = Z_to_bv 64 (ENVP + 8 * Z.of_nat 0)).
    { rewrite (HR1 9%bv). change (sr_get _ 9%bv) with e_envp. apply bv_eq.
      rewrite u_small by (unfold ENVP; lia).
      pose proof (u_e_envp PH sp rdraw argv envp uid hw Hsp Hva Hve Hfit) as U. unfold EntryKn.uE in U.
      unfold E7. rewrite U. unfold ENVP, usp, argc. lia. }
    destruct (env_loop SEGS A_envloop w1 w2 w3 ltac:(unfold A_envloop; lia) F1 F2 F3 E1 E2 E3 D1 D2 D3
                M1 ROM ENVP (length envp) (cat_envp_ptr sp argv envp) ER)
      with (n := length envp) (k := 0%nat) (regs := R1)
      as (R2 & MS2 & P9 & P10 & Pag).
    - (* [comment removed for export] *) intros k Hk. split.
      + rewrite <- n_to_le_8_spec, <- (read_envp_ptr_k SEGS PH sp rdraw argv envp uid hw Hva Hve Hhi' k Hk), envp_slot_eq.
        apply rdn_above; [exact A1 | rewrite u_small; unfold ENVP in *; lia | rewrite u_small; unfold ENVP in *; change (Z.of_nat 8) with 8; lia].
      + apply (cat_envp_ptr_nz PH sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' k Hk).
    - (* [comment removed for export] *)
      rewrite <- n_to_le_8_spec, <- (read_envp_null SEGS PH sp rdraw argv envp uid hw Hva Hve Hhi'), envp_slot_eq.
      apply rdn_above; [exact A1 | rewrite u_small; unfold ENVP in *; lia | rewrite u_small; unfold ENVP in *; change (Z.of_nat 8) with 8; lia].
    - lia.
    - exact He9.
    - (* [comment removed for export] *)
      exists R2, M1. split; [|split; [|split; [exact HK1 | split; [exact A1 | exact G1]]]].
      + eapply msteps_trans; [exact MS1|]. rewrite envloop_exit_eq. exact MS2.
      + unfold SR2. apply (regs_ok_upd2 E7 _ R1 R2 9%bv 10%bv); try exact HR1;
          try (intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH).
        * rewrite P9. symmetry. apply bv_eq.
          pose proof (u_e_auxv PH sp rdraw argv envp uid hw Hsp Hva Hve Hfit) as U. unfold EntryKn.uE in U.
          unfold E7. rewrite U. rewrite u_small by (unfold ENVP in *; lia). unfold ENVP, usp, argc. lia.
        * rewrite P10. reflexivity.
        * intros r Hra Hrb. apply Pag. intros [C|C]; [apply Hra | apply Hrb]; exact C.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition PN : Z := usp + 8 * argc + 8 * envc + 184.
  Let s0 : list byte := nth 0 argv [].

  Definition is_kblob_k (k : nat) (K : kentry) : bool :=
    match K with KBlob _ _ k' => Nat.eqb k k' | _ => false end.

  #[using="sp rdraw envp uid hw Hva Hfit usp envc"] Lemma s0_len : Z.of_nat (length s0) <= 131071.
  Proof. unfold s0. destruct Hva as (H1 & _ & H3 & _). destruct argv as [|a t]; [cbn in H1; lia|]. cbn. inversion H3. lia. Qed.

  #[using="sp rdraw envp uid hw Hva Hfit usp envc"] Lemma s0_nonul : ~ In (Z_to_bv 8 0) s0.
  Proof. unfold s0. destruct Hva as (H1 & _ & _ & H4 & _). destruct argv as [|a t]; [cbn in H1; lia|]. cbn. inversion H4. assumption. Qed.

  #[using="rdraw uid hw Hsp Hva Hfit bsb"] Lemma PN_range : 0 <= PN /\ PN + Z.of_nat (length s0) + 2 < 2 ^ 48.
  Proof.
    pose proof usp_lo. pose proof usp_fit as SF.
    pose proof (argv0_end_le PH sp rdraw argv envp uid hw Hva) as AE. fold bsb in AE.
    unfold PN, usp, argc, envc, s0 in *. lia.
  Qed.

  #[using="Type"] Lemma x11_after_B2 : sr_get SR2e 11%bv = mkAlu ALU_ADD e_str0 (ELit 1).
  Proof. vmeq_refl. Qed.

  #[using="Hsp Hva Hve Hfit argc envc bsb s0"] Lemma phase2 : forall R M,
    regs_ok E7 SR2 R -> know_ok SEGS E7 M KN1 -> above_ok M -> mem_grows MEM0 M ->
    exists R' M', msteps SEGS (mkst R (Z_to_bv 64 A_envloop_exit) M ROM) (mkst R' (Z_to_bv 64 A_pnloop_exit) M' ROM)
      /\ regs_ok E7 SR3 R' /\ know_ok SEGS E7 M' KN3 /\ above_ok M' /\ mem_grows MEM0 M'.
  Proof.
    intros R M HR HK HA HG.
    pose proof usp_lo as SL. pose proof usp_fit as SF. pose proof len_av as LA. pose proof len_ev as LE.
    pose proof PN_range as PR. pose proof s0_len as SLEN.
    pose proof (u_e_str0 PH sp rdraw argv envp uid hw Hsp Hva Hve Hfit) as US0. unfold EntryKn.uE in US0.
    pose proof (u_e_str1 PH sp rdraw argv envp uid hw Hsp Hva Hve Hfit) as US1. unfold EntryKn.uE in US1.
    (* [comment removed for export] *)
    ms_block_with HR HK FUEL [A_pnloop] noscr 7%nat R2 HR2 HK2 MS2.
    lazymatch type of HK2 with know_ok _ _ ?m _ => set (M2 := m) in * end.
    assert (A2 : above_ok M2).
    { unfold M2. apply above_ok_block; [exact HA | vmc]. }
    assert (G2 : mem_grows MEM0 M2) by (unfold M2; eapply mem_grows_trans; [exact HG | apply mem_denot_grows]).
    clearbody M2. clear HR HK HA HG.
    (* [comment removed for export] *)
    destruct (fetchd_some _ _ pnloop_code_m8) as (w0 & F0 & NE0 & D0).
    destruct (fetchd_some _ _ pnloop_code_m4) as (w1 & F1 & NE1 & D1).
    destruct (fetchd_some _ _ pnloop_code_0) as (w2 & F2 & NE2 & D2).
    destruct (fetchd_some _ _ pnloop_code_4) as (w3 & F3 & NE3 & D3).
    destruct (fetchd_some _ _ pnloop_code_8) as (w4 & F4 & NE4 & D4).
    (* [comment removed for export] *)
    assert (Hrd : forall j, (j <= length s0)%nat -> rdn SEGS M2 (Z_to_bv 64 (PN + Z.of_nat j)) 1 = Some [byte_at s0 j]).
    { let i := kidx KN2 (is_kblob_k K_ARGV0) in
      pose proof (know_nth SEGS E7 M2 KN2 i _ HK2 eq_refl) as KB.
      cbn [kentry_ok] in KB. destruct KB as (Hfl & Hlen & Hby).
      lazymatch type of Hlen with _ = elenZ E7 ?n =>
        assert (Elen : elenZ E7 n = Z.of_nat (length s0) + 1)
          by (rewrite <- Hlen; unfold E7, E0; cbn [eb blobs0 K_ARGV0 K_RND Nat.eqb]; rewrite length_app; cbn [length]; unfold s0; lia)
      end.
      lazymatch type of Hby with (forall i, _ -> M2 (Z_to_bv 64 (?st + i)) = _) =>
        assert (Est : st = PN)
      end.
      { unfold estart. cbn [a_base a_off]. unfold E7. cbn [edenot]. rewrite !u_add64, !u_mul64, !u_small by lia.
        cbn [ev EntryKn.E0 vals_ev vals0 nth]. rewrite !u_small by lia.
        rewrite (Z.mod_small (8 * Z.of_nat (length argv))) by lia. rewrite (Z.mod_small (8 * Z.of_nat (length envp))) by lia.
        rewrite (Z.mod_small (8 * _ + _)) by lia. rewrite Z.mod_small by (unfold usp in *; lia).
        unfold PN, usp, argc, envc. lia. }
      intros j Hj. cbn [rdn].
      rewrite Est, Elen in Hby. rewrite (Hby (Z.of_nat j)) by lia. rewrite Nat2Z.id.
      unfold byte_at. unfold E7, E0. cbn [eb blobs0 K_ARGV0 K_RND Nat.eqb]. reflexivity. }
    assert (Hst : store_ok SEGS M2 (Z_to_bv 64 A_progname) 8 = true).
    { let i := kidx KN2 (is_kwr_cov (ELit 0) A_progname 8) in
      eapply (kwr_store_ok_lit SEGS E7 M2 KN2 i); [exact HK2 | reflexivity | ..]; unfold A_progname; lia. }
    destruct (pn_loop SEGS A_pnloop w0 w1 w2 w3 w4 ltac:(unfold A_pnloop; lia) F0 F1 F2 F3 F4 NE0 NE1 NE2 NE3 NE4 D0 D1 D2 D3 D4
                M2 ROM A_progname PN s0 ltac:(unfold A_progname; lia) ltac:(lia) ltac:(unfold A_progname, PN; lia) s0_nonul Hrd Hst
                s0 0%nat R2 M2 eq_refl ltac:(lia))
      as (R3 & M3 & MS3 & (P11 & P13 & Pag) & (C1 & C2)).
    - rewrite (HR2 10%bv). reflexivity.
    - rewrite (HR2 11%bv). change (sr_get _ 11%bv) with (mkAlu ALU_ADD e_str0 (ELit 1)). rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold E7. rewrite US0.
      change (1 mod 2 ^ 64) with 1. rewrite !Z.mod_small by (unfold PN, usp in *; lia). unfold PN, usp, argc, envc. lia.
    - rewrite (HR2 12%bv). reflexivity.
    - apply cellrel_refl.
    - (* [comment removed for export] *)
      exists R3, M3. split; [|split; [|split; [|split]]].
      + eapply msteps_trans; [exact MS2|]. rewrite pnloop_exit_eq. exact MS3.
      + unfold SR3. apply (regs_ok_upd2 E7 _ R2 R3 11%bv 13%bv); try exact HR2;
          try (intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH).
        * rewrite P11. symmetry. apply bv_eq. unfold E7. rewrite US1. rewrite u_small by (unfold PN in *; lia).
          unfold PN, usp, argc, envc, s0. lia.
        * rewrite P13. reflexivity.
        * intros r Hra Hrb. apply Pag. intros [C|C]; [apply Hra | apply Hrb]; exact C.
      + unfold KN3. apply (know_change_keep SEGS E7 M2 M3); [exact HK2 | | exact C2].
        intros x Hx. apply C1. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx.
        rewrite !u_small in Hx by (unfold A_progname; lia). lia.
      + intros x Hx. rewrite C1; [apply A2; exact Hx|]. unfold A_progname. right. unfold usp in *. lia.
      + eapply mem_grows_trans; [exact G2 | exact C2].
  Qed.

End Walk.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanStartLoops.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boot1_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  (* [comment removed for export] *)
  Definition E7 : env := E0 PH sp rdraw argv envp uid hw.
  Definition MEM0 : word -> option byte := M0 PH sp rdraw argv envp uid hw.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).

  (* [comment removed for export] *)
  Definition above_ok (M : word -> option byte) : Prop :=
    forall x : word, usp <= bv_unsigned x -> M x = MEM0 x.

  #[using="Hsp"] Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. destruct Hsp as (H & _ & _). unfold sp_window_lo in H. exact H. Qed.
  #[using="Hsp"] Lemma usp_hi : usp <= 0x800000000000.
  Proof. destruct Hsp as (_ & H & _). unfold sp_window_hi in H. exact H. Qed.
  #[using="Hsp"] Lemma usp_al : usp mod 16 = 0.
  Proof. destruct Hsp as (_ & _ & H). exact H. Qed.
  #[using="sp envp Hva usp envc"] Lemma len_av : 1 <= argc <= 1024. Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  #[using="sp argv Hve usp argc"] Lemma len_ev : 0 <= envc <= 256. Proof. unfold envc. destruct Hve as [H _]. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma kx_ok : know_ok SEGS E7 MEM0 kx.
  Proof. unfold kx. constructor. Qed.

  #[using="Hsp Hva Hve Hfit Huid"] Lemma KN0_ok : know_ok SEGS E7 MEM0 KN0.
  Proof.
    unfold KN0, E7, MEM0. apply kn0_ok; try assumption.
    - exact img_hull.
    - exact rw_window.
    - exact kx_ok.
  Qed.

  #[using="Type"] Lemma R0_ok : regs_ok E7 sr_init (R0 sp).
  Proof. unfold E7. apply regs0_ok. Qed.

  (* [comment removed for export] *)
  Let bsb := build_stack_bytes PH sp argv envp uid hw rdraw.
  Let stk := stack_to_mem sp (entry_stack_image PH sp argv envp uid hw rdraw).

  #[using="Hfit argc envc"] Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    pose proof (build_stack_bytes_within_span PH sp argv envp uid hw rdraw) as B. fold bsb in B.
    unfold entry_stack_fits, sp_window_hi in Hfit. unfold usp. lia.
  Qed.
  #[using="argv envp Hsp usp argc envc"] Lemma Hhi' : bv_unsigned sp <= sp_window_hi. Proof. pose proof usp_hi. unfold sp_window_hi, usp in *. lia. Qed.
  #[using="argv envp Hsp usp argc envc"] Lemma Hlo' : sp_window_lo <= bv_unsigned sp. Proof. pose proof usp_lo. unfold sp_window_lo, usp in *. lia. Qed.

  #[using="argc envc"] Lemma rdn_above : forall M (a : word) n,
    above_ok M -> usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    rdn SEGS M a n = rdn SEGS stk a n.
  Proof.
    intros M a n HA Ha Hn. unfold stk.
    rewrite <- (rdn_wrap_stack_above SEGS PH sp argv envp a n uid hw rdraw) by (unfold usp in *; lia).
    apply rdn_ext; [exact Hn|]. intros x Hx. rewrite (HA x) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Hsp argc envc"] Lemma above_ok_block : forall M log,
    above_ok M -> log_below_b 0%nat [] log = true -> above_ok (mem_denot E7 M log).
  Proof.
    intros M log HA Hb x Hx. pose proof usp_lo. pose proof usp_hi.
    rewrite (mem_denot_above E7 M log 0%nat [] usp x Hb); try (cbn [ev E7 E0 vals_ev vals0 nth]; unfold usp in *; lia).
    - apply HA. exact Hx.
    - constructor.
  Qed.

  (* [comment removed for export] *)
  Ltac vmc := lazymatch goal with |- log_below_b _ _ _ = true => vmeq_refl end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ENVP : Z := usp + 8 * argc + 16.

  #[using="rdraw uid hw Hsp Hva Hve envc"] Lemma ENVP_range : 0 <= ENVP /\ ENVP + 8 * Z.of_nat (length envp) + 16 < 2 ^ 64.
  Proof.
    pose proof (lay_bsb_nw PH sp rdraw argv envp uid hw Hva Hve Hhi') as NW.
    pose proof (auxv_off_bound PH sp rdraw argv envp uid hw) as AB.
    pose proof usp_lo. unfold auxv_off, envp_off in AB. unfold ENVP, usp, argc. lia.
  Qed.

  #[using="envp envc"] Lemma envp_slot_eq : forall k,
    (sp + nat_to_word (envp_off argv + 8 * k))%bv = Z_to_bv 64 (ENVP + 8 * Z.of_nat k).
  Proof.
    intros k. apply bv_eq. rewrite word_add_nat. f_equal. f_equal. unfold envp_off, ENVP, usp, argc. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit Huid argc envc bsb stk"] Lemma phase1 : exists R M,
      msteps SEGS (mkst (R0 sp) (Z_to_bv 64 A_start) MEM0 ROM) (mkst R (Z_to_bv 64 A_envloop_exit) M ROM)
      /\ regs_ok E7 SR2 R /\ know_ok SEGS E7 M KN1 /\ above_ok M /\ mem_grows MEM0 M.
  Proof.
    pose proof R0_ok as HR. pose proof KN0_ok as HK.
    pose proof usp_lo as SL. pose proof usp_fit as SF. pose proof len_av as LA. pose proof len_ev as LE.
    pose proof ENVP_range as ER.
    (* [comment removed for export] *)
    ms_block_with HR HK FUEL [A_envloop] noscr 7%nat R1 HR1 HK1 MS1.
    lazymatch type of HK1 with know_ok _ _ ?m _ => set (M1 := m) in * end.
    assert (A1 : above_ok M1).
    { unfold M1. apply above_ok_block; [intros x Hx; reflexivity | vmc]. }
    assert (G1 : mem_grows MEM0 M1) by (unfold M1; apply mem_denot_grows).
    clearbody M1.
    (* [comment removed for export] *)
    destruct (fetchd_some _ _ envloop_code_0) as (w1 & F1 & E1 & D1).
    destruct (fetchd_some _ _ envloop_code_4) as (w2 & F2 & E2 & D2).
    destruct (fetchd_some _ _ envloop_code_8) as (w3 & F3 & E3 & D3).
    assert (He9 : getr R1 9%bv = Z_to_bv 64 (ENVP + 8 * Z.of_nat 0)).
    { rewrite (HR1 9%bv). change (sr_get _ 9%bv) with e_envp. apply bv_eq.
      rewrite u_small by (unfold ENVP; lia).
      pose proof (u_e_envp PH sp rdraw argv envp uid hw Hsp Hva Hve Hfit) as U. unfold EntryKn.uE in U.
      unfold E7. rewrite U. unfold ENVP, usp, argc. lia. }
    destruct (env_loop SEGS A_envloop w1 w2 w3 ltac:(unfold A_envloop; lia) F1 F2 F3 E1 E2 E3 D1 D2 D3
                M1 ROM ENVP (length envp) (cat_envp_ptr sp argv envp) ER)
      with (n := length envp) (k := 0%nat) (regs := R1)
      as (R2 & MS2 & P9 & P10 & Pag).
    - (* [comment removed for export] *) intros k Hk. split.
      + rewrite <- n_to_le_8_spec, <- (read_envp_ptr_k SEGS PH sp rdraw argv envp uid hw Hva Hve Hhi' k Hk), envp_slot_eq.
        apply rdn_above; [exact A1 | rewrite u_small; unfold ENVP in *; lia | rewrite u_small; unfold ENVP in *; change (Z.of_nat 8) with 8; lia].
      + apply (cat_envp_ptr_nz PH sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' k Hk).
    - (* [comment removed for export] *)
      rewrite <- n_to_le_8_spec, <- (read_envp_null SEGS PH sp rdraw argv envp uid hw Hva Hve Hhi'), envp_slot_eq.
      apply rdn_above; [exact A1 | rewrite u_small; unfold ENVP in *; lia | rewrite u_small; unfold ENVP in *; change (Z.of_nat 8) with 8; lia].
    - lia.
    - exact He9.
    - (* [comment removed for export] *)
      exists R2, M1. split; [|split; [|split; [exact HK1 | split; [exact A1 | exact G1]]]].
      + eapply msteps_trans; [exact MS1|]. rewrite envloop_exit_eq. exact MS2.
      + unfold SR2. apply (regs_ok_upd2 E7 _ R1 R2 9%bv 10%bv); try exact HR1;
          try (intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH).
        * rewrite P9. symmetry. apply bv_eq.
          pose proof (u_e_auxv PH sp rdraw argv envp uid hw Hsp Hva Hve Hfit) as U. unfold EntryKn.uE in U.
          unfold E7. rewrite U. rewrite u_small by (unfold ENVP in *; lia). unfold ENVP, usp, argc. lia.
        * rewrite P10. reflexivity.
        * intros r Hra Hrb. apply Pag. intros [C|C]; [apply Hra | apply Hrb]; exact C.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition PN : Z := usp + 8 * argc + 8 * envc + 184.
  Let s0 : list byte := nth 0 argv [].

  Definition is_kblob_k (k : nat) (K : kentry) : bool :=
    match K with KBlob _ _ k' => Nat.eqb k k' | _ => false end.

  #[using="sp rdraw envp uid hw Hva Hfit usp envc"] Lemma s0_len : Z.of_nat (length s0) <= 131071.
  Proof. unfold s0. destruct Hva as (H1 & _ & H3 & _). destruct argv as [|a t]; [cbn in H1; lia|]. cbn. inversion H3. lia. Qed.

  #[using="sp rdraw envp uid hw Hva Hfit usp envc"] Lemma s0_nonul : ~ In (Z_to_bv 8 0) s0.
  Proof. unfold s0. destruct Hva as (H1 & _ & _ & H4 & _). destruct argv as [|a t]; [cbn in H1; lia|]. cbn. inversion H4. assumption. Qed.

  #[using="rdraw uid hw Hsp Hva Hfit bsb"] Lemma PN_range : 0 <= PN /\ PN + Z.of_nat (length s0) + 2 < 2 ^ 48.
  Proof.
    pose proof usp_lo. pose proof usp_fit as SF.
    pose proof (argv0_end_le PH sp rdraw argv envp uid hw Hva) as AE. fold bsb in AE.
    unfold PN, usp, argc, envc, s0 in *. lia.
  Qed.

  #[using="Type"] Lemma x11_after_B2 : sr_get SR2e 11%bv = mkAlu ALU_ADD e_str0 (ELit 1).
  Proof. vmeq_refl. Qed.

  #[using="Hsp Hva Hve Hfit argc envc bsb s0"] Lemma phase2 : forall R M,
    regs_ok E7 SR2 R -> know_ok SEGS E7 M KN1 -> above_ok M -> mem_grows MEM0 M ->
    exists R' M', msteps SEGS (mkst R (Z_to_bv 64 A_envloop_exit) M ROM) (mkst R' (Z_to_bv 64 A_pnloop_exit) M' ROM)
      /\ regs_ok E7 SR3 R' /\ know_ok SEGS E7 M' KN3 /\ above_ok M' /\ mem_grows MEM0 M'.
  Proof.
    intros R M HR HK HA HG.
    pose proof usp_lo as SL. pose proof usp_fit as SF. pose proof len_av as LA. pose proof len_ev as LE.
    pose proof PN_range as PR. pose proof s0_len as SLEN.
    pose proof (u_e_str0 PH sp rdraw argv envp uid hw Hsp Hva Hve Hfit) as US0. unfold EntryKn.uE in US0.
    pose proof (u_e_str1 PH sp rdraw argv envp uid hw Hsp Hva Hve Hfit) as US1. unfold EntryKn.uE in US1.
    (* [comment removed for export] *)
    ms_block_with HR HK FUEL [A_pnloop] noscr 7%nat R2 HR2 HK2 MS2.
    lazymatch type of HK2 with know_ok _ _ ?m _ => set (M2 := m) in * end.
    assert (A2 : above_ok M2).
    { unfold M2. apply above_ok_block; [exact HA | vmc]. }
    assert (G2 : mem_grows MEM0 M2) by (unfold M2; eapply mem_grows_trans; [exact HG | apply mem_denot_grows]).
    clearbody M2. clear HR HK HA HG.
    (* [comment removed for export] *)
    destruct (fetchd_some _ _ pnloop_code_m8) as (w0 & F0 & NE0 & D0).
    destruct (fetchd_some _ _ pnloop_code_m4) as (w1 & F1 & NE1 & D1).
    destruct (fetchd_some _ _ pnloop_code_0) as (w2 & F2 & NE2 & D2).
    destruct (fetchd_some _ _ pnloop_code_4) as (w3 & F3 & NE3 & D3).
    destruct (fetchd_some _ _ pnloop_code_8) as (w4 & F4 & NE4 & D4).
    (* [comment removed for export] *)
    assert (Hrd : forall j, (j <= length s0)%nat -> rdn SEGS M2 (Z_to_bv 64 (PN + Z.of_nat j)) 1 = Some [byte_at s0 j]).
    { let i := kidx KN2 (is_kblob_k K_ARGV0) in
      pose proof (know_nth SEGS E7 M2 KN2 i _ HK2 eq_refl) as KB.
      cbn [kentry_ok] in KB. destruct KB as (Hfl & Hlen & Hby).
      lazymatch type of Hlen with _ = elenZ E7 ?n =>
        assert (Elen : elenZ E7 n = Z.of_nat (length s0) + 1)
          by (rewrite <- Hlen; unfold E7, E0; cbn [eb blobs0 K_ARGV0 K_RND Nat.eqb]; rewrite length_app; cbn [length]; unfold s0; lia)
      end.
      lazymatch type of Hby with (forall i, _ -> M2 (Z_to_bv 64 (?st + i)) = _) =>
        assert (Est : st = PN)
      end.
      { unfold estart. cbn [a_base a_off]. unfold E7. cbn [edenot]. rewrite !u_add64, !u_mul64, !u_small by lia.
        cbn [ev EntryKn.E0 vals_ev vals0 nth]. rewrite !u_small by lia.
        rewrite (Z.mod_small (8 * Z.of_nat (length argv))) by lia. rewrite (Z.mod_small (8 * Z.of_nat (length envp))) by lia.
        rewrite (Z.mod_small (8 * _ + _)) by lia. rewrite Z.mod_small by (unfold usp in *; lia).
        unfold PN, usp, argc, envc. lia. }
      intros j Hj. cbn [rdn].
      rewrite Est, Elen in Hby. rewrite (Hby (Z.of_nat j)) by lia. rewrite Nat2Z.id.
      unfold byte_at. unfold E7, E0. cbn [eb blobs0 K_ARGV0 K_RND Nat.eqb]. reflexivity. }
    assert (Hst : store_ok SEGS M2 (Z_to_bv 64 A_progname) 8 = true).
    { let i := kidx KN2 (is_kwr_cov (ELit 0) A_progname 8) in
      eapply (kwr_store_ok_lit SEGS E7 M2 KN2 i); [exact HK2 | reflexivity | ..]; unfold A_progname; lia. }
    destruct (pn_loop SEGS A_pnloop w0 w1 w2 w3 w4 ltac:(unfold A_pnloop; lia) F0 F1 F2 F3 F4 NE0 NE1 NE2 NE3 NE4 D0 D1 D2 D3 D4
                M2 ROM A_progname PN s0 ltac:(unfold A_progname; lia) ltac:(lia) ltac:(unfold A_progname, PN; lia) s0_nonul Hrd Hst
                s0 0%nat R2 M2 eq_refl ltac:(lia))
      as (R3 & M3 & MS3 & (P11 & P13 & Pag) & (C1 & C2)).
    - rewrite (HR2 10%bv). reflexivity.
    - rewrite (HR2 11%bv). change (sr_get _ 11%bv) with (mkAlu ALU_ADD e_str0 (ELit 1)). rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold E7. rewrite US0.
      change (1 mod 2 ^ 64) with 1. rewrite !Z.mod_small by (unfold PN, usp in *; lia). unfold PN, usp, argc, envc. lia.
    - rewrite (HR2 12%bv). reflexivity.
    - apply cellrel_refl.
    - (* [comment removed for export] *)
      exists R3, M3. split; [|split; [|split; [|split]]].
      + eapply msteps_trans; [exact MS2|]. rewrite pnloop_exit_eq. exact MS3.
      + unfold SR3. apply (regs_ok_upd2 E7 _ R2 R3 11%bv 13%bv); try exact HR2;
          try (intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH).
        * rewrite P11. symmetry. apply bv_eq. unfold E7. rewrite US1. rewrite u_small by (unfold PN in *; lia).
          unfold PN, usp, argc, envc, s0. lia.
        * rewrite P13. reflexivity.
        * intros r Hra Hrb. apply Pag. intros [C|C]; [apply Hra | apply Hrb]; exact C.
      + unfold KN3. apply (know_change_keep SEGS E7 M2 M3); [exact HK2 | | exact C2].
        intros x Hx. apply C1. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx.
        rewrite !u_small in Hx by (unfold A_progname; lia). lia.
      + intros x Hx. rewrite C1; [apply A2; exact Hx|]. unfold A_progname. right. unfold usp in *. lia.
      + eapply mem_grows_trans; [exact G2 | exact C2].
  Qed.

End Walk.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
