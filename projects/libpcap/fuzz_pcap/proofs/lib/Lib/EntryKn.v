(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition V_SP : nat := 0.
Definition V_ARGC : nat := 1.
Definition V_ENVC : nat := 2.
Definition V_L0 : nat := 3.
Definition V_W : nat := 4.
Definition V_UID : nat := 5.
Definition V_HW : nat := 6.
Definition NX0 : nat := 7.          (* [comment removed for export] *)
Definition K_ARGV0 : nat := 1.      (* [comment removed for export] *)
Definition K_RND : nat := 25.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition eadd (a b : expr) : expr := mkAlu ALU_ADD a b.
Definition escale (c : Z) (e : expr) : expr := mkMd M_MUL (ELit c) e.
Definition eaddz (a : expr) (z : Z) : expr := mkAlu ALU_ADD a (ELit z).

Definition e_sp : expr := EVar V_SP.
Definition e_envp : expr := eadd e_sp (eadd (escale 8 (EVar V_ARGC)) (ELit 16)).
Definition e_auxv : expr := eadd e_envp (eadd (escale 8 (EVar V_ENVC)) (ELit 8)).
Definition e_str0 : expr := eaddz e_auxv 160.
Definition e_str1 : expr := eadd e_str0 (eaddz (EVar V_L0) 1).
Definition e_atrandom : expr := eadd e_str0 (escale 8 (EVar V_W)).
(* [comment removed for export] *)
Definition e_argv1w : expr := EMd M_MUL (EAlu ALU_SLTU (ELit 1) (EVar V_ARGC)) e_str1.

Definition e_auxb : expr * Z := split_lit e_auxv.
Definition e_atrb : expr * Z := split_lit e_atrandom.
Definition e_strb : expr * Z := split_lit e_str0.
Definition auxw (i : Z) (ty : Z) (v : expr) : list kentry :=
  [KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty); KWord (SA (fst e_auxb) (snd e_auxb + 16 * i + 8)) 8 v].

Section Entry.
  Variable segs : list Segment.
  Variable ph : PhdrInfo.
  (* [comment removed for export] *)
  Variables ilo ihi rwlo rwlen : Z.
  Hypothesis Hhull : 0 <= ilo <= ihi /\ ihi <= 2 ^ 32.
  Hypothesis Hrw : (0 <= rwlo /\ 0 <= rwlen /\ rwlo + rwlen < 2 ^ 64)
                   /\ forall m (x : word), rwlo <= bv_unsigned x < rwlo + rwlen -> wview segs m x <> None.
  (* [comment removed for export] *)
  Variable kn_extra : list kentry.

  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  Let bsb := build_stack_bytes ph sp argv envp uid hw rdraw.
  Let SIMG := entry_stack_image ph sp argv envp uid hw rdraw.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  Let L0 := Z.of_nat (length s0).
  Let W := (Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184)) / 8.

  Definition M0 : word -> option byte := wrap_mem ph sp argv envp uid hw rdraw.
  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.

  Definition vals0 : list word :=
    [sp; Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W; uid; hw].
  Definition blobs0 (k : nat) : list byte :=
    if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw)
    else if Nat.eqb k K_ARGV0 then s0 ++ [Z_to_bv 8 0]
    else [].
  Definition E0 : env := Env (vals_ev vals0) blobs0.

  Definition kn0 : list kentry :=
    [KRange (EVar V_SP) 0x7fff80000000 0x7fffffffff40; KAlign (EVar V_SP) 16;
     KRange (eaddz e_atrandom 16) 0x7fff800000c0 0x800000000000;
     KRange (EVar V_ARGC) 1 1024; KRange (EVar V_ENVC) 0 256; KRange (EVar V_L0) 0 131071;
     KRange (EVar V_W) 0 280000; KRange (EVar V_UID) 0 0xFFFFFFFE;
     KWr (SA e_sp (-8388608)) (ELit 8388608); KZero (SA e_sp (-8388608)) (ELit 8388608);
     KWord (SA e_sp 0) 8 (EVar V_ARGC); KWord (SA e_sp 8) 8 e_str0; KWord (SA e_sp 16) 8 e_argv1w]
    ++ auxw 0 3 (ELit (Z.of_N (ph_addr ph))) ++ auxw 1 4 (ELit (Z.of_N (ph_ent ph))) ++ auxw 2 5 (ELit (Z.of_N (ph_num ph)))
    ++ auxw 3 16 (EVar V_HW) ++ auxw 4 6 (ELit 4096)
    ++ auxw 5 11 (EVar V_UID) ++ auxw 6 12 (EVar V_UID) ++ auxw 7 23 (ELit 0) ++ auxw 8 25 e_atrandom ++ auxw 9 0 (ELit 0)
    ++ [KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND;
        KBlob (SA (fst e_strb) (snd e_strb)) (eaddz (EVar V_L0) 1) K_ARGV0;
        KImg ilo ihi; KWr (SA (ELit 0) rwlo) (ELit rwlen)]
    ++ kn_extra.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hsp"] Lemma Hlo' : (sp_window_lo <= bv_unsigned sp)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  #[using="Hsp"] Lemma Hhi' : (bv_unsigned sp <= sp_window_hi)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  #[using="Hsp"] Lemma Hal' : (bv_unsigned sp mod 16 = 0)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  #[using="ph sp rdraw envp uid hw Hva bsb usp argc envc s0 L0 W"] Lemma Hav0 : (0 < length argv)%nat. Proof. destruct Hva as [[? ?] _]; lia. Qed.
  #[using="ph sp rdraw envp uid hw Hva bsb usp envc s0 L0 W"] Lemma len_av : 1 <= argc <= 1024. Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  #[using="ph sp rdraw argv uid hw Hve bsb usp argc s0 L0 W"] Lemma len_ev : 0 <= envc <= 256. Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  #[using="ph rdraw argv envp uid hw Hsp bsb argc envc s0 L0 W"] Lemma usp_lo : 0x7fff80000000 <= usp. Proof. pose proof Hlo'. unfold sp_window_lo in *. unfold usp. lia. Qed.
  (* [comment removed for export] *)
  Definition stack_image_size : Z :=
    let struct_size := (8 + (argc + 1) * 8 + (envc + 1) * 8 + 160)%Z in
    let len := (struct_size + total_arg_bytes argv + total_arg_bytes envp)%Z in
    (len + ((8 - len mod 8) mod 8) + 16)%Z.

  #[using="usp s0 L0 W"] Lemma length_bsb_eq : Z.of_nat (length bsb) = stack_image_size.
  Proof.
    unfold bsb, build_stack_bytes, stack_image_size, argc, envc. cbv zeta.
    rewrite (string_addrs_pair argv). cbv beta iota.
    rewrite (string_addrs_pair envp). cbv beta iota.
    rewrite !length_app, length_at_random_bytes, repeat_length, !length_flat_map_le8,
      !length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
      !length_flatten_strings.
    rewrite !total_arg_bytes_Z. unfold auxv_size.
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
    match goal with
    | |- context [Z.to_nat ?pd] =>
        assert (Hpd : (0 <= pd < 8)%Z) by (apply Z.mod_pos_bound; lia); rewrite (Z2Nat.id pd) by lia
    end.
    lia.
  Qed.

  #[using="Hfit argc envc s0 L0 W"] Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    pose proof (build_stack_bytes_within_span ph sp argv envp uid hw rdraw) as B. fold bsb in B.
    unfold entry_stack_fits, sp_window_hi in Hfit. unfold usp. lia.
  Qed.

  #[using="usp s0 L0 W"] Lemma bsb_ge : 8 * argc + 8 * envc + 200 <= Z.of_nat (length bsb) /\ (Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184)) mod 8 = 0.
  Proof.
    rewrite length_bsb_eq. unfold stack_image_size, argc, envc. cbv zeta.
    pose proof (total_arg_bytes_Z argv). pose proof (total_arg_bytes_Z envp).
    match goal with |- context [((8 - ?l mod 8) mod 8)%Z] => set (len := l) end.
    assert (0 <= Z.of_nat (total_arg_bytes_nat argv)) by lia.
    split; [lia|].
    assert (Hpd : 0 <= (8 - len mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Hm : (len + (8 - len mod 8) mod 8) mod 8 = 0).
    { rewrite <- Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r.
      replace (len mod 8 + (8 - len mod 8)) with 8 by lia. reflexivity. }
    replace (len + (8 - len mod 8) mod 8 + 16 - 16 - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184))
      with (len + (8 - len mod 8) mod 8 - 8 * (Z.of_nat (length argv) + Z.of_nat (length envp) + 23)) by (unfold len; lia).
    rewrite Zminus_mod, Hm, Z.mul_comm, Z_mod_mult. reflexivity.
  Qed.

  #[using="Hva Hve usp s0 L0"] Lemma W_range : 0 <= W /\ 8 * W = Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184) /\ W <= 280000.
  Proof.
    pose proof bsb_ge as [G M]. pose proof (bsb_bound ph sp argv envp uid hw rdraw Hva Hve) as B. fold bsb in B.
    unfold W. pose proof len_av. pose proof len_ev.
    lia.
  Qed.
  #[using="ph sp rdraw envp uid hw Hva bsb usp argc envc W"] Lemma L0_range : 0 <= L0 <= 131071.
  Proof. unfold L0, s0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. Qed.
  #[using="ph rdraw argv envp uid hw Hva Hve Hfit bsb argc envc s0 L0 W"] Lemma usp_hi : usp + 192 <= 2 ^ 47.
  Proof. pose proof usp_fit. pose proof bsb_ge. pose proof len_av. pose proof len_ev. lia. Qed.

  Definition uE (e : expr) : Z := bv_unsigned (edenot E0 e).

  #[using="Hsp Hva Hve Hfit"] Lemma uE0 :
    uE (EVar V_SP) = usp /\ uE (EVar V_ARGC) = argc /\ uE (EVar V_ENVC) = envc /\ uE (EVar V_L0) = L0
    /\ uE (EVar V_W) = W /\ uE (EVar V_UID) = bv_unsigned uid /\ uE (EVar V_HW) = bv_unsigned hw.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    pose proof L0_range.
    unfold uE. cbn [edenot E0 ev nth vals0 vals_ev V_SP V_ARGC V_ENVC V_L0 V_W V_UID V_HW].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.

  #[using="Type"] Lemma edenot_sp : edenot E0 e_sp = sp. Proof. reflexivity. Qed.
  #[using="Type"] Lemma edenot_uid : edenot E0 (EVar V_UID) = uid. Proof. reflexivity. Qed.
  #[using="Type"] Lemma edenot_hw : edenot E0 (EVar V_HW) = hw. Proof. reflexivity. Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma u_e_envp : uE e_envp = usp + 8 * argc + 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. destruct uE0 as (U0 & U1 & _).
    unfold e_envp, e_sp, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U0, U1. rewrite !Z.mod_small by lia. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma u_e_auxv : uE e_auxv = usp + 8 * argc + 8 * envc + 24.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. destruct uE0 as (_ & _ & U2 & _).
    pose proof u_e_envp as UE. unfold e_auxv, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UE, U2. rewrite !Z.mod_small by lia. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma u_e_str0 : uE e_str0 = usp + 8 * argc + 8 * envc + 184.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof u_e_auxv as UA. unfold e_str0, eaddz, uE in *. rewrite mkAlu_denot, edenot_lit.
    rewrite u_add64, u64_lit by lia. rewrite UA. rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma u_e_str1 : uE e_str1 = usp + 8 * argc + 8 * envc + 184 + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    destruct uE0 as (_ & _ & _ & U3 & _). pose proof L0_range.
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U3. rewrite !Z.mod_small by lia. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma u_e_atrandom : uE e_atrandom = usp + Z.of_nat (length bsb) - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    destruct uE0 as (_ & _ & _ & _ & U4 & _).
    pose proof u_e_str0 as US. unfold e_atrandom, eadd, escale, uE in *. rewrite mkAlu_denot, mkMd_denot, edenot_lit.
    rewrite u_add64, u_mul64, u64_lit by lia. rewrite US, U4. rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="bsb SIMG argc envc s0 L0 W"] Lemma M0_below : forall a : word, usp - 8388608 <= bv_unsigned a < usp -> M0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. unfold M0, wrap_mem.
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
    replace (Z.leb (bv_unsigned sp - 8 * 1024 * 1024) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  #[using="bsb SIMG argc envc s0 L0 W"] Lemma M0_low : forall a : word, bv_unsigned a < usp - 8388608 -> M0 a = None.
  Proof.
    intros a Ha. unfold M0, wrap_mem.
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
    replace (Z.leb (bv_unsigned sp - 8 * 1024 * 1024) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  #[using="bsb argc envc s0 L0 W"] Lemma rdn_M0_stack : forall (a : word) n,
    usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    rdn segs M0 a n = rdn segs (stack_to_mem sp SIMG) a n.
  Proof.
    intros a n Ha Hn. unfold M0, SIMG. apply rdn_wrap_stack_above; unfold usp in *; lia.
  Qed.

  #[using="ph sp rdraw argv envp uid hw bsb usp argc envc s0 L0 W"] Lemma firstn1_skipn_nth : forall (l : list byte) (i : nat) (d : byte),
    (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
  Proof.
    induction l as [|x l IH]; intros i d Hi; cbn in Hi; [lia|].
    destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
  Qed.

  #[using="ph sp rdraw argv envp uid hw bsb usp argc envc s0 L0 W"] Lemma split_lit_denot : forall E e b k, split_lit e = (b, k) ->
    edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
  Proof.
    intros E e b k H.
    assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
    { intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    unfold split_lit in H.
    destruct e; try (injection H as <- <-; apply G).
    - injection H as <- <-. cbn [edenot]. rewrite u64_lit by lia. rewrite Z.add_0_l. reflexivity.
    - lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
      lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
      injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
      rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
  Qed.

  #[using="usp"] Lemma split_u : forall e b k, split_lit e = (b, k) -> 0 <= k -> k <= uE e ->
    bv_unsigned (edenot E0 b) + k = uE e.
  Proof.
    intros e b k Hs Hk Hle. unfold uE in *. rewrite (split_lit_denot E0 e b k Hs) in Hle |- *.
    pose proof (u64_range (edenot E0 b)) as Rb.
    rewrite Z_to_bv_unsigned in Hle |- *. unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
    destruct (Z_lt_le_dec (bv_unsigned (edenot E0 b) + k) (2 ^ 64)).
    - rewrite Z.mod_small by lia. reflexivity.
    - exfalso.
      assert ((bv_unsigned (edenot E0 b) + k) mod 2 ^ 64 = bv_unsigned (edenot E0 b) + k - 2 ^ 64).
      { replace (bv_unsigned (edenot E0 b) + k) with ((bv_unsigned (edenot E0 b) + k - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      lia.
  Qed.

  #[using="Type"] Lemma adenot_SA : forall E b k, adenot E (SA b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
  Proof. intros. unfold adenot, v_addi. cbn [a_base a_off]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hfit"] Lemma kword_stack : forall b k v (w : word),
    bv_unsigned (edenot E0 b) + k = bv_unsigned w ->
    usp <= bv_unsigned w -> bv_unsigned w + 8 <= usp + Z.of_nat (length bsb) ->
    rdn segs (stack_to_mem sp SIMG) w 8%nat = Some (word_le8 (edenot E0 v)) ->
    kentry_ok segs E0 M0 (KWord (SA b k) 8 v).
  Proof.
    intros b k v w Hw Hlo Hhi Hrd. pose proof usp_fit. pose proof usp_lo. pose proof (u64_range w).
    cbn [kentry_ok]. split; [lia|].
    assert (Hfl : flat E0 (SA b k) (Z.of_nat 8)) by (unfold flat, estart; cbn [a_base a_off]; change (Z.of_nat 8) with 8; lia).
    split; [exact Hfl|].
    rewrite adenot_SA. rewrite Hw, Z_to_bv_bv_unsigned.
    rewrite rdn_M0_stack; [| lia | change (Z.of_nat 8) with 8; lia].
    rewrite Hrd. rewrite n_to_le_8_spec. reflexivity.
  Qed.

  #[using="Type"] Lemma auxb_eq : split_lit e_auxv = (fst e_auxb, snd e_auxb).
  Proof. unfold e_auxb; destruct (split_lit e_auxv); reflexivity. Qed.
  #[using="Type"] Lemma auxk_eq : snd e_auxb = 24. Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit SIMG usp"] Lemma auxv_word_ok : forall (j : nat) v,
    (j < 20)%nat ->
    nth j (auxv_words ph (at_random_ptr sp argv envp) uid hw) (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 M0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u e_auxv ab ak auxb_eq) as Hs. rewrite u_e_auxv in Hs.
    pose proof auxk_eq as Hak. fold ak in Hak.
    specialize (Hs ltac:(lia) ltac:(lia)).
    apply (kword_stack ab (ak + 8 * Z.of_nat j) v (sp + nat_to_word (auxv_off argv envp + 8 * j))%bv).
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - rewrite <- Hv. exact (read_auxv_word segs ph sp rdraw argv envp uid hw Hva Hve Hhi' j Hj).
  Qed.

  #[using="Hsp Hva Hve Hfit SIMG usp"] Lemma auxw_ok : forall i ty v,
    (0 <= i <= 9) ->
    nth (Z.to_nat (2 * i)) (auxv_words ph (at_random_ptr sp argv envp) uid hw) (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1)) (auxv_words ph (at_random_ptr sp argv envp) uid hw) (Z_to_bv 64 0) = edenot E0 v ->
    know_ok segs E0 M0 (auxw i ty v).
  Proof.
    intros i ty v Hi H1 H2. unfold auxw.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
  Qed.

  #[using="Type"] Lemma kr_ok : forall e lo hi, lo <= uE e <= hi -> kentry_ok segs E0 M0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  #[using="Hsp Hva Hve Hfit SIMG usp"] Lemma stack_window_ok :
    kentry_ok segs E0 M0 (KWr (SA e_sp (-8388608)) (ELit 8388608))
    /\ kentry_ok segs E0 M0 (KZero (SA e_sp (-8388608)) (ELit 8388608)).
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    assert (Hst : estart E0 (SA e_sp (-8388608)) = usp - 8388608).
    { unfold estart. cbn [a_base a_off]. rewrite edenot_sp. lia. }
    assert (Hl : elenZ E0 (ELit 8388608) = 8388608) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
    assert (Hfl : flat E0 (SA e_sp (-8388608)) (elenZ E0 (ELit 8388608))).
    { unfold flat. rewrite Hst, Hl. lia. }
    split; cbn [kentry_ok]; (split; [exact Hfl|]); rewrite Hst, ?Hl.
    - intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by lia; [lia|].
      intros x Hx. unfold wview. rewrite (M0_below x) by lia. discriminate.
    - intros i Hi. apply M0_below. rewrite u_small by lia. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit SIMG usp"] Lemma argc_word_ok : kentry_ok segs E0 M0 (KWord (SA e_sp 0) 8 (EVar V_ARGC)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    apply (kword_stack e_sp 0 (EVar V_ARGC) sp).
    - rewrite edenot_sp. unfold usp. lia.
    - unfold usp. lia.
    - unfold usp in *. lia.
    - pose proof (read_argc ph segs sp argv envp uid hw rdraw) as RW.
      assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
      { apply bv_eq. destruct uE0 as (_ & U1 & _). unfold uE in U1. rewrite U1. unfold argc. exact (u_argcN argv Hva). }
      rewrite <- Hv. apply RW. fold bsb. unfold usp in *. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit SIMG usp"] Lemma argv0_word_ok : kentry_ok segs E0 M0 (KWord (SA e_sp 8) 8 e_str0).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    apply (kword_stack e_sp 8 e_str0 (sp + nat_to_word (8 + 8 * 0))%bv).
    - rewrite edenot_sp. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - pose proof (read_argv_ptr_k ph segs sp argv envp 0 uid hw rdraw Hav0) as RW.
      assert (Hv : cat_argv_ptr sp argv envp 0 = edenot E0 e_str0).
      { apply bv_eq. rewrite (@u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' 0 Hav0).
        pose proof u_e_str0 as U. unfold uE in U. rewrite U. unfold cat_struct_size, auxv_size. replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat by reflexivity.
        unfold usp, argc, envc. lia. }
      rewrite <- Hv. apply RW. fold bsb. unfold usp in *. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit SIMG usp"] Lemma argv1_word_ok : kentry_ok segs E0 M0 (KWord (SA e_sp 16) 8 e_argv1w).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    pose proof L0_range as HL0.
    assert (Hw1 : edenot E0 e_argv1w = if (1 <? argc) then edenot E0 e_str1 else Z_to_bv 64 0).
    { unfold e_argv1w. cbn [edenot]. destruct uE0 as (_ & U1 & _). unfold uE in U1. cbn [edenot] in U1.
      apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U1 by lia.
      pose proof (u64_range (edenot E0 e_str1)).
      destruct (1 <? argc); [rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity | rewrite u64_lit by lia; reflexivity]. }
    apply (kword_stack e_sp 16 e_argv1w (sp + nat_to_word (8 + 8 * 1))%bv).
    - rewrite edenot_sp. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite Hw1. destruct (1 <? argc) eqn:Hc.
      + apply Z.ltb_lt in Hc. assert (Hav1 : (1 < length argv)%nat) by (unfold argc in Hc; lia).
        pose proof (read_argv_ptr_k ph segs sp argv envp 1 uid hw rdraw Hav1) as RW.
        assert (Hv : cat_argv_ptr sp argv envp 1 = edenot E0 e_str1).
        { apply bv_eq. rewrite (@u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' 1 Hav1).
          pose proof u_e_str1 as U. unfold uE in U. rewrite U. unfold cat_struct_size, auxv_size.
          assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                        Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
            by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
          rewrite Nat2Z.inj_add, (TF argv Hav0). unfold L0, s0, usp, argc, envc. lia. }
        rewrite <- Hv. apply RW. fold bsb. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        pose proof (read_argv_null segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as RW. rewrite Hav1 in RW.
        exact RW.
  Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit SIMG usp"] Lemma atrandom_ok : kentry_ok segs E0 M0 (KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
    set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
    pose proof (split_u e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 184) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + Z.of_nat (length bsb) - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    assert (HE : eb E0 K_RND = at_random_bytes (ed_random rdraw)) by reflexivity.
    rewrite HE.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    split; [rewrite length_at_random_bytes; reflexivity|].
    intros i Hi.
    destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & Hrd)].
    fold bsb in Hlen.
    assert (Hu : bv_unsigned (at_random_ptr sp argv envp) = usp + Z.of_nat off).
    { rewrite Hp, word_add_nat. apply u64_lit. unfold usp in *. lia. }
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd. fold SIMG in Hrd.
    rewrite (firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
    assert (Ha : (at_random_ptr sp argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    unfold M0. rewrite (wrap_above_sp ph sp argv envp _ uid hw rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    cbn [rdn] in Hrd.
    destruct (stack_to_mem sp SIMG (Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i))) as [b|] eqn:Hstk.
    - cbn in Hrd. injection Hrd as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + Z.of_nat (length bsb) - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, entry_stack_image; cbv zeta; rewrite length_app; fold bsb; lia).
      replace (usp + Z.of_nat (length bsb) - 16 + i - usp <? Z.of_nat (length SIMG)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva W"] Lemma argv0_end_le : usp + 8 * argc + 8 * envc + 184 + L0 + 1 <= usp + Z.of_nat (length bsb).
  Proof.
    destruct (bsb_byte_k ph sp argv envp 0 uid hw rdraw Hav0) as [pre [post [E Hlen]]].
    pose proof (f_equal (@length byte) E) as HL. rewrite !length_app in HL. cbn [length] in HL.
    fold bsb in HL. rewrite Hlen in HL. unfold cat_struct_size, auxv_size in HL.
    replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat in HL by reflexivity.
    fold s0 in HL. unfold L0, argc, envc. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit SIMG usp"] Lemma argv0_str_ok : kentry_ok segs E0 M0 (KBlob (SA (fst e_strb) (snd e_strb)) (eaddz (EVar V_L0) 1) K_ARGV0).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    pose proof L0_range as HL0. pose proof argv0_end_le as HEND.
    assert (Hab : split_lit e_str0 = (fst e_strb, snd e_strb)) by (unfold e_strb; destruct (split_lit e_str0); reflexivity).
    set (ab := fst e_strb) in *. set (ak := snd e_strb) in *.
    pose proof (split_u e_str0 ab ak Hab) as Hs. rewrite u_e_str0 in Hs.
    assert (Hak : ak = 184) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + 8 * argc + 8 * envc + 184) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (eaddz (EVar V_L0) 1) = L0 + 1).
    { unfold elenZ, eaddz. rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & U3 & _). unfold uE in U3. rewrite U3. apply Z.mod_small. lia. }
    assert (HE : eb E0 K_ARGV0 = s0 ++ [Z_to_bv 8 0]) by reflexivity.
    pose proof (@u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' 0 Hav0) as Hp0.
    unfold cat_struct_size, auxv_size in Hp0. replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat in Hp0 by reflexivity.
    assert (Hp0' : bv_unsigned (cat_argv_ptr sp argv envp 0) = usp + 8 * argc + 8 * envc + 184) by (unfold usp, argc, envc; lia).
    cbn [kentry_ok]. rewrite Hst, Hl, HE.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    split; [rewrite length_app; cbn [length]; unfold L0; lia|].
    intros i Hi.
    pose proof (read_argv_byte_k ph segs sp argv envp 0 (Z.to_nat i) uid hw rdraw Hav0 ltac:(fold s0; unfold L0 in Hi; lia)
                  ltac:(fold bsb; unfold usp in *; lia)) as RB.
    fold SIMG in RB. fold s0 in RB.
    rewrite word_add_nat, Hp0' in RB. rewrite Z2Nat.id in RB by lia.
    unfold M0. rewrite (wrap_above_sp ph sp argv envp _ uid hw rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    cbn [rdn] in RB.
    destruct (stack_to_mem sp SIMG (Z_to_bv 64 (usp + 8 * argc + 8 * envc + 184 + i))) as [b|] eqn:Hstk.
    - cbn in RB. injection RB as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + 8 * argc + 8 * envc + 184 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, entry_stack_image; cbv zeta; rewrite length_app; fold bsb; lia).
      replace (usp + 8 * argc + 8 * envc + 184 + i - usp <? Z.of_nat (length SIMG)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
  Qed.

  #[using="Hhull Hsp SIMG"] Lemma kimg_ok : ihi <= usp - 8388608 -> kentry_ok segs E0 M0 (KImg ilo ihi).
  Proof.
    intros Hh. pose proof usp_lo. destruct Hhull as [H1 H2]. cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    apply M0_low. rewrite u64_lit; lia.
  Qed.

  #[using="Hrw usp"] Lemma rw_window_ok : kentry_ok segs E0 M0 (KWr (SA (ELit 0) rwlo) (ELit rwlen)).
  Proof.
    destruct Hrw as ((R1 & R0 & R2) & R3).
    assert (Hst : estart E0 (SA (ELit 0) rwlo) = rwlo) by (unfold estart; cbn [a_base a_off]; rewrite edenot_lit, u64_lit; lia).
    assert (Hl : elenZ E0 (ELit rwlen) = rwlen) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; lia|].
    intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
    assert (Hu : bv_unsigned (Z_to_bv 64 (rwlo + d)) = rwlo + d) by (apply u_small; rewrite Nat2Z.inj_succ in Hdm; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. apply R3. lia.
  Qed.

  #[using="segs Hsp Hva Hve Hfit usp"] Lemma atr_ptr_eq : at_random_ptr sp argv envp = edenot E0 e_atrandom.
  Proof.
    pose proof usp_lo. pose proof usp_fit.
    destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & _)]. fold bsb in Hlen.
    apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia).
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold usp. lia.
  Qed.

  Hypothesis Hextra : know_ok segs E0 M0 kn_extra.

  #[using="Hhull Hrw Hsp Hva Hve Hfit Huid SIMG usp Hextra"] Theorem kn0_ok : know_ok segs E0 M0 kn0.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    pose proof bsb_ge as [G _]. destruct Hhull as [I1 I2]. pose proof L0_range.
    destruct uE0 as (U0 & U1 & U2 & U3 & U4 & U5 & U6).
    pose proof stack_window_ok as [SW1 SW2].
    pose proof (auxv_words_eq ph uid hw (at_random_ptr sp argv envp)) as AW.
    unfold kn0. unfold know_ok.
    repeat (apply Forall_app; split).
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply kr_ok. lia.
      + cbn [kentry_ok]. split; [lia|]. unfold uE in U0. rewrite U0. exact Hal'.
      + apply kr_ok. pose proof u_e_atrandom as UA. unfold uE in UA |- *. unfold eaddz. rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit, UA by lia.
        rewrite Z.mod_small by lia. lia.
      + apply kr_ok. lia.
      + apply kr_ok. lia.
      + apply kr_ok. lia.
      + apply kr_ok. lia.
      + apply kr_ok. rewrite U5. unfold valid_id in Huid. pose proof (u64_range uid). lia.
      + exact SW1.
      + exact SW2.
      + apply argc_word_ok.
      + apply argv0_word_ok.
      + apply argv1_word_ok.
    - apply auxw_ok; [lia | rewrite AW; reflexivity | rewrite AW, edenot_lit; reflexivity].
    - apply auxw_ok; [lia | rewrite AW; reflexivity | rewrite AW, edenot_lit; reflexivity].
    - apply auxw_ok; [lia | rewrite AW; reflexivity | rewrite AW, edenot_lit; reflexivity].
    - apply auxw_ok; [lia | rewrite AW; reflexivity | rewrite AW, edenot_hw; reflexivity].
    - apply auxw_ok; [lia | rewrite AW; reflexivity | rewrite AW, edenot_lit; reflexivity].
    - apply auxw_ok; [lia | rewrite AW; reflexivity | rewrite AW, edenot_uid; reflexivity].
    - apply auxw_ok; [lia | rewrite AW; reflexivity | rewrite AW, edenot_uid; reflexivity].
    - apply auxw_ok; [lia | rewrite AW; reflexivity | rewrite AW, edenot_lit; reflexivity].
    - apply auxw_ok; [lia | rewrite AW; reflexivity | rewrite AW; rewrite <- atr_ptr_eq; reflexivity].
    - apply auxw_ok; [lia | rewrite AW; reflexivity | rewrite AW, edenot_lit; reflexivity].
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply atrandom_ok.
      + apply argv0_str_ok.
      + apply kimg_ok. lia.
      + apply rw_window_ok.
    - exact Hextra.
  Qed.

  #[using="Type"] Theorem regs0_ok : regs_ok E0 sr_init R0.
  Proof. unfold E0, vals0, R0. apply regs_ok_init. Qed.

End Entry.
