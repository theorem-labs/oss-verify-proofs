(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput; the CONFIG_RSEQ flag; the new auxv layout; the launch's stack window; the recorded proofs of D_main_none, seg_rom_high, rdn_pointwise_inv, total_arg_bytes_firstn_S, nth_all_regs, regs_ok_by_index and 28 more replaced by plain proofs). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv SymExec MemSplit RefLayout StartupTac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23StartupDefs V23Startup V23StartupFacts.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP1.
Lemma D_main_none : forall sp0 inp drw tid (i : Z),
  valid_argv (in_argv inp) -> (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  D_main_missb i 1 = true ->
  D_main sp0 inp drw tid (Z_to_bv 64 i) = None.
Proof.
  intros sp0 inp drw tid i Hva Hlo Hhi Hb.
  pose proof (u64_range tid) as Ht.
  unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
  repeat match goal with
         | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
         end.
  repeat match goal with
         | H : range_disjoint_b _ _ _ = true |- _ =>
             apply range_disjoint_djw in H; cbn [fst snd] in H
         | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
         | H : true = true |- _ => clear H
         end.
  assert (Hui : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small; lia).
  unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
  repeat (rewrite MemSplit.wbytes_outside;
    [ | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
      | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Hui; rewrite u_small by (cbn; lia);
        match goal with H : djw _ |- _ => unfold djw in H; clear -H; lia end ]).
  reflexivity.
Qed.
End VP1.

(* [comment removed for export] *)
Section VP2.
Lemma seg_rom_high : forall (a : word), (0x159000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
Proof.
  intros a Ha. unfold seg_rom. unfold memory_read.
  cbn -[bv_unsigned Z.leb Z.ltb Z.add Z.sub N.leb N.ltb N.add bv_extract Z.of_N Z.to_N].
  cbn [Z.of_N].
  repeat (lazymatch goal with
          | |- context [((?lo <=? bv_unsigned a)%Z && ?c)%bool] =>
              replace c with false by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r
          end).
  reflexivity.
Qed.
End VP2.

(* [comment removed for export] *)
Section VP3.
Lemma rdn_pointwise_inv : forall segs m n (a : word) bs,
  (forall j, (j < n)%nat -> seg_rom segs (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = None) ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn segs m a n = Some bs ->
  forall j, (j < n)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof.
  intros segs m n. induction n as [|n IH]; intros a bs Hseg Hnw Hr j Hj; [lia|].
  cbn [rdn] in Hr. pose proof (u64_range a) as Ha.
  pose proof (Hseg 0%nat ltac:(lia)) as H0. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0.
  destruct (m a) as [b|] eqn:Hm.
  - destruct (rdn segs m (a + 1) n) as [rest|] eqn:Hr'; [|discriminate]. injection Hr as <-.
    destruct j as [|j].
    + rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned. exact Hm.
    + cbn [nth]. assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
      replace (bv_unsigned a + Z.of_nat (S j))%Z with (bv_unsigned (a + 1) + Z.of_nat j)%Z by lia.
      apply (IH (a + 1) rest); [ | lia | exact Hr' | lia].
      intros k Hk. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat k)%Z with (bv_unsigned a + Z.of_nat (S k))%Z by lia.
      apply Hseg. lia.
  - rewrite H0 in Hr. discriminate.
Qed.
End VP3.

(* [comment removed for export] *)
Lemma total_arg_bytes_firstn_S : forall k l, (k < length l)%nat ->
  (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1 <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros l Hk.
  - destruct l as [|s0 l']; [cbn in Hk; lia|]. cbn [firstn nth]. rewrite total_arg_bytes_cons. cbn. lia.
  - destruct l as [|s0 l']; [cbn in Hk; lia|]. cbn [firstn nth length] in *. rewrite !total_arg_bytes_cons.
    specialize (IH l' ltac:(lia)). lia.
Qed.

Section MainEntry.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable ev : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av ev tid regs mem.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Definition p0 : word := cat_argv_ptr (ed_top a_draw) av ev a_execfn 0.
  Definition p1 : word := cat_argv_ptr (ed_top a_draw) av ev a_execfn 1.
  Definition auxvp : word := auxv_w sp0 (inpA av ev).
  Definition rnd : word := at_random_ptr sp0 (kb_rseq a_kernel) av ev.

  (* [comment removed for export] *)
  Definition vals0 : list word := [sp0; p0; p1; auxvp; rnd; tid] ++ junk_vals regs.
  Definition blobs0 : list (list byte) := [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]; guard_bytes a_draw].   (* [comment removed for export] *)
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  Definition sr_main : list expr :=
    [ELit 0; ELit 0x10df20; spx (-48); ELit 0x10800; ELit 0x1381d0; EVar 11; EVar 12; EVar 13;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x63140; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-6144513)) 6144513;
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  Definition kn_auxv : list kentry :=   (* [comment removed for export] *) [].

  Definition kn_image : list kentry :=
    [KWr (SA (ELit 0) 0x127000) 0x32000;
     KImg 0x10000 0x127ec0;
     KImg 0x127ec1 0x127f09; KImg 0x127f09 0x137f09; KImg 0x137f09 0x138100; (* [comment removed for export] *) KImg 0x1381e8 0x1581f8;
     KWord (SA (ELit 0) 0x138108) 8 (ELit 0x138108);
     KWord (SA (ELit 0) 0x138128) 4 (EVar 5);
     KImg 0x138134 0x138180; KImg 0x138188 0x1381a0; KImg 0x1381a8 0x1381c0;
     (* [comment removed for export] *)
     KImg 0x1381d0 0x1381e0; KImg 0x158210 0x158440;
     KBlob (SA (ELit 0) 0x158440) (ELit 8) 2;   (* [comment removed for export] *)
     KImg 0x158448 0x158450;
     KImg 0x158461 0x158468; KWord (SA (ELit 0) 0x158468) 8 (EVar 3);
     KImg 0x158470 0x158478; KImg 0x158488 0x158490; KWord (SA (ELit 0) 0x158490) 8 (ELit 4096);
     KImg 0x158498 0x1584c8; (* [comment removed for export] *) KImg 0x1584d0 0x158880; KImg 0x158890 0x159000; (* [comment removed for export] *)
     KRange (EVar 5) 1 4194303;
     KImg 0 0x1000 (* [comment removed for export] *)].

  (* [comment removed for export] *)
  Definition kn_main : list kentry := kn_stack ++ kn_auxv ++ kn_image.
End MainEntry.

Definition all_regs : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Section VP4.
Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.
End VP4.

Section VP5.
Lemma regs_ok_by_index : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (nth i all_regs 0%bv) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot].
    reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.
End VP5.

Section MainEntryProofs.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid regs mem.

  Let E := E0 sp0 a0s path envv tid regs.

  Lemma sp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Proof. exact (proj1 Hvsp). Qed.
  Lemma sp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma sp_al : (bv_unsigned sp0 mod 16 = 0)%Z.
  Proof. exact (proj2 (proj2 Hvsp)). Qed.

  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 a0s path envv; p1 a0s path envv; auxvp sp0 a0s path envv; rnd sp0 a0s path envv; tid] ++ junk_vals regs) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  Lemma ev_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 a0s path envv; p1 a0s path envv; auxvp sp0 a0s path envv; rnd sp0 a0s path envv; tid] + i)%nat.
    rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.

Section MainRegs.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid regs mem.
  Let E := E0 sp0 a0s path envv tid regs.

  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ lazymatch goal with |- _ = edenot _ (spx ?k) =>
                    transitivity (Z_to_bv 64 (bv_unsigned sp0 + k)); [| symmetry; exact (spx_val sp0 a0s path envv tid regs k)] end
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk sp0 a0s path envv tid regs (n - 6)) by lia; reflexivity | idtac ]
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | apply (me_szero _ _ _ _ _ _ ME); cbn; tauto
                | idtac ].

  Theorem main_regs_ok : regs_ok E sr_main regs.
  Proof.
    pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
  Qed.
End MainRegs.

Section KnowProofs.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid regs mem.
  Let E := E0 sp0 a0s path envv tid regs.

  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z.
  Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0.
  Proof. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 a0s path envv.
  Proof. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 a0s path envv.
  Proof. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp sp0 a0s path envv.
  Proof. reflexivity. Qed.
  Lemma ke4 : ev E 4 = rnd sp0 a0s path envv.
  Proof. reflexivity. Qed.
  Lemma ke5 : ev E 5 = tid.
  Proof. reflexivity. Qed.

  Lemma know_stack : know_ok RSEGS E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    unfold kn_stack, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win sp0 av envv tid regs mem ME); rewrite u_small by lia;
        unfold wok_lo, stack_window_reach, stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (me_argc sp0 av envv tid regs mem ME Hva Hve Hvsp RSEGS).
      rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      pose proof (me_argv_ptr sp0 av envv tid regs mem ME Hva Hve Hvsp RSEGS 0%nat ltac:(subst av; cbn; lia)) as Hr.
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      pose proof (me_argv_ptr sp0 av envv tid regs mem ME Hva Hve Hvsp RSEGS 1%nat ltac:(subst av; cbn; lia)) as Hr.
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      pose proof (me_argv_null sp0 av envv tid regs mem ME Hva Hve Hvsp RSEGS) as Hr.
      rewrite w_add_nat in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  Lemma auxvp_eq : auxvp sp0 a0s path envv = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_w, auxv_off, inpA, mkProcInputC. cbn [in_argv in_envp]. subst av. cbn [length]. f_equal. lia. Qed.


  Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof. unfold kn_auxv, know_ok. apply Forall_nil. Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxvp : forall segs,
    rdn segs (D_main sp0 (inpA av envv) a_draw tid) (Z_to_bv 64 0x158468) 8
    = Some (word_to_le_bytes 8 (auxvp sp0 a0s path envv)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof kp_lo. pose proof kp_hi.
    unfold auxvp, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x127000) 0x32000 = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)

  Lemma range_disjoint_sub : forall lo n c i, range_disjoint_b lo n c = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> range_disjoint_b i 1 c = true.
  Proof.
    intros lo n [c w] i H Hlo Hhi. unfold range_disjoint_b in *. cbn [fst snd] in *.
    apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  Qed.

  Lemma missb_sub : forall lo n i, D_main_missb lo n = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> D_main_missb i 1 = true.
  Proof.
    intros lo n i H Hlo Hhi. unfold D_main_missb in *.
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia].
    apply forallb_forall. intros c Hc. apply (range_disjoint_sub lo n); [|lia|lia].
    apply (proj1 (forallb_forall _ _) H1). exact Hc.
  Qed.

  (* [comment removed for export] *)
  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x159000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 (inpA av envv) a_draw tid i Hva); [lia | lia |].
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_mem L := kw_pre; rewrite (L RSEGS); try reflexivity.

  Lemma know_image : know_ok RSEGS E mem kn_image.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimg;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - (* [comment removed for export] *) split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x127000) (Z_to_bv 64 (0x127000 + d)) 0x32000 m 0x127000 0x159000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_data (D_main_self sp0 av envv tid).
    - kw_mem (main_entry_tid sp0 av envv tid Hlo regs mem ME).
    - (* [comment removed for export] *)
      rewrite (u_small 8) by lia.
      split; [lia|]. split; [change (eb E 2) with (guard_bytes a_draw); rewrite length_guard_bytes; reflexivity|].
      intros i Hi. change (eb E 2) with (guard_bytes a_draw).
      rewrite (main_entry_mem_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
      rewrite Z.add_0_l. apply (D_main_guard_at sp0 av envv tid). lia.
    - kw_data D_main_auxvp.
    - kw_data (D_main_pagesize sp0 av envv tid Hva).
    - (* [comment removed for export] *) lia.
  Qed.


  Theorem main_know_ok : know_ok RSEGS E mem kn_main.
  Proof.
    unfold kn_main, know_ok.
    apply Forall_app; split; [apply know_stack|].
    apply Forall_app; split; [apply know_auxv | apply know_image].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma main_str_fits : forall k, (k < 2)%nat -> entry_stack_fits sp0 av envv ->
    (bv_unsigned (cat_argv_ptr (ed_top a_draw) av envv a_execfn k) + Z.of_nat (length (nth k av [])) + 1 <= 0x800000000000)%Z.
  Proof using Hva Hve Hvsp ME.
    intros k Hk _. assert (Hk' : (k < length av)%nat) by (subst av; cbn; lia).
    exact (me_argv_fits sp0 av envv tid regs mem ME Hva Hve Hvsp k Hk').
  Qed.

  Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top a_draw) av envv a_execfn k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top a_draw) av envv a_execfn k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top a_draw) av envv a_execfn k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z.
  Proof using Hva Hve Hvsp ME.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    assert (Hk' : (k < length av)%nat) by (subst av; cbn; lia).
    destruct (me_argv_bounds sp0 av envv tid regs mem ME Hva Hve Hvsp k Hk') as [B1 B2].
    pose proof (me_argv_near sp0 av envv tid regs mem ME Hva Hve Hvsp k Hk') as Bn.
    pose proof (valid_argv_str_len av k Hva Hk') as Hlen.
    repeat split.
    - apply rdn_app.
      + exact (me_argv_str sp0 av envv tid regs mem ME Hva Hve Hvsp RSEGS k Hk').
      + pose proof (me_argv_byte sp0 av envv tid regs mem ME Hva Hve Hvsp RSEGS k (length (nth k av [])) Hk' ltac:(lia)) as Hb.
        rewrite app_nth2, Nat.sub_diag in Hb by lia. cbn [nth] in Hb. exact Hb.
    - exact B1.
    - lia.
    - exact Hlen.
  Qed.
End KnowProofs.
