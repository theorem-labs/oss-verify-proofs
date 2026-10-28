(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  WsegFast PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv
  SymExec SymExec2 SymExec2Sound SymRun SymDrive
  MemSplit RefLayout StartupTac ClaBytes HUStartupDefs HUStartup4 HUStartup HUStartupFacts.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Export HUMainEntryDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma D_main_none : forall sp0 av ev hw rdraw tid (i : Z),
  valid_argv av -> (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  D_main_missb i 1 = true ->
  D_main sp0 av ev hw rdraw tid (Z_to_bv 64 i) = None.
Proof.
  intros sp0 av ev hw rdraw tid i Hva Hlo Hhi Hb.
  pose proof (u64_range tid) as Ht. pose proof (u64_range hw) as Hh.
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
    [ | rewrite ?length_N_to_le_bytes, ?len_guard_lo, ?len_guard_hi, ?len_canary8; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
      | rewrite ?length_N_to_le_bytes, ?len_guard_lo, ?len_guard_hi, ?len_canary8; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Hui; rewrite u_small by (cbn; lia);
        match goal with H : djw _ |- _ => unfold djw in H; clear -H; lia end ]).
  reflexivity.
Qed.

(* [comment removed for export] *)
Ltac dm_side := rewrite ?length_N_to_le_bytes, ?len_guard_lo, ?len_guard_hi, ?len_canary8;
                cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?u_small by (cbn; lia); cbn; lia.

Lemma D_main_canary_at : forall sp0 av ev hw rdraw tid (i : Z), (0 <= i < 8)%Z ->
  D_main sp0 av ev hw rdraw tid (Z_to_bv 64 (0x331ad8 + i)) = Some (nth (Z.to_nat i) (canary8 rdraw) (Z_to_bv 8 0)).
Proof.
  intros sp0 av ev hw rdraw tid i Hi. pose proof (len_canary8 rdraw) as L8.
  unfold D_main, D_fd, D_ssp.
  rewrite MemSplit.wbytes_outside by dm_side.
  rewrite MemSplit.wbytes_inside by dm_side.
  f_equal. f_equal. rewrite !u_small by lia. lia.
Qed.

Lemma canary8_nth : forall rdraw (i : Z), (0 <= i < 8)%Z ->
  nth (Z.to_nat i) (canary8 rdraw) (Z_to_bv 8 0)
  = if (i =? 1)%Z then Z_to_bv 8 0
    else if (i <? 4)%Z then nth (Z.to_nat i) (guard_lo rdraw) (Z_to_bv 8 0)
    else nth (Z.to_nat (i - 4)) (guard_hi rdraw) (Z_to_bv 8 0).
Proof.
  intros rdraw i Hi. pose proof (len_rnd16 rdraw) as L.
  unfold canary8, guard_lo, guard_hi.
  destruct (rnd16 rdraw) as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 l]]]]]]]]]; try discriminate L.
  assert (Hc : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%Z) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity.
Qed.

Lemma D_main_guard_at : forall sp0 av ev hw rdraw tid (i : Z), (0 <= i < 8)%Z ->
  D_main sp0 av ev hw rdraw tid (Z_to_bv 64 (0x351b28 + i)) = Some (nth (Z.to_nat i) (canary8 rdraw) (Z_to_bv 8 0)).
Proof.
  intros sp0 av ev hw rdraw tid i Hi.
  pose proof (len_canary8 rdraw) as L8. pose proof (len_guard_lo rdraw) as L4. pose proof (len_guard_hi rdraw) as L4'.
  rewrite canary8_nth by lia.
  unfold D_main, D_fd, D_ssp.
  rewrite MemSplit.wbytes_outside by dm_side.          (* [comment removed for export] *)
  rewrite MemSplit.wbytes_outside by dm_side.          (* [comment removed for export] *)
  destruct (Z.eqb_spec i 1) as [->|Hn1].
  - rewrite MemSplit.wbytes_inside by dm_side. cbn [length]. rewrite !u_small by lia. reflexivity.
  - rewrite MemSplit.wbytes_outside by dm_side.
    destruct (Z.ltb_spec i 4) as [Hl|Hge].
    + rewrite MemSplit.wbytes_outside by dm_side. rewrite MemSplit.wbytes_inside by dm_side.
      f_equal. f_equal. rewrite !u_small by lia. lia.
    + rewrite MemSplit.wbytes_inside by dm_side.
      f_equal. f_equal. rewrite !u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma seg_rom_high : forall (a : word), (0x354000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma w8_le : forall bs, length bs = 8%nat -> word_to_le_bytes 8 (le_bytes_to_word bs) = bs.
Proof. intros bs H. unfold le_bytes_to_word. apply w8_of_bytes. exact H. Qed.

Definition all_regs : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.

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

Section MainEntryProofs.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hfits : entry_stack_fits sp0 av envv.   (* [comment removed for export] *)
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv uid hw rdraw tid regs mem.

  Let E := E0 sp0 a0s path envv rdraw tid regs.

  Lemma sp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma sp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma sp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.

  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 sp0 a0s path envv; p1 sp0 a0s path envv; auxvp sp0 a0s path envv; rnd sp0 a0s path envv; tid] ++ junk_vals regs) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  Lemma length_junk_vals : length (junk_vals regs) = 32%nat.
  Proof. unfold junk_vals. rewrite length_map, length_seq. reflexivity. Qed.

  Lemma ev_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 sp0 a0s path envv; p1 sp0 a0s path envv; auxvp sp0 a0s path envv; rnd sp0 a0s path envv; tid] + i)%nat.
    rewrite app_nth2_plus.
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma eb2 : eb E 2 = rnd16 rdraw. Proof. reflexivity. Qed.
  Lemma eb3 : eb E 3 = canary8 rdraw. Proof. reflexivity. Qed.

  Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.

Section MainRegs.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv uid hw rdraw tid regs mem.
  Let E := E0 sp0 a0s path envv rdraw tid regs.

  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ rewrite (spx_val sp0 a0s path envv rdraw tid regs)
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk sp0 a0s path envv rdraw tid regs (n - 6)) by lia; reflexivity | idtac ]
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | apply (me_szero _ _ _ _ _ _ _ _ _ ME); cbn; tauto
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
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hfits : entry_stack_fits sp0 av envv.   (* [comment removed for export] *)
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv uid hw rdraw tid regs mem.
  Let E := E0 sp0 a0s path envv rdraw tid regs.

  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke4 : ev E 4 = rnd sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.
  Lemma keb2 : eb E 2 = rnd16 rdraw. Proof. reflexivity. Qed.
  Lemma keb3 : eb E 3 = canary8 rdraw. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma bsb_top : (bv_unsigned sp0 + Z.of_nat (length (build_stack_bytes RPH sp0 av envv uid hw rdraw)) <= 0x800000000000)%Z.
  Proof.
    pose proof (build_stack_bytes_within_span RPH sp0 av envv uid hw rdraw) as Hs.
    unfold entry_stack_fits, sp_window_hi in Hfits. lia.
  Qed.

  Lemma know_stack : know_ok RSEGS E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    unfold kn_stack, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win sp0 av envv uid hw rdraw tid regs mem ME); rewrite u_small by lia; unfold stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by lia.
      pose proof (read_argc_w RSEGS RPH sp0 av envv uid hw rdraw Hva) as Hr. unfold wmem in Hr.
      rewrite (Hr Hve) by (unfold sp_window_hi; lia).
      rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv uid hw rdraw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat ltac:(subst av; cbn; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv uid hw rdraw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 1%nat ltac:(subst av; cbn; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_null RSEGS RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_hi; lia)) as Hr.
      rewrite w_add_nat in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      rewrite <- (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv uid hw rdraw) in Hr by (try rewrite u_small by lia; lia).
      unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  Lemma auxvp_eq : auxvp sp0 a0s path envv = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_w, auxv_off. subst av. cbn [length]. f_equal. lia. Qed.

  Lemma auxvp_u : bv_unsigned (auxvp sp0 a0s path envv) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
    /\ (Z.of_nat (auxv_off av envv) + 160 + 16 <= Z.of_nat (length (build_stack_bytes RPH sp0 av envv uid hw rdraw)))%Z.
  Proof.
    pose proof kp_lo. pose proof kp_hi.
    pose proof (auxv_off_bound RPH sp0 rdraw av envv uid hw) as Hb.
    pose proof (lay_bsb_len RPH sp0 rdraw av envv uid hw Hva Hve) as Hl.
    rewrite auxvp_eq. rewrite u_small by lia. lia.
  Qed.

  Lemma rnd_u : (bv_unsigned sp0 <= bv_unsigned (rnd sp0 a0s path envv))%Z
    /\ (bv_unsigned (rnd sp0 a0s path envv) + 16 <= bv_unsigned sp0 + Z.of_nat (length (build_stack_bytes RPH sp0 av envv uid hw rdraw)))%Z
    /\ (bv_unsigned (rnd sp0 a0s path envv) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn RSEGS (stack_to_mem sp0 (entry_stack_image RPH sp0 av envv uid hw rdraw))
              (Z_to_bv 64 (bv_unsigned (rnd sp0 a0s path envv) + Z.of_nat j)) n = Some (firstn n (skipn j (rnd16 rdraw)))).
  Proof.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    pose proof (lay_bsb_len RPH sp0 rdraw av envv uid hw Hva Hve) as Hl.
    destruct (rnd_facts RSEGS RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) kp_al)
      as (A & B & C & D & F).
    unfold rnd, rnd16. subst av. repeat split; try assumption; try lia.
  Qed.

  Lemma auxv_word_at : forall j, (j < 20)%nat ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j)) 8
    = Some (word_to_le_bytes 8 (nth j (auxv_words RPH (rnd sp0 a0s path envv) uid hw) (Z_to_bv 64 0))).
  Proof.
    intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct auxvp_u as [Hu Hb]. pose proof bsb_top as Htop.
    rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv uid hw rdraw) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia).
    replace (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off av envv + 8 * j)) by (rewrite w_add_nat; f_equal; lia).
    rewrite (read_auxv_word RSEGS RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_hi; lia) j Hj).
    rewrite n_to_le_8_spec. unfold rnd. reflexivity.
  Qed.

  Ltac kw_auxv j :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
      replace k with (8 * Z.of_nat j)%Z by reflexivity end;
    rewrite (auxv_word_at j) by lia; unfold auxv_words; cbn [nth]; try reflexivity.

  (* [comment removed for export] *)
  Lemma rnd_word_at : forall k, (k < 2)%nat ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (rnd sp0 a0s path envv) + 8 * Z.of_nat k)) 8
    = Some (word_to_le_bytes 8 (nth k [rndw0 rdraw; rndw1 rdraw] (Z_to_bv 64 0))).
  Proof.
    intros k Hk. pose proof kp_lo as HLO. pose proof kp_hi as HHI. pose proof bsb_top as Htop.
    destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
    rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv uid hw rdraw) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia).
    pose proof (len_rnd16 rdraw) as L16.
    replace (8 * Z.of_nat k)%Z with (Z.of_nat (8 * k)) by lia.
    rewrite (Hr4 (8 * k)%nat 8%nat) by lia.
    destruct k as [|[|k]]; [ | | lia]; cbn [nth Nat.mul Nat.add].
    - unfold rndw0. rewrite w8_le by (rewrite length_firstn, L16; reflexivity). reflexivity.
    - unfold rndw1. rewrite w8_le by (rewrite length_skipn, L16; reflexivity).
      rewrite firstn_all2 by (rewrite length_skipn, L16; lia). reflexivity.
  Qed.

  Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal. pose proof bsb_top as Htop.
    destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
    unfold kn_auxv, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3, ?ke4, ?keb2; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4, ?keb2;
      try rewrite Hau; try lia.
    - (* [comment removed for export] *) split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
        by (unfold auxv_off; subst av; cbn [length]; lia).
      apply Z_mod_mult.
    - kw_auxv 0%nat. - kw_auxv 1%nat. - kw_auxv 2%nat. - kw_auxv 3%nat. - kw_auxv 4%nat. - kw_auxv 5%nat.
    - kw_auxv 6%nat. - kw_auxv 8%nat. - kw_auxv 9%nat. - kw_auxv 10%nat.
    - kw_auxv 12%nat. - kw_auxv 14%nat. - kw_auxv 15%nat. - kw_auxv 16%nat. - kw_auxv 17%nat.
    - kw_auxv 18%nat. - kw_auxv 19%nat.
    - (* [comment removed for export] *)
      pose proof (len_rnd16 rdraw) as L16.
      rewrite u_small by lia. split; [lia|]. split; [rewrite L16; reflexivity|]. intros i Hi.
      assert (Hr : rdn RSEGS mem (rnd sp0 a0s path envv) 16 = Some (rnd16 rdraw)).
      { rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by lia.
        pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv uid hw rdraw) as Hw. unfold wmem in Hw.
        rewrite Hw by lia.
        pose proof (Hr4 0%nat 16%nat ltac:(lia)) as H16. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H16.
        rewrite H16. f_equal; cbn [skipn]; try reflexivity; apply firstn_all2; rewrite L16; lia. }
      pose proof (rdn_pointwise_inv RSEGS mem 16 (rnd sp0 a0s path envv) _
                    ltac:(intros j Hj; apply seg_rom_high; rewrite u_small by lia; lia)
                    ltac:(lia) Hr (Z.to_nat i) ltac:(lia)) as Hp.
      rewrite Z2Nat.id in Hp by lia.
      replace (bv_unsigned (rnd sp0 a0s path envv) + 0 + i)%Z with (bv_unsigned (rnd sp0 a0s path envv) + i)%Z by lia.
      exact Hp.
  Qed.

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x31e000) 0x36000 = true.
  Proof. apply wseg_fast_sound. vm_cast_no_check (@eq_refl bool true). Qed.

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
  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x354000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 av envv hw rdraw tid i Hva); [lia | lia |].
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_mem L := kw_pre; rewrite (L RSEGS); try reflexivity.

  (* [comment removed for export] *)
  Lemma can_bytes : word_to_le_bytes 8 (can rdraw) = canary8 rdraw.
  Proof. unfold can, guard8. apply w8_le. apply len_canary8. Qed.

  (* [comment removed for export] *)
  Ltac kblob3 L :=
    pose proof (len_canary8 rdraw) as L8;
    rewrite (u_small 8) by lia; rewrite ?Z.add_0_l;
    split; [lia|]; split; [rewrite L8; reflexivity|]; intros i Hi;
    rewrite (main_entry_mem_data sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    exact (L i Hi).

  (* [comment removed for export] *)
  Ltac kw_peel := kw_pre;
    rewrite (main_entry_rdn_data sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    pose proof (u64_range tid); pose proof (u64_range hw);
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc;
    repeat (rewrite rdn_wbytes_out by (rewrite ?length_N_to_le_bytes, ?len_guard_lo, ?len_guard_hi, ?len_canary8; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)).
  Ltac kw_cell := kw_peel; apply rdn_wbytes_hit8; unorm; lia.
  Ltac kw_cell4 v := kw_peel;
    let H := fresh in pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 v)) as H;
    rewrite length_N_to_le_bytes in H; apply H; unorm; lia.

  Lemma know_image : know_ok RSEGS E mem kn_image.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimg;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5, ?keb3; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - (* [comment removed for export] *) split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x31e000) (Z_to_bv 64 (0x31e000 + d)) 0x36000 m 0x31e000 0x354000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - (* [comment removed for export] *) kw_cell.
    - (* [comment removed for export] *) kw_cell.
    - (* [comment removed for export] *) kw_cell.
    - kw_data (D_main_self sp0 av envv hw rdraw tid).
    - (* [comment removed for export] *) kw_cell.
    - (* [comment removed for export] *) kw_cell.
    - (* [comment removed for export] *) kw_cell.
    - kw_mem (main_entry_tid sp0 av envv uid hw rdraw tid Hlo regs mem ME).
    - (* [comment removed for export] *) kw_cell4 (Z_to_bv 64 2).
    - (* [comment removed for export] *) kw_cell.
    - (* [comment removed for export] *) kw_cell.
    - (* [comment removed for export] *) kblob3 (D_main_canary_at sp0 av envv hw rdraw tid).
    - (* [comment removed for export] *) kw_cell.
    - (* [comment removed for export] *) kw_cell.
    - (* [comment removed for export] *) kblob3 (D_main_guard_at sp0 av envv hw rdraw tid).
    - kw_data (D_main_auxv sp0 av envv hw rdraw tid Hva).
    - (* [comment removed for export] *) kw_cell.
    - (* [comment removed for export] *) kw_cell.
    - kw_data (D_main_pagesize sp0 av envv hw rdraw tid Hva).
    - (* [comment removed for export] *) kw_peel.
      let H := fresh in pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 1]) as H; cbn [length] in H; apply H; unorm; lia.
    - (* [comment removed for export] *) lia.
  Qed.

  Theorem main_know_ok : know_ok RSEGS E mem kn_main.
  Proof.
    unfold kn_main, know_ok.
    apply Forall_app; split; [apply know_stack|].
    apply Forall_app; split; [apply know_auxv | apply know_image].
  Qed.

  (* [comment removed for export] *)
  Lemma argv_str_end_le : forall k, (k < length av)%nat ->
    (bv_unsigned (cat_argv_ptr sp0 av envv k) + Z.of_nat (length (nth k av [])) + 1
     <= bv_unsigned sp0 + Z.of_nat (length (build_stack_bytes RPH sp0 av envv uid hw rdraw)))%Z.
  Proof.
    intros k Hk. pose proof kp_lo. pose proof kp_hi.
    rewrite (u_cat_argv_ptr sp0 av envv Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk).
    destruct (bsb_byte_k RPH sp0 av envv k uid hw rdraw Hk) as (pre & post & Ebsb & Hpre).
    rewrite Ebsb. rewrite !length_app. cbn [length]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr sp0 av envv k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr sp0 av envv k))%Z
    /\ (bv_unsigned (cat_argv_ptr sp0 av envv k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z
    /\ (bv_unsigned (cat_argv_ptr sp0 av envv k) + Z.of_nat (length (nth k av [])) + 1 <= 0x800000000000)%Z.
  Proof.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof bsb_top as Htop.
    pose proof (lay_bsb_nw RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    assert (Hk' : (k < length av)%nat) by (subst av; cbn; lia).
    destruct (argv_ptr_bounds_at sp0 av envv Hva Hve ltac:(unfold sp_window_hi; lia) k Hk') as [B1 B2].
    pose proof (u_cat_argv_ptr sp0 av envv Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (struct_av_bound av envv Hva Hve) as Hsb.
    pose proof (total_arg_bytes_firstn_le k av) as Hf.
    pose proof (argv_str_len av Hva k Hk') as Hlen.
    pose proof (argv_str_end_le k Hk') as Hend.
    repeat split.
    - rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by lia.
      pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv uid hw rdraw) as Hw. unfold wmem in Hw. rewrite Hw by lia.
      apply read_argv_cstr_k; [exact Hk' | exact Hnw].
    - exact B1.
    - lia.
    - exact Hlen.
    - lia.
  Qed.
  (* [comment removed for export] *)
  Lemma main_entry_hi : exists s : Z,
    (bv_unsigned sp0 + 192 <= s < 2 ^ 47 - 32)%Z /\ (s mod 8 = 0)%Z /\ mem (Z_to_bv 64 s) = Some (Z_to_bv 8 0).
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal. pose proof bsb_top as Htop.
    destruct auxvp_u as [Hau Hab].
    assert (Hoff : Z.of_nat (auxv_off av envv) = (40 + 8 * Z.of_nat (length envv))%Z) by (unfold auxv_off; subst av; cbn [length]; lia).
    assert (Hfit : (bv_unsigned sp0 + 192 + 8 * Z.of_nat (length envv) + 33 <= 2 ^ 47)%Z).
    { unfold entry_stack_fits, entry_stack_span, sp_window_hi, StackLayout.auxv_size in Hfits. subst av.
      assert (Ht : total_arg_bytes [a0s; path] = (Z.of_nat (length a0s) + 1 + (Z.of_nat (length path) + 1 + 0))%Z) by reflexivity.
      rewrite Ht in Hfits. cbn [length] in Hfits.
      pose proof (total_arg_bytes_nonneg envv). lia. }
    pose proof (auxv_word_at 19%nat ltac:(lia)) as Hw.
    change (nth 19 (auxv_words RPH (rnd sp0 a0s path envv) uid hw) (Z_to_bv 64 0)) with (Z_to_bv 64 0) in Hw.
    set (a := Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat 19)) in Hw.
    assert (Ua : bv_unsigned a = (bv_unsigned sp0 + 192 + 8 * Z.of_nat (length envv))%Z) by (unfold a; rewrite u_small by lia; lia).
    pose proof (rdn_pointwise_inv RSEGS mem 8 a _
                  ltac:(intros j Hj; apply seg_rom_high; rewrite u_small by lia; lia) ltac:(lia) Hw 0%nat ltac:(lia)) as Hp.
    exists (bv_unsigned a). rewrite Ua. split; [lia|]. split.
    - destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + 192 + 8 * Z.of_nat (length envv))%Z with ((2 * q + 24 + Z.of_nat (length envv)) * 8)%Z by lia.
      apply Z_mod_mult.
    - rewrite <- Ua. replace (bv_unsigned a) with (bv_unsigned a + Z.of_nat 0)%Z by (cbn; lia). rewrite Hp. reflexivity.
  Qed.
End KnowProofs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
