(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, main_entry names the launch input, mmap base and entry point, the argv strings sit at the top of the stack block and AT_RANDOM moves with the rseq flag, the writable window is 6144513 bytes, was 8388608, the whole auxv is readable, and every section lemma takes every section variable; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import MemSplit RefLayout StartupTac RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbStartupDefs UbStartup UbStartupFacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require UbWseg.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* LPS 08b1429: every Section lemma below takes every Section variable and hypothesis, in declaration
   order, so its consumers can apply it positionally without depending on which ones its proof reads. *)
Local Set Default Proof Using "All".

Lemma D_main_none : forall inp sp0 rdraw tid (i : Z),
  valid_argv (in_argv inp) -> (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  D_main_missb i 1 = true ->
  D_main inp sp0 rdraw tid (Z_to_bv 64 i) = None.
Proof.
  intros inp sp0 rdraw tid i Hva Hlo Hhi Hb.
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

(* [comment removed for export] *)
Lemma seg_rom_high : forall (a : word), (0x58000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
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
Definition junk_vals2 (a b : word) (R : bvmap 5 word) : list word := a :: b :: skipn 2 (junk_vals R).
Lemma junk_vals2_length : forall a b R, length (junk_vals2 a b R) = 32%nat.
Proof. intros. unfold junk_vals2, junk_vals. cbn [length]. rewrite length_skipn, length_map, length_seq. reflexivity. Qed.

Section MainEntry.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable ev : list (list byte).
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variables uid hw : word.
  Hypothesis ME : main_entry inp mbase entry sp0 av ev uid hw rdraw tid regs mem.

  (* LPS 08b1429: the strings sit at the top of the stack block ([cat_argv_ptr] over the stack VMA's
     end and the exec file name), and AT_RANDOM's place depends on the input's CONFIG_RSEQ flag. *)
  Definition p0 : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0.
  Definition p1 : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 1.
  Definition auxvp : word := Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  (* [comment removed for export] *)
  Definition cnw : word := canary_w rdraw.
  Definition rnd : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev.
  (* [comment removed for export] *)
  Definition secw : word := Z_to_bv 64 (bytes_le_to_Z (firstn 8 (skipn 8 (at_random_bytes (ed_random rdraw))))).

  (* [comment removed for export] *)
  Definition vals0 : list word := [sp0; p0; p1; auxvp; cnw; tid] ++ junk_vals2 rnd secw regs.
  Definition blobs0 : list (list byte) := [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]].
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  Definition sr_main : list expr :=
    [ELit 0; ELit 0x1ba3c; spx (-48); ELit 0x10800; ELit 0x36c60; EVar 11; EVar 12; EVar 13;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x13ac0; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  (* LPS 08b1429: the stack mapping is [Run.stack_window_lo, ed_top) with stack_window_lo at or above
     [ed_top - stack_max_size], and the block lies between sp0 and ed_top, so the window guaranteed
     writable below sp0 is [MemSplit.wok_lo sp0, sp0): stack_max_size - StoreOk.stack_window_reach
     = 6144513 bytes, not 8 MiB. *)
  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-6144513)) 6144513;
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  (* LPS 08b1429: the auxv is [StackLayout.auxv_entries] — ARCH_DLINFO's ten, create_elf_tables'
     sixteen, the CONFIG_RSEQ pair, AT_NULL.  The first 26 pairs (416 bytes) do not depend on
     CONFIG_RSEQ, so they are recorded here: every type word, and every value that is a constant of
     this image or of the env (AT_RANDOM).  The values the launch draws (AT_SYSINFO_EHDR, the cache
     words, AT_MINSIGSTKSZ, AT_HWCAP, AT_ENTRY, the ids, AT_EXECFN) are not. *)
  Definition kn_auxv : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000400000; KRange (EVar 6) 0x7fff80000000 0x800000400000;
     KDisj (SA (EVar 0) (-6144513)) 6144513 (SA (EVar 3) 0) 416;
     KDisj (SA (EVar 0) (-6144513)) 6144513 (SA (EVar 6) 0) 16;
     KAlign (EVar 3) 8; KAlign (EVar 6) 8;
     KWord (SA (EVar 3) 0) 8 (ELit 33);
     KWord (SA (EVar 3) 16) 8 (ELit 40); KWord (SA (EVar 3) 32) 8 (ELit 41);
     KWord (SA (EVar 3) 48) 8 (ELit 42); KWord (SA (EVar 3) 64) 8 (ELit 43);
     KWord (SA (EVar 3) 80) 8 (ELit 44); KWord (SA (EVar 3) 96) 8 (ELit 45);
     KWord (SA (EVar 3) 112) 8 (ELit 46); KWord (SA (EVar 3) 128) 8 (ELit 47);
     KWord (SA (EVar 3) 144) 8 (ELit 51);
     KWord (SA (EVar 3) 160) 8 (ELit 16);
     KWord (SA (EVar 3) 176) 8 (ELit 6); KWord (SA (EVar 3) 184) 8 (ELit 4096);
     KWord (SA (EVar 3) 192) 8 (ELit 17); KWord (SA (EVar 3) 200) 8 (ELit 100);
     KWord (SA (EVar 3) 208) 8 (ELit 3); KWord (SA (EVar 3) 216) 8 (ELit 0x10040);
     KWord (SA (EVar 3) 224) 8 (ELit 4); KWord (SA (EVar 3) 232) 8 (ELit 56);
     KWord (SA (EVar 3) 240) 8 (ELit 5); KWord (SA (EVar 3) 248) 8 (ELit 10);
     KWord (SA (EVar 3) 256) 8 (ELit 7); KWord (SA (EVar 3) 264) 8 (ELit 0);
     KWord (SA (EVar 3) 272) 8 (ELit 8); KWord (SA (EVar 3) 280) 8 (ELit 0);
     KWord (SA (EVar 3) 288) 8 (ELit 9);
     KWord (SA (EVar 3) 304) 8 (ELit 11); KWord (SA (EVar 3) 320) 8 (ELit 12);
     KWord (SA (EVar 3) 336) 8 (ELit 13); KWord (SA (EVar 3) 352) 8 (ELit 14);
     KWord (SA (EVar 3) 368) 8 (ELit 23); KWord (SA (EVar 3) 376) 8 (ELit 0);
     KWord (SA (EVar 3) 384) 8 (ELit 25); KWord (SA (EVar 3) 392) 8 (EVar 6);
     KWord (SA (EVar 3) 400) 8 (ELit 31);
     KWord (SA (EVar 6) 8) 8 (EVar 7)   (* [comment removed for export] *)].

  Definition kn_image : list kentry :=
    [KWr (SA (ELit 0) 0x26000) 0x32000;
     KImg 0x10000 0x26af0;
     KImg 0x26af1 0x36b90; KImg 0x56c68 0x56c88;
     KWord (SA (ELit 0) 0x36b98) 8 (ELit 0x36b98);
     KWord (SA (ELit 0) 0x36bb8) 4 (EVar 5);
     KImg 0x36bc4 0x36c10; KImg 0x36c18 0x36c30; KImg 0x36c38 0x36c50;
     KWord (SA (ELit 0) 0x36c50) 8 (EVar 4);
     KImg 0x36c60 0x36c70; KImg 0x36c78 0x36ce8; KImg 0x56ca8 0x56ed0;
     KWord (SA (ELit 0) 0x56ca0) 8 (EVar 4);
     KImg 0x56ed0 0x56ed8;
     KImg 0x56ee9 0x56ef0; KWord (SA (ELit 0) 0x56ef0) 8 (EVar 3);
     KImg 0x56ef8 0x56f00; KImg 0x56f10 0x56f18; KWord (SA (ELit 0) 0x56f18) 8 (ELit 4096);
     KImg 0x56f20 0x56f50; (* [comment removed for export] *) KImg 0x56f58 0x58000;
     KRange (EVar 5) 1 4194303;
     KImg 0 0x1000 (* [comment removed for export] *)].

  (* [comment removed for export] *)
  Definition kn_main : list kentry := kn_stack ++ kn_auxv ++ kn_image.
End MainEntry.

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
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variables uid hw : word.
  Hypothesis ME : main_entry inp mbase entry sp0 av envv uid hw rdraw tid regs mem.

  Local Notation E := (E0 sp0 a0s path envv rdraw tid regs inp) (only parsing).

  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 a0s path envv rdraw inp; p1 a0s path envv rdraw inp; auxvp sp0 a0s path envv; cnw rdraw; tid] ++ junk_vals2 (rnd sp0 a0s path envv inp) (secw rdraw) regs) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  Lemma ev_junk : forall i, (2 <= i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 a0s path envv rdraw inp; p1 a0s path envv rdraw inp; auxvp sp0 a0s path envv; cnw rdraw; tid] + i)%nat.
    rewrite app_nth2_plus. unfold junk_vals2.
    destruct i as [|[|i]]; [lia | lia |]. cbn [nth]. rewrite nth_skipn.
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. try (f_equal; f_equal; f_equal; lia).
  Qed.

  Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ rewrite spx_val
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk (n - 6)) by lia; reflexivity | idtac ]
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | apply (me_szero _ _ _ _ _ _ _ _ _ _ _ _ ME); cbn; tauto
                | idtac ].

  Theorem main_regs_ok : regs_ok E sr_main regs.
  Proof.
    pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
  Qed.

  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 a0s path envv rdraw inp. Proof. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 a0s path envv rdraw inp. Proof. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke4 : ev E 4 = cnw rdraw. Proof. reflexivity. Qed.
  Lemma ke6 : ev E 6 = rnd sp0 a0s path envv inp. Proof. reflexivity. Qed.
  Lemma ke7 : ev E 7 = secw rdraw. Proof. reflexivity. Qed.
  Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.

  (** The launch [main_entry] hides, in this Section's names. *)
  Lemma me_launch : exists brk,
    in_argv inp = av /\ in_envp inp = envv /\ in_uid inp = uid /\ in_hwcap inp = hw
    /\ valid_launch inp /\ entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Proof. exact (main_entry_launch inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME). Qed.

  Ltac launch_facts :=
    destruct me_launch as (brk & Eav & Eev & Euid & Ehw & Hvl & Hlau);
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva);
    assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).

  Ltac layout_side :=
    first [ eassumption | exact kp_al
          | (unfold sp_window_lo; pose proof kp_lo; lia) | (unfold sp_window_hi; pose proof kp_hi; lia) ].

  Lemma know_stack : know_ok RSEGS E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    launch_facts.
    unfold kn_stack, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME);
        rewrite u_small by lia; unfold wok_lo, stack_window_reach, stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by lia.
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rdraw) sp0 8 = Some (word_le8 (argcN inp)))
        by (eapply (read_argc_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw); layout_side).
      rewrite Hr. unfold argcN. rewrite Eav.
      rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rdraw) (sp0 + nat_to_word (8 + 8 * 0)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw);
            first [layout_side | rewrite Eav; subst av; cbn; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. unfold p0. rewrite Eav, Eev. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rdraw) (sp0 + nat_to_word (8 + 8 * 1)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw);
            first [layout_side | rewrite Eav; subst av; cbn; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. unfold p1. rewrite Eav, Eev. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rdraw))
                     (sp0 + nat_to_word (8 + 8 * length (in_argv inp))) 8 = Some (word_le8 (Z_to_bv 64 0)))
        by (eapply (read_argv_null RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw); layout_side).
      rewrite w_add_nat in Hr. rewrite Eav in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw; unfold wmem in Hw; rewrite Hw by (rewrite ?u_small by lia; lia).
      rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  Lemma auxvp_eq : auxvp sp0 a0s path envv = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_off. subst av. cbn [length]. f_equal. lia. Qed.

  Lemma auxvp_u : bv_unsigned (auxvp sp0 a0s path envv) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
    /\ (Z.of_nat (auxv_off av envv) + 416 <= 2240000)%Z.
  Proof.
    pose proof kp_lo. pose proof kp_hi. destruct Hve as [Hle _].
    rewrite auxvp_eq. unfold auxv_off in *. subst av. cbn [length] in *.
    rewrite u_small by lia. split; lia.
  Qed.

  Lemma rnd_u : (bv_unsigned sp0 <= bv_unsigned (rnd sp0 a0s path envv inp))%Z
    /\ (bv_unsigned (rnd sp0 a0s path envv inp) + 16 <= bv_unsigned sp0 + 2240000)%Z
    /\ (bv_unsigned (rnd sp0 a0s path envv inp) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rdraw))
              (Z_to_bv 64 (bv_unsigned (rnd sp0 a0s path envv inp) + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
  Proof.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    launch_facts.
    assert (Hl : (Z.of_nat (length (entry_stack_image inp mbase RPH entry sp0 rdraw)) <= 2101782)%Z)
      by (eapply lay_bsb_len; layout_side).
    pose proof (rnd_facts RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw) as RF.
    repeat match type of RF with ?P -> _ =>
      let H := fresh in assert (H : P) by layout_side; specialize (RF H) end.
    destruct RF as (A & B & C & D & F).
    unfold rnd. subst av. rewrite <- Eav, <- Eev. repeat split; try assumption; try lia.
  Qed.

  Lemma auxv_word_at : forall j, (j < 52)%nat ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j)) 8
    = Some (word_to_le_bytes 8 (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entry
                                          (in_uid inp) (in_gid inp) (in_hwcap inp)
                                          (rnd sp0 a0s path envv inp)
                                          (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                                  (Z_to_bv 64 0))).
  Proof.
    intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    launch_facts.
    destruct auxvp_u as [Hu Hb].
    rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw; unfold wmem in Hw; rewrite Hw by (rewrite u_small by lia; lia).
    replace (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j))
      by (rewrite Eav, Eev, w_add_nat; f_equal; lia).
    assert (Hr : rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rdraw))
                   (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j)) 8
                 = Some (word_le8 (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entry
                                            (in_uid inp) (in_gid inp) (in_hwcap inp)
                                            (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
                                            (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                                     (Z_to_bv 64 0))))
      by (eapply (read_auxv_word RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw);
          first [ layout_side | (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia) ]).
    rewrite Hr. rewrite n_to_le_8_spec. unfold rnd. rewrite Eav, Eev. reflexivity.
  Qed.

  (* LPS 08b1429/75d69e00: the same read over the WHOLE auxiliary vector. [auxv_word_at] stops at
     j < 52 (the first 26 pairs, the ones [kn_main] records) because pair 26 onward depends on the
     input's free CONFIG_RSEQ flag ([StackLayout.auxv_entries]); a plan that walks the vector to
     AT_NULL (musl's malloc-init auxv scan, RefPilotOOM_defs block C) reads past it. *)
  Lemma auxv_word_any : forall j, (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j)) 8
    = Some (word_to_le_bytes 8 (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entry
                                          (in_uid inp) (in_gid inp) (in_hwcap inp)
                                          (rnd sp0 a0s path envv inp)
                                          (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                                  (Z_to_bv 64 0))).
  Proof.
    intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hj57 : (j <= 57)%nat) by (unfold auxv_count in Hj; destruct (kb_rseq (in_kernel inp)); lia).
    launch_facts.
    destruct auxvp_u as [Hu _].
    assert (Hb : (Z.of_nat (auxv_off av envv) + 464 <= 2240000)%Z)
      by (destruct Hve as [Hle _]; unfold auxv_off; subst av; cbn [length] in *; lia).
    rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw; unfold wmem in Hw; rewrite Hw by (rewrite u_small by lia; lia).
    replace (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j))
      by (rewrite Eav, Eev, w_add_nat; f_equal; lia).
    assert (Hr : rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rdraw))
                   (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j)) 8
                 = Some (word_le8 (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entry
                                            (in_uid inp) (in_gid inp) (in_hwcap inp)
                                            (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
                                            (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                                     (Z_to_bv 64 0))))
      by (eapply (read_auxv_word RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw);
          first [ layout_side | exact Hj ]).
    rewrite Hr. rewrite n_to_le_8_spec. unfold rnd. rewrite Eav, Eev. reflexivity.
  Qed.

  Ltac kw_auxv j :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
      replace k with (8 * Z.of_nat j)%Z by reflexivity end;
    rewrite (auxv_word_at j) by lia; unfold auxv_words, auxv_entries; cbn [flat_map fst snd app nth]; reflexivity.

  Lemma w2b_b2z8 : forall bs, length bs = 8%nat -> word_to_le_bytes 8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
  Proof.
    intros bs Hl. unfold word_to_le_bytes.
    pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb.
    pose proof (bytes_le_to_Z_nonneg bs).
    rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by (cbn in Hb; lia).
    rewrite <- Hl. apply Z_to_le_bytes_lez.
  Qed.

  Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
    unfold kn_auxv, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3, ?ke6, ?ke7; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke6, ?ke7;
      try rewrite Hau; try lia.
    - (* [comment removed for export] *) split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
        by (unfold auxv_off; subst av; cbn [length]; lia).
      apply Z_mod_mult.
    - kw_auxv 0%nat.
    - kw_auxv 2%nat. - kw_auxv 4%nat. - kw_auxv 6%nat. - kw_auxv 8%nat.
    - kw_auxv 10%nat. - kw_auxv 12%nat. - kw_auxv 14%nat. - kw_auxv 16%nat.
    - kw_auxv 18%nat.
    - kw_auxv 20%nat.
    - kw_auxv 22%nat. - kw_auxv 23%nat. - kw_auxv 24%nat. - kw_auxv 25%nat.
    - kw_auxv 26%nat. - kw_auxv 27%nat. - kw_auxv 28%nat. - kw_auxv 29%nat.
    - kw_auxv 30%nat. - kw_auxv 31%nat. - kw_auxv 32%nat. - kw_auxv 33%nat.
    - kw_auxv 34%nat. - kw_auxv 35%nat. - kw_auxv 36%nat.
    - kw_auxv 38%nat. - kw_auxv 40%nat. - kw_auxv 42%nat. - kw_auxv 44%nat.
    - kw_auxv 46%nat. - kw_auxv 47%nat. - kw_auxv 48%nat. - kw_auxv 49%nat.
    - kw_auxv 50%nat.
    - (* [comment removed for export] *)
      split; [lia|]. split; [lia|].
      unfold adenot; cbn [a_base a_off edenot]. rewrite ke6. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw; unfold wmem in Hw; rewrite Hw by (rewrite u_small by lia; lia).
      pose proof (Hr4 8%nat 8%nat ltac:(lia)) as H8. change (Z.of_nat 8) with 8%Z in H8. rewrite H8.
      unfold secw. rewrite w2b_b2z8; [reflexivity|].
      rewrite length_firstn, length_skipn, length_at_random_bytes. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxvp : forall segs,
    rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0x56ef0) 8
    = Some (word_to_le_bytes 8 (auxvp sp0 a0s path envv)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof kp_lo. pose proof kp_hi.
    destruct me_launch as (brk & Eav & Eev & _).
    assert (Ea : auxvp sp0 a0s path envv = auxv_w inp sp0) by (unfold auxvp, auxv_w; rewrite Eav, Eev; reflexivity).
    rewrite Ea.
    unfold auxv_w, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x26000) 204800 = true.
  Proof. exact UbWseg.wseg_data_z. Qed.

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
  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x58000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    destruct me_launch as (brk & Eav & _).
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none inp sp0 rdraw tid i ltac:(rewrite Eav; exact Hva)); [lia | lia |].
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    erewrite L by first [eassumption | exact kp_lo | exact kp_hi]; reflexivity.

  Lemma know_image : know_ok RSEGS E mem kn_image.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
    destruct me_launch as (brk & Eav & _).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva).
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimg;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke4, ?ke5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - (* [comment removed for export] *) split; [lia|]. intros d m Hd Hm.
      apply UbWseg.store_ok_data_win; [rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_data D_main_self.
    - kw_data D_main_tid.
    - kw_data D_main_canary.
    - kw_data D_main_guard.
    - kw_data D_main_auxvp.
    - kw_data D_main_pagesize.
    - (* [comment removed for export] *) lia.
  Qed.

  Theorem main_know_ok : know_ok RSEGS E mem kn_main.
  Proof.
    unfold kn_main, know_ok.
    apply Forall_app; split; [apply know_stack|].
    apply Forall_app; split; [apply know_auxv | apply know_image].
  Qed.

  (* [comment removed for export] *)
  Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) + Z.of_nat (length (nth k av [])) + 1 <= 2 ^ 47)%Z.
  Proof.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    launch_facts.
    assert (Ec : cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k
                 = cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k) by (rewrite Eav, Eev; reflexivity).
    assert (El : nth k av [] = nth k (in_argv inp) []) by (rewrite Eav; reflexivity).
    rewrite Ec, El.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Eav; subst av; cbn; lia).
    destruct (argv_ptr_bounds Sv48 inp mbase sp0 brk rdraw k Hlau Hk') as [B1 B2].
    assert (Hu : bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
                 = (bv_unsigned sp0
                    + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rdraw)
                                  (in_argv inp) (in_envp inp) (in_execfn inp)
                                + total_arg_bytes_nat (firstn k (in_argv inp))))%Z)
      by (eapply (u_cat_argv_ptr Sv48 inp mbase RPH entry sp0 brk rdraw); first [layout_side | exact Hk']).
    assert (Hsb : (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp)
                    + total_arg_bytes_nat (in_argv inp) + total_arg_bytes_nat (in_envp inp)
                    <= length (entry_stack_image inp mbase RPH entry sp0 rdraw))%nat)
      by (eapply struct_av_bound; layout_side).
    assert (Hl : (Z.of_nat (length (entry_stack_image inp mbase RPH entry sp0 rdraw)) <= 2101782)%Z)
      by (eapply lay_bsb_len; layout_side).
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)) as Hf.
    pose proof (valid_argv_str_len (in_argv inp) k Hva' Hk') as Hlen.
    (* the string end bound: the argv strings end at the stack VMA's end less 8
       ([CatExec.u_cat_string_base]), and that end is at most the Sv48 stack top *)
    pose proof (launch_string_base_arith Sv48 inp mbase sp0 brk rdraw Hlau) as HA.
    pose proof (u_cat_string_base Sv48 inp mbase sp0 brk rdraw Hlau) as Hub.
    pose proof (u64_range sp0). pose proof (u64_range (ed_top rdraw)).
    pose proof (Nat2Z.is_nonneg (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
    pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat (firstn k (in_argv inp)))).
    assert (Hstr : (Z.of_nat (total_arg_bytes_nat (firstn k (in_argv inp)))
                    + Z.of_nat (length (nth k (in_argv inp) [])) + 1
                    <= Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)))%Z).
    { pose proof (total_arg_bytes_firstn_within (in_argv inp) k Hk') as Hw.
      unfold launch_string_bytes. rewrite length_flatten_strings.
      pose proof (Nat2Z.is_nonneg (length (flatten_strings (in_envp inp)))).
      pose proof (Nat2Z.is_nonneg (length (in_execfn inp))).
      lia. }
    pose proof Hlau as Hlau2. cbn [entry_launch_ok_va] in Hlau2. destruct Hlau2 as ((_ & Htop & _) & _).
    assert (Hv : (va_stack_top Sv48 <= 0x800000000000)%Z) by (unfold Z.le; vm_compute; discriminate).
    repeat split.
    - rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by lia.
      pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw; unfold wmem in Hw; rewrite Hw by lia.
      exact (read_argv_cstr_k Sv48 RSEGS inp mbase RPH entry sp0 brk rdraw k Hlau Hk').
    - exact B1.
    - lia.
    - exact Hlen.
    - rewrite (cat_argv_ptr_offset _ _ _ _ k Hk'), word_add_nat_Z2bv, Hub.
      rewrite u_Z2bv_lt by lia.
      change (2 ^ 47)%Z with 0x800000000000%Z. lia.
  Qed.
End MainEntryProofs.
