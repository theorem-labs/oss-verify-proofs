(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's validity hypotheses; the process input's new fields; the new initial stack layout; the start-up taken per CONFIG_RSEQ value). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  WsegFast PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv
  SymExec SymExec2 SymExec2Sound SymRun SymDrive
  MemSplit RefLayout StartupTac UbStartupDefs UbStartup UbStartupFacts.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast LiaTier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast2.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := ImgU.M.loaded_segments.
Abbreviation RPH := ImgU.M.phdrs.
Abbreviation RENT := (Z_to_bv 64 (Z.of_N ImgU.M.init_pc)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma seg_rom_high : forall (a : word), (0xe6000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
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
Definition secret_bytes (rdraw : EntryDraw) : list byte := firstn 8 (skipn 8 (at_random_bytes (ed_random rdraw))).
Definition secret_w (rdraw : EntryDraw) : word := Z_to_bv 64 (bytes_le_to_Z (secret_bytes rdraw)).

Lemma length_secret_bytes : forall rdraw, length (secret_bytes rdraw) = 8%nat.
Proof.
  intros rdraw. unfold secret_bytes. pose proof (length_at_random_bytes (ed_random rdraw)) as HL.
  rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia.
Qed.

Lemma secret_bytes_w : forall rdraw, secret_bytes rdraw = word_to_le_bytes 8 (secret_w rdraw).
Proof. intros rdraw. unfold secret_w. symmetry. apply word_to_le_bytes_of_lez; [apply length_secret_bytes | lia]. Qed.

Lemma u_secret_w : forall rdraw, (0 <= bv_unsigned (secret_w rdraw) < 2 ^ 64)%Z.
Proof. intros rdraw. exact (u64_range (secret_w rdraw)). Qed.

Section MainEntry.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable inp : ProcInput.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.

  (* 08b1429: the argv strings end at the stack VMA's top (ed_top), after AT_EXECFN's string *)
  Definition p0 : word := cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0.
  Definition p1 : word := cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1.
  Definition auxvp : word := auxv_w sp0 inp.
  Definition rnd : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp).
  Definition canary : word := canary_w rdraw.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition vals0 : list word := [sp0; p0; p1; auxvp; rnd; tid; canary; secret_w rdraw] ++ skipn 2 (junk_vals regs).
  Definition blobs0 : list (list byte) := [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]].
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  Definition sr_main : list expr :=
    [ELit 0; ELit 0x96140; spx (-48); ELit 0x10800; ELit 0xc5018; EVar 11; EVar 12; EVar 13;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x32634; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-6144513)) 6144513;
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  (* LPS 727298f3: twin of RefMainEntry.kn_auxv -- every type word of the first 26 auxv pairs and
     every constant value; musl's malloc-init scan (UbPilotOOM_defs block B) walks them to AT_NULL.
     The words after pair 25 are the pilot's (UbPilotOOM_defs.kn_tail). *)
  Definition kn_auxv : list kentry :=   (* [comment removed for export] *)
    [KRange (EVar 3) 0x7fff80000000 0x800000400000; KRange (EVar 4) 0x7fff80000000 0x800000400000;
     KDisj (SA (EVar 0) (-6144513)) 6144513 (SA (EVar 3) 0) 464;
     KDisj (SA (EVar 0) (-6144513)) 6144513 (SA (EVar 4) 0) 16;
     KAlign (EVar 3) 8; KAlign (EVar 4) 8;
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
     KWord (SA (EVar 3) 384) 8 (ELit 25); KWord (SA (EVar 3) 392) 8 (EVar 4);
     KWord (SA (EVar 3) 400) 8 (ELit 31);
     KWord (SA (EVar 4) 8) 8 (EVar 7)].     (* [comment removed for export] *)

  Definition kn_image : list kentry :=
    [KWr (SA (ELit 0) 0xb3000) 0x33000;
     KImg 0x10000 0xb35a0;
     KImg 0xb35a1 0xc4f48; KImg 0xe5020 0xe5040;     (* [comment removed for export] *)
     KWord (SA (ELit 0) 0xc4f50) 8 (ELit 0xc4f50);
     KWord (SA (ELit 0) 0xc4f70) 4 (EVar 5);
     KImg 0xc4f7c 0xc4fc8; KImg 0xc4fd0 0xc4fe8; KImg 0xc4ff0 0xc5008;
     KWord (SA (ELit 0) 0xc5008) 8 (EVar 6);          (* [comment removed for export] *)
     KImg 0xc5018 0xc5028; KImg 0xc5030 0xc50a0; KImg 0xe5058 0xe5288;
     KWord (SA (ELit 0) 0xe5288) 8 (EVar 6);          (* [comment removed for export] *)
     KImg 0xe5290 0xe5298;
     KImg 0xe52a9 0xe52b0; KWord (SA (ELit 0) 0xe52b0) 8 (EVar 3);
     KImg 0xe52b8 0xe52c0; KImg 0xe52d0 0xe52d8; KWord (SA (ELit 0) 0xe52d8) 8 (ELit 4096);
     KImg 0xe52e0 0xe5310; (* [comment removed for export] *) KImg 0xe5318 0xe6000;
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
  Variable inp : ProcInput.
  Variables mbase brk : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation envv := (in_envp inp) (only parsing).
  Hypothesis Hav : in_argv inp = [a0s; path].
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs mem.
  Ltac lctx := first [ exact Hva | exact Hve | exact Hvl | exact Hlau
                     | exact (proj1 Hvsp) | exact (proj1 (proj2 Hvsp)) | exact (proj2 (proj2 Hvsp)) ].

  Let E := E0 sp0 a0s path inp rdraw tid regs.

  Lemma sp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma sp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma sp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.

  #[using="Type"] Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 inp rdraw; p1 inp rdraw; auxvp sp0 inp; rnd sp0 inp; tid; canary rdraw; secret_w rdraw] ++ skipn 2 (junk_vals regs)) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  #[using="Type"] Lemma ev_junk : forall i, (2 <= i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).   (* [comment removed for export] *)
  Proof.
    intros i Hi. rewrite ev_vals. destruct i as [|[|i']]; [lia|lia|].
    change (6 + S (S i'))%nat with (length [sp0; p0 inp rdraw; p1 inp rdraw; auxvp sp0 inp; rnd sp0 inp; tid; canary rdraw; secret_w rdraw] + i')%nat.
    rewrite app_nth2_plus. unfold junk_vals. change (seq 0 32) with (0%nat :: 1%nat :: seq 2 30). cbn [map skipn].
    rewrite (nth_map_seq_gen (fun i => getr regs (Z_to_bv 5 (Z.of_nat i))) 30 2 i') by lia. reflexivity.
  Qed.

  #[using="Type"] Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.

Section MainRegs.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable inp : ProcInput.
  Variables mbase brk : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation envv := (in_envp inp) (only parsing).
  Hypothesis Hav : in_argv inp = [a0s; path].
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs mem.
  Ltac lctx := first [ exact Hva | exact Hve | exact Hvl | exact Hlau
                     | exact (proj1 Hvsp) | exact (proj1 (proj2 Hvsp)) | exact (proj2 (proj2 Hvsp)) ].
  Let E := E0 sp0 a0s path inp rdraw tid regs.

  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ rewrite (spx_val sp0 a0s path inp rdraw tid regs)
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk sp0 a0s path inp rdraw tid regs (n - 6)) by lia; reflexivity | idtac ]
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ _ ME); rewrite Hav; f_equal; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ _ ME); rewrite Hav; f_equal; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ _ ME); unfold argcN, len_word; rewrite Hav; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ _ ME); unfold argcN, len_word; rewrite Hav; reflexivity
                | apply (me_szero _ _ _ _ _ _ _ ME); cbn; tauto
                | idtac ].

  Theorem main_regs_ok : regs_ok E sr_main regs.
  Proof using All.
    pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
  Qed.
End MainRegs.

Section KnowProofs.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable inp : ProcInput.
  Variables mbase brk : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation envv := (in_envp inp) (only parsing).
  Hypothesis Hav : in_argv inp = [a0s; path].
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs mem.
  Ltac lctx := first [ exact Hva | exact Hve | exact Hvl | exact Hlau
                     | exact (proj1 Hvsp) | exact (proj1 (proj2 Hvsp)) | exact (proj2 (proj2 Hvsp)) ].
  Let E := E0 sp0 a0s path inp rdraw tid regs.

  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  #[using="Type"] Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke1 : ev E 1 = p0 inp rdraw. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke2 : ev E 2 = p1 inp rdraw. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke3 : ev E 3 = auxvp sp0 inp. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke4 : ev E 4 = rnd sp0 inp. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke6 : ev E 6 = canary rdraw. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke7 : ev E 7 = secret_w rdraw. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.

  Lemma len_av2 : length (in_argv inp) = 2%nat.
  Proof. rewrite Hav. reflexivity. Qed.

  Lemma rd_above : forall (a : word) n, (bv_unsigned sp0 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn RSEGS mem a n = rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH RENT sp0 rdraw)) a n.
  Proof.
    intros a n Ha Hn. rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME RSEGS a n Ha Hn).
    eapply rdn_wmem_stack; [exact Ha | exact Hn].   (* twin of RefMainEntry.v:309-313 *)
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
      apply (main_entry_store_ok_win sp0 inp mbase rdraw tid regs mem ME); rewrite ?u_small by lia;
        unfold wok_lo, stack_window_reach, stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME) by lia.
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH RENT sp0 rdraw) sp0 8%nat = Some (word_le8 (argcN inp)))
        by (eapply read_argc_w; lctx).
      rewrite Hr. unfold argcN, len_word. rewrite Hav. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH RENT sp0 rdraw) (sp0 + nat_to_word (8 + 8 * 0)) 8%nat
                   = Some (word_le8 (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0)))
        by (eapply read_argv_ptr_w; first [lctx | rewrite len_av2; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH RENT sp0 rdraw) (sp0 + nat_to_word (8 + 8 * 1)) 8%nat
                   = Some (word_le8 (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1)))
        by (eapply read_argv_ptr_w; first [lctx | rewrite len_av2; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      pose proof (lay_bsb_nw Sv48 inp mbase RPH RENT sp0 brk rdraw) as NW.
      rewrite rd_above by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH RENT sp0 rdraw))
                     (sp0 + nat_to_word (8 + 8 * length (in_argv inp))) 8%nat = Some (word_le8 (Z_to_bv 64 0)))
        by (eapply read_argv_null; lctx).
      rewrite w_add_nat, len_av2 in Hr. change (Z.of_nat (8 + 8 * 2)) with 24%Z in Hr.
      rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  Lemma auxvp_eq : auxvp sp0 inp = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off (in_argv inp) (in_envp inp))).
  Proof. unfold auxvp, auxv_w, auxv_off. f_equal. lia. Qed.

  Lemma auxvp_u : bv_unsigned (auxvp sp0 inp) = (bv_unsigned sp0 + Z.of_nat (auxv_off (in_argv inp) (in_envp inp)))%Z
    /\ (Z.of_nat (auxv_off (in_argv inp) (in_envp inp)) + 464 <= 2101782)%Z
    /\ (32 <= Z.of_nat (auxv_off (in_argv inp) (in_envp inp)))%Z.
  Proof.
    pose proof kp_lo. pose proof kp_hi.
    assert (Hb : (auxv_off (in_argv inp) (in_envp inp) + auxv_size (kb_rseq (in_kernel inp)) + 16
                  <= length (entry_stack_image inp mbase RPH RENT sp0 rdraw))%nat)
      by (apply (auxv_off_bound inp mbase RPH RENT sp0 brk rdraw)).   (* see RefMainEntry.v:363-367 *)
    assert (Hl : (Z.of_nat (length (entry_stack_image inp mbase RPH RENT sp0 rdraw)) <= 2101782)%Z)
      by (apply (lay_bsb_len Sv48 inp mbase RPH RENT sp0 brk rdraw); lctx).
    assert (Hs : (432 <= auxv_size (kb_rseq (in_kernel inp)))%nat)
      by (unfold auxv_size, auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
    assert (Ho : (32 <= auxv_off (in_argv inp) (in_envp inp))%nat)
      by (unfold auxv_off; destruct Hva as [[Hav1 _] _]; lia).   (* see RefMainEntry.v:380-394 *)
    assert (Hoa : (Z.of_nat (auxv_off (in_argv inp) (in_envp inp)) + 464 <= 2101782)%Z)
      by (unfold auxv_off; destruct Hva as [[_ Hav2] _]; destruct Hve as [Hev2 _]; lia).
    rewrite auxvp_eq. rewrite u_small by lia. split; [lia|]. split; lia.
  Qed.

  Lemma rnd_u : (bv_unsigned sp0 <= bv_unsigned (rnd sp0 inp))%Z
    /\ (bv_unsigned (rnd sp0 inp) + 16 <= bv_unsigned sp0 + 2101782)%Z
    /\ (bv_unsigned (rnd sp0 inp) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH RENT sp0 rdraw))
              (Z_to_bv 64 (bv_unsigned (rnd sp0 inp) + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
  Proof.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hl : (Z.of_nat (length (entry_stack_image inp mbase RPH RENT sp0 rdraw)) <= 2101782)%Z)
      by (eapply lay_bsb_len; lctx).
    pose proof (rnd_facts RSEGS Sv48 inp mbase RPH RENT sp0 brk rdraw) as RF.
    repeat (specialize (RF ltac:(lctx))).
    (* see RefMainEntry.v:411-413 *)
    destruct RF as (A & B & C & D & F).
    unfold rnd. repeat split; try assumption; try lia.
  Qed.

  (* twin of RefMainEntry.auxv_word_any *)
  Lemma auxv_word_any : forall j, (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp sp0 inp) + 8 * Z.of_nat j)) 8
    = Some (word_to_le_bytes 8 (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH RENT
                                          (in_uid inp) (in_gid inp) (in_hwcap inp)
                                          (rnd sp0 inp)
                                          (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                                  (Z_to_bv 64 0))).
  Proof.
    intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hj57 : (j <= 57)%nat) by (unfold auxv_count in Hj; destruct (kb_rseq (in_kernel inp)); lia).
    destruct auxvp_u as (Hu & Hb & Ho).
    rewrite rd_above by (rewrite u_small by lia; lia).
    assert (Hr : rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH RENT sp0 rdraw))
                   (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j)) 8%nat
                 = Some (word_le8 (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH RENT
                                            (in_uid inp) (in_gid inp) (in_hwcap inp)
                                            (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
                                            (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                                     (Z_to_bv 64 0))))
      by (eapply (read_auxv_word RSEGS Sv48 inp mbase RPH RENT sp0 brk rdraw); first [lctx | exact Hj]).
    rewrite w_add_nat in Hr.
    replace (bv_unsigned (auxvp sp0 inp) + 8 * Z.of_nat j)%Z
      with (bv_unsigned sp0 + Z.of_nat (auxv_off (in_argv inp) (in_envp inp) + 8 * j))%Z by lia.
    rewrite Hr, n_to_le_8_spec. reflexivity.
  Qed.

  Ltac kw_auxv j :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
      replace k with (8 * Z.of_nat j)%Z by reflexivity end;
    rewrite (auxv_word_any j) by (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia);
    unfold auxv_words, auxv_entries; cbn [flat_map fst snd app nth]; reflexivity.

  Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as (Hau & Hab & Hao). destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
    unfold kn_auxv, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3, ?ke4, ?ke7; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4, ?ke7;
      try rewrite Hau; try lia.
    - (* [comment removed for export] *) split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off (in_argv inp) (in_envp inp)))%Z
        with ((2 * q + 3 + Z.of_nat (length (in_argv inp)) + Z.of_nat (length (in_envp inp))) * 8)%Z
        by (unfold auxv_off; lia).
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
      split; [lia|]. split; [lia|]. unfold adenot; cbn [a_base a_off edenot]; rewrite ke4; unfold v_addi.
      rewrite rd_above by (rewrite u_small by lia; lia).
      replace 8%Z with (Z.of_nat 8) by reflexivity.
      rewrite (Hr4 8%nat 8%nat ltac:(lia)). f_equal. fold (secret_bytes rdraw). apply secret_bytes_w.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma main_hwcap : rdn RSEGS mem (Z_to_bv 64 0xe5310) 8 = Some (word_to_le_bytes 8 (in_hwcap inp)).
  Proof.
    pose proof kp_lo as Hlo.
    rewrite (main_entry_rdn_data sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply D_main_hwcap.
  Qed.

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0xb3000) 208896 = true.
  Proof. apply wseg_fast_sound. vm_cast_no_check (@eq_refl bool true). Qed.  (* [comment removed for export] *)

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
  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0xe6000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 inp rdraw tid i).
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
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
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0xb3000) (Z_to_bv 64 (0xb3000 + d)) 208896 m 0xb3000 0xe6000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_data (D_main_self sp0 inp rdraw tid).
    - kw_mem (main_entry_tid sp0 inp mbase rdraw tid Hlo regs mem ME).
    - rewrite ?ke4. kw_data (D_main_canary sp0 inp rdraw tid).          (* [comment removed for export] *)
    - rewrite ?ke4. kw_mem (main_entry_guard sp0 inp mbase rdraw tid Hlo regs mem ME).   (* [comment removed for export] *)
    - kw_data (D_main_auxvp sp0 inp rdraw tid).
    - kw_data (D_main_pagesize sp0 inp rdraw tid Hva).
    - (* [comment removed for export] *) lia.
  Qed.


  Theorem main_know_ok : know_ok RSEGS E mem kn_main.
  Proof using All.
    unfold kn_main, know_ok.
    apply Forall_app; split; [apply know_stack|].
    apply Forall_app; split; [apply know_auxv | apply know_image].
  Qed.

  (* [comment removed for export] *)
  Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
        (length (nth k [a0s; path] []) + 1) = Some (nth k [a0s; path] [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k) <= bv_unsigned sp0 + 2101782)%Z   (* [comment removed for export] *)
    /\ (Z.of_nat (length (nth k [a0s; path] [])) <= 131071)%Z.
  Proof using All.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite len_av2; lia).
    assert (B : (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k))%Z /\
                (bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
                   + Z.of_nat (length (nth k (in_argv inp) [])) + 1 < 2^64)%Z)
      by (eapply argv_ptr_bounds_at; first [lctx | exact Hk']).
    destruct B as [B1 B2].
    assert (Hu : bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
                 = (bv_unsigned sp0 + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp)
                                                + total_arg_bytes_nat (firstn k (in_argv inp))))%Z)
      by (eapply u_cat_argv_ptr with (ph := RPH) (entry := RENT); first [lctx | exact Hk']).
    assert (Hsb : (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp)
                   + total_arg_bytes_nat (in_argv inp) + total_arg_bytes_nat (in_envp inp)
                   <= length (entry_stack_image inp mbase RPH RENT sp0 rdraw))%nat)
      by (apply (struct_av_bound inp mbase RPH RENT sp0 brk rdraw)).   (* see RefMainEntry.v, the same assert *)
    assert (Hl : (Z.of_nat (length (entry_stack_image inp mbase RPH RENT sp0 rdraw)) <= 2101782)%Z)
      by (eapply lay_bsb_len; lctx).
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)) as Hf.
    assert (Hlen : (Z.of_nat (length (nth k (in_argv inp) [])) <= 131071)%Z)
      by (eapply argv_str_len; first [lctx | exact Hk']).
    rewrite Hav in Hlen, B2. repeat split.
    - rewrite rd_above by (rewrite Hav in *; lia).
      assert (Hrd : rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH RENT sp0 rdraw))
                      (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
                      (length (nth k (in_argv inp) []) + 1) = Some (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]))
        by (eapply read_argv_cstr_k; first [lctx | exact Hk']).
      rewrite <- Hav. exact Hrd.
    - exact B1.
    - lia.
    - exact Hlen.
  Qed.
End KnowProofs.
