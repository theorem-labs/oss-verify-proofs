(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the rseq-dependent auxv, the 6144513-byte zero-filled stack window): changed D_main_auxvp, D_main_none, E and 26 more; added DRV_ZWIN, entry, inp and 2 more; removed auxv_word_at, kw_auxv, main_auxv and 1 more; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/U/Pm10MainEntry_u.v, 244 lines within its lines 22-636. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import MuslStrlen.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv
  SymExec SymExec2 SymExec2Sound SymRun SymDrive
  MemSplit RefLayout StartupTac. From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6StartupDefs_u5 Pm6Startup_u5 Pm6StartupFacts_u5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

(* THE ZERO-FILLED WINDOW below sp.  OLD [8388608] (8 MiB, [stack_max_size]) -> NEW [DRV_ZWIN].
   [DRV_ZWIN] = 6144513 = [StoreOk.stack_window_depth] ([StoreOk.stack_window_depth_val]); at LPS
   75d69e00 [wrap_mem] zero-fills only down to [MemSplit.wok_lo sp0 = sp0 - 6144513], so a
   [KWr (SA (EVar 0) (-8388608)) 8388608] row is FALSE.  Kept a numeral (the model's plan spells it
   at AsanPlanCore.v:3911).  Beware the homonym: [sp0 - 8388608] in the [hl_ceil] / [stack_max_size]
   family ([HeapIface.hl_ceil], [DrvKit.rg_stack]'s [- 2 ^ 23]) is a different quantity and stays. *)
Notation DRV_ZWIN := 6144513%Z (only parsing).

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.


Lemma D_main_none : forall inp sp0 rdraw rnd tid (i : Z),
  valid_argv (in_argv inp) -> (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  D_main_missb i 1 = true ->
  D_main inp sp0 rdraw rnd tid (Z_to_bv 64 i) = None.
Proof.
  intros inp sp0 rdraw rnd tid i Hva Hlo Hhi Hb.
  pose proof (u64_range tid) as Ht. pose proof (u64_range (in_hwcap inp)) as Hhw.
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
  Time repeat (rewrite MemSplit.wbytes_outside;
    [ | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
      | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Hui; rewrite u_small by (cbn; lia);
        match goal with H : djw _ |- _ => unfold djw in H; clear -H; lia end ]).
  reflexivity.
Qed.

Lemma seg_rom_high : forall (a : word), (0xfe000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
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

Section MainEntry.
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
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
  Hypothesis ME : main_entry inp mbase entry sp0 av ev uid hw rdraw tid regs mem.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* 08b1429: the strings sit at the top of the block ([cat_argv_ptr] over the stack top and the exec file
     name), and AT_RANDOM's place depends on the input's rseq flag *)
  Definition p0 : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0.
  Definition p1 : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 1.
  Definition auxvp : word := Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition rnd : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev.

  Definition vals0 : list word := [sp0; p0; p1; auxvp; rnd; tid] ++ junk_vals regs.
  Definition blobs0 : list (list byte) :=
    [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]; word_to_le_bytes 8 (canary_w (ed_random rdraw)); word_to_le_bytes 8 hw].
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  Definition sr_main : list expr :=
    [ELit 0; ELit 0xad2c8; spx (-48); ELit 0x10800; ELit 0xdd010; EVar 11; EVar 12; EVar 13;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x3a170; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     (* 08b1429: the mapped window under sp is [wok_lo sp0, sp0) (MemSplit), 6144513 bytes *)
     KWr (SA (EVar 0) (-6144513)) 6144513;
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  Definition kn_auxv : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000400000; KRange (EVar 4) 0x7fff80000000 0x800000400000;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 160;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 4) 0) 16;
     KAlign (EVar 3) 8; KAlign (EVar 4) 8
     (* 08b1429: the auxv's words are not recorded here; the vector is Linux's own (27 pairs, or 29 under
        CONFIG_RSEQ) and its contents reach the heap only through the auxv cell ([rauxv_ok]) *)
      ].

  Definition kn_image : list kentry :=
    [KWr (SA (ELit 0) 0xcb000) 0x33000;
     KImg 0x10000 0xcb538;
     KImg 0xcb541 0xdcf40; KImg 0xfd018 0xfd038;
     KWord (SA (ELit 0) 0xdcf48) 8 (ELit 0xdcf48);
     KWord (SA (ELit 0) 0xdcf68) 4 (EVar 5);
     KImg 0xdcf74 0xdcfc0; KImg 0xdcfc8 0xdcfe0; KWord (SA (ELit 0) 0xdcfe0) 8 (ELit 0xfd2d8); KImg 0xdcfe8 0xdd000;
     KBlob (SA (ELit 0) 0xdd000) (ELit 8) 2;                       (* [comment removed for export] *)
     KImg 0xdd010 0xdd020; KImg 0xdd028 0xfd018; KImg 0xfd050 0xfd280;
     KBlob (SA (ELit 0) 0xfd280) (ELit 8) 2;                       (* [comment removed for export] *)
     KImg 0xfd288 0xfd290;
     KImg 0xfd2a1 0xfd2a8; KWord (SA (ELit 0) 0xfd2a8) 8 (EVar 3);
     KImg 0xfd2b0 0xfd2b8; KImg 0xfd2c8 0xfd2d0; KWord (SA (ELit 0) 0xfd2d0) 8 (ELit 4096);
     KImg 0xfd2d8 0xfd308; KBlob (SA (ELit 0) 0xfd308) (ELit 8) 3 (* [comment removed for export] *); KImg 0xfd310 0xfd418 (* [comment removed for export] *); KImg 0xfd418 0xfe000;
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
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
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
  Hypothesis ME : main_entry inp mbase entry sp0 av envv uid hw rdraw tid regs mem.

  Let E := E0 sp0 a0s path envv hw rdraw tid regs inp.

  Lemma sp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma sp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma sp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.

  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 a0s path envv rdraw inp; p1 a0s path envv rdraw inp; auxvp sp0 a0s path envv; rnd sp0 a0s path envv inp; tid] ++ junk_vals regs) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  Lemma ev_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 a0s path envv rdraw inp; p1 a0s path envv rdraw inp; auxvp sp0 a0s path envv; rnd sp0 a0s path envv inp; tid] + i)%nat.
    rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.

Section MainRegs.
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
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
  Hypothesis ME : main_entry inp mbase entry sp0 av envv uid hw rdraw tid regs mem.
  Let E := E0 sp0 a0s path envv hw rdraw tid regs inp.

  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ rewrite (spx_val sp0 a0s path envv hw rdraw tid regs inp)
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk sp0 a0s path envv hw rdraw tid regs inp (n - 6)) by lia; reflexivity | idtac ]
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
  Proof using All.
    pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
  Qed.
End MainRegs.

Section KnowProofs.
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
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
  Hypothesis ME : main_entry inp mbase entry sp0 av envv uid hw rdraw tid regs mem.
  Let E := E0 sp0 a0s path envv hw rdraw tid regs inp.

  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 a0s path envv rdraw inp. Proof. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 a0s path envv rdraw inp. Proof. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke4 : ev E 4 = rnd sp0 a0s path envv inp. Proof. reflexivity. Qed.
  Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.

  Lemma know_stack : know_ok RSEGS E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct (main_entry_inp inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) as (Eav & Eev & Euid & Ehw & Hvl & brk & Hlau).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva). assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
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
        by (eapply (read_argc_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw); try eassumption; unfold sp_window_hi; lia).
      rewrite Hr. unfold argcN. rewrite Eav.
      rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rdraw) (sp0 + nat_to_word (8 + 8 * 0)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia | rewrite Eav; subst av; cbn; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. unfold p0. rewrite Eav, Eev. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rdraw) (sp0 + nat_to_word (8 + 8 * 1)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia | rewrite Eav; subst av; cbn; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. unfold p1. rewrite Eav, Eev. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rdraw))
                     (sp0 + nat_to_word (8 + 8 * length (in_argv inp))) 8 = Some (word_le8 (Z_to_bv 64 0)))
        by (eapply (read_argv_null RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
      rewrite w_add_nat in Hr. rewrite Eav in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      rewrite <- (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) in Hr by (try eassumption; try rewrite u_small by lia; lia).
      unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  Lemma auxvp_eq : auxvp sp0 a0s path envv = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_off. subst av. cbn [length]. f_equal. lia. Qed.

  Lemma auxvp_u : bv_unsigned (auxvp sp0 a0s path envv) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
    /\ (Z.of_nat (auxv_off av envv) + 176 <= 2240000)%Z.
  Proof using Hva Hve Hvsp Htid ME.
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
  Proof using Hva Hve Hvsp Htid ME.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct (main_entry_inp inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) as (Eav & Eev & Euid & Ehw & Hvl & brk & Hlau).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva). assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
    assert (Hl : (Z.of_nat (length (entry_stack_image inp mbase RPH entry sp0 rdraw)) <= 2101782)%Z)
      by (eapply lay_bsb_len; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact kp_al | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]).
    pose proof (rnd_facts RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw) as RF.
    (* the [repeat (...] was never closed: "Syntax error: ')' expected after [ltac_expr]" at the full stop *)
    repeat (specialize (RF ltac:(first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact kp_al | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]))).
    destruct RF as (A & B & C & D & F).
    (* [rewrite <- Eav] on the goal found no [av], and rewriting [rnd_facts]' own
       conclusions the other way left [lia] with two different atoms ([av] in the
       hypotheses, [[a0s; path]] in the goal), so the bound conjunct stayed open.
       [rnd_facts] states everything in [in_argv inp] / [in_envp inp], so the goal is the
       side that must move: [unfold rnd] exposes [av]'s VALUE (it is a section [Let],
       :104), [fold av] names it again, and then the original rewrite applies.  A is
       [sp0 <= ptr], B is [ptr + 16 <= sp0 + length image], C is
       [sp0 + length < 2 ^ 64], D is [ptr mod 8 = 0], F is the [rdn] fact
       (Pm6Startup3.v:51-62); the goal's second conjunct is B with Hl
       ([length image <= 2101782]), which is [lia]'s. *)
    unfold rnd. try fold av.
    rewrite <- ?Eav, <- ?Eev. repeat split; try assumption; try lia.
  Qed.

  Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
    unfold kn_auxv, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3, ?ke4; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4;
      try rewrite Hau; try lia.
    -   split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
        by (unfold auxv_off; subst av; cbn [length]; lia).
      apply Z_mod_mult.
  Qed.

  Lemma D_main_auxvp : forall segs,
    rdn segs (D_main inp sp0 rdraw (ed_random rdraw) tid) (Z_to_bv 64 0xfd2a8) 8
    = Some (word_to_le_bytes 8 (auxvp sp0 a0s path envv)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range (in_hwcap inp)). pose proof kp_lo. pose proof kp_hi.
    destruct (main_entry_inp inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) as (Eav & Eev & _).
    assert (Ea : auxvp sp0 a0s path envv = auxv_w inp sp0) by (unfold auxvp, auxv_w; rewrite Eav, Eev; reflexivity).
    rewrite Ea.
    unfold auxv_w, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0xcb000) 0x33000 = true.
  Proof. vm_compute. reflexivity. Qed.

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
  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0xfe000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    destruct (main_entry_inp inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) as (Eav & _).
    apply (D_main_none inp sp0 rdraw (ed_random rdraw) tid i ltac:(rewrite Eav; exact Hva)); [lia | lia |].
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_mem L := kw_pre; rewrite (L RSEGS); try reflexivity.
  (* [comment removed for export] *)
  Ltac kblob8 L :=
    unorm; rewrite ?Z.add_0_l; repeat split; try lia;
    try (subst E; unfold E0; cbn [eb blobs_ev blobs0 nth]; rewrite length_N_to_le_bytes; reflexivity);
    intros i Hi; subst E; unfold E0; cbn [eb blobs_ev blobs0 nth];
    rewrite (main_entry_mem_data inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    apply L; lia.

  Lemma know_image : know_ok RSEGS E mem kn_image.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
    destruct (main_entry_inp inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) as (Eav & Eev & Euid & Ehw & _).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva).
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimg;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    -   split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0xcb000) (Z_to_bv 64 (0xcb000 + d)) 0x33000 m 0xcb000 0xfe000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    (* Pm6StartupFacts_u5's two sections discharge [inp sp0 rdraw tid] (Section Facts) and
       [sp0 av ev uid hw rdraw tid .. regs mem inp mbase entry ME] (Section FactsME) followed
       by WHICHEVER of [Hva Hlo Hhi] each proof happened to use - and a [first [...]] inside
       those proofs means that set is not stable across revisions: a hypothesis a revision
       makes unused is dropped from the signature and every positional caller shifts by one.
       [main_entry_tid] was called with [Hlo] in [Hva]'s slot ("The term "Hlo" has type ...
       while it is expected to have type "valid_argv av"").  Every call below now tries the
       plausible discharges in turn, the same idiom Pm6StartupFacts_u5 uses internally, with
       a unification-built fallback that no discharge order can break. *)
    - first [ kw_data (D_main_self inp sp0 rdraw tid)
            | kw_data (D_main_self inp sp0 rdraw tid Hva')
            | kw_data (D_main_self inp sp0 rdraw tid Hva' Hlo Hhi) ].
    -   (* The diagnostic round printed the discharged signature, and it is [Hva] and [Hlo]
           WITHOUT [Hhi] - the one combination the previous chain did not try:
             forall sp0 av ev uid hw rdraw tid, valid_argv av ->
               (140735340871680 <= bv_unsigned sp0)%Z ->
               forall regs mem inp mbase entry, main_entry .. ->
               forall segs, rdn segs mem (Z_to_bv 64 905064) 4 = Some (word_to_le_bytes 4 tid)
           ([Hhi] is dead in its proof, so Rocq dropped it: rule 25j). *)
        first [ kw_mem (main_entry_tid sp0 av envv uid hw rdraw tid Hva Hlo regs mem inp mbase entry ME)
              | kw_mem (main_entry_tid sp0 av envv uid hw rdraw tid Hva Hlo Hhi regs mem inp mbase entry ME)
              | kw_mem (main_entry_tid sp0 av envv uid hw rdraw tid Hva regs mem inp mbase entry ME)
              | kw_mem (main_entry_tid sp0 av envv uid hw rdraw tid regs mem inp mbase entry ME) ].
    - first [ kw_data (D_main_locale inp sp0 rdraw tid)
            | kw_data (D_main_locale inp sp0 rdraw tid Hva')
            | kw_data (D_main_locale inp sp0 rdraw tid Hva' Hlo Hhi) ].
    -   first [ kblob8 (D_canary_pt inp sp0 rdraw tid Hva' Hlo)
              | kblob8 (D_canary_pt inp sp0 rdraw tid Hva')
              | kblob8 (D_canary_pt inp sp0 rdraw tid Hva' Hlo Hhi)
              | kblob8 (D_canary_pt inp sp0 rdraw tid) ].
    -   first [ kblob8 (D_guard_pt inp sp0 rdraw tid Hva' Hlo)
              | kblob8 (D_guard_pt inp sp0 rdraw tid Hva')
              | kblob8 (D_guard_pt inp sp0 rdraw tid Hva' Hlo Hhi)
              | kblob8 (D_guard_pt inp sp0 rdraw tid) ].
    - kw_data D_main_auxvp.
    - first [ kw_data (D_main_pagesize inp sp0 rdraw tid Hva' Hlo)
            | kw_data (D_main_pagesize inp sp0 rdraw tid Hva')
            | kw_data (D_main_pagesize inp sp0 rdraw tid Hva' Hlo Hhi)
            | kw_data (D_main_pagesize inp sp0 rdraw tid) ].
    -   unorm; rewrite ?Z.add_0_l; repeat split; try lia;
        try (subst E; unfold E0; cbn [eb blobs_ev blobs0 nth]; rewrite length_N_to_le_bytes; reflexivity);
        intros i Hi; subst E; unfold E0; cbn [eb blobs_ev blobs0 nth];
        rewrite (main_entry_mem_data inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
        rewrite <- Ehw;
        first [ apply (D_hwcap_pt inp sp0 rdraw tid Hva' Hlo)
              | apply (D_hwcap_pt inp sp0 rdraw tid Hva')
              | apply (D_hwcap_pt inp sp0 rdraw tid Hva' Hlo Hhi)
              | apply (D_hwcap_pt inp sp0 rdraw tid) ]; lia.
    -   lia.
  Qed.

  Theorem main_know_ok : know_ok RSEGS E mem kn_main.
  Proof using All.
    unfold kn_main, know_ok.
    apply Forall_app; split; [apply know_stack|].
    apply Forall_app; split; [apply know_auxv | apply know_image].
  Qed.

  Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z.
  Proof using All.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    destruct (main_entry_inp inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) as (Eav & Eev & Euid & Ehw & Hvl & brk & Hlau).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva). assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
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
      by (eapply (u_cat_argv_ptr Sv48 inp mbase RPH entry sp0 brk rdraw); try eassumption;
          first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
    (* know_image closes now; this is the next one.  [struct_av_bound] has a premise none of
       the seven alternatives below discharges ("No applicable tactic", :581 - [first] again
       reports only itself).  Print its discharged signature and widen the list; the added
       alternatives are all sound side-condition closers, tried only after the original seven. *)
    assert (Hsb : (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp)
                    + total_arg_bytes_nat (in_argv inp) + total_arg_bytes_nat (in_envp inp)
                    <= length (entry_stack_image inp mbase RPH entry sp0 rdraw))%nat)
      by (eapply struct_av_bound;
          first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact kp_al
                | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)
                | exact Hvsp | exact Htid | eassumption | assumption | lia | reflexivity]).
    assert (Hl : (Z.of_nat (length (entry_stack_image inp mbase RPH entry sp0 rdraw)) <= 2101782)%Z)
      by (eapply lay_bsb_len; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact kp_al | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]).
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)) as Hf.
    pose proof (valid_argv_str_len (in_argv inp) k Hva' Hk') as Hlen.
    repeat split.
    - rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by lia.
      pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw. unfold wmem in Hw. rewrite Hw by lia.
      exact (read_argv_cstr_k Sv48 RSEGS inp mbase RPH entry sp0 brk rdraw k Hlau Hk').
    - exact B1.
    - lia.
    - exact Hlen.
  Qed.

  (* 08b1429: the argv strings end at the stack VMA's end less 8 ([CatExec.u_cat_string_base],
     [launch_string_base_arith]), and that end is at most the Sv48 stack top; the old proof went
     through [build_stack_bytes_within_span] and [entry_stack_fits], which no longer bound the block. *)
  Lemma main_str_fits : forall k, (k < 2)%nat ->
    (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) + Z.of_nat (length (nth k av [])) + 9 <= 0x800000000000)%Z.
  Proof using All.
    intros k Hk.
    destruct (main_entry_inp inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) as (Eav & Eev & Euid & Ehw & Hvl & brk & Hlau).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva). assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
    assert (Ec : cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k
                 = cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k) by (rewrite Eav, Eev; reflexivity).
    assert (El : nth k av [] = nth k (in_argv inp) []) by (rewrite Eav; reflexivity).
    rewrite Ec, El.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Eav; subst av; cbn; lia).
    pose proof (launch_string_base_arith Sv48 inp mbase sp0 brk rdraw Hlau) as HA.
    pose proof (u_cat_string_base Sv48 inp mbase sp0 brk rdraw Hlau) as Hu.
    pose proof (u64_range sp0). pose proof (u64_range (ed_top rdraw)).
    pose proof (Nat2Z.is_nonneg
      (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
    pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat (firstn k (in_argv inp)))).
    assert (Hstr : (Z.of_nat (total_arg_bytes_nat (firstn k (in_argv inp)))
                    + Z.of_nat (length (nth k (in_argv inp) [])) + 1
                    <= Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                   (in_execfn inp)))%Z).
    { pose proof (total_arg_bytes_firstn_within (in_argv inp) k Hk') as Hw.
      unfold launch_string_bytes. rewrite length_flatten_strings.
      pose proof (Nat2Z.is_nonneg (length (flatten_strings (in_envp inp)))).
      pose proof (Nat2Z.is_nonneg (length (in_execfn inp))).
      lia. }
    pose proof Hlau as Hlau2. cbn [entry_launch_ok_va] in Hlau2. destruct Hlau2 as ((_ & Htop & _) & _).
    assert (Hv : (va_stack_top Sv48 <= 0x800000000000)%Z) by (unfold Z.le; vm_compute; discriminate).
    rewrite (cat_argv_ptr_offset _ _ _ _ k Hk'), word_add_nat_Z2bv, Hu.
    rewrite u_Z2bv_lt by lia.
    lia.
  Qed.
End KnowProofs.

End FPX_1.
