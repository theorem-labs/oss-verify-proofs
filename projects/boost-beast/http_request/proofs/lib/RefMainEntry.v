(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3; and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); internal commit ids in comments replaced by public commits or removed. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv
  SymExec SymExec2 SymExec2Sound SymRun SymDrive
  MemSplit RefLayout StartupTac RefStartupDefs RefStartup RefStartupFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* 75d69e00: [D_main] is a function of the run's input (RefStartupDefs.v:210). *)
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
  unfold D_main, D_cx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
  repeat (rewrite MemSplit.wbytes_outside;
    [ | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
      | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Hui; rewrite u_small by (cbn; lia);
        match goal with H : djw _ |- _ => unfold djw in H; clear -H; lia end ]).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma seg_rom_high : forall (a : word), (0xb4000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
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
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable ev : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Hve' : in_envp inp = ev.
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Definition p0 : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0.
  Definition p1 : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 1.
  Definition auxvp : word := auxv_w inp sp0.
  Definition rnd : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev.

  (* [comment removed for export] *)
  (* Word 38 is the hwcap the launch writes - [in_hwcap inp], both in the auxv
     ([RefLayout.auxv_words_eq]) and in libc's cell ([RefStartupDefs.v:74]). *)
  Definition vals0 : list word := [sp0; p0; p1; auxvp; rnd; tid] ++ junk_vals regs ++ [in_hwcap inp; canary_w rdraw].
  Definition blobs0 : list (list byte) := [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]].
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  Definition sr_main : list expr :=
    [ELit 0; ELit 0x67178; spx (-48); ELit 0x10800; ELit 0x92650; EVar 11; EVar 12; EVar 13;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x2ac68; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     (* The write window is [wok_lo sp0, sp0), stated with the SYMBOLS, never
        the literal: [MemSplit.wok_lo sp0 = bv_unsigned sp0 + stack_window_reach
        - stack_max_size] (MemSplit.v:122-123), so the offset below sp0 is
        [stack_max_size - stack_window_reach].  The old row claimed the full
        [stack_max_size] window; at this revision the model certifies only from
        [wok_lo], so that claim was 2,244,095 bytes too wide and FALSE. *)
     KWr (SA (EVar 0) (stack_window_reach - stack_max_size))
         (stack_max_size - stack_window_reach);
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  Definition kn_auxv : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000400000; KRange (EVar 4) 0x7fff80000000 0x800000400000;
     (* Rule 12k: the extent of the CLAIMED PREFIX, not the auxv's size.  The
        revision inserts ten pairs ahead of the old vector, so the same facts
        now sit at pairs 10..24, i.e. words 0..49, i.e. 400 bytes. *)
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 400;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 4) 0) 16;
     KAlign (EVar 3) 8; KAlign (EVar 4) 8;
     (* RETABLED to the revision's auxv vector (rule 12k, printed from the model
        on the farm and confirmed five ways):
          0 AT_SYSINFO_EHDR | 1..8 cache words | 9 AT_MINSIGSTKSZ | 10 AT_HWCAP
          11 AT_PAGESZ | 12 AT_CLKTCK | 13 AT_PHDR | 14 AT_PHENT | 15 AT_PHNUM
          16 AT_BASE | 17 AT_FLAGS | 18 AT_ENTRY | 19..22 UID/EUID/GID/EGID
          23 AT_SECURE | 24 AT_RANDOM | 25 AT_EXECFN | (AT_RSEQ x2 if la_rseq) | AT_NULL
        The old table read the SAME nine pairs starting at AT_PHDR = pair 0, so
        every row named the wrong slot at this revision.  Offsets are re-derived
        as 8 * (2 * pair + 0|1), not grepped: AT_RANDOM's value moves from
        16 * 8 + 8 = 136 to 16 * 24 + 8 = 392.  The values are this binary's own.
        AT_NULL IS NO LONGER CLAIMED: its pair index is 26 or 28 according to
        la_rseq, and this list must stay CLOSED - kn_main feeds twelve
        [Eval vm_compute] walk dumps in MainWalk_defs.v - so a parametric
        index 26 + 2 * r is not available here and a literal 26 or 28 would pin
        kb_rseq.  Claiming nothing there keeps every kernel build admitted. *)
     KWord (SA (EVar 3) 160) 8 (ELit 16); KWord (SA (EVar 3) 168) 8 (EVar 38);
     KWord (SA (EVar 3) 176) 8 (ELit 6); KWord (SA (EVar 3) 184) 8 (ELit 4096);
     KWord (SA (EVar 3) 208) 8 (ELit 3); KWord (SA (EVar 3) 216) 8 (ELit 0x10040);
     KWord (SA (EVar 3) 224) 8 (ELit 4); KWord (SA (EVar 3) 232) 8 (ELit 56);
     KWord (SA (EVar 3) 240) 8 (ELit 5); KWord (SA (EVar 3) 248) 8 (ELit 11);
     KWord (SA (EVar 3) 304) 8 (ELit 11); (* [comment removed for export] *)
     KWord (SA (EVar 3) 320) 8 (ELit 12); (* [comment removed for export] *)
     KWord (SA (EVar 3) 368) 8 (ELit 23); KWord (SA (EVar 3) 376) 8 (ELit 0);
     KWord (SA (EVar 3) 384) 8 (ELit 25); KWord (SA (EVar 3) 392) 8 (EVar 4)].
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition kn_image : list kentry :=
    [KWr (SA (ELit 0) 0x80000) 0x34000;
     KImg 0x10000 0x80c20;
     KImg 0x80c21 0x90ca0;
     KImg 0x90caa 0x90cb0; KImg 0x90cba 0x90cc0; KImg 0x90cca 0x90cd0; KImg 0x90cda 0x90ce8;
     KImg 0x90ce9 0x90cf8; KImg 0x90cf9 0x90d08; KImg 0x90d09 0x90d18; KImg 0x90d19 0x90d28;
     KImg 0x90d29 0x92580; KImg 0xb2658 0xb2668;
     KWord (SA (ELit 0) 0x92588) 8 (ELit 0x92588);
     KWord (SA (ELit 0) 0x925a8) 4 (EVar 5);
     KImg 0x925b4 0x92600; KImg 0x92608 0x92620; KImg 0x92628 0x92640;
     KWord (SA (ELit 0) 0x92640) 8 (EVar 39);
     KImg 0x92650 0x92660; KImg 0x92670 0x926d8;
     KWord (SA (ELit 0) 0xb2690) 8 (EVar 39);
     KImg 0xb28c8 0xb28d0;
     KImg 0xb28e1 0xb28e8; KWord (SA (ELit 0) 0xb28e8) 8 (EVar 3);
     KWord (SA (ELit 0) 0xb2910) 8 (ELit 4096);
     KImg 0xb2918 0xb2948; KWord (SA (ELit 0) 0xb2948) 8 (EVar 38); KImg 0xb2950 0xb4000;
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

(* 75d69e00: the three proof sections (MainEntryProofs, MainRegs, KnowProofs) are one
   Section over the run's input, as [Section MainEntry] above states the environment:
   [main_entry] is the record over inp/mbase/entry (RefStartup.v:82), [av]/[envv] are
   tied to the input by [Hargv]/[Henvp], and the launch facts the stack-image layer
   ([ArgvEnv], [RefLayout]) takes are SECTION HYPOTHESES - this unit's [main_entry]
   carries no launch field, so they arrive as MainTop/MainOpen already carry them
   ([Hvl]/[Hlau], RepairG3b.SstepClassG3b).  Shape read
   from coturn/FuzzStunClient RefMainEntry.v:238-665 (plain text), every literal
   re-derived from this binary.  The exports a consumer applies are [Proof using All],
   so their arity is the Section's, in declaration order, whatever a proof touches. *)
Section MainEntryProofs.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variables (mbase entry : word).
  Variables (sp0 brk : word).
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Local Notation av := [a0s; path] (only parsing).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Henvp : in_envp inp = envv.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.

  Local Notation E := (E0 inp sp0 a0s path envv rdraw tid regs) (only parsing).

  Lemma sp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma sp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma sp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma Hva_in : valid_argv (in_argv inp). Proof. rewrite Hargv. exact Hva. Qed.
  Lemma Hve_in : valid_envp (in_envp inp). Proof. rewrite Henvp. exact Hve. Qed.

  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 inp a0s path envv rdraw; p1 inp a0s path envv rdraw; auxvp inp sp0; rnd inp sp0 a0s path envv; tid] ++ junk_vals regs ++ [in_hwcap inp; canary_w rdraw]) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  Lemma length_junk_vals : length (junk_vals regs) = 32%nat.
  Proof. unfold junk_vals. rewrite length_map, length_seq. reflexivity. Qed.

  Lemma ev_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 inp a0s path envv rdraw; p1 inp a0s path envv rdraw; auxvp inp sp0; rnd inp sp0 a0s path envv; tid] + i)%nat.
    rewrite app_nth2_plus. rewrite app_nth1 by (rewrite length_junk_vals; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma ev_38 : ev E 38 = in_hwcap inp.
  Proof.
    rewrite ev_vals. change 38%nat with (length [sp0; p0 inp a0s path envv rdraw; p1 inp a0s path envv rdraw; auxvp inp sp0; rnd inp sp0 a0s path envv; tid] + 32)%nat.
    rewrite app_nth2_plus. rewrite app_nth2 by (rewrite length_junk_vals; lia). rewrite length_junk_vals. reflexivity.
  Qed.

  Lemma ev_39 : ev E 39 = canary_w rdraw.
  Proof.
    rewrite ev_vals. change 39%nat with (length [sp0; p0 inp a0s path envv rdraw; p1 inp a0s path envv rdraw; auxvp inp sp0; rnd inp sp0 a0s path envv; tid] + 33)%nat.
    rewrite app_nth2_plus. rewrite app_nth2 by (rewrite length_junk_vals; lia). rewrite length_junk_vals. reflexivity.
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
                | exact (me_ra _ _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ _ _ ME), Hargv; f_equal; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ _ _ ME), Hargv; f_equal; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; rewrite Hargv; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; rewrite Hargv; reflexivity
                | apply (me_szero _ _ _ _ _ _ _ _ ME); cbn; tauto
                | idtac ].

  Theorem main_regs_ok : regs_ok E sr_main regs.
  Proof using All.
    pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
  Qed.

  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 inp a0s path envv rdraw. Proof. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 inp a0s path envv rdraw. Proof. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp inp sp0. Proof. reflexivity. Qed.
  Lemma ke4 : ev E 4 = rnd inp sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.
  Lemma ke38 : ev E 38 = in_hwcap inp. Proof. exact ev_38. Qed.
  Lemma ke39 : ev E 39 = canary_w rdraw. Proof. exact ev_39. Qed.

  (* The stack-image layer's premises, discharged BY TYPE rather than by slot. *)
  Ltac layout_side :=
    first [ eassumption | exact Hva_in | exact Hve_in | exact kp_al
          | (unfold sp_window_lo; pose proof kp_lo; lia) | (unfold sp_window_hi; pose proof kp_hi; lia) ].

  Lemma know_stack : know_ok RSEGS E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    unfold kn_stack, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
    - split; [lia | exact Hal].
    - lia.
    - split; [unfold stack_max_size, stack_window_reach in *; lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win _ _ _ _ _ _ _ _ ME);
        rewrite u_small by (unfold stack_max_size, stack_window_reach in *; lia);
        unfold wok_lo, stack_max_size, stack_window_reach in *; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (main_entry_rdn_above _ _ _ _ _ _ _ _ ME) by lia.
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rdraw) sp0 8 = Some (word_le8 (argcN inp)))
        by (eapply (read_argc_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw); layout_side).
      rewrite Hr. unfold argcN. rewrite Hargv.
      rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above _ _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rdraw) (sp0 + nat_to_word (8 + 8 * 0)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw);
            first [layout_side | rewrite Hargv; cbn; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. unfold p0. rewrite Hargv, Henvp. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above _ _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rdraw) (sp0 + nat_to_word (8 + 8 * 1)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw);
            first [layout_side | rewrite Hargv; cbn; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. unfold p1. rewrite Hargv, Henvp. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above _ _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rdraw))
                     (sp0 + nat_to_word (8 + 8 * length (in_argv inp))) 8 = Some (word_le8 (Z_to_bv 64 0)))
        by (eapply (read_argv_null RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw); layout_side).
      rewrite w_add_nat in Hr. rewrite Hargv in Hr. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw; unfold wmem in Hw; rewrite Hw by (rewrite ?u_small by lia; lia).
      rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  Lemma auxvp_eq : auxvp inp sp0 = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_w, auxv_off. rewrite Hargv, Henvp. cbn [length]. f_equal. lia. Qed.

  (* The BLOCK size bounds the claimed prefix: [auxv_off_bound] puts the whole vector,
     [auxv_size (kb_rseq ..)] = 464 or 432 bytes, inside the image, and the image is at
     most 2101782 bytes ([lay_bsb_len]); the larger layout's 464 is stated, so the bound
     holds for either kernel build without fixing one. *)
  Lemma auxvp_u : bv_unsigned (auxvp inp sp0) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
    /\ (Z.of_nat (auxv_off av envv) + 464 <= 2240000)%Z.
  Proof using All.
    pose proof kp_lo. pose proof kp_hi.
    assert (Hb : (auxv_off (in_argv inp) (in_envp inp) + auxv_size (kb_rseq (in_kernel inp)) + 16
                  <= length (entry_stack_image inp mbase RPH entry sp0 rdraw))%nat)
      by (eapply auxv_off_bound; layout_side).
    assert (Hl : (Z.of_nat (length (entry_stack_image inp mbase RPH entry sp0 rdraw)) <= 2101782)%Z)
      by (eapply lay_bsb_len; layout_side).
    assert (Hs : (432 <= auxv_size (kb_rseq (in_kernel inp)))%nat)
      by (unfold auxv_size, auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
    rewrite Hargv, Henvp in Hb.
    rewrite auxvp_eq. rewrite u_small by lia. lia.
  Qed.

  Lemma rnd_u : (bv_unsigned sp0 <= bv_unsigned (rnd inp sp0 a0s path envv))%Z
    /\ (bv_unsigned (rnd inp sp0 a0s path envv) + 16 <= bv_unsigned sp0 + 2240000)%Z
    /\ (bv_unsigned (rnd inp sp0 a0s path envv) mod 8 = 0)%Z.
  Proof using All.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hl : (Z.of_nat (length (entry_stack_image inp mbase RPH entry sp0 rdraw)) <= 2101782)%Z)
      by (eapply lay_bsb_len; layout_side).
    pose proof (rnd_facts RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw) as RF.
    repeat match type of RF with ?P -> _ =>
      let H := fresh in assert (H : P) by layout_side; specialize (RF H) end.
    destruct RF as (A & B & C & D & F).
    unfold rnd. rewrite <- Hargv, <- Henvp. repeat split; try assumption; try lia.
  Qed.

  (* Rule 12k: the claimed prefix runs to word 49 (pairs 10..24), inside the 54 words
     of the shorter layout, so [j < 2 * auxv_count] holds for either kernel build. *)
  Lemma auxv_word_at : forall j, (j < 50)%nat ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j)) 8
    = Some (word_to_le_bytes 8 (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entry
                                          (in_uid inp) (in_gid inp) (in_hwcap inp)
                                          (rnd inp sp0 a0s path envv)
                                          (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                                  (Z_to_bv 64 0))).
  Proof using All.
    intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct auxvp_u as [Hu Hb].
    rewrite (main_entry_rdn_above _ _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw; unfold wmem in Hw; rewrite Hw by (rewrite u_small by lia; lia).
    replace (Z_to_bv 64 (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j))
      by (rewrite Hargv, Henvp, w_add_nat; f_equal; lia).
    assert (Hr : rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rdraw))
                   (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j)) 8
                 = Some (word_le8 (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entry
                                            (in_uid inp) (in_gid inp) (in_hwcap inp)
                                            (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
                                            (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                                     (Z_to_bv 64 0))))
      by (eapply (read_auxv_word RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw);
          first [ layout_side | (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia) ]).
    rewrite Hr. rewrite n_to_le_8_spec. unfold rnd. rewrite Hargv, Henvp. reflexivity.
  Qed.

  Ltac kw_auxv j :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
      replace k with (8 * Z.of_nat j)%Z by reflexivity end;
    rewrite (auxv_word_at j) by lia; unfold auxv_words, auxv_entries; cbn [flat_map fst snd app nth]; reflexivity.

  Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3).
    unfold kn_auxv, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3, ?ke4, ?ke38; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4, ?ke38;
      try rewrite Hau; try lia.
    - (* [comment removed for export] *) split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
        by (unfold auxv_off; cbn [length]; lia).
      apply Z_mod_mult.
    (* Re-keyed to the revision's vector: AT_HWCAP words 20,21; AT_PAGESZ 22,23;
       AT_PHDR 26,27; AT_PHENT 28,29; AT_PHNUM 30,31; AT_UID type 38; AT_EUID
       type 40; AT_SECURE 46,47; AT_RANDOM 48,49.  Sixteen rows, in the order
       [kn_auxv] lists them. *)
    - kw_auxv 20%nat. - kw_auxv 21%nat. - kw_auxv 22%nat. - kw_auxv 23%nat.
    - kw_auxv 26%nat. - kw_auxv 27%nat. - kw_auxv 28%nat. - kw_auxv 29%nat.
    - kw_auxv 30%nat. - kw_auxv 31%nat.
    - kw_auxv 38%nat. - kw_auxv 40%nat.
    - kw_auxv 46%nat. - kw_auxv 47%nat. - kw_auxv 48%nat. - kw_auxv 49%nat.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxvp : forall segs,
    rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0xb28e8) 8
    = Some (word_to_le_bytes 8 (auxvp inp sp0)).
  Proof using All.
    intros segs. pose proof (u64_range tid). pose proof kp_lo. pose proof kp_hi.
    unfold auxvp, auxv_w, D_main, D_cx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x80000) 0x34000 = true.
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
  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0xb4000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data _ _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none inp sp0 rdraw tid i Hva_in); [lia | lia |].
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  (* The [RefStartupFacts] reads are applied BY NAME: [erewrite] instantiates the
     Section binders from the goal, the side premises close by type. *)
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data _ _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    erewrite L by first [eassumption | exact Hva_in | exact kp_lo | exact kp_hi]; try reflexivity.
  Ltac kw_mem L := kw_pre; rewrite L; try reflexivity.

  Lemma know_image : know_ok RSEGS E mem kn_image.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimg;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5, ?ke38, ?ke39; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - (* [comment removed for export] *) split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x80000) (Z_to_bv 64 (0x80000 + d)) 0x34000 m 0x80000 0xb4000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_data D_main_self.
    - kw_mem (main_entry_tid _ _ _ _ kp_lo _ _ _ _ ME RSEGS).
    - kw_data D_main_canary; rewrite ?ke39; reflexivity.
    - kw_mem (main_entry_guard _ _ _ _ kp_lo _ _ _ _ ME RSEGS); rewrite ?ke39, ?canary_bytes_w; reflexivity.
    - kw_data D_main_auxvp.
    - kw_data D_main_pagesize.
    - kw_data D_main_hwcap; rewrite ?ke38; reflexivity.
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
    rdn RSEGS mem (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) <= bv_unsigned sp0 + 2107576)%Z   (* [comment removed for export] *)
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z.
  Proof using All.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    rewrite <- Hargv, <- Henvp.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Hargv; cbn; lia).
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
    pose proof (valid_argv_str_len (in_argv inp) k Hva_in Hk') as Hlen.
    repeat split.
    - rewrite (main_entry_rdn_above _ _ _ _ _ _ _ _ ME) by lia.
      pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw; unfold wmem in Hw; rewrite Hw by lia.
      exact (read_argv_cstr_k Sv48 RSEGS inp mbase RPH entry sp0 brk rdraw k Hlau Hk').
    - exact B1.
    - lia.
    - exact Hlen.
  Qed.
End MainEntryProofs.
