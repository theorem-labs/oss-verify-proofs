(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the string pointers p0 and p1 measured from the stack VMA's end and the exec file name, auxvp computed directly and rnd placed by the kernel's CONFIG_RSEQ flag; the recorded writable window below sp narrowed to 6144513 bytes and the auxv words no longer recorded, auxv_word_at and kw_auxv removed; the know proofs, rnd_u, main_str and main_str_top go through the launch main_entry names; encoded (CDefT) statements and definitions written out in plain text, the CDefT name table and recorded LiaOrc tables removed). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk FileSim ArgvEnv SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit Layout StartupTac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_startup_defs P_startup P_startup_facts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma D_main_none : forall (inp : ProcInput) (sp0 : word) (rd : EntryDraw) (tid : word) (i : Z),
  valid_argv (in_argv inp) -> (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  D_main_missb i 1 = true ->
  D_main sp0 inp rd tid (Z_to_bv 64 i) = None.
Proof.
  intros inp sp0 rd tid i Hva Hlo Hhi Hb.
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
Lemma seg_rom_high : forall (a : word), (0x7b000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
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
Section MainEntry.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable ev : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av ev tid rd regs mem.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* 08b1429: the strings sit at the top of the block ([cat_argv_ptr] over the stack VMA's end and the
     exec file name, both the launch's: [main_entry] fixes the exec file name to the ambient one), and
     AT_RANDOM's place depends on the kernel's rseq flag *)
  Definition p0 : word := cat_argv_ptr (ed_top rd) av ev a_execfn 0.
  Definition p1 : word := cat_argv_ptr (ed_top rd) av ev a_execfn 1.
  Definition auxvp : word := Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition rnd : word := at_random_ptr sp0 (kb_rseq a_kernel) av ev.

  (* [comment removed for export] *)
  Definition junk_vals2 (R : bvmap 5 word) : list word :=
    map (fun i => getr R (Z_to_bv 5 (Z.of_nat i))) (seq 2 30).
  Definition vals0 : list word := [sp0; p0; p1; auxvp; rnd; tid; canary_w rd; a_hwcap] ++ junk_vals2 regs.
  Definition blobs0 : list (list byte) := [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]].
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  Definition sr_main : list expr := (cons (ELit 0) (cons (ELit 0x3bbb0) (cons (spx (-48)) (cons (ELit 0x10800) (cons (ELit 0x599c8) (cons (EVar 11) (cons (EVar 12) (cons (EVar 13) (cons (spx 8) (cons (ELit 2) (cons (ELit 2) (cons (spx 8) (cons (spx 32) (cons (EVar 19) (cons (EVar 20) (cons (EVar 21) (cons (EVar 22) (cons (EVar 23) (cons (ELit 0x1cdcc) (cons (spx 32) (cons (ELit 0) (cons (ELit 0) (cons (ELit 0) (cons (ELit 0) (cons (ELit 0) (cons (ELit 0) (cons (ELit 0) (cons (ELit 0) (cons (EVar 34) (cons (EVar 35) (cons (EVar 36) [(EVar 37)]))))))))))))))))))))))))))))))).

  (* 08b1429: the mapped window under sp is [wok_lo sp0, sp0) ([MemSplit.wok_lo]): 6144513 bytes *)
  Definition kn_stack : list kentry := (cons (KAlign (EVar 0) 16) (cons (KRange (EVar 0) 0x7fff80000000 0x800000000000) (cons (KWr (SA (EVar 0) (-6144513)) 6144513) (cons (KWord (SA (EVar 0) 0) 8 (ELit 2)) (cons (KWord (SA (EVar 0) 8) 8 (EVar 1)) (cons (KWord (SA (EVar 0) 16) 8 (EVar 2)) [(KWord (SA (EVar 0) 24) 8 (ELit 0))])))))).

  (* 08b1429: the auxv's words are not recorded here: the vector is Linux's own (27 pairs, or 29 under
     CONFIG_RSEQ), and its contents reach the heap through the auxv cell ([rauxv_ok]) *)
  Definition kn_auxv : list kentry := [KRange (EVar 3) 0x7fff80000000 0x800000400000; KRange (EVar 4) 0x7fff80000000 0x800000400000;
    KDisj (SA (EVar 0) (-0x800000)) 0x800000 (SA (EVar 3) 0) 160; KDisj (SA (EVar 0) (-0x800000)) 0x800000 (SA (EVar 4) 0) 16;
    KAlign (EVar 3) 8; KAlign (EVar 4) 8].

  Definition kn_image : list kentry := (cons (KWr (SA (ELit 0) 0x49000) 0x32000) (cons (KImg 0x10000 0x49820) (cons (KImg 0x49821 0x598f8) (cons (KImg 0x799d0 0x799f0) (cons (KWord (SA (ELit 0) 0x59900) 8 (ELit 0x59900)) (cons (KWord (SA (ELit 0) 0x59920) 4 (EVar 5)) (cons (KImg 0x5992c 0x59978) (cons (KImg 0x59980 0x59998) (cons (KImg 0x599a0 0x599b8) (cons (KWord (SA (ELit 0) 0x599b8) 8 (EVar 6)) (cons (KImg 0x599c8 0x599d8) (cons (KImg 0x599e0 0x59a50) (cons (KImg 0x79a08 0x79c30) (cons (KWord (SA (ELit 0) 0x79c30) 8 (EVar 6)) (cons (KImg 0x79c38 0x79c40) (cons (KImg 0x79c51 0x79c58) (cons (KWord (SA (ELit 0) 0x79c58) 8 (EVar 3)) (cons (KImg 0x79c60 0x79c68) (cons (KImg 0x79c78 0x79c80) (cons (KWord (SA (ELit 0) 0x79c80) 8 (ELit 0x1000)) (cons (KImg 0x79c88 0x79cb8) (cons (KWord (SA (ELit 0) 0x79cb8) 8 (EVar 7)) (cons (KImg 0x79cc0 0x7b000) (cons (KRange (EVar 5) 1 0x3fffff) [(KImg 0 0x1000)])))))))))))))))))))))))).

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
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid rd regs mem.

  Let E := E0 sp0 a0s path envv tid rd regs.

      
  #[using="Type"] Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 a0s path envv rd; p1 a0s path envv rd; auxvp sp0 a0s path envv; rnd sp0 a0s path envv; tid; canary_w rd; a_hwcap] ++ junk_vals2 regs) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  #[using="Type"] Lemma junk_vals2_length : length (junk_vals2 regs) = 30%nat.
  Proof. unfold junk_vals2. rewrite length_map, length_seq. reflexivity. Qed.

  #[using="Type"] Lemma vals0_length : length (vals0 sp0 a0s path envv tid rd regs) = 38%nat.
  Proof. unfold vals0. rewrite length_app, junk_vals2_length. reflexivity. Qed.

  #[using="Type"] Lemma ev_junk : forall i, (2 <= i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals.
    replace (6 + i)%nat with (length [sp0; p0 a0s path envv rd; p1 a0s path envv rd; auxvp sp0 a0s path envv; rnd sp0 a0s path envv; tid; canary_w rd; a_hwcap] + (i - 2))%nat by (cbn [length]; lia).
    rewrite app_nth2_plus. unfold junk_vals2. rewrite (nth_map_seq_gen (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia.
    f_equal. f_equal. lia.
  Qed.

    
  #[using="Type"] Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.

Section MainRegs.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid rd regs mem.
  Let E := E0 sp0 a0s path envv tid rd regs.

  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ lazymatch goal with |- _ = edenot _ (spx ?k) => rewrite (spx_val sp0 a0s path envv tid rd regs k) end
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk sp0 a0s path envv tid rd regs (n - 6)) by lia; reflexivity | idtac ]
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | apply (me_szero _ _ _ _ _ _ _ ME); cbn; tauto
                | idtac ].

  #[using="mem av Hvsp Htid ME"] Theorem main_regs_ok : regs_ok E sr_main regs.
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
  Variable rd : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid rd regs mem.
  Let E := E0 sp0 a0s path envv tid rd regs.

  #[using="Hvsp"] Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  #[using="Hvsp"] Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  #[using="Hvsp"] Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  #[using="Type"] Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke1 : ev E 1 = p0 a0s path envv rd. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke2 : ev E 2 = p1 a0s path envv rd. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke3 : ev E 3 = auxvp sp0 a0s path envv. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke4 : ev E 4 = rnd sp0 a0s path envv. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke6 : ev E 6 = canary_w rd. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ke7 : ev E 7 = a_hwcap. Proof. reflexivity. Qed.

  #[using="av Hva Hve Hvsp ME"] Lemma know_stack : know_ok RSEGS E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct (main_entry_launch sp0 av envv tid rd regs mem ME) as (inp & mbase & brk & Eav & Eev & Euid & Egid & Ehw & Ekb & Eef & Hvl & Hlau & RDA & MD & RDD).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva). assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
    unfold kn_stack, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win sp0 av envv tid rd regs mem ME);
        rewrite u_small by lia; unfold wok_lo, stack_window_reach, stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite RDA by lia.
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH (0x1cc80 : word) sp0 rd) sp0 8 = Some (word_le8 (argcN inp)))
        by (eapply (read_argc_w RSEGS Sv48 inp mbase RPH (0x1cc80 : word) sp0 brk rd); try eassumption; unfold sp_window_hi; lia).
      rewrite Hr. unfold argcN. rewrite Eav.
      rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite RDA by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH (0x1cc80 : word) sp0 rd) (sp0 + nat_to_word (8 + 8 * 0)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rd) (in_argv inp) (in_envp inp) (in_execfn inp) 0)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH (0x1cc80 : word) sp0 brk rd); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia | rewrite Eav; subst av; cbn; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. unfold p0. rewrite Eav, Eev, Eef. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite RDA by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH (0x1cc80 : word) sp0 rd) (sp0 + nat_to_word (8 + 8 * 1)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rd) (in_argv inp) (in_envp inp) (in_execfn inp) 1)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH (0x1cc80 : word) sp0 brk rd); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia | rewrite Eav; subst av; cbn; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. unfold p1. rewrite Eav, Eev, Eef. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite RDA by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH (0x1cc80 : word) sp0 rd))
                     (sp0 + nat_to_word (8 + 8 * length (in_argv inp))) 8 = Some (word_le8 (Z_to_bv 64 0)))
        by (eapply (read_argv_null RSEGS Sv48 inp mbase RPH (0x1cc80 : word) sp0 brk rd); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
      rewrite w_add_nat in Hr. rewrite Eav in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      rewrite <- (rdn_wmem_stack RSEGS inp mbase RPH (0x1cc80 : word) sp0 rd) in Hr by (try eassumption; try rewrite u_small by lia; lia).
      unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  #[using="Type"] Lemma auxvp_eq : auxvp sp0 a0s path envv = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_off. subst av. cbn [length]. f_equal. lia. Qed.

  #[using="Hve Hvsp"] Lemma auxvp_u : bv_unsigned (auxvp sp0 a0s path envv) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
    /\ (Z.of_nat (auxv_off av envv) + 176 <= 0x222e00)%Z.
  Proof.
    pose proof kp_lo. pose proof kp_hi. destruct Hve as [Hle _].
    rewrite auxvp_eq. unfold auxv_off in *. subst av. cbn [length] in *.
    rewrite u_small by lia. split; lia.
  Qed.

  (* 08b1429: the AT_RANDOM bytes are read back through [mem] (the stack block is the launch's, which
     [main_entry] names existentially) *)
  #[using="AMB tid rd regs Hva Hve Hvsp ME"] Lemma rnd_u : (bv_unsigned sp0 <= bv_unsigned (rnd sp0 a0s path envv))%Z
    /\ (bv_unsigned (rnd sp0 a0s path envv) + 16 <= bv_unsigned sp0 + 0x222e00)%Z
    /\ (bv_unsigned (rnd sp0 a0s path envv) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (rnd sp0 a0s path envv) + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random rd))))).
  Proof.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct (main_entry_launch sp0 av envv tid rd regs mem ME) as (inp & mbase & brk & Eav & Eev & Euid & Egid & Ehw & Ekb & Eef & Hvl & Hlau & RDA & MD & RDD).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva). assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
    assert (Hl : (Z.of_nat (length (entry_stack_image inp mbase RPH (0x1cc80 : word) sp0 rd)) <= 2101782)%Z)
      by (eapply lay_bsb_len; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact kp_al | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]).
    pose proof (rnd_facts RSEGS Sv48 inp mbase RPH (0x1cc80 : word) sp0 brk rd) as RF.
    repeat (specialize (RF ltac:(first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact kp_al | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]))).
    destruct RF as (A & B & C & D & F).
    assert (Er : rnd sp0 a0s path envv = at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
      by (unfold rnd; rewrite Eav, Eev, Ekb; reflexivity).
    rewrite Er. repeat split; try lia.
    intros j n Hjn. rewrite RDA by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS inp mbase RPH (0x1cc80 : word) sp0 rd) as Hw. unfold wmem in Hw.
    rewrite Hw by (try eassumption; try rewrite u_small by lia; lia).
    apply F. exact Hjn.
  Qed.

  #[using="AMB tid regs av Hva Hve Hvsp ME"] Lemma main_entry_secret :
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (rnd sp0 a0s path envv) + 8)) 8 = Some (word_to_le_bytes 8 (secret_w rd)).
  Proof.
    destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
    rewrite secret_store. unfold secret_bytes. change 8%Z with (Z.of_nat 8) at 1. apply (Hr4 8%nat 8%nat). lia.
  Qed.

  #[using="av Hva Hve Hvsp ME"] Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
    unfold kn_auxv, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3, ?ke4; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4;
      try rewrite Hau; try lia.
    - split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
        by (unfold auxv_off; subst av; cbn [length]; lia).
      apply Z_mod_mult.
  Qed.

  #[using="Hvsp"] Lemma D_main_auxvp : forall (inp : ProcInput) segs, in_argv inp = av -> in_envp inp = envv ->
    rdn segs (D_main sp0 inp rd tid) (Z_to_bv 64 0x79c58) 8 = Some (word_to_le_bytes 8 (auxvp sp0 a0s path envv)).
  Proof.
    intros inp segs Ea Ee. pose proof (u64_range tid). pose proof kp_lo. pose proof kp_hi.
    assert (E' : auxvp sp0 a0s path envv = auxv_w sp0 inp) by (unfold auxvp, auxv_w; rewrite Ea, Ee; reflexivity).
    rewrite E'.
    unfold auxv_w, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.
  (* [comment removed for export] *)

  #[using="Type"] Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x49000) 0x32000 = true.
  Proof. vm_compute. reflexivity. Qed.

  #[using="Type"] Lemma range_disjoint_sub : forall lo n c i, range_disjoint_b lo n c = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> range_disjoint_b i 1 c = true.
  Proof.
    intros lo n [c w] i H Hlo Hhi. unfold range_disjoint_b in *. cbn [fst snd] in *.
    apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  Qed.

  #[using="Type"] Lemma missb_sub : forall lo n i, D_main_missb lo n = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> D_main_missb i 1 = true.
  Proof.
    intros lo n i H Hlo Hhi. unfold D_main_missb in *.
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia].
    apply forallb_forall. intros c Hc. apply (range_disjoint_sub lo n); [|lia|lia].
    apply (proj1 (forallb_forall _ _) H1). exact Hc.
  Qed.

  #[using="av Hva Hvsp ME"] Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x7b000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct (main_entry_launch sp0 av envv tid rd regs mem ME) as (inp & mbase & brk & Eav & Eev & Euid & Egid & Ehw & Ekb & Eef & Hvl & Hlau & RDA & MD & RDD).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva).
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite MD by (rewrite u_small by lia; rewrite stack_max_size_val; lia).
    apply (D_main_none inp sp0 rd tid i Hva'); [lia | lia |].
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data RD L :=
    kw_pre;
    rewrite RD by (rewrite u_small by lia; rewrite stack_max_size_val; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_mem L := kw_pre; rewrite (L RSEGS); try reflexivity.

  #[using="av Hva Hvsp Htid ME"] Lemma know_image : know_ok RSEGS E mem kn_image.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
    destruct (main_entry_launch sp0 av envv tid rd regs mem ME) as (inp & mbase & brk & Eav & Eev & Euid & Egid & Ehw & Ekb & Eef & Hvl & Hlau & RDA & MD & RDD).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva).
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimg;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5, ?ke6, ?ke7; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x49000) (Z_to_bv 64 (0x49000 + d)) 0x32000 m 0x49000 0x7b000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_data RDD (D_main_self inp sp0 tid rd).
    - kw_mem (main_entry_tid sp0 av envv tid rd Hlo regs mem ME).
    - kw_data RDD (D_main_canary inp sp0 tid rd).
    - kw_mem (main_entry_guard sp0 av envv tid rd Hlo regs mem ME). rewrite canary_store. reflexivity.
    - (* [kw_data] applies its lemma to RSEGS; D_main_auxvp now binds segs before its premises *)
      kw_data RDD (fun segs => D_main_auxvp inp segs Eav Eev).
    - kw_data RDD (D_main_pagesize inp sp0 tid rd Hva').
    - kw_data RDD (D_main_hwcap inp sp0 tid rd Hva'); rewrite ?Ehw; try reflexivity.
    - lia.
  Qed.

  #[using="av Hva Hve Hvsp Htid ME"] Theorem main_know_ok : know_ok RSEGS E mem kn_main.
  Proof.
    unfold kn_main, know_ok.
    apply Forall_app; split; [apply know_stack|].
    apply Forall_app; split; [apply know_auxv | apply know_image].
  Qed.

  #[using="AMB tid rd regs Hva Hve Hvsp ME"] Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top rd) av envv a_execfn k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rd) av envv a_execfn k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rd) av envv a_execfn k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z.
  Proof.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    destruct (main_entry_launch sp0 av envv tid rd regs mem ME) as (inp & mbase & brk & Eav & Eev & Euid & Egid & Ehw & Ekb & Eef & Hvl & Hlau & RDA & MD & RDD).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva). assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
    assert (Ec : cat_argv_ptr (ed_top rd) av envv a_execfn k
                 = cat_argv_ptr (ed_top rd) (in_argv inp) (in_envp inp) (in_execfn inp) k) by (rewrite Eav, Eev, Eef; reflexivity).
    assert (El : nth k av [] = nth k (in_argv inp) []) by (rewrite Eav; reflexivity).
    rewrite Ec, El.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Eav; subst av; cbn; lia).
    destruct (argv_ptr_bounds Sv48 inp mbase sp0 brk rd k Hlau Hk') as [B1 B2].
    assert (Hu : bv_unsigned (cat_argv_ptr (ed_top rd) (in_argv inp) (in_envp inp) (in_execfn inp) k)
                 = (bv_unsigned sp0
                    + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rd)
                                  (in_argv inp) (in_envp inp) (in_execfn inp)
                                + total_arg_bytes_nat (firstn k (in_argv inp))))%Z)
      by (eapply (u_cat_argv_ptr Sv48 inp mbase RPH (0x1cc80 : word) sp0 brk rd); try eassumption;
          first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
    assert (Hsb : (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rd) (in_argv inp) (in_envp inp) (in_execfn inp)
                    + total_arg_bytes_nat (in_argv inp) + total_arg_bytes_nat (in_envp inp)
                    <= length (entry_stack_image inp mbase RPH (0x1cc80 : word) sp0 rd))%nat)
      by (eapply struct_av_bound; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact kp_al | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]).
    assert (Hl : (Z.of_nat (length (entry_stack_image inp mbase RPH (0x1cc80 : word) sp0 rd)) <= 2101782)%Z)
      by (eapply lay_bsb_len; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact kp_al | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]).
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)) as Hf.
    pose proof (valid_argv_str_len (in_argv inp) k Hva' Hk') as Hlen.
    repeat split.
    - rewrite RDA by lia.
      pose proof (rdn_wmem_stack RSEGS inp mbase RPH (0x1cc80 : word) sp0 rd) as Hw. unfold wmem in Hw.
      rewrite Hw by (try eassumption; try lia).
      exact (read_argv_cstr_k Sv48 RSEGS inp mbase RPH (0x1cc80 : word) sp0 brk rd k Hlau Hk').
    - exact B1.
    - lia.
    - exact Hlen.
  Qed.

  (* 08b1429: the argv strings end at the stack VMA's end less 8 ([CatExec.u_cat_string_base],
     [launch_string_base_arith]), and that end is at most the Sv48 stack top; the old proof went
     through [build_stack_bytes_within_span] and [main_entry_block_top], which no longer bound the block. *)
  #[using="AMB tid rd regs mem Hva Hve Hvsp ME"] Lemma main_str_top : forall k, (k < 2)%nat ->
    (bv_unsigned (cat_argv_ptr (ed_top rd) av envv a_execfn k) + Z.of_nat (length (nth k av [])) + 9 <= 0x800000000000)%Z.
  Proof.
    intros k Hk.
    destruct (main_entry_launch sp0 av envv tid rd regs mem ME) as (inp & mbase & brk & Eav & Eev & Euid & Egid & Ehw & Ekb & Eef & Hvl & Hlau & RDA & MD & RDD).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva). assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
    assert (Ec : cat_argv_ptr (ed_top rd) av envv a_execfn k
                 = cat_argv_ptr (ed_top rd) (in_argv inp) (in_envp inp) (in_execfn inp) k) by (rewrite Eav, Eev, Eef; reflexivity).
    assert (El : nth k av [] = nth k (in_argv inp) []) by (rewrite Eav; reflexivity).
    rewrite Ec, El.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Eav; subst av; cbn; lia).
    pose proof (launch_string_base_arith Sv48 inp mbase sp0 brk rd Hlau) as HA.
    pose proof (u_cat_string_base Sv48 inp mbase sp0 brk rd Hlau) as Hu.
    pose proof (u64_range sp0). pose proof (u64_range (ed_top rd)).
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

