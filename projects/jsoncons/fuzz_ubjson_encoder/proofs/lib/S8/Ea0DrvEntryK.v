(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the SIGPIPE disposition as a launch variable; the new launch (process input, auxv, group id, exec file name); the CONFIG_RSEQ flag; the channel-reader premise of writev; the string read-ahead slack of 9; imports; new lemmas; unused lemmas removed; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0DrvEntryK.v, 390 lines within its lines 23-1248. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec AgentLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BackingAlgebra.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import AsanPlacement.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanCeil.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Ea0DefsK Ea0PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK Ea0HandoffK Ea0ArtCellsK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import HeapIface HeapIfaceA HeapIfaceAEx ArtBridge CatExec ArgvEnv FileSim MemSplit RefLayout MuslStrlen AsanPlanSoundSumsK StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanCoreK.APCK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition KE_SPK (k : Z) : expr := EAlu ALU_ADD e_sp0 (ELit k).

Definition KE_ENVP : expr :=
  EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1))
     (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 4096) (EVar 10))))) (ELit 16).


Definition DRV_REGS : list (Z * expr) :=
  [(1, ELit 0x119c34); (2, KE_SPK (-48)); (3, ELit 0x10800); (4, ELit 0x675a80); (8, KE_SPK 8); (9, EVar 1); (10, EVar 1); (11, KE_SPK 8);
   (12, KE_ENVP); (18, ELit 0xa8488); (19, KE_ENVP); (20, ELit 0); (21, ELit 0); (22, ELit 0); (23, ELit 0); (24, ELit 0); (25, ELit 0);
   (26, ELit 0); (27, ELit 0)].

Definition opt_eqb (o : option expr) (e : expr) : bool := match o with Some v => expr_eqb v e | None => false end.
Definition img_cover (k : list kentry) (lo hi : Z) : bool :=
  existsb (fun K => match K with KImg l h => (l <=? lo) && (hi <=? h) | _ => false end)%bool k.

Definition DRV_IMG : list (Z * Z) := [(0x10000, 0x13b208); (0x13b224, 0x13e340); (0x66404a, 0x6759b0); (0x695d48, 0x695d78)].

Definition drv_chk (r : Z) (cs : acs) : bool :=
  (Z.eqb (pc cs) 0xa8488
   && forallb (fun p => expr_eqb (sr_get (s_regs (a_ss cs)) (Z_to_bv 5 (fst p))) (snd p)) DRV_REGS
   && lin_nowrapR (kn cs) e_sp0 && lin_nowrapR (kn cs) (KE_SPK (-48)) && lin_nowrapR (kn cs) (KE_SPK 8) && lin_nowrapR (kn cs) KE_ENVP
   && lin_nowrapR (kn cs) (e_str0 r) && lin_nowrapR (kn cs) (e_str1 r)
   && opt_eqb (kfind_word (kn cs) e_sp0 0 8) (EVar V_ARGC) && opt_eqb (kfind_word (kn cs) e_sp0 8 8) (e_str0 r)
   && opt_eqb (kfind_word (kn cs) e_sp0 16 8) (e_argv1w r)
   && opt_eqb (kfind_wr (kn cs) e_sp0 (-stack_window_depth)) (ELit stack_window_depth)
   && match kfind_word (kn cs) (ELit 0) 0x695ac0 8 with Some v => opt_eqb (kfind_word (kn cs) (ELit 0) 0x675a70 8) v | None => false end
   && forallb (fun r' => img_cover (kn cs) (fst r') (snd r')) DRV_IMG
   && match a_fd cs with FdStd => true | _ => false end)%bool.

Definition KE_AUX : expr :=
  EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2))
    (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 4096) (EVar 10))))).
Definition KE_RND (r : Z) : expr := fst (e_atrb r).
Definition KE_RNDOFF (r : Z) : Z := snd (e_atrb r).

Definition AUX_PAIRS (r : Z) : list Z := [10; 11; 13; 14; 15; 19; 20; 23; 24; 26 + 2 * r].
Definition AUX_OFFS (r : Z) : list Z := flat_map (fun i => [24 + 16 * i; 24 + 16 * i + 8]) (AUX_PAIRS r).
Definition is_some {X} (o : option X) : bool := match o with Some _ => true | None => false end.
Definition kfind_blob16 (k : list kentry) (b : expr) (off : Z) : option nat :=
  match List.find (fun K => match K with
                            | KBlob a n _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off && expr_eqb n (ELit 16))%bool
                            | _ => false end) k with
  | Some (KBlob _ _ i) => Some i
  | _ => None
  end.
Lemma kfind_blob16_In : forall k b off i, kfind_blob16 k b off = Some i -> In (KBlob (SA b off) (ELit 16) i) k.
Proof.
  intros k b off i H. unfold kfind_blob16 in H.
  destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hin HK]. destruct K as [ | |a n i'| | | | | | | ]; try discriminate.
  injection H as <-. apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. apply expr_eqb_eq in H3. destruct a as [ab ao]. cbn in H1, H2. subst. exact Hin.
Qed.
Definition stk_core (r : Z) (cs : acs) : bool :=
  (forallb (fun off => is_some (kfind_word (kn cs) KE_AUX off 8)) (AUX_OFFS r)
   && lin_nowrapR (kn cs) KE_AUX && lin_nowrapR (kn cs) (e_atrandom r)
   && is_some (kfind_blob16 (kn cs) (KE_RND r) (KE_RNDOFF r)))%bool.
Definition stk_cover (r : Z) (cs : acs) : bool :=
  (lin_nowrapR (kn cs) (KE_RND r) && lin_nowrapR (kn cs) (escale 8 (EVar V_G))
   && existsb (kentry_eqb (KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (AUXSZ r)))) (kn cs)
   && existsb (kentry_eqb (KUnk (SA (fst e_auxb) (snd e_auxb + AUXSZ r)) (escale 8 (EVar V_G)))) (kn cs)
   && existsb (kentry_eqb (KUnk (SA (KE_RND r) (KE_RNDOFF r + 16)) (EVar V_W))) (kn cs))%bool.
Definition stk_chk (r : Z) (cs : acs) : bool := (stk_core r cs && stk_cover r cs)%bool.


Definition KE_RNDP (r : Z) : expr := e_atrandom r.
Definition KE_AUXP : expr := EAlu ALU_ADD KE_AUX (ELit 24).
Definition AUXV_EXP (r : Z) : list (Z * expr) :=
  combine (AUX_OFFS r)
    [ELit 16; EVar V_HW; ELit 6; ELit 4096; ELit 3; ELit 0x10040; ELit 4; ELit 56; ELit 5; ELit 11;
     ELit 11; EVar V_UID; ELit 12; EVar V_UID; ELit 23; ELit 0; ELit 25; KE_RNDP r; ELit 0; ELit 0].
Definition lib_chk (r : Z) (cs : acs) : bool :=
  (opt_eqb (kfind_word (kn cs) (ELit 0) 0x6759b8 8) (ELit 0x6759b8)
   && match kfind_word (kn cs) (ELit 0) 0x6759d8 4 with Some v => existsb (kentry_eqb (KRange v 1 4194303)) (kn cs) | None => false end
   && opt_eqb (kfind_word (kn cs) (ELit 0) 0x675a50 8) (ELit 0x695d48)
   && opt_eqb (kfind_word (kn cs) (ELit 0) 0x695d18 8) KE_AUXP
   && lin_nowrapR (kn cs) KE_AUXP
   && forallb (fun p => opt_eqb (kfind_word (kn cs) KE_AUX (fst p) 8) (snd p)) (AUXV_EXP r)
   && existsb (kentry_eqb (KRange (EVar V_UID) 0 4294967294)) (kn cs))%bool.

Definition AUXE (r : Z) : list (option expr) :=
  [Some (ELit 33); None; Some (ELit 40); None; Some (ELit 41); None; Some (ELit 42); None; Some (ELit 43); None;
   Some (ELit 44); None; Some (ELit 45); None; Some (ELit 46); None; Some (ELit 47); None; Some (ELit 51); None;
   Some (ELit 16); Some (EVar V_HW); Some (ELit 6); Some (ELit 4096); Some (ELit 17); Some (ELit 100);
   Some (ELit 3); Some (ELit 0x10040); Some (ELit 4); Some (ELit 56); Some (ELit 5); Some (ELit 11);
   Some (ELit 7); Some (ELit 0); Some (ELit 8); Some (ELit 0); Some (ELit 9); None;
   Some (ELit 11); Some (EVar V_UID); Some (ELit 12); Some (EVar V_UID); Some (ELit 13); Some (EVar V_GID); Some (ELit 14); Some (EVar V_GID);
   Some (ELit 23); Some (ELit 0); Some (ELit 25); Some (KE_RNDP r); Some (ELit 31); None]
  ++ (if Z.eqb r 1 then [Some (ELit 27); Some (ELit 28); Some (ELit 28); Some (ELit 32)] else [])
  ++ [Some (ELit 0); Some (ELit 0)].
Fixpoint aux_chk_from (k : list kentry) (j : nat) (l : list (option expr)) : bool :=
  match l with
  | [] => true
  | o :: l' => ((match o with Some e => opt_eqb (kfind_word k KE_AUX (24 + 8 * Z.of_nat j) 8) e | None => true end)
                && aux_chk_from k (Datatypes.S j) l')%bool
  end.
Definition aux_chk (r : Z) (cs : acs) : bool := aux_chk_from (kn cs) 0 (AUXE r).
Lemma aux_chk_from_nth : forall k l j0 j e, aux_chk_from k j0 l = true -> nth j l None = Some e ->
  kfind_word k KE_AUX (24 + 8 * Z.of_nat (j0 + j)%nat) 8 = Some e.
Proof.
  intros k l. induction l as [|o l IH]; intros j0 j e Hc Hn.
  - destruct j; discriminate.
  - cbn [aux_chk_from] in Hc. apply andb_prop in Hc as [H1 H2]. destruct j as [|j].
    + cbn [nth] in Hn. subst o. rewrite Nat.add_0_r.
      destruct (kfind_word k KE_AUX (24 + 8 * Z.of_nat j0) 8) as [v|]; [|discriminate].
      apply expr_eqb_eq in H1. subst. reflexivity.
    + cbn [nth] in Hn. replace (j0 + Datatypes.S j)%nat with (Datatypes.S j0 + j)%nat by lia. exact (IH (Datatypes.S j0) j e H2 Hn).
Qed.
Lemma aph0_addr : Z.of_N (ph_addr APH0) = 0x10040.  Proof. vm_compute. reflexivity. Qed.
Lemma aph0_ent : Z.of_N (ph_ent APH0) = 56.        Proof. vm_compute. reflexivity. Qed.
Lemma aph0_num : Z.of_N (ph_num APH0) = 11.        Proof. vm_compute. reflexivity. Qed.

Definition XC9K : list (Z * nat * Z) :=
  [(6905072, 4%nat, 0); (6905107, 1%nat, 0); (6904544, 8%nat, 6904552); (6904536, 4%nat, 1); (6904560, 8%nat, 1156008); (6904816, 8%nat, 622312); (6904532, 4%nat, 0); (6904552, 8%nat, 0);
   (6906504, 8%nat, 0); (6904528, 1%nat, 0); (6905328, 4%nat, 0)].
Definition xc_chk (cs : acs) : bool := forallb (chk_lit1 (kn cs)) XC9K.

Lemma all_andb_split : forall a b, (a && b)%bool = true -> a = true /\ b = true.
Proof. intros a b H. apply andb_prop in H. exact H. Qed.

Section Entry.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Variable mbase : word.
  Variable stdin : InputStream.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable abrt : bool.
  Variable ur : InputStream.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdf : bool.
  Variable apc : N.
  Variable r : Z.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  Hypothesis Hvl : valid_launch
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).

  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation argc := (Z.of_nat (length argv)).
  #[local] Notation envc := (Z.of_nat (length envp)).
  #[local] Notation INP := (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation entryw := (Z_to_bv 64 (Z.of_N apc)).
  #[local] Notation rseq := (kb_rseq (in_kernel INP)).
  #[local] Notation top := (ed_top rdraw).
  #[local] Notation utop := (bv_unsigned top).
  #[local] Notation CHEAD := (Z.of_nat (block_head_size rseq argv envp)).
  #[local] Notation LSTR := (Z.of_nat (launch_string_bytes argv envp execfn)).
  #[local] Notation PADW := (Z.of_nat (block_pad_len rseq sp top argv envp execfn)).
  #[local] Notation STR0 := (usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn)).
  #[local] Notation GAPW := (Z.of_nat (block_items argv envp mod 2)).

  Hypothesis HRZ : r = rseq_z rseq.

  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  Let AH := argH0_high sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva.

  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.

  Variable cs : acs.
  Hypothesis CHK0 : as0_chk cs = true.
  Hypothesis CHKD : drv_chk r cs = true.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
                   + (Z.of_nat (length (segments_reserved ASEGS0) + n_resx ASAN0 + length (a_maps cs)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis HC : CSOK E cs R FULL model.

  #[local] Notation A0 := (as0_A0 EXTRA cs E).
  #[local] Notation Hx := (ahid A0 model).
  #[local] Notation MV := (mrestrict Hx FULL).
  #[local] Notation HIDK := (hid ASAN0 argH E cs model).

  Lemma drv_chk_parts :
    pc cs = 0xa8488
    /\ (forall rg e, In (rg, e) DRV_REGS -> sr_get (s_regs (a_ss cs)) (Z_to_bv 5 rg) = e)
    /\ lin_nowrapR (kn cs) e_sp0 = true /\ lin_nowrapR (kn cs) (KE_SPK (-48)) = true /\ lin_nowrapR (kn cs) (KE_SPK 8) = true
    /\ lin_nowrapR (kn cs) KE_ENVP = true /\ lin_nowrapR (kn cs) (e_str0 r) = true /\ lin_nowrapR (kn cs) (e_str1 r) = true
    /\ kfind_word (kn cs) e_sp0 0 8 = Some (EVar V_ARGC) /\ kfind_word (kn cs) e_sp0 8 8 = Some (e_str0 r)
    /\ kfind_word (kn cs) e_sp0 16 8 = Some (e_argv1w r)
    /\ kfind_wr (kn cs) e_sp0 (-stack_window_depth) = Some (ELit stack_window_depth)
    /\ (exists v, kfind_word (kn cs) (ELit 0) 0x695ac0 8 = Some v /\ kfind_word (kn cs) (ELit 0) 0x675a70 8 = Some v)
    /\ (forall lo hi, In (lo, hi) DRV_IMG -> img_cover (kn cs) lo hi = true)
    /\ a_fd cs = FdStd.
  Proof.
    pose proof CHKD as H. unfold drv_chk in H.
    apply andb_prop in H as [H Cfd]. apply andb_prop in H as [H Cimg]. apply andb_prop in H as [H Cg]. apply andb_prop in H as [H Cwr]. apply andb_prop in H as [H Cp1].
    apply andb_prop in H as [H Cp0]. apply andb_prop in H as [H Cac]. apply andb_prop in H as [H L6]. apply andb_prop in H as [H L5].
    apply andb_prop in H as [H L4]. apply andb_prop in H as [H L3]. apply andb_prop in H as [H L2]. apply andb_prop in H as [H L1].
    apply andb_prop in H as [H Creg].
    assert (OE : forall o e, opt_eqb o e = true -> o = Some e).
    { intros o e Ho. destruct o as [v|]; [|discriminate]. apply expr_eqb_eq in Ho. subst. reflexivity. }
    split; [apply Z.eqb_eq; exact H|].
    split; [intros rg e Hin; pose proof (proj1 (forallb_forall _ _) Creg (rg, e) Hin) as Hb; cbn [fst snd] in Hb; apply expr_eqb_eq; exact Hb|].
    do 6 (split; [assumption|]).
    do 4 (split; [apply OE; assumption|]).
    split.
    - destruct (kfind_word (kn cs) (ELit 0) 0x695ac0 8) as [v|]; [|discriminate]. exists v. split; [reflexivity | apply OE; assumption].
    - split; [intros lo hi Hin; exact (proj1 (forallb_forall _ _) Cimg (lo, hi) Hin)|].
      destruct (a_fd cs); first [reflexivity | discriminate].
  Qed.

  Ltac LINEQ e Hn H :=
    pose proof (hb_lin ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model e HC Hn) as H;
    unfold LZ in H;
    match type of H with context [lin_of ?x] => let l := eval vm_compute in (lin_of x) in change (lin_of x) with l in H end;
    cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE] in H; cbn [edenot] in H;
    repeat match type of H with context [bv_unsigned (ev E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) in H end;
    rewrite ?Z.add_0_r in H.

  Lemma ent_vals : VZ E 1 = argc /\ VZ E 2 = envc /\ VZ E 3 = Z.of_nat (length (nth 0 argv []))
                   /\ 32768 * VZ E 0 + 16 * VZ E 6 + 4096 * VZ E 10 = usp.
  Proof.
    destruct (hbi_vals ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp uid hw fs stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc
                Hsp Hva Hve Hfit Hlau E cs R FULL model HC)
      as (_ & _ & U1 & U2 & U3 & _).
    pose proof (hbi_sp0 ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp uid hw fs stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc
                  Hsp Hva Hve Hfit Hlau E cs R FULL model HC) as U0.
    auto.
  Qed.

  Lemma ent_w : VZ E 4 = PADW.
  Proof.
    destruct (hbi_vals ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp uid hw fs stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc
                Hsp Hva Hve Hfit Hlau E cs R FULL model HC)
      as (_ & _ & _ & _ & _ & _ & U4 & _).
    unfold HandoffBridgeK.Wsb in U4. exact U4.
  Qed.

  Lemma ent_g : VZ E 11 = GAPW.
  Proof.
    pose proof (hbi_E0 ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp uid hw fs stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc
                  E cs R FULL model HC 11%nat ltac:(unfold NX0; lia)) as HE.
    pose proof (AsanInitK.uE0_G sp rdraw brk0 argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc) as UG.
    unfold VZ. rewrite HE. unfold APSK.uE in UG. cbn [edenot] in UG. change V_G with 11%nat in UG. exact UG.
  Qed.

  Lemma sp0_val : uE E e_sp0 = usp.
  Proof.
    destruct drv_chk_parts as (_ & _ & L1 & _). destruct ent_vals as (_ & _ & _ & U0).
    unfold uE. remember (bv_unsigned (edenot E e_sp0)) as s0 eqn:Es. LINEQ e_sp0 L1 H. rewrite <- Es in H. lia.
  Qed.

  Lemma sp_rng : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0.
  Proof. destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in *. lia. Qed.


  #[local] Notation SIMGx := (entry_stack_image INP mbase APH0 entryw sp rdraw).
  #[local] Notation LBx := (Z.of_nat (length SIMGx)).

  Lemma chead_eq : CHEAD = 8 * argc + 8 * envc + 8 * GAPW + 472 + 32 * rseq_z rseq.
  Proof.
    unfold block_head_size, block_items, auxv_size, auxv_count, rseq_z.
    destruct rseq; cbn [Nat.add]; rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul; cbn [Z.of_nat]; lia.
  Qed.

  Lemma gap_rng : 0 <= GAPW <= 1.
  Proof. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. Qed.

  Lemma simg_len : LBx = utop - usp.
  Proof. exact (length_entry_stack_image_launch Sv48 INP mbase APH0 entryw sp brk0 rdraw Hlau). Qed.

  Lemma simg_sum : LBx = Z.of_nat (cat_string_off rseq sp top argv envp execfn) + LSTR + 8.
  Proof.
    rewrite entry_stack_image_block, length_build_stack_bytes.
    unfold cat_string_off.
    change (la_rseq (launch_auxv INP sp mbase)) with (kb_rseq (in_kernel INP)).
    (* the block lemma speaks of [in_argv INP] etc.; name them as this Section does so [lia] sees one atom each *)
    change (in_argv INP) with argv. change (in_envp INP) with envp. change (in_execfn INP) with execfn. lia.
  Qed.

  Lemma str0_top : STR0 + LSTR + 8 = utop.
  Proof. pose proof simg_len. pose proof simg_sum. lia. Qed.

  Lemma str0_ge : usp <= STR0.
  Proof. pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp top argv envp execfn)). lia. Qed.

  Lemma utop_hi : utop <= 2 ^ 47.
  Proof.
    pose proof (entry_page_top_within_window Sv48 INP mbase sp brk0 rdraw Hlau) as H.
    unfold entry_page_top, va_stack_top in H. exact H.
  Qed.

  Lemma utop_pg : utop mod 4096 = 0.
  Proof. destruct Hlau as ((Hm & _ & _) & _ & _). unfold page_size in Hm. exact Hm. Qed.

  Lemma simg_nw : usp + LBx < 2 ^ 64.
  Proof. exact (entry_stack_image_no_wrap Sv48 INP mbase APH0 entryw sp brk0 rdraw Hlau). Qed.

  Lemma simg_top : usp + LBx <= 2 ^ 47 /\ LBx = utop - usp /\ (usp + LBx) mod 4096 = 0.
  Proof.
    pose proof simg_len. pose proof utop_hi. pose proof utop_pg.
    split; [lia|]. split; [lia|]. replace (usp + LBx) with utop by lia. assumption.
  Qed.

  Lemma ent_binv : BInv ASEGS0 (vm_maps (m_vmmaps model)) (vm_reserved (m_vmmaps model)) (vm_noaccess (m_vmmaps model))
                        (uE E e_sp0 - 8388608) (as0_BASE EXTRA cs) BUDGET [] A0 FULL model.
  Proof.
    exact (as0_binv_main sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc
             Hsp Hva BUDGET LENMAX KMAX BUD EXTRA EXTRA_wf cs CHK0 GAP E R FULL model HC).
  Qed.

  Lemma hx_le : forall a : word, Hx a = true -> HIDK a = true.
  Proof.
    intros a Ha. destruct (HIDK a) eqn:Hh; [reflexivity|]. exfalso.
    unfold ahid, mkH in Ha. apply andb_prop in Ha as [Hl Hn]. apply negb_true_iff in Hn.
    pose proof (lazy_cover_cs ASEGS0 ASAN0 AsanInitK.LIMIT (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None)
                  asan0_hull_ok SINV argH fs 0%nat E cs R FULL model HC a Hl Hh) as Hc.
    unfold as0_A0, A0_of in Hn. rewrite (page_allowedb_app_l _ _ _ Hc) in Hn. discriminate.
  Qed.

  Lemma avoid_x : forall a n, range_avoids HIDK a n -> range_avoids Hx a n.
  Proof. intros a n Hr k Hk. destruct (Hx (woff a k)) eqn:Hh; [|reflexivity]. pose proof (hx_le _ Hh) as Hc. rewrite (Hr k Hk) in Hc. discriminate. Qed.

  Lemma ent_lz : H_off_segments ASEGS0 Hx /\ lazy_cover Hx (m_vm_lazy model) A0 /\ A_wf A0 /\ MInv A0 model /\ m_halted model = None.
  Proof.
    pose proof ent_binv as B.
    split; [intros a Ha; unfold ahid, mkH in Ha; apply andb_prop in Ha as [Hl _]; exact (proj2 (bi_lazy_in _ _ _ _ _ _ _ _ _ _ _ B a Hl))|].
    split; [unfold ahid; apply lazy_cover_mkH; intros rg Hr; exact Hr|].
    split; [exact (bi_awf _ _ _ _ _ _ _ _ _ _ _ B)|].
    split; [exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B) | exact (bi_halt _ _ _ _ _ _ _ _ _ _ _ B)].
  Qed.

  Lemma ent_model : m_fds model = fds_std /\ m_fs model = fs.
  Proof.
    split; [|exact (hb_fs ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC)].
    apply (hb_fds_std ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC).
    exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 drv_chk_parts)))))))))))))).
  Qed.

  Lemma ent_rdr : m_channel_reader model = true.
  Proof. exact (APSK.co_rdr ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC). Qed.

  Variables a0s path : list byte.
  Hypothesis Hargv : argv = [a0s; path].
  #[local] Notation L0 := (Z.of_nat (length a0s)).

  Lemma ent_vals2 : VZ E 1 = 2 /\ VZ E 2 = envc /\ VZ E 3 = L0 /\ 32768 * VZ E 0 + 16 * VZ E 6 + 4096 * VZ E 10 = usp.
  Proof. destruct ent_vals as (U1 & U2 & U3 & U0). rewrite Hargv in U1, U3. cbn [length nth] in U1, U3. auto. Qed.

  Lemma word_of_u : forall (w : word) z, bv_unsigned w = z -> w = Z_to_bv 64 z.
  Proof. intros w z <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Lemma val_spk48 : edenot E (KE_SPK (-48)) = Z_to_bv 64 (usp - 48).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & L2 & _). destruct ent_vals2 as (_ & _ & _ & U0). pose proof sp_rng.
    apply word_of_u. remember (bv_unsigned (edenot E (KE_SPK (-48)))) as x eqn:Ex. LINEQ (KE_SPK (-48)) L2 H0. rewrite <- Ex in H0. lia.
  Qed.
  Lemma val_spk8 : edenot E (KE_SPK 8) = Z_to_bv 64 (usp + 8).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & L3 & _). destruct ent_vals2 as (_ & _ & _ & U0).
    apply word_of_u. remember (bv_unsigned (edenot E (KE_SPK 8))) as x eqn:Ex. LINEQ (KE_SPK 8) L3 H0. rewrite <- Ex in H0. lia.
  Qed.
  Lemma val_envp : edenot E KE_ENVP = Z_to_bv 64 (usp + 32).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & L4 & _). destruct ent_vals2 as (U1 & _ & _ & U0).
    apply word_of_u. remember (bv_unsigned (edenot E KE_ENVP)) as x eqn:Ex. LINEQ KE_ENVP L4 H0. rewrite <- Ex in H0. lia.
  Qed.

  Lemma val_str0 : edenot E (e_str0 r) = Z_to_bv 64 STR0.
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & L5 & _).
    destruct ent_vals2 as (U1 & U2 & _ & U0). pose proof ent_w as UW. pose proof ent_g as UG.
    pose proof chead_eq as CH. pose proof gap_rng. pose proof sp_rng.
    pose proof (Nat2Z.is_nonneg (block_pad_len rseq sp top argv envp execfn)).
    assert (CS : Z.of_nat (cat_string_off rseq sp top argv envp execfn) = CHEAD + PADW)
      by (unfold cat_string_off; lia).
    assert (R01 : r = 0 \/ r = 1) by (rewrite HRZ; unfold rseq_z; destruct (kb_rseq (in_kernel INP)); auto).
    pose proof HRZ as HZ. apply word_of_u.
    destruct R01 as [Er|Er]; rewrite Er in L5, HZ |- *;
      match goal with |- bv_unsigned (edenot E ?e) = _ =>
        remember (bv_unsigned (edenot E e)) as x eqn:Ex; LINEQ e L5 HL5; rewrite <- Ex in HL5 end;
      rewrite Hargv in *; cbn [length] in *; change (Z.of_nat 2) with 2 in *; lia.
  Qed.

  Lemma val_str1 : edenot E (e_str1 r) = Z_to_bv 64 (STR0 + L0 + 1).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & L6 & _).
    destruct ent_vals2 as (U1 & U2 & U3 & U0). pose proof ent_w as UW. pose proof ent_g as UG.
    pose proof chead_eq as CH. pose proof gap_rng. pose proof sp_rng.
    pose proof (Nat2Z.is_nonneg (block_pad_len rseq sp top argv envp execfn)).
    assert (CS : Z.of_nat (cat_string_off rseq sp top argv envp execfn) = CHEAD + PADW)
      by (unfold cat_string_off; lia).
    assert (R01 : r = 0 \/ r = 1) by (rewrite HRZ; unfold rseq_z; destruct (kb_rseq (in_kernel INP)); auto).
    pose proof HRZ as HZ. apply word_of_u.
    destruct R01 as [Er|Er]; rewrite Er in L6, HZ |- *;
      match goal with |- bv_unsigned (edenot E ?e) = _ =>
        remember (bv_unsigned (edenot E e)) as x eqn:Ex; LINEQ e L6 HL6; rewrite <- Ex in HL6 end;
      rewrite Hargv in *; cbn [length] in *; change (Z.of_nat 2) with 2 in *; lia.
  Qed.

  Lemma val_argc : edenot E (EVar V_ARGC) = Z_to_bv 64 2.
  Proof. destruct ent_vals2 as (U1 & _). apply word_of_u. exact U1. Qed.

  Lemma val_argv1w : edenot E (e_argv1w r) = Z_to_bv 64 (STR0 + L0 + 1).
  Proof.
    unfold e_argv1w. cbn [edenot]. fold (edenot E (e_str1 r)). rewrite val_str1. apply word_of_u.
    rewrite u_mul64, u_sltu64. destruct ent_vals2 as (U1 & _).
    (* [V_ARGC] is slot 1; read the guard's operand off [ent_vals2] *)
    unfold VZ in U1. unfold V_ARGC. cbn [edenot] in *. rewrite U1.
    rewrite (u64_lit 1) by lia. change (1 <? 2) with true. cbv iota.
    pose proof sp_rng. pose proof str0_ge. pose proof str0_top. pose proof utop_hi.
    pose proof (Zle_0_nat (length a0s)).
    assert (Hb : 0 <= STR0 + L0 + 1 < 2 ^ 64).
    { (* [L0 + 1 <= LSTR] as [AsanInitK.s0_in_strings] proves it, at this section's [argv] *)
      assert (SI : L0 + 1 <= LSTR).
      { rewrite Hargv. unfold launch_string_bytes, flatten_strings. cbn [flat_map].
        rewrite !length_app. cbn [length]. lia. }
      lia. }
    rewrite u64_lit by exact Hb. rewrite Z.mul_1_l. apply Z.mod_small. exact Hb.
  Qed.

  Lemma ent_reg : forall rg e, In (rg, e) DRV_REGS -> getr R (Z_to_bv 5 rg) = edenot E e.
  Proof.
    intros rg e Hin. destruct drv_chk_parts as (_ & HRg & _). rewrite <- (HRg rg e Hin).
    exact (hb_reg ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC).
  Qed.

  Definition DRV_REGV : list (Z * Z) :=
    [(1, 0x119c34); (2, usp - 48); (3, 0x10800); (4, 0x675a80); (8, usp + 8); (9, 2); (10, 2); (11, usp + 8);
     (12, usp + 32); (18, 0xa8488); (19, usp + 32); (20, 0); (21, 0); (22, 0); (23, 0); (24, 0); (25, 0); (26, 0); (27, 0)].

  Theorem ent_regs : forall rg v, In (rg, v) DRV_REGV -> getr R (Z_to_bv 5 rg) = Z_to_bv 64 v.
  Proof.
    intros rg v Hin. unfold DRV_REGV in Hin.
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 1 (ELit 0x119c34)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 2 (KE_SPK (-48))) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_spk48|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 3 (ELit 0x10800)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 4 (ELit 0x675a80)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 8 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_spk8|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 9 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_argc|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 10 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_argc|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 11 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_spk8|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 12 (KE_ENVP)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_envp|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 18 (ELit 0xa8488)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 19 (KE_ENVP)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_envp|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 20 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 21 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 22 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 23 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 24 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 25 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 26 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 27 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin.
  Qed.

  Lemma adr_sp : forall off n, flat E (SA e_sp0 off) n -> adenot E (SA e_sp0 off) = Z_to_bv 64 (usp + off).
  Proof. intros off n Hf. rewrite (hb_adenot E _ _ Hf), hb_estart. fold (uE E e_sp0). rewrite sp0_val. reflexivity. Qed.

  Lemma ent_stkword : forall off v, kfind_word (kn cs) e_sp0 off 8 = Some v ->
    rdn ASEGS0 MV (Z_to_bv 64 (usp + off)) 8 = Some (word_to_le_bytes 8 (edenot E v)).
  Proof.
    intros off v Hk.
    destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model e_sp0 off 8 v HC Hk)
      as (_ & Hf & Hr & Hav).
    rewrite (adr_sp off _ Hf) in Hr, Hav. rewrite (rdn_mrestrict_eq ASEGS0 Hx 8 FULL _ (avoid_x _ _ Hav)). exact Hr.
  Qed.

  Theorem ent_stack_words :
    rdn ASEGS0 MV (Z_to_bv 64 usp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 2))
    /\ rdn ASEGS0 MV (Z_to_bv 64 (usp + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 STR0))
    /\ rdn ASEGS0 MV (Z_to_bv 64 (usp + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (STR0 + L0 + 1))).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & K0 & K8 & K16 & _).
    pose proof (ent_stkword 0 _ K0) as H0. pose proof (ent_stkword 8 _ K8) as H8. pose proof (ent_stkword 16 _ K16) as H16.
    rewrite Z.add_0_r, val_argc in H0. rewrite val_str0 in H8. rewrite val_argv1w in H16. auto.
  Qed.

  Theorem ent_window : forall d (m : nat), 0 <= d -> d + Z.of_nat m <= stack_window_depth ->
    store_ok ASEGS0 MV (Z_to_bv 64 (usp - stack_window_depth + d)) m = true.
  Proof.
    intros d m Hd Hm. destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KW & _).
    destruct (hb_wr_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model e_sp0 (-stack_window_depth) _ HC KW)
      as (Hf & HW).
    assert (EL : elenZ E (ELit stack_window_depth) = stack_window_depth)
      by (unfold elenZ; cbn [edenot]; apply u64_lit; rewrite stack_window_depth_val; lia).
    destruct (HW d m Hd ltac:(rewrite EL; exact Hm)) as (Hs & Hav).
    rewrite hb_estart in Hs, Hav. fold (uE E e_sp0) in Hs, Hav. rewrite sp0_val in Hs, Hav.
    replace (usp + - stack_window_depth + d) with (usp - stack_window_depth + d) in Hs, Hav by ring.
    rewrite (store_ok_mrestrict_eq ASEGS0 Hx m FULL _ (avoid_x _ _ Hav)). exact Hs.
  Qed.

  Theorem ent_guard : exists can : word,
    rdn ASEGS0 MV (Z_to_bv 64 0x695ac0) 8 = Some (word_to_le_bytes 8 can) /\ rdn ASEGS0 MV (Z_to_bv 64 0x675a70) 8 = Some (word_to_le_bytes 8 can).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (v & G1 & G2) & _).
    exists (edenot E v).
    assert (HW : forall a, kfind_word (kn cs) (ELit 0) a 8 = Some v -> 0 <= a < 2 ^ 63 ->
                 rdn ASEGS0 MV (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (edenot E v))).
    { intros a Hk Ha.
      destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model (ELit 0) a 8 v HC Hk)
        as (_ & Hf & Hr & Hav).
      rewrite (hb_adenot E _ _ Hf), hb_estart in Hr, Hav. cbn [edenot] in Hr, Hav. rewrite (u64_lit 0) in Hr, Hav by lia. rewrite Z.add_0_l in Hr, Hav.
      rewrite (rdn_mrestrict_eq ASEGS0 Hx 8 FULL _ (avoid_x _ _ Hav)). exact Hr. }
    split; apply HW; first [assumption | lia].
  Qed.

  Theorem ent_img : forall lo hi i, In (lo, hi) DRV_IMG -> lo <= i < hi -> MV (Z_to_bv 64 i) = None.
  Proof.
    intros lo hi i Hin Hi.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HI & _).
    pose proof (HI lo hi Hin) as Hc. unfold img_cover in Hc. apply existsb_exists in Hc as (K & HK & Hb).
    destruct K as [| | | l h | | | | | |]; try discriminate. apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
    assert (Hh : in_hull ASAN0 i = true).
    { unfold DRV_IMG in Hin. destruct Hin as [Hin|[Hin|[Hin|[Hin|[]]]]]; injection Hin as <- <-; unfold in_hull; cbn [img_lo img_hi ASAN0];
        apply andb_true_intro; split; first [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    pose proof (hb_img ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_hull_ok AH E cs R FULL model l h HC HK i ltac:(lia) Hh) as Hn.
    unfold mrestrict. destruct (Hx (Z_to_bv 64 i)); [reflexivity | exact Hn].
  Qed.

  Lemma vis_high : forall x : word, usp - 8388608 <= bv_unsigned x -> Hx x = false.
  Proof.
    intros x Hxx. destruct (Hx x) eqn:Hh; [exfalso | reflexivity].
    unfold ahid, mkH in Hh. apply andb_prop in Hh as [Hl _].
    destruct (bi_lazy_in _ _ _ _ _ _ _ _ _ _ _ ent_binv x Hl) as [Hc _].
    unfold BackingAlgebra.covered in Hc. apply existsb_exists in Hc as (q & Hq & Hin).
    unfold BackingAlgebra.in_iv, BackingAlgebra.in_rng, BackingAlgebra.B, BackingAlgebra.S in Hin. apply andb_prop in Hin as [I1 I2].
    apply Z.leb_le in I1. apply Z.ltb_lt in I2.
    destruct (hl_maps_pos ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model q HC Hq) as [_ Hle].
    rewrite sp0_val in Hle. lia.
  Qed.


  Theorem ent_strblock : forall x : word,
    STR0 <= bv_unsigned x < utop -> MV x = wrap_mem INP mbase APH0 entryw sp rdraw x.
  Proof.
    intros x Hxr. pose proof sp_rng as SR. pose proof str0_ge as SG.
    unfold mrestrict. rewrite (vis_high x ltac:(lia)).
    apply (hbi_argblock ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp uid hw fs stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc
             E cs R FULL model HC).
    rewrite hbi_argH. rewrite sp0_val.
    apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. right.
    apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  Qed.

  Theorem ent_str : forall k, (k < 2)%nat ->
    rdn ASEGS0 MV (cat_argv_ptr top argv envp execfn k) (length (nth k argv []) + 1) = Some (nth k argv [] ++ [Z_to_bv 8 0])
    /\ bv_unsigned (cat_argv_ptr top argv envp execfn k) = STR0 + Z.of_nat (total_arg_bytes_nat (firstn k argv)).
  Proof.
    intros k Hk. pose proof sp_rng as SR. pose proof str0_ge. pose proof str0_top. pose proof utop_hi. pose proof simg_nw.
    assert (Hk' : (k < length argv)%nat) by (rewrite Hargv; cbn [length]; lia).
    pose proof (bsb_len_lower INP mbase APH0 entryw sp rdraw) as Hlow.
    change (in_argv INP) with argv in Hlow. change (in_envp INP) with envp in Hlow. change (in_execfn INP) with execfn in Hlow.
    pose proof simg_len as SL.
    pose proof (total_arg_bytes_firstn_le k argv) as Hmono.
    pose proof (total_arg_bytes_firstn_within argv k Hk') as Hw.
    pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp top argv envp execfn)) as Z0.
    assert (PTR : cat_argv_ptr top argv envp execfn k
                  = (sp + nat_to_word (cat_string_off rseq sp top argv envp execfn + total_arg_bytes_nat (firstn k argv)))%bv).
    { pose proof (cat_string_base_offset Sv48 INP mbase sp brk0 rdraw Hlau) as HB.
              change (in_argv INP) with argv in HB. change (in_envp INP) with envp in HB. change (in_execfn INP) with execfn in HB.
              rewrite (cat_argv_ptr_offset top argv envp execfn k Hk'), HB.
      rewrite nat_to_word_add_merge. reflexivity. }
    assert (UPTR : bv_unsigned (cat_argv_ptr top argv envp execfn k)
                   = STR0 + Z.of_nat (total_arg_bytes_nat (firstn k argv))).
    { rewrite PTR, word_add_nat_Z2bv. rewrite u64_lit by lia. lia. }
    split; [|exact UPTR].
    pose proof (read_argv_cstr_k Sv48 ASEGS0 INP mbase APH0 entryw sp brk0 rdraw k Hlau Hk') as RA.
    change (in_argv INP) with argv in RA. change (in_envp INP) with envp in RA. change (in_execfn INP) with execfn in RA.
    rewrite <- RA.
    rewrite <- (rdn_wmem_stack ASEGS0 INP mbase APH0 entryw sp rdraw) by lia.
    apply rdn_ext; [lia|]. intros x Hxr. unfold wmem. apply ent_strblock.
    lia.
  Qed.

  Hypothesis CHKS : stk_chk r cs = true.

  Lemma stk_chk_parts :
    (forall off, In off (AUX_OFFS r) -> exists v, kfind_word (kn cs) KE_AUX off 8 = Some v)
    /\ lin_nowrapR (kn cs) KE_AUX = true /\ lin_nowrapR (kn cs) (e_atrandom r) = true
    /\ exists i, kfind_blob16 (kn cs) (KE_RND r) (KE_RNDOFF r) = Some i.
  Proof.
    pose proof CHKS as H. unfold stk_chk in H. apply andb_prop in H as [H _]. unfold stk_core in H.
    apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
    split.
    { intros off Hin. pose proof (proj1 (forallb_forall _ _) C1 off Hin) as Hb. cbv beta in Hb.
      destruct (kfind_word (kn cs) KE_AUX off 8) as [v|]; [exists v; reflexivity | discriminate]. }
    split; [exact C2|]. split; [exact C3|].
    destruct (kfind_blob16 (kn cs) (KE_RND r) (KE_RNDOFF r)) as [i|]; [exists i; reflexivity | discriminate].
  Qed.

  Lemma stk_cover_parts :
    lin_nowrapR (kn cs) (KE_RND r) = true /\ lin_nowrapR (kn cs) (escale 8 (EVar V_G)) = true
    /\ In (KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (AUXSZ r))) (kn cs)
    /\ In (KUnk (SA (fst e_auxb) (snd e_auxb + AUXSZ r)) (escale 8 (EVar V_G))) (kn cs)
    /\ In (KUnk (SA (KE_RND r) (KE_RNDOFF r + 16)) (EVar V_W)) (kn cs).
  Proof.
    pose proof CHKS as H. unfold stk_chk in H. apply andb_prop in H as [_ H]. unfold stk_cover in H.
    apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3].
    apply andb_prop in H as [C1 C2].
    split; [exact C1|]. split; [exact C2|].
    split; [exact (hb_knb_In _ _ C3)|]. split; [exact (hb_knb_In _ _ C4) | exact (hb_knb_In _ _ C5)].
  Qed.

  Theorem ent_str_hi : forall k, (k < 2)%nat ->
    bv_unsigned (cat_argv_ptr top argv envp execfn k) + Z.of_nat (length (nth k argv [])) + 1 + 9 <= 2 ^ 47.
  Proof.
    intros k Hk. pose proof sp_rng as SR. pose proof str0_top. pose proof str0_ge. pose proof utop_hi.
    assert (Hk' : (k < length argv)%nat) by (rewrite Hargv; cbn [length]; lia).
    destruct (ent_str k Hk) as (_ & Hu).
    pose proof (total_arg_bytes_firstn_le (Datatypes.S k) argv) as Hmono.
    pose proof (total_arg_bytes_firstn_S argv k Hk') as Hstep.
    destruct Hvl as [Hfn _].
    change (in_execfn INP) with execfn in Hfn.
    assert (Hfnlen : 1 <= Z.of_nat (length execfn)).
    { destruct Hfn as [[Hp _]|[(ds & Hds & _)|(ds & rest & Hds & _)]];
        [lia | rewrite Hds, length_app; cbn [length dev_fd_prefix]; lia | rewrite Hds, !length_app; cbn [length dev_fd_prefix]; lia]. }
    assert (HL : Z.of_nat (total_arg_bytes_nat argv) + Z.of_nat (length execfn) + 1 <= LSTR).
    { unfold launch_string_bytes. rewrite (length_flatten_strings argv).
      pose proof (Zle_0_nat (length (flatten_strings envp))). lia. }
    rewrite Hu.
    lia.
  Qed.

  Lemma argH_defined : forall x : word, usp <= bv_unsigned x < usp + LBx -> argH E x = true -> FULL x <> None.
  Proof.
    intros x Hx Ha.
    rewrite (hbi_argblock ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp uid hw fs stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc
               E cs R FULL model HC x Ha).
    rewrite wrap_above_sp by lia. unfold stack_to_mem.
    replace (usp <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
    replace (bv_unsigned x - usp <? LBx) with true by (symmetry; apply Z.ltb_lt; lia).
    apply nth_error_Some. lia.
  Qed.

  Lemma mr_defined : forall (x : word) b, Mr ASAN0 argH E cs model FULL x = Some b -> FULL x <> None.
  Proof. intros x b H. rewrite (hb_mr_some ASAN0 argH E cs model FULL x b H). discriminate. Qed.

  Theorem ent_stack_defined : forall i, 0 <= i < LBx -> FULL (Z_to_bv 64 (usp + i)) <> None.
  Proof.
    intros i Hi. pose proof sp_rng as SR. pose proof simg_len as SL. pose proof utop_hi. pose proof str0_ge. pose proof str0_top.
    destruct drv_chk_parts as (_ & _ & L1 & _ & _ & _ & _ & _ & K0 & K8 & K16 & _).
    assert (AC : argc = 2) by (rewrite Hargv; reflexivity).
    assert (UX : bv_unsigned (Z_to_bv 64 (usp + i)) = usp + i) by (apply u_small; lia).

    assert (KW : forall b off v d, kfind_word (kn cs) b off 8 = Some v -> lin_nowrapR (kn cs) b = true ->
                 (flat E (SA b off) 8 -> estart E (SA b off) = usp + d) -> d <= i < d + 8 -> FULL (Z_to_bv 64 (usp + i)) <> None).
    { intros b off v d Hk Hl Hst Hd.
      destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model b off 8 v HC Hk)
        as (_ & Hf & Hr & _).
      rewrite (hb_adenot E _ _ Hf), (Hst Hf) in Hr.
      apply (rdn_bytes_some ASEGS0 ASAN0 asan0_in_hull FULL _ 8 _ Hr).
      - rewrite UX, u_small by lia. change (Z.of_nat 8) with 8. lia.
      - rewrite UX. unfold in_hull. cbn [img_lo img_hi ASAN0]. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
    destruct (Z_lt_le_dec i 24) as [C1|C1].
    {
      assert (ST : forall off, flat E (SA e_sp0 off) 8 -> estart E (SA e_sp0 off) = usp + off)
        by (intros off _; rewrite hb_estart; fold (uE E e_sp0); rewrite sp0_val; reflexivity).
      destruct (Z_lt_le_dec i 8); [apply (KW e_sp0 0 _ 0 K0 L1 (ST 0)); lia|].
      destruct (Z_lt_le_dec i 16); [apply (KW e_sp0 8 _ 8 K8 L1 (ST 8)); lia | apply (KW e_sp0 16 _ 16 K16 L1 (ST 16)); lia]. }
    destruct (Z_lt_le_dec i (8 * argc + 8 * envc + 24)) as [C2|C2].
    {
      apply argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, sp0_val, UX.
      apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. left.
      apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    destruct (Z_lt_le_dec i (Z.of_nat (cat_string_off rseq sp top argv envp execfn))) as [C3|C3].
    {
      destruct stk_chk_parts as (_ & LA & _ & (bi & CB)).
      destruct stk_cover_parts as (LRB & LG & KU1 & KU2 & KU3).
      destruct ent_vals2 as (U1 & U2 & _ & U0). pose proof ent_w as UW. pose proof ent_g as UG.
      pose proof chead_eq as CH. pose proof gap_rng as GR.
      pose proof (Nat2Z.is_nonneg (block_pad_len rseq sp top argv envp execfn)).
      assert (CS : Z.of_nat (cat_string_off rseq sp top argv envp execfn) = CHEAD + PADW)
        by (unfold cat_string_off; lia).
      assert (UNK : forall b k n s L, In (KUnk (SA b k) n) (kn cs) -> uE E b + k = usp + s ->
                      elenZ E n = L -> s <= i < s + L -> FULL (Z_to_bv 64 (usp + i)) <> None).
      { intros b k n s L Hin Hs HL Hi'.
        destruct (hb_unk ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ _ HC Hin) as (_ & Hd).
        specialize (Hd (i - s) ltac:(lia)). rewrite hb_estart in Hd. unfold uE in Hs.
        replace (bv_unsigned (edenot E b) + k + (i - s)) with (usp + i) in Hd by lia. exact Hd. }
      assert (UA : uE E KE_AUX = usp + 8 * argc + 8 * envc).
      { unfold uE. remember (bv_unsigned (edenot E KE_AUX)) as s0 eqn:Es. LINEQ KE_AUX LA HUA. rewrite <- Es in HUA. lia. }
      assert (EA : fst e_auxb = KE_AUX) by (vm_compute; reflexivity).
      assert (EA2 : snd e_auxb = 24) by (vm_compute; reflexivity).
      rewrite EA, EA2 in KU1, KU2. rewrite HRZ in KU1, KU2, KU3, CB, LRB.
      pose proof (AsanInitK.e_atrb_off rseq) as RO.
      change (snd (e_atrb (rseq_z rseq))) with (KE_RNDOFF (rseq_z rseq)) in RO.
      assert (AX : AUXSZ (rseq_z rseq) = 432 + 32 * rseq_z rseq) by reflexivity.
      assert (UR : uE E (KE_RND (rseq_z rseq)) = usp + 8 * argc + 8 * envc + 8 * GAPW).
      { revert LRB.
        destruct (kb_rseq (in_kernel INP)); cbn [rseq_z]; intros LRB; unfold uE;
          match goal with |- bv_unsigned (edenot E ?e) = _ =>
            remember (bv_unsigned (edenot E e)) as xr eqn:Exr; LINEQ e LRB HRr; rewrite <- Exr in HRr end;
          lia. }
      assert (LGp : elenZ E (escale 8 (EVar V_G)) = 8 * GAPW).
      { unfold elenZ. remember (bv_unsigned (edenot E (escale 8 (EVar V_G)))) as g eqn:Eg.
        LINEQ (escale 8 (EVar V_G)) LG HG. rewrite <- Eg in HG. lia. }
      assert (L1A : elenZ E (ELit (AUXSZ (rseq_z rseq))) = AUXSZ (rseq_z rseq)).
      { unfold elenZ. cbn [edenot]. pose proof (rseq_z_range rseq). apply u64_lit. lia. }
      assert (LW : elenZ E (EVar V_W) = PADW) by exact UW.
      destruct (Z_lt_le_dec i (8 * argc + 8 * envc + 24 + AUXSZ (rseq_z rseq))) as [D1|D1].
      { apply (UNK KE_AUX 24 (ELit (AUXSZ (rseq_z rseq))) (8 * argc + 8 * envc + 24) (AUXSZ (rseq_z rseq)) KU1);
          [lia | exact L1A | lia]. }
      destruct (Z_lt_le_dec i (8 * argc + 8 * envc + 24 + AUXSZ (rseq_z rseq) + 8 * GAPW)) as [D2|D2].
      { apply (UNK KE_AUX (24 + AUXSZ (rseq_z rseq)) (escale 8 (EVar V_G))
                   (8 * argc + 8 * envc + 24 + AUXSZ (rseq_z rseq)) (8 * GAPW) KU2); [lia | exact LGp | lia]. }
      destruct (Z_lt_le_dec i CHEAD) as [D3|D3].
      {
        pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC (kfind_blob16_In _ _ _ _ CB))
          as (_ & _ & Hb).
        assert (EL : elenZ E (ELit 16) = 16) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
        rewrite EL in Hb. specialize (Hb (i - (CHEAD - 16)) ltac:(lia)). rewrite hb_estart in Hb.
        unfold uE in UR. rewrite UR in Hb.
        match type of Hb with context [Z_to_bv 64 ?t] => replace t with (usp + i) in Hb by lia end.
        exact (mr_defined _ _ Hb). }
      apply (UNK (KE_RND (rseq_z rseq)) (KE_RNDOFF (rseq_z rseq) + 16) (EVar V_W) CHEAD PADW KU3);
        [lia | exact LW | lia].
    }
    apply argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, sp0_val, UX.
    apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. right.
    apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  Qed.

  Corollary ent_stack_defined_top : forall tp, tp mod 4096 = 0 -> tp <= usp + 4096 ->
    forall i, 0 <= i < tp - usp -> FULL (Z_to_bv 64 (usp + i)) <> None.
  Proof.
    intros tp Hm Hle i Hi. apply ent_stack_defined. destruct simg_top as (T1 & T2 & T3).
    assert (G : 8 * argc + 8 * envc + 482 <= LBx) by (eapply AsanInitK.bsb_ge; eassumption).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  Theorem ent_str_defined : forall k, (k < 2)%nat ->
    forall i, 0 <= i < Z.of_nat (length (nth k argv [])) + 1 + 8 -> FULL (Z_to_bv 64 (bv_unsigned (cat_argv_ptr top argv envp execfn k) + i)) <> None.
  Proof.
    intros k Hk i Hi. pose proof sp_rng as SR. pose proof str0_ge. pose proof str0_top. pose proof utop_hi. pose proof simg_len as SL.
    assert (Hk' : (k < length argv)%nat) by (rewrite Hargv; cbn [length]; lia).
    destruct (ent_str k Hk) as (_ & Hu).
    pose proof (total_arg_bytes_firstn_le (Datatypes.S k) argv) as Hmono.
    pose proof (total_arg_bytes_firstn_S argv k Hk') as Hstep.
    destruct Hvl as [Hfn _].
    change (in_execfn INP) with execfn in Hfn.
    assert (Hfnlen : 1 <= Z.of_nat (length execfn)).
    { destruct Hfn as [[Hp _]|[(ds & Hds & _)|(ds & rest & Hds & _)]];
        [lia | rewrite Hds, length_app; cbn [length dev_fd_prefix]; lia | rewrite Hds, !length_app; cbn [length dev_fd_prefix]; lia]. }
    assert (HL : Z.of_nat (total_arg_bytes_nat argv) + Z.of_nat (length execfn) + 1 <= LSTR).
    { unfold launch_string_bytes. rewrite (length_flatten_strings argv).
      pose proof (Zle_0_nat (length (flatten_strings envp))). lia. }
    set (q := bv_unsigned (cat_argv_ptr top argv envp execfn k)) in *.
    assert (UXq : bv_unsigned (Z_to_bv 64 (q + i)) = q + i) by (apply u_small; lia).
    apply argH_defined; [rewrite UXq; lia|].
    rewrite hbi_argH, sp0_val, UXq.
    apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. right.
    apply andb_true_intro. split; [apply Z.leb_le; lia|].
    apply Z.ltb_lt.
    lia.
  Qed.

  Hypothesis CHKLIB : lib_chk r cs = true.

  Lemma lib_chk_parts :
    kfind_word (kn cs) (ELit 0) 0x6759b8 8 = Some (ELit 0x6759b8)
    /\ (exists v, kfind_word (kn cs) (ELit 0) 0x6759d8 4 = Some v /\ existsb (kentry_eqb (KRange v 1 4194303)) (kn cs) = true)
    /\ kfind_word (kn cs) (ELit 0) 0x675a50 8 = Some (ELit 0x695d48)
    /\ kfind_word (kn cs) (ELit 0) 0x695d18 8 = Some KE_AUXP
    /\ lin_nowrapR (kn cs) KE_AUXP = true
    /\ (forall off e, In (off, e) (AUXV_EXP r) -> kfind_word (kn cs) KE_AUX off 8 = Some e)
    /\ existsb (kentry_eqb (KRange (EVar V_UID) 0 4294967294)) (kn cs) = true.
  Proof.
    pose proof CHKLIB as H. unfold lib_chk in H.
    apply andb_prop in H as [H C7]. apply andb_prop in H as [H C6]. apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4].
    apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
    assert (OE : forall o e, opt_eqb o e = true -> o = Some e).
    { intros o e Ho. destruct o as [v|]; [|discriminate]. apply expr_eqb_eq in Ho. subst. reflexivity. }
    split; [apply OE; exact C1|]. split.
    { destruct (kfind_word (kn cs) (ELit 0) 0x6759d8 4) as [v|]; [|discriminate]. exists v. split; [reflexivity | exact C2]. }
    split; [apply OE; exact C3|]. split; [apply OE; exact C4|]. split; [exact C5|]. split; [|exact C7].
    intros off e Hin. apply OE. exact (proj1 (forallb_forall _ _) C6 (off, e) Hin).
  Qed.

  Lemma ent_litcell : forall a (w : nat) v, kfind_word (kn cs) (ELit 0) a w = Some v -> 0 <= a < 2 ^ 63 ->
    rdn ASEGS0 MV (Z_to_bv 64 a) w = Some (word_to_le_bytes w (edenot E v)).
  Proof.
    intros a w v Hk Ha.
    destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model (ELit 0) a w v HC Hk)
      as (_ & Hf & Hr & Hav).
    rewrite (hb_adenot E _ _ Hf), hb_estart in Hr, Hav. cbn [edenot] in Hr, Hav. rewrite (u64_lit 0) in Hr, Hav by lia. rewrite Z.add_0_l in Hr, Hav.
    rewrite (rdn_mrestrict_eq ASEGS0 Hx w FULL _ (avoid_x _ _ Hav)). exact Hr.
  Qed.

  Theorem ent_xcells : xc_chk cs = true ->
    Forall (fun c : Z * nat * Z => rdn ASEGS0 MV (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (word_to_le_bytes (snd (fst c)) (Z_to_bv 64 (snd c)))) XC9K.
  Proof.
    intros CHKX. unfold xc_chk in CHKX. rewrite forallb_forall in CHKX. apply Forall_forall. intros c Hin.
    pose proof (art_lit1 sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc
                  Hsp Hva E cs R FULL model c HC (CHKX c Hin)) as CELL. unfold ArtMem.cell in CELL.
    destruct ent_lz as (HOFF & _).
    rewrite rdn_mrestrict_eq; [exact CELL|].
    intros k Hk. destruct (Hx (woff (Z_to_bv 64 (fst (fst c))) k)) eqn:Hh; [exfalso | reflexivity].
    pose proof (HOFF _ Hh) as X. clear - Hin Hk X. unfold XC9K in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [subst c; cbn [fst snd] in *; do 8 (destruct k as [|k]; [exfalso; lazymatch type of X with find_segment ?S ?a ?n = None =>
        assert (Hs : match find_segment S a n with Some _ => true | None => false end = true) by (vm_compute; reflexivity); rewrite X in Hs; discriminate Hs end|]); lia|]).     destruct Hin.
  Qed.

  Lemma val_auxp : edenot E KE_AUXP = Z_to_bv 64 (usp + 8 * argc + 8 * envc + 24).
  Proof.
    destruct lib_chk_parts as (_ & _ & _ & _ & LN & _). destruct ent_vals2 as (U1 & U2 & _ & U0). pose proof sp_rng.
    apply word_of_u. remember (bv_unsigned (edenot E KE_AUXP)) as x eqn:Ex. LINEQ KE_AUXP LN H0. rewrite <- Ex in H0.
    rewrite Hargv in *. cbn [length] in *. change (Z.of_nat 2) with 2 in *. lia.
  Qed.

  Theorem ent_libcells : exists tid : word,
    1 <= bv_unsigned tid <= 4194303
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x6759b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6759b8))
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x6759d8) 4 = Some (word_to_le_bytes 4 tid)
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x675a50) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x695d48))
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x695d18) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * argc + 8 * envc + 24))).
  Proof.
    destruct lib_chk_parts as (K1 & (v & K2 & K2r) & K3 & K4 & _).
    exists (edenot E v).
    pose proof (hb_knb ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC K2r) as RG. cbn [kentry_ok] in RG.
    split; [exact RG|].
    split; [exact (ent_litcell _ _ _ K1 ltac:(lia))|].
    split; [exact (ent_litcell _ _ _ K2 ltac:(lia))|].
    split; [exact (ent_litcell _ _ _ K3 ltac:(lia))|].
    pose proof (ent_litcell _ _ _ K4 ltac:(lia)) as X. rewrite val_auxp in X. exact X.
  Qed.

  Lemma ent_aux_defined : forall i, 24 <= i < 24 + AUXSZ r -> FULL (Z_to_bv 64 (usp + 8 * argc + 8 * envc + i)) <> None.
  Proof.
    intros i Hi.
    destruct stk_chk_parts as (_ & LA & _ & _). destruct stk_cover_parts as (_ & _ & KU1 & _ & _).
    destruct ent_vals2 as (V1 & V2 & _ & V0). pose proof sp_rng as SR.
    assert (UA : uE E KE_AUX = usp + 8 * argc + 8 * envc).
    { unfold uE. remember (bv_unsigned (edenot E KE_AUX)) as s0 eqn:Es. LINEQ KE_AUX LA H. rewrite <- Es in H.
      rewrite Hargv in *. cbn [length] in *. change (Z.of_nat 2) with 2 in *. lia. }
    assert (EA : fst e_auxb = KE_AUX) by (vm_compute; reflexivity).
    assert (EA2 : snd e_auxb = 24) by (vm_compute; reflexivity).
    rewrite EA, EA2 in KU1.
    assert (L1A : elenZ E (ELit (AUXSZ r)) = AUXSZ r).
    { unfold elenZ. cbn [edenot]. assert (R01 : 0 <= r <= 1) by (rewrite HRZ; apply rseq_z_range).
      apply u64_lit. unfold AUXSZ. lia. }
    destruct (hb_unk ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ _ HC KU1) as (_ & Hd).
    rewrite L1A in Hd. specialize (Hd (i - 24) ltac:(lia)). rewrite hb_estart in Hd. unfold uE in UA.
    replace (bv_unsigned (edenot E KE_AUX) + 24 + (i - 24)) with (usp + 8 * argc + 8 * envc + i) in Hd by lia. exact Hd.
  Qed.

    Local Ltac aux_cell KC EV VR :=
      cbn [nth RefLayout.auxv_words auxv_entries flat_map app fst snd la_sysinfo_ehdr la_cache la_minsigstksz la_rseq
           cw_l1i_size cw_l1i_geom cw_l1d_size cw_l1d_geom cw_l2_size cw_l2_geom cw_l3_size cw_l3_geom];
      first
        [ match goal with H : rdn _ _ ?a _ = _ |- rdn _ _ ?a _ = _ => exact H end
        | match goal with |- rdn _ _ (Z_to_bv 64 (_ + 24 + 8 * Z.of_nat ?k)) _ = _ =>
            rewrite (KC k _ eq_refl); apply (f_equal Some); apply (f_equal (word_to_le_bytes 8));
            rewrite ?aph0_addr, ?aph0_ent, ?aph0_num;
            first [exact VR | exact (EV _) | reflexivity] end
        | assumption ].
  Hypothesis CHKAUX : aux_chk r cs = true.
  Theorem ent_auxv : exists (uidz rnd hwz : Z) (la : LaunchAuxv) (entry gidw ae : word),
    (forall j, (j < 2 * auxv_count (la_rseq la))%nat ->
       rdn ASEGS0 FULL (Z_to_bv 64 (usp + 8 * argc + 8 * envc + 24 + 8 * Z.of_nat j)) 8
       = Some (word_to_le_bytes 8 (nth j (RefLayout.auxv_words la APH0 entry (Z_to_bv 64 uidz) gidw (Z_to_bv 64 hwz) (Z_to_bv 64 rnd) ae)
                                        (Z_to_bv 64 0))))
    /\ usp + 8 * argc + 8 * envc + 24 + 16 * Z.of_nat (auxv_count (la_rseq la)) <= 2 ^ 47
    /\ 0 <= uidz < 2 ^ 32 /\ 0 <= hwz < 2 ^ 64 /\ usp <= rnd /\ rnd + 16 <= 2 ^ 64.
  Proof.
    destruct lib_chk_parts as (_ & _ & _ & _ & _ & _ & KU).
    destruct stk_chk_parts as (_ & LA & LR & _).
    destruct ent_vals2 as (V1 & V2 & _ & V0). pose proof sp_rng as SR.
    pose proof gap_rng. pose proof chead_eq as CH. pose proof ent_g as UG.
    pose proof str0_ge. pose proof str0_top. pose proof utop_hi.
    pose proof (Nat2Z.is_nonneg (block_pad_len rseq sp top argv envp execfn)).
    pose proof (Zle_0_nat (length envp)) as EN.
    pose proof (Nat2Z.is_nonneg (launch_string_bytes argv envp execfn)).
    assert (CS : Z.of_nat (cat_string_off rseq sp top argv envp execfn) = CHEAD + PADW) by (unfold cat_string_off; lia).
    assert (AC : argc = 2) by (rewrite Hargv; reflexivity).
    assert (UA : uE E KE_AUX = usp + 8 * argc + 8 * envc).
    { unfold uE. remember (bv_unsigned (edenot E KE_AUX)) as s0 eqn:Es. LINEQ KE_AUX LA HLA. rewrite <- Es in HLA.
      rewrite Hargv in *. cbn [length] in *. change (Z.of_nat 2) with 2 in *. lia. }
    assert (UR : uE E (e_atrandom r) = usp + 8 * argc + 8 * envc + 8 * GAPW + 24 + (432 + 32 * r)).
    { assert (R01 : r = 0 \/ r = 1) by (rewrite HRZ; unfold rseq_z; destruct (kb_rseq (in_kernel INP)); auto).
      unfold uE. destruct R01 as [Er|Er]; rewrite Er in LR |- *;
        match goal with |- bv_unsigned (edenot E ?e) = _ =>
          remember (bv_unsigned (edenot E e)) as s0 eqn:Es; LINEQ e LR HLR; rewrite <- Es in HLR end;
        rewrite Hargv in *; cbn [length] in *; change (Z.of_nat 2) with 2 in *; lia. }
    pose proof (hb_knb ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC KU) as RGU. cbn [kentry_ok edenot] in RGU.
    assert (EV : forall n, edenot E (EVar n) = Z_to_bv 64 (bv_unsigned (ev E n))) by (intros n; cbn [edenot]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (VR : edenot E (KE_RNDP r) = Z_to_bv 64 (uE E (e_atrandom r))).
    { unfold KE_RNDP. apply word_of_u. reflexivity. }
    assert (KC : forall j e, nth j (AUXE r) None = Some e ->
               rdn ASEGS0 FULL (Z_to_bv 64 (usp + 8 * argc + 8 * envc + 24 + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 (edenot E e))).
    { intros j e Hn. pose proof (aux_chk_from_nth (kn cs) (AUXE r) 0 j e CHKAUX Hn) as Hk. cbn [Nat.add] in Hk.
      destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model KE_AUX _ 8 e HC Hk)
        as (_ & Hf & Hr & _).
      rewrite (hb_adenot E _ _ Hf), hb_estart in Hr. fold (uE E KE_AUX) in Hr. rewrite UA in Hr.
      replace (usp + 8 * argc + 8 * envc + 24 + 8 * Z.of_nat j) with (usp + 8 * argc + 8 * envc + (24 + 8 * Z.of_nat j)) by ring.
      exact Hr. }
    assert (UK : forall j, 8 * Z.of_nat j + 8 <= AUXSZ r ->
               exists w, rdn ASEGS0 FULL (Z_to_bv 64 (usp + 8 * argc + 8 * envc + 24 + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 w)).
    { intros j Hj. assert (R01 : 0 <= r <= 1) by (rewrite HRZ; apply rseq_z_range). unfold AUXSZ in Hj.
      destruct (AX2SK.rdn_defined ASEGS0 FULL 8 (Z_to_bv 64 (usp + 8 * argc + 8 * envc + 24 + 8 * Z.of_nat j))) as (bs & Hr & Hl).
      - rewrite u64_lit by lia. lia.
      - intros k Hk. rewrite u64_lit by lia. unfold AX2SK.rd1.
        pose proof (ent_aux_defined (24 + 8 * Z.of_nat j + Z.of_nat k) ltac:(unfold AUXSZ; lia)) as D.
        replace (usp + 8 * argc + 8 * envc + 24 + 8 * Z.of_nat j + Z.of_nat k)
          with (usp + 8 * argc + 8 * envc + (24 + 8 * Z.of_nat j + Z.of_nat k)) by ring.
        destruct (FULL (Z_to_bv 64 (usp + 8 * argc + 8 * envc + (24 + 8 * Z.of_nat j + Z.of_nat k)))) as [b|] eqn:HF;
          [discriminate | exfalso; apply D; first [reflexivity | exact HF]].
      - pose proof (AsanPlanSoundSumsK.APSXK.word_to_le_bytes_of_bytes_n 8 bs Hl ltac:(lia)) as X.
        eexists. rewrite Hr. apply (f_equal Some). symmetry. exact X. }
    rewrite <- HRZ in CH.
    assert (R01 : r = 0 \/ r = 1) by (rewrite HRZ; unfold rseq_z; destruct (kb_rseq (in_kernel INP)); auto).
    destruct R01 as [Er|Er]; rewrite Er in KC, UK, UR, VR, CH.
    - destruct (UK 1%nat ltac:(unfold AUXSZ; lia)) as (w1 & W1). destruct (UK 3%nat ltac:(unfold AUXSZ; lia)) as (w3 & W3).
      destruct (UK 5%nat ltac:(unfold AUXSZ; lia)) as (w5 & W5). destruct (UK 7%nat ltac:(unfold AUXSZ; lia)) as (w7 & W7).
      destruct (UK 9%nat ltac:(unfold AUXSZ; lia)) as (w9 & W9). destruct (UK 11%nat ltac:(unfold AUXSZ; lia)) as (w11 & W11).
      destruct (UK 13%nat ltac:(unfold AUXSZ; lia)) as (w13 & W13). destruct (UK 15%nat ltac:(unfold AUXSZ; lia)) as (w15 & W15).
      destruct (UK 17%nat ltac:(unfold AUXSZ; lia)) as (w17 & W17). destruct (UK 19%nat ltac:(unfold AUXSZ; lia)) as (w19 & W19).
      destruct (UK 37%nat ltac:(unfold AUXSZ; lia)) as (w37 & W37). destruct (UK 51%nat ltac:(unfold AUXSZ; lia)) as (w51 & W51).
      exists (bv_unsigned (ev E V_UID)), (uE E (e_atrandom 0)), (bv_unsigned (ev E V_HW)),
             (mkLaunchAuxv w1 (mkCacheWords w3 w5 w7 w9 w11 w13 w15 w17) w19 false), w37, (edenot E (EVar V_GID)), w51.
      cbn [la_rseq auxv_count].
      split; [|split; [lia|]; split; [lia|]; split; [pose proof (u64_range (ev E V_HW)); lia|]; split; rewrite UR; lia].
      intros j Hj.
      do 54 (destruct j as [|j]; [aux_cell KC EV VR|]). lia.
    - destruct (UK 1%nat ltac:(unfold AUXSZ; lia)) as (w1 & W1). destruct (UK 3%nat ltac:(unfold AUXSZ; lia)) as (w3 & W3).
      destruct (UK 5%nat ltac:(unfold AUXSZ; lia)) as (w5 & W5). destruct (UK 7%nat ltac:(unfold AUXSZ; lia)) as (w7 & W7).
      destruct (UK 9%nat ltac:(unfold AUXSZ; lia)) as (w9 & W9). destruct (UK 11%nat ltac:(unfold AUXSZ; lia)) as (w11 & W11).
      destruct (UK 13%nat ltac:(unfold AUXSZ; lia)) as (w13 & W13). destruct (UK 15%nat ltac:(unfold AUXSZ; lia)) as (w15 & W15).
      destruct (UK 17%nat ltac:(unfold AUXSZ; lia)) as (w17 & W17). destruct (UK 19%nat ltac:(unfold AUXSZ; lia)) as (w19 & W19).
      destruct (UK 37%nat ltac:(unfold AUXSZ; lia)) as (w37 & W37). destruct (UK 51%nat ltac:(unfold AUXSZ; lia)) as (w51 & W51).
      exists (bv_unsigned (ev E V_UID)), (uE E (e_atrandom 1)), (bv_unsigned (ev E V_HW)),
             (mkLaunchAuxv w1 (mkCacheWords w3 w5 w7 w9 w11 w13 w15 w17) w19 true), w37, (edenot E (EVar V_GID)), w51.
      cbn [la_rseq auxv_count].
      split; [|split; [lia|]; split; [lia|]; split; [pose proof (u64_range (ev E V_HW)); lia|]; split; rewrite UR; lia].
      intros j Hj.
      do 58 (destruct j as [|j]; [aux_cell KC EV VR|]). lia.
  Qed.
End Entry.
