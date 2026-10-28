(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b Ba0PlanImagesK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0HandoffK_b Ba0ArtCellsK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface HeapIfaceA HeapIfaceABx ArtBridge CatExec ArgvEnv FileSim MemSplit RefLayout MuslStrlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition KE_SPK (k : Z) : expr := EAlu ALU_ADD e_sp0 (ELit k).
(* [comment removed for export] *)
Definition KE_ENVP : expr :=
  EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1))
     (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 4096) (EVar 10))))) (ELit 16).
(* [comment removed for export] *)
Definition KE_P0 : expr :=
  EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2))
     (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 4096) (EVar 10)))))) (ELit 184).
(* [comment removed for export] *)
Definition KE_P1X : expr :=
  EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2))
     (EAlu ALU_ADD (EVar 3) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 4096) (EVar 10))))))) (ELit 185).
Definition KE_P1 : expr := EMd M_MUL (EAlu ALU_SLTU (ELit 1) (EVar 1)) KE_P1X.

(* [comment removed for export] *)
Definition DRV_REGS : list (Z * expr) :=
  [(1, ELit 0x1180b0); (2, KE_SPK (-48)); (3, ELit 0x10800); (4, ELit 0x673d00); (8, KE_SPK 8); (9, EVar 1); (10, EVar 1); (11, KE_SPK 8);
   (12, KE_ENVP); (18, ELit 0xa7b04); (19, KE_ENVP); (20, ELit 0); (21, ELit 0); (22, ELit 0); (23, ELit 0); (24, ELit 0); (25, ELit 0);
   (26, ELit 0); (27, ELit 0)].

Definition opt_eqb (o : option expr) (e : expr) : bool := match o with Some v => expr_eqb v e | None => false end.
Definition img_cover (k : list kentry) (lo hi : Z) : bool :=
  existsb (fun K => match K with KImg l h => (l <=? lo) && (hi <=? h) | _ => false end)%bool k.

(* [comment removed for export] *)
Definition DRV_IMG : list (Z * Z) := [(0x10000, 0x139510); (0x13952c, 0x13c580); (0x66228a, 0x673c30); (0x693fc8, 0x693ff8)].   (* [comment removed for export] *)   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition drv_chk (cs : acs) : bool :=
  (Z.eqb (pc cs) 0xa7b04
   && forallb (fun p => expr_eqb (sr_get (s_regs (a_ss cs)) (Z_to_bv 5 (fst p))) (snd p)) DRV_REGS
   && lin_nowrapR (kn cs) e_sp0 && lin_nowrapR (kn cs) (KE_SPK (-48)) && lin_nowrapR (kn cs) (KE_SPK 8) && lin_nowrapR (kn cs) KE_ENVP
   && lin_nowrapR (kn cs) KE_P0 && lin_nowrapR (kn cs) KE_P1X
   && opt_eqb (kfind_word (kn cs) e_sp0 0 8) (EVar 1) && opt_eqb (kfind_word (kn cs) e_sp0 8 8) KE_P0
   && opt_eqb (kfind_word (kn cs) e_sp0 16 8) KE_P1
   && opt_eqb (kfind_wr (kn cs) e_sp0 (-8388608)) (ELit 8388608)
   && match kfind_word (kn cs) (ELit 0) 0x693d40 8 with Some v => opt_eqb (kfind_word (kn cs) (ELit 0) 0x673cf0 8) v | None => false end
   && forallb (fun r => img_cover (kn cs) (fst r) (snd r)) DRV_IMG
   && match a_fd cs with FdStd => true | _ => false end)%bool.

(* [comment removed for export] *)
Definition KE_AUX : expr :=
  EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2))
    (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 4096) (EVar 10))))).
Definition KE_RND : expr :=
  EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2))
    (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 4)) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 4096) (EVar 10)))))).
Definition AUX_OFFS : list Z := [24; 32; 40; 48; 56; 64; 72; 80; 88; 96; 104; 112; 120; 128; 136; 144; 152; 160; 168; 176].
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
Definition stk_chk (cs : acs) : bool :=
  (forallb (fun off => is_some (kfind_word (kn cs) KE_AUX off 8)) AUX_OFFS
   && lin_nowrapR (kn cs) KE_AUX && lin_nowrapR (kn cs) KE_RND
   && is_some (kfind_blob16 (kn cs) KE_RND 184))%bool.


(* [comment removed for export] *)
Definition KE_RNDP : expr := EAlu ALU_ADD KE_RND (ELit 184).
Definition KE_AUXP : expr := EAlu ALU_ADD KE_AUX (ELit 24).
Definition AUXV_EXP : list (Z * expr) :=
  combine AUX_OFFS [ELit 3; ELit 0x10040; ELit 4; ELit 56; ELit 5; ELit 11; ELit 16; EVar 9; ELit 6; ELit 4096; ELit 11; EVar 8; ELit 12; EVar 8;
                    ELit 23; ELit 0; ELit 25; KE_RNDP; ELit 0; ELit 0].
Definition lib_chk (cs : acs) : bool :=
  (opt_eqb (kfind_word (kn cs) (ELit 0) 0x673c38 8) (ELit 0x673c38)
   && match kfind_word (kn cs) (ELit 0) 0x673c58 4 with Some v => existsb (kentry_eqb (KRange v 1 4194303)) (kn cs) | None => false end
   && opt_eqb (kfind_word (kn cs) (ELit 0) 0x673cd0 8) (ELit 0x693fc8)
   && opt_eqb (kfind_word (kn cs) (ELit 0) 0x693f98 8) KE_AUXP
   && lin_nowrapR (kn cs) KE_AUXP
   && forallb (fun p => opt_eqb (kfind_word (kn cs) KE_AUX (fst p) 8) (snd p)) AUXV_EXP
   && existsb (kentry_eqb (KRange (EVar 8) 0 4294967294)) (kn cs))%bool.

(* [comment removed for export] *)
Definition XC9K : list (Z * nat * Z) :=
  [(6897520, 4%nat, 0); (6897555, 1%nat, 0); (6896992, 8%nat, 6897000); (6896984, 4%nat, 1); (6897008, 8%nat, 1148964); (6897264, 8%nat, 619876); (6896980, 4%nat, 0); (6897000, 8%nat, 0);
   (6898952, 8%nat, 0); (6896976, 1%nat, 0); (6897776, 4%nat, 0)].      (* [comment removed for export] *)
Definition xc_chk (cs : acs) : bool := forallb (chk_lit1 (kn cs)) XC9K.

Lemma all_andb_split : forall a b, (a && b)%bool = true -> a = true /\ b = true.
Proof. intros a b H. apply andb_prop in H. exact H. Qed.

Section Entry.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  Let AH := argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva.

  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.

  Variable cs : acs.
  Hypothesis CHK0 : as0_chk cs = true.
  Hypothesis CHKD : drv_chk cs = true.
  Hypothesis BUD_le : a_eager cs + a_abytes cs + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
                   + (Z.of_nat (length (segments_reserved ASEGS0) + length (a_maps cs)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis HC : CSOK E cs R FULL model.

  #[local] Notation A0 := (as0_A0 EXTRA cs E).
  #[local] Notation Hx := (ahid A0 model).
  #[local] Notation MV := (mrestrict Hx FULL).
  #[local] Notation HIDK := (hid ASAN0 argH E cs model).
  #[local] Notation usp := (bv_unsigned sp).

  (* [comment removed for export] *)
  Lemma drv_chk_parts :
    pc cs = 0xa7b04
    /\ (forall r e, In (r, e) DRV_REGS -> sr_get (s_regs (a_ss cs)) (Z_to_bv 5 r) = e)
    /\ lin_nowrapR (kn cs) e_sp0 = true /\ lin_nowrapR (kn cs) (KE_SPK (-48)) = true /\ lin_nowrapR (kn cs) (KE_SPK 8) = true
    /\ lin_nowrapR (kn cs) KE_ENVP = true /\ lin_nowrapR (kn cs) KE_P0 = true /\ lin_nowrapR (kn cs) KE_P1X = true
    /\ kfind_word (kn cs) e_sp0 0 8 = Some (EVar 1) /\ kfind_word (kn cs) e_sp0 8 8 = Some KE_P0
    /\ kfind_word (kn cs) e_sp0 16 8 = Some KE_P1
    /\ kfind_wr (kn cs) e_sp0 (-8388608) = Some (ELit 8388608)
    /\ (exists v, kfind_word (kn cs) (ELit 0) 0x693d40 8 = Some v /\ kfind_word (kn cs) (ELit 0) 0x673cf0 8 = Some v)
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
    split; [intros r e Hin; pose proof (proj1 (forallb_forall _ _) Creg (r, e) Hin) as Hb; cbn [fst snd] in Hb; apply expr_eqb_eq; exact Hb|].
    do 6 (split; [assumption|]).
    do 4 (split; [apply OE; assumption|]).
    split.
    - destruct (kfind_word (kn cs) (ELit 0) 0x693d40 8) as [v|]; [|discriminate]. exists v. split; [reflexivity | apply OE; assumption].
    - split; [intros lo hi Hin; exact (proj1 (forallb_forall _ _) Cimg (lo, hi) Hin)|].
      destruct (a_fd cs); first [reflexivity | discriminate].
  Qed.

  (* [comment removed for export] *)
  Ltac LINEQ e Hn H :=
    pose proof (hb_lin ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model e HC Hn) as H;
    unfold LZ in H;
    match type of H with context [lin_of ?x] => let l := eval vm_compute in (lin_of x) in change (lin_of x) with l in H end;
    cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE] in H; cbn [edenot] in H;
    repeat match type of H with context [bv_unsigned (ev E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) in H end;
    rewrite ?Z.add_0_r in H.

  Lemma ent_vals : VZ E 1 = Z.of_nat (length argv) /\ VZ E 2 = Z.of_nat (length envp) /\ VZ E 3 = Z.of_nat (length (nth 0 argv []))
                   /\ 32768 * VZ E 0 + 16 * VZ E 6 + 4096 * VZ E 10 = usp.
  Proof.
    destruct (hbi_vals ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC)
      as (_ & _ & U1 & U2 & U3 & _).
    pose proof (hbi_sp0 ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC) as U0.
    auto.
  Qed.

  Lemma sp0_val : uE E e_sp0 = usp.
  Proof.
    destruct drv_chk_parts as (_ & _ & L1 & _). destruct ent_vals as (_ & _ & _ & U0).
    unfold uE. remember (bv_unsigned (edenot E e_sp0)) as s0 eqn:Es. LINEQ e_sp0 L1 H. rewrite <- Es in H. lia.
  Qed.

  Lemma sp_rng : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0.
  Proof. destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma ent_binv : BInv ASEGS0 (vm_maps (m_vmmaps model)) (segments_reserved ASEGS0) (vm_noaccess (m_vmmaps model))
                        (uE E e_sp0 - 8388608) (as0_BASE EXTRA cs) BUDGET [] A0 FULL model.
  Proof. exact (as0_binv_main sp brk0 rdraw argv envp uid hw fs Hsp Hva BUDGET LENMAX KMAX BUD EXTRA EXTRA_wf cs CHK0 BUD_le GAP E R FULL model HC). Qed.

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Lemma ent_lz : H_off_segments ASEGS0 Hx /\ lazy_cover Hx (m_vm_lazy model) A0 /\ A_wf A0 /\ MInv A0 model /\ m_halted model = None.
  Proof.
    pose proof ent_binv as B.
    split; [intros a Ha; unfold ahid, mkH in Ha; apply andb_prop in Ha as [Hl _]; exact (proj2 (bi_lazy_in _ _ _ _ _ _ _ _ _ _ _ B a Hl))|].
    split; [unfold ahid; apply lazy_cover_mkH; intros r Hr; exact Hr|].
    split; [exact (bi_awf _ _ _ _ _ _ _ _ _ _ _ B)|].
    split; [exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B) | exact (bi_halt _ _ _ _ _ _ _ _ _ _ _ B)].
  Qed.

  Lemma ent_model : m_fds model = fds_std /\ m_fs model = fs.
  Proof.
    split; [|exact (hb_fs ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC)].
    apply (hb_fds_std ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC).
    exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 drv_chk_parts)))))))))))))).
  Qed.

  (* [comment removed for export] *)
  Variables a0s path : list byte.
  Hypothesis Hargv : argv = [a0s; path].
  #[local] Notation envc := (Z.of_nat (length envp)).
  #[local] Notation L0 := (Z.of_nat (length a0s)).

  Lemma ent_vals2 : VZ E 1 = 2 /\ VZ E 2 = envc /\ VZ E 3 = L0 /\ 32768 * VZ E 0 + 16 * VZ E 6 + 4096 * VZ E 10 = usp.
  Proof. destruct ent_vals as (U1 & U2 & U3 & U0). rewrite Hargv in U1, U3. cbn [length nth] in U1, U3. auto. Qed.

  Lemma word_of_u : forall (w : word) z, bv_unsigned w = z -> w = Z_to_bv 64 z.
  Proof. intros w z <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  (* [comment removed for export] *)
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
  Lemma val_p0 : edenot E KE_P0 = Z_to_bv 64 (usp + 8 * envc + 200).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & L5 & _). destruct ent_vals2 as (U1 & U2 & _ & U0).
    apply word_of_u. remember (bv_unsigned (edenot E KE_P0)) as x eqn:Ex. LINEQ KE_P0 L5 H0. rewrite <- Ex in H0. lia.
  Qed.
  Lemma val_p1x : edenot E KE_P1X = Z_to_bv 64 (usp + 8 * envc + L0 + 201).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & L6 & _). destruct ent_vals2 as (U1 & U2 & U3 & U0).
    apply word_of_u. remember (bv_unsigned (edenot E KE_P1X)) as x eqn:Ex. LINEQ KE_P1X L6 H0. rewrite <- Ex in H0. lia.
  Qed.
  Lemma val_argc : edenot E (EVar 1) = Z_to_bv 64 2.
  Proof. destruct ent_vals2 as (U1 & _). apply word_of_u. exact U1. Qed.
  Lemma val_p1 : edenot E KE_P1 = Z_to_bv 64 (usp + 8 * envc + L0 + 201).
  Proof.
    unfold KE_P1. cbn [edenot]. fold (edenot E KE_P1X). rewrite val_p1x. apply word_of_u.
    rewrite u_mul64, u_sltu64. destruct ent_vals2 as (U1 & _). unfold VZ in U1. rewrite U1.
    rewrite (u64_lit 1) by lia. change (1 <? 2) with true. cbv iota.
    pose proof sp_rng. pose proof (Zle_0_nat (length envp)). pose proof (Zle_0_nat (length a0s)).
    assert (Hb : 0 <= usp + 8 * envc + L0 + 201 < 2 ^ 64).
    { pose proof Hve as [Hle _]. pose proof Hva as (_ & _ & Hfa & _). rewrite Hargv in Hfa. inversion Hfa as [|x l Hx _]; subst. lia. }
    rewrite u64_lit by exact Hb. rewrite Z.mul_1_l. apply Z.mod_small. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma ent_reg : forall r e, In (r, e) DRV_REGS -> getr R (Z_to_bv 5 r) = edenot E e.
  Proof.
    intros r e Hin. destruct drv_chk_parts as (_ & HRg & _). rewrite <- (HRg r e Hin).
    exact (hb_reg ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC).
  Qed.

  Definition DRV_REGV : list (Z * Z) :=
    [(1, 0x1180b0); (2, usp - 48); (3, 0x10800); (4, 0x673d00); (8, usp + 8); (9, 2); (10, 2); (11, usp + 8);
     (12, usp + 32); (18, 0xa7b04); (19, usp + 32); (20, 0); (21, 0); (22, 0); (23, 0); (24, 0); (25, 0); (26, 0); (27, 0)].

  Theorem ent_regs : forall r v, In (r, v) DRV_REGV -> getr R (Z_to_bv 5 r) = Z_to_bv 64 v.
  Proof.
    intros r v Hin. unfold DRV_REGV in Hin.
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 1 (ELit 0x1180b0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 2 (KE_SPK (-48))) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_spk48|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 3 (ELit 0x10800)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 4 (ELit 0x673d00)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 8 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_spk8|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 9 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_argc|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 10 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_argc|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 11 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_spk8|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 12 (KE_ENVP)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_envp|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 18 (ELit 0xa7b04)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
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

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Theorem ent_stack_words :
    rdn ASEGS0 MV (Z_to_bv 64 usp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 2))
    /\ rdn ASEGS0 MV (Z_to_bv 64 (usp + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * envc + 200)))
    /\ rdn ASEGS0 MV (Z_to_bv 64 (usp + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * envc + L0 + 201))).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & K0 & K8 & K16 & _).
    pose proof (ent_stkword 0 _ K0) as H0. pose proof (ent_stkword 8 _ K8) as H8. pose proof (ent_stkword 16 _ K16) as H16.
    rewrite Z.add_0_r, val_argc in H0. rewrite val_p0 in H8. rewrite val_p1 in H16. auto.
  Qed.

  (* [comment removed for export] *)
  Theorem ent_window : forall d (m : nat), 0 <= d -> d + Z.of_nat m <= 8388608 ->
    store_ok ASEGS0 MV (Z_to_bv 64 (usp - 8388608 + d)) m = true.
  Proof.
    intros d m Hd Hm. destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KW & _).
    destruct (hb_wr_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model e_sp0 (-8388608) _ HC KW)
      as (Hf & HW).
    assert (EL : elenZ E (ELit 8388608) = 8388608) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
    destruct (HW d m Hd ltac:(rewrite EL; exact Hm)) as (Hs & Hav).
    rewrite hb_estart in Hs, Hav. fold (uE E e_sp0) in Hs, Hav. rewrite sp0_val in Hs, Hav.
    replace (usp + -8388608 + d) with (usp - 8388608 + d) in Hs, Hav by ring.
    rewrite (store_ok_mrestrict_eq ASEGS0 Hx m FULL _ (avoid_x _ _ Hav)). exact Hs.
  Qed.

  (* [comment removed for export] *)
  Theorem ent_guard : exists can : word,
    rdn ASEGS0 MV (Z_to_bv 64 0x693d40) 8 = Some (word_to_le_bytes 8 can) /\ rdn ASEGS0 MV (Z_to_bv 64 0x673cf0) 8 = Some (word_to_le_bytes 8 can).
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

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
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

  Lemma wsb_eq : 8 * Wsb APH0 sp rdraw argv envp uid hw
                 = Z.of_nat (length (build_stack_bytes APH0 sp argv envp uid hw rdraw)) - 16 - (8 * 2 + 8 * envc + 184).
  Proof.
    destruct (bsb_ge APH0 sp rdraw argv envp uid hw) as [_ Hm]. unfold Wsb. rewrite Hargv in *. cbn [length] in *. change (Z.of_nat 2) with 2 in *.
    set (n := Z.of_nat (length (build_stack_bytes APH0 sp [a0s; path] envp uid hw rdraw)) - 16 - (8 * 2 + 8 * envc + 184)) in *.
    pose proof (Z.div_mod n 8 ltac:(lia)) as D. rewrite Hm in D. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ent_strblock : forall x : word,
    usp + 8 * envc + 200 <= bv_unsigned x < usp + Z.of_nat (length (build_stack_bytes APH0 sp argv envp uid hw rdraw)) - 16 ->
    MV x = wrap_mem APH0 sp argv envp uid hw rdraw x.
  Proof.
    intros x Hxr. pose proof sp_rng as SR. unfold mrestrict. rewrite (vis_high x ltac:(lia)).
    apply (hbi_argblock ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs E cs R FULL model HC).
    rewrite hbi_argH. rewrite sp0_val. pose proof wsb_eq as W. rewrite Hargv in *. cbn [length] in *. change (Z.of_nat 2) with 2 in *.
    apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. left. apply orb_true_iff. right.   (* [comment removed for export] *)
    apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  Qed.

  (* [comment removed for export] *)
  Theorem ent_str : forall k, (k < 2)%nat ->
    rdn ASEGS0 MV (cat_argv_ptr sp argv envp k) (length (nth k argv []) + 1) = Some (nth k argv [] ++ [Z_to_bv 8 0])
    /\ bv_unsigned (cat_argv_ptr sp argv envp k) = usp + 8 * envc + 200 + Z.of_nat (total_arg_bytes_nat (firstn k argv)).
  Proof.
    intros k Hk. pose proof sp_rng as SR.
    assert (Hk' : (k < length argv)%nat) by (rewrite Hargv; cbn [length]; lia).
    pose proof (u_cat_argv_ptr APH0 sp rdraw argv envp uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    assert (CS : Z.of_nat (cat_struct_size argv envp) = 8 * envc + 200).
    { unfold cat_struct_size, auxv_size. rewrite Hargv. cbn [length]. lia. }
    pose proof (bsb_len_lower APH0 sp argv envp uid hw rdraw) as Hlow.
    pose proof (total_arg_bytes_firstn_le (Datatypes.S k) argv) as Hmono.
    pose proof (total_arg_bytes_firstn_S argv k Hk') as Hstep.
    pose proof (bsb_nw APH0 sp argv envp uid hw rdraw Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    split; [|rewrite Hu; lia].
    rewrite <- (read_argv_cstr_k APH0 ASEGS0 sp argv envp k uid hw rdraw Hk' Hnw).
    rewrite <- (rdn_wmem_stack ASEGS0 APH0 sp argv envp uid hw rdraw) by lia.
    apply rdn_ext; [lia|]. intros x Hxr. unfold wmem. apply ent_strblock. lia.
  Qed.
  (* [comment removed for export] *)
  Hypothesis CHKS : stk_chk cs = true.

  Lemma stk_chk_parts :
    (forall off, In off AUX_OFFS -> exists v, kfind_word (kn cs) KE_AUX off 8 = Some v)
    /\ lin_nowrapR (kn cs) KE_AUX = true /\ lin_nowrapR (kn cs) KE_RND = true
    /\ exists i, kfind_blob16 (kn cs) KE_RND 184 = Some i.
  Proof.
    pose proof CHKS as H. unfold stk_chk in H.
    apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
    split.
    { intros off Hin. pose proof (proj1 (forallb_forall _ _) C1 off Hin) as Hb. cbv beta in Hb.
      destruct (kfind_word (kn cs) KE_AUX off 8) as [v|]; [exists v; reflexivity | discriminate]. }
    split; [exact C2|]. split; [exact C3|].
    destruct (kfind_blob16 (kn cs) KE_RND 184) as [i|]; [exists i; reflexivity | discriminate].
  Qed.

  #[local] Notation SIMGx := (entry_stack_image APH0 sp argv envp uid hw rdraw).
  #[local] Notation LBx := (Z.of_nat (length (build_stack_bytes APH0 sp argv envp uid hw rdraw))).

  Lemma simg_top : usp + Z.of_nat (length SIMGx) <= 2 ^ 47 /\ LBx <= Z.of_nat (length SIMGx)
                   /\ (usp + Z.of_nat (length SIMGx)) mod 4096 = 0.
  Proof.
    pose proof (entry_stack_image_top APH0 sp argv envp uid hw rdraw) as T.
    pose proof (entry_page_top_within_window APH0 sp argv envp uid hw rdraw Hfit) as W. rewrite <- T in W. unfold sp_window_hi in W.
    split; [lia|]. split.
    - unfold entry_stack_image. cbv zeta. rewrite length_app. lia.
    - rewrite T. unfold entry_page_top, page_round_up_Z, page_size. apply Z_mod_mult.
  Qed.

  (* [comment removed for export] *)
  Theorem ent_str_hi : forall k, (k < 2)%nat ->
    bv_unsigned (cat_argv_ptr sp argv envp k) + Z.of_nat (length (nth k argv [])) + 1 + 16 <= 2 ^ 47.
  Proof.
    intros k Hk. pose proof sp_rng as SR.
    assert (Hk' : (k < length argv)%nat) by (rewrite Hargv; cbn [length]; lia).
    pose proof (u_cat_argv_ptr APH0 sp rdraw argv envp uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (bsb_len_lower APH0 sp argv envp uid hw rdraw) as Hlow.
    pose proof (total_arg_bytes_firstn_le (Datatypes.S k) argv) as Hmono.
    pose proof (total_arg_bytes_firstn_S argv k Hk') as Hstep.
    destruct simg_top as (T1 & T2 & _). rewrite Hu. lia.
  Qed.

  Lemma argH_defined : forall x : word, usp <= bv_unsigned x < usp + Z.of_nat (length SIMGx) -> argH E x = true -> FULL x <> None.
  Proof.
    intros x Hx Ha.
    rewrite (hbi_argblock ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs E cs R FULL model HC x Ha).
    rewrite wrap_above_sp by lia. unfold stack_to_mem.
    replace (usp <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
    replace (bv_unsigned x - usp <? Z.of_nat (length SIMGx)) with true by (symmetry; apply Z.ltb_lt; lia).
    apply nth_error_Some. lia.
  Qed.

  Lemma mr_defined : forall (x : word) b, Mr ASAN0 argH E cs model FULL x = Some b -> FULL x <> None.
  Proof. intros x b H. rewrite (hb_mr_some ASAN0 argH E cs model FULL x b H). discriminate. Qed.

  Theorem ent_stack_defined : forall i, 0 <= i < Z.of_nat (length SIMGx) -> FULL (Z_to_bv 64 (usp + i)) <> None.
  Proof.
    intros i Hi. pose proof sp_rng as SR. destruct simg_top as (T1 & T2 & _).
    destruct stk_chk_parts as (CA & LA & LR & (bi & CB)).
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & K0 & K8 & K16 & _).
    destruct (hbi_vals ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC)
      as (_ & _ & _ & _ & _ & _ & U4 & _).
    destruct ent_vals2 as (V1 & V2 & _ & V0).
    pose proof wsb_eq as WE. assert (AC : Z.of_nat (length argv) = 2) by (rewrite Hargv; reflexivity).
    assert (UX : bv_unsigned (Z_to_bv 64 (usp + i)) = usp + i) by (apply u_small; lia).
    (* [comment removed for export] *)
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
    { (* [comment removed for export] *)
      assert (ST : forall off, flat E (SA e_sp0 off) 8 -> estart E (SA e_sp0 off) = usp + off)
        by (intros off _; rewrite hb_estart; fold (uE E e_sp0); rewrite sp0_val; reflexivity).
      destruct drv_chk_parts as (_ & _ & L1 & _).
      destruct (Z_lt_le_dec i 8); [apply (KW e_sp0 0 _ 0 K0 L1 (ST 0)); lia|].
      destruct (Z_lt_le_dec i 16); [apply (KW e_sp0 8 _ 8 K8 L1 (ST 8)); lia | apply (KW e_sp0 16 _ 16 K16 L1 (ST 16)); lia]. }
    destruct (Z_lt_le_dec i (8 * envc + 40)) as [C2|C2].
    { apply argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, sp0_val, UX, AC.
      apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. left. apply orb_true_iff. left.
      apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    destruct (Z_lt_le_dec i (8 * envc + 200)) as [C3|C3].
    { (* [comment removed for export] *)
      assert (UA : uE E KE_AUX = usp + 16 + 8 * envc).
      { unfold uE. remember (bv_unsigned (edenot E KE_AUX)) as s0 eqn:Es. LINEQ KE_AUX LA H. rewrite <- Es in H. lia. }
      assert (ST : forall off, flat E (SA KE_AUX off) 8 -> estart E (SA KE_AUX off) = usp + (16 + 8 * envc + off))
        by (intros off _; rewrite hb_estart; fold (uE E KE_AUX); rewrite UA; ring).
      set (k := (i - (16 + 8 * envc)) / 8).
      assert (Hk : i - (16 + 8 * envc) = 8 * k + (i - (16 + 8 * envc)) mod 8) by (apply Z.div_mod; lia).
      pose proof (Z.mod_pos_bound (i - (16 + 8 * envc)) 8 ltac:(lia)) as Hm.
      assert (Hin : In (8 * k) AUX_OFFS).
      { assert (Hk3 : 3 <= k < 23) by lia. unfold AUX_OFFS.
        assert (Hc : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15
                     \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22) by lia.
        repeat (destruct Hc as [->|Hc]; [cbn [In]; tauto|]). subst k. rewrite Hc. cbn [In]. tauto. }
      destruct (CA _ Hin) as (v & Hv).
      apply (KW KE_AUX (8 * k) v (16 + 8 * envc + 8 * k) Hv LA (ST (8 * k))). lia. }
    destruct (Z_lt_le_dec i (LBx - 16)) as [C4|C4].
    { apply argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, sp0_val, UX, AC.
      apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. left. apply orb_true_iff. right.
      apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    destruct (Z_lt_le_dec i LBx) as [C5|C5].
    { (* [comment removed for export] *)
      assert (UR : uE E KE_RND = usp + 16 + 8 * envc + 8 * Wsb APH0 sp rdraw argv envp uid hw).
      { unfold uE. remember (bv_unsigned (edenot E KE_RND)) as s0 eqn:Es. LINEQ KE_RND LR H. rewrite <- Es in H. rewrite U4 in H. lia. }
      pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC (kfind_blob16_In _ _ _ _ CB)) as (Hf & _ & Hb).
      assert (EL : elenZ E (ELit 16) = 16) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
      rewrite EL in Hb. rewrite hb_estart in Hb. fold (uE E KE_RND) in Hb. rewrite UR in Hb.
      specialize (Hb (i - (LBx - 16)) ltac:(lia)).
      replace (usp + 16 + 8 * envc + 8 * Wsb APH0 sp rdraw argv envp uid hw + 184 + (i - (LBx - 16))) with (usp + i) in Hb by lia.
      exact (mr_defined _ _ Hb). }
    apply argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, sp0_val, UX.
    apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. right.
    apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  Qed.

  (* [comment removed for export] *)
  Corollary ent_stack_defined_top : forall top, top mod 4096 = 0 -> top <= usp + 4096 ->
    forall i, 0 <= i < top - usp -> FULL (Z_to_bv 64 (usp + i)) <> None.
  Proof.
    intros top Hm Hle i Hi. apply ent_stack_defined. destruct simg_top as (T1 & T2 & T3).
    pose proof (bsb_ge APH0 sp rdraw argv envp uid hw) as [G _].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  Theorem ent_str_defined : forall k, (k < 2)%nat ->
    forall i, 0 <= i < Z.of_nat (length (nth k argv [])) + 1 + 16 -> FULL (Z_to_bv 64 (bv_unsigned (cat_argv_ptr sp argv envp k) + i)) <> None.
  Proof.
    intros k Hk i Hi. pose proof sp_rng as SR.
    assert (Hk' : (k < length argv)%nat) by (rewrite Hargv; cbn [length]; lia).
    pose proof (u_cat_argv_ptr APH0 sp rdraw argv envp uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (bsb_len_lower APH0 sp argv envp uid hw rdraw) as Hlow.
    pose proof (total_arg_bytes_firstn_le (Datatypes.S k) argv) as Hmono.
    pose proof (total_arg_bytes_firstn_S argv k Hk') as Hstep.
    destruct simg_top as (_ & T2 & _).
    set (q := bv_unsigned (cat_argv_ptr sp argv envp k)) in *.
    replace (q + i) with (usp + (q - usp + i)) by ring.
    apply ent_stack_defined. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis CHKLIB : lib_chk cs = true.

  Lemma lib_chk_parts :
    kfind_word (kn cs) (ELit 0) 0x673c38 8 = Some (ELit 0x673c38)
    /\ (exists v, kfind_word (kn cs) (ELit 0) 0x673c58 4 = Some v /\ existsb (kentry_eqb (KRange v 1 4194303)) (kn cs) = true)
    /\ kfind_word (kn cs) (ELit 0) 0x673cd0 8 = Some (ELit 0x693fc8)
    /\ kfind_word (kn cs) (ELit 0) 0x693f98 8 = Some KE_AUXP
    /\ lin_nowrapR (kn cs) KE_AUXP = true
    /\ (forall off e, In (off, e) AUXV_EXP -> kfind_word (kn cs) KE_AUX off 8 = Some e)
    /\ existsb (kentry_eqb (KRange (EVar 8) 0 4294967294)) (kn cs) = true.
  Proof.
    pose proof CHKLIB as H. unfold lib_chk in H.
    apply andb_prop in H as [H C7]. apply andb_prop in H as [H C6]. apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4].
    apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
    assert (OE : forall o e, opt_eqb o e = true -> o = Some e).
    { intros o e Ho. destruct o as [v|]; [|discriminate]. apply expr_eqb_eq in Ho. subst. reflexivity. }
    split; [apply OE; exact C1|]. split.
    { destruct (kfind_word (kn cs) (ELit 0) 0x673c58 4) as [v|]; [|discriminate]. exists v. split; [reflexivity | exact C2]. }
    split; [apply OE; exact C3|]. split; [apply OE; exact C4|]. split; [exact C5|]. split; [|exact C7].
    intros off e Hin. apply OE. exact (proj1 (forallb_forall _ _) C6 (off, e) Hin).
  Qed.

  (* [comment removed for export] *)
  Lemma ent_litcell : forall a (w : nat) v, kfind_word (kn cs) (ELit 0) a w = Some v -> 0 <= a < 2 ^ 63 ->
    rdn ASEGS0 MV (Z_to_bv 64 a) w = Some (word_to_le_bytes w (edenot E v)).
  Proof.
    intros a w v Hk Ha.
    destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model (ELit 0) a w v HC Hk)
      as (_ & Hf & Hr & Hav).
    rewrite (hb_adenot E _ _ Hf), hb_estart in Hr, Hav. cbn [edenot] in Hr, Hav. rewrite (u64_lit 0) in Hr, Hav by lia. rewrite Z.add_0_l in Hr, Hav.
    rewrite (rdn_mrestrict_eq ASEGS0 Hx w FULL _ (avoid_x _ _ Hav)). exact Hr.
  Qed.

  (* [comment removed for export] *)
  Theorem ent_xcells : xc_chk cs = true ->
    Forall (fun c : Z * nat * Z => rdn ASEGS0 MV (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (word_to_le_bytes (snd (fst c)) (Z_to_bv 64 (snd c)))) XC9K.
  Proof.
    intros CHKX. unfold xc_chk in CHKX. rewrite forallb_forall in CHKX. apply Forall_forall. intros c Hin.
    pose proof (art_lit1 sp brk0 rdraw argv envp uid hw fs Hsp Hva E cs R FULL model c HC (CHKX c Hin)) as CELL. unfold ArtMem.cell in CELL.
    destruct ent_lz as (HOFF & _).
    rewrite rdn_mrestrict_eq; [exact CELL|].
    intros k Hk. destruct (Hx (woff (Z_to_bv 64 (fst (fst c))) k)) eqn:Hh; [exfalso | reflexivity].
    pose proof (HOFF _ Hh) as X. clear - Hin Hk X. unfold XC9K in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [subst c; cbn [fst snd] in *; do 8 (destruct k as [|k]; [exfalso; lazymatch type of X with find_segment ?S ?a ?n = None =>
        assert (Hs : match find_segment S a n with Some _ => true | None => false end = true) by (vm_compute; reflexivity); rewrite X in Hs; discriminate Hs end|]); lia|]).   (* [comment removed for export] *) destruct Hin.
  Qed.

  Lemma val_auxp : edenot E KE_AUXP = Z_to_bv 64 (usp + 8 * envc + 40).
  Proof.
    destruct lib_chk_parts as (_ & _ & _ & _ & LN & _). destruct ent_vals2 as (U1 & U2 & _ & U0). pose proof sp_rng.
    apply word_of_u. remember (bv_unsigned (edenot E KE_AUXP)) as x eqn:Ex. LINEQ KE_AUXP LN H0. rewrite <- Ex in H0. lia.
  Qed.

  Theorem ent_libcells : exists tid : word,
    1 <= bv_unsigned tid <= 4194303
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x673c38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x673c38))
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x673c58) 4 = Some (word_to_le_bytes 4 tid)
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x673cd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x693fc8))
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x693f98) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * envc + 40))).
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

  (* [comment removed for export] *)
  Definition auxv_list (uidz rnd hwz : Z) : list Z := [3; 0x10040; 4; 56; 5; 11; 16; hwz; 6; 4096; 11; uidz; 12; uidz; 23; 0; 25; rnd; 0; 0].
  Theorem ent_auxv : exists uidz rnd hwz : Z,
    (forall j, (j < 20)%nat ->
       rdn ASEGS0 FULL (Z_to_bv 64 (usp + 8 * envc + 40 + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (nth j (auxv_list uidz rnd hwz) 0))))
    /\ 0 <= uidz < 2 ^ 32 /\ 0 <= hwz < 2 ^ 64 /\ usp <= rnd /\ rnd + 16 <= 2 ^ 64.
  Proof.
    destruct lib_chk_parts as (_ & _ & _ & _ & _ & KA & KU).
    destruct stk_chk_parts as (_ & LA & LR & (bi & CB)).
    destruct (hbi_vals ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC)
      as (_ & _ & _ & _ & _ & _ & U4 & _).
    destruct ent_vals2 as (V1 & V2 & _ & V0). pose proof sp_rng as SR. pose proof wsb_eq as WE.
    destruct (bsb_ge APH0 sp rdraw argv envp uid hw) as [BG _].
    assert (UA : uE E KE_AUX = usp + 16 + 8 * envc).
    { unfold uE. remember (bv_unsigned (edenot E KE_AUX)) as s0 eqn:Es. LINEQ KE_AUX LA H. rewrite <- Es in H. lia. }
    assert (UR : uE E KE_RND = usp + 16 + 8 * envc + 8 * Wsb APH0 sp rdraw argv envp uid hw).
    { unfold uE. remember (bv_unsigned (edenot E KE_RND)) as s0 eqn:Es. LINEQ KE_RND LR H. rewrite <- Es in H. rewrite U4 in H. lia. }
    pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC (kfind_blob16_In _ _ _ _ CB)) as (Hfb & _ & _).
    assert (EL : elenZ E (ELit 16) = 16) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
    rewrite EL in Hfb. destruct Hfb as (FB1 & FB2 & _ & FB4). rewrite hb_estart in FB1, FB2, FB4. fold (uE E KE_RND) in FB1, FB2, FB4.
    assert (AC : Z.of_nat (length argv) = 2) by (rewrite Hargv; reflexivity). rewrite AC in BG. pose proof (Zle_0_nat (length envp)) as EN.
    pose proof (hb_knb ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC KU) as RGU. cbn [kentry_ok edenot] in RGU.
    set (rnd := uE E KE_RND + 184).
    assert (VR : edenot E KE_RNDP = Z_to_bv 64 rnd).
    { unfold KE_RNDP. cbn [edenot]. fold (edenot E KE_RND). rewrite alu_add. unfold v_add. apply bv_eq.
      rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold (uE E KE_RND). rewrite (Z.mod_small 184) by lia. reflexivity. }
    exists (bv_unsigned (ev E 8)), rnd, (bv_unsigned (ev E 9)).
    split; [|split; [lia|]; split; [pose proof (u64_range (ev E 9)); lia|]; split; [unfold rnd; rewrite UR; lia | unfold rnd; lia]].
    (* [comment removed for export] *)
    assert (CELL : forall off e, In (off, e) AUXV_EXP ->
               rdn ASEGS0 FULL (Z_to_bv 64 (usp + 16 + 8 * envc + off)) 8 = Some (word_to_le_bytes 8 (edenot E e))).
    { intros off e Hin.
      destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model KE_AUX off 8 e HC (KA off e Hin))
        as (_ & Hf & Hr & _).
      rewrite (hb_adenot E _ _ Hf), hb_estart in Hr. fold (uE E KE_AUX) in Hr. rewrite UA in Hr. exact Hr. }
    intros j Hj.
    assert (EV : forall n, edenot E (EVar n) = Z_to_bv 64 (bv_unsigned (ev E n))) by (intros n; cbn [edenot]; symmetry; apply Z_to_bv_bv_unsigned).
    do 20 (destruct j as [|j];
           [ match goal with |- rdn _ _ (Z_to_bv 64 (_ + 8 * Z.of_nat ?k)) 8 = _ =>
               let o := eval cbv in (24 + 8 * Z.of_nat k) in
               let e := eval cbv in (nth k (map snd AUXV_EXP) (ELit 0)) in
               pose proof (CELL o e ltac:(unfold AUXV_EXP, AUX_OFFS, KE_RNDP; cbn [combine In]; tauto)) as X end;
             cbn [nth auxv_list]; rewrite ?EV, ?VR in X; cbn [edenot] in X;
             match type of X with rdn _ _ (Z_to_bv 64 ?a) _ = _ => match goal with |- rdn _ _ (Z_to_bv 64 ?b) _ = _ => replace b with a by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) end end;
             exact X |]).
    lia.
  Qed.
End Entry.
