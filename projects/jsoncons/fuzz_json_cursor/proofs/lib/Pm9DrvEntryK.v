(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free, the reserved-interval ledger, the nine-byte string read-ahead, the rseq-dependent auxv): changed AH, CHKD, CHKLIB and 40 more; added DRV_WINDOW, Hapc, Hbrk and 45 more; removed AUXV_EXP, AUX_OFFS, KE_AUX and 10 more; internal commit ids in comments replaced by public commits or removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Pm9DefsK Pm9PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK
  Pm9HandoffK Pm9ArtCellsK.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface HeapIfaceA ArtBridge CatExec ArgvEnv FileSim MemSplit RefLayout MuslStrlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* LAYOUT, OLD BESIDE NEW.  Every address this file used to spell out as a linear
   form over the plan's variables is now the plan's OWN expression, from
   [AsanPlanCoreK] (APCK below).  The point is not brevity: a hand-written copy of
   the layout silently keeps the pre-revision one, which is what broke this file.
   Reading the addresses off the plan means the checker and the driver cannot
   disagree about where the auxv is.

     OLD local definition                     NEW plan expression
     KE_ENVP = sp + 8*argc + 16               e_envp                       (APCK:211)
     KE_AUX  = sp + 8*argc + 8*envc           e_auxv, offsets less 24      (APCK:212)
       (the auxv base MINUS 24: every use of KE_AUX carried a +24 offset)
     KE_AUXP = KE_AUX + 24                    e_auxv
     KE_RND  = KE_AUX + 8*V_W                 -- gone; the pad moved
     KE_RNDP = KE_RND + 184                   e_atrandom rz                (APCK:231)
     KE_P0   = sp + 8*argc + 8*envc + 184     e_str0 rz                    (APCK:232)
     KE_P1X  = KE_P0 + L0 + 1                 e_str1 rz                    (APCK:233)
     KE_P1   = (1 <u argc) * KE_P1X           e_argv1w rz                  (APCK:2968)

   The 184 was the old 160-byte auxv plus the 24-byte argc/NULL/NULL struct, with
   the strings immediately above it.  At the revision the auxv is 27 pairs, or 29
   under CONFIG_RSEQ ([StackLayout.auxv_count]), the sixteen AT_RANDOM bytes sit at
   the top of the HEAD, and the strings are at the top of the stack VMA.  So the
   old formula is not stale, it is FALSE -- [AsanInitK:174-186] says the same of
   [V_W], which changed meaning as well as value.

   [rz] is the run's CONFIG_RSEQ flag as 0 or 1 ([APCK.rseq_z]).  It is a parameter
   of every check below that reads the auxv's size, and the size itself is NEVER a
   literal: it travels as [APCK.AUXSZ rz = 432 + 32*rz], tied to the model by the
   hypothesis-free [APCK.AUXSZ_of] (APCK:217-222), so each lemma here holds at both
   auxv sizes with no kernel hypothesis. *)

Definition KE_SPK (k : Z) : expr := EAlu ALU_ADD e_sp0 (ELit k).

Definition DRV_REGS : list (Z * expr) :=
  [(1, ELit 0x134bcc); (2, KE_SPK (-48)); (3, ELit 0x10800); (4, ELit 0x691d90); (8, KE_SPK 8); (9, EVar 1); (10, EVar 1); (11, KE_SPK 8);
   (12, e_envp); (18, ELit 0xaf0a4); (19, e_envp); (20, ELit 0); (21, ELit 0); (22, ELit 0); (23, ELit 0); (24, ELit 0); (25, ELit 0);
   (26, ELit 0); (27, ELit 0)].

Definition opt_eqb (o : option expr) (e : expr) : bool := match o with Some v => expr_eqb v e | None => false end.
Definition img_cover (k : list kentry) (lo hi : Z) : bool :=
  existsb (fun K => match K with KImg l h => (l <=? lo) && (hi <=? h) | _ => false end)%bool k.

Definition DRV_IMG : list (Z * Z) := [(0x10000, 0x156568); (0x156584, 0x15a640); (0x68034a, 0x691cc0); (0x6b2058, 0x6b2088); (0x6b2100, 0x6b2104)].

(* THE ZERO WINDOW, old beside new:
     OLD  kfind_wr (kn cs) e_sp0 (-8388608) = Some (ELit 8388608)
     NEW  the same two numbers at 6144513.
   The 8 MiB width is FALSE at the revision, not stale: [PropExec.wrap_mem]
   zero-fills down to [Run.stack_window_lo kb mbase draw], which is strictly above
   [sp - 8388608] on every run because [ed_top] is strictly above [sp].  6144513 is
   [StoreOk.stack_window_depth]; the plan's own initial knowledge already carries it
   (APCK:3480-3495) and [AsanInitK.stack_window_ok] proves it. *)
Definition DRV_WINDOW : Z := 6144513.

Definition drv_chk (rz : Z) (cs : acs) : bool :=
  (Z.eqb (pc cs) 0xaf0a4
   && forallb (fun p => expr_eqb (sr_get (s_regs (a_ss cs)) (Z_to_bv 5 (fst p))) (snd p)) DRV_REGS
   && lin_nowrapR (kn cs) e_sp0 && lin_nowrapR (kn cs) (KE_SPK (-48)) && lin_nowrapR (kn cs) (KE_SPK 8) && lin_nowrapR (kn cs) e_envp
   && lin_nowrapR (kn cs) (e_str0 rz) && lin_nowrapR (kn cs) (e_str1 rz)
   && opt_eqb (kfind_word (kn cs) e_sp0 0 8) (EVar 1) && opt_eqb (kfind_word (kn cs) e_sp0 8 8) (e_str0 rz)
   && opt_eqb (kfind_word (kn cs) e_sp0 16 8) (e_argv1w rz)
   && opt_eqb (kfind_wr (kn cs) e_sp0 (- DRV_WINDOW)) (ELit DRV_WINDOW)
   && match kfind_word (kn cs) (ELit 0) 0x6b1dd0 8 with Some v => opt_eqb (kfind_word (kn cs) (ELit 0) 0x691d80 8) v | None => false end
   && forallb (fun r => img_cover (kn cs) (fst r) (snd r)) DRV_IMG
   && match a_fd cs with FdStd => true | _ => false end)%bool.

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

(* THE AUXV, old beside new.  This is the substance of the port.

     OLD  AUX_OFFS := [24; 32; ...; 176], twenty CONTIGUOUS eight-byte slots
          relative to KE_AUX -- the whole of a ten-pair vector -- and
          AUXV_EXP := combine AUX_OFFS [3; 0x10040; 4; 56; 5; 11; 16; hw; 6; 4096;
                                        11; uid; 12; uid; 23; 0; 25; rnd; 0; 0].
     INTERIM AUXV_EXP rz := the ten pairs the pre-spine plan
          claimed, at their [auxv_entries] indices.  DELETED with [auxw_eq]: its only
          value-reading consumer was [ent_auxv] (option D).
     NEW  the plan's OWN record of what it claims, [APCK.aux_key_claimed] /
          [APCK.aux_val_claimed], which [init_kn_with] is built from: every
          pair's key, every value but pairs 1..9's.  So the checks below cannot drift
          from the plan, and [APCK.aux_partition] says every auxv word is either one
          of these or an [argH0] hole -- which is what [ent_stack_defined] needs. *)
(* the two words of auxv pair [i]: its key at [16*i], its value at [16*i + 8], both
   based at [e_auxb = split_lit e_auxv], exactly as [APCK.auxk]/[auxv_val] lay them down *)
Definition aux_key_off (i : Z) : Z := snd e_auxb + 16 * i.
Definition aux_val_off (i : Z) : Z := snd e_auxb + 16 * i + 8.
Definition auxk_present (k : list kentry) (i : Z) : bool := is_some (kfind_word k (fst e_auxb) (aux_key_off i) 8).
Definition auxv_present (k : list kentry) (i : Z) : bool := is_some (kfind_word k (fst e_auxb) (aux_val_off i) 8).

(* The AT_RANDOM block is the plan's [atr_entry rz] (APCK:3509): a sixteen-byte blob
   at [e_atrandom rz] under blob index [K_RND].  It WAS a blob at [KE_RND + 184],
   the auxv's end plus the pad, with the strings below it. *)
Definition stk_chk (rz : Z) (cs : acs) : bool :=
  (forallb (fun p => auxk_present (kn cs) (fst p)) (aux_key_claimed rz)
   && forallb (fun p => auxv_present (kn cs) (fst p)) (aux_val_claimed rz ASAN0)
   && lin_nowrapR (kn cs) e_auxv && lin_nowrapR (kn cs) (e_atrandom rz)
   && is_some (kfind_blob16 (kn cs) (fst (e_atrb rz)) (snd (e_atrb rz)))
   (* NEW, and needed by every string address: the ranges of the two plan
      variables the revision added or changed.  [V_W] is the arch_align_stack pad
      in BYTES (at most 4095 plus an alignment remainder below 16) and [V_G] is
      [block_items argv envp mod 2].  Both are entries of [APCK.init_kn_with]
      (APCK:3478); witnessing them here is how [wg_range] gets its bounds, the way
      [lib_chk] already witnesses the uid range for [ent_libcells].  The old file
      needed neither: [V_G] did not exist, and [V_W] was a count of string words
      that no address of its depended on. *)
   && existsb (kentry_eqb (KRange (EVar V_W) 0 4110)) (kn cs)
   && existsb (kentry_eqb (KRange (EVar V_G) 0 1)) (kn cs))%bool.

Definition lib_chk (rz : Z) (cs : acs) : bool :=
  (opt_eqb (kfind_word (kn cs) (ELit 0) 0x691cc8 8) (ELit 0x691cc8)
   && match kfind_word (kn cs) (ELit 0) 0x691ce8 4 with Some v => existsb (kentry_eqb (KRange v 1 4194303)) (kn cs) | None => false end
   && opt_eqb (kfind_word (kn cs) (ELit 0) 0x691d60 8) (ELit 0x6b2058)
   && opt_eqb (kfind_word (kn cs) (ELit 0) 0x6b2028 8) e_auxv
   && lin_nowrapR (kn cs) e_auxv
   (* DROPPED, old beside new: [&& forallb (auxw_eq (kn cs)) (AUXV_EXP rz)] -- the auxv
      VALUES, read only by [ent_auxv], which option D deleted.  The __auxv cell above
      (0x6b2028 = e_auxv) is TRUE at the revision and is kept: the base did not move. *)
   && existsb (kentry_eqb (KRange (EVar V_UID) 0 4294967294)) (kn cs))%bool.

Definition XC9K : list (Z * nat * Z) :=
  [(7020544, 4%nat, 0); (7020579, 1%nat, 0); (7020016, 8%nat, 7020024); (7020008, 4%nat, 1); (7020032, 8%nat, 1266496); (7020288, 8%nat, 649988); (7020004, 4%nat, 0); (7020024, 8%nat, 0);
   (7021976, 8%nat, 0); (7020000, 1%nat, 0)].
Definition xc_chk (cs : acs) : bool := forallb (chk_lit1 (kn cs)) XC9K.

Lemma all_andb_split : forall a b, (a && b)%bool = true -> a = true /\ b = true.
Proof. intros a b H. apply andb_prop in H. exact H. Qed.

Section Entry.
  (* THE SECTION'S PARAMETERS, old beside new.
       OLD  sp brk0 rdraw argv envp uid hw fs, with Hsp Hva Hve Hfit.
       NEW  the launch's whole input, as [AsanInitK]'s own Section takes it at the
            revision: [State.mkProcInput_full] now has twenty places, and
            [SINV0]/[argH0] are instantiated at all of them.
     [ifs] is the filesystem the input carries and [fs] is the plan's FS0; they are
     two different things and were one before.  The list below is copied from
     [HandoffBridgeK]'s Section Image, which instantiates the SAME [SINV0] and
     [argH0], so the two cannot drift apart. *)
  Variables (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)).
  Variables (ifs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue).
  Variables (nofile sigmask : word) (abrt : bool) (urnd : InputStream) (tmp0 : Fs.Fs).
  Variables (kb : KernelBuild) (execfn : list byte) (sdf : bool) (apc : N) (fs : Fs.Fs).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  (* KEPT, not deleted: [entry_stack_fits] is still [Run.v]'s and still the fourth
     conjunct of [valid_entry_va], so a caller that has it goes on passing it.
     What changed is its MEANING, so nothing below uses it as a bound on the block
     or on where a string ends; those come from [Hlau] through the RefLayout and
     CatExec lemmas instead. *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN0.
  #[local] Notation INP := (AsanInitK.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  (* The run's CONFIG_RSEQ flag, and the plan's 0-or-1 form of it.  Taken from THIS
     launch's own kernel, never pinned to [default_kernel]: [Run.valid_input] leaves
     the flag free, so a lemma that pinned it would not cover the input the
     published statement quantifies over. *)
  #[local] Notation rseq := (kb_rseq (in_kernel INP)).
  #[local] Notation RZ := (rseq_z rseq).

  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  Let AH := argH0_high sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc Hsp Hva.

  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.

  Variable cs : acs.
  Hypothesis CHK0 : as0_chk cs = true.
  Hypothesis CHKD : drv_chk RZ cs = true.
  Hypothesis BUD_le : a_eager cs + a_abytes cs + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
                   + (Z.of_nat (length (segments_reserved ASEGS0) + n_resx ASAN0 + length (a_maps cs)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis HC : CSOK E cs R FULL model.

  #[local] Notation A0 := (as0_A0 EXTRA cs E).
  #[local] Notation Hx := (ahid A0 model).
  #[local] Notation MV := (mrestrict Hx FULL).
  #[local] Notation HIDK := (hid ASAN0 argH E cs model).
  #[local] Notation usp := (bv_unsigned sp).
  (* THE BLOCK AND ITS STRING BAND, in THIS Section's vocabulary.  NEW.
     [HandoffBridgeK] has a [utop] notation, but it lives inside its Section Image: the
     notation does not escape it.  The band is restated here, and every [argH] region is
     reached through AsanInitK's navigation lemmas ([argH0_argblock] .. [argH0_strings]).
     [SIMGx] IS [build_stack_bytes] at 75d69e00 ([PropExec.entry_stack_image_block]),
     so the old [SIMGx]/[LBx] pair is now one list; [LBx] is kept as its length. *)
  #[local] Notation utop := (bv_unsigned (ed_top rdraw)).
  #[local] Notation STRLO := (usp + Z.of_nat (cat_string_off rseq sp (ed_top rdraw) argv envp execfn)).
  #[local] Notation SIMGx := (entry_stack_image INP mbase APH0 (Z_to_bv 64 (Z.of_N apc)) sp rdraw).
  #[local] Notation LBx := (Z.of_nat (length (entry_stack_image INP mbase APH0 (Z_to_bv 64 (Z.of_N apc)) sp rdraw))).

  (* HandoffBridgeK's Section Image lemmas are generalised over exactly the Section
     variables and hypotheses their proofs use, which nobody can count from the text,
     so every call below is [eapply X; sec] rather than positional. *)
  Local Ltac sec := first [ eassumption | exact asan0_in_hull | exact asan0_hull_ok | exact asan0_img_facts ].

  Lemma drv_chk_parts :
    pc cs = 0xaf0a4
    /\ (forall r e, In (r, e) DRV_REGS -> sr_get (s_regs (a_ss cs)) (Z_to_bv 5 r) = e)
    /\ lin_nowrapR (kn cs) e_sp0 = true /\ lin_nowrapR (kn cs) (KE_SPK (-48)) = true /\ lin_nowrapR (kn cs) (KE_SPK 8) = true
    /\ lin_nowrapR (kn cs) e_envp = true /\ lin_nowrapR (kn cs) (e_str0 RZ) = true /\ lin_nowrapR (kn cs) (e_str1 RZ) = true
    /\ kfind_word (kn cs) e_sp0 0 8 = Some (EVar 1) /\ kfind_word (kn cs) e_sp0 8 8 = Some (e_str0 RZ)
    /\ kfind_word (kn cs) e_sp0 16 8 = Some (e_argv1w RZ)
    /\ kfind_wr (kn cs) e_sp0 (- DRV_WINDOW) = Some (ELit DRV_WINDOW)
    /\ (exists v, kfind_word (kn cs) (ELit 0) 0x6b1dd0 8 = Some v /\ kfind_word (kn cs) (ELit 0) 0x691d80 8 = Some v)
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
    - destruct (kfind_word (kn cs) (ELit 0) 0x6b1dd0 8) as [v|]; [|discriminate]. exists v. split; [reflexivity | apply OE; assumption].
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

  (* [HandoffBridgeK.hbi_vals] / [hbi_sp0] at this launch, restated so the rest of
     the file reads them by name.  OLD: positional calls over the eight-place
     Section ([hbi_vals ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva
     Hve Hfit E cs R FULL model HC]), which the 22-place Section Image no longer
     accepts.  Slot 4 is [Wpad] and slot 11 [Gap], written out here by their bodies
     so that nothing reaches into Section Image's definitions. *)
  Lemma ent_hbi :
    VZ E 0 = usp / 32768 /\ VZ E 6 = (usp mod 4096) / 16
    /\ VZ E 1 = Z.of_nat (length argv) /\ VZ E 2 = Z.of_nat (length envp)
    /\ VZ E 3 = Z.of_nat (length (nth 0 argv [])) /\ VZ E 7 = Z.of_nat (length (nth 1 argv []))
    /\ VZ E 4 = Z.of_nat (block_pad_len rseq sp (ed_top rdraw) argv envp execfn)
    /\ VZ E 5 = bv_unsigned brk0 / 4096 /\ ev E 8 = uid
    /\ ev E 9 = hw /\ VZ E 10 = (usp mod 32768) / 4096
    /\ VZ E 11 = Z.of_nat (block_items argv envp mod 2).
  Proof. eapply hbi_vals; sec. Qed.

  Lemma ent_sp0 : 32768 * VZ E 0 + 16 * VZ E 6 + 4096 * VZ E 10 = usp.
  Proof. eapply hbi_sp0; sec. Qed.

  Lemma ent_vals : VZ E 1 = Z.of_nat (length argv) /\ VZ E 2 = Z.of_nat (length envp) /\ VZ E 3 = Z.of_nat (length (nth 0 argv []))
                   /\ 32768 * VZ E 0 + 16 * VZ E 6 + 4096 * VZ E 10 = usp.
  Proof. destruct ent_hbi as (_ & _ & U1 & U2 & U3 & _). pose proof ent_sp0 as U0. auto. Qed.

  Lemma sp0_val : uE E e_sp0 = usp.
  Proof.
    destruct drv_chk_parts as (_ & _ & L1 & _). destruct ent_vals as (_ & _ & _ & U0).
    unfold uE. remember (bv_unsigned (edenot E e_sp0)) as s0 eqn:Es. LINEQ e_sp0 L1 H. rewrite <- Es in H. lia.
  Qed.

  Lemma sp_rng : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0.
  Proof. destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in *. lia. Qed.

  Lemma ent_binv : BInv ASEGS0 (vm_maps (m_vmmaps model)) (vm_reserved (m_vmmaps model)) (vm_noaccess (m_vmmaps model))
                        (uE E e_sp0 - 8388608) (as0_BASE EXTRA cs) BUDGET [] A0 FULL model.
  Proof. eapply as0_binv_main; sec. Qed.

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

  Variables a0s path : list byte.
  Hypothesis Hargv : argv = [a0s; path].
  #[local] Notation envc := (Z.of_nat (length envp)).
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
  Lemma val_envp : edenot E e_envp = Z_to_bv 64 (usp + 32).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & L4 & _). destruct ent_vals2 as (U1 & _ & _ & U0).
    apply word_of_u. remember (bv_unsigned (edenot E e_envp)) as x eqn:Ex. LINEQ e_envp L4 H0. rewrite <- Ex in H0. lia.
  Qed.

  (* WHY THESE TWO CASE-SPLIT ON THE FLAG, and why that is the rule applied rather
     than broken.  [LINEQ] reads a linear form out of an expression with
     [eval vm_compute in (lin_of ...)], which needs the expression's literals to BE
     numerals.  [e_str0 rz] carries [ELit (AUXSZ rz)], and [AUXSZ RZ] is not closed
     here: [RZ] is [rseq_z (kb_rseq (in_kernel INP))] and [Run.valid_input] leaves
     that flag free.  Splitting gives [vm_compute] a closed 432 or 464 in each
     branch while the STATEMENT stays parametric in [RZ], so the lemma still holds
     at both auxv sizes and no kernel hypothesis enters.  This is the third part of
     the stream's no-literal rule -- a proof may case-split on [kb_rseq] and use
     closed arithmetic in each branch -- not a violation of its first. *)
  Ltac rz_split Ers := destruct (kb_rseq (in_kernel INP)) eqn:Ers; cbn [rseq_z AUXSZ] in *.

  (* STATEMENT CHANGED, old beside new:
       OLD  edenot E KE_P0  = Z_to_bv 64 (usp + 8*envc + 200)
       NEW  edenot E (e_str0 RZ) = Z_to_bv 64 (usp + 8*envc + 488 + 32*RZ + 8*(VZ E 11) + VZ E 4)
     The 200 was 8*argc + 184 at argc = 2, the 184 being the old 160-byte auxv plus
     the 24-byte struct, with the strings immediately above.  The new right-hand
     side is [STR0]: [e_auxv] (usp + 8*envc + 40) + [AUXSZ RZ] (432 + 32*RZ) + the
     STACK_ROUND gap 8*G + the sixteen random bytes + the arch_align_stack pad W.
     [VZ E 11] is G and [VZ E 4] is W ([HandoffBridgeK.hbi_vals], which gives them
     as [Gap] and [Wpad]).  The old right-hand side is FALSE, not stale. *)
  Lemma val_p0 : edenot E (e_str0 RZ)
                 = Z_to_bv 64 (usp + 8 * envc + 488 + 32 * RZ + 8 * VZ E 11 + VZ E 4).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & L5 & _). destruct ent_vals2 as (U1 & U2 & _ & U0).
    pose proof sp_rng.
    apply word_of_u. remember (bv_unsigned (edenot E (e_str0 RZ))) as x eqn:Ex.
    rz_split Ers; [ LINEQ (e_str0 1) L5 H0 | LINEQ (e_str0 0) L5 H0 ];
      rewrite <- Ex in H0; lia.
  Qed.

  (* STATEMENT CHANGED, old beside new:
       OLD  edenot E KE_P1X = Z_to_bv 64 (usp + 8*envc + L0 + 201)
       NEW  edenot E (e_str1 RZ) = val_p0's right-hand side + L0 + 1
     [e_str1 = e_str0 + L0 + 1] is unchanged in shape; only [e_str0] moved. *)
  Lemma val_p1x : edenot E (e_str1 RZ)
                  = Z_to_bv 64 (usp + 8 * envc + 489 + 32 * RZ + 8 * VZ E 11 + VZ E 4 + L0).
  Proof.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & L6 & _). destruct ent_vals2 as (U1 & U2 & U3 & U0).
    pose proof sp_rng.
    apply word_of_u. remember (bv_unsigned (edenot E (e_str1 RZ))) as x eqn:Ex.
    rz_split Ers; [ LINEQ (e_str1 1) L6 H0 | LINEQ (e_str1 0) L6 H0 ];
      rewrite <- Ex in H0; lia.
  Qed.
  Lemma val_argc : edenot E (EVar 1) = Z_to_bv 64 2.
  Proof. destruct ent_vals2 as (U1 & _). apply word_of_u. exact U1. Qed.

  (* The two NEW plan variables' ranges, which every address above needs and the
     pre-revision file had no use for.  Both are entries of the plan's own initial
     knowledge, [APCK.init_kn_with]: [KRange (EVar V_W) 0 4110] and
     [KRange (EVar V_G) 0 1] (APCK:3478).  4110 is not a magic number: it is
     [arch_align_stack]'s draw, at most 4095, plus the alignment remainder below 16
     ([Run.launch_sp_lo] / [Run.launch_sp_hi]); G is [block_items argv envp mod 2].

     Taken the way this file already takes the thread-id range in [ent_libcells] --
     a check witnesses the [KRange] entry and [hb_knb] turns it into the bound --
     rather than re-derived from [Hlau].  That keeps the argument in one place: if
     the plan's ranges move, these move with them.

     An earlier draft of this lemma read the two values off [hbi_vals] and then
     bounded the pad with a lemma called [block_pad_len_le].  THERE IS NO SUCH
     LEMMA: `git grep -l block_pad_len_le -- projects/jsoncons/fuzz_json_cursor`
     returned one file, and that file was this one -- the line I had just written.
     A hit count of one is not a hit when the one is your own text.

     The two witnesses are arguments rather than uses of [CHKS], so that this lemma
     need not sit below the [stk_chk] hypothesis. *)
  Lemma wg_range :
    existsb (kentry_eqb (KRange (EVar V_W) 0 4110)) (kn cs) = true ->
    existsb (kentry_eqb (KRange (EVar V_G) 0 1)) (kn cs) = true ->
    (0 <= VZ E 4 <= 4110) /\ (0 <= VZ E 11 <= 1).
  Proof.
    intros HWk HGk.
    pose proof (hb_knb ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC HWk) as RW.
    pose proof (hb_knb ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC HGk) as RG.
    cbn [kentry_ok edenot] in RW, RG. unfold V_W, V_G in *. split; [exact RW | exact RG].
  Qed.

  (* [e_argv1w rz = (1 <u V_ARGC) * e_str1 rz] ([APCK:2968]), which is [KE_P1]'s
     shape with the new string address inside it.  The [argc = 2] discharge of the
     guard is unchanged; only the value it multiplies moved. *)
  Lemma val_p1 :
    existsb (kentry_eqb (KRange (EVar V_W) 0 4110)) (kn cs) = true ->
    existsb (kentry_eqb (KRange (EVar V_G) 0 1)) (kn cs) = true ->
    edenot E (e_argv1w RZ)
    = Z_to_bv 64 (usp + 8 * envc + 489 + 32 * RZ + 8 * VZ E 11 + VZ E 4 + L0).
  Proof.
    intros HWk HGk.
    unfold e_argv1w. cbn [edenot]. fold (edenot E (e_str1 RZ)). rewrite val_p1x. apply word_of_u.
    rewrite u_mul64, u_sltu64. destruct ent_vals2 as (U1 & _). unfold VZ in U1.
    (* [V_ARGC] is slot 1; read the guard's operand off [ent_vals2] *)
    unfold V_ARGC. cbn [edenot] in *. rewrite U1.
    rewrite (u64_lit 1) by lia. change (1 <? 2) with true. cbv iota.
    pose proof sp_rng. pose proof (Zle_0_nat (length envp)). pose proof (Zle_0_nat (length a0s)).
    pose proof (rseq_z_range (kb_rseq (in_kernel INP))) as HRZ.
    (* W is the arch_align_stack pad, at most 4110, and G is 0 or 1; both from the
       plan's own KRange entries, through [wg_range]. *)
    destruct (wg_range HWk HGk) as [HW HG].
    assert (Hb : 0 <= usp + 8 * envc + 489 + 32 * RZ + 8 * VZ E 11 + VZ E 4 + L0 < 2 ^ 64).
    { pose proof Hve as [Hle _]. pose proof Hva as (_ & _ & Hfa & _). rewrite Hargv in Hfa. inversion Hfa as [|x l Hx _]; subst. lia. }
    rewrite u64_lit by exact Hb. rewrite Z.mul_1_l. apply Z.mod_small. exact Hb.
  Qed.

  Lemma ent_reg : forall r e, In (r, e) DRV_REGS -> getr R (Z_to_bv 5 r) = edenot E e.
  Proof.
    intros r e Hin. destruct drv_chk_parts as (_ & HRg & _). rewrite <- (HRg r e Hin).
    exact (hb_reg ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC).
  Qed.

  Definition DRV_REGV : list (Z * Z) :=
    [(1, 0x134bcc); (2, usp - 48); (3, 0x10800); (4, 0x691d90); (8, usp + 8); (9, 2); (10, 2); (11, usp + 8);
     (12, usp + 32); (18, 0xaf0a4); (19, usp + 32); (20, 0); (21, 0); (22, 0); (23, 0); (24, 0); (25, 0); (26, 0); (27, 0)].

  Theorem ent_regs : forall r v, In (r, v) DRV_REGV -> getr R (Z_to_bv 5 r) = Z_to_bv 64 v.
  Proof.
    intros r v Hin. unfold DRV_REGV in Hin.
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 1 (ELit 0x134bcc)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 2 (KE_SPK (-48))) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_spk48|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 3 (ELit 0x10800)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 4 (ELit 0x691d90)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 8 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_spk8|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 9 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_argc|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 10 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_argc|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 11 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_spk8|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 12 e_envp) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_envp|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 18 (ELit 0xaf0a4)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (ent_reg 19 e_envp) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact val_envp|].
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

  (* STATEMENT CHANGED, old beside new.  The three ADDRESSES are untouched -- argc,
     argv[0] and argv[1] are still the first three words at [sp] -- and the two
     string VALUES move with [e_str0]:
       OLD  .. (usp + 8) = usp + 8*envc + 200
            .. (usp + 16) = usp + 8*envc + L0 + 201
       NEW  .. (usp + 8) = usp + 8*envc + 488 + 32*RZ + 8*(VZ E 11) + VZ E 4
            .. (usp + 16) = the same + L0 + 1
     Takes the two [KRange] witnesses because [val_p1] does; they come from
     [stk_chk], which is hypothesised further down, so passing them keeps this
     lemma above it. *)
  Theorem ent_stack_words :
    existsb (kentry_eqb (KRange (EVar V_W) 0 4110)) (kn cs) = true ->
    existsb (kentry_eqb (KRange (EVar V_G) 0 1)) (kn cs) = true ->
    rdn ASEGS0 MV (Z_to_bv 64 usp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 2))
    /\ rdn ASEGS0 MV (Z_to_bv 64 (usp + 8)) 8
       = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * envc + 488 + 32 * RZ + 8 * VZ E 11 + VZ E 4)))
    /\ rdn ASEGS0 MV (Z_to_bv 64 (usp + 16)) 8
       = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * envc + 489 + 32 * RZ + 8 * VZ E 11 + VZ E 4 + L0))).
  Proof.
    intros HWk HGk.
    destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & K0 & K8 & K16 & _).
    pose proof (ent_stkword 0 _ K0) as H0. pose proof (ent_stkword 8 _ K8) as H8. pose proof (ent_stkword 16 _ K16) as H16.
    rewrite Z.add_0_r, val_argc in H0. rewrite val_p0 in H8. rewrite (val_p1 HWk HGk) in H16. auto.
  Qed.

  (* STATEMENT CHANGED, old beside new:
       OLD  forall d m, 0 <= d -> d + m <= 8388608 ->
              store_ok ASEGS0 MV (Z_to_bv 64 (usp - 8388608 + d)) m = true
       NEW  the same with [DRV_WINDOW] (= 6144513) in all three places.
     The 8 MiB width is FALSE at the revision, not merely stale: [PropExec.wrap_mem]
     zero-fills down to [Run.stack_window_lo kb mbase draw], which is
     [max (ed_top draw - stack_max_size) (mbase + stack_guard_gap_bytes kb)], and
     [ed_top] is strictly ABOVE [sp] on every run, so [stack_window_lo] is strictly
     above [sp - 8388608] and the old conclusion cannot hold at the window's foot.
     6144513 is [StoreOk.stack_window_depth] = [stack_max_size - stack_window_reach],
     the depth [StoreOk.stack_window_lo_valid] guarantees at every kernel build; the
     plan's own initial knowledge already carries it (APCK:3480-3495) and
     [AsanInitK.stack_window_ok] proves it.  A caller that needed the full 8 MiB
     would now be asking for something false; none does. *)
  Theorem ent_window : forall d (m : nat), 0 <= d -> d + Z.of_nat m <= DRV_WINDOW ->
    store_ok ASEGS0 MV (Z_to_bv 64 (usp - DRV_WINDOW + d)) m = true.
  Proof.
    intros d m Hd Hm. destruct drv_chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KW & _).
    destruct (hb_wr_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model e_sp0 (- DRV_WINDOW) _ HC KW)
      as (Hf & HW).
    assert (EL : elenZ E (ELit DRV_WINDOW) = DRV_WINDOW)
      by (unfold elenZ, DRV_WINDOW; cbn [edenot]; apply u64_lit; lia).
    destruct (HW d m Hd ltac:(rewrite EL; exact Hm)) as (Hs & Hav).
    rewrite hb_estart in Hs, Hav. fold (uE E e_sp0) in Hs, Hav. rewrite sp0_val in Hs, Hav.
    replace (usp + - DRV_WINDOW + d) with (usp - DRV_WINDOW + d) in Hs, Hav by ring.
    rewrite (store_ok_mrestrict_eq ASEGS0 Hx m FULL _ (avoid_x _ _ Hav)). exact Hs.
  Qed.

  Theorem ent_guard : exists can : word,
    rdn ASEGS0 MV (Z_to_bv 64 0x6b1dd0) 8 = Some (word_to_le_bytes 8 can) /\ rdn ASEGS0 MV (Z_to_bv 64 0x691d80) 8 = Some (word_to_le_bytes 8 can).
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
    { unfold DRV_IMG in Hin. destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]]; injection Hin as <- <-; unfold in_hull; cbn [img_lo img_hi ASAN0];
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

  (* DELETED, not ported: [wsb_eq].
       OLD  8 * Wsb APH0 sp rdraw argv envp uid hw
            = |build_stack_bytes ..| - 16 - (8*2 + 8*envc + 184)
     Its subject no longer exists.  [Wsb] was the pad in WORDS below the AT_RANDOM
     block, and the whole point of the lemma was to turn [8 * Wsb] back into a byte
     count so that the middle range of [argH] could be spelled.  At the revision
     plan variable 4 is [block_pad_len] in BYTES already ([HandoffBridgeK.Wpad],
     [AsanInitK:174-186]), so there is nothing to multiply by 8, and the middle
     range it served is gone with it (see [ent_strblock] below).  Deleted rather
     than restated: a restatement would be a true sentence about a quantity no
     definition in this tree computes any more. *)

  (* THE BLOCK'S TOP AND LENGTH, from [Hlau] directly.  NEW.  The old file had
     [entry_stack_image_top] and [entry_page_top_within_window] over the seven
     positional arguments; the first no longer exists, and at the revision the image
     ends exactly at the stack VMA's end [ed_top], which [Run.valid_stack_top_va]
     (the first conjunct of [entry_launch_ok_va]) pins page-aligned and at most
     [va_stack_top Sv48 = sp_window_hi = 2^47]. *)
  Lemma ent_top : utop mod 4096 = 0 /\ utop <= 2 ^ 47.
  Proof.
    pose proof Hlau as H. cbn [entry_launch_ok_va] in H. destruct H as ((T1 & T2 & _) & _).
    assert (V : va_stack_top Sv48 = 2 ^ 47) by reflexivity. rewrite V in T2.
    unfold page_size in T1. split; [exact T1 | exact T2].
  Qed.

  Lemma ent_len : LBx = utop - usp.
  Proof. exact (length_entry_stack_image_launch Sv48 INP mbase APH0 (Z_to_bv 64 (Z.of_N apc)) sp brk0 rdraw Hlau). Qed.

  (* [MuslStrlen.bsb_len_lower9]: the argv strings end at least 9 bytes below the
     top -- the [create_init_stack_vma] slot and the exec file name's NUL, plus the
     envp strings and the exec file name, which sit above them. *)
  Lemma ent_bsb_lower : STRLO + Z.of_nat (total_arg_bytes_nat argv) + 9 <= utop.
  Proof.
    pose proof (bsb_len_lower9 INP mbase APH0 (Z_to_bv 64 (Z.of_N apc)) sp rdraw) as H.
    change (in_argv INP) with argv in H. change (in_envp INP) with envp in H. change (in_execfn INP) with execfn in H.
    pose proof ent_len. lia.
  Qed.

  (* argv string [k]'s address, in Z.  Built from global lemmas with explicit
     arguments ([CatExec.cat_argv_ptr_offset], [cat_string_base_offset],
     [word_add_nat_Z2bv], [u_Z2bv_lt]) rather than from [RefLayout.u_cat_argv_ptr],
     whose Section arity is not readable from the text. *)
  Lemma ent_ptr : forall k, (k < length argv)%nat ->
    bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp execfn k) = STRLO + Z.of_nat (total_arg_bytes_nat (firstn k argv)).
  Proof.
    intros k Hk.
    pose proof (cat_string_base_offset Sv48 INP mbase sp brk0 rdraw Hlau) as HB.
    change (in_argv INP) with argv in HB. change (in_envp INP) with envp in HB. change (in_execfn INP) with execfn in HB.
    pose proof ent_bsb_lower as Hlow. destruct ent_top as (_ & T2).
    pose proof (total_arg_bytes_firstn_le k argv) as Hle.
    pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp (ed_top rdraw) argv envp execfn)) as Z0.
    pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat (firstn k argv))) as Z1.
    pose proof (u64_range sp) as R0.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) argv envp execfn k Hk), HB, !word_add_nat_Z2bv.
    rewrite (u_Z2bv_lt (usp + Z.of_nat (cat_string_off rseq sp (ed_top rdraw) argv envp execfn))) by lia.
    rewrite u_Z2bv_lt by lia. reflexivity.
  Qed.

  (* NEW: the plan's string address and CatExec's are the same number.  [STRLO] is
     [usp + cat_string_off], [CatExec.cat_string_off = block_head_size + block_pad_len],
     and [block_head_size] at argc = 2 is [8*(envc + 5) + auxv_size + 8*G + 16]; the
     plan carries G as [VZ E 11] and the pad as [VZ E 4] ([ent_hbi]).  The one flag
     split is [AUXSZ_of]'s, hypothesis-free; the arithmetic is AsanInitK.chead_eq's at
     the hand-off env instead of the initial one. *)
  Lemma ent_str0_off : Z.of_nat (cat_string_off rseq sp (ed_top rdraw) argv envp execfn)
                       = 8 * envc + 488 + 32 * RZ + 8 * VZ E 11 + VZ E 4.
  Proof.
    destruct ent_hbi as (_ & _ & _ & _ & _ & _ & W4 & _ & _ & _ & _ & G11). rewrite W4, G11.
    pose proof (AUXSZ_of rseq) as HA. unfold AUXSZ in HA.
    (* only [length argv] is rewritten: [rseq] itself mentions [argv] (through INP), and
       rewriting it there would split [HA]'s atom from the goal's *)
    assert (LA : length argv = 2%nat) by (rewrite Hargv; reflexivity).
    (* one name per unfold: [block_head_size] only appears once [cat_string_off] has expanded *)
    unfold cat_string_off. unfold block_head_size. unfold block_items. cbv zeta. rewrite LA.
    lia.
  Qed.

  (* NEW: argv[0]'s and argv[1]'s pointers as the words [ent_stack_words] reads at
     [usp + 8] / [usp + 16], so the driver's [p0]/[p1] can be CatExec's
     [cat_argv_ptr (ed_top rdraw) ..] and the string lemmas ([ent_str], [ent_str_hi],
     [ent_str_defined]) apply to them unchanged. *)
  Lemma ent_p0_eq : cat_argv_ptr (ed_top rdraw) argv envp execfn 0
                    = Z_to_bv 64 (usp + 8 * envc + 488 + 32 * RZ + 8 * VZ E 11 + VZ E 4).
  Proof.
    apply word_of_u. rewrite (ent_ptr 0 ltac:(rewrite Hargv; cbn [length]; lia)).
    change (total_arg_bytes_nat (firstn 0 argv)) with 0%nat. rewrite ent_str0_off. lia.
  Qed.
  Lemma ent_p1_eq : cat_argv_ptr (ed_top rdraw) argv envp execfn 1
                    = Z_to_bv 64 (usp + 8 * envc + 489 + 32 * RZ + 8 * VZ E 11 + VZ E 4 + L0).
  Proof.
    apply word_of_u. rewrite (ent_ptr 1 ltac:(rewrite Hargv; cbn [length]; lia)).
    rewrite ent_str0_off. rewrite Hargv. unfold total_arg_bytes_nat. cbn [firstn fold_right]. lia.
  Qed.

  (* [HandoffBridgeK.hbi_argblock] at this launch.  OLD: [hbi_argblock ASEGS0 ASAN0
     APH0 sp rdraw brk0 argv envp uid hw fs E cs R FULL model HC] (positional). *)
  Lemma ent_argblock : forall a : word, argH E a = true ->
    FULL a = wrap_mem INP mbase APH0 (Z_to_bv 64 (Z.of_N apc)) sp rdraw a.
  Proof. intros a Ha. eapply hbi_argblock; sec. Qed.

  (* The string band is in [argH].  OLD: [hbi_argH] (a [reflexivity] restatement of
     [argH0]'s body, deleted) and its second disjunct by [orb] position.  NEW:
     [AsanInitK.argH0_strings], an earlier port's navigation lemma, so a change to
     [argH0]'s disjuncts is absorbed in AsanInitK and nowhere here. *)
  Lemma ent_argH_str : forall x : word, STRLO <= bv_unsigned x < utop -> argH E x = true.
  Proof.
    intros x Hx. pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp (ed_top rdraw) argv envp execfn)) as Z0.
    assert (G1 : uE E e_sp0 <= bv_unsigned x) by (rewrite sp0_val; lia).
    (* AsanInitK's navigation lemmas may also take section hypotheses (as goals before
       their two premises), so the goals are closed by type, not by position *)
    eapply argH0_strings; try exact G1; try exact Hx; eassumption.
  Qed.

  (* STATEMENT CHANGED, old beside new:
       OLD  forall x, usp + 8*envc + 200 <= x < usp + |build_stack_bytes ..| - 16 ->
              MV x = wrap_mem APH0 sp argv envp uid hw rdraw x
       NEW  forall x, STRLO <= x < utop -> MV x = wrap_mem INP mbase APH0 ENT sp rdraw x
     The BAND: the strings used to sit immediately above the auxv, up to sixteen
     bytes below the block's end (AT_RANDOM, then at the top).  They are now at the
     top of the stack VMA, so the band is [STRLO, utop), [argH0]'s string disjunct.
     The old "[-16]" is not an off-by-one: the sixteen bytes it excluded are at the
     other end of the block now.  The MEMORY: [wrap_mem] takes the input, the mmap
     base and the entry at the revision. *)
  Theorem ent_strblock : forall x : word,
    STRLO <= bv_unsigned x < utop ->
    MV x = wrap_mem INP mbase APH0 (Z_to_bv 64 (Z.of_N apc)) sp rdraw x.
  Proof.
    intros x Hxr. pose proof sp_rng as SR.
    pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp (ed_top rdraw) argv envp execfn)) as Z0.
    unfold mrestrict. rewrite (vis_high x ltac:(lia)).
    apply ent_argblock. apply ent_argH_str. exact Hxr.
  Qed.

  (* STATEMENT CHANGED, old beside new:
       OLD  rdn .. (cat_argv_ptr sp argv envp k) .. /\
            bv_unsigned (cat_argv_ptr sp argv envp k) = usp + 8*envc + 200 + |firstn k argv|
       NEW  the pointer is [cat_argv_ptr (ed_top rdraw) argv envp execfn k] (CatExec
            at the revision: string addresses hang from the stack VMA's end), and
            its value is [STRLO + |firstn k argv|].
     The old proof unfolded [auxv_size] to get the 200; that literal is the layout
     the revision changed, and nothing here needs it. *)
  Theorem ent_str : forall k, (k < 2)%nat ->
    rdn ASEGS0 MV (cat_argv_ptr (ed_top rdraw) argv envp execfn k) (length (nth k argv []) + 1) = Some (nth k argv [] ++ [Z_to_bv 8 0])
    /\ bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp execfn k) = STRLO + Z.of_nat (total_arg_bytes_nat (firstn k argv)).
  Proof.
    intros k Hk. pose proof sp_rng as SR.
    assert (Hk0 : (k < length argv)%nat) by (rewrite Hargv; cbn [length]; lia).
    assert (Hk' : (k < length (in_argv INP))%nat) by exact Hk0.
    pose proof (ent_ptr k Hk0) as Hu.
    pose proof ent_bsb_lower as Hlow.
    pose proof (total_arg_bytes_firstn_within argv k Hk0) as Hw.
    pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp (ed_top rdraw) argv envp execfn)) as Z0.
    split; [|exact Hu].
    transitivity (rdn ASEGS0 (stack_to_mem sp SIMGx) (cat_argv_ptr (ed_top rdraw) argv envp execfn k) (length (nth k argv []) + 1)).
    - apply rdn_ext; [destruct ent_top; lia|]. intros x Hxr.
      rewrite ent_strblock by lia. apply wrap_above_sp. lia.
    - exact (read_argv_cstr_k Sv48 ASEGS0 INP mbase APH0 (Z_to_bv 64 (Z.of_N apc)) sp brk0 rdraw k Hlau Hk').
  Qed.

  Hypothesis CHKS : stk_chk RZ cs = true.

  (* STATEMENT CHANGED, old beside new.
       OLD  (forall off, In off AUX_OFFS -> exists v, kfind_word (kn cs) KE_AUX off 8 = Some v)
            /\ lin_nowrapR (kn cs) KE_AUX /\ lin_nowrapR (kn cs) KE_RND
            /\ exists i, kfind_blob16 (kn cs) KE_RND 184 = Some i
       NEW  the per-pair form over the ten CLAIMED indices, both words of each;
            nowrap for [e_auxv] and [e_atrandom RZ]; the blob at [e_atrb RZ]; and
            the two new plan-variable ranges.
     The quantifier changed shape with the layout: the old one ran over a list of
     contiguous OFFSETS because the whole vector was claimed, the new one runs over
     the pairs the plan actually claims, each giving a key word and a value word. *)
  Lemma stk_chk_parts :
    (* the claimed key words and value words, over the plan's own lists (was: per
       pair over the interim [AUXV_EXP RZ], both words of each) *)
    (forall p, In p (aux_key_claimed RZ) -> exists v, kfind_word (kn cs) (fst e_auxb) (aux_key_off (fst p)) 8 = Some v)
    /\ (forall p, In p (aux_val_claimed RZ ASAN0) -> exists v, kfind_word (kn cs) (fst e_auxb) (aux_val_off (fst p)) 8 = Some v)
    /\ lin_nowrapR (kn cs) e_auxv = true /\ lin_nowrapR (kn cs) (e_atrandom RZ) = true
    /\ (exists i, kfind_blob16 (kn cs) (fst (e_atrb RZ)) (snd (e_atrb RZ)) = Some i)
    /\ existsb (kentry_eqb (KRange (EVar V_W) 0 4110)) (kn cs) = true
    /\ existsb (kentry_eqb (KRange (EVar V_G) 0 1)) (kn cs) = true.
  Proof.
    pose proof CHKS as H. unfold stk_chk in H.
    apply andb_prop in H as [H CG]. apply andb_prop in H as [H CW].
    apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [H C2].
    apply andb_prop in H as [CK CV].
    split.
    { intros p Hin. pose proof (proj1 (forallb_forall _ _) CK p Hin) as Hb. unfold auxk_present in Hb.
      destruct (kfind_word (kn cs) (fst e_auxb) (aux_key_off (fst p)) 8) as [v|]; [exists v; reflexivity | discriminate]. }
    split.
    { intros p Hin. pose proof (proj1 (forallb_forall _ _) CV p Hin) as Hb. unfold auxv_present in Hb.
      destruct (kfind_word (kn cs) (fst e_auxb) (aux_val_off (fst p)) 8) as [v|]; [exists v; reflexivity | discriminate]. }
    split; [exact C2|]. split; [exact C3|]. split; [|split; [exact CW | exact CG]].
    destruct (kfind_blob16 (kn cs) (fst (e_atrb RZ)) (snd (e_atrb RZ))) as [i|]; [exists i; reflexivity | discriminate].
  Qed.

  (* STATEMENT CHANGED, old beside new:
       OLD  usp + |SIMGx| <= 2^47 /\ LBx <= |SIMGx| /\ (usp + |SIMGx|) mod 4096 = 0
       NEW  the first and last.  The middle said the Linux block fits inside the
            mapped image with the page tail [entry_slack] above it; at 75d69e00 they
            are the same list, so it is [LBx <= LBx] and is dropped.  The top is
            now [ed_top] itself ([ent_len], [ent_top]), not a page round-up. *)
  Lemma simg_top : usp + LBx <= 2 ^ 47 /\ (usp + LBx) mod 4096 = 0.
  Proof. rewrite ent_len. destruct ent_top as (T1 & T2). replace (usp + (utop - usp)) with utop by ring. auto. Qed.

  (* STATEMENT CHANGED, old beside new -- the string SLACK, Main's ruling (a):
       OLD  bv_unsigned (cat_argv_ptr sp argv envp k) + |argv[k]| + 1 + 16 <= 2^47
       NEW  bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp execfn k) + |argv[k]| + 1 + 9 <= 2^47
     Sixteen bytes past the NUL is FALSE at the revision.  Above argv[1]'s NUL sit
     only the envp strings, the exec file name with its NUL and the eight-byte top
     slot ([StackLayout.string_base_addr] = top - (8 + launch_string_bytes)), and
     [Run.valid_envp] allows envp = [] while [Run.valid_execfn]/[valid_path_name]
     allows a one-byte name ([State.default_execfn] is "a"): ten bytes, then the
     end of the VMA.  Sixteen held in the old layout only because AT_RANDOM sat
     above the strings.  Eight is what is READ, and ASan's region check [chk_pre] needs the read to end at or
     below HIGHEND = 2^47 - 1, hence NINE (the exec file name's NUL gives the ninth byte,
     [MuslStrlen.bsb_len_lower9]): the Diag chain's only string fact is
     [Pm9DiagStrnlen.cstr], [length bs + 9] bytes from the string's start, and
     [Pm9DiagStrK.str_cstr] reads exactly the 8 bytes after the NUL.  In-corpus
     precedent for the 9: [AsanNodesStartXK.v:150], [Pm10MainEntry.main_str_fits]. *)
  Theorem ent_str_hi : forall k, (k < 2)%nat ->
    bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp execfn k) + Z.of_nat (length (nth k argv [])) + 1 + 9 <= 2 ^ 47.
  Proof.
    intros k Hk.
    assert (Hk0 : (k < length argv)%nat) by (rewrite Hargv; cbn [length]; lia).
    rewrite (ent_ptr k Hk0). pose proof ent_bsb_lower as Hlow. destruct ent_top as (_ & T2).
    pose proof (total_arg_bytes_firstn_within argv k Hk0) as Hw. lia.
  Qed.

  Lemma argH_defined : forall x : word, usp <= bv_unsigned x < usp + LBx -> argH E x = true -> FULL x <> None.
  Proof.
    intros x Hx Ha.
    rewrite (ent_argblock x Ha).
    rewrite wrap_above_sp by lia. unfold stack_to_mem.
    replace (usp <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
    replace (bv_unsigned x - usp <? Z.of_nat (length SIMGx)) with true by (symmetry; apply Z.ltb_lt; lia).
    apply nth_error_Some. lia.
  Qed.

  (* NEW: the whole string band is defined, through [argH] rather than through the
     stack-wide [ent_stack_defined], so the string lemmas below do not depend on
     the auxv arm of that lemma. *)
  Lemma ent_band_defined : forall x : word, STRLO <= bv_unsigned x < utop -> FULL x <> None.
  Proof.
    intros x Hx. pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp (ed_top rdraw) argv envp execfn)) as Z0.
    apply argH_defined; [rewrite ent_len; lia | apply ent_argH_str; exact Hx].
  Qed.

  Lemma mr_defined : forall (x : word) b, Mr ASAN0 argH E cs model FULL x = Some b -> FULL x <> None.
  Proof. intros x b H. rewrite (hb_mr_some ASAN0 argH E cs model FULL x b H). discriminate. Qed.

  (* NEW: [block_head_size] at ANY argc, in the plan's variables.  [AsanInitK.chead_eq] is
     the same arithmetic at the initial env.  Argc-general on purpose: [ent_stack_defined]
     below is used by the usage path (Pm9UsageEntryK, argc <> 2) as well, so nothing on its
     path may read [Hargv]. *)
  Lemma ent_chead : Z.of_nat (block_head_size rseq argv envp)
                    = 8 * Z.of_nat (length argv) + 8 * envc + 472 + 32 * RZ + 8 * VZ E 11.
  Proof.
    destruct ent_hbi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G11). rewrite G11.
    pose proof (AUXSZ_of rseq) as HA. unfold AUXSZ in HA.
    unfold block_head_size. unfold block_items. cbv zeta.
    lia.
  Qed.

  (* STATEMENT UNCHANGED; PROOF REWRITTEN for the revision's layout (Main's option 2).
     OLD  seven ranges over a CONTIGUOUS claimed vector: [0,24) the words at sp;
          [24, 8envc+40) argH; [8envc+40, +200) twenty claimed words at KE_AUX;
          strings argH; the last sixteen bytes the AT_RANDOM blob at KE_RND+184.
     NEW  [0,24)                              the three KWords at sp ([KW]);
          [24, EAUX)                          argH0_argblock;
          [EAUX, EAUX + AUXSZ RZ)             word by word: [APCK.aux_partition] says each
                                              auxv word is claimed XOR hidden -- claimed ones
                                              by [KW] from [stk_chk_parts] over
                                              aux_key_claimed / aux_val_claimed, hidden ones
                                              by argH0_auxhole;
          [EAUX + AUXSZ RZ, CHEAD - 16)       STACK_ROUND's gap, argH0_gap;
          [CHEAD - 16, CHEAD)                 the AT_RANDOM blob at [e_atrb RZ];
          [CHEAD, STRLO)                      arch_align_stack's pad, argH0_pad;
          [STRLO, utop)                       the strings, argH0_strings.
     Every [argH0] region is reached through an earlier port's navigation lemmas
     (AsanInitK), never by [orb] position.  Consumer that needs
     the whole range: [HeapIfaceA.astack_ok]'s [defined M sp (ar_stack_top - sp)],
     through Pm9MainPhaseA's [as0_main_phase] and Pm9DrvLib.dinv_stack_defined. *)
  Theorem ent_stack_defined : forall i, 0 <= i < Z.of_nat (length SIMGx) -> FULL (Z_to_bv 64 (usp + i)) <> None.
  Proof.
    (* [AsanInitK.split_u]'s statement and proof at this [E]: the Section lemma takes
       leading AsanInitK Section arguments its proof touches, whose number and order
       the text does not show, so its premises cannot be matched by position *)
    assert (SPU : forall e b k, split_lit e = (b, k) -> 0 <= k -> k <= uE E e -> bv_unsigned (edenot E b) + k = uE E e).
    { intros e b k Hs Hk Hle. clear - Hs Hk Hle. unfold uE in Hle |- *. rewrite (split_lit_denot E e b k Hs) in Hle |- *.
      pose proof (u64_range (edenot E b)) as Rb.
      rewrite Z_to_bv_unsigned in Hle |- *. unfold bv_wrap, bv_modulus in Hle |- *. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hle |- *.
      pose proof (Z.mod_pos_bound (bv_unsigned (edenot E b) + k) (2 ^ 64) ltac:(lia)) as MB.
      destruct (Z_lt_le_dec (bv_unsigned (edenot E b) + k) (2 ^ 64)).
      - rewrite Z.mod_small by lia. reflexivity.
      - exfalso.
        assert ((bv_unsigned (edenot E b) + k) mod 2 ^ 64 = bv_unsigned (edenot E b) + k - 2 ^ 64).
        { replace (bv_unsigned (edenot E b) + k) with ((bv_unsigned (edenot E b) + k - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
          rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
        lia. }
    intros i Hi. pose proof sp_rng as SR. destruct simg_top as (T1 & T2).
    destruct stk_chk_parts as (CK & CV & LA & LR & (bi & CB) & CW & CG).
    destruct (wg_range CW CG) as (WR & GR).
    pose proof (rseq_z_range rseq) as RZR.
    destruct drv_chk_parts as (_ & _ & L1 & _ & _ & _ & _ & _ & K0 & K8 & K16 & _).
    destruct ent_vals as (V1 & V2 & _ & V0).
    pose proof ent_len as LEN. pose proof ent_chead as CHD.
    pose proof ent_bsb_lower as Hlow. pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat argv)) as ZT.
    (* argc-general: no [Hargv] on this path ([ent_vals], not [ent_vals2]) *)
    pose proof (Nat2Z.is_nonneg (length argv)) as AC.
    assert (UX : bv_unsigned (Z_to_bv 64 (usp + i)) = usp + i) by (apply u_small; lia).
    assert (SPV : uE E e_sp0 = usp) by exact sp0_val.
    (* [e_auxv] at this env, and [e_auxb]'s base: [split_lit e_auxv] keeps its literal 24 *)
    assert (UEA : uE E e_auxv = usp + 8 * Z.of_nat (length argv) + 8 * envc + 24).
    { unfold uE. remember (bv_unsigned (edenot E e_auxv)) as s0 eqn:Es. LINEQ e_auxv LA H. rewrite <- Es in H. lia. }
    assert (SKA : snd e_auxb = 24) by (vm_compute; reflexivity).
    assert (SUA : bv_unsigned (edenot E (fst e_auxb)) + snd e_auxb = uE E e_auxv).
    { eapply SPU; [unfold e_auxb; destruct (split_lit e_auxv); reflexivity | rewrite SKA; lia | rewrite SKA, UEA; lia]. }
    rewrite SKA, UEA in SUA.

    (* a claimed word: the [KWord] the know-set holds for it is read through [Mr] *)
    assert (KW : forall b off v d, kfind_word (kn cs) b off 8 = Some v ->
                 (flat E (SA b off) 8 -> estart E (SA b off) = usp + d) -> d <= i < d + 8 -> FULL (Z_to_bv 64 (usp + i)) <> None).
    { intros b off v d Hk Hst Hd.
      destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model b off 8 v HC Hk)
        as (_ & Hf & Hr & _).
      rewrite (hb_adenot E _ _ Hf), (Hst Hf) in Hr.
      apply (rdn_bytes_some ASEGS0 ASAN0 asan0_in_hull FULL _ 8 _ Hr).
      - rewrite UX, u_small by lia. change (Z.of_nat 8) with 8. lia.
      - rewrite UX. unfold in_hull. cbn [img_lo img_hi ASAN0]. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
    (* an [argH0] cell is [wrap_mem]'s, which is defined below the image's top *)
    assert (AHD : argH E (Z_to_bv 64 (usp + i)) = true -> FULL (Z_to_bv 64 (usp + i)) <> None)
      by (apply argH_defined; rewrite UX; lia).
    assert (GS : uE E e_sp0 <= bv_unsigned (Z_to_bv 64 (usp + i))) by (rewrite SPV, UX; lia).

    (* [0, 24): argc, argv[0], argv[1] *)
    destruct (Z_lt_le_dec i 24) as [C1|C1].
    { assert (ST : forall off, flat E (SA e_sp0 off) 8 -> estart E (SA e_sp0 off) = usp + off)
        by (intros off _; rewrite hb_estart; fold (uE E e_sp0); rewrite sp0_val; reflexivity).
      destruct (Z_lt_le_dec i 8); [apply (KW e_sp0 0 _ 0 K0 (ST 0)); lia|].
      destruct (Z_lt_le_dec i 16); [apply (KW e_sp0 8 _ 8 K8 (ST 8)); lia | apply (KW e_sp0 16 _ 16 K16 (ST 16)); lia]. }
    (* [24, EAUX): the argv/envp pointer arrays *)
    destruct (Z_lt_le_dec i (8 * Z.of_nat (length argv) + 8 * envc + 24)) as [C2|C2].
    { apply AHD. eapply argH0_argblock; try exact GS; try eassumption. rewrite UX; lia. }
    (* [EAUX, EAUX + AUXSZ RZ): the auxv, word by word *)
    destruct (Z_lt_le_dec i (8 * Z.of_nat (length argv) + 8 * envc + 24 + (432 + 32 * RZ))) as [C3|C3].
    { set (j := i - (8 * Z.of_nat (length argv) + 8 * envc + 24)).
      assert (JD : j = i - (8 * Z.of_nat (length argv) + 8 * envc + 24)) by reflexivity.
      assert (J16 : j = 16 * (j / 16) + j mod 16) by (apply Z.div_mod; lia).
      pose proof (Z.mod_pos_bound j 16 ltac:(lia)) as M16.
      set (p := j / 16) in *. set (m := j mod 16) in *.
      assert (M8 : m = 8 * (m / 8) + m mod 8) by (apply Z.div_mod; lia).
      pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as R8.
      set (k := m / 8) in *. set (r := m mod 8) in *.
      assert (K01 : k = 0 \/ k = 1) by lia.
      assert (P0 : 0 <= p < 27 + 2 * RZ) by lia.
      destruct (aux_hidden p k) eqn:HH.
      - (* a hidden word: one of pairs 1..9's values *)
        apply AHD. eapply argH0_auxhole; try exact GS; try eassumption. split; [unfold AUXSZ; rewrite UX; lia|].
        rewrite UX.
        match goal with |- aux_hidden ((?z - ?e) / 16) (((?z - ?e) mod 16) / 8) = true =>
          replace (z - e) with j by lia end.
        exact HH.
      - (* a claimed word: [aux_partition] says so *)
        pose proof (aux_partition rseq ASAN0) as AP. rewrite forallb_forall in AP.
        assert (HINP : In p (map Z.of_nat (seq 0 (27 + 2 * Z.to_nat (rseq_z rseq))))).
        { apply in_map_iff. exists (Z.to_nat p). split; [lia | apply in_seq; lia]. }
        specialize (AP p HINP). cbn [forallb] in AP. apply andb_prop in AP as [A0 AP]. apply andb_prop in AP as [A1 _].
        destruct K01 as [Ek|Ek]; rewrite Ek in HH, M8.
        + rewrite HH, xorb_false_r in A0. unfold aux_claimed in A0. rewrite Z.eqb_refl in A0. cbv iota in A0.
          apply existsb_exists in A0 as (pr & Hin & Heq). apply Z.eqb_eq in Heq.
          destruct (CK pr Hin) as (v & Hv). rewrite Heq in Hv.
          apply (KW (fst e_auxb) (aux_key_off p) v (8 * Z.of_nat (length argv) + 8 * envc + 24 + 16 * p) Hv).
          * intros _. rewrite hb_estart. unfold aux_key_off. rewrite SKA. lia.
          * lia.
        + rewrite HH, xorb_false_r in A1. unfold aux_claimed in A1. change (Z.eqb 1 0) with false in A1. cbv iota in A1.
          apply existsb_exists in A1 as (pr & Hin & Heq). apply Z.eqb_eq in Heq.
          destruct (CV pr Hin) as (v & Hv). rewrite Heq in Hv.
          apply (KW (fst e_auxb) (aux_val_off p) v (8 * Z.of_nat (length argv) + 8 * envc + 32 + 16 * p) Hv).
          * intros _. rewrite hb_estart. unfold aux_val_off. rewrite SKA. lia.
          * lia. }
    (* [EAUX + AUXSZ RZ, CHEAD - 16): STACK_ROUND's gap *)
    destruct (Z_lt_le_dec i (Z.of_nat (block_head_size rseq argv envp) - 16)) as [C4|C4].
    { apply AHD. eapply argH0_gap; try exact GS; try eassumption. unfold AUXSZ; rewrite UX; lia. }
    (* [CHEAD - 16, CHEAD): the sixteen AT_RANDOM bytes, the plan's blob *)
    destruct (Z_lt_le_dec i (Z.of_nat (block_head_size rseq argv envp))) as [C5|C5].
    { (* the flag is split ABOVE the [vm_compute] in [LINEQ]; the statement stays in [RZ] *)
      assert (UR : uE E (e_atrandom RZ) = usp + 8 * Z.of_nat (length argv) + 8 * envc + 456 + 32 * RZ + 8 * VZ E 11).
      { unfold uE. remember (bv_unsigned (edenot E (e_atrandom RZ))) as s0 eqn:Es. revert LR Es.
        rz_split Ers; intros LR Es; [LINEQ (e_atrandom 1) LR H | LINEQ (e_atrandom 0) LR H]; rewrite <- Es in H; lia. }
      assert (SUR : bv_unsigned (edenot E (fst (e_atrb RZ))) + snd (e_atrb RZ) = uE E (e_atrandom RZ)).
      { pose proof (e_atrb_off rseq) as EO. unfold AUXSZ in EO.
        eapply SPU; [unfold e_atrb; destruct (split_lit (e_atrandom RZ)); reflexivity | lia | rewrite UR; lia]. }
      pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC (kfind_blob16_In _ _ _ _ CB)) as (Hf & _ & Hb).
      assert (EL : elenZ E (ELit 16) = 16) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
      rewrite EL in Hb. rewrite hb_estart in Hb. rewrite SUR, UR in Hb.
      specialize (Hb (i - (Z.of_nat (block_head_size rseq argv envp) - 16)) ltac:(lia)).
      match type of Hb with context [Z_to_bv 64 ?t] => replace t with (usp + i) in Hb by lia end.
      exact (mr_defined _ _ Hb). }
    (* [CHEAD, STRLO): arch_align_stack's pad *)
    destruct (Z_lt_le_dec i (Z.of_nat (cat_string_off rseq sp (ed_top rdraw) argv envp execfn))) as [C6|C6].
    { apply AHD. eapply argH0_pad; try exact GS; try eassumption. rewrite UX; lia. }
    (* [STRLO, utop): the strings *)
    apply AHD. apply ent_argH_str. rewrite UX. lia.
  Qed.

  (* The page above sp.  STATEMENT UNCHANGED; proof re-pointed: the image now ends
     exactly at the page-aligned [ed_top] ([simg_top]) and is at least eight bytes
     long ([ent_bsb_lower]), so any page boundary [top <= usp + 4096] is inside it.
     OLD proof used [bsb_ge APH0 sp rdraw argv envp uid hw]. *)
  Corollary ent_stack_defined_top : forall top, top mod 4096 = 0 -> top <= usp + 4096 ->
    forall i, 0 <= i < top - usp -> FULL (Z_to_bv 64 (usp + i)) <> None.
  Proof.
    intros top Hm Hle i Hi. apply ent_stack_defined. destruct simg_top as (T1 & T3).
    pose proof ent_bsb_lower as Hlow. rewrite ent_len in T1, T3 |- *.
    pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp (ed_top rdraw) argv envp execfn)) as Z0.
    pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat argv)) as Z1.
    replace (usp + (utop - usp)) with utop in T1, T3 by ring.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* STATEMENT CHANGED, old beside new -- the string slack, as [ent_str_hi]:
       OLD  forall i, 0 <= i < |argv[k]| + 1 + 16 ->
              FULL (Z_to_bv 64 (bv_unsigned (cat_argv_ptr sp argv envp k) + i)) <> None
       NEW  forall i, 0 <= i < |argv[k]| + 1 + 8 ->
              FULL (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp execfn k) + i)) <> None
     Sixteen is false at the revision (see [ent_str_hi]); eight past the NUL is what
     [Pm9DiagStrK.str_cstr] reads.  The proof no longer goes through
     [ent_stack_defined]: every byte asked for is inside the string band. *)
  Theorem ent_str_defined : forall k, (k < 2)%nat ->
    forall i, 0 <= i < Z.of_nat (length (nth k argv [])) + 1 + 8 ->
      FULL (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp execfn k) + i)) <> None.
  Proof.
    intros k Hk i Hi.
    assert (Hk0 : (k < length argv)%nat) by (rewrite Hargv; cbn [length]; lia).
    rewrite (ent_ptr k Hk0). pose proof ent_bsb_lower as Hlow. destruct ent_top as (_ & T2).
    pose proof (total_arg_bytes_firstn_within argv k Hk0) as Hw.
    pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp (ed_top rdraw) argv envp execfn)) as Z0.
    pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat (firstn k argv))) as Z1.
    pose proof sp_rng as SR.
    apply ent_band_defined. rewrite u_small by lia. lia.
  Qed.

  Hypothesis CHKLIB : lib_chk RZ cs = true.

  (* STATEMENT CHANGED in two of its seven conjuncts, old beside new.  The four
     literal library cells (0x691cc8, 0x691ce8, 0x691d60) and the uid range are
     untouched -- they are image addresses, not stack addresses, and the revision
     moved neither.
       OLD  kfind_word (kn cs) (ELit 0) 0x6b2028 8 = Some KE_AUXP
            /\ lin_nowrapR (kn cs) KE_AUXP
            /\ (forall off e, In (off, e) AUXV_EXP ->
                  kfind_word (kn cs) KE_AUX off 8 = Some e)
       NEW  the first two over [e_auxv] -- [KE_AUXP] WAS [KE_AUX + 24], which IS
            the auxv base, so this is a rename and not a move -- and the third
            per-pair over [AUXV_EXP RZ], giving the key word and the value word of
            each claimed pair at [e_auxb + 16*i] and [+ 8].
     [KRange (EVar 8) ...] is spelled [KRange (EVar V_UID) ...]: same entry, named
     rather than numbered, because V_UID is 8 only by accident of the index table. *)
  Lemma lib_chk_parts :
    kfind_word (kn cs) (ELit 0) 0x691cc8 8 = Some (ELit 0x691cc8)
    /\ (exists v, kfind_word (kn cs) (ELit 0) 0x691ce8 4 = Some v /\ existsb (kentry_eqb (KRange v 1 4194303)) (kn cs) = true)
    /\ kfind_word (kn cs) (ELit 0) 0x691d60 8 = Some (ELit 0x6b2058)
    /\ kfind_word (kn cs) (ELit 0) 0x6b2028 8 = Some e_auxv
    /\ lin_nowrapR (kn cs) e_auxv = true
    (* DROPPED, old beside new: [/\ (forall p, In p (AUXV_EXP RZ) -> kfind_word .. key = Some (ELit ..)
       /\ kfind_word .. value = Some ..)] -- read only by [ent_auxv] (option D). *)
    /\ existsb (kentry_eqb (KRange (EVar V_UID) 0 4294967294)) (kn cs) = true.
  Proof.
    pose proof CHKLIB as H. unfold lib_chk in H.
    apply andb_prop in H as [H C7]. apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4].
    apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
    assert (OE : forall o e, opt_eqb o e = true -> o = Some e).
    { intros o e Ho. destruct o as [v|]; [|discriminate]. apply expr_eqb_eq in Ho. subst. reflexivity. }
    split; [apply OE; exact C1|]. split.
    { destruct (kfind_word (kn cs) (ELit 0) 0x691ce8 4) as [v|]; [|discriminate]. exists v. split; [reflexivity | exact C2]. }
    split; [apply OE; exact C3|]. split; [apply OE; exact C4|]. split; [exact C5 | exact C7].
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
    assert (CELL : ArtMem.cell ASEGS0 FULL (fst (fst c)) (snd (fst c)) (snd c))
      by (eapply art_lit1; first [exact (CHKX c Hin) | eassumption]).
    unfold ArtMem.cell in CELL.
    destruct ent_lz as (HOFF & _).
    rewrite rdn_mrestrict_eq; [exact CELL|].
    intros k Hk. destruct (Hx (woff (Z_to_bv 64 (fst (fst c))) k)) eqn:Hh; [exfalso | reflexivity].
    pose proof (HOFF _ Hh) as X. clear - Hin Hk X. unfold XC9K in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [subst c; cbn [fst snd] in *; do 8 (destruct k as [|k]; [exfalso; lazymatch type of X with find_segment ?S ?a ?n = None =>
        assert (Hs : match find_segment S a n with Some _ => true | None => false end = true) by vmc_refl; rewrite X in Hs; discriminate Hs end|]); lia|]).     destruct Hin.
  Qed.

  (* RENAME, value unchanged: [KE_AUXP] was [KE_AUX + 24], which is the plan's
     [e_auxv] -- the auxv base did not move. *)
  Lemma val_auxp : edenot E e_auxv = Z_to_bv 64 (usp + 8 * envc + 40).
  Proof.
    destruct lib_chk_parts as (_ & _ & _ & _ & LN & _). destruct ent_vals2 as (U1 & U2 & _ & U0). pose proof sp_rng.
    apply word_of_u. remember (bv_unsigned (edenot E e_auxv)) as x eqn:Ex. LINEQ e_auxv LN H0. rewrite <- Ex in H0. lia.
  Qed.

  Theorem ent_libcells : exists tid : word,
    1 <= bv_unsigned tid <= 4194303
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x691cc8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x691cc8))
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x691ce8) 4 = Some (word_to_le_bytes 4 tid)
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x691d60) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6b2058))
    /\ rdn ASEGS0 MV (Z_to_bv 64 0x6b2028) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * envc + 40))).
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

  (* DELETED, old beside new (Main's ruling, option D):
       OLD  Definition auxv_list (uidz rnd hwz : Z) : list Z :=
              [3; 0x10040; 4; 56; 5; 11; 16; hwz; 6; 4096; 11; uidz; 12; uidz; 23; 0; 25; rnd; 0; 0].
            Theorem ent_auxv : exists uidz rnd hwz : Z,
              (forall j, (j < 20)%nat -> rdn ASEGS0 FULL (Z_to_bv 64 (usp + 8 * envc + 40 + 8 * Z.of_nat j)) 8
                                         = Some (word_to_le_bytes 8 (Z_to_bv 64 (nth j (auxv_list uidz rnd hwz) 0))))
              /\ 0 <= uidz < 2 ^ 32 /\ 0 <= hwz < 2 ^ 64 /\ usp <= rnd /\ rnd + 16 <= 2 ^ 64.
     Twenty contiguous words at [e_auxv] holding the old ten pairs is FALSE at LPS 75d69e00
     (27/29 pairs, AT_SYSINFO_EHDR and the cache words first).  Its only consumer was
     Pm9DrvEntryInst.as0_main_auxv -> Pm9MainPhaseA's auxv_atA premise -> LibIface.lib_init_facts'
     auxv conjuncts, which no lib_statics_init prover reads; all are dropped in this series.
     The pair-list restatement approved for it is therefore retired, not written.
     [stk_chk] now ranges over the plan's own [aux_key_claimed]/[aux_val_claimed] and
     [lib_chk] no longer reads auxv values; [AUXV_EXP] is gone (see THE AUXV, above). *)
End Entry.
