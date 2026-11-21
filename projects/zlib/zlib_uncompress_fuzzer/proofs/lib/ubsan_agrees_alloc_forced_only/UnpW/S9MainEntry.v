(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import WsegFast PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit RefLayout StartupTac DrawDefs. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import S9StartupDefs S9Startup S9StartupFacts.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require S9Wseg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments.
Abbreviation RPH := SrcO_zlib_zlib_uncompress_fuzzer_repro.M.phdrs.
(* a worker port727 (): the entry pc as the launch block sees it. *)
Local Notation ENT := (Z_to_bv 64 (Z.of_N SrcO_zlib_zlib_uncompress_fuzzer_repro.M.init_pc)) (only parsing).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* a worker port727 (): Common/CatExec reads an argv string without its NUL (read_argv_str_k) and byte by
   byte (read_argv_byte_k); main needs the NUL-terminated read, built the same way. *)
Lemma read_argv_cstr727_k :
  forall v segs inp mbase ph entry (sp brk : word) draw k,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
      (length (nth k (in_argv inp) []) + 1)
  = Some (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]).
Proof.
  intros v segs inp mbase ph entry sp brk draw k Hlaunch Hk.
  pose proof (entry_stack_image_no_wrap v inp mbase ph entry sp brk draw Hlaunch) as Hnw.
  destruct (bsb_byte_k inp mbase ph entry sp draw k Hk) as [pre [post [E Hlen]]].
  pose proof (read_at_offset_image segs inp mbase ph entry sp draw
    pre (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) post
    (length (nth k (in_argv inp) []) + 1)) as H.
  rewrite Hlen in H.
  replace (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
    with (sp + nat_to_word
                 (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                    (in_argv inp) (in_envp inp) (in_execfn inp)
                  + total_arg_bytes_nat (firstn k (in_argv inp)))).
  2:{ rewrite (cat_argv_ptr_offset _ _ _ _ k Hk),
        (cat_string_base_offset v inp mbase sp brk draw Hlaunch).
      rewrite nat_to_word_add_merge. reflexivity. }
  apply H; [ | rewrite length_app; cbn [length]; lia | exact Hnw].
  rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma D_main_none : forall sp0 inp rdraw tid (i : Z),
  valid_argv (in_argv inp) -> (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  D_main_missb i 1 = true ->
  D_main sp0 inp rdraw tid (Z_to_bv 64 i) = None.
Proof.
  intros sp0 inp rdraw tid i Hva Hlo Hhi Hb.
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
  repeat (rewrite MemSplit.wbytes_outside;
    [ | rewrite ?length_N_to_le_bytes, ?length_canary_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
      | rewrite ?length_N_to_le_bytes, ?length_canary_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Hui; rewrite u_small by (cbn; lia);
        match goal with H : djw _ |- _ => unfold djw in H; clear -H; lia end ]).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section MainEntry.
  (* a worker port727 (): over the launch input (argv = [a0s; path] by Hav) and the ruled VLAUNCH + LOK. *)
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable inp : ProcInput.
  Variables mbase brk : word.
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp0 mbase.  (* a worker (A1) tool *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hav : in_argv inp = av.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs mem.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Definition p0 : word := cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0.
  Definition p1 : word := cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1.
  Definition auxvp : word := auxv_w sp0 inp.
  Definition rnd : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp).

  (* [comment removed for export] *)
  Definition cw : word := canary_w rdraw.
  Definition sw : word := secret_w rdraw.
  Definition vals0 : list word := [sp0; p0; p1; auxvp; rnd; tid; cw; sw] ++ junk_vals regs.
  Definition blobs0 : list (list byte) := [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]].
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  Definition sr_main : list expr :=
    [ELit 0; ELit 0x18c50; spx (-48); ELit 0x10800; ELit 0x72fb0; EVar 13; EVar 14; EVar 15;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 21; EVar 22; EVar 23;
     EVar 24; EVar 25; ELit 0x148cc; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 36; EVar 37; EVar 38; EVar 39].

  (* a worker port727 (): the stack write window is the ruled [sp0 - 6144513, sp0) (MemSplit.wok_lo). *)
  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-6144513)) 6144513;
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  (* [comment removed for export] *)
  (* a worker port727 (): StackLayout.auxv_entries' order. Only the 26 entries COMMON to both kernels
     (indices 0-25, through AT_EXECFN; 416 bytes) are listed: the tail (CONFIG_RSEQ on: AT_RSEQ_FEATURE_SIZE,
     AT_RSEQ_ALIGN, AT_NULL; off: AT_NULL) is kn_auxv_tail rs, added only by the paths that scan the vector to its 0
     key (a worker). Every key is listed; a value only where it is a constant, or AT_RANDOM's (EVar 4). *)
  Definition kn_auxv : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000400000; KRange (EVar 4) 0x7fff80000000 0x800000400000;
     KDisj (SA (EVar 0) (-6144513)) 6144513 (SA (EVar 3) 0) 416;
     KDisj (SA (EVar 0) (-6144513)) 6144513 (SA (EVar 4) 0) 16;
     KAlign (EVar 3) 8; KAlign (EVar 4) 8;
     KWord (SA (EVar 3) 0) 8 (ELit 33);                                       (* AT_SYSINFO_EHDR *)
     KWord (SA (EVar 3) 16) 8 (ELit 40); KWord (SA (EVar 3) 32) 8 (ELit 41);   (* the cache words *)
     KWord (SA (EVar 3) 48) 8 (ELit 42); KWord (SA (EVar 3) 64) 8 (ELit 43);
     KWord (SA (EVar 3) 80) 8 (ELit 44); KWord (SA (EVar 3) 96) 8 (ELit 45);
     KWord (SA (EVar 3) 112) 8 (ELit 46); KWord (SA (EVar 3) 128) 8 (ELit 47);
     KWord (SA (EVar 3) 144) 8 (ELit 51);                                     (* AT_MINSIGSTKSZ *)
     KWord (SA (EVar 3) 160) 8 (ELit 16);                                     (* AT_HWCAP *)
     KWord (SA (EVar 3) 176) 8 (ELit 6); KWord (SA (EVar 3) 184) 8 (ELit 4096);
     KWord (SA (EVar 3) 192) 8 (ELit 17); KWord (SA (EVar 3) 200) 8 (ELit 100);
     KWord (SA (EVar 3) 208) 8 (ELit 3); KWord (SA (EVar 3) 216) 8 (ELit 0x10040);
     KWord (SA (EVar 3) 224) 8 (ELit 4); KWord (SA (EVar 3) 232) 8 (ELit 56);
     KWord (SA (EVar 3) 240) 8 (ELit 5); KWord (SA (EVar 3) 248) 8 (ELit 10);
     KWord (SA (EVar 3) 256) 8 (ELit 7); KWord (SA (EVar 3) 264) 8 (ELit 0);
     KWord (SA (EVar 3) 272) 8 (ELit 8); KWord (SA (EVar 3) 280) 8 (ELit 0);
     KWord (SA (EVar 3) 288) 8 (ELit 9); KWord (SA (EVar 3) 296) 8 (ELit 0x14780);
     KWord (SA (EVar 3) 304) 8 (ELit 11);                                     (* AT_UID *)
     KWord (SA (EVar 3) 320) 8 (ELit 12);                                     (* AT_EUID *)
     KWord (SA (EVar 3) 336) 8 (ELit 13);                                     (* AT_GID *)
     KWord (SA (EVar 3) 352) 8 (ELit 14);                                     (* AT_EGID *)
     KWord (SA (EVar 3) 368) 8 (ELit 23); KWord (SA (EVar 3) 376) 8 (ELit 0);
     KWord (SA (EVar 3) 384) 8 (ELit 25); KWord (SA (EVar 3) 392) 8 (EVar 4);
     KWord (SA (EVar 3) 400) 8 (ELit 31);                                     (* AT_EXECFN *)
     KWord (SA (EVar 4) 8) 8 (EVar 7)].

  (* a worker port727 (): the per-kernel tail of the vector, rs = CONFIG_RSEQ (kb_rseq (in_kernel inp)):
     on: (AT_RSEQ_FEATURE_SIZE 27, 28), (AT_RSEQ_ALIGN 28, 32), (AT_NULL 0, 0); off: (AT_NULL 0, 0). *)
  Definition kn_auxv_tail (rs : bool) : list kentry :=
    if rs then
      [KDisj (SA (EVar 0) (-6144513)) 6144513 (SA (EVar 3) 416) 48;
       KWord (SA (EVar 3) 416) 8 (ELit 27); KWord (SA (EVar 3) 424) 8 (ELit 28);
       KWord (SA (EVar 3) 432) 8 (ELit 28); KWord (SA (EVar 3) 440) 8 (ELit 32);
       KWord (SA (EVar 3) 448) 8 (ELit 0); KWord (SA (EVar 3) 456) 8 (ELit 0)]
    else
      [KDisj (SA (EVar 0) (-6144513)) 6144513 (SA (EVar 3) 416) 16;
       KWord (SA (EVar 3) 416) 8 (ELit 0); KWord (SA (EVar 3) 424) 8 (ELit 0)].

  Definition kn_image : list kentry :=
    [
     KWr (SA (ELit 0) 0x22000) 0x72000;
     KImg 0x10000 0x22e60;
     KImg 0x22e61 0x72ee0;
     KWord (SA (ELit 0) 0x72ee8) 8 (ELit 0x72ee8);
     KWord (SA (ELit 0) 0x72f08) 4 (EVar 5);
     KImg 0x72f14 0x72f60;
     KImg 0x72f68 0x72f80;
     KImg 0x72f88 0x72fa0;
     KWord (SA (ELit 0) 0x72fa0) 8 (EVar 6);
     KImg 0x72fb0 0x72fc0;
     KImg 0x72fc8 0x92fd8;
     KImg 0x92ff0 0x93218;
     KWord (SA (ELit 0) 0x93218) 8 (EVar 6);
     KImg 0x93220 0x93228;
     KImg 0x93239 0x93240;
     KWord (SA (ELit 0) 0x93240) 8 (EVar 3);
     KImg 0x93248 0x93250;
     KImg 0x93260 0x93268;
     KWord (SA (ELit 0) 0x93268) 8 (ELit 4096);
     KImg 0x93270 0x932a0;
     KImg 0x932a8 0x94000;
     KRange (EVar 5) 1 4194303;
     KImg 0 0x1000].

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
#[local] Instance RC_a1_2 : RunCtx := mkRunCtx inp sp0 mbase.  (* a worker (A1) tool *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hav : in_argv inp = av.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs mem.

  Let E := E0 sp0 a0s path inp rdraw tid regs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 inp rdraw; p1 inp rdraw; auxvp sp0 inp; rnd sp0 inp; tid; cw rdraw; sw rdraw] ++ junk_vals regs) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  Lemma ev_junk : forall i, (i < 32)%nat -> ev E (8 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals. change (8 + i)%nat with (length [sp0; p0 inp rdraw; p1 inp rdraw; auxvp sp0 inp; rnd sp0 inp; tid; cw rdraw; sw rdraw] + i)%nat.
    rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.

Section MainRegs.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable inp : ProcInput.
  Variables mbase brk : word.
#[local] Instance RC_a1_3 : RunCtx := mkRunCtx inp sp0 mbase.  (* a worker (A1) tool *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hav : in_argv inp = av.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs mem.
  Let E := E0 sp0 a0s path inp rdraw tid regs.
  Lemma len_av_inp' : length (in_argv inp) = 2%nat. Proof. rewrite Hav. reflexivity. Qed.

  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ rewrite (spx_val sp0 a0s path inp rdraw tid regs)
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk sp0 a0s path inp rdraw tid regs (n - 8)) by lia; reflexivity | idtac ]
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ _ ME); f_equal; rewrite len_av_inp'; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ _ ME); f_equal; rewrite len_av_inp'; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ _ ME); unfold argcN, len_word; rewrite Hav; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ _ ME); unfold argcN, len_word; rewrite Hav; reflexivity
                | apply (me_szero _ _ _ _ _ _ _ ME); cbn; (first [solve [liafast_keep_section; tauto] | tauto])
                | idtac ].

  Ltac lia ::= lia_old.
  Theorem main_regs_ok : regs_ok E sr_main regs.
  Proof.
    pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
  Qed.
  Ltac lia ::= lia_fast.
End MainRegs.

Section KnowProofs.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable inp : ProcInput.
  Variables mbase brk : word.
#[local] Instance RC_a1_4 : RunCtx := mkRunCtx inp sp0 mbase.  (* a worker (A1) tool *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hav : in_argv inp = av.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs mem.
  Let E := E0 sp0 a0s path inp rdraw tid regs.

  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 inp rdraw. Proof. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 inp rdraw. Proof. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp sp0 inp. Proof. reflexivity. Qed.
  Lemma ke4 : ev E 4 = rnd sp0 inp. Proof. reflexivity. Qed.
  Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.
  Lemma ke6 : ev E 6 = canary_w rdraw. Proof. reflexivity. Qed.
  Lemma ke7 : ev E 7 = secret_w rdraw. Proof. reflexivity. Qed.
  Lemma Hva_inp : valid_argv (in_argv inp). Proof. rewrite Hav. exact Hva. Qed.
  Lemma len_av_inp : length (in_argv inp) = 2%nat. Proof. rewrite Hav. reflexivity. Qed.

  Lemma know_stack : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    unfold kn_stack, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win sp0 inp mbase rdraw tid regs mem ME); rewrite u_small by lia; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME) by lia.
      pose proof (read_argc_w (run_segments RSEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau ltac:(unfold sp_window_hi; lia)) as Hr.
      unfold wmem in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. unfold argcN, len_word. rewrite Hav. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w (run_segments RSEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH ENT sp0 brk rdraw Hva_inp Hvl Hlau
                    ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat
                    ltac:(rewrite len_av_inp; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w (run_segments RSEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH ENT sp0 brk rdraw Hva_inp Hvl Hlau
                    ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 1%nat
                    ltac:(rewrite len_av_inp; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_null (run_segments RSEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau
                    ltac:(unfold sp_window_hi; lia)) as Hr.
      rewrite w_add_nat in Hr. rewrite len_av_inp in Hr. change (Z.of_nat (8 + 8 * 2)) with 24%Z in Hr.
      rewrite <- (rdn_wmem_stack (run_segments RSEGS rc_inp rc_sp rc_mb) inp mbase RPH ENT sp0 rdraw) in Hr by (try rewrite u_small by lia; lia).
      unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  Lemma auxvp_eq : auxvp sp0 inp
    = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off (in_argv inp) (in_envp inp))).
  Proof. unfold auxvp, auxv_w, auxv_off. f_equal. lia. Qed.

  (* a worker port727 (): the whole vector (auxv_size, either kernel) plus 16 sits inside the entry block,
     whose length is at most 2101782 (lay_bsb_len); 448 = the 27 entries of the shorter (rseq off) vector + 16. *)
  Lemma auxvp_u : bv_unsigned (auxvp sp0 inp)
      = (bv_unsigned sp0 + Z.of_nat (auxv_off (in_argv inp) (in_envp inp)))%Z
    /\ (Z.of_nat (auxv_off (in_argv inp) (in_envp inp)) + 448 <= 2101782)%Z.
  Proof.
    pose proof kp_lo. pose proof kp_hi.
    pose proof (auxv_off_bound inp mbase RPH ENT sp0 brk rdraw) as Hb.
    pose proof (lay_bsb_len Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau) as Hl.
    assert (Has : (432 <= auxv_size (kb_rseq (in_kernel inp)))%nat)
      by (unfold auxv_size, auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
    rewrite auxvp_eq. rewrite u_small by lia. lia.
  Qed.

  Lemma rnd_u : (bv_unsigned sp0 <= bv_unsigned (rnd sp0 inp))%Z
    /\ (bv_unsigned (rnd sp0 inp) + 16 <= bv_unsigned sp0 + 2240000)%Z
    /\ (bv_unsigned (rnd sp0 inp) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn (run_segments RSEGS rc_inp rc_sp rc_mb) (stack_to_mem sp0 (entry_stack_image inp mbase RPH ENT sp0 rdraw))
              (Z_to_bv 64 (bv_unsigned (rnd sp0 inp) + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
  Proof.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    pose proof (lay_bsb_len Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau) as Hl.
    destruct (rnd_facts (run_segments RSEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau
                ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) kp_al)
      as (A & B & C & D & F).
    unfold rnd. repeat split; try assumption; try lia.
  Qed.

  (* a worker port727 (): words 0-51 = the 26 entries common to both kernels. *)
  Lemma auxv_word_at : forall j, (j < 52)%nat ->
    rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned (auxvp sp0 inp) + 8 * Z.of_nat j)) 8
    = Some (word_to_le_bytes 8 (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH ENT
                                          (in_uid inp) (in_gid inp) (in_hwcap inp) (rnd sp0 inp)
                                          (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                                       (Z_to_bv 64 0))).
  Proof.
    intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct auxvp_u as [Hu Hb].
    rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack (run_segments RSEGS rc_inp rc_sp rc_mb) inp mbase RPH ENT sp0 rdraw) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia).
    replace (Z_to_bv 64 (bv_unsigned (auxvp sp0 inp) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j))
      by (rewrite w_add_nat; f_equal; lia).
    rewrite (read_auxv_word (run_segments RSEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau ltac:(unfold sp_window_hi; lia) j
               ltac:(unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia)).
    rewrite n_to_le_8_spec. unfold rnd. reflexivity.
  Qed.

  (* a worker port727 (): any word of the vector, either kernel (the tail words included). *)
  Lemma auxv_word_at_k : forall j, (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
    rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned (auxvp sp0 inp) + 8 * Z.of_nat j)) 8
    = Some (word_to_le_bytes 8 (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH ENT
                                          (in_uid inp) (in_gid inp) (in_hwcap inp) (rnd sp0 inp)
                                          (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                                       (Z_to_bv 64 0))).
  Proof.
    intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct auxvp_u as [Hu _].
    pose proof (auxv_off_bound inp mbase RPH ENT sp0 brk rdraw) as Hb.
    pose proof (lay_bsb_len Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau) as Hl.
    assert (Hj8 : (8 * j + 8 <= auxv_size (kb_rseq (in_kernel inp)))%nat)
      by (unfold auxv_size, auxv_count in *; destruct (kb_rseq (in_kernel inp)); lia).
    rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack (run_segments RSEGS rc_inp rc_sp rc_mb) inp mbase RPH ENT sp0 rdraw) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia).
    replace (Z_to_bv 64 (bv_unsigned (auxvp sp0 inp) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j))
      by (rewrite w_add_nat; f_equal; lia).
    rewrite (read_auxv_word (run_segments RSEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau ltac:(unfold sp_window_hi; lia) j Hj).
    rewrite n_to_le_8_spec. unfold rnd. reflexivity.
  Qed.

  Ltac kw_auxv j :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
      replace k with (8 * Z.of_nat j)%Z by reflexivity end;
    rewrite (auxv_word_at j) by lia; unfold auxv_words, auxv_entries; cbn [nth flat_map app fst snd];
    try reflexivity.

  Ltac kw_tail RS :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
      let j := eval vm_compute in (Z.to_nat (k / 8)) in
      replace k with (8 * Z.of_nat j)%Z by reflexivity;
      rewrite (auxv_word_at_k j) by (rewrite RS; cbn; lia) end;
    unfold auxv_words, auxv_entries;
    change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)); rewrite RS;
    cbn [nth flat_map app fst snd]; reflexivity.

  (* a worker port727 (): the per-kernel tail (rs = CONFIG_RSEQ), for the paths that scan to AT_NULL. *)
  Lemma know_auxv_tail : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (kn_auxv_tail (kb_rseq (in_kernel inp))).
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as [Hau Hab].
    pose proof (auxv_off_bound inp mbase RPH ENT sp0 brk rdraw) as Hb.
    pose proof (lay_bsb_len Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau) as Hl.
    destruct (kb_rseq (in_kernel inp)) eqn:RS; rewrite ?RS in Hb; cbn [auxv_size auxv_count] in Hb;
      unfold kn_auxv_tail, know_ok;
      repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3;
      try rewrite Hau; try lia.
    all: kw_tail RS.
  Qed.

  Lemma know_auxv : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
    unfold kn_auxv, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3, ?ke4, ?ke7; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4, ?ke7;
      try rewrite Hau; try lia.
    - (* [comment removed for export] *) split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off (in_argv inp) (in_envp inp)))%Z
        with ((2 * q + 5 + Z.of_nat (length (in_envp inp))) * 8)%Z
        by (unfold auxv_off; rewrite len_av_inp; lia).
      apply Z_mod_mult.
    - kw_auxv 0%nat. - kw_auxv 2%nat. - kw_auxv 4%nat. - kw_auxv 6%nat. - kw_auxv 8%nat.
    - kw_auxv 10%nat. - kw_auxv 12%nat. - kw_auxv 14%nat. - kw_auxv 16%nat. - kw_auxv 18%nat.
    - kw_auxv 20%nat. - kw_auxv 22%nat. - kw_auxv 23%nat. - kw_auxv 24%nat. - kw_auxv 25%nat.
    - kw_auxv 26%nat. - kw_auxv 27%nat. - kw_auxv 28%nat. - kw_auxv 29%nat. - kw_auxv 30%nat.
    - kw_auxv 31%nat. - kw_auxv 32%nat. - kw_auxv 33%nat. - kw_auxv 34%nat. - kw_auxv 35%nat.
    - kw_auxv 36%nat. - kw_auxv 37%nat. - kw_auxv 38%nat. - kw_auxv 40%nat. - kw_auxv 42%nat.
    - kw_auxv 44%nat. - kw_auxv 46%nat. - kw_auxv 47%nat. - kw_auxv 48%nat. - kw_auxv 49%nat.
    - kw_auxv 50%nat.
    - (* [comment removed for export] *)
      split; [lia|]. split; [lia|].
      unfold adenot; cbn [a_base a_off edenot]; rewrite ke4; unfold v_addi.
      rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (rdn_wmem_stack (run_segments RSEGS rc_inp rc_sp rc_mb) inp mbase RPH ENT sp0 rdraw) as Hw. unfold wmem in Hw.
      rewrite Hw by (rewrite u_small by lia; lia).
      pose proof (Hr4 8%nat 8%nat ltac:(lia)) as H8. change (Z.of_nat 8) with 8%Z in H8. rewrite H8.
      rewrite rnd_sub by lia. rewrite w8_secret. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxvp : forall segs,
    rdn segs (D_main sp0 inp rdraw tid) (Z_to_bv 64 0x93240) 8
    = Some (word_to_le_bytes 8 (auxvp sp0 inp)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range (in_hwcap inp)). pose proof kp_lo. pose proof kp_hi.
    unfold auxvp, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma wseg_data {RCa1 : RunCtx}  : wseg_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (Z_to_bv 64 0x22000) 0x72000 = true.
  Proof.  (* [comment removed for export] *)
    replace (0x72000)%nat with 466944%nat by (apply Stdlib.NArith.Nnat.Nat2N.inj; vm_cast_no_check (@eq_refl N 466944%N)).
    exact S9Wseg.data_window_wseg.
  Qed.

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
  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x94000)%Z ->
    kentry_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 inp rdraw tid i Hva_inp); [lia | lia |].
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L (run_segments RSEGS rc_inp rc_sp rc_mb)); try reflexivity.
  Ltac kw_mem L := kw_pre; rewrite (L (run_segments RSEGS rc_inp rc_sp rc_mb)); try reflexivity.

  Lemma know_image : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E mem kn_image.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimg;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5, ?ke6; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - (* [comment removed for export] *) split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22000) (Z_to_bv 64 (0x22000 + d)) 0x72000 m 0x22000 0x94000);
        [reflexivity | vm_cast_no_check (@eq_refl Z 0x94000%Z) | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_data (D_main_self sp0 inp rdraw tid).
    - kw_mem (main_entry_tid sp0 inp mbase rdraw tid Hlo regs mem ME).
    - kw_data (D_main_canary sp0 inp rdraw tid).
    - kw_data (S9StartupFacts.D_main_guard_w sp0 inp rdraw tid).
    - kw_data D_main_auxvp.
    - kw_data (D_main_pagesize sp0 inp rdraw tid Hva_inp).
    - (* [comment removed for export] *) lia.
  Qed.


  Theorem main_know_ok : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E mem kn_main.
  Proof.
    unfold kn_main, know_ok.
    apply Forall_app; split; [apply know_stack|].
    apply Forall_app; split; [apply know_auxv | apply know_image].
  Qed.

  (* a worker port727 (): what a path that scans the auxv to AT_NULL starts from (a worker). *)
  Theorem main_know_ok_tail : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (kn_main ++ kn_auxv_tail (kb_rseq (in_kernel inp))).
  Proof.
    unfold know_ok. apply Forall_app; split; [apply main_know_ok | apply know_auxv_tail].
  Qed.

  (* [comment removed for export] *)
  (* a worker port727 (): the strings sit at the top of the entry block (under ed_top rdraw); the bound
     below is the block's (lay_bsb_len 2101782), which the old figure 2107576 still covers. *)
  Lemma main_str : forall k, (k < 2)%nat ->
    rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
        (length (nth k (in_argv inp) []) + 1)
      = Some (nth k (in_argv inp) [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0
        <= bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
        <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k (in_argv inp) [])) <= 131071)%Z.
  Proof.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    pose proof (lay_bsb_nw Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau ltac:(unfold sp_window_hi; lia)) as Hnw.
    pose proof (lay_bsb_len Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau) as Hbl.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite len_av_inp; lia).
    destruct (argv_ptr_bounds_at Sv48 inp mbase sp0 brk rdraw Hlau k Hk') as [B1 B2].
    pose proof (u_cat_argv_ptr Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau
                  ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (struct_av_bound inp mbase RPH ENT sp0 brk rdraw) as Hsb.
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)) as Hf.
    pose proof (argv_str_len inp Hva_inp k Hk') as Hlen.
    repeat split.
    - rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME) by lia.
      pose proof (rdn_wmem_stack (run_segments RSEGS rc_inp rc_sp rc_mb) inp mbase RPH ENT sp0 rdraw) as Hw. unfold wmem in Hw. rewrite Hw by lia.
      exact (read_argv_cstr727_k Sv48 (run_segments RSEGS rc_inp rc_sp rc_mb) inp mbase RPH ENT sp0 brk rdraw k Hlau Hk').
    - exact B1.
    - lia.
    - exact Hlen.
  Qed.
End KnowProofs.
