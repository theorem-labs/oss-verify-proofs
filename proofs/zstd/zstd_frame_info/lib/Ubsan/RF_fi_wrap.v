(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge Image Mem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg RF_fi_iface RF_fi_gfha RF_fi_gfha2.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Definition WRAP_FRAME : Z := 112.

(* [comment removed for export] *)
Definition leaf_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (depth lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (r : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : fmem),
    ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(SP - depth, SP)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SP.

Definition wrap_stmt (pc : Z) : Prop :=
  forall (ra : word) (SP : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (S : Z) (bl : list Z) (lo : Z),
    buf_at m S bl -> zlen bl < 2^62 ->
    stk usegs m lo SP -> lo <= SP - WRAP_FRAME -> 0 <= SP < 2^64 ->
    (S + zlen bl <= SP - WRAP_FRAME \/ SP <= S) ->
    mem_inv usegs m -> SP mod 16 = 0 ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlen bl) ->
    evt usegs (leaf_post ra SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc WRAP_FRAME lo m)
        (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

Definition gfcs_stmt : Prop := wrap_stmt PFI_GFCS.
Definition gds_stmt : Prop := wrap_stmt PFI_GDS.
Definition gdid_stmt : Prop := wrap_stmt PFI_GDID.

Section W.
  #[using="Type"] Lemma gfcs_proof : gfcs_stmt.
  Proof.
    intros until lo; intros BUF NB ST LO SPH SEP MI S16 -> ->.
    unfold PFI_GFCS, PFI_GDS, PFI_GDID, WRAP_FRAME in *.
    pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = zlen bl) by (rewrite length_map; reflexivity).
    pose proof (munch_refl [(SP - 112, SP)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ST0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    Local Ltac2 Set LiaHints.tbl := fun () => "00Q0>10287669065.5812428150072.7714433549809.7817761707061.5523068901782.7423194932694.5524630998586.5825076071819.7725076071819.7828040491972.7831749291223.5832563876970.7339304366957.4939379649219.5539935544557.7040482790070.7141997600746.7342002100550.54455922125.85  4703816314.77 47852169094.5152074235542.8557622410744.7861396519294.5864267890458.5465569337201.5865569337201.8065569337201.826741545311.55 67702150001.8167818065135.558402510058.55 8945778604.58 00000100200300700800<00A00B00C00M00N00O00S00X00Y00]00^00_00`00a00b00c00f01001101201301401901:01F01G01KSFFS2NBSS2LOS3SPHSSS3SEP4LENBSSS2LOS3SEPSS2LOSSSSSFS1HS3SEP4LENBSSSSS3SEPSS2LO3SPH3ST0SS2HB".
carve_frame 64%nat ST.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs m _ [] 64 _ [] [8; 48; 8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
    zstep. zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ ?m1 ?A [?c0; ?c1; ?c2] =>
      apply (proj1 (rw_cells_app m1 A [c0] [c1; c2])) in FR; destruct FR as [F0 FZ]; cbn [cells_size csize Nat.add] in FZ;
      apply (proj1 (rw_cells_app m1 _ [c1] [c2])) in FZ; destruct FZ as [FZ F8]; cbn [cells_size csize Nat.add] in F8 end.
    replace (SP + -64 + Z.of_nat 8) with (SP + -56) in FZ by lia.
    replace (SP + -64 + Z.of_nat 8 + Z.of_nat 48) with (SP + -8) in F8 by lia.
    do 4 zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof gfha_proof as G. unfold gfha_stmt, gfha_stmt_at, gfha_post, GFHA_FRAME in G.
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply G; [ split; [exact PL| exact PLR] | lia | exact FZ | lia | exact ST | lia | lia | lia | lia | lia | assumption | reflexivity
                   | reflexivity | reflexivity | reflexivity ] | ]; post_call usegs mc end.
    clear G. try rename MI0 into MI.
    (* [comment removed for export] *) unfold GFHA_FRAME in *.
    zstep. if_cases KR; clear KR.
    - (* [comment removed for export] *) do 6 zstep.
    (* [comment removed for export] *)
    lazymatch goal with FZx : rw_cells _ ?m2 (SP + -56) ?cz, F0x : rw_cells _ _ (SP + -64) [?c0], F8x : rw_cells _ _ (SP + -8) [?c8] |- _ =>
      assert (FR : rw_cells usegs m2 (SP + -64) ([c0] ++ (cz ++ [c8])))
        by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact F0x|]; cbn [cells_size csize Nat.add];
            replace (SP + -64 + Z.of_nat 8) with (SP + -56) by lia;
            apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact FZx|]; cbn [cells_size csize Nat.add];
            match goal with |- rw_cells _ _ ?a _ => replace a with (SP + -8) by lia end; exact F8x);
      clear F0x FZx F8x; cbn [app] in FR end.
      zstep. lazymatch goal with STx : stk _ _ lo _ |- _ => release_frame FR STx SP end. zstep. zstep. finish.
    - zstep.
    (* [comment removed for export] *)
    lazymatch goal with FZx : rw_cells _ ?m2 (SP + -56) ?cz, F0x : rw_cells _ _ (SP + -64) [?c0], F8x : rw_cells _ _ (SP + -8) [?c8] |- _ =>
      assert (FR : rw_cells usegs m2 (SP + -64) ([c0] ++ (cz ++ [c8])))
        by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact F0x|]; cbn [cells_size csize Nat.add];
            replace (SP + -64 + Z.of_nat 8) with (SP + -56) by lia;
            apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact FZx|]; cbn [cells_size csize Nat.add];
            match goal with |- rw_cells _ _ ?a _ => replace a with (SP + -8) by lia end; exact F8x);
      clear F0x FZx F8x; cbn [app] in FR end.
      zstep. lazymatch goal with STx : stk _ _ lo _ |- _ => release_frame FR STx SP end. zstep. zstep. finish.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="Type"] Lemma gds_proof : gds_stmt.
  Proof.
    intros until lo; intros BUF NB ST LO SPH SEP MI S16 -> ->.
    unfold PFI_GFCS, PFI_GDS, PFI_GDID, WRAP_FRAME in *.
    pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = zlen bl) by (rewrite length_map; reflexivity).
    pose proof (munch_refl [(SP - 112, SP)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ST0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    Local Ltac2 Set LiaHints.tbl := fun () => "00T0>10287669065.5812373220886.7412428150072.7714433549809.7817761707061.5523194932694.5524630998586.5825076071819.7725076071819.7828040491972.7831749291223.5832563876970.7339304366957.4939379649219.5539935544557.7040482790070.7141997600746.7342002100550.5442708860738.85455922125.85  4703816314.77 47852169094.5152074235542.8557622410744.7859588178610.8561396519294.5864267890458.5465569337201.5865569337201.7865569337201.826741545311.55 67683096182.8567702150001.8167818065135.558402510058.55 8945778604.58 00000100200300400800<00A00B00C00M00N00O00S00X00Y00]00^00_00`00a00b00c00d00g00h01201301401501601;01<01=01I01J01NSSFFS2NBS2LOS3SPHSSS3SEP4LENBSSS2LOS3SEPSS2LOSSFSSSFS1HSS3SEP4LENBSSSSS3SEPFSS2LO3SPH3ST0SS2HB".
carve_frame 64%nat ST.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs m _ [] 64 _ [] [8; 48; 8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
    zstep. zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ ?m1 ?A [?c0; ?c1; ?c2] =>
      apply (proj1 (rw_cells_app m1 A [c0] [c1; c2])) in FR; destruct FR as [F0 FZ]; cbn [cells_size csize Nat.add] in FZ;
      apply (proj1 (rw_cells_app m1 _ [c1] [c2])) in FZ; destruct FZ as [FZ F8]; cbn [cells_size csize Nat.add] in F8 end.
    replace (SP + -64 + Z.of_nat 8) with (SP + -56) in FZ by lia.
    replace (SP + -64 + Z.of_nat 8 + Z.of_nat 48) with (SP + -8) in F8 by lia.
    do 4 zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof gfha_proof as G. unfold gfha_stmt, gfha_stmt_at, gfha_post, GFHA_FRAME in G.
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply G; [ split; [exact PL| exact PLR] | lia | exact FZ | lia | exact ST | lia | lia | lia | lia | lia | assumption | reflexivity
                   | reflexivity | reflexivity | reflexivity ] | ]; post_call usegs mc end.
    clear G. try rename MI0 into MI.
    (* [comment removed for export] *) unfold GFHA_FRAME in *.
    zstep. if_cases KR; clear KR.
    - do 9 zstep.
    (* [comment removed for export] *)
    lazymatch goal with FZx : rw_cells _ ?m2 (SP + -56) ?cz, F0x : rw_cells _ _ (SP + -64) [?c0], F8x : rw_cells _ _ (SP + -8) [?c8] |- _ =>
      assert (FR : rw_cells usegs m2 (SP + -64) ([c0] ++ (cz ++ [c8])))
        by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact F0x|]; cbn [cells_size csize Nat.add];
            replace (SP + -64 + Z.of_nat 8) with (SP + -56) by lia;
            apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact FZx|]; cbn [cells_size csize Nat.add];
            match goal with |- rw_cells _ _ ?a _ => replace a with (SP + -8) by lia end; exact F8x);
      clear F0x FZx F8x; cbn [app] in FR end.
      zstep. lazymatch goal with STx : stk _ _ lo _ |- _ => release_frame FR STx SP end. zstep. zstep. finish.
    - do 4 zstep.
    (* [comment removed for export] *)
    lazymatch goal with FZx : rw_cells _ ?m2 (SP + -56) ?cz, F0x : rw_cells _ _ (SP + -64) [?c0], F8x : rw_cells _ _ (SP + -8) [?c8] |- _ =>
      assert (FR : rw_cells usegs m2 (SP + -64) ([c0] ++ (cz ++ [c8])))
        by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact F0x|]; cbn [cells_size csize Nat.add];
            replace (SP + -64 + Z.of_nat 8) with (SP + -56) by lia;
            apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact FZx|]; cbn [cells_size csize Nat.add];
            match goal with |- rw_cells _ _ ?a _ => replace a with (SP + -8) by lia end; exact F8x);
      clear F0x FZx F8x; cbn [app] in FR end.
      zstep. lazymatch goal with STx : stk _ _ lo _ |- _ => release_frame FR STx SP end. zstep. zstep. finish.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="Type"] Lemma gdid_proof : gdid_stmt.
  Proof.
    intros until lo; intros BUF NB ST LO SPH SEP MI S16 -> ->.
    unfold PFI_GFCS, PFI_GDS, PFI_GDID, WRAP_FRAME in *.
    pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = zlen bl) by (rewrite length_map; reflexivity).
    pose proof (munch_refl [(SP - 112, SP)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ST0 : 0 <= lo) by (destruct ST as [? _]; assumption).
carve_frame 64%nat ST.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs m _ [] 64 _ [] [8; 48; 8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
    zstep. zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ ?m1 ?A [?c0; ?c1; ?c2] =>
      apply (proj1 (rw_cells_app m1 A [c0] [c1; c2])) in FR; destruct FR as [F0 FZ]; cbn [cells_size csize Nat.add] in FZ;
      apply (proj1 (rw_cells_app m1 _ [c1] [c2])) in FZ; destruct FZ as [FZ F8]; cbn [cells_size csize Nat.add] in F8 end.
    replace (SP + -64 + Z.of_nat 8) with (SP + -56) in FZ by lia.
    replace (SP + -64 + Z.of_nat 8 + Z.of_nat 48) with (SP + -8) in F8 by lia.
    zstep. zstep. (* [comment removed for export] *)
    do 6 zstep.   (* [comment removed for export] *)
    lazymatch goal with FZx : rw_cells _ ?m1 (SP + -56) ?cz |- _ =>
      let j := fresh "zj" in destruct (rw_cells_forget usegs m1 _ cz FZx) as [j FZ']; clear FZx; cbn [cells_size csize Nat.add] in FZ'; rename FZ' into FZ end.
    zstep. zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof gfha_proof as G. unfold gfha_stmt, gfha_stmt_at, gfha_post, GFHA_FRAME in G.
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply G; [ split; [exact PL| exact PLR] | lia | exact FZ | lia | exact ST | lia | lia | lia | lia | lia | assumption | reflexivity
                   | reflexivity | reflexivity | reflexivity ] | ]; post_call usegs mc end.
    clear G. try rename MI0 into MI.
    (* [comment removed for export] *) unfold GFHA_FRAME in *.
    do 4 zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with FZx : rw_cells _ ?m2 (SP + -56) ?cz, F0x : rw_cells _ _ (SP + -64) [?c0], F8x : rw_cells _ _ (SP + -8) [?c8] |- _ =>
      assert (FR : rw_cells usegs m2 (SP + -64) ([c0] ++ (cz ++ [c8])))
        by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact F0x|]; cbn [cells_size csize Nat.add];
            replace (SP + -64 + Z.of_nat 8) with (SP + -56) by lia;
            apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact FZx|]; cbn [cells_size csize Nat.add];
            match goal with |- rw_cells _ _ ?a _ => replace a with (SP + -8) by lia end; exact F8x);
      clear F0x FZx F8x; cbn [app] in FR end.
    zstep. lazymatch goal with STx : stk _ _ lo _ |- _ => release_frame FR STx SP end. zstep. zstep. finish.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

End W.
