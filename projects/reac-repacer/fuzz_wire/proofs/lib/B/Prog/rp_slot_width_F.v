(* rp_slot_width_F: the footprint walk of fuzz_wire.asan-ubsan's rp_slot_width (image B, entry 0x8151c, 208 bytes),
   against the frozen lib/B/Prog/rp_slot_width_F_c.v rp_slot_width_F_holds_stmt: the callee rp_frame_channels is taken
   by its footprint contract rp_frame_channels_contract_F (rp_frame_channels_F_c.v), the statement's premise. It is the
   image-A walk lib/A/Prog/rp_slot_width_F.v step for step (itself the plain walk lib/Prog/rp_slot_width.v, whose
   sw_tail and fc_model_range it reuses by name, in the footprint style of lib/B/Prog/reac_frame_clean_len_F.v), with
   image B's addresses and the three UBSan checks of f that image B adds.
   The code:
     +0x00 .. +0x1c  frame [sp - 16, sp) (ra, s0); s0 := slot, a2 := f, a0 := -1; `bltu a1, a3 (= 50)` to +0x9c;
     +0x20           `beqz a2` to the `unimp` at +0xac (0x815c8; f == NULL);
     +0x24 / +0x28   `addi a3, zero, -0x10`, `bgeu a2, a3` to +0xac (f + 16 wraps);
     +0x2c .. +0x34  the shadow base: the GOT word 0x98878 (GOT_CELL_K), then the cell 0xa07f8 (CELL_K);
     +0x38 .. +0x48  the shadow byte k of x = f + 16 (`lb`), `bnez` to +0xb0: `andi a6, a3, 7`; `blt a6, a5` back to
                     +0x4c, else `jal __asan_report_load1` (+0xbc, 0x815d8);
     +0x4c / +0x50   `lbu` f[16], `bnez` to +0x9c (-1);
     +0x54 / +0x58   `addi a3, zero, -0x12`, `bltu a3, a2` to +0xac (f + 17 wraps);
     +0x5c .. +0x6c  the same check for x = f + 17, slow path +0xc0 .. +0xcc (report at +0xcc, 0x815e8); +0x70 / +0x74
                     `lbu` f[17], `bnez` to +0x9c (-1);
     +0x78 / +0x7c   `jal rp_frame_channels` (0x813a0) with a0 = n; +0x80 .. +0x98 the width test;
     +0x9c .. +0xa8  ra / s0 restored, `ret`.
   No branch to the `unimp` is taken: f == NULL is refuted by the premise `bv_unsigned a0 <> 0`, and the two wrap tests
   (f >= 2^64 - 16, f > 2^64 - 18) by addressable's f + 16 + 2 <= APPMEM_END (= 2^47). The premise
   `addressable m (f + RP_SW_OFF) RP_SW_LEN` gives the shadow byte k of each x with k = 0 \/ (x mod 8 < k <= 7)
   (AsanCells.shadow_ok): k = 0 skips the check, otherwise the `blt` is taken back to the load, so neither report call
   is reached. The frame lies in application memory (app_mem at both of its ends), no shadow byte does, so the two
   frame stores leave the shadow bytes, the GOT word, the cell, the two frame bytes and the three constants
   WIRE_RFC_CONSTS unchanged (mrd_tp / bytes_tp over the window's munch). The callee's result is image B's
   rp_frame_channels_model (lib/B/Prog/rp_frame_channels_c.v), the same definition as lib/Prog/rp_frame_channels_c.v's,
   so the width test closes with the plain walk's sw_tail. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof reac_frame_clean_len_c
  rp_frame_channels_c rp_frame_channels_F_c rp_slot_width_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_frame_channels_c rp_slot_width_c rp_slot_width.
Import ListNotations.
Open Scope Z_scope.
Module PSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width_c.
Module PFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_frame_channels_c.
Module PW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width.

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of [a, a + n). *)
Lemma rsw_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(* lib/Prog/rp_frame_channels.v a0_of / set_a0, on an evtF goal. *)
Ltac rsw_a0_of R := lazymatch R with TNode _ _ (TNode _ _ (TNode (TNode _ (Some ?w) _) _ _)) => w end.
Ltac rsw_set_a0 v := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => let w := rsw_a0_of R in replace w with v end.

(* lib/Prog/rp_slot_width.v sw_finish, on an evtF goal: release the frame and close the post. *)
Ltac rsw_finish sp :=
  lazymatch goal with
  | FR : rw_cells _ _ _ _, ST : stk _ _ _ _, MU : munch _ _ _, WM : wmono _ _ _ |- _ =>
      release_frame FR ST (bv_unsigned sp);
      apply evtF_done; do 15 eexists; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|exact ST]
  end.

(* lib/Prog/rp_slot_width.v sw_minus1: the model's first test, n < 50 or not. *)
Ltac rsw_minus1 a1 HN :=
  f_equal; unfold PSW.rp_slot_width_model, PSW.slot_byte;
  first [ rewrite (proj2 (Z.ltb_lt (bv_unsigned a1) 50) HN); reflexivity
        | rewrite (proj2 (Z.ltb_ge (bv_unsigned a1) 50) HN) ].

Theorem rp_slot_width_holds_F : rp_slot_width_F_holds_stmt.
Proof.
  unfold rp_slot_width_F_holds_stmt. intros HFC.
  unfold rp_slot_width_contract_F, RP_SLOT_WIDTH, RP_SLOT_WIDTH_STK, RP_SLOT_WIDTH_FRAME, RP_FRAME_CHANNELS_FRAME,
    RP_SW_OFF, RP_SW_LEN, WIRE_RFC_CONSTS.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    HM HT HK ST HLO APS1 APS2 CELLS DG DC HB HUB RFR RGOT RCELL OFF3 RNG3 RBUF RSH.
  change (16 + 16) with 32 in *.
  (* the three constant words, one row each of WIRE_RFC_CONSTS: (A_M, 8), (A_K36, 8), (A_T, 8) *)
  inversion_clear OFF3 as [|? ? OM OFF3a]. inversion_clear OFF3a as [|? ? OK36 OFF3b].
  inversion_clear OFF3b as [|? ? OT _].
  inversion_clear RNG3 as [|? ? RM RNG3a]. inversion_clear RNG3a as [|? ? RK RNG3b].
  inversion_clear RNG3b as [|? ? RT _].
  cbn [fst snd] in OM, OK36, OT, RM, RK, RT.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (Z.ltb_spec (bv_unsigned a1) 50) as [HN|HN].
  - (* n < 50: -1, no load and no check *)
    clear HB HUB RGOT RCELL RBUF RSH HM HT HK APS1 APS2 CELLS DG DC.
    carve_frame 16%nat ST. do 8 step. if_true. do 4 step.
    rsw_set_a0 (Z_to_bv 64 (PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2))).
    2: { rsw_minus1 a1 HN. }
    rsw_finish sp.
  - (* 50 <= n *)
    pose proof (conj HM (conj HT HK)) as HK3. clear HM HT HK.
    carve_frame 16%nat ST. do 8 step. if_false.
    match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into mf end.
    destruct HK3 as (HM & HT & HK).
    specialize (RBUF HN). specialize (RSH HN).
    destruct (HUB HN) as (NZ & W18). clear HUB.
    destruct (HB HN) as (L18 & BB & DB & ADR). clear HB.
    assert (L18z : 18 <= Z.of_nat (length bs)) by lia.
    pose proof (bytes_at_bound _ _ _ _ BB) as BBB.
    pose proof (rsw_shadow_byte_rng RNG (bv_unsigned a0 + 16) 2 0 ltac:(lia) RSH) as RS16.
    pose proof (rsw_shadow_byte_rng RNG (bv_unsigned a0 + 16) 2 1 ltac:(lia) RSH) as RS17.
    rewrite Z.add_0_r in RS16.
    replace (bv_unsigned a0 + 16 + 1) with (bv_unsigned a0 + 17) in RS17 by lia.
    clear RSH.
    destruct CELLS as (CK & GCK & _).
    destruct ADR as (P0 & N0 & PE & AB).
    destruct (AB 0 ltac:(lia)) as (APP16 & k16 & MK16 & SK16).
    destruct (AB 1 ltac:(lia)) as (APP17 & k17 & MK17 & SK17).
    clear AB.
    unfold off_stk in DB, DG, DC, OM, OT, OK36.
    unfold GOT_CELL_K, CELL_K in DG, DC, CK, GCK, RGOT, RCELL. unfold ASAN_K in CK.
    unfold shadow_addr, ASAN_K in MK16, MK17, RS16, RS17.
    unfold shadow_ok in SK16, SK17.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP16, APP17, APS1, APS2, PE.
    rewrite Z.add_0_r in APP16, MK16, SK16.
    replace (bv_unsigned a0 + 16 + 1) with (bv_unsigned a0 + 17) in APP17, MK17, SK17 by lia.
    (* what the run reads, carried over the two frame stores *)
    pose proof (bytes_tp m mf _ _ 624760 (le8 (wa 657400)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
    pose proof (bytes_tp m mf _ _ 657400 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
    pose proof (bytes_tp m mf _ _ A_M (le8 (Z_to_bv 64 KM)) MU1 ltac:(rewrite length_le8; lia) HM) as HM0.
    pose proof (bytes_tp m mf _ _ A_T (le8 (Z_to_bv 64 KT)) MU1 ltac:(rewrite length_le8; lia) HT) as HT0.
    pose proof (bytes_tp m mf _ _ A_K36 (le8 (Z_to_bv 64 K36)) MU1 ltac:(rewrite length_le8; lia) HK) as HK0.
    clear GCK CK HM HT HK.
    assert (RDG : ov_read_bytes rsegs mf (wa 624760) 8 = Some (le8 (wa 657400))).
    { replace (wa 624760) with (wa (624760 + 0)) by reflexivity.
      rewrite (bytes_at_read rsegs mf 624760 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
    assert (RDS : ov_read_bytes rsegs mf (wa 657400) 8 = Some (le8 (wa 2147450880))).
    { replace (wa 657400) with (wa (657400 + 0)) by reflexivity.
      rewrite (bytes_at_read rsegs mf 657400 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
    pose proof (mrd_tp m mf _ _ ((bv_unsigned a0 + 16) / 8 + 2147450880) _ MU1
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK16) as M16.
    pose proof (mrd_tp m mf _ _ ((bv_unsigned a0 + 17) / 8 + 2147450880) _ MU1
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK17) as M17.
    pose proof (mrd_tp m mf _ _ (bv_unsigned a0 + Z.of_nat 16) _ MU1 ltac:(lia) ltac:(lia)
      (bytes_nth m _ bs 16 BB ltac:(lia))) as F16.
    pose proof (mrd_tp m mf _ _ (bv_unsigned a0 + Z.of_nat 17) _ MU1 ltac:(lia) ltac:(lia)
      (bytes_nth m _ bs 17 BB ltac:(lia))) as F17.
    change (Z.of_nat 16) with 16 in F16. change (Z.of_nat 17) with 17 in F17.
    clear MK16 MK17.
    pose proof (Z.mod_pos_bound (bv_unsigned a0 + 16) 8 ltac:(lia)) as MB16.
    pose proof (Z.mod_pos_bound (bv_unsigned a0 + 17) 8 ltac:(lia)) as MB17.
    (* +0x20: the UBSan null check of f; NZ (f <> NULL) refutes the branch to the `unimp` *)
    step. if_false.
    (* +0x24 / +0x28: the UBSan wrap check of f + 16; PE (f + 18 <= 2^47) refutes the branch to the `unimp` *)
    step. step. if_false.
    (* +0x2c .. +0x34: the shadow base *)
    step. step. step.
    (* +0x38 .. +0x48: the shadow byte of f + 16 and its check *)
    step. gen_addi a0 w16 U16.
    pose proof (rng_sub' _ _ _ (bv_unsigned w16) 1 RBUF ltac:(lia)) as RW16.
    step. gen_shr w16 g16 G16.
    rewrite U16 in G16.
    step. gen_addi g16 h16 H16.
    pose proof (rng_sub' _ _ _ (bv_unsigned h16) 1 RS16 ltac:(lia)) as RH16.
    pose proof (rdw0 mf h16 _ _ M16 ltac:(lia)) as R. step. clear R.
    step.
    destruct SK16 as [C|[C Cu]].
    1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k16) 0) ltac:(lia)); cbn [negb]; step; step;
       rewrite land7, U16, (lts_low ((bv_unsigned a0 + 16) mod 8) k16 MB16), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    (* +0x4c / +0x50: f[16] *)
    all: remember (nth 16 bs (Z_to_bv 8 0)) as b16 eqn:E16.
    all: remember (nth 17 bs (Z_to_bv 8 0)) as b17 eqn:E17.
    all: pose proof (rdw0 mf w16 _ _ F16 ltac:(lia)) as R; step; clear R.
    all: step; if_cases HC; zify_cond HC; try rewrite zxb_u in HC.
    1, 3: do 4 step;
          rsw_set_a0 (Z_to_bv 64 (PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)));
          [ rsw_finish sp
          | rsw_minus1 a1 HN; rewrite <- E16; rewrite (proj2 (Z.eqb_neq _ 0) HC); reflexivity ].
    (* +0x54 / +0x58: the UBSan wrap check of f + 17; PE refutes the branch to the `unimp` *)
    all: step; step; if_false.
    (* +0x5c .. +0x6c: the shadow byte of f + 17 and its check *)
    all: step; gen_addi a0 w17 U17.
    all: pose proof (rng_sub' _ _ _ (bv_unsigned w17) 1 RBUF ltac:(lia)) as RW17.
    all: step; gen_shr w17 g17 G17.
    all: rewrite U17 in G17.
    all: step; gen_addi g17 h17 H17.
    all: pose proof (rng_sub' _ _ _ (bv_unsigned h17) 1 RS17 ltac:(lia)) as RH17.
    all: pose proof (rdw0 mf h17 _ _ M17 ltac:(lia)) as R; step; clear R.
    all: step.
    all: destruct SK17 as [C'|[C' Cu']].
    1, 3: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C'); cbn [negb].
    all: try (rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k17) 0) ltac:(lia)); cbn [negb]; step; step;
              rewrite land7, U17, (lts_low ((bv_unsigned a0 + 17) mod 8) k17 MB17), (proj2 (Z.ltb_lt _ _) C');
              cbn [negb]).
    (* +0x70 / +0x74: f[17] *)
    all: pose proof (rdw0 mf w17 _ _ F17 ltac:(lia)) as R; step; clear R.
    all: step; if_cases HC'; zify_cond HC'; try rewrite zxb_u in HC'.
    1, 3, 5, 7: do 4 step;
          rsw_set_a0 (Z_to_bv 64 (PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)));
          [ rsw_finish sp
          | rsw_minus1 a1 HN; rewrite <- E16, <- E17;
            rewrite (proj2 (Z.eqb_eq _ 0) HC), (proj2 (Z.eqb_neq _ 0) HC'); reflexivity ].
    (* +0x78 / +0x7c: the call; rp_frame_channels by its footprint contract on [sp - 32, sp - 16) *)
    all: step; step.
    all: eapply evtF_cut;
      [ eapply HFC with (lo := lo);
        [ exact HM0 | exact HT0 | exact HK0
        | rewrite unsigned_lit by lia; exact ST
        | unfold RP_FRAME_CHANNELS_FRAME; rewrite unsigned_lit by lia; lia
        | unfold off_stk, RP_FRAME_CHANNELS_FRAME; rewrite unsigned_lit by lia; lia
        | unfold off_stk, RP_FRAME_CHANNELS_FRAME; rewrite unsigned_lit by lia; lia
        | unfold off_stk, RP_FRAME_CHANNELS_FRAME; rewrite unsigned_lit by lia; lia
        | unfold RP_FRAME_CHANNELS_FRAME; rewrite unsigned_lit by lia; eapply rng_sub; [exact RFR | lia | lia]
        | exact RM | exact RT | exact RK ]
      | ].
    all: intros ms' (a1' & a2' & a3' & m2 & -> & MU2 & WM2 & ST2).
    all: unfold RP_FRAME_CHANNELS_FRAME in MU2.
    all: rewrite (unsigned_lit (bv_unsigned sp + -16)) in MU2, ST2 by lia.
    all: pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU2 WM2
                       ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I])) as FR2.
    all: assert (MU3 : munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m2)
           by (eapply munch_trans; [exact MU1|];
               apply (munch_weaken [(bv_unsigned sp + -16 - 16, bv_unsigned sp + -16)]); [|exact MU2];
               intros x Hx; cbn [outside] in *; destruct Hx as [Hx _]; split; [lia | exact I]).
    all: pose proof (wmono_trans _ _ _ _ WM WM2) as WM3.
    all: clear FR MU1 WM MU2 WM2 ST.
    all: replace (ret_pc (Z_to_bv 64 529820)) with (Z_to_bv 64 529820)
           by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    (* +0x80 .. +0x98: the width test; +0x9c .. +0xa8: return *)
    all: do 7 step; do 4 step.
    all: rsw_set_a0 (Z_to_bv 64 (PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)));
      [ rsw_finish sp
      | transitivity (Z_to_bv 64
          (if (PFC.rp_frame_channels_model (bv_signed a1) <? 0) || (bv_signed a2 <? 0)
              || (PFC.rp_frame_channels_model (bv_signed a1) <=? bv_signed a2)
           then -1 else PFC.rp_frame_channels_model (bv_signed a1)));
        [ rsw_minus1 a1 HN; rewrite <- E16, <- E17;
          rewrite (proj2 (Z.eqb_eq _ 0) HC), (proj2 (Z.eqb_eq _ 0) HC'); reflexivity
        | symmetry; apply PW.sw_tail; [reflexivity | apply PW.fc_model_range] ] ].
Qed.

Check (rp_slot_width_holds_F : rp_slot_width_F_holds_stmt).
