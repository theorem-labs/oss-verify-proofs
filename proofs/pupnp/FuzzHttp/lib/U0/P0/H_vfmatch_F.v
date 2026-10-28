(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_ctype H_scanner_get_token H_vfmatch_A H_vfmatch_B.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import HU_list_kit.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Ltac sstep := step; fix_lit_store.

Ltac split_chunk FR n H1 H2 :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let cs1 := eval cbv beta iota delta [firstn skipn] in (firstn n cs) in
    let cs2 := eval cbv beta iota delta [firstn skipn] in (skipn n cs) in
    change (rw_cells segs m A (cs1 ++ cs2)) in FR;
    destruct (proj1 (rw_cells_app segs m A cs1 cs2) FR) as [H1 H2]; clear FR;
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in H2;
    try (lazymatch type of H2 with rw_cells _ _ (?a + ?b + ?c)%Z _ =>
           let v := eval vm_compute in (b + c)%Z in replace (a + b + c)%Z with (a + v)%Z in H2 by lia end)
  end.

Ltac recell FR i :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn skipn] in (firstn i cs) in
    let post := eval cbv beta iota delta [firstn skipn] in (skipn (S i) cs) in
    lazymatch eval cbv beta iota delta [firstn skipn nth_error] in (nth_error cs i) with
    | Some (CB 8 ?b) => change (rw_cells segs m A (pre ++ CB 8 b :: post)) in FR; apply (rw_cells_CB_C8 segs m A pre b post) in FR; cbn [app] in FR
    | Some (CB 4 ?b) => change (rw_cells segs m A (pre ++ CB 4 b :: post)) in FR; apply (rw_cells_CB_C4 segs m A pre b post) in FR; cbn [app] in FR
    end end.

Ltac splitcb FR i sizes :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn skipn] in (firstn i cs) in
    let post := eval cbv beta iota delta [firstn skipn] in (skipn (S i) cs) in
    lazymatch eval cbv beta iota delta [firstn skipn nth_error] in (nth_error cs i) with
    | Some (CB ?n ?b) => change (rw_cells segs m A (pre ++ CB n b :: post)) in FR;
        apply (rw_cells_split_CB segs m A pre n b post sizes) in FR; [| reflexivity]; cbn [app mk_CB_cells] in FR
    end end.

Ltac name_junk FR :=
  repeat lazymatch type of FR with context [CB _ (firstn ?a ?b)] => let j := fresh "jk" in remember (firstn a b) as j in FR
                      | context [CB _ (skipn ?a ?b)] => let j := fresh "jk" in remember (skipn a b) as j in FR end;
  repeat match goal with E : _ = firstn _ _ |- _ => clear E | E : _ = skipn _ _ |- _ => clear E end.

Section VFF.
Context {HCEIL : HasCeiling}.
  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte).
  Hypothesis VOK : vf_ok q lo S MB A len cap cur0 bs.

  Notation qq := (q + -208)%Z.
  Notation W0 := [(q - 304, q - 104); (S + 8, S + 16)]%Z.
  Notation dpost := (dpost q lo S MB A len cap cur0 bs).
  Notation linv := (linv q lo S MB A len cap bs).
  Notation headst := (headst q S cur0). Notation contst := (contst q S cur0). Notation exitst := (exitst q S cur0).
  Notation SCc := (SCc S MB). Notation MBc := (MBc MB A len cap). Notation BUFc := (BUFc A bs). Notation FX := (FX q).
  Notation F0 := (F0 q). Notation F36 := (F36 q). Notation F40 := (F40 q). Notation F56 := (F56 q).
  Notation F72 := (F72 q). Notation F76 := (F76 q). Notation F84 := (F84 q). Notation F88 := (F88 q).
  Ltac sgtcall T TY cur := sgtcall_ (q + -208)%Z lo S T TY MB A cur len cap bs.

  Definition FS (m : mem) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : Prop :=
    rw_cells rsegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition vpost (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (W : list ivl) (X : mem -> Z -> Z -> Prop) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (r cur' : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo q
      /\ SCc m' cur' /\ MBc m' /\ BUFc m'
      /\ (0 <= r <= 5)%Z /\ (0 <= cur' <= len)%Z
      /\ (r = PARSE_OK -> cur0 <= cur')%Z /\ (r <> PARSE_OK -> cur' = cur0)
      /\ X m' r cur'.

  Ltac open_FX H := unfold H_vfmatch_A.FX, H_vfmatch_A.F0, H_vfmatch_A.F36, H_vfmatch_A.F40, H_vfmatch_A.F56,
                           H_vfmatch_A.F72, H_vfmatch_A.F76, H_vfmatch_A.F84, H_vfmatch_A.F88 in H;
    destruct H as (FR0 & FR36 & FR40 & FR56 & FR72 & FR76 & FR84 & FR88); dex.

  Ltac release_all :=
    repeat lazymatch goal with
    | ST : stk rsegs ?m lo ?a, FR : rw_cells rsegs ?m ?a ?cs |- _ =>
        eapply stk_release in FR; [| exact ST| lia]; clear ST; rename FR into ST;
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in ST;
        lazymatch type of ST with stk _ _ _ (?a + ?b + ?c)%Z =>
          let v := eval vm_compute in (b + c)%Z in replace (a + b + c)%Z with (a + v)%Z in ST by lia end
    end; try match goal with ST : stk rsegs _ lo (?a + 0)%Z |- _ => rewrite Z.add_0_r in ST end.

  Notation WF Wx := ((lo, q) :: (S + 8, S + 16) :: Wx)%Z.

  Definition rframe (R : mem -> Prop) : Prop :=
    forall m m', R m -> munch [(lo, q); (S + 8, S + 16)]%Z m m' -> wmono rsegs m m' -> R m'.

  #[using="VOK"] Lemma tail_ret : forall (r cur' : Z) (Wx : list ivl) (R : mem -> Prop) (XP : Z -> Z -> Prop)
      ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc m0
      x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m,
    FS m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 -> FX m -> stk rsegs m lo qq ->
    SCc m cur' -> MBc m -> BUFc m -> mem_inv rsegs m -> munch (WF Wx) m0 m -> wmono rsegs m0 m ->
    (0 <= r <= 5)%Z -> (0 <= cur' <= len)%Z -> (r = PARSE_OK -> cur0 <= cur')%Z -> (r <> PARSE_OK -> cur' = cur0) ->
    R m -> XP r cur' ->
    evt rsegs (vpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WF Wx) (fun m' r c => R m' /\ XP r c) m0)
      (MS (mkR x1 (wz qq) gp tp x5 x6 x7 x8 x9 (wz r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (wz 0x148c0) fc None m (seg_rom rsegs)).
  Proof.
    vok VOK.
    intros until m. intros FSH FXH ST SC MBC BUF MI MU WM HR HC HOK HNOK HRm HX.
    unfold FS in FSH. open_FX FXH.
    do 14 zstep.
    release_all.
    zstep. apply evt_done. unfold vpost. exists r, cur'. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. repeat (split; [assumption|]). exact HX.
  Qed.

  #[using="VOK"] Lemma tail_err : forall (r cur' : Z) (Wx : list ivl) (R : mem -> Prop) (XP : Z -> Z -> Prop)
      ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc m0
      x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 m,
    FS m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 -> FX m -> stk rsegs m lo qq ->
    SCc m cur' -> MBc m -> BUFc m -> mem_inv rsegs m -> munch (WF Wx) m0 m -> wmono rsegs m0 m ->
    (0 <= r <= 5)%Z -> r <> PARSE_OK -> R m -> rframe R -> XP r cur0 ->
    evt rsegs (vpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WF Wx) (fun m' r c => R m' /\ XP r c) m0)
      (exitst gp tp F fc r x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros FSH FXH ST SC MBC BUF MI MU WM HR HNOK HRm RF HX. unfold H_vfmatch_A.exitst. unfold PARSE_OK in HNOK.
    unfold FS in FSH. open_FX FXH. unfold H_vfmatch_A.SCc, H_vfmatch_A.MBc, H_vfmatch_A.BUFc, mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
    pose proof (munch_refl [(lo, q); (S + 8, S + 16)]%Z m) as MU2. pose proof (wmono_refl rsegs m) as WM2.
    zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|]. sstep.
    eapply tail_ret; try eassumption; try LiaTuning.alia.
    - unfold H_vfmatch_A.FX, H_vfmatch_A.F0, H_vfmatch_A.F36, H_vfmatch_A.F40, H_vfmatch_A.F56, H_vfmatch_A.F72, H_vfmatch_A.F76, H_vfmatch_A.F84, H_vfmatch_A.F88.
      repeat match goal with |- _ /\ _ => split end;
      repeat (lazymatch goal with |- ex _ => eexists end); eassumption.
    - eapply RF; [exact HRm| exact MU2| exact WM2].
  Qed.

  Ltac unfx := unfold H_vfmatch_A.SCc, H_vfmatch_A.MBc, H_vfmatch_A.BUFc, mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  Ltac close_FX := unfold H_vfmatch_A.FX, H_vfmatch_A.F0, H_vfmatch_A.F36, H_vfmatch_A.F40, H_vfmatch_A.F56, H_vfmatch_A.F72, H_vfmatch_A.F76, H_vfmatch_A.F84, H_vfmatch_A.F88;
      repeat match goal with |- _ /\ _ => split end;
      repeat (lazymatch goal with |- ex _ => eexists end); eassumption.

  #[using="VOK"] Lemma cont_err : forall (r cur' fp' G' : Z) (b : byte) (Wx : list ivl) (R : mem -> Prop) (XP : Z -> Z -> Prop)
      ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc m0
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 m,
    FS m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 -> FX m -> stk rsegs m lo qq ->
    SCc m cur' -> MBc m -> BUFc m -> mem_inv rsegs m -> munch (WF Wx) m0 m -> wmono rsegs m0 m ->
    ov_read_bytes rsegs m (wa fp') 1 = Some [b] -> (0 < fp' /\ fp' + 1 < 2^63)%Z ->
    (0 <= r <= 5)%Z -> r <> PARSE_OK -> R m -> rframe R -> XP r cur0 ->
    evt rsegs (vpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WF Wx) (fun m' r c => R m' /\ XP r c) m0)
      (contst gp tp F fc r fp' G' x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros FSH FXH ST SC MBC BUF MI MU WM RD FP HR HNOK HRm RF HX. unfold H_vfmatch_A.contst.
    pose proof (byte_lt256 b) as BR. unfold PARSE_OK in HNOK.
    zstep. ub_null. zstep. zstep. rewrite (STRW_merge.swrap32_small (r + 0)) by lia. rewrite Z.add_0_r.
    zstep. if_cases K0; zify_cond K0.
    - eapply tail_err; try eassumption; unfold PARSE_OK; lia.
    - zstep. if_cases K1; zify_cond K1; try (exfalso; lia).
      eapply tail_err; try eassumption; unfold PARSE_OK; lia.
  Qed.

  #[using="VOK"] Lemma cont_end : forall (cur' fp' G' : Z) (b : byte) (Wx : list ivl) (R : mem -> Prop) (XP : Z -> Z -> Prop)
      ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc m0
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 m,
    FS m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 -> FX m -> stk rsegs m lo qq ->
    SCc m cur' -> MBc m -> BUFc m -> mem_inv rsegs m -> munch (WF Wx) m0 m -> wmono rsegs m0 m ->
    ov_read_bytes rsegs m (wa fp') 1 = Some [b] -> bv_unsigned b = 0 -> (0 < fp' /\ fp' + 1 < 2^63)%Z ->
    (cur0 <= cur' <= len)%Z -> R m -> XP 4 cur' ->
    evt rsegs (vpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WF Wx) (fun m' r c => R m' /\ XP r c) m0)
      (contst gp tp F fc 4 fp' G' x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros FSH FXH ST SC MBC BUF MI MU WM RD Hb FP HC HRm HX. unfold H_vfmatch_A.contst.
    zstep. ub_null. zstep. cbn beta. rewrite Hb. zstep. try (replace (bv_swrap 32 (4 + 0)) with 4%Z by (vm_compute; reflexivity)).
    zstep. if_cases K0; zify_cond K0; [| exfalso; lia].
    zstep. zstep. if_cases K1; zify_cond K1; [| exfalso; lia].
    eapply tail_ret; try eassumption; unfold PARSE_OK; try lia.
  Qed.

  #[using="lo MB A len cap cur0 bs VOK"] Lemma cont_next : forall (Q : machine_state -> Prop) (c fp' G' : Z) (b : byte) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 m,
    ov_read_bytes rsegs m (wa fp') 1 = Some [b] -> bv_unsigned b = c -> c <> 0 -> (0 < fp' /\ fp' + 1 < 2^63)%Z ->
    evt rsegs Q (headst gp tp F fc fp' c G' x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 m) ->
    evt rsegs Q (contst gp tp F fc 4 fp' G' x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros RD Hb Hc FP H. unfold H_vfmatch_A.contst. pose proof (byte_lt256 b) as BR.
    zstep. ub_null. zstep. cbn beta. rewrite Hb. zstep. try (replace (bv_swrap 32 (4 + 0)) with 4%Z by (vm_compute; reflexivity)).
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    zstep. if_cases K1; zify_cond K1; try (exfalso; lia).
    exact H.
  Qed.

  #[using="A len cap bs VOK"] Lemma prologue : forall (fp0 c0 G : Z) (b0 : byte) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> SCc m cur0 ->
    (forall m1, mem_inv rsegs m1 -> ov_read_bytes rsegs m1 (wa fp0) 1 = Some [b0]) -> bv_unsigned b0 = c0 -> c0 <> 0 -> (0 < fp0 /\ fp0 + 1 < 2^63)%Z ->
    evt rsegs (fun ms' => exists m',
        ms' = headst gp tp F fc fp0 c0 G ra t0 t1 t2 (wz G) a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 m'
        /\ munch [(q - 208, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo qq /\ FS m' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 /\ FX m' /\ (exists w8, F0 m' w8 1))
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz fp0) (wz G) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz vfmatch_entry) fc None m (seg_rom rsegs)).
  Proof.
    vok VOK.
    intros until m. intros ST MI SC RD Hb Hc FP. unfold vfmatch_entry. unfx.
    pose proof (munch_refl [(q - 208, q)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB. pose proof (byte_lt256 b0) as BR.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 208%nat ST. rewrite !E in *.
    do 14 sstep.
    zstep. ub_align. zstep. zstep. zstep.
    do 9 zstep. sstep. zstep. zstep. sstep. zstep.
    pose proof (RD _ MI) as RD0.
    zstep. ub_null. zstep. cbn beta. rewrite Hb. zstep. try (replace (bv_swrap 32 (4 + 0)) with 4%Z by (vm_compute; reflexivity)).
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    zstep. if_cases K1; zify_cond K1; try (exfalso; lia).
    name_junk FR.
    splitcb FR 0%nat [8;8]%nat. name_junk FR. recell FR 1%nat.
    splitcb FR 4%nat [4;4;8;8;8;8;4;8;4;8;8]%nat. name_junk FR.
    recell FR 5%nat. recell FR 6%nat. recell FR 7%nat. recell FR 8%nat. recell FR 9%nat. recell FR 10%nat.
    recell FR 12%nat. recell FR 13%nat. recell FR 14%nat.
    split_chunk FR 5%nat FR0 R1. split_chunk R1 1%nat FR36 R2. split_chunk R2 2%nat FR40 R3. split_chunk R3 2%nat FR56 R4.
    split_chunk R4 1%nat FR72 R5. split_chunk R5 1%nat FR76 R6. split_chunk R6 1%nat FR84 R7. split_chunk R7 2%nat FR88 FSH.
    apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact FSH|]. close_FX.
  Qed.

  #[using="Type"] Lemma vpost_mono : forall (X1 X2 : mem -> Z -> Z -> Prop) ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W m0 ms,
    (forall m r c, X1 m r c -> X2 m r c) ->
    vpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W X1 m0 ms -> vpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W X2 m0 ms.
  Proof.
    intros until ms. intros IMP V. unfold vpost in *. destruct_exs V.
    repeat (lazymatch goal with |- ex _ => eexists end).
    repeat (lazymatch goal with |- _ /\ _ => split; [apply V|]; apply proj2 in V end). apply IMP. exact V.
  Qed.

  #[using="Type"] Lemma fmt_rd : forall m a fb (i : nat) c, bytes_at rsegs m a fb -> nth_error fb i = Some (Z_to_bv 8 c) ->
    ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [Z_to_bv 8 c].
  Proof.
    intros m a fb i c B N. pose proof (nth_error_lt _ _ _ N) as L.
    rewrite (bytes_at_read rsegs m a fb (Z.of_nat i) 1 B) by lia. rewrite Nat2Z.id.
    f_equal. rewrite <- (firstn_skipn i fb) in N. rewrite nth_error_app2 in N by (rewrite firstn_length; lia).
    rewrite firstn_length, Nat.min_l, Nat.sub_diag in N by lia.
    destruct (skipn i fb) as [|x l]; [discriminate|]. cbn in N. injection N as ->. reflexivity.
  Qed.

End VFF.

Ltac unfx := unfold H_vfmatch_A.SCc, H_vfmatch_A.MBc, H_vfmatch_A.BUFc, mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
Ltac open_FX H := unfold H_vfmatch_A.FX, H_vfmatch_A.F0, H_vfmatch_A.F36, H_vfmatch_A.F40, H_vfmatch_A.F56,
                         H_vfmatch_A.F72, H_vfmatch_A.F76, H_vfmatch_A.F84, H_vfmatch_A.F88 in H;
  destruct H as (FR0 & FR36 & FR40 & FR56 & FR72 & FR76 & FR84 & FR88); dex.
Ltac release_all_ lo :=
  repeat lazymatch goal with
  | ST : stk rsegs ?m lo ?a, FR : rw_cells rsegs ?m ?a ?cs |- _ =>
      eapply stk_release in FR; [| exact ST| lia]; clear ST; rename FR into ST;
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in ST;
      lazymatch type of ST with stk _ _ _ (?a + ?b + ?c)%Z =>
        let v := eval vm_compute in (b + c)%Z in replace (a + b + c)%Z with (a + v)%Z in ST by lia end
  end; try match goal with ST : stk rsegs _ lo (?a + 0)%Z |- _ => rewrite Z.add_0_r in ST end.
Ltac close_FX := unfold H_vfmatch_A.FX, H_vfmatch_A.F0, H_vfmatch_A.F36, H_vfmatch_A.F40, H_vfmatch_A.F56, H_vfmatch_A.F72, H_vfmatch_A.F76, H_vfmatch_A.F84, H_vfmatch_A.F88;
    repeat match goal with |- _ /\ _ => split end;
    repeat (lazymatch goal with |- ex _ => eexists end); eassumption.
Ltac post_dir m r cur HX :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO;
  repeat match goal with
    | H : stk rsegs m _ _ |- _ => clear H
    | H : rw_cells rsegs m _ [C8 _; C8 _; C4 (Z_to_bv 64 0)] |- _ => clear H
    | H : rw_cells rsegs m _ [C8 _; C8 _; C8 _; C8 (Z_to_bv 64 5)] |- _ => clear H
    | H : bytes_at rsegs m _ _ |- _ => clear H
    | H : H_vfmatch_A.SCc _ _ m _ |- _ => clear H | H : H_vfmatch_A.MBc _ _ _ _ m |- _ => clear H
    | H : H_vfmatch_A.BUFc _ _ m |- _ => clear H end;
  let HC := fresh "HC" in let HR := fresh "HR" in
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIn := fresh "MIn" in
  destruct PO as [PO|PO]; destruct PO as [r [cur PO]]; destruct_exs PO;
  [ destruct PO as (E & MUc & WMc & MIn & ST & SC & MBC & BUF & FXH & F0H & HC & HR & HX)
  | destruct PO as (E & MUc & WMc & MIn & ST & SC & MBC & BUF & FXH & HC & HR & HX & HXE) ];
  subst ms';
  lazymatch type of MUc with munch _ _ ?m' =>
    transport_after_call rsegs m m' MUc WMc; clear MUc WMc;
    try match goal with H : mem_inv rsegs m |- _ => clear H end; rename MIn into MI; try clear m end.
Ltac dside := first [ eassumption | reflexivity | lia
                    | (unfold H_vfmatch_A.F0, H_vfmatch_A.F36, H_vfmatch_A.F40, H_vfmatch_A.F56, H_vfmatch_A.F72, H_vfmatch_A.F76, H_vfmatch_A.F84, H_vfmatch_A.F88;
                       repeat (lazymatch goal with |- ex _ => eexists end); eassumption)
                    | idtac ].
Ltac dcall LEM r cur HX := try unfold H_vfmatch_A.headst;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [eapply LEM; dside | post_dir m r cur HX] end.

Ltac rdfmt FBAT BASE :=
  lazymatch goal with |- ov_read_bytes _ ?m (wa ?a) 1 = Some _ =>
    let i := eval vm_compute in (Z.to_nat (a - BASE)) in
    replace (wa a) with (wa (BASE + Z.of_nat i)) by (unfold wa; f_equal; lia);
    eapply (fmt_rd m BASE _ i); [apply FBAT; assumption| reflexivity] end.

Ltac use_ok := unfold PARSE_OK in *; repeat match goal with H : 4 = 4 -> _ |- _ => specialize (H eq_refl) end.

Ltac rf1 H MUR WMR := eapply (rw_cells_transport rsegs _ _ _ _ _ H MUR WMR); cbn [disjoint_from]; simpl_sizes; lia.

Ltac err1 P FBAT BASE XT :=
  lazymatch goal with PCH : rw_cells rsegs _ P [C8 ?pa; C8 ?pb] |- _ =>
  eapply evt_mono;
  [ first [ eapply cont_err with (R := fun mm => rw_cells rsegs mm P [C8 pa; C8 pb]) (XP := fun r c => r <> PARSE_OK)
          | eapply tail_err with (R := fun mm => rw_cells rsegs mm P [C8 pa; C8 pb]) (XP := fun r c => r <> PARSE_OK) ];
    try eassumption; try rdfmt FBAT BASE; try (unfold PARSE_OK in *; lia);
    unfold rframe; intros mA mB HRR MUR WMR; rf1 HRR MUR WMR
  | intros ms' V; eapply vpost_mono; [| exact V]; cbn beta; intros mm rr cc [HRm HXP];
    unfold XT; do 2 eexists; split; [exact HRm|]; let E := fresh in intros E; exfalso; exact (HXP E) ] end.

Ltac err2 P1 P2 FBAT BASE XT :=
  lazymatch goal with PC1 : rw_cells rsegs _ P1 [C8 ?pa; C8 ?pb], PC2 : rw_cells rsegs _ P2 [C8 ?pc; C8 ?pd] |- _ =>
  eapply evt_mono;
  [ first [ eapply cont_err with (R := fun mm => rw_cells rsegs mm P1 [C8 pa; C8 pb] /\ rw_cells rsegs mm P2 [C8 pc; C8 pd]) (XP := fun r c => r <> PARSE_OK)
          | eapply tail_err with (R := fun mm => rw_cells rsegs mm P1 [C8 pa; C8 pb] /\ rw_cells rsegs mm P2 [C8 pc; C8 pd]) (XP := fun r c => r <> PARSE_OK) ];
    try eassumption; try rdfmt FBAT BASE; try (unfold PARSE_OK in *; lia); try (split; assumption);
    unfold rframe; intros mA mB [HQ1 HQ2] MUR WMR; split; [rf1 HQ1 MUR WMR| rf1 HQ2 MUR WMR]
  | intros ms' V; eapply vpost_mono; [| exact V]; cbn beta; intros mm rr cc [[HRm1 HRm2] HXP];
    unfold XT; do 4 eexists; split; [exact HRm1|]; split; [exact HRm2|]; let E := fresh in intros E; exfalso; exact (HXP E) ] end.
Ltac err3 P1 P2 P3 FBAT BASE XT :=
  lazymatch goal with PC1 : rw_cells rsegs _ P1 [C8 ?pa; C8 ?pb], PC2 : rw_cells rsegs _ P2 [C8 ?pc; C8 ?pd], PC3 : rw_cells rsegs _ P3 [C8 ?pe; C8 ?pf] |- _ =>
  eapply evt_mono;
  [ first [ eapply cont_err with (R := fun mm => rw_cells rsegs mm P1 [C8 pa; C8 pb] /\ rw_cells rsegs mm P2 [C8 pc; C8 pd] /\ rw_cells rsegs mm P3 [C8 pe; C8 pf]) (XP := fun r c => r <> PARSE_OK)
          | eapply tail_err with (R := fun mm => rw_cells rsegs mm P1 [C8 pa; C8 pb] /\ rw_cells rsegs mm P2 [C8 pc; C8 pd] /\ rw_cells rsegs mm P3 [C8 pe; C8 pf]) (XP := fun r c => r <> PARSE_OK) ];
    try eassumption; try rdfmt FBAT BASE; try (unfold PARSE_OK in *; lia); try (split; [assumption| split; assumption]);
    unfold rframe; intros mA mB [HQ1 [HQ2 HQ3]] MUR WMR; split; [rf1 HQ1 MUR WMR| split; [rf1 HQ2 MUR WMR| rf1 HQ3 MUR WMR]]
  | intros ms' V; eapply vpost_mono; [| exact V]; cbn beta; intros mm rr cc [[HRm1 [HRm2 HRm3]] HXP];
    unfold XT; do 6 eexists; split; [exact HRm1|]; split; [exact HRm2|]; split; [exact HRm3|]; let E := fresh in intros E; exfalso; exact (HXP E) ] end.

