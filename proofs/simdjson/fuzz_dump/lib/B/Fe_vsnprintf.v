(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import SFModel Arr SysStep ImageA FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Monad PrintfModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Printf_mlib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import FX_lib F_memset F_memcpy F_fwritex Fe_pop_arg Fe_printf_iface Fe_printf_core.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Printf_sn.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Fe_printf_snsink F_sn_write F_towrite Fe_vfprintf.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Fe_pkit R_m2s I_consts I_qck F_achk I_memsetw Fe_icalls.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import PrintfModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_begin_rw sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Lemma rw_cells_recast : forall m A cs cs', rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells bsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma rw_cells_C4_eqv : forall m A pre v v' post, rw_cells bsegs m A (pre ++ C4 v :: post) -> le4 v = le4 v' -> rw_cells bsegs m A (pre ++ C4 v' :: post).
Proof.
  intros m A pre v v' post H E. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 [_ W2]]. apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
Qed.

Ltac c4_eqv H k v' :=
  lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
    lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some (C4 ?v) =>
      let H' := fresh in
      pose proof (rw_cells_C4_eqv m A pre v v' post) as H'; cbn [app] in H';
      specialize (H' H ltac:(unfold le4; cbn [Z_to_le_bytes]; repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity)); clear H; rename H' into H
    end end.

Lemma arg_ok_relayout_g : forall F0 B0 BS0 ap0 Fp' B' BS' m lo sp ap' sp' w a,
  arg_ok F0 B0 BS0 m lo sp ap0 w a -> lo <= Fp' -> Fp' + 232 <= sp -> lo <= B' -> B' + BS' <= sp -> lo <= ap' -> ap' + 8 <= sp -> sp' <= sp ->
  arg_ok Fp' B' BS' m lo sp' ap' w a.
Proof.
  intros F0 B0 BS0 ap0 Fp' B' BS' m lo sp ap' sp' w a H H1 H2 H3 H4 H5 H6 H7. destruct a as [s| |i|u|u|d|i]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4 & CK). exists slack.
  repeat (split; [first [assumption | lia]|]). exact CK.
Qed.
Lemma args_ok_relayout_g : forall F0 B0 BS0 ap0 Fp' B' BS' m lo sp ap' sp' ws args,
  args_ok F0 B0 BS0 m lo sp ap0 ws args -> lo <= Fp' -> Fp' + 232 <= sp -> lo <= B' -> B' + BS' <= sp -> lo <= ap' -> ap' + 8 <= sp -> sp' <= sp ->
  args_ok Fp' B' BS' m lo sp' ap' ws args.
Proof.
  intros F0 B0 BS0 ap0 Fp' B' BS' m lo sp ap' sp' ws args. revert ws. induction args as [|a args IH]; intros ws H H1 H2 H3 H4 H5 H6 H7; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [Ha Hr].
  split; [eapply arg_ok_relayout_g; eassumption | apply IH; assumption].
Qed.

Definition VSN_FRAME : Z := 304.
Definition IVF_DEPTH : Z := 7904.
Definition VSN_DEPTH : Z := 8208.
Definition VSN_W (lo q D : Z) (dn : nat) : list (Z * Z) := [(lo, q); (D, D + Z.of_nat dn)].

Definition vsnprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (D : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells bsegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)].

Section VSN.
Hypothesis RIP : rip_stmt.

Variable PCOK : list Z -> list parg -> list word -> Z -> Z -> Z -> mem -> Prop.

Definition e_vfprintf_stub : Z := 0x69f94.
Definition ivfsn_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (Fp CK D n bufp A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells bsegs m Fp (snfile_head 0 0 0 bufp 0 (Z_to_bv 64 0)) -> rw_cells bsegs m (Fp + 148) (snfile_rest CK) ->
    rw_cells bsegs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
    rw_cells bsegs m D [CB dn junkd] ->
    bytes_at bsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> args_ok Fp (q - 400) 80 m lo q (q - 416) slots args ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    fpcalls_sn_ok fmt args ->
    (length o < dn)%nat -> (zlength o <= n < 2^63) -> (0 < bufp < 2^64) ->
    stk bsegs m lo q -> (lo <= q - IVF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q <= 2^47) -> (q mod 16 = 0) ->
    ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT \/ (VA + 8 * zlength slots <= A /\ A + zlength fmt <= 2^62)) ->
    (q <= Fp) -> (Fp + 232 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (q <= CK) -> (CK + 16 <= Fp \/ Fp + 232 <= CK) -> (CK + 16 < 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= Fp \/ Fp + 232 <= D) -> (D + Z.of_nat dn <= CK \/ CK + 16 <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    (kHighShadowEnd + 8 <= lo) -> ictx m -> (forall p n, lo <= p -> p + n <= q -> chkr m p n) ->
    chkr m A (zlength fmt) -> rod_chk m -> chkr m D (zlength o) -> (D + Z.of_nat dn <= SHADOW_LO \/ SHADOW_HI <= D) ->
    rod_chk_fp m -> ifx_real m ->
    PCOK fmt args slots A VA lo m ->
    evt bsegs (vfprintf_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D n dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 e_vfprintf_stub) fc None m (seg_rom bsegs)).
Hypothesis IVF : ivfsn_stmt.

Definition vsnprintf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z) (F0 B0 BS0 ap0 : Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells bsegs m D [CB dn junkd] ->
    bytes_at bsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> (forall m', munch (VSN_W lo q D dn) m m' -> args_ok F0 B0 BS0 m' lo q ap0 slots args) ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    fpcalls_sn_ok fmt args ->
    (length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
    stk bsegs m lo q -> (lo <= q - VSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT \/ (VA + 8 * zlength slots <= A /\ A + zlength fmt <= 2^62)) ->
    (D + Z.of_nat dn <= A \/ A + zlength fmt <= D) ->
    (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->

    (q <= 2^47) -> (q mod 16 = 0) ->
    (kHighShadowEnd + 8 <= lo) -> ictx m -> (forall p n, lo <= p -> p + n <= q -> chkr m p n) ->
    chkr m A (zlength fmt) -> rod_chk m -> chkr m D (zlength o) -> (D + Z.of_nat dn <= SHADOW_LO \/ SHADOW_HI <= D) ->
    rod_chk_fp m -> ifx_real m ->
    (forall m', munch (VSN_W lo q D dn) m m' -> wmono bsegs m m' -> PCOK fmt args slots A VA lo m') ->
    evt bsegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15e39c) fc None m (seg_rom bsegs)).

Theorem vsnprintf_proof : vsnprintf_stmt.
Proof using RIP IVF.
  unfold vsnprintf_stmt. intros until ap0. cbv zeta.
  intros -> -> -> -> DST BY HF P1 VAA AOK MODEL FPF ROOM Hn Hn1 ST LO GLO QHI SSP MI FRM HA0 HA DFMT QVA VAHI DD1 DVA GD
    HQ47 HQ16 HSH IC STKC FMTC ROD CHD DSH RODFP IFX PCO.
  unfold VSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT, VSN_W in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
  pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 304%nat ST.
  zidle_begin_rw sp 304%Z MUz WMz.
  do 9 zs.
  do 3 zs.
  zidle_end MUz WMz.
  zs. zs. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  zs. zs. zs. zs. zs.

  replace (n <? n + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.add].
  change (Z.land (0 + -1) 18446744073709551615) with 18446744073709551615.
  replace (Z.land 18446744073709551615 (n + -1)) with (n + -1)
    by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  zs. zs. zs. zs. zs.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -304)%Z (CB 232 ?j :: _) |- _ => rename H into FRv; set (j0 := j) in FRv; clearbody j0 end.
  match type of FRv with rw_cells _ _ _ [_; _; _; CB 8 ?j; _; _; _; _; _; _] => set (j8 := j) in FRv; clearbody j8 end.
  apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FRv. destruct FRv as [FZ FRv]. cbn [cells_size csize Nat.add app] in FRv.
  replace (bv_unsigned sp + -304 + Z.of_nat 232)%Z with (bv_unsigned sp + -72)%Z in FRv by lia.

  zs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CHF : chk_ok mm (bv_unsigned sp + -304) 232)
      by (apply chkr_chk_ok; apply (chkr_munch _ m mm _ _ (STKC (bv_unsigned sp + -304) 232 ltac:(lia) ltac:(lia)) MU);
          intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia);
    assert (IC2 : ictx mm) by (apply (ictx_munch _ m mm IC MU WM); intros ?x ?Hx; cbn [in_rl ICR outside] in *; unfold kHighShadowEnd in *; lia) end.
  zstep.
  eapply evt_cut.
  { destruct IC2 as (_ & ICM & _ & M2S).
    eapply (imemset_spec RIP) with (d := bv_unsigned sp + -304) (C := 0) (n := 232) (lo := lo);
      rewrite ?unsigned_lit by lia; unfold kHighShadowEnd in *;
      [ reflexivity | reflexivity | reflexivity | match goal with H : stk _ _ lo _ |- _ => exact H end | lia | lia | lia | lia | lia | lia | lia | lia
      | cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact FZ | exact CHF | exact M2S | exact ICM | assumption ]. }
  cbv beta. intros ms' P. unfold imemset_post in P. rewrite !unsigned_lit in P by lia.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m2 & -> & MUc & WMc & MI2 & STc & FZ').
  clear FZ CHF.
  rewrite ?unsigned_lit in MUc, STc by lia.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m2 MUc WMc; clear MUc WMc; try clear MI end.
  try clear ST. rename STc into ST.
  fix_ret.
  change (Z.to_nat 232) with 232%nat in FZ'. change (0 mod 256) with 0 in FZ'.

  pose proof (rw_cells_recast _ _ _ (gfile_cells (Z_to_bv 64 0) 0 0 0 0 0 0 0 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) 0 ++ snfile_rest 0) FZ'
                ltac:(cbn [cells_wf cell_wf gfile_cells snfile_rest app]; repeat split) ltac:(vm_compute; reflexivity)) as FC. clear FZ'.
  unfold gfile_cells, snfile_rest in FC. cbn [app] in FC.
  do 10 zs.
  c4_eqv FC 20%nat (Z_to_bv 64 4294967295). c4_eqv FC 21%nat (Z_to_bv 64 4294967295).

  pose proof (rw_CB_length _ _ _ _ DST) as LJ.
  pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
  pose proof (u8arr_store_ok bsegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJ; lia) ltac:(f_equal; lia)) as SOK.
  zs. rewrite le1_zero. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia).
  pose proof (u8arr_write bsegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJ; lia)) as DA2. clear DA. store_done.
  pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJ in DST. clear DA2.
  zs. zs. zs. zs.

  apply (proj1 (rw_cells_app bsegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in FC. destruct FC as [FH FR]. cbn [cells_size csize Nat.add app] in FR.
  replace (bv_unsigned sp + -304 + Z.of_nat 148)%Z with (bv_unsigned sp + -304 + 148)%Z in FR by lia.
  apply (proj1 (rw_cells_app bsegs _ _ [_;_] _)) in FRv. destruct FRv as [CKC FRv]. cbn [cells_size csize Nat.add app] in FRv.
  replace (bv_unsigned sp + -72 + Z.of_nat 16)%Z with (bv_unsigned sp + -56)%Z in FRv by lia.
  pose proof IVF as VF. unfold ivfsn_stmt, e_vfprintf_stub in VF.
  eapply evt_cut.
  { eapply VF with (Fp := bv_unsigned sp + -304) (CK := bv_unsigned sp + -72) (D := D) (n := n + -1) (bufp := bv_unsigned sp + -49) (A := A) (VA := VA)
                   (dn := dn) (junkd := upd junkd (Z.to_nat 0) (Z_to_bv 8 0)) (fmt := fmt) (slots := slots) (args := args) (lo := lo) (canary := canary) (r := r) (o := o);
      clear VF; rewrite ?unsigned_lit by lia; unfold IVF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength.
    all: try reflexivity.
    all: try lia.
    all: try first [ exact DSH | exact I
               | (apply PCO; [exact MU | exact WM])
               | (apply (ictx_munch _ m _ IC MU WM); intros ?x ?Hx; cbn [in_rl ICR outside] in *; unfold kHighShadowEnd in *; lia)
               | (intros p n' Hp1 Hp2; apply (chkr_munch _ m _ p n' (STKC p n' Hp1 ltac:(lia)) MU);
                  intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia)
               | (apply (chkr_munch _ m _ _ _ FMTC MU); intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia)
               | (destruct ROD as (R1 & R2 & R3); split; [| split];
                  [apply (chkr_munch _ m _ _ _ R1 MU) | apply (chkr_munch _ m _ _ _ R2 MU) | apply (chkr_munch _ m _ _ _ R3 MU)];
                  intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia)
               | (destruct RODFP as (R1 & R2 & R3 & R4 & R5 & R6); split; [|split; [|split; [|split; [|split]]]];
                  [apply (chkr_munch _ m _ _ _ R1 MU) | apply (chkr_munch _ m _ _ _ R2 MU) | apply (chkr_munch _ m _ _ _ R3 MU)
                  | apply (chkr_munch _ m _ _ _ R4 MU) | apply (chkr_munch _ m _ _ _ R5 MU) | apply (chkr_munch _ m _ _ _ R6 MU)];
                  intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia)
               | (unfold ifx_real in *; eapply ro_cells_transport; [exact IFX | exact MU |]; cbn [disjoint_from cells_size csize];
                  unfold kHighShadowEnd in *; lia)
               | (unfold zlength in CHD; apply (chkr_munch _ m _ _ _ CHD MU); intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia)
               | (unfold kHighShadowEnd in *; lia) ].
    - unfold snfile_head, gfile_cells. exact FH.
    - unfold snfile_rest. exact FR.
    - exact CKC.
    - exact DST.
    - exact BY.
    - exact HF.
    - exact P1.
    - exact VAA.
    - eapply args_ok_relayout_g; [apply AOK; exact MU | lia | lia | lia | lia | lia | lia | lia].
    - exact MODEL.
    - exact FPF.
    - exact ST.
    - split; [exact SSP1 | exact SSP2].
    - exact MI2.
    - exact FRM. }
  cbv beta. intros ms' P. clear VF.
  unfold vfprintf_sn_post in P. rewrite !unsigned_lit in P by lia.
  destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & fjunk & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SSP3 & DST3 & CK3 & FJ3).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m3 MUc WMc; clear MUc WMc; try clear MI2 end.
  fix_ret.
  clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

  zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
  do 7 zs.
  lazymatch goal with FJ : rw_cells _ ?mm (bv_unsigned sp + -304)%Z _, CK : rw_cells _ ?mm (bv_unsigned sp + -72)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -56)%Z _ |- _ =>
    assert (FALL : rw_cells bsegs mm (bv_unsigned sp + -304) ([CB 232 fjunk] ++ [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n + -1 - zlength o))] ++ [CB 8 j8; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
    [ apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [exact FJ|];
      apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact CK | lia] |];
      cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
    | clear FJ CK FR ] end.
  cbn [app] in FALL.
  release_frame FALL ST3 (bv_unsigned sp).
  apply evt_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST3|].
  split; [split; [exact SSP1 | exact SSP2]|].
  rewrite upd_firstn_skipn in DST3 by (rewrite LJ; lia). change (Z.to_nat 0) with 0%nat in DST3.
  change (firstn 0 junkd) with (@nil byte) in DST3. rewrite app_nil_l in DST3.
  change (skipn (S (length o)) (Z_to_bv 8 0 :: skipn 1 junkd)) with (skipn (length o) (skipn 1 junkd)) in DST3.
  rewrite skipn_skipn, Nat.add_1_r in DST3. exact DST3.
Qed.

End VSN.

Definition e_vsnprintf_stub : Z := 0x69f98.
Definition IVSN_DEPTH : Z := 10368.
Definition ivsn_stmt (PCOK2 : list Z -> list parg -> list word -> Z -> Z -> Z -> mem -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z) (F0 B0 BS0 ap0 : Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells bsegs m D [CB dn junkd] ->
    bytes_at bsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> (forall m', munch (VSN_W lo q D dn) m m' -> args_ok F0 B0 BS0 m' lo q ap0 slots args) ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    fpcalls_sn_ok fmt args ->
    (length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
    stk bsegs m lo q -> (lo <= q - IVSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT \/ (VA + 8 * zlength slots <= A /\ A + zlength fmt <= 2^62)) ->
    (D + Z.of_nat dn <= A \/ A + zlength fmt <= D) ->
    (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    (q <= 2^47) -> (q mod 16 = 0) ->
    (kHighShadowEnd + 8 <= lo) -> ictx m -> (forall p n, lo <= p -> p + n <= q -> chkr m p n) ->
    chkr m A (zlength fmt) -> rod_chk m -> chkr m D (zlength o + 1) -> (D + Z.of_nat dn <= SHADOW_LO \/ SHADOW_HI <= D) ->
    rod_chk_fp m -> ifx_real m ->
    (forall m', munch (VSN_W lo q D dn) m m' -> wmono bsegs m m' -> PCOK2 fmt args slots A VA lo m') ->
    evt bsegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 e_vsnprintf_stub) fc None m (seg_rom bsegs)).

Lemma fmt_bytes_at : forall m A f, mem_inv bsegs m -> ro_bytes_b bsegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at bsegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at bsegs m A _ (ro_cells_image bsegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.
