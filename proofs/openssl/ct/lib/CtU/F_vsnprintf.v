(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_mlib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Printf_lib F_memset F_memcpy F_fwritex F_pop_arg F_printf_iface F_printf_core.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import F_printf_snsink F_sn_write F_towrite F_vfprintf Printf_sn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
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
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call ctusegs m mm MU WM end end.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Local Ltac tslia ::= first [ exact I | clear_big; first [ tlia | split; [ tlia | exact I ] ] ].
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= clear_big; lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs cs', rw_cells ctusegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells ctusegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma rw_cells_C4_eqv : forall m A pre v v' post, rw_cells ctusegs m A (pre ++ C4 v :: post) -> le4 v = le4 v' -> rw_cells ctusegs m A (pre ++ C4 v' :: post).
Proof.
  intros m A pre v v' post H E. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 [_ W2]]. apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac c4_eqv H k v' :=
  lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
    lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some (C4 ?v) =>
      let H' := fresh in
      pose proof (rw_cells_C4_eqv m A pre v v' post) as H'; cbn [app] in H';
      specialize (H' H ltac:(unfold le4; cbn [Z_to_le_bytes]; repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity)); clear H; rename H' into H
    end end.

(* [comment removed for export] *)
Lemma arg_ok_relayout : forall Fp' B' BS' m lo sp ap' sp' w a,
  arg_ok 0 0 0 m lo sp 0 w a -> lo <= Fp' -> Fp' + 232 <= sp -> lo <= B' -> B' + BS' <= sp -> lo <= ap' -> ap' + 8 <= sp -> sp' <= sp ->
  arg_ok Fp' B' BS' m lo sp' ap' w a.
Proof.
  intros Fp' B' BS' m lo sp ap' sp' w a H H1 H2 H3 H4 H5 H6 H7. destruct a as [s| |i|u|u|d]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4). exists slack.
  repeat (split; [first [assumption | lia]|]). lia.
Qed.
Lemma args_ok_relayout : forall Fp' B' BS' m lo sp ap' sp' ws args,
  args_ok 0 0 0 m lo sp 0 ws args -> lo <= Fp' -> Fp' + 232 <= sp -> lo <= B' -> B' + BS' <= sp -> lo <= ap' -> ap' + 8 <= sp -> sp' <= sp ->
  args_ok Fp' B' BS' m lo sp' ap' ws args.
Proof.
  intros Fp' B' BS' m lo sp ap' sp' ws args. revert ws. induction args as [|a args IH]; intros ws H H1 H2 H3 H4 H5 H6 H7; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [Ha Hr].
  split; [eapply arg_ok_relayout; eassumption | apply IH; assumption].
Qed.
(* [comment removed for export] *)
Lemma arg_okx_relayout : forall Fp' B' BS' m lo sp ap' sp' w a cov,
  arg_okx 0 0 0 m lo sp 0 w a cov -> lo <= Fp' -> Fp' + 232 <= sp -> lo <= B' -> B' + BS' <= sp -> lo <= ap' -> ap' + 8 <= sp -> sp' <= sp ->
  arg_okx Fp' B' BS' m lo sp' ap' w a cov.
Proof.
  intros Fp' B' BS' m lo sp ap' sp' w a cov H H1 H2 H3 H4 H5 H6 H7. destruct a as [s| |i|u|u|d]; cbn [arg_okx] in H |- *; try (eapply arg_ok_relayout; eassumption).
  destruct H as [H | (Hp & BY & HF & NZ & HI & D1 & D2 & D3 & D4)]; [left; eapply arg_ok_relayout; eassumption | right].
  repeat (split; [first [assumption | lia]|]). lia.
Qed.
Lemma args_okx_relayout : forall Fp' B' BS' m lo sp ap' sp' ws args covs,
  args_okx 0 0 0 m lo sp 0 ws args covs -> lo <= Fp' -> Fp' + 232 <= sp -> lo <= B' -> B' + BS' <= sp -> lo <= ap' -> ap' + 8 <= sp -> sp' <= sp ->
  args_okx Fp' B' BS' m lo sp' ap' ws args covs.
Proof.
  intros Fp' B' BS' m lo sp ap' sp' ws args. revert ws. induction args as [|a args IH]; intros ws covs H H1 H2 H3 H4 H5 H6 H7; [destruct ws; exact I|].
  cbn [args_okx] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [Ha Hr].
  split; [eapply arg_okx_relayout; eassumption | apply IH; assumption].
Qed.

Definition VSN_FRAME : Z := 304.
Definition VSN_DEPTH : Z := 5856.   (* [comment removed for export] *)
Definition VSN_W (lo q D : Z) (dn : nat) : list (Z * Z) := [(lo, q); (D, D + Z.of_nat dn)].

Definition vsnprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (D : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells ctusegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vsnprintf_stmtx : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells ctusegs m D [CB dn junkd] ->
    bytes_at ctusegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1x_ok fmt = true ->
    va_area m VA slots -> (forall m', munch (VSN_W lo q D dn) m m' -> args_okx 0 0 0 m' lo q 0 slots args (arg_covs (length fmt) fmt args)) ->
    printf_modelx OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    fp_callsx (length fmt) fmt args = [] ->
    (length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
    stk ctusegs m lo q -> (lo <= q - VSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv ctusegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt ctusegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2bc20c) fc None m (seg_rom ctusegs)).


Definition vsnprintf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells ctusegs m D [CB dn junkd] ->
    bytes_at ctusegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1x_ok fmt = true ->
    va_area m VA slots -> (forall m', munch (VSN_W lo q D dn) m m' -> args_ok 0 0 0 m' lo q 0 slots args) ->
    printf_modelx OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    fp_callsx (length fmt) fmt args = [] ->
    (length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
    stk ctusegs m lo q -> (lo <= q - VSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv ctusegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt ctusegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2bc20c) fc None m (seg_rom ctusegs)).

Theorem vsnprintf_proofx : vsnprintf_stmtx.
Proof.
  unfold vsnprintf_stmtx. intros until o. cbv zeta.
  intros -> -> -> -> DST BY HF P1 VAA AOK MODEL FPF ROOM Hn Hn1 ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI DD1 DVA GD.
  unfold VSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT, VSN_W in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
  pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  carve_frame 304%nat ST.
  zidle_begin sp 304%Z MUz WMz.
  do 9 zs.
  zidle_end MUz WMz.
  do 3 zs.
  zs. zs. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  zs. zs. zs. zs. zs.
  (* [comment removed for export] *)
  replace (n <? n + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.add].
  change (Z.land (0 + -1) 18446744073709551615) with 18446744073709551615.
  replace (Z.land 18446744073709551615 (n + -1)) with (n + -1)
    by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  zs. zs. zs. zs. zs.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -304)%Z (CB 232 ?j :: _) |- _ => rename H into FRv; set (j0 := j) in FRv; clearbody j0 end.
  match type of FRv with rw_cells _ _ _ [_; _; _; CB 8 ?j; _; _; _; _; _; _] => set (j8 := j) in FRv; clearbody j8 end.
  apply (proj1 (rw_cells_app ctusegs _ _ [_] _)) in FRv. destruct FRv as [FZ FRv]. cbn [cells_size csize Nat.add app] in FRv.
  replace (bv_unsigned sp + -304 + Z.of_nat 232)%Z with (bv_unsigned sp + -72)%Z in FRv by lia.
  (* [comment removed for export] *)
  zs. eapply evt_cut.
  { eapply memset_spec; rewrite ?unsigned_lit by lia; [ | eassumption ]. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact FZ. }
  cbv beta. intros ms' P. unfold memset_post in P. rewrite !unsigned_lit in P by lia.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m2 & -> & MUc & WMc & MI2 & FZ').
  clear FZ.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call ctusegs mm m2 MUc WMc; clear MUc WMc; try clear MI end.
  fix_ret.
  (* [comment removed for export] *)
  pose proof (rw_cells_recast _ _ _ (gfile_cells (Z_to_bv 64 0) 0 0 0 0 0 0 0 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) 0 ++ snfile_rest 0) FZ'
                ltac:(cbn [cells_wf cell_wf gfile_cells snfile_rest app]; repeat split) ltac:(vm_compute; reflexivity)) as FC. clear FZ'.
  unfold gfile_cells, snfile_rest in FC. cbn [app] in FC.
  do 10 zs.
  c4_eqv FC 20%nat (Z_to_bv 64 4294967295). c4_eqv FC 21%nat (Z_to_bv 64 4294967295).
  (* [comment removed for export] *)
  pose proof (rw_CB_length _ _ _ _ DST) as LJ.
  pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
  pose proof (u8arr_store_ok ctusegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJ; lia) ltac:(f_equal; lia)) as SOK.
  zs. rewrite le1_zero. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia).
  pose proof (u8arr_write ctusegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJ; lia)) as DA2. clear DA. store_done.
  pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJ in DST. clear DA2.
  zs. zs. zs. zs.
  (* [comment removed for export] *)
  apply (proj1 (rw_cells_app ctusegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in FC. destruct FC as [FH FR]. cbn [cells_size csize Nat.add app] in FR.
  replace (bv_unsigned sp + -304 + Z.of_nat 148)%Z with (bv_unsigned sp + -304 + 148)%Z in FR by lia.
  apply (proj1 (rw_cells_app ctusegs _ _ [_;_] _)) in FRv. destruct FRv as [CKC FRv]. cbn [cells_size csize Nat.add app] in FRv.
  replace (bv_unsigned sp + -72 + Z.of_nat 16)%Z with (bv_unsigned sp + -56)%Z in FRv by lia.
  pose proof vfprintf_sn_proof as VF. unfold vfprintf_sn_stmt in VF.
  eapply evt_cut.
  { eapply VF with (Fp := bv_unsigned sp + -304) (CK := bv_unsigned sp + -72) (D := D) (n := n + -1) (bufp := bv_unsigned sp + -49) (A := A) (VA := VA)
                   (dn := dn) (junkd := upd junkd (Z.to_nat 0) (Z_to_bv 8 0)) (fmt := fmt) (slots := slots) (args := args) (lo := lo) (canary := canary) (r := r) (o := o);
      clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength.
    all: try reflexivity.
    all: try lia.
    - unfold snfile_head, gfile_cells. exact FH.
    - unfold snfile_rest. exact FR.
    - exact CKC.
    - exact DST.
    - exact BY.
    - exact HF.
    - exact P1.
    - exact VAA.
    - eapply args_okx_relayout; [apply AOK; exact MU | lia | lia | lia | lia | lia | lia | lia].
    - exact MODEL.
    - exact FPF.
    - exact ST.
    - split; [exact SSP1 | exact SSP2].
    - exact MI2.
    - exact FRM. }
  cbv beta. intros ms' P. clear VF.
  unfold vfprintf_sn_post in P. rewrite !unsigned_lit in P by lia.
  destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & fjunk & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SSP3 & DST3 & CK3 & FJ3).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call ctusegs mm m3 MUc WMc; clear MUc WMc; try clear MI2 end.
  fix_ret.
  clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  (* [comment removed for export] *)
  zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
  do 7 zs.
  lazymatch goal with FJ : rw_cells _ ?mm (bv_unsigned sp + -304)%Z _, CK : rw_cells _ ?mm (bv_unsigned sp + -72)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -56)%Z _ |- _ =>
    assert (FALL : rw_cells ctusegs mm (bv_unsigned sp + -304) ([CB 232 fjunk] ++ [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n + -1 - zlength o))] ++ [CB 8 j8; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
    [ apply (proj2 (rw_cells_app ctusegs _ _ _ _)); split; [exact FJ|];
      apply (proj2 (rw_cells_app ctusegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact CK | lia] |];
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

Theorem vsnprintf_proof : vsnprintf_stmt.
Proof.
  unfold vsnprintf_stmt. intros until o. cbv zeta. intros Ha0 Ha1 Ha2 Ha3 DST BY HF P1 VAA AOK.
  eapply vsnprintf_proofx; try eassumption.
  intros m' MU. apply args_ok_okx. exact (AOK m' MU).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fmt_bytes_at : forall m A f, mem_inv ctusegs m -> ro_bytes_b ctusegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at ctusegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at ctusegs m A _ (ro_cells_image ctusegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.
