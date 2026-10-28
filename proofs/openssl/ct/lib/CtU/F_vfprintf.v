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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_mlib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Printf_lib F_memset F_memcpy F_fwritex F_pop_arg F_printf_iface F_printf_core.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import F_printf_snsink F_sn_write F_towrite.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import PrintfModel PrintfModelX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Definition zpk__ (P : Prop) : Prop := P.
Local Ltac zpk1__ H := let T := type of H in change (zpk__ T) in H.
Local Ltac zpk_nf__ H A q := lazymatch A with context [q] => fail | _ => zpk1__ H end.
(* [comment removed for export] *)
Local Ltac zidleF__ q n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(q, q + n)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zpk_nf__ H A q
    | H : ro_cells segs m ?A _ |- _ => zpk_nf__ H A q
    | H : u8arr segs m ?A _ |- _ => zpk_nf__ H A q
    | H : bytes_at segs m ?A _ |- _ => zpk_nf__ H A q
    end
  end.
Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
(* [comment removed for export] *)
Module DJR.
  Import Ltac2.
  Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
  Ltac2 unhide_rel () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let rm := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None =>
          match is_hidden ty with
          | Some p => if SF2.meets (SF2.vars_of [] p) gv
                      then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
                      else Some id
          | None => None
          end
      end) (Control.hyps ()) in
    match rm with [] => () | _ :: _ => Std.clear rm end.
  Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
Local Ltac lia ::= lia3.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arg_ok_vf : forall Fp B BS m m' lo sp sp' ap w a,
  arg_ok Fp B BS m lo sp ap w a -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> arg_ok Fp B BS m' lo sp' ap w a.
Proof.
  intros Fp B BS m m' lo sp sp' ap w a H Hsp MU. destruct a as [s| |i|u|u|d]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4). exists slack.
  split; [|repeat (split; [first [assumption | lia]|]); exact D4].
  eapply bytes_at_transport; [exact BY | exact MU |].
  cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
Lemma args_ok_vf : forall Fp B BS m m' lo sp sp' ap ws args,
  args_ok Fp B BS m lo sp ap ws args -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> args_ok Fp B BS m' lo sp' ap ws args.
Proof.
  intros Fp B BS m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp MU; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.
(* [comment removed for export] *)
Lemma arg_okx_vf : forall Fp B BS m m' lo sp sp' ap w a cov,
  arg_okx Fp B BS m lo sp ap w a cov -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> arg_okx Fp B BS m' lo sp' ap w a cov.
Proof.
  intros Fp B BS m m' lo sp sp' ap w a cov H Hsp MU. destruct a as [s| |i|u|u|d]; cbn [arg_okx] in H |- *; try (eapply arg_ok_vf; eassumption).
  destruct H as [H | (Hp & BY & HF & NZ & HI & D1 & D2 & D3 & D4)]; [left; eapply arg_ok_vf; eassumption | right].
  split; [exact Hp|]. split; [|repeat (split; [first [assumption | lia]|]); exact D4].
  eapply bytes_at_transport; [exact BY | exact MU |].
  cbn [disjoint_from]. rewrite zb_length. unfold zlength in *. lia.
Qed.
Lemma args_okx_vf : forall Fp B BS m m' lo sp sp' ap ws args covs,
  args_okx Fp B BS m lo sp ap ws args covs -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> args_okx Fp B BS m' lo sp' ap ws args covs.
Proof.
  intros Fp B BS m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws covs H Hsp MU; [destruct ws; exact I|].
  cbn [args_okx] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_okx_vf; eassumption | apply IH; assumption].
Qed.

Lemma rw_cells_unmerge : forall m A pre mid post,
  rw_cells ctusegs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post) -> cells_wf mid ->
  rw_cells ctusegs m A (pre ++ mid ++ post).
Proof.
  intros m A pre mid post [[Hwf Hb] Hw] WF.
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]].
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [exact WF | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite ?app_assoc in Hb |- *. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite ?Nat.add_assoc in Hw |- *. exact Hw.
Qed.

Lemma rwc_eq : forall m A A' cs, rw_cells ctusegs m A cs -> A = A' -> rw_cells ctusegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

Lemma rw_cells_CB0 : forall m B, 0 <= B -> B <= 2^64 -> rw_cells ctusegs m B [CB 0 []].
Proof.
  intros m B H0 H1. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition snfile_head (wend wpos wbase buf bufsize : Z) (mode : word) : list cell :=
  gfile_cells (Z_to_bv 64 0) 0 0 0 wend wpos wbase 0x2bc2d8 0 buf bufsize 0 mode (Z_to_bv 64 0xffffffff) 0xffffffff.
Definition snfile_rest (CK : Z) : list cell :=
  [C4 z64; C8 (Z_to_bv 64 CK); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64].

Definition VF_FRAME : Z := 368.

Definition vfprintf_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (Fp CK D n : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (fjunk : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells ctusegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)]
    /\ rw_cells ctusegs m' CK [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n - zlength o))]
    /\ rw_cells ctusegs m' Fp [CB 232 fjunk].

Definition vfprintf_sn_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (Fp CK D n bufp A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells ctusegs m Fp (snfile_head 0 0 0 bufp 0 (Z_to_bv 64 0)) -> rw_cells ctusegs m (Fp + 148) (snfile_rest CK) ->
    rw_cells ctusegs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
    rw_cells ctusegs m D [CB dn junkd] ->
    bytes_at ctusegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1x_ok fmt = true ->
    va_area m VA slots -> args_okx Fp (q - 352) 80 m lo q (q - VF_FRAME) slots args (arg_covs (length fmt) fmt args) ->
    printf_modelx OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    fp_callsx (length fmt) fmt args = [] ->      (* [comment removed for export] *)
    (length o < dn)%nat -> (zlength o <= n < 2^63) -> (0 < bufp < 2^64) ->
    stk ctusegs m lo q -> (lo <= q - VF_FRAME - PC_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv ctusegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (q <= Fp) -> (Fp + 232 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (q <= CK) -> (CK + 16 <= Fp \/ Fp + 232 <= CK) -> (CK + 16 < 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= Fp \/ Fp + 232 <= D) -> (D + Z.of_nat dn <= CK \/ CK + 16 <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt ctusegs (vfprintf_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D n dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b7854) fc None m (seg_rom ctusegs)).

Theorem vfprintf_sn_proof : vfprintf_sn_stmt.
Proof.
  unfold vfprintf_sn_stmt. intros until o. cbv zeta.
  intros -> -> -> FH FR CKC DST BY HF P1 VAA AOK MODEL FPF ROOM Hn Hbufp ST LO GLO QHI SSP MI FRM HA0 HA QF FVA VAHI QCK CKF CKHI DD1 DD2 DD3 GD.
  unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
  pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  pose proof (wmono_refl ctusegs m) as WM.
  unfold snfile_head, gfile_cells in FH. unfold snfile_rest in FR.
  carve_frame 368%nat ST.
  (* [comment removed for export] *)
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
  stash FH. stash FR. stash CKC. stash DST. stash BY. stash VAA.
  do 12 zs. do 14 zs.
  unstash.
  lazymatch type of MUp with munch ?Wp ?ma ?mb =>
    transport_after_call ctusegs ma mb MUp WM;
    assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z ma mb)
      by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; intros; slia | exact MUp]);
    assert (MU1 : munch [(lo, bv_unsigned sp); (Fp, Fp + 232)]%Z ma mb)
      by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; intros; slia | exact MUp])
  end.
  clear MUp.
  (* [comment removed for export] *)
  pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
  eapply evt_cut.
  { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
      [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
      | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
  cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
  rewrite !unsigned_lit in MUc, STc by lia.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call ctusegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
  fix_ret.
  clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  (* [comment removed for export] *)
  zs. if_lit. zs. zs. if_lit. zs. zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) in *. zs. zs. zs. zs. if_lit.
  do 10 zs.
  pose proof (rw_cells_bound _ _ _ _ FH) as FB. cbn [cells_size csize Nat.add] in FB.
  (* [comment removed for export] *)
  pose proof towrite_g_proof as TW. unfold towrite_g_stmt in TW.
  eapply evt_cut.
  { eapply (TW _ _ _ _ _ _ _ _ _ (Z_to_bv 64 Fp)) with (flags := Z_to_bv 64 0) (rpos := 0) (rend := 0) (close := 0) (wend := 0) (wpos := 0) (wbase := 0)
      (writefn := 2867928) (seekfn := 0) (buf := bv_unsigned sp + -352) (bufsize := 80) (fd := 0) (mode := Z_to_bv 64 0) (lock := Z_to_bv 64 4294967295) (lbf := 4294967295);
      rewrite ?unsigned_lit by lia; [ unfold gfile_cells; exact FH | reflexivity | lia | lia | lia | assumption ]. }
  cbv beta. intros ms' P. clear TW.
  destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FH').
  rewrite !unsigned_lit in MUc, FH' by lia. clear FH.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call ctusegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
  fix_ret.
  zs. if_lit. do 6 zs.
  (* [comment removed for export] *)
  set (B := bv_unsigned sp + -352) in *.
  unfold gfile_cells in FH'.
  apply (rw_cells_merge ctusegs _ _ [] [C4 (Z_to_bv 64 0); C4 z64; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in FH'.
  apply (rw_cells_split_CB ctusegs _ _ [] _ _ _ [1; 31]%nat) in FH'; [|reflexivity].
  apply (rw_cells_merge ctusegs _ _ [_; _; _; _]
           [C8 z64; C8 (Z_to_bv 64 B); C8 z64; C8 (Z_to_bv 64 2867928); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 80);
            C8 z64; C8 z64; C4 (Z_to_bv 64 0); C4 z64; C8 z64; C4 mode'; C4 (Z_to_bv 64 4294967295)]) in FH'.
  cbn [app mk_CB_cells cells_size csize Nat.add] in FH'.
  match type of FH' with rw_cells _ _ _ (CB 1 ?b1 :: CB 31 ?b31 :: _ :: _ :: CB 96 ?b96 :: _) =>
    let v1 := eval vm_compute in b1 in change b1 with v1 in FH'; set (j1 := b31) in FH'; set (j2 := b96) in FH' end.
  (* [comment removed for export] *)
  match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
  apply (rw_cells_split_CB ctusegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
  apply (proj1 (rw_cells_app ctusegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
  apply (proj1 (rw_cells_app ctusegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
  apply (proj1 (rw_cells_app ctusegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
  replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with B in BUFc by lia.
  replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FRv by lia.
  replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in AP2 by lia.
  match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
  match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
  pose proof (rw_CB_length _ _ _ _ BUFc) as LJB.
  replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).
  (* [comment removed for export] *)
  assert (SNK : SINK_sn Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368) m'' []).
  { exists jb. split; [|split; [exact FR | split; [reflexivity | split; [unfold zlength, SN_CAP; rewrite LJB; reflexivity | unfold SN_CAP; split; [lia | split; lia]]]]].
    unfold wfile. cbn [zb map length Z.of_nat]. rewrite LJB. rewrite !Z.add_0_r.
    split; [unfold FILE_cells; exact FH'|].
    split. { apply (proj2 (rw_cells_app ctusegs _ _ [CB 0 []] [CB 80 jb])). split; [apply rw_cells_CB0; lia|]. cbn [cells_size csize Nat.add]. rewrite Z.add_0_r. exact BUFc. }
    split; [reflexivity|]. split; [vm_compute; discriminate|]. lia. }
  (* [comment removed for export] *)
  assert (PCALL : forall Q ms, implM ctusegs (printf_modelx OUT_sn OUTFP_sn fmt args) [] Q ms -> evt ctusegs (Q r o) ms).
  { intros Q ms H. unfold implM in H. rewrite MODEL in H. exact H. }
  pose proof (printf_core_proof (list Z) Fp B 80 _ _ OUT_sn OUTFP_sn
                (sn_sink_frame Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))
                (sn_sink_flags Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))
                (sn_topok (bv_unsigned sp + -368))
                (sn_out Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))) as PC2.
  unfold printf_core_stmt in PC2.
  eapply evt_cut.
  { apply PCALL. eapply PC2 with (i := 0%Z) (slots := slots); rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_sn, zlength;
      [ exact SNK | exact BY | exact HF | reflexivity | exact APC | exact VAA | lia | | | match goal with H : stk _ _ lo _ |- _ => exact H end | lia | lia | lia | lia
      | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | exact FRM | lia | lia | lia | lia | lia | lia | lia ].
    - (* [comment removed for export] *) cbn [skipn Z.to_nat]. eapply args_okx_vf; [exact AOK | lia |].
      exact MU1.
    - (* [comment removed for export] *)
      rewrite FPF. apply Forall_nil. }
  cbv beta. intros ms' P. clear PC2 PCALL MODEL FPF AOK HF BY VAA P1.
  unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
  destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
  unfold INT_MAX in Hr.
  unfold SR in MUc. cbn [app] in MUc.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call ctusegs mm m3 MUc WMc; clear MUc WMc; try clear MIt end.
  fix_ret.
  (* [comment removed for export] *)
  destruct SNK3 as (junk3 & WF3 & FR3 & FRL3 & LEN3 & SEPB3 & T13 & T23).
  destruct WF3 as (FC3 & BUF3 & FL3 & LBF3 & B03 & BHI3 & SEPfb3).
  pose proof (zb_length o) as LZo. rewrite LZo in *. unfold zlength, SN_CAP in LEN3.
  unfold FILE_cells in FC3. subst j2.
  (* [comment removed for export] *)
  lazymatch type of FC3 with rw_cells _ ?mm _ [?c1; ?c2; ?c3; ?c4; CB 96 _; ?c6] =>
    pose proof (rw_cells_unmerge mm Fp [c1; c2; c3; c4]
           [C8 z64; C8 (Z_to_bv 64 B); C8 z64; C8 (Z_to_bv 64 2867928); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 80);
            C8 z64; C8 z64; C4 (Z_to_bv 64 0); C4 z64; C8 z64; C4 mode'; C4 (Z_to_bv 64 4294967295)] [c6]) as UM end.
  cbn [cells_size csize cells_bytes cbytes Nat.add app] in UM.
  specialize (UM FC3 ltac:(cbn [cells_wf cell_wf]; repeat split)). clear FC3. rename UM into FC3.
  subst j1.
  apply (rw_cells_merge ctusegs _ _ [] [CB 1 _; CB 31 _]) in FC3. cbn [app cells_size csize Nat.add cells_bytes cbytes] in FC3.
  match type of FC3 with rw_cells _ _ _ (CB 32 ?b :: _) => let v := eval vm_compute in b in change b with v in FC3 end.
  lazymatch type of FC3 with rw_cells _ ?mm _ (CB 32 _ :: ?rest) =>
    pose proof (rw_cells_unmerge mm Fp [] [C4 (Z_to_bv 64 0); C4 z64; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] rest) as UM end.
  cbn [cells_size csize cells_bytes cbytes Nat.add app] in UM.
  lazymatch type of UM with rw_cells _ _ _ (CB 32 ?b :: _) -> _ => let v := eval vm_compute in b in change b with v in UM end.
  specialize (UM FC3 ltac:(cbn [cells_wf cell_wf]; repeat split)). clear FC3. rename UM into FC3.
  zs. zs. zs. brf Kb; [exfalso; lia|].
  zs. zs. zs. zs. zs.
  (* [comment removed for export] *)
  apply (proj1 (rw_cells_app ctusegs _ _ [_; _; _; _; _; _] _)) in FC3. destruct FC3 as [F0 FC3]. cbn [cells_size csize Nat.add app] in FC3.
  apply (proj1 (rw_cells_app ctusegs _ _ [_] _)) in FC3. destruct FC3 as [F40 FC3]. cbn [cells_size csize Nat.add app] in FC3.
  apply (proj1 (rw_cells_app ctusegs _ _ [_] _)) in FC3. destruct FC3 as [F48 FC3]. cbn [cells_size csize Nat.add app] in FC3.
  apply (proj1 (rw_cells_app ctusegs _ _ [_] _)) in FC3. destruct FC3 as [F56 FC3]. cbn [cells_size csize Nat.add app] in FC3.
  apply (proj1 (rw_cells_app ctusegs _ _ [_; _; _] _)) in FC3. destruct FC3 as [F64 FC3]. cbn [cells_size csize Nat.add app] in FC3.
  apply (proj1 (rw_cells_app ctusegs _ _ [_] _)) in FC3. destruct FC3 as [F88 F96]. cbn [cells_size csize Nat.add app] in F96.
  replace (Fp + Z.of_nat 40)%Z with (Fp + 40)%Z in F40 by lia.
  replace (Fp + Z.of_nat 40 + Z.of_nat 8)%Z with (Fp + 48)%Z in F48 by lia.
  replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8)%Z with (Fp + 56)%Z in F56 by lia.
  replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8)%Z with (Fp + 64)%Z in F64 by lia.
  replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 24)%Z with (Fp + 88)%Z in F88 by lia.
  replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 24 + Z.of_nat 8)%Z with (Fp + 96)%Z in F96 by lia.
  unfold snfile_rest in FR3.
  apply (proj1 (rw_cells_app ctusegs _ _ [_] _)) in FR3. destruct FR3 as [F148 FR3]. cbn [cells_size csize Nat.add app] in FR3.
  apply (proj1 (rw_cells_app ctusegs _ _ [_] _)) in FR3. destruct FR3 as [F152 F160]. cbn [cells_size csize Nat.add app] in F160.
  replace (Fp + 148 + Z.of_nat 4)%Z with (Fp + 152)%Z in F152 by lia.
  replace (Fp + 148 + Z.of_nat 4 + Z.of_nat 8)%Z with (Fp + 160)%Z in F160 by lia.
  pose proof (rw_cells_bytes_at' _ _ _ _ BUF3) as SRC3. cbn [cells_bytes cbytes app] in SRC3. rewrite app_nil_r in SRC3.
  apply bytes_at_app in SRC3. destruct SRC3 as [SRC3 _].
  replace (Z_to_bv 64 (B + Z.of_nat (length o))) with (Z_to_bv 64 (B + zlength o)) in F40 by reflexivity.
  clear MU1. clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 64) _ H ltac:(lia)) as [ST4a ST4b]; clear H end.
  eapply evt_cut.
  { eapply sn_write_spec with (o := o) (B := B) (n := n) (D := D) (CK := CK) (dn := dn) (bufp := B) (Fp := Fp) (junk := junkd);
      rewrite ?unsigned_lit by lia; unfold zlength;
      [ reflexivity | reflexivity | exact F40 | exact F56 | exact F88 | exact F152 | | exact SRC3 | | exact ROOM | lia | lia | lia | exact ST4b | lia | assumption
      | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia ].
    all: lazymatch goal with |- rw_cells _ _ ?a _ => match goal with H : rw_cells _ _ a _ |- _ => exact H end end. }
  cbv beta. intros ms' P.
  unfold sn_write_post in P. rewrite !unsigned_lit in P by lia.
  destruct P as (z5 & z6 & z7 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & ST4b' & CK4 & DST4 & F40' & F56' & SRC4).
  rewrite ?unsigned_lit in ST4b' by lia.
  clear F56 F40 DST CKC.  (* [comment removed for export] *)
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call ctusegs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
  fix_ret.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zidleF__ Fp 232%Z MUk__ WMk__.
  zs. zs. zs. zs. zs.
  unfold zpk__ in *.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUk__ with munch _ ?m0 _ => transport_after_call segs m0 mm MUk__ WMk__; clear MUk__ WMk__ end end.
  zs. replace (0 <? B)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  zs. zs. rewrite ?Z.lor_0_l. zs.
  zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zs. zs. zs. zs. zs. rewrite ?Z.lor_0_l. zs. zs. if_lit.
  zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
  do 9 zs.
  try rewrite (land_M64_id r) by lia.
  (* [comment removed for export] *)
  match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z [C8 apv] |- _ => rename H into APC4 end.
  match goal with H : rw_cells _ ?mm B _ |- _ => rename H into BUF4 end.
  match goal with H : stk _ ?mm lo (bv_unsigned sp + -368 - 64)%Z, H' : stk _ ?mm (bv_unsigned sp + -368 - 64)%Z _ |- _ =>
    pose proof (stk_merge _ _ _ _ _ H H' ltac:(lia)) as ST5; clear H H' end.
  release_frame APC4 ST5 (bv_unsigned sp + -360)%Z.
  release_frame AP2 ST5 B.
  release_frame BUF4 ST5 (bv_unsigned sp + -272)%Z.
  release_frame FRv ST5 (bv_unsigned sp).
  lazymatch goal with F0 : rw_cells _ ?mm Fp _, F40 : rw_cells _ ?mm (Fp + 40)%Z _, F48 : rw_cells _ ?mm (Fp + 48)%Z _, F56 : rw_cells _ ?mm (Fp + 56)%Z _,
                   F64 : rw_cells _ ?mm (Fp + 64)%Z _, F88 : rw_cells _ ?mm (Fp + 88)%Z _, F96 : rw_cells _ ?mm (Fp + 96)%Z _,
                   F148 : rw_cells _ ?mm (Fp + 148)%Z _, F152 : rw_cells _ ?mm (Fp + 152)%Z _, F160 : rw_cells _ ?mm (Fp + 160)%Z _ |- _ =>
    assert (FALL : rw_cells ctusegs mm Fp ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
              ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2867928); C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 bufp)]
              ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode'; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)]
              ++ [C4 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 CK)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]));
    [ apply (proj2 (rw_cells_app ctusegs _ _ _ _)); split; [piece F0|];
      apply (proj2 (rw_cells_app ctusegs _ _ _ _)); split; [piece F40|];
      apply (proj2 (rw_cells_app ctusegs _ _ _ _)); split; [piece F48|];
      apply (proj2 (rw_cells_app ctusegs _ _ _ _)); split; [piece F56|];
      apply (proj2 (rw_cells_app ctusegs _ _ _ _)); split; [piece F64|];
      apply (proj2 (rw_cells_app ctusegs _ _ _ _)); split; [piece F88|];
      apply (proj2 (rw_cells_app ctusegs _ _ _ _)); split; [piece F96|];
      apply (proj2 (rw_cells_app ctusegs _ _ _ _)); split; [piece F148|];
      apply (proj2 (rw_cells_app ctusegs _ _ _ _)); split; [piece F152|];
      piece F160
    | ] end.
  destruct (rw_cells_forget _ _ _ _ FALL) as [fjunk FJ]. cbn [cells_size csize Nat.add app] in FJ.
  apply evt_done. unfold vfprintf_sn_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact FOK|].
  split; [exact ST5|].
  split; [split; [exact SSP1 | exact SSP2]|].
  split; [exact DST4|]. split; [exact CK4|]. exact FJ.
Qed.
