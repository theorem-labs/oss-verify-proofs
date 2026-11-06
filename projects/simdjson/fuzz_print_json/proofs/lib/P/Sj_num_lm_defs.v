(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition LM_ENTRY : Z := 0x53e5c.
Definition NUM_MEMCPY : Z := 0xc4f08.
Definition NUM_MEMSET : Z := 0xc5488.
Definition memcpy_stmt : Prop := memcpyZ_stmt_g psegs NUM_MEMCPY.
Definition memset_stmt : Prop := memsetZ_stmt_g psegs NUM_MEMSET.

Record lmenv : Type := mkLmEnv {
  l_ra : word; l_sp : word; l_gp : word; l_tp : word;
  l_s0 : word; l_s1 : word; l_s2 : word; l_s3 : word; l_s4 : word; l_s5 : word;
  l_s6 : word; l_s7 : word; l_s8 : word; l_s9 : word; l_s10 : word; l_s11 : word;
  l_F : bvmap 5 word; l_fc : bv 32;
  l_X : Z; l_Y : Z; l_ny : Z; l_lo : Z; l_ybs : list byte; l_m0 : mem }.

Notation l_SP E := (bv_unsigned (l_sp E)).

Record lm_ok (E : lmenv) : Prop := mkLmOk {
  lo_room : (l_lo E + LM_STACK <= l_SP E)%Z;
  lo_xhi : (l_SP E <= l_X E)%Z;
  lo_ylen : Z.of_nat (length (l_ybs E)) = (8 * l_ny E)%Z;
  lo_ylo : (l_Y E + 8 * l_ny E <= l_lo E)%Z }.

Definition lm_W (E : lmenv) : list (Z * Z) := [(l_SP E - LM_STACK, l_SP E); (l_X E, l_X E + 498)]%Z.
Notation lm_post E := (lm_post_g psegs (l_ra E) (l_sp E) (l_gp E) (l_tp E) (l_s0 E) (l_s1 E) (l_s2 E) (l_s3 E) (l_s4 E) (l_s5 E)
                          (l_s6 E) (l_s7 E) (l_s8 E) (l_s9 E) (l_s10 E) (l_s11 E) (l_F E) (l_fc E) (l_X E) (l_lo E) (l_m0 E)).

Definition lm_saved (E : lmenv) : list cell :=
  [C8 (l_s11 E); C8 (l_s10 E); C8 (l_s9 E); C8 (l_s8 E); C8 (l_s7 E); C8 (l_s6 E); C8 (l_s5 E); C8 (l_s4 E);
   C8 (l_s3 E); C8 (l_s2 E); C8 (l_s1 E); C8 (l_s0 E); C8 (l_ra E)].

Definition LMINV (E : lmenv) (mm : mem) (xlen : Z) (w16 : word) : Prop :=
  (exists j0, rw_cells psegs mm (l_SP E + -1136) [CB 16 j0; C8 w16]) /\
  (exists zis, u64arr psegs mm (l_SP E + -1112) zis /\ length zis = 62%nat) /\
  (exists jzi, rw_cells psegs mm (l_SP E + -616) [CB 8 jzi]) /\
  (exists zs, u64arr psegs mm (l_SP E + -608) zs /\ length zs = 62%nat) /\
  (exists jz, rw_cells psegs mm (l_SP E + -112) [CB 8 jz]) /\
  rw_cells psegs mm (l_SP E + -104) (lm_saved E) /\
  (exists ws, u64arr psegs mm (l_X E) ws /\ length ws = 62%nat) /\
  rw_cells psegs mm (l_X E + 496) [C2 (Z_to_bv 64 xlen)] /\ (0 <= xlen <= 62)%Z /\
  bytes_at psegs mm (l_Y E) (l_ybs E) /\
  mem_inv psegs mm /\ munch (lm_W E) (l_m0 E) mm /\ wmono psegs (l_m0 E) mm /\ stk psegs mm (l_lo E) (l_SP E + -1136).

Ltac lm_open H :=
  let j0 := fresh "j0" in let zis := fresh "zis" in let jzi := fresh "jzi" in
  let zs := fresh "zs" in let jz := fresh "jz" in let ws := fresh "ws" in
  destruct H as ((j0 & FRlo) & (zis & ZIA & ZIL) & (jzi & ZIN) & (zs & ZA & ZL) & (jz & ZN) & SAVED & (ws & XA & XL) & XN & ?LEN
                 & YB & MI & MU & WM & ST);
  unfold lm_saved in SAVED; unfold lm_W, LM_STACK in MU.

Ltac lm_forget8 :=
  lazymatch goal with
  | |- exists j, rw_cells ?s ?m ?A [CB 8 j] =>
      lazymatch goal with
      | H : rw_cells s m A ?cs |- _ =>
          let j := fresh "j" in let Hj := fresh "Hj" in
          destruct (rw_cells_forget s m A cs H) as [j Hj]; exists j; exact Hj
      end
  end.
Ltac lm_close :=
  lazymatch goal with
  | |- LMINV _ _ _ _ =>
      split; [eexists; eassumption|]; split; [eexists; split; [eassumption| rewrite ?upd_length; assumption]|];
      split; [lm_forget8|]; split; [eexists; split; [eassumption| rewrite ?upd_length; assumption]|];
      split; [lm_forget8|]; split; [eassumption|];
      split; [eexists; split; [eassumption| rewrite ?upd_length; assumption]|];
      split; [eassumption|]; split; [lia|]; split; [eassumption|];
      split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.
Ltac lm_forget := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H | H : u64arr _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : length _ = 62%nat |- _ => clear H
  | H : (0 <= _ /\ _ + 8 * Z.of_nat 62 <= 2 ^ 64)%Z |- _ => clear H end.

Notation LM E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
  (MS (mkR xra (Z_to_bv 64 (l_SP E + -1136)) (l_gp E) (l_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) (l_F E) (Z_to_bv 64 pc) (l_fc E) None mm (seg_rom psegs)).

Section LMDEFS.
  Variable E : lmenv.
  Hypothesis OK : lm_ok E.
  Notation SP := (l_SP E).
  Notation X := (l_X E).

  Lemma lm_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm xlen w16,
    LMINV E mm xlen w16 ->
    evt psegs (lm_post E) (LM E 0x541a8 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until w16. intros INV. lm_open INV. destruct OK as [ROOM XHI YLEN YLO]. unfold LM_STACK in *.
    pose proof (bv_unsigned_in_range 64 (l_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    do 13 zstep. zstep. zstep.
    apply rw_cells_of_u64arr in ZIA, ZA. rewrite ZIL in ZIA. rewrite ZL in ZA.
    release_frame FRlo ST (SP + -1112)%Z.
    release_frame ZIA ST (SP + -616)%Z.
    release_frame ZIN ST (SP + -608)%Z.
    release_frame ZA ST (SP + -112)%Z.
    release_frame ZN ST (SP + -104)%Z.
    release_frame SAVED ST (l_SP E).
    apply evt_done. unfold lm_post_g. do 15 eexists. exists mm, ws, xlen.
    split; [cbv delta [mkR]; reflexivity|].
    unfold LM_STACK, bigint_at.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [split; [exact XA| split; [exact XL| split; [exact XN| exact LEN]]] | exact ST].
  Qed.

  Lemma lm_false : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm xlen w16,
    LMINV E mm xlen w16 ->
    evt psegs (lm_post E) (LM E 0x541a4 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK. intros. zstep. eapply lm_exit. eassumption. Qed.

  Lemma lm_norm_loop : forall (f : nat) (k : Z) xra xt0 xt1 xt2 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm w16,
    LMINV E mm k w16 -> (1 <= k)%Z -> (k <= Z.of_nat f)%Z ->
    evt psegs (lm_post E) (LM E 0x53f48 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 (Z_to_bv 64 k) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until w16; intros INV Hk Hf; [exfalso; lia|].
    pose proof INV as INV0.
    lm_open INV. destruct OK as [ROOM XHI YLEN YLO]. unfold LM_STACK in *.
    pose proof (bv_unsigned_in_range 64 (l_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (u64arr_bound _ _ _ _ XA) as XB. rewrite XL in XB.
    zstep. zstep. nnorm. zstep.
    u64_read XA (k - 1)%Z w.
    zstep. zstep.
    if_cases K; zify_cond K.
    { eapply lm_exit. exact INV0. }
    zstep. zstep. zstep. zstep.
    num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV E m1 (k - 1) w16) by lm_close).
    if_cases K2; zify_cond K2.
    - eapply evt_eq; [| eapply (IH (k - 1)%Z); [exact INV1 | | lia]]; [num_st_eq|].
      destruct (Z.eq_dec k 1) as [->|]; [|lia]. exfalso. apply K2. reflexivity.
    - zstep. eapply lm_exit. exact INV1.
  Qed.

  Lemma lm_norm : forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm xlen w16,
    LMINV E mm xlen w16 ->
    evt psegs (lm_post E) (LM E 0x53f3c xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until w16; intros INV.
    pose proof INV as INV0.
    lm_open INV. destruct OK as [ROOM XHI YLEN YLO]. unfold LM_STACK in *.
    pose proof (bv_unsigned_in_range 64 (l_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    zstep. nnorm. zstep. zstep.
    if_cases K; zify_cond K.
    { eapply lm_exit. exact INV0. }
    eapply (lm_norm_loop (Z.to_nat xlen)); [exact INV0 | lia | lia].
  Qed.
End LMDEFS.
