(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_num_kitu Sj_num_kitn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Definition LMN_ENTRY : Z := 0x5e768.
Definition lmN_memcpy_stmt : Prop := memcpyZ_stmt_g usegs 0xd06e8.
Definition lmN_laf_stmt : Prop := lafuN_stmt_g usegs 0x5eaa8.

Section LMU.
  Hypothesis HCPY : lmN_memcpy_stmt.
  Hypothesis HLAF : lmN_laf_stmt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X Y ny lo len0 : Z) (ybs : list byte) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Hypothesis ROOM : (lo + LMU_STACK <= SP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis XLO : (SP <= X)%Z.
  Hypothesis XHI : (X + 498 <= 2^64)%Z.
  Hypothesis YL : Z.of_nat (length ybs) = (8 * ny)%Z.
  Hypothesis YHI : (Y + 8 * ny <= lo)%Z.
  Hypothesis Y0 : (0 < Y)%Z.
  Hypothesis Y8 : (Y mod 8 = 0)%Z.
  Hypothesis NY : (0 <= ny <= 62)%Z.

  Notation W := [(SP - LMU_STACK, SP); (X, X + 498)]%Z.
  Notation CAPL := (len0 + ny + 1 <= 62)%Z.
  Notation GM := (fun (a0 : word) (ws' : list word) (len' : Z) => CAPL -> a0 = Z_to_bv 64 1 /\ bignorm ws' len' /\ (len' <= len0 + ny + 1)%Z).
  Notation POST := (biguN_post_g LMU_STACK GM usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m0).
  Notation FB := (SP + -1120)%Z.
  Notation LM pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 FB) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
             xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition lmu_saved : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition LMINV (mm : mem) (len : Z) (P : Prop) : Prop :=
    (exists j, rw_cells usegs mm FB [CB 8 j]) /\
    (exists zb, u8arr usegs mm (SP + -1112) zb /\ length zb = 496%nat) /\
    (exists j, rw_cells usegs mm (SP + -616) [CB 2 j]) /\ (exists j, rw_cells usegs mm (SP + -614) [CB 6 j]) /\
    (exists xb, u8arr usegs mm (SP + -608) xb /\ length xb = 496%nat) /\
    (exists j, rw_cells usegs mm (SP + -112) [CB 2 j]) /\ (exists j, rw_cells usegs mm (SP + -110) [CB 6 j]) /\
    rw_cells usegs mm (SP + -104) lmu_saved /\
    (exists bs, u8arr usegs mm X bs /\ length bs = 496%nat /\ (P -> bignorm_b bs len)) /\
    rw_cells usegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    bytes_at usegs mm Y ybs /\
    mem_inv usegs mm /\ munch W m0 mm /\ wmono usegs m0 mm /\ stk usegs mm lo FB.

  Ltac lm_open H :=
    let j0 := fresh "j" in let zb := fresh "zb" in let jz := fresh "j" in let j1 := fresh "j" in let xb := fresh "xb" in let js := fresh "j" in
    let j2 := fresh "j" in let bs := fresh "bs" in
    destruct H as ((j0 & PAD0) & (zb & ZA & ?ZL) & (jz & ZN) & (j1 & ZP) & (xb & SA & ?SL) & (js & SN) & (j2 & SPD) & SAVED & (bs & XA & ?XL & NB) & XN & ?LEN & YA & MI & MU & WM & ST);
    unfold lmu_saved in SAVED; unfold LMU_STACK, LAFU_STACK in MU.
  Ltac lm_forget_cell :=
    lazymatch goal with
    | |- exists j, rw_cells ?s ?m ?A [CB ?n j] =>
        lazymatch goal with
        | H : rw_cells s m A ?cs |- _ =>
            let j := fresh "j" in let Hj := fresh "Hj" in
            destruct (rw_cells_forget s m A cs H) as [j Hj]; exists j; exact Hj
        end
    end.
  Ltac lm_close_with nb :=
    lazymatch goal with
    | |- LMINV _ _ _ =>
        split; [eexists; eassumption|]; split; [eexists; split; [eassumption| lia]|]; split; [lm_forget_cell|]; split; [eexists; eassumption|];
        split; [eexists; split; [eassumption| lia]|]; split; [lm_forget_cell|]; split; [eexists; eassumption|];
        split; [eassumption|]; split; [eexists; split; [eassumption| split; [lia | nb]]|]; split; [eassumption|]; split; [lia|];
        split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.
  Ltac lm_close := lm_close_with ltac:(let HF := fresh in intros HF; exact (False_ind _ HF)).
  Ltac lm_env :=
    pose proof ROOM as ROOM'; unfold LMU_STACK, LAFU_STACK in ROOM';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof XHI as XHI'; change (2 ^ 64)%Z with 18446744073709551616%Z in XHI';
    pose proof XLO as XLO'; pose proof YL as YL'; pose proof YHI as YHI'; pose proof Y0 as Y0'; pose proof Y8 as Y8'; pose proof NY as NY'; pose proof SP16 as SP16'.

  Lemma lm_exit : forall (r : Z) (P : Prop) xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len,
    LMINV mm len P -> (CAPL -> P /\ r = 1 /\ len <= len0 + ny + 1)%Z ->
    evt usegs POST (LM 0x5ea68 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM SP16 XLO XHI YL YHI Y0 Y8 NY.
    intros until len. intros INV HR. lm_open INV. lm_env.
    do 13 zstep. zstep. zstep.
    apply (rw_cells_of_u8arr usegs) in ZA. apply (rw_cells_of_u8arr usegs) in SA. rewrite ZL in ZA. rewrite SL in SA.
    release_frame PAD0 ST (SP + -1112)%Z.
    release_frame ZA ST (SP + -616)%Z.
    release_frame ZN ST (SP + -614)%Z.
    release_frame ZP ST (SP + -608)%Z.
    release_frame SA ST (SP + -112)%Z.
    release_frame SN ST (SP + -110)%Z.
    release_frame SPD ST (SP + -104)%Z.
    release_frame SAVED ST (bv_unsigned sp).
    destruct (u64arr_of_u8arr_s usegs mm X bs XA XL) as (ws & WL & EW & WA).
    apply evt_done. unfold biguN_post_g. do 15 eexists. exists mm, ws, len.
    split; [cbv delta [mkR]; reflexivity|].
    unfold LMU_STACK, LAFU_STACK, bigint_at.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [split; [exact WA| split; [exact WL| split; [exact XN| lia]]] |]. split; [exact ST|].
    intros HC. destruct (HR HC) as (HP & -> & HL). split; [reflexivity|]. split; [|exact HL].
    apply bignorm_of_b; [rewrite EW; apply NB; exact HP | lia].
  Qed.

  Lemma lm_false : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len,
    LMINV mm len False -> (CAPL -> False) ->
    evt usegs POST (LM 0x5ea64 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM SP16 XLO XHI YL YHI Y0 Y8 NY.
    intros until len. intros INV HF. zstep. eapply evt_eq; [| eapply lm_exit with (r := 0%Z) (P := False)]; [num_st_eq | exact INV | intros HC; exfalso; exact (HF HC)].
  Qed.

  Lemma lm_N : forall (f : nat) (k : Z) xra xt0 xt1 xt2 xs1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm,
    LMINV mm k False -> (1 <= k)%Z -> (k <= Z.of_nat f)%Z -> (CAPL -> k <= len0 + ny + 1)%Z ->
    evt usegs POST (LM 0x5e8b8 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 (Z_to_bv 64 1) (Z_to_bv 64 k) (Z_to_bv 64 (18446744073709551615 - X)) xa3 xa4 xa5 xa6 xa7
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM SP16 XLO XHI YL YHI Y0 Y8 NY.
    intros f. induction f as [|f IH]; intros until mm; intros INV Hk Hf HB; [exfalso; lia|].
    pose proof INV as INV0. lm_open INV0. lm_env.
    ukstep.
    ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5eaa4%Z => u_trap pc
      | 0x5ea68%Z => first [ fold_limbz; lazymatch goal with
                             | KB : (bv_unsigned (limbz _ _) <> 0)%Z |- _ =>
                                 assert (INV1 : LMINV mm k True) by (lm_close_with ltac:(intros _; right; lazymatch type of KB with (bv_unsigned (limbz _ ?o) <> _)%Z => replace (8 * (k - 1))%Z with o by lia; exact KB end));
                                 eapply evt_eq; [| eapply lm_exit with (r := 1%Z) (P := True)]; [num_st_eq | exact INV1 | intros HC; split; [exact I | lia]]
                             | _ =>
                                 num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV m1 (k + -1) True) by (lm_close_with ltac:(intros _; left; lia)));
                                 eapply evt_eq; [| eapply lm_exit with (r := 1%Z) (P := True)]; [num_st_eq | exact INV1 | intros HC; split; [exact I | lia]]
                             end | fail 100 "cut" pc ]
      | 0x5e8b8%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV m1 (k + -1) False) by lm_close);
                             eapply evt_eq; [| eapply (IH (k + -1)%Z)]; [num_st_eq | exact INV1 | lia | lia | intros HC; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_norm : forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len,
    LMINV mm len False -> (CAPL -> len <= len0 + ny + 1)%Z ->
    evt usegs POST (LM 0x5e8a0 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM SP16 XLO XHI YL YHI Y0 Y8 NY.
    intros until len. intros INV HB. pose proof INV as INV0. lm_open INV0. lm_env.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5eaa4%Z => u_trap pc
      | 0x5ea68%Z => first [ assert (INV1 : LMINV mm len True) by (lm_close_with ltac:(intros _; left; lia)); eapply evt_eq; [| eapply lm_exit with (r := 1%Z) (P := True)]; [num_st_eq | exact INV1 | intros HC; split; [exact I | lia]] | fail 100 "cut" pc ]
      | 0x5e8b8%Z => first [ eapply evt_eq; [| eapply (lm_N (Z.to_nat len) len)]; [num_st_eq | exact INV | lia | lia | exact HB] | fail 100 "cut" pc ]
      end).
  Qed.

  Section XLS.
  Variable xl : Z.
  Hypothesis XL62 : (0 <= xl <= 62)%Z.
  Hypothesis XL0 : (xl = len0)%Z.
  Notation LJ pc j xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm :=
    (LM pc xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 ny) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        (Z_to_bv 64 Y) (Z_to_bv 64 j) (Z_to_bv 64 (8 * xl)) (Z_to_bv 64 xl) (Z_to_bv 64 (18446744073709551615 - Y)) (Z_to_bv 64 (Z.shiftl xl 48)) xs8
        (Z_to_bv 64 (SP + -1104)) (Z_to_bv 64 (18446744073709551615 - (SP + -1112))) (Z_to_bv 64 (18446744073709551615 - (SP + -608))) xt3 xt4 xt5 xt6 mm).

  Section JBODY.
    Variable j : Z.
    Hypothesis Hj : (1 <= j < ny)%Z.
    Hypothesis KBF8 : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm len,
      LMINV mm len False -> (CAPL -> len <= xl + j + 2)%Z -> evt usegs POST (LJ 0x5e944 j xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm).

    Lemma lm_bdc : forall xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm len zl,
      LMINV mm len False -> (0 <= zl <= 62)%Z -> (zl <= xl + 1)%Z -> (CAPL -> len <= xl + j + 1)%Z ->
      evt usegs POST (LJ 0x5e928 j xra xt0 xt1 xt2 (Z_to_bv 64 zl) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm).
    Proof using HLAF ROOM SP16 XLO XHI YL YHI Y0 Y8 NY XL62 XL0 Hj KBF8.
      intros until zl. intros INV Hz Hz1 HB. pose proof INV as INV0. lm_open INV0. lm_env. pose proof XL0 as XL0'. pose proof Hj as Hj'.
      assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
      uwalk ltac:(fun pc => lazymatch pc with | 0x5eaa8%Z => idtac end).
      destruct (u64arr_of_u8arr usegs mm X bs XA XL) as (ws & WL & WA).
      pose proof ZA as [ZB _].
      pose proof (bytes_at_sub usegs mm (SP + -1112) zb 0 (Z.to_nat (8 * zl)) ZB ltac:(lia)) as YB.
      change (skipn 0 zb) with zb in YB. change (Z.of_nat 0) with 0%Z in YB. replace (SP + -1112 + 0)%Z with (SP + -1112)%Z in YB by lia.
      pose proof HLAF as HL. unfold lmN_laf_stmt, lafuN_stmt_g in HL.
      eapply evt_cut.
      { eapply evt_eq; [| eapply HL with (X := X) (Y := (SP + -1112)%Z) (ny := zl) (st := j) (lo := lo) (ws := ws) (len := len)
                                        (ybs := firstn (Z.to_nat (8 * zl)) zb)];
          [ num_st_eq | .. ]; rewrite ?unsigned_lit by lia; unfold LAFU_STACK;
          [ exact MI | exact ST | lia | split; [exact WA| split; [exact WL| split; [exact XN| lia]]] | lia | exact YB
          | rewrite length_firstn; lia | lia | lia | lia | Z.div_mod_to_equations; lia | lia | lia ]. }
      cbv beta. intros ms' P. unfold biguN_post_g in P.
      destruct P as (? & ? & ? & r0 & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & ws3 & len3 & -> & MUc & WMc & MIc & BIG3 & STc & G).
      rewrite !unsigned_lit in MUc, STc by lia. unfold LAFU_STACK in MUc.
      assert (G' : (CAPL -> bv_unsigned r0 = 1 /\ len3 <= xl + j + 2)%Z).
      { intros HC. destruct (G ltac:(lia) ltac:(lia)) as (-> & G1 & _). rewrite unsigned_lit by lia. lia. }
      clear G.
      clear XA XN WA YB.
      lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call usegs mo mn MUc WMc end.
      clear MUc WMc MI HL. destruct BIG3 as (WA3 & WL3 & XN & LEN3).
      num_ret_pc.
      destruct (u8arr_of_u64arr usegs m3 X ws3 WA3 WL3) as (bs3 & XL3 & XA). clear WA3 WL3.
      rename MIc into MI. rename STc into ST.
      assert (INV1 : LMINV m3 len3 False) by lm_close.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5eaa4%Z => u_trap pc
        | 0x5ea64%Z => first [ eapply lm_false; [exact INV1 | intros HC; lia] | fail 100 "cut" pc ]
        | 0x5e944%Z => first [ eapply evt_eq; [| eapply KBF8]; [num_st_eq | exact INV1 | intros HC; lia] | fail 100 "cut" pc ]
        end).
    Qed.

    Lemma lm_S2 : forall (f : nat) (i : Z) xra xt0 xt1 xt2 xa2 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm len zl,
      LMINV mm len False -> (0 <= i < zl)%Z -> (zl <= 62)%Z -> (zl - i <= Z.of_nat f)%Z -> (zl = xl)%Z -> (CAPL -> len <= xl + j + 1)%Z ->
      evt usegs POST (LJ 0x5e9d8 j xra xt0 xt1 xt2 (Z_to_bv 64 zl) (Z_to_bv 64 zl) xa2 (Z_to_bv 64 (63 - i)) (Z_to_bv 64 (SP + -1112 + 8 * zl))
                         (Z_to_bv 64 (SP + -1112 + 8 * i)) xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm).
    Proof using HLAF ROOM SP16 XLO XHI YL YHI Y0 Y8 NY XL62 XL0 Hj KBF8.
      intros f. induction f as [|f IH]; intros until zl; intros INV Hi Hz Hf HZX HB; [exfalso; lia|].
      pose proof INV as INV0. lm_open INV0. lm_env. pose proof XL0 as XL0'. pose proof Hj as Hj'.
      assert (DA2 : IsData xa2) by exact I. assert (DS8 : IsData xs8) by exact I.
      nstep.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5eaa4%Z => u_trap pc
        | 0x5ea64%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV m1 len False) by lm_close); eapply lm_false; [exact INV1 | intros HC; lia] | fail 100 "cut" pc ]
        | 0x5e928%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV m1 len False) by lm_close);
                               eapply evt_eq; [| eapply (lm_bdc)]; [num_st_eq | exact INV1 | lia | lia | exact HB]
                             | num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV m1 len False) by lm_close);
                               eapply evt_eq; [| eapply (lm_bdc)]; [num_st_eq | exact INV1 | lia | lia | exact HB]
                             | fail 100 "cut" pc ]
        | 0x5e9d8%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV m1 len False) by lm_close);
                               eapply evt_eq; [| eapply (IH (i + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia | lia | exact HZX | exact HB] | fail 100 "cut" pc ]
        end).
    Qed.

    Lemma lm_c1c : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm len,
      LMINV mm len False -> (CAPL -> len <= xl + j + 1)%Z ->
      evt usegs POST (LJ 0x5e968 j xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm).
    Proof using HCPY HLAF ROOM SP16 XLO XHI YL YHI Y0 Y8 NY XL62 XL0 Hj KBF8.
      intros until len. intros INV HB. pose proof INV as INV0. lm_open INV0. lm_env.
      assert (DS8 : IsData xs8) by exact I.
      assert (S48 : (Z.shiftl xl 48 mod 18446744073709551616 = xl * 281474976710656)%Z) by (apply shl48_small; lia).
      nstep. nstep.
      if_cases KB; zify_cond KB; [exfalso; lia|].
      nstep.
      if_cases KB0; zify_cond KB0; rewrite S48 in KB0.
      -
        uwalk ltac:(fun pc => lazymatch pc with
          | 0x5eaa4%Z => u_trap pc
          | 0x5e928%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV m1 len False) by lm_close);
                                 eapply evt_eq; [| eapply lm_bdc with (zl := (0 + xl)%Z)]; [num_st_eq | exact INV1 | lia | lia | exact HB] | fail 100 "cut" pc ]
          end).
      -
        uwalk ltac:(fun pc => lazymatch pc with | 0xd06e8%Z => idtac end).
        pose proof SA as [SB0 _].
        pose proof (bytes_at_sub usegs _ (SP + -608) xb 0 (Z.to_nat (8 * xl)) SB0 ltac:(lia)) as SRC.
        change (skipn 0 xb) with xb in SRC. change (Z.of_nat 0) with 0%Z in SRC. replace (SP + -608 + 0)%Z with (SP + -608)%Z in SRC by lia.
        num_call_memcpy HCPY ZA 0%Z (8 * xl)%Z (SP + -608)%Z (firstn (Z.to_nat (8 * xl)) xb) SRC.
        uwalk ltac:(fun pc => lazymatch pc with
          | 0x5eaa4%Z => u_trap pc
          | 0x5e928%Z => first [ exfalso; lia | fail 100 "cut" pc ]
          | 0x5e9d8%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV m1 len False) by lm_close);
                                 eapply evt_eq; [| eapply (lm_S2 (Z.to_nat xl) 0%Z)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | exact HB] | fail 100 "cut" pc ]
          end).
    Qed.

    Lemma lm_c00 : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm len,
      LMINV mm len False -> (CAPL -> len <= xl + j + 1)%Z ->
      evt usegs POST (LJ 0x5e94c j xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm).
    Proof using HCPY HLAF ROOM SP16 XLO XHI YL YHI Y0 Y8 NY XL62 XL0 Hj KBF8.
      intros until len. intros INV HB. pose proof INV as INV0. lm_open INV0. lm_env.
      pose proof (bytes_at_bound _ _ _ _ YA) as YB.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5eaa4%Z => u_trap pc
        | 0x5e944%Z => first [ eapply evt_eq; [| eapply KBF8]; [num_st_eq | exact INV | intros HC; lia] | fail 100 "cut" pc ]
        | 0x5e968%Z => first [ eapply evt_eq; [| eapply lm_c1c]; [num_st_eq | exact INV | exact HB] | fail 100 "cut" pc ]
        end).
    Qed.
  End JBODY.

  Lemma lm_bf8 : forall (j : Z), (1 <= j < ny)%Z ->
    (forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm len, (j + 1 < ny)%Z ->
       LMINV mm len False -> (CAPL -> len <= xl + (j + 1) + 1)%Z -> evt usegs POST (LJ 0x5e94c (j + 1) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm)) ->
    forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm len,
    LMINV mm len False -> (CAPL -> len <= xl + j + 2)%Z -> evt usegs POST (LJ 0x5e944 j xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM SP16 XLO XHI YL YHI Y0 Y8 NY XL62 XL0.
    intros j Hj KJ. intros until len. intros INV HB. lm_env. pose proof XL0 as XL0'.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e8a0%Z => first [ eapply evt_eq; [| eapply lm_norm]; [num_st_eq | exact INV | intros HC; lia] | fail 100 "cut" pc ]
      | 0x5e94c%Z => first [ eapply evt_eq; [| eapply KJ]; [num_st_eq | lia | exact INV | intros HC; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_J : forall (f : nat) (j : Z), (1 <= j < ny)%Z -> (ny - j <= Z.of_nat f)%Z ->
    forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm len,
    LMINV mm len False -> (CAPL -> len <= xl + j + 1)%Z -> evt usegs POST (LJ 0x5e94c j xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 mm).
  Proof using HCPY HLAF ROOM SP16 XLO XHI YL YHI Y0 Y8 NY XL62 XL0.
    intros f. induction f as [|f IH]; intros j Hj Hf; [exfalso; lia|].
    intros until len. intros INV HB.
    eapply (lm_c00 j Hj); [| exact INV | exact HB].
    intros. eapply (lm_bf8 j Hj); [| eassumption | eassumption].
    intros. eapply (IH (j + 1)%Z); [lia | lia | eassumption | eassumption].
  Qed.

  Notation LH pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (LM pc xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 ny) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        (Z_to_bv 64 Y) xs3 xs4 (Z_to_bv 64 xl) xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).

  Lemma lm_b4c : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len,
    LMINV mm len False -> (1 <= ny)%Z -> (CAPL -> len <= xl + 1)%Z ->
    evt usegs POST (LH 0x5e898 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using HCPY HLAF ROOM SP16 XLO XHI YL YHI Y0 Y8 NY XL62 XL0.
    intros until len. intros INV Hn HB. lm_env. pose proof XL62 as XL62'. pose proof XL0 as XL0'.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5eaa4%Z => u_trap pc
      | 0x5ea30%Z => u_trap pc
      | 0x5e8a0%Z => first [ eapply evt_eq; [| eapply lm_norm]; [num_st_eq | exact INV | intros HC; lia] | fail 100 "cut" pc ]
      | 0x5e94c%Z => first [ eapply evt_eq; [| eapply (lm_J (Z.to_nat ny) 1%Z)]; [num_st_eq | lia | lia | exact INV | intros HC; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_S1 : forall (f : nat) (i N : Z) xra xt0 xt1 xt2 xa0 xa3 xa6 xa7 xs3 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len,
    LMINV mm len False -> (0 <= i < len)%Z -> (62 <= N < 2305843009213693952)%Z -> (1 <= ny)%Z -> (len - i <= Z.of_nat f)%Z -> (CAPL -> len <= xl)%Z ->
    evt usegs POST (LH 0x5e83c xra xt0 xt1 xt2 xa0 (Z_to_bv 64 (63 - i)) (Z_to_bv 64 (N - i)) xa3 (Z_to_bv 64 (18446744073709551615 - (len - 1) + N))
                       (Z_to_bv 64 (X + 8 * i)) xa6 xa7 xs3 (Z_to_bv 64 len) xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using HCPY HLAF ROOM SP16 XLO XHI YL YHI Y0 Y8 NY XL62 XL0.
    intros f. induction f as [|f IH]; intros until len; intros INV Hi HN Hn Hf HB; [exfalso; lia|].
    pose proof INV as INV0. lm_open INV0. lm_env. pose proof XL0 as XL0'.
    assert (DA0 : IsData xa0) by exact I. assert (DA3 : IsData xa3) by exact I.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5eaa4%Z => u_trap pc
      | 0x5ea64%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV m1 len False) by lm_close); eapply lm_false; [exact INV1 | intros HC; lia] | fail 100 "cut" pc ]
      | 0x5e898%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV m1 len False) by lm_close);
                             eapply evt_eq; [| eapply lm_b4c]; [num_st_eq | exact INV1 | lia | intros HC; lia]
                           | num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV m1 (len + 1) False) by lm_close);
                             eapply evt_eq; [| eapply lm_b4c]; [num_st_eq | exact INV1 | lia | intros HC; lia]
                           | fail 100 "cut" pc ]
      | 0x5e83c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV m1 len False) by lm_close);
                             eapply evt_eq; [| eapply (IH (i + 1)%Z N)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | exact HB] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_ab0 : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len,
    LMINV mm len False -> (CAPL -> len <= xl)%Z ->
    evt usegs POST (LH 0x5e7fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 len) xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using HCPY HLAF ROOM SP16 XLO XHI YL YHI Y0 Y8 NY XL62 XL0.
    intros until len. intros INV HB. pose proof INV as INV0. lm_open INV0. lm_env. pose proof XL62 as XL62'. pose proof XL0 as XL0'.
    pose proof (bytes_at_bound _ _ _ _ YA) as YB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5eaa4%Z => u_trap pc
      | 0x5e8a0%Z => first [ eapply evt_eq; [| eapply lm_norm]; [num_st_eq | exact INV | intros HC; lia] | fail 100 "cut" pc ]
      | 0x5e898%Z => first [ eapply evt_eq; [| eapply lm_b4c]; [num_st_eq | exact INV | lia | intros HC; lia] | fail 100 "cut" pc ]
      | 0x5e83c%Z => first [ eapply evt_eq; [| eapply (lm_S1 (Z.to_nat len) 0%Z ((0 - X) mod 18446744073709551616 / 8)%Z)];
                             [num_st_eq | exact INV | lia | lia | lia | lia | exact HB] | fail 100 "cut" pc ]
      end).
  Qed.
  End XLS.

  Ltac peel_cell FR H :=
    lazymatch type of FR with
    | rw_cells ?s ?m ?A0 (?c :: ?rest) =>
        change (c :: rest) with ([c] ++ rest) in FR; apply num_rw_cells_app in FR; destruct FR as [H FR];
        cbn [cells_size csize Nat.add] in FR;
        lazymatch type of FR with
        | rw_cells _ _ (?b + ?k + Z.of_nat ?n)%Z _ =>
            let v := eval vm_compute in (k + Z.of_nat n)%Z in replace (b + k + Z.of_nat n)%Z with (b + v)%Z in FR by lia
        end
    end.

  Lemma lm_body : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ws,
    mem_inv usegs m0 -> stk usegs m0 lo SP -> bigint_at usegs m0 X ws len0 -> bytes_at usegs m0 Y ybs ->
    evt usegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 ny) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 LMN_ENTRY) fc None m0 (seg_rom usegs)).
  Proof using HCPY HLAF ROOM SP16 XLO XHI YL YHI Y0 Y8 NY.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ws MI ST (WA & WL & XN0 & LEN0) YA. pose (len := len0). assert (ELEN : len = len0) by reflexivity. change len0 with len in XN0, LEN0. clearbody len.
    unfold LMN_ENTRY. lm_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl usegs m0) as WM. unfold LMU_STACK, LAFU_STACK in MU.
    set (m := m0) in MI, ST, WA, XN0, YA, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 1120%nat ST.
    apply (rw_cells_split_CB usegs m _ [] 1120 junk [] [8;496;2;6;496;2;6;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 13 step.
    peel_cell FR PAD0. peel_cell FR ZC. peel_cell FR ZN. peel_cell FR ZP. peel_cell FR SC. peel_cell FR SN. peel_cell FR SPD.
    rename FR into SAVED.
    pose proof (u8arr_of_rw_cells usegs _ _ _ _ ZC) as ZA. assert (ZL : length j0 = 496%nat) by (destruct ZC as [[Hwf _] _]; cbn in Hwf; tauto). clear ZC.
    pose proof (u8arr_of_rw_cells usegs _ _ _ _ SC) as SA. assert (SL : length j3 = 496%nat) by (destruct SC as [[Hwf _] _]; cbn in Hwf; tauto). clear SC.
    destruct (u8arr_of_u64arr usegs _ X ws WA WL) as (bs & XL & XA). clear WA WL.
    rename XN0 into XN.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5eaa4%Z => u_trap pc
      | 0x5e7fc%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV m1 len False) by lm_close);
                             eapply evt_eq; [| eapply (lm_ab0 (0 + len)%Z ltac:(lia) ltac:(lia))]; [num_st_eq | exact INV1 | intros HC; lia] | fail 100 "cut" pc ]
      | 0xd06e8%Z => idtac
      end).
    pose proof XA as [XB0 _].
    pose proof (bytes_at_sub usegs _ X bs 0 (Z.to_nat (8 * len)) XB0 ltac:(lia)) as SRC.
    change (skipn 0 bs) with bs in SRC. change (Z.of_nat 0) with 0%Z in SRC. replace (X + 0)%Z with X in SRC by lia.
    num_call_memcpy HCPY SA 0%Z (8 * len)%Z X (firstn (Z.to_nat (8 * len)) bs) SRC.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5eaa4%Z => u_trap pc
      | 0x5e7fc%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV m1 len False) by lm_close);
                             eapply evt_eq; [| eapply (lm_ab0 (0 + len)%Z ltac:(lia) ltac:(lia))]; [num_st_eq | exact INV1 | intros HC; lia] | fail 100 "cut" pc ]
      end).
  Qed.

End LMU.

Theorem lmuN_spec : lmN_memcpy_stmt -> lmN_laf_stmt -> lmuN_stmt_g usegs LMN_ENTRY.
Proof.
  intros HC HL. unfold lmuN_stmt_g. intros until ybs. intros MI ST ROOM SP16 BIG XLO XHI YA YL YHI Y0 Y8 NY.
  eapply lm_body; eassumption.
Qed.
