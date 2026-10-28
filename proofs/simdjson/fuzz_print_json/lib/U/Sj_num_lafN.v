(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Definition LAFN_ENTRY : Z := 0x5edb8.

Section LAF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X Y ny st lo len0 : Z) (ybs : list byte) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Hypothesis ROOM : (lo + LAFU_STACK <= SP)%Z.
  Hypothesis XHI : (X + 498 <= 2^64)%Z.
  Hypothesis YL : Z.of_nat (length ybs) = (8 * ny)%Z.
  Hypothesis YLO : (SP <= Y)%Z.
  Hypothesis YHI : (Y + 8 * ny <= X)%Z.
  Hypothesis Y0 : (0 < Y)%Z.
  Hypothesis Y8 : (Y mod 8 = 0)%Z.
  Hypothesis NY : (0 <= ny <= 62)%Z.
  Hypothesis ST0 : (0 <= st <= 62)%Z.

  Notation W := [(SP - LAFU_STACK, SP); (X, X + 498)]%Z.
  Notation GL := (fun (a0 : word) (ws' : list word) (len' : Z) => (len0 <= 61 -> ny + st <= 61 -> a0 = Z_to_bv 64 1 /\ len' <= Z.max len0 (ny + st) + 1 /\ Z.max len0 (ny + st) <= len')%Z).
  Notation POST := (biguN_post_g LAFU_STACK GL usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m0).
  Notation LA pc xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR ra (Z_to_bv 64 (SP + -32)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3
             s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition LAINV (mm : mem) (len : Z) : Prop :=
    rw_cells usegs mm (SP + -32) [C8 s3; C8 s2; C8 s1; C8 s0] /\
    (exists bs, u8arr usegs mm X bs /\ length bs = 496%nat) /\
    rw_cells usegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    bytes_at usegs mm Y ybs /\
    mem_inv usegs mm /\ munch W m0 mm /\ wmono usegs m0 mm /\ stk usegs mm lo (SP + -32).

  Ltac la_open H :=
    let bs := fresh "bs" in
    destruct H as (FR & (bs & XA & ?XL) & XN & ?LEN & YA & MI & MU & WM & ST); unfold LAFU_STACK in MU.
  Ltac la_close :=
    lazymatch goal with
    | |- LAINV _ _ =>
        split; [eassumption|]; split; [eexists; split; [eassumption| lia]|]; split; [eassumption|]; split; [lia|];
        split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.
  Ltac la_env :=
    pose proof ROOM as ROOM'; unfold LAFU_STACK in ROOM';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof XHI as XHI'; change (2 ^ 64)%Z with 18446744073709551616%Z in XHI';
    pose proof YL as YL'; pose proof YLO as YLO'; pose proof YHI as YHI'; pose proof Y0 as Y0'; pose proof NY as NY'; pose proof ST0 as ST0'.

  Lemma la_exit : forall (r : Z) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    LAINV mm len -> (len0 <= 61 -> ny + st <= 61 -> r = 1 /\ len <= Z.max len0 (ny + st) + 1 /\ Z.max len0 (ny + st) <= len)%Z ->
    evt usegs POST (LA 0x5ef70 xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 r) xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI YL YLO YHI Y0 Y8 NY ST0.
    intros until len. intros INV HR. la_open INV. la_env.
    do 5 zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    destruct (u64arr_of_u8arr usegs mm X bs XA XL) as (ws & WL & WA).
    apply evt_done. unfold biguN_post_g. do 15 eexists. exists mm, ws, len.
    split; [cbv delta [mkR]; reflexivity|].
    unfold LAFU_STACK, bigint_at.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [split; [exact WA| split; [exact WL| split; [exact XN| lia]]] |]. split; [exact ST|].
    intros H1 H2. destruct (HR H1 H2) as (-> & H3 & H4). split; [reflexivity|]. split; assumption.
  Qed.

  Lemma la_false : forall xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    LAINV mm len -> (len0 <= 61 -> ny + st <= 61 -> False)%Z ->
    evt usegs POST (LA 0x5ef6c xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI YL YLO YHI Y0 Y8 NY ST0.
    intros until len. intros INV HF. zstep. eapply evt_eq; [| eapply la_exit with (r := 0%Z)]; [num_st_eq | exact INV | intros H1 H2; exfalso; exact (HF H1 H2)].
  Qed.

  Lemma la_push : forall xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    LAINV mm len -> (len = Z.max len0 (ny + st))%Z ->
    evt usegs POST (LA 0x5ef44 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 X) (Z_to_bv 64 len) xa2 xa3 xa4 (Z_to_bv 64 (18446744073709551615 - X)) xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI YL YLO YHI Y0 Y8 NY ST0.
    intros until len. intros INV HLEN. pose proof INV as INV0. la_open INV0. la_env.
    walk ltac:(fun pc => lazymatch pc with
      | 0x5ef98%Z => u_trap pc
      | 0x5ef6c%Z => first [ eapply la_false; [exact INV | intros; lia] | fail 100 "cut" pc ]
      | 0x5ef70%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 (len + 1)) by la_close); eapply evt_eq; [| eapply la_exit with (r := 1%Z)]; [num_st_eq | exact INV1 | intros; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma la_C : forall (f : nat) (k : Z) xt0 xt1 xt2 xs0 xs1 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    LAINV mm len -> (len = Z.max len0 (ny + st))%Z -> (0 <= k <= len)%Z -> (len - k <= Z.of_nat f)%Z ->
    evt usegs POST (LA 0x5ef14 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 X) (Z_to_bv 64 len) (Z_to_bv 64 (18446744073709551552 + k)) (Z_to_bv 64 (8 * k)) (Z_to_bv 64 1)
                       (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (len - k)) xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI YL YLO YHI Y0 Y8 NY ST0.
    intros f. induction f as [|f IH]; intros until len; intros INV HLEN Hk Hf.
    - pose proof INV as INV0. la_open INV0. la_env. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x5ef98%Z => u_trap pc
        | 0x5ef44%Z => first [ eapply evt_eq; [| eapply la_push]; [num_st_eq | exact INV | exact HLEN] | fail 100 "cut" pc ]
        end).
    - pose proof INV as INV0. la_open INV0. la_env. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x5ef98%Z => u_trap pc
        | 0x5ef44%Z => first [ eapply evt_eq; [| eapply la_push]; [num_st_eq | exact INV | exact HLEN] | fail 100 "cut" pc ]
        | 0x5ef70%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 len) by la_close); eapply evt_eq; [| eapply la_exit with (r := 1%Z)]; [num_st_eq | exact INV1 | intros; lia] | fail 100 "cut" pc ]
        | 0x5ef14%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 len) by la_close);
                               eapply evt_eq; [| eapply (IH (k + 1)%Z)]; [num_st_eq | exact INV1 | exact HLEN | lia | lia] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma la_e80 : forall xt0 xt1 xt2 xs0 xs1 xa1 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    LAINV mm len -> (len = Z.max len0 (ny + st))%Z -> (st + ny <= len)%Z ->
    evt usegs POST (LA 0x5eedc xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 X) xa1 (Z_to_bv 64 ny) (Z_to_bv 64 st) (Z_to_bv 64 1)
                       (Z_to_bv 64 (18446744073709551615 - X)) xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI YL YLO YHI Y0 Y8 NY ST0.
    intros until len. intros INV HLEN HL. pose proof INV as INV0. la_open INV0. la_env.
    assert (DA7 : IsData xa7) by exact I.
    walk ltac:(fun pc => lazymatch pc with
      | 0x5ef98%Z => u_trap pc
      | 0x5ef70%Z => first [ eapply evt_eq; [| eapply la_exit with (r := 1%Z)]; [num_st_eq | exact INV | intros; lia] | fail 100 "cut" pc ]
      | 0x5ef14%Z => first [ eapply evt_eq; [| eapply (la_C (Z.to_nat len) (st + ny)%Z)]; [num_st_eq | exact INV | exact HLEN | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma la_A : forall (f : nat) (j : Z) xt5 xt6 xs0 xs1 xa7 xs2 xs3 mm len,
    LAINV mm len -> (len = Z.max len0 (ny + st))%Z -> (st + ny <= len)%Z -> (0 <= j < ny)%Z -> (ny - j <= Z.of_nat f)%Z ->
    evt usegs POST (LA 0x5eea0 (Z_to_bv 64 0) (Z_to_bv 64 (18446744073709551615 - Y)) (Z_to_bv 64 (st + -63 + j)) xs0 xs1
                       (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 ny) (Z_to_bv 64 st) (Z_to_bv 64 1)
                       (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (8 * j)) xa7 xs2 xs3
                       (Z_to_bv 64 (8 * (st + j))) (Z_to_bv 64 (ny - j)) xt5 xt6 mm).
  Proof using ROOM XHI YL YLO YHI Y0 Y8 NY ST0.
    intros f. induction f as [|f IH]; intros until len; intros INV HLEN HL Hj Hf; [exfalso; lia|].
    pose proof INV as INV0. la_open INV0. la_env.
    assert (DA7 : IsData xa7) by exact I.
    nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x5ef98%Z => u_trap pc
      | 0x5eedc%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 len) by la_close);
                             eapply evt_eq; [| eapply la_e80]; [num_st_eq | exact INV1 | exact HLEN | lia] | fail 100 "cut" pc ]
      | 0x5eea0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 len) by la_close);
                             eapply evt_eq; [| eapply (IH (j + 1)%Z)]; [num_st_eq | exact INV1 | exact HLEN | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma la_de8 : forall xt0 xt1 xt2 xs0 xs1 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    LAINV mm len -> (len = Z.max len0 (ny + st))%Z -> (st + ny <= len)%Z -> (0 < ny)%Z ->
    evt usegs POST (LA 0x5ee44 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 ny) (Z_to_bv 64 st) (Z_to_bv 64 1) xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI YL YLO YHI Y0 Y8 NY ST0.
    intros until len. intros INV HLEN HL Hn. pose proof INV as INV0. la_open INV0. la_env. pose proof Y8 as Y8'.
    assert (XR : (0 <= X)%Z) by (destruct XA as [BA _]; pose proof (bytes_at_bound _ _ _ _ BA); lia).
    walk ltac:(fun pc => lazymatch pc with
      | 0x5ef98%Z => u_trap pc
      | 0x5ef8c%Z => u_trap pc
      | 0x5eea0%Z => first [ eapply evt_eq; [| eapply (la_A (Z.to_nat ny) 0%Z)]; [num_st_eq | exact INV | exact HLEN | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma la_Z : forall (f : nat) (i : Z) xt1 xt2 xs0 xs1 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    LAINV mm len -> (len0 <= ny + st)%Z -> (0 <= i < ny + st)%Z -> (ny + st <= 62)%Z -> (ny + st - i <= Z.of_nat f)%Z ->
    evt usegs POST (LA 0x5ee24 (Z_to_bv 64 1) xt1 xt2 xs0 xs1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 ny) (Z_to_bv 64 st) (Z_to_bv 64 (ny + st))
                       (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 (ny + st - i + 1)) (Z_to_bv 64 18446744073709551608) xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI YL YLO YHI Y0 Y8 NY ST0.
    intros f. induction f as [|f IH]; intros until len; intros INV HL0 Hi Hn Hf; [exfalso; lia|].
    pose proof INV as INV0. la_open INV0. la_env.
    assert (XR : (0 <= X)%Z) by (destruct XA as [BA _]; pose proof (bytes_at_bound _ _ _ _ BA); lia).
    nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x5ef98%Z => u_trap pc
      | 0x5ef70%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 (ny + st)) by la_close); eapply evt_eq; [| eapply la_exit with (r := 1%Z)]; [num_st_eq | exact INV1 | intros; lia] | fail 100 "cut" pc ]
      | 0x5ee44%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 (ny + st)) by la_close);
                             eapply evt_eq; [| eapply la_de8]; [num_st_eq | exact INV1 | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5ee24%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 len) by la_close);
                             eapply evt_eq; [| eapply (IH (i + 1)%Z)]; [num_st_eq | exact INV1 | exact HL0 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma la_body : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ws,
    mem_inv usegs m0 -> stk usegs m0 lo SP -> bigint_at usegs m0 X ws len0 -> bytes_at usegs m0 Y ybs ->
    evt usegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 ny) (Z_to_bv 64 st) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 LAFN_ENTRY) fc None m0 (seg_rom usegs)).
  Proof using ROOM XHI YL YLO YHI Y0 Y8 NY ST0.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ws MI ST (WA & WL & XN0 & LEN0) YA. pose (len := len0). assert (ELEN : len = len0) by reflexivity. change len0 with len in XN0, LEN0. clearbody len.
    unfold LAFN_ENTRY. la_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl usegs m0) as WM. unfold LAFU_STACK in MU.
    set (m := m0) in MI, ST, WA, XN0, YA, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 32%nat ST.
    apply (rw_cells_split_CB usegs m _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 4 step.
    destruct (u8arr_of_u64arr usegs _ X ws WA WL) as (bs & XL & XA). clear WA WL.
    rename XN0 into XN.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (INV : LAINV m1 len) by la_close end.
    assert (XR : (0 <= X)%Z) by (destruct XA as [BA _]; pose proof (bytes_at_bound _ _ _ _ BA); lia).
    walk ltac:(fun pc => lazymatch pc with
      | 0x5ef98%Z => u_trap pc
      | 0x5ef6c%Z => first [ eapply la_false; [exact INV | intros; lia] | fail 100 "cut" pc ]
      | 0x5ef70%Z => first [ eapply evt_eq; [| eapply la_exit with (r := 1%Z)]; [num_st_eq | exact INV | intros; lia] | fail 100 "cut" pc ]
      | 0x5ee44%Z => first [ eapply evt_eq; [| eapply la_de8]; [num_st_eq | exact INV | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5ee24%Z => first [ eapply evt_eq; [| eapply (la_Z (Z.to_nat 62) len)]; [num_st_eq | exact INV | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End LAF.

Theorem lafuN_spec : lafuN_stmt_g usegs LAFN_ENTRY.
Proof.
  unfold lafuN_stmt_g. intros until ybs. intros MI ST ROOM BIG XHI YA YL YLO YHI Y0 Y8 NY ST0.
  eapply la_body; eassumption.
Qed.
