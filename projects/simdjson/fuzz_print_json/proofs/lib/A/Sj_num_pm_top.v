(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_pm_kit Sj_num_pm_defs Sj_num_pm_z8 Sj_num_pm_z1 Sj_num_pm_int1 Sj_num_pm_int3 Sj_num_pm_ti3 Sj_num_pm_fent.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac addr_near k ::= let inb := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 16384))%Z in lazymatch inb with true => idtac end.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section PMA.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X N DG A IP IL FPT FL lo : Z) (txt : list byte) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation TL := (Z.of_nat (length txt)).
  Hypothesis ROOM : (lo + PMA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XR : (0x6c9000 <= X /\ X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis NR : (N mod 8 = 0 /\ 0x6c9000 <= N /\ N + 64 <= lo)%Z.
  Hypothesis DGR : (DG mod 8 = 0 /\ SP <= DG /\ DG + 8 <= USTACK_TOP)%Z.
  Hypothesis TXR : (0 < A /\ A + TL <= lo /\ TL < 2147483648)%Z.
  Hypothesis SPANS : pm_spans_ok A txt IP IL FPT FL.

  Hypothesis XSEP : ((X + 504 <= N \/ N + 64 <= X) /\ (X + 504 <= A \/ A + TL <= X)
                     /\ (X / 8 + 2147450880 + 63 <= N \/ N + 64 <= X / 8 + 2147450880) /\ (X / 8 + 2147450880 + 63 <= A \/ A + TL <= X / 8 + 2147450880))%Z.
  Notation W := [(SP - 160, SP); (X, X + 504); (DG, DG + 8)]%Z.

  Hypothesis SHPT : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' (8 * (A / 8)) (A + TL - 8 * (A / 8)).
  Hypothesis SHPN : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' N 64.
  Hypothesis SHPD : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' DG 8.
  Hypothesis SHPL : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' 0x2e600 160.
  Variable Q : machine_state -> Prop.
  Collection PMH := ROOM TOP X8 XR XSH XS0 NR DGR TXR SPANS XSEP SHPT SHPN SHPD SHPL.
  Notation PMINV := (pm_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X N DG A IP IL FPT FL txt lo m0).

  Notation PMS pc xra xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -160)) gp tp (Z_to_bv 64 (DG / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 DG) xa4 xa5 xa6 xa7
             xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Hypothesis KEXIT : forall xra xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 w8 w16 w24 w32 w40 (mm : mem) len dg,
    PMINV w8 w16 w24 w32 w40 mm len dg ->
    evt asegs Q (PMS 0xe7d38 xra xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).

  Ltac fam L := constr:(L sp F fc X N DG A IP IL FPT FL lo txt m0 ROOM TOP X8 XR XSH XS0 NR DGR TXR SPANS XSEP SHPT SHPN SHPD SHPL Q).

  Notation PMD D := (D ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X N DG A IP IL FPT FL lo txt m0 Q) (only parsing).
  Notation PML L := (L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X N DG A IP IL FPT FL lo txt m0
                       ROOM TOP X8 XR XSH XS0 NR DGR TXR SPANS XSEP SHPT SHPN SHPD SHPL Q) (only parsing).

  Ltac pm_fam_clear m1 := repeat match goal with
    | H : u8arr asegs m1 _ _ |- _ => clear H
    | H : bytes_at asegs m1 (_ / 8 + 2147450880)%Z _ |- _ => clear H
    | H : mem_inv asegs m1 |- _ => clear H
    | H : munch _ _ m1 |- _ => clear H
    | H : wmono asegs _ m1 |- _ => clear H end.
  Ltac pm_fam_intro m1 :=
    pm_fam_clear m1; repeat lazymatch goal with |- u8arr _ _ _ _ -> _ => fail | |- forall _, _ => intro end;
    let XA := fresh "XA" in let XL := fresh "XL" in let ZR := fresh "ZR" in let MI := fresh "MI" in
    let MU := fresh "MU" in let WM := fresh "WM" in let MUX := fresh "MUX" in let WMX := fresh "WMX" in
    intros XA XL ZR MI MU WM MUX WMX;
    lazymatch type of MUX with munch _ _ ?mm2 => transport_after_call asegs m1 mm2 MUX WMX end; clear MUX WMX.

  Ltac pm_len k := lazymatch goal with XN : rw_cells asegs _ (_ + 496)%Z [C2 (Z_to_bv 64 ?l)] |- _ => k l end.
  Ltac pm_mul_cut L KW :=
    pm_len ltac:(fun l => num_cur_mem ltac:(fun m1 =>
      eapply evt_eq; [| eapply (L 62%nat 0%Z l)];
      [ num_st_eq | eassumption | lia | eassumption | eassumption | eassumption | eassumption | apply munch_refl | apply wmono_refl | lia | lia | lia
      | pm_fam_intro m1; KW ])).
  Ltac pm_car_cut L KW :=
    pm_len ltac:(fun l => num_cur_mem ltac:(fun m1 =>
      eapply evt_eq; [| eapply (L 62%nat 1%Z l)];
      [ num_st_eq | eassumption | lia | eassumption | eassumption | eassumption | eassumption | apply munch_refl | apply wmono_refl | lia | lia | lia | lia
      | pm_fam_intro m1; KW | pm_fam_intro m1; KW ])).

  Ltac pm_env :=
    unfold PMA_STACK, USTACK_TOP in *;
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let RL := fresh "RL" in pose proof (repeat_length (Z_to_bv 8 0) 63) as RL;
    let SO := fresh "SO" in pose proof SPANS as SO; unfold pm_spans_ok in SO.

  Notation PE := (IP + IL)%Z.

  Lemma spill_c8 : forall (m : mem) B j0 j1 j2 j3 j4 j5 rest,
    rw_cells asegs m B (CB 8 j0 :: CB 8 j1 :: CB 8 j2 :: CB 8 j3 :: CB 8 j4 :: CB 8 j5 :: rest) ->
    rw_cells asegs m B (CB 8 j0 :: C8 (le_bytes_to_word j1) :: C8 (le_bytes_to_word j2) :: C8 (le_bytes_to_word j3) :: C8 (le_bytes_to_word j4) :: C8 (le_bytes_to_word j5) :: rest).
  Proof.
    intros m B j0 j1 j2 j3 j4 j5 rest H.
    apply (num_cb8_c8 asegs _ _ [CB 8 j0] _ j1) in H. cbn [app] in H.
    apply (num_cb8_c8 asegs _ _ [CB 8 j0; C8 (le_bytes_to_word j1)] _ j2) in H. cbn [app] in H.
    apply (num_cb8_c8 asegs _ _ [CB 8 j0; C8 (le_bytes_to_word j1); C8 (le_bytes_to_word j2)] _ j3) in H. cbn [app] in H.
    apply (num_cb8_c8 asegs _ _ [CB 8 j0; C8 (le_bytes_to_word j1); C8 (le_bytes_to_word j2); C8 (le_bytes_to_word j3)] _ j4) in H. cbn [app] in H.
    apply (num_cb8_c8 asegs _ _ [CB 8 j0; C8 (le_bytes_to_word j1); C8 (le_bytes_to_word j2); C8 (le_bytes_to_word j3); C8 (le_bytes_to_word j4)] _ j5) in H. cbn [app] in H.
    exact H.
  Qed.

  Lemma pm_d58 : forall (p : Z) xra xt2 xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 w8 w16 w24 w32 w40 (mm : mem) len dg,
    PMINV w8 w16 w24 w32 w40 mm len dg -> (IP <= p <= PE)%Z -> (0 <= dg < 769)%Z ->
    evt asegs Q (PMS 0xe6758 xra xt2 xs0 xs1 (Z_to_bv 64 X) (Z_to_bv 64 N) (Z_to_bv 64 769) (Z_to_bv 64 p) (Z_to_bv 64 p) xa6 xa7
                     xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 189952) (Z_to_bv 64 PE) xt5 xt6 mm).
  Proof using PMH KEXIT.
    intros until dg. intros INV Hp Hd. pose proof INV as INV0. pm_open INV0. pm_env.
    let L1 := fam constr:(pm_z1a) in
    awalk ltac:(fun pc => lazymatch pc with
      | 0xe6cf8%Z => first [ eapply evt_eq; [| eapply (PML pm_fent KEXIT); [exact INV | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xe676c%Z => first [ eapply evt_eq; [| eapply (L1 (Z.to_nat (PE - p)) p PE)];
            [ num_st_eq | eassumption | eassumption | eassumption | lia | lia | lia
            | intros q Hq; intros; awalk ltac:(fun pc => lazymatch pc with
                | 0xe6cf8%Z => first [ eapply evt_eq; [| eapply (PML pm_fent KEXIT); [pm_close | lia]]; num_st_eq | fail 100 "cut" pc ]
                | 0xe6830%Z => first [ eapply evt_eq; [| eapply (PML pm_i_head _ _ _ _ (PML pm_ti KEXIT _ _ _ _) (fun len' dg' xra xt2 xs0 xs1 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 mm' I' D' => PML pm_fent KEXIT xra xt2 xs0 xs1 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 _ _ _ _ _ mm' len' dg' I' D') (Z.to_nat (PE - q)) q len dg); [pm_close | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
                end)
            | intros; awalk ltac:(fun pc => lazymatch pc with
                | 0xe6cf8%Z => first [ eapply evt_eq; [| eapply (PML pm_fent KEXIT); [exact INV | lia]]; num_st_eq | fail 100 "cut" pc ]
                end) ] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_entry : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 xbs jd len,
    mem_inv asegs m0 -> stk asegs m0 lo SP -> client_consts m0 ->
    u8arr asegs m0 X xbs -> length xbs = 496%nat -> rw_cells asegs m0 (X + 496) [C2 (Z_to_bv 64 len)] -> (0 <= len <= 62)%Z ->
    bytes_at asegs m0 (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    rw_cells asegs m0 DG [CB 8 jd] ->
    rw_cells asegs m0 (N + 32) [C8 (Z_to_bv 64 IP); C8 (Z_to_bv 64 IL); C8 (Z_to_bv 64 FPT); C8 (Z_to_bv 64 FL)] ->
    bytes_at asegs m0 A txt -> (exists tb, bytes_at asegs m0 0x2e600 tb /\ length tb = 160%nat) ->
    evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 N) (Z_to_bv 64 769) (Z_to_bv 64 DG) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xe65c8) fc None m0 (seg_rom asegs)).
  Proof using PMH KEXIT.
    intros until len. intros MI ST (G1 & G2 & G3 & G4) XA XL XN LEN ZR DGC NUMC TXT (tb & TB & TBL).
    unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in G1, G2, G3, G4.
    pm_env.
    pose proof (munch_refl [(SP - 160, SP); (X, X + 504); (DG, DG + 8)]%Z m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    set (m := m0) in MI, ST, G1, G2, G3, G4, XA, XN, ZR, DGC, NUMC, TXT, TB, MU at 2, WM at 2 |- *. clearbody m.
    step.
    carve_frame 160%nat ST.
    apply (rw_cells_split_CB asegs m _ [] 160 junk [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    apply spill_c8 in FR.
    let L8 := fam constr:(pm_z8a) in
    awalk ltac:(fun pc => lazymatch pc with
      | 0xe6758%Z => first [ eapply evt_eq; [| eapply (pm_d58 IP); [pm_close | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xe6694%Z => first [ eapply evt_eq; [| eapply (L8 (Z.to_nat IL) IP IL 0%Z)];
            [ num_st_eq | eassumption | eassumption | eassumption | lia | lia | lia | lia | lia
            | intros j'; intros; awalk ltac:(fun pc => lazymatch pc with
                | 0xe6758%Z => first [ eapply evt_eq; [| eapply (pm_d58 (IP + 8 * j')%Z); [pm_close | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
                end)
            | intros j'; intros; awalk ltac:(fun pc => lazymatch pc with
                | 0xe6758%Z => first [ eapply evt_eq; [| eapply (pm_d58 (IP + 8 * j')%Z); [pm_close | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
                end) ] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_exit :
    (forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (m' : mem) xbs' len' dg',
       munch [(SP - 160, SP); (X, X + 504); (DG, DG + 8)]%Z m0 m' -> wmono asegs m0 m' -> mem_inv asegs m' -> stk asegs m' lo SP ->
       u8arr asegs m' X xbs' -> length xbs' = 496%nat -> rw_cells asegs m' (X + 496) [C2 (Z_to_bv 64 len')] -> (0 <= len' <= 62)%Z ->
       bytes_at asegs m' (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
       rw_cells asegs m' DG [C8 (Z_to_bv 64 dg')] -> (0 <= dg' <= 770)%Z ->
       rw_cells asegs m' (N + 32) [C8 (Z_to_bv 64 IP); C8 (Z_to_bv 64 IL); C8 (Z_to_bv 64 FPT); C8 (Z_to_bv 64 FL)] ->
       bytes_at asegs m' A txt ->
       evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' (seg_rom asegs))) ->
    forall xra xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 w8 w16 w24 w32 w40 (mm : mem) len dg,
    PMINV w8 w16 w24 w32 w40 mm len dg ->
    evt asegs Q (PMS 0xe7d38 xra xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using PMH.
    intros HK. intros until dg. intros INV. pm_open INV. pm_env.
    do 13 zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    eapply evt_eq; [| eapply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm bs len dg); eassumption].
    num_st_eq.
  Qed.
End PMA.

Definition pma_stmt : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (X N DG A IP IL FPT FL lo : Z) (txt : list byte) (m0 : mem),
    ((lo + PMA_STACK <= (bv_unsigned sp))%Z) ->
    (((bv_unsigned sp) + 16 <= USTACK_TOP)%Z) ->
    ((X mod 8 = 0)%Z) ->
    ((0x6c9000 <= X /\ X + 504 <= lo)%Z) ->
    ((X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z) ->
    ((0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z) ->
    ((N mod 8 = 0 /\ 0x6c9000 <= N /\ N + 64 <= lo)%Z) ->
    ((DG mod 8 = 0 /\ (bv_unsigned sp) <= DG /\ DG + 8 <= USTACK_TOP)%Z) ->
    ((0 < A /\ A + (Z.of_nat (length txt)) <= lo /\ (Z.of_nat (length txt)) < 2147483648)%Z) ->
    (pm_spans_ok A txt IP IL FPT FL) ->
    (((X + 504 <= N \/ N + 64 <= X) /\ (X + 504 <= A \/ A + (Z.of_nat (length txt)) <= X) /\ (X / 8 + 2147450880 + 63 <= N \/ N + 64 <= X / 8 + 2147450880) /\ (X / 8 + 2147450880 + 63 <= A \/ A + (Z.of_nat (length txt)) <= X / 8 + 2147450880))%Z) ->
    (forall m', munch [(bv_unsigned sp - 160, bv_unsigned sp); (X, X + 504); (DG, DG + 8)]%Z m0 m' -> wmono asegs m0 m' -> shz m' (8 * (A / 8)) (A + (Z.of_nat (length txt)) - 8 * (A / 8))) ->
    (forall m', munch [(bv_unsigned sp - 160, bv_unsigned sp); (X, X + 504); (DG, DG + 8)]%Z m0 m' -> wmono asegs m0 m' -> shz m' N 64) ->
    (forall m', munch [(bv_unsigned sp - 160, bv_unsigned sp); (X, X + 504); (DG, DG + 8)]%Z m0 m' -> wmono asegs m0 m' -> shz m' DG 8) ->
    (forall m', munch [(bv_unsigned sp - 160, bv_unsigned sp); (X, X + 504); (DG, DG + 8)]%Z m0 m' -> wmono asegs m0 m' -> shz m' 0x2e600 160) ->
    forall (Q : machine_state -> Prop),
    (forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (m' : mem) xbs' len' dg',
       munch [(bv_unsigned sp - 160, bv_unsigned sp); (X, X + 504); (DG, DG + 8)]%Z m0 m' -> wmono asegs m0 m' -> mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) ->
       u8arr asegs m' X xbs' -> length xbs' = 496%nat -> rw_cells asegs m' (X + 496) [C2 (Z_to_bv 64 len')] -> (0 <= len' <= 62)%Z ->
       bytes_at asegs m' (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
       rw_cells asegs m' DG [C8 (Z_to_bv 64 dg')] -> (0 <= dg' <= 770)%Z ->
       rw_cells asegs m' (N + 32) [C8 (Z_to_bv 64 IP); C8 (Z_to_bv 64 IL); C8 (Z_to_bv 64 FPT); C8 (Z_to_bv 64 FL)] ->
       bytes_at asegs m' A txt ->
       evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' (seg_rom asegs))) ->
    forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 xbs jd len,
    mem_inv asegs m0 -> stk asegs m0 lo (bv_unsigned sp) -> client_consts m0 ->
    u8arr asegs m0 X xbs -> length xbs = 496%nat -> rw_cells asegs m0 (X + 496) [C2 (Z_to_bv 64 len)] -> (0 <= len <= 62)%Z ->
    bytes_at asegs m0 (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    rw_cells asegs m0 DG [CB 8 jd] ->
    rw_cells asegs m0 (N + 32) [C8 (Z_to_bv 64 IP); C8 (Z_to_bv 64 IL); C8 (Z_to_bv 64 FPT); C8 (Z_to_bv 64 FL)] ->
    bytes_at asegs m0 A txt -> (exists tb, bytes_at asegs m0 0x2e600 tb /\ length tb = 160%nat) ->
    evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 N) (Z_to_bv 64 769) (Z_to_bv 64 DG) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xe65c8) fc None m0 (seg_rom asegs)).

Theorem pma_ok : pma_stmt.
Proof.
  unfold pma_stmt. intros until Q. intros HK. intros.
  eapply (pm_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X N DG A IP IL FPT FL lo txt m0); try eassumption.
  eapply (pm_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X N DG A IP IL FPT FL lo txt m0); try eassumption.
Qed.
