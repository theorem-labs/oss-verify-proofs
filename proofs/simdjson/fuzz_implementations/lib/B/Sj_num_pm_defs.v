(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU SjNumN.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Definition PMB_POW10 : Z := 0x2f920.
Definition PMB_GTOP : Z := 0x6e0000.

Definition pmb_pow10_tbl : list byte :=
  Eval vm_compute in match image_bytes bsegs PMB_POW10 160 with Some bs => bs | None => [] end.
Lemma pmb_pow10_len : length pmb_pow10_tbl = 160%nat.
Proof. reflexivity. Qed.
Lemma pmb_pow10_at : forall m, mem_inv bsegs m -> bytes_at bsegs m PMB_POW10 pmb_pow10_tbl.
Proof.
  intros m MI.
  assert (RO : ro_cells bsegs m PMB_POW10 [CB (length pmb_pow10_tbl) pmb_pow10_tbl]).
  { apply (ro_cells_image bsegs m PMB_POW10 pmb_pow10_tbl MI); [vm_compute; reflexivity | unfold PMB_POW10; lia | unfold PMB_POW10; cbn; lia]. }
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma pmb_pow10_nz : forall cn, (0 <= cn <= 19)%Z -> (0 < bv_unsigned (limbz pmb_pow10_tbl (8 * cn)))%Z.
Proof.
  intros cn H.
  assert (C : (cn = 0 \/ cn = 1 \/ cn = 2 \/ cn = 3 \/ cn = 4 \/ cn = 5 \/ cn = 6 \/ cn = 7 \/ cn = 8 \/ cn = 9 \/ cn = 10 \/ cn = 11 \/ cn = 12 \/
               cn = 13 \/ cn = 14 \/ cn = 15 \/ cn = 16 \/ cn = 17 \/ cn = 18 \/ cn = 19)%Z) by lia.
  repeat (destruct C as [->|C]; [vm_compute; reflexivity|]). subst cn. vm_compute. reflexivity.
Qed.

Record pmbenv : Type := mkPmbEnv {
  p_ra : word; p_sp : word; p_gp : word; p_tp : word;
  p_s0 : word; p_s1 : word; p_s2 : word; p_s3 : word; p_s4 : word; p_s5 : word;
  p_s6 : word; p_s7 : word; p_s8 : word; p_s9 : word; p_s10 : word; p_s11 : word;
  p_F : bvmap 5 word; p_fc : bv 32;
  p_X : Z; p_N : Z; p_DG : Z; p_A : Z; p_IP : Z; p_IL : Z; p_FPT : Z; p_FL : Z; p_lo : Z; p_txt : list byte; p_m0 : mem }.

Notation p_SP E := (bv_unsigned (p_sp E)).
Notation p_TL E := (Z.of_nat (length (p_txt E))).

Record pmb_ok (E : pmbenv) : Prop := mkPmbOk {
  po_room : (p_lo E + PMB_STACK <= p_SP E)%Z;
  po_x8 : (p_X E mod 8 = 0)%Z;
  po_xr : (PMB_GTOP <= p_X E /\ p_X E + 504 <= p_lo E)%Z;
  po_xsh : (p_X E + 504 <= p_X E / 8 + 2147450880 \/ p_X E / 8 + 2147450880 + 63 <= p_X E)%Z;
  po_xs0 : (PMB_GTOP <= p_X E / 8 + 2147450880 /\ p_X E / 8 + 2147450880 + 63 <= p_lo E)%Z;
  po_nr : (p_N E mod 8 = 0 /\ p_SP E <= p_N E /\ p_N E + 64 <= p_DG E)%Z;
  po_dgr : (p_DG E mod 8 = 0 /\ p_SP E <= p_DG E /\ p_DG E + 8 <= USTACK_TOP)%Z;
  po_txr : (0 < p_A E /\ p_A E + p_TL E <= p_lo E /\ p_TL E < NUM_TXT_MAX)%Z;
  po_xa : (p_X E + 504 <= p_A E \/ p_A E + p_TL E <= p_X E)%Z;
  po_spans : pm_spans_ok (p_A E) (p_txt E) (p_IP E) (p_IL E) (p_FPT E) (p_FL E) }.

Definition pmb_W (E : pmbenv) : list (Z * Z) := [(p_SP E - PMB_STACK, p_SP E); (p_X E, p_X E + 498); (p_DG E, p_DG E + 8)]%Z.

Definition pmb_prov (E : pmbenv) : Prop :=
  (forall m', munch (pmb_W E) (p_m0 E) m' -> wmono bsegs (p_m0 E) m' -> shz m' (8 * (p_A E / 8)) (p_A E + p_TL E - 8 * (p_A E / 8)))%Z /\
  (forall m', munch (pmb_W E) (p_m0 E) m' -> wmono bsegs (p_m0 E) m' -> shz m' (p_N E) 64) /\
  (forall m', munch (pmb_W E) (p_m0 E) m' -> wmono bsegs (p_m0 E) m' -> shz m' (p_DG E) 8) /\
  (forall m', munch (pmb_W E) (p_m0 E) m' -> wmono bsegs (p_m0 E) m' -> shz m' PMB_POW10 160).

Definition pmb_post_g (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X DG lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' bs' len' dg',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - PMB_STACK, bv_unsigned sp); (X, X + 498); (DG, DG + 8)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ u8arr bsegs m' X bs' /\ length bs' = 496%nat /\ rw_cells bsegs m' (X + 496) [C2 (Z_to_bv 64 len')] /\ (0 <= len' <= 62)%Z
    /\ rw_cells bsegs m' DG [C8 (Z_to_bv 64 dg')]
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ pmb_export bs' len' dg'.
Notation pmb_post E := (pmb_post_g (p_ra E) (p_sp E) (p_gp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E)
                          (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) (p_fc E) (p_X E) (p_DG E) (p_lo E) (p_m0 E)).

Definition pmb_saved (E : pmbenv) : list cell :=
  [C8 (p_s11 E); C8 (p_s10 E); C8 (p_s9 E); C8 (p_s8 E); C8 (p_s7 E); C8 (p_s6 E); C8 (p_s5 E); C8 (p_s4 E); C8 (p_s3 E); C8 (p_s2 E); C8 (p_s1 E);
   C8 (p_s0 E); C8 (p_ra E)].
Definition pmb_spans (E : pmbenv) : list cell :=
  [C8 (Z_to_bv 64 (p_IP E)); C8 (Z_to_bv 64 (p_IL E)); C8 (Z_to_bv 64 (p_FPT E)); C8 (Z_to_bv 64 (p_FL E))].

Definition pmb_frame (E : pmbenv) (j0 : list byte) (w8 w16 w24 w32 w40 w48 w56 w64 : word) : list cell :=
  CB 8 j0 :: C8 w8 :: C8 w16 :: C8 w24 :: C8 w32 :: C8 w40 :: C8 w48 :: C8 w56 :: C8 w64 :: pmb_saved E.

Definition PMBINVg (E : pmbenv) (mm : mem) (len dg : Z) (w8 w16 w24 w32 w40 w48 w56 w64 : word) (P : Prop) : Prop :=
  (exists j0, rw_cells bsegs mm (p_SP E + -176) (pmb_frame E j0 w8 w16 w24 w32 w40 w48 w56 w64)) /\
  (exists bs, u8arr bsegs mm (p_X E) bs /\ length bs = 496%nat /\ (P -> bignorm_b bs len)) /\
  rw_cells bsegs mm (p_X E + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
  bytes_at bsegs mm (p_X E / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) /\
  rw_cells bsegs mm (p_DG E) [C8 (Z_to_bv 64 dg)] /\
  rw_cells bsegs mm (p_N E + 32) (pmb_spans E) /\
  bytes_at bsegs mm (p_A E) (p_txt E) /\
  bytes_at bsegs mm PMB_POW10 pmb_pow10_tbl /\
  mem_inv bsegs mm /\ munch (pmb_W E) (p_m0 E) mm /\ wmono bsegs (p_m0 E) mm /\ stk bsegs mm (p_lo E) (p_SP E + -176).
Notation PMBINV E mm len dg w8 w16 w24 w32 w40 w48 w56 w64 := (PMBINVg E mm len dg w8 w16 w24 w32 w40 w48 w56 w64 (dg < PMB_NORM_DG)%Z).

Ltac pm_open H :=
  let j0 := fresh "j0" in let bs := fresh "bs" in
  destruct H as ((j0 & FR) & (bs & XA & ?XL & NB) & XN & ?LEN & ZR & DG & SPANS & TXT & TBL & MI & MU & WM & ST);
  unfold pmb_frame, pmb_saved in FR; unfold pmb_spans in SPANS; unfold pmb_W, PMB_STACK in MU; unfold PMB_POW10 in TBL; unfold PMB_NORM_DG in NB;
  let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB;
  let TBLL := fresh "TBLL" in pose proof pmb_pow10_len as TBLL;
  let RL := fresh "RL" in pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.

Ltac pm_close_with nb :=
  lazymatch goal with
  | |- PMBINVg _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      split; [eexists; unfold pmb_frame, pmb_saved; eassumption|]; split; [eexists; split; [eassumption| split; [lia | unfold PMB_NORM_DG; nb]]|];
      split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|]; split; [unfold pmb_spans; eassumption|]; split; [eassumption|];
      split; [unfold PMB_POW10; eassumption|];
      split; [eassumption|]; split; [unfold pmb_W, PMB_STACK; eassumption|]; split; eassumption
  end.

Ltac pm_close := pm_close_with ltac:(first [ eassumption | intro; exfalso; lia | intro; lazymatch goal with NB : _ -> bignorm_b _ _ |- _ => apply NB; lia end ]).

Notation PMB E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
  (MS (mkR xra (Z_to_bv 64 (p_SP E + -176)) (p_gp E) (p_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) (p_F E) (Z_to_bv 64 pc) (p_fc E) None mm (seg_rom bsegs)).

Ltac pm_env OK :=
  let ROOM := fresh "ROOM" in let X8 := fresh "X8" in let XR := fresh "XR" in let XSH := fresh "XSH" in let XS0 := fresh "XS0" in
  let NR := fresh "NR" in let DGR := fresh "DGR" in let TXR := fresh "TXR" in let XAS := fresh "XAS" in let SPN := fresh "SPN" in
  destruct OK as [ROOM X8 XR XSH XS0 NR DGR TXR XAS SPN];
  unfold PMB_STACK, PMB_GTOP, NUM_TXT_MAX, USTACK_TOP, pm_spans_ok in *;
  destruct SPN as (SPN1 & SPN2 & SPN3 & SPN4);
  lazymatch goal with E : pmbenv |- _ =>
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 (p_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR end.

Ltac pm_prov PV :=
  let SHPT := fresh "SHPT" in let SHPN := fresh "SHPN" in let SHPD := fresh "SHPD" in let SHPL := fresh "SHPL" in
  pose proof PV as (SHPT & SHPN & SHPD & SHPL); unfold pmb_W, PMB_STACK, PMB_POW10 in SHPT, SHPN, SHPD, SHPL.

Section PMBDEFS.
  Variable E : pmbenv.
  Hypothesis OK : pmb_ok E.
  Hypothesis PV : pmb_prov E.
  Notation X := (p_X E).

  Lemma pm_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len dg
      w8 w16 w24 w32 w40 w48 w56 w64,
    PMBINV E mm len dg w8 w16 w24 w32 w40 w48 w56 w64 -> (0 <= dg <= 770)%Z -> (19 * len <= 2 * dg + 76)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xfa960 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until w64. intros INV HD HC. pm_open INV. pm_env OK.
    do 13 zstep. zstep. zstep.
    release_frame FR ST (p_SP E).
    apply evt_done. unfold pmb_post_g. do 15 eexists. exists mm, bs, len, dg.
    split; [cbv delta [mkR]; reflexivity|].
    unfold PMB_STACK.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact XA|]. split; [exact XL|]. split; [exact XN|]. split; [lia|].
    split; [exact DG|]. split; [exact ST|].
    unfold pmb_export, PMB_NORM_DG. split; [lia|]. split; [lia|]. exact NB.
  Qed.
End PMBDEFS.
