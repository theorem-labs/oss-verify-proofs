(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec Cells CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AsKit ECH_AC6_acc ECH_AC7_kit ECH_AC9_kit ECH_AC9_rdseg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import N6_tac.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require ECH_C9_ctrl.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ARD_RA_SM : Z := 0x51ca80.      (* [comment removed for export] *)
Definition ARD_RA_GD : Z := 0x51cb1c.      (* [comment removed for export] *)
Definition ARD_RA_NX : Z := 0x51cb2c.      (* [comment removed for export] *)
Definition ARD_RA_CF : Z := 0x51cb50.      (* [comment removed for export] *)
Definition ARD_RA_DI1 : Z := 0x51cc00.     (* [comment removed for export] *)
Definition ARD_RA_CNR : Z := 0x51d4ec.     (* [comment removed for export] *)
Definition AMAGIC : Z := 0x41b58ab3.       (* [comment removed for export] *)
Definition ARETIRED : Z := 0x45e0360e.     (* [comment removed for export] *)
Definition ADESCR_b64_read : Z := 0x3ae46. (* [comment removed for export] *)

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac killb K :=
    first [ apply Bool.andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia
          | apply Bool.andb_true_iff in K; destruct K as [K K']; apply Z.ltb_lt in K; apply Z.ltb_lt in K'; exfalso; revert K K'; rewrite ?unsigned_lit, ?signed_lit by lia; lia
          | exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia ].

  (* [comment removed for export] *)
  Lemma apro_b :
    forall (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (sp0 fb ff fp a out outl lo : Z) (jfr j1 j2 : list byte) (z0 z1 z2 z3 z4 z5 z6 z7 : byte),
      0 < out < 2^64 -> 0 < ff -> ff + 64 <= aceil -> (ff + 64 <= ALOWSH_LO \/ AHI_LO <= ff) ->
      ASHADOW_BASE <= Z.shiftr ff 3 + ASHB -> Z.shiftr ff 3 + ASHB + 8 <= AHI_LO ->
      rw_cells asegs m fb [CB 280 jfr] ->
      rw_cells asegs m ff [CB 24 j1; C8 (Z_to_bv 64 fb); CB 24 j2; C8 (Z_to_bv 64 fp)] ->
      rw_cells asegs m (Z.shiftr ff 3 + ASHB) [C1 z0; C1 z1; C1 z2; C1 z3; C1 z4; C1 z5; C1 z6; C1 z7] ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_GD) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb)
                       (Z_to_bv 64 a) (Z_to_bv 64 ADESCR_b64_read) (Z_to_bv 64 P_b64_read) (Z_to_bv 64 (Z.shiftr ff 3)) (Z_to_bv 64 (-13)) a5 a6 a7
                       (Z_to_bv 64 ASHB) s3 (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_get_data) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280); (ff, ff + 24); (Z.shiftr ff 3 + ASHB, Z.shiftr ff 3 + ASHB + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 fb [CB 272 (firstn 272 jfr); C8 (Z_to_bv 64 ff)]
          /\ rw_cells asegs m1 ff [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 ADESCR_b64_read); C8 (Z_to_bv 64 P_b64_read); C8 (Z_to_bv 64 fb); CB 24 j2; C8 (Z_to_bv 64 fp)]
          /\ rw_cells asegs m1 (Z.shiftr ff 3 + ASHB) b64rd_shpat)
        (MS (mkR (Z_to_bv 64 ARD_RA_SM) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 ff) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) s3 s4 s5 s6 (Z_to_bv 64 a) (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_SM) fc None m (seg_rom asegs)).
  Proof.
    intros until z7. intros OUT FF0 FFC NSff SH1 SH2 FRM FFR SHC ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_SM, ARD_RA_GD, P_BIO_get_data, P_b64_read, AMAGIC, ADESCR_b64_read, ASHB, ALOWSH_LO, AHI_LO in *.
    rewrite ASHADOW_BASE_val in SH1.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280); (ff, ff + 24); (Z.shiftr ff 3 + 2147450880, Z.shiftr ff 3 + 2147450880 + 8)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (rw_cells_bound _ _ _ _ FRM) as FRB. cbn [cells_size csize Nat.add] in FRB.
    (* [comment removed for export] *)
    assert (DJ1 : chunk_disj ff 64 fb 280) by (unfold chunk_disj; lia).
    assert (DJ2 : chunk_disj (Z.shiftr ff 3 + 2147450880) 8 fb 280) by (unfold chunk_disj; lia).
    assert (DJ3 : chunk_disj fb 280 ff 64) by (unfold chunk_disj; lia).
    assert (DJ4 : chunk_disj (Z.shiftr ff 3 + 2147450880) 8 ff 64) by (unfold chunk_disj; lia).
    assert (DJ5 : chunk_disj fb 280 (Z.shiftr ff 3 + 2147450880) 8) by (unfold chunk_disj; lia).
    assert (DJ6 : chunk_disj ff 64 (Z.shiftr ff 3 + 2147450880) 8) by (unfold chunk_disj; lia).
    (* [comment removed for export] *)
    step. step. step. step. if_cases K0; zify_cond K0; [| kill K0]. clear K0.
    (* [comment removed for export] *)
    st1.
    (* [comment removed for export] *)
    step. step. step. zstep. step. step. step. step.
    (* [comment removed for export] *)
    st1. st1. st1.
    (* [comment removed for export] *)
    step. zstep. st1. st1. st1. st1. step. st1. st1. st1. st1.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
    step. step. step.
    finish.
    all: try (replace (Z.shiftr ff 3 + 2147450888) with (Z.shiftr ff 3 + 2147450880 + 8) by lia; exact MU).
    all: match goal with |- ?G => idtac "PB-LEFT:" G end.
  Qed.
  (* [comment removed for export] *)
  Lemma apro_c :
    forall (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (sp0 fb ff a out outl ctx : Z),
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_NX) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb)
                       (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ASHB) (Z_to_bv 64 ctx) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_next) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ARD_RA_GD) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 ctx) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) s3 (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_GD) fc None m (seg_rom asegs)).
  Proof.
    intros. unfold ARD_RA_GD, ARD_RA_NX, P_BIO_next, ASHB in *.
    step. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma apro_d :
    forall (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (sp0 fb ff a out outl ctx mb lo : Z) (jfr : list byte),
      0 < ctx < 2^64 -> 0 < mb < 2^64 ->
      rw_cells asegs m fb [CB 272 jfr; C8 (Z_to_bv 64 ff)] ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_CF) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb)
                       (Z_to_bv 64 a) (Z_to_bv 64 15) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ASHB) (Z_to_bv 64 ctx) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) (Z_to_bv 64 0) (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_clear_flags) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 fb [CB 248 (firstn 248 jfr); C8 (Z_to_bv 64 ctx); CB 16 (skipn 256 jfr); C8 (Z_to_bv 64 ff)])
        (MS (mkR (Z_to_bv 64 ARD_RA_NX) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) (Z_to_bv 64 ctx) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) s9 (Z_to_bv 64 out) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_NX) fc None m (seg_rom asegs)).
  Proof.
    intros until jfr. intros CTX MB FRM ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_NX, ARD_RA_CF, P_BIO_clear_flags, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (rw_cells_bound _ _ _ _ FRM) as FRB. cbn [cells_size csize Nat.add] in FRB.
    (* [comment removed for export] *)
    step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
    (* [comment removed for export] *)
    step. step. st1. step. step.
    finish.
    all: match goal with |- ?G => idtac "PD-LEFT:" G end.
  Qed.
  Local Ltac reacc ACC MU NSW AC2 :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AC2 : accessible mx _ 2584) by (eapply accessible_across2; [exact ACC| exact MU| exact NSW]) end.
  Local Ltac reacc128 ACC MU NSW AC2 :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AC2 : accessible mx _ 128) by (eapply accessible_across2; [exact ACC| exact MU| exact NSW]) end.

  (* [comment removed for export] *)
  Lemma apro_e :
    forall (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (sp0 fb ff a out outl ctx mb enc lo : Z) (j248 j16 bjunk : list byte),
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE -> accessible m ctx B64CTX_SIZE -> 0 <= enc < 2^64 ->
      rw_cells asegs m fb [CB 248 j248; C8 (Z_to_bv 64 ctx); CB 16 j16; C8 (Z_to_bv 64 ff)] ->
      rw_cells asegs m ctx (b64ctx_fresh_cells enc bjunk) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 (a1' a2' a3' a5' : word) (j96 j16a j48 j64 : list byte),
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_DI1) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb)
                       (Z_to_bv 64 enc) a1' a2' a3' (Z_to_bv 64 ctx) a5' a6 a7
                       (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr ctx 3)) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) (Z_to_bv 64 0) (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_EVP_DecodeInit) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280); (ctx, ctx + 20)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 fb [CB 96 j96; C8 (Z_to_bv 64 (ctx + 4)); CB 16 j16a; C8 (Z_to_bv 64 (ctx + 8)); CB 48 j48; C8 (Z_to_bv 64 (ctx + 32)); CB 64 j64;
                                 C8 (Z_to_bv 64 ctx); CB 16 j16; C8 (Z_to_bv 64 ff)]
          /\ rw_cells asegs m1 ctx [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 2); C4 (wz 1); C4 (wz 1); C4 (wz 0);
                                  C8 (wz enc); CB 2528 bjunk; C8 (wz 0); C8 (wz 0)])
        (MS (mkR (Z_to_bv 64 ARD_RA_CF) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) (Z_to_bv 64 ctx) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) (Z_to_bv 64 0) (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_CF) fc None m (seg_rom asegs)).
  Proof.
    intros until bjunk. intros CP CAL CL CAP ACC ENC FRM CX ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_CF, ARD_RA_DI1, P_EVP_DecodeInit, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280); (ctx, ctx + 20)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    pose proof (rw_cells_bound _ _ _ _ FRM) as FRB. cbn [cells_size csize Nat.add] in FRB.
    pose proof (rw_cells_bound _ _ _ _ CX) as CXB. cbn [cells_size csize Nat.add] in CXB.
    unfold b64ctx_fresh_cells, wz in CX.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280); (ctx, ctx + 20)]) by nsw_tac.
    assert (DJ1 : chunk_disj ctx 2584 fb 280) by (unfold chunk_disj; lia).
    assert (DJ2 : chunk_disj fb 280 ctx 2584) by (unfold chunk_disj; lia).
    (* [comment removed for export] *)
    st1. zstep. zstep. zstep.
    reacc ACC MU NSW0 ACC1. ck8_check ACC1 (ctx + 16).
    (* [comment removed for export] *)
    st1. rewrite ?(sx32_lit 0) by lia. step. zstep. zstep. st1. zstep. st1. zstep. st1.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    (* [comment removed for export] *)
    reacc ACC MU NSW0 ACC2. ck8_check ACC2 (ctx + 16). clear ACC1.
    step. st1.
    (* [comment removed for export] *)
    zstep. reacc ACC MU NSW0 ACC3. ck8_check ACC3 ctx. clear ACC2. st1.
    (* [comment removed for export] *)
    st1. zstep. zstep. reacc ACC MU NSW0 ACC4. ck8_check ACC4 (ctx + 4). clear ACC3. st1.
    (* [comment removed for export] *)
    st1. zstep. zstep. reacc ACC MU NSW0 ACC5. ck8_check ACC5 (ctx + 8). clear ACC4. st1.
    (* [comment removed for export] *)
    st1. zstep. zstep. reacc ACC MU NSW0 ACC6. ck8_check ACC6 (ctx + 32). clear ACC5. st1. step. step.
    finish.
    all: try eassumption.
    all: match goal with |- ?G => idtac "PE-LEFT:" G end.
  Qed.
  (* [comment removed for export] *)
  Definition aheadslots (ctx ff mb a : Z) (j0 j104 j128 j152 j216 j240 j256 : list byte) : list cell :=
    [CB 24 j0; C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)); C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 0);
     C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (Z.shiftr ctx 3 + ASHB)); C8 (Z_to_bv 64 (ctx + 4)); CB 8 j104; C8 (Z_to_bv 64 (ctx + 1542));
     C8 (Z_to_bv 64 (ctx + 8)); CB 16 j128; C8 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)); CB 8 j152; C8 (Z_to_bv 64 (ctx + 40));
     C8 (Z_to_bv 64 (Z.shiftr (ctx + 32) 3 + ASHB)); C8 (Z_to_bv 64 (ctx + 32)); C8 (Z_to_bv 64 (Z.shiftr (ctx + 24) 3 + ASHB)); C8 (Z_to_bv 64 (ctx + 24));
     C8 (Z_to_bv 64 (ctx + 12)); C8 (Z_to_bv 64 (ctx + 1542)); CB 16 j216; C8 (Z_to_bv 64 (ff + 32)); CB 8 j240; C8 (Z_to_bv 64 ctx); CB 16 j256; C8 (Z_to_bv 64 ff)].

  (* [comment removed for export] *)
  Lemma apro_f :
    forall (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (sp0 fb ff a out outl ctx mb enc lo : Z) (j96 j16a j48 j64 j16 bjunk : list byte),
      0 < outl < 2^31 -> 0 <= ff -> ff + 64 <= aceil ->
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE -> accessible m ctx B64CTX_SIZE -> 0 <= enc < 2^64 ->
      rw_cells asegs m fb [CB 96 j96; C8 (Z_to_bv 64 (ctx + 4)); CB 16 j16a; C8 (Z_to_bv 64 (ctx + 8)); CB 48 j48; C8 (Z_to_bv 64 (ctx + 32)); CB 64 j64;
                           C8 (Z_to_bv 64 ctx); CB 16 j16; C8 (Z_to_bv 64 ff)] ->
      rw_cells asegs m ctx [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 2); C4 (wz 1); C4 (wz 1); C4 (wz 0); C8 (wz enc); CB 2528 bjunk; C8 (wz 0); C8 (wz 0)] ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 (j0 j104 j128 j152 j216 j240 : list byte),
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_DI1) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb)
                       (Z_to_bv 64 3) (Z_to_bv 64 (Z.shiftr (ctx + 8) 3)) (Z_to_bv 64 3) (Z_to_bv 64 (Z.shiftr (ctx + 32) 3 + ASHB)) (Z_to_bv 64 ctx) a5 a6 a7
                       (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr ctx 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a)
                       (Z_to_bv 64 outl) (Z_to_bv 64 0) (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
                   F (Z_to_bv 64 ARD_HEAD) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 fb (aheadslots ctx ff mb a j0 j104 j128 j152 j216 j240 j16)
          /\ rw_cells asegs m1 ctx [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 2); C4 (wz 1); C4 (wz 1); C4 (wz 0); C8 (wz enc); CB 2528 bjunk; C8 (wz 0); C8 (wz 0)])
        (MS (mkR (Z_to_bv 64 ARD_RA_DI1) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr ctx 3)) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (Z_to_bv 64 a)
                 (Z_to_bv 64 outl) (Z_to_bv 64 0) (Z_to_bv 64 out) (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_DI1) fc None m (seg_rom asegs)).
  Proof.
    intros until bjunk. intros OUTL FF0 FFC CP CAL CL CAP ACC ENC FRM CX ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_DI1, ARD_HEAD, B64CTX_SIZE, ASHB, aheadslots in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    pose proof (rw_cells_bound _ _ _ _ FRM) as FRB. cbn [cells_size csize Nat.add] in FRB.
    unfold wz in CX.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280)]) by nsw_tac.
    assert (DJ1 : chunk_disj ctx 2584 fb 280) by (unfold chunk_disj; lia).
    assert (M8a : (ctx + 24) mod 8 = 0) by (clear - CAL; Z.div_mod_to_equations; lia).
    assert (M8b : (ctx + 8) mod 8 = 0) by (clear - CAL; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    st1. zstep. st1.
    reacc ACC MU NSW0 ACC1. ck8_check ACC1 ctx.
    (* [comment removed for export] *)
    st1. rewrite ?(sx32_lit 0) by lia. step. if_cases K0; zify_cond K0; [| killb K0]. try clear K0. step.
    (* [comment removed for export] *)
    zstep. st1. zstep. zstep. st1.
    reacc ACC MU NSW0 ACC2. ck8_check ACC2 (ctx + 24). clear ACC1.
    (* [comment removed for export] *)
    st1. st1. st1.
    (* [comment removed for export] *)
    st1. rewrite ?(sx32_lit 1) by lia. zstep. zstep. st1.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [killb K1|]. try clear K1.
    (* [comment removed for export] *)
    zstep. st1. zstep. st1. zstep. zstep. st1. zstep. st1. zstep. st1.
    (* [comment removed for export] *)
    st1. zstep.
    replace (Z.land (ctx + 24) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia).
    st1. zstep. zstep.
    replace (Z.land (ctx + 8) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia).
    st1. zstep. zstep. st1.
    (* [comment removed for export] *)
    zstep. zstep. st1. zstep. st1. st1. st1. st1.
    finish.
    all: try eassumption.
    all: try (match goal with H : rw_cells _ _ ?A ?cs |- _ => idtac "HYP:" A cs; fail end).
    all: match goal with |- ?G => idtac "PF-LEFT:" G end.
  Qed.
  (* [comment removed for export] *)
  Definition b64rd_f5 : list cell :=
    [C1 (b8 245); C1 (b8 245); C1 (b8 245); C1 (b8 245); C1 (b8 245); C1 (b8 245); C1 (b8 245); C1 (b8 245)].
  Lemma aexit :
    forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s8 s10 t3 t4 t5 t6 : word) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word) (d1 d2 d3 : word) (fl5 : byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx ff fp mb a vret rcf lo : Z) (B : biorep) (M : membio),
      0 <= vret < 2^31 -> (rcf = 0 \/ rcf = -1) -> 0 < ff -> ff + 64 <= aceil -> (ff + 64 <= ALOWSH_LO \/ AHI_LO <= ff) ->
      ASHADOW_BASE <= Z.shiftr ff 3 + ASHB -> Z.shiftr ff 3 + ASHB + 8 <= AHI_LO -> 0 <= fp -> fp + 1 <= ff -> AIMG_TOP <= fp -> (fp + 1 <= ALOWSH_LO \/ AHI_LO <= fp) ->
      0 < a -> a + BIO_SIZE <= lo -> aapp a BIO_SIZE -> accessible m a BIO_SIZE -> bio_ok B -> bio_next B = mb ->
      0 < mb -> mb + BIO_SIZE <= lo -> aapp mb BIO_SIZE -> accessible m mb BIO_SIZE -> 0 <= mb_flags M < 2^31 ->
      (a + BIO_SIZE <= mb \/ mb + BIO_SIZE <= a) -> ACONST m ->
      (a + BIO_SIZE <= fp \/ ff + 64 <= a) -> (mb + BIO_SIZE <= fp \/ ff + 64 <= mb) ->   (* [comment removed for export] *)
      rw_cells asegs m (fb + 24) (ardslots ctx ff ff vret mb a (ff + 32) w104 w128 j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m (sp0 + -104) (ardsaves q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra) ->
      rw_cells asegs m a (bio_cells B) -> rw_cells asegs m mb (bio_cells (membio_bio M)) ->
      rw_cells asegs m ff [C8 d1; C8 d2; C8 d3] -> rw_cells asegs m (ff + 56) [C8 (Z_to_bv 64 fp)] ->
      rw_cells asegs m (Z.shiftr ff 3 + ASHB) b64rd_shpat -> rw_cells asegs m fp [C1 fl5] ->
      stk asegs m lo fb -> aceil <= lo -> lo + 16 <= fb -> 0 <= fb -> fb + 280 <= sp0 - 104 -> sp0 < 2^64 -> mem_inv asegs m -> bv_unsigned qra mod 2 = 0 ->
      evt asegs (fun ms' => exists m1 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          ms' = MS (mkR qra (Z_to_bv 64 sp0) gp tp t0' t1' t2' q0 q1 (Z_to_bv 64 (if vret =? 0 then rcf else vret)) a1' a2' a3' a4' a5' a6' a7'
                       q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 t3' t4' t5' t6')
                   F (ret_pc qra) fc None m1 (seg_rom asegs)
          /\ munch [(fb - 16, fb); (a + 48, a + 56); (Z.shiftr ff 3 + ASHB, Z.shiftr ff 3 + ASHB + 8); (ff, ff + 8); (fp, fp + 1)] m m1
          /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 24) (ardslots ctx ff ff vret mb a (ff + 32) w104 w128 j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 (sp0 + -104) (ardsaves q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
          /\ rw_cells asegs m1 a (bio_cells (mkBIO (bio_method B) (bio_init B) (bio_shutdown B) (Z.lor (bio_flags B) ((mb_flags M) mod 16)) 0 (bio_numf B)
                                              (bio_ptr B) (bio_next B) (bio_prev B) (bio_refs B) (bio_nread B) (bio_nwrite B)))
          /\ rw_cells asegs m1 mb (bio_cells (membio_bio M))
          /\ rw_cells asegs m1 ff [C8 (Z_to_bv 64 ARETIRED); C8 d2; C8 d3] /\ rw_cells asegs m1 (ff + 56) [C8 (Z_to_bv 64 fp)]
          /\ rw_cells asegs m1 (Z.shiftr ff 3 + ASHB) b64rd_f5 /\ rw_cells asegs m1 fp [C1 (b8 0)])
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) s3 s4 (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 a) s8 (Z_to_bv 64 rcf) s10 (Z_to_bv 64 mb) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_EXIT) fc None m (seg_rom asegs)).
  Proof.
    intros until M. intros VR RC FF0 FFC NSff SH1 SH2 FP0 FP1 FP2 NSfp AP ALO AAP ACCa BOK NXT MP MLO MAP ACCm MFL AM AC AFF MFF SL SV AH MH FH FT SHC FPC ST CEIL LO FB0 FBT SPT MI RAE. acb.
    unfold b64rd_shpat, b64rd_f5 in *. unfold ARD_EXIT, ASHB, ALOWSH_LO, AHI_LO, AIMG_TOP, BIO_SIZE, ARETIRED in *.
    rewrite ASHADOW_BASE_val in SH1.
    pose proof (ACONST_shbase _ AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (aapp_not_shadowland _ _ AAP) as NSa. pose proof (aapp_not_shadowland _ _ MAP) as NSm.
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (_ & _ & AHIa & _). pose proof (aapp_bounds _ _ MAP ltac:(lia)) as (_ & _ & AHIm & _).
    unfold ALOWSH_LO, AHI_LO, AAPP_HI in NSa, NSm, AHIa, AHIm.
    pose proof (aword_range qra) as RAR.
    unfold ardslots, ASHB in SL. unfold ardsaves in SV. unfold bio_cells, membio_bio, wz in AH, MH |- *.
    cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in AH, MH |- *.
    rewrite NXT in AH.
    pose proof BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    (* [comment removed for export] *)
    pose proof (munch_refl [(fb - 16, fb); (a + 48, a + 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb - 16, fb); (a + 48, a + 56)]) by nsw_tac.
    assert (DJ1 : chunk_disj a 128 (fb - 16) 16) by (unfold chunk_disj; lia).
    assert (DJ2 : chunk_disj mb 128 (fb - 16) 16) by (unfold chunk_disj; lia).
    assert (DJ3 : chunk_disj (fb - 16) 16 a 128) by (unfold chunk_disj; lia).
    assert (DJ4 : chunk_disj mb 128 a 128) by (unfold chunk_disj; lia).
    assert (DJ5 : chunk_disj (fb + 24) 256 a 128) by (unfold chunk_disj; lia).
    assert (DJ6 : chunk_disj (sp0 + -104) 104 a 128) by (unfold chunk_disj; lia).
    assert (DJ7 : chunk_disj ff 24 a 128) by (unfold chunk_disj; lia).
    assert (DJ8 : chunk_disj (ff + 56) 8 a 128) by (unfold chunk_disj; lia).
    assert (DJ9 : chunk_disj (Z.shiftr ff 3 + 2147450880) 8 a 128) by (unfold chunk_disj; lia).
    assert (DJ10 : chunk_disj fp 1 a 128) by (unfold chunk_disj; lia).
    (* [comment removed for export] *)
    step. step. step.
    carve_frame 16%nat ST. step. st1. st1. step.
    (* [comment removed for export] *)
    step. st1. st1.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    reacc128 ACCa MU NSW0 ACa1. ck8_check ACa1 (a + 72).
    (* [comment removed for export] *)
    st1. zstep. zstep. zstep.
    reacc128 ACCm MU NSW0 ACm1. ck8_check ACm1 (mb + 48).
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_load ACa1 (a + 48). st1. rewrite ?zx32_lit by lia. step. if_false_by (ck1_bnez_false 0 eq_refl).
    (* [comment removed for export] *)
    st1. rewrite ?(sx32_lit (bio_flags B)) by lia.
    zstep. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16.
    assert (M16 : 0 <= mb_flags M mod 16 < 16) by (apply Z.mod_pos_bound; lia).
    zstep. zstep. rewrite ?unsigned_lit by lia. rewrite ?(Z.mod_small (mb_flags M) (2^32)) by lia.
    zstep. st1. zstep.
    (* [comment removed for export] *)
    clear ACa1 ACm1. reacc128 ACCm MU NSW0 ACm2. ck8_check ACm2 (mb + 52).
    (* [comment removed for export] *)
    zstep. zstep. zstep. reacc128 ACCa MU NSW0 ACa2. ck8_load ACa2 (a + 52). st1. rewrite ?(sx32_lit 0) by lia. step. if_false_by (ck1_bnez_false 0 eq_refl).
    st1.
    (* [comment removed for export] *)
    st1. st1. step. step. unfold ARD_RA_CNR.
    replace (ret_pc (Z_to_bv 64 5362924)) with (Z_to_bv 64 5362924) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    release_frame FR ST fb.
    clear ACa2 ACm2.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (MU' : munch [(fb - 16, fb); (a + 48, a + 56); (Z.shiftr ff 3 + 2147450880, Z.shiftr ff 3 + 2147450880 + 8); (ff, ff + 8); (fp, fp + 1)] m mx)
        by (eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside fst snd] in Hx |- *; tauto) end.
    clear MU. rename MU' into MU.
    assert (DK1 : chunk_disj (fb + 24) 256 (Z.shiftr ff 3 + 2147450880) 8) by (unfold chunk_disj; lia).
    assert (DK2 : chunk_disj (sp0 + -104) 104 (Z.shiftr ff 3 + 2147450880) 8) by (unfold chunk_disj; lia).
    assert (DK3 : chunk_disj a 128 (Z.shiftr ff 3 + 2147450880) 8) by (unfold chunk_disj; lia).
    assert (DK4 : chunk_disj mb 128 (Z.shiftr ff 3 + 2147450880) 8) by (unfold chunk_disj; lia).
    assert (DK5 : chunk_disj ff 24 (Z.shiftr ff 3 + 2147450880) 8) by (unfold chunk_disj; lia).
    assert (DK6 : chunk_disj (ff + 56) 8 (Z.shiftr ff 3 + 2147450880) 8) by (unfold chunk_disj; lia).
    assert (DK7 : chunk_disj fp 1 (Z.shiftr ff 3 + 2147450880) 8) by (unfold chunk_disj; lia).
    assert (DL1 : chunk_disj (fb + 24) 256 ff 24) by (unfold chunk_disj; lia).
    assert (DL2 : chunk_disj (sp0 + -104) 104 ff 24) by (unfold chunk_disj; lia).
    assert (DL3 : chunk_disj a 128 ff 24) by (unfold chunk_disj; lia).
    assert (DL4 : chunk_disj mb 128 ff 24) by (unfold chunk_disj; lia).
    assert (DL5 : chunk_disj (ff + 56) 8 ff 24) by (unfold chunk_disj; lia).
    assert (DL6 : chunk_disj fp 1 ff 24) by (unfold chunk_disj; lia).
    assert (DL7 : chunk_disj (Z.shiftr ff 3 + 2147450880) 8 ff 24) by (unfold chunk_disj; lia).
    assert (DM1 : chunk_disj (fb + 24) 256 fp 1) by (unfold chunk_disj; lia).
    assert (DM2 : chunk_disj (sp0 + -104) 104 fp 1) by (unfold chunk_disj; lia).
    assert (DM3 : chunk_disj a 128 fp 1) by (unfold chunk_disj; lia).
    assert (DM4 : chunk_disj mb 128 fp 1) by (unfold chunk_disj; lia).
    assert (DM5 : chunk_disj (ff + 56) 8 fp 1) by (unfold chunk_disj; lia).
    assert (DM6 : chunk_disj ff 24 fp 1) by (unfold chunk_disj; lia).
    assert (DM7 : chunk_disj (Z.shiftr ff 3 + 2147450880) 8 fp 1) by (unfold chunk_disj; lia).
    (* [comment removed for export] *)
    st1.
    evar (TGT : machine_state).
    eapply evt_cut with (P := fun msx => msx = TGT).
    { step. if_cases K; zify_cond K; rewrite ?unsigned_lit, ?signed_lit in K by lia.
      - replace (vret =? 0) with true by (symmetry; apply Z.eqb_eq; lia). apply evt_done. subst TGT.
        replace (Z_to_bv 64 rcf) with (Z_to_bv 64 (if vret =? 0 then rcf else vret)) by (replace (vret =? 0) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
        reflexivity.
      - step. apply evt_done. subst TGT.
        replace (Z_to_bv 64 vret) with (Z_to_bv 64 (if vret =? 0 then rcf else vret)) at 2 by (replace (vret =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        reflexivity. }
    subst TGT. cbv beta. intros ms' ->.
    (* [comment removed for export] *)
    st1. st1. st1. step. st1. step. step. st1. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
    (* [comment removed for export] *)
    step. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. step.
    (* [comment removed for export] *)
    step. zstep. do 13 st1. zstep. step.
    finish.
    all: try eassumption.
    all: try (replace (Z.shiftr ff 3 + 2147450888) with (Z.shiftr ff 3 + 2147450880 + 8) by lia; exact MU).
    all: try (rewrite NXT; eassumption).
    all: match goal with |- ?G => idtac "PX-LEFT:" G end.
  Qed.
End S.
