From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s2_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_tbl_iface2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s1_iface.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Tactic Notation "kx_runFLd" uconstr(STOPS) uconstr(FUEL) uconstr(DIRS) uconstr(KZS) uconstr(RRS) uconstr(WWS) uconstr(UWS) :=
  let S := constr:(STOPS : list Z) in let Fu := constr:(FUEL : nat) in
  let D := eval vm_compute in (DIRS : list bool) in
  let K := constr:(KZS : list kz) in let R := constr:(RRS : list (Z * Z)) in let W := constr:(WWS : list (Z * Z)) in
  let U := constr:(UWS : list (Z * Z)) in
  kx_prepFm S Fu K R W U; kx_goFL D.

Lemma z4m_shd_ap : forall E X B O k w H Lw Nw,
  KXGoM.apart Lw Nw O (H / 8 + 1) ->
  bv_unsigned (edenot E X) < H -> 0 <= O -> 0 <= H -> O + H / 8 + 1 <= 2^64 -> 0 < w < 2^64 ->
  Lw <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + w <= Lw + Nw ->
  0 <= Lw -> Lw + Nw <= 2^64 ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit w)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit w) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) O)).
Proof.
  intros E X B O k w H Lw Nw HAP HX HO HH HO2 HW HB1 HB2 HL1 HL2.
  unfold KXGoM.apart in HAP.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  change (2 ^ (3 mod 64)) with 8.
  rewrite (Z_to_bv_unsigned 64 w). unfold bv_wrap, bv_modulus. rewrite (Z.mod_small w) by lia.
  assert (HD : bv_unsigned (edenot E X) / 8 <= H / 8) by (apply Z.div_le_mono; lia).
  assert (HD0 : 0 <= bv_unsigned (edenot E X) / 8) by (apply Z.div_pos; lia).
  repeat split; lia.
Qed.

Ltac z4m_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac z4m_lin T :=
  lazymatch goal with
  | |- context [edenot ?E _] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let na := eval vm_compute in (length zv) in
        change E with (kE zv xs);
        rewrite ?(ez_ok zv (kE zv xs) (kE_atoms zv xs));
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        repeat match goal with
        | |- context [?c mod 64] => z4m_zlit c; let v := eval vm_compute in (c mod 64) in change (c mod 64) with v
        end;
        kx_tbl_idx T;
        rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64);
        rewrite ?Z.mod_small by lia;
        first [lia | Z.div_mod_to_equations; lia]
      end
  end.

Lemma z4m_ap : forall E A1 k1 w1 A2 k2 w2 L1 N1 L2 N2,
  KXGoM.apart L1 N1 L2 N2 \/ KXGoM.apart L2 N2 L1 N1 ->
  0 < w1 < 2^64 -> 0 < w2 < 2^64 ->
  L1 <= bv_unsigned (edenot E A1) + k1 -> bv_unsigned (edenot E A1) + k1 + w1 <= L1 + N1 ->
  L2 <= bv_unsigned (edenot E A2) + k2 -> bv_unsigned (edenot E A2) + k2 + w2 <= L2 + N2 ->
  0 <= L1 -> L1 + N1 <= 2^64 -> 0 <= L2 -> L2 + N2 <= 2^64 ->
  flat E (SA A1 k1) (elenZ E (ELit w1)) /\ flat E (SA A2 k2) (elenZ E (ELit w2)) /\
  (estart E (SA A1 k1) + elenZ E (ELit w1) <= estart E (SA A2 k2) \/
   estart E (SA A2 k2) + elenZ E (ELit w2) <= estart E (SA A1 k1)).
Proof.
  intros E A1 k1 w1 A2 k2 w2 L1 N1 L2 N2 HAP HW1 HW2 H1 H2 H3 H4 H5 H6 H7 H8.
  unfold KXGoM.apart in HAP. unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite (Z.mod_small w1), (Z.mod_small w2) by lia.
  repeat split; lia.
Qed.

Ltac z4m_flat T FS DS TF TD :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ ?E (ELit ?w)) /\ _ =>
      let AP := lazymatch k with Zneg _ => FS | _ => DS end in
      apply (z4m_shd_ap E X B O k w _ _ _ AP);
      [z4m_lin T | lia | lia | lia | lia | z4m_lin T | z4m_lin T | lia | lia]
  | |- flat ?E (SA ?A ?k1) (elenZ ?E (ELit ?w1)) /\ flat ?E (SA ?B ?k) (elenZ ?E (ELit ?w)) /\ _ =>
      let AP := lazymatch k with Zneg _ => TF | _ => TD end in
      apply (z4m_ap E A k1 w1 B k w _ _ _ _ (or_introl AP));
      [lia | lia | z4m_lin T | z4m_lin T | z4m_lin T | z4m_lin T | lia | lia | lia | lia]
  end.

Ltac z4m_br T :=
  lazymatch goal with
  | |- branch_taken BC_GEU _ _ = true =>
      eapply (range_branch_sound BC_GEU (2^64 - 2^47 - 5) (2^64 - 1) 0 (4 * 4096));
      [z4m_lin T | z4m_lin T | vm_compute; reflexivity]
  | |- branch_taken BC_EQ _ _ = true =>
      eapply (range_branch_sound BC_EQ 0 0 0 0); [z4m_lin T | z4m_lin T | vm_compute; reflexivity]
  end.

Ltac z4m_stok4 :=
  lazymatch goal with
  | |- store_ok ?segs ?m (adenot ?E ?a) 4 = true =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        match goal with H : rw_cells segs m ?A (BD4A ?c ?bb ?jp ?p ?s ?l) |- _ =>
          eapply (rw_cells_store_ok_at segs m A (BD4A c bb jp p s l) 8%nat (C4 bb) 4%nat _ H eq_refl eq_refl);
          rewrite adenot_wa; f_equal; change E with (kE zv xs); kx_estart_z zv
        end
      end
  end.

Section CANSEC1. Context {rc : runConstT}.

Lemma z4m_shd_dj : forall A1 N1 B1 E1 A2 N2 B2 E2 lo hi,
  KXGoM.apart A1 N1 ASHOFF (ATOP / 8 + 1) -> A1 <= B1 -> E1 <= A1 + N1 ->
  KXGoM.apart A2 N2 ASHOFF (ATOP / 8 + 1) -> A2 <= B2 -> E2 <= A2 + N2 ->
  0 <= lo -> lo < hi -> hi <= ATOP ->
  disjoint_from [(B1, E1); (B2, E2)] (shad lo) (shad (hi - 1) + 1 - shad lo).
Proof.
  intros A1 N1 B1 E1 A2 N2 B2 E2 lo hi HA1 HB1 HE1 HA2 HB2 HE2 HL HLH HH.
  unfold KXGoM.apart, shad in *. cbn [disjoint_from].
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (D1 : lo / 8 <= (hi - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : (hi - 1) / 8 <= ATOP / 8) by (apply Z.div_le_mono; lia).
  assert (D0 : 0 <= lo / 8) by (apply Z.div_pos; lia).
  split; [| split; [| exact I]]; lia.
Qed.

End CANSEC1.

Lemma z4m_ms_eq : forall r r' F pc fc rv m rom, r = r' -> MS r F pc fc rv m rom = MS r' F pc fc rv m rom.
Proof. intros r r' F pc fc rv m rom H. subst r'. reflexivity. Qed.

Ltac z4m_req zv na :=
  first [ reflexivity
        | cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
          first [ apply Z_to_bv_bv_unsigned | f_equal; lia ] ].

Ltac z4m_regs :=
  lazymatch goal with
  | |- MS (kx_regs ?E ?sr) _ _ _ _ _ _ = _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let na := eval vm_compute in (length zv) in
        apply z4m_ms_eq;
        rewrite (kx_regs_ez zv E (kE_atoms zv xs) sr); cbv [kx_regs_z]; cbn [nth];
        f_equal; z4m_req zv na
      end
  end.

Ltac z4m_rng :=
  lazymatch goal with
  | |- context [ez ?zv ?E _] =>
      let na := eval vm_compute in (length zv) in
      cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
      rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64);
      repeat match goal with
      | |- context [bv_unsigned (ev E ?j)] =>
          lazymatch goal with
          | _ : _ <= bv_unsigned (ev E j) <= _ |- _ => fail
          | _ => let H := fresh "RG" in kx_range (EVar j) H
          end
      end;
      rewrite ?Z.mod_small by lia; lia
  end.

Ltac z4m_frame H CL :=
  lazymatch goal with
  | KXLF : log_flat ?E ?log, HK : know_ok ?segs ?E ?m ?kn |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      let na := eval vm_compute in (length zv) in
      lazymatch type of H with
      | bytes_at _ m ?A ?bs =>
          apply (kx_bytes_at_log segs E m log A bs) in H;
          [ | exact KXLF
            | change E with (kE zv xs); apply log_apart_ez_ok; cbn [log_apart_ez]; cbv [ez a_base a_off];
              change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; repeat (first [exact I | split]); CL ]
      | rw_cells _ m ?A ?cs =>
          apply (kx_rw_cells_log segs E m log A cs) in H;
          [ | exact KXLF
            | change E with (kE zv xs); apply log_apart_ez_ok; cbn [log_apart_ez]; cbv [ez a_base a_off];
              change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; cbn [cells_size csize];
              repeat (first [exact I | split]); CL ]
      end
    end
  end.

Ltac z4m_linc T CL :=
  lazymatch goal with
  | |- context [edenot ?E _] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let na := eval vm_compute in (length zv) in
        change E with (kE zv xs);
        rewrite ?(ez_ok zv (kE zv xs) (kE_atoms zv xs));
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        repeat match goal with
        | |- context [?c mod 64] => z4m_zlit c; let v := eval vm_compute in (c mod 64) in change (c mod 64) with v
        end;
        kx_tbl_idx T;
        rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64);
        rewrite ?Z.mod_small by CL;
        CL
      end
  end.

Ltac z4m_wrc T W CL :=
  eapply wr_at_covers; [exact W | unfold estart; cbn [a_base a_off]; z4m_linc T CL | unfold estart; cbn [a_base a_off]; z4m_linc T CL].
