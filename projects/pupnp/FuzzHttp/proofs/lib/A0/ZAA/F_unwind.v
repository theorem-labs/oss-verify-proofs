(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
Import ListNotations.
Open Scope Z_scope.

Definition unwind_fast_entry := 0x78ec0%Z.
Notation PAGE_CELL := 1323936%Z.
Notation GOT_PAGE := 696496%Z.

Section U.
Context {HC : HasCeiling}.
Variable FI : fs_if.

#[using="Type"] Lemma land7_mod8 : forall a, Z.land a 7 = a mod 8.
Proof. intros a. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

#[using="Type"] Lemma rd64_load : forall m a v, rd64 m a v -> ov_read_bytes asegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v [B _]. replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read asegs m a _ 0 8 B); [reflexivity| lia| rewrite length_le8; cbn; lia].
Qed.

Definition uf_post (ra0 : word) (q : Z) (gp tp : word) (s0v s1v s2v s3v s4v s5v s6v : word) (s7 s8 s9 s10 s11 : word)
    (F_ : bvmap 5 word) (fc : bv 32) (T : Z) (tr rest : list Z) (W : list ivl) (m0 : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ws' : list word) (tg : word),
    ms' = MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch W m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (T + 8) [C4 (wz (Z.of_nat (length (tr ++ rest)))); C4 tg]
    /\ u64arr asegs m' (T + 16) ws' /\ length ws' = 30%nat /\ firstn (length (tr ++ rest)) ws' = map wz (tr ++ rest)
    /\ (exists junk, rw_cells asegs m' (q + -64) [CB 64 junk]) /\ stk asegs m' lo (q + -64).

  Variables (ra0 gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q T top pc0 : Z) (m0 : mem).
  Hypothesis QT : 64 <= q + -64 /\ q <= T + 8 /\ T + 16 + 240 <= top /\ top <= 2^47.
  Hypothesis PC0 : 0 <= pc0 < 2^64.

  Notation W := [(q - 64, q); (T + 8, T + 12); (T + 16, T + 256)].

  Notation ST pc mm x12 x15 x16 x17 :=
    (MS (mkR ra0 (wz (q + -64)) gp tp t0 t1 t2 (wz 30) (wz (top - 16)) (wz T) (wz pc0) x12 (wz 4096) (wz (T + 16)) x15 x16 x17
              (wz PAGE_CELL) s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz pc) fc None mm (seg_rom asegs)).

  #[using="PC0"] Lemma uf_exit : forall (lo : Z) (m1 : mem) (ws : list word) (tr : list Z) (tg x12 x15 x16 x17 : word),
    u64arr asegs m1 (T + 16) ws -> length ws = 30%nat -> firstn (length tr) ws = map wz tr ->
    rw_cells asegs m1 (T + 8) [C4 (wz (Z.of_nat (length tr))); C4 tg] ->
    rw_cells asegs m1 (q + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    stk asegs m1 lo (q + -64) ->
    mem_inv asegs m1 -> munch W m0 m1 -> wmono asegs m0 m1 ->
    evt asegs (uf_post ra0 q gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 F_ fc T tr [] W m0 lo)
      (ST 0x78fbc m1 x12 x15 x16 x17).
  Proof.
    intros lo m1 ws tr tg x12 x15 x16 x17 BUF LWS TR SZ FR STK MI MU WM.
    do 8 zstep. zstep. replace (q + -64 + 64) with q by lia. zstep.
    apply evt_done. unfold uf_post. rewrite app_nil_r.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SZ|].
    split; [exact BUF|]. split; [exact LWS|]. split; [exact TR|]. split; [exact (rw_cells_forget asegs _ _ _ FR)| exact STK].
  Qed.

  #[using="pc0 PC0"] Lemma firstn_upd_snoc : forall (tr : list Z) (ws : list word) (r : Z),
    firstn (length tr) ws = map wz tr -> (length tr < length ws)%nat ->
    firstn (length (tr ++ [r])) (upd ws (length tr) (wz r)) = map wz (tr ++ [r]).
  Proof.
    intros tr ws r H L. rewrite length_app, map_app. cbn [length map].
    destruct (upd_app_split ws (length tr) (wz r) L) as (pre & y & post & E & Hlen & Hupd).
    rewrite Hupd. rewrite E in H. rewrite firstn_app, Hlen, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in H by lia.
    rewrite firstn_app, firstn_all2 by lia. rewrite <- Hlen.
    replace (length pre + 1 - length pre)%nat with 1%nat by lia. cbn [firstn]. rewrite H. reflexivity.
  Qed.

  #[using="QT PC0"] Lemma uf_loop : forall (rest : list Z) (lo : Z) (m1 : mem) (ws : list word) (tr : list Z) (a a' : Z) (tg x16 x17 : word),
    u64arr asegs m1 (T + 16) ws -> length ws = 30%nat -> firstn (length tr) ws = map wz tr ->
    rw_cells asegs m1 (T + 8) [C4 (wz (Z.of_nat (length tr))); C4 tg] ->
    (2 <= length tr)%nat -> (length tr + length rest <= 30)%nat ->
    rd64 m1 (a - 16) a' -> fpchain m1 top a a' rest -> Forall (fun r => r <> pc0) rest ->
    T + 16 + 240 + 16 <= a -> a < top - 16 ->
    rw_cells asegs m1 (q + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    stk asegs m1 lo (q + -64) ->
    mem_inv asegs m1 -> munch W m0 m1 -> wmono asegs m0 m1 ->
    evt asegs (uf_post ra0 q gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 F_ fc T tr rest W m0 lo)
      (ST 0x78fa4 m1 (wz a) (wz (Z.of_nat (length tr))) x16 x17).
  Proof.
    induction rest as [|ra' rest IH]; intros lo m1 ws tr a a' tg x16 x17 BUF LWS TR SZ K2 KB RD CH NP LOA ATOP FR STK MI MU WM.
    -
      cbn [fpchain] in CH. unfold valid_frame in CH. destruct RD as [RDB RDR].
      pose proof (rd64_load m1 (a - 16) a' (conj RDB RDR)) as HR.
      zstep.
      zstep. if_cases K1; zify_cond K1.
      + eapply uf_exit; eauto.
      + zstep. if_cases K2'; zify_cond K2'.
        * eapply uf_exit; eauto.
        * zstep. zstep. zstep. if_cases K3; zify_cond K3.
          { exfalso. apply CH. rewrite land7_mod8 in K3. lia. }
          eapply uf_exit; eauto.
    - cbn [fpchain] in CH. destruct CH as (V & V16 & R1 & R2 & a'' & R3 & CH'). unfold valid_frame in V.
      destruct RD as [RDB RDR]. pose proof (rd64_load m1 (a - 16) a' (conj RDB RDR)) as HR.
      inversion NP as [|x l NP1 NP2]; subst x l.
      zstep.
      zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
      zstep. if_cases K2'; zify_cond K2'. { exfalso. lia. }
      zstep. zstep. zstep. if_cases K3; zify_cond K3.
      2:{ exfalso. rewrite land7_mod8 in K3. lia. }

      zstep. if_cases K4; zify_cond K4. { exfalso. cbn [length] in KB. lia. }
      pose proof (rd64_load m1 (a' - 8) ra' R1) as HR2. clear HR. destruct R1 as [R1B R1R].
      zstep.
      zstep. if_cases K5; zify_cond K5. { exfalso. lia. }
      zstep. if_cases K6; zify_cond K6. { exfalso. apply NP1. try rewrite Z.mod_small in K6 by lia. lia. }
      zstep. zstep. zstep.
      replace (Z.shiftl (Z.of_nat (length tr)) 3) with (8 * Z.of_nat (length tr)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      destruct R3 as [R3B R3R].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(T + 8, T + 12); (T + 16, T + 256)] mm) as ML; pose proof (wmono_refl asegs mm) as WL end.
      sstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u64arr_store_ok asegs mm (T + 16) ws (Z.of_nat (length tr)) (wa (T + 16 + 8 * Z.of_nat (length tr))) BUF ltac:(lia) eq_refl) as SOK end.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
        pose proof (u64arr_write asegs mm (T + 16) ws (Z.of_nat (length tr)) (Z_to_bv 64 ra') BUF ltac:(lia)) as BUF2 end.
      clear BUF. store_done. rename BUF2 into BUF.

      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (fpchain_frame rest _ mm top a' a'' _ CH' ML WL ltac:(repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil)) as CH2 end.
      clear CH' ML WL.

      replace (Z.of_nat (length tr) + 1) with (Z.of_nat (length (tr ++ [ra']))) in * by (rewrite length_app; cbn; lia).
      rewrite Nat2Z.id in BUF.
      assert (PEQ : forall ms', uf_post ra0 q gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 F_ fc T (tr ++ [ra']) rest W m0 lo ms' ->
                                uf_post ra0 q gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 F_ fc T tr (ra' :: rest) W m0 lo ms').
      { intros ms' P. unfold uf_post in *. rewrite <- app_assoc in P. cbn [app] in P. exact P. }
      eapply evt_mono; [| exact PEQ].
      eapply (IH lo _ (upd ws (length tr) (Z_to_bv 64 ra')) (tr ++ [ra']) a' a''); try eassumption; try lia.
      + rewrite upd_length. exact LWS.
      + apply firstn_upd_snoc; [exact TR| rewrite LWS; lia].
      + rewrite length_app. cbn. lia.
      + rewrite length_app. cbn. cbn [length] in KB. lia.
      + split; assumption.
  Qed.

  Definition uf_post2 (tr rest : list Z) (lo : Z) : machine_state -> Prop :=
    fun ms' => uf_post ra0 q gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 F_ fc T tr rest W m0 lo ms'.

  #[using="QT PC0"] Lemma uf_entry : forall (lo bp bottom ra1 a1' : Z) (ras : list Z) (ws : list word) (szj tg : word) a6 a7,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q + -64 ->
    rw_cells asegs m0 GOT_PAGE [C8 (wz PAGE_CELL)] -> rw_cells asegs m0 PAGE_CELL [C8 (wz 4096)] ->
    rw_cells asegs m0 (T + 8) [C4 szj; C4 tg] -> u64arr asegs m0 (T + 16) ws -> length ws = 30%nat ->
    bottom < bp -> bp < top - 16 -> bp mod 8 = 0 -> bottom < top -> 4096 <= top ->
    T + 16 + 240 + 16 <= bp ->
    rd64 m0 (bp - 8) ra1 -> 4096 <= ra1 -> ra1 <> pc0 ->
    rd64 m0 (bp - 16) a1' -> fpchain m0 top bp a1' ras -> Forall (fun r => r <> pc0) ras -> (length ras <= 28)%nat ->
    0 <= bottom ->
    mem_inv asegs m0 ->
    evt asegs (uf_post ra0 q gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 F_ fc T [pc0; ra1] ras W m0 lo)
      (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0v s1v (wz T) (wz pc0) (wz bp) (wz top) (wz bottom) (wz 30) a6 a7
                s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6) F_ (wz unwind_fast_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo bp bottom ra1 a1' ras ws szj tg a6 a7 ST CLO LO GP PG SZ BUF LWS V1 V2 V3 BT TP LOA R1 R1P R1N R2 CH NP LR B0 MI.
    unfold unwind_fast_entry. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. pose proof (munch_refl W m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    destruct R1 as [R1B R1R]. destruct R2 as [R2B R2R].
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 64%nat ST. rewrite !E in *.
    replace (q + -64) with (q + -64) in * by lia.
    do 9 sstep.
    zstep. zstep. zstep. zstep.
    zstep. if_cases KC; zify_cond KC. { exfalso. lia. }
    zstep. zstep. zstep.
    zstep. if_cases KP; zify_cond KP. { exfalso; lia. }
    zstep. zstep.
    sstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u64arr_store_ok asegs mm (T + 16) ws 0 (wa (T + 16 + 8 * 0)) BUF ltac:(lia) eq_refl) as SOK end.
    replace (T + 16 + 8 * 0) with (T + 16) in SOK by lia.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u64arr_write asegs mm (T + 16) ws 0 (Z_to_bv 64 pc0) BUF ltac:(lia)) as BUF2 end.
    replace (T + 16 + 8 * 0) with (T + 16) in BUF2 by lia.
    clear BUF. store_done. rename BUF2 into BUF.
    zstep. if_cases KT; zify_cond KT. 2:{ exfalso. rewrite Z.shiftr_div_pow2 in KT by lia. Z.div_mod_to_equations. lia. }

    zstep. if_cases KB1; zify_cond KB1. { exfalso; lia. }
    zstep. if_cases KB2; zify_cond KB2. { exfalso; lia. }
    zstep. zstep. if_cases KB3; zify_cond KB3. { exfalso; lia. }
    zstep. zstep. if_cases KB4; zify_cond KB4. { exfalso. rewrite land7_mod8 in KB4. lia. }
    zstep. zstep.

    zstep. if_cases K4; zify_cond K4. { exfalso; lia. }
    pose proof (rd64_load _ (bp - 8) ra1 (conj R1B R1R)) as HR1.
    zstep.
    zstep. if_cases K5; zify_cond K5. { exfalso; lia. }
    zstep. if_cases K6; zify_cond K6. { exfalso. apply R1N. try rewrite Z.mod_small in K6 by lia. lia. }
    zstep. zstep. zstep.
    sstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u64arr_store_ok asegs mm (T + 16) _ 1 (wa (T + 16 + 8 * 1)) BUF ltac:(rewrite upd_length; lia) eq_refl) as SOK end.
    replace (T + 16 + 8 * 1) with (T + 24) in SOK by lia.
    replace (Z.shiftl 1 3) with 8 by reflexivity.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u64arr_write asegs mm (T + 16) _ 1 (Z_to_bv 64 ra1) BUF ltac:(rewrite upd_length; lia)) as BUF2 end.
    replace (T + 16 + 8 * 1) with (T + 24) in BUF2 by lia. change (Z.to_nat 1) with 1%nat in BUF2. change (Z.to_nat 0) with 0%nat in BUF2.
    clear BUF. store_done. rename BUF2 into BUF.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (fpchain_frame ras _ mm top bp a1' _ CH MU WM ltac:(repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil)) as CH3 end.
    clear CH.

    replace (top + -16) with (top - 16) by lia.
    eapply (uf_loop ras lo _ (upd (upd ws 0 (Z_to_bv 64 pc0)) 1 (Z_to_bv 64 ra1)) [pc0; ra1] bp a1'); try eassumption; try lia.
    all: try (rewrite !upd_length; exact LWS).
    all: try (split; assumption).
    all: try exact BUF.
    all: try (cbn; lia).
    all: destruct ws as [|w0 [|w1 ws']]; [cbn in LWS; lia| cbn in LWS; lia|]; reflexivity.
  Qed.

  #[using="pc0 PC0"] Lemma uf_exit_g : forall (lo : Z) (m1 : mem) (ws : list word) (tr : list Z) (tg x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : word),
    u64arr asegs m1 (T + 16) ws -> length ws = 30%nat -> firstn (length tr) ws = map wz tr ->
    rw_cells asegs m1 (T + 8) [C4 (wz (Z.of_nat (length tr))); C4 tg] ->
    rw_cells asegs m1 (q + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    stk asegs m1 lo (q + -64) ->
    mem_inv asegs m1 -> munch W m0 m1 -> wmono asegs m0 m1 ->
    evt asegs (uf_post ra0 q gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 F_ fc T tr [] W m0 lo)
      (MS (mkR ra0 (wz (q + -64)) gp tp t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x78fbc) fc None m1 (seg_rom asegs)).
  Proof.
    intros lo m1 ws tr tg x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 BUF LWS TR SZ FR STK MI MU WM.
    do 8 zstep. zstep. replace (q + -64 + 64) with q by lia. zstep.
    apply evt_done. unfold uf_post. rewrite app_nil_r.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SZ|].
    split; [exact BUF|]. split; [exact LWS|]. split; [exact TR|]. split; [exact (rw_cells_forget asegs _ _ _ FR)| exact STK].
  Qed.

  #[using="QT PC0"] Lemma uf_entry_top : forall (lo bp bottom : Z) (ws : list word) (szj tg : word) a6 a7,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q + -64 ->
    rw_cells asegs m0 GOT_PAGE [C8 (wz PAGE_CELL)] -> rw_cells asegs m0 PAGE_CELL [C8 (wz 4096)] ->
    rw_cells asegs m0 (T + 8) [C4 szj; C4 tg] -> u64arr asegs m0 (T + 16) ws -> length ws = 30%nat ->
    bottom < bp -> top - 16 <= bp -> bp < 2^64 -> bottom < top -> 4096 <= top ->
    0 <= bottom ->
    mem_inv asegs m0 ->
    evt asegs (uf_post ra0 q gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 F_ fc T [pc0] [] W m0 lo)
      (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0v s1v (wz T) (wz pc0) (wz bp) (wz top) (wz bottom) (wz 30) a6 a7
                s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6) F_ (wz unwind_fast_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo bp bottom ws szj tg a6 a7 ST CLO LO GP PG SZ BUF LWS V1 V2 BPH BT TP B0 MI.
    unfold unwind_fast_entry. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. pose proof (munch_refl W m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 64%nat ST. rewrite !E in *.
    replace (q + -64) with (q + -64) in * by lia.
    do 9 sstep.
    zstep. zstep. zstep. zstep.
    zstep. if_cases KC; zify_cond KC. { exfalso. lia. }
    zstep. zstep. zstep.
    zstep. if_cases KP; zify_cond KP. { exfalso; lia. }
    zstep. zstep.
    sstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u64arr_store_ok asegs mm (T + 16) ws 0 (wa (T + 16 + 8 * 0)) BUF ltac:(lia) eq_refl) as SOK end.
    replace (T + 16 + 8 * 0) with (T + 16) in SOK by lia.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u64arr_write asegs mm (T + 16) ws 0 (Z_to_bv 64 pc0) BUF ltac:(lia)) as BUF2 end.
    replace (T + 16 + 8 * 0) with (T + 16) in BUF2 by lia.
    clear BUF. store_done. rename BUF2 into BUF.
    zstep. if_cases KT; zify_cond KT. 2:{ exfalso. rewrite Z.shiftr_div_pow2 in KT by lia. Z.div_mod_to_equations. lia. }

    zstep. if_cases KB1; zify_cond KB1. { exfalso; lia. }
    zstep. if_cases KB2; zify_cond KB2. { exfalso; lia. }
    zstep. zstep. if_cases KB3; zify_cond KB3. 2:{ exfalso; lia. }
    change (Z.to_nat 0) with 0%nat in BUF.
    eapply (uf_exit_g lo _ (upd ws 0 (Z_to_bv 64 pc0)) [pc0]); try eassumption; try lia.
    all: try (rewrite !upd_length; exact LWS).
    all: try (split; assumption).
    all: try exact BUF.
    all: try (cbn; lia).
    all: destruct ws as [|w0 ws']; [cbn in LWS; lia|]; reflexivity.
  Qed.
End U.
