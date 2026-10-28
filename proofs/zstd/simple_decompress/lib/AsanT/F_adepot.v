(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AKit ShadowTac ADepot_iface ADepot ADepotKit F_adepot1.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma bkt_offset : forall h, (0 <= h)%Z ->
  Z.shiftr ((Z.shiftl h 44) mod 18446744073709551616) 42 = (4 * bkt h)%Z.
Proof.
  intros h Hh. unfold bkt. rewrite Z.shiftl_mul_pow2 by lia.
  change 18446744073709551616%Z with (2^20 * 2^44)%Z.
  rewrite Zmult_mod_distr_r. rewrite Z.shiftr_div_pow2 by lia.
  change (2^44)%Z with (4 * 2^42)%Z. rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma bkt_offset_land : forall h, (0 <= h)%Z ->
  Z.shiftr (Z.land (Z.shiftl h 44) 18446744073709551615) 42 = (4 * bkt h)%Z.
Proof.
  intros h Hh. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  change (2^64)%Z with 18446744073709551616%Z. apply bkt_offset. exact Hh.
Qed.

(* [comment removed for export] *)
Lemma amo_add_w_le4_gen : forall tf (c : bv 32), (0 <= tf)%Z -> (tf + bv_unsigned c < 2^32)%Z ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) c))
  = le4 (Z_to_bv 64 (tf + bv_unsigned c)).
Proof.
  intros tf c H0 H2. pose proof (bv_unsigned_in_range 32 c) as HC. unfold bv_modulus in HC. change (2 ^ Z.of_N 32)%Z with (2^32)%Z in HC.
  unfold le4 at 2. rewrite unsigned_lit by lia. f_equal.
  cbn [amo_val]. rewrite bv_add_unsigned.
  assert (E1 : bv_unsigned (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) = tf).
  { rewrite bv_extract_unsigned. rewrite le_bytes_to_word_le4. rewrite unsigned_lit by lia.
    rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite !Z.mod_small by lia. reflexivity. }
  rewrite E1. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite Z.mod_small by lia. reflexivity.
Qed.

End CANSEC1.
Ltac amo_stepW4c :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i;
        erewrite amo_add_w_le4_gen;
        [ match goal with |- context [le4 (Z_to_bv 64 (_ + bv_unsigned ?c))] =>
            let v := eval vm_compute in (bv_unsigned c) in change (bv_unsigned c) with v end;
          mem_after_store_opt
        | lia
        | match goal with |- context [bv_unsigned ?c] =>
            let v := eval vm_compute in (bv_unsigned c) in change (bv_unsigned c) with v end; lia ] ]
    end end
  end.

(* [comment removed for export] *)
Notation WFINE sp BA NDp FA sz :=
  ([(sp + -1024, sp); (BA, BA + 4); (5970904, 5970904 + 4); (NDp, NDp + 16);
    (1711048, 1711048 + 8); (1711072, 1711072 + 4); (FA, FA + 8 * (sz + 1))]%Z) (only parsing).

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma dcells_ins : forall L D m m' (sp h v sid : Z) (u : list Z) csF,
  let N := dN D in let tf := dtf D in let b0 := bkt h in
  let BA := (TAB + 4 * b0)%Z in let NDp := (al_nodes L + 16 * (N + 1))%Z in let FA := (al_store L + 8 * tf)%Z in
  let sz := Z.of_nat (length u) in
  dcells L D m -> dlayout L -> (ATOP <= sp - 1024)%Z -> (sp <= 2^64)%Z -> (0 <= h)%Z ->
  (1 <= N)%Z -> (16 * (N + 2) <= 1048576)%Z -> (0 <= tf)%Z -> (8 * (tf + sz + 1) <= 8388608)%Z ->
  munch (WFINE sp BA NDp FA sz) m m' -> wmono bsegs m m' ->
  rw_cells bsegs m' BA [C4 (Z_to_bv 64 (N + 1))] ->
  rw_cells bsegs m' NUNIQ [C4 (Z_to_bv 64 (N + 1))] ->
  rw_cells bsegs m' NDp [C8 (Z_to_bv 64 h); C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 sid)] ->
  rw_cells bsegs m' SSTF [C8 (Z_to_bv 64 (tf + sz + 1))] ->
  rw_cells bsegs m' SSST [C4 (Z_to_bv 64 (tf + sz + 1))] ->
  rw_cells bsegs m' SSPTR [C8 (Z_to_bv 64 (al_store L))] ->
  rw_cells bsegs m' MAP1 [C8 (Z_to_bv 64 (al_nodes L))] ->
  rw_cells bsegs m' FA csF -> Z.of_nat (cells_size csF) = (8 * (sz + 1))%Z ->
  dcells L (dins D b0 h v sid sz) m'.
Proof.
  intros L D m m' sp h v sid u csF N tf b0 BA NDp FA sz DC LY SPL SPH Hh N1 NR TF0 TFR MU WM CBA CNU CND CTF CST CPTR CMAP CFA SF.
  assert (HB : (0 <= b0 < 1048576)%Z) by (subst b0; unfold bkt; apply Z.mod_pos_bound; lia).
  destruct DC as (_ & _ & _ & _ & _ & CT & CN & SKN & SKS).
  pose proof LY as (_ & _ & LN0 & LN1 & LS0 & LS1 & DISJ). unfold AIMG_HI, TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST in *.
  subst N tf BA NDp FA.
  (* [comment removed for export] *)
  assert (OUT : forall x,
    ((1776600 <= x < 1776600 + 4 * 1048576 /\ ~ (1776600 + 4 * b0 <= x < 1776600 + 4 * b0 + 4))
     \/ (al_nodes L + 16 <= x < al_nodes L + 1048576 /\ ~ (al_nodes L + 16 * (dN D + 1) <= x < al_nodes L + 16 * (dN D + 1) + 16))
     \/ (al_store L <= x < al_store L + 8388608 /\ ~ (al_store L + 8 * dtf D <= x < al_store L + 8 * dtf D + 8 * (sz + 1))))%Z ->
    m' (wa x) = m (wa x)).
  { intros x Hx. apply (munch_point _ m m' x MU); [lia|]. cbn [outside]. lia. }
  clear MU.
  split; [exact CTF|]. split; [exact CPTR|]. split; [exact CST|]. split; [exact CNU|]. split; [exact CMAP|].
  split.
  { intros b Hb. cbn [dhd dins]. destruct (Z.eqb_spec b b0) as [->|NE]; [exact CBA|].
    eapply rw_cells_agree; [exact (CT b Hb) | | exact WM]. intros x Hx. apply OUT. unfold TAB in Hx. cbn in Hx. left. lia. }
  split.
  { intros i Hi. cbn [dN dhs dlk dsid dins] in Hi |- *. destruct (Z.eqb_spec i (dN D + 1)) as [->|NE]; [exact CND|].
    eapply rw_cells_agree; [exact (CN i ltac:(lia)) | | exact WM]. intros x Hx. apply OUT. cbn in Hx. right; left. lia. }
  split.
  { cbn [dN dins]. destruct (stk_split bsegs m _ (al_nodes L + 16 * (dN D + 1 + 1)) _ SKN ltac:(lia)) as [_ SK2].
    eapply stk_agree; [exact SK2 | | exact WM]. intros x Hx. apply OUT. right; left. lia. }
  { destruct (stk_split bsegs m _ (al_store L + 8 * dtf D) _ SKS ltac:(lia)) as [SK1 SK23].
    destruct (stk_split bsegs m _ (al_store L + 8 * dtf D + 8 * (sz + 1)) _ SK23 ltac:(lia)) as [_ SK3].
    apply (stk_merge bsegs m' _ (al_store L + 8 * dtf D)); [| | lia].
    - eapply stk_agree; [exact SK1 | | exact WM]. intros x Hx. apply OUT. right; right. lia.
    - apply (stk_merge bsegs m' _ (al_store L + 8 * dtf D + 8 * (sz + 1))); [| | lia].
      + pose proof (stk_of_rw_cells bsegs m' _ _ CFA) as SKF. rewrite SF in SKF. exact SKF.
      + eapply stk_agree; [exact SK3 | | exact WM]. intros x Hx. apply OUT. right; right. lia. }
Qed.

Section PUT.
  Variables (L : alayout) (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo T sz pc : Z) (tb : list word) (tr : list Z).
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis ALO : (ATOP <= lo)%Z.
  Hypothesis LO : (lo <= bv_unsigned sp - 1024)%Z.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis A0 : a0 = Z_to_bv 64 T.
  Hypothesis A1 : a1 = Z_to_bv 64 sz.
  Hypothesis SZ1 : sz = (1 + Z.of_nat (length tr))%Z.
  Hypothesis SZ2 : (sz <= 255)%Z.
  Hypothesis TB : u64arr bsegs m T tb.
  Hypothesis LTB : length tb = 255%nat.
  Hypothesis TR : map bv_unsigned (firstn (S (length tr)) tb) = pc :: tr.
  Hypothesis INU : In (pc :: tr) (al_U L).
  Hypothesis SPT : (bv_unsigned sp <= T)%Z.
  Hypothesis T47 : (T + 2040 <= 2^47)%Z.
  Hypothesis AD : ADEPOTi L m.
  Hypothesis LN0 : (AIMG_HI <= al_nodes L)%Z.
  Hypothesis LN1 : (al_nodes L + 1048576 <= ATOP)%Z.
  Hypothesis LS0 : (AIMG_HI <= al_store L)%Z.
  Hypothesis LS1 : (al_store L + 8388608 <= ATOP)%Z.
  Hypothesis RI : rng RNG 0x10000 0x615000.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RT : rng RNG T 2040.
  Hypothesis RNODES : rng RNG (al_nodes L) 1048576.
  Hypothesis RSTORE : rng RNG (al_store L) 8388608.

  Notation POST := (depot_put_post L ADEPOTi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  Lemma put_body :
    evtF bsegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x74a48) fc None m (seg_rom bsegs)).
  Proof.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    unfold AIMG_HI in *.
    assert (RSTK' : rng RNG (bv_unsigned sp + -1024) 1024) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (SZ : (1 <= sz <= 255)%Z) by lia.
    assert (LU : Z.of_nat (length (pc :: tr)) = sz) by (cbn [length]; lia).
    (* [comment removed for export] *)
    destruct AD as (D & WF & DC & LY). pose proof DC as DC0. pose proof LY as LY0.
    pose proof WF as (N1 & LK & HD & ND & CMP & TF0 & TFB & NB).
    destruct DC as (CTF & CPTR & CST & CNU & CMAP & CT & CN & SKN & SKS).
    unfold TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST in *.
    remember (al_nodes L) as NODES eqn:ENODES. remember (al_store L) as STORE eqn:ESTORE.
    pose proof (CNT_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as CNT0.
    pose proof (BUD_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as BUD0.
    remember (dN D) as N eqn:EN. remember (dtf D) as tf eqn:ETF.
    assert (BN : (1 <= N < 65536 /\ 0 <= tf < 1048576)%Z) by lia.
    clear TFB NB CNT0 BUD0.
    destruct LY as (AN & AS & _ & _ & _ & _ & DISJ). rewrite <- ENODES in AN. rewrite <- ESTORE in AS, DISJ. box DISJ.
    (* [comment removed for export] *)
    pose proof (mz_init_range sz) as HR0.
    remember (mz_adds (mz_init sz) (pc :: tr)) as HA eqn:EHA.
    pose proof (mz_adds_range (pc :: tr) (mz_init sz) HR0) as HRA. rewrite <- EHA in HRA.
    pose proof (mz_fin_range HA) as HRH. remember (mz_fin HA) as HSH eqn:EHSH.
    assert (HU : hashU (pc :: tr) = HSH).
    { rewrite EHSH, EHA. unfold hashU. rewrite LU. reflexivity. }
    assert (HB : (0 <= bkt HSH < 1048576)%Z) by (unfold bkt; apply Z.mod_pos_bound; lia).
    remember (bkt HSH) as b0 eqn:EB0.
    pose proof (CT b0 HB) as CB0. destruct (HD b0 HB) as [VR VB]. remember (dhd D b0) as v eqn:EV.
    remember (1776600 + 4 * b0)%Z as BA eqn:EBA.
    remember (NODES + 16 * (N + 1))%Z as NDp eqn:ENDp.
    remember (STORE + 8 * tf)%Z as FA eqn:EFA.
    pose proof (munch_refl [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z m) as MU1.
    pose proof (munch_refl (WFINE (bv_unsigned sp) BA NDp FA sz) m) as MU2.
    pose proof (wmono_refl bsegs m) as WM.
    subst a0 a1.
    (* [comment removed for export] *)
    do 8 zstep.
    carve_frame 112%nat ST.
    do 16 zstep. zstep. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true; cbv iota.
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    { exfalso. clear -K1 SZ. rewrite Z.add_0_r in K1. rewrite bv_swrap_small in K1 by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      rewrite Z.mod_small in K1 by lia. lia. }
    zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2 SPT LO LO0. lia. }
    do 14 zstep.
    (* [comment removed for export] *)
    setreg 12%Z (Z_to_bv 64 (mz_init sz))
      ltac:(f_equal; unfold mz_init;
            first [ replace (Z.land sz 4294967295) with sz by (change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity)
                  | rewrite (Z.mod_small sz 4294967296) by lia
                  | idtac ];
            reflexivity).
    setreg 13%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
    setreg 14%Z (Z_to_bv 64 (T + 8 * sz))
      ltac:(f_equal;
            first [ replace (Z.land sz 4294967295) with sz by (change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity)
                  | rewrite (Z.mod_small sz 4294967296) by lia
                  | idtac ];
            rewrite Z.shiftl_mul_pow2 by lia; lia).
    setreg 11%Z (Z_to_bv 64 (T + 8 * 0)) ltac:(f_equal; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply (hash_loop RNG) with (m := mc) (tb := tb) (k := Z.to_nat sz) (i := 0%Z);
      [ eassumption | exact LTB | exact SZ | lia | exact RT | lia | lia | exact HR0 | ]
    end.
    intros x15' x16'.
    replace (map bv_unsigned (firstn (Z.to_nat (sz - 0)) (skipn (Z.to_nat 0) tb))) with (pc :: tr)
      by (rewrite <- TR, Z.sub_0_r; replace (Z.to_nat sz) with (S (length tr)) by lia; reflexivity).
    rewrite <- EHA.
    do 16 zstep.
    setreg 19%Z (Z_to_bv 64 (mz_fin HA)) ltac:(reflexivity). rewrite <- EHSH.
    do 3 zstep.
    match goal with |- context [Z.shiftr ?e 42] =>
      replace (Z.shiftr e 42) with (4 * bkt HSH)%Z by (symmetry; first [apply bkt_offset | apply bkt_offset_land]; lia) end.
    rewrite <- EB0. rewrite <- EBA.
    (* [comment removed for export] *)
    zstep. rewrite sx32_lit by lia.
    zstep. zstep. fold_lits. zstep.
    zstep. setreg 25%Z (Z_to_bv 64 v) ltac:(f_equal; change 2147483647%Z with (Z.ones 31); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zstep. zstep. fold_lits. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (CN1 : forall i, (1 <= i <= N)%Z ->
        rw_cells bsegs mc (NODES + 16 * i) [C8 (Z_to_bv 64 (dhs D i)); C4 (Z_to_bv 64 (dlk D i)); C4 (Z_to_bv 64 (dsid D i))])
        by (intros i Hi; apply (rw_cells_transport bsegs [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z m mc);
            [apply CN; exact Hi | exact MU1 | exact WM | cbn [disjoint_from fst snd cells_size csize Nat.add]; lia])
    end.
    eapply (find_loop RNG) with (N := N) (hs := dhs D) (lk := dlk D) (sid := dsid D) (k := Z.to_nat v) (j := v);
      [ exact HRH | lia | exact CMAP | exact CN1 | unfold AIMG_HI; lia | exact LK
      | intros i Hi; exact (proj1 (ND i Hi)) | exact RI | exact RNODES | lia | lia | |].
    { (* [comment removed for export] *)
      intros j' x11 x12' Hj' Hhs Hin.
      do 13 zstep.
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. unfold depot_put_post. exists j'. do 15 eexists. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [lia|].
      eapply (adepot_frame L m _ [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z); [exact AD | exact MU1 | assumption |].
      constructor; [| constructor]. cbn [fst snd]. intros a Ha. subst NODES STORE. lia. }
    (* [comment removed for export] *)
    intros x10' x12' FA0. cbv delta [MAP1].
    assert (FA1 : Forall (fun j => dhs D j <> HSH) (chain (dlk D) (dhd D (bkt HSH)))) by (rewrite <- EB0, <- EV; exact FA0).
    pose proof (dwf_absent_budget (al_U L) D (pc :: tr) HSH WF INU HU FA1) as BUDG.
    rewrite LU, <- ETF, <- EN in BUDG. destruct BUDG as [BTF BNN].
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      destruct (stk_split bsegs mc _ (NDp + 16) _ SKN ltac:(lia)) as [SKa SKN'];
      destruct (stk_carve bsegs mc _ _ 16 SKa ltac:(lia)) as [_ [jn NODEC]];
      replace (NDp + 16 - Z.of_nat 16)%Z with NDp in NODEC by lia;
      apply (rw_cells_split_CB bsegs mc NDp [] 16 jn [] [8;4;4]%nat) in NODEC; [| reflexivity]; cbn [mk_CB_cells app] in NODEC;
      destruct (stk_split bsegs mc _ FA _ SKS ltac:(lia)) as [SKS1 SKS23];
      destruct (stk_split bsegs mc _ (FA + 8 * (sz + 1)) _ SKS23 ltac:(lia)) as [SKSm SKS3];
      destruct (stk_carve bsegs mc _ _ (Z.to_nat (8 * (sz + 1))) SKSm ltac:(lia)) as [_ [jf FRC]];
      replace (FA + 8 * (sz + 1) - Z.of_nat (Z.to_nat (8 * (sz + 1))))%Z with FA in FRC by lia;
      apply (rw_cells_split_CB bsegs mc FA [] _ jf [] [8; Z.to_nat (8 * sz)]%nat) in FRC; [| cbn [sum_nat]; lia]; cbn [mk_CB_cells app] in FRC
    end.
    clear SKa SKSm MU1 CN1.
    (* [comment removed for export] *)
    zstep. zstep.
    name_sp sp (-112)%Z.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evtF_cut;
      [ eapply (lock_body RNG) with (lo := lo) (B := BA) (v := v);
        [ eassumption | rewrite Hsp; exact ST | rewrite Hsp; lia | unfold AIMG_HI; lia | reflexivity | exact CB0 | lia
        | unfold TAB, NUNIQ; lia | rewrite Hsp; eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RI | lia] ]
      | post_call bsegs mc ]
    end.
    unname_sp.
    zstep. zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3. lia. }
    (* [comment removed for export] *)
    zstep. zstep. fold_lits. zstep.
    amo_stepW4c. rewrite sx32_lit by lia.
    zstep. rewrite bv_swrap_small by (change (bv_half_modulus 32) with 2147483648%Z; lia).
    zstep. zstep.
    setreg 9%Z (Z_to_bv 64 (N + 1))
      ltac:(f_equal; first [ rewrite Z.mod_small by lia; reflexivity
                           | change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity ]).
    zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4 BN. lia. }
    zstep. zstep. shr0.
    zstep. zstep. fold_lits. zstep. zstep. if_cases K5; zify_cond K5. { exfalso. clear -K5 LN0. lia. }
    zstep. setreg 11%Z (Z_to_bv 64 (N + 1)) ltac:(f_equal; change 65535%Z with (Z.ones 16); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zstep. zstep. setreg 9%Z (Z_to_bv 64 NDp) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FR. destruct FR as [FRa FRbc].
    cbn [cells_size csize Nat.add] in FRbc. change (Z.of_nat 8) with 8%Z in FRbc.
    replace (bv_unsigned sp + -112 + 8)%Z with (bv_unsigned sp + -104)%Z in FRbc by lia.
    apply (proj1 (rw_cells_app bsegs _ _ [_; _] _)) in FRbc. destruct FRbc as [FRb FRc].
    cbn [cells_size csize Nat.add] in FRc. change (Z.of_nat 16) with 16%Z in FRc.
    replace (bv_unsigned sp + -104 + 16)%Z with (bv_unsigned sp + -88)%Z in FRc by lia.
    apply (rw_cells_C8_C4C4 bsegs _ _ [_] [] sz) in FRb; [cbn [app] in FRb | lia].
    unbox DISJ.
    name_sp sp (-112)%Z.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evtF_cut;
      [ eapply (nstore_body RNG) with (lo := lo) (NDp := NDp) (AR := (bv_unsigned sp + -104)%Z) (T := T) (sz := sz) (tf := tf)
                                      (STORE := STORE) (HW := Z_to_bv 64 HSH) (tb := tb);
        [ eassumption | rewrite Hsp; eassumption | rewrite Hsp; lia | atop_facts; lia | reflexivity | reflexivity | reflexivity
        | exact FRb | rewrite Hsp; lia | exact NODEC | exact CTF | exact CPTR | exact CST | rewrite EFA in FRC; exact FRC | eassumption | exact LTB | exact SZ
        | lia | lia | unfold AIMG_HI; lia | unfold AIMG_HI; lia | lia
        | exact RI | rewrite Hsp; eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RSTK' | lia]
        | eapply rng_sub'; [exact RNODES | lia] | eapply rng_sub'; [exact RSTORE | lia] | exact RT ]
      | let ms' := fresh "ms'" in let PO := fresh "PO" in
        intros ms' PO; cbv beta delta [nstore_post SSTF SSST] in PO; revert ms' PO; post_call bsegs mc ]
    end.
    unname_sp.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true; cbv iota.
    do 13 zstep.
    match goal with H : stk bsegs _ lo _ |- _ => rename H into STK end.
    release_frame FRa STK (bv_unsigned sp + -104)%Z.
    release_frame FRb STK (bv_unsigned sp + -88)%Z.
    release_frame FRc STK (bv_unsigned sp).
    apply evtF_done. unfold depot_put_post. exists (N + 1)%Z. do 15 eexists. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn [outside]. intros ax Hax. subst NODES STORE. lia. }
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [lia|].
    exists (dins D b0 HSH v (tf + 1) (Z.of_nat (length (pc :: tr)))). split; [| split; [| exact LY0]].
    - rewrite EB0, EV, EB0. eapply dwf_insert; [exact WF | exact INU | exact HU | reflexivity | rewrite <- EB0, <- EV; exact FA0 | lia].
    - rewrite EB0.
      lazymatch goal with |- dcells _ _ ?mf => eapply (dcells_ins L D m mf (bv_unsigned sp) HSH v (tf + 1)%Z (pc :: tr)) end.
      all: cbv zeta; unfold TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST.
      all: rewrite <- ?ENODES, <- ?ESTORE, <- ?EN, <- ?ETF, ?LU, <- ?EB0.
      all: rewrite <- ?EBA, <- ?ENDp, <- ?EFA.
      all: try assumption. all: try lia.
      { rewrite EFA. eassumption. }
      cbn [cells_size csize Nat.add]. lia.
  Qed.
End PUT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem adepot_put : depot_put_stmt ADEPOTi.
Proof. unfold depot_put_stmt. intros. eapply put_body; eassumption. Qed.

Definition adepot_iface : ADepotIface := mkADepotIface ADEPOTi adepot_put adepot_frame.
End CANSEC2.
