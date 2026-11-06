(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Mem Cells Step Frame.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew ROpNew_nt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require RMalloc_ifaceP RF_free_spec.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad HarnessP ProgP SjStage1 SjS1Bytes SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw PU_iface PC_s12iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib SegVCx.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPU_sum PFFU_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2G2 S2WalkVC S2WalkVCok S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import S2TabU U2_defs U2_cert.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2U Require Import PU2_t0 PU2_entry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Import ITree.Exc.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.

Section S.
  Context {rc : runConstT}.

  (* [comment removed for export] *)
  Lemma p2_munch : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      THIS DOC BUF LEN ASI N ATP CAPT ASB CAPS AOC AIA (m m' : mem),
    let E := mkEZ (ZLe ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                       THIS DOC BUF LEN ASI N ATP CAPT ASB CAPS AOC AIA) in
    (forall x : word, SP.outside_wins E (SP.p_W U2) (u x) -> m' x = m x) ->
    0 <= THIS -> THIS + 96 < M64 -> 0 <= ATP -> ATP + 8 * CAPT < M64 -> 0 <= CAPT -> 0 <= ASB -> ASB + CAPS < M64 -> 0 <= CAPS ->
    0 <= AOC -> AOC + 8192 < M64 -> 0 <= AIA -> AIA + 1024 < M64 -> 2976 <= u sp ->
    munch [(u sp - 2976, u sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (ATP, ATP + 8 * CAPT); (ASB, ASB + CAPS);
           (AOC, AOC + 8192); (AIA, AIA + 1024)] m m'.
  Proof.
    intros until m'. intros E FR. intros. intros x Hx. apply FR. unfold SP.outside_wins. cbn [SP.p_W U2].
    pose proof (u_rng' sp). pose proof (u_rng' x).
    cbn [outside] in Hx.
    repeat constructor; cbn [SP.win_den]; unfold E; rewrite ?u_zden by reflexivity;
      cbn [zden nth ZLe ZL0 vSP vTHIS vTBASE vCAPT vSBASE vCAPS vOCB vIAB V mul];
      rewrite ?(Z.mod_small _ M64) by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ev_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      THIS DOC BUF LEN ASI N ATP CAPT ASB CAPS AOC AIA (E' : env),
    SP.gagree 28 (mkEZ (ZLe ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                            THIS DOC BUF LEN ASI N ATP CAPT ASB CAPS AOC AIA)) E' ->
    ev E' 0 = ra /\ ev E' 1 = sp /\ ev E' 2 = gp /\ ev E' 3 = tp /\ ev E' 4 = s0 /\ ev E' 5 = s1 /\ ev E' 6 = s2 /\ ev E' 7 = s3 /\
    ev E' 8 = s4 /\ ev E' 9 = s5 /\ ev E' 10 = s6 /\ ev E' 11 = s7 /\ ev E' 12 = s8 /\ ev E' 13 = s9 /\ ev E' 14 = s10 /\
    ev E' 15 = s11.
  Proof.
    intros until E'. intros Hg.
    repeat split; match goal with |- ev E' ?k = _ => rewrite <- (Hg k ltac:(lia)) end;
      cbn [ev mkEZ nth ZLe ZL0]; apply Z_to_bv_bv_unsigned.
  Qed.

  (* [comment removed for export] *)
  Lemma xret_post : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : PState) (LB : list block) (lo B : Z) (errv : word) (THIS ATP ntp ASB nsb AOC AIA : Z)
      (pim ptp psb poc pia : bptr) (nim noc nia : Z)
      (m m' : mem) (R' F' : bvmap 5 word) (fc' : bv 32) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    RHEAP s LB m ->
    In (pim, THIS, nim) LB -> 96 <= nim -> In (ptp, ATP, ntp) LB -> In (psb, ASB, nsb) LB ->
    In (poc, AOC, noc) LB -> 8192 <= noc -> In (pia, AIA, nia) LB -> 1024 <= nia ->
    DJ 0x10000 0xa3000 THIS 96 -> DJ 0x10000 0xa3000 ATP ntp -> DJ 0x10000 0xa3000 ASB nsb ->
    DJ 0x10000 0xa3000 AOC 8192 -> DJ 0x10000 0xa3000 AIA 1024 ->
    ATOP <= lo -> lo <= u sp - 2976 -> u sp <= B ->
    stk usegs m lo (u sp) -> rw_cells usegs m (errno_addr tp) [C4 errv] -> tp = Z_to_bv 64 RATP -> rauxv_ok m B ->
    munch [(u sp - 2976, u sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (ATP, ATP + ntp); (ASB, ASB + nsb);
           (AOC, AOC + 8192); (AIA, AIA + 1024)] m m' ->
    wmono usegs m m' -> mem_inv usegs m' -> (forall lo hi, stk usegs m lo hi -> stk usegs m' lo hi) -> frm0 fc' -> u x10 < 64 ->
    R' = mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 ->
    evt usegs (s2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo B (s2_win THIS ATP ntp ASB nsb AOC AIA) m tt s)
        (MS R' F' (Z_to_bv 64 0x323b8) fc' None m' (seg_rom usegs)).
  Proof.
    intros until x31. intros HR Ith Hnim Itp Isb Ioc Hnoc Iia Hnia UT UP US UO UA Hlo Hlo2 HspB HSTK HERR HTP HAUX MU WM MI' STK' HZ HA0 ->.
    atop_facts. pose proof (u_rng' sp) as Rsp.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Ith) as (Rt1 & Rt2 & Rt3 & Rt4 & _); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Itp) as (Rp1 & Rp2 & Rp3 & Rp4 & _); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Isb) as (Rs1 & Rs2 & Rs3 & Rs4 & _); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Ioc) as (Ro1 & Ro2 & Ro3 & Ro4 & _); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Iia) as (Ra1 & Ra2 & Ra3 & Ra4 & _); cbn [blk_addr blk_size fst snd] in *.
    zstep. apply evt_done. unfold s2_post.
    exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F', fc', m', errv.
    split; [reflexivity|]. split; [exact HZ|]. split; [exact HA0|]. split; [exact MI'|]. split; [exact (STK' _ _ HSTK)|].
    (* [comment removed for export] *)
    assert (IMGW : forall a, 0x10000 <= a < 0xb3000 -> outside [(u sp - 2976, u sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96);
                     (ATP, ATP + ntp); (ASB, ASB + nsb); (AOC, AOC + 8192); (AIA, AIA + 1024)] a).
    { intros a Ha. unfold DJ in UT, UP, US, UO, UA. cbn [outside]. lia. }
    split.
    { subst tp. rewrite errno_lit in HERR |- *. eapply rw_cells_transport; [exact HERR | exact MU | exact WM |].
      unfold RERRNO. cbn [disjoint_from cells_size csize]. unfold DJ in UT, UP, US, UO, UA. lia. }
    split.
    { eapply RF_free_spec.rauxv_ok_pres_B with (C := fun a => u sp - 2976 <= a < u sp \/ THIS + 24 <= a < THIS + 28 \/
                     THIS + 88 <= a < THIS + 96 \/ ATP <= a < ATP + ntp \/ ASB <= a < ASB + nsb \/ AOC <= a < AOC + 8192 \/
                     AIA <= a < AIA + 1024); [exact HAUX | | |].
      - intros a Ha Hc. split; [apply MU; rewrite unsigned_lit by lia; cbn [outside]; lia|]. apply WM.
      - intros a Ha Hc. lia.
      - intros a Ha Hc. pose proof (IMGW a ltac:(unfold RAUXV_CELL in Ha; lia)) as O. cbn [outside] in O. lia. }
    split.
    { intros a Ha Hc Hout. split; [apply MU; rewrite unsigned_lit by lia|apply WM].
      unfold s2_win in Hout. cbn [outside] in Hout |- *. split; [|exact Hout].
      destruct Hc as [Hc|[Hc|(b & Hb & B1 & B2)]]; [lia | lia |].
      pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m b HR Hb) as (_ & _ & _ & Rb4 & _). lia. }
    split; [reflexivity|]. split; [reflexivity|].
    eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HR | exact MU | exact WM |].
    repeat apply Forall_cons; [..| apply Forall_nil]; unfold rclient_write_ok.
    - left. cbn [fst]. lia.
    - right; right. exists (pim, THIS, nim). cbn [fst snd blk_addr blk_size]. split; [exact Ith|]. lia.
    - right; right. exists (pim, THIS, nim). cbn [fst snd blk_addr blk_size]. split; [exact Ith|]. lia.
    - right; right. exists (ptp, ATP, ntp). cbn [fst snd blk_addr blk_size]. split; [exact Itp|]. lia.
    - right; right. exists (psb, ASB, nsb). cbn [fst snd blk_addr blk_size]. split; [exact Isb|]. lia.
    - right; right. exists (poc, AOC, noc). cbn [fst snd blk_addr blk_size]. split; [exact Ioc|]. lia.
    - right; right. exists (pia, AIA, nia). cbn [fst snd blk_addr blk_size]. split; [exact Iia|]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma PW_refl : forall LB SP W m, rheap_pres_W LB SP W m m.
  Proof. intros LB SP W m a _ _ _. auto. Qed.
  Lemma PW_trans : forall LB SP W m1 m2 m3, rheap_pres_W LB SP W m1 m2 -> rheap_pres_W LB SP W m2 m3 -> rheap_pres_W LB SP W m1 m3.
  Proof.
    intros LB SP W m1 m2 m3 H1 H2 a Ha Hc Ho. destruct (H1 a Ha Hc Ho) as [E1 W1]. destruct (H2 a Ha Hc Ho) as [E2 W2].
    split; [congruence | auto].
  Qed.
  Lemma PW_of_munch : forall LB SP W W' m m', munch W' m m' -> wmono usegs m m' ->
    (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a -> outside W' a) -> rheap_pres_W LB SP W m m'.
  Proof.
    intros LB SP W W' m m' MU WM OUT a Ha Hc Ho. split; [apply MU; rewrite unsigned_lit by lia; exact (OUT a Ha Hc Ho) | apply WM].
  Qed.
  Lemma PW_of_pres : forall LB LB' SP SP' W m m', rheap_pres LB' SP' m m' -> SP' <= SP -> (forall b, In b LB -> In b LB') ->
    rheap_pres_W LB SP W m m'.
  Proof.
    intros LB LB' SP SP' W m m' H HS HL a Ha Hc _. exact (rheap_pres_weaken LB' LB SP' SP m m' H HS HL a Ha Hc).
  Qed.

  (* [comment removed for export] *)
  Lemma PW_bytes_at : forall LB SP W m m' A bs, rheap_pres_W LB SP W m m' -> bytes_at usegs m A bs ->
    rclient_range LB SP A (Z.of_nat (length bs)) -> (forall a, A <= a < A + Z.of_nat (length bs) -> outside W a) ->
    bytes_at usegs m' A bs.
  Proof.
    intros LB SP W m m' A bs HP (H0 & H1 & HB) HR HW. split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite <- (HB i Hi). unfold mrd.
    destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia]) ltac:(apply HW; lia)) as [E _].
    rewrite E. reflexivity.
  Qed.
  Lemma PW_wr_at : forall LB SP W m m' A n, rheap_pres_W LB SP W m m' -> wr_at usegs m A n ->
    rclient_range LB SP A n -> (forall a, A <= a < A + n -> outside W a) -> wr_at usegs m' A n.
  Proof.
    intros LB SP W m m' A n HP (H0 & H1 & HW0) HR HW. split; [exact H0|]. split; [exact H1|].
    intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia]) ltac:(apply HW; lia)) as [_ W'].
    apply W'. apply HW0. exact Hi.
  Qed.
  Lemma PW_rw_cells : forall LB SP W m m' A cs, rheap_pres_W LB SP W m m' -> rw_cells usegs m A cs ->
    rclient_range LB SP A (Z.of_nat (cells_size cs)) -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> outside W a) ->
    rw_cells usegs m' A cs.
  Proof.
    intros LB SP W m m' A cs HP [[Hwf HB] HW0] HR HW. split; [split; [exact Hwf|]|].
    - eapply PW_bytes_at; [exact HP | exact HB | rewrite cells_bytes_length by exact Hwf; exact HR |].
      rewrite cells_bytes_length by exact Hwf. exact HW.
    - eapply PW_wr_at; [exact HP | exact HW0 | exact HR | exact HW].
  Qed.

  (* [comment removed for export] *)
  Lemma xret_post2 : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s s' : PState) (LB : list block) (lo B : Z) (errv : word) (W : list (Z * Z))
      (m m' : mem) (R' F' : bvmap 5 word) (fc' : bv 32) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    RHEAP s' LB m' -> rauxv_ok m' B -> rw_cells usegs m' (errno_addr tp) [C4 errv] -> stk usegs m' lo (u sp) -> mem_inv usegs m' ->
    rheap_pres_W LB (u sp) W m m' -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> frm0 fc' -> u x10 < 64 ->
    R' = mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 ->
    evt usegs (s2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo B W m tt s')
        (MS R' F' (Z_to_bv 64 0x323b8) fc' None m' (seg_rom usegs)).
  Proof.
    intros until x31. intros HR HAUX HERR HSTK MI PW HFA HSO HZ HA0 ->.
    zstep. apply evt_done. unfold s2_post.
    exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F', fc', m', errv.
    split; [reflexivity|]. repeat (split; [assumption|]). exact HR.
  Qed.

  (* [comment removed for export] *)
  Lemma gagree_ext1 : forall ZL (E' : env) z, length ZL = 28%nat -> SP.gagree 28 (mkEZ ZL) E' -> ev E' 28 = Z_to_bv 64 z ->
    SP.gagree 29 (mkEZ (ZL ++ [z])) E'.
  Proof.
    intros ZL E' z HL Hg H28 j Hj. destruct (Nat.eq_dec j 28) as [->|Nj].
    - cbn [ev mkEZ]. rewrite app_nth2 by lia. rewrite HL. cbn. rewrite <- H28. reflexivity.
    - rewrite <- (Hg j ltac:(lia)). cbn [ev mkEZ]. rewrite app_nth1 by lia. reflexivity.
  Qed.

  Lemma firstn28_ZLe : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      THIS DOC BUF LEN ASI N ATP CAPT ASB CAPS AOC AIA,
    SP.gagree 28 (mkEZ (ZLe ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                            THIS DOC BUF LEN ASI N ATP CAPT ASB CAPS AOC AIA))
                 (mkEZ [u ra; u sp; u gp; u tp; u s0; u s1; u s2; u s3; u s4; u s5; u s6; u s7; u s8; u s9; u s10; u s11;
                        THIS; DOC; BUF; LEN; ASI; N; ATP; CAPT; ASB; CAPS; AOC; AIA]).
  Proof.
    intros. intros j Hj. cbn [ev mkEZ].
    do 28 (destruct j as [|j]; [reflexivity|]). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma edenot_zl : forall G ZL (E' : env) e, SP.gagree G (mkEZ ZL) E' -> eb (mkEZ ZL) = eb E' -> expr_vars_lt G e = true ->
    zok e = true -> edenot E' e = Z_to_bv 64 (zden ZL e).
  Proof. intros G ZL E' e Hg Hb Hv Hz. rewrite <- (SP.edenot_gagree G _ _ e Hg Hb Hv). apply zden_ok. exact Hz. Qed.

  (* [comment removed for export] *)
  Lemma gagree_app_l : forall G L1 L2 (E : env), length L1 = G -> SP.gagree G (mkEZ (L1 ++ L2)) E -> SP.gagree G (mkEZ L1) E.
  Proof.
    intros G L1 L2 E HL Hg j Hj. rewrite <- (Hg j Hj). cbn [ev mkEZ]. rewrite app_nth1 by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma xnew_regs : forall (GZ : list Z) (E' : env) (R' : bvmap 5 word) (i0 : Z),
    length GZ = 28%nat -> SP.gagree 29 (mkEZ (GZ ++ [i0])) E' -> eb (mkEZ (GZ ++ [i0])) = eb E' -> rfull R' ->
    regs_ok E' XNEW_regs R' ->
    exists x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x27 x28 x29 x30 x31,
      R' = mkR x1 (Z_to_bv 64 (nth 1 GZ 0 - 368)) (Z_to_bv 64 (nth 2 GZ 0)) (Z_to_bv 64 (nth 3 GZ 0)) x5 x6 x7
               (Z_to_bv 64 (nth 19 GZ 0)) x9 (Z_to_bv 64 (nth 19 GZ 0 - i0 + 64)) x11
               x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (nth 18 GZ 0 + i0)) (Z_to_bv 64 (nth 20 GZ 0)) x20 (Z_to_bv 64 (nth 18 GZ 0))
               x22 x23 x24 x25 (Z_to_bv 64 (nth 22 GZ 0)) x27 x28 x29 x30 x31.
  Proof.
    intros GZ E' R' i0 HL Hg Hb HF HR.
    rewrite (regs_ok_canon E' XNEW_regs R' HF HR).
    change (sr_get XNEW_regs 2) with (EAlu ALU_ADD (EVar 1) (ELit (-368))). change (sr_get XNEW_regs 3) with (EVar 2).
    change (sr_get XNEW_regs 4) with (EVar 3). change (sr_get XNEW_regs 8) with (EVar 19).
    change (sr_get XNEW_regs 10) with (EAlu ALU_ADD (EAlu ALU_SUB (EVar 19) (EVar 28)) (ELit 64)).
    change (sr_get XNEW_regs 18) with (EAlu ALU_ADD (EVar 18) (EVar 28)). change (sr_get XNEW_regs 19) with (EVar 20).
    change (sr_get XNEW_regs 21) with (EVar 18). change (sr_get XNEW_regs 26) with (EVar 22).
    let rw e := rewrite (edenot_zl 29 (GZ ++ [i0]) E' e) by first [exact Hg | exact Hb | reflexivity] in
    rw (EAlu ALU_ADD (EVar 1) (ELit (-368))); rw (EVar 2); rw (EVar 3); rw (EVar 19);
    rw (EAlu ALU_ADD (EAlu ALU_SUB (EVar 19) (EVar 28)) (ELit 64)); rw (EAlu ALU_ADD (EVar 18) (EVar 28));
    rw (EVar 20); rw (EVar 18); rw (EVar 22).
    assert (N28 : nth 28 (GZ ++ [i0]) 0 = i0) by (rewrite app_nth2 by lia; rewrite HL; reflexivity).
    assert (NK : forall k, (k < 28)%nat -> nth k (GZ ++ [i0]) 0 = nth k GZ 0) by (intros k Hk; apply app_nth1; lia).
    cbn [zden]. rewrite N28, !NK by lia.
    do 22 eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma p2_frame_facts : forall (sp tp : word) (s : PState) (LB : list block) (lo B : Z) (errv : word) (THIS ATP ntp ASB nsb AOC AIA : Z)
      (pim ptp psb poc pia : bptr) (nim noc nia : Z) (m m' : mem),
    RHEAP s LB m ->
    In (pim, THIS, nim) LB -> 96 <= nim -> In (ptp, ATP, ntp) LB -> In (psb, ASB, nsb) LB ->
    In (poc, AOC, noc) LB -> 8192 <= noc -> In (pia, AIA, nia) LB -> 1024 <= nia ->
    DJ 0x10000 0xa3000 THIS 96 -> DJ 0x10000 0xa3000 ATP ntp -> DJ 0x10000 0xa3000 ASB nsb ->
    DJ 0x10000 0xa3000 AOC 8192 -> DJ 0x10000 0xa3000 AIA 1024 ->
    ATOP <= lo -> lo <= u sp - 2976 -> u sp <= B ->
    rw_cells usegs m (errno_addr tp) [C4 errv] -> tp = Z_to_bv 64 RATP -> rauxv_ok m B ->
    munch [(u sp - 2976, u sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (ATP, ATP + ntp); (ASB, ASB + nsb);
           (AOC, AOC + 8192); (AIA, AIA + 1024)] m m' -> wmono usegs m m' ->
    RHEAP s LB m' /\ rauxv_ok m' B /\ rw_cells usegs m' (errno_addr tp) [C4 errv] /\
    rheap_pres_W LB (u sp) (s2_win THIS ATP ntp ASB nsb AOC AIA) m m'.
  Proof.
    intros until m'. intros HR Ith Hnim Itp Isb Ioc Hnoc Iia Hnia UT UP US UO UA Hlo Hlo2 HspB HERR HTP HAUX MU WM.
    atop_facts. pose proof (u_rng' sp) as Rsp.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Ith) as (Rt1 & Rt2 & Rt3 & Rt4 & _); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Itp) as (Rp1 & Rp2 & Rp3 & Rp4 & _); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Isb) as (Rs1 & Rs2 & Rs3 & Rs4 & _); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Ioc) as (Ro1 & Ro2 & Ro3 & Ro4 & _); cbn [blk_addr blk_size fst snd] in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HR Iia) as (Ra1 & Ra2 & Ra3 & Ra4 & _); cbn [blk_addr blk_size fst snd] in *.
    assert (IMGW : forall a, 0x10000 <= a < 0xb3000 -> outside [(u sp - 2976, u sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96);
                     (ATP, ATP + ntp); (ASB, ASB + nsb); (AOC, AOC + 8192); (AIA, AIA + 1024)] a).
    { intros a Ha. unfold DJ in UT, UP, US, UO, UA. cbn [outside]. lia. }
    split.
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HR | exact MU | exact WM |].
      repeat apply Forall_cons; [..| apply Forall_nil]; unfold rclient_write_ok.
      - left. cbn [fst]. lia.
      - right; right. exists (pim, THIS, nim). cbn [fst snd blk_addr blk_size]. split; [exact Ith|]. lia.
      - right; right. exists (pim, THIS, nim). cbn [fst snd blk_addr blk_size]. split; [exact Ith|]. lia.
      - right; right. exists (ptp, ATP, ntp). cbn [fst snd blk_addr blk_size]. split; [exact Itp|]. lia.
      - right; right. exists (psb, ASB, nsb). cbn [fst snd blk_addr blk_size]. split; [exact Isb|]. lia.
      - right; right. exists (poc, AOC, noc). cbn [fst snd blk_addr blk_size]. split; [exact Ioc|]. lia.
      - right; right. exists (pia, AIA, nia). cbn [fst snd blk_addr blk_size]. split; [exact Iia|]. lia. }
    split.
    { eapply RF_free_spec.rauxv_ok_pres_B with (C := fun a => u sp - 2976 <= a < u sp \/ THIS + 24 <= a < THIS + 28 \/
                     THIS + 88 <= a < THIS + 96 \/ ATP <= a < ATP + ntp \/ ASB <= a < ASB + nsb \/ AOC <= a < AOC + 8192 \/
                     AIA <= a < AIA + 1024); [exact HAUX | | |].
      - intros a Ha Hc. split; [apply MU; rewrite unsigned_lit by lia; cbn [outside]; lia|]. apply WM.
      - intros a Ha Hc. lia.
      - intros a Ha Hc. pose proof (IMGW a ltac:(unfold RAUXV_CELL in Ha; lia)) as O. cbn [outside] in O. lia. }
    split.
    { subst tp. rewrite errno_lit in HERR |- *. eapply rw_cells_transport; [exact HERR | exact MU | exact WM |].
      unfold RERRNO. cbn [disjoint_from cells_size csize]. unfold DJ in UT, UP, US, UO, UA. lia. }
    { intros a Ha Hc Hout. split; [apply MU; rewrite unsigned_lit by lia|apply WM].
      unfold s2_win in Hout. cbn [outside] in Hout |- *. split; [|exact Hout].
      destruct Hc as [Hc|[Hc|(b & Hb & B1 & B2)]]; [lia | lia |].
      pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m b HR Hb) as (_ & _ & _ & Rb4 & _). lia. }
  Qed.

End S.
