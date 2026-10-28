(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.

From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_w4m AF_huf_w4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4fin.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_kit AF_fse_rd_mem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXCell.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Definition AW4_DBC2 : Z := AW4_DBC.

Section CANSEC1. Context {rc : runConstT}.
Section W4FIN2.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (pdt pb : aptr) (SBL SBH : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -480).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TL11 : tl = 11.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis HDB : In (HB pb DST dcap) LB.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis NSM : n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis SRCB : 0 < n -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= SS /\ SS + n <= SBH.
  Hypothesis DJ1 : KXGoM.apart DT DTL SS n.
  Hypothesis DJ2 : KXGoM.apart DST dcap SS n.
  Hypothesis DJ3 : KXGoM.apart DST dcap DT DTL.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : SP <= r_hi rstk.
  Hypothesis RRL : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation W4FX := (W4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Notation W4KFL := (@AF_huf_w4fin.W4KFL rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs).
  Local Notation w4f_dtl := (@AF_huf_w4fin.w4f_dtl rc sp dcap mtl tl src cbs MTL TL11 TLM DC).
  Local Notation w4f_unp := (@AF_huf_w4fin.w4f_unp rc AI L RNG st LB ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs pdt pb SBL SBH AH MTL TL11 TLM HDT HDB DC SRCB LOA LOS SPT SP16 WSK).
  Local Notation w4fr := (@AF_huf_w4fin.w4fr DST dcap SS DT src).
  Local Notation w4mid := (@AF_huf_w4fin.w4mid DST SS).
  Local Notation w4sr1 := (@AF_huf_w4fin.w4sr1 dcap src).
  Local Notation W4SR := (@AF_huf_w4fin.W4SR DST dcap src).
  Local Notation W4KF3 := (@AF_huf_w4fin.W4KF3 rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs).
  Local Notation W4KERR := (@AF_huf_w4fin.W4KERR rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs).
  Local Notation W4KFX2 := (@AF_huf_w4fin.W4KFX2 rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs).
  Local Notation w4se := (@AF_huf_w4fin.w4se DST dcap).
  Local Notation W4KFE := (@AF_huf_w4fin.W4KFE rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs).
  Local Notation w4f_loop := (@AF_huf_w4fin.w4f_loop rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pdt pb SBL SBH AH MTL TL11 TLM HDT LCB HDB DC NSM SRCB DJ1 DJ2 DJ3 LOA LOS SPT SP16 WSK WIM).
  Local Notation w4f_x1631 := (@AF_huf_w4fin.w4f_x1631 rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pb AH TL11 TLM LCB HDB DC LOA LOS SPT).
  Local Notation w4f_x1675 := (@AF_huf_w4fin.w4f_x1675 rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pb AH TL11 TLM LCB HDB DC LOA LOS SPT).
  Local Notation w4f_x1674 := (@AF_huf_w4fin.w4f_x1674 rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pb AH TL11 TLM LCB HDB DC LOA LOS SPT).
  Local Notation w4f_else := (@AF_huf_w4fin.w4f_else rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pdt pb SBL SBH AH MTL TL11 TLM HDT LCB HDB DC NSM S16 SRCB LOA LOS SPT SP16 WSK).
  Local Notation w4f_end := (@AF_huf_w4fin.w4f_end rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pdt pb SBL SBH AH MTL TL11 TLM HDT LCB HDB DC SRCB LOA LOS SPT SP16 WSK).
  Local Notation w4f_tail := (@AF_huf_w4fin.w4f_tail rc AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs pdt pb SBL SBH AH MTL TL11 TLM HDT LCB HDB DC SRCB DJ1 DJ2 DJ3 LOA LOS SPT SP16 WSK).

  
  Lemma w4f_lay : ATOP_MIN + 12288 <= SP /\ SP <= 2^47 /\ ATOP + 4096 <= lo /\ lo + 8192 <= SP /\ KHIGH <= lo
    /\ AIMG_HI <= DST /\ DST + dcap <= ATOP /\ AIMG_HI <= DT /\ DT + DTL <= ATOP
    /\ (0 < n -> AIMG_HI <= SBL /\ SBH <= ATOP).
  Proof using All.
    pose proof (AI_layout AI L RNG st LB m0 AH) as HL. pose proof (@ATOP_lo rc) as HA.
    pose proof (AI_block_bounds AI L RNG st LB m0 _ AH HDB) as HB1. pose proof (AI_block_bounds AI L RNG st LB m0 _ AH HDT) as HB2.
    cbn [ab_addr ab_size] in HB1, HB2.
    unfold HUF_DEC_STACK_A in LOS. unfold ATOP_MIN, KHIGH in *.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))); try lia.
    intros HN. destruct (SRCB HN) as (p & HP & _ & _).
    pose proof (AI_block_bounds AI L RNG st LB m0 _ AH HP) as HB3. cbn [ab_addr ab_size] in HB3. lia.
  Qed.

  
  Lemma w4f_rel : forall m A B cs sz, stk bsegs m lo A -> rw_cells bsegs m A cs -> cells_size cs = sz -> lo <= A ->
    B = A + Z.of_nat sz -> stk bsegs m lo B.
  Proof.
    intros m A B cs sz ST RW HS HL ->. subst sz. exact (stk_release bsegs m lo A cs ST RW HL).
  Qed.

  
  Lemma w4f_stk : forall mm fr mid l256 l296 l336, W4FX mm fr mid l256 l296 l336 -> stk bsegs mm lo (SP + -104).
  Proof using All.
    intros mm fr mid l256 l296 l336 HW. pose proof w4f_lay as LY.
    destruct HW as (_ & _ & _ & _ & ST & F0 & S0 & F1 & S1 & F2 & S2 & F3 & S3 & F4 & S4 & _).
    pose proof (w4f_rel mm _ (SPF + 104) _ _ ST F0 S0 ltac:(lia) ltac:(lia)) as T1.
    pose proof (w4f_rel mm _ (SPF + 256) _ _ T1 F1 S1 ltac:(lia) ltac:(lia)) as T2.
    pose proof (w4f_rel mm _ (SPF + 296) _ _ T2 F2 S2 ltac:(lia) ltac:(lia)) as T3.
    pose proof (w4f_rel mm _ (SPF + 336) _ _ T3 F3 S3 ltac:(lia) ltac:(lia)) as T4.
    exact (w4f_rel mm _ (SP + -104) _ _ T4 F4 S4 ltac:(lia) ltac:(lia)).
  Qed.

  Definition w4hide (P : Prop) : Prop := P.
  
  Lemma w4h_mk : forall P : Prop, P -> w4hide P.
  Proof. intros P H. exact H. Qed.

  
  Lemma w4f_err : W4KERR.
  Proof using All.
    intros mm fr mid l256 l296 l336 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
      x27 x28 x29 x30 x31 HW.
    pose proof (w4f_stk _ _ _ _ _ _ HW) as ST. pose proof w4f_lay as LY.
    destruct HW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FRC & MI & MU & WM).
    pose proof (w4h_mk _ (conj MI (conj MU WM))) as HID. clear MI MU WM.
    unfold AW4_FERR. idtac "@@"; idtac "LEMMA w4f_err".
    Time kx_runFm [AW4_ERR] 12%nat [KZRange SP (ATOP_MIN + 12288) (2^47)] (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
    all: kx_post_regs. all: cbn [mem_denot]. all: unfold w4hide in HID. all: destruct HID as (MI & MU & WM).
    all: eapply w4_err; eassumption.
  Qed.

  
  Lemma w4f_fx2 : W4KFX2.
  Proof using All.
    intros mm w0 w8 w16 w24 w32 mid l256 l296 l336 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
      x23 x24 x25 x26 x27 x28 x29 x30 x31 HW HD.
    pose proof (w4f_stk _ _ _ _ _ _ HW) as ST. pose proof w4f_lay as LY.
    destruct HW as (_ & _ & _ & _ & _ & FR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & FRC & MI & MU & WM).
    pose proof (w4h_mk _ (conj MI (conj MU WM))) as HID. clear MI MU WM.
    assert (HDC : 1 <= dcap <= 2^32 - 1) by lia.
    unfold AF_huf_w4fin.w4fr in FR0.
    pose proof (proj2 (proj1 FR0)) as FRB.
    pose proof (cells_bytes_length _ (proj1 (proj1 FR0))) as FBL. cbn [cells_size csize Nat.add] in FBL.
    set (fbs := cells_bytes _) in FRB, FBL. assert (FBZ : Z.of_nat (length fbs) = 104) by (rewrite FBL; reflexivity). clear FBL.
    unfold AW4_FX2. idtac "@@"; idtac "LEMMA w4f_fx2".
    Time kx_runFm [AW4_EPI] 40%nat
      [KZRange SP (ATOP_MIN + 12288) (2^47); KZRange dcap 1 (2^32 - 1);
       KZWord (SP + -408) 8 dcap; KZWord (SP + -400) 8 DST]
      [(SP + -480, 104)] [(SP + -480, 104)] (@nil (Z * Z)).
    all: try w4br.
    all: try (lazymatch goal with |- 0 <= _ < 2 ^ 64 => clear - LY HDC; unfold AIMG_HI in *; lia end).
    all: kx_post_regs. all: cbn [mem_denot]. all: unfold w4hide in HID. all: destruct HID as (MI & MU & WM).
    all: eapply w4_epi; eassumption.
  Qed.

  
  Lemma w4f_ktb : AW4_KTB = AW4_CTZ.
  Proof. reflexivity. Qed.

  Definition w4ctz_ok : bool :=
    forallb (fun j => match seg_rom bsegs (Z_to_bv 64 (AW4_CTZ + Z.of_nat j)) with
                      | Some b => (bv_unsigned b <=? 63) && ro_addr bsegs (Z_to_bv 64 (AW4_CTZ + Z.of_nat j))
                      | None => false end) (seq 0 64).

  
  Lemma w4ctz_ok_true : w4ctz_ok = true.
  Proof. vm_compute. reflexivity. Qed.

  
  Lemma w4f_ctz_tab : forall m, mem_inv bsegs m -> ztab_fact bsegs m AW4_CTZ 64 1 [(0, 0, 63)].
  Proof.
    intros m MI z Hz l0 h0 Hf.
    rewrite Z.mod_1_r in Hf. cbn in Hf. injection Hf as <- <-.
    pose proof w4ctz_ok_true as T. unfold w4ctz_ok in T. rewrite forallb_forall in T.
    specialize (T (Z.to_nat (z - AW4_CTZ)) ltac:(apply in_seq; lia)).
    rewrite Z2Nat.id in T by lia. replace (AW4_CTZ + (z - AW4_CTZ)) with z in T by lia.
    destruct (seg_rom bsegs (Z_to_bv 64 z)) as [b|] eqn:ER; [|discriminate].
    apply andb_prop in T as [T1 T2]. apply Z.leb_le in T1.
    exists b. split; [|pose proof (bv_unsigned_in_range _ b); lia].
    cbn [rdn]. destruct (m (Z_to_bv 64 z)) as [b'|] eqn:EM.
    - apply MI in EM. congruence.
    - rewrite ER. reflexivity.
  Qed.

  
  Lemma w4_evtF_eq : forall (P : machine_state -> Prop) ms ms', evtF bsegs RNG P ms' -> ms' = ms -> evtF bsegs RNG P ms.
  Proof. intros P ms ms' H E. subst ms'. exact H. Qed.

  
  Lemma w4_bveq2 : forall a b, a = b \/ a = b + 2^64 \/ a + 2^64 = b -> Z_to_bv 64 a = Z_to_bv 64 b.
  Proof.
    intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2^64).
    destruct H as [E | [E | E]]; subst; [reflexivity | | symmetry].
    - rewrite <- (Z.mod_add b 1 (2^64)) by lia. f_equal; lia.
    - rewrite <- (Z.mod_add a 1 (2^64)) by lia. f_equal; lia.
  Qed.

  Lemma w4f_br_nz1 : forall E X, 1 <= bv_unsigned (edenot E X) ->
    branch_taken BC_NE (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU X (ELit 1)))) (edenot E (ELit 0)) = true.
  Proof.
    intros E X HX.
    cbn [edenot branch_taken].
    rewrite bv_eqb_Z, u_xor64, u_sltu64.
    change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    destruct (Z.ltb_spec (bv_unsigned (edenot E X)) 1); [lia|].
    reflexivity.
  Qed.

  Lemma w4f_srl58 : forall E X, 0 <= bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58))) < 64.
  Proof.
    intros E X. pose proof (kx_srl_tl_gen E X (ELit 58) 6 ltac:(reflexivity) ltac:(lia)) as H.
    change (2 ^ 6) with 64 in H. exact H.
  Qed.

  Lemma w4f_ctz_acc : forall E X off, off = AW4_CTZ -> rng_aimg RNG ->
    accP RNG E ({| a_base := EAlu ALU_SRL X (ELit 58); a_off := off |}, 1%nat).
  Proof.
    intros E X off -> RI. pose proof (w4f_srl58 E X) as HS.
    unfold accP, adenot, PropExec.v_addi. cbn [fst snd a_base a_off].
    unfold AW4_CTZ in *.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    rewrite Z.mod_small by lia.
    destruct RI as (_ & _ & R). apply R; lia.
  Qed.

  Lemma w4f_ctz_rd : forall E X off m, off = AW4_CTZ -> ztab_fact bsegs m AW4_CTZ 64 1 [(0, 0, 63)] ->
    exists bs, rdn bsegs m (adenot E {| a_base := EAlu ALU_SRL X (ELit 58); a_off := off |}) 1 = Some bs.
  Proof.
    intros E X off m -> T. pose proof (w4f_srl58 E X) as HS.
    unfold adenot, PropExec.v_addi. cbn [a_base a_off].
    destruct (T (bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))+ AW4_CTZ) ltac:(lia) 0 63) as (b & Hb & _).
    { replace (bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58))) + AW4_CTZ - AW4_CTZ)
        with (bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))) by lia.
      rewrite Z.mod_1_r. reflexivity. }
    exists [b]. exact Hb.
  Qed.

  Definition w4hm (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word) (mm : amem) : Prop :=
    rw_cells bsegs mm (SP + -480) (w4fr w0 w8 w16 w24 w32)
    /\ rw_cells bsegs mm (SP + -376)
         (w4mid k a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3)
    /\ bytes_at bsegs mm SS (map (Z_to_bv 8) src)
    /\ unpoisoned mm SBL SBH /\ rng RNG (shad SBL) (shlen (SBH - SBL + 7)) /\ SBL mod 8 = 0 /\ 0 <= SBL
    /\ rng RNG SBL (SBH - SBL) /\ SBL <= SS /\ SS + n <= SBH
    /\ rng RNG SPF 480 /\ KXGoM.apart SS n SPF 480 /\ mem_inv bsegs mm
    /\ AIMG_HI <= SBL /\ SBH <= ATOP /\ AIMG_HI <= DT /\ DT <= ATOP /\ AIMG_HI <= DST /\ DST + dcap <= ATOP /\ ATOP + 4096 <= lo /\ lo + 8192 <= SP
    /\ SP <= 2^47 /\ ATOP_MIN + 12288 <= SP.

  Definition w4hs (k : nat) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word) (mm : amem)
      : machine_state :=
    MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 9)
            (Z_to_bv 64 (2^64 - DT - 5)) x18 x19 (Z_to_bv 64 (DST + Z.of_nat k * seg)) x21 x22 (Z_to_bv 64 (DT + 4))
            (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB) x27 x28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64))
       FR (Z_to_bv 64 AW4_F3) fc None mm (seg_rom bsegs).

  Definition w4kl (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 : Z) (mm : amem) : Prop :=
    forall (bc : Z) (x6 x7 x11 x12 x13 x14 x16 x28 : word), 0 <= bc <= 64 ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (w4se k)) (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 (DST + w4nth k o0 o1 o2 o3)) x6 x7
               (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 bc) (Z_to_bv 64 (SS + w4nth k i0 i1 i2 i3)) x11 x12 x13 x14
               (Z_to_bv 64 (Z.of_nat k)) x16 (Z_to_bv 64 (2^64 - DT - 5))
               (Z_to_bv 64 (w4se k - (DST + w4nth k o0 o1 o2 o3)))
               (Z_to_bv 64 SS) (Z_to_bv 64 (w4se k)) (Z_to_bv 64 (SP + -344 + 8 * Z.of_nat k))
               (Z_to_bv 64 (DST + w4nth k o0 o1 o2 o3)) (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 AW4_KSB) (Z_to_bv 64 (DST + w4nth k o0 o1 o2 o3 - (DST + w4nth k o0 o1 o2 o3)))
               (Z_to_bv 64 AW4_KTB) (Z_to_bv 64 (w4se k - 3))
               x28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64))
          FR (Z_to_bv 64 AW4_FL) fc None mm (seg_rom bsegs)).

  Definition w4ke (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 : Z) (mm : amem) : Prop :=
    forall (bc : Z) (x6 x7 x11 x12 x13 x14 x16 x22 x25 x27 x28 : word), 0 <= bc <= 64 ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (w4se k)) (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 (DST + w4nth k o0 o1 o2 o3)) x6 x7
               (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 bc) (Z_to_bv 64 (SS + w4nth k i0 i1 i2 i3)) x11 x12 x13 x14
               (Z_to_bv 64 (Z.of_nat k)) x16 (Z_to_bv 64 (2^64 - DT - 5)) (Z_to_bv 64 (w4se k - (DST + w4nth k o0 o1 o2 o3)))
               (Z_to_bv 64 SS) (Z_to_bv 64 (w4se k)) (Z_to_bv 64 (SP + -344 + 8 * Z.of_nat k)) x22 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB) x27 x28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64))
          FR (Z_to_bv 64 AW4_FE) fc None mm (seg_rom bsegs)).

  Definition w4kr (mm : amem) : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 AW4_FERR) fc None mm (seg_rom bsegs)).

  Ltac w4nat :=
    try change (Z.of_nat 0) with 0 in *; try change (Z.of_nat 1) with 1 in *;
    try change (Z.of_nat 2) with 2 in *; try change (Z.of_nat 3) with 3 in *.

  Ltac w4meq :=
    f_equal;
    try (lazymatch goal with |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => f_equal end);
    unfold AF_huf_w4fin.w4se, w4nth; cbn [nth Nat.ltb Nat.leb]; w4nat;
    lazymatch goal with
    | |- Z_to_bv 64 ?a = Z_to_bv 64 ?b => first [ reflexivity | f_equal; ring
        | f_equal; lazymatch goal with H : 4 * seg = dcap |- _ => clear - H; lia end | apply w4_bveq2; lia ]
    | |- Z_to_bv 64 ?a = ?w => apply Z_to_bv_bv_unsigned
    | |- _ => reflexivity
    end.

  Ltac w4clr :=
    repeat match goal with
    | H : rw_cells _ _ _ _ |- _ => clear H
    | H : bytes_at _ _ _ _ |- _ => clear H
    | H : rng _ _ _ |- _ => clear H
    | H : ztab_fact _ _ _ _ _ _ |- _ => clear H
    | H : KXGoM.apart _ _ _ _ |- _ => clear H
    | H : mem_inv _ _ |- _ => clear H
    end.

  Ltac w4brs :=
    lazymatch goal with
    | |- branch_taken _ _ _ = _ =>
        w4ez; unfold branch_taken; try unfold bv_lts;
        rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?zb_signed, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        try change (Z.of_N 64) with 64;
        rewrite ?Z.mod_small by lia;
        repeat match goal with |- context [if (?x <? ?y)%Z then _ else _] => destruct (Z.ltb_spec x y) end;
        repeat match goal with |- context [(?x <? ?y)%Z] => destruct (Z.ltb_spec x y) end;
        repeat match goal with |- context [(?x =? ?y)%Z] => destruct (Z.eqb_spec x y) end;
        cbn [negb]; first [reflexivity | exfalso; lia]
    end.

  Ltac w4bc :=
    lazymatch goal with |- context [bv_unsigned (ev ?E ?j)] => let H := fresh "HB" in kx_range (EVar j) H;
      first [clear - H; lia | lia] end.

  Ltac w4fit K := eapply w4_evtF_eq; [eapply K | w4meq]; try w4bc.

  Lemma w4_cb_of : forall m A cs, rw_cells bsegs m A cs -> rw_cells bsegs m A [CB (cells_size cs) (cells_bytes cs)].
  Proof.
    intros m A cs [[WF BA] WR]. split; [split|].
    - cbn [cells_wf cell_wf]. split; [apply cells_bytes_length; exact WF | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BA.
    - cbn [cells_size csize]. rewrite Nat.add_0_r. exact WR.
  Qed.

  Lemma w4_of_cb : forall m A cs bs, rw_cells bsegs m A [CB (cells_size cs) bs] -> bs = cells_bytes cs -> cells_wf cs ->
    rw_cells bsegs m A cs.
  Proof.
    intros m A cs bs [[_ BA] WR] E WF. subst bs. split; [split|]; [exact WF | |].
    - cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. exact BA.
    - cbn [cells_size csize] in WR. rewrite Nat.add_0_r in WR. exact WR.
  Qed.

  Lemma w4f_aheap : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> AHEAP AI L RNG st LB mm.
  Proof using All.
    intros mm MU WM. pose proof (AI_layout AI L RNG st LB m0 AH) as HL. unfold HUF_DEC_STACK_A in LOS.
    eapply (AI_frame AI); [exact AH | exact MU | exact WM |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; unfold aclient_range, aclient_app_range.
    - left. left. lia.
    - right. left. exists (HB pb DST dcap). split; [exact HDB|]. cbn. lia.
  Qed.

  Lemma w4f_appW : appW DW.
  Proof using All.
    pose proof w4f_lay as LY.
    destruct (AI_block AI L RNG st LB m0 pb DST dcap AH HDB) as (_ & (AB & _) & _).
    pose proof (ablk_app_blk _ _ AB ltac:(lia)) as AP. unfold app_blk in AP.
    unfold appW. apply Forall_cons; [cbv beta; cbn [fst snd]; lia |].
    apply Forall_cons; [cbv beta; cbn [fst snd]; lia | apply Forall_nil].
  Qed.

  Lemma w4f_mc : forall (A : Z) (mm m' : amem) (fr pre d s post l256 l296 l336 : list cell),
    W4FX mm fr (pre ++ d ++ post) l256 l296 l336 -> 0 < n ->
    A = SPF + 104 + Z.of_nat (cells_size pre) -> (cells_size pre + 32 <= 152)%nat ->
    cells_size d = 32%nat -> cells_size s = 32%nat -> cells_wf s ->
    munch [(SPF - 2224, SPF); (A, A + 32)] mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' -> stk bsegs m' lo SPF ->
    rw_cells bsegs m' A [CB 32 (cells_bytes s)] ->
    W4FX m' fr (pre ++ s ++ post) l256 l296 l336.
  Proof using All.
    intros A mm m' fr pre d s post l256 l296 l336 HW HN HA Hpre Hd Hs WFs MU WM MI ST RW.
    pose proof w4f_lay as LY. pose proof w4f_dtl as DL. pose proof (w4f_unp _ _ _ _ _ _ HW HN) as U.
    destruct U as ((_ & _ & _ & _ & _ & U6 & U7 & _) & _ & _ & _ & _ & _ & _ & U11 & U12 & U13 & U14 & U15 & U16 & U17 & U18 & U19 & _).
    destruct HW as ((buf & OUT & LBF) & BSS & BDT4 & BDT & _ & F0 & S0 & F1 & S1 & F2 & S2 & F3 & S3 & F4 & S4 & FRC & _ & MUD & WMD).
    assert (LC : zlen cbs = 4096) by (rewrite LCB, TL11; reflexivity).
    apply (proj1 (kx_rw_cells_app bsegs mm _ pre (d ++ post))) in F1. destruct F1 as [Fpre F1].
    apply (proj1 (kx_rw_cells_app bsegs mm _ d post)) in F1. destruct F1 as [_ Fpost].
    rewrite Hd in Fpost.
    assert (Sp : (cells_size pre + cells_size post = 120)%nat).
    { rewrite !cells_size_app in S1. lia. }
    assert (Snew : rw_cells bsegs m' (SPF + 104) (pre ++ s ++ post)).
    { apply (proj2 (kx_rw_cells_app bsegs m' _ pre (s ++ post))). split.
      - eapply rw_cells_transport; [exact Fpre | exact MU | exact WM |]. cbn [disjoint_from]. lia.
      - apply (proj2 (kx_rw_cells_app bsegs m' _ s post)). split.
        + rewrite <- HA. eapply w4_of_cb; [rewrite Hs; exact RW | reflexivity | exact WFs].
        + rewrite Hs. eapply rw_cells_transport; [exact Fpost | exact MU | exact WM |]. cbn [disjoint_from]. lia. }
    refine (conj _ (conj _ (conj _ (conj _ (conj ST (conj _ (conj S0 (conj Snew (conj _ (conj _ (conj S2 (conj _ (conj S3
      (conj _ (conj S4 (conj _ (conj MI (conj _ _)))))))))))))))))).
    - exists buf. split; [|exact LBF]. eapply u8arr_transport; [exact OUT | exact MU | exact WM |].
      rewrite length_map. cbn [disjoint_from]. lia.
    - eapply bytes_at_transport; [exact BSS | exact MU |]. rewrite length_map. cbn [disjoint_from]. lia.
    - eapply bytes_at_transport; [exact BDT4 | exact MU |]. cbn [disjoint_from]. lia.
    - eapply bytes_at_transport; [exact BDT | exact MU |]. cbn [disjoint_from length]. lia.
    - eapply rw_cells_transport; [exact F0 | exact MU | exact WM |]. rewrite S0. cbn [disjoint_from]. lia.
    - rewrite !cells_size_app in *. lia.
    - eapply rw_cells_transport; [exact F2 | exact MU | exact WM |]. rewrite S2. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact F3 | exact MU | exact WM |]. rewrite S3. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact F4 | exact MU | exact WM |]. rewrite S4. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact FRC | exact MU | exact WM |]. cbn [disjoint_from cells_size csize]. lia.
    - eapply munch_trans; [exact MUD |]. eapply munch_weaken; [| exact MU].
      intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (H1 & H2 & _).
      split; [|split; [|exact I]]; intro Hc; apply H1; lia.
    - eapply wmono_trans; [exact WMD | exact WM].
  Qed.

  Lemma w4f_mcstep : forall (A S : Z) (mm : amem) (fr pre d s post l256 l296 l336 : list cell)
      (xra t0 t1 t2 y8 y9 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6 : word),
    W4FX mm fr (pre ++ d ++ post) l256 l296 l336 -> 0 < n ->
    A = SPF + 104 + Z.of_nat (cells_size pre) -> (cells_size pre + 32 <= 152)%nat ->
    cells_size d = 32%nat -> cells_size s = 32%nat -> cells_wf s ->
    bytes_at bsegs mm S (cells_bytes s) -> SPF + 256 <= S -> S + 32 <= SP + -104 ->
    (forall (m' : amem) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
       W4FX m' fr (pre ++ s ++ post) l256 l296 l336 ->
       evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPF) gp tp u0 u1 u2 y8 y9 (Z_to_bv 64 A) b1 b2 b3 b4 b5 b6 b7
                               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 u3 u4 u5 u6) FR (ret_pc xra) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPF) gp tp t0 t1 t2 y8 y9 (Z_to_bv 64 A) (Z_to_bv 64 S) (Z_to_bv 64 32)
                             a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6)
                        FR (Z_to_bv 64 0x510d8) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros A S mm fr pre d s post l256 l296 l336 xra t0 t1 t2 y8 y9 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
      t3 t4 t5 t6 HW HN HA Hpre Hd Hs WFs BS HS1 HS2 K.
    pose proof w4f_lay as LY. pose proof (AI_layout AI L RNG st LB m0 AH) as HLY.
    pose proof HW as HW'.
    destruct HW' as (_ & _ & _ & _ & ST & _ & _ & F1 & S1 & _ & _ & _ & _ & _ & _ & _ & MI & MUD & WMD).
    pose proof (w4f_aheap mm MUD WMD) as AHm.
    destruct (fse_rt_of_aheap AI L RNG st LB mm AHm) as (R1 & R2 & R3 & R4 & _ & R6 & R7).
    pose proof (rclean_transport DW m0 mm rstk RCL MUD WMD w4f_appW) as RC.
    pose proof (rclean_shclean _ _ RC) as SHC.
    pose proof (shclean_hull _ _ _ _ _ SHC) as HU. pose proof (shclean_unpoisoned _ _ _ _ _ SHC) as UZ.
    pose proof (shclean_wr _ _ _ _ _ SHC) as WRS. pose proof (shclean_app_blk _ _ _ _ _ SHC) as APB.
    unfold rrng in RRS.
    apply (proj1 (kx_rw_cells_app bsegs mm _ pre (d ++ post))) in F1. destruct F1 as [_ F1].
    apply (proj1 (kx_rw_cells_app bsegs mm _ d post)) in F1. destruct F1 as [Fd _].
    pose proof (w4_cb_of _ _ _ Fd) as FdC. rewrite Hd, <- HA in FdC.
    eapply evtF_cut.
    { eapply (amemcpy_specZ A S 32 SPF RNG xra gp tp t0 t1 t2 y8 y9 (Z_to_bv 64 A) (Z_to_bv 64 S) (Z_to_bv 64 32)
               a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6 FR fc mm lo (cells_bytes s)
               (cells_bytes d) (r_rlo rstk) (r_rhi rstk) (r_rlo rstk) (r_rhi rstk)).
      all: first [ exact MI | exact ST | exact BS | exact FdC | exact WIM | exact RRS | exact WRS | exact R1 | exact R2
                 | exact R3 | exact R4 | exact R6 | exact R7 | reflexivity
                 | (rewrite (cells_bytes_length s WFs), Hs; reflexivity)
                 | (eapply app_blk_sub; [exact APB | lia | lia | lia])
                 | (eapply unpoisoned_sub; [exact UZ | lia | lia])
                 | (eapply rng_sub; [exact WSK | lia | lia])
                 | (unfold KHIGH in *; lia) | lia ]. }
    intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & EQ & MU1 & WM1 & MI1 & ST1 & RW1 & BS1).
    subst ms'. apply K.
    eapply w4f_mc; [exact HW | exact HN | exact HA | exact Hpre | exact Hd | exact Hs | exact WFs | exact MU1 | exact WM1
                   | exact MI1 | exact ST1 | exact RW1].
  Qed.

  Lemma w4f_h0nA : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 0 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (w4se 0 < (DST + w4nth 0 o0 o1 o2 o3)) -> w4kr mm ->
    evtF bsegs RNG POST (w4hs 0 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat.
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c0 < 2^64) by (pose proof (bv_unsigned_in_range 64 c0) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c0) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 0) with 0. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J5 J6 J7 J8 J9 J10 J11 J12 J13 J14 J15 J16 J17 J18 J19 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-376) | constr_eq o (-344) | constr_eq o (-312) | constr_eq o (-272) | constr_eq o (-256)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h0nA".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i0 0 (2^26); KZRange (n - i0) 8 (2^26); KZRange o0 0 (2^32); KZRange (dcap - o0) 0 (2^32);
         KZRange e0 6 (2^26); KZRange (n - e0) 0 (2^26); KZRange (bv_unsigned c0) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -376) 8 (SS + i0); KZWord (SP + -344) 8 (DST + o0); KZWord (SP + -312) 8 (bv_unsigned c0);
         KZWord (SP + -272) 8 SS; KZWord (SP + -256) 8 (SS + e0);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h0nB : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 0 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> ((DST + w4nth 0 o0 o1 o2 o3) <= w4se 0 /\ (w4nth 0 i0 i1 i2 i3) < (w4nth 0 e0 e1 e2 e3) - 8) -> w4kr mm ->
    evtF bsegs RNG POST (w4hs 0 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c0 < 2^64) by (pose proof (bv_unsigned_in_range 64 c0) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c0) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 0) with 0. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J5 J6 J7 J8 J9 J10 J11 J12 J13 J14 J15 J16 J17 J18 J19 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-376) | constr_eq o (-344) | constr_eq o (-312) | constr_eq o (-272) | constr_eq o (-256)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h0nB".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: false :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i0 0 (2^26); KZRange (n - i0) 8 (2^26); KZRange o0 0 (2^32); KZRange (dcap - o0) 0 (2^32);
         KZRange e0 6 (2^26); KZRange (n - e0) 0 (2^26); KZRange (bv_unsigned c0) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -376) 8 (SS + i0); KZWord (SP + -344) 8 (DST + o0); KZWord (SP + -312) 8 (bv_unsigned c0);
         KZWord (SP + -272) 8 SS; KZWord (SP + -256) 8 (SS + e0);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h0nC : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 0 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> ((DST + w4nth 0 o0 o1 o2 o3) <= w4se 0 /\ (w4nth 0 e0 e1 e2 e3) - 8 <= (w4nth 0 i0 i1 i2 i3) /\ w4se 0 - (DST + w4nth 0 o0 o1 o2 o3) < 4) -> w4ke 0 i0 i1 i2 i3 o0 o1 o2 o3 mm ->
    evtF bsegs RNG POST (w4hs 0 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2 & HC3).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c0 < 2^64) by (pose proof (bv_unsigned_in_range 64 c0) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c0) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 0) with 0. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J5 J6 J7 J8 J9 J10 J11 J12 J13 J14 J15 J16 J17 J18 J19 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-376) | constr_eq o (-344) | constr_eq o (-312) | constr_eq o (-272) | constr_eq o (-256)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h0nC".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: false :: false :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i0 0 (2^26); KZRange (n - i0) 8 (2^26); KZRange o0 0 (2^32); KZRange (dcap - o0) 0 (2^32);
         KZRange e0 6 (2^26); KZRange (n - e0) 0 (2^26); KZRange (bv_unsigned c0) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -376) 8 (SS + i0); KZWord (SP + -344) 8 (DST + o0); KZWord (SP + -312) 8 (bv_unsigned c0);
         KZWord (SP + -272) 8 SS; KZWord (SP + -256) 8 (SS + e0);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h0nD : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 0 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> ((DST + w4nth 0 o0 o1 o2 o3) <= w4se 0 /\ (w4nth 0 e0 e1 e2 e3) - 8 <= (w4nth 0 i0 i1 i2 i3) /\ 4 <= w4se 0 - (DST + w4nth 0 o0 o1 o2 o3)) -> w4kl 0 i0 i1 i2 i3 o0 o1 o2 o3 mm ->
    evtF bsegs RNG POST (w4hs 0 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2 & HC3).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c0 < 2^64) by (pose proof (bv_unsigned_in_range 64 c0) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c0) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 0) with 0. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J5 J6 J7 J8 J9 J10 J11 J12 J13 J14 J15 J16 J17 J18 J19 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-376) | constr_eq o (-344) | constr_eq o (-312) | constr_eq o (-272) | constr_eq o (-256)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h0nD".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: false :: false :: false :: true :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i0 0 (2^26); KZRange (n - i0) 8 (2^26); KZRange o0 0 (2^32); KZRange (dcap - o0) 0 (2^32);
         KZRange e0 6 (2^26); KZRange (n - e0) 0 (2^26); KZRange (bv_unsigned c0) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -376) 8 (SS + i0); KZWord (SP + -344) 8 (DST + o0); KZWord (SP + -312) 8 (bv_unsigned c0);
         KZWord (SP + -272) 8 SS; KZWord (SP + -256) 8 (SS + e0);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h1nA : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 1 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (w4se 1 < (DST + w4nth 1 o0 o1 o2 o3)) -> w4kr mm ->
    evtF bsegs RNG POST (w4hs 1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat.
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c1 < 2^64) by (pose proof (bv_unsigned_in_range 64 c1) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c1) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 1) with 1. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J10 J11 J12 J13 J14 J15 J16 J17 J18 J19 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-368) | constr_eq o (-336) | constr_eq o (-304) | constr_eq o (-272) | constr_eq o (-248)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h1nA".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i1 0 (2^26); KZRange (n - i1) 8 (2^26); KZRange o1 0 (2^32); KZRange (dcap - o1) 0 (2^32);
         KZRange e1 6 (2^26); KZRange (n - e1) 0 (2^26); KZRange (bv_unsigned c1) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -368) 8 (SS + i1); KZWord (SP + -336) 8 (DST + o1); KZWord (SP + -304) 8 (bv_unsigned c1);
         KZWord (SP + -272) 8 SS; KZWord (SP + -248) 8 (SS + e1);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h1nB : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 1 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> ((DST + w4nth 1 o0 o1 o2 o3) <= w4se 1 /\ (w4nth 1 i0 i1 i2 i3) < (w4nth 1 e0 e1 e2 e3) - 8) -> w4kr mm ->
    evtF bsegs RNG POST (w4hs 1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c1 < 2^64) by (pose proof (bv_unsigned_in_range 64 c1) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c1) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 1) with 1. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J10 J11 J12 J13 J14 J15 J16 J17 J18 J19 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-368) | constr_eq o (-336) | constr_eq o (-304) | constr_eq o (-272) | constr_eq o (-248)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h1nB".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: false :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i1 0 (2^26); KZRange (n - i1) 8 (2^26); KZRange o1 0 (2^32); KZRange (dcap - o1) 0 (2^32);
         KZRange e1 6 (2^26); KZRange (n - e1) 0 (2^26); KZRange (bv_unsigned c1) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -368) 8 (SS + i1); KZWord (SP + -336) 8 (DST + o1); KZWord (SP + -304) 8 (bv_unsigned c1);
         KZWord (SP + -272) 8 SS; KZWord (SP + -248) 8 (SS + e1);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h1nC : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 1 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> ((DST + w4nth 1 o0 o1 o2 o3) <= w4se 1 /\ (w4nth 1 e0 e1 e2 e3) - 8 <= (w4nth 1 i0 i1 i2 i3) /\ w4se 1 - (DST + w4nth 1 o0 o1 o2 o3) < 4) -> w4ke 1 i0 i1 i2 i3 o0 o1 o2 o3 mm ->
    evtF bsegs RNG POST (w4hs 1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2 & HC3).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c1 < 2^64) by (pose proof (bv_unsigned_in_range 64 c1) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c1) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 1) with 1. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J10 J11 J12 J13 J14 J15 J16 J17 J18 J19 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-368) | constr_eq o (-336) | constr_eq o (-304) | constr_eq o (-272) | constr_eq o (-248)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h1nC".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: false :: false :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i1 0 (2^26); KZRange (n - i1) 8 (2^26); KZRange o1 0 (2^32); KZRange (dcap - o1) 0 (2^32);
         KZRange e1 6 (2^26); KZRange (n - e1) 0 (2^26); KZRange (bv_unsigned c1) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -368) 8 (SS + i1); KZWord (SP + -336) 8 (DST + o1); KZWord (SP + -304) 8 (bv_unsigned c1);
         KZWord (SP + -272) 8 SS; KZWord (SP + -248) 8 (SS + e1);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h1nD : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 1 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> ((DST + w4nth 1 o0 o1 o2 o3) <= w4se 1 /\ (w4nth 1 e0 e1 e2 e3) - 8 <= (w4nth 1 i0 i1 i2 i3) /\ 4 <= w4se 1 - (DST + w4nth 1 o0 o1 o2 o3)) -> w4kl 1 i0 i1 i2 i3 o0 o1 o2 o3 mm ->
    evtF bsegs RNG POST (w4hs 1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2 & HC3).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c1 < 2^64) by (pose proof (bv_unsigned_in_range 64 c1) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c1) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 1) with 1. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J10 J11 J12 J13 J14 J15 J16 J17 J18 J19 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-368) | constr_eq o (-336) | constr_eq o (-304) | constr_eq o (-272) | constr_eq o (-248)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h1nD".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: false :: false :: false :: true :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i1 0 (2^26); KZRange (n - i1) 8 (2^26); KZRange o1 0 (2^32); KZRange (dcap - o1) 0 (2^32);
         KZRange e1 6 (2^26); KZRange (n - e1) 0 (2^26); KZRange (bv_unsigned c1) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -368) 8 (SS + i1); KZWord (SP + -336) 8 (DST + o1); KZWord (SP + -304) 8 (bv_unsigned c1);
         KZWord (SP + -272) 8 SS; KZWord (SP + -248) 8 (SS + e1);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h2nA : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 2 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (w4se 2 < (DST + w4nth 2 o0 o1 o2 o3)) -> w4kr mm ->
    evtF bsegs RNG POST (w4hs 2 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat.
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c2 < 2^64) by (pose proof (bv_unsigned_in_range 64 c2) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c2) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 2) with 2. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J15 J16 J17 J18 J19 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-360) | constr_eq o (-328) | constr_eq o (-296) | constr_eq o (-272) | constr_eq o (-240)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h2nA".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i2 0 (2^26); KZRange (n - i2) 8 (2^26); KZRange o2 0 (2^32); KZRange (dcap - o2) 0 (2^32);
         KZRange e2 6 (2^26); KZRange (n - e2) 0 (2^26); KZRange (bv_unsigned c2) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -360) 8 (SS + i2); KZWord (SP + -328) 8 (DST + o2); KZWord (SP + -296) 8 (bv_unsigned c2);
         KZWord (SP + -272) 8 SS; KZWord (SP + -240) 8 (SS + e2);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h2nB : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 2 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> ((DST + w4nth 2 o0 o1 o2 o3) <= w4se 2 /\ (w4nth 2 i0 i1 i2 i3) < (w4nth 2 e0 e1 e2 e3) - 8) -> w4kr mm ->
    evtF bsegs RNG POST (w4hs 2 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c2 < 2^64) by (pose proof (bv_unsigned_in_range 64 c2) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c2) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 2) with 2. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J15 J16 J17 J18 J19 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-360) | constr_eq o (-328) | constr_eq o (-296) | constr_eq o (-272) | constr_eq o (-240)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h2nB".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: false :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i2 0 (2^26); KZRange (n - i2) 8 (2^26); KZRange o2 0 (2^32); KZRange (dcap - o2) 0 (2^32);
         KZRange e2 6 (2^26); KZRange (n - e2) 0 (2^26); KZRange (bv_unsigned c2) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -360) 8 (SS + i2); KZWord (SP + -328) 8 (DST + o2); KZWord (SP + -296) 8 (bv_unsigned c2);
         KZWord (SP + -272) 8 SS; KZWord (SP + -240) 8 (SS + e2);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h2nC : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 2 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> ((DST + w4nth 2 o0 o1 o2 o3) <= w4se 2 /\ (w4nth 2 e0 e1 e2 e3) - 8 <= (w4nth 2 i0 i1 i2 i3) /\ w4se 2 - (DST + w4nth 2 o0 o1 o2 o3) < 4) -> w4ke 2 i0 i1 i2 i3 o0 o1 o2 o3 mm ->
    evtF bsegs RNG POST (w4hs 2 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2 & HC3).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c2 < 2^64) by (pose proof (bv_unsigned_in_range 64 c2) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c2) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 2) with 2. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J15 J16 J17 J18 J19 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-360) | constr_eq o (-328) | constr_eq o (-296) | constr_eq o (-272) | constr_eq o (-240)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h2nC".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: false :: false :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i2 0 (2^26); KZRange (n - i2) 8 (2^26); KZRange o2 0 (2^32); KZRange (dcap - o2) 0 (2^32);
         KZRange e2 6 (2^26); KZRange (n - e2) 0 (2^26); KZRange (bv_unsigned c2) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -360) 8 (SS + i2); KZWord (SP + -328) 8 (DST + o2); KZWord (SP + -296) 8 (bv_unsigned c2);
         KZWord (SP + -272) 8 SS; KZWord (SP + -240) 8 (SS + e2);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h2nD : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 2 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> ((DST + w4nth 2 o0 o1 o2 o3) <= w4se 2 /\ (w4nth 2 e0 e1 e2 e3) - 8 <= (w4nth 2 i0 i1 i2 i3) /\ 4 <= w4se 2 - (DST + w4nth 2 o0 o1 o2 o3)) -> w4kl 2 i0 i1 i2 i3 o0 o1 o2 o3 mm ->
    evtF bsegs RNG POST (w4hs 2 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2 & HC3).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c2 < 2^64) by (pose proof (bv_unsigned_in_range 64 c2) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c2) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 2) with 2. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J15 J16 J17 J18 J19 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-360) | constr_eq o (-328) | constr_eq o (-296) | constr_eq o (-272) | constr_eq o (-240)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h2nD".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: false :: false :: false :: true :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i2 0 (2^26); KZRange (n - i2) 8 (2^26); KZRange o2 0 (2^32); KZRange (dcap - o2) 0 (2^32);
         KZRange e2 6 (2^26); KZRange (n - e2) 0 (2^26); KZRange (bv_unsigned c2) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -360) 8 (SS + i2); KZWord (SP + -328) 8 (DST + o2); KZWord (SP + -296) 8 (bv_unsigned c2);
         KZWord (SP + -272) 8 SS; KZWord (SP + -240) 8 (SS + e2);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h3XA : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> seg <= dcap - 3 * seg -> (w4se 3 < (DST + w4nth 3 o0 o1 o2 o3)) -> w4kr mm ->
    evtF bsegs RNG POST (w4hs 3 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HX HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat.
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c3 < 2^64) by (pose proof (bv_unsigned_in_range 64 c3) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c3) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 3) with 3. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 J11 J12 J13 J14 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-352) | constr_eq o (-320) | constr_eq o (-288) | constr_eq o (-272) | constr_eq o (-232)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h3XA".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i3 0 (2^26); KZRange (n - i3) 8 (2^26); KZRange o3 0 (2^32); KZRange (dcap - o3) 0 (2^32);
         KZRange e3 6 (2^26); KZRange (n - e3) 0 (2^26); KZRange (bv_unsigned c3) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -352) 8 (SS + i3); KZWord (SP + -320) 8 (DST + o3); KZWord (SP + -288) 8 (bv_unsigned c3);
         KZWord (SP + -272) 8 SS; KZWord (SP + -232) 8 (SS + e3);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    all: assert (HE4 : 4 * seg = dcap) by (clear - HX HSG; lia).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h3XB : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> seg <= dcap - 3 * seg -> ((DST + w4nth 3 o0 o1 o2 o3) <= w4se 3 /\ (w4nth 3 i0 i1 i2 i3) < (w4nth 3 e0 e1 e2 e3) - 8) -> w4kr mm ->
    evtF bsegs RNG POST (w4hs 3 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HX HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c3 < 2^64) by (pose proof (bv_unsigned_in_range 64 c3) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c3) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 3) with 3. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 J11 J12 J13 J14 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-352) | constr_eq o (-320) | constr_eq o (-288) | constr_eq o (-272) | constr_eq o (-232)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h3XB".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: false :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i3 0 (2^26); KZRange (n - i3) 8 (2^26); KZRange o3 0 (2^32); KZRange (dcap - o3) 0 (2^32);
         KZRange e3 6 (2^26); KZRange (n - e3) 0 (2^26); KZRange (bv_unsigned c3) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -352) 8 (SS + i3); KZWord (SP + -320) 8 (DST + o3); KZWord (SP + -288) 8 (bv_unsigned c3);
         KZWord (SP + -272) 8 SS; KZWord (SP + -232) 8 (SS + e3);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    all: assert (HE4 : 4 * seg = dcap) by (clear - HX HSG; lia).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h3XC : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> seg <= dcap - 3 * seg -> ((DST + w4nth 3 o0 o1 o2 o3) <= w4se 3 /\ (w4nth 3 e0 e1 e2 e3) - 8 <= (w4nth 3 i0 i1 i2 i3) /\ w4se 3 - (DST + w4nth 3 o0 o1 o2 o3) < 4) -> w4ke 3 i0 i1 i2 i3 o0 o1 o2 o3 mm ->
    evtF bsegs RNG POST (w4hs 3 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HX HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2 & HC3).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c3 < 2^64) by (pose proof (bv_unsigned_in_range 64 c3) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c3) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 3) with 3. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 J11 J12 J13 J14 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-352) | constr_eq o (-320) | constr_eq o (-288) | constr_eq o (-272) | constr_eq o (-232)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h3XC".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: false :: false :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i3 0 (2^26); KZRange (n - i3) 8 (2^26); KZRange o3 0 (2^32); KZRange (dcap - o3) 0 (2^32);
         KZRange e3 6 (2^26); KZRange (n - e3) 0 (2^26); KZRange (bv_unsigned c3) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -352) 8 (SS + i3); KZWord (SP + -320) 8 (DST + o3); KZWord (SP + -288) 8 (bv_unsigned c3);
         KZWord (SP + -272) 8 SS; KZWord (SP + -232) 8 (SS + e3);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    all: assert (HE4 : 4 * seg = dcap) by (clear - HX HSG; lia).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h3XD : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> seg <= dcap - 3 * seg -> ((DST + w4nth 3 o0 o1 o2 o3) <= w4se 3 /\ (w4nth 3 e0 e1 e2 e3) - 8 <= (w4nth 3 i0 i1 i2 i3) /\ 4 <= w4se 3 - (DST + w4nth 3 o0 o1 o2 o3)) -> w4kl 3 i0 i1 i2 i3 o0 o1 o2 o3 mm ->
    evtF bsegs RNG POST (w4hs 3 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HX HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2 & HC3).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c3 < 2^64) by (pose proof (bv_unsigned_in_range 64 c3) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c3) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 3) with 3. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 J11 J12 J13 J14 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-352) | constr_eq o (-320) | constr_eq o (-288) | constr_eq o (-272) | constr_eq o (-232)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h3XD".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (false :: false :: false :: false :: true :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i3 0 (2^26); KZRange (n - i3) 8 (2^26); KZRange o3 0 (2^32); KZRange (dcap - o3) 0 (2^32);
         KZRange e3 6 (2^26); KZRange (n - e3) 0 (2^26); KZRange (bv_unsigned c3) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -352) 8 (SS + i3); KZWord (SP + -320) 8 (DST + o3); KZWord (SP + -288) 8 (bv_unsigned c3);
         KZWord (SP + -272) 8 SS; KZWord (SP + -232) 8 (SS + e3);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    all: assert (HE4 : 4 * seg = dcap) by (clear - HX HSG; lia).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h3YA : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> dcap - 3 * seg < seg -> (w4se 3 < (DST + w4nth 3 o0 o1 o2 o3)) -> w4kr mm ->
    evtF bsegs RNG POST (w4hs 3 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HX HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat.
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c3 < 2^64) by (pose proof (bv_unsigned_in_range 64 c3) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c3) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 3) with 3. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 J11 J12 J13 J14 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-352) | constr_eq o (-320) | constr_eq o (-288) | constr_eq o (-272) | constr_eq o (-232)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h3YA".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (true :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i3 0 (2^26); KZRange (n - i3) 8 (2^26); KZRange o3 0 (2^32); KZRange (dcap - o3) 0 (2^32);
         KZRange e3 6 (2^26); KZRange (n - e3) 0 (2^26); KZRange (bv_unsigned c3) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -352) 8 (SS + i3); KZWord (SP + -320) 8 (DST + o3); KZWord (SP + -288) 8 (bv_unsigned c3);
         KZWord (SP + -272) 8 SS; KZWord (SP + -232) 8 (SS + e3);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h3YB : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> dcap - 3 * seg < seg -> ((DST + w4nth 3 o0 o1 o2 o3) <= w4se 3 /\ (w4nth 3 i0 i1 i2 i3) < (w4nth 3 e0 e1 e2 e3) - 8) -> w4kr mm ->
    evtF bsegs RNG POST (w4hs 3 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HX HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c3 < 2^64) by (pose proof (bv_unsigned_in_range 64 c3) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c3) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 3) with 3. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 J11 J12 J13 J14 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-352) | constr_eq o (-320) | constr_eq o (-288) | constr_eq o (-272) | constr_eq o (-232)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h3YB".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (true :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i3 0 (2^26); KZRange (n - i3) 8 (2^26); KZRange o3 0 (2^32); KZRange (dcap - o3) 0 (2^32);
         KZRange e3 6 (2^26); KZRange (n - e3) 0 (2^26); KZRange (bv_unsigned c3) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -352) 8 (SS + i3); KZWord (SP + -320) 8 (DST + o3); KZWord (SP + -288) 8 (bv_unsigned c3);
         KZWord (SP + -272) 8 SS; KZWord (SP + -232) 8 (SS + e3);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h3YC : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> dcap - 3 * seg < seg -> ((DST + w4nth 3 o0 o1 o2 o3) <= w4se 3 /\ (w4nth 3 e0 e1 e2 e3) - 8 <= (w4nth 3 i0 i1 i2 i3) /\ w4se 3 - (DST + w4nth 3 o0 o1 o2 o3) < 4) -> w4ke 3 i0 i1 i2 i3 o0 o1 o2 o3 mm ->
    evtF bsegs RNG POST (w4hs 3 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HX HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2 & HC3).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c3 < 2^64) by (pose proof (bv_unsigned_in_range 64 c3) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c3) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 3) with 3. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 J11 J12 J13 J14 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-352) | constr_eq o (-320) | constr_eq o (-288) | constr_eq o (-272) | constr_eq o (-232)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h3YC".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (true :: false :: true :: false :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i3 0 (2^26); KZRange (n - i3) 8 (2^26); KZRange o3 0 (2^32); KZRange (dcap - o3) 0 (2^32);
         KZRange e3 6 (2^26); KZRange (n - e3) 0 (2^26); KZRange (bv_unsigned c3) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -352) 8 (SS + i3); KZWord (SP + -320) 8 (DST + o3); KZWord (SP + -288) 8 (bv_unsigned c3);
         KZWord (SP + -272) 8 SS; KZWord (SP + -232) 8 (SS + e3);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_h3YD : forall (mm : amem) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    w4hm 3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm -> W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> dcap - 3 * seg < seg -> ((DST + w4nth 3 o0 o1 o2 o3) <= w4se 3 /\ (w4nth 3 e0 e1 e2 e3) - 8 <= (w4nth 3 i0 i1 i2 i3) /\ 4 <= w4se 3 - (DST + w4nth 3 o0 o1 o2 o3)) -> w4kl 3 i0 i1 i2 i3 o0 o1 o2 o3 mm ->
    evtF bsegs RNG POST (w4hs 3 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 mm).
  Proof.
    intros mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HM HSR HX HC K.
    destruct HM as (HFR & HMD & HSB & HUB & HRSH & HA8 & HA0 & HRB & HBL & HBH & HRF & HAP & MI & L1 & L2 & L3 & L4 & L5 & L6
      & L7 & L8 & L9 & L10).
    unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR.
    destruct HSR as (HS3 & HN9 & (J0 & J1 & J2 & J3 & J4) & (J5 & J6 & J7 & J8 & J9) & (J10 & J11 & J12 & J13 & J14)
      & (J15 & J16 & J17 & J18 & J19)).
    unfold AF_huf_w4fin.w4se, w4nth in HC; cbn [nth Nat.ltb Nat.leb] in HC. w4nat. destruct HC as (HC1 & HC2 & HC3).
    unfold w4kr, w4ke, w4kl in K.
    assert (HSG : dcap <= 4 * seg <= dcap + 3) by (clear - DC; Z.div_mod_to_equations; lia).
    assert (HUS : unpoisoned mm SS (SS + n)) by (eapply unpoisoned_sub; [exact HUB | lia | lia]).
    assert (HRS : rng RNG SS n) by (eapply rng_sub; [exact HRB | lia | lia]).
    pose proof (w4f_ctz_tab mm MI) as CT. unfold AW4_CTZ in CT.
    assert (HCB : bv_unsigned c3 < 2^64) by (pose proof (bv_unsigned_in_range 64 c3) as [_ X]; exact X).
    unfold AF_huf_w4fin.w4fr, AW4_ST64 in HFR. unfold AF_huf_w4fin.w4mid, w4sel in HMD. cbn [firstn skipn map app] in HMD.
    rewrite <- (Z_to_bv_bv_unsigned c3) in HMD.
    unfold AIMG_HI in L1, L3, L5.
    unfold w4hs. change (Z.of_nat 3) with 3. unfold AW4_F3, AW4_KTB, AW4_KSB.
    assert (WR1 : wr_at bsegs mm (SP + -480) 104) by exact (proj2 HFR).
    assert (WR2 : wr_at bsegs mm (SP + -376) 152) by exact (proj2 HMD).
    clear J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 J11 J12 J13 J14 MTL TL11 TLM LCB SP16.
    kx_cells_split HFR. kx_cells_split HMD.
    repeat match goal with H : rw_cells bsegs mm (SP + ?o) [_] |- _ =>
      tryif first [constr_eq o (-416) | constr_eq o (-408) | constr_eq o (-400) | constr_eq o (-392) | constr_eq o (-384) | constr_eq o (-352) | constr_eq o (-320) | constr_eq o (-288) | constr_eq o (-272) | constr_eq o (-232)] then fail else clear H end.
    idtac "@@"; idtac "LEMMA w4f_h3YD".
    Time kx_runFmd [AW4_FL; AW4_FE; AW4_FERR] 120%nat (true :: false :: false :: false :: true :: true :: repeat false 16)
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47); KZRange DT 4096 (2^47); KZRange n 9 (2^26);
         KZRange i3 0 (2^26); KZRange (n - i3) 8 (2^26); KZRange o3 0 (2^32); KZRange (dcap - o3) 0 (2^32);
         KZRange e3 6 (2^26); KZRange (n - e3) 0 (2^26); KZRange (bv_unsigned c3) 1 (2^64 - 1);
         KZRange seg 1 (2^30);
         KZWord (SP + -352) 8 (SS + i3); KZWord (SP + -320) 8 (DST + o3); KZWord (SP + -288) 8 (bv_unsigned c3);
         KZWord (SP + -272) 8 SS; KZWord (SP + -232) 8 (SS + e3);
         KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWord (SP + -392) 8 (DST + dcap); KZWord (SP + -384) 8 seg;
         KZWr (SP + -480) 104; KZWr (SP + -376) 152;
         KZWord (SP + -416) 8 151050438420815295; KZImg 134547 (134547 + 64); KZTab 134547 64 1 [(0, 0, 63)];
         KZDisj SS n (SP + -480) 480]
      [(SS, n)] [(SP + -480, 480)] [(SS, n)].
    Time all: try w4br.
    Time all: try (lazymatch goal with |- branch_taken _ _ _ = _ => try clear K; w4clr; w4brs end).
    all: try (apply w4f_br_nz1; w4uz).
    all: try (kx_asan I).
    all: try (eapply w4f_ctz_acc; [reflexivity | exact WIM]).
    all: try (eapply w4f_ctz_rd; [reflexivity | exact CT]).
    all: try (lazymatch goal with |- context [edenot ?E _] => let v := eval unfold E in E in
           lazymatch v with kx_env (map (Z_to_bv 64) ?zv) _ => idtac "@@"; idtac "ATOMS"; idtac zv end end).
    Time all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    all: try (lazymatch goal with E := kx_env _ _ |- _ => clearbody E end).
    Time all: w4fit K.
  Time Qed.

  Lemma w4f_hm : forall (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word) (l256 l296 l336 : list cell) (mm : amem),
    W4FX mm (w4fr w0 w8 w16 w24 w32) (w4mid k a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3) l256 l296 l336 -> 0 < n ->
    w4hm k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm.
  Proof.
    intros k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew l256 l296 l336 mm HW HN.
    pose proof w4f_lay as LY. pose proof w4f_dtl as DL.
    pose proof (w4f_unp _ _ _ _ _ _ HW HN) as U.
    destruct HW as (_ & HB & _ & _ & _ & F0 & _ & F1 & _ & _ & _ & _ & _ & _ & _ & _ & MI & _ & _).
    destruct U as ((U1 & U2 & U3 & U4 & U5 & U6 & U7 & _) & (V1 & V2 & V3 & V4 & V5 & V6 & V7) & _ & U9 & U10 & _ & _
      & U11 & U12 & U13 & U14 & U15 & U16 & U17 & U18 & U19 & U20).
    replace (SP + -480 + 104) with (SP + -376) in F1 by lia.
    unfold w4hm.
    refine (conj F0 (conj F1 (conj HB (conj U1 (conj U2 (conj U3 (conj U4 (conj U5 (conj U6 (conj U7 (conj U9 (conj U10
      (conj MI (conj U11 (conj U12 (conj U13 (conj _ (conj U15 (conj U16 (conj U17 (conj U18 (conj U19
      _)))))))))))))))))))))); lia.
  Qed.

  Lemma w4f_head0 : forall (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word),
    W4KFE 0 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KERR ->
    (W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> forall (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word) (l256 l296 l336 : list cell),
       W4KFL 0 (w4se 0) (DST + w4nth 0 o0 o1 o2 o3) (w4fr w0 w8 w16 w24 w32)
         (w4mid 0 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3) l256 l296 l336) ->
    W4KF3 0 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    intros i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HE HR HL.
    intros mm w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew l256 l296 l336 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HW HSR HK.
    assert (HM : w4hm 0 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm) by (eapply w4f_hm; [exact HW | unfold AF_huf_w4fin.W4SR in HSR; lia]).
    destruct (Z_lt_ge_dec (w4se 0) (DST + w4nth 0 o0 o1 o2 o3)) as [CA | CA].
    { eapply (w4f_h0nA mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | lia | unfold w4kr; intros; eapply HR; exact HW]. }
    destruct (Z_lt_ge_dec (w4nth 0 i0 i1 i2 i3) ((w4nth 0 e0 e1 e2 e3) - 8)) as [CB | CB].
    { eapply (w4f_h0nB mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | lia | unfold w4kr; intros; eapply HR; exact HW]. }
    destruct (Z_lt_ge_dec (w4se 0 - (DST + w4nth 0 o0 o1 o2 o3)) 4) as [CC | CC].
    { eapply (w4f_h0nC mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | lia | ].
      unfold w4ke. intros bc y6 y7 y11 y12 y13 y14 y16 y22 y25 y27 y28 Hbc.
      eapply HE; [do 26 eexists; exact HW | exact HSR | exact HK | exact Hbc | lia]. }
    { eapply (w4f_h0nD mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | lia | ].
      unfold w4kl. intros bc y6 y7 y11 y12 y13 y14 y16 y28 Hbc.
      pose proof HSR as HSR'. unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR'.
      eapply (HL HSR w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew l256 l296 l336 mm (DST + w4nth 0 o0 o1 o2 o3) (w4nth 0 i0 i1 i2 i3) bc); [exact HW | exact HK | | | | | exact Hbc];
        unfold AF_huf_w4fin.w4se, w4nth in *; cbn [nth Nat.ltb Nat.leb] in *; w4nat; lia. }
  Qed.

  Lemma w4f_head1 : forall (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word),
    W4KFE 1 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KERR ->
    (W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> forall (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word) (l256 l296 l336 : list cell),
       W4KFL 1 (w4se 1) (DST + w4nth 1 o0 o1 o2 o3) (w4fr w0 w8 w16 w24 w32)
         (w4mid 1 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3) l256 l296 l336) ->
    W4KF3 1 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    intros i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HE HR HL.
    intros mm w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew l256 l296 l336 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HW HSR HK.
    assert (HM : w4hm 1 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm) by (eapply w4f_hm; [exact HW | unfold AF_huf_w4fin.W4SR in HSR; lia]).
    destruct (Z_lt_ge_dec (w4se 1) (DST + w4nth 1 o0 o1 o2 o3)) as [CA | CA].
    { eapply (w4f_h1nA mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | lia | unfold w4kr; intros; eapply HR; exact HW]. }
    destruct (Z_lt_ge_dec (w4nth 1 i0 i1 i2 i3) ((w4nth 1 e0 e1 e2 e3) - 8)) as [CB | CB].
    { eapply (w4f_h1nB mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | lia | unfold w4kr; intros; eapply HR; exact HW]. }
    destruct (Z_lt_ge_dec (w4se 1 - (DST + w4nth 1 o0 o1 o2 o3)) 4) as [CC | CC].
    { eapply (w4f_h1nC mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | lia | ].
      unfold w4ke. intros bc y6 y7 y11 y12 y13 y14 y16 y22 y25 y27 y28 Hbc.
      eapply HE; [do 26 eexists; exact HW | exact HSR | exact HK | exact Hbc | lia]. }
    { eapply (w4f_h1nD mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | lia | ].
      unfold w4kl. intros bc y6 y7 y11 y12 y13 y14 y16 y28 Hbc.
      pose proof HSR as HSR'. unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR'.
      eapply (HL HSR w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew l256 l296 l336 mm (DST + w4nth 1 o0 o1 o2 o3) (w4nth 1 i0 i1 i2 i3) bc); [exact HW | exact HK | | | | | exact Hbc];
        unfold AF_huf_w4fin.w4se, w4nth in *; cbn [nth Nat.ltb Nat.leb] in *; w4nat; lia. }
  Qed.

  Lemma w4f_head2 : forall (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word),
    W4KFE 2 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KERR ->
    (W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> forall (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word) (l256 l296 l336 : list cell),
       W4KFL 2 (w4se 2) (DST + w4nth 2 o0 o1 o2 o3) (w4fr w0 w8 w16 w24 w32)
         (w4mid 2 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3) l256 l296 l336) ->
    W4KF3 2 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    intros i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HE HR HL.
    intros mm w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew l256 l296 l336 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HW HSR HK.
    assert (HM : w4hm 2 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm) by (eapply w4f_hm; [exact HW | unfold AF_huf_w4fin.W4SR in HSR; lia]).
    destruct (Z_lt_ge_dec (w4se 2) (DST + w4nth 2 o0 o1 o2 o3)) as [CA | CA].
    { eapply (w4f_h2nA mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | lia | unfold w4kr; intros; eapply HR; exact HW]. }
    destruct (Z_lt_ge_dec (w4nth 2 i0 i1 i2 i3) ((w4nth 2 e0 e1 e2 e3) - 8)) as [CB | CB].
    { eapply (w4f_h2nB mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | lia | unfold w4kr; intros; eapply HR; exact HW]. }
    destruct (Z_lt_ge_dec (w4se 2 - (DST + w4nth 2 o0 o1 o2 o3)) 4) as [CC | CC].
    { eapply (w4f_h2nC mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | lia | ].
      unfold w4ke. intros bc y6 y7 y11 y12 y13 y14 y16 y22 y25 y27 y28 Hbc.
      eapply HE; [do 26 eexists; exact HW | exact HSR | exact HK | exact Hbc | lia]. }
    { eapply (w4f_h2nD mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | lia | ].
      unfold w4kl. intros bc y6 y7 y11 y12 y13 y14 y16 y28 Hbc.
      pose proof HSR as HSR'. unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR'.
      eapply (HL HSR w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew l256 l296 l336 mm (DST + w4nth 2 o0 o1 o2 o3) (w4nth 2 i0 i1 i2 i3) bc); [exact HW | exact HK | | | | | exact Hbc];
        unfold AF_huf_w4fin.w4se, w4nth in *; cbn [nth Nat.ltb Nat.leb] in *; w4nat; lia. }
  Qed.

  Lemma w4f_head3 : forall (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word),
    W4KFE 3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KERR ->
    (W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> forall (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word) (l256 l296 l336 : list cell),
       W4KFL 3 (w4se 3) (DST + w4nth 3 o0 o1 o2 o3) (w4fr w0 w8 w16 w24 w32)
         (w4mid 3 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3) l256 l296 l336) ->
    W4KF3 3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    intros i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HE HR HL.
    intros mm w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew l256 l296 l336 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 HW HSR HK.
    assert (HM : w4hm 3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew mm) by (eapply w4f_hm; [exact HW | unfold AF_huf_w4fin.W4SR in HSR; lia]).
    destruct (Z_le_gt_dec seg (dcap - 3 * seg)) as [HX | HX].
    {
      destruct (Z_lt_ge_dec (w4se 3) (DST + w4nth 3 o0 o1 o2 o3)) as [CA | CA].
      { eapply (w4f_h3XA mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
          [exact HM | exact HSR | exact HX | lia | unfold w4kr; intros; eapply HR; exact HW]. }
      destruct (Z_lt_ge_dec (w4nth 3 i0 i1 i2 i3) ((w4nth 3 e0 e1 e2 e3) - 8)) as [CB | CB].
      { eapply (w4f_h3XB mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
          [exact HM | exact HSR | exact HX | lia | unfold w4kr; intros; eapply HR; exact HW]. }
      destruct (Z_lt_ge_dec (w4se 3 - (DST + w4nth 3 o0 o1 o2 o3)) 4) as [CC | CC].
      { eapply (w4f_h3XC mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
          [exact HM | exact HSR | exact HX | lia | ].
        unfold w4ke. intros bc y6 y7 y11 y12 y13 y14 y16 y22 y25 y27 y28 Hbc.
        eapply HE; [do 26 eexists; exact HW | exact HSR | exact HK | exact Hbc | lia]. }
      { eapply (w4f_h3XD mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
          [exact HM | exact HSR | exact HX | lia | ].
        unfold w4kl. intros bc y6 y7 y11 y12 y13 y14 y16 y28 Hbc.
        pose proof HSR as HSR'. unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR'.
        eapply (HL HSR w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew l256 l296 l336 mm (DST + w4nth 3 o0 o1 o2 o3) (w4nth 3 i0 i1 i2 i3) bc); [exact HW | exact HK | | | | | exact Hbc];
          unfold AF_huf_w4fin.w4se, w4nth in *; cbn [nth Nat.ltb Nat.leb] in *; w4nat; lia. }
    }
    assert (HY : dcap - 3 * seg < seg) by lia. clear HX. rename HY into HX.
    destruct (Z_lt_ge_dec (w4se 3) (DST + w4nth 3 o0 o1 o2 o3)) as [CA | CA].
    { eapply (w4f_h3YA mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | exact HX | lia | unfold w4kr; intros; eapply HR; exact HW]. }
    destruct (Z_lt_ge_dec (w4nth 3 i0 i1 i2 i3) ((w4nth 3 e0 e1 e2 e3) - 8)) as [CB | CB].
    { eapply (w4f_h3YB mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | exact HX | lia | unfold w4kr; intros; eapply HR; exact HW]. }
    destruct (Z_lt_ge_dec (w4se 3 - (DST + w4nth 3 o0 o1 o2 o3)) 4) as [CC | CC].
    { eapply (w4f_h3YC mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | exact HX | lia | ].
      unfold w4ke. intros bc y6 y7 y11 y12 y13 y14 y16 y22 y25 y27 y28 Hbc.
      eapply HE; [do 26 eexists; exact HW | exact HSR | exact HK | exact Hbc | lia]. }
    { eapply (w4f_h3YD mm i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28);
        [exact HM | exact HSR | exact HX | lia | ].
      unfold w4kl. intros bc y6 y7 y11 y12 y13 y14 y16 y28 Hbc.
      pose proof HSR as HSR'. unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR'.
      eapply (HL HSR w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew l256 l296 l336 mm (DST + w4nth 3 o0 o1 o2 o3) (w4nth 3 i0 i1 i2 i3) bc); [exact HW | exact HK | | | | | exact Hbc];
        unfold AF_huf_w4fin.w4se, w4nth in *; cbn [nth Nat.ltb Nat.leb] in *; w4nat; lia. }
  Qed.

  Lemma w4f_stream : forall (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word),
    (k <= 3)%nat -> ((k < 3)%nat -> W4KF3 (S k) i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3) -> (k = 3%nat -> W4KFX2) -> W4KF3 k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    intros k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 Hk HN HX.
    pose proof (w4f_end k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HN HX) as HEND.
    pose proof (w4f_tail k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HEND) as HFT.
    pose proof (w4f_else k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HFT HEND) as HFE.
    pose proof (w4f_x1631 k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HFT HEND) as X1.
    pose proof (w4f_x1674 k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HFT HEND) as X2.
    pose proof (w4f_x1675 k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HFT HEND) as X3.
    assert (HL : W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> forall (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word) (l256 l296 l336 : list cell),
       W4KFL k (w4se k) (DST + w4nth k o0 o1 o2 o3) (w4fr w0 w8 w16 w24 w32)
         (w4mid k a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3) l256 l296 l336)
      by (intros HSR w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew l256 l296 l336; exact (w4f_loop k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew l256 l296 l336 HSR Hk X1 X2 X3)).
    destruct k as [|[|[|[|k]]]].
    - exact (w4f_head0 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HFE w4f_err HL).
    - exact (w4f_head1 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HFE w4f_err HL).
    - exact (w4f_head2 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HFE w4f_err HL).
    - exact (w4f_head3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HFE w4f_err HL).
    - lia.
  Qed.

  Lemma w4f_all : forall (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word), W4KF3 0 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    intros i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
    apply w4f_stream; [lia | intros _ | intros H; lia].
    apply w4f_stream; [lia | intros _ | intros H; lia].
    apply w4f_stream; [lia | intros _ | intros H; lia].
    apply w4f_stream; [lia | intros H; lia | intros _; exact w4f_fx2].
  Qed.

  Lemma w4f_rw_bytes : forall m A cs, rw_cells bsegs m A cs -> bytes_at bsegs m A (cells_bytes cs).
  Proof. intros m A cs H. exact (proj2 (proj1 H)). Qed.

  Lemma w4f_rw_pre : forall m A cs1 cs2, rw_cells bsegs m A (cs1 ++ cs2) -> rw_cells bsegs m A cs1.
  Proof. intros m A cs1 cs2 H. exact (proj1 (proj1 (kx_rw_cells_app bsegs m A cs1 cs2) H)). Qed.

  Ltac w4csz :=
    repeat match goal with
    | |- context [Z.of_nat (cells_size ?l)] =>
        let v := eval vm_compute in (Z.of_nat (cells_size l)) in change (Z.of_nat (cells_size l)) with v
    | |- context [cells_size ?l] => let v := eval vm_compute in (cells_size l) in change (cells_size l) with v
    end.

  Lemma w4f_f2c3 : forall (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) (w0 w8 w16 w24 w32 w64 w96 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew po4 pi4 pb4 : word)
      (mm : amem) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word),
    W4FX mm [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 n); C8 w64;
            C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap)); C8 w96]
         ([C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3))] ++ [C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))] ++ [C8 c0; C8 c1; C8 c2; C8 c3] ++ [C8 adt; C8 (Z_to_bv 64 SS); C8 oew; C8 (Z_to_bv 64 (SS + e0)); C8 (Z_to_bv 64 (SS + e1));
             C8 (Z_to_bv 64 (SS + e2)); C8 (Z_to_bv 64 (SS + e3))])
         ([C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))] ++ [C8 po4]) ([C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3))] ++ [C8 pi4]) ([C8 c0; C8 c1; C8 c2; C8 c3] ++ [C8 pb4]) ->
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KF3 0 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
               (Z_to_bv 64 AW4_K21) x22 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB)
               x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x892f4) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 w64 w96 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew po4 pi4 pb4 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 HW HSR K0.
    pose proof w4f_lay as LY. pose proof w4f_dtl as DL.
    assert (HN : 0 < n) by (unfold AF_huf_w4fin.W4SR in HSR; lia).
    pose proof (w4f_unp _ _ _ _ _ _ HW HN) as U.
    destruct U as ((_ & _ & _ & _ & _ & U6 & U7 & _) & _ & _ & U9 & U10 & _ & _ & U11 & U12 & U13 & U14 & U15 & U16 & U17 & U18
      & U19 & U20).
    pose proof HSR as HSR'. unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR'.
    unfold AIMG_HI in U11, U13, U15.
    pose proof HW as HWX.
    destruct HWX as (_ & _ & _ & _ & ST & F0 & _ & F1 & _ & F2 & _ & F3 & _ & F4 & _ & FRC & MI & MUD & WMD).
    unfold AW4_K21, AW4_KTB, AW4_KSB.
    destruct HW as ((buf & OUT & LBF) & BSS & BDT4 & BDT & _ & _ & S0 & _ & S1 & _ & S2 & _ & S3 & _ & S4 & _ & _ & _ & _).
    idtac "@@"; idtac "LEMMA call 3".
    Time kx_runFm [AW4_F3] 60%nat
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
       KZRange SS 4096 (2^47); KZRange DT 4096 (2^47);
       KZWord (SP + -400) 8 DST; KZWord (SP + -408) 8 dcap; KZWr (SP + -480) 104; KZImg 66480 (66480 + 8)]
      (@nil (Z * Z)) [(SP + -480, 480)] (@nil (Z * Z)).
    all: try w4br.
    all: try (kx_asan I).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    kx_post_regs_keep.
    pose proof (munch_refl [(SP + -416, SP + -416 + 8); (SP + -384, SP + -384 + 8)] mm) as MUW.
    pose proof (wmono_refl bsegs mm) as WMr.
    kx_munch_wins MUW [(SP + -416, 8); (SP + -384, 8)].
    kx_munch_wins MUD [(SP + -416, 8); (SP + -384, 8)].
    kx_post_mem_free.
    kx_cells_split F0.
    kx_cells_post.
    lazymatch goal with |- context [mem_denot ?E mm ?l] => set (m1 := mem_denot E mm l) in *; clearbody m1 end.
    assert (LCB' : Z.of_nat (length cbs) = 4096) by (rewrite LCB, TL11; reflexivity).
    lazymatch type of MUW with munch ?W _ _ =>
      apply (bytes_at_transport bsegs W mm m1 _ _) in BSS;
        [| exact MUW | cbn [disjoint_from]; rewrite length_map; clear - U7 U12 LY; lia];
      apply (bytes_at_transport bsegs W mm m1 _ _) in BDT4;
        [| exact MUW | cbn [disjoint_from]; rewrite LCB'; clear - U14 DL LY; lia] end.
    transport_after_call bsegs mm m1 MUW WMr.
    lazymatch type of F0 with rw_cells _ _ _ [C8 (Z_to_bv 64 ?v)] =>
      replace (Z_to_bv 64 v) with (Z_to_bv 64 seg) in F0
        by (f_equal; clear - DC; first [rewrite !Z.mod_small by lia; reflexivity | Z.div_mod_to_equations; lia]) end.
    unfold AF_huf_w4fin.W4KF3 in K0.
    eapply w4_evtF_eq.
    { eapply (K0 m1 w0 w8 w16 w24 w32 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 ipa0 ipa1 ipa2 ipa3 adt oew
                 ([C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))] ++ [C8 po4]) ([C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3))] ++ [C8 pi4]) ([C8 c0; C8 c1; C8 c2; C8 c3] ++ [C8 pb4])); [| exact HSR | lia].
      unfold W4F.
      split; [exists buf; split; assumption |].
      split; [exact BSS |]. split; [exact BDT4 |]. split; [exact BDT |]. split; [exact ST |].
      split; [unfold AF_huf_w4fin.w4fr, AW4_ST64; kx_cells_merge |]. split; [reflexivity |].
      split; [unfold AF_huf_w4fin.w4mid, w4sel; cbn [firstn skipn map app]; exact F1 |]. split; [reflexivity |].
      split; [exact F2 |]. split; [reflexivity |]. split; [exact F3 |]. split; [reflexivity |].
      split; [exact F4 |]. split; [reflexivity |]. split; [exact FRC |].
      split; [assumption |]. split; assumption. }
    w4meq.
  Time Qed.

  Lemma w4f_f2c2 : forall (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) (w0 w8 w16 w24 w32 w64 w96 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew po4 pi4 pb4 : word)
      (mm : amem) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word),
    W4FX mm [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 n); C8 w64;
            C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap)); C8 w96]
         ([C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3))] ++ [C8 opa0; C8 opa1; C8 opa2; C8 opa3] ++ [C8 c0; C8 c1; C8 c2; C8 c3] ++ [C8 adt; C8 (Z_to_bv 64 SS); C8 oew; C8 (Z_to_bv 64 (SS + e0)); C8 (Z_to_bv 64 (SS + e1));
             C8 (Z_to_bv 64 (SS + e2)); C8 (Z_to_bv 64 (SS + e3))])
         ([C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))] ++ [C8 po4]) ([C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3))] ++ [C8 pi4]) ([C8 c0; C8 c1; C8 c2; C8 c3] ++ [C8 pb4]) ->
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KF3 0 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
               (Z_to_bv 64 AW4_K21) x22 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB)
               x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x892e4) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 w64 w96 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew po4 pi4 pb4 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 HW HSR K0.
    pose proof w4f_lay as LY. pose proof w4f_dtl as DL.
    assert (HN : 0 < n) by (unfold AF_huf_w4fin.W4SR in HSR; lia).
    pose proof (w4f_unp _ _ _ _ _ _ HW HN) as U.
    destruct U as ((_ & _ & _ & _ & _ & U6 & U7 & _) & _ & _ & U9 & U10 & _ & _ & U11 & U12 & U13 & U14 & U15 & U16 & U17 & U18
      & U19 & U20).
    pose proof HSR as HSR'. unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR'.
    unfold AIMG_HI in U11, U13, U15.
    pose proof HW as HWX.
    destruct HWX as (_ & _ & _ & _ & ST & F0 & _ & F1 & _ & F2 & _ & F3 & _ & F4 & _ & FRC & MI & MUD & WMD).
    unfold AW4_K21, AW4_KTB, AW4_KSB.
    idtac "@@"; idtac "LEMMA call 2".
    Time kx_runFm [0x510d8] 60%nat
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange DT 4096 (2^47)]
      (@nil (Z * Z)) [(SP + -480, 480)] (@nil (Z * Z)).
    all: try w4br.
    all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    replace (SPF + 256) with (SP + -224) in F2 by lia.
    eapply (w4f_mcstep (SP + -344) (SP + -224) mm [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 n); C8 w64;
            C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap)); C8 w96]
              [C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3))] [C8 opa0; C8 opa1; C8 opa2; C8 opa3] [C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))] ([C8 c0; C8 c1; C8 c2; C8 c3] ++ [C8 adt; C8 (Z_to_bv 64 SS); C8 oew; C8 (Z_to_bv 64 (SS + e0)); C8 (Z_to_bv 64 (SS + e1));
             C8 (Z_to_bv 64 (SS + e2)); C8 (Z_to_bv 64 (SS + e3))])
              ([C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))] ++ [C8 po4]) ([C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3))] ++ [C8 pi4]) ([C8 c0; C8 c1; C8 c2; C8 c3] ++ [C8 pb4]));
      [exact HW | exact HN | w4csz; lia | w4csz; lia | reflexivity | reflexivity
      | cbn; tauto | exact (w4f_rw_bytes _ _ _ (w4f_rw_pre _ _ [C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))] [C8 po4] F2)) | lia | lia | ].
    intros m' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 HW1.
    rewrite ret_pc_even by (first [lia | reflexivity]).
    eapply (w4f_f2c3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 w64 w96 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew po4 pi4 pb4 m'); [exact HW1 | exact HSR | exact K0].
  Qed.

  Lemma w4f_f2c1 : forall (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) (w0 w8 w16 w24 w32 w64 w96 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew po4 pi4 pb4 : word)
      (mm : amem) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word),
    W4FX mm [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 n); C8 w64;
            C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap)); C8 w96]
         ([C8 ipa0; C8 ipa1; C8 ipa2; C8 ipa3] ++ [C8 opa0; C8 opa1; C8 opa2; C8 opa3] ++ [C8 c0; C8 c1; C8 c2; C8 c3] ++ [C8 adt; C8 (Z_to_bv 64 SS); C8 oew; C8 (Z_to_bv 64 (SS + e0)); C8 (Z_to_bv 64 (SS + e1));
             C8 (Z_to_bv 64 (SS + e2)); C8 (Z_to_bv 64 (SS + e3))])
         ([C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))] ++ [C8 po4]) ([C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3))] ++ [C8 pi4]) ([C8 c0; C8 c1; C8 c2; C8 c3] ++ [C8 pb4]) ->
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KF3 0 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
               (Z_to_bv 64 AW4_K21) x22 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB)
               x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x892d4) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 w64 w96 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew po4 pi4 pb4 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 HW HSR K0.
    pose proof w4f_lay as LY. pose proof w4f_dtl as DL.
    assert (HN : 0 < n) by (unfold AF_huf_w4fin.W4SR in HSR; lia).
    pose proof (w4f_unp _ _ _ _ _ _ HW HN) as U.
    destruct U as ((_ & _ & _ & _ & _ & U6 & U7 & _) & _ & _ & U9 & U10 & _ & _ & U11 & U12 & U13 & U14 & U15 & U16 & U17 & U18
      & U19 & U20).
    pose proof HSR as HSR'. unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR'.
    unfold AIMG_HI in U11, U13, U15.
    pose proof HW as HWX.
    destruct HWX as (_ & _ & _ & _ & ST & F0 & _ & F1 & _ & F2 & _ & F3 & _ & F4 & _ & FRC & MI & MUD & WMD).
    unfold AW4_K21, AW4_KTB, AW4_KSB.
    idtac "@@"; idtac "LEMMA call 1".
    Time kx_runFm [0x510d8] 60%nat
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange DT 4096 (2^47)]
      (@nil (Z * Z)) [(SP + -480, 480)] (@nil (Z * Z)).
    all: try w4br.
    all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    replace (SPF + 296) with (SP + -184) in F3 by lia.
    eapply (w4f_mcstep (SP + -376) (SP + -184) mm [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 n); C8 w64;
            C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap)); C8 w96]
              [] [C8 ipa0; C8 ipa1; C8 ipa2; C8 ipa3] [C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3))] ([C8 opa0; C8 opa1; C8 opa2; C8 opa3] ++ [C8 c0; C8 c1; C8 c2; C8 c3] ++ [C8 adt; C8 (Z_to_bv 64 SS); C8 oew; C8 (Z_to_bv 64 (SS + e0)); C8 (Z_to_bv 64 (SS + e1));
             C8 (Z_to_bv 64 (SS + e2)); C8 (Z_to_bv 64 (SS + e3))])
              ([C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))] ++ [C8 po4]) ([C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3))] ++ [C8 pi4]) ([C8 c0; C8 c1; C8 c2; C8 c3] ++ [C8 pb4]));
      [exact HW | exact HN | w4csz; lia | w4csz; lia | reflexivity | reflexivity
      | cbn; tauto | exact (w4f_rw_bytes _ _ _ (w4f_rw_pre _ _ [C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3))] [C8 pi4] F3)) | lia | lia | ].
    intros m' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 HW1.
    rewrite ret_pc_even by (first [lia | reflexivity]).
    eapply (w4f_f2c2 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 w64 w96 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew po4 pi4 pb4 m'); [exact HW1 | exact HSR | exact K0].
  Qed.

  Lemma w4f_f2 : forall (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) (w0 w8 w16 w24 w32 w64 w96 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew po4 pi4 pb4 : word)
      (mm : amem) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word),
    W4FX mm [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 n); C8 w64;
            C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap)); C8 w96]
         ([C8 ipa0; C8 ipa1; C8 ipa2; C8 ipa3] ++ [C8 opa0; C8 opa1; C8 opa2; C8 opa3] ++ [C8 ba0; C8 ba1; C8 ba2; C8 ba3] ++ [C8 adt; C8 (Z_to_bv 64 SS); C8 oew; C8 (Z_to_bv 64 (SS + e0)); C8 (Z_to_bv 64 (SS + e1));
             C8 (Z_to_bv 64 (SS + e2)); C8 (Z_to_bv 64 (SS + e3))])
         ([C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))] ++ [C8 po4]) ([C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3))] ++ [C8 pi4]) ([C8 c0; C8 c1; C8 c2; C8 c3] ++ [C8 pb4]) ->
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KF3 0 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
               (Z_to_bv 64 AW4_K21) x22 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB)
               x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 AW4_FX) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 w64 w96 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew po4 pi4 pb4 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 HW HSR K0.
    pose proof w4f_lay as LY. pose proof w4f_dtl as DL.
    assert (HN : 0 < n) by (unfold AF_huf_w4fin.W4SR in HSR; lia).
    pose proof (w4f_unp _ _ _ _ _ _ HW HN) as U.
    destruct U as ((_ & _ & _ & _ & _ & U6 & U7 & _) & _ & _ & U9 & U10 & _ & _ & U11 & U12 & U13 & U14 & U15 & U16 & U17 & U18
      & U19 & U20).
    pose proof HSR as HSR'. unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1 in HSR'.
    unfold AIMG_HI in U11, U13, U15.
    pose proof HW as HWX.
    destruct HWX as (_ & _ & _ & _ & ST & F0 & _ & F1 & _ & F2 & _ & F3 & _ & F4 & _ & FRC & MI & MUD & WMD).
    unfold AW4_K21, AW4_KTB, AW4_KSB, AW4_FX.
    idtac "@@"; idtac "LEMMA call 0".
    Time kx_runFm [0x510d8] 60%nat
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SP (ATOP_MIN + 12288) (2^47);
         KZRange SS 4096 (2^47); KZRange DT 4096 (2^47)]
      (@nil (Z * Z)) [(SP + -480, 480)] (@nil (Z * Z)).
    all: try w4br.
    all: try (kx_post_regs; cbn [mem_denot]).
    all: match goal with |- ?g => idtac "@@"; idtac g end.
    replace (SPF + 336) with (SP + -144) in F4 by lia.
    eapply (w4f_mcstep (SP + -312) (SP + -144) mm [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 n); C8 w64;
            C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap)); C8 w96]
              ([C8 ipa0; C8 ipa1; C8 ipa2; C8 ipa3] ++ [C8 opa0; C8 opa1; C8 opa2; C8 opa3]) [C8 ba0; C8 ba1; C8 ba2; C8 ba3] [C8 c0; C8 c1; C8 c2; C8 c3] [C8 adt; C8 (Z_to_bv 64 SS); C8 oew; C8 (Z_to_bv 64 (SS + e0)); C8 (Z_to_bv 64 (SS + e1));
             C8 (Z_to_bv 64 (SS + e2)); C8 (Z_to_bv 64 (SS + e3))]
              ([C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))] ++ [C8 po4]) ([C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3))] ++ [C8 pi4]) ([C8 c0; C8 c1; C8 c2; C8 c3] ++ [C8 pb4]));
      [exact HW | exact HN | w4csz; lia | w4csz; lia | reflexivity | reflexivity
      | cbn; tauto | exact (w4f_rw_bytes _ _ _ (w4f_rw_pre _ _ [C8 c0; C8 c1; C8 c2; C8 c3] [C8 pb4] F4)) | lia | lia | ].
    intros m' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 HW1.
    rewrite ret_pc_even by (first [lia | reflexivity]).
    eapply (w4f_f2c1 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 w64 w96 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew po4 pi4 pb4 m'); [exact HW1 | exact HSR | exact K0].
  Qed.

  Lemma w4fx_ok : w4fx_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
    src cbs.
  Proof using All.
    unfold w4fx_goal.
    intros i0 o0 e0 i1 o1 e1 i2 o2 e2 i3 o3 e3 c0 c1 c2 c3 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew
      po4 pi4 pb4 w0 w8 w16 w24 w32 w64 w96 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27
      x28 x29 x30 x31 HW H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22.
    assert (HSR : W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3) by (unfold AF_huf_w4fin.W4SR, AF_huf_w4fin.w4sr1; lia).
    exact (w4f_f2 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 w64 w96 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 adt oew po4 pi4 pb4 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 HW HSR (w4f_all i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3)).
  Qed.

End W4FIN2.
End CANSEC1.
