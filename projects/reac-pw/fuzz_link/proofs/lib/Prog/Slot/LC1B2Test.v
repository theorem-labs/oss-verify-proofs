(* Segment B2 of the op_write arm, middle part: the refusal test 0x14010-0x14040.
   `if (!name || !name[0] || strlen(alias) >= 256 || !index_of(name)) check_refused(opened_before,
   g_nl.opened)`: each of the four readings goes to 0x14038, where check_refused (0x151ac) compares
   s4 (g_nl.opened before the library wrote) with g_nl.opened now; index_of (0x15120) answering a
   real index goes straight to 0x14044. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Frame Step Tac Bytes Arr Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  link_mem strlen_c index_of_c check_refused_c check_write_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import
  LDefs LC1Defs LC1Call LC1B2Lib LC1B2Tab LC1B2Rc LC1B2St LC1B2Tail.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Branch conditions on literal words
   ========================================================================== *)

Lemma c1b2_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma c1b2_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma c1b2_ltu_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma c1b2_sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

(* g_nl.opened as `lw a1, 0x218(s1)` reads it (s1 = g_nl + 0x40000) *)
Lemma c1b2_read_opened : forall m kbs, nlk_at m kbs ->
  ov_read_bytes rsegs m (wa (A_G_NL + NK_OPENED)) 4 = Some (le4 (wz (nk_opened kbs))).
Proof.
  intros m kbs [HU HL].
  rewrite (c1b2_read4_arr m A_G_NL kbs NK_OPENED HU ltac:(unfold NK_OPENED; lia)
             ltac:(unfold NK_OPENED, NK_SIZE in *; lia)).
  f_equal. unfold nk_opened, fld_u32, rdn. symmetry. apply c1b2_le4_of.
  apply c1b2_slice_len; unfold NK_OPENED, NK_SIZE in *; lia.
Qed.

Section B2Test.

Hypothesis STRLEN_OK : strlen_contract.
Hypothesis INDEX_OF_OK : index_of_contract_P.
Hypothesis CHECK_REFUSED_OK : check_refused_contract.
Hypothesis CHECK_WRITE_OK : check_write_contract.
Hypothesis CHECK_REQUESTS_OK : check_requests_contract.

(* ==========================================================================
   2. 0x14038: check_refused, then the tail
   ========================================================================== *)

Lemma c1b2_refuse : forall E i gp own nb rm op0 s rl (t sl : list byte) m0
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (P N : Z) (kbs mbs gbs : list byte),
  lenv_ok E -> frm0 fc -> 0 <= i <= 47 -> 0 <= N ->
  rm = norm_rc rl -> - 2 ^ 31 <= rl < 2 ^ 31 -> 0 <= op0 < 2 ^ 31 ->
  requests_are kbs mbs -> nk_opened kbs = op0 ->
  c1b2_car E i own s t sl P N kbs mbs gbs m0 m ->
  evt rsegs (eqv_cl (c1b2_post E i gp own m0))
    (MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
             a0 a1 a2 a3 a4 a5 a6 a7
             (wz (sel_ptr nb)) (wz rm) (wz op0) (wz s) (wz rl) (wz (e_mk E)) (wz 0xab) (wz 4)
             (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
        F (wz 0x14038) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp own nb rm op0 s rl t sl m0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m P N
         kbs mbs gbs HE FRM Hi HNn HRM HRL HOP HRQ HOK CAR.
  assert (SB : 0x960e0 + 65536 <= e_S E <= 2 ^ 47)
    by (unfold lenv_ok, SLOT_STACK_Z in HE; lia).
  assert (USP : bv_unsigned (Z_to_bv 64 (e_S E - SLOT_FRAME)) = e_S E - SLOT_FRAME)
    by (apply unsigned_lit; unfold SLOT_FRAME; lia).
  assert (HK : nlk_at m kbs).
  { unfold c1b2_car in CAR. destruct CAR as (_ & NL & _). unfold c1b2_nl in NL.
    destruct NL as (X & _). exact X. }
  assert (MI : mem_inv rsegs m)
    by (unfold c1b2_car in CAR; destruct CAR as (_ & _ & _ & _ & _ & X & _); exact X).
  assert (ST : stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME))
    by (unfold c1b2_car in CAR; destruct CAR as (_ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  pose proof (c1b2_read_opened m kbs HK) as HOB. rewrite HOK in HOB. unfold wz in HOB.
  unfold wz.
  do 3 step.
  eapply leaf_call_eqv.
  { exact CHECK_REFUSED_OK. }
  { cbv beta. rewrite c1b2_g10, c1b2_g11. rewrite c1b2_sx32_small by lia. reflexivity. }
  { exact MI. }
  { rewrite USP. exact ST. }
  { rewrite USP. unfold SLOT_STACK_Z, SLOT_FRAME. lia. }
  { rewrite USP. unfold SLOT_FRAME. lia. }
  intros ra1 t01 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 m1
         (regs1 & HR1 & HP1) MU1 WM1 MI1 ST1.
  unfold unchanged in HP1. subst m1.
  rewrite (ret_pc_even 81988 ltac:(lia) ltac:(reflexivity)).
  apply (c1b2_tail CHECK_WRITE_OK CHECK_REQUESTS_OK E i gp own nb rm op0 s rl t sl m0); [exact HE|].
  unfold c1b2_s44. do 16 eexists. exists F, fc, m, P, N, kbs, mbs, gbs.
  split; [reflexivity|].
  split; [exact FRM|]. split; [exact Hi|]. split; [exact HNn|]. split; [exact HRM|].
  split; [exact HRL|]. split; [exact HRQ | exact CAR].
Qed.

(* ==========================================================================
   3. 0x14010: the refusal test
   ========================================================================== *)

Lemma c1b2_test : forall E i gp own nb rm op0 s rl (t sl : list byte) m0 ms,
  lenv_ok E -> c1b2_s10 E i gp own nb rm op0 s rl t sl m0 ms ->
  evt rsegs (eqv_cl (c1b2_post E i gp own m0)) ms.
Proof.
  intros E i gp own nb rm op0 s rl t sl m0 ms HE HS.
  destruct HS as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6
                  & F & fc & m & P & N & kbs & mbs & gbs & -> & FRM & Hi & Hnb & HNn & HRM & HRL & HOP
                  & HRQ & HRF & CAR).
  assert (SB : 0x960e0 + 65536 <= e_S E <= 2 ^ 47)
    by (unfold lenv_ok, SLOT_STACK_Z in HE; lia).
  assert (USP : bv_unsigned (Z_to_bv 64 (e_S E - SLOT_FRAME)) = e_S E - SLOT_FRAME)
    by (apply unsigned_lit; unfold SLOT_FRAME; lia).
  destruct (Z.eq_dec nb 255) as [E255|N255].
  { (* the selector byte was 255: name_of answered NULL *)
    subst nb. unfold wz. step.
    assert (C : bv_eqb (Z_to_bv 64 (sel_ptr 255)) (Z_to_bv 64 0) = true) by reflexivity.
    rewrite C. cbv iota.
    eapply (c1b2_refuse E i gp own 255 rm op0 s rl t sl m0) with (P := P) (N := N) (kbs := kbs)
      (mbs := mbs) (gbs := gbs); try eassumption.
    apply HRF. left. reflexivity. }
  (* a real name: a g_names slot or an `odd` string *)
  assert (REST : c1b2_rest E P N mbs gbs m)
    by (unfold c1b2_car in CAR; destruct CAR as (X & _); exact X).
  assert (NL : c1b2_nl (i + 1) kbs m)
    by (unfold c1b2_car in CAR; destruct CAR as (_ & X & _); exact X).
  assert (AL : al_ok E m s t sl)
    by (unfold c1b2_car in CAR; destruct CAR as (_ & _ & _ & _ & X & _); exact X).
  assert (MI : mem_inv rsegs m)
    by (unfold c1b2_car in CAR; destruct CAR as (_ & _ & _ & _ & _ & X & _); exact X).
  assert (ST : stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME))
    by (unfold c1b2_car in CAR; destruct CAR as (_ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (HGN : gnames_at m)
    by (unfold c1b2_rest in REST; destruct REST as (_ & _ & X & _); exact X).
  assert (HOD : odd_at m)
    by (unfold c1b2_rest in REST; destruct REST as (_ & _ & _ & X & _); exact X).
  assert (HIF : ifptrs_at m)
    by (unfold c1b2_rest in REST; destruct REST as (_ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (HK : nlk_at m kbs) by (unfold c1b2_nl in NL; destruct NL as (X & _); exact X).
  assert (HT : iftab_at m kbs link_tab) by (unfold c1b2_nl in NL; destruct NL as (_ & _ & X & _); exact X).
  pose proof (c1b2_sel_str m nb Hnb HGN HOD) as HSA.
  destruct (sel_name nb) as [s0|] eqn:ESN.
  2:{ exfalso. unfold sel_name in ESN. destruct (nb =? 255) eqn:E1; [apply Z.eqb_eq in E1; lia|].
      destruct (nb <? 64); discriminate ESN. }
  destruct HSA as [HP0 HCS].
  pose proof (c1b2_sel_rng nb s0 Hnb ESN) as HSR.
  pose proof (c1b2_sel_ptr_rng nb Hnb) as HSP.
  destruct (c1b2_first_byte m (sel_ptr nb) s0 HCS) as (b & HR1 & HB0).
  unfold wz. step.
  assert (C1 : bv_eqb (Z_to_bv 64 (sel_ptr nb)) (Z_to_bv 64 0) = false)
    by (rewrite c1b2_eqb_lit by lia; apply Z.eqb_neq; exact HP0).
  rewrite C1. cbv iota.
  step. step.
  assert (C2 : bv_eqb (zxb b) (Z_to_bv 64 0) = (bv_unsigned b =? 0)).
  { unfold zxb. pose proof (c1b2_byte_rng b). apply c1b2_eqb_lit; lia. }
  rewrite C2.
  destruct (Z.eqb_spec (bv_unsigned b) 0) as [Hb|Hb]; cbv iota.
  { (* an empty name *)
    apply HB0 in Hb. subst s0.
    eapply (c1b2_refuse E i gp own nb rm op0 s rl t sl m0) with (P := P) (N := N) (kbs := kbs)
      (mbs := mbs) (gbs := gbs); try eassumption.
    apply HRF. right. left. exact ESN. }
  (* strlen(alias) *)
  destruct AL as (AN0 & ABT & ANN & ALT & ASL & AD1 & AD2 & AD3 & AD4 & AD5).
  pose proof (bytes_at_bound rsegs m s (t ++ zb 0 :: sl) ABT) as ABB.
  rewrite length_app in ABB. cbn [length] in ABB.
  step. step.
  eapply evt_cut.
  { eapply STRLEN_OK with (str := t) (slack := sl).
    - rewrite unsigned_lit by lia. exact ABT.
    - exact ANN.
    - rewrite unsigned_lit by lia. lia.
    - exact MI. }
  intros ms1 (t01 & t11 & t21 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & t31 & t41 & t51 & t61 & m1
              & -> & MU1 & WM1 & MI1 & BA1).
  apply c1b2_munch_nil in MU1. subst m1.
  rewrite (ret_pc_even 81956 ltac:(lia) ltac:(reflexivity)).
  step. step.
  assert (C3 : bv_ltu (Z_to_bv 64 255) (Z_to_bv 64 (Z.of_nat (length t))) = (255 <? Z.of_nat (length t)))
    by (apply c1b2_ltu_lit; lia).
  rewrite C3.
  destruct (Z.ltb_spec 255 (Z.of_nat (length t))) as [Hl|Hl]; cbv iota.
  { (* an alias of 256 bytes or more *)
    eapply (c1b2_refuse E i gp own nb rm op0 s rl t sl m0) with (P := P) (N := N) (kbs := kbs)
      (mbs := mbs) (gbs := gbs); try eassumption.
    apply HRF. right. right. left. unfold ALIAS_MAX. lia. }
  (* index_of(name) *)
  step. step.
  eapply leaf_call_eqv.
  { exact INDEX_OF_OK. }
  { exists kbs, link_tab, s0. rewrite c1b2_arg0. rewrite (unsigned_lit (sel_ptr nb)) by lia.
    unfold frame_apart_gnl, apart_frame, apart_gnl. rewrite c1b2_spZ, USP.
    split; [exact HK|].
    split; [unfold A_G_NL, NK_SIZE, SLOT_FRAME; lia|].
    split; [exact HT|].
    split; [exact HP0|].
    split; [exact HCS|].
    split.
    - destruct (c1b2_sel_apart nb s0 (e_S E - SLOT_FRAME) 48 Hnb ESN
                  ltac:(unfold SLOT_FRAME; lia) ltac:(unfold SLOT_FRAME; lia)) as [X _]. exact X.
    - intros k n2 ix p HEk HUp.
      destruct (c1b2_ptr_apart m kbs k n2 ix p (e_S E - SLOT_FRAME) 48 HIF HT HEk HUp
                  ltac:(unfold SLOT_FRAME; lia) ltac:(unfold SLOT_FRAME; lia)) as [X _]. exact X. }
  { exact MI. }
  { rewrite USP. exact ST. }
  { rewrite USP. unfold SLOT_STACK_Z, SLOT_FRAME. lia. }
  { rewrite USP. unfold SLOT_FRAME. lia. }
  intros ra2 t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 t32 t42 t52 t62 m2
         (regs2 & HR2 & HP2) MU2 WM2 MI2 ST2.
  pose proof (HP2 kbs link_tab s0 HK HT) as HI.
  rewrite c1b2_arg0 in HI. rewrite (unsigned_lit (sel_ptr nb)) in HI by lia.
  specialize (HI HCS). rewrite HR2, c1b2_g10 in HI. subst a02.
  unfold writes_nothing in MU2. rewrite USP in MU2, ST2.
  assert (CAR2 : c1b2_car E i own s t sl P N kbs mbs gbs m0 m2).
  { eapply c1b2_car_keep with (W := [(e_S E - SLOT_FRAME - 48, e_S E - SLOT_FRAME)]);
      [exact HE | exact CAR | exact MU2 | exact WM2 | exact MI2 | exact ST2 |].
    intros x Hx. apply c1b2_inside1 in Hx. unfold SLOT_STACK_Z, SLOT_FRAME in *. lia. }
  rewrite (ret_pc_even 81972 ltac:(lia) ltac:(reflexivity)).
  unfold wz. step.
  assert (C4 : bv_eqb (Z_to_bv 64 (index_of link_tab s0)) (Z_to_bv 64 0) = (index_of link_tab s0 =? 0))
    by (pose proof (c1b2_index_rng s0); apply c1b2_eqb_lit; lia).
  rewrite C4.
  destruct (Z.eqb_spec (index_of link_tab s0) 0) as [Hz|Hz]; cbn [negb]; cbv iota.
  { (* the name is not in the table *)
    eapply (c1b2_refuse E i gp own nb rm op0 s rl t sl m0) with (P := P) (N := N) (kbs := kbs)
      (mbs := mbs) (gbs := gbs); try eassumption.
    apply HRF. right. right. right. intros s' Hs'. rewrite ESN in Hs'. injection Hs' as <-. exact Hz. }
  (* a real index: straight to check_write *)
  apply (c1b2_tail CHECK_WRITE_OK CHECK_REQUESTS_OK E i gp own nb rm op0 s rl t sl m0); [exact HE|].
  unfold c1b2_s44. do 16 eexists. exists F, fc, m2, P, N, kbs, mbs, gbs.
  split; [reflexivity|].
  split; [exact FRM|]. split; [exact Hi|]. split; [exact HNn|]. split; [exact HRM|].
  split; [exact HRL|]. split; [exact HRQ | exact CAR2].
Qed.

End B2Test.
