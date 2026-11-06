(* Segment G07 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13b04, 0x13b5c], U13b04 (v1.8
   U13b10) -> U13b60 (v1.8 U13b68). v1.9 replaced the v1.8 frame-state reads: #63 is not taken
   (record_sum_closes returned 1 since the CLOSE record sums to 0, FRAG C1.7); `lw a0,36(sp)` reads first->have
   (the NEW 40-byte local `first` at sp+36: have u32 at +0, n u8 at +4, body at +5) and #64 (have != 0) is not
   taken; `lhu s10,1750(sp)` reloads addr_f (v1.8 read it into a2 at 0x13b44 and kept rf in s9; v1.9 rf is s10, so
   this segment writes over it); the two bytes of the joined address are the NEW-only leaf function joined_byte
   (0x14400) at i = 9 and i = 10 with a0 = sp+36, a1 = blk (s8), taken through a Theorem Labs lane's joined_byte_contract
   (lib/U/Prog/joined_byte_c.v, proved by joined_byte.joined_byte_holds); s0 (= sp+128) is parked in s2 over the
   two calls and both are restored (0x13b24, 0x13b40, 0x13b44); #65 is the address check `bne a0,s10`; then
   reac_identity_ingest (0x163ec) (sp+76 = id (v1.8 sp+154), addr_f, pp = sp+139 from [sp+1736], pll_f from
   [sp+1728]). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag RcLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import joined_byte_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require joined_byte.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF reac_identity_ingest_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u4 Tac_u5.
Import ListNotations.
Open Scope Z_scope.

(* joined_byte (0x14400) is a Theorem Labs lane's function proof: g07_evt takes joined_byte_contract at its two calls and
   seg_G07 discharges it with joined_byte.joined_byte_holds. *)
Lemma g07_jb_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. pose proof (RcLib.byte_range b). unfold zxb. apply MState.unsigned_lit. lia. Qed.

(* The whole segment, 0x13b04 -> 0x13b60: #63, first->have, the two joined_byte calls, #65 and
   reac_identity_ingest(sp+76, addr, pp, pll). `first` is at sp+36 (have u32, n at +4, body at +5), blk = s8. *)
Lemma g07_evt : reac_identity_ingest_contract -> joined_byte_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv blk pll addr : Z)
         (pb idb : list byte) (nb b9 b10 : byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 1 -> s0 = Z_to_bv 64 (spv + 128) -> s2 = Z_to_bv 64 1 ->
    s8 = Z_to_bv 64 blk ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 -> 1 <= pll <= 51 -> 4096 <= blk -> blk + 32 < 2 ^ 63 ->
    ov_read_bytes rsegs m (wa (spv + 36)) 4 = Some (le4 (Z_to_bv 64 1)) ->
    bytes_at rsegs m (spv + 40) [nb] ->
    bytes_at rsegs m (jb_addr (spv + 36) blk (bv_unsigned nb) 9) [b9] ->
    bytes_at rsegs m (jb_addr (spv + 36) blk (bv_unsigned nb) 10) [b10] ->
    addr = 256 * bv_unsigned b9 + bv_unsigned b10 ->
    ov_read_bytes rsegs m (wa (spv + 1750)) 2 = Some (le2 (Z_to_bv 64 addr)) ->
    ov_read_bytes rsegs m (wa (spv + 1736)) 8 = Some (le8 (Z_to_bv 64 (spv + 139))) ->
    ov_read_bytes rsegs m (wa (spv + 1728)) 8 = Some (le8 (Z_to_bv 64 pll)) ->
    rw_cells rsegs m (spv + 76) [CB 38 idb] -> length pb = Z.to_nat pll -> bytes_at rsegs m (spv + 139) pb ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13b60) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ING idb addr pb)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 addr) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13b60) fc None m' (seg_rom rsegs) /\
         munch [(spv + 76, spv + 114)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 76) (snd (ING idb addr pb)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13b04) fc None m (seg_rom rsegs)).
Proof.
  intros ING JB ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv blk pll addr pb idb nb b9 b10 -> -> -> -> -> Hlo Hhi H16 Hp Hblk Hblk2
    Rhv Rnb R9 R10 Had R1750 R1736 R1728 HC Hpb HPB.
  pose proof (RcLib.byte_range b9) as B9. pose proof (RcLib.byte_range b10) as B10.
  pose proof (RcLib.byte_range nb) as Bn.
  (* 0x13b04 beqz a0 (#63); 0x13b08 lw a0,36(sp) = have; 0x13b0c beqz a0 (#64) *)
  step. u5_br false.
  step.
  step. u5_br false.
  (* 0x13b10 lhu s10,1750(sp); 0x13b14 addi a0,sp,36; 0x13b18 li a2,9; 0x13b1c mv a1,s8; 0x13b20 jal *)
  step. step. step. step. step.
  eapply evt_cut.
  { eapply JB with (i := 9) (nb := nb) (b := b9);
      [ left; reflexivity | reflexivity
      | rewrite MState.unsigned_lit by lia; clear -H16; Z.div_mod_to_equations; lia
      | rewrite MState.unsigned_lit by lia; replace (spv + 36 + 4) with (spv + 40) by lia; exact Rnb
      | intros _; rewrite MState.unsigned_lit by lia; lia
      | rewrite !MState.unsigned_lit by lia; exact R9 ]. }
  intros ms' (a1' & a2' & a3' & ->).
  rewrite (MState.ret_pc_even 0x13b24) by (first [reflexivity | lia]).
  (* 0x13b24 mv s2,s0; 0x13b28 slli s0,a0,8; 0x13b2c addi a0,sp,36; 0x13b30 li a2,10; 0x13b34 mv a1,s8;
     0x13b38 jal *)
  step. step. step. step. step. step.
  eapply evt_cut.
  { eapply JB with (i := 10) (nb := nb) (b := b10);
      [ right; reflexivity | reflexivity
      | rewrite MState.unsigned_lit by lia; clear -H16; Z.div_mod_to_equations; lia
      | rewrite MState.unsigned_lit by lia; replace (spv + 36 + 4) with (spv + 40) by lia; exact Rnb
      | intros _; rewrite MState.unsigned_lit by lia; lia
      | rewrite !MState.unsigned_lit by lia; exact R10 ]. }
  intros ms'' (a1'' & a2'' & a3'' & ->).
  rewrite (MState.ret_pc_even 0x13b3c) by (first [reflexivity | lia]).
  (* 0x13b3c or a0,s0,a0; 0x13b40 mv s0,s2; 0x13b44 li s2,1; 0x13b48 bne a0,s10 (#65) *)
  step.
  lazymatch goal with
  | |- context [Z.lor ?x ?y] =>
      assert (Elor : Z.lor x y = 256 * bv_unsigned b9 + bv_unsigned b10);
      [ rewrite !g07_jb_zxb, Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256;
        rewrite (MState.unsigned_lit (bv_unsigned b9 * 256)) by lia; rewrite u5_lor8 by lia; lia
      | rewrite Elor ]
  end.
  step. step. step.
  rewrite <- Had. rewrite (u5_zx16 addr) by lia. u5_br false.
  (* 0x13b4c lhu a1,1750(sp); 0x13b50 ld a2,1736(sp); 0x13b54 ld a3,1728(sp); 0x13b58 addi a0,sp,76;
     0x13b5c jal reac_identity_ingest *)
  step. step. step. step. step.
  assert (Href : ingest_refused (spv + 76) (spv + 139) pll = false).
  { unfold ingest_refused. apply orb_false_iff. split; [apply Z.eqb_neq; lia|].
    apply andb_false_iff. right. apply Z.eqb_neq. lia. }
  eapply evt_cut.
  { eapply ING with (id := spv + 76) (ad := addr) (p := spv + 139) (len := pll) (idb := idb) (pb := pb);
      [ first [reflexivity | u5_weq] | first [reflexivity | apply u5_zx16; lia] | reflexivity | reflexivity
      | lia | lia | lia | lia
      | intros _; split; [lia | exact HC] | exact Hpb | intros _ _; exact HPB | intros _ _ _; right; lia ]. }
  intros ms3 (t0' & t1' & t2' & a1g & a2g & a3g & a4g & a5g & a6g & a7g & m' & E & MUc & WMc & _ & _ & Hz).
  subst ms3. specialize (Hz Href). unfold ingest_ret. rewrite Href.
  replace (spv + 76 + 38) with (spv + 114) in MUc by lia.
  replace (ret_pc (Z_to_bv 64 0x13b60)) with (Z_to_bv 64 0x13b60)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1g, a2g, a3g, a4g, a5g, a6g, a7g, m'.
  split; [reflexivity|]. split; [exact MUc|]. split; [exact WMc|].
  exact (sl_rw_bytes _ _ _ _ Hz).
Qed.

Lemma g07_byte_lit : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact (bv_unsigned_in_range 8 b).
Qed.

Lemma g07_lit8 : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof. intros v Hv. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

(* The byte that joined_byte(&first, blk, i) reads (blk = Φ + 18): first->body[i] at first + 5 + i for i < n, else
   Φ[27 + i - n]; in both cases the model's SlotModel.joined_byte s g i (g = Φ's first 50 bytes). *)
Lemma g07_jb_mrd : forall m p phi (s : fstate) (g : list byte) i,
  (i = 9 \/ i = 10) -> 0 <= fs_nb s -> Z.of_nat (length (fs_body s)) = fs_nb s -> length g = 50%nat ->
  bytes_at rsegs m (p + 5) (fs_body s) -> bytes_at rsegs m phi g ->
  bytes_at rsegs m (jb_addr p (phi + 18) (fs_nb s) i) [Z_to_bv 8 (joined_byte s g i)].
Proof.
  intros m p phi s g i Hi Hn0 HL Hg HB HG. unfold jb_addr, joined_byte, RcFrag.bat.
  destruct (Z.ltb_spec i (fs_nb s)) as [E | E]; cbv iota; rewrite g07_byte_lit.
  - pose proof (u5_ba_sub m (p + 5) (fs_body s) (Z.to_nat i) 1 HB ltac:(lia)) as X.
    rewrite Z2Nat.id in X by lia. rewrite (u5_first1 (fs_body s) (Z.to_nat i) (Z_to_bv 8 0)) in X by lia.
    exact X.
  - pose proof (u5_ba_sub m phi g (Z.to_nat (27 + i - fs_nb s)) 1 HG ltac:(lia)) as X.
    rewrite Z2Nat.id in X by lia. rewrite (u5_first1 g (Z.to_nat (27 + i - fs_nb s)) (Z_to_bv 8 0)) in X by lia.
    replace (phi + 18 + (9 + i - fs_nb s)) with (phi + (27 + i - fs_nb s)) by lia. exact X.
Qed.

Section G07.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis ING : reac_identity_ingest_contract.
Hypothesis INGOK : reac_identity_ingest_id_ok_kept.

Lemma seg_G07 : forall j : nat, Hat B APIf ra (Inv_U13b60_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13b04_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HGF & H26 & Hrf & H10).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof (u4_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof HGF as (HFB & HI & HG & HS & _ & Hrs).
  destruct (Hrs Hrf) as (Hadr & Hpl & Hpll).
  pose proof HFB as ((HLK & _ & _ & Hphi & _) & (_ & _ & _ & Hbig & (H24 & _ & _))).
  pose proof (u4_LK_s0 g j regs mem HLK) as H8.
  pose proof (u4_LK_s2 g j regs mem HLK) as H18.
  pose proof HS as (Hhave & Hnbs & Hbody & HLb & HFI).
  unfold u32, b8 in Hhave, Hnbs.
  destruct (u5_close_facts (g_in g) j Hrf) as (HT & _ & _ & _ & _ & HR).
  destruct (u5_P4l (g_in g) j Hrf HFI) as (Hhv & Had).
  pose proof (u4_fst_nb (g_in g) j) as (Hnb & _).
  assert (Hnbu : bv_unsigned (Z_to_bv 8 (fs_nb (fst_at (g_in g) j))) = fs_nb (fst_at (g_in g) j))
    by (apply g07_lit8; lia).
  pose proof HI as (HID & HIok).
  pose proof HG as (HFG & _).
  unfold IDB, FGB in *.
  unfold spk, SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (Hpll5 : 1 <= f_pll (t_FG (g_in g) j) (t_g (g_in g) j) <= 51) by (unfold f_pll; lia).
  assert (Hb50 : 50 <= t_len (g_in g) j).
  { unfold t_rf in Hrf. destruct (u5_close _ _ _ Hrf) as (_ & Efr & _).
    exact (proj1 (u5_fr_n _ _ Efr)). }
  assert (Ebig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; exact Hb50).
  pose proof (u5_norm mem _ _ HMI HFG) as HFGn.
  pose proof (u5_norm mem _ _ HMI Hphi) as HPHIn.
  pose proof (u4_phi_g _ _ _ _ HPHIn Hb50) as HGg.
  pose proof (u5_norm mem _ _ HMI Hbody) as Hbodyn.
  assert (HPB : bytes_at rsegs (normalize rsegs mem) (g_S g - 1936 + 139)
                  (f_pl (t_len (g_in g) j) (t_FG (g_in g) j) (t_g (g_in g) j))).
  { change (f_pl (t_len (g_in g) j) (t_FG (g_in g) j) (t_g (g_in g) j))
      with (RcFrag.bsl (t_FGf (g_in g) j) 19 (f_pll (t_FG (g_in g) j) (t_g (g_in g) j))).
    pose proof (u5_ba_bsl _ _ _ 19 (f_pll (t_FG (g_in g) j) (t_g (g_in g) j)) HFGn ltac:(lia) ltac:(lia)
                  ltac:(rewrite u4_tFGf_len; lia)) as X.
    replace (g_S g - 1936 + 120 + 19) with (g_S g - 1936 + 139) in X by lia. exact X. }
  assert (LPB : length (f_pl (t_len (g_in g) j) (t_FG (g_in g) j) (t_g (g_in g) j)) =
                Z.to_nat (f_pll (t_FG (g_in g) j) (t_g (g_in g) j))).
  { change (f_pl (t_len (g_in g) j) (t_FG (g_in g) j) (t_g (g_in g) j))
      with (RcFrag.bsl (t_FGf (g_in g) j) 19 (f_pll (t_FG (g_in g) j) (t_g (g_in g) j))).
    apply u5_bsl_len; [lia | lia | rewrite u4_tFGf_len; lia]. }
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 76) 38 ST ltac:(lia) ltac:(lia)) as (jk & Hjk).
  pose proof (u5_rw_ba _ _ _ _ _ Hjk (u5_norm mem _ _ HMI HID) (u4_tIDr_len _ _)) as Hid.
  eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _ [(g_S g - 1936 + 76, g_S g - 1936 + 114)]);
    [exact HFR | exact HP | u4_fp_tac | | |].
  - rewrite sl_mkR_of.
    apply (g07_evt ING joined_byte.joined_byte_holds) with (spv := g_S g - 1936) (blk := phi + 18)
      (pll := f_pll (t_FG (g_in g) j) (t_g (g_in g) j))
      (addr := RcFrag.fg_addr (t_FG (g_in g) j) (t_g (g_in g) j))
      (pb := f_pl (t_len (g_in g) j) (t_FG (g_in g) j) (t_g (g_in g) j)) (idb := t_IDr (g_in g) j)
      (nb := Z_to_bv 8 (fs_nb (fst_at (g_in g) j)))
      (b9 := Z_to_bv 8 (joined_byte (fst_at (g_in g) j) (t_g (g_in g) j) 9))
      (b10 := Z_to_bv 8 (joined_byte (fst_at (g_in g) j) (t_g (g_in g) j) 10)).
    + exact Hsp.
    + unfold rg in H10. rewrite H10. unfold f_pll.
      replace (RcFrag.fg_T (t_FG (g_in g) j) (t_g (g_in g) j) - 13 + 5)
        with (RcFrag.fg_T (t_FG (g_in g) j) (t_g (g_in g) j) - 8) by lia.
      rewrite HR. reflexivity.
    + exact H8.
    + exact H18.
    + unfold rg in H24. rewrite H24, Ebig. reflexivity.
    + lia.
    + lia.
    + exact H16.
    + exact Hpll5.
    + lia.
    + lia.
    (* `first`: have (= 1 at CLOSE by FI), n, and the two bytes joined_byte reads (a Theorem Labs lane's FSb, SlotModel). *)
    + pose proof (u5_ovr _ _ _ (u5_norm mem _ _ HMI Hhave)) as X. rewrite length_le4, Hhv in X. exact X.
    + exact (u5_norm mem _ _ HMI Hnbs).
    + rewrite Hnbu. apply g07_jb_mrd; [left; reflexivity | lia | exact HLb | apply u4_tg_len | | exact HGg].
      replace (g_S g - 1936 + 36 + 5) with (g_S g - 1936 + 41) by lia. exact Hbodyn.
    + rewrite Hnbu. apply g07_jb_mrd; [right; reflexivity | lia | exact HLb | apply u4_tg_len | | exact HGg].
      replace (g_S g - 1936 + 36 + 5) with (g_S g - 1936 + 41) by lia. exact Hbodyn.
    + rewrite (g07_lit8 _ (u5_jb_range _ _ 9)), (g07_lit8 _ (u5_jb_range _ _ 10)). exact Had.
    + exact (u5_u16_read _ _ _ (u5_u16_norm mem _ _ HMI Hadr)).
    + exact (u5_q64_read _ _ _ (u5_q64_norm mem _ _ HMI Hpl)).
    + exact (u5_q64_read _ _ _ (u5_q64_norm mem _ _ HMI Hpll)).
    + exact Hid.
    + exact LPB.
    + exact HPB.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & HZ).
    injection HE; intros; subst.
    assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; [|split; [|split]]|split].
    + apply (u4_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); u4_dj.
    + unfold IDj, IDb, IDB. rewrite (u5_tID_S1 (g_in g) j Hrf).
      split; [exact (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel) HZ)|].
      exact (INGOK _ _ _ (u4_tIDr_len _ _) HIok).
    + exact (u4_FGb_keep g _ mem m' _ (u4_tFGf_len _ _) HG MU' ltac:(u4_dj)).
    + exact (u4_FSj_keep g j mem m' _ HS MU' ltac:(u4_dj)).
    + exact Hrf.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End G07.
