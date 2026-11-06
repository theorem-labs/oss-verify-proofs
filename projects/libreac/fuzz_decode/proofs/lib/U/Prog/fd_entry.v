From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import ReacDecodeLib memcpy_c reac_frame_is_reac_c
  reac_frame_clean_len_c check_round_trip_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr fd_segments_c fd_glue
  fd_seghelp fd_entry_evt fd_exit.
Import ListNotations.
Open Scope Z_scope.

Lemma en_out1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x NO. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); try lia;
    exfalso; apply NO; cbn [outside]; (split; [lia | exact I]).
Qed.

Lemma ob_eq : forall o1 o2 : option byte,
  option_map (@bv_unsigned 8) o1 = option_map (@bv_unsigned 8) o2 -> o1 = o2.
Proof.
  intros [x|] [y|] H; cbn in H; try discriminate; [|reflexivity].
  injection H as H. f_equal. apply bv_eq. exact H.
Qed.

Definition rom_chk (a : Z) (bs : list byte) : bool :=
  forallb (fun i => match option_map (@bv_unsigned 8) (seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i))),
                          option_map (@bv_unsigned 8) (nth_error bs i) with
                    | Some x, Some y => Z.eqb x y
                    | _, _ => false
                    end) (seq 0 (length bs)).

Lemma rom_chk_ok : forall a bs, rom_chk a bs = true ->
  forall i, (i < length bs)%nat -> seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  intros a bs H i Hi. unfold rom_chk in H. rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_seq; lia)). cbv beta in H. apply ob_eq. revert H.
  destruct (option_map (@bv_unsigned 8) (seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)))) as [x|];
    destruct (option_map (@bv_unsigned 8) (nth_error bs i)) as [y|]; intros H; try discriminate.
  apply Z.eqb_eq in H. rewrite H. reflexivity.
Qed.

Lemma got_rom : rom_chk 0x1d6b8 GOTB = true.
Proof. vm_compute. reflexivity. Qed.

Lemma got_bytes : forall B mem, ms_segs B = rsegs -> G_img_c B llvm_RELRO mem -> ro_agree rsegs mem ->
  bytes_at rsegs (normalize rsegs mem) 0x1d6b8 GOTB.
Proof.
  intros B mem HS HG Hro. apply bytes_at_normalize; [exact Hro|].
  assert (L : length GOTB = 24%nat) by reflexivity.
  split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi.
  change (mbyte rsegs mem (0x1d6b8 + Z.of_nat i) = nth_error GOTB i).
  rewrite <- HS. rewrite (HG (0x1d6b8 + Z.of_nat i)).
  - rewrite HS. apply rom_chk_ok; [exact got_rom | rewrite L; exact Hi].
  - exists 0x1d640, 184. split; [left; reflexivity | lia].
Qed.

Lemma blk_of_rom : forall B mem a bs, ms_segs B = rsegs -> ro_agree rsegs mem ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> Mem.ro_addr rsegs (Z_to_bv 64 (a + i)) = true) ->
  rom_chk a bs = true -> blk_data B mem a bs.
Proof.
  intros B mem a bs HS Hro HR HC i Hi. rewrite HS.
  change (mrd rsegs mem (Z_to_bv 64 (a + i)) = nth_error bs (Z.to_nat i)).
  rewrite (Hro _ (HR i Hi)).
  pose proof (rom_chk_ok a bs HC (Z.to_nat i) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. exact E.
Qed.

Lemma mode_ok_const : forall B S mode mem, ms_segs B = rsegs -> ro_agree rsegs mem ->
  mode = MODE_44K1 \/ mode = MODE_48K \/ mode = MODE_96K -> fd_mode_ok B S mode 40 12 mem.
Proof.
  intros B S mode mem HS Hro Hm.
  assert (L4 : forall z, Z.of_nat (length (Z_to_le_bytes 4 z)) = 4) by reflexivity.
  assert (HR : forall k i, (k = 4 \/ k = 8) -> 0 <= i < 4 -> Mem.ro_addr rsegs (Z_to_bv 64 (mode + k + i)) = true).
  { intros k i Hk Hi. apply mode_ro. unfold MODE_44K1, MODE_48K, MODE_96K in Hm. lia. }
  unfold fd_mode_ok. split; [tauto|]. split; [lia|]. split; [lia|]. split.
  - apply (blk_of_rom B mem); [exact HS | exact Hro | intros i Hi; rewrite L4 in Hi; exact (HR 4 i (or_introl eq_refl) Hi) |].
    destruct Hm as [-> | [-> | ->]]; vm_compute; reflexivity.
  - apply (blk_of_rom B mem); [exact HS | exact Hro | intros i Hi; rewrite L4 in Hi; exact (HR 8 i (or_intror eq_refl) Hi) |].
    destruct Hm as [-> | [-> | ->]]; vm_compute; reflexivity.
Qed.

Lemma cells_mode_blk : forall B m A j a b c w, ms_segs B = rsegs ->
  rw_cells rsegs m A (CB 60 j :: C4 a :: C4 b :: C4 c :: w) ->
  blk_data B m (A + 64) (le4 b) /\ blk_data B m (A + 68) (le4 c).
Proof.
  intros B m A j a b c w HS [[Hwf Hb] _].
  destruct Hwf as [Hj _]. cbn [cell_wf] in Hj.
  cbn [cells_bytes cbytes] in Hb.
  apply bytes_at_app in Hb as [_ Hb]. rewrite Hj in Hb.
  apply bytes_at_app in Hb as [_ Hb]. rewrite length_le4 in Hb.
  apply bytes_at_app in Hb as [H1 Hb]. rewrite length_le4 in Hb.
  apply bytes_at_app in Hb as [H2 _].
  replace (A + Z.of_nat 60 + Z.of_nat 4) with (A + 64) in H1 by lia.
  replace (A + Z.of_nat 60 + Z.of_nat 4 + Z.of_nat 4) with (A + 68) in H2 by lia.
  split; apply (bytes_at_blk B); assumption.
Qed.

Lemma rw_cells_tl : forall segs m A c cs, rw_cells segs m A (c :: cs) ->
  rw_cells segs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros segs m A c cs [[[Hc Hwf] Hb] (W0 & W1 & Hw)].
  cbn [cells_bytes] in Hb. apply bytes_at_app in Hb as [_ Hb]. rewrite cbytes_length in Hb by exact Hc.
  split; [split; [exact Hwf | exact Hb]|]. cbn [cells_size] in W1, Hw.
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia. apply Hw. lia.
Qed.

Definition q_en2 (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp mode frame len : Z) (fr : list byte) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (Z_to_bv 64 0x12f10) fc None m' (seg_rom rsegs) /\
    reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\ reg_get R 19 = Z_to_bv 64 mode /\
    reg_get R 9 = Z_to_bv 64 len /\ reg_get R 25 = Z_to_bv 64 frame /\
    munch [(frame, frame + len)] m0 m' /\ wmono rsegs m0 m' /\ bytes_at rsegs m' frame fr.

Section N.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis BND : blocks_nodup B API.
Context (MC : memcpy_contract) (IIR : reac_frame_is_reac_contract) (ICL : reac_frame_clean_len_contract).

Definition fd_entry_post (stk : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word)
    (mem0 : word -> option byte) (md0 : Model) (b : sbound) (c : config) : Prop :=
  exists (fx' : YK11.FPState) L A regs mem md (frame len mode nch ns : Z) (fr : list byte) (u1 u2 u3 : word),
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 FD_DOWN) mem (YK11.seg_rom (ms_segs B))) md /\
    frm_zero (@fp_csr fx') /\
    fd_inv B API (spZ regs0) len frame fr L A regs mem md (sb_malloc b len) /\
    YK11.getr regs 9 = Z_to_bv 64 len /\ YK11.getr regs 25 = Z_to_bv 64 frame /\
    YK11.getr regs 19 = Z_to_bv 64 mode /\ fd_mode_ok B (spZ regs0) mode nch ns mem /\
    YK11.getr regs 3 = YK11.getr regs0 3 /\ YK11.getr regs 4 = YK11.getr regs0 4 /\
    lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md /\
    (forall a k, In (a, k) (blocks L0 A0) -> a <> frame) /\
    rw_cells rsegs mem (spZ regs0 - 116) (C4 u1 :: C4 u2 :: C4 u3 :: llvm_saved_cells regs0).

Theorem fd_entry_holds : forall stk empty L0 A0 regs0 mem0 md0 ra p n pl b,
  llvm_binds B API -> LLVM_K <= stk ->
  lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n ->
  n = Z.of_nat (length pl) -> blk_data B mem0 p pl ->
  spZ regs0 <= 2 ^ 47 -> res_ok_slots A0 b -> llvm_room b ->
  ro_agree rsegs mem0 -> G_img_c B llvm_RELRO mem0 -> frm_zero (@fp_csr fx) -> n < 2 ^ 26 ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 (YK11.seg_rom (ms_segs B))) md0)
    (fd_entry_post stk L0 A0 regs0 mem0 md0 b).
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n pl b (SEGS & HMAL & HFRE & HGG & HG & AX) Hk Hpre Hn Hpd Hsp
    Hres Hroom Hro Hrelro Hfrm H26.
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn1 & Hpl & Hrod).
  pose proof (lf_fr_init B API stk empty L0 A0 regs0 mem0 md0 ra p n Hpre Hro) as FR0.
  unfold LLVM_K, LLVM_FRAME, CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK in Hk.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt. unfold LF_RES_TOP in Hrt.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  assert (Esp : spZ regs0 = bv_unsigned (reg_get regs0 2)) by reflexivity.
  pose proof (bv_unsigned_in_range _ (reg_get regs0 2)) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  set (p' := bv_unsigned (reg_get regs0 10)).
  assert (HP01 : 0 <= p' < 2 ^ 64).
  { unfold p'. pose proof (bv_unsigned_in_range _ (reg_get regs0 10)) as R. unfold bv_modulus in R.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in R. exact R. }
  assert (E10 : reg_get regs0 10 = Z_to_bv 64 p') by (unfold p'; symmetry; apply Z_to_bv_bv_unsigned).
  assert (E11 : reg_get regs0 11 = Z_to_bv 64 (Z.of_nat (length pl))) by (rewrite <- Hn; exact Hn1).
  assert (PAY : 0 < n -> In (p, n) (blocks L0 A0) /\ 4096 <= p /\ p + n <= YM05.alloc_ceiling).
  { intros Hn0. destruct Hpl as [[-> _] | [_ (q & Hq & Hqp)]]; [lia|].
    pose proof (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q n HM Hq) as (R1 & R2). rewrite Hqp in R1, R2.
    split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. lia. }
  assert (Hpp : 0 < n -> p' = p).
  { intros Hn0. destruct (PAY Hn0) as (_ & R1 & R2). unfold p'.
    assert (E : reg_get regs0 10 = Z_to_bv 64 p) by exact Hp. rewrite E. apply MState.unsigned_lit. lia. }
  assert (ST0 : Frame.stk rsegs (normalize rsegs mem0) (spZ regs0 - stk) (bv_unsigned (reg_get regs0 2))).
  { rewrite <- Esp. eapply norm_stk; try eassumption; try lia; unfold LF_RES_TOP; lia. }
  assert (LO0 : spZ regs0 - stk + 176 <= bv_unsigned (reg_get regs0 2)) by lia.
  assert (S630 : bv_unsigned (reg_get regs0 2) < 2 ^ 63) by lia.
  pose proof (mem_inv_normalize rsegs mem0) as MI0.
  assert (HN0 : Z.of_nat (length pl) < 2 ^ 26) by lia.
  assert (HP1 : (0 < length pl)%nat -> bytes_at rsegs (normalize rsegs mem0) p' pl).
  { intros H0. assert (Hn0 : 0 < n) by lia. destruct (PAY Hn0) as (_ & R1 & R2). rewrite (Hpp Hn0).
    apply bytes_at_normalize; [exact Hro|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact Hpd]. }
  assert (HPL1 : (0 < length pl)%nat -> p' + Z.of_nat (length pl) <= spZ regs0 - stk).
  { intros H0. assert (Hn0 : 0 < n) by lia. destruct (PAY Hn0) as (_ & R1 & R2). rewrite (Hpp Hn0). lia. }
  assert (HGL1 : 0x1d6d0 <= spZ regs0 - stk) by lia.
  assert (HPO1 : (0 < length pl)%nat -> 4096 <= p').
  { intros H0. assert (Hn0 : 0 < n) by lia. destruct (PAY Hn0) as (_ & R1 & R2). rewrite (Hpp Hn0). lia. }
  pose proof (got_bytes B mem0 SEGS Hrelro Hro) as HGB. unfold GOTB in HGB.
  apply bytes_at_app in HGB as [HG1 HGB]. rewrite length_le8 in HGB.
  apply bytes_at_app in HGB as [HG2 HG3]. rewrite length_le8 in HG3.
  change (0x1d6b8 + Z.of_nat 8) with 0x1d6c0 in HG2, HG3. change (0x1d6c0 + Z.of_nat 8) with 0x1d6c8 in HG3.
  rewrite SEGS.
  eapply g_run with (stk := stk) (S := spZ regs0) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
    (Q := q_en1 (@fp_regs fx) (@fp_csr fx) (reg_get regs0 3) (reg_get regs0 4) (normalize rsegs mem0)
            (bv_unsigned (reg_get regs0 2) - 176) (spZ regs0 - stk) (p' + en_k pl) (en_len pl)
            [C8 (reg_get regs0 27); C8 (reg_get regs0 26); C8 (reg_get regs0 25); C8 (reg_get regs0 24);
             C8 (reg_get regs0 23); C8 (reg_get regs0 22); C8 (reg_get regs0 21); C8 (reg_get regs0 20);
             C8 (reg_get regs0 19); C8 (reg_get regs0 18); C8 (reg_get regs0 9); C8 (reg_get regs0 8);
             C8 (reg_get regs0 1)]).
  all: try eassumption. all: try lia.
  { unfold Regs6ss.mkR_of, LLVM_ENTRY.
    eapply en1_eq with (lo := spZ regs0 - stk) (p := p') (pl := pl); eassumption. }
  { intros ms (R & m' & mode & nch & ns & j' & -> & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & _).
    exists R, (@fp_regs fx), (Z_to_bv 64 0x14df4), (@fp_csr fx), m',
      [(bv_unsigned (reg_get regs0 2) - 176, bv_unsigned (reg_get regs0 2) - 176 + 176)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply en_out1 in NO. lia. }
  intros R F pc' fc ma HQ regs1 m1 Hx Hrel FR1.
  destruct HQ as (R' & m'' & mode & nch & ns & j' & HE & R1 & R2 & R3 & R4 & R10 & R9 & R18 & R19 & MU1 & WM1 & MI1
    & ST1 & RW1 & Hnch & Hns & Hmode).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  assert (G1 : YK11.getr regs1 1 = Z_to_bv 64 0x12e14) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R1).
  assert (G12 : YK11.getr regs1 2 = Z_to_bv 64 (spZ regs0 - 176)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R2).
  assert (G13 : YK11.getr regs1 3 = YK11.getr regs0 3) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R3).
  assert (G14 : YK11.getr regs1 4 = YK11.getr regs0 4) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R4).
  assert (G110 : YK11.getr regs1 10 = Z_to_bv 64 (en_len pl)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R10).
  assert (G119 : YK11.getr regs1 19 = Z_to_bv 64 mode) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R19).
  assert (G118 : YK11.getr regs1 18 = Z_to_bv 64 (p' + en_k pl)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R18).
  assert (G19 : YK11.getr regs1 9 = Z_to_bv 64 (en_len pl)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R9).
  assert (Hsp1 : spZ regs1 = spZ regs0 - 176) by (unfold spZ at 1; rewrite G12; apply MState.unsigned_lit; lia).
  assert (Hra1' : YK0s.ret_ok (YK11.getr regs1 1)) by (rewrite G1; apply ret_ok_even; reflexivity).
  assert (Hal1 : spZ regs1 mod 16 = 0) by (rewrite Hsp1; Z.div_mod_to_equations; lia).
  assert (Htp1 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by (rewrite G14; exact Htp).
  assert (ROOM1 : room_slots b (en_len pl)).
  { destruct Hroom as (Hl1 & Hl2 & Hl3). apply lf_room; unfold en_len, en_k; lia. }
  pose proof (lf_rw_cells_rel m1 ma _ _ Hrel RW1) as RWa.
  rewrite <- SEGS. change (Z_to_bv 64 0x14df4) with (Z_to_bv 64 LLVM_MALLOC).
  eapply g_malloc with (stk := stk) (S := spZ regs0) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
    (n := en_len pl) (bres := b).
  all: try eassumption. all: try (rewrite ?Hsp1; lia). all: try (rewrite ?Hsp1; unfold ALLOC_STACK; lia).
  intros L1 A1 regs2 mem2 md2 res FR2 Hrp2 G210 Hr1 Hr2 Hr16 Hnimg (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 Hkept2.
  rewrite G1, SEGS.
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & _ & _ & _ & _ & _ & HwX2 & _ & _ & Hro2).
  assert (Hres_in : In (res, en_len pl) (blocks L1 A1)) by (rewrite Eb1; apply in_or_app; right; left; reflexivity).
  assert (PW : pairwise ranges_disjoint (b1 ++ (res, en_len pl) :: b2)).
  { rewrite <- Eb1. exact (mr_blocks_disjoint B _ (aa_laws API) L1 A1 mem2 md2 HM2). }
  assert (MINE : forall a k, In (a, k) (blocks L0 A0) -> a + k <= res \/ res + en_len pl <= a).
  { intros a k Hak. rewrite Eb2 in Hak. pose proof (disj_mid b1 (res, en_len pl) b2 (a, k) PW Hak) as H.
    cbn [fst snd] in H. lia. }
  assert (Hnf : forall a k, In (a, k) (blocks L0 A0) -> a <> res).
  { intros a k Hak Ea. subst a. pose proof (BND L1 A1 mem2 md2 HM2) as ND. rewrite Eb1, map_app in ND.
    cbn [map fst] in ND. apply NoDup_ListNoDup in ND. apply NoDup_remove_2 in ND. apply ND. rewrite <- map_app, <- Eb2.
    apply in_map_iff. exists (res, k). split; [reflexivity | exact Hak]. }
  assert (Y2 : forall r, callee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs1 (Z_to_bv 5 r))
    by exact Hrp2.
  assert (E22 : reg_get regs2 2 = Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 176)).
  { change (reg_get regs2 2) with (YK11.getr regs2 (Z_to_bv 5 2)).
    rewrite (Y2 2 ltac:(unfold callee_saved; lia)). exact G12. }
  assert (E210 : reg_get regs2 10 = Z_to_bv 64 res) by exact G210.
  assert (E219 : reg_get regs2 19 = Z_to_bv 64 mode).
  { change (reg_get regs2 19) with (YK11.getr regs2 (Z_to_bv 5 19)).
    rewrite (Y2 19 ltac:(unfold callee_saved; lia)). exact G119. }
  assert (E218 : reg_get regs2 18 = Z_to_bv 64 (p' + en_k pl)).
  { change (reg_get regs2 18) with (YK11.getr regs2 (Z_to_bv 5 18)).
    rewrite (Y2 18 ltac:(unfold callee_saved; lia)). exact G118. }
  assert (E29 : reg_get regs2 9 = Z_to_bv 64 (en_len pl)).
  { change (reg_get regs2 9) with (YK11.getr regs2 (Z_to_bv 5 9)).
    rewrite (Y2 9 ltac:(unfold callee_saved; lia)). exact G19. }
  assert (HSp2 : 0 <= bv_unsigned (reg_get regs0 2) - 176 < 2 ^ 63) by lia.
  assert (HLB2 : 0 <= en_len pl < 2 ^ 26) by (unfold en_len, en_k; lia).
  assert (HSR2 : 0 < en_len pl -> 0 <= p' + en_k pl < 2 ^ 60).
  { intros Hl0. assert (Hn0 : 0 < n) by (unfold en_len, en_k in Hl0; lia). destruct (PAY Hn0) as (_ & P1 & P2).
    rewrite (Hpp Hn0). unfold en_k. lia. }
  assert (HLEN2 : Z.of_nat (length (skipn (Z.to_nat (en_k pl)) pl)) = en_len pl).
  { rewrite length_skipn. unfold en_len, en_k. lia. }
  assert (HSRC2 : 0 < en_len pl ->
    bytes_at rsegs (normalize rsegs mem2) (p' + en_k pl) (skipn (Z.to_nat (en_k pl)) pl)).
  { intros Hl0. assert (Hn0 : 0 < n) by (unfold en_len, en_k in Hl0; lia). destruct (PAY Hn0) as (Hin0 & P1 & P2).
    rewrite (Hpp Hn0).
    assert (BD : blk_data B mem2 p pl) by (eapply blk_keep; [exact FR2 | rewrite <- Hn; exact Hin0 | exact Hpd]).
    assert (BA : bytes_at rsegs (normalize rsegs mem2) p pl).
    { apply bytes_at_normalize; [exact Hro2|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact BD]. }
    rewrite <- (firstn_skipn (Z.to_nat (en_k pl)) pl) in BA.
    apply bytes_at_app in BA as [_ BA].
    rewrite firstn_length_le in BA by (unfold en_k; lia).
    rewrite Z2Nat.id in BA by (unfold en_k; lia). exact BA. }
  assert (JK : exists junk, 0 < en_len pl -> rw_cells rsegs (normalize rsegs mem2) res [CB (Z.to_nat (en_len pl)) junk]).
  { destruct (Z_lt_le_dec 0 (en_len pl)) as [Hl0|Hl0].
    - destruct (norm_blk B API SEGS AX L1 A1 mem2 md2 res (en_len pl) HM2 Hres_in Hl0 Hro2) as [junk HJ].
      exists junk. intros _. exact HJ.
    - exists []. intros H. lia. }
  destruct JK as [junk HO2].
  assert (HFP2 : 4096 <= res < 2 ^ 60) by lia.
  assert (DSF2 : res + en_len pl <= p' + en_k pl \/ p' + en_k pl + en_len pl <= res).
  { destruct (Z_lt_le_dec 0 n) as [Hn0|Hn0].
    - destruct (PAY Hn0) as (Hin0 & _ & _). rewrite (Hpp Hn0). pose proof (MINE p n Hin0) as H.
      unfold en_len, en_k in *. lia.
    - unfold en_len, en_k. lia. }
  pose proof (mem_inv_normalize rsegs mem2) as MI2.
  eapply g_run with (stk := stk) (S := spZ regs0) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
    (Q := q_en2 (@fp_regs fx) (@fp_csr fx) (reg_get regs2 3) (reg_get regs2 4) (normalize rsegs mem2)
            (bv_unsigned (reg_get regs0 2) - 176) mode res (en_len pl) (skipn (Z.to_nat (en_k pl)) pl)).
  all: try eassumption. all: try lia.
  { unfold Regs6ss.mkR_of.
    eapply en2_eq with (Sp := bv_unsigned (reg_get regs0 2) - 176) (mode := mode) (src := p' + en_k pl)
      (frame := res) (len := en_len pl) (fr := skipn (Z.to_nat (en_k pl)) pl) (junk := junk).
    all: try eassumption.
    unfold en2_k. intros z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m' MU WM _ HBF.
    apply evt_done. unfold q_en2. eexists _, m'. split; [reflexivity|].
    do 6 (split; [reflexivity|]). split; [exact MU|]. split; [exact WM | exact HBF]. }
  { intros ms (R0 & m' & -> & _ & _ & _ & _ & _ & _ & MU & WM & _).
    exists R0, (@fp_regs fx), (Z_to_bv 64 0x12f10), (@fp_csr fx), m', [(res, res + en_len pl)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx0 NO. apply en_out1 in NO. right. exists res, (en_len pl). split; [|lia].
    unfold lf_mine. split; [exact Hres_in|]. split; [lia|]. exact MINE. }
  intros Rb F pc' fc mb HQ regs3 m3 Hx3 Hrel3 FR3.
  destruct HQ as (R' & m'' & HE & Q2 & Q3 & Q4 & Q19 & Q9 & Q25 & MU3 & WM3 & HBF3).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  apply SR_ret.
  pose proof FR3 as (HM3 & HW3 & HB3 & HID3 & _ & _ & _ & _ & _ & Hstw3 & Herr3 & _ & Hro3).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM3) as (Hh3 & Hl3 & _).
  assert (G32 : YK11.getr regs3 2 = Z_to_bv 64 (spZ regs0 - 176)) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact Q2).
  assert (G33 : YK11.getr regs3 3 = YK11.getr regs0 3).
  { rewrite (lf_getr_eqv _ _ _ Hx3). transitivity (YK11.getr regs2 (Z_to_bv 5 3)); [exact Q3|].
    rewrite (Y2 3 ltac:(unfold callee_saved; lia)). exact G13. }
  assert (G34 : YK11.getr regs3 4 = YK11.getr regs0 4).
  { rewrite (lf_getr_eqv _ _ _ Hx3). transitivity (YK11.getr regs2 (Z_to_bv 5 4)); [exact Q4|].
    rewrite (Y2 4 ltac:(unfold callee_saved; lia)). exact G14. }
  assert (G319 : YK11.getr regs3 19 = Z_to_bv 64 mode) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact Q19).
  assert (G39 : YK11.getr regs3 9 = Z_to_bv 64 (en_len pl)) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact Q9).
  assert (G325 : YK11.getr regs3 25 = Z_to_bv 64 res) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact Q25).
  assert (Hsp3 : spZ regs3 = spZ regs0 - 176) by (unfold spZ at 1; rewrite G32; apply MState.unsigned_lit; lia).
  assert (BLK3 : blk_data B m3 res (skipn (Z.to_nat (en_k pl)) pl)).
  { apply (bytes_at_blk B); [exact SEGS|]. exact (proj2 (bytes_at_rel rsegs m3 mb res _ Hrel3) HBF3). }
  assert (RWb : forall a, bv_unsigned (reg_get regs0 2) - 176 <= a < bv_unsigned (reg_get regs0 2) ->
     mbyte rsegs mem2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs mem2 a)).
  { intros a Ha. pose proof (Habove2 a ltac:(lia)) as E. rewrite SEGS in E. exact E. }
  pose proof (lf_rw_cells_frame m1 mem2 _ _ RWa (fun a Ha => RWb a ltac:(cbn [cells_size csize] in Ha; lia))) as RW2.
  assert (NI : forall a, 0x50000 <= a -> ~ in_img B a)
    by (intros a Ha Hi; pose proof (lf_in_img_top B a SEGS Hi) as H; unfold LF_RES_TOP in H; lia).
  assert (SPB : 0x50000 + 176 <= bv_unsigned (reg_get regs0 2)) by (unfold LF_RES_TOP in *; lia).
  pose proof (fun H => lf_rw_cells_norm B mem2 _ _ SEGS Hro2 H RW2) as RW3.
  specialize (RW3 (fun i Hi => NI (bv_unsigned (reg_get regs0 2) - 176 + i) ltac:(destruct Hi as [Hi0 _]; lia))).
  pose proof (rw_cells_transport rsegs [(res, res + en_len pl)] (normalize rsegs mem2) mb _ _ RW3 MU3 WM3
    ltac:(cbn [disjoint_from cells_size csize]; split; [right; lia | exact I])) as RW4.
  pose proof (lf_rw_cells_rel m3 mb _ _ Hrel3 RW4) as RW5.
  assert (MOK : exists nch' ns', fd_mode_ok B (spZ regs0) mode nch' ns' m3).
  { destruct Hmode as [Hc | Hc].
    - exists 40, 12. apply mode_ok_const; [exact SEGS | exact Hro3 | exact Hc].
    - exists nch, ns. destruct (cells_mode_blk B _ _ _ _ _ _ _ SEGS RW5) as [K1 K2].
      rewrite le4_mod in K1, K2.
      unfold fd_mode_ok. split; [right; right; right; unfold FD_KEEP; lia|].
      split; [lia|]. split; [lia|].
      replace (mode + 4) with (bv_unsigned (reg_get regs0 2) - 176 + 64) by lia.
      replace (mode + 8) with (bv_unsigned (reg_get regs0 2) - 176 + 68) by lia.
      split; [exact K1 | exact K2]. }
  destruct MOK as (nch' & ns' & MOK).
  pose proof (rw_cells_tl rsegs m3 _ _ _ RW5) as RWt. cbn [csize] in RWt.
  replace (bv_unsigned (reg_get regs0 2) - 176 + Z.of_nat 60) with (spZ regs0 - 116) in RWt by lia.
  unfold fd_entry_post.
  exists (mkFP (@fp_regs fx) (@fp_csr fx)), L1, A1, regs3, m3, md2, res, (en_len pl), mode, nch', ns',
    (skipn (Z.to_nat (en_k pl)) pl), (Z_to_bv 64 48000), (Z_to_bv 64 nch), (Z_to_bv 64 ns).
  split; [rewrite SEGS; reflexivity|].
  split; [exact Hfrm|].
  split.
  { unfold fd_inv. rewrite Hsp3.
    split; [exact HM3|]. split; [exact HW3|]. split; [exact HB3|].
    split; [Z.div_mod_to_equations; lia|].
    split; [unfold FD_WIN, CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK; lia|].
    split; [lia|].
    split; [intros a Ha; apply Hstw3; unfold FD_WIN, CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK in Ha; lia|].
    split; [intros a Ha; apply Hstw3; unfold FD_FRAME in Ha; lia|].
    split; [rewrite G34; exact Htp|].
    split; [exact Herr3|]. split; [exact HID3|]. split; [rewrite SEGS; exact Hro3|].
    split; [exact Hh3|]. split; [exact Hl3|]. split; [unfold FD_FRAME; reflexivity|].
    split; [exact HLB2|]. split; [exact HLEN2|]. split; [exact Hres_in|].
    split; [exact BLK3|]. split; [exact Hres2|].
    destruct Hroom as (Hl1 & Hl2 & Hl4). unfold fd_room, sb_malloc. cbn [sb_live sb_bytes sb_cap].
    unfold en_len, en_k. repeat split; lia. }
  split; [exact G39|]. split; [exact G325|]. split; [exact G319|]. split; [exact MOK|]. split; [exact G33|]. split; [exact G34|].
  split; [exact FR3|]. split; [exact Hnf|].
  exact RWt.
Qed.

End N.
